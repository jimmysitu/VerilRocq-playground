Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Pfv.Lib.Lib. Import SZNotations.
Require Import Pfv.Lang.Lang.
Require Import common.Common.

Require Import Verification.VerilogArithmeticModule.Adder.RCA.common_gen.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.fa_gen.

Import Fa.
Import HMapNotations.
Import SFMonadNotations.

(* Use the instances from fa_gen *)
#[local] Existing Instance vid_t_c_impl.
#[local] Existing Instance vid_ops_impl.

#[local] Existing Instance SZ_sz_ops.
#[local] Existing Instance hmap_array_ops.

Module FaTrs.
Section AbsOps.
  Context `{sz_ops} `{array_ops hmap}.

  Import ListNotations.
  Import HMapNotations.

  Definition trs_structured_sigT: {trs: forall (inputs: Inputs) (flops: Flops), (Updates * Outputs) |
    is_module_trs M.m fmapEmpty etrs Inputs Flops (to_unstructured_trs update_to_state output_to_state trs)
  }.
  Proof.
    unshelve epose (trs := _ : Inputs -> Flops -> Updates * Outputs).
    { intros i f. destruct i, f. split; econstructor; eapply _. }
    exists trs.
    red. unfold to_unstructured_trs. intros ???? Htrs. unfold format.
    destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
    vm_compute in Htrs; injection Htrs as <- <-.
    2-4: eauto.
    eexists _. split; [split|].
    { eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity. }
    - cbv. reflexivity.
    - cbv. reflexivity.
    all: cbv; reflexivity.
  Defined.

  Definition trs_structured := proj1_sig trs_structured_sigT.

  Definition mtrs: MTrsOf M.m fmapEmpty etrs Inputs Flops.
  Proof.
    eapply mk_MTrsOf with (mtrsof_mtrs := (Build_MTrs _ _ (to_unstructured_trs _ _ trs_structured))).
    1-2: vm_compute; reflexivity. unfold mtrs_func.
    eapply (proj2_sig trs_structured_sigT).
  Defined.

  #[global] Opaque trs_structured.

End AbsOps.
End FaTrs.

Module FaSpec.

  Import Fa.
  Import SZNotations. (* Import bitvector notations, such as .^, etc. *)

  (* 1. Define the correctness property (Specification) of the full adder *)
  Definition fa_spec_prop (i: Inputs) (o: Outputs) : Prop :=
    o.(sum_v) =
      sz_b_xor (sz_b_xor i.(src1_v) i.(src2_v)) i.(carry_in_v) /\
    o.(carry_out_v) =
      sz_b_or
        (sz_b_or
           (sz_b_and i.(src1_v) i.(src2_v))
           (sz_b_and i.(src2_v) i.(carry_in_v)))
        (sz_b_and i.(carry_in_v) i.(src1_v)).

  (* Make it avaliable for unfold *)
  #[local] Transparent FaTrs.trs_structured.

  (* 2. Correctness theorem *)
  Theorem fa_correct : forall (i: Inputs) (f: Flops),
    let (u, o) := FaTrs.trs_structured i f in
    fa_spec_prop i o.
  Proof.
    intros i f.
    unfold fa_spec_prop.
    unfold FaTrs.trs_structured.

    unfold FaTrs.trs_structured_sigT.
    cbn.

    destruct i;
    destruct f.

    simpl.

    split; reflexivity.
  Qed.

  (* Full adder arithmetic Spec *)
  Definition fa_arithmetic_spec (i: Inputs) (o: Outputs) : Prop :=
    forall (src1_b src2_b carry_in_b : bool),
    i.(src1_v) = #{Z.b2z src1_b, 1, false} ->
    i.(src2_v) = #{Z.b2z src2_b, 1, false} ->
    i.(carry_in_v) = #{Z.b2z carry_in_b, 1, false} ->
    (
      o.(sum_v).(szof) = 1 /\
      o.(carry_out_v).(szof) = 1 /\
      let a := Z.b2z src1_b in
      let b := Z.b2z src2_b in
      let cin := Z.b2z carry_in_b in
      let s := szNorm (szUnsigned o.(sum_v)) in
      let c := szNorm (szUnsigned o.(carry_out_v)) in
      (a + b + cin)%Z = (s + 2 * c)%Z
    ).

  Theorem fa_arithmetic_correct : forall (i: Inputs) (f: Flops),
    fa_arithmetic_spec i (snd (FaTrs.trs_structured i f)).
  Proof.
    intros i f.

    (* 1. Use the previously proven logical Spec (fa_correct) *)
    pose proof (fa_correct i f) as H_logic.

    unfold fa_arithmetic_spec.

    intros src1_b src2_b carry_in_b H_src1 H_src2 H_cin.

    destruct (FaTrs.trs_structured i f) as [u o].
    unfold fa_spec_prop in H_logic.
    destruct H_logic as [Hsum Hcarry].

    rewrite H_src1, H_src2, H_cin in Hsum.
    rewrite H_src1, H_src2, H_cin in Hcarry.
    unfold snd.
    rewrite Hsum, Hcarry.

    destruct src1_b, src2_b, carry_in_b.
    all:
      simpl szof;
      split; [reflexivity | split; [reflexivity | vm_compute; reflexivity]].
  Qed.

End FaSpec.

