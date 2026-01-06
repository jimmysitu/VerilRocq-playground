Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Pfv.Lib.Lib. Import SZNotations.
Require Import Pfv.Lang.Lang.
Require Import common.Common.

Require Import Verification.VerilogArithmeticModule.Adder.HA.ha_gen.

Import Ha.
Import HMapNotations.
Import SFMonadNotations.

(* Use the instances from ha_gen *)
Existing Instance vid_t_c_impl.
Existing Instance vid_ops_impl.

#[local] Existing Instance SZ_sz_ops.
#[local] Existing Instance hmap_array_ops.

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

Module HaSpec.

  Import Ha.
  Import SZNotations. (* Import bitvector notations, such as .^, etc. *)

  (* 1. Define the correctness property (Specification) of the half-adder
     Here, we use bit-level logic:
     - sum should be the XOR of src1 and src2
     - carry should be the AND of src1 and src2
     
     Note: VerilRocq's library (Pfv.Lib.Lib) typically provides szBXor (for ^) and szBAnd (for &) 
     or similar bitwise operators. We assume these standard operators are present.
     According to the Verilog code in ha_gen.v:
     assign sum = src1 ^ src2;
     assign carry = src1 & src2;
  *)
  Definition ha_spec_prop (i: Inputs) (o: Outputs) : Prop :=
    o.(sum_v) = sz_b_xor i.(src1_v) i.(src2_v) /\
    o.(carry_v) = sz_b_and i.(src1_v) i.(src2_v).

  (* To unfold trs_structured in the proof,
     we need to make it transparent, or explicitly unfold it in the proof script. *)
  #[local] Transparent trs_structured.

  (* 2. Correctness theorem 
     Theorem statement: For any input i and any state f (the half-adder is stateless, so f is empty),
     if we take one transition (trs_structured) at this state,
     the output o must satisfy the property defined by ha_spec_prop.
  *)
  Theorem ha_correct : forall (i: Inputs) (f: Flops),
    let (u, o) := trs_structured i f in
    ha_spec_prop i o.
  Proof.
    intros i f.
    (* Unfold the definition of the spec *)
    unfold ha_spec_prop.
    unfold trs_structured.

    unfold trs_structured_sigT.
    cbn.

    (* Must destruct both i (Inputs) and f (Flops) *)
    destruct i;
    destruct f.

    simpl.

    split; reflexivity.
  
  Qed.

  (* Half adder arithmetic Spec *)
  Definition ha_arithmetic_spec (i: Inputs) (o: Outputs) : Prop :=
    (* For 1-bit inputs *)
    (i.(src1_v).(szof) = 1 /\ i.(src2_v).(szof) = 1 ) ->
    
    (* Accessing szof field to check if the width is 1 *)
    o.(sum_v).(szof)  = 1 /\
    o.(carry_v).(szof) = 1 /\
    
    (* Use szNorm (szUnsigned ...) to convert bitvectors to unsigned integers (Z) *)
    let a := szNorm (szUnsigned i.(src1_v)) in
    let b := szNorm (szUnsigned i.(src2_v)) in
    let s := szNorm (szUnsigned o.(sum_v)) in
    let c := szNorm (szUnsigned o.(carry_v)) in
 
    (* Here, + and * are arithmetic operations on Z *)
    (a + b)%Z = (s + 2 * c)%Z.
  
  Theorem ha_arithmetic_correct : forall (i: Inputs) (f: Flops),
    ha_arithmetic_spec i (snd (trs_structured i f)).
  Proof.
    intros i f.

    (* 1. Use the previously proven logical Spec (ha_correct) *)
    (* ha_correct tells us that the output sum equals XOR, and carry equals AND *)
    pose proof (ha_correct i f) as H_logic.

    (* 2. Unfold the definition, preparing for substitution *)
    unfold ha_arithmetic_spec.

    (* 3. The key step: now we need to introduce the hypothesis that the inputs are valid *)
    intros H_inputs_valid.
    destruct H_inputs_valid as [H_src1_wd H_src2_wd]. 
    (* Now we have the hypotheses:
      H_src1_wd: i.(src1_v).(szof) = 1 
      H_src2_wd: i.(src2_v).(szof) = 1 
    *)

    (* The trick here is to destruct the return value of trs_structured
       so that sum_v and carry_v in the Goal are exposed *)
    destruct (trs_structured i f) as [u o].
    unfold ha_spec_prop in H_logic. (* This yields o.sum_v = ... /\ o.carry_v = ... *)
    destruct H_logic as [Hsum Hcarry].
  
    unfold snd.
    (* 3. Substitute the output variables of Spec with input expressions *)
    rewrite Hsum, Hcarry.
 
    split.
    { (* Prove that the width of sum is 1 *)
      (* sum_v = sz_b_xor i.(src1_v) i.(src2_v).
         The width of sz_b_xor is max(i.(src1_v).szof, i.(src2_v).szof). *)
      unfold sz_b_xor.
      simpl.
      rewrite H_src1_wd, H_src2_wd.
      simpl Z.max.
      reflexivity.
    }

    split.
    { (* Prove that the width of carry is 1 *)
      (* carry_v = sz_b_and i.(src1_v) i.(src2_v);
         The width of sz_b_and is max(i.(src1_v).szof, i.(src2_v).szof). *)
      unfold sz_b_and.
      simpl.
      rewrite H_src1_wd, H_src2_wd.
      simpl Z.max.
      reflexivity.
    }
    
    (* Prove the arithmetic equality *)
    unfold szUnsigned, szNorm.
    simpl.
    unfold szNorm.
    rewrite H_src1_wd, H_src2_wd.
    simpl Z.pow; simpl Z.max.

    (* Abstract the values of the input bits *)
    remember (zof i.(src1_v) mod 2) as bit1.
    remember (zof i.(src2_v) mod 2) as bit2.

    assert (Hbit1: bit1 = 0 \/ bit1 = 1).
    { rewrite Heqbit1. 
      pose proof (Z.mod_pos_bound (zof i.(src1_v)) 2).
      lia. }
    assert (Hbit2: bit2 = 0 \/ bit2 = 1).
    { rewrite Heqbit2. 
      pose proof (Z.mod_pos_bound (zof i.(src2_v)) 2).
      lia. }

    unfold szNormZ.
    destruct (snof i.(src1_v)); destruct (snof i.(src2_v)).
    - destruct Hbit1 as [-> | ->]. destruct Hbit2 as [-> | ->].
      * unfold szNormZ.
  Qed.
  
End HaSpec.