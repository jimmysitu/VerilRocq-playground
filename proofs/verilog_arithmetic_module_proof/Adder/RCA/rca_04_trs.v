Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Pfv.Lib.Lib. Import SZNotations.
Require Import Pfv.Lang.Lang.
Require Import common.Common.

Require Import Verification.VerilogArithmeticModule.Adder.RCA.common_gen.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.fa_gen.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.fa_trs.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.rca_04_gen.

Import Rca_04.
Import HMapNotations.
Import SFMonadNotations.

(* Use the instances from rca_04_gen *)
#[local] Existing Instance vid_t_c_impl.
#[local] Existing Instance vid_ops_impl.

#[local] Existing Instance SZ_sz_ops.
#[local] Existing Instance hmap_array_ops.

Module Rca_04Trs.
  Section AbsOps.
    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.
  
    Import ListNotations.
    Import HMapNotations.
  
    Definition trs_structured_sigT: {trs: forall (inputs: Inputs) (flops: Flops), (Updates * Outputs) |
      is_module_trs M.m fmapEmpty etrs Inputs Flops (to_unstructured_trs update_to_state output_to_state trs)
    }.
    Proof.
      destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
      match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
      match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
      clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.

      unshelve epose (trs := _ : Inputs -> Flops -> Updates * Outputs).
      { intros i f. destruct i, f. split; econstructor; eapply _. }
      exists trs.
      red. unfold to_unstructured_trs. intros ???? Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *;
      vm_compute in Htrs; injection Htrs as <- <-.
      2-4: eauto.
      eexists. split; [split|].
      - eapply trsM_iff_rep_is_chain with (n := 3%nat).
        cbv.
        reflexivity.
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
End Rca_04Trs.

