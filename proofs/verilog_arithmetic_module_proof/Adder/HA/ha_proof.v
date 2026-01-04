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
