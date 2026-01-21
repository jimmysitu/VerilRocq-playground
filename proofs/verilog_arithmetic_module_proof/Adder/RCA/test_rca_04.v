Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Pfv.Lib.Lib. Import SZNotations.
(*Require Import Pfv.Lang.Semantics.*)
Require Import Pfv.Lang.Lang.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.common_gen.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.fa_gen.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.fa_trs.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.rca_04_gen.
Import Rca_04.
#[local] Existing Instance vid_t_c_impl.
#[local] Existing Instance vid_ops_impl.
#[local] Existing Instance SZ_sz_ops.
#[local] Existing Instance hmap_array_ops.

Definition ins_s : State := HMapStr [(src1, HMapBits #{3, 4, false});
                                     (src2, HMapBits #{1, 4, false});
                                     (sub_flag, HMapBits #{0, 1, false});
                                     (carry_in, HMapBits #{0, 1, false})].

Definition flp_s : State := HMapStr [(fa_00, HMapEmpty);
                                     (fa_01, HMapEmpty);
                                     (fa_02, HMapEmpty);
                                     (fa_03, HMapEmpty)].

Set Printing Depth 200.
Eval vm_compute in (MTrs_rep_n M.m fmapEmpty etrs 12%nat ins_s flp_s).


(* Step-by-step M.m evaluation to expose hupds effects. *)
Definition decls_m : Decls := declsVModuleDecl M.m.
Definition ctxs_m : State := HMapEmpty.
Definition funcs_m : Funcs := fmapEmpty.
Definition iff0 : State * State := (hupds ins_s flp_s, HMapEmpty).

Definition step_m (iff: State * State) : trsOk (State * State) :=
  trsVModuleDecl_IFF decls_m funcs_m ctxs_m etrs M.m iff.

Definition mitems_m : VModuleItems :=
  match M.m with
  | VModuleDeclAnsi _ _ _ mitems => mitems
  end.

Fixpoint item_at (n: nat) (mitems: @VModuleItems vid_t): option (@VModuleItem vid_t) :=
  match mitems with
  | VModuleItemsOne mitem =>
      match n with
      | O => Some mitem
      | S _ => None
      end
  | VModuleItemsCons mitem rest =>
      match n with
      | O => Some mitem
      | S n' => item_at n' rest
      end
  end.

Definition step_items_n (n: nat) (iff: State * State) : trsOk (State * State) :=
  let fix go n mitems iff :=
    match n with
    | O => Sret iff
    | S n' =>
        match mitems with
        | VModuleItemsOne mitem =>
            trsVModuleItem decls_m funcs_m ctxs_m etrs mitem iff
        | VModuleItemsCons mitem rest =>
            match trsVModuleItem decls_m funcs_m ctxs_m etrs mitem iff with
            | Sret niff => go n' rest niff
            | Fail f => Fail f
            end
        end
    end
  in go n mitems_m iff.


(* Print intermediate states after each module item. *)
Eval vm_compute in (step_items_n 1%nat iff0).
Eval vm_compute in (step_items_n 2%nat iff0).
Eval vm_compute in (step_items_n 3%nat iff0).
Eval vm_compute in (step_items_n 4%nat iff0).
Eval vm_compute in (step_items_n 5%nat iff0).
Eval vm_compute in (step_items_n 6%nat iff0).
Eval vm_compute in (step_items_n 7%nat iff0).
Eval vm_compute in (step_items_n 8%nat iff0).
Eval vm_compute in (step_items_n 9%nat iff0).

(* Inspect the module item order to locate fa_00..fa_03. *)
Eval vm_compute in (item_at 0%nat mitems_m).
Eval vm_compute in (item_at 1%nat mitems_m).
Eval vm_compute in (item_at 2%nat mitems_m). (* assign to src2_reg *)
Eval vm_compute in (item_at 3%nat mitems_m). (* fa_00 *)
Eval vm_compute in (item_at 4%nat mitems_m). (* fa_01 *)
Eval vm_compute in (item_at 5%nat mitems_m). (* fa_02*)
Eval vm_compute in (item_at 6%nat mitems_m). (* fa_03*)

(* Extract sum after each FA instance step. *)
Definition sum_of_iff (iff: State * State) : option hmap :=
  hfind [HEltVid sum] (fst iff).

Definition iff_after_fa_00 : State * State :=
  match step_items_n 4%nat iff0 with
  | Sret iff => iff
  | Fail _ => (HMapEmpty, HMapEmpty)
  end.

Definition iff_after_fa_01 : State * State :=
  match step_items_n 5%nat iff0 with
  | Sret iff => iff
  | Fail _ => (HMapEmpty, HMapEmpty)
  end.

Definition iff_after_fa_02 : State * State :=
  match step_items_n 6%nat iff0 with
  | Sret iff => iff
  | Fail _ => (HMapEmpty, HMapEmpty)
  end.

Definition iff_after_fa_03 : State * State :=
  match step_items_n 7%nat iff0 with
  | Sret iff => iff
  | Fail _ => (HMapEmpty, HMapEmpty)
  end.

Eval vm_compute in (sum_of_iff iff_after_fa_00).
Eval vm_compute in (sum_of_iff iff_after_fa_01).
Eval vm_compute in (sum_of_iff iff_after_fa_02).
Eval vm_compute in (sum_of_iff iff_after_fa_03).

(* Show why sum becomes HMapArr [(0, ...)] after fa_00:
   lvposfind produces HEltInd 0, and hsingle builds HMapArr at that index. *)
Definition sum_bit0_path : hpath := [HEltVid sum; HEltInd #{0, 1, false}].
Definition sum_bit0_val : hmap := HMapBits #{0, 1, false}.
Eval vm_compute in (hsingle sum_bit0_path sum_bit0_val).