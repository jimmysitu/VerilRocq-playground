Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Pfv.Lib.Lib. Import SZNotations. Import HMapNotations.
Require Import Pfv.Lang.Lang.
Require Import common.Common.

Inductive vid : Type :=
| carry (* from rca_04.v, rca_08.v, rca_16.v, rca_32.v *)
| carry_in (* from fa.v, rca_04.v *)
| carry_out (* from fa.v, rca_04.v, rca_08.v, rca_16.v, rca_32.v *)
| fa (* from fa.v, rca_04.v *)
| fa_00 (* from rca_04.v *)
| fa_01 (* from rca_04.v *)
| fa_02 (* from rca_04.v *)
| fa_03 (* from rca_04.v *)
| high_16bit (* from rca_32.v *)
| high_4bit (* from rca_08.v *)
| high_8bit (* from rca_16.v *)
| low_16bit (* from rca_32.v *)
| low_4bit (* from rca_08.v *)
| low_8bit (* from rca_16.v *)
| rca_04 (* from rca_04.v, rca_08.v *)
| rca_08 (* from rca_08.v, rca_16.v *)
| rca_16 (* from rca_16.v, rca_32.v *)
| rca_32 (* from rca_32.v *)
| src1 (* from fa.v, rca_04.v, rca_08.v, rca_16.v, rca_32.v *)
| src2 (* from fa.v, rca_04.v, rca_08.v, rca_16.v, rca_32.v *)
| src2_reg (* from rca_04.v *)
| sub_flag (* from rca_04.v, rca_08.v, rca_16.v, rca_32.v *)
| sum (* from fa.v, rca_04.v, rca_08.v, rca_16.v, rca_32.v *)
.

Definition VExprIdVId := @VExprId vid.
Coercion VExprIdVId: vid >-> VExpr.
Definition VPortIdsOneVId := @VPortIdsOne vid.
Coercion VPortIdsOneVId: vid >-> VPortIds.

Definition vid_vid_eq_dec: forall (v1 v2: vid), {v1 = v2} + {v1 <> v2} := ltac:(decide equality).
#[export] Instance vid_t_c_impl : vid_t_c := {| vid_t := vid |}.
#[export] Instance vid_ops_impl : vid_ops := {| vid_eq_dec := vid_vid_eq_dec |}.
