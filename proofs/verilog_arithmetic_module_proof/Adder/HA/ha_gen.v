Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Pfv.Lib.Lib. Import SZNotations. Import HMapNotations.
Require Import Pfv.Lang.Lang.
Require Import common.Common.

Module Ha.
  Inductive vid : Type :=
  | carry
  | ha
  | src1
  | src2
  | sum
  .
  
  Definition VExprIdVId := @VExprId vid.
  Coercion VExprIdVId: vid >-> VExpr.
  Definition VPortIdsOneVId := @VPortIdsOne vid.
  Coercion VPortIdsOneVId: vid >-> VPortIds.

  Definition vid_eq_dec: forall (v1 v2: vid), {v1 = v2} + {v1 <> v2} := ltac:(decide equality).
  #[export] Instance vid_t_c_impl : vid_t_c := { vid_t := vid }.
  #[export] Instance vid_ops_impl : vid_ops := { vid_eq_dec := vid_eq_dec }.


  Module M.

    Notation "'carry'" := carry (in custom ce_top).
    Notation "'carry'" := carry (in custom ce_expr).
    Notation "'carry'" := carry (in custom ce_stmt).
    Notation "'carry'" := carry (in custom ce_assign).
    Notation "'carry'" := carry (in custom ce_netdeclassign).
    Notation "'carry'" := carry (in custom ce_vardeclassign).
    Notation "'carry'" := carry (in custom ce_paramassign).
    Notation "'.carry'" := carry (in custom ce_portconnid).
    Notation "'carry'" := carry (in custom ce_ports).
    Notation "'ha'" := ha (in custom ce_top).
    Notation "'ha'" := ha (in custom ce_expr).
    Notation "'ha'" := ha (in custom ce_stmt).
    Notation "'ha'" := ha (in custom ce_assign).
    Notation "'ha'" := ha (in custom ce_netdeclassign).
    Notation "'ha'" := ha (in custom ce_vardeclassign).
    Notation "'ha'" := ha (in custom ce_paramassign).
    Notation "'.ha'" := ha (in custom ce_portconnid).
    Notation "'ha'" := ha (in custom ce_ports).
    Notation "'src1'" := src1 (in custom ce_top).
    Notation "'src1'" := src1 (in custom ce_expr).
    Notation "'src1'" := src1 (in custom ce_stmt).
    Notation "'src1'" := src1 (in custom ce_assign).
    Notation "'src1'" := src1 (in custom ce_netdeclassign).
    Notation "'src1'" := src1 (in custom ce_vardeclassign).
    Notation "'src1'" := src1 (in custom ce_paramassign).
    Notation "'.src1'" := src1 (in custom ce_portconnid).
    Notation "'src1'" := src1 (in custom ce_ports).
    Notation "'src2'" := src2 (in custom ce_top).
    Notation "'src2'" := src2 (in custom ce_expr).
    Notation "'src2'" := src2 (in custom ce_stmt).
    Notation "'src2'" := src2 (in custom ce_assign).
    Notation "'src2'" := src2 (in custom ce_netdeclassign).
    Notation "'src2'" := src2 (in custom ce_vardeclassign).
    Notation "'src2'" := src2 (in custom ce_paramassign).
    Notation "'.src2'" := src2 (in custom ce_portconnid).
    Notation "'src2'" := src2 (in custom ce_ports).
    Notation "'sum'" := sum (in custom ce_top).
    Notation "'sum'" := sum (in custom ce_expr).
    Notation "'sum'" := sum (in custom ce_stmt).
    Notation "'sum'" := sum (in custom ce_assign).
    Notation "'sum'" := sum (in custom ce_netdeclassign).
    Notation "'sum'" := sum (in custom ce_vardeclassign).
    Notation "'sum'" := sum (in custom ce_paramassign).
    Notation "'.sum'" := sum (in custom ce_portconnid).
    Notation "'sum'" := sum (in custom ce_ports).

    Definition m: @VModuleDecl vid := #[
module ha(
    input src1,
    input src2,
    output sum,
    output carry
);
    assign sum = src1 ^ src2;
    assign carry = src1 & src2;
endmodule
    ].
  End M.

  Record Inputs := {
    src1_v: SZ;
    src2_v: SZ
  }.

  Record Outputs := {
    sum_v: SZ;
    carry_v: SZ
  }.

  Record Flops := {
    dummy_flop_v: unit
  }.

  Record Updates := {
    dummy_update: unit
  }.

  Section Helpers.
    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.
    Import ListNotations.
    Import HMapNotations.

    #[export] Instance inputs_structured: StructuredState Inputs := {|
      from_state :=
        fun (state : State) =>
          src1_v <- sfind src1 state;
          src2_v <- sfind src2 state;
          Sret {|
            src1_v := hbits src1_v;
            src2_v := hbits src2_v;
          |};
      to_state := fun i =>
        match i with
        | {| src1_v := src1_v;
             src2_v := src2_v |} =>
          HMapStr [(src1, HMapBits src1_v);
                   (src2, HMapBits src2_v)]
        end
    |}.

    Definition output_to_state (o: Outputs): State :=
      HMapStr [(sum, HMapBits o.(sum_v));
               (carry, HMapBits o.(carry_v))].

    Definition update_to_state (u: Updates): State :=
      HMapStr [].

    #[export] Instance flops_structured: StructuredState Flops := {|
      from_state :=
        fun (state : State) =>
          Sret {| dummy_flop_v := tt |};
      to_state := fun f =>
        match f with
        | _ => HMapStr []
        end
    |}.

    Definition etrs (eid: vid): trsOk MTrs :=
    match eid with
    | _ => Fail TrsUndeclared
    end.

  End Helpers.

End Ha.