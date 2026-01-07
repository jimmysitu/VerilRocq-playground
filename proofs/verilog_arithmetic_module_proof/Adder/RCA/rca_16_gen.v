Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Pfv.Lib.Lib. Import SZNotations. Import HMapNotations.
Require Import Pfv.Lang.Lang.
Require Import common.Common.

Require Import Verification.VerilogArithmeticModule.Adder.RCA.rca_08_gen.

Module Rca_16.
  Inductive vid : Type :=
  | carry
  | carry_out
  | high_8bit
  | low_8bit
  | rca_08
  | rca_16
  | src1
  | src2
  | sub_flag
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
    Notation "'carry_out'" := carry_out (in custom ce_top).
    Notation "'carry_out'" := carry_out (in custom ce_expr).
    Notation "'carry_out'" := carry_out (in custom ce_stmt).
    Notation "'carry_out'" := carry_out (in custom ce_assign).
    Notation "'carry_out'" := carry_out (in custom ce_netdeclassign).
    Notation "'carry_out'" := carry_out (in custom ce_vardeclassign).
    Notation "'carry_out'" := carry_out (in custom ce_paramassign).
    Notation "'.carry_out'" := carry_out (in custom ce_portconnid).
    Notation "'carry_out'" := carry_out (in custom ce_ports).
    Notation "'high_8bit'" := high_8bit (in custom ce_top).
    Notation "'high_8bit'" := high_8bit (in custom ce_expr).
    Notation "'high_8bit'" := high_8bit (in custom ce_stmt).
    Notation "'high_8bit'" := high_8bit (in custom ce_assign).
    Notation "'high_8bit'" := high_8bit (in custom ce_netdeclassign).
    Notation "'high_8bit'" := high_8bit (in custom ce_vardeclassign).
    Notation "'high_8bit'" := high_8bit (in custom ce_paramassign).
    Notation "'.high_8bit'" := high_8bit (in custom ce_portconnid).
    Notation "'high_8bit'" := high_8bit (in custom ce_ports).
    Notation "'low_8bit'" := low_8bit (in custom ce_top).
    Notation "'low_8bit'" := low_8bit (in custom ce_expr).
    Notation "'low_8bit'" := low_8bit (in custom ce_stmt).
    Notation "'low_8bit'" := low_8bit (in custom ce_assign).
    Notation "'low_8bit'" := low_8bit (in custom ce_netdeclassign).
    Notation "'low_8bit'" := low_8bit (in custom ce_vardeclassign).
    Notation "'low_8bit'" := low_8bit (in custom ce_paramassign).
    Notation "'.low_8bit'" := low_8bit (in custom ce_portconnid).
    Notation "'low_8bit'" := low_8bit (in custom ce_ports).
    Notation "'rca_08'" := rca_08 (in custom ce_top).
    Notation "'rca_08'" := rca_08 (in custom ce_expr).
    Notation "'rca_08'" := rca_08 (in custom ce_stmt).
    Notation "'rca_08'" := rca_08 (in custom ce_assign).
    Notation "'rca_08'" := rca_08 (in custom ce_netdeclassign).
    Notation "'rca_08'" := rca_08 (in custom ce_vardeclassign).
    Notation "'rca_08'" := rca_08 (in custom ce_paramassign).
    Notation "'.rca_08'" := rca_08 (in custom ce_portconnid).
    Notation "'rca_08'" := rca_08 (in custom ce_ports).
    Notation "'rca_16'" := rca_16 (in custom ce_top).
    Notation "'rca_16'" := rca_16 (in custom ce_expr).
    Notation "'rca_16'" := rca_16 (in custom ce_stmt).
    Notation "'rca_16'" := rca_16 (in custom ce_assign).
    Notation "'rca_16'" := rca_16 (in custom ce_netdeclassign).
    Notation "'rca_16'" := rca_16 (in custom ce_vardeclassign).
    Notation "'rca_16'" := rca_16 (in custom ce_paramassign).
    Notation "'.rca_16'" := rca_16 (in custom ce_portconnid).
    Notation "'rca_16'" := rca_16 (in custom ce_ports).
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
    Notation "'sub_flag'" := sub_flag (in custom ce_top).
    Notation "'sub_flag'" := sub_flag (in custom ce_expr).
    Notation "'sub_flag'" := sub_flag (in custom ce_stmt).
    Notation "'sub_flag'" := sub_flag (in custom ce_assign).
    Notation "'sub_flag'" := sub_flag (in custom ce_netdeclassign).
    Notation "'sub_flag'" := sub_flag (in custom ce_vardeclassign).
    Notation "'sub_flag'" := sub_flag (in custom ce_paramassign).
    Notation "'.sub_flag'" := sub_flag (in custom ce_portconnid).
    Notation "'sub_flag'" := sub_flag (in custom ce_ports).
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
module rca_16(
    input [15:0] src1,
    input [15:0] src2,
    input sub_flag,
    output [15:0] sum,
    output carry_out
);

    wire carry;

    rca_08 low_8bit(
        .src1       (src1[7:0]),
        .src2       (src2[7:0]),
        .sub_flag   (sub_flag),
        .sum        (sum[7:0]),
        .carry_out  (carry)
    );

    rca_08 high_8bit(
        .src1       (src1[15:8]),
        .src2       (src2[15:8]),
        .sub_flag   (carry),
        .sum        (sum[15:8]),
        .carry_out  (carry_out)
    );
endmodule
    ].
  End M.

  Record Inputs := {
    src1_v: SZ;
    src2_v: SZ;
    sub_flag_v: SZ
  }.

  Record Outputs := {
    sum_v: SZ;
    carry_out_v: SZ
  }.

  Record Flops := {
    low_8bit_v: Rca_08.Flops;
    high_8bit_v: Rca_08.Flops
  }.

  Record Updates := {
    low_8bit_update: Rca_08.Updates;
    high_8bit_update: Rca_08.Updates
  }.

  Section Helpers.
    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.
    Import ListNotations.
    Import HMapNotations.

    #[export] Instance inputs_structured: StructuredState Inputs := {
      from_state :=
        fun (state : State) =>
          src1_v <- sfind src1 state;
          src2_v <- sfind src2 state;
          sub_flag_v <- sfind sub_flag state;
          Sret {|
            src1_v := hbits src1_v;
            src2_v := hbits src2_v;
            sub_flag_v := hbits sub_flag_v;
          |};
      to_state := fun i =>
        match i with
        | {| src1_v := src1_v;
             src2_v := src2_v;
             sub_flag_v := sub_flag_v |} =>
          HMapStr [(src1, HMapBits src1_v);
                   (src2, HMapBits src2_v);
                   (sub_flag, HMapBits sub_flag_v)]
        end
    }.

    Definition output_to_state (o: Outputs): State :=
      HMapStr [(sum, HMapBits o.(sum_v));
               (carry_out, HMapBits o.(carry_out_v))].

    Definition update_to_state (u: Updates): State :=
      HMapStr [(low_8bit, Rca_08.update_to_state u.(low_8bit_update));
               (high_8bit, Rca_08.update_to_state u.(high_8bit_update))].

    #[export] Instance flops_structured: StructuredState Flops := {
      from_state :=
        fun (state : State) =>
          low_8bit_s <- sfind low_8bit state;
          low_8bit_v <- from_state (A := Rca_08.Flops) low_8bit_s;
          high_8bit_s <- sfind high_8bit state;
          high_8bit_v <- from_state (A := Rca_08.Flops) high_8bit_s;
          Sret {|
            low_8bit_v := low_8bit_v;
            high_8bit_v := high_8bit_v
          |};
      to_state := fun f =>
        match f with
        | {| low_8bit_v := low_8bit_v;
             high_8bit_v := high_8bit_v |} =>
          HMapStr [(low_8bit, to_state low_8bit_v);
                   (high_8bit, to_state high_8bit_v)]
        end
    }.

    Definition etrs (eid: vid): trsOk MTrs :=
    match eid with
    | low_8bit => Sret (Rca_08.mtrs : MTrs)
    | high_8bit => Sret (Rca_08.mtrs : MTrs)
    | _ => Fail TrsUndeclared
    end.

  End Helpers.

End Rca_16.