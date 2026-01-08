Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Pfv.Lib.Lib. Import SZNotations. Import HMapNotations.
Require Import Pfv.Lang.Lang.
Require Import common.Common.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.common_gen.

Require Import Verification.VerilogArithmeticModule.Adder.RCA.rca_04_gen.

#[local] Existing Instance Rca_04.inputs_structured.
#[local] Existing Instance Rca_04.flops_structured.

Module Rca_08.
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
    Notation "'high_4bit'" := high_4bit (in custom ce_top).
    Notation "'high_4bit'" := high_4bit (in custom ce_expr).
    Notation "'high_4bit'" := high_4bit (in custom ce_stmt).
    Notation "'high_4bit'" := high_4bit (in custom ce_assign).
    Notation "'high_4bit'" := high_4bit (in custom ce_netdeclassign).
    Notation "'high_4bit'" := high_4bit (in custom ce_vardeclassign).
    Notation "'high_4bit'" := high_4bit (in custom ce_paramassign).
    Notation "'.high_4bit'" := high_4bit (in custom ce_portconnid).
    Notation "'high_4bit'" := high_4bit (in custom ce_ports).
    Notation "'low_4bit'" := low_4bit (in custom ce_top).
    Notation "'low_4bit'" := low_4bit (in custom ce_expr).
    Notation "'low_4bit'" := low_4bit (in custom ce_stmt).
    Notation "'low_4bit'" := low_4bit (in custom ce_assign).
    Notation "'low_4bit'" := low_4bit (in custom ce_netdeclassign).
    Notation "'low_4bit'" := low_4bit (in custom ce_vardeclassign).
    Notation "'low_4bit'" := low_4bit (in custom ce_paramassign).
    Notation "'.low_4bit'" := low_4bit (in custom ce_portconnid).
    Notation "'low_4bit'" := low_4bit (in custom ce_ports).
    Notation "'rca_04'" := rca_04 (in custom ce_top).
    Notation "'rca_04'" := rca_04 (in custom ce_expr).
    Notation "'rca_04'" := rca_04 (in custom ce_stmt).
    Notation "'rca_04'" := rca_04 (in custom ce_assign).
    Notation "'rca_04'" := rca_04 (in custom ce_netdeclassign).
    Notation "'rca_04'" := rca_04 (in custom ce_vardeclassign).
    Notation "'rca_04'" := rca_04 (in custom ce_paramassign).
    Notation "'.rca_04'" := rca_04 (in custom ce_portconnid).
    Notation "'rca_04'" := rca_04 (in custom ce_ports).
    Notation "'rca_08'" := rca_08 (in custom ce_top).
    Notation "'rca_08'" := rca_08 (in custom ce_expr).
    Notation "'rca_08'" := rca_08 (in custom ce_stmt).
    Notation "'rca_08'" := rca_08 (in custom ce_assign).
    Notation "'rca_08'" := rca_08 (in custom ce_netdeclassign).
    Notation "'rca_08'" := rca_08 (in custom ce_vardeclassign).
    Notation "'rca_08'" := rca_08 (in custom ce_paramassign).
    Notation "'.rca_08'" := rca_08 (in custom ce_portconnid).
    Notation "'rca_08'" := rca_08 (in custom ce_ports).
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
module rca_08(
    input [7:0] src1,
    input [7:0] src2,
    input sub_flag,
    output [7:0] sum,
    output carry_out
);

    wire carry;

    rca_04 low_4bit(
        .src1       (src1[3:0]),
        .src2       (src2[3:0]),
        .sub_flag   (sub_flag),
        .sum        (sum[3:0]),
        .carry_out  (carry)
    );

    rca_04 high_4bit(
        .src1       (src1[7:4]),
        .src2       (src2[7:4]),
        .sub_flag   (carry),
        .sum        (sum[7:4]),
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
    low_4bit_v: Rca_04.Flops;
    high_4bit_v: Rca_04.Flops
  }.

  Record Updates := {
    low_4bit_update: Rca_04.Updates;
    high_4bit_update: Rca_04.Updates
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
      HMapStr [(low_4bit, Rca_04.update_to_state u.(low_4bit_update));
               (high_4bit, Rca_04.update_to_state u.(high_4bit_update))].

    #[export] Instance flops_structured: StructuredState Flops := {
      from_state :=
        fun (state : State) =>
          low_4bit_s <- sfind low_4bit state;
          low_4bit_v <- from_state (A := Rca_04.Flops) low_4bit_s;
          high_4bit_s <- sfind high_4bit state;
          high_4bit_v <- from_state (A := Rca_04.Flops) high_4bit_s;
          Sret {|
            low_4bit_v := low_4bit_v;
            high_4bit_v := high_4bit_v
          |};
      to_state := fun f =>
        match f with
        | {| low_4bit_v := low_4bit_v;
             high_4bit_v := high_4bit_v |} =>
          HMapStr [(low_4bit, to_state low_4bit_v);
                   (high_4bit, to_state high_4bit_v)]
        end
    }.

    Definition etrs (eid: vid): trsOk MTrs :=
    match eid with
    | low_4bit => Sret (Rca_04.mtrs : MTrs)
    | high_4bit => Sret (Rca_04.mtrs : MTrs)
    | _ => Fail TrsUndeclared
    end.

  End Helpers.

End Rca_08.