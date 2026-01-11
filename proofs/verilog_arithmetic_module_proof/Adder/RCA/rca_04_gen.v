Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Pfv.Lib.Lib. Import SZNotations. Import HMapNotations.
Require Import Pfv.Lang.Lang.
Require Import common.Common.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.common_gen.

Require Import Verification.VerilogArithmeticModule.Adder.RCA.fa_gen.
Require Import Verification.VerilogArithmeticModule.Adder.RCA.fa_trs.

#[local] Existing Instance Fa.inputs_structured.
#[local] Existing Instance Fa.flops_structured.

Module Rca_04.
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
    Notation "'carry_in'" := carry_in (in custom ce_top).
    Notation "'carry_in'" := carry_in (in custom ce_expr).
    Notation "'carry_in'" := carry_in (in custom ce_stmt).
    Notation "'carry_in'" := carry_in (in custom ce_assign).
    Notation "'carry_in'" := carry_in (in custom ce_netdeclassign).
    Notation "'carry_in'" := carry_in (in custom ce_vardeclassign).
    Notation "'carry_in'" := carry_in (in custom ce_paramassign).
    Notation "'.carry_in'" := carry_in (in custom ce_portconnid).
    Notation "'carry_in'" := carry_in (in custom ce_ports).
    Notation "'carry_out'" := carry_out (in custom ce_top).
    Notation "'carry_out'" := carry_out (in custom ce_expr).
    Notation "'carry_out'" := carry_out (in custom ce_stmt).
    Notation "'carry_out'" := carry_out (in custom ce_assign).
    Notation "'carry_out'" := carry_out (in custom ce_netdeclassign).
    Notation "'carry_out'" := carry_out (in custom ce_vardeclassign).
    Notation "'carry_out'" := carry_out (in custom ce_paramassign).
    Notation "'.carry_out'" := carry_out (in custom ce_portconnid).
    Notation "'carry_out'" := carry_out (in custom ce_ports).
    Notation "'fa'" := fa (in custom ce_top).
    Notation "'fa'" := fa (in custom ce_expr).
    Notation "'fa'" := fa (in custom ce_stmt).
    Notation "'fa'" := fa (in custom ce_assign).
    Notation "'fa'" := fa (in custom ce_netdeclassign).
    Notation "'fa'" := fa (in custom ce_vardeclassign).
    Notation "'fa'" := fa (in custom ce_paramassign).
    Notation "'.fa'" := fa (in custom ce_portconnid).
    Notation "'fa'" := fa (in custom ce_ports).
    Notation "'fa_00'" := fa_00 (in custom ce_top).
    Notation "'fa_00'" := fa_00 (in custom ce_expr).
    Notation "'fa_00'" := fa_00 (in custom ce_stmt).
    Notation "'fa_00'" := fa_00 (in custom ce_assign).
    Notation "'fa_00'" := fa_00 (in custom ce_netdeclassign).
    Notation "'fa_00'" := fa_00 (in custom ce_vardeclassign).
    Notation "'fa_00'" := fa_00 (in custom ce_paramassign).
    Notation "'.fa_00'" := fa_00 (in custom ce_portconnid).
    Notation "'fa_00'" := fa_00 (in custom ce_ports).
    Notation "'fa_01'" := fa_01 (in custom ce_top).
    Notation "'fa_01'" := fa_01 (in custom ce_expr).
    Notation "'fa_01'" := fa_01 (in custom ce_stmt).
    Notation "'fa_01'" := fa_01 (in custom ce_assign).
    Notation "'fa_01'" := fa_01 (in custom ce_netdeclassign).
    Notation "'fa_01'" := fa_01 (in custom ce_vardeclassign).
    Notation "'fa_01'" := fa_01 (in custom ce_paramassign).
    Notation "'.fa_01'" := fa_01 (in custom ce_portconnid).
    Notation "'fa_01'" := fa_01 (in custom ce_ports).
    Notation "'fa_02'" := fa_02 (in custom ce_top).
    Notation "'fa_02'" := fa_02 (in custom ce_expr).
    Notation "'fa_02'" := fa_02 (in custom ce_stmt).
    Notation "'fa_02'" := fa_02 (in custom ce_assign).
    Notation "'fa_02'" := fa_02 (in custom ce_netdeclassign).
    Notation "'fa_02'" := fa_02 (in custom ce_vardeclassign).
    Notation "'fa_02'" := fa_02 (in custom ce_paramassign).
    Notation "'.fa_02'" := fa_02 (in custom ce_portconnid).
    Notation "'fa_02'" := fa_02 (in custom ce_ports).
    Notation "'fa_03'" := fa_03 (in custom ce_top).
    Notation "'fa_03'" := fa_03 (in custom ce_expr).
    Notation "'fa_03'" := fa_03 (in custom ce_stmt).
    Notation "'fa_03'" := fa_03 (in custom ce_assign).
    Notation "'fa_03'" := fa_03 (in custom ce_netdeclassign).
    Notation "'fa_03'" := fa_03 (in custom ce_vardeclassign).
    Notation "'fa_03'" := fa_03 (in custom ce_paramassign).
    Notation "'.fa_03'" := fa_03 (in custom ce_portconnid).
    Notation "'fa_03'" := fa_03 (in custom ce_ports).
    Notation "'rca_04'" := rca_04 (in custom ce_top).
    Notation "'rca_04'" := rca_04 (in custom ce_expr).
    Notation "'rca_04'" := rca_04 (in custom ce_stmt).
    Notation "'rca_04'" := rca_04 (in custom ce_assign).
    Notation "'rca_04'" := rca_04 (in custom ce_netdeclassign).
    Notation "'rca_04'" := rca_04 (in custom ce_vardeclassign).
    Notation "'rca_04'" := rca_04 (in custom ce_paramassign).
    Notation "'.rca_04'" := rca_04 (in custom ce_portconnid).
    Notation "'rca_04'" := rca_04 (in custom ce_ports).
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
    Notation "'src2_reg'" := src2_reg (in custom ce_top).
    Notation "'src2_reg'" := src2_reg (in custom ce_expr).
    Notation "'src2_reg'" := src2_reg (in custom ce_stmt).
    Notation "'src2_reg'" := src2_reg (in custom ce_assign).
    Notation "'src2_reg'" := src2_reg (in custom ce_netdeclassign).
    Notation "'src2_reg'" := src2_reg (in custom ce_vardeclassign).
    Notation "'src2_reg'" := src2_reg (in custom ce_paramassign).
    Notation "'.src2_reg'" := src2_reg (in custom ce_portconnid).
    Notation "'src2_reg'" := src2_reg (in custom ce_ports).
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
module rca_04(
    input [3:0] src1,
    input [3:0] src2,
    input sub_flag,
    input carry_in,
    output [3:0] sum,
    output carry_out
);
    wire [3:0] src2_reg;
    wire [2:0] carry;

(* always @* begin *)
(* if(sub_flag)    src2_reg = ~src2; *)
(* else            src2_reg = src2; *)
(* end *)
    assign src2_reg = sub_flag ? ~src2 : src2;

    fa fa_00(
        .src1       (src1[0]),
        .src2       (src2_reg[0]),
        .carry_in   (carry_in),
        .sum        (sum[0]),
        .carry_out  (carry[0])   
    );

    fa fa_01(
        .src1       (src1[1]),
        .src2       (src2_reg[1]),
        .carry_in   (carry[0]),
        .sum        (sum[1]),
        .carry_out  (carry[1])   
    );

    fa fa_02(
        .src1       (src1[2]),
        .src2       (src2_reg[2]),
        .carry_in   (carry[1]),
        .sum        (sum[2]),
        .carry_out  (carry[2])   
    );

    fa fa_03(
        .src1       (src1[3]),
        .src2       (src2_reg[3]),
        .carry_in   (carry[2]),
        .sum        (sum[3]),
        .carry_out  (carry_out)   
    );
endmodule
    ].
  End M.

  Record Inputs := {
    src1_v: SZ;
    src2_v: SZ;
    sub_flag_v: SZ;
    carry_in_v: SZ
  }.

  Record Outputs := {
    sum_v: SZ;
    carry_out_v: SZ
  }.

  Record Flops := {
    fa_00_v: Fa.Flops;
    fa_01_v: Fa.Flops;
    fa_02_v: Fa.Flops;
    fa_03_v: Fa.Flops
  }.

  Record Updates := {
    fa_00_update: Fa.Updates;
    fa_01_update: Fa.Updates;
    fa_02_update: Fa.Updates;
    fa_03_update: Fa.Updates
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
          carry_in_v <- sfind carry_in state;
          Sret {|
            src1_v := hbits src1_v;
            src2_v := hbits src2_v;
            sub_flag_v := hbits sub_flag_v;
            carry_in_v := hbits carry_in_v;
          |};
      to_state := fun i =>
        match i with
        | {| src1_v := src1_v;
             src2_v := src2_v;
             sub_flag_v := sub_flag_v;
             carry_in_v := carry_in_v |} =>
          HMapStr [(src1, HMapBits src1_v);
                   (src2, HMapBits src2_v);
                   (sub_flag, HMapBits sub_flag_v);
                   (carry_in, HMapBits carry_in_v)]
        end
    }.

    Definition output_to_state (o: Outputs): State :=
      HMapStr [(sum, HMapBits o.(sum_v));
               (carry_out, HMapBits o.(carry_out_v))].

    Definition update_to_state (u: Updates): State :=
      hupds (hsingle_opt fa_00 (Fa.update_to_state u.(fa_00_update)))
      (hupds (hsingle_opt fa_01 (Fa.update_to_state u.(fa_01_update)))
      (hupds (hsingle_opt fa_02 (Fa.update_to_state u.(fa_02_update)))
      (      (hsingle_opt fa_03 (Fa.update_to_state u.(fa_03_update))))))
      .

    (*
      HMapStr [(fa_00, Fa.update_to_state u.(fa_00_update));
               (fa_01, Fa.update_to_state u.(fa_01_update));
               (fa_02, Fa.update_to_state u.(fa_02_update));
               (fa_03, Fa.update_to_state u.(fa_03_update))].
    *)

    #[export] Instance flops_structured: StructuredState Flops := {
      from_state :=
        fun (state : State) =>
          fa_00_s <- sfind fa_00 state <~ HMapEmpty;
          fa_00_v <- from_state (A := Fa.Flops) fa_00_s;
          fa_01_s <- sfind fa_01 state <~ HMapEmpty;
          fa_01_v <- from_state (A := Fa.Flops) fa_01_s;
          fa_02_s <- sfind fa_02 state <~ HMapEmpty;
          fa_02_v <- from_state (A := Fa.Flops) fa_02_s;
          fa_03_s <- sfind fa_03 state <~ HMapEmpty;
          fa_03_v <- from_state (A := Fa.Flops) fa_03_s;
          Sret {|
            fa_00_v := fa_00_v;
            fa_01_v := fa_01_v;
            fa_02_v := fa_02_v;
            fa_03_v := fa_03_v
          |};
      to_state := fun f =>
        match f with
        | {| fa_00_v := fa_00_v;
             fa_01_v := fa_01_v;
             fa_02_v := fa_02_v;
             fa_03_v := fa_03_v |} =>
          hupds (hsingle_opt fa_00 (to_state  fa_00_v))
          (hupds (hsingle_opt fa_01 (to_state fa_01_v))
          (hupds (hsingle_opt fa_02 (to_state fa_02_v))
                 (hsingle_opt fa_03 (to_state fa_03_v))))
        (*
          HMapStr [(fa_00, to_state fa_00_v);
                   (fa_01, to_state fa_01_v);
                   (fa_02, to_state fa_02_v);
                   (fa_03, to_state fa_03_v)]
        *)
        end
    }.

    Definition etrs (eid: vid): trsOk MTrs :=
    match eid with
    | fa_00 => Sret (FaTrs.mtrs : MTrs)
    | fa_01 => Sret (FaTrs.mtrs : MTrs)
    | fa_02 => Sret (FaTrs.mtrs : MTrs)
    | fa_03 => Sret (FaTrs.mtrs : MTrs)
    | _ => Fail TrsUndeclared
    end.

  End Helpers.

End Rca_04.