#! /usr/bin/env python3

import sys
import os
import re
from pyverilog.vparser.parser import parse
from pyverilog.vparser.ast import *

class VerilogDataCollector:
    def __init__(self):
        self.module_name = ""
        self.inputs = []  # (name, width_node)
        self.outputs = [] # (name, width_node)
        self.regs = {}    # name -> width_node
        self.wires = {}   # name -> width_node
        self.flops = set() # set of names (LHS of <=)
        self.instances = [] # (type, name)
        self.identifiers = set()

    def visit(self, node):
        if isinstance(node, ModuleDef):
            self.module_name = node.name
            self.identifiers.add(node.name)
        
        elif isinstance(node, Input):
            self.inputs.append((node.name, node.width))
            self.identifiers.add(node.name)
        
        elif isinstance(node, Output):
            self.outputs.append((node.name, node.width))
            self.identifiers.add(node.name)
            
        elif isinstance(node, Reg):
            self.regs[node.name] = node.width
            self.identifiers.add(node.name)
            
        elif isinstance(node, Wire):
            self.wires[node.name] = node.width
            self.identifiers.add(node.name)

        elif isinstance(node, Instance):
            self.instances.append((node.module, node.name))
            self.identifiers.add(node.module)
            self.identifiers.add(node.name)

        elif isinstance(node, PortArg):
            if node.portname:
                self.identifiers.add(node.portname)

        elif isinstance(node, NonblockingSubstitution):
            # LHS is likely a flop
            self._collect_lvalue(node.left)

        elif isinstance(node, Identifier):
            self.identifiers.add(node.name)

        # Recursively visit children
        for child in node.children():
            self.visit(child)

    def _collect_lvalue(self, node):
        if isinstance(node, Lvalue):
            for child in node.children():
                self._collect_lvalue(child)
        elif isinstance(node, Identifier):
            self.flops.add(node.name)
            self.identifiers.add(node.name)
        elif isinstance(node, Pointer):
            self._collect_lvalue(node.var)
        elif isinstance(node, Partselect):
            self._collect_lvalue(node.var)

class RocqGenerator:
    def __init__(self, data: VerilogDataCollector, verilog_content: str, output_path: str = None, logical_prefix: str = ""):
        self.data = data
        self.raw_verilog = self._sanitize_verilog(verilog_content)
        self.mod_name = data.module_name
        self.cap_mod_name = self.mod_name.capitalize() if self.mod_name else "Mod"
        self.output_path = output_path
        self.logical_prefix = logical_prefix

    def _get_logical_dir(self):
        if not self.output_path:
            return ""
        dirname = os.path.dirname(self.output_path)
        if not dirname or dirname == ".":
            return ""
        # Convert path/to/dir to path.to.dir
        return dirname.replace("/", ".").replace("\\", ".")

    def _sanitize_verilog(self, content: str) -> str:
        # 1. Replace // comments with (* ... *)
        def repl_line_comment(match):
            return "(* " + match.group(1).strip() + " *)"
        
        content = re.sub(r'//(.*)', repl_line_comment, content)
        
        # 2. Replace /* ... */ with (* ... *)
        content = content.replace("/*", "(*").replace("*/", "*)")
        
        # 3. Replace @(*) with @*  to avoid Coq comment conflict and ensure notation match
        content = content.replace("@(*)", "@* ")
        
        # 4. Wrap unsupported directives like `include, `timescale in (* ... *)
        def repl_directive(match):
            return "(* " + match.group(0).strip() + " *)"
            
        content = re.sub(r'^\s*`include.*', repl_directive, content, flags=re.MULTILINE)
        content = re.sub(r'^\s*`timescale.*', repl_directive, content, flags=re.MULTILINE)
        
        return content

    def generate(self):
        lines = []
        lines.append("Require Import Coq.ZArith.BinInt.")
        lines.append("Require Import Coq.Lists.List.")
        lines.append("Require Import Pfv.Lib.Lib. Import SZNotations. Import HMapNotations.")
        lines.append("Require Import Pfv.Lang.Lang.")
        lines.append("Require Import common.Common.")
        
        # Add imports for sub-modules
        unique_mods = sorted(list(set(i[0] for i in self.data.instances)))
        logical_dir = self._get_logical_dir()
        
        if unique_mods:
            lines.append("")
            for mod in unique_mods:
                if mod.lower() != self.mod_name.lower(): # avoid self-import
                    import_path = f"{logical_dir}.{mod}_gen" if logical_dir else f"{mod}_gen"
                    if self.logical_prefix:
                        import_path = f"{self.logical_prefix}.{import_path}"
                    lines.append(f"Require Import {import_path}.")
        
        lines.append("")
        
        lines.append(f"Module {self.cap_mod_name}.")
        
        # VId Definition (OUTSIDE Module M)
        sorted_ids = sorted(list(self.data.identifiers))
        
        lines.append("  Inductive vid : Type :=")
        if not sorted_ids:
            lines.append("  | dummy_id")
        else:
            for ident in sorted_ids:
                lines.append(f"  | {ident}")
        lines.append("  .")
        lines.append("  ")
        
        # Coercions and Instances (OUTSIDE Module M)
        lines.append("  Definition VExprIdVId := @VExprId vid.")
        lines.append("  Coercion VExprIdVId: vid >-> VExpr.")
        lines.append("  Definition VPortIdsOneVId := @VPortIdsOne vid.")
        lines.append("  Coercion VPortIdsOneVId: vid >-> VPortIds.")
        lines.append("")
        
        lines.append("  Definition vid_eq_dec: forall (v1 v2: vid), {v1 = v2} + {v1 <> v2} := ltac:(decide equality).")
        lines.append("  #[export] Instance vid_t_c_impl : vid_t_c := { vid_t := vid }.")
        lines.append("  #[export] Instance vid_ops_impl : vid_ops := { vid_eq_dec := vid_eq_dec }.")
        lines.append("")
        lines.append("")
        
        # Module M (for notations and module definition)
        lines.append("  Module M.")
        lines.append("")
        
        # Notations (INSIDE Module M)
        custom_entries = ["ce_top", "ce_expr", "ce_stmt", "ce_assign", "ce_netdeclassign", 
                          "ce_vardeclassign", "ce_paramassign", "ce_portconnid", "ce_ports"]
        
        for ident in sorted_ids:
             for ce in custom_entries:
                 if ce == "ce_portconnid":
                     lines.append(f"    Notation \"'.{ident}'\" := {ident} (in custom {ce}).")
                 else:
                     lines.append(f"    Notation \"'{ident}'\" := {ident} (in custom {ce}).")
        
        lines.append("")
        
        # Module Body (INSIDE Module M)
        lines.append(f"    Definition m: @VModuleDecl vid := #[")
        lines.append(self.raw_verilog)
        lines.append("    ].")
        lines.append("  End M.")
        lines.append("")
        # Records
        self._generate_records(lines)
        
        # Helpers
        self._generate_helpers(lines)
        
        lines.append(f"End {self.cap_mod_name}.")
        
        return "\n".join(lines)

    def _generate_records(self, lines):
        # Inputs Record
        lines.append("  Record Inputs := {")
        inputs_list = [inp[0] for inp in self.data.inputs]
        if inputs_list:
            for i, name in enumerate(inputs_list):
                sep = ";" if i < len(inputs_list) - 1 else ""
                lines.append(f"    {name}_v: SZ{sep}")
        lines.append("  }.")
        lines.append("")

        # Outputs Record
        lines.append("  Record Outputs := {")
        outputs_list = [out[0] for out in self.data.outputs]
        if outputs_list:
            for i, name in enumerate(outputs_list):
                sep = ";" if i < len(outputs_list) - 1 else ""
                lines.append(f"    {name}_v: SZ{sep}")
        lines.append("  }.")
        lines.append("")
        
        # Flops Record
        lines.append("  Record Flops := {")
        
        flop_fields = []
        
        sorted_flops = sorted(list(self.data.flops))
        inst_names = [i[1] for i in self.data.instances]
        
        for flop in sorted_flops:
            if flop not in inst_names:
                flop_fields.append(f"{flop}_v: SZ")
        
        for mod_type, inst_name in self.data.instances:
            mod_type_cap = mod_type.capitalize()
            flop_fields.append(f"{inst_name}_v: {mod_type_cap}.Flops")
            
        if flop_fields:
            for i, field in enumerate(flop_fields):
                sep = ";" if i < len(flop_fields) - 1 else ""
                lines.append(f"    {field}{sep}")
                
        lines.append("  }.")
        lines.append("")

        # Updates Record
        lines.append("  Record Updates := {")
        
        update_fields = []
        # Re-calculate reg_flops to ensure consistency
        reg_flops = [f for f in sorted_flops if f not in inst_names]
        
        for flop in reg_flops:
            update_fields.append(f"{flop}_update: State")
            
        for mod_type, inst_name in self.data.instances:
            mod_type_cap = mod_type.capitalize()
            update_fields.append(f"{inst_name}_update: {mod_type_cap}.Updates")
            
        if update_fields:
            for i, field in enumerate(update_fields):
                sep = ";" if i < len(update_fields) - 1 else ""
                lines.append(f"    {field}{sep}")
                
        lines.append("  }.")
        lines.append("")

    def _generate_helpers(self, lines):
        lines.append("  Section Helpers.")
        lines.append("    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.")
        lines.append("    Import ListNotations.")
        lines.append("    Import HMapNotations.")
        lines.append("")
        
        # Inputs Structured
        lines.append("    #[export] Instance inputs_structured: StructuredState Inputs := {")
        lines.append("      from_state :=")
        lines.append("        fun (state : State) =>")
        
        inputs_list = [inp[0] for inp in self.data.inputs]
        if not inputs_list:
            lines.append("          Sret Build_Inputs;")
        else:
            for name in inputs_list:
                lines.append(f"          {name}_v <- sfind {name} state;")
            lines.append("          Sret {|")
            for name in inputs_list:
                lines.append(f"            {name}_v := hbits {name}_v;")
            lines.append("          |};")
            
        lines.append("      to_state := fun i =>")
        lines.append("        match i with")
        if not inputs_list:
             lines.append("        | _ => HMapStr []")
        else:
            fields_pat = (";\n" + "             ").join([f"{n}_v := {n}_v" for n in inputs_list])
            lines.append(f"        | {{| {fields_pat} |}} =>")
            pairs = (";\n" + "                   ").join([f"({n}, HMapBits {n}_v)" for n in inputs_list])
            lines.append(f"          HMapStr [{pairs}]")
        lines.append("        end")
        lines.append("    }.")
        lines.append("")
        
        # Outputs to State
        lines.append("    Definition output_to_state (o: Outputs): State :=")
        outputs_list = [out[0] for out in self.data.outputs]
        if not outputs_list:
            lines.append("      HMapStr [].")
        else:
            pairs = (";\n" + "               ").join([f"({n}, HMapBits o.({n}_v))" for n in outputs_list])
            lines.append(f"      HMapStr [{pairs}].")
        lines.append("")
        
        # Updates to State
        lines.append("    Definition update_to_state (u: Updates): State :=")
        
        sorted_flops = sorted(list(self.data.flops))
        inst_names = [i[1] for i in self.data.instances]
        reg_flops = [f for f in sorted_flops if f not in inst_names]
        
        if not (reg_flops or self.data.instances):
            lines.append("      HMapStr [].")
        else:
            pairs = []
            for n in reg_flops:
                pairs.append(f"({n}, u.({n}_update))")
            for mod_type, n in self.data.instances:
                mod_type_cap = mod_type.capitalize()
                pairs.append(f"({n}, {mod_type_cap}.update_to_state u.({n}_update))")
                
            pairs_str = (";\n" + "               ").join(pairs)
            lines.append(f"      HMapStr [{pairs_str}].")
        lines.append("")

        # Flops Structured
        lines.append("    #[export] Instance flops_structured: StructuredState Flops := {")
        lines.append("      from_state :=")
        lines.append("        fun (state : State) =>")
        
        sorted_flops = sorted(list(self.data.flops))
        inst_names = [i[1] for i in self.data.instances]
        reg_flops = [f for f in sorted_flops if f not in inst_names]
        
        all_flop_fields = reg_flops + inst_names
        
        if not all_flop_fields:
            lines.append("          Sret Build_Flops;")
        else:
            for name in reg_flops:
                lines.append(f"          {name}_v <- sfind {name} state;")
            for mod_type, inst_name in self.data.instances:
                mod_type_cap = mod_type.capitalize()
                lines.append(f"          {inst_name}_s <- sfind {inst_name} state;")
                lines.append(f"          {inst_name}_v <- from_state (A := {mod_type_cap}.Flops) {inst_name}_s;")
                
            lines.append("          Sret {|")
            for i, name in enumerate(reg_flops):
                sep = ";" if i < len(all_flop_fields) - 1 else ""
                lines.append(f"            {name}_v := hbits {name}_v{sep}")
            for i, (_, inst_name) in enumerate(self.data.instances):
                idx = len(reg_flops) + i
                sep = ";" if idx < len(all_flop_fields) - 1 else ""
                lines.append(f"            {inst_name}_v := {inst_name}_v{sep}")
            lines.append("          |};")
            
        lines.append("      to_state := fun f =>")
        lines.append("        match f with")
        if not all_flop_fields:
            lines.append("        | _ => HMapStr []")
        else:
            pats = []
            for n in reg_flops: pats.append(f"{n}_v := {n}_v")
            for _, n in self.data.instances: pats.append(f"{n}_v := {n}_v")
            lines.append("        | {| " + (";\n             ").join(pats) + " |} =>")
            
            pairs = []
            for n in reg_flops: pairs.append(f"({n}, HMapBits {n}_v)")
            for _, n in self.data.instances: pairs.append(f"({n}, to_state {n}_v)")
            
            lines.append("          HMapStr [" + (";\n                   ").join(pairs) + "]")
        lines.append("        end")
        lines.append("    }.")
        lines.append("")
        
        # ETrs
        lines.append("    Definition etrs (eid: vid): trsOk MTrs :=")
        lines.append("    match eid with")
        for mod_type, inst_name in self.data.instances:
            mod_type_cap = mod_type.capitalize()
            lines.append(f"    | {inst_name} => Sret ({mod_type_cap}.mtrs : MTrs)")
        lines.append("    | _ => Fail TrsUndeclared")
        lines.append("    end.")
        lines.append("")
        lines.append("  End Helpers.")
        lines.append("")

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description='Convert Verilog to Rocq')
    parser.path = argparse.ArgumentParser(description='Convert Verilog to Rocq')
    parser.add_argument('input_file', help='Input Verilog file')
    parser.add_argument('output_file', nargs='?', help='Output Rocq file')
    parser.add_argument('--prefix', default='', help='Logical prefix for imports')
    
    args = parser.parse_args()
    
    input_file = os.path.abspath(args.input_file)
    
    if not os.path.exists(input_file):
        print(f"Error: File not found: {input_file}")
        sys.exit(1)
        
    # Read original content to embed in Rocq
    with open(input_file, 'r') as f:
        content = f.read()

    try:
        # Parse using pyverilog
        ast, directives = parse([input_file])
    except Exception as e:
        print(f"Error parsing Verilog file: {e}")
        sys.exit(1)
        
    collector = VerilogDataCollector()
    collector.visit(ast)
    
    generator = RocqGenerator(collector, content, args.output_file, args.prefix)
    rocq_code = generator.generate()
    
    if args.output_file:
        output_file = args.output_file
        output_dir = os.path.dirname(output_file)
        if output_dir and not os.path.exists(output_dir):
            os.makedirs(output_dir)
        with open(output_file, 'w') as f:
            f.write(rocq_code)
        print(f"Generated {output_file}")
    else:
        print(rocq_code)
