(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printers for RTL code *)

open Format
open Camlcoq
open Datatypes
open Maps
open AST
open Integers
open RTL
open PrintOp

let name_of_chunk = function
  | Mint8signed -> "int8signed"
  | Mint8unsigned -> "int8unsigned"
  | Mint16signed -> "int16signed"
  | Mint16unsigned -> "int16unsigned"
  | Mint32 -> "int32"
  | Mfloat32 -> "float32"
  | Mfloat64 -> "float64"

let reg pp r =
  fprintf pp "x%ld" (camlint_of_positive r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_succ pp s dfl =
  let s = camlint_of_positive s in
  if s <> dfl then fprintf pp "       goto %ld@ " s

let print_instruction pp (pc, i) =
  fprintf pp "%5ld: " pc;
  match i with
  | Inop s ->
      let s = camlint_of_positive s in
      if s = Int32.pred pc
      then fprintf pp "nop@ "
      else fprintf pp "goto %ld@ " s
  | Iop(op, args, res, s) ->
      fprintf pp "%a = %a@ " reg res (print_operator reg) (op, args);
      print_succ pp s (Int32.pred pc)
  | Iload(chunk, addr, args, dst, s) ->
      fprintf pp "%a = %s[%a]@ "
         reg dst (name_of_chunk chunk) (print_addressing reg) (addr, args);
      print_succ pp s (Int32.pred pc)
  | Istore(chunk, addr, args, src, s) ->
      fprintf pp "%s[%a] = %a@ "
         (name_of_chunk chunk) (print_addressing reg) (addr, args) reg src;
      print_succ pp s (Int32.pred pc)
  | Icall(sg, fn, args, res, s) ->
      fprintf pp "%a = %a(%a)@ "
        reg res ros fn regs args;
      print_succ pp s (Int32.pred pc)
  | Itailcall(sg, fn, args) ->
      fprintf pp "tailcall %a(%a)@ "
        ros fn regs args
  | Icond(cond, args, s1, s2) ->
      fprintf pp "if (%a) goto %ld else goto %ld@ "
        (print_condition reg) (cond, args)
        (camlint_of_positive s1) (camlint_of_positive s2)
  | Ijumptable(arg, tbl) ->
      let tbl = Array.of_list tbl in
      fprintf pp "@[<v 2>jumptable (%a)" reg arg;
      for i = 0 to Array.length tbl - 1 do
        fprintf pp "@ case %d: goto %ld" i (camlint_of_positive tbl.(i))
      done;
      fprintf pp "@]@ "
  | Ireturn None ->
      fprintf pp "return@ "
  | Ireturn (Some arg) ->
      fprintf pp "return %a@ " reg arg

let print_function pp f =
  fprintf pp "@[<v 2>f(%a) {@ " regs f.fn_params;
  let instrs =
    List.sort
      (fun (pc1, _) (pc2, _) -> Pervasives.compare pc2 pc1)
      (List.map
        (fun (Coq_pair(pc, i)) -> (camlint_of_positive pc, i))
        (PTree.elements f.fn_code)) in
  print_succ pp f.fn_entrypoint 
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1l);
  List.iter (print_instruction pp) instrs;
  fprintf pp "@;<0 -2>}@]@."

let print_fundef fd =
  begin match fd with
  | Internal f -> print_function std_formatter f
  | External _ -> ()
  end;
  fd


