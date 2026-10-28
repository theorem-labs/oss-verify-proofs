(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvRead_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.

Section FPX_1. Context {fx : PropExec.FPState}.

Definition STOPS_LA : list Z := 0xa7b8c :: STOPSA.
Definition runLA (scr : scripts) (ss : sym_state) := sym_exec ASEGS FUELA true STOPS_LA scr ss [].

(* [comment removed for export] *)
Definition kn_blk2A (v : nat) : list kentry := [KRange (EVar v) 4096 (2 ^ 47); KAlign (EVar v) 16].

(* [comment removed for export] *)
Definition keepalloc_G (kn : list kentry) : list kentry := keep_allocA MSO 4096 [(48%nat, 65536)] [] kn.

(* [comment removed for export] *)
Definition below_frameA (K : kentry) : bool :=
  match K with KWord (SA (EVar 0) off) _ _ => (off <? -128) | _ => false end.
Definition knLP6A : list kentry := Eval vm_compute in List.filter (fun K => negb (below_frameA K)) keepB.
Definition knLPA : list kentry := kn_blkA 48 65536 ++ knLP6A.

(* [comment removed for export] *)
Definition srLPA : list expr :=
  [ELit 0; EVar 7; EAlu ALU_ADD (EVar 0) (ELit (-128)); ELit 67584; ELit 6765824; EVar 11; EVar 12; EVar 13;
   ELit 2; EVar 48; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 2; EVar 70; ELit 3; EVar 38; ELit 6693520; EVar 48; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 34; EVar 35; EVar 36; EVar 37].

(* [comment removed for export] *)
Definition rC0L := Eval vm_compute in runLA scr0 (SS 0xa7b58 srC0 [] knC0 70).
Definition srC0L : list expr := Eval vm_compute in s_regs (fst (fst rC0L)).

(* [comment removed for export] *)
Definition knLPpA : list kentry := KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLPA.
Definition rPa := Eval vm_compute in runLA (SCR [false; false] [] []) (SS 0xa7b8c srLPA [] knLPpA 71).
Definition srPa : list expr := Eval vm_compute in s_regs (fst (fst rPa)).
Definition rPb := Eval vm_compute in runLA (SCR [false; true] [] []) (SS 0xa7b8c srLPA [] knLPpA 71).
Definition srPb : list expr := Eval vm_compute in s_regs (fst (fst rPb)).
Definition want_xA : expr := Eval vm_compute in nth 12 srPb (ELit 0).

(* [comment removed for export] *)
Definition srRDA : list expr := sr_upd (sr_upd srPa (ridx 12) (EVar 71)) (ridx 23) (EVar 29).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition srRA0 : list expr := Eval vm_compute in sr_after_call_j srRDA (map ridx c_kept) 72.
Definition knRA : list kentry := Eval vm_compute in keep_readA MSO [(48%nat, 65536)] [] knLPA.
(* [comment removed for export] *)
Definition knRe0A : list kentry := KRange (EVar 82) 1 65536 :: knRA.
Definition rRe_tk := Eval vm_compute in runLA scr0 (SS 0xa7bec srRA0 [] knRe0A 104).
Definition srRe_tk : list expr := Eval vm_compute in s_regs (fst (fst rRe_tk)).
(* [comment removed for export] *)
Definition srRm0 : list expr := Eval vm_compute in sr_after_call_j srRe_tk (map ridx c_kept) 104.
Definition knRm0 : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knRe0A.
Definition rRm := Eval vm_compute in runLA scr0 (SS 0xa7b84 srRm0 [] knRm0 136).
Definition srRm : list expr := Eval vm_compute in s_regs (fst (fst rRm)).
Definition len_xA : expr := Eval vm_compute in nth 19 srRm (ELit 0).
(* [comment removed for export] *)
Definition knRf0A : list kentry := KRange (EVar 82) 0 0 :: knRA.
Definition rRe_ft := Eval vm_compute in runLA scr0 (SS 0xa7bec srRA0 [] knRf0A 104).
Definition srRe_ft : list expr := Eval vm_compute in s_regs (fst (fst rRe_ft)).
Definition cellCA : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0xa7c00).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint expr_canon (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => (Nat.ltb v 6 || Nat.eqb v 38 || Nat.eqb v 48 || Nat.eqb v 70)%bool
  | EAlu _ a b => (expr_canon a && expr_canon b)%bool
  | EMd _ a b => (expr_canon a && expr_canon b)%bool
  | _ => false
  end.
Fixpoint relay_sr_from (i : nat) (sr : list expr) : list expr :=
  match sr with [] => [] | e :: r => (if expr_canon e then e else EVar (6 + i)) :: relay_sr_from (Datatypes.S i) r end.
Definition srGLA : list expr := Eval vm_compute in relay_sr_from 0 (sr_upd srRe_ft (ridx 10) (ELit 0)).
Definition knGbaseA : list kentry := cellCA :: knLPA.
Definition knGA (lo hi : Z) : list kentry := KRange (EVar 70) lo hi :: knGbaseA.

(* [comment removed for export] *)
Definition knLPgA : list kentry := KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLPA.
Definition rGa := Eval vm_compute in runLA (SCR [true] [] []) (SS 0xa7b8c srLPA [] knLPgA 71).
Definition srGa : list expr := Eval vm_compute in s_regs (fst (fst rGa)).
Definition cap2_xA : expr := Eval vm_compute in nth 10 srGa (ELit 0).
(* [comment removed for export] *)
Definition srGb0 : list expr := Eval vm_compute in sr_after_call_j srGa (map ridx c_kept) 71.
Definition knGb0 : list kentry := Eval vm_compute in kn_blk2A 81 ++ keepalloc_G knLPgA.
Definition rGb := Eval vm_compute in runLA scr0 (SS 0xa7bac srGb0 [] knGb0 103).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
(* [comment removed for export] *)
Definition srGc0 : list expr := Eval vm_compute in sr_after_call_j srGb (map ridx c_kept) 103.
Definition knGc0 : list kentry := Eval vm_compute in keepalloc_G knGb0.
Definition rGc := Eval vm_compute in runLA scr0 (SS 0xa7bc8 srGc0 [] knGc0 135).
Definition srGc : list expr := Eval vm_compute in s_regs (fst (fst rGc)).
(* [comment removed for export] *)
Definition srGd0 : list expr := Eval vm_compute in sr_after_call_j srGc (map ridx c_kept) 135.
Definition knGd0 : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] knGc0.
Definition rGd := Eval vm_compute in runLA scr0 (SS 0xa7bd0 srGd0 [] knGd0 167).
Definition srGd : list expr := Eval vm_compute in s_regs (fst (fst rGd)).

(* [comment removed for export] *)
Definition summG (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
Definition kdiff (a b : list kentry) := List.filter (fun K => negb (existsb (kentry_eqb K) b)) a.

End FPX_1.
