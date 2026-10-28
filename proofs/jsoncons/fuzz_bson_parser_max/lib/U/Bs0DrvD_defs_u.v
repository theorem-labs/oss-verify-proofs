(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0MainEntry_u Bs0LibStdioCall_u.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface DrvKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0Drv_defs_u Bs0DrvG_defs_u Bs0DrvC_defs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS_T : list Z := (0x34604 :: 0x343f0 :: STOPS)%Z.
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_T scr ss [].
(* [comment removed for export] *)
Definition STOPS_P : list Z := [0x9adf0; 0x9ff58; 0x9cdd4; 0x9cc94; 0x3471c]%Z.
Definition STOPS_R : list Z := (0x34628 :: STOPS_P)%Z.
Definition runP (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_P scr ss [].
Definition runR (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_R scr ss [].

(* [comment removed for export] *)
Definition knTc (clo chi plo phi : Z) : list kentry := KRange (EVar 73) clo chi :: KRange (EVar 79) plo phi :: knT0.
Definition rT00 := Eval vm_compute in runT scr0 (SS 0x3454c srT0 [] (knTc 0 0 0 0) 81).
Definition rT01 := Eval vm_compute in runT scr0 (SS 0x3454c srT0 [] (knTc 0 0 1 67108857) 81).
Definition rT10 := Eval vm_compute in runT scr0 (SS 0x3454c srT0 [] (knTc 1 32767 0 0) 81).
Definition rT11 := Eval vm_compute in runT scr0 (SS 0x3454c srT0 [] (knTc 1 32767 1 67108857) 81).
Definition sr00 : list expr := Eval vm_compute in s_regs (fst (fst rT00)).
Definition sr01 : list expr := Eval vm_compute in s_regs (fst (fst rT01)).
Definition sr10 : list expr := Eval vm_compute in s_regs (fst (fst rT10)).
Definition sr11 : list expr := Eval vm_compute in s_regs (fst (fst rT11)).
(* [comment removed for export] *)
Definition calls_x : expr := Eval vm_compute in nth 21 sr11 (ELit 0).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_case_entry (K : kentry) : bool :=
  existsb (kentry_eqb K) [KRange (EVar 73) 0 0; KRange (EVar 73) 1 32767; KRange (EVar 79) 0 0; KRange (EVar 79) 1 67108857].
Definition uncase (kn : list kentry) : list kentry := List.filter (fun K => negb (is_case_entry K)) kn.
Definition knTe : list kentry := Eval vm_compute in uncase (kn_after rT11 (knTc 1 32767 1 67108857)).

(* [comment removed for export] *)
Definition knTk : list kentry := Eval vm_compute in keep_alloc (-208) [(48%nat, 65536%Z)] [] knTe.

(* [comment removed for export] *)
Definition srTm0 : list expr := Eval vm_compute in sr_upd sr11 (ridx 21) (EVar 81).
Definition srU0 : list expr := Eval vm_compute in sr_after_call_j srTm0 (map ridx c_kept) 82.
(* [comment removed for export] *)
Definition knU0 : list kentry := Eval vm_compute in kn_blk2 92 ++ knTk.
Definition rU := Eval vm_compute in runT scr0 (SS 0x345b0 srU0 [] knU0 114).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
(* [comment removed for export] *)
Definition srV0 : list expr := Eval vm_compute in sr_after_call_j srU (map ridx callee_kept) 114.
Definition knV0 : list kentry := Eval vm_compute in keep_rd knU0.
Definition rV := Eval vm_compute in runT scr0 (SS 0x345c4 srV0 [] knV0 146).
Definition srV : list expr := Eval vm_compute in s_regs (fst (fst rV)).

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
(* [comment removed for export] *)
Definition srLH : list expr :=
  [ELit 0; EVar 85; spx (-208); ELit 67584; ELit 827328; EVar 86; EVar 87; EVar 88;
   EVar 79; EVar 82; EVar 89; EVar 90; EVar 91; EVar 92; EVar 93; EVar 94; EVar 95; EVar 96;
   EVar 83; EVar 84; ELit 820560; EVar 81; ELit 0; ELit 18446744073709551614; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 97; EVar 98; EVar 99; EVar 100].
(* [comment removed for export] *)
Definition knLH1 : list kentry := Eval vm_compute in keep_rd knTk.
(* [comment removed for export] *)
Definition shared_pos : list nat := [2; 3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition relay_ok_b (sr : list expr) : bool :=
  forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLH (ELit 0)) && expr_vars_lt 82 (nth i sr (ELit 0))) shared_pos.
(* [comment removed for export] *)
Definition IMG_LIB : list (Z * Z) := [(0x10000, 0xc8570); (0xc9738, 0xc9ee8); (0xc9ef0, 0xc9f1c); (0xc9f20, 0xea008); (0xea228, 0xea3c8); (0xea770, 0xeb000)]%Z.
Definition keep_lib (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 65536 bls vbnd [3%nat; 4%nat] IMG_LIB IMG_RW kn.

(* [comment removed for export] *)
Definition rLB1 := Eval vm_compute in runT scr0 (SS 0x34604 srLH [] knLH1 102).
Definition srLB : list expr := Eval vm_compute in s_regs (fst (fst rLB1)).
Definition knLc1 : list kentry := Eval vm_compute in kn_after rLB1 knLH1.
(* [comment removed for export] *)
Definition srLr0 : list expr := Eval vm_compute in sr_upd (sr_after_call_j srLB (map ridx c_kept) 102) (ridx 10) (ELit 0).
Definition knLr1 : list kentry := Eval vm_compute in keep_lib (-208) [(48%nat, 65536%Z)] [] knLc1.
(* [comment removed for export] *)
Definition rLc1 := Eval vm_compute in runT scr0 (SS 0x34618 srLr0 [] knLr1 134).
Definition srP0 : list expr := Eval vm_compute in s_regs (fst (fst rLc1)).
Definition knLp1 : list kentry := Eval vm_compute in kn_after rLc1 knLr1.
(* [comment removed for export] *)
Definition rP := Eval vm_compute in runP scr0 (SS 0x346d4 srP0 [] knLp1 134).
Definition srP : list expr := Eval vm_compute in s_regs (fst (fst rP)).
Definition knP : list kentry := Eval vm_compute in kn_after rP knLp1.
(* [comment removed for export] *)
Definition srQ0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) (ELit 18446744073709551591).
Definition rQ := Eval vm_compute in runP scr0 (SS 0xa0980 srQ0 [] knP 134).
Definition srQ : list expr := Eval vm_compute in s_regs (fst (fst rQ)).
Definition knQ : list kentry := Eval vm_compute in kn_after rQ knP.
Definition scP : stdio_res := Eval vm_compute in the_sc (stdio_call 134 srQ knQ).
Definition srR0 : list expr := Eval vm_compute in sc_sr scP.
Definition knR0 : list kentry := Eval vm_compute in sc_kn scP.
Definition rR := Eval vm_compute in runR scr0 (SS (sc_ret scP) srR0 [] knR0 166).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition knR : list kentry := Eval vm_compute in kn_after rR knR0.

(* [comment removed for export] *)
Definition IMG_PF : list (Z * Z) := [(0x10000, 0xb83f0); (0xb83f4, 0xb8418); (0xb8420, 0xc8570); (0xc9ef0, 0xc9f1c); (0xc9f20, 0xea3c8); (0xea770, 0xea7b0); (0xeabb0, 0xeb000)]%Z.
Definition keep_pf (kn : list kentry) : list kentry := kn_keep 0 (-208) 1056 [(48%nat, 65536%Z)] [] [3%nat; 4%nat] IMG_PF IMG_RW kn.
Definition wposK (e : expr) : kentry := KWord (SA (ELit 0) 0xb8418) 8 e.
Definition flagsK : kentry := KWord (SA (ELit 0) 0xb83f0) 4 (ELit 5).
(* [comment removed for export] *)
Definition knR2 : list kentry := Eval vm_compute in keep_pf (keep_lib (-208) [(48%nat, 65536%Z)] [] knR).
Definition knLH2 : list kentry := wposK (EVar 101) :: KRange (EVar 101) 0xea7b0 0xea7b6 :: flagsK :: knR2.

(* [comment removed for export] *)
Definition rLB2 := Eval vm_compute in runT scr0 (SS 0x34604 srLH [] knLH2 102).
Definition knLc2 : list kentry := Eval vm_compute in kn_after rLB2 knLH2.
Definition knLr2 : list kentry := Eval vm_compute in keep_lib (-208) [(48%nat, 65536%Z)] [] knLc2.
Definition rLc2 := Eval vm_compute in runT scr0 (SS 0x34618 srLr0 [] knLr2 134).
Definition knLp2 : list kentry := Eval vm_compute in kn_after rLc2 knLr2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition srS0 : list expr := sr_upd srLH (ridx 19) (ELit 0).
Definition rS_tk := Eval vm_compute in runT (SCR [true] [] []) (SS 0x34628 srS0 [] knLH2 102).
Definition rS_ft := Eval vm_compute in runT (SCR [false] [] []) (SS 0x34628 srS0 [] knLH2 102).
Definition srS_tk : list expr := Eval vm_compute in s_regs (fst (fst rS_tk)).
Definition srS_ft : list expr := Eval vm_compute in s_regs (fst (fst rS_ft)).
Definition dec_x : expr := EAluw ALU_ADD (EVar 81) (ELit (-1)).

(* [comment removed for export] *)
Definition srX0 : list expr := Eval vm_compute in sr_after_call_j srS_ft (map ridx c_kept) 102.
Definition knX0 : list kentry := Eval vm_compute in keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2.
Definition rX := Eval vm_compute in runT scr0 (SS 0x34644 srX0 [] knX0 134).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).
(* [comment removed for export] *)
Definition srY0 : list expr :=
  Eval vm_compute in sr_upd (sr_upd (sr_upd (sr_upd srX (ridx 8) (ELit 0)) (ridx 10) (ELit 0)) (ridx 1) (EVar 134)) (ridx 11) (EVar 135).
Definition rY := Eval vm_compute in runT scr0 (SS 0x34470 srY0 [] knX0 136).
Definition srY : list expr := Eval vm_compute in s_regs (fst (fst rY)).
(* [comment removed for export] *)
Definition srZ0 : list expr := Eval vm_compute in sr_after_call_j srY (map ridx c_kept) 136.
Definition knZ0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knX0.
Definition rZ := Eval vm_compute in runT scr0 (SS 0x34478 srZ0 [] knZ0 168).
Definition srZ : list expr := Eval vm_compute in s_regs (fst (fst rZ)).
Definition knZ : list kentry := Eval vm_compute in kn_after rZ knZ0.

(* [comment removed for export] *)
Definition flag1 : list sentry := [SE (SA (ELit 0) 0xc8554) 1 (ELit 1)].
Definition flag0 : list sentry := [SE (SA (ELit 0) 0xc8554) 1 (ELit 0)].

(* [comment removed for export] *)
Lemma tgt_itinerary_ok :
  (s_pc (fst (fst rT00)), snd (fst rT00)) = (0x34604%Z, []) /\ (s_pc (fst (fst rT10)), snd (fst rT10)) = (0x34604%Z, [])
  /\ (s_pc (fst (fst rT01)), snd (fst rT01)) = (0x9cdd4%Z, []) /\ (s_pc (fst (fst rT11)), snd (fst rT11)) = (0x9cdd4%Z, [])
  /\ ksubl_b (kn_after rT00 (knTc 0 0 0 0)) knTe = true /\ ksubl_b (kn_after rT01 (knTc 0 0 1 67108857)) knTe = true
  /\ ksubl_b (kn_after rT10 (knTc 1 32767 0 0)) knTe = true /\ ksubl_b (kn_after rT11 (knTc 1 32767 1 67108857)) knTe = true
  /\ sr_upd sr01 (ridx 21) (EVar 81) = srTm0
  /\ ksubl_b knTe knLH1 = true /\ ksubl_b knV0 knLH1 = true /\ kn_after rV knV0 = knV0 /\ kn_after rU knU0 = knU0
  /\ relay_ok_b (sr_upd sr00 (ridx 21) (EVar 81)) = true /\ relay_ok_b (sr_upd sr10 (ridx 21) (EVar 81)) = true
  /\ relay_ok_b srV = true /\ relay_ok_b srR = true /\ relay_ok_b (sr_upd srS_tk (ridx 21) (EVar 81)) = true
  /\ kn_vars_lt 82 knLH1 = true /\ sr_vars_lt 82 srTm0 = true
  /\ (s_pc (fst (fst rU)), snd (fst rU), s_log (fst (fst rU))) = (0xab480%Z, [], [])
  /\ (s_pc (fst (fst rV)), snd (fst rV), s_log (fst (fst rV))) = (0x34604%Z, [], [])
  /\ (s_pc (fst (fst rLB1)), snd (fst rLB1), s_log (fst (fst rLB1))) = (0x3471c%Z, [], flag1)
  /\ (s_pc (fst (fst rLB2)), snd (fst rLB2), s_log (fst (fst rLB2)), s_regs (fst (fst rLB2))) = (0x3471c%Z, [], flag1, srLB)
  /\ (s_pc (fst (fst rLc1)), snd (fst rLc1), s_log (fst (fst rLc1))) = (0x346d4%Z, [], flag0)
  /\ (s_pc (fst (fst rLc2)), snd (fst rLc2), s_log (fst (fst rLc2)), s_regs (fst (fst rLc2))) = (0x346d4%Z, [], flag0, srP0)
  /\ kn_after rLc1 knLr1 = knLp1 /\ kn_after rLc2 knLr2 = knLp2 /\ kn_after rLB1 knLH1 = knLc1 /\ kn_after rLB2 knLH2 = knLc2
  /\ knLr2 = knLc2 /\ ksubl_b knLp2 knLH2 = true /\ ksubl_b knLH2 knLp2 = true /\ ksubl_b knR (wposK (ELit 0xea7b0) :: flagsK :: knR2) = true
  /\ keep_pf knLH2 = KRange (EVar 101) 0xea7b0 0xea7b6 :: knR2
  /\ kn_vars_lt 102 knLH2 = true /\ kn_vars_lt 81 knR2 = true
  /\ relay_ok_b (sr_after_call_j srP0 (map ridx callee_saved) 134) = true /\ ksubl_b knLH2 knX0 = true
  /\ keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2 = knX0
  /\ (s_pc (fst (fst rP)), snd (fst rP)) = (0xa097c%Z, [])
  /\ (s_pc (fst (fst rQ)), snd (fst rQ)) = (0x9ff58%Z, [])
  /\ stdio_call 134 srQ knQ = Some scP /\ (sc_ret scP, sc_f scP, sc_fd scP, sc_wb scP, sc_wp scP, sc_s scP, sc_l scP)
                                           = (0xa09a0%Z, 0xb83f0%Z, 1%Z, ELit 0xea7b0, ELit 0xea7b1, ELit 0x10c9d, ELit 1)
  /\ (s_pc (fst (fst rR)), snd (fst rR)) = (0x34628%Z, [])
  /\ (s_pc (fst (fst rS_tk)), snd (fst rS_tk), s_log (fst (fst rS_tk))) = (0x34604%Z, [SCBr true BC_NE dec_x (ELit 0)], [])
  /\ (s_pc (fst (fst rS_ft)), snd (fst rS_ft), s_log (fst (fst rS_ft))) = (0x9cc94%Z, [SCBr false BC_NE dec_x (ELit 0)], [])
  /\ (s_pc (fst (fst rX)), snd (fst rX), s_log (fst (fst rX))) = (0x343f0%Z, [], []) /\ nth 10 (s_regs (fst (fst rX))) (ELit 1) = ELit 0
  /\ (s_pc (fst (fst rY)), snd (fst rY), s_log (fst (fst rY))) = (0x9cc94%Z, [], [])
  /\ (s_pc (fst (fst rZ)), snd (fst rZ), s_log (fst (fst rZ))) = (0x9adf0%Z, [], []).
Proof. vm_compute. repeat split; reflexivity. Qed.

End FPX_1.
