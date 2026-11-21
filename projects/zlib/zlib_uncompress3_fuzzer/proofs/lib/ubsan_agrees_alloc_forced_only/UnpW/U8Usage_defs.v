(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress3_fuzzer_ubsan.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec2 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymExec2Sound OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymRun OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDrive OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDriveX OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8MainEntry OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SymDriveH4 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8LibStdioCall OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U8OpenFail_defs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U8MainEntryN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_ssA0 : sym_state := SS 0x14904 sr_mainN [] kn_mainN 40.
Definition u_scrA : scripts := SCR [true] [] [].       (* [comment removed for export] *)
Definition u_rA {RCa1 : RunCtx}  := Eval vm_compute in run u_scrA u_ssA0.
Definition u_srA {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rA)).
Definition u_knA {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rA kn_mainN.
(* [comment removed for export] *)
Definition u_logM1 : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 9071406455288693)].
Definition u_knB0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in fst (fst (carry u_logM1 u_knA [])).
Definition u_srB0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j u_srA KEPT_MC 40.

(* [comment removed for export] *)
Definition u_ssB0 {RCa1 : RunCtx}  : sym_state := SS 0x1c5c4 u_srB0 [] u_knB0 72.
Definition u_rB {RCa1 : RunCtx}  := Eval vm_compute in run scr0 u_ssB0.
Definition u_srB {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rB)).
Definition u_knB {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rB u_knB0.
Definition u_srC0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j u_srB KEPT_MC 72.

(* [comment removed for export] *)
Definition u_ssC0 {RCa1 : RunCtx}  : sym_state := SS 0x1c5c4 u_srC0 [] u_knB 104.
Definition u_rC {RCa1 : RunCtx}  := Eval vm_compute in run scr0 u_ssC0.
Definition u_srC {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rC)).
Definition u_knC {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rC u_knB.
Definition LX : expr := EVar 114.
Definition u_knD0 {RCa1 : RunCtx}  : list kentry := KRange LX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI u_knC.
Definition u_srD0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j u_srC KEPT_CS 104.

(* [comment removed for export] *)
Definition u_ssD0 {RCa1 : RunCtx}  : sym_state := SS 0x1d314 u_srD0 [] u_knD0 136.
Definition u_scrD : scripts := SCR [false] [ELit 0] [].
Definition u_rD {RCa1 : RunCtx}  := Eval vm_compute in run u_scrD u_ssD0.
Definition u_srD {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rD)).
Definition u_knD {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rD u_knD0.
Definition u_srE0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j u_srD KEPT_MC 136.

(* [comment removed for export] *)
Definition u_ssE0 {RCa1 : RunCtx}  : sym_state := SS 0x1c5c4 u_srE0 [] u_knD 168.
Definition u_scrE : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition u_rE {RCa1 : RunCtx}  := Eval vm_compute in run u_scrE u_ssE0.
Definition u_srE {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rE)).
Definition u_knE {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rE u_knD.
Definition u_knF0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knE.
Definition u_srF0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j u_srE KEPT_MC 168.

(* [comment removed for export] *)
Definition u_ssF0 {RCa1 : RunCtx}  : sym_state := SS 0x1c5c4 u_srF0 [] u_knF0 200.
Definition u_scrF : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition u_rF {RCa1 : RunCtx}  := Eval vm_compute in run u_scrF u_ssF0.
Definition u_srF {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rF)).
Definition u_knF {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rF u_knF0.
Definition u_knG0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_cut 0 (-553) BUF_HI IHI u_knF.
Definition u_srG0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j u_srF KEPT_MC 200.
(* [comment removed for export] *)
Definition u_ssG0 {RCa1 : RunCtx}  : sym_state := SS 0x1c5c4 u_srG0 [] u_knG0 232.
Definition u_rG {RCa1 : RunCtx}  := Eval vm_compute in run scr0 u_ssG0.
Definition u_srG {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rG)).
Definition u_knG {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rG u_knG0.
Definition u_scG {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in sc_of 232 u_srG u_knG.
Definition u_srH0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr u_scG.
Definition u_knH0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn u_scG.
(* [comment removed for export] *)
Definition u_ssH0 {RCa1 : RunCtx}  : sym_state := SS 0x1cc74 u_srH0 [] u_knH0 264.
Definition u_rH {RCa1 : RunCtx}  := Eval vm_compute in run scr0 u_ssH0.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition u_scrF3 : scripts := SCR [false] [] [].   (* [comment removed for export] *)
Definition u_rF3 {RCa1 : RunCtx}  := Eval vm_compute in run u_scrF3 u_ssF0.
Definition u_srF3 {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rF3)).
Definition u_knF3 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rF3 u_knF0.
Definition u_scF3 {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in sc_of 200 u_srF3 u_knF3.
Definition u_srG30 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr u_scF3.
Definition u_knG30 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn u_scF3.
(* [comment removed for export] *)
Definition u_ssG30 {RCa1 : RunCtx}  : sym_state := SS (sc_ret u_scF3) u_srG30 [] u_knG30 232.
Definition u_rG3 {RCa1 : RunCtx}  := Eval vm_compute in run scr0 u_ssG30.
Definition u_srG3 {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rG3)).
Definition u_knG3 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rG3 u_knG30.
Definition u_scG3 {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in sc_of 232 u_srG3 u_knG3.
Definition u_srH30 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr u_scG3.
Definition u_knH30 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn u_scG3.
(* [comment removed for export] *)
Definition u_ssH30 {RCa1 : RunCtx}  : sym_state := SS 0x1cc74 u_srH30 [] u_knH30 264.
Definition u_rH3 {RCa1 : RunCtx}  := Eval vm_compute in run scr0 u_ssH30.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u_scrE4 : scripts := SCR [true; false] [] [].  (* [comment removed for export] *)
Definition u_rE4 {RCa1 : RunCtx}  := Eval vm_compute in run u_scrE4 u_ssE0.
Definition u_srE4 {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rE4)).
Definition u_knE4 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rE4 u_knD.
Definition u_scE4 {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in sc_of 168 u_srE4 u_knE4.
Definition u_srF40 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr u_scE4.
Definition u_knF40 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn u_scE4.
(* [comment removed for export] *)
Definition u_ssF40 {RCa1 : RunCtx}  : sym_state := SS (sc_ret u_scE4) u_srF40 [] u_knF40 200.
Definition u_rF4 {RCa1 : RunCtx}  := Eval vm_compute in run scr0 u_ssF40.
Definition u_srF4 {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rF4)).
Definition u_knF4 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rF4 u_knF40.
(* [comment removed for export] *)
Definition u_logSUF : list sentry := [SE (SA (EVar 0) (-560)) 7 (ELit 2907475163367712)].
Definition u_knG40 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in fst (fst (carry u_logSUF u_knF4 [])).
Definition u_srG40 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j u_srF4 KEPT_MC 200.
(* [comment removed for export] *)
Definition u_ssG40 {RCa1 : RunCtx}  : sym_state := SS 0x1c5c4 u_srG40 [] u_knG40 232.
Definition u_rG4 {RCa1 : RunCtx}  := Eval vm_compute in run scr0 u_ssG40.
Definition u_srG4 {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst u_rG4)).
Definition u_knG4 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after u_rG4 u_knG40.
Definition u_scG4 {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in sc_of 232 u_srG4 u_knG4.
Definition u_srH40 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr u_scG4.
Definition u_knH40 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn u_scG4.
(* [comment removed for export] *)
Definition u_ssH40 {RCa1 : RunCtx}  : sym_state := SS 0x1cc74 u_srH40 [] u_knH40 264.
Definition u_rH4 {RCa1 : RunCtx}  := Eval vm_compute in run scr0 u_ssH40.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_itinerary {RCa1 : RunCtx}  :
  (s_pc (fst (fst u_rA)), snd (fst u_rA)) = (0x2150c%Z, [SCBr true BC_NE (EVar 18) (ELit 2)])
  /\ (s_pc (fst (fst u_rB)), snd (fst u_rB)) = (0x2150c%Z, [])
  /\ (s_pc (fst (fst u_rC)), snd (fst u_rC)) = (0x21a08%Z, [])
  /\ (s_pc (fst (fst u_rD)), snd (fst u_rD))
     = (0x2150c%Z, [SCBr false BC_LT (EAluw ALU_ADD LX (ELit 0)) LX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 1) LX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst u_rE)), snd (fst u_rE))
     = (0x2150c%Z, [SCBr true BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst u_rF)), snd (fst u_rF))
     = (0x2150c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ (s_pc (fst (fst u_rG)), snd (fst u_rG)) = (0x1c914%Z, [])
  /\ stdio_call 232 u_srG u_knG = Some u_scG
  /\ (sc_ret u_scG, sc_f u_scG, sc_fd u_scG) = (0x1cc74%Z, 0x23fc8%Z, 2%Z)
  /\ (sc_wb u_scG, sc_wp u_scG, sc_l u_scG)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-546)), ELit 0)
  /\ (s_pc (fst (fst u_rH)), snd (fst u_rH)) = (0x1a444%Z, [])
  /\ (s_pc (fst (fst u_rF3)), snd (fst u_rF3))
     = (0x1c914%Z, [SCBr false BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) LX) (ELit 73)) (ELit 7)])
  /\ stdio_call 200 u_srF3 u_knF3 = Some u_scF3
  /\ (sc_ret u_scF3, sc_f u_scF3, sc_fd u_scF3) = (0x1ce44%Z, 0x23fc8%Z, 2%Z)
  /\ (sc_wb u_scF3, sc_wp u_scF3, sc_s u_scF3, sc_l u_scF3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) LX) (ELit (-553)), ELit 0x10360, ELit 7)
  /\ (s_pc (fst (fst u_rG3)), snd (fst u_rG3)) = (0x1c914%Z, [])
  /\ stdio_call 232 u_srG3 u_knG3 = Some u_scG3
  /\ (sc_ret u_scG3, sc_f u_scG3, sc_fd u_scG3) = (0x1cc74%Z, 0x23fc8%Z, 2%Z)
  /\ (sc_wb u_scG3, sc_wp u_scG3, sc_l u_scG3)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-560)), ELit 0)
  /\ (s_pc (fst (fst u_rH3)), snd (fst u_rH3)) = (0x1a444%Z, [])
  /\ (s_pc (fst (fst u_rE4)), snd (fst u_rE4))
     = (0x1c914%Z, [SCBr false BC_GEU (ELit 73) LX;
                    SCBr true BC_GE (EExt true 0 4 LX) (EAluw ALU_ADD (EAluw ALU_ADD LX (ELit 0)) (ELit 0))])
  /\ stdio_call 168 u_srE4 u_knE4 = Some u_scE4
  /\ (sc_ret u_scE4, sc_f u_scE4, sc_fd u_scE4) = (0x1d864%Z, 0x23fc8%Z, 2%Z)
  /\ (sc_wb u_scE4, sc_wp u_scE4, sc_s u_scE4, sc_l u_scE4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), EVar 1, LX)
  /\ (s_pc (fst (fst u_rF4)), snd (fst u_rF4)) = (0x2150c%Z, [])
  /\ (s_pc (fst (fst u_rG4)), snd (fst u_rG4)) = (0x1c914%Z, [])
  /\ stdio_call 232 u_srG4 u_knG4 = Some u_scG4
  /\ (sc_ret u_scG4, sc_f u_scG4, sc_fd u_scG4) = (0x1cc74%Z, 0x23fc8%Z, 2%Z)
  /\ (sc_wb u_scG4, sc_wp u_scG4, sc_l u_scG4)
     = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-553)), ELit 0)
  /\ (s_pc (fst (fst u_rH4)), snd (fst u_rH4)) = (0x1a444%Z, []).
Proof. (* [comment removed for export] *)
  repeat apply conj; lazymatch goal with |- @eq ?T ?x ?y => vm_cast_no_check (@eq_refl T y) end.
Qed.
