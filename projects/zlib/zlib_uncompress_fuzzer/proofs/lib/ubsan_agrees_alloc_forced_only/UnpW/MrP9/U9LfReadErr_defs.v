(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U9MainEntry. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import SymDriveH4. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import U9LibStdioCall.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP9 Require Import U9LfBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments.

Definition STOPS : list Z := [0x21450; 0x21854; 0x2194c; 0x21990; 0x14d98; 0x1bc8c; 0x1a388; 0x1c858]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run {RCa1 : RunCtx}  (scr : scripts) (ss : sym_state) := sym_exec (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0x95000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0x74250; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.


(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x14b24 srRE0 [] knLF0 39.
Definition rB {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssB0.
Definition srB {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rB knLF0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-542)) 1 (ELit 32);
   SE (SA (EVar 0) (-544)) 2 (ELit 28271);
   SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
Definition knC0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 {RCa1 : RunCtx}  : sym_state := SS 0x1c508 srC0 [] knC0 71.
Definition rC {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssC0.
Definition srC {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 {RCa1 : RunCtx}  : sym_state := SS 0x1c508 srD0 [] knC 103.
Definition rD {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssD0.
Definition srD {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 {RCa1 : RunCtx}  : list kentry := KRange PX 0 131155 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 {RCa1 : RunCtx}  : sym_state := SS 0x1d258 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE {RCa1 : RunCtx}  := Eval vm_compute in run scrE ssE0.
Definition srE {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 {RCa1 : RunCtx}  : sym_state := SS 0x1c508 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF {RCa1 : RunCtx}  := Eval vm_compute in run scrF ssF0.
Definition srF {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 {RCa1 : RunCtx}  : sym_state := SS 0x1c508 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG {RCa1 : RunCtx}  := Eval vm_compute in run scrG ssG0.
Definition srG {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 {RCa1 : RunCtx}  : sym_state := SS 0x1c508 srH0 [] knH0 231.
Definition rH {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssH0.
Definition srH {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE {RCa1 : RunCtx}  : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 {RCa1 : RunCtx}  : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 {RCa1 : RunCtx}  : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 {RCa1 : RunCtx}  : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI {RCa1 : RunCtx}  := Eval vm_compute in run scr0 ssI0.
Definition srI {RCa1 : RunCtx}  : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI {RCa1 : RunCtx}  : list kentry := Eval vm_compute in kn_after rI knI0.

Lemma itinerary_re {RCa1 : RunCtx}  :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0x21450%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0x21450%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0x2194c%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0x21450%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0x21450%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0x21450%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0x1c858%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0x1cbb8%Z, 0x23f10%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x1a388%Z, []).
Proof. (* [comment removed for export] *)
  repeat apply conj; lazymatch goal with |- @eq ?T ?x ?y => vm_cast_no_check (@eq_refl T y) end.
Qed.

