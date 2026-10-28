(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall LibKnowFrame LibKnowXfer.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MainEntry V23LibStdioCall V23OpenFail_defs V23Open_defs V23Oom_defs V23DirRead_defs V23ReadLoop_defs V23Hdr_defs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23TRun_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes3nat02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond01K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4prod01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr07K47Corelib7Numbers7BinNums1Z02K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr03I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24s_pcC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4list02C7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25s_logC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall9log_wdl_bC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer;sr_mismatchC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer4kmapC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver;LibKnowXfer:kn_missingC5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs8kn_afterC47Corelib5Lists7ListDef3nthK47Corelib4Init5Logic3and01C47Corelib5Lists7ListDef3mapI7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX28sidecond00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry00c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs4kn_Tc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5kn_TLK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I47Corelib4Init9Datatypes3nat00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX29sym_state00I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX27scripts00c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5t_r1ac5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5t_r1cc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5t_r1bc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5t_r1dc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tm_rvlaC5ARocqVerifyHarness?AgentSubmission3V23@V23ReadLoop_defs3idbc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6t_sr1ac5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5sr_TMc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5t_kn1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tm_rvlcc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6t_sr1cC5ARocqVerifyHarness?AgentSubmission3V23;V23Hdr_defs4kn_Rc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl_rvlbc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6t_sr1bc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5sr_TLc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl_rvldc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6t_sr1dc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7calls_xK7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry06K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry05K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry07K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX25saddr01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry08K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry04C6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:kn_vars_ltC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver6SymRun:sr_vars_ltC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymDrive?sr_after_call_jC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall7kn_callK47Corelib7Numbers7BinNums1Z03K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26kentry01c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6tm_sr2I7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sentry00c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5tm_r2c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6tm_kn2C5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs7KEPT_MCc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tm_sr3iC5ARocqVerifyHarness?AgentSubmission3V23@V23OpenFail_defs3IHIc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tm_kn3ic5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5tm_r3c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl_rvlmc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6tm_sr3c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6tm_kn3c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs9kn_acallTI47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tn_kn1iC5ARocqVerifyHarness?AgentSubmission3V23;V23Oom_defs8kn_acallc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6fn_sr1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6fn_sr2c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5fn_r1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6fn_kn1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7fn_kn2ic5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5fn_r2K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26sentry01I47Corelib4Init9Datatypes6option00K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr08K6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res01K47Corelib4Init9Datatypes6option01K7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX24expr04c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs8kn_fcallC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall:stdio_callC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall6sc_retC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_fC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_fdC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_sC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall4sc_lC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wbC6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall5sc_wpc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6tl_sr1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5p_sr1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6p_sr3eI6ARocqVerifyHarness?AgentSubmission6Common4Musl<LibStdioCall9stdio_res00c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5tl_r1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6tl_kn1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl_kn2ic5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5tl_r2c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs4p_r1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs4p_r2C5ARocqVerifyHarness?AgentSubmission3V238V23Reloc9v23_relocC5ARocqVerifyHarness?AgentSubmission3V23;V23RelocImg8v23_datac5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5p_sr2c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5p_kn2c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs4p_scc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5p_r3lc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5p_r3ec5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6p_kn3ic5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5p_kn3c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6kn_TL1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl1_sr1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl1_sr2c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs8tl1_sr3ec5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs8tl1_rvl0c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6p_sr3lc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6tl1_r1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl1_kn1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs8tl1_kn2ic5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6tl1_r2c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl1_kn2c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl1_r3lc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl1_r3ec5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs8tl1_kn3ic5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl1_kn3c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl1_rvlc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs8tl1_sr3lC6ARocqVerifyHarness?AgentSubmission6Common9CliDriver7SymCall9log_win_bC7ARocqVerifyHarness?AgentSubmission6Common9CliDriver8SymExec23SX26s_regsc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7fn1_rvlc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6sr_FN1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6kn_FN1K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6e_r2pnc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6e_r2pcc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6e_r2tnc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6e_r2tcc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6e_kn1pc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6e_kn1tc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7fn1_sr1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7fn1_sr2c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6fn1_r1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7fn1_kn1c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs8fn1_kn2ic5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6fn1_r2c5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5kn_FEc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7fe_rvlpc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs5sr_FEc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7fe_rvltc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7fe_kn1ic5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6fe_r2nc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs6fe_r2cc5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs8tl1_sr2ic5ARocqVerifyHarness?AgentSubmission3V23<V23TRun_defs7tl_sr2i".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPST : list Z := (0x634c8 :: 0x63598 :: 0x63334 :: STOPS2)%Z.
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPST scr ss [].
(* [comment removed for export] *)
Definition STOPSP : list Z := [0x1139cc; 0x634c8; 0x63334; 0x10e818]%Z.
Definition runP (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSP scr ss [].

(* [comment removed for export] *)
Definition t_ss1 := SS 0x63410 sr_R [] kn_R 45.
Definition t_r1a := Eval vm_compute in runT (SCR [false; false] [] []) t_ss1.   (* [comment removed for export] *)
Definition t_r1b := Eval vm_compute in runT (SCR [false; true] [] []) t_ss1.    (* [comment removed for export] *)
Definition t_r1c := Eval vm_compute in runT (SCR [true; true] [] []) t_ss1.     (* [comment removed for export] *)
Definition t_r1d := Eval vm_compute in runT (SCR [true; false] [] []) t_ss1.    (* [comment removed for export] *)
Definition t_sr1a := Eval vm_compute in s_regs (fst (fst t_r1a)).
Definition t_sr1b := Eval vm_compute in s_regs (fst (fst t_r1b)).
Definition t_sr1c := Eval vm_compute in s_regs (fst (fst t_r1c)).
Definition t_sr1d := Eval vm_compute in s_regs (fst (fst t_r1d)).
Definition t_kn1 := Eval vm_compute in kn_after t_r1a kn_R.
Definition calls_x : expr := Eval vm_compute in nth 21 t_sr1a (ELit 0).   (* [comment removed for export] *)   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kimg_fix (K : kentry) : list kentry :=
  match K with
  | KImg 0x10000 0x127ec0 => [KImg 0x10000 0x127c68; KImg 0x127c78 0x127ec0]
  | KImg 0x158890 0x159000 => [KImg 0x158890 0x1588b8; KImg 0x158cb8 0x159000]
  | KImg 0x137f11 0x137f40 => [KImg 0x137f11 0x137f14; KImg 0x137f15 0x137f40]   (* [comment removed for export] *)
  | _ => [K]
  end.
(* [comment removed for export] *)
Definition keepT (K : kentry) : bool :=
  kentry_vars_lt 13 K && match K with KWord (SA (EVar 0) k) _ _ => (-208 <=? k)%Z | _ => true end.
(* [comment removed for export] *)
Definition fixT (K : kentry) : list kentry :=
  match K with
  | KWord (SA (EVar 0) (-192)) 8 (EVar 35) => [KWord (SA (EVar 0) (-192)) 8 (EVar 36)]
  | KWord (SA (EVar 0) (-200)) 8 (EVar 36) => [KWord (SA (EVar 0) (-200)) 8 (EVar 37)]
  | _ => if keepT K then [K] else []
  end.
Definition kn_T : list kentry := Eval vm_compute in flat_map kimg_fix (flat_map fixT t_kn1).
Definition fixTL (K : kentry) : kentry :=
  match K with
  | KWord (SA (EVar 0) (-192)) 8 (EVar 36) => KWord (SA (EVar 0) (-192)) 8 (EVar 21)
  | KWord (SA (EVar 0) (-200)) 8 (EVar 37) => KWord (SA (EVar 0) (-200)) 8 (EVar 22)
  | _ => K
  end.
(* [comment removed for export] *)
Definition slots2 (e21 e22 : expr) (l : list expr) : list expr := sr_upd (sr_upd l 21 e21) 22 e22.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition JM (i : nat) : expr := EVar (14 + i).
Definition sr_TM : list expr :=
  [ELit 0; ELit 0x63474; spx (-208); ELit 0x10800; ELit 0x1381d0; JM 5; JM 6; JM 7;
   EVar 9; EVar 12; EVar 9; JM 11; JM 12; JM 13; JM 14; JM 15;
   JM 16; JM 17; JM 18; JM 19; ELit 0x137f10; EVar 13; JM 22; JM 23;
   JM 24; JM 25; JM 26; JM 27; JM 28; JM 29; JM 30; JM 31].
Definition rvl13 (ecalls : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; ecalls] ++ (ELit 0 :: tl sr).
Definition tm_rvla : list expr := rvl13 calls_x t_sr1a.
Definition tm_rvlc : list expr := rvl13 (ELit 1) t_sr1c.
(* [comment removed for export] *)
Definition kn_acallT (kn : list kentry) : list kentry := kn_call GLOB (-208 - 1024) (-208) IHI 0x127000 kn.
(* [comment removed for export] *)
Definition tm_srM : list expr := sr_after_call_j sr_TM KEPT_AL 46.
Definition tm_knM : list kentry := Eval vm_compute in KRange (EVar 56) 0x1000 0x7fffff800000 :: kn_acallT kn_T.
Definition tm_r2 := Eval vm_compute in runT scr0 (SS 0x63474 tm_srM [] tm_knM 78).
Definition tm_sr2 := Eval vm_compute in s_regs (fst (fst tm_r2)).
Definition tm_kn2 := Eval vm_compute in kn_after tm_r2 tm_knM.
(* [comment removed for export] *)
Definition tm_sr3i := Eval vm_compute in sr_after_call_j tm_sr2 KEPT_MC 78.
Definition tm_kn3i := Eval vm_compute in kn_call [(0x1000, 0x10000)%Z] 0 0 IHI 0x127000 tm_kn2.
Definition tm_r3 := Eval vm_compute in runT scr0 (SS 0x63488 tm_sr3i [] tm_kn3i 110).
Definition tm_sr3 := Eval vm_compute in s_regs (fst (fst tm_r3)).
Definition tm_kn3 := Eval vm_compute in kn_after tm_r3 tm_kn3i.
(* [comment removed for export] *)
Definition tn_sr1i := sr_upd tm_srM (ridx 10) (ELit 0).
Definition tn_kn1i : list kentry := Eval vm_compute in kn_acallT kn_T.
Definition tn_r1n := Eval vm_compute in runT (SCR [false] [] []) (SS 0x63474 tn_sr1i [] tn_kn1i 78).  (* [comment removed for export] *)
Definition tn_r1c := Eval vm_compute in runT (SCR [true] [] []) (SS 0x63474 tn_sr1i [] tn_kn1i 78).   (* [comment removed for export] *)
Definition tn_sr1n := Eval vm_compute in s_regs (fst (fst tn_r1n)).
Definition tn_sr1c := Eval vm_compute in s_regs (fst (fst tn_r1c)).
Definition tn_kn1 := Eval vm_compute in kn_after tn_r1n tn_kn1i.

(* [comment removed for export] *)
Definition JN (i : nat) : expr := EVar (8 + i).
Definition sr_FN : list expr :=
  [ELit 0; JN 1; spx (-128); ELit 0x10800; ELit 0x1381d0; JN 5; JN 6; JN 7;
   EVar 7; EVar 6; JN 10; JN 11; JN 12; JN 13; JN 14; JN 15;
   JN 16; JN 17; JN 18; JN 19; JN 20; JN 21; JN 22; JN 23;
   JN 24; JN 25; JN 26; JN 27; JN 28; JN 29; JN 30; JN 31].
Definition kn_FN : list kentry := Eval vm_compute in List.filter (kentry_vars_lt 7) tn_kn1.
Definition fn_rvln : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ELit 2] ++ (ELit 0 :: tl tn_sr1n).
Definition fn_rvlc : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ELit 0] ++ (ELit 0 :: tl tn_sr1c).
Definition fn_r1 := Eval vm_compute in runT scr0 (SS 0x63334 sr_FN [] kn_FN 40).
Definition fn_sr1 := Eval vm_compute in s_regs (fst (fst fn_r1)).
Definition fn_kn1 := Eval vm_compute in kn_after fn_r1 kn_FN.
Definition fn_sr2i := Eval vm_compute in sr_after_call_j fn_sr1 KEPT_AL 40.
Definition fn_kn2i := Eval vm_compute in kn_acall fn_kn1.
Definition fn_r2 := Eval vm_compute in runT scr0 (SS 0x6333c fn_sr2i [] fn_kn2i 72).
Definition fn_sr2 := Eval vm_compute in s_regs (fst (fst fn_r2)).
Definition fn_kn2 := Eval vm_compute in kn_after fn_r2 fn_kn2i.

(* [comment removed for export] *)
Definition keepTL (K : kentry) : bool :=
  match K with KWord (SA (EVar 6) _) _ _ => false | KWr (SA (EVar 6) _) _ => false | _ => true end.
Definition kn_TL : list kentry := Eval vm_compute in map fixTL (List.filter keepTL kn_T).
Definition JL (i : nat) : expr := EVar (18 + i).
Definition sr_TL : list expr :=
  [ELit 0; JL 1; spx (-208); ELit 0x10800; ELit 0x1381d0; JL 5; JL 6; JL 7;
   EVar 9; EVar 14; JL 10; JL 11; JL 12; JL 13; JL 14; JL 15;
   JL 16; JL 17; EVar 15; EVar 17; ELit 0x137f10; EVar 16; ELit 0; ELit 18446744073709551614;
   JL 24; JL 25; JL 26; JL 27; JL 28; JL 29; JL 30; JL 31].
Definition rvl18 (e13 e14 e15 e16 e17 : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; e13; e14; e15; e16; e17] ++ (ELit 0 :: tl sr).
Definition tl_rvlb : list expr := slots2 (EVar 35) (EVar 36) (rvl18 calls_x (ELit 0x137f20) (ELit 0) calls_x (nth 19 t_sr1b (ELit 0)) t_sr1b).
Definition tl_rvld : list expr := slots2 (EVar 35) (EVar 36) (rvl18 (ELit 1) (ELit 0x137f20) (ELit 0) (ELit 1) (nth 19 t_sr1d (ELit 0)) t_sr1d).
Definition tl_rvlm : list expr := slots2 (EVar 36) (EVar 37) (rvl18 (EVar 13) (EVar 56) (EVar 56) (EVar 13) (nth 19 tm_sr3 (ELit 0)) tm_sr3).
(* [comment removed for export] *)
Definition tl_r1 := Eval vm_compute in runT scr0 (SS 0x634c8 sr_TL [] kn_TL 50).
Definition tl_sr1 := Eval vm_compute in s_regs (fst (fst tl_r1)).
Definition tl_kn1 := Eval vm_compute in kn_after tl_r1 kn_TL.
(* [comment removed for export] *)
Definition LGLOB : list (Z * Z) := ((0x127c68, 0x127c70) :: GLOB)%Z.
Definition kn_fcall (kn : list kentry) : list kentry := kn_call LGLOB (-208 - 16384) (-208) IHI 0x127000 kn.
(* [comment removed for export] *)
Definition tl_sr2i : list expr := Eval vm_compute in sr_upd (sr_after_call_j tl_sr1 KEPT_AL 50) (ridx 10) (ELit 0).
Definition tl_kn2i : list kentry := Eval vm_compute in kn_fcall tl_kn1.
Definition tl_r2 := Eval vm_compute in runT scr0 (SS 0x634dc tl_sr2i [] tl_kn2i 82).
Definition tl_sr2 := Eval vm_compute in s_regs (fst (fst tl_r2)).
Definition tl_kn2 := Eval vm_compute in kn_after tl_r2 tl_kn2i.
(* [comment removed for export] *)
Definition p_r1 := Eval vm_compute in runP scr0 (SS 0x63598 tl_sr2 [] tl_kn2 82).
Definition p_sr1 := Eval vm_compute in s_regs (fst (fst p_r1)).
Definition p_kn1 := Eval vm_compute in kn_after p_r1 tl_kn2.
(* [comment removed for export] *)
Definition p_r2 := Eval vm_compute in runP scr0 (SS 0x114a78 (sr_upd p_sr1 (ridx 10) (ELit (2^64 - 25))) [] p_kn1 82).
Definition p_sr2 := Eval vm_compute in s_regs (fst (fst p_r2)).
Definition p_kn2 := Eval vm_compute in kn_after p_r2 p_kn1.
Definition p_sc : stdio_res := Eval vm_compute in sc_of 82 p_sr2 p_kn2.
(* [comment removed for export] *)
Definition p_sr3i := Eval vm_compute in sc_sr p_sc.
Definition p_kn3i := Eval vm_compute in sc_kn p_sc.
Definition p_r3l := Eval vm_compute in runP (SCR [true] [] []) (SS (sc_ret p_sc) p_sr3i [] p_kn3i 114).   (* [comment removed for export] *)
Definition p_r3e := Eval vm_compute in runP (SCR [false] [] []) (SS (sc_ret p_sc) p_sr3i [] p_kn3i 114).  (* [comment removed for export] *)
Definition p_sr3l := Eval vm_compute in s_regs (fst (fst p_r3l)).
Definition p_sr3e := Eval vm_compute in s_regs (fst (fst p_r3e)).
Definition p_kn3 := Eval vm_compute in kn_after p_r3l p_kn3i.


(* [comment removed for export] *)
Definition keepTL1 (K : kentry) : bool :=
  match K with KWord (SA (EVar 0) (-192)) 8 (EVar 21) => true | KWord (SA (EVar 0) (-200)) 8 (EVar 22) => true | _ =>   (* [comment removed for export] *)
  kentry_vars_lt 18 K &&
  match K with
  | KWord (SA (EVar 0) k) _ _ => (-208 <=? k)%Z
  | KWord (SA (ELit 0) 1411256) _ _ => false
  | KWord (SA (ELit 0) _) _ _ => true
  | KWord _ _ _ => false
  | _ => true
  end end.
Definition fixw (K : kentry) : kentry :=
  match K with KWord (SA (ELit 0) 1211864) 8 _ => KWord (SA (ELit 0) 1211864) 8 (EVar 18) | _ => K end.
Definition kn_TL1 : list kentry := Eval vm_compute in KRange (EVar 18) 0x1588b8 0x158cb0 :: map fixw (List.filter keepTL1 p_kn3).
(* [comment removed for export] *)
Definition rvl18w (e13 e14 e15 e16 e17 ew : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; e13; e14; e15; e16; e17; ew] ++ tl sr.
Definition tl1_rvl0 : list expr :=      (* [comment removed for export] *)
  slots2 (EVar 21) (EVar 22) (rvl18w (EVar 13) (EVar 14) (EVar 15) (EAluw ALU_ADD (EVar 16) (ELit (-1))) (nth 19 p_sr3l (ELit 0)) (ELit 0x1588b8) p_sr3l).
(* [comment removed for export] *)
Definition tl1_r1 := Eval vm_compute in runT scr0 (SS 0x634c8 sr_TL [] kn_TL1 50).
Definition tl1_sr1 := Eval vm_compute in s_regs (fst (fst tl1_r1)).
Definition tl1_kn1 := Eval vm_compute in kn_after tl1_r1 kn_TL1.
Definition tl1_sr2i : list expr := Eval vm_compute in sr_upd (sr_after_call_j tl1_sr1 KEPT_AL 50) (ridx 10) (ELit 0).
Definition tl1_kn2i : list kentry := Eval vm_compute in kn_fcall tl1_kn1.
Definition tl1_r2 := Eval vm_compute in runT scr0 (SS 0x634dc tl1_sr2i [] tl1_kn2i 82).
Definition tl1_sr2 := Eval vm_compute in s_regs (fst (fst tl1_r2)).
Definition tl1_kn2 := Eval vm_compute in kn_after tl1_r2 tl1_kn2i.
(* [comment removed for export] *)
Definition tl1_sr3i : list expr := Eval vm_compute in sr_after_call_j tl1_sr2 KEPT_CS 82.
Definition tl1_kn3i : list kentry := Eval vm_compute in
  KWord (SA (ELit 0) 1211864) 8 (EAlu ALU_ADD (EVar 18) (ELit 2)) :: KWord (SA (ELit 0) 1211824) 4 (ELit 5)
  :: kn_call [(0x127db0, 0x127db4); (0x127dd8, 0x127de0); (0x1588b8, 0x158cb8)]%Z (-208 - 1056) (-208) IHI 0x127000 tl1_kn2.
Definition tl1_r3l := Eval vm_compute in runT (SCR [true] [] []) (SS 0x634ec tl1_sr3i [] tl1_kn3i 114).
Definition tl1_r3e := Eval vm_compute in runT (SCR [false] [] []) (SS 0x634ec tl1_sr3i [] tl1_kn3i 114).
Definition tl1_sr3l := Eval vm_compute in s_regs (fst (fst tl1_r3l)).
Definition tl1_sr3e := Eval vm_compute in s_regs (fst (fst tl1_r3e)).
Definition tl1_kn3 := Eval vm_compute in kn_after tl1_r3l tl1_kn3i.
Definition tl1_rvl : list expr :=
  slots2 (EVar 21) (EVar 22) (rvl18w (EVar 13) (EVar 14) (EVar 15) (EAluw ALU_ADD (EVar 16) (ELit (-1))) (nth 19 tl1_sr3l (ELit 0)) (EAlu ALU_ADD (EVar 18) (ELit 2)) tl1_sr3l).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition keepFN1 (K : kentry) : bool :=
  kentry_vars_lt 19 K &&
  match K with
  | KWord (SA (EVar 0) k) _ _ => (-128 <=? k)%Z
  | KWord (SA (ELit 0) 1411256) _ _ => false
  | KWord (SA (ELit 0) _) _ _ => true
  | KWord _ _ _ => false
  | KRange (EVar i) _ _ => Nat.ltb i 8
  | KAlign (EVar i) _ => Nat.ltb i 8
  | KDisj _ _ (SA (EVar i) _) _ => Nat.ltb i 8
  | _ => true
  end.
Definition fixw7 (K : kentry) : kentry :=
  match K with KWord (SA (ELit 0) 1211864) 8 _ => KWord (SA (ELit 0) 1211864) 8 (EVar 7) | _ => K end.
Definition kn_FN1 : list kentry := Eval vm_compute in KRange (EVar 7) 0x1588b8 0x158cb8 :: map fixw7 (List.filter keepFN1 (kn_acallT tl1_kn3)).
Definition sr_FN1 : list expr :=
  [ELit 0; JN 1; spx (-128); ELit 0x10800; ELit 0x1381d0; JN 5; JN 6; JN 7;
   ELit 0; EVar 6; JN 10; JN 11; JN 12; JN 13; JN 14; JN 15;
   JN 16; JN 17; JN 18; JN 19; JN 20; JN 21; JN 22; JN 23;
   JN 24; JN 25; JN 26; JN 27; JN 28; JN 29; JN 30; JN 31].
(* [comment removed for export] *)
Definition e_sr1p : list expr := Eval vm_compute in sr_after_call_j p_sr3e KEPT_AL 114.
Definition e_kn1p : list kentry := Eval vm_compute in kn_acallT p_kn3.
Definition e_r2pn := Eval vm_compute in runT (SCR [false] [] []) (SS 0x63508 e_sr1p [] e_kn1p 146).
Definition e_r2pc := Eval vm_compute in runT (SCR [true] [] []) (SS 0x63508 e_sr1p [] e_kn1p 146).
Definition e_sr1t : list expr := Eval vm_compute in sr_after_call_j tl1_sr3e KEPT_AL 114.
Definition e_kn1t : list kentry := Eval vm_compute in kn_acallT tl1_kn3.
Definition e_r2tn := Eval vm_compute in runT (SCR [false] [] []) (SS 0x63508 e_sr1t [] e_kn1t 146).
Definition e_r2tc := Eval vm_compute in runT (SCR [true] [] []) (SS 0x63508 e_sr1t [] e_kn1t 146).
Definition fn1_rvl (ew : expr) (sr : list expr) : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ew] ++ (ELit 0 :: tl sr).
(* [comment removed for export] *)
Definition fn1_r1 := Eval vm_compute in runT scr0 (SS 0x63334 sr_FN1 [] kn_FN1 40).
Definition fn1_sr1 := Eval vm_compute in s_regs (fst (fst fn1_r1)).
Definition fn1_kn1 := Eval vm_compute in kn_after fn1_r1 kn_FN1.
Definition fn1_sr2i := Eval vm_compute in sr_after_call_j fn1_sr1 KEPT_AL 40.
Definition fn1_kn2i := Eval vm_compute in kn_acall fn1_kn1.
Definition fn1_r2 := Eval vm_compute in runT scr0 (SS 0x6333c fn1_sr2i [] fn1_kn2i 72).
Definition fn1_sr2 := Eval vm_compute in s_regs (fst (fst fn1_r2)).
Definition fn1_kn2 := Eval vm_compute in kn_after fn1_r2 fn1_kn2i.

Section VP1.
Lemma t_itin1 :
  (s_pc (fst (fst t_r1a)), snd (fst t_r1a), log_wdl_b 0 [(0x127000, 0x138100); (0x158218, 0x158438); (0x158890, 0x159000)]%Z (s_log (fst (fst t_r1a))))
    = (0x10e958%Z, [SCBr false BC_EQ (EVar 9) (ELit 0); SCBr false BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1c)), snd (fst t_r1c), log_wdl_b 0 [(0x127000, 0x138100); (0x158218, 0x158438); (0x158890, 0x159000)]%Z (s_log (fst (fst t_r1c))))
    = (0x10e958%Z, [SCBr true BC_NE (EVar 9) (ELit 0); SCBr true BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1b)), snd (fst t_r1b), log_wdl_b 0 [(0x127000, 0x138100); (0x158218, 0x158438); (0x158890, 0x159000)]%Z (s_log (fst (fst t_r1b))))
    = (0x634c8%Z, [SCBr true BC_EQ (EVar 9) (ELit 0); SCBr false BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1d)), snd (fst t_r1d), log_wdl_b 0 [(0x127000, 0x138100); (0x158218, 0x158438); (0x158890, 0x159000)]%Z (s_log (fst (fst t_r1d))))
    = (0x634c8%Z, [SCBr false BC_NE (EVar 9) (ELit 0); SCBr true BC_EQ (EVar 8) (ELit 0)], true)
  /\ (sr_mismatch tm_rvla idb t_sr1a sr_TM 0, kn_missing t_kn1 (map (kmap tm_rvla idb) kn_T)) = ([], [])
  /\ (sr_mismatch tm_rvlc idb t_sr1c sr_TM 0, kn_missing (kn_after t_r1c kn_R) (map (kmap tm_rvlc idb) kn_T)) = ([], [])
  /\ (sr_mismatch tl_rvlb idb t_sr1b sr_TL 0, kn_missing (kn_after t_r1b kn_R) (map (kmap tl_rvlb idb) kn_TL)) = ([], [])
  /\ (sr_mismatch tl_rvld idb t_sr1d sr_TL 0, kn_missing (kn_after t_r1d kn_R) (map (kmap tl_rvld idb) kn_TL)) = ([], [])
  /\ calls_x = EAlu ALU_ADD (EAlu ALU_AND (EExt false 0 1 (EVar 11)) (ELit 3)) (ELit 1)
  /\ nth 19 t_sr1b (ELit 0) = EAlu ALU_ADD (EVar 6) (ELit 2) /\ nth 19 t_sr1d (ELit 0) = EAlu ALU_ADD (EVar 6) (ELit 2).
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRun_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g0000j1UTg000Pj2DTg0010j10Tg001Uj1BTg0024j1HTg003=j1FTg004Fj4@Tg005Sj1QTg0063j34Tg006Mj17Tg0072j4CTg007Rj4]Tg008[j1MTg0099j3TTg00:Bj22Tg00:]j2<Tg00;7j36Tg00;Tj1JTg00<[j3ITg00=8j3NTg00=Xj1OTg00>`j3KTg00?gj5GTg00A4j2ETg00B:j2LTg00CFj2VTg00DHj4ZTg00Ddj4YTg00E?j4XTf0R0#0#0p==%00#7p=3%70#7p=>%70#0p=1%00#0#0#Mp=8%B0#Bp=;g00E[R1f1R2;N0p=?g00FhR3f2R4P2P0CCp=:P2g00GFR5P0g00GfR6CCp=P%00#Mp=\f6R7f5R8f4R9f3R:P4P2P0CYCYp=A%00#0#0#0p=5%70#7#0#0p=SP3P3P2P0CCp=Rg00HFR;P;P0g00IQCXp=WP;P;P0g00JKCXp=[A4789A4:42/20'2p=^P8P9P:P4CC=472/20p=9%U1R0,D3R7/D5R2g00KFR4#0#=#3#>#3#=#1#1#>#8R:g00KkR9g00LKR8g00M=R<#BR=#B#;#;R>#;R?#BR@#HRAg00M\#FRBC@P9P8%H?R?PBC@%Q1R1'?RC'?5:0,P7RD;4DP6g00N:REPAPBC@P6P8P?PBC@/?1R1'?9:0:,P7R:=42:R?%74#=#3#1#1#3#1#3#8RFP6P8PAPBC@/?C5:0,P7RC=42CR8P9PEPAPBC@/?19:0F,P7RF=42FR1g00NlRA#URE%U;R6'DRGPEP6%QA%Q;CCR;;4;RAg00OKRHg00PTRIg00Q@P9P<P=%;@R@#HC]%74#M#F3T%M4#F3TR=;4=R9%H>%\4#F5TIRI=4HIR>/2>RJ'2RK,2ARL,2ARM,2ARN'2RO'2RP'2RQ'21<2DP?PQ1<2:P8PP1<2CP1PO1<2FPAPN1<G;RNPAPMPNPAPLPNPAPKPNP9PJ1<H=P>P>1<HIR>P>FAFAFAFAFAP2P7P5g00QlR>1D>0RJg00S:R9g00TF36RN760RK#JAI>0N5:01D33R3%04#3#=#>#1#5#5#8%04#3#S#5#1#5#8'R%04#1#>#5#3#5#>#8%04#1#>#5#1#=#3#>#8'R%04#1#S#3#=#3#=#1#8%04#1#S#1#5#5#8'R%Q35N35N33NR3%OK5K<PDP2P7P5g00UARD96J9RK96>0R4#JAI>0K5:0%O49K<3P:P2P7P5g00V<R:96J9R496>0RK#JAI>045:0%OK9K<3PCP2P7P5g00W7R596J9R996>0RJ#JAI>095:0%OJ9K<3PFPGPEP6g00X2RFg00XoR3g00Ylg00ZhRJP<DGg00[c1EF3#W'LP;PGPEP6g00\^RFP3g00][PJP<DGg00^WRJ,VD1EF3#W'LP;PGPEP6g00_PRFP3g00`MRDg00aIR0P<DG1V:J1EF3#['LP;PGPEP6g00bDR6P3g00cAREP0P<DG1V5J1E63#['LP;PHg00d=P=PHPH%;@#;#;#;R@PDPBCZPIPHP@PEPBCZ=4HIF^F9F9F9F9F9F9F9F9do"). Qed.

Lemma tm_itin :
  (s_pc (fst (fst tm_r2)), snd (fst tm_r2), s_log (fst (fst tm_r2))) = (0x11e154%Z, [], [])
  /\ (nth 1 tm_sr2 (ELit 0), nth 10 tm_sr2 (ELit 0), nth 11 tm_sr2 (ELit 0), nth 12 tm_sr2 (ELit 0)) = (ELit 0x63488, EVar 56, EVar 12, EVar 9)
  /\ kn_vars_lt 46 kn_T = true /\ sr_vars_lt 78 tm_sr2 = true /\ kn_vars_lt 78 tm_kn2 = true
  /\ sr_after_call_j tm_sr2 KEPT_MC 78 = tm_sr3i /\ kn_call [(0x1000, 0x10000)%Z] 0 0 IHI 0x127000 tm_kn2 = tm_kn3i /\ kn_vars_lt 78 tm_kn3i = true
  /\ (s_pc (fst (fst tm_r3)), snd (fst tm_r3), s_log (fst (fst tm_r3))) = (0x634c8%Z, [], [])
  /\ (sr_mismatch tl_rvlm idb tm_sr3 sr_TL 0, kn_missing tm_kn3 (map (kmap tl_rvlm idb) kn_TL)) = ([0%nat], [])
  /\ nth 19 tm_sr3 (ELit 0) = EVar 33.
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRun_defs ()) ["VP1"] "p&0p;1p;2p;3p;4p;6p;5g0000j1cTg000Pj2OTg005Sj1YTg0063j3;Tg001Uj12Tg0024j18Tg0072j4TTg006Mj11Tg0010j10Tg003=j1ETg0099j3gTg008[j16Tg00e:j3^Tg00fEj2xTg00gPj2wTg00h[j2VTg00iek407Tg00k0k306Tg00l;j2PTg00=8j39Tg00:Bj2CTg00:]j2LTg00;7j3hTg00;Tj1tTg00<[j3sTg00=Xj1rTg00mFj2kTg00nMj2|Tg00oTj3{Tg010bj6~Tg00?gk500Tg00A4j2zTg00E?k401Tg00B:k202Tg00DHj4qTg011gj1jTg012Ej3mTg00Ddj4pTf0R0#0#0#0p=F%10#1#1#1p=:%00#0#0#0p=3%10#0#1#0p=[%00#6p>04f6R1f5R2f4R3f3R4f2R5f1R6CTP0CTp=Z%10#0p=e%00#0#1#1p=<%00#1#0#0p=5%10#0#0#0p=4%60#Ep=D%20#2p=W%20#2#2#2p=\%20#2#2#2#2#2#2#2p=`%00#jp=}%00#0#0#0#0#0#0#0p=G%00#1#1#1p=>%00#0#0#6p==%00#1#1#0p=X%10#1#1#0p=S%00#0#1#0p=?g00OKR7%85%86=97039p=IA97609975p=R%86=970p=o%00#0p=n%10#1p=y%00#0#0#0#0#0#0#6p=Q%00#1#0#1#1#0#0#0#0p=@1V45?m60p>0:%00#1#0#1p=]%10#1#0#0p=A%10#0#1#1p>09%j0,V6p>08%00#0#0#1p=B%10#1#0#1p=i%00#1#0#1#1p=v%00#0#1p=M%10#0#0#1p=H%00#1#0#1#1#0#0p=J%66/P0p>05g00HFR8A9860795p=U%05#6/P6=980p=_%05#6%06#0#0#6'P=980p=N1V34?m56=980p=K1P56=980p>031P341P56=980598p=u%06#6,P5=980p=l%j4,V3?m56=980p=7P1P2P3P4P5P6P0CpCpp=aP7P6g013PR4P0Cqp=dg00GFR3g00GfR27;0p=f1C60,C5p=bg00FhR5g00E[R6#cR0'OR1g014LR9#cR:'OR;P1P:P5P0g00KFR<#F#:#3#[#[$04%Y6R6%Y9R9FZR=;;=1O77R>/O7R?/O7R@P?P7P>P7P7P7%e<#<#5#4#4#DRAg00M=RB#2RC#2RD#2RE#2RF#2RG#2RH#WRI#2RJ#2RK#2RL#2RM#2RN#W#\RO#W#\#`RP#2#WRQ#2RR#2RS#2RT#2RU#2RV#2#\RW#W#`RX#8RYCT%8MRZ%8JRJFZR[;;[R\A;322R]%c7R^%WX#\#`#`RXg00PTR_%8BR`%1<Ra#0Rb#4Rc#}#E3g%0<Rd#0Re#0Rf#0Rg#4#G#D%0<#>#3#<#[#=Rh#E%2X#\Ri%2iRi%2iRi%\iRi#8%2iRi%2iRi%2iRi%2iRi%2iRi%2iRi%8PRP%0<#X#:#S#?#=Rj#E%8N%8QRQ%8RRR%2i#W#`Ri%2iRi%2iRi%2i%Y73I3I9IUV9IST3R3R5RY3I3I3I5RY9RJZ'o3I3R5RA'oRA;;ART%c8RS%0gRV#0RU#n#3Ri#6RN%1aRa#1Rk#:Rl#:#:Rm#y#:Rn#1Ro#1#G#G#Q5^Yg00M\RY#ERp%@<#5#5#=RqPF%6<Rr#ERsH0:Pp%@<#X#>#=RtPI%e<#<#]#X#4#DPp%@<#5#>#=RuPI%3<#S#5#4#A#DPp%@<#5#]#=RvPI%@<#5#X#=Rw#EPpPjPCPsP`%0bRb#4RsPIPRP`%FbRb#0PIPQP`%1dRQ#1RR#4PI%8KP`%FRRR#0PIPJP`%0QRQ#4PIPZP`%FQRQ#0PI%8IP`%1eRe#4PI%8HRHP`%FeRe#0PI%DdRd9g_HP`%4fPI%e<#<#?$09#5#D%8L%6l7^Y%6gRg,x`%Gm#G#G#Q%3iRi#F#3Rm#0#G#G#Q5^`208`mRl%6mRm'wP`%FkPIPpP`%FaRa#0PIPpP`PcPIPpP`PbPIPpP`PRPI%DV9g_`P`PQPI%e<#<#B#5#3#DP`PePIPdP`PUPI%DfRf9g_`P`PaPI%3<#i#:#?#3#D%v<#?#3#QRa%0o#:#S#G#Q5^H1xHgPlPm1VHY%6iRiH07%0<#5#S#3#QRH,Vp%Fs#Q'w%M<#<#S#<#5%M<#<#S#<#A%0<#5#:#i#4%?<#>#S#A#B#6%?<#>#:#3#H#6%<<#>#:#3#H#6Pj%<<#>#:#B#B#6%M<#A#3#4#3%M<#A#3#:#5%@<#<#:Pp%0<#>#3#?#B#=RjPI%EjPp%0<#>#3#?#]#=PF%8GRG%M<#A#3#H#[%0<#>#3#<#3%M<#A#3#A#5%0<#>#3#<#5%M<#A#3#i#5%0<#>#3#<#4%M<#A#3#:#3%J<#B#3#4%J<#B#B#?PwPu%@<#5#4#=Pt%J<#B#[#3%@<#4#4#=Rt1Vpt@06fD%]<#4#5#5#4%@<#4#[#=+05%]<#4#5#X#B#6%@<#4#i#=RfPpPfPI%8E%J<#?#<#4%@<#4#:%J<#?#5#5%@<#H#?#=REPpPEPI%EN%J<#?#5#A%@<#H#H%J<#5#5#4%v<#B#B#>%J<#X#]#A%6n9^Gr1PYN%Y8RG3U7_a3N3NDK3_3NDK4033U3_Du7_v7_q5lh3N3N3NDKDK3N3lDu3N5li3U3UD7D7D7D7D7D7D7D7D73U3UD7D7D7D7D7D7D7D7D7DKDKDKDK3URh;;hRqP1P:P5P0%1<#n#X#H#H#=P6P9FZR9=;;9R6g00NlR<#cRv/OSRaPvPS%Y<99<BPGCTRG;;GR<A;7PPRr'CRn'CRI,C]RE'CRf'CRD,C]Rt,C]Ru'CRw'C1L;=P\Pw1L@[P]Pu1L32R2P]PtP2P]PDP2PTPf1L^APqPE1LShP]PIP2P6Pn1L;9P<Pr1LaG1L7PFaFaFaFaFaP1P:P5P0g00QlRr1Or0R<g00S:Rng015W3hR67h0R2#tAsr06%r2FZ=;;=P?P7P>P7P7P71dCp1dKpCT1dLp1dMpFZ=;@[g00IQ,kW#f1|X4#fg016RRW,kX#fg017N={4Xg018O5;^1O55R^P5P5PNPiCT%Y^39PYPYg019LPHPWE~g01:IRW5;S1kXW#fP1P:P5P0g01;F9h<nRn9hr0R<#tAsr0n%r<FZ=;;9PvPSg01<ARSg00XoRvg01=>R9g00aIPBI00g01>:P8P81zSvg00JKH01+02CT=;aGP7POP9PpCq=;7P3b3b3b3b3bdo"). Qed.

Lemma tn_itin :   (* [comment removed for export] *)
  True /\ True /\ True /\ True
  /\ kn_acallT kn_T = tn_kn1i.
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRun_defs ()) ["VP1"] "p;1p;3p;2p;4g0000j1pTg003=j1RTg001Uj18Tg008[j15Tg0010j10Tg0024j1ATg006Mj11Tg0099j3WTg00e:j3UTg00fEj2[Tg00gPj2ZTg00h[j2NTg00iej4aTg00k0j3oTg00l;j2BTg005Sj1mTg0063j3]Tg00:]j2jTg01?6j1iTg011gj1\Tg00=8j3>Tg012Ej3^Tg00:Bj2hTg00Ddj4gTf0R0#0#1#0#1#1#0#0#0#0p==%00#1#0#0p=3%00#0#0#5p=6%00#1#1#0p=H%00#1#1#1p=<%80#8p=e%10#0p=K%00#0#1#1p=:%00#1#0#1p=O%10#0#0#0p=4%50#Rp=E%00#0#0#0p=2%10#1#1#0p=I%10#1#0#0p=?%10#1#1#1p=;%00#0#1#0p=9%80#8#8#8p=P%00#0#0p=G%10#0#1#1p=f%00#0#0#0#0#0#0#0p=F%00#0p=df1R1%\0'Np=c%00#0#0#1p=@%10#1#0#1p=T%00#1#0#1#1p=Y%10#1p=b%00#0#1p=M%10#0#0#1p=S%00#1#0#1#1#0#0p=J%51/B0p=ng00HFR2f2R3A>2103>p=Q%03#5/B1=>20p=X%03#5%01#0#0#5'B=>20p=Cf4R4f3R5'N?^31=>20p=D1B31=>20p=l1B451B31=>205>2p=`%04#5/B5%03#5/B1=>205>2p=k%01#5,B3=>20p=_%\5,N4?^31=>20p=7g01@5R3/h0p=LP3P1g01@QP0Cgp=V%p2R0g00M\R1#RR3g00KFR4#=#3#3#6R5g00M=R6#8R7#8R8#8R9#8R:%54R;#RR<P3%=4#H#<#6R=%8:R>#8R?#eR@%K4#:#O#H#4#EP3%=4#3#<#6RAP@%24#I#3#4#?#EP3%=4#3#O#6RBP@%=4#3#H#6RC#RP3%04#H#;#I#9#6RDP7P<%A6R6%14R<#0R7#0RE#4RFP@%8@RG#8RH#8RI#8RJ#P#P#P#P#P#PRK#8#AP6%GERE#0P@%AKP6%04RK#1RL#1RM#4P@%AHP6%GMRM#0P@%AGP6%0LRL#4P@%AJP6%GLRL#0P@%A@P6%0KRJ#1RG#4P@%A?R?P6%GGRG#0P@g00PTRH%EKRK7W?P6%0JRJ#4P@%K4#:#9#f#3#E%AI%1<R<#1RI#;RN#57U1%0JRO#5RP,[6%;N#;RN#2#F#F#F#6%0ORO#0RQ#d#2RR#2RS#G#2RT#0#2#F#F#65U61c6TRU%5TRT'ZP6%GIP@P3P6%G<R<#0P@P3P6%47P@P3P6PEP@P3P6PMP@%EO9WH6P6PLP@%K4#:#@#3#2#EP6PGP@PKP6PQP@%EJRJ9WH6P6P<P@%24#T#;#9#2#E%Y4#9#F#6R<%bN#;RN#K#;#I#2#F#65U?1[?PPUPT1N?1%5SRSCa%04#3#I#F#6,N3%GF#2#6'Z%M4#:#I#:#3%M4#:#I#:#?%04#3#;#T#4%94#<#I#?#@#5%94#<#;#2#S#5%:4#<#;#2#S#5PD%:4#<#;#@#@#5%M4#?#2#4#2%M4#?#2#;#3%=4#:#;P3%04#<#2#9#@#6RDP@%RDP3%04#<#2#9#O#6P:%A>R>%04#<#2#9#H#K%04#<#2#:#2%M4#?#2#?#3%04#<#2#:#3%M4#?#2#T#3%04#<#2#:#4%M4#?#2#I#4%04#<#2#:#?%J4#@#2#4P5%J4#@#@#9PBPCPA%=4#3#4#6P=%=4#H#K#2%=4#4#4#6R=1N3=?oJ8%O4#4#3#3#4%J4#9#9#K#6'n%O4#4#3#H#@#5%=4#4#T#6RJP3PJP@%A9%J4#9#:#4%=4#4#;%J4#9#3#3%=4#S#9#6R9P3P9P@%5RRR#R%J4#9#3#?%=4#S#S%J4#3#3#4%Y4#@#@#<%J4#H#O#?%5N9U>;1B1R%m23Q7X<3C3CDD3X3CDD3l3Q3XD`Dk3C3C3C3CDDDD3C3_D`3C5_S3Q3QD7D7D7D7D7D7D7D7D73Q3QD7D7D7D7D7D7D7D7D7DDDDDDDDDDRS;]SR<#LR2#LRR#L1j0S,V<,V2,VR'Vg00IQ#ig01@m5]0#L#L#L#Ldo"). Qed.

Lemma fn_itin :
  (s_pc (fst (fst fn_r1)), snd (fst fn_r1), s_log (fst (fst fn_r1))) = (0x10e818%Z, [], [])
  /\ (nth 1 fn_sr1 (ELit 0), nth 10 fn_sr1 (ELit 0), nth 2 fn_sr1 (ELit 0), nth 4 fn_sr1 (ELit 0))
     = (ELit 0x6333c, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x1381d0)
  /\ kn_vars_lt 40 fn_kn1 = true /\ kn_acall fn_kn1 = fn_kn2i
  /\ (s_pc (fst (fst fn_r2)), snd (fst fn_r2), s_log (fst (fst fn_r2))) = (0x10e4e0%Z, [], [])
  /\ (nth 10 fn_sr2 (ELit 0), nth 2 fn_sr2 (ELit 0), nth 4 fn_sr2 (ELit 0)) = (EVar 7, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x1381d0).
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRun_defs ()) ["VP1"] "p;1p;2p;4p;3g0000j1fTg000Pj2VTg0010j10Tg005Sj1bTg0072j4@Tg0063j3?Tg001Uj1;Tg0024j1ZTg011gj1XTg003=j1ETg0099j3^Tg008[j16Tg00fEj2hTg006Mj11Tg00e:j3aTg00gPj2gTg00h[j2PTg00iej4wTg00k0j3vTg00l;j2KTg00:Bj2BTg00:]j2RTg00Ddj4[Tg00;7j3]Tg00;Tj1mTg00<[j3lTg00=Xj1kTg00mFj2sTg01Ajj1rTg012Ej3eTg00=8j3ATg00DHj4iTf0R0#0#0#0#1p=>%10#1#0#1p=\%00#0#0#0p=2%00#0#1#1p=7%00#0#0#6p=4%10#0p=M%10#1#0#0p=8%60#Ep=Ng00OKR1P1f1R2P0C@p=`f2R3P1P2P0C@p=S%00#0#1p=G%10#1#1#0p=J%00#1#0#1#1#0#0#0#0p==%00#1#0#0p=3%00#1#1#0p=H%00#1#1#1p=<%00#1#0#1p=Q%10#0#0#0p=5%10#1#1#1p=:%00#0#1#0p=9%00#0#0#0#0#0#0#0p=D%00#0p=W%X0,P2p=qf3R4/P3?e20p=p%00#1#0#1#1p=o%10#1p=x%10#0#0#1p=U%00#1#0#1#1#0#0p=L%62/K0p=ug00HFR5AA5207A3p=T%03#6/K2=A50p=Y%03#6%02#0#0#6'K=A50p=If4R6/P4?e32=A50p=C1K32=A50p=t1K641K32=A505A5p=n%02#6,K3=A50p=d%X4,P6?e32=A50p=FP1P2g01BgP0Cip=_%;0#;p=j%;0#;#;#;p=OP1P2g01CcP0Cip=cg00FhR0g00E[R2#fR3'VR6g014LR4#fR7'VR8P6P7P0P3g00KFR9#0#>#\#2#7#4%b2R2C@%b4R4C@R:;?:1V11R;/V1R</V1R1%M9#7#7#7#8#Ng00M=R=#;R>#;R?#;R@#;RA#;RB#;RC#ZRD'`g00PTRE%Z=R=%09RF#0RG#0RH#0RI#0RJ#0RK#0RL#X#E3^5S;%G9#8#2#J#M#4RM#ERN5S<RO;?ORPg00GFRQg00GfRR;?RRS%f5RTg00M\RU#ERV%=9#3#3#4RWPA%69RX#ERYPV%=9#H#<#4RZ%;CRC#;R[%M9#7#Q#H#5#NPV%=9#3#<#4R\P[%29#J#3#5#8#NPV%=9#3#Q#4R]P[%=9#3#H#4R^#EPV%09#H#:#J#9#4R_P>PY%6IRI,h=%19RY#1R`#1Ra#:#:#:Rb#2#D#D#D#4%0L#2RL#2Rc#0#W#2Rd#0#2#D#D#45a=1q=dRe%6dRd'gP=%0a#W#XP[PVCpP=%0`#WR`#0P[PVP=%0YRY#5P[PVP=%0YRY#WRa#0P[PVP=%1FRf#5P[%NJ9^E=P=%2fP[%M9#7#>#3#2#NP=%5GP[%NFP=PKP[%NHRH9^E=P=P`P[%29#\#:#9#2#N%o9#9#D#4R`%xb#:Rb#M#:#J#2#D#45aD1hDIPePd1PDU%6cRcCw%09#3#J#D#4,PV%1Y#W#D#4'g%G9#7#J#7#3%G9#7#J#7#8%09#3#:#\#5%99#<#J#8#>#6%99#<#:#2#U#6%79#<#:#2#U#6P_%79#<#:#>#>#6%G9#8#2#5#2%G9#8#2#:#3%=9#7#:PV%09#<#2#9#>#4R_P[%E_PV%09#<#2#9#Q#4PA%ZBRB%09#<#2#9#H#M%09#<#2#7#2%G9#8#2#8#3%09#<#2#7#3%G9#8#2#\#3%09#<#2#7#5%G9#8#2#:#2%L9#>#2#5%L9#>#>#9P^P\%=9#3#5#4PZ%=9#H#M#2%=9#5#5#4RZ1PVZ?vH?%Q9#5#3#3#5%L9#9#9#M#4'u%Q9#5#3#H#>#6%=9#5#\#4RHPVPHP[%Z@%L9#9#7#5%=9#5#:%L9#9#3#3%=9#U#9#4R@PVP@P[%6LRL#E%L9#9#3#8%=9#U#U%L9#3#3#5%o9#>#>#<%L9#H#Q#8%6b9aBX1KUL%b53T7Y`3I3IDC3Y3IDC3t3T3YDn7Y]7YW5dM3I3I3IDCDC3I3dDn3I5dc3T3TDFDFDFDFDFDFDFDF3T3TDCDCDCDCDCRc;?cRMP6P7P0P3%09#>#8#U#8#4P2C@P4C@R4=?84R2%ZC%Xa#E9^E='`=S;NRN=?<NR='BRE'BRa'BRC'B1R8:PPPC1R1OPSPa1RQRPMPE1RTcP2P=1R841R<NC[C[C[C[C[P6P7P0P3g00QlR=1V=3R2g00S:Rcg01D_3]RE7]3RM#mAl=3EC@%kMC@=?8:1_>V%j[R[/_V'`1_?V5S;1_AV5S<=?1O%j[#O#O#O#O#O#O#Og01EZRO's=?QR%rOg01FV5?TP6P7P0P3g01GS9]2cRc9]=3R2#mAl=3cC@%k2C@=?841c[V1c?V'`1cAV5S;=?<N'B'B'B'B'Bdo"). Qed.

Lemma tl_itin :
  (s_pc (fst (fst tl_r1)), snd (fst tl_r1), s_log (fst (fst tl_r1))) = (0x635e0%Z, [], [SE (SA (ELit 0) 0x137f14) 1 (ELit 1)])
  /\ (nth 1 tl_sr1 (ELit 0), nth 10 tl_sr1 (ELit 0), nth 11 tl_sr1 (ELit 0), nth 2 tl_sr1 (ELit 0), nth 3 tl_sr1 (ELit 0), nth 4 tl_sr1 (ELit 0))
     = (ELit 0x634dc, EVar 14, EVar 9, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x10800, ELit 0x1381d0)
  /\ kn_vars_lt 50 tl_kn1 = true /\ sr_vars_lt 50 tl_sr1 = true /\ kn_fcall tl_kn1 = tl_kn2i
  /\ (s_pc (fst (fst tl_r2)), snd (fst tl_r2), s_log (fst (fst tl_r2))) = (0x63598%Z, [], [SE (SA (ELit 0) 0x137f14) 1 (ELit 0)])
  /\ (s_pc (fst (fst p_r1)), snd (fst p_r1), log_wdl_b 0 [(0x127000, 0x138100); (0x158218, 0x158438); (0x158890, 0x159000)]%Z (s_log (fst (fst p_r1))))
     = (0x114a74%Z, [], true)
  /\ (nth 17 p_sr1 (ELit 0), nth 10 p_sr1 (ELit 0), nth 11 p_sr1 (ELit 0)) = (ELit 29, ELit 1, ELit 0x5413)
  /\ (s_pc (fst (fst p_r2)), snd (fst p_r2), log_wdl_b 0 [(0x127000, 0x138100); (0x158218, 0x158438); (0x158890, 0x159000)]%Z (s_log (fst (fst p_r2))))
     = (0x1139cc%Z, [], true)
  /\ stdio_call 82 p_sr2 p_kn2 = Some p_sc
  /\ (sc_ret p_sc, sc_f p_sc, sc_fd p_sc, sc_s p_sc, sc_l p_sc, sc_wb p_sc, sc_wp p_sc) = (0x114a98%Z, 0x127db0%Z, 1%Z, ELit 0x134ba, ELit 1, ELit 0x1588b8, ELit 0x1588b9)
  /\ (s_pc (fst (fst p_r3l)), snd (fst p_r3l), log_wdl_b 0 [(0x127000, 0x138100); (0x158218, 0x158438); (0x158890, 0x159000)]%Z (s_log (fst (fst p_r3l))))
     = (0x634c8%Z, [SCBr true BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], true)
  /\ (s_pc (fst (fst p_r3e)), snd (fst p_r3e), log_wdl_b 0 [(0x127000, 0x138100); (0x158218, 0x158438); (0x158890, 0x159000)]%Z (s_log (fst (fst p_r3e))))
     = (0x10e818%Z, [SCBr false BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], true)
  /\ kn_after p_r3e p_kn3i = p_kn3
  /\ (nth 10 p_sr3e (ELit 0), nth 1 p_sr3e (ELit 0), nth 2 p_sr3e (ELit 0), nth 4 p_sr3e (ELit 0)) = (EVar 15, ELit 0x63508, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x1381d0).
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRun_defs ()) ["VP1"] "p%0p%1p&0p;1p;2p;3p;4p;<p;5g0000k10?Tg000Pj2_Tg005Sj1yTg003=j1BTg0010j10Tg00h[j2@Tg001Uj12Tg008[j1=Tg01HNk30HTg00=8j36Tg0063j3ETg0024j18Tg006Mj11Tg00e:k305Tg00fEk20ITg00gPk20FTg00iek40^Tg00k0k30[Tg00l;j2[Tg01IYk10YTg01J;k40XTg011gj1PTg01KDm<0TTg01LMk20ATg0072j4UTg01Lok30STg004Fk40@Tg00:Bj2HTg00:]k208Tg00;7j3gTg00;Tj1tTg00=Xj1jTg00mFk20QTg00nMk20PTg01N8k10OTg00>`j3{Tg01O6k50NTg01P>k10MTg01QBk10UTg01RDk10VTg01SGk10dTg01TIk10cTg01UKk10bTg01VNk10aTg00CFk20`Tg0099k30KTg012Ej3ZTg00Ddk40=Tg00<[k30_Tg00DHk40>Tf0R0#1#0#0p>0<%00#1#1#0p=N%10#0#1#1p=V%10#1#0#0p=7%00#0#0#=p=3%10#1#1#1p=<%10#1#1#0p=L%00#0#1#0p=;%10#0#0#=p>07f5R1f4R2g00FhR3f3R4f2R5f1R6CUP0CUp=bg00OKR7,_0p=`%10#0#0#0p=5%10#1#0#1p=O%00#0#1#1p=9%00#1#1#1p=Q%00#0#=#Bp=M%20#2p=|P7P7P6P0CUp=n%00#0#0p=C%00#Pp>09g00PTR8%B080K6p=]P2P7P4P7P5P6CUP0CUp=Y%00#0#1#1#1#0#0#0#0p=d%10#0#1#0p=X%00#1#0#1#1#0#0#0#0p=F%00#1#0#0p=:1@45?Z60p=J%10#0p>0e%00#1#0#1p=W1@45%=0#B7Z6p>0L%00#0#0#0p=D%20#2#2#2p=h%P5,@4?Z60p=>%00#0p=G%=0#Bp=KB0K860p>0J%10#1p>06%10#1#1#1#1#1#1#1p=s%00#0#0#0#0#0#0#0p=f%00#0#0#0#0#0#0#=p=c%P0,@6p>0G%00#1#0#1#1p>04%00#0#1#0#0p>0]%=0,[6p>0\%00#1#0#0#1#1#1#1p>02%00#0#1#0#0#1#1p=a%10#=p=r%00#0#1p=e%00#0#0#1p=T%10#0#0#1p=R%00#1#0p=q%=6/[0p>0Zg00HFR9A6960765p>011[241[56=690569p=p%05#=/[6=690p=xAZ456=690p>00%02#=/[4%05#=/[6=690569p=w1[56=690p>0Ef6R:?Z12AZ456=690569p>0;A6960969596949692p=4P3P5P6P0CUp=~P6g00GFR;P0g00GfR<CUp=}P5P7P6P0CUp>0D%00#0#1#0#0#1#1#1#1#1#0#1#1p=^%20#2#2#2#2#2#2#2p=z%85%86=670567p=oA67609675p=\%86=670p>0C%15#0#0#0#P,@4?Z60p=A%05#P,@4?Z60p=I%05#P,@4%=0#B7Z6p=v%00#0#0#Pp>0W%P4,@2?Z56=690p=?A6960p>0BP3P3P6P0CUp=uP2P420856P0H0=p=SP:P1P2P4P5P6P0H0=H0=p>0Rg00QlR=?g60p=mB0_=60p=lP7P6g01WQS00P0H0>p=kP7P6g01XMP0H0>p>0:P7P6g01YHP0H0>p>03AE:12AE456/H0'Hp=ig00E[R0$0?R6,_3R5g014LR4$0?R:'_R2P5P:P6g00KFR1$0<#N#V#7#3%y0R>g00M\R?#BR@%01#N#<#L#;$07RA'@RBg00M=RC#2RD%=1RE#BRF40H%y4RG564EbRH;EH1_77RI#`RJ#`RK#`S01#`S02Q01PKPJPI%51#O#9#Q#M%2DRL#2RM#2RN#2RO#2RP#|RQ#2RR#2RS#2RT#2RU#|RV#8S03'n%8RS04%8CRR%11RW#0RX#1S05#CRY$09']S06DY%01RZ#0R[#0R\#0R]#5S07#CS08#C#MS09%d1#9#X#3R^#BR_DYR`;E`S0:AE;<<Ra&0?9RbPBPDPFP@%F1#:#:#3RcPNPFCJS0;P@%F1#N#Q#3RdPQ&0e1#9#W#N#5H0LS0<P@%F1#:#Q#3RePQ%D1#L#:#5#7H0LS0=P@%F1#:#W#3RfPQ%F1#:#N#3Rg#BCJS0>P@%01#N#<#L#;#3RhPDPFCJS0?PR%0XRX#1S0@#CRiPQ%2VS0A#2S0B#2S0C#hRV#2Rj#8C>S0DPR%0XS0E#0S0F#0RX#0S0GPQ%8VC>S0HPR%1ZRV#1Rk#1S0I#0S0J#GS0KPQ%8SC>S0LPR%0kS0M#0S0N#0Rk#0S0OPQQ04C>S0PPR%0VRl#1S0Q#0S0R#GRmPQ%8UC>S0SPR%0lS0T#0Rl#0RU#0RnPQ%8QC>S0UPR%1[R[#1Ro#0Rp#0S0V#0RqPQ%8PRPC>S0WPR%0[R[#0Rr#0S0X#0S0YPQ%KZRZ-0JPC>S0ZPR%1\S0[#0S0\#0S0]#0RsPQ%51#7#X#O#MC>S0^%8T%1WRW#1Rt#1S0_#1$06Ru#=805?S0`%=]Rv-0IRS0a%suRu#f#f#f#c%0]R]#0Rw#GRx#GRy#GRz#DR{#C#DR|#0#f#f#c605RS0b20GR|R}%=|R|+0FS0cPR%CtS0dPQP@C>S0ePR%0WRW#GRt#0S0fPQP@C>S0gPRPYPQP@C>S0hPRPXPQP@C>S0iPRPkPQ%=],]RC>S0jPRPUPQ%51#7#W#D#MC>S0kPRQ0XPQPZC>S0lPRPwPQ%K\R\-0JRC>S0mPRPtPQ%G1#9#Q#7#5#MC>S0n&041#;#D#cRt&06u#<Ru#1Rw#0#<#L#f#c605PS0o20IPvS0pP}P|1@P?%={R{H0^S0q&0]1#L#D#cS0r,@@%Ci#c+0FS0s%;1#Q#7#N#5-0\{S0t%01$02#5#<#3S0u%01$02#O#5#3S0v%a1#<#N#D#r%a1#<#5#:#r%e1#V#<#5#:#rPh%e1#V#<#5#5#rPA%e1#V#<#5#X#r%d1#;#cS0w%e1#7#D#<#:%F1#9#<#3%d1#;#T#3RA,@@PQ%BA%d1#;#W#3,@@PN%8ORO%e1#7#D#R#X%d1#9#c%e1#7#D#7#:%d1#9#:#3%e1#7#D#O#:%d1#9#5#3P^%d1#9#7#3%F1#:#;#3Pc%q1#7#T#T#;PgPe%F1#:#5#3Pd%q1#7#T#X#D%F1#5#5#3Rd1@@d@0[\L%W1#5#:#:#5%F1#5#X#3+0Z%q1#7#;#9#D#r%F1#5#O#3R\1@@\PQ%8M%q1#7#;#9#5%F1#5#<#3%q1#7#;#:#:%F1#R#;#3R\1@@\PQ%=zRz#B%q1#7#;#:#7%F1#R#R#3&041#T#T#;#3S0x&041#T#T#Q#3R\&041#T#R#Q#3RePt%=u:05OE1[?z%y9401Dp3xH00DwH0040E4013xDp7xfDp3xDwK0;3xDpDpS0y40ED4D4D4D4D4D4D4D4H00Rf;EfS0zP5P:P6&0<1#N#V#9#3P>B0HBD@=64GEbRG=E2GS0{1_5;R4%01#;#R#:#L$07=~6>,}5R9;E9S0|%1WRW#K/nF%0mS0}#0S0~#1#9#K60DIRm=EJmS10%01#;#Q#9#R$07Rz=~6>,}5RO=E4OS11g01ZDRu$0YS12%^1#N#3RgPE%01#;#R#W#9#3Rc%B\R^%W1#5#5#V#R#KS13P^%Ky%91#:#V#X#KRAPF%5lS14$09,]RRl%hj#z#zRj#2R{#2Ri#2RP#2#hR|#h#zR}#2Rv#2RZ#2R]#2Rk#2RX#2#|#h#zRY%BcQ09%2Y#hR~%2~R~%2~R~%BdRd%h~R~#8%2~R~%2~R~%2~R~%2~R~%2~R~%2~R~%91#:#V#V#KS15%2~#|#zR~%2~R~%2~R~%2~%y73o3o9\FF9\F@9\FA5\@9\AF3o3o3o5\F7\F+0C3o7\_7\l+0CP@%^1#X#3S09PQ%BeCJS16P@%^1#V#3PQP^CJS17P@%^1#O#3S18PQP^CJS19P@%01$02#7#5#3S1:PN%1w$06#<Rw#1Re#1$06Rl#1#<#sR7#s#sR~#1#KS1;CJS1<P@%^1#<#3S1=PQ%BzCJS1>PRPUPQg00KkS1?PLP?PQH0XR?CAS1@PR%0nS1A#0PQ%BgRnCIS1BPR%1oRo#7PQ%G1#W#D#L#X#MCIS1CPR%0oRoPQQ15CAS15PR%GoRo#0PQPnCIS1DPR%1pRpPQPFCAS1EPR%CpPQ%0wCvS1FPRQ0VPQ%KeCAS0VPR%0qRq#0PQ%1[R[CvS1GPR%1[RePQ%G1#W#9#N#7#MCAS1HP@P\PDQ0F#KR\CJS0FPRPyPDP\C>S1IPR%0[R[PQP@CAS1JPR%1rRr#CPQPFCIS1KPR%G[R[#0PQP@CIS1LPR%CePQQ08#1#XCvS08PRPrPQP@CAS1MPR%GsPQP@CIS1NPRQ0T#1Rs#CRr$09RePQ%PxRx,]RCJS0TPRQ0XPQ%Gl#7#7#7#7#7#7#O#KCAS0XPRQ0Y#0Rl#0PQ%07#s#sCvS0YPRQ0]PQQ0@#1#9#9#9#9#9#MCAS0@PRQ0[#1R7#0R\#GRy#0RwPQ%5[#RCvS0[PRQ0G#0RpPQP?CIS0GPRQ0\#1RU#CPQPdCIS0\PRPUPQP@CAS0]PRP\PQ1]ReCAS1OPR%17R7PQ%Pw,]RCAS1PPR%C7PQQ0E#1$0WR7,]RCIS0EPRQ0I#1RwPQ%8PCAS0IPR%CwRwPQ%8iCIS1QPRQ0JPQ%8{CAS0JPRQ0K#0R{PQ%8jCIS0KPRQ0M#1RjPQ%0~#KCAS0MPR%CjRjPQP@CIS1RPRQ0NPQ%KVRVCAS0NPRQ0O#0R~PQP@CIS0OPRQ0Q#1RiPQPFCAS0QPR%CiRiPQPdCIS1SPRQ0RPQ%G1#O#;#L#MCARdPRQ0~PQPnC>RnPRPsPQ%G1#W#;#<#D#MCARsP@%^1#5#3PQP@CJRPP@%^1#Q#3RePQP@CJR\P@%01$02#7#Q#3RUPNQ1;CJRzP@PgPNPVCJRVPRP{PQP@PRPwPQP@PRPpPQP@1@R7PQP@20GRjPQP@PRQ14PQQ07#PRj,]RR7PRP~PQP?PRPiPQQ0B#8RiPRQ0}PQ%BhPRPrPQP@PRQ1APQQ0A#8RrPRPoPQQ03PRPqPQQ04PRP[PQ%51#O#Q#W#MPRPlPQP7PRQ0d#0PQ%8ZPRQ0_#CPQ%8v1@RxPQ%8}1@RjPQP@PRQ05#5PQ%8XPRQ0f#0PQ%8kPR%CWPQ%8]PRPyPQ%51#O#9#V#MPBPDP@Q0;Q0<Q0=Q0>Q0?Q0DQ0HQ0LQ0PQ0SQ0UQ0WQ0ZQ0^Q0`Q0aQ0bQ0cQ0eQ0gQ0hQ0iQ0jQ0kQ0lQ0mQ0nQ0oQ0pQ0qQ0sQ0tQ0uPg%^1#N$07Pe%a1#L#L#:Q09%a1#L#<#DQ18%a1#L#<#5Q1=%a1#<#fPU%a1#<#T#LQ1:%a1#<#;#;Q0vQ0yDwDwDwDpD4D4D4D4D4D4D4D4H00D?D?D?D?K0;D?D?D?D?D?D?D?D?D?D?D?D?K0;D?D?D?RU+0B401D4D4D4D4D4D4D4D4D4D4D4D4N<0T-0AuRe;EeRB1_33RQ/_3Ry#`RR#`R]#`RW#`RkPWP]PRPyPQP31ucgPECUPAPFDYP^Q13DYR^;E^RF&0<1#N#R#R#3P<g00N:RA%P1#B:0S8iRiP@H0@=60>5~6,}5R8=E48RE%01#T#O#D#9#3Q1?PAPiP@H0@=60>5~6,}5R>=E4>R0PVQ17Q16Q19Q1<Q1>Q1@Q1BQ1CQ15Q1DQ1EQ1FQ0VQ1GQ1HQ0FQ1IQ1JQ1KQ1LQ08Q1MQ1NQ0TQ0XQ0YQ0@Q0[Q0GQ0\Q0]Q1OQ1PQ0EQ0IQ1QQ0JQ0KQ0MQ1RQ0NQ0OQ0QQ1SPdPnPs20BzU:01P\D4D4D4D4D4D4D4D4D4D4D4D4R\=Eb\RPPJPI%51#O#:#;#M,nrQ06P_DYR_=EK_Rr'HRU'HRz'HRs'HRn'HRd'HRV'HRi'HRA'HRc'HRg,HaRX'HRj'HP2PHQ0:PjQ02P`PaPX208;<RXPaPgPXQ0zPcPbPfQ0{PAP2PGQ0|PiP4P9Q10PVPJPmQ11PdP4POPBPnQ12PePFPsPkP^PEPzP4P8P0PUP4P>PPPrPbP\208K_DSDSDSDSDSDSDSDSDSDSK0RDSDSP2P5P:P61_=6R=g00S:R\g01[M3gRr,m6RP#t1l6r%jPEbPHQ02Q01PKPJPI1kD@1kS@'n1kT@1kL@DY1kM@1kN@DYP`P;g01\HR`-0Q|P<P;Q00-0P|P<Pb&0O`g01]DP2P5P:P6g01^A9g=\R:,m6R2#t1l6:%j2EbPGP4P5P;P6g01_<9g=\RG,m6R2#t1l6GQ0rQ0w'u%F1#:#9#3%F1#5#Q#3'uQ0x/ut%yQ56Q56Q56QRt%j25{CEbP9PJQ0C00:@20:S@'n20:T@60DIPmP4P5P;P6g01`69g=\Rm,m6RT#t1l6m%jT9{CtEbPOQ12g01a0g01akPYg01bhg01ccI0Ng01d^RY-0AuPkPWP]PRPyPQP3&0MY&0UY'u&0VYCU&0dY&0cYDY&0bY&0aYDYP^P4P5P;P6g01eX9g=\R^,m6RY#t1l6^%jY9{CtEbP8P4P5P;P6g01fSR;9g=\R\,m6R=#t1l6\%j=9{CtEbP>Pbg01gN-0`;g01hJPJPI203S@203D@'n203L@203N@DY=EK_FiFiFiFiFiFiFido"). Qed.

Lemma tl1_itin :
  (sr_mismatch tl1_rvl0 idb p_sr3l sr_TL 0, kn_missing p_kn3 (map (kmap tl1_rvl0 idb) kn_TL1)) = ([0%nat], [KRange (ELit 0x1588b8) 0x1588b8 0x158cb0])
  /\ (s_pc (fst (fst tl1_r1)), snd (fst tl1_r1), s_log (fst (fst tl1_r1))) = (0x635e0%Z, [], [SE (SA (ELit 0) 0x137f14) 1 (ELit 1)])
  /\ (nth 1 tl1_sr1 (ELit 0), nth 10 tl1_sr1 (ELit 0), nth 11 tl1_sr1 (ELit 0), nth 2 tl1_sr1 (ELit 0), nth 3 tl1_sr1 (ELit 0), nth 4 tl1_sr1 (ELit 0))
     = (ELit 0x634dc, EVar 14, EVar 9, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x10800, ELit 0x1381d0)
  /\ kn_vars_lt 50 tl1_kn1 = true /\ sr_vars_lt 50 tl1_sr1 = true /\ kn_fcall tl1_kn1 = tl1_kn2i
  /\ (s_pc (fst (fst tl1_r2)), snd (fst tl1_r2), s_log (fst (fst tl1_r2))) = (0x63598%Z, [], [SE (SA (ELit 0) 0x137f14) 1 (ELit 0)])
  /\ (nth 1 tl1_sr2 (ELit 0), nth 2 tl1_sr2 (ELit 0), nth 11 tl1_sr2 (ELit 0)) = (ELit 0x634ec, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0)
  /\ sr_vars_lt 82 tl1_sr2 = true /\ kn_vars_lt 82 tl1_kn2 = true
  /\ (s_pc (fst (fst tl1_r3l)), snd (fst tl1_r3l), s_log (fst (fst tl1_r3l))) = (0x634c8%Z, [SCBr true BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], [])
  /\ (s_pc (fst (fst tl1_r3e)), snd (fst tl1_r3e), s_log (fst (fst tl1_r3e))) = (0x10e818%Z, [SCBr false BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], [])
  /\ kn_after tl1_r3e tl1_kn3i = tl1_kn3
  /\ (nth 10 tl1_sr3e (ELit 0), nth 1 tl1_sr3e (ELit 0), nth 2 tl1_sr3e (ELit 0), nth 4 tl1_sr3e (ELit 0)) = (EVar 15, ELit 0x63508, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x1381d0)
  /\ (sr_mismatch tl1_rvl idb tl1_sr3l sr_TL 0, kn_missing tl1_kn3 (map (kmap tl1_rvl idb) kn_TL1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x1588b8 0x158cb0]).
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRun_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;5g0000j1rTg000Pj2STg005Sj1lTg00=8j3=Tg003=j1FTg00e:j3]Tg0072j4NTg0063j3CTg006Mj11Tg00h[j2TTg001Uj14Tg008[j16Tg01HNk303Tg0024j1BTg0010j10Tg0099j3fTg00fEk20:Tg00gPk209Tg00iek40FTg00k0k30DTg00l;j2RTg011gj1mTg01Lok30ATg004Fk405Tg012Ej3gTg00:Bj2?Tg00:]j2vTg00?gk502Tg00A4k201Tg00B:j2~Tg00;7j3VTg00;Tj1kTg00<[j3jTg00=Xj1oTg00mFj2}Tg00nMj2|Tg01N8k10?Tg00CFk20>Tg00Ddj4zTg00E?k40=Tg00DHj4tTf0R0#0#1#0#1#1p=q%00#0#0#1p=A%00#1#1#1p=9%00#0#0#6p=2%10#0#0#1p=H%00#1#1#0p=Og00HFR1f1R2;=0p=s%00#0p=`%10#0#1#1p=G%10#1#0#0p=7%00#0#1p=b%10#1#1#1p=;%10#0#0#0p=3%10#0#1#0p=Q%00#6p>0Bf5R3f4R4g00FhR5f3R6f2R7P2CNP0CNp=U%10#1#0#1p=I%00#0#1#1p=:%00#0#6#Fp=K%40#4p=ng00OKR8P8P2P0CNp=d%00#mp>0<P4P8P6P8P7P2CNP0CNp=a%10#0p>0;%00#0#0#0#0#0#0#0p=[%00#0#0#0p=5%00#0#1#0#0#1#1#1#1p=L%60#Fp=h1T67?g20p>0I%10#1#1#1#1#1#1#1p=e%10#1p>0H%00#1#0#0p=8%10#1#1#0p=D%00#1#0#1#1#0#0#0#0p=E%00#1#0#1p=_%00#0#1#0p=>%00#0#0p=Z%00#0#0#0#0#0#0#6p=Y%m0,T2p>0G%00#0#1#0#0p>0E%00#0#1#0#0#1#1p=P%00#1#0p=^%62/R0p>0CA=1209=17p=W1R72==10p>08%04#6/R6%07#6/R2==105=1p=X1T46?g72==10p=@%07#6/R2==10p=y1R461R72==105=1p=x%02#6,R7==10p>07%m6,T4?g72==10p=<Ag672==10p=wP7P8P2P0CNp>06P4P61v72P0Czp=Jf6P3P4P6P7P2P0CzCzp>04P1P1P0g01iEH0=p>00P8P2g01jAR4P0Ctp=c%40#4#4#4p>0@%40#4#4#4#4#4#4#4p=\g00GFR3g00GfR97C0p=iP8P2g01k>R:P0Ctp=uP8P2g01l;P0Ctp=pAC672/?0p=M1?20,?7p={g00NlR7#rR2%r1R0'SR6P2P0g00M=R;%l75=7S00g00KFR7#q#A#A#9#2R<#FR=%q7#A#H#O#2R>7]<%l1R1'sCNR?;C?g00E[R@#rRA,S5R5g014LRB#rRC'SRDP5PCPA%17#`#O#G#7#2%l@REg00M\RF#FRG%b7#G#;#3#Q$0BS01'TRH%4;RI%67RJ#FRK403%lBRL5=BEURM;CMS021S88RN/S8RO/S8RP/S8RQ/S8R8PQPPPOPN%37#I#:#9#K%4IRR#4RS#4RT#4RU#4RV#nRW#4RX#4RY#4RZ#4R[#nR\#B'd%BXRXg00PTR]%B;R^%17R_#0R`#3Ra$0<#F3fRbDa%07Rc#0Rd#0Re#0Rf$0;#[#K%07#9#5#:#Q#2Rg#FS03DaRh;ChS04AC399RiPHPIPK%4\R\#4Rj#nRk#BRl?]<>RmPG%L7#G#O#2S05PT%1cRn#hH0IRo%L7#G#G#2,TGS06PWPlPG%L7#G#Q#2RpPW%q7#A#H#9#2Rq#FPG%L7#G#I#2RrPWP=PG%L7#7#3#2R=PT%1_R_#1Rs#;Rt#eRu$0H#;Rv#1Rw#1#e#e#e#e#e#hRxPG%L7#G#;#2RyPW%`7#8#D#9#:#KPG%L7#G#3#2PWPGPG%L7#G#9#2RzPWPGPG%L7#7#9#2R{PTPxPG%E7#8#8#2S07PTPKPG%E7#O#9#2S08PW%37#I#_#Q#KPG%E7#8#9#2S09PW%`7#:#H#>#:#KPG%E7#8#_#2S0:PW%E7#8#O#2S0;#FPG%07#O#;#D#>#2RxPIPKP^%0`R`#3RKPW%4k#nRk#4R|#BP^%Z`R`#0PW%BkP^%1nRk#3PW%BYP^%ZkRk#0PWPXP^%0nRn#3PW%B[P^%ZnRn#0PW%BWP^%1dRd#3PW%BVRVP^%ZdRd#0PW%hcRc9f]VP^%3ePW%37#7#Q#I#K%BZ%6t7]F%6fRt-0:^%[u#[#[#Y%0fRf#0Ru#`#5R[#5RX#Z#5R}#0#[#[#Y5]^20G^}R~%6}R}+09P^%ZsPWPGP^%Z_R_#0PWPGP^PaPWPGP^P`PWPGP^PkPW%hf9f]^P^PnPW%37#7#_#5#KP^PdPWPcP^PuPW%heRe9f]^P^P_PW%`7#:#9#7#3#K%q7#>#5#YR_%0w#;#D#[#Y5]V20:VtP~P}1TVF%6XRXH0F&0E7#D#5#Y,TG%ZK#Y+09%P7#D#:#8%P7#D#:#7Q05%P7#D#I#QPz%P7#D#D#8Pp%P7#D#;#5Pr%P7#D#;#3Py%P7#;#[P{%P7#;#A#DP=%P7#;#>#>%L7#I#3#2%>7#9#D#7#A#6%>7#9#;#5#H#6%:7#9#;#5#H#6Px%:7#9#;#A#A#6Q01%:7#9#;#A#_#6%07#9#5#>#Y%b7#7#5#;#8%E7#:#;#2PG%07#9#5#>#A#2RxPW%FxPG%07#9#5#>#_#2PT%BURU%b7#7#5#H#Q%07#9#5#:#Y%b7#7#5#7#8%07#9#5#:#8#2%b7#7#5#I#8%07#9#5#:#3#2%b7#7#5#;#5%^7#7#A#5#3Q07%^7#7#A#A#>Q0:Q0;Q09%E7#8#3#2Q08%^7#7#A#Q#5%E7#3#3#2Rx1TGx@0DeR%_7#3#8#8#3%E7#3#Q#2+0C%_7#3#8#O#A#6%E7#3#I#2RePGPePW%BS%^7#7#>#:#3%E7#3#;#2%^7#7#>#8#8%E7#H#>#2RePGPePW%6[R[#F%^7#7#>#8#7%E7#H#H#2%^7#7#8#8#3P<%6v9]UJ1RF[;W1:08q_DXD@DXD@4083W3yDxDX607g3yDXD@D@3yDxDxDXDXDXDX607X3W3WD<D<D<D<D<D<D<D<D<3W3WD<D<D<D<D<D<D<D<D<D@D@D@D@D@D@D@D@D@D@D@D@RXCw3WCwRg=C0gR_P5PCPA%17#`#O#G#:#2PEB03HIG==BLEURB=CDBRq%37#I#:#G#K/db>06NGR[=CO[RFP5PCPA%17#`#O#H#H#2P9g00N:RU%Bj%m7#F60A]RjPGH05==@EPLEURJ=CDJRvP5PCPA%07#A#I#5#:#2g00KkPUPjPGH05==@EPLEURL=CDLREQ06PWAf]lcRcAgHIG1smX5WoCwRo=C0oRXPOPN%B\%37#I#8#>#K'dPbQ03DaRb=CPbR7P2P0Q00A]c<>/s1CNR1=C61Rc'?R>'?R<'?R\'?Rm,?iRH,?iRl'?R]'?RW'?R@,?iRj'?RU'?Re'?P6P?Q02PePDPMQ04PUP8PhPiPj1v39R9PiP@P9P_PWP0PgPqP]PDPBPFPlPOP[PiPHP9PiPmP9PvP\PDPJPEP<PDPLPXP>P0PoP7PcPPPb1v61DJDJDJDJK04DJDJDJK04DJDJDJP6P2P0g01m9Rcg00XoR7g01n7g00aIRoP;I02g01hJ201c7$00'~CNP?PDP5PCPAg00QlR?1S?ARcg00S:R>g01o33VRX7VAR<#kAj?AX%o<EUPMP8PQPPPOPN1cIG1cYG'd1cZG1cRGDa1cSG1cTGDaPh&0@|#\#\#\R|g01ooRh'}#i1||4#iP0&0?hg020lPDP5PCPAg021j9Vc>Rh9V?AR4#kAj?Ah%o4EUPBPO1uIG1uRG'd1uZG606NP[%\|#\#\#\R|/|:#ig022f,}|#iPDP5PCPAg023c9Vc>R|9V?AR:#kAj?A|%o:EUPJPDP5PCPAg024`RC9Vc>R>9V?ARc#kAj?A>%ocEUPLP0g025]-0>Cg026[RCPPPOPN1pYG1pIG'd1pRG1pTGDaPbP2P0g027XR0P7g028UPoP;I0220107$00,~CCN=C61CMCMCMCM3{CMCMCM3{CMCMCMdo"). Qed.

Lemma e_itin :
  (s_pc (fst (fst e_r2pn)), snd (fst e_r2pn), log_win_b 0 (s_log (fst (fst e_r2pn)))) = (0x63334%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2pc)), snd (fst e_r2pc), log_win_b 0 (s_log (fst (fst e_r2pc)))) = (0x63334%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2tn)), snd (fst e_r2tn), log_win_b 0 (s_log (fst (fst e_r2tn)))) = (0x63334%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2tc)), snd (fst e_r2tc), log_win_b 0 (s_log (fst (fst e_r2tc)))) = (0x63334%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (let r := e_r2pc in
       (sr_mismatch (fn1_rvl (ELit 0x1588b8) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1p) (map (kmap (fn1_rvl (ELit 0x1588b8) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (ELit 0x1588b8) 0x1588b8 0x158cb8]))
  /\ (let r := e_r2pn in
       (sr_mismatch (fn1_rvl (ELit 0x1588b8) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1p) (map (kmap (fn1_rvl (ELit 0x1588b8) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (ELit 0x1588b8) 0x1588b8 0x158cb8]))
  /\ (let r := e_r2tc in
       (sr_mismatch (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1t) (map (kmap (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x1588b8 0x158cb8]))
  /\ (let r := e_r2tn in
       (sr_mismatch (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1t) (map (kmap (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x1588b8 0x158cb8]))
  /\ kn_vars_lt 114 p_kn3 = true /\ kn_acallT p_kn3 = e_kn1p /\ kn_vars_lt 114 tl1_kn3 = true /\ kn_acallT tl1_kn3 = e_kn1t.
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRun_defs ()) ["VP1"] "h01rp%0p&0p;1p;2p;4p;3p;5g0000j1uTg000Pj2fTg006Mj11Tg001Uj12Tg0024j1FTg003=j1OTg004Fj4yTg005Sj1oTg00=8j37Tg0072j4GTg0063j3:Tg00e:j3YTg0010j10Tg0099j3gTg00h[j2NTg012Ej3]Tg01J;k40DTg008[j19Tg00fEk207Tg00gPk206Tg00iek40BTg00k0k30@Tg00l;j2LTg00:Bj2BTg00:]j2[Tg00Ddj4qTg00;7j3KTg00;Tj1jTg00<[j3iTg00=Xj1kTg029Sj2hTg02:Zk10<Tg02;ck200Tg00CFj2}Tg00A4j2xTg00B:j2|Tg00mFj2{Tg01?6k105Tg011gj1pTg00?gk50:Tg00E?k409Tf0R0#0#0#0#1p=@%10#0#0#1p=R%10#0#1#0p=P%00#9p>04%20#2p=rg00FhR1f2R2f1R3P0CGp=a%00#1#0#1#1p=m%00#1#1#1p=D%00#0#0#9p=6g00HFR4?730p>03%20#2#2#2p>01%90#Op=?%00#0#1#0#0#1#1#1#1p=I%10#0#1#1p=<%00#1#1#0p=Vf3R5/N2?]30p=M%10#1#0#1p=_%10#1#0#0p=A%10#0#0#0p=4%10#1#1#1p=8%10#1#1#1#1#1#1#1p=\%10#1p>08%00#0#1#1p=>%00#0#0p=S%00#1#0#0p=5%00#0#0#0p=3%00#0p=w%00#0#1p=Q%00#1#0#1#1#0#0#0#0p=C%10#0p=v%00#1#0#1p=n%10#1#1#0p=E%00#0#1#0p==%00#0#0#0#0#0#0#0p=Z%00#0#0#0#0#0#0#9p=X%p0,N3p>0C%00#0#1#0#0p>0A%00#0#1#0#0#1#1p=H%10#9p=^%00#1#0#1#1#0#0p=U%93/L0p>0?A74309742p=l1L23=740p>02%02#9/L3=740p=t%02#9%03#0#0#9'L=740p=Wf4R6/N5?]23=740p=J1L651L23=740574p=s%06#9/L5%02#9/L3=740574p=c%03#9,L2=740p>0>A7430974297459746p=`%p5,N6?]23=740p=;%15#0#0#0#p,N6?]23=740p=TA]523=740p>0=f6f5P6P5P2P3P0CqCqp=bP3g00XoR5P0g02<`g00M=R6I0:p=~P4P4P0g02=\H09p=z%20#2#2#2#2#2#2#2p>0;%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=d1B30,B2p=eg00E[R2#uR3,f1R1g00GFR7'fR8P1P7g00KFR9#1#@#R#R#P$04R:g00KkR;g02>XR<%26R=#2R>#2R?#2R@#2RA#2RB#rRC#2RD#2RE#FRFg00M\RG#ORHCy%o2RI5725a3g00GfRJCGRK;:KRLP1P7PJP<PFPHCy=72I9a3:PJCGR:=:8:RIg00NlR2#uR<%u4RM'fRNP<PM%o29726R2%m9#@#@#D#6RO#ORP%m9#@#R#D#6RQ7YO%o4R4+03CGRR;:RRSP<PMP2g00PTR2%2ERE#2RT#r$01RU#FRV%09RW#?RX3gRY?YOQ0034CGRZ=:NZR[A:7JJR\PH%I9#<#V#6R]P@%1WR^#?CMS00%I9#<#<#6,NHS01?]CPPH%I9#<#P#6R_PC%OQCMS02PH%I9#<#_#6R`PCPPCMS03PH%I9#A#4#6RaP@%19Rb#1Rc#1Rd#8Re#\Rf$08#8Rg#1Rh#1#\#\#\#\#\#?RiCMS04PH%I9#<#8#6RjPC%@9#>#R#A#A#?CMS05%F6Rk%0^Rl#SRmPCP;P>PGPCH0DPk%0mR;#SPC%O]RnPk%0WRW#1Ro#1Rp#1Rq#1PC%@9#5#>#P#4#?Pk%0qRqPC%>9#5#<#<#?Pk%3qPCPnPk%0pRp#1PC%99Rn#ORqPHPOP=%0bRb#0Rr#wRs#?PH%I9#<#4#6PCPHCMS06PH%I9#<#D#6RtPCPHCMRuPH%I9#A#D#6RvP@PiCMRiPH%Q9#<#8#4#P$04RwP=PHCMRxPH%C9#5#5#6RyP@PqPH%C9#V#D#6RzPC%v9#>#n#V#4#?PH%C9#5#D#6R{PC%39#E#5#4#A#?PH%C9#5#n#6R|PC%C9#5#V#6R}#OPH%09#V#8#E#=#6R~P=PqPk%4rRrPC%2U#rRU#2Rq#FPk%0sRs#0PC%FUPk%1^R^PCPFPk%S^R^#0PC%FDPkPlPC%FTPkP;PC%FCPk%wpPC%FBRBPk%SoRo#0PCAg2BXPk%0WRWPC%v9#>#=#<#5#?%FE%9e7YG%0WRe#9RE-07k%Zf#Z#Z#X%0eRe#0Rf#w#3Rp#3R;#S#3RT#0#Z#Z#X5Yk20CkTRl%9TRT+06Pk%SdPCPHPk%ScRc#0PCPHPkPbPCPHPkPsPCPHPkP^PC%?e9g2kPkPmPC%v9#>#@#5#3#?PkPoPCPXPkPfPC%?WRW9g2kPkPcPC%39#_#8#=#3#?%m9#=#3#XRc%0h#8#E#Z#X5YB207BEPlPT1NBG%9;R;H0B&0A9#E#3#X,NH%Sr#X+06%H9#E#>#5%H9#E#>#AP]%H9#E#_#PPt%H9#E#E#5P_%H9#E#8#3P`%H9#E#8#4Pj%H9#8#ZPv%H9#8#@#EPa%H9#8#=#=%I9#_#4#6%H9#8#V#3#^%H9#8#4#5#^%Q9#<#8#4#5#^P~%Q9#<#8#4#4#^Pw%Q9#<#8#4#P#^%09#D#3#=#X%Q9#A#3#8#5%C9#>#8PH%09#D#3#=#@#6RwPC%OwPH%09#D#3#=#n#6P@%FARA%Q9#A#3#R#P%09#D#3#>#3%Q9#A#3#A#5%09#D#3#>#5%Q9#A#3#_#5%09#D#3#>#4%Q9#A#3#E#4%09#D#3#>#A%U9#@#3#4Py%U9#@#@#=P|P}P{%C9#5#4#6Pz%U9#@#P#3%C9#4#4#6Rz1NHz@0@W>%n9#4#5#5#4%C9#4#P#6+0?%U9#=#>#3#^%C9#4#_#6RWPHPWPC%F?%U9#=#>#4%C9#4#8%U9#=#5#5%C9#R#=#6R?PHP?PC%9pRp#O%U9#=#5#A%C9#R#R%U9#5#5#4%9g9YAn1LGp;l4:02Qc7tO3WDJ3t3WDJ4023l3tDsDc3W3W3W3WDJDJ3WDsDsDcDcDcDc60>;D`D;D;D;D;D;D;DTD;D;D`DTD;D;D;DTD;DTD;D;DJDJDJDJDJR;D`DJDTD;DTDTD;DT3lD`Rc=:McRQQ01PCPYQ00Px%m9#@#R#V#69YVOQ02Q03Q04Q05Q06Alui;D`D`H0=R;=:M;Ri,B\Ru'BRV'BRO,B[R9'BRx,BSRC'BR4,BIRp,BLRG'B1[8KRAPIPG1[8:RGPLPpPAPIP4PGPSPC1[NRRCPSPxPCP[P91[NZR9P[POP9P\PV1[7JRVPQPu1[McP\PiPV1[M;CqFbFbFbFbFbP1P7g00QlR;1f;3RVg00S:Rig02?JR\3KRc7K3Ru#jAi;3c5a3%ku,h6CG=:8KP1P7g02@FRu9KViRc9K;3RQ#jAi;3c5a3%kQ,h6CG=:8:P1P7g02ABRQ9KViRc9K;3R9#jAi;3c5a3%k9,h6CG=:8KP1P7g02B>R19KViRK9K;3R9#jAi;3K5a3%k9,h6CG=:8:Pu1fViRuP<PMAKVi09K;3$0<R;-00PRP/~;g02C:R3,}01xP5#z'|CG=:NRRRb0P\PuPRb0P1PuP<PM200Y;RY/~;g02D6R;,}01xY5#z'|CG=:NZRZb0PQPuPZb0&01q$0;#d#d#d#d#dRqg01hJRZ'{=:7J&05Z=:M3g026[R3,{q=:7J&053=:M;'B3e3e3e3e3edo"). Qed.

Lemma fn1_itin :
  (s_pc (fst (fst fn1_r1)), snd (fst fn1_r1), s_log (fst (fst fn1_r1))) = (0x10e818%Z, [], [])
  /\ (nth 1 fn1_sr1 (ELit 0), nth 10 fn1_sr1 (ELit 0), nth 2 fn1_sr1 (ELit 0), nth 4 fn1_sr1 (ELit 0))
     = (ELit 0x6333c, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x1381d0)
  /\ kn_vars_lt 40 fn1_kn1 = true /\ kn_acall fn1_kn1 = fn1_kn2i
  /\ (s_pc (fst (fst fn1_r2)), snd (fst fn1_r2), s_log (fst (fst fn1_r2))) = (0x10e4e0%Z, [], [])
  /\ (nth 10 fn1_sr2 (ELit 0), nth 2 fn1_sr2 (ELit 0), nth 4 fn1_sr2 (ELit 0)) = (ELit 0, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x1381d0).
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRun_defs ()) ["VP1"] "p&0p;1p;2p;4p;3g0000j1lTg000Pj2[Tg0010j10Tg005Sj1gTg0072j4ETg0063j3ATg001Uj1>Tg0024j1_Tg011gj1^Tg003=j1BTg0099j3cTg00e:j3aTg006Mj11Tg008[j17Tg00fEj2wTg00gPj2vTg00h[j2STg00iek400Tg00k0j3}Tg00l;j2KTg00:Bj2ITg00:]j2ZTg00Ddj4]Tg00;7j3bTg00;Tj1sTg00<[j3rTg00=Xj1qTg00mFj2{Tg01Ajj1zTg012Ej3kTg00=8j3CTg00DHj4oTf0R0#0#0#0#1p=<%10#1#0#1p=R%00#0#0#0p=3%00#0#1#1p=;%00#0#0#7p=2%10#0p=f%10#1#0#0p=4%70#Bp=Dg00OKR1P1f1R2P0CEp=df2R3P1P2P0CEp=Y%00#1#1#1p=:%10#0#1#0p=T%00#1#0#1#1p=j%10#0#0#1p=J%00#0#1#0#0#1#1#1#1p=F%10#0#1#1p=Gf3R4/S3?k20p=n%00#1#1#0p=X%00#0#1p=W%10#1#1#1p=8%10#0#0#0p=5%00#7p=y%10#1#1#1#1#1#1#1p=V%10#1p=x%00#1#0#1#1#0#0#0#0p=?%00#1#0#0p=6%00#1#0#1p=\%10#1#1#0p=@%00#0#1#0p==%00#0#0#0#0#0#0#0p=U%00#0#0#0#0#0#0#7p=N%00#0p=`%^0,S2p>01%00#0#1#0#0p=~%00#0#1#0#0#1#1p=H%00#1#0p=Q%72/K0p=|g00HFR5AC5207C3p=P1K32=C50p=uf4R6#0#7/K4%03#7/K2=C505C5p=M1S64?k32=C50p=9%03#7/K2=C50p=i1K641K32=C505C5p=h%02#7,K3=C50p=t%^4,S6?k32=C50p=LP1P2g02E2P0Cop=e%>0#>p=p%>0#>#>#>p=OP1P2g02EoP0Cop=mg00FhR0g00E[R2#lR3'[R6g014LR4#lR7'[R8P6P7P0P3g00KFR9#0#<#R#3#;#2%g2R2CE%g4R4CER:;A:1[11R;/[1R</[1R1%f9#;#;#;#4#Dg00M=R=#>R>#>R?#>R@#>RA#>RB#>RC#_RD'dg00PTRE%_=R=%09RF#0RG#0RH#0RI#0RJ#0RK#0RL#^#B3c5Y;%09#:#3#;#T#2RM#BRN5Y<RO;AORPg00GFRQg00GfRR;ARRS%l5RT%>CRC#_RU%j9#<#<#:#2RV%j9#<#J#:#2RW3ag00M\RX#BRY%F9#G#G#2%>CRCPUCnPY%F9#G#X#2RUPA%1FRZ#DPY%W9#G#8#5#T#yR[P>PYPY%F9#G#T#2R\PC%BWPY%F9#G#R#2R]PC%BVPY%F9#4#5#2R^PA%19R_#1R`#1Ra#8#VRb#x#8Rc#1Rd#1#V#V#V#V#V#DRePY%F9#G#8#2RfPC%<9#;#J#4#4#DPY%F9#G#5#2PCPYPY%F9#G#:#2RgPCPYPY%F9#4#:#2RhPAPePY%?9#6#6#2RePA%79Ri#BRjPY%?9#X#:#2RkPC%f9#;#\#X#5#DPY%?9#6#:#2RlPC%39#@#6#5#4#DPY%?9#6#\#2RmPC%?9#6#X#2Rn#BPY%09#X#8#@#=#2RoP>Pj%7IRI,w=%Ub#U#U#N%0L#3RL#3Rb#0#`#3Rj#0#U#U#N5a=201=jRp%7jRj'vP=%0a#`#^PCPYCnP=%0`#`R`#0PCPYP=%0_R_#5PCPYP=%0_R_#`Ra#0PCPYP=%5ZPC%DJ9cE=P=%3ZPC%f9#;#<#6#3#DP=%5GPC%DFP=PKPC%DHRH9cE=P=P`PC%39#R#8#=#3#D%j9#=#3#NR`%0d#8#@#U#N5aD1wDIPpPj1SDX%7bRbH00%~9#@#3#N,SY%1_#`#3#N'v%H9#@#;#6%H9#@#;#4PU%H9#@#R#TPg%H9#@#@#6P\%H9#@#8#3P]%H9#@#8#5Pf%H9#8#UPh%H9#8#<#@P^%H9#8#=#=%F9#R#5#2%=9#:#@#4#<#7%=9#:#8#3#J#7%;9#:#8#3#J#7Po%;9#:#8#<#<#7P[%;9#:#8#<#\#7%09#:#3#=#N%W9#4#3#8#6%?9#;#8#2PY%09#:#3#=#<#2R[PC%B[PY%09#:#3#=#\#2PA%_BRB%W9#4#3#J#T%09#:#3#;#N%W9#4#3#4#6%09#:#3#;#6#2%W9#4#3#R#6%09#:#3#;#5#2%W9#4#3#8#3%Q9#4#<#3#5Pe%Q9#4#<#<#=PmPnPl%?9#6#5#2Pk%Q9#4#<#T#3%?9#5#5#2Rk1SYk?}H?%\9#5#6#6#5%?9#5#T#2'|%\9#5#6#X#<#7%?9#5#R#2RHPYPHPC%_@%Q9#4#=#;#5%?9#5#8#2%Q9#4#=#6#6%?9#J#=#2R@PYP@PC%7LRL#B%Q9#4#=#6#4%?9#J#J#2%Q9#4#6#6#5PV%7c9aBi1KXL%g53P9uW`DMD9DMD93u3P3iDhDM5tM3iDMD9D93iDhDhDMDMDMDM5tb3P3PDLDLDLDLDLDLDLDL3P3PD9D9D9D9D9D9D9D9D9D9D9D9D9D93PRb;AbRMP6P7P0P3%09#<#4#J#4#2P2CEP4CER4=A84R2%^a#B9cE=,dY=Y;NRN=A<NR='IRE'IRa'IR9'I1Z8:PPP91Z1OPSPa1ZQRPMPE1ZTbP2P=1Z841Z<NC]C]C]C]C]P6P7P0P3g00QlR=1[=3R2g00S:Rbg02Fl3bRE7b3RM#sAr=3ECE%qMCE=A8:1e>Y%pCRC/eY'd1e?Y5Y;1eAY5Y<=A1O%pC#O#O#O#O#O#O#Og02GhRO'{=AQR%zOg02He5ATP6P7P0P3g02Ic9b2bRb9b=3R2#sAr=3bCE%q2CE=A841mCY1m?Y'd1mAY5Y;=A<N'I'I'I'I'Ido"). Qed.
End VP1.

(* [comment removed for export] *)
Definition sr_FE : list expr :=
  [ELit 0; ELit 0x63508; spx (-208); ELit 0x10800; ELit 0x1381d0; JL 5; JL 6; JL 7;
   EVar 9; EVar 14; EVar 15; JL 11; JL 12; JL 13; JL 14; JL 15;
   JL 16; JL 17; EVar 15; ELit 18446744073709551615; ELit 0x137f10; ELit 0; ELit 0; ELit 18446744073709551614;
   JL 24; JL 25; JL 26; JL 27; JL 28; JL 29; JL 30; JL 31].
Definition kn_FE : list kentry := kn_TL1.
Definition fe_rvlp : list expr :=
  slots2 (EVar 21) (EVar 22) (rvl18w (EVar 13) (EVar 14) (EVar 15) (EVar 16) (nth 19 p_sr3e (ELit 0)) (ELit 0x1588b8) p_sr3e).
Definition fe_rvlt : list expr :=
  slots2 (EVar 21) (EVar 22) (rvl18w (EVar 13) (EVar 14) (EVar 15) (EVar 16) (nth 19 tl1_sr3e (ELit 0)) (EAlu ALU_ADD (EVar 18) (ELit 2)) tl1_sr3e).
Definition fe_sr1i : list expr := Eval vm_compute in sr_after_call_j sr_FE KEPT_AL 50.
Definition fe_kn1i : list kentry := Eval vm_compute in kn_acallT kn_FE.
Definition fe_r2n := Eval vm_compute in runT (SCR [false] [] []) (SS 0x63508 fe_sr1i [] fe_kn1i 82).
Definition fe_r2c := Eval vm_compute in runT (SCR [true] [] []) (SS 0x63508 fe_sr1i [] fe_kn1i 82).

Section VP2.
Lemma fe_itin :
  (sr_mismatch fe_rvlp idb p_sr3e sr_FE 0, kn_missing p_kn3 (map (kmap fe_rvlp idb) kn_FE)) = ([0; 21]%nat, [KRange (ELit 0x1588b8) 0x1588b8 0x158cb0])
  /\ (sr_mismatch fe_rvlt idb tl1_sr3e sr_FE 0, kn_missing tl1_kn3 (map (kmap fe_rvlt idb) kn_FE)) = ([0; 21]%nat, [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x1588b8 0x158cb0])
  /\ kn_vars_lt 50 kn_FE = true /\ kn_acallT kn_FE = fe_kn1i
  /\ (s_pc (fst (fst fe_r2n)), snd (fst fe_r2n), log_win_b 0 (s_log (fst (fst fe_r2n)))) = (0x63334%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst fe_r2c)), snd (fst fe_r2c), log_win_b 0 (s_log (fst (fst fe_r2c)))) = (0x63334%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (let r := fe_r2n in
       (sr_mismatch (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r fe_kn1i) (map (kmap (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], []))
  /\ (let r := fe_r2c in
       (sr_mismatch (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r fe_kn1i) (map (kmap (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], []))
  /\ nth 19 p_sr3e (ELit 0) = ELit 18446744073709551615 /\ nth 19 tl1_sr3e (ELit 0) = ELit 18446744073709551615   (* [comment removed for export] *)
  /\ tl1_sr1 = tl_sr1 /\ tl1_sr2i = tl_sr2i.
Proof.
ltac2:(KReplay.run1 (kr_t_V23TRun_defs ()) ["VP2"] "h01rp&0p;1p;2p;3p;4p;5g0000j1iTg000Pj2fTg001Uj12Tg005Sj1jTg00=8j36Tg003=j1HTg00e:j3\Tg0072j4BTg0063j3GTg0024j15Tg0010j10Tg0099j3dTg006Mj11Tg008[j18Tg00fEk201Tg00gPk200Tg00h[j2ZTg00iek40@Tg00k0k30>Tg00l;j2PTg004Fj4|Tg00:Bj2ETg00:]j2JTg00Ddj4nTg00?gj5mTg00A4j2pTg00B:j2lTg00mFk209Tg01?6k108Tg00;7j3^Tg00;Tj1yTg00<[j3xTg00=Xj1wTg029Sj2vTg02:Zk106Tg02;ck205Tg00CFk207Tg00E?j4uTg00DHj4{Tg012Ej3kTg011gj1sTf0R0#2#2p=e%00#1#0#1#1p=h%00#0#0#1p=@%00#1#1#1p=;%00#0#0#8p=3%10#0#0#1p=I%00#1#1#0p=]g00HFR1f1R2;60p>02%80#Hp=b%00#0#1#0#0#1#1#1#1p=K%10#0#1#1p=Mf3R3f2R4'Z?k20p>0:%10#0#1#0p=L%10#1#0#1p=T%10#1#0#0p=9%10#0#0#0p=4%10#1#1#1p=<%10#1#1#1#1#1#1#1p=`%10#1p>04%00#0p=g%00#1#0#0p=:%10#1#1#0p=D%00#0#1#1p=?%00#0#8#Hp=Q%00#0#1p=_%00#8p=t%00#1#0#1#1#0#0#0#0p=C%00#1#0#1p=[%00#0#1#0p=A%00#0#0p=W%00#0#0#0#0#0#0#0p=V%00#0#0#0#0#0#0#8p=U%00#0#0#0p=7%s0,Z2p>0A%00#0#1#0#0p>0?%00#0#1#0#0#1#1p=N%00#1#0p=Y%82/P0p>0=A61209614p=X1P42=610p=~f4R5#0#8/P3%04#8/P2=610561p=R1Z53?k42=610p=>%04#8/P2=610p=r1P531P42=610561p=q%02#8,P4=610p=}%s3,Z5?k42=610p==%00#sp>0<%10#0p>0;%20#2#2#2p=ag00OKR6%54%52=66036p=FA66209664p=oA6620966496639665p=Sf6f5P5P3P4P2P0CnCnp=cP1P1P0g02J_R5Cup=zAG342/E0p=O1E20,E4p>03g00NlR4#iR2%i1R3'fR7P2P3g00M=R8%28R9#2R:#2R;#2R<#2R=#2R>#eR?#2R@#2RA#2RB#2RC#eRD#2RE#2RF#2RG#2RH#2RI#eRJ%j4RK564564RLg00KFRM#h#@#@#;#3RN#HRO%hM#@#I#]#3RP7\N%j1RQ+02CBRR;GRP2P3PLg00PTRL%5HRH%0MRS#bRT3d?\NP002QCBRU=G7URVg00GFRWg00GfRX;GXRYA\HNPg00M\RP#HRZ%KM#M#]#3R[P<%1SR\#bH0:PZ%KM#M#M#3P?PHPZ%KM#M#L#3R]P?%hM#@#I#;#3R^#HPZ%KM#M#T#3R_P?POPZ%KM#9#4#3ROP<%1MR`#1Ra#1Rb#<Rc#`Rd$04#<Re#1Rf#`#`#`#`#`Rg#1#bRhPZ%KM#M#<#3RiP?%gM#:#D#;#?#QPZ%KM#M#4#3P?PZPZ%KM#M#;#3RjP?PZPZ%KM#9#;#3RkP<PhPZ%_M#M#<#4#L#tRlP9PZPZ%CM#:#:#3RmP<%8MRn#HRoPZ%CM#]#;#3RpP?%4M#T#[#L#QPZ%CM#:#;#3RqP?%gM#?#I#A#?#QPZ%CM#:#[#3RrP?%CM#:#]#3Rs#HPZ%0M#]#<#D#A#3RtP9Po%58Ro%0`R`#0R9#4RuP?%2JRv#5Po%W9R9#0P?%5JPo%1\RJ#4P?%5ARAPo%WJRJ#0P?%5@R@Po%0\R\#4P?%5CPo%W\R\#0P?%5?Po%0SRS#1RC#4P?%5>R>Po%WCRC#0P?AdL>TPo%0SRS#4P?%4M#9#L#T#Q%5B%8c7\P%0SRc#8RB-01o%Vd#V#V#U%0cRd#0Rw#g#7Rx#7Ry#W#7Rz#0#V#V#U5\o20AozR{%8zRz+00Po%WbP?PZPo%WaRa#0P?PZPo%4`R`P?PZPoP9P?PZPoPJP?%bd9dLoPoP\P?%4M#9#[#7#QPoPCP?PTPoPwP?%bSRS9dLoPoPaP?%gM#?#;#9#4#Q%hM#A#7#URa%0f#<#D#V#U5\>201>BP{Pz1Z>P%8yRyH0@&0?M#D#7#U,ZZ%Wu#U+00%NM#D#?#:%NM#D#?#9P[%NM#D#T#LPj%NM#D#D#:P]%NM#D#<#7P_%NM#D#<#4Pi%NM#<#VPk%NM#<#@#DPO%NM#<#A#A%KM#T#4#3%AM#;#D#9#@#8%AM#;#<#7#I#8%?M#;#<#7#I#8Pt%?M#;#<#@#@#8Pl%?M#;#<#@#[#8%0M#;#7#A#U%_M#9#7#<#:%CM#?#<#3PZ%0M#;#7#A#@#3RlP?%HlPZ%0M#;#7#A#[#3P<%5=R=%_M#9#7#I#L%0M#;#7#?#U%_M#9#7#9#:%0M#;#7#?#:#3%_M#9#7#T#:%0M#;#7#?#4#3%0M#;#7#?#L#3R<%_M#9#7#<#7%YM#9#@#7#4Pm%YM#9#@#@#APrPsPq%CM#:#4#3Pp%YM#9#@#L#7%CM#4#4#3Rp1ZZp@0>S:%[M#4#:#:#4%CM#4#L#3+0=%[M#4#:#]#@#8%CM#4#T#3RSPZPSP?%5;%YM#9#A#?#4%CM#4#<#3%YM#9#A#:#:%CM#I#A#3R;PZP;P?%8xRx#H%YM#9#A#:#9%CM#I#I#3%YM#9#:#:#4PN%8e9\=n1PPx;XQ9~^aDRD>DRD>3~3X3rDqDR3}3rDRD>D>3rDqDqDRDRDRDR5}y3X3XD=D=D=D=D=D=D=D=D=3X3XD=D=D=D=D=D=D=D=D=D>D>D>D>D>D>D>D>D>D>D>D>D>D>3XRy=G3yRag00FhR^g00E[Rx#iRP'fR=/fWRnP=PWP^PP%1M#@#I#I#L#tReg00Kkg02>XRNPAPZC|%jxR?56xCBPXCBR;;G;RSP=PWP^PPPePXPNPAPZC|=6x?CBPXCBR?=Gn?RxP2P3A648KPQCBRQ=G7QRKAG6hhR4%i6RAPZ%4M#T#?#;#Q&0<`#H9dLoRo&0;c#V#QRc%H<R<%2vRv#5%2vRv%2vRvP@%5DRDPDP@%2v#aRv%2vRv%2vRv%2vRv%2vRv%2vRv%5ERE%5GRG%HtRt%5FRFPZ%0g#bRg%2v#e#aRv#5RL%2vRv#5R`%2vRv#5RM%2vRv#5RN%2vRv%2vRv%2vRv%2vRv%j6Re3F3F3oDSDS3F3F3FDS3F3oDSR:;G:Rp%2vRv%2vRqPoPcP<%aqRq#5%2qRq%2qRqP@PDPZ%aqRq#5%2qRq%2qRq%2qRq%2qRq%2qRq%2qRqPEPGPtPFPZPgPLP`%2q#e#a#aRq%2qRq%2qRq%2q;Fe3F9oMNDSDS3F3F3FDS3FDS3FRN=GANRM'ERe,E4Rq'ER`,EKRL'ERg'ERF'ERt'ERG'ERE'E1J7RPVPE1J7UPYPG1JWXPaPt1J3yPSPF1Jn;PxPg1Jn?PKPL1J7QRLPKP`PLP4Pq1J6hRqP4PePqPpPM1JA:1JANCnFcFcFcFcFcP7P2P3g02KZRNg00XoR:g01YHRMg02LWRpP8Dmg01hJ1pN:#z'lCBPRP7P2P3g02MRRRP:g01l;RNPpP8Dmg026[1pR:#z'lCBPUPW209v5PXP3&085g02NOR5PnP=PWP^PPg00QlRX1fXPRvg00S:RUg02OLRR3^Rp7^PRq#yAxXPpCB%wq,v8CBP;PnP=PWP^PPg02PHR^9^vURW9^XPR=#yAxXPWCB%w=,v8CBP?PR1fvURRP2P3A^vU09^XP$06RX-05HRHP:PXg02<`P8Dm20705P1P11pH:g02=\Cu'lCB=G7QRQb0P^PRPQb0P6P6PIPMPZC{PhP6P6PIPNPZC{PhPAg01jAg01WQg02QDg02RB5GACOCOCO403COCOCOCOCOCOdo"). Qed.
End VP2.
