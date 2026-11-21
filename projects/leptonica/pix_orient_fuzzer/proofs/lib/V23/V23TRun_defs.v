(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of tm_itin, tn_itin, fn_itin, tl_itin, tl1_itin, e_itin, fn1_itin and fe_itin, made over the old 8 MiB launch stack window, replaced by vm_compute proofs). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall LibKnowFrame LibKnowXfer.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MainEntry V23LibStdioCall V23OpenFail_defs V23Open_defs V23Oom_defs V23DirRead_defs V23ReadLoop_defs V23Hdr_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_V23TRun_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4prod01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4list02C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_wdl_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK47Corelib4Init5Logic3and01C47Corelib5Lists7ListDef3mapI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs4kn_TC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5kn_TLC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I47Corelib4Init9Datatypes3nat00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5t_r1aC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5t_r1cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5t_r1bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5t_r1dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tm_rvlaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6t_sr1aC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5sr_TMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5t_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tm_rvlcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6t_sr1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23Hdr_defs4kn_RC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl_rvlbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6t_sr1bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5sr_TLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl_rvldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6t_sr1dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7calls_xC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6tm_sr2C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5tm_r2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6tm_kn2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tm_sr3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23@V23OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tm_kn3iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5tm_r3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl_rvlmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6tm_sr3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6tm_kn3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs9kn_acallTC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib3V23<V23TRun_defs7tn_kn1iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23Oom_defs8kn_acallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6fn_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6fn_sr2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5fn_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6fn_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7fn_kn2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5fn_r2C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs8kn_fcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6tl_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5p_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6p_sr3eC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5tl_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6tl_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl_kn2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5tl_r2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs4p_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs4p_r2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V238V23Reloc9v23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3V23;V23RelocImg8v23_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5p_sr2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5p_kn2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs4p_scC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5p_r3lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5p_r3eC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6p_kn3iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5p_kn3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6kn_TL1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl1_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl1_sr2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs8tl1_sr3eC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs8tl1_rvl0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6p_sr3lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6tl1_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl1_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs8tl1_kn2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6tl1_r2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl1_kn2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl1_r3lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl1_r3eC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs8tl1_kn3iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl1_kn3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl1_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs8tl1_sr3lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7fn1_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6sr_FN1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6kn_FN1C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c59OSSVerify5KrLib3V23<V23TRun_defs6e_r2pnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6e_r2pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6e_r2tnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6e_r2tcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6e_kn1pC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6e_kn1tC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7fn1_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7fn1_sr2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6fn1_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7fn1_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs8fn1_kn2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6fn1_r2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5kn_FEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7fe_rvlpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs5sr_FEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7fe_rvltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7fe_kn1iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6fe_r2nC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs6fe_r2cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs8tl1_sr2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3V23<V23TRun_defs7tl_sr2iC1?~~~~~~~~~~~~~~~".
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
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma tn_itin :   (* [comment removed for export] *)
  True /\ True /\ True /\ True
  /\ kn_acallT kn_T = tn_kn1i.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma fn_itin :
  (s_pc (fst (fst fn_r1)), snd (fst fn_r1), s_log (fst (fst fn_r1))) = (0x10e818%Z, [], [])
  /\ (nth 1 fn_sr1 (ELit 0), nth 10 fn_sr1 (ELit 0), nth 2 fn_sr1 (ELit 0), nth 4 fn_sr1 (ELit 0))
     = (ELit 0x6333c, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x1381d0)
  /\ kn_vars_lt 40 fn_kn1 = true /\ kn_acall fn_kn1 = fn_kn2i
  /\ (s_pc (fst (fst fn_r2)), snd (fst fn_r2), s_log (fst (fst fn_r2))) = (0x10e4e0%Z, [], [])
  /\ (nth 10 fn_sr2 (ELit 0), nth 2 fn_sr2 (ELit 0), nth 4 fn_sr2 (ELit 0)) = (EVar 7, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x1381d0).
Proof. vm_compute. repeat split; reflexivity. Qed.

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
Proof. vm_compute. repeat split; reflexivity. Qed.

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
Proof. vm_compute. repeat split; reflexivity. Qed.

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
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma fn1_itin :
  (s_pc (fst (fst fn1_r1)), snd (fst fn1_r1), s_log (fst (fst fn1_r1))) = (0x10e818%Z, [], [])
  /\ (nth 1 fn1_sr1 (ELit 0), nth 10 fn1_sr1 (ELit 0), nth 2 fn1_sr1 (ELit 0), nth 4 fn1_sr1 (ELit 0))
     = (ELit 0x6333c, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x1381d0)
  /\ kn_vars_lt 40 fn1_kn1 = true /\ kn_acall fn1_kn1 = fn1_kn2i
  /\ (s_pc (fst (fst fn1_r2)), snd (fst fn1_r2), s_log (fst (fst fn1_r2))) = (0x10e4e0%Z, [], [])
  /\ (nth 10 fn1_sr2 (ELit 0), nth 2 fn1_sr2 (ELit 0), nth 4 fn1_sr2 (ELit 0)) = (ELit 0, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x1381d0).
Proof. vm_compute. repeat split; reflexivity. Qed.
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
Proof. vm_compute. repeat split; reflexivity. Qed.
End VP2.
