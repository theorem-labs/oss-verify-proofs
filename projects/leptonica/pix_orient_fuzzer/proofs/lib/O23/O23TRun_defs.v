(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall LibKnowFrame LibKnowXfer.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MainEntry O23LibStdioCall O23OpenFail_defs O23Open_defs O23Oom_defs O23DirRead_defs O23ReadLoop_defs O23Hdr_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23TRun_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes3nat02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4prod01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4list02C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_wdl_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer;sr_mismatchC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer4kmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver;LibKnowXfer:kn_missingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs8kn_afterC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK47Corelib4Init5Logic3and01C47Corelib5Lists7ListDef3mapI79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs4kn_TC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5kn_TLC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I47Corelib4Init9Datatypes3nat00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5t_r1aC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5t_r1cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5t_r1bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5t_r1dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tm_rvlaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23ReadLoop_defs3idbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6t_sr1aC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5sr_TMC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5t_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tm_rvlcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6t_sr1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23Hdr_defs4kn_RC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl_rvlbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6t_sr1bC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5sr_TLC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl_rvldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6t_sr1dC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7calls_xC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver8SymDrive?sr_after_call_jC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall7kn_callC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6tm_sr2C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5tm_r2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6tm_kn2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs7KEPT_MCC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tm_sr3iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23@O23OpenFail_defs3IHIC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tm_kn3iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5tm_r3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl_rvlmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6tm_sr3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6tm_kn3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs9kn_acallTC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c59OSSVerify5KrLib3O23<O23TRun_defs7tn_kn1iC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23Oom_defs8kn_acallC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6fn_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6fn_sr2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5fn_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6fn_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7fn_kn2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5fn_r2C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs8kn_fcallC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall:stdio_callC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall6sc_retC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_fC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_fdC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall4sc_lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl<LibStdioCall5sc_wpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6tl_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5p_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6p_sr3eC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl<LibStdioCall9stdio_res00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5tl_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6tl_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl_kn2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5tl_r2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs4p_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs4p_r2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O238O23Reloc9o23_relocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O23;O23RelocImg8o23_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5p_sr2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5p_kn2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs4p_scC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5p_r3lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5p_r3eC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6p_kn3iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5p_kn3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6kn_TL1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl1_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl1_sr2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs8tl1_sr3eC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs8tl1_rvl0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6p_sr3lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6tl1_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl1_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs8tl1_kn2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6tl1_r2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl1_kn2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl1_r3lC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl1_r3eC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs8tl1_kn3iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl1_kn3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl1_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs8tl1_sr3lC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9CliDriver7SymCall9log_win_bC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7fn1_rvlC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6sr_FN1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6kn_FN1C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c59OSSVerify5KrLib3O23<O23TRun_defs6e_r2pnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6e_r2pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6e_r2tnC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6e_r2tcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6e_kn1pC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6e_kn1tC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7fn1_sr1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7fn1_sr2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6fn1_r1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7fn1_kn1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs8fn1_kn2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6fn1_r2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5kn_FEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7fe_rvlpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs5sr_FEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7fe_rvltC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7fe_kn1iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6fe_r2nC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs6fe_r2cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs8tl1_sr2iC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23<O23TRun_defs7tl_sr2iC1?~~~~~~~~~~~~~~~".
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation RSEGS := Plain.M.loaded_segments.

Definition STOPST : list Z := (0x62ea4 :: 0x62f74 :: 0x62d10 :: STOPS2)%Z.
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPST scr ss [].
(* [comment removed for export] *)
Definition STOPSP : list Z := [0xff528; 0x62ea4; 0x62d10; 0xfa374]%Z.
Definition runP (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSP scr ss [].

(* [comment removed for export] *)
Definition t_ss1 := SS 0x62dec sr_R [] kn_R 45.
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
  | KImg 0x10000 0x113a10 => [KImg 0x10000 0x1137c0; KImg 0x1137d0 0x113a10]
  | KImg 0x1443e0 0x145000 => [KImg 0x1443e0 0x144408; KImg 0x144808 0x145000]
  | KImg 0x123a61 0x123a90 => [KImg 0x123a61 0x123a64; KImg 0x123a65 0x123a90]   (* [comment removed for export] *)
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
  [ELit 0; ELit 0x62e50; spx (-208); ELit 0x10800; ELit 0x123d20; JM 5; JM 6; JM 7;
   EVar 9; EVar 12; EVar 9; JM 11; JM 12; JM 13; JM 14; JM 15;
   JM 16; JM 17; JM 18; JM 19; ELit 0x123a60; EVar 13; JM 22; JM 23;
   JM 24; JM 25; JM 26; JM 27; JM 28; JM 29; JM 30; JM 31].
Definition rvl13 (ecalls : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; ecalls] ++ (ELit 0 :: tl sr).
Definition tm_rvla : list expr := rvl13 calls_x t_sr1a.
Definition tm_rvlc : list expr := rvl13 (ELit 1) t_sr1c.
(* [comment removed for export] *)
Definition kn_acallT (kn : list kentry) : list kentry := kn_call GLOB (-208 - 1024) (-208) IHI 0x113000 kn.
(* [comment removed for export] *)
Definition tm_srM : list expr := sr_after_call_j sr_TM KEPT_AL 46.
Definition tm_knM : list kentry := Eval vm_compute in KRange (EVar 56) 0x1000 0x7fffff800000 :: kn_acallT kn_T.
Definition tm_r2 := Eval vm_compute in runT scr0 (SS 0x62e50 tm_srM [] tm_knM 78).
Definition tm_sr2 := Eval vm_compute in s_regs (fst (fst tm_r2)).
Definition tm_kn2 := Eval vm_compute in kn_after tm_r2 tm_knM.
(* [comment removed for export] *)
Definition tm_sr3i := Eval vm_compute in sr_after_call_j tm_sr2 KEPT_MC 78.
Definition tm_kn3i := Eval vm_compute in kn_call [(0x1000, 0x10000)%Z] 0 0 IHI 0x113000 tm_kn2.
Definition tm_r3 := Eval vm_compute in runT scr0 (SS 0x62e64 tm_sr3i [] tm_kn3i 110).
Definition tm_sr3 := Eval vm_compute in s_regs (fst (fst tm_r3)).
Definition tm_kn3 := Eval vm_compute in kn_after tm_r3 tm_kn3i.
(* [comment removed for export] *)
Definition tn_sr1i := sr_upd tm_srM (ridx 10) (ELit 0).
Definition tn_kn1i : list kentry := Eval vm_compute in kn_acallT kn_T.
Definition tn_r1n := Eval vm_compute in runT (SCR [false] [] []) (SS 0x62e50 tn_sr1i [] tn_kn1i 78).  (* [comment removed for export] *)
Definition tn_r1c := Eval vm_compute in runT (SCR [true] [] []) (SS 0x62e50 tn_sr1i [] tn_kn1i 78).   (* [comment removed for export] *)
Definition tn_sr1n := Eval vm_compute in s_regs (fst (fst tn_r1n)).
Definition tn_sr1c := Eval vm_compute in s_regs (fst (fst tn_r1c)).
Definition tn_kn1 := Eval vm_compute in kn_after tn_r1n tn_kn1i.

(* [comment removed for export] *)
Definition JN (i : nat) : expr := EVar (8 + i).
Definition sr_FN : list expr :=
  [ELit 0; JN 1; spx (-128); ELit 0x10800; ELit 0x123d20; JN 5; JN 6; JN 7;
   EVar 7; EVar 6; JN 10; JN 11; JN 12; JN 13; JN 14; JN 15;
   JN 16; JN 17; JN 18; JN 19; JN 20; JN 21; JN 22; JN 23;
   JN 24; JN 25; JN 26; JN 27; JN 28; JN 29; JN 30; JN 31].
Definition kn_FN : list kentry := Eval vm_compute in List.filter (kentry_vars_lt 7) tn_kn1.
Definition fn_rvln : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ELit 2] ++ (ELit 0 :: tl tn_sr1n).
Definition fn_rvlc : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ELit 0] ++ (ELit 0 :: tl tn_sr1c).
Definition fn_r1 := Eval vm_compute in runT scr0 (SS 0x62d10 sr_FN [] kn_FN 40).
Definition fn_sr1 := Eval vm_compute in s_regs (fst (fst fn_r1)).
Definition fn_kn1 := Eval vm_compute in kn_after fn_r1 kn_FN.
Definition fn_sr2i := Eval vm_compute in sr_after_call_j fn_sr1 KEPT_AL 40.
Definition fn_kn2i := Eval vm_compute in kn_acall fn_kn1.
Definition fn_r2 := Eval vm_compute in runT scr0 (SS 0x62d18 fn_sr2i [] fn_kn2i 72).
Definition fn_sr2 := Eval vm_compute in s_regs (fst (fst fn_r2)).
Definition fn_kn2 := Eval vm_compute in kn_after fn_r2 fn_kn2i.

(* [comment removed for export] *)
Definition keepTL (K : kentry) : bool :=
  match K with KWord (SA (EVar 6) _) _ _ => false | KWr (SA (EVar 6) _) _ => false | _ => true end.
Definition kn_TL : list kentry := Eval vm_compute in map fixTL (List.filter keepTL kn_T).
Definition JL (i : nat) : expr := EVar (18 + i).
Definition sr_TL : list expr :=
  [ELit 0; JL 1; spx (-208); ELit 0x10800; ELit 0x123d20; JL 5; JL 6; JL 7;
   EVar 9; EVar 14; JL 10; JL 11; JL 12; JL 13; JL 14; JL 15;
   JL 16; JL 17; EVar 15; EVar 17; ELit 0x123a60; EVar 16; ELit 0; ELit 18446744073709551614;
   JL 24; JL 25; JL 26; JL 27; JL 28; JL 29; JL 30; JL 31].
Definition rvl18 (e13 e14 e15 e16 e17 : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; e13; e14; e15; e16; e17] ++ (ELit 0 :: tl sr).
Definition tl_rvlb : list expr := slots2 (EVar 35) (EVar 36) (rvl18 calls_x (ELit 0x123a70) (ELit 0) calls_x (nth 19 t_sr1b (ELit 0)) t_sr1b).
Definition tl_rvld : list expr := slots2 (EVar 35) (EVar 36) (rvl18 (ELit 1) (ELit 0x123a70) (ELit 0) (ELit 1) (nth 19 t_sr1d (ELit 0)) t_sr1d).
Definition tl_rvlm : list expr := slots2 (EVar 36) (EVar 37) (rvl18 (EVar 13) (EVar 56) (EVar 56) (EVar 13) (nth 19 tm_sr3 (ELit 0)) tm_sr3).
(* [comment removed for export] *)
Definition tl_r1 := Eval vm_compute in runT scr0 (SS 0x62ea4 sr_TL [] kn_TL 50).
Definition tl_sr1 := Eval vm_compute in s_regs (fst (fst tl_r1)).
Definition tl_kn1 := Eval vm_compute in kn_after tl_r1 kn_TL.
(* [comment removed for export] *)
Definition LGLOB : list (Z * Z) := ((0x1137c0, 0x1137c8) :: GLOB)%Z.
Definition kn_fcall (kn : list kentry) : list kentry := kn_call LGLOB (-208 - 16384) (-208) IHI 0x113000 kn.
(* [comment removed for export] *)
Definition tl_sr2i : list expr := Eval vm_compute in sr_upd (sr_after_call_j tl_sr1 KEPT_AL 50) (ridx 10) (ELit 0).
Definition tl_kn2i : list kentry := Eval vm_compute in kn_fcall tl_kn1.
Definition tl_r2 := Eval vm_compute in runT scr0 (SS 0x62eb8 tl_sr2i [] tl_kn2i 82).
Definition tl_sr2 := Eval vm_compute in s_regs (fst (fst tl_r2)).
Definition tl_kn2 := Eval vm_compute in kn_after tl_r2 tl_kn2i.
(* [comment removed for export] *)
Definition p_r1 := Eval vm_compute in runP scr0 (SS 0x62f74 tl_sr2 [] tl_kn2 82).
Definition p_sr1 := Eval vm_compute in s_regs (fst (fst p_r1)).
Definition p_kn1 := Eval vm_compute in kn_after p_r1 tl_kn2.
(* [comment removed for export] *)
Definition p_r2 := Eval vm_compute in runP scr0 (SS 0x1005d4 (sr_upd p_sr1 (ridx 10) (ELit (2^64 - 25))) [] p_kn1 82).
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
  | KWord (SA (ELit 0) 1328136) _ _ => false
  | KWord (SA (ELit 0) _) _ _ => true
  | KWord _ _ _ => false
  | _ => true
  end end.
Definition fixw (K : kentry) : kentry :=
  match K with KWord (SA (ELit 0) 1128736) 8 _ => KWord (SA (ELit 0) 1128736) 8 (EVar 18) | _ => K end.
Definition kn_TL1 : list kentry := Eval vm_compute in KRange (EVar 18) 0x144408 0x144800 :: map fixw (List.filter keepTL1 p_kn3).
(* [comment removed for export] *)
Definition rvl18w (e13 e14 e15 e16 e17 ew : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; e13; e14; e15; e16; e17; ew] ++ tl sr.
Definition tl1_rvl0 : list expr :=      (* [comment removed for export] *)
  slots2 (EVar 21) (EVar 22) (rvl18w (EVar 13) (EVar 14) (EVar 15) (EAluw ALU_ADD (EVar 16) (ELit (-1))) (nth 19 p_sr3l (ELit 0)) (ELit 0x144408) p_sr3l).
(* [comment removed for export] *)
Definition tl1_r1 := Eval vm_compute in runT scr0 (SS 0x62ea4 sr_TL [] kn_TL1 50).
Definition tl1_sr1 := Eval vm_compute in s_regs (fst (fst tl1_r1)).
Definition tl1_kn1 := Eval vm_compute in kn_after tl1_r1 kn_TL1.
Definition tl1_sr2i : list expr := Eval vm_compute in sr_upd (sr_after_call_j tl1_sr1 KEPT_AL 50) (ridx 10) (ELit 0).
Definition tl1_kn2i : list kentry := Eval vm_compute in kn_fcall tl1_kn1.
Definition tl1_r2 := Eval vm_compute in runT scr0 (SS 0x62eb8 tl1_sr2i [] tl1_kn2i 82).
Definition tl1_sr2 := Eval vm_compute in s_regs (fst (fst tl1_r2)).
Definition tl1_kn2 := Eval vm_compute in kn_after tl1_r2 tl1_kn2i.
(* [comment removed for export] *)
Definition tl1_sr3i : list expr := Eval vm_compute in sr_after_call_j tl1_sr2 KEPT_CS 82.
Definition tl1_kn3i : list kentry := Eval vm_compute in
  KWord (SA (ELit 0) 1128736) 8 (EAlu ALU_ADD (EVar 18) (ELit 2)) :: KWord (SA (ELit 0) 1128696) 4 (ELit 5)
  :: kn_call [(0x1138f8, 0x1138fc); (0x113920, 0x113928); (0x144408, 0x144808)]%Z (-208 - 1056) (-208) IHI 0x113000 tl1_kn2.
Definition tl1_r3l := Eval vm_compute in runT (SCR [true] [] []) (SS 0x62ec8 tl1_sr3i [] tl1_kn3i 114).
Definition tl1_r3e := Eval vm_compute in runT (SCR [false] [] []) (SS 0x62ec8 tl1_sr3i [] tl1_kn3i 114).
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
  | KWord (SA (ELit 0) 1328136) _ _ => false
  | KWord (SA (ELit 0) _) _ _ => true
  | KWord _ _ _ => false
  | KRange (EVar i) _ _ => Nat.ltb i 8
  | KAlign (EVar i) _ => Nat.ltb i 8
  | KDisj _ _ (SA (EVar i) _) _ => Nat.ltb i 8
  | _ => true
  end.
Definition fixw7 (K : kentry) : kentry :=
  match K with KWord (SA (ELit 0) 1128736) 8 _ => KWord (SA (ELit 0) 1128736) 8 (EVar 7) | _ => K end.
Definition kn_FN1 : list kentry := Eval vm_compute in KRange (EVar 7) 0x144408 0x144808 :: map fixw7 (List.filter keepFN1 (kn_acallT tl1_kn3)).
Definition sr_FN1 : list expr :=
  [ELit 0; JN 1; spx (-128); ELit 0x10800; ELit 0x123d20; JN 5; JN 6; JN 7;
   ELit 0; EVar 6; JN 10; JN 11; JN 12; JN 13; JN 14; JN 15;
   JN 16; JN 17; JN 18; JN 19; JN 20; JN 21; JN 22; JN 23;
   JN 24; JN 25; JN 26; JN 27; JN 28; JN 29; JN 30; JN 31].
(* [comment removed for export] *)
Definition e_sr1p : list expr := Eval vm_compute in sr_after_call_j p_sr3e KEPT_AL 114.
Definition e_kn1p : list kentry := Eval vm_compute in kn_acallT p_kn3.
Definition e_r2pn := Eval vm_compute in runT (SCR [false] [] []) (SS 0x62ee4 e_sr1p [] e_kn1p 146).
Definition e_r2pc := Eval vm_compute in runT (SCR [true] [] []) (SS 0x62ee4 e_sr1p [] e_kn1p 146).
Definition e_sr1t : list expr := Eval vm_compute in sr_after_call_j tl1_sr3e KEPT_AL 114.
Definition e_kn1t : list kentry := Eval vm_compute in kn_acallT tl1_kn3.
Definition e_r2tn := Eval vm_compute in runT (SCR [false] [] []) (SS 0x62ee4 e_sr1t [] e_kn1t 146).
Definition e_r2tc := Eval vm_compute in runT (SCR [true] [] []) (SS 0x62ee4 e_sr1t [] e_kn1t 146).
Definition fn1_rvl (ew : expr) (sr : list expr) : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ew] ++ (ELit 0 :: tl sr).
(* [comment removed for export] *)
Definition fn1_r1 := Eval vm_compute in runT scr0 (SS 0x62d10 sr_FN1 [] kn_FN1 40).
Definition fn1_sr1 := Eval vm_compute in s_regs (fst (fst fn1_r1)).
Definition fn1_kn1 := Eval vm_compute in kn_after fn1_r1 kn_FN1.
Definition fn1_sr2i := Eval vm_compute in sr_after_call_j fn1_sr1 KEPT_AL 40.
Definition fn1_kn2i := Eval vm_compute in kn_acall fn1_kn1.
Definition fn1_r2 := Eval vm_compute in runT scr0 (SS 0x62d18 fn1_sr2i [] fn1_kn2i 72).
Definition fn1_sr2 := Eval vm_compute in s_regs (fst (fst fn1_r2)).
Definition fn1_kn2 := Eval vm_compute in kn_after fn1_r2 fn1_kn2i.

Section VP1.
Lemma t_itin1 :
  (s_pc (fst (fst t_r1a)), snd (fst t_r1a), log_wdl_b 0 [(0x113000, 0x123c50); (0x143d68, 0x143f88); (0x1443e0, 0x145000)]%Z (s_log (fst (fst t_r1a))))
    = (0xfa4b4%Z, [SCBr false BC_EQ (EVar 9) (ELit 0); SCBr false BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1c)), snd (fst t_r1c), log_wdl_b 0 [(0x113000, 0x123c50); (0x143d68, 0x143f88); (0x1443e0, 0x145000)]%Z (s_log (fst (fst t_r1c))))
    = (0xfa4b4%Z, [SCBr true BC_NE (EVar 9) (ELit 0); SCBr true BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1b)), snd (fst t_r1b), log_wdl_b 0 [(0x113000, 0x123c50); (0x143d68, 0x143f88); (0x1443e0, 0x145000)]%Z (s_log (fst (fst t_r1b))))
    = (0x62ea4%Z, [SCBr true BC_EQ (EVar 9) (ELit 0); SCBr false BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1d)), snd (fst t_r1d), log_wdl_b 0 [(0x113000, 0x123c50); (0x143d68, 0x143f88); (0x1443e0, 0x145000)]%Z (s_log (fst (fst t_r1d))))
    = (0x62ea4%Z, [SCBr false BC_NE (EVar 9) (ELit 0); SCBr true BC_EQ (EVar 8) (ELit 0)], true)
  /\ (sr_mismatch tm_rvla idb t_sr1a sr_TM 0, kn_missing t_kn1 (map (kmap tm_rvla idb) kn_T)) = ([], [])
  /\ (sr_mismatch tm_rvlc idb t_sr1c sr_TM 0, kn_missing (kn_after t_r1c kn_R) (map (kmap tm_rvlc idb) kn_T)) = ([], [])
  /\ (sr_mismatch tl_rvlb idb t_sr1b sr_TL 0, kn_missing (kn_after t_r1b kn_R) (map (kmap tl_rvlb idb) kn_TL)) = ([], [])
  /\ (sr_mismatch tl_rvld idb t_sr1d sr_TL 0, kn_missing (kn_after t_r1d kn_R) (map (kmap tl_rvld idb) kn_TL)) = ([], [])
  /\ calls_x = EAlu ALU_ADD (EAlu ALU_AND (EExt false 0 1 (EVar 11)) (ELit 3)) (ELit 1)
  /\ nth 19 t_sr1b (ELit 0) = EAlu ALU_ADD (EVar 6) (ELit 2) /\ nth 19 t_sr1d (ELit 0) = EAlu ALU_ADD (EVar 6) (ELit 2).
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun_defs ()) ["VP1"] "p;1p;2p;4p;3p;5g0000j1VTg000Pj2ETg0010j1BTg001Oj1KTg002Xj1ITg003aj4@Tg004nj1FTg005Nj34Tg005hj1>Tg006Mj4CTg006mj4\Tg0086j1OTg008Tj3UTg009]j10Tg00:Bj22Tg00:]j2=Tg00;7j37Tg00;Tj1LTg00<[j3JTg00=8j3HTg00=Xj1NTg00>`j3GTg00?gj5PTg00A4j2MTg00B:j2QTg00CFj2STg00DHj4ZTg00Ddj4XTg00E?j4YTf0R0#>#>p=3%00#>p=1%00#0p=8%>0#0p=6%00#Op=:%B0#Bp=9g00E[R1f1R2;H0p=?g00FhR3f2R4P2P0CCp=;P2g00GFR5P0g00GfR6CCp=Rf6R7f5R8f4R9f3R:P4P2P0CXCXp=A%>0#0#0#0p=5%00#0#0#0p=DP3P3P2P0CCp=Tg00HFR;P;P0g00IQCYp=WP;P;P0g00JKCYp=[A4789A4:42/20'2p=]P8P9P:P4CC=472/20p=<%V1R0,E3R7/E5R2g00KFR4#3#3#1#8#6#1#1#6#6#:R:g00KkR9g00LKR8g00M=R<#BR=#B#9#9R>#9R?#BR@#KRAg00M\#IRBC@P9P8%K?R?PBC@%F1R1'?RC'?5;0,R7RD;4DP6g00N:REPAPBC@P6P8P?PBC@/?1R1'?9;0:,R7R:=42:R?%>4#8#1#1#3#1#1#8#6#:RFP6P8PAPBC@/?C5;0,R7RC=42CR8P9PEPAPBC@/?19;0F,R7RF=42FR1g00NlRA#VRE%V;R6'ERGPEP6%FA%F;CCR;;4;RAg00OKRHg00PTRIg00Q@P9P<P=%9@R@#KC\%>4#O#I3U%O4#I3UR=;4=R9%K>%04R>#O#I5UIRI=4HIRJ/2JRK'2RL,2ARM,2ARN,2ARO'2RP'2RQ'2RR'21=2DP?PR1=2:P8PQ1=2CP1PP1=2FPAPO1=G;ROPAPNPOPAPMPOPAPLPOP9PK1=H=PJPJ1=HIRJPJFAFAFAFAFAP2P7P5g00QlRJ1EJ0RKg00S:R9g00TF37RO770RL#LAJJ0O5;01E33R3%8>#6#1#5#D#D#:%04#1#8#1#3#5#6#5#:'T%04#5#1#3#6#6#3#1#8#:%04#5#1#3#3#3#8#1#8#:'T%04#5#5#1#3#3#D#:%04#5#6#5#D#D#:'T%F35H35H33HR3%NL5G<PDP2P7P5g00UARD97K9RL97J0R4#LAJJ0L5;0%N49G<3P:P2P7P5g00V<R:97K9R497J0RL#LAJJ045;0%NL9G<3PCP2P7P5g00W7R597K9R997J0RK#LAJJ095;0%NK9G<3PFPGPEP6g00X2RFg00XoR3g00Ylg00ZhRKP<DPg00[c1MF3#W'QP;PGPEP6g00\^RFP3g00][PKP<DPg00^WRK,SD1MF3#W'QP;PGPEP6g00_PRFP3g00`MRDg00aIR0P<DP1S:K1MF3#['QP;PGPEP6g00bDR6P3g00cAREP0P<DP1S5K1M63#['QP;PHg00d=P=PHPH%9@#9#9#9R@PDPBCZPIPHP@PEPBCZ=4HIF]F<F<F<F<F<F<F<F<do"). Qed.

Lemma tm_itin :
  (s_pc (fst (fst tm_r2)), snd (fst tm_r2), s_log (fst (fst tm_r2))) = (0x109cb0%Z, [], [])
  /\ (nth 1 tm_sr2 (ELit 0), nth 10 tm_sr2 (ELit 0), nth 11 tm_sr2 (ELit 0), nth 12 tm_sr2 (ELit 0)) = (ELit 0x62e64, EVar 56, EVar 12, EVar 9)
  /\ kn_vars_lt 46 kn_T = true /\ sr_vars_lt 78 tm_sr2 = true /\ kn_vars_lt 78 tm_kn2 = true
  /\ sr_after_call_j tm_sr2 KEPT_MC 78 = tm_sr3i /\ kn_call [(0x1000, 0x10000)%Z] 0 0 IHI 0x113000 tm_kn2 = tm_kn3i /\ kn_vars_lt 78 tm_kn3i = true
  /\ (s_pc (fst (fst tm_r3)), snd (fst tm_r3), s_log (fst (fst tm_r3))) = (0x62ea4%Z, [], [])
  /\ (sr_mismatch tl_rvlm idb tm_sr3 sr_TL 0, kn_missing tm_kn3 (map (kmap tl_rvlm idb) kn_TL)) = ([0%nat], [])
  /\ nth 19 tm_sr3 (ELit 0) = EVar 33.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun_defs ()) ["VP1"] "p&0p;1p;2p;3p;4p;6p;5g0000j1cTg000Pj2STg009]j10Tg004nj1ZTg005Nj3<Tg0010j12Tg001Oj17Tg006Mj4UTg005hj11Tg002Xj1JTg008Tj3gTg0086j15Tg00e:j3dTg00fEj2zTg00gPj2yTg00h[j2WTg00iek409Tg00k0k308Tg00l;j2PTg00=8j39Tg00:Bj2CTg00:]j2NTg00;7j3iTg00;Tj1wTg00<[j3vTg00=Xj1uTg00mFj2mTg00nMk203Tg00oTk302Tg010bk601Tg00?gj5}Tg00A4j2~Tg00E?k400Tg00B:j2|Tg00DHj4tTg011gj1pTg012Ej3oTg00Ddj4sTf0R0#0#0#0#1p=;%00#0#1#1p=^%10#0#0#1p=:%00#1#1#0p=j%00#0#0#5p=>f6R1f5R2f4R3f3R4f2R5f1R6CUP0CUp=]%10#0p=Y%00#0#1#0p==%10#1#1#0p=A%00#1#0#0p=3%50#Jp=E%20#2p=V%20#2#2#2p=[%20#2#2#2#2#2#2#2p=b%10#0#0#0p=8%00#pp>04%00#0#0#0#0#0#0#0p=H%00#1#1#1p=D%10#0#1#0p=B%10#1#0#0p=Gg00OKR7%75%76=97039p=MA97609975p=T%76=970p=r%00#0p=e%00#0#0#0p=?%10#1#1#1p=4%10#1p=l%00#0#0#0#0#0#0#5p=K%00#1#0#0#0#0#1#1#1p=@1W45?o60p>0;%10#1#0#1p={%10#0#1#1p=F%00#0#0p=I%p0,W6p>0:%00#1#0#0#0p=q%00#1p=k%00#0#1p=\%00#0#0#1#1#1#1#0p=O%00#1#0p=Q%56/P0p>07g00HFR8A9860795p=X%05#5/P6=980p=a%05#5%06#0#0#5'P=980p=L1W34?o56=980p=R1P56=980p>061P341P56=980598p=x%06#5,P5=980p=n%p4,W3?o56=980p=6%00#5p>05P1P2P3P4P5P6P0CsCsp=_P7P6g013PR4P0Ctp=hg00GFR3g00GfR27<0p=f1C60,C5p=`g00FhR5g00E[R6#cR0'SR1g014LR9#cR:'SR;P1P:P5P0g00KFR<#0#;#^#:#j#>%Z6R6%Z9R9F]R=;<=1S77R>/S7R?/S7R@P?P7P>P7P7P7%Y<#=#A#j#3#ERAg00M=RB#2RC#2RD#2RE#2RF#2RG#2RH#VRI#2RJ#2RK#2RL#2RM#2RN#V#[RO#V#[#bRP#2#VRQ#2RR#2RS#2RT#2RU#2RV#2#[RW#V#bRX#7RYCU%7MRZ%7JRJF]R[;<[R\A<322R]%c7R^%VX#[#b#bRXg00PTR_%7BR`%1<Ra#0Rb#8Rc$04#J3g%0<Rd#0Re#0Rf#0Rg#8#H#E%0<#3#D#B#3#>Rh#J%2X#[Ri%2iRi%2iRi%[iRi#7%2iRi%2iRi%2iRi%2iRi%2iRi%2iRi%7PRP%0<#3#D#3#G#>Rj#J%7N%7QRQ%7RRR%2i#V#bRi%2iRi%2iRi%2i%Z73M3M9MUV9MST3T3T5TY3M3M3M5TY9TJZ'r3M3T5TA'rRA;<ART%c8RS%0gRV#0RU#e#?Ri#5RN%1aRa#1Rk#4Rl#4#4Rm#l#4Rn#1Ro#1#H#H#K5dYg00M\RY#JRp%@<#B#A#>RqPF%5<Rr#JRsH0;Pp%@<#{#;#>RtPI%Y<#=#4#3#3#EPp%@<#F#;#>RuPI%1<#l#:#4#A#8#EPp%@<#B#4#>RvPI%@<#F#KRw#JPpPjPCPsP`%0bRb#8PIPRP`%IbRb#0PIPQP`%1dRQ#1RR#8PI%7KP`%IRRR#0PIPJP`%0QRQ#8PIPZP`%IQRQ#0PI%7IP`%1eRe#8PI%7HRHP`%IeRe#0PI%EdRd9g_HP`%1f#eRZ#0PI%Y<#=#G#:#?#E%7L%5l7dY%5gRg,z`%Hm#H#H#K%?iRi#I#?Rm#0#H#H#K5d`20:`mRl%5mRm'yP`%IkPIPpP`%IaRa#0PIPpP`PcPIPpP`PbPIPpP`PRPI%EV9g_`P`PQPI%Y<#=#F#;#G#EP`PePIPdP`PUPI%EfRf9g_`P`PaPI%1<#l#:#B#D#G#E%q<#B#?#KRa%0o#4#A#H#K5dH1zHgPlPm1WHY%5iRiH09%1Z#Y#?#KRZ,Wp%Y<#3#?#K'y%I<#:#F#A#?%I<#:#F#A#8%0<#=#D#3#=%;<#^#B#;#;#5%e<#3#A#:#k#:#5%e<#8#A#:#k#:#5Pj%=<#^#B#j#;#5%\<#O#=#8%\<#O#:#G%@<#B#:Pp%0<#3#D#8#F#>RjPI%JjPp%0<#3#D#8#4#>PF%7GRG%\<#O#3#=%0<#3#D#:#B%\<#O#j#G%0<#3#D#:#A%\<#O#D#G%0<#3#D#B#=%\<#O#:#8%Q<#O#F#?%Q<#O#F#BPwPu%@<#F#=#>Pt%Q<#;#4#3#8%@<#4#=#>Rt1Wpt@08fD%3<#^#4#:#8%@<#4#3#>+07%3<#^#4#F#;#5%@<#4#D#>RfPpPfPI%7E%Q<#;#4#A#?%@<#4#:%Q<#;#4#A#G%@<#4#G#>REPpPEPI%JN%Q<#;#4#4#3%q<#8#?#^%Q<#=#;#4#?%q<#8#8#;%Q<#=#3#?#3%5n9dGr1PYN%Z8RG3X7aa3L3LDR3a3LDR4063X3aDx7av7aq5nh3L3L3LDRDR3L3nDx3L5ni3X3XD6D6D6D6D6D6D6D6D63X3XD6D6D6D6D6D6D6D6D6DRDRDRDR3XRh;<hRqP1P:P5P0%1<#;#k#{#k#=$05P6P9F]R9=<;9R6g00NlR<#cRv/SSRaPvPS%Z<99<BPGCURG;<GR<A<7PPRr'CRn'CRI,C]RE'CRf'CRD,C]Rt,C]Ru'CRw'C1N;=P\Pw1N@[P]Pu1N32R2P]PtP2P]PDP2PTPf1N^APqPE1NShP]PIP2P6Pn1N;9P<Pr1NaG1N7PF_F_F_F_F_P1P:P5P0g00QlRr1Sr0R<g00S:Rng015W3iR67i0R2#wAvr06%u2F]=<;=P?P7P>P7P7P71hCp1hKpCU1hLp1hMpF]=<@[g00IQ,mW#f203X4#fg016RRW,mX#fg017N>024Xg018O5<^1S55R^P5P5PNPiCU%Z^39PYPYg019LPZPWJ01g01:IRW5<S1mXW#fP1P:P5P0g01;F9i<nRn9ir0R<#wAvr0n%u<F]=<;9PvPSg01<ARSg00XoRvg01=>R9g00aIPBD}g01>:P8P81~Svg00JKH00'|CU=<aGP7POP9PpCt=<7P3`3`3`3`3`do"). Qed.

Lemma tn_itin :   (* [comment removed for export] *)
  True /\ True /\ True /\ True
  /\ kn_acallT kn_T = tn_kn1i.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun_defs ()) ["VP1"] "p;1p;3p;2p;4g0000j1rTg002Xj1RTg0010j17Tg0086j14Tg005hj11Tg009]j10Tg001Oj1?Tg008Tj3ZTg00e:j3UTg00fEj2_Tg00gPj2^Tg00h[j2NTg00iej4eTg00k0j3qTg00l;j2CTg004nj1oTg005Nj3`Tg00:]j2kTg01?6j1jTg011gj1bTg00=8j3=Tg012Ej3dTg00:Bj2iTg00Ddj4nTf0R0#0#1#0#0#0#0#1#1#1p=>%10#0#1#0p=A%10#1#1#0p=D%00#0#0#4p=5%10#1#0#1p=h%00#0#0#1p=;%70#7p=g%10#0p=O%00#0#1#0p=<%10#1#1#1p=2%00#1#0#0p=3%40#Rp=J%10#0#1#1p=B%10#1p=X%10#0#0#1p=9%10#0#0#0p=8%00#0#0#0p=:%00#1#1#1p=@%10#1#0#0p=H%70#7#7#7p=P%00#0#0p=G%00#0p=V%00#0#0#0#0#0#0#0p=Ff1R1%b0'Np=f%00#1#0#0#0p=Y%00#0#1#1p=T%00#1p=]%00#1#1#0p=\%00#0#1p=S%00#0#0#1#1#1#1#0p=L%00#1#0p=K%41/C0p=pg00HFR2f2R3A=2103=p=Q%03#4/C1==20p=[%03#4%01#0#0#4'C==20p=If4R4f3R5'N?d31==20p=E1C31==20p=m1C451C31==205=2p=c%04#4/C5%03#4/C1==205=2p=l%01#4,C3==20p=a%b5,N4?d31==20p=6g01@5R3/i0p=MP3P1g01@QP0Cnp=W%r2R0g00M\R1#RR3g00KFR4#>#A#D#5R5g00M=R6#7R7#7R8#7R9#7R:%44R;#RR<P3%>4#h#;#5R=%7:R>#7R?#gR@%O4#<#2#3#3#JP3%>4#B#;#5RAP@%14#X#9#2#D#8#JP3%>4#A#2#5RBP@%>4#B#:#5RC#RP3%04#3#@#3#H#5RDP7P<%?6R6%14R<#0R7#0RE#8P@%7@RF#7RG#7RH#7RI#P#P#P#P#P#PRJ#7#?P6%GERE#0P@%?JP6%04RJ#1RK#1RL#8P@%?GP6%GLRL#0P@%?FP6%0KRK#8P@%?IP6%GKRK#0P@%?@P6%0JRI#1RF#8P@%??R?P6%GFRF#0P@g00PTRG%JJRJ7Z?P6%0IRI#1#VRM#0P@%O4#<#H#9#:#J%?H%1<R<#1RH#2RN#47U1%0IRO#4RP,_6%2N#2RN#:#F#F#F#5%0ORO#0RQ#V#:RR#:RS#G#:RT#0#:#F#F#55U61f6TRU%4TRT'^P6%GHP@P3P6%G<R<#0P@P3P6%87P@P3P6PEP@P3P6PLP@%JO9ZG6P6PKP@%O4#<#B#;#H#JP6PFP@PJP6PQP@%JIRI9ZG6P6P<P@%14#X#9#A#@#H#J%Y4#A#F#5R<%XN#2RN#O#2#D#:#F#55U?1_?PPUPT1N?1%4SRSCe%1M#O#F#5,N3%O4#3#F#5'^%G4#9#B#D#:%G4#9#B#D#8%04#<#@#3#<%;4#T#A#;#;#4%V4#3#D#9#]#9#4%V4#8#D#9#]#9#4PD%<4#T#A#\#;#4%S4#L#<#8%S4#L#9#H%>4#A#9P3%04#3#@#8#B#5RDP@%RDP3%04#3#@#8#2#5P:%?>R>%S4#L#3#<%04#3#@#9#A%S4#L#\#H%04#3#@#9#D%S4#L#@#H%04#3#@#A#<%S4#L#9#:%04#3#@#A#\%K4#L#B#:P5%K4#L#B#APBPCPA%>4#B#<#5P=%K4#;#2#3#8%>4#2#<#5R=1N3=?qI8%34#T#2#9#8%>4#2#3#5'p%34#T#2#B#;#4%>4#2#@#5RIP3PIP@%?9%K4#;#2#D#:%>4#2#9%K4#;#2#D#H%>4#2#H#5R9P3P9P@%4RRR#R%K4#;#2#2#3%Y4#8#:#T%K4#<#;#2#:%Y4#8#8#;%K4#<#3#:#3%4N9U>;1C1R%o23Q7[<3I3IDE3[3IDE3m3Q3[DcDl3I3I3I3IDEDE3I3aDc3I5aS3Q3QD6D6D6D6D6D6D6D6D63Q3QD6D6D6D6D6D6D6D6D6DEDEDEDEDERS;`SR<#MR2#MRR#M1k0S,W<,W2,WR'Wg00IQ#jg01@m5`0#M#M#M#Mdo"). Qed.

Lemma fn_itin :
  (s_pc (fst (fst fn_r1)), snd (fst fn_r1), s_log (fst (fst fn_r1))) = (0xfa374%Z, [], [])
  /\ (nth 1 fn_sr1 (ELit 0), nth 10 fn_sr1 (ELit 0), nth 2 fn_sr1 (ELit 0), nth 4 fn_sr1 (ELit 0))
     = (ELit 0x62d18, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x123d20)
  /\ kn_vars_lt 40 fn_kn1 = true /\ kn_acall fn_kn1 = fn_kn2i
  /\ (s_pc (fst (fst fn_r2)), snd (fst fn_r2), s_log (fst (fst fn_r2))) = (0xfa03c%Z, [], [])
  /\ (nth 10 fn_sr2 (ELit 0), nth 2 fn_sr2 (ELit 0), nth 4 fn_sr2 (ELit 0)) = (EVar 7, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x123d20).
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun_defs ()) ["VP1"] "p;1p;2p;4p;3g0000j1hTg000Pj2WTg004nj1dTg006Mj4ATg005Nj3>Tg0010j1:Tg001Oj1ZTg009]j10Tg011gj1\Tg002Xj1ETg008Tj3bTg0086j15Tg005hj11Tg00fEj2lTg00e:j3cTg00gPj2kTg00h[j2PTg00iej4|Tg00k0j3{Tg00l;j2KTg00:Bj2FTg00:]j2UTg00Ddj4XTg00;7j3`Tg00;Tj1qTg00<[j3pTg00=Xj1oTg00mFj2xTg01Ajj1wTg012Ej3fTg00=8j3CTg00DHj4mTf0R0#1#1p=[%10#1#0#1p=^%00#0#0#1p=7%10#0#1#1p=@%10#0#1#0p==%00#5p=n%10#0p=S%00#0#1#0p=;%10#0#0#0p=6%50#Ep=Ng00OKR1P1f1R2P0CAp=af2R3P1P2P0CAp=Q%00#1#0#0p=3%00#1#1#1p=?%00#0#0#5p=4%00#1#0#0#0#0#1#1#1p=<%10#1#1#0p=B%10#1#1#1p=2%10#0#0#1p=8%00#0#0#0p=9%10#1#0#0p=I%00#0#0#0#0#0#0#0p=D%00#0#0p=R%\0,P2p=vf3R4/P3?f20p=}%00#1#0#0#0p=j%00#1#1#0p=i%00#0#1#1p=]%00#0p=u%00#1p=t%00#0#1p=T%00#0#0#1#1#1#1#0p=H%00#1#0p=M%52/K0p=zg00HFR5AC5207C3p=V%03#5/K2=C50p=Y%03#5%02#0#0#5'K=C50p=Lf4R6/P4?f32=C50p=G1K32=C50p=y1K641K32=C505C5p=r%02#5,K3=C50p=g%\4,P6?f32=C50p=JP1P2g01BgP0Cmp=_%:0#:p=s%:0#:#:#:p=OP1P2g01CcP0Cmp=eg00FhR0g00E[R2#hR3'WR6g014LR4#hR7'WR8P6P7P0P3g00KFR9#[#^#7#@#=#n%d2R2CA%d4R4CAR:;>:1W11R;/W1R</W1R1%S9#;#^#7#6#Ng00M=R=#:R>#:R?#:R@#:RA#:RB#:RC#ZRD'ag00PTRE%Z=R=%09RF#0RG#0RH#0RI#0RJ#0RK#0RL#\#E3b5Q;%09#3#?#=#3#4RM#ERN5Q<RO;>ORPg00GFRQg00GfRR;>RRS%h5RTg00M\RU#ERV%<9#=#B#4RWPA%59RX#ERYPV%<9#^#7#4RZ%:CRC#:R[%S9#;#2#3#3#NPV%<9#@#7#4R\P[%19#[#8#2#B#6#NPV%<9#=#2#4R]P[%<9#@#9#4R^#EPV%09#3#?#3#I#4R_P>PY%5IRI,l=%19RY#1R`#1Ra#2#2#2Rb#9#D#D#D#4%0L#9RL#9Rc#R#9Rd#0#9#D#D#45c=1v=dRe%5dRd'kP=%Ra#\P[PVC}P=%R`R`#0P[PVP=%0YRY#6P[PVP=%RYRY#0P[PVP=%1FRa#6P[%NJ9bE=P=%9aP[%S9#;#@#7#I#NP=%6GP[%NFP=PKP[%NHRK9bE=P=P`P[%19#[#8#=#?#I#N%j9#=#D#4R`%[b#2Rb#S#2#B#9#D#45cD1lDIPePd1PDU%5cRcC|%SH#i#D#4,PV%S9#3#D#4'k%R9#8#@#B#9%R9#8#@#B#6%09#;#?#3#;%79#]#=#7#7#5%u9#3#B#8#t#8#5%u9#6#B#8#t#8#5P_%;9#]#=#i#7#5%T9#H#;#6%T9#H#8#I%<9#=#8PV%09#3#?#6#@#4R_P[%E_PV%09#3#?#6#2#4PA%ZBRB%T9#H#3#;%09#3#?#8#=%T9#H#i#I%09#3#?#8#B%T9#H#?#I%09#3#?#=#;%T9#H#8#6%M9#H#@#9%M9#H#@#=P^P\%<9#@#;#4PZ%M9#7#2#3#6%<9#2#;#4RZ1PVZ?{K?%39#]#2#8#6%<9#2#3#4'z%39#]#2#@#7#5%<9#2#?#4RKPVPKP[%Z@%M9#7#2#B#9%<9#2#8%M9#7#2#B#I%<9#2#I#4R@PVP@P[%5LRL#E%M9#7#2#2#3%j9#6#9#]%M9#;#7#2#9%j9#6#6#7%M9#;#3#9#3%5b9cBX1KUL%d53V7Y`3L3LDG3Y3LDG3y3V3YDr7Y]7YW5gM3L3L3LDGDG3L3gDr3L5gc3V3VDJDJDJDJDJDJDJDJ3V3VDGDGDGDGDGRc;>cRMP6P7P0P3%[9#^#9#H#nP2CAP4CAR4=>84R2%ZC%\Y#E9bE='a=Q;NRN=><NR='FRE'FRY'FRC'F1U8:PPPC1U1OPSPY1UQRPMPE1UTcP2P=1U841U<NCXCXCXCXCXP6P7P0P3g00QlR=1W=3R2g00S:Rcg01D_3`RE7`3RM#qAp=3ECA%oMCA=>8:1_>V%s[R[/_V'a1_?V5Q;1_AV5Q<=>1O%s[#O#O#O#O#O#O#Og01EZRO'x=>QR%wOg01FV5>TP6P7P0P3g01GS9`2cRc9`=3R2#qAp=3cCA%o2CA=>841e[V1e?V'a1eAV5Q;=><N'F'F'F'F'Fdo"). Qed.

Lemma tl_itin :
  (s_pc (fst (fst tl_r1)), snd (fst tl_r1), s_log (fst (fst tl_r1))) = (0x62fbc%Z, [], [SE (SA (ELit 0) 0x123a64) 1 (ELit 1)])
  /\ (nth 1 tl_sr1 (ELit 0), nth 10 tl_sr1 (ELit 0), nth 11 tl_sr1 (ELit 0), nth 2 tl_sr1 (ELit 0), nth 3 tl_sr1 (ELit 0), nth 4 tl_sr1 (ELit 0))
     = (ELit 0x62eb8, EVar 14, EVar 9, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x10800, ELit 0x123d20)
  /\ kn_vars_lt 50 tl_kn1 = true /\ sr_vars_lt 50 tl_sr1 = true /\ kn_fcall tl_kn1 = tl_kn2i
  /\ (s_pc (fst (fst tl_r2)), snd (fst tl_r2), s_log (fst (fst tl_r2))) = (0x62f74%Z, [], [SE (SA (ELit 0) 0x123a64) 1 (ELit 0)])
  /\ (s_pc (fst (fst p_r1)), snd (fst p_r1), log_wdl_b 0 [(0x113000, 0x123c50); (0x143d68, 0x143f88); (0x1443e0, 0x145000)]%Z (s_log (fst (fst p_r1))))
     = (0x1005d0%Z, [], true)
  /\ (nth 17 p_sr1 (ELit 0), nth 10 p_sr1 (ELit 0), nth 11 p_sr1 (ELit 0)) = (ELit 29, ELit 1, ELit 0x5413)
  /\ (s_pc (fst (fst p_r2)), snd (fst p_r2), log_wdl_b 0 [(0x113000, 0x123c50); (0x143d68, 0x143f88); (0x1443e0, 0x145000)]%Z (s_log (fst (fst p_r2))))
     = (0xff528%Z, [], true)
  /\ stdio_call 82 p_sr2 p_kn2 = Some p_sc
  /\ (sc_ret p_sc, sc_f p_sc, sc_fd p_sc, sc_s p_sc, sc_l p_sc, sc_wb p_sc, sc_wp p_sc) = (0x1005f4%Z, 0x1138f8%Z, 1%Z, ELit 0x1349e, ELit 1, ELit 0x144408, ELit 0x144409)
  /\ (s_pc (fst (fst p_r3l)), snd (fst p_r3l), log_wdl_b 0 [(0x113000, 0x123c50); (0x143d68, 0x143f88); (0x1443e0, 0x145000)]%Z (s_log (fst (fst p_r3l))))
     = (0x62ea4%Z, [SCBr true BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], true)
  /\ (s_pc (fst (fst p_r3e)), snd (fst p_r3e), log_wdl_b 0 [(0x113000, 0x123c50); (0x143d68, 0x143f88); (0x1443e0, 0x145000)]%Z (s_log (fst (fst p_r3e))))
     = (0xfa374%Z, [SCBr false BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], true)
  /\ kn_after p_r3e p_kn3i = p_kn3
  /\ (nth 10 p_sr3e (ELit 0), nth 1 p_sr3e (ELit 0), nth 2 p_sr3e (ELit 0), nth 4 p_sr3e (ELit 0)) = (EVar 15, ELit 0x62ee4, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x123d20).
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun_defs ()) ["VP1"] "p%0p%1p&0p;1p;2p;3p;4p;<p;5g0000k10@Tg000Pj2^Tg005hj11Tg004nj1{Tg002Xj1?Tg009]j10Tg00h[j2@Tg0010j12Tg0086j1<Tg01HNk30LTg00=8j35Tg005Nj3ETg001Oj17Tg00e:k306Tg00fEk20JTg00gPk20HTg00iek40_Tg00k0k30\Tg00l;j2[Tg01IYk10YTg01J;k40XTg011gj1PTg01KDm<0UTg01LMk20BTg006Mj4STg01Lok30TTg003ak40ATg00:Bj2ITg00:]k20=Tg00;7j3jTg00;Tj1wTg00=Xj1nTg00mFk20QTg00nMk20PTg01N8k10RTg00>`j3~Tg01O6k50OTg01P>k10WTg01QBk10gTg01RDk10fTg01SGk10eTg01TIk10dTg01UKk10cTg01VNk10bTg00CFk20aTg008Tk30MTg012Ej3WTg00Ddk40?Tg00<[k30`Tg00DHk40>Tf0R0#0#0#0#1p=6%00#1p>08%10#1#1#1p=8%00#1#1#1p=h%10#0#0#<p=f%00#1#0#0#0#1#1#1p=e%00#1#0#0p=;%10#1#0#0p=:f5R1f4R2g00FhR3f3R4f2R5f1R6CSP0CSp=ag00OKR7,^0p=`%10#0#0#0p=9%10#0#1#1p=L%10#0#1#0p=T%10#1#1#0p=C%00#0#<#?p=N%20#2p>02P7P7P6P0CSp=o%00#0#0p==%00#Pp>0;g00PTR8%?080M6p=]P2P7P4P7P5P6CSP0CSp=Y%00#0#1#0#0p>09%00#1#1#1#1#0#1#0p=d%00#0#0#<p=4%00#1#0#0#0p=U1@45?W60p=M%00#1#0#0#0#0#1#1#1p=V%10#1#0#1p=X%10#0p>07%00#0#1#0p=A1@45%<0#?7W6p>0N%10#1p=v%10#0#0#1p=O%00#0#0#0#0#0#0#<p=\%00#0p=F%20#2#2#2p=k%05#P,@4?W60p=G%P5,@4?W60p=>%<0#?p=KB0M860p>0K%10#1#1#1#1#1#1#1p=c%00#0#0#0#0#0#0#0p=b%00#0#0#0p=J%P0,@6p>0I%00#1#1#0p=i%00#0#1#1p=H%<0,[6p>0^%00#0#0#1#0p>0]%00#0#0#1#0#0#1#1#1p=R%00#0#0#1#0#0#1p>0G%10#<p=u%00#0#1p=g%10#0#0#1#1#1#0#0p=_%00#1#0p=t%<6/[0p>0[%10#0#0#0#0#1#1#1p>0Zg00HFR9A5960755p>041[241[56=590559p=s%05#</[6=590p=}AW456=590p>03%02#</[4%05#</[6=590559p=z1[56=590p>0Ff6R:?W12AW456=590559p>0<A5960959595949592p=3P3P5P6P0CSp>01P6g00GFR;P0g00GfR<CSp>00P5P7P6P0CSp>0E%20#2#2#2#2#2#2#2p=y%75%76=570557p=rA57609575p=Z%76=570p>0D%15#0#0#0#P,@4?W60p=D%05#P,@4%<0#?7W6p=x%00#0#0#Pp>0V%P4,@2?W56=590p=BA5960p>0CP3P3P6P0CSp=|P2P420=56P0H0?p=QP:P1P2P4P5P6P0H0?H0?p>0Sg00QlR=?j60p=pB0`=60p=qP7P6g01WQS00P0H0>p=mP7P6g01XMP0H0>p>0:P7P6g01YHP0H0>p>05AE:12AE456/I0'Ip=lg00E[R0$0@R6,^3R5g014LR4$0@R:'^R2P5P:P6g00KFR1#1#6$08#8#h#f%{0R>g00M\R?#?R@%01#e#;#:#fRA'@RBg00M=RC#2RD%<1RE#?RF40L%{4RG554EaRH;EH1^77RI#`RJ#`RK#`S01#`S02Q01PKPJPI%91#L#T#C#N%2DRL#2RM#2RN#2RO#2RP$02RQ#2RR#2RS#2RT#2RU$02RV#7S03'o%7RS04%7CRR%11RW#0RX#1S05#=RY$0;']S06DY%01RZ#0R[#0R\#0R]#9S07#=S08#=#NS09&091#d#;#4R^#?R_DYR`;E`S0:AE;<<Ra&0@9RbPBPDPFP@%U1#d#C#4RcPNPFCMS0;P@%V1#X#6#4RdPQ&071#A#8#;#;H0NS0<P@%V1#L#6#4RePQ%11#v#O#8#C#9H0NS0=P@%U1#d#8#4RfPQ%V1#L#\Rg#?CMS0>P@%01#e#;#:#4RhPDPFCMS0?PR%0XRX#1S0@#FPQ%2VS0A#2S0B#2S0C#kRV#2Ri#7CGS0DPR%0XS0E#0S0F#0RX#0S0GPQ%7VC>S0HPR%1ZRV#1Rj#1S0I#0S0J#FS0KPQ%7SC>S0LPR%0jS0M#0S0N#0Rj#0S0OPQQ04C>S0PPR%0VRk#1S0Q#0S0R#FRlPQ%7UC>S0SPR%0kS0T#0Rk#0RU#0RmPQ%7QC>S0UPR%1[R[#1Rn#0Ro#0S0V#0RpPQ%7PRPC>S0WPR%0[R[#0S0X#0S0Y#0S0ZPQ%KZRZ-0KPC>S0[PR%1\S0\#0S0]#0Rq#0S0^PQ%91#L#A#;#NC>S0_%7T%1WRW#1Rr#1S0`#1#vRs#<806?S0a%<]Rt-0JRS0b%csRs#b#b#b#\%0]R]#0Ru#FS0c#FRv#FRw#JRx#=#JRy#0#b#b#\606RS0d20IRyRz%<yRy+0HS0ePR%=rS0fPQP@C>S0gPR%0WRW#FRr#0S0hPQP@C>S0iPRPYPQP@C>S0jPRPXPQP@C>S0kPRPjPQ%<],]RC>S0lPRPUPQ%91#T#:#h#NC>S0mPRQ0YPQPZC>S0nPRPuPQ%K\R\-0KRC>S0oPRPrPQ%11#C#i#O#8#NC>S0p%U1#T#J#\Rr%vs#8Rs#1Ru#0#8#C#b#\606PS0q20JPtS0rPzPy1@P?%<xRxH0_S0s%1qRq$07#J#\S0t,@@&071#;#J#\+0HS0u%61#H#h#:#J-0^xS0v&0]1#i#8#T#4S0w%R1#;#A#4S0x&0G1#X#J#9#u&0G1#X#A#:#u%g1#6#X#A#:#uPh%g1#6#X#H#J#uPA%g1#6#X#H#A#u%01#e#9#T#4S0y%g1#6#C#_%U1#d#O#4%01#e#9#L#4RA,@@PQ%?A%01#e#9#8#4,@@PN%7ORO%g1#6#C#;#A%01#e#O#T#4%g1#6#C#i#:%01#e#O#C#4%g1#6#C#h#:&091#d#A#4P^&091#d#i#4%U1#d#:#4Pc%t1#6#C#L#TPgPe%V1#L#A#4Pd%t1#6#8#;#9%V1#8#A#4Rd1@@d@0\\L%;1#H#8#O#9%V1#8#;#4+0[%t1#6#8#X#9#u%V1#8#h#4R\1@@\PQ%7M%t1#6#8#C#J%V1#8#O#4%t1#6#8#C#:%V1#8#:#4R\1@@\PQ%<wRw#?%t1#6#c#;%U1#9#J#H#4%U1$0Z#:#4S0z%U1#9#9#6#4R\%U1#O#J#6#4RePr%<s:06OE1[?w%{9404Ds3}H03DzH0340F4043}Ds7}fDs3}DzK0<3}DsDsS0{40FD3D3D3D3D3D3D3D3H03Rf;EfS0|P5P:P6%11#6$08#C#C#fP>B0LBD@=54GEaRG=E2GS0}1^5;R4%01#b#L#T#4>016>-005R9;E9S0~%1WRW#K/oF%0lS10#0S11#1#H#K60EIRl=EJlS12%v1#8#T#O$08#4Rw>016>-005RO=E4OS13g01ZDRs$0YS14%R1#6#8#4RgPE%01#b#L#C#fRc%?\R^%;1#;#;#J#O#KS15P^%Kv%1oS16#FRo$07#hRA#1Rx#0#KRPPF%9kS17$0;,]RRk%ki#y#yRi#2Ry#2Rz#2Rt#2#kRZ#k#yR]#2Rj#2RX#2RY#2R{#2R|#2$02#k#yR}%?cQ09%2}#kR~%2~R~%2~R~%?dRd%k~R~#7%2~R~%2~R~%2~R~%2~R~%2~R~%2~R~%1x#KRx%2~$02#yR~%2~R~%2~R~%2~%{73r3r9ZFF9ZF@9ZFP5Z@9ZPF3r3r3r5ZF7ZF+0D3r7Z_7Zk+0DP@%R1#A#H#4S09PQ%?eCMS18P@%R1#A#;#4PQP^CMS19P@%R1#A#i#4S1:PQP^CMS1;P@%R1#H#6#4S1<PN%1u#v#8Ru#1Re#1#vRk#1#8#cR7#c#cR~#1#KS1=CMS1>P@%R1#A#9#4S1?PQ%?wCMS1@PRPUPQg00KkS1APLP?PQH0XR?CDS1BPR%0mS1C#0PQ%?gRmCGS1DPR%1nRn#:PQ%11#c#:#6#NCGS1EPR%0nRnPQPxCDS1FPR%FnRn#0PQPmCGS1GPRQ16PQPFCDS16PR%0oPQ%0uCxS1HPRQ0VPQ%KeCDS0VPR%0pRp#0PQ%1[R[CxS1IPR%1[RePQ%F1#J#A#;#H#NCDS1JP@P\PDQ0F#KR\CMS0FPRPvPDP\C>S1KPR%0[R[PQP@CDS1LPRQ0X#1R\#=PQPFCGS0XPR%F[R[#0PQP@CGS1MPR%=ePQQ08#1#TCxS08PRP\PQP@CDS1NPRQ0^#FPQP@CGS0^PRQ0T#1R\#=Re$0;RvPQQ0c#PRu,]RCMS0cPRQ0YPQ%Fk#:#:#:#:#:#:#X#KCDS0YPRQ0Z#0Rk#0PQ%07#c#cCxS0ZPR%FqPQQ0@#1#H#H#H#H#H#NCGS0@PRQ0\#1Rq#0R7#FRo#0RxPQ%9[#OCxS0\PRQ0G#0RUPQP?CGS0GPRQ0]#1Rw#=PQPdCGS0]PRPwPQP@CDS0TPRP7PQ1]RvCDS1OPR%1qRqPQ%Px,]RCDS1PPR%=qPQQ0E#1$0VRq,]RCGS0EPRQ0I#1RxPQ%7tCDS0IPR%=xRxPQ%7zCGS1QPRQ0JPQ%7yCDS0JPRQ0K#0RyPQ%7iCGS0KPRQ0M#1RiPQ%0~#KCDS0MPR%=iRiPQP@CGS1RPRQ0NPQ%KVRVCDS0NPRQ0O#0R~PQP@CGS0OPRQ0Q#1RzPQPFCDS0QPR%=zRzPQPdCGS1SPRQ0RPQ%NACDRAPRQ11PQPmC>RmPRP\PQ%F1#J#6#:#h#NCDR\P@%R1#A#6#4PQP@CMRdP@%R1#A#\RtPQP@CMRvP@%R1#H#\R7PNQ1=CMRwP@PgPNPVCMRVPRPyPQP@PRPxPQP@PRPUPQP@1@RqPQP@20IRiPQP@PRQ17PQQ07#PRi,]RRqPRP~PQP?PRPzPQQ0B#7RzPRQ10PQ%?hPRPePQP@PRQ1CPQQ0A#7RePRPnPQQ03PRPpPQQ04PRP[PQ%91#L#C#:#NPRPkPQPqPRQ0f#0PQ%7XPRQ0`#=PQ%7j1@RuPQ%7]1@RiPQP@PRQ05#9PQ%7|PRQ0h#0PQ%7{PR%=WPQ%7YPRPoPQ%91#L#L#A#NPBPDP@Q0;Q0<Q0=Q0>Q0?Q0DQ0HQ0LQ0PQ0SQ0UQ0WQ0[Q0_Q0aQ0bQ0dQ0eQ0gQ0iQ0jQ0kQ0lQ0mQ0nQ0oQ0pQ0qQ0rQ0sQ0uQ0vQ0wPg%R1#6#8#fPt%=1#_#9#9Q09%=1#_#O#;Q1:%=1#_#_Q1?%=1#_#T#;P7%=1#_#:#AQ1<%=1#_#:#iQ0xQ0{DzDzDzDsD3D3D3D3D3D3D3D3H03DBDBDBDBK0<DBDBDBDBDBDBDBDBDBDBDBDBK0<DBDBDBR7+0C404D3D3D3D3D3D3D3D3D3D3D3D3N<0U-0BsRt;EtRB1^33RQ/^3Ro#`RR#`RY#`RW#`R{PWPYPRPoPQP31|cgPECSPPPFDYP^Q15DYR^;E^RF%11#6$08#X#;#fP<g00N:RP%P1#?:0T8zRzP@H0A=50>6016-005R8=E48RE%81#;#i#C#fQ1APPPzP@H0A=50>6016-005R>=E4>R0PVQ19Q18Q1;Q1>Q1@Q1BQ1DQ1EQ1FQ1GQ16Q1HQ0VQ1IQ1JQ0FQ1KQ1LQ0XQ1MQ08Q1NQ0^Q0cQ0YQ0ZQ0@Q0\Q0GQ0]Q0TQ1OQ1PQ0EQ0IQ1QQ0JQ0KQ0MQ1RQ0NQ0OQ0QQ1SPAPmP\20Cw7:04dvD3D3D3D3D3D3D3D3D3D3D3D3Rv=EbvRdPJPI%91#L#L#O#N,oeQ06P_DYR_=EK_Re'IR7'IRw'IR\'IRm'IRA'IRV'IRz'IRP'IRc'IRg,IaR|'IRi'IP2PHQ0:PiQ02P`PaP|20=;<R|PaPgP|Q0|PcPbPfQ0}PPP2PGQ0~PzP4P9Q12PVPJPlQ13PAP4POPBPmQ14PtPFP\P{P^PEPwP4P8P0P7P4P>PdPePbPv20=K_DQDQDQDQDQDQDQDQDQDQK0SDQDQP2P5P:P61^=6R=g00S:Rvg01[M3jRe,p6Rd#w1q6e%ndEaPHQ02Q01PKPJPI1mD@1mS@'o1mT@1mL@DY1mM@1mN@DYP`P;g01\HR`-0QZP<P;Q00-0PZP<Pb&0R`g01]DP2P5P:P6g01^A9j=vR:,p6R2#w1q6:%n2EaPGP4P5P;P6g01_<9j=vRG,p6R2#w1q6GQ0tQ0y'|%U1#d#X#4%V1#8#6#4'|Q0z/|r%{Q55Q55Q55QRr%n25~CEaP9PJQ0C00:@20:S@'o20:T@60EIPlP4P5P;P6g01`69j=vRl,p6RT#w1q6l%nT9~CrEaPOQ14g01a0g01akP}g01bhg01ccI0Og01d^R}-0BsP{PWPYPRPoPQP3&0W}&0g}'|&0f}CS&0e}&0d}DY&0c}&0b}DYP^P4P5P;P6g01eX9j=vR^,p6R}#w1q6^%n}9~CrEaP8P4P5P;P6g01fSR;9j=vRv,p6R=#w1q6v%n=9~CrEaP>Pbg01gN-0a;g01hJPJPI205S@205D@'o205L@205N@DY=EK_FlFlFlFlFlFlFldo"). Qed.

Lemma tl1_itin :
  (sr_mismatch tl1_rvl0 idb p_sr3l sr_TL 0, kn_missing p_kn3 (map (kmap tl1_rvl0 idb) kn_TL1)) = ([0%nat], [KRange (ELit 0x144408) 0x144408 0x144800])
  /\ (s_pc (fst (fst tl1_r1)), snd (fst tl1_r1), s_log (fst (fst tl1_r1))) = (0x62fbc%Z, [], [SE (SA (ELit 0) 0x123a64) 1 (ELit 1)])
  /\ (nth 1 tl1_sr1 (ELit 0), nth 10 tl1_sr1 (ELit 0), nth 11 tl1_sr1 (ELit 0), nth 2 tl1_sr1 (ELit 0), nth 3 tl1_sr1 (ELit 0), nth 4 tl1_sr1 (ELit 0))
     = (ELit 0x62eb8, EVar 14, EVar 9, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x10800, ELit 0x123d20)
  /\ kn_vars_lt 50 tl1_kn1 = true /\ sr_vars_lt 50 tl1_sr1 = true /\ kn_fcall tl1_kn1 = tl1_kn2i
  /\ (s_pc (fst (fst tl1_r2)), snd (fst tl1_r2), s_log (fst (fst tl1_r2))) = (0x62f74%Z, [], [SE (SA (ELit 0) 0x123a64) 1 (ELit 0)])
  /\ (nth 1 tl1_sr2 (ELit 0), nth 2 tl1_sr2 (ELit 0), nth 11 tl1_sr2 (ELit 0)) = (ELit 0x62ec8, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0)
  /\ sr_vars_lt 82 tl1_sr2 = true /\ kn_vars_lt 82 tl1_kn2 = true
  /\ (s_pc (fst (fst tl1_r3l)), snd (fst tl1_r3l), s_log (fst (fst tl1_r3l))) = (0x62ea4%Z, [SCBr true BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], [])
  /\ (s_pc (fst (fst tl1_r3e)), snd (fst tl1_r3e), s_log (fst (fst tl1_r3e))) = (0xfa374%Z, [SCBr false BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], [])
  /\ kn_after tl1_r3e tl1_kn3i = tl1_kn3
  /\ (nth 10 tl1_sr3e (ELit 0), nth 1 tl1_sr3e (ELit 0), nth 2 tl1_sr3e (ELit 0), nth 4 tl1_sr3e (ELit 0)) = (EVar 15, ELit 0x62ee4, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x123d20)
  /\ (sr_mismatch tl1_rvl idb tl1_sr3l sr_TL 0, kn_missing tl1_kn3 (map (kmap tl1_rvl idb) kn_TL1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x144408 0x144800]).
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun_defs ()) ["VP1"] "p%0p&0p;1p;2p;3p;4p;5g0000j1rTg000Pj2TTg004nj1oTg00=8j3=Tg002Xj1GTg00e:j3YTg006Mj4LTg005Nj3ATg005hj11Tg00h[j2RTg0010j13Tg0086j16Tg01HNk303Tg001Oj1BTg009]j10Tg008Tj3dTg00fEk20>Tg00gPk20=Tg00iek40GTg00k0k30FTg00l;j2OTg011gj1pTg01Lok30DTg003ak408Tg012Ej3hTg00:Bj2?Tg00:]j2wTg00?gk506Tg00A4k205Tg00B:k204Tg00;7j3UTg00;Tj1lTg00<[j3mTg00=Xj1qTg00mFk201Tg00nMk200Tg01N8k10BTg00CFk20ATg00Ddj4uTg00E?k40@Tg00DHj4{Tf0R0#0#1#0#0#0p=j%10#0#0#0p=5%00#0#0#1p=4%00#0#0#6p=2%10#0#0#1p=E%00#0#0#0p=D%00#0#0#0#0#0#0#6p=Kg00HFR1f1R2;=0p=}%00#0p=g%00#1#0#1p=b%10#1#1#1p=7%00#1#1#1p=a%10#0#0#6p=e%00#0#1#0#0#0#1#1#1p=Q%00#1#0#0p=:%10#1#0#0p=Sf5R3f4R4g00FhR5f3R6f2R7P2CLP0CLp=V%10#0#1#1p=@%10#0#1#0p=9%10#1#1#0p=8%00#0#6#Gp=I%30#3p=sg00OKR8P8P2P0CLp=_%00#pp>0?P4P8P6P8P7P2CLP0CLp=c%10#0p=|%00#0#0#0#0#0#0#0p=^%00#0#0#1#0#0#1#1#1p=N%60#Gp=i1R67?h20p>0J%00#0#1#0p=;%00#0#1#1p=H%00#1#1#0p=]%10#1#1#1#1#1#1#1p=\%10#1p>0I%10#1#0#1p=t%00#1#0#0#0#0#1#1#1p=F%00#0#0p=C%p0,R2p>0H%00#0#0#1#0#0#1p>0<%10#0#0#1#1#1#0#0p=P%00#0#1p=f%00#1#0p=Z%62/O0p>0EA=1209=17p=W1O72==10p>0;%04#6/O6%07#6/O2==105=1p=X1R46?h72==10p=>%07#6/O2==10p=z1O461O72==105=1p=y%02#6,O7==10p>0:%p6,R4?h72==10p=<Ah672==10p=xP7P8P2P0CLp>09P4P61w72P0Cup=Jf6P3P4P6P7P2P0CuCup>07P1P1P0g01iEH0@p>02P8P2g01jAR4P0C{p=`%30#3#3#3p>0C%30#3#3#3#3#3#3#3p=[g00GFR3g00GfR97A0p=kP8P2g01k>R:P0C{p=vP8P2g01l;P0C{p=nAA672/?0p=M1?20,?7p=~g00NlR7#rR2%r1R0'TR6P2P0g00M=R;%o75=7S00g00KFR7#j#5#5#4#2R<#GR=%j7#E#D#KR>7Y<%o1R1'}CLR?;A?g00E[R@#rRA,T5R5g014LRB#rRC'TRDP5PCPA%17#g#b#7#a#e%o@REg00M\RF#GRG%Q7#:#S#eS01'RRH%3;RI%67RJ#GRK403%oBRL5=BEVRM;AMS021T88RN/T8RO/T8RP/T8RQ/T8R8PQPPPOPN%57#@#9#8#I%3IRR#3RS#3RT#3RU#3RV#sRW#3RX#3RY#3RZ#3R[#sR\#B'_%BXRXg00PTR]%B;R^%17R_#0R`#5Ra$0?#G3dRbDc%07Rc#0Rd#0Re#0Rf#|#^#I%Q7#9#:#2Rg#GS03DcRh;AhS04AA399RiPHPIPK%3\R\#3Rj#sRk#BRl?Y<>RmPG%N7#4#7#2S05PT%1cRn#iH0JRo%N7#;#:#2,RGS06PWPlPG%N7#;#H#2RpPW%j7#E#D#4#2Rq#GPG%N7#;#]#2RrPWP=PG%N7#H#4#2R=PT%1_R_#1Rs#7Rt#\Ru$0I#7Rv#1Rw#1#\#\#\#\#\#iRxPG%N7#;#5#2RyPW%17#7#t#:#9#IPG%N7#;#4#2PWPGPG%N7#;#KRzPWPGPG%N7#H#KR{PTPxPG%F7#9#8#2S07PTPKPG%F7#t#4#2S08PW%57#@#t#4#IPG%F7#@#4#2S09PW%17#8#a#7#9#IPG%F7#9#7#2S0:PW%F7#@#KS0;#GPG%Q7#:#S#2RxPIPKP^%0`R`#5PW%3k#sRk#3RK#BP^%C`R`#0PW%BkP^%1nRk#5PW%BYP^%CkRk#0PWPXP^%0nRn#5PW%B[P^%CnRn#0PW%BWP^%1dRd#5PW%BVRVP^%CdRd#0PW%icRc9d]VP^%1e#gR[#0PW%57#@#;#:#I%BZ%6t7YF%6fRt-0>^%^u#^#^#K%0fRf#0Ru#g#DRX#DR|#C#DR}#0#^#^#K5Y^20H^}R~%6}R}+0=P^%CsPWPGP^%C_R_#0PWPGP^PaPWPGP^P`PWPGP^PkPW%if9d]^P^PnPW%57#9#S#a#IP^PdPWPcP^PuPW%ieRe9d]^P^P_PW%17#8#]#E#7#I%j7#9#D#KR_%0w#7#8#^#K5YV20>VtP~P}1RVF%6|R|H0G%1[#|#D#K,RG%|7#:#D#K+0=&0<7#@#8#D&0<7#@#8#5Q05%C7#P#a#8Pz%C7#P#5#5Pp%C7#P#E#:Pr%C7#P#PPy%C7#P#9#:P{%C7#P#S#;P=%C7#P#S#]%N7#:#;#2%47#H#9#4#4#6%47#H#9#b#E#6%;7#H#9#b#E#6Px%;7#H#9#]#4#6Q01%;7#H#9#]#b#6%Q7#5#9#2%f7#4#8#P%F7#9#E#2PG%Q7#5#@#2RxPW%GxPG%Q7#5#7#2PT%BURU%f7#4#8#:#;%Q7#E#9#2%f7#4#8#]#S%Q7#E#8#2%f7#4#8#a#S%Q7#9#;#2%f7#4#8#E#5%Z7#4#8#@#DQ07%Z7#4#8#@#9Q0:Q0;Q09%F7#@#;#2Q08%Z7#4#7#:#5%F7#7#;#2Rx1RGx@0FeR%:7#H#7#E#5%F7#7#:#2+0E%:7#H#7#@#4#6%F7#7#a#2RePGPePW%BS%Z7#4#7#8#D%F7#7#E#2%Z7#4#7#8#S%F7#7#S#2RePGPePW%6XRX#G%Z7#4#\#:%j7#5#D#H#2%Z7#;#4#7#DP<%6v9YUJ1OFX;W1:0;q_DXD>DXD>40;3W3zDyDX60:g3zDXD>D>3zDyDyDXDXDXDX60:|3W3WD<D<D<D<D<D<D<D<D<3W3WD<D<D<D<D<D<D<D<D<D>D>D>D>D>D>D>D>D>D>D>D>R|Cx3WCxRg=A0gR_P5PCPA%17#g#b#8#8#ePEB03HIG==BLEVRB=ADBRq%57#@#@#;#I/_b>09NGRX=AOXRFP5PCPA%17#g#b#t#:#eP9g00N:RU%Bj%p7#G60D]RjPGH08==@EPLEVRJ=ADJRvP5PCPA%77#:#]#8#eg00KkPUPjPGH08==@EPLEVRL=ADLREQ06PWAd]lcRcAhHIG1}m|5WoCxRo=A0oR|POPN%B\%57#@#@#E#I'_PbQ03DcRb=APbR7P2P0Q00AYc<>/}1CLR1=A61Rc'?R>'?R<'?R\'?Rm,?iRH,?iRl'?R]'?RW'?R@,?iRj'?RU'?Re'?P6P?Q02PePDPMQ04PUP8PhPiPj1w39R9PiP@P9P_PWP0PgPqP]PDPBPFPlPOPXPiPHP9PiPmP9PvP\PDPJPEP<PDPLP|P>P0PoP7PcPPPb1w61DJDJDJDJK07DJDJDJK07DJDJDJP6P2P0g01m9Rcg00XoR7g01n7g00aIRoP;I06g01hJ205c7$02+04CLP?PDP5PCPAg00QlR?1T?ARcg00S:R>g01o33UR|7UAR<#lAm?A|%q<EVPMP8PQPPPOPN1`IG1`YG'_1`ZG1`RGDc1`SG1`TGDcPh&0CK#[#[#[RKg01ooRh+01#k200K4#kP0&0Bhg020lPDP5PCPAg021j9Uc>Rh9U?AR4#lAm?Ah%q4EVPBPO1vIG1vRG'_1vZG609NPX%[K#[#[#[RK000:#kg022f-01K#kPDP5PCPAg023c9Uc>RK9U?AR:#lAm?AK%q:EVPJPDP5PCPAg024`RC9Uc>R>9U?ARc#lAm?A>%qcEVPLP0g025]-0ACg026[RCPPPOPN1nYG1nIG'_1nRG1nTGDcPbP2P0g027XR0P7g028UPoP;I0620507$02-04CCL=A61CMCMCMCM3~CMCMCM3~CMCMCMdo"). Qed.

Lemma e_itin :
  (s_pc (fst (fst e_r2pn)), snd (fst e_r2pn), log_win_b 0 (s_log (fst (fst e_r2pn)))) = (0x62d10%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2pc)), snd (fst e_r2pc), log_win_b 0 (s_log (fst (fst e_r2pc)))) = (0x62d10%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2tn)), snd (fst e_r2tn), log_win_b 0 (s_log (fst (fst e_r2tn)))) = (0x62d10%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2tc)), snd (fst e_r2tc), log_win_b 0 (s_log (fst (fst e_r2tc)))) = (0x62d10%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (let r := e_r2pc in
       (sr_mismatch (fn1_rvl (ELit 0x144408) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1p) (map (kmap (fn1_rvl (ELit 0x144408) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (ELit 0x144408) 0x144408 0x144808]))
  /\ (let r := e_r2pn in
       (sr_mismatch (fn1_rvl (ELit 0x144408) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1p) (map (kmap (fn1_rvl (ELit 0x144408) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (ELit 0x144408) 0x144408 0x144808]))
  /\ (let r := e_r2tc in
       (sr_mismatch (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1t) (map (kmap (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x144408 0x144808]))
  /\ (let r := e_r2tn in
       (sr_mismatch (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1t) (map (kmap (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x144408 0x144808]))
  /\ kn_vars_lt 114 p_kn3 = true /\ kn_acallT p_kn3 = e_kn1p /\ kn_vars_lt 114 tl1_kn3 = true /\ kn_acallT tl1_kn3 = e_kn1t.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun_defs ()) ["VP1"] "h01rp%0p&0p;1p;2p;4p;3p;5g0000j1yTg000Pj2gTg005hj11Tg0010j12Tg001Oj1CTg002Xj1OTg003aj4zTg004nj1xTg00=8j35Tg006Mj4GTg005Nj39Tg00e:j3[Tg009]j10Tg008Tj3kTg00h[j2QTg012Ej3\Tg01J;k40ETg0086j17Tg00fEk206Tg00gPk205Tg00iek40BTg00k0k30ATg00l;j2KTg00:Bj2ATg00:]j2ZTg00Ddj4uTg00;7j3HTg00;Tj1mTg00<[j3lTg00=Xj1rTg029Sj2oTg02:Zk10=Tg02;ck200Tg00CFk207Tg00A4j2{Tg00B:k201Tg00mFj2|Tg01?6k108Tg011gj1sTg00?gk50;Tg00E?k40:Tf0R0#0#0#0#1p=:%00#1p>09%10#0#1#0p=D%00#0#1#0p=4%00#0#0#7p=3%20#2p=tg00FhR1f2R2f1R3P0CGp=_%00#1#0#0#0p=e%10#0#0#0p=<%10#0#0#1p=B%00#0#0#0p=8g00HFR4?530p>03%20#2#2#2p>02%70#Op=?%00#0#0#1#0#0#1#1#1p=L%10#1#1#1p=6f3R5/Q2?\30p=P%00#1#0#0p=>%00#0#1#1p=U%00#1#1#0p=j%10#1#1#1#1#1#1#1p=T%10#1p=i%10#1#0#1p=M%00#0#0p=@%00#0p=h%00#0#0#0#0#0#0#7p=I%00#0#1#0#0#0#1p=S%00#7p>0D%00#1#0#0#0#0#1#1#1p=F%10#1#1#0p=;%10#0p=f%10#0#1#1p=R%00#0#1#0#0#0#1#1#1p=X%10#1#0#0p=E%00#0#0#0#0#0#0#0p=^%s0,Q3p>0C%00#1#1#1p=q%00#0#0#1#0#0#1p=p%10#0#0#1#1#1#0#0p=N%10#7p=]%00#1#0p=W%73/K0p>0@A54309542p=n1K23=540p>04%02#7/K3=540p=w%02#7%03#0#0#7'K=540p=Yf4R6/Q5?\23=540p=J1K651K23=540554p=v%06#7/K5%02#7/K3=540554p=c%03#7,K2=540p>0?A5430954295459546p=`%s5,Q6?\23=540p==%15#0#0#0#s,Q6?\23=540p=VA\523=540p>0>f6f5P6P5P2P3P0CuCup=bP3g00XoR5P0g02<`g00M=R6I0;p=~P4P4P0g02=\H0:p=}%20#2#2#2#2#2#2#2p>0<%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=a1A30,A2p=dg00E[R2#yR3,g1R1g00GFR7'gR8P1P7g00KFR9#1#:$09#D#4#3R:g00KkR;g02>XR<%26R=#2R>#2R?#2R@#2RA#2RB#tRC#2RD#2RE#CRFg00M\RG#ORHCz%x2RI5525_3g00GfRJCGRK;9KRLP1P7PJP<PFPHCz=52I9_3:PJCGR:=98:RIg00NlR2#yR<%y4RM'gRNP<PM%x29526R2%e9#<#<#:#3RO#ORP%e9#B#8#:#3RQ7[O%x4R4+03CGRR;9RRSP<PMP2g00PTR2%2ERE#2RT#t$02RU#CRV%09RW#?RX3kRY?[OQ0034CGRZ=9NZR[A97JJR\PH%L9#:#6#3R]P@%1WR^#?CPS00%L9#4#>#3,QHS01?\CPPH%L9#4#U#3R_PC%OQCPS02PH%L9#4#j#3R`PCPPCPS03PH%L9#U#:#3RaP@%19Rb#1Rc#1Rd#6Re#TRf#i#6Rg#1Rh#1#T#T#T#T#T#?RiCPS04PH%L9#4#<#3RjPC%19#6#M$09#4#<#?CPS05%C6Rk%0^Rl#@RmPCP;P>PGPCH0EPk%0mR;#@PC%O]RnPk%0WRW#1Ro#1Rp#1Rq#1PC%19#i#T#8#>#?Pk%0qRqPC%0pRp#1Rr#h#B#6#?Pk%8qPCPnPkPrPC%79Rr#ORnPHPOP=%0bRb#0Rq#hRs#?PH%L9#4#:#3PCPHCPS06PH%L9#4#IRtPCPHCPRuPH%L9#U#IRvP@PiCPRiPH%S9#M#U#4$0DRwP=PHCPRxPH%F9#D#;#3RyP@PnPH%F9#M#:#3RzPC%f9#4#6#>#>#?PH%F9#R#:#3R{PC%19#i#B#6#;#<#?PH%F9#D#6#3R|PC%F9#R#IR}#OPH%X9#>#E#3R~P=PnPkPqPC%2U#tRU#2Rq#CPk%0sRs#0PC%CUPk%1^R^PCPFPk%@^R^#0PC%CDPkPlPC%CTPkP;PC%CCPk%hpPC%CBRBPk%@oRo#0PCAk2BXPk%0WRW#1#hRp#0PC%f9#4#E#B#8#?%CE%7e7[G%0WRe#7RE-06k%^f#^#^#I%0eRe#0Rf#h#8R;#8RT#@#8Rl#0#^#^#I5[k20CklRD%7lRl+05Pk%@dPCPHPk%@cRc#0PCPHPkPbPCPHPkPsPCPHPkP^PC%?e9k2kPkPmPC%f9#4#R#:#E#?PkPoPCPXPkPfPC%?WRW9k2kPkPcPC%19#i#B#D#q#E#?%e9#D#8#IRc%0h#6#;#^#I5[B206BEPDPl1QBG%7TRTH0B%1p#f#8#I,QH%f9#>#8#I+05%p9#R#;#8%p9#R#;#<P]%@9#N#q#;Pt%@9#N#<#<P_%@9#N#B#>P`%@9#N#NPj%@9#N#D#>Pv%@9#N#E#4Pa%@9#N#E#j%L9#>#4#3%p9#M#8#<#]%p9#M#4#E#]%S9#M#4#E#]P~%S9#M#U#8#]Pw%S9#M#U#4#]%X9#<#D#3%S9#;#N%F9#D#BPH%X9#<#R#3RwPC%OwPH%X9#<#6#3P@%CARA%S9#;#>#4%X9#B#D%S9#;#j#E%X9#B#;%S9#;#q#E%X9#D#4%S9#;#B#8%X9#D#j%W9#:#;#R#8Py%W9#:#;#R#DP|P}P{%F9#R#4#3Pz%W9#:#6#>#<%F9#6#4#3Rz1QHz@0AW>%>9#U#6#B#<%F9#6#>#3+0@%W9#:#6#M#<#]%F9#6#q#3RWPHPWPC%C?%W9#:#6#;#8%F9#6#B%W9#:#6#;#E%F9#6#E#3R?PHP?PC%7;R;#O%W9#:#T#>%e9#<#8#U%W9#4#:#6#8%7g9[Ar1KG;;n4:04Qc7wO3YDJ3w3YDJ4043n3wDvDc3Y3Y3Y3YDJDJ3YDvDvDcDcDcDc60?TD`D=D=D=D=D=D=DVD=D=D`D=D=D=D=DVD=DVD=DVDJDJDJDJDJRTD`DJDVD=DVDVD=DV3nD`Rc=9McRQQ01PCPYQ00Px%e9#B#8#I9[VOQ02Q03Q04Q05Q06AnuiTD`D`H0>RT=9MTRi,A\Ru'ARV'ARO,A[R9'ARx,ASRC'AR4,AIR;,ALRG'A1Z8KRAPIPG1Z8:RGPLP;PAPIP4PGPSPC1ZNRRCPSPxPCP[P91ZNZR9P[POP9P\PV1Z7JRVPQPu1ZMcP\PiPV1ZMTCuFbFbFbFbFbP1P7g00QlRT1gT3RVg00S:Rig02?JR\3HRc7H3Ru#mAlT3c5_3%ru,o6CG=98KP1P7g02@FRu9HViRc9HT3RQ#mAlT3c5_3%rQ,o6CG=98:P1P7g02ABRQ9HViRc9HT3R9#mAlT3c5_3%r9,o6CG=98KP1P7g02B>R19HViRK9HT3R9#mAlT3K5_3%r9,o6CG=98:Pu1gViRuP<PMAHVi09HT3$0=RT-00PRP/~Tg02C:R3-0701{P5#}+01CG=9NRRRb0P\PuPRb0P1PuP<PM200YTRY/~Tg02D6RT-0701{Y5#}+01CG=9NZRZb0PQPuPZb0&02q$0<#a#a#a#a#aRqg01hJRZ'|=97J&08Z=9M3g026[R3,|q=97J&083=9MT'A3d3d3d3d3ddo"). Qed.

Lemma fn1_itin :
  (s_pc (fst (fst fn1_r1)), snd (fst fn1_r1), s_log (fst (fst fn1_r1))) = (0xfa374%Z, [], [])
  /\ (nth 1 fn1_sr1 (ELit 0), nth 10 fn1_sr1 (ELit 0), nth 2 fn1_sr1 (ELit 0), nth 4 fn1_sr1 (ELit 0))
     = (ELit 0x62d18, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x123d20)
  /\ kn_vars_lt 40 fn1_kn1 = true /\ kn_acall fn1_kn1 = fn1_kn2i
  /\ (s_pc (fst (fst fn1_r2)), snd (fst fn1_r2), s_log (fst (fst fn1_r2))) = (0xfa03c%Z, [], [])
  /\ (nth 10 fn1_sr2 (ELit 0), nth 2 fn1_sr2 (ELit 0), nth 4 fn1_sr2 (ELit 0)) = (ELit 0, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x123d20).
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun_defs ()) ["VP1"] "p&0p;1p;2p;4p;3g0000j1oTg000Pj2ZTg004nj1kTg006Mj4GTg005Nj3@Tg0010j1<Tg001Oj1_Tg009]j10Tg011gj1]Tg002Xj1CTg008Tj3dTg00e:j3bTg005hj11Tg0086j16Tg00fEj2|Tg00gPj2{Tg00h[j2UTg00iek402Tg00k0k301Tg00l;j2MTg00:Bj2ITg00:]j2WTg00Ddj4\Tg00;7j3cTg00;Tj1vTg00<[j3uTg00=Xj1tTg00mFj2~Tg01Ajj1}Tg012Ej3qTg00=8j3DTg00DHj4sTf0R0#1#1#1#1p=4%00#1#0#0p=8%00#1#1#0p=X%10#1#1#0p=7%10#0#0#6p=n%10#0p=[%00#0#1#0p=:%10#1#0#1p=i%00#0#0#1p=3%10#0#0#0p=5%60#Cp=Ag00OKR1P1f1R2P0CGp=gf2R3P1P2P0CGp=V%00#0#1#0#0#0#1#1#1p=L%10#0#1#0p=>%00#0#0#6p=2%00#1#0#0#0p=f%10#0#0#1p=;%00#0#0#0p==%00#0#0#1#0#0#1#1#1p=Ff3R4/U3?q20p=r%10#1#0#0p=E%00#0#1#1p=N%10#1#1#1#1#1#1#1p=Q%10#1p=h%00#1p=a%00#0#0#0#0#0#0#6p=K%00#1#0#0#0#0#1#1#1p=?%10#0#1#1p=H%00#0#0#0#0#0#0#0p=Y%00#0#0p=B%]0,U2p>03%00#1#1#1p=`%00#0#0#1#0#0#1p=z%10#0#0#1#1#1#0#0p=J%00#0p=p%00#0#1p=^%00#1#0p=T%62/M0p>00g00HFR5AD5207D3p=S1M32=D50p=yf4R6#0#6/M4%03#6/M2=D505D5p=O1U64?q32=D50p=9%03#6/M2=D50p=m1M641M32=D505D5p=l%02#6,M3=D50p=x%]4,U6?q32=D50p=PP1P2g02E2P0Csp=e%<0#<p=w%<0#<#<#<p=RP1P2g02EoP0Csp=jg00FhR0g00E[R2#oR3'ZR6g014LR4#oR7'ZR8P6P7P0P3g00KFR9#4#8#X#7#n%k2R2CG%k4R4CGR:;@:1Z11R;/Z1R</Z1R1%[9#:#i#3#5#Ag00M=R=#<R>#<R?#<R@#<RA#<RB#<RC#_RD'gg00PTRE%_=R=%09RF#0RG#0RH#0RI#0RJ#0RK#0RL#]#C3d5V;%L9#>#8#2RM#CRN5V<RO;@ORPg00GFRQg00GfRR;@RRS%o5RT%<CRC#_RU%f9#5#5#3#2RV%f9#;#=#3#2RW3bg00M\RX#CRY%F9#:#8#2%<CRCPUCrPY%F9#3#4#2RUPA%1FRZ#APY%L9#8#E#nR[P>PYPY%F9#:#N#2R\PC%CWPY%F9#:#X#2R]PC%CVPY%F9#N#3#2R^PA%19R_#1R`#1Ra#4#QRb#h#4Rc#1Rd#1#Q#Q#Q#Q#Q#ARePY%F9#:#5#2RfPC%19#4#i#a#:#5#APY%F9#:#3#2PCPYPY%F9#:#KRgPCPYPY%F9#N#KRhPAPePY%?9#>#7#2RePA%69Ri#CRjPY%?9#i#3#2RkPC%[9#:#4#8#8#APY%?9#H#3#2RlPC%19#h#;#4#7#5#APY%?9#>#4#2RmPC%?9#H#KRn#CPY%L9#8#E#2RoP>Pj%6IRI,|=%Yb#Y#Y#K%0L#=RL#=Rb#B#=Rj#0#Y#Y#K5b=203=jRp%6jRj'{P=%Ba#]PCPYCrP=%B`R`#0PCPYP=%0_R_#5PCPYP=%B_R_#0PCPYP=%5ZPC%AJ9dE=P=%=ZPC%[9#:#H#3#E#AP=%5GPC%AFP=PKPC%AHRK9dE=P=P`PC%19#h#;#>#`#E#A%f9#>#=#KR`%0d#4#7#Y#K5bD1|DIPpPj1UDX%6bRbH02%[H#X#=#K,UY%[9#8#=#K'{%z9#H#7#=%z9#H#7#5PU%B9#J#`#7Pg%B9#J#5#5P\%B9#J#;#8P]%B9#J#JPf%B9#J#>#8Ph%B9#J#E#:P^%B9#J#E#X%F9#8#:#2%39#N#>#3#3#6%p9#8#7#;#a#;#6%p9#5#7#;#a#;#6Po%:9#N#>#X#3#6P[%p9#5#7#;#;#a#6%L9#5#>#2%^9#3#7#J%?9#>#;#2PY%L9#5#H#2R[PC%C[PY%L9#5#4#2PA%_BRB%^9#3#7#8#:%L9#;#>#2%^9#3#7#X#E%L9#;#7#2%^9#3#7#`#E%L9#>#:#2%^9#3#7#;#5%T9#3#7#H#=Pe%T9#3#7#H#>PmPnPl%?9#H#:#2Pk%T9#3#4#8#5%?9#4#:#2Rk1UYk@01K?%89#N#4#;#5%?9#4#8#2+00%89#N#4#H#3#6%?9#4#`#2RKPYPKPC%_@%T9#3#4#7#=%?9#4#;#2%T9#3#4#7#E%?9#4#E#2R@PYP@PC%6LRL#C%T9#3#Q#8%f9#5#=#N#2%T9#:#3#4#=PV%6c9bBi1MXL%k53S9yW`DOD9DOD93y3S3mDlDO5xM3mDOD9D93mDlDlDODODODO5xb3S3SDPDPDPDPDPDPDPDP3S3SD9D9D9D9D9D9D9D9D9D9D9D9D9D93SRb;@bRMP6P7P0P3%49#8#=#`#nP2CGP4CGR4=@84R2%]_#C9dE=,gY=V;NRN=@<NR='IRE'IR_'IR9'I1W8:PPP91W1OPSP_1WQRPMPE1WTbP2P=1W841W<NC\C\C\C\C\P6P7P0P3g00QlR=1Z=3R2g00S:Rbg02Fl3cRE7c3RM#vAu=3ECG%tMCG=@8:1e>Y%wCRC/eY'g1e?Y5V;1eAY5V<=@1O%wC#R#R#R#R#R#R#Rg02GhRO'~=@QR%}Og02He5@TP6P7P0P3g02Ic9c2bRb9c=3R2#vAu=3bCG%t2CG=@841jCY1j?Y'g1jAY5V;=@<N'I'I'I'I'Ido"). Qed.
End VP1.

(* [comment removed for export] *)
Definition sr_FE : list expr :=
  [ELit 0; ELit 0x62ee4; spx (-208); ELit 0x10800; ELit 0x123d20; JL 5; JL 6; JL 7;
   EVar 9; EVar 14; EVar 15; JL 11; JL 12; JL 13; JL 14; JL 15;
   JL 16; JL 17; EVar 15; ELit 18446744073709551615; ELit 0x123a60; ELit 0; ELit 0; ELit 18446744073709551614;
   JL 24; JL 25; JL 26; JL 27; JL 28; JL 29; JL 30; JL 31].
Definition kn_FE : list kentry := kn_TL1.
Definition fe_rvlp : list expr :=
  slots2 (EVar 21) (EVar 22) (rvl18w (EVar 13) (EVar 14) (EVar 15) (EVar 16) (nth 19 p_sr3e (ELit 0)) (ELit 0x144408) p_sr3e).
Definition fe_rvlt : list expr :=
  slots2 (EVar 21) (EVar 22) (rvl18w (EVar 13) (EVar 14) (EVar 15) (EVar 16) (nth 19 tl1_sr3e (ELit 0)) (EAlu ALU_ADD (EVar 18) (ELit 2)) tl1_sr3e).
Definition fe_sr1i : list expr := Eval vm_compute in sr_after_call_j sr_FE KEPT_AL 50.
Definition fe_kn1i : list kentry := Eval vm_compute in kn_acallT kn_FE.
Definition fe_r2n := Eval vm_compute in runT (SCR [false] [] []) (SS 0x62ee4 fe_sr1i [] fe_kn1i 82).
Definition fe_r2c := Eval vm_compute in runT (SCR [true] [] []) (SS 0x62ee4 fe_sr1i [] fe_kn1i 82).

Section VP2.
Lemma fe_itin :
  (sr_mismatch fe_rvlp idb p_sr3e sr_FE 0, kn_missing p_kn3 (map (kmap fe_rvlp idb) kn_FE)) = ([0; 21]%nat, [KRange (ELit 0x144408) 0x144408 0x144800])
  /\ (sr_mismatch fe_rvlt idb tl1_sr3e sr_FE 0, kn_missing tl1_kn3 (map (kmap fe_rvlt idb) kn_FE)) = ([0; 21]%nat, [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x144408 0x144800])
  /\ kn_vars_lt 50 kn_FE = true /\ kn_acallT kn_FE = fe_kn1i
  /\ (s_pc (fst (fst fe_r2n)), snd (fst fe_r2n), log_win_b 0 (s_log (fst (fst fe_r2n)))) = (0x62d10%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst fe_r2c)), snd (fst fe_r2c), log_win_b 0 (s_log (fst (fst fe_r2c)))) = (0x62d10%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (let r := fe_r2n in
       (sr_mismatch (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r fe_kn1i) (map (kmap (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], []))
  /\ (let r := fe_r2c in
       (sr_mismatch (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r fe_kn1i) (map (kmap (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], []))
  /\ nth 19 p_sr3e (ELit 0) = ELit 18446744073709551615 /\ nth 19 tl1_sr3e (ELit 0) = ELit 18446744073709551615   (* [comment removed for export] *)
  /\ tl1_sr1 = tl_sr1 /\ tl1_sr2i = tl_sr2i.
Proof.
ltac2:(KReplay.run1 (kr_t_O23TRun_defs ()) ["VP2"] "h01rp&0p;1p;2p;3p;4p;5g0000j1iTg000Pj2eTg0010j12Tg004nj1kTg00=8j36Tg002Xj1HTg00e:j3[Tg006Mj4BTg005Nj3DTg001Oj15Tg009]j10Tg008Tj3bTg005hj11Tg0086j18Tg00fEk204Tg00gPk202Tg00h[j2YTg00iek40ATg00k0k30@Tg00l;j2PTg003aj4}Tg00:Bj2ETg00:]j2JTg00Ddj4oTg00?gj5nTg00A4j2tTg00B:j2rTg00mFk20<Tg01?6k10;Tg00;7j3_Tg00;Tj1yTg00<[j3xTg00=Xj1vTg029Sj2wTg02:Zk10:Tg02;ck209Tg00CFk208Tg00E?j4{Tg00DHj4zTg012Ej3mTg011gj1lTf0R0#2#2p=c%00#1#0#0#0p=d%10#0#0#0p=7%00#0#0#1p=4%00#0#0#8p=3%10#0#0#1p=?%00#0#0#0p=F%00#0#0#0#0#0#0#8p=Lg00HFR1f1R2;60p>03%80#Hp=\%00#0#0#1#0#0#1#1#1p=K%10#1#1#1p=:f3R3f2R4'Y?m20p>0=%00#0#1#0p==%00#1#0#0p=@%00#0#1#1p=M%00#1#1#0p=`%10#1#1#1#1#1#1#1p=V%10#1p>07%10#1#0#1p=j%10#0#1#0p=>%00#0#8#Hp=Q%00#0#1p=]%00#8p>05%00#1#0#0#0#0#1#1#1p=G%10#1#1#0p=9%10#0#1#1p=I%00#1#1#1p=g%00#0#1#0#0#0#1#1#1p=U%10#1#0#0p=T%00#0#0p=A%00#0p=f%00#0#0#0#0#0#0#0p=Z%l0,Y2p>0B%10#0p=u%00#0#0#1#0#0#1p>01%10#0#0#1#1#1#0#0p=N%00#1p=h%00#1#0p=X%82/P0p>0?A61209614p=W1P42=610p>00f4R5#0#8/P3%04#8/P2=610561p=R1Y53?m42=610p=;%04#8/P2=610p=s1P531P42=610561p=q%02#8,P4=610p=~%l3,Y5?m42=610p=<%00#lp>0>%20#2#2#2p=^g00OKR6%54%52=66036p=CA66209664p=pA6620966496639665p=Sf6f5P5P3P4P2P0CoCop=aP1P1P0g02J_R5C{p=|AD342/E0p=O1E20,E4p>06g00NlR4#iR2%i1R3'eR7P2P3g00M=R8%28R9#2R:#2R;#2R<#2R=#2R>#cR?#2R@#2RA#2RB#2RC#cRD#2RE#2RF#2RG#2RH#2RI#cRJ%k4RK564564RLg00KFRM#d#7#7#4#3RN#HRO%dM#?#F#LRP7[N%k1RQ+03CBRR;DRP2P3PLg00PTRL%5HRH%0MRS#\RT3b?[NP003QCBRU=D7URVg00GFRWg00GfRX;DXRYA[HNPg00M\RP#HRZ%KM#4#:#3R[P<%1SR\#\H0=PZ%KM#=#@#3P?PHPZ%KM#=#M#3R]P?%dM#?#F#4#3R^#HPZ%KM#=#`#3R_P?POPZ%KM#M#4#3ROP<%1MR`#1Ra#1Rb#:Rc#VRd$07#:Re#1Rf#V#V#V#V#VRg#1#\RhPZ%KM#=#7#3RiP?%1M#:#j#@#>#QPZ%KM#=#4#3P?PZPZ%KM#=#LRjP?PZPZ%KM#M#LRkP<PhPZ%]M#4#j#M#=$05RlP9PZPZ%GM#>#9#3RmP<%8MRn#HRoPZ%GM#j#4#3RpP?%7M#I#j#4#QPZ%GM#I#4#3RqP?%1M#9#g#:#>#QPZ%GM#>#:#3RrP?%GM#I#LRs#HPZ%UM#@#T#3RtP9Po%58Ro%0`R`#0R9#7P?%2JRu#5Po%A9R9#0P?%5JPo%1\RJ#7P?%5ARAPo%AJRJ#0P?%5@R@Po%0\R\#7P?%5CPo%A\R\#0P?%5?Po%0SRS#1RC#7P?%5>R>Po%ACRC#0P?AbL>TPo%0SRS#1#fRv#0P?%7M#I#=#@#Q%5B%8c7[P%0SRc#8RB-04o%Zd#Z#Z#L%0cRd#0Rw#f#FRx#FRy#A#FRz#0#Z#Z#L5[o20BozR{%8zRz+02Po%AbP?PZPo%AaRa#0P?PZPo%7`R`P?PZPoP9P?PZPoPJP?%\d9bLoPoP\P?%7M#>#T#g#QPoPCP?PTPoPwP?%\SRS9bLoPoPaP?%1M#9#`#?#:#Q%dM#>#F#LRa%0f#:#9#Z#L5[>204>BP{Pz1Y>P%8yRyH0A%1v#u#F#L,YZ%uM#@#F#L+02&01M#I#9#F&01M#I#9#7P[%AM#N#g#9Pj%AM#N#7#7P]%AM#N#?#@P_%AM#N#NPi%AM#N#>#@Pk%AM#N#T#=PO%AM#N#T#`%KM#@#=#3%4M#M#>#4#4#8%fM#@#9#?#h#?#8%fM#7#9#?#h#?#8Pt%=M#M#>#`#4#8Pl%fM#7#9#?#?#h#8%UM#7#>#3%]M#4#9#N%GM#>#?#3PZ%UM#7#I#3RlP?%HlPZ%UM#7#:#3P<%5=R=%]M#4#9#@#=%UM#?#>#3%]M#4#9#`#T%UM#?#9#3%]M#4#9#g#T%UM#>#=#3%UM#>#@#3R<%]M#4#9#?#7%XM#4#9#I#FPm%XM#4#9#I#>PrPsPq%GM#I#=#3Pp%XM#4#:#@#7%GM#:#=#3Rp1YZp@0@S:%@M#M#:#?#7%GM#:#@#3+0?%@M#M#:#I#4#8%GM#:#g#3RSPZPSP?%5;%XM#4#:#9#F%GM#:#?#3%XM#4#:#9#T%GM#:#T#3R;PZP;P?%8xRx#H%XM#4#V#@%dM#7#F#M#3%XM#=#4#:#FPN%8e9[=n1PPx;WQ:00^aDRD;DRD;4003W3sDqDR3~3sDRD;D;3sDqDqDRDRDRDR5~y3W3WD<D<D<D<D<D<D<D<D<3W3WD<D<D<D<D<D<D<D<D<D;D;D;D;D;D;D;D;D;D;D;D;D;D;3WRy=D3yRag00FhR^g00E[Rx#iRP'eR=/eWRnP=PWP^PP%1M#4#h#>#=#3Reg00Kkg02>XRNPAPZC}%kxR?56xCBPXCBR;;D;RSP=PWP^PPPePXPNPAPZC}=6x?CBPXCBR?=Dn?RxP2P3A648KPQCBRQ=D7QRKAD6hhR4%i6RAPZ%7M#I#>#9#Q&0>`#H9bLoRo%uc#Z#QRc%H<R<%2uRu#5%2uRu%2uRuP@%5DRDPDP@%2u#^Ru%2uRu%2uRu%2uRu%2uRu%2uRu%5ERE%5GRG%HtRt%5FRFPZ%0g#\Rg%2u#c#^Ru#5RL%2uRu#5R`%2uRu#5RM%2uRu#5RN%2uRu%2uRu%2uRu%2uRu%k6Re3C3C3pDSDS3C3C3CDS3C3pDSR:;D:Rp%2uRu%2uRqPoPcP<%^qRq#5%2qRq%2qRqP@PDPZ%^qRq#5%2qRq%2qRq%2qRq%2qRq%2qRq%2qRqPEPGPtPFPZPgPLP`%2q#c#^#^Rq%2qRq%2qRq%2q;Ce3C9pMNDSDS3C3C3CDS3CDS3CRN=DANRM'ERe,E4Rq'ER`,EKRL'ERg'ERF'ERt'ERG'ERE'E1J7RPVPE1J7UPYPG1JWXPaPt1J3yPSPF1Jn;PxPg1Jn?PKPL1J7QRLPKP`PLP4Pq1J6hRqP4PePqPpPM1JA:1JANCoFaFaFaFaFaP7P2P3g02KZRNg00XoR:g01YHRMg02LWRpP8Dng01hJ1tN:#|'rCBPRP7P2P3g02MRRRP:g01l;RNPpP8Dng026[1tR:#|'rCBPUPW20<u5PXP3&0;5g02NOR5PnP=PWP^PPg00QlRX1eXPRug00S:RUg02OLRR3_Rp7_PRq#yAxXPpCB%vq,w8CBP;PnP=PWP^PPg02PHR^9_uURW9_XPR=#yAxXPWCB%v=,w8CBP?PR1euURRP2P3A_uU09_XP$0:RX-09HRHP:PXg02<`P8Dn20805P1P11tH:g02=\C{'rCB=D7QRQb0P^PRPQb0P6P6PIPMPZCzPhP6P6PIPNPZCzPhPAg01jAg01WQg02QDg02RB5DACOCOCO406COCOCOCOCOCOdo"). Qed.
End VP2.
