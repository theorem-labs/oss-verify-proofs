(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymCall LibKnowFrame LibKnowXfer.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec RefMemcpyLib AllocIface.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MainEntry V2LibStdioCall V2OpenFail_defs V2Open_defs V2Oom_defs V2DirRead_defs V2ReadLoop_defs V2Hdr_defs.
Import ListNotations. Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation RSEGS := Ubsan.M.loaded_segments.

Definition STOPST : list Z := (0x17bf0 :: 0x17cc0 :: 0x17a5c :: STOPS2)%Z.
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPST scr ss [].
(* [comment removed for export] *)
Definition STOPSP : list Z := [0x3e37c; 0x17bf0; 0x17a5c; 0x3c230]%Z.
Definition runP (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPSP scr ss [].

(* [comment removed for export] *)
Definition t_ss1 := SS 0x17b38 sr_R [] kn_R 45.
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
  | KImg 0x10000 0x46120 => [KImg 0x10000 0x45f10; KImg 0x45f18 0x46120]
  | KImg 0x76918 0x77000 => [KImg 0x76918 0x76940; KImg 0x76d40 0x77000]
  | KImg 0x56171 0x561a0 => [KImg 0x56171 0x56174; KImg 0x56175 0x561a0]   (* [comment removed for export] *)
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
  [ELit 0; ELit 0x17b9c; spx (-208); ELit 0x10800; ELit 0x56270; JM 5; JM 6; JM 7;
   EVar 9; EVar 12; EVar 9; JM 11; JM 12; JM 13; JM 14; JM 15;
   JM 16; JM 17; JM 18; JM 19; ELit 0x56170; EVar 13; JM 22; JM 23;
   JM 24; JM 25; JM 26; JM 27; JM 28; JM 29; JM 30; JM 31].
Definition rvl13 (ecalls : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; ecalls] ++ (ELit 0 :: tl sr).
Definition tm_rvla : list expr := rvl13 calls_x t_sr1a.
Definition tm_rvlc : list expr := rvl13 (ELit 1) t_sr1c.
(* [comment removed for export] *)
Definition kn_acallT (kn : list kentry) : list kentry := kn_call GLOB (-208 - 1024) (-208) IHI 0x45000 kn.
(* [comment removed for export] *)
Definition tm_srM : list expr := sr_after_call_j sr_TM KEPT_AL 46.
Definition tm_knM : list kentry := Eval vm_compute in KRange (EVar 56) 0x1000 0x7fffff800000 :: kn_acallT kn_T.
Definition tm_r2 := Eval vm_compute in runT scr0 (SS 0x17b9c tm_srM [] tm_knM 78).
Definition tm_sr2 := Eval vm_compute in s_regs (fst (fst tm_r2)).
Definition tm_kn2 := Eval vm_compute in kn_after tm_r2 tm_knM.
(* [comment removed for export] *)
Definition tm_sr3i := Eval vm_compute in sr_after_call_j tm_sr2 KEPT_MC 78.
Definition tm_kn3i := Eval vm_compute in kn_call [(0x1000, 0x10000)%Z] 0 0 IHI 0x45000 tm_kn2.
Definition tm_r3 := Eval vm_compute in runT scr0 (SS 0x17bb0 tm_sr3i [] tm_kn3i 110).
Definition tm_sr3 := Eval vm_compute in s_regs (fst (fst tm_r3)).
Definition tm_kn3 := Eval vm_compute in kn_after tm_r3 tm_kn3i.
(* [comment removed for export] *)
Definition tn_sr1i := sr_upd tm_srM (ridx 10) (ELit 0).
Definition tn_kn1i : list kentry := Eval vm_compute in kn_acallT kn_T.
Definition tn_r1n := Eval vm_compute in runT (SCR [false] [] []) (SS 0x17b9c tn_sr1i [] tn_kn1i 78).  (* [comment removed for export] *)
Definition tn_r1c := Eval vm_compute in runT (SCR [true] [] []) (SS 0x17b9c tn_sr1i [] tn_kn1i 78).   (* [comment removed for export] *)
Definition tn_sr1n := Eval vm_compute in s_regs (fst (fst tn_r1n)).
Definition tn_sr1c := Eval vm_compute in s_regs (fst (fst tn_r1c)).
Definition tn_kn1 := Eval vm_compute in kn_after tn_r1n tn_kn1i.

(* [comment removed for export] *)
Definition JN (i : nat) : expr := EVar (8 + i).
Definition sr_FN : list expr :=
  [ELit 0; JN 1; spx (-128); ELit 0x10800; ELit 0x56270; JN 5; JN 6; JN 7;
   EVar 7; EVar 6; JN 10; JN 11; JN 12; JN 13; JN 14; JN 15;
   JN 16; JN 17; JN 18; JN 19; JN 20; JN 21; JN 22; JN 23;
   JN 24; JN 25; JN 26; JN 27; JN 28; JN 29; JN 30; JN 31].
Definition kn_FN : list kentry := Eval vm_compute in List.filter (kentry_vars_lt 7) tn_kn1.
Definition fn_rvln : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ELit 2] ++ (ELit 0 :: tl tn_sr1n).
Definition fn_rvlc : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ELit 0] ++ (ELit 0 :: tl tn_sr1c).
Definition fn_r1 := Eval vm_compute in runT scr0 (SS 0x17a5c sr_FN [] kn_FN 40).
Definition fn_sr1 := Eval vm_compute in s_regs (fst (fst fn_r1)).
Definition fn_kn1 := Eval vm_compute in kn_after fn_r1 kn_FN.
Definition fn_sr2i := Eval vm_compute in sr_after_call_j fn_sr1 KEPT_AL 40.
Definition fn_kn2i := Eval vm_compute in kn_acall fn_kn1.
Definition fn_r2 := Eval vm_compute in runT scr0 (SS 0x17a64 fn_sr2i [] fn_kn2i 72).
Definition fn_sr2 := Eval vm_compute in s_regs (fst (fst fn_r2)).
Definition fn_kn2 := Eval vm_compute in kn_after fn_r2 fn_kn2i.

(* [comment removed for export] *)
Definition keepTL (K : kentry) : bool :=
  match K with KWord (SA (EVar 6) _) _ _ => false | KWr (SA (EVar 6) _) _ => false | _ => true end.
Definition kn_TL : list kentry := Eval vm_compute in map fixTL (List.filter keepTL kn_T).
Definition JL (i : nat) : expr := EVar (18 + i).
Definition sr_TL : list expr :=
  [ELit 0; JL 1; spx (-208); ELit 0x10800; ELit 0x56270; JL 5; JL 6; JL 7;
   EVar 9; EVar 14; JL 10; JL 11; JL 12; JL 13; JL 14; JL 15;
   JL 16; JL 17; EVar 15; EVar 17; ELit 0x56170; EVar 16; ELit 0; ELit 18446744073709551614;
   JL 24; JL 25; JL 26; JL 27; JL 28; JL 29; JL 30; JL 31].
Definition rvl18 (e13 e14 e15 e16 e17 : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; e13; e14; e15; e16; e17] ++ (ELit 0 :: tl sr).
Definition tl_rvlb : list expr := slots2 (EVar 35) (EVar 36) (rvl18 calls_x (ELit 0x56180) (ELit 0) calls_x (nth 19 t_sr1b (ELit 0)) t_sr1b).
Definition tl_rvld : list expr := slots2 (EVar 35) (EVar 36) (rvl18 (ELit 1) (ELit 0x56180) (ELit 0) (ELit 1) (nth 19 t_sr1d (ELit 0)) t_sr1d).
Definition tl_rvlm : list expr := slots2 (EVar 36) (EVar 37) (rvl18 (EVar 13) (EVar 56) (EVar 56) (EVar 13) (nth 19 tm_sr3 (ELit 0)) tm_sr3).
(* [comment removed for export] *)
Definition tl_r1 := Eval vm_compute in runT scr0 (SS 0x17bf0 sr_TL [] kn_TL 50).
Definition tl_sr1 := Eval vm_compute in s_regs (fst (fst tl_r1)).
Definition tl_kn1 := Eval vm_compute in kn_after tl_r1 kn_TL.
(* [comment removed for export] *)
Definition LGLOB : list (Z * Z) := ((0x45f10, 0x45f18) :: GLOB)%Z.
Definition kn_fcall (kn : list kentry) : list kentry := kn_call LGLOB (-208 - 16384) (-208) IHI 0x45000 kn.
(* [comment removed for export] *)
Definition tl_sr2i : list expr := Eval vm_compute in sr_upd (sr_after_call_j tl_sr1 KEPT_AL 50) (ridx 10) (ELit 0).
Definition tl_kn2i : list kentry := Eval vm_compute in kn_fcall tl_kn1.
Definition tl_r2 := Eval vm_compute in runT scr0 (SS 0x17c04 tl_sr2i [] tl_kn2i 82).
Definition tl_sr2 := Eval vm_compute in s_regs (fst (fst tl_r2)).
Definition tl_kn2 := Eval vm_compute in kn_after tl_r2 tl_kn2i.
(* [comment removed for export] *)
Definition p_r1 := Eval vm_compute in runP scr0 (SS 0x17cc0 tl_sr2 [] tl_kn2 82).
Definition p_sr1 := Eval vm_compute in s_regs (fst (fst p_r1)).
Definition p_kn1 := Eval vm_compute in kn_after p_r1 tl_kn2.
(* [comment removed for export] *)
Definition p_r2 := Eval vm_compute in runP scr0 (SS 0x3e8e4 (sr_upd p_sr1 (ridx 10) (ELit (2^64 - 25))) [] p_kn1 82).
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
  | KWord (SA (ELit 0) 485696) _ _ => false
  | KWord (SA (ELit 0) _) _ _ => true
  | KWord _ _ _ => false
  | _ => true
  end end.
Definition fixw (K : kentry) : kentry :=
  match K with KWord (SA (ELit 0) 286792) 8 _ => KWord (SA (ELit 0) 286792) 8 (EVar 18) | _ => K end.
Definition kn_TL1 : list kentry := Eval vm_compute in KRange (EVar 18) 0x76940 0x76d38 :: map fixw (List.filter keepTL1 p_kn3).
(* [comment removed for export] *)
Definition rvl18w (e13 e14 e15 e16 e17 ew : expr) (sr : list expr) : list expr :=
  [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; e13; e14; e15; e16; e17; ew] ++ tl sr.
Definition tl1_rvl0 : list expr :=      (* [comment removed for export] *)
  slots2 (EVar 21) (EVar 22) (rvl18w (EVar 13) (EVar 14) (EVar 15) (EAluw ALU_ADD (EVar 16) (ELit (-1))) (nth 19 p_sr3l (ELit 0)) (ELit 0x76940) p_sr3l).
(* [comment removed for export] *)
Definition tl1_r1 := Eval vm_compute in runT scr0 (SS 0x17bf0 sr_TL [] kn_TL1 50).
Definition tl1_sr1 := Eval vm_compute in s_regs (fst (fst tl1_r1)).
Definition tl1_kn1 := Eval vm_compute in kn_after tl1_r1 kn_TL1.
Definition tl1_sr2i : list expr := Eval vm_compute in sr_upd (sr_after_call_j tl1_sr1 KEPT_AL 50) (ridx 10) (ELit 0).
Definition tl1_kn2i : list kentry := Eval vm_compute in kn_fcall tl1_kn1.
Definition tl1_r2 := Eval vm_compute in runT scr0 (SS 0x17c04 tl1_sr2i [] tl1_kn2i 82).
Definition tl1_sr2 := Eval vm_compute in s_regs (fst (fst tl1_r2)).
Definition tl1_kn2 := Eval vm_compute in kn_after tl1_r2 tl1_kn2i.
(* [comment removed for export] *)
Definition tl1_sr3i : list expr := Eval vm_compute in sr_after_call_j tl1_sr2 KEPT_CS 82.
Definition tl1_kn3i : list kentry := Eval vm_compute in
  KWord (SA (ELit 0) 286792) 8 (EAlu ALU_ADD (EVar 18) (ELit 2)) :: KWord (SA (ELit 0) 286752) 4 (ELit 5)
  :: kn_call [(0x46020, 0x46024); (0x46048, 0x46050); (0x76940, 0x76d40)]%Z (-208 - 1056) (-208) IHI 0x45000 tl1_kn2.
Definition tl1_r3l := Eval vm_compute in runT (SCR [true] [] []) (SS 0x17c14 tl1_sr3i [] tl1_kn3i 114).
Definition tl1_r3e := Eval vm_compute in runT (SCR [false] [] []) (SS 0x17c14 tl1_sr3i [] tl1_kn3i 114).
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
  | KWord (SA (ELit 0) 485696) _ _ => false
  | KWord (SA (ELit 0) _) _ _ => true
  | KWord _ _ _ => false
  | KRange (EVar i) _ _ => Nat.ltb i 8
  | KAlign (EVar i) _ => Nat.ltb i 8
  | KDisj _ _ (SA (EVar i) _) _ => Nat.ltb i 8
  | _ => true
  end.
Definition fixw7 (K : kentry) : kentry :=
  match K with KWord (SA (ELit 0) 286792) 8 _ => KWord (SA (ELit 0) 286792) 8 (EVar 7) | _ => K end.
Definition kn_FN1 : list kentry := Eval vm_compute in KRange (EVar 7) 0x76940 0x76d40 :: map fixw7 (List.filter keepFN1 (kn_acallT tl1_kn3)).
Definition sr_FN1 : list expr :=
  [ELit 0; JN 1; spx (-128); ELit 0x10800; ELit 0x56270; JN 5; JN 6; JN 7;
   ELit 0; EVar 6; JN 10; JN 11; JN 12; JN 13; JN 14; JN 15;
   JN 16; JN 17; JN 18; JN 19; JN 20; JN 21; JN 22; JN 23;
   JN 24; JN 25; JN 26; JN 27; JN 28; JN 29; JN 30; JN 31].
(* [comment removed for export] *)
Definition e_sr1p : list expr := Eval vm_compute in sr_after_call_j p_sr3e KEPT_AL 114.
Definition e_kn1p : list kentry := Eval vm_compute in kn_acallT p_kn3.
Definition e_r2pn := Eval vm_compute in runT (SCR [false] [] []) (SS 0x17c30 e_sr1p [] e_kn1p 146).
Definition e_r2pc := Eval vm_compute in runT (SCR [true] [] []) (SS 0x17c30 e_sr1p [] e_kn1p 146).
Definition e_sr1t : list expr := Eval vm_compute in sr_after_call_j tl1_sr3e KEPT_AL 114.
Definition e_kn1t : list kentry := Eval vm_compute in kn_acallT tl1_kn3.
Definition e_r2tn := Eval vm_compute in runT (SCR [false] [] []) (SS 0x17c30 e_sr1t [] e_kn1t 146).
Definition e_r2tc := Eval vm_compute in runT (SCR [true] [] []) (SS 0x17c30 e_sr1t [] e_kn1t 146).
Definition fn1_rvl (ew : expr) (sr : list expr) : list expr := [EVar 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; ew] ++ (ELit 0 :: tl sr).
(* [comment removed for export] *)
Definition fn1_r1 := Eval vm_compute in runT scr0 (SS 0x17a5c sr_FN1 [] kn_FN1 40).
Definition fn1_sr1 := Eval vm_compute in s_regs (fst (fst fn1_r1)).
Definition fn1_kn1 := Eval vm_compute in kn_after fn1_r1 kn_FN1.
Definition fn1_sr2i := Eval vm_compute in sr_after_call_j fn1_sr1 KEPT_AL 40.
Definition fn1_kn2i := Eval vm_compute in kn_acall fn1_kn1.
Definition fn1_r2 := Eval vm_compute in runT scr0 (SS 0x17a64 fn1_sr2i [] fn1_kn2i 72).
Definition fn1_sr2 := Eval vm_compute in s_regs (fst (fst fn1_r2)).
Definition fn1_kn2 := Eval vm_compute in kn_after fn1_r2 fn1_kn2i.

Section VP1.
Lemma t_itin1 :
  (s_pc (fst (fst t_r1a)), snd (fst t_r1a), log_wdl_b 0 [(0x45000, 0x561a0); (0x762b0, 0x764d0); (0x76918, 0x77000)]%Z (s_log (fst (fst t_r1a))))
    = (0x3c370%Z, [SCBr false BC_EQ (EVar 9) (ELit 0); SCBr false BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1c)), snd (fst t_r1c), log_wdl_b 0 [(0x45000, 0x561a0); (0x762b0, 0x764d0); (0x76918, 0x77000)]%Z (s_log (fst (fst t_r1c))))
    = (0x3c370%Z, [SCBr true BC_NE (EVar 9) (ELit 0); SCBr true BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1b)), snd (fst t_r1b), log_wdl_b 0 [(0x45000, 0x561a0); (0x762b0, 0x764d0); (0x76918, 0x77000)]%Z (s_log (fst (fst t_r1b))))
    = (0x17bf0%Z, [SCBr true BC_EQ (EVar 9) (ELit 0); SCBr false BC_EQ (EVar 8) (ELit 0)], true)
  /\ (s_pc (fst (fst t_r1d)), snd (fst t_r1d), log_wdl_b 0 [(0x45000, 0x561a0); (0x762b0, 0x764d0); (0x76918, 0x77000)]%Z (s_log (fst (fst t_r1d))))
    = (0x17bf0%Z, [SCBr false BC_NE (EVar 9) (ELit 0); SCBr true BC_EQ (EVar 8) (ELit 0)], true)
  /\ (sr_mismatch tm_rvla idb t_sr1a sr_TM 0, kn_missing t_kn1 (map (kmap tm_rvla idb) kn_T)) = ([], [])
  /\ (sr_mismatch tm_rvlc idb t_sr1c sr_TM 0, kn_missing (kn_after t_r1c kn_R) (map (kmap tm_rvlc idb) kn_T)) = ([], [])
  /\ (sr_mismatch tl_rvlb idb t_sr1b sr_TL 0, kn_missing (kn_after t_r1b kn_R) (map (kmap tl_rvlb idb) kn_TL)) = ([], [])
  /\ (sr_mismatch tl_rvld idb t_sr1d sr_TL 0, kn_missing (kn_after t_r1d kn_R) (map (kmap tl_rvld idb) kn_TL)) = ([], [])
  /\ calls_x = EAlu ALU_ADD (EAlu ALU_AND (EExt false 0 1 (EVar 11)) (ELit 3)) (ELit 1)
  /\ nth 19 t_sr1b (ELit 0) = EAlu ALU_ADD (EVar 6) (ELit 2) /\ nth 19 t_sr1d (ELit 0) = EAlu ALU_ADD (EVar 6) (ELit 2).
Proof.
  repeat match goal with |- _ /\ _ => split end; first [exact I | vm_compute; reflexivity]. Qed.

Lemma tm_itin :
  (s_pc (fst (fst tm_r2)), snd (fst tm_r2), s_log (fst (fst tm_r2))) = (0x4347c%Z, [], [])
  /\ (nth 1 tm_sr2 (ELit 0), nth 10 tm_sr2 (ELit 0), nth 11 tm_sr2 (ELit 0), nth 12 tm_sr2 (ELit 0)) = (ELit 0x17bb0, EVar 56, EVar 12, EVar 9)
  /\ kn_vars_lt 46 kn_T = true /\ sr_vars_lt 78 tm_sr2 = true /\ kn_vars_lt 78 tm_kn2 = true
  /\ sr_after_call_j tm_sr2 KEPT_MC 78 = tm_sr3i /\ kn_call [(0x1000, 0x10000)%Z] 0 0 IHI 0x45000 tm_kn2 = tm_kn3i /\ kn_vars_lt 78 tm_kn3i = true
  /\ (s_pc (fst (fst tm_r3)), snd (fst tm_r3), s_log (fst (fst tm_r3))) = (0x17bf0%Z, [], [])
  /\ (sr_mismatch tl_rvlm idb tm_sr3 sr_TL 0, kn_missing tm_kn3 (map (kmap tl_rvlm idb) kn_TL)) = ([0%nat], [])
  /\ nth 19 tm_sr3 (ELit 0) = EVar 33.
Proof.
  repeat match goal with |- _ /\ _ => split end; first [exact I | vm_compute; reflexivity]. Qed.

Lemma tn_itin :   (* [comment removed for export] *)
  True /\ True /\ True /\ True
  /\ kn_acallT kn_T = tn_kn1i.
Proof.
  repeat match goal with |- _ /\ _ => split end; first [exact I | vm_compute; reflexivity]. Qed.

Lemma fn_itin :
  (s_pc (fst (fst fn_r1)), snd (fst fn_r1), s_log (fst (fst fn_r1))) = (0x3c230%Z, [], [])
  /\ (nth 1 fn_sr1 (ELit 0), nth 10 fn_sr1 (ELit 0), nth 2 fn_sr1 (ELit 0), nth 4 fn_sr1 (ELit 0))
     = (ELit 0x17a64, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x56270)
  /\ kn_vars_lt 40 fn_kn1 = true /\ kn_acall fn_kn1 = fn_kn2i
  /\ (s_pc (fst (fst fn_r2)), snd (fst fn_r2), s_log (fst (fst fn_r2))) = (0x3bef8%Z, [], [])
  /\ (nth 10 fn_sr2 (ELit 0), nth 2 fn_sr2 (ELit 0), nth 4 fn_sr2 (ELit 0)) = (EVar 7, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x56270).
Proof.
  repeat match goal with |- _ /\ _ => split end; first [exact I | vm_compute; reflexivity]. Qed.

Lemma tl_itin :
  (s_pc (fst (fst tl_r1)), snd (fst tl_r1), s_log (fst (fst tl_r1))) = (0x17d08%Z, [], [SE (SA (ELit 0) 0x56174) 1 (ELit 1)])
  /\ (nth 1 tl_sr1 (ELit 0), nth 10 tl_sr1 (ELit 0), nth 11 tl_sr1 (ELit 0), nth 2 tl_sr1 (ELit 0), nth 3 tl_sr1 (ELit 0), nth 4 tl_sr1 (ELit 0))
     = (ELit 0x17c04, EVar 14, EVar 9, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x10800, ELit 0x56270)
  /\ kn_vars_lt 50 tl_kn1 = true /\ sr_vars_lt 50 tl_sr1 = true /\ kn_fcall tl_kn1 = tl_kn2i
  /\ (s_pc (fst (fst tl_r2)), snd (fst tl_r2), s_log (fst (fst tl_r2))) = (0x17cc0%Z, [], [SE (SA (ELit 0) 0x56174) 1 (ELit 0)])
  /\ (s_pc (fst (fst p_r1)), snd (fst p_r1), log_wdl_b 0 [(0x45000, 0x561a0); (0x762b0, 0x764d0); (0x76918, 0x77000)]%Z (s_log (fst (fst p_r1))))
     = (0x3e8e0%Z, [], true)
  /\ (nth 17 p_sr1 (ELit 0), nth 10 p_sr1 (ELit 0), nth 11 p_sr1 (ELit 0)) = (ELit 29, ELit 1, ELit 0x5413)
  /\ (s_pc (fst (fst p_r2)), snd (fst p_r2), log_wdl_b 0 [(0x45000, 0x561a0); (0x762b0, 0x764d0); (0x76918, 0x77000)]%Z (s_log (fst (fst p_r2))))
     = (0x3e37c%Z, [], true)
  /\ stdio_call 82 p_sr2 p_kn2 = Some p_sc
  /\ (sc_ret p_sc, sc_f p_sc, sc_fd p_sc, sc_s p_sc, sc_l p_sc, sc_wb p_sc, sc_wp p_sc) = (0x3e904%Z, 0x46020%Z, 1%Z, ELit 0x10a4c, ELit 1, ELit 0x76940, ELit 0x76941)
  /\ (s_pc (fst (fst p_r3l)), snd (fst p_r3l), log_wdl_b 0 [(0x45000, 0x561a0); (0x762b0, 0x764d0); (0x76918, 0x77000)]%Z (s_log (fst (fst p_r3l))))
     = (0x17bf0%Z, [SCBr true BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], true)
  /\ (s_pc (fst (fst p_r3e)), snd (fst p_r3e), log_wdl_b 0 [(0x45000, 0x561a0); (0x762b0, 0x764d0); (0x76918, 0x77000)]%Z (s_log (fst (fst p_r3e))))
     = (0x3c230%Z, [SCBr false BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], true)
  /\ kn_after p_r3e p_kn3i = p_kn3
  /\ (nth 10 p_sr3e (ELit 0), nth 1 p_sr3e (ELit 0), nth 2 p_sr3e (ELit 0), nth 4 p_sr3e (ELit 0)) = (EVar 15, ELit 0x17c30, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x56270).
Proof.
  repeat match goal with |- _ /\ _ => split end; first [exact I | vm_compute; reflexivity]. Qed.

Lemma tl1_itin :
  (sr_mismatch tl1_rvl0 idb p_sr3l sr_TL 0, kn_missing p_kn3 (map (kmap tl1_rvl0 idb) kn_TL1)) = ([0%nat], [KRange (ELit 0x76940) 0x76940 0x76d38])
  /\ (s_pc (fst (fst tl1_r1)), snd (fst tl1_r1), s_log (fst (fst tl1_r1))) = (0x17d08%Z, [], [SE (SA (ELit 0) 0x56174) 1 (ELit 1)])
  /\ (nth 1 tl1_sr1 (ELit 0), nth 10 tl1_sr1 (ELit 0), nth 11 tl1_sr1 (ELit 0), nth 2 tl1_sr1 (ELit 0), nth 3 tl1_sr1 (ELit 0), nth 4 tl1_sr1 (ELit 0))
     = (ELit 0x17c04, EVar 14, EVar 9, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x10800, ELit 0x56270)
  /\ kn_vars_lt 50 tl1_kn1 = true /\ sr_vars_lt 50 tl1_sr1 = true /\ kn_fcall tl1_kn1 = tl1_kn2i
  /\ (s_pc (fst (fst tl1_r2)), snd (fst tl1_r2), s_log (fst (fst tl1_r2))) = (0x17cc0%Z, [], [SE (SA (ELit 0) 0x56174) 1 (ELit 0)])
  /\ (nth 1 tl1_sr2 (ELit 0), nth 2 tl1_sr2 (ELit 0), nth 11 tl1_sr2 (ELit 0)) = (ELit 0x17c14, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0)
  /\ sr_vars_lt 82 tl1_sr2 = true /\ kn_vars_lt 82 tl1_kn2 = true
  /\ (s_pc (fst (fst tl1_r3l)), snd (fst tl1_r3l), s_log (fst (fst tl1_r3l))) = (0x17bf0%Z, [SCBr true BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], [])
  /\ (s_pc (fst (fst tl1_r3e)), snd (fst tl1_r3e), s_log (fst (fst tl1_r3e))) = (0x3c230%Z, [SCBr false BC_NE (EAluw ALU_ADD (EVar 16) (ELit (-1))) (ELit 0)], [])
  /\ kn_after tl1_r3e tl1_kn3i = tl1_kn3
  /\ (nth 10 tl1_sr3e (ELit 0), nth 1 tl1_sr3e (ELit 0), nth 2 tl1_sr3e (ELit 0), nth 4 tl1_sr3e (ELit 0)) = (EVar 15, ELit 0x17c30, EAlu ALU_ADD (EVar 0) (ELit (-208)), ELit 0x56270)
  /\ (sr_mismatch tl1_rvl idb tl1_sr3l sr_TL 0, kn_missing tl1_kn3 (map (kmap tl1_rvl idb) kn_TL1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x76940 0x76d38]).
Proof.
  repeat match goal with |- _ /\ _ => split end; first [exact I | vm_compute; reflexivity]. Qed.

Lemma e_itin :
  (s_pc (fst (fst e_r2pn)), snd (fst e_r2pn), log_win_b 0 (s_log (fst (fst e_r2pn)))) = (0x17a5c%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2pc)), snd (fst e_r2pc), log_win_b 0 (s_log (fst (fst e_r2pc)))) = (0x17a5c%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2tn)), snd (fst e_r2tn), log_win_b 0 (s_log (fst (fst e_r2tn)))) = (0x17a5c%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst e_r2tc)), snd (fst e_r2tc), log_win_b 0 (s_log (fst (fst e_r2tc)))) = (0x17a5c%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (let r := e_r2pc in
       (sr_mismatch (fn1_rvl (ELit 0x76940) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1p) (map (kmap (fn1_rvl (ELit 0x76940) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (ELit 0x76940) 0x76940 0x76d40]))
  /\ (let r := e_r2pn in
       (sr_mismatch (fn1_rvl (ELit 0x76940) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1p) (map (kmap (fn1_rvl (ELit 0x76940) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (ELit 0x76940) 0x76940 0x76d40]))
  /\ (let r := e_r2tc in
       (sr_mismatch (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1t) (map (kmap (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x76940 0x76d40]))
  /\ (let r := e_r2tn in
       (sr_mismatch (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r e_kn1t) (map (kmap (fn1_rvl (EAlu ALU_ADD (EVar 18) (ELit 2)) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x76940 0x76d40]))
  /\ kn_vars_lt 114 p_kn3 = true /\ kn_acallT p_kn3 = e_kn1p /\ kn_vars_lt 114 tl1_kn3 = true /\ kn_acallT tl1_kn3 = e_kn1t.
Proof.
  repeat match goal with |- _ /\ _ => split end; first [exact I | vm_compute; reflexivity]. Qed.

Lemma fn1_itin :
  (s_pc (fst (fst fn1_r1)), snd (fst fn1_r1), s_log (fst (fst fn1_r1))) = (0x3c230%Z, [], [])
  /\ (nth 1 fn1_sr1 (ELit 0), nth 10 fn1_sr1 (ELit 0), nth 2 fn1_sr1 (ELit 0), nth 4 fn1_sr1 (ELit 0))
     = (ELit 0x17a64, EVar 6, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 0x56270)
  /\ kn_vars_lt 40 fn1_kn1 = true /\ kn_acall fn1_kn1 = fn1_kn2i
  /\ (s_pc (fst (fst fn1_r2)), snd (fst fn1_r2), s_log (fst (fst fn1_r2))) = (0x3bef8%Z, [], [])
  /\ (nth 10 fn1_sr2 (ELit 0), nth 2 fn1_sr2 (ELit 0), nth 4 fn1_sr2 (ELit 0)) = (ELit 0, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 0x56270).
Proof.
  repeat match goal with |- _ /\ _ => split end; first [exact I | vm_compute; reflexivity]. Qed.
End VP1.

(* [comment removed for export] *)
Definition sr_FE : list expr :=
  [ELit 0; ELit 0x17c30; spx (-208); ELit 0x10800; ELit 0x56270; JL 5; JL 6; JL 7;
   EVar 9; EVar 14; EVar 15; JL 11; JL 12; JL 13; JL 14; JL 15;
   JL 16; JL 17; EVar 15; ELit 18446744073709551615; ELit 0x56170; ELit 0; ELit 0; ELit 18446744073709551614;
   JL 24; JL 25; JL 26; JL 27; JL 28; JL 29; JL 30; JL 31].
Definition kn_FE : list kentry := kn_TL1.
Definition fe_rvlp : list expr :=
  slots2 (EVar 21) (EVar 22) (rvl18w (EVar 13) (EVar 14) (EVar 15) (EVar 16) (nth 19 p_sr3e (ELit 0)) (ELit 0x76940) p_sr3e).
Definition fe_rvlt : list expr :=
  slots2 (EVar 21) (EVar 22) (rvl18w (EVar 13) (EVar 14) (EVar 15) (EVar 16) (nth 19 tl1_sr3e (ELit 0)) (EAlu ALU_ADD (EVar 18) (ELit 2)) tl1_sr3e).
Definition fe_sr1i : list expr := Eval vm_compute in sr_after_call_j sr_FE KEPT_AL 50.
Definition fe_kn1i : list kentry := Eval vm_compute in kn_acallT kn_FE.
Definition fe_r2n := Eval vm_compute in runT (SCR [false] [] []) (SS 0x17c30 fe_sr1i [] fe_kn1i 82).
Definition fe_r2c := Eval vm_compute in runT (SCR [true] [] []) (SS 0x17c30 fe_sr1i [] fe_kn1i 82).

Section VP2.
Lemma fe_itin :
  (sr_mismatch fe_rvlp idb p_sr3e sr_FE 0, kn_missing p_kn3 (map (kmap fe_rvlp idb) kn_FE)) = ([0; 21]%nat, [KRange (ELit 0x76940) 0x76940 0x76d38])
  /\ (sr_mismatch fe_rvlt idb tl1_sr3e sr_FE 0, kn_missing tl1_kn3 (map (kmap fe_rvlt idb) kn_FE)) = ([0; 21]%nat, [KRange (EAlu ALU_ADD (EVar 18) (ELit 2)) 0x76940 0x76d38])
  /\ kn_vars_lt 50 kn_FE = true /\ kn_acallT kn_FE = fe_kn1i
  /\ (s_pc (fst (fst fe_r2n)), snd (fst fe_r2n), log_win_b 0 (s_log (fst (fst fe_r2n)))) = (0x17a5c%Z, [SCBr false BC_LT (EVar 10) (ELit 0)], true)
  /\ (s_pc (fst (fst fe_r2c)), snd (fst fe_r2c), log_win_b 0 (s_log (fst (fst fe_r2c)))) = (0x17a5c%Z, [SCBr true BC_LT (EVar 10) (ELit 0)], true)
  /\ (let r := fe_r2n in
       (sr_mismatch (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r fe_kn1i) (map (kmap (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], []))
  /\ (let r := fe_r2c in
       (sr_mismatch (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb (s_regs (fst (fst r))) sr_FN1 0,
        kn_missing (kn_after r fe_kn1i) (map (kmap (fn1_rvl (EVar 18) (s_regs (fst (fst r)))) idb) kn_FN1)) = ([0%nat], []))
  /\ nth 19 p_sr3e (ELit 0) = ELit 18446744073709551615 /\ nth 19 tl1_sr3e (ELit 0) = ELit 18446744073709551615   (* [comment removed for export] *)
  /\ tl1_sr1 = tl_sr1 /\ tl1_sr2i = tl_sr2i.
Proof.
  repeat match goal with |- _ /\ _ => split end; first [exact I | vm_compute; reflexivity]. Qed.
End VP2.
