(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith LeptRecs LeptSel LeptSlots GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCopyT O23LeptPixHdr O23LeptCmapValid O23LeptCmap2 O23LeptGrayAT O23LeptSelGP O23LeptPma1 O23LeptPma1G O23LeptSelFMT O23LeptHmtW O23LeptHmtNW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23LeptPma1.
From LinuxProcessSemantics.Riscv Require Import Sem Fpu.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExec LeptExecW LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23ExecUb V23LeptErr V23LeptCmap2 V23LeptSelGP V23LeptPixClone V23LeptPma1.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Ltac exB_sc_hook ::= v23_sc_hook.

Lemma cells9_FR9 : forall m s ret regs, (80 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS (O23LeptPma1G.FR9 m s ret regs) (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS (O23LeptPma1G.FR9 m s ret regs) (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
  rdn SEGS (O23LeptPma1G.FR9 m s ret regs) (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
  rdn SEGS (O23LeptPma1G.FR9 m s ret regs) (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\
  rdn SEGS (O23LeptPma1G.FR9 m s ret regs) (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
  rdn SEGS (O23LeptPma1G.FR9 m s ret regs) (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\
  rdn SEGS (O23LeptPma1G.FR9 m s ret regs) (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) /\
  rdn SEGS (O23LeptPma1G.FR9 m s ret regs) (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) /\
  rdn SEGS (O23LeptPma1G.FR9 m s ret regs) (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 23)).
Proof. intros m s ret regs Hs Hs64. unfold O23LeptPma1G.FR9. repeat split; rdn_solve. Qed.

Lemma pm_ne_t : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b ->
  branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof.
  intros a b Ha Hb NE. cbn [branch_taken]. unfold bv_eqb. rewrite !u_Z2bv by lia.
  apply negb_true_iff. apply Z.eqb_neq. exact NE.
Qed.

Lemma pm_eq_f : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b ->
  branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof.
  intros a b Ha Hb NE. cbn [branch_taken]. unfold bv_eqb. rewrite !u_Z2bv by lia.
  apply Z.eqb_neq. exact NE.
Qed.

Section Pma1G.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac pc_as RUN :=
  lazymatch type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?gpc _ _) _) _ => replace gpc with pc by (apply bv_eq; reflexivity) end end.

Lemma FR9_WP : forall C A m md (s s' : Z) ret regs, Cok C -> W C A m md ->
  (c_top C - LSTK <= s - 72)%Z -> (s <= s')%Z -> (s' <= c_top C)%Z ->
  W C A (O23LeptPma1G.FR9 m s ret regs) md /\ POSTM C A s' m (O23LeptPma1G.FR9 m s ret regs).
Proof.
  intros C A m md s s' ret regs CK HW H1 H2 H3. pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold O23LeptPma1G.FR9. wp_win CK.
Qed.

Section Segs.
  Variable rom : word -> option byte.

  Lemma pm_pre : forall regs m (s pd pp : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pp)%Z -> (pp + 8 < 2 ^ 64)%Z -> (pp mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true -> store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pd -> getr regs 13 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0xa1b7c : word) m rom) (mkst regs' (0xa1ba4 : word) (O23LeptPma1.MA m s ret regs pp) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pd /\ getr regs' 14 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [2; 8; 14]%list) regs regs'.
  Proof.
    intros regs m s pd pp ret Hs Hs64 Hp0 Hp64 ALp SOK SOKp H2 H1 H10 H13.
    replace (0xa1b7c : word) with (Z_to_bv 64 0xa1b7c) by (apply bv_eq; reflexivity).
    replace (0xa1ba4 : word) with (Z_to_bv 64 0xa1ba4) by (apply bv_eq; reflexivity).
    ex_entry regs [s; pd; pp] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pd; pp]) m
      [KWr (SA (EVar 32) (-48)) 48; KWr (SA (EVar 34) 0) 8; KAlign (EVar 34) 8;
       KRange (EVar 32) 48 (2 ^ 64 - 1); KRange (EVar 34) 0 (2 ^ 64 - 9)]%Z) by (ex_know regs).
    ex_run 400%nat [0xa1ba4%Z] (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R'. split; [unfold O23LeptPma1.MA, O23LeptCmap2.FR5; subst ret; v23_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
    all: try (rewrite ?Z.add_0_r; first [exact SOK | exact SOKp]).
  Qed.

  (* [comment removed for export] *)
  Lemma pmn_tail : forall regs m (s pd : Z) (ret s0v s1v s2v s3v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0xa1ba4 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10355 /\ getr regs' 11 = Z_to_bv 64 0x1b54a
      /\ getr regs' 12 = Z_to_bv 64 pd /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pd ret s0v s1v s2v s3v Hs Hs64 RG RV R0 R1 R2 R3 R4 H2 H8 H11.
    replace (0xa1ba4 : word) with (Z_to_bv 64 0xa1ba4) by (apply bv_eq; reflexivity).
    replace (0x63740 : word) with (Z_to_bv 64 0x63740) by (apply bv_eq; reflexivity).
    ex_entryL [ret; s0v; s1v; s2v; s3v] regs [s; pd] HR.
    assert (HK : know_ok SEGS (ex_envL [ret; s0v; s1v; s2v; s3v] regs [s; pd]) m
      [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3);
       KWord (SA (EVar 37) (-8)) 8 (EVar 0); KWord (SA (EVar 37) (-16)) 8 (EVar 1); KWord (SA (EVar 37) (-24)) 8 (EVar 2);
       KWord (SA (EVar 37) (-32)) 8 (EVar 3); KWord (SA (EVar 37) (-40)) 8 (EVar 4);
       KRange (EVar 37) 48 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0x63740%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR'].
  Qed.

  (* [comment removed for export] *)
  Lemma pmg_tail : forall regs m (s pd pixs sel pp : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs + 64 <= 2 ^ 64)%Z -> (pixs mod 8 = 0)%Z -> (1 <= sel < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 sel ->
    getr regs 13 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0xa1ba4 : word) m rom) (mkst regs' (0xa4fd0 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0xa1be0
      /\ getr regs' 10 = Z_to_bv 64 sel /\ getr regs' 11 = Z_to_bv 64 (s - 44) /\ getr regs' 12 = Z_to_bv 64 (s - 48)
      /\ getr regs' 13 = Z_to_bv 64 0 /\ getr regs' 14 = Z_to_bv 64 0
      /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 sel /\ getr regs' 19 = Z_to_bv 64 pp
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 14; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pd pixs sel pp Hs Hs64 Hp1 Hp64 ALp Hsel RD H2 H8 H11 H12 H13.
    replace (0xa1ba4 : word) with (Z_to_bv 64 0xa1ba4) by (apply bv_eq; reflexivity).
    replace (0xa4fd0 : word) with (Z_to_bv 64 0xa4fd0) by (apply bv_eq; reflexivity).
    ex_entry regs [s; pd; pixs; sel; pp] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pd; pixs; sel; pp]) m
      [KWord (SA (EVar 34) 8) 4 (ELit 1); KAlign (EVar 34) 8;
       KRange (EVar 32) 48 (2 ^ 64 - 1); KRange (EVar 34) 1 (2 ^ 64 - 64); KRange (EVar 35) 1 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0xa4fd0%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR'].
  Qed.

  (* [comment removed for export] *)
  Lemma pmg_C : forall regs m (s pd pixs sy sx : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= sy < 2 ^ 31)%Z -> (1 <= sx < 2 ^ 31)%Z -> (1 <= pd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 44)) 4 = Some (Z_to_le_bytes 4 sy) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 4 = Some (Z_to_le_bytes 4 sx) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pd -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0xa1be0 : word) m rom) (mkst regs' (0x6edec : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa1c00 /\ getr regs' 10 = Z_to_bv 64 pd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s pd pixs sy sx Hs Hs64 Hsy Hsx Hpd RY RX H2 H8 H9.
    replace (0xa1be0 : word) with (Z_to_bv 64 0xa1be0) by (apply bv_eq; reflexivity).
    replace (0x6edec : word) with (Z_to_bv 64 0x6edec) by (apply bv_eq; reflexivity).
    ex_entry regs [s; pd; pixs; sy; sx] HR.
    assert (HK : know_ok SEGS (ex_env regs [s; pd; pixs; sy; sx]) m
      [KWord (SA (EVar 32) (-44)) 4 (EVar 35); KWord (SA (EVar 32) (-48)) 4 (EVar 36);
       KRange (EVar 32) 48 (2 ^ 64 - 1); KRange (EVar 33) 1 (2 ^ 64 - 1);
       KRange (EVar 35) 1 (2 ^ 31 - 1); KRange (EVar 36) 1 (2 ^ 31 - 1)]%Z) by (ex_know regs).
    ex_run 100%nat [0x6edec%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR'].
  Qed.

  (* [comment removed for export] *)
  Lemma pmg_D : forall regs m (pd pixs : Z),
    (0 <= pd < 2 ^ 64)%Z -> (0 <= pixs < 2 ^ 64)%Z -> pd <> pixs -> getr regs 8 = Z_to_bv 64 pd -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0xa1c00 : word) m rom) (mkst regs' (0x6eb08 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa1d20 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m pd pixs Hpd Hpx NE H8 H9.
    replace (0xa1c00 : word) with (Z_to_bv 64 0xa1c00) by (apply bv_eq; reflexivity).
    replace (0x6eb08 : word) with (Z_to_bv 64 0x6eb08) by (apply bv_eq; reflexivity).
    ex_entry regs [pd; pixs] HR.
    assert (HK : know_ok SEGS (ex_env regs [pd; pixs]) m
      [KRange (EVar 32) 0 (2 ^ 64 - 1); KRange (EVar 33) 0 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 100%nat [0x6eb08%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    { exists R'. split; [ex_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR']. }
    all: try (apply pm_ne_t; lia).
  Qed.

  Lemma prd_1 : forall regs m (s : Z) (ret : word),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 80)) 80 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret ->
    exists regs',
      msteps SEGS (mkst regs (0x6edec : word) m rom) (mkst regs' (0x6ee14 : word) (O23LeptPma1G.FR9 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 80) /\ regs_agree (fun r => In r [2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1.
    replace (0x6edec : word) with (Z_to_bv 64 0x6edec) by (apply bv_eq; reflexivity).
    replace (0x6ee14 : word) with (Z_to_bv 64 0x6ee14) by (apply bv_eq; reflexivity).
    ex_entry regs [s] HR.
    assert (HK : know_ok SEGS (ex_env regs [s]) m [KWr (SA (EVar 32) (-80)) 80; KRange (EVar 32) 80 (2 ^ 64 - 1)]%Z) by (ex_know regs).
    ex_run 100%nat [0x6ee14%Z] (SCR [] [] []) HR HK R' HR' Hms.
    exists R'. split; [unfold O23LeptPma1G.FR9; subst ret; v23_mem regs Hms | repeat split; try (v23_reg regs HR'); ex_agree HR HR'].
  Qed.

  Lemma prd_2 : forall regs m (s pd pixs w h d : Z) (ret v8 v9 v18 v19 v20 v21 v22 v23 : word),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> (1 <= pd)%Z -> (pd + 12 <= 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs + 12 <= 2 ^ 64)%Z ->
    pd <> pixs -> (pd mod 8 = 0)%Z -> (pixs mod 8 = 0)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> (0 <= d < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 pixs) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
    rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
    rdn SEGS m (Z_to_bv 64 pd) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (pd + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
    rdn SEGS m (Z_to_bv 64 (pd + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v19) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
    rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 v21) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
    rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
    getr regs 2 = Z_to_bv 64 (s - 80) -> getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6ee14 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\ getr regs' 18 = v18 /\ getr regs' 19 = v19
      /\ getr regs' 20 = v20 /\ getr regs' 21 = v21 /\ getr regs' 22 = v22 /\ getr regs' 23 = v23
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23]%list) regs regs'.
  Proof.
    intros regs m s pd pixs w h d ret v8 v9 v18 v19 v20 v21 v22 v23 Hs Hs64 Hret Hd1 Hd64 Hp1 Hp64 NE ALd ALs Hw Hh Hdd
      Rsw Rsh Rsd Rdw Rdh Rdd C0 C1 C2 C3 C4 C5 C6 C7 C8 H2 H10 H11.
    replace (0x6ee14 : word) with (Z_to_bv 64 0x6ee14) by (apply bv_eq; reflexivity).
    ex_entryL [ret; v8; v9; v18; v19; v20; v21; v22; v23] regs [s; pd; pixs; w; h; d] HR.
    assert (HK : know_ok SEGS (ex_envL [ret; v8; v9; v18; v19; v20; v21; v22; v23] regs [s; pd; pixs; w; h; d]) m
      [KWord (SA (EVar 43) 0) 4 (EVar 44); KWord (SA (EVar 43) 4) 4 (EVar 45); KWord (SA (EVar 43) 8) 4 (EVar 46);
       KWord (SA (EVar 42) 0) 4 (EVar 44); KWord (SA (EVar 42) 4) 4 (EVar 45); KWord (SA (EVar 42) 8) 4 (EVar 46);
       KWord (SA (EVar 41) (-8)) 8 (EVar 0); KWord (SA (EVar 41) (-16)) 8 (EVar 1); KWord (SA (EVar 41) (-24)) 8 (EVar 2);
       KWord (SA (EVar 41) (-32)) 8 (EVar 3); KWord (SA (EVar 41) (-40)) 8 (EVar 4); KWord (SA (EVar 41) (-48)) 8 (EVar 5);
       KWord (SA (EVar 41) (-56)) 8 (EVar 6); KWord (SA (EVar 41) (-64)) 8 (EVar 7); KWord (SA (EVar 41) (-72)) 8 (EVar 8);
       KAlign (EVar 42) 8; KAlign (EVar 43) 8;
       KRange (EVar 41) 80 (2 ^ 64 - 1); KRange (EVar 42) 1 (2 ^ 64 - 12); KRange (EVar 43) 1 (2 ^ 64 - 12);
       KRange (EVar 44) 0 (2 ^ 31 - 1); KRange (EVar 45) 0 (2 ^ 31 - 1); KRange (EVar 46) 0 (2 ^ 31 - 1)]%Z) by (ex_know regs).
    ex_run 400%nat [0x6f084%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    all: cycle -1.
    { assert (E1 : getr R' 1 = ret) by (ex_reg regs HR').
      exists R'. split.
      - cbn [s_pc] in Hms.
        assert (F : fetch_word SEGS (Z_to_bv 64 0x6f084) = Some (0x00008067 : bv 32)) by v23_vm_refl.
        assert (D : decode_any (0x00008067 : bv 32) = Some (Jalr 0 1 0, 4%Z)) by v23_vm_refl.
        eapply ex_msteps_snoc; [ex_mem regs Hms | reflexivity |].
        rewrite (step_jalr_x0 _ _ _ _ _ _ _ _ _ F eq_refl D E1).
        change (v_jalr ret (bv_signed (0 : bv 12))) with (v_jalr ret 0). rewrite (Hret : v_jalr ret 0 = ret). reflexivity.
      - repeat split; try (v23_reg regs HR'); ex_agree HR HR'. }
    all: try (apply pm_eq_f; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma prd_eq_run : forall regs m (s pd pixs : Z) (vd vs : pixv) (ret : word),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> (1 <= pd < 2 ^ 64)%Z -> (1 <= pixs < 2 ^ 64)%Z -> pd <> pixs -> (pd mod 8 = 0)%Z -> (pixs mod 8 = 0)%Z ->
    PIXat (O23LeptPma1G.FR9 m s ret regs) pd vd -> PIXat (O23LeptPma1G.FR9 m s ret regs) pixs vs ->
    p_w vd = p_w vs -> p_h vd = p_h vs -> p_d vd = p_d vs ->
    store_ok SEGS m (Z_to_bv 64 (s - 80)) 80 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6edec : word) m rom) (mkst regs' ret (O23LeptPma1G.FR9 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 13; 18; 19; 20; 21; 22; 23]%list) regs regs'.
  Proof.
    intros regs m s pd pixs vd vs ret Hs Hs64 Hret Hpd Hpx NE ALd ALs PXd PXs Ew Eh Ed SOK H2 H1 H10 H11.
    pose proof PXd as (Hd0 & Hd64 & _). pose proof PXs as (Hx0 & Hx64 & WFs & _).
    pose proof (wf_w _ WFs). pose proof (wf_h _ WFs). pose proof (wf_d _ WFs).
    destruct (prd_1 regs m s ret Hs Hs64 SOK H2 H1) as (r1 & RUN1 & Q2 & AG1).
    pose proof (cells9_FR9 m s ret regs Hs Hs64) as (C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
    pose proof (PIX_rd_w SEGS _ pixs vs PXs) as Rsw. pose proof (PIX_rd_h SEGS _ pixs vs PXs) as Rsh.
    pose proof (PIX_rd_d SEGS _ pixs vs PXs) as Rsd.
    pose proof (PIX_rd_w SEGS _ pd vd PXd) as Rdw. pose proof (PIX_rd_h SEGS _ pd vd PXd) as Rdh.
    pose proof (PIX_rd_d SEGS _ pd vd PXd) as Rdd.
    rewrite Ew in Rdw. rewrite Eh in Rdh. rewrite Ed in Rdd.
    destruct (prd_2 r1 (O23LeptPma1G.FR9 m s ret regs) s pd pixs (p_w vs) (p_h vs) (p_d vs) ret
                (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
                Hs Hs64 Hret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) NE ALd ALs ltac:(lia) ltac:(lia) ltac:(lia) Rsw Rsh Rsd Rdw Rdh Rdd
                C0 C1 C2 C3 C4 C5 C6 C7 C8 Q2 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (r2 & RUN2 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & AG2).
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2] |].
    repeat split; try assumption.
    eapply regs_agree_trans; [eapply regs_agree_mono; [| exact AG1] | eapply regs_agree_mono; [| exact AG2]];
      intros r Hr; cbn [In] in Hr |- *; tauto.
  Qed.
End Segs.

Lemma str_pixs_nd : str16 0x10355 16.
Proof. str16_tac. Qed.     (* [comment removed for export] *)

(* [comment removed for export] *)
Theorem pma1_given_W : forall C A m md regs (s pd pixs sel pp w h cm datas sy sx cy cx sdata sname : Z) (vd : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + O23LeptPma1G.PMA1G_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 sel -> getr regs 13 = Z_to_bv 64 pp ->
  (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  PIXat m pd vd -> p_w vd = w -> p_h vd = h -> p_d vd = 1%Z -> live A (Z_to_bv 64 pd) = Some 64%Z -> pd <> pixs ->
  RECat m sel (sel_flds sy sx cy cx sdata sname) -> live A (Z_to_bv 64 sel) = Some 32%Z -> (1 <= sy < 2 ^ 31)%Z -> (1 <= sx < 2 ^ 31)%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s (O23LeptPma1.clone_mem m pixs pp) m' -> getr regs' 10 = Z_to_bv 64 pd ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa1b7c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pd pixs sel pp w h cm datas sy sx cy cx sdata sname vd ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13
    Hpp Hpp8 ALpp PXs Lps L0s PXd Ew Eh Ed Lpd NE RC Lsel Hsy Hsx HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold O23LeptPma1G.PMA1G_STACK in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof PXs as (Hs0 & Hs64' & WFs & _). pose proof PXd as (Hd0 & Hd64' & WFd & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (blk_range C A m md (Z_to_bv 64 pd) 64 CK HW Lpd ltac:(lia)) as [Gpd TOPpd]. rewrite u_Z2bv in Gpd, TOPpd by lia.
  pose proof (RECat_range _ _ _ RC) as [Hsel0 Hsel32].
  change (Z.of_nat (flds_len (sel_flds sy sx cy cx sdata sname))) with 32%Z in Hsel32.
  destruct (blk_range C A m md (Z_to_bv 64 sel) 32 CK HW Lsel ltac:(lia)) as [Gsel TOPsel]. rewrite u_Z2bv in Gsel, TOPsel by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lpd) as (_ & ALpd & _). rewrite u_Z2bv in ALpd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lsel) as (_ & ALsel & _). rewrite u_Z2bv in ALsel by lia.
  set (M1 := O23LeptPma1.MA m s ret regs pp).
  assert (OUT1 : forall x : word, (bv_unsigned x < s - 48)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold O23LeptPma1.MA, O23LeptCmap2.FR5.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia. reflexivity. }
  destruct (pm_pre al_rom regs m s pd pp ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALpp
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia))
              (W_sok_win C A m md pp 8 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H13)
    as (r1 & RUN1 & Q2 & Q8 & Q14 & AG1).
  rzs HW RUN1.
  assert (WP0 : W C A (O23LeptCmap2.FR5 m s ret regs) md /\ POSTM C A s m (O23LeptCmap2.FR5 m s ret regs))
    by (unfold O23LeptCmap2.FR5; wp_win CK).
  destruct WP0 as [HW0 PM0].
  assert (HW1 : W C A M1 md).
  { subst M1. unfold O23LeptPma1.MA. apply (W_store_win C A _ md); [exact CK | exact HW0 | rewrite u_Z2bv by lia; lia | lenb]. }
  assert (PM1 : POSTM C A s (O23LeptPma1.null_mem m pp) M1).
  { subst M1. unfold O23LeptPma1.MA, O23LeptPma1.null_mem. apply pma1_POSTM_wb2; [lenb | exact PM0]. }
  assert (PXs1 : PIXat M1 pixs (O23LeptPixCopyT.hdv w h 1 cm datas)) by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT1; lia]).
  destruct (pmg_tail al_rom r1 M1 s pd pixs sel pp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (al16_mod8 _ ALps) ltac:(lia)
              (PIX_rd_d SEGS _ _ _ PXs1) Q2 Q8 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P13 & P14 & P9 & P18 & P19 & AG2).
  rzs HW1 RUN2.
  set (M2 := O23LeptSelGP.SGP2 M1 (s - 44) (s - 48) sy sx).
  assert (OUT2 : forall x : word, ~ (s - 48 <= bv_unsigned x < s - 40)%Z -> M2 x = M1 x).
  { intros x Hx. subst M2. apply O23LeptSelGP.SGP2_out; unfold O23LeptSelGP.cell_ok; lia. }
  assert (RC1 : RECat M1 sel (sel_flds sy sx cy cx sdata sname)).
  { apply (RECat_frame m); [exact RC|]. intros x Hx. change (Z.of_nat (flds_len (sel_flds sy sx cy cx sdata sname))) with 32%Z in Hx.
    apply OUT1. lia. }
  destruct (sgp2_run al_rom r2 M1 sel (s - 44) (s - 48) sy sx cy cx sdata sname (Z_to_bv 64 0xa1be0) RC1 ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold O23LeptSelGP.cell_ok; lia) ltac:(unfold O23LeptSelGP.cell_ok; lia)
              (W_sok_win C A M1 md (s - 44) 4 CK HW1 ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A M1 md (s - 48) 4 CK HW1 ltac:(lia) ltac:(cbn; lia))
              ltac:(lia) ltac:(lia) (al16_mod8 _ ALsel) (sp_slot_al4' s 44 Hs16 eq_refl) (sp_slot_al4' s 48 Hs16 eq_refl)
              P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13 P14)
    as (r3 & RUN3 & R10 & AG3).
  rzs HW1 RUN3.
  assert (INC2 : forall a : word, M2 a <> M1 a -> (s - 48 <= bv_unsigned a < s - 40)%Z).
  { intros a NEa. destruct (Z_le_gt_dec (s - 48) (bv_unsigned a)); destruct (Z_lt_ge_dec (bv_unsigned a) (s - 40)); try lia;
      exfalso; apply NEa; apply OUT2; lia. }
  assert (HW2 : W C A M2 md).
  { apply (W_local C A M1 md M2 s CK HW1 Hhi); [| subst M2; apply O23LeptSelGP.SGP2_grows].
    intros a NEa. left. unfold scratch. pose proof (INC2 a NEa). lia. }
  assert (PM2 : POSTM C A s M1 M2) by (apply (POSTM_range C A M1 md M2 (s - 48) (s - 40) s CK HW1 OUT2); lia).
  destruct (SGP2_rd M1 (s - 44) (s - 48) sy sx ltac:(unfold O23LeptSelGP.cell_ok; lia) ltac:(unfold O23LeptSelGP.cell_ok; lia)
              ltac:(unfold O23LeptSelGP.cell_apart; lia) ltac:(lia) ltac:(lia)) as [Ry Rx].
  destruct (pmg_C al_rom r3 M2 s pd pixs sy sx ltac:(lia) ltac:(lia) Hsy Hsx ltac:(lia) Ry Rx
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r4 & RUN4 & S1 & S10 & S11 & AG4).
  pc_as RUN4. rzs HW2 RUN4.
  assert (OUT5 : forall x : word, (bv_unsigned x < s - 48 - 72)%Z -> O23LeptPma1G.FR9 M2 (s - 48) (Z_to_bv 64 0xa1c00) r4 x = m x).
  { intros x Hx. rewrite O23LeptPma1G.FR9_out by lia. rewrite OUT2 by lia. apply OUT1. lia. }
  assert (PXd5 : PIXat (O23LeptPma1G.FR9 M2 (s - 48) (Z_to_bv 64 0xa1c00) r4) pd vd)
    by (apply (PIXat_frame m); [exact PXd | intros x Hx; apply OUT5; lia]).
  assert (PXs5 : PIXat (O23LeptPma1G.FR9 M2 (s - 48) (Z_to_bv 64 0xa1c00) r4) pixs (O23LeptPixCopyT.hdv w h 1 cm datas))
    by (apply (PIXat_frame m); [exact PXs | intros x Hx; apply OUT5; lia]).
  destruct (prd_eq_run al_rom r4 M2 (s - 48) pd pixs vd (O23LeptPixCopyT.hdv w h 1 cm datas) (Z_to_bv 64 0xa1c00)
              ltac:(lia) ltac:(lia) ltac:(red; apply bv_eq; reflexivity) ltac:(lia) ltac:(lia) NE (al16_mod8 _ ALpd) (al16_mod8 _ ALps)
              PXd5 PXs5 Ew Eh Ed (W_sok_win C A M2 md (s - 48 - 80) 80 CK HW2 ltac:(lia) ltac:(cbn; lia))
              ltac:(csr; reflexivity) S1 S10 S11)
    as (r5 & RUN5 & U2 & U1 & U10 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & U23 & AG5).
  rzs HW2 RUN5.
  set (M5 := O23LeptPma1G.FR9 M2 (s - 48) (Z_to_bv 64 0xa1c00) r4) in *.
  destruct (FR9_WP C A M2 md (s - 48) s (Z_to_bv 64 0xa1c00) r4 CK HW2 ltac:(lia) ltac:(lia) Hhi) as [HW5 PM5].
  destruct (pmg_D al_rom r5 M5 pd pixs ltac:(lia) ltac:(lia) NE ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r6 & RUN6 & D1 & D10 & AG6).
  pc_as RUN6. rzs HW5 RUN6.
  replace (0x6eb08 : word) with (Z_to_bv 64 PC_pixClone) by (apply bv_eq; reflexivity).
  apply (pixClone_W fx C A M5 md r6 (s - 48) pixs (O23LeptPixCopyT.hdv w h 1 cm datas) (Z_to_bv 64 0xa1d20) S CK HW5 ltac:(csr; reflexivity)
           ltac:(lia) ltac:(lia) D1 ltac:(red; apply bv_eq; reflexivity) D10 PXs5 eq_refl Lps L0s).
  intros m7 r7 Em7 HW7 CS7 V10.
  assert (OUT7 : forall x : word, ~ (pixs + 20 <= bv_unsigned x < pixs + 24)%Z -> m7 x = M5 x).
  { intros x Hx. rewrite Em7. rewrite wbytes_outside; [reflexivity | lenb | lenb]. }
  set (m8 := wbytes m7 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 pixs))).
  assert (OUT8 : forall x : word, ~ (pp <= bv_unsigned x < pp + 8)%Z -> m8 x = m7 x).
  { intros x Hx. subst m8. rewrite wbytes_outside; [reflexivity | lenb | lenb]. }
  assert (CE8 : cells5 m8 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  { pose proof (cells5_FR5 m s ret regs ltac:(lia) ltac:(lia)) as CE0.
    apply (cells5_out m7 m8 pp (pp + 8) s); [exact OUT8 | lia | lia | lia |].
    apply (cells5_out M5 m7 (pixs + 20) (pixs + 24) s); [exact OUT7 | lia | lia | lia |].
    apply (cells5_out M2 M5 (s - 48 - 72) (s - 48) s); [intros x Hx; subst M5; apply O23LeptPma1G.FR9_out; lia | lia | lia | lia |].
    apply (cells5_out M1 M2 (s - 48) (s - 40) s); [exact OUT2 | lia | lia | lia |].
    apply (cells5_out (O23LeptCmap2.FR5 m s ret regs) M1 pp (pp + 8) s); [| lia | lia | lia | exact CE0].
    intros x Hx. subst M1. unfold O23LeptPma1.MA. rewrite wbytes_outside; [reflexivity | lenb | lenb]. }
  destruct (pma_E al_rom r7 m7 s pp pd pixs ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) Hret ltac:(lia) ltac:(lia)
              CE8 (W_sok_win C A m7 md pp 8 CK HW7 ltac:(lia) ltac:(cbn; lia)) ltac:(csr; reflexivity) V10 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r8 & RUN8 & E2 & E1 & E10 & E8 & E9 & E18 & E19 & AG8).
  pc_as RUN8. rzs HW7 RUN8.
  assert (HW8 : W C A m8 md).
  { subst m8. apply (W_store_win C A m7 md); [exact CK | exact HW7 | rewrite u_Z2bv by lia; lia | lenb]. }
  apply (HK m8 r8 HW8).
  - apply cs_kept_intro; csr; reflexivity.
  - apply (POSTM_trans C A s _ (wbytes (wbytes (O23LeptPma1.null_mem m pp) (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 pixs)))).
    + apply pma1_POSTM_ext. intros x. unfold O23LeptPma1.clone_mem, O23LeptPma1.null_mem.
      apply pma1_wb_same; [lenb |]. intros Hx. apply pma1_wb_same; [lenb |]. intros _.
      rewrite wbytes_outside; [reflexivity | lenb | revert Hx; lenb].
    + subst m8. rewrite Em7. apply pma1_POSTM_wb2; [lenb |]. apply pma1_POSTM_wb2; [lenb |].
      eapply POSTM_trans; [exact PM1 |]. eapply POSTM_trans; [exact PM2 |]. exact PM5.
  - exact E10.
Qed.

(* [comment removed for export] *)
Theorem pma1_nullpixs_W : forall C A m md regs (s pd pp : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + O23LeptPma1G.PMA1N_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pd -> getr regs 11 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 pp ->
  (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z -> (0 <= pd < 2 ^ 64)%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s (O23LeptPma1.null_mem m pp) m' -> getr regs' 10 = Z_to_bv 64 pd ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa1b7c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pd pp ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H13 Hpp Hpp8 ALp Hpd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold O23LeptPma1G.PMA1N_STACK, O23LeptBase.LSF in Hlo.
  destruct (pm_pre al_rom regs m s pd pp ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALp
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia))
              (W_sok_win C A m md pp 8 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H13)
    as (r1 & RUN1 & Q2 & Q8 & Q14 & AG1).
  assert (WP0 : W C A (O23LeptCmap2.FR5 m s ret regs) md /\ POSTM C A s m (O23LeptCmap2.FR5 m s ret regs))
    by (unfold O23LeptCmap2.FR5; wp_win CK).
  destruct WP0 as [HW0 PM0].
  assert (HWa : W C A (O23LeptPma1.MA m s ret regs pp) md).
  { unfold O23LeptPma1.MA. apply (W_store_win C A _ md); [exact CK | exact HW0 | rewrite u_Z2bv by lia; lia | lenb]. }
  assert (PMa : POSTM C A s (O23LeptPma1.null_mem m pp) (O23LeptPma1.MA m s ret regs pp)).
  { unfold O23LeptPma1.MA, O23LeptPma1.null_mem. apply pma1_POSTM_wb2; [lenb | exact PM0]. }
  assert (R0 : rdn SEGS (O23LeptPma1.MA m s ret regs pp) (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret))
    by (unfold O23LeptPma1.MA, O23LeptCmap2.FR5; rdn_solve).
  assert (R1 : rdn SEGS (O23LeptPma1.MA m s ret regs pp) (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)))
    by (unfold O23LeptPma1.MA, O23LeptCmap2.FR5; rdn_solve).
  assert (R2 : rdn SEGS (O23LeptPma1.MA m s ret regs pp) (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)))
    by (unfold O23LeptPma1.MA, O23LeptCmap2.FR5; rdn_solve).
  assert (R3 : rdn SEGS (O23LeptPma1.MA m s ret regs pp) (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)))
    by (unfold O23LeptPma1.MA, O23LeptCmap2.FR5; rdn_solve).
  assert (R4 : rdn SEGS (O23LeptPma1.MA m s ret regs pp) (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)))
    by (unfold O23LeptPma1.MA, O23LeptCmap2.FR5; rdn_solve).
  destruct (pmn_tail al_rom r1 _ s pd ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia)
              (W_sev_got C A _ md HWa) (W_sev C A _ md HWa) R0 R1 R2 R3 R4 Q2 Q8 ltac:(csr; reflexivity))
    as (r2 & RUN2 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & AG2).
  rzs HW RUN1. rzs HWa RUN2.
  apply (returnErrorPtr_W C A _ md r2 s _ _ 16 17 ret (Z_to_bv 64 pd) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi
           V1 Hret V10 V11 V12 str_pixs_nd str_pma1).
  intros m' r' HW' OUT' GR' CS' V10'.
  apply (HK m' r' HW').
  - eapply cs_kept_trans; [| exact CS']. apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PMa |].
    exact (POSTM_range C A _ md m' (s - (16 + LSF)) s s CK HWa OUT' ltac:(unfold LSF; lia) ltac:(lia) Hhi).
  - exact V10'.
Qed.

End Pma1G.
