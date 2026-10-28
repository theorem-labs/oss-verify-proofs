(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptExec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptErr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptCmap2.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Segs.
Context {fx : FPState}.
Variable rom : word -> option byte.

Lemma cn_urange : forall x : word, (0 <= bv_unsigned x < 2 ^ 64)%Z.
Proof. intros x. pose proof (bv_unsigned_in_range _ x) as R. change (bv_modulus 64) with (2 ^ 64)%Z in R. exact R. Qed.

Lemma cn_rdn_w2z : forall (m : word -> option byte) (a : Z) (x : word),
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 x) -> rdn SEGS m (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 (bv_unsigned x)).
Proof.
  intros m a x H. pose proof (cn_urange x) as Rx.
  rewrite <- (w2b_Z 8 (bv_unsigned x) Rx), zbv_self. exact H.
Qed.

(* [comment removed for export] *)
Lemma rbn_run : forall regs m,
  rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
  getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (0x711d4 : word) m rom) (mkst regs' (0x63740 : word) m rom)
    /\ getr regs' 10 = Z_to_bv 64 0x10355 /\ getr regs' 11 = Z_to_bv 64 0x1712a /\ getr regs' 12 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
Proof.
  intros regs m RG RS H10.
  replace (0x711d4 : word) with (Z_to_bv 64 0x711d4) by (apply bv_eq; reflexivity).
  replace (0x63740 : word) with (Z_to_bv 64 0x63740) by (apply bv_eq; reflexivity).
  ex_entry regs (@nil Z) HR.
  assert (HK : know_ok SEGS (ex_env regs (@nil Z)) m
    [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3)]%Z) by (ex_know regs).
  ex_run 100%nat [0x63740%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma pcn_A : forall regs m (s pixd : Z) (ret : word),
  (48 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 0 ->
  exists regs',
    msteps SEGS (mkst regs (0x6eb5c : word) m rom) (mkst regs' (0x6ebf8 : word) (O23LeptCmap2.FR5 m s ret regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pixd
    /\ regs_agree (fun r => In r [2; 8]%list) regs regs'.
Proof.
  intros regs m s pixd ret Hs Hs64 SOK H2 H1 H10 H11.
  replace (0x6eb5c : word) with (Z_to_bv 64 0x6eb5c) by (apply bv_eq; reflexivity).
  replace (0x6ebf8 : word) with (Z_to_bv 64 0x6ebf8) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixd] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixd]) m [KWr (SA (EVar 32) (-48)) 48]%Z) by (ex_know regs).
  ex_run 100%nat [0x6ebf8%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - unfold O23LeptCmap2.FR5. subst ret. ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); ex_agree HR HR'.
Qed.

(* [comment removed for export] *)
Lemma pcn_N : forall regs m (s pixd : Z) (ret v0 v1 v2 v3 : word),
  (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v0) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v1) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 v2) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 v3) ->
  getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pixd ->
  exists regs',
    msteps SEGS (mkst regs (0x6ebf8 : word) m rom) (mkst regs' (0x63740 : word) m rom)
    /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10355 /\ getr regs' 11 = Z_to_bv 64 0x18bc4
    /\ getr regs' 12 = Z_to_bv 64 pixd
    /\ getr regs' 8 = v0 /\ getr regs' 9 = v1 /\ getr regs' 18 = v2 /\ getr regs' 19 = v3
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19]%list) regs regs'.
Proof.
  intros regs m s pixd ret v0 v1 v2 v3 Hs Hs64 RG RS R8 R16 R24 R32 R40 H2 H8.
  apply cn_rdn_w2z in R8, R16, R24, R32, R40.
  pose proof (cn_urange ret) as Wr. pose proof (cn_urange v0) as W0. pose proof (cn_urange v1) as W1.
  pose proof (cn_urange v2) as W2. pose proof (cn_urange v3) as W3.
  replace (0x6ebf8 : word) with (Z_to_bv 64 0x6ebf8) by (apply bv_eq; reflexivity).
  replace (0x63740 : word) with (Z_to_bv 64 0x63740) by (apply bv_eq; reflexivity).
  ex_entry regs [s; pixd; bv_unsigned ret; bv_unsigned v0; bv_unsigned v1; bv_unsigned v2; bv_unsigned v3] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pixd; bv_unsigned ret; bv_unsigned v0; bv_unsigned v1; bv_unsigned v2; bv_unsigned v3]) m
    [KWord (SA (ELit 0) 0x126a70) 8 (ELit 0x127c60); KWord (SA (ELit 0) 0x127c60) 4 (ELit 3);
     KWord (SA (EVar 32) (-8)) 8 (EVar 34); KWord (SA (EVar 32) (-16)) 8 (EVar 35); KWord (SA (EVar 32) (-24)) 8 (EVar 36);
     KWord (SA (EVar 32) (-32)) 8 (EVar 37); KWord (SA (EVar 32) (-40)) 8 (EVar 38)]%Z) by (ex_know regs).
  ex_run 100%nat [0x63740%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split.
  - ex_mem regs Hms.
  - repeat split; try (ex_reg regs HR'); try (apply zbv_self); ex_agree HR HR'.
Qed.

End Segs.

Section CloseN.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].

Lemma str_rb_proc : str16 0x1712a 15.
Proof. str16_tac. Qed.
Lemma str_pc_proc : str16 0x18bc4 7.
Proof. str16_tac. Qed.
Lemma str_cn_msg : str16 0x10355 16.
Proof. str16_tac. Qed.

(* [comment removed for export] *)
Theorem pixRemoveBorder_null_W : forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + (16 + LSF) <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x711d4 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  destruct (rbn_run al_rom regs m (W_sev_got C A m md HW) (W_sev C A m md HW) H10) as (r1 & RUN1 & Q10 & Q11 & Q12 & AG1).
  rzs HW RUN1.
  apply (returnErrorPtr_W C A m md r1 s 0x10355 0x1712a 16 15 ret (Z_to_bv 64 0) S CK HW ltac:(csr; reflexivity) Hs16 Hlo Hhi
           ltac:(csr; reflexivity) Hret Q10 Q11 Q12 str_cn_msg str_rb_proc).
  intros m' r' HW' OUT' GR' CS' V10.
  apply (HK m' r' HW').
  - eapply cs_kept_trans; [| exact CS']. apply cs_kept_intro; csr; reflexivity.
  - eapply (POSTM_range C A m md m'); [exact CK | exact HW | exact OUT' | lia | lia | lia].
  - exact V10.
Qed.

(* [comment removed for export] *)
Theorem pixCopy_nullpixs_W : forall C A m md regs (s pixd : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + (48 + 16 + LSF) <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 pixd ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6eb5c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixd ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  destruct (pcn_A al_rom regs m s pixd ret ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q8 & AG1).
  rzs HW RUN1.
  assert (WP1 : W C A (O23LeptCmap2.FR5 m s ret regs) md /\ POSTM C A s m (O23LeptCmap2.FR5 m s ret regs))
    by (unfold O23LeptCmap2.FR5; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (R8 : rdn SEGS (O23LeptCmap2.FR5 m s ret regs) (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret))
    by (unfold O23LeptCmap2.FR5; rdn_solve).
  assert (R16 : rdn SEGS (O23LeptCmap2.FR5 m s ret regs) (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)))
    by (unfold O23LeptCmap2.FR5; rdn_solve).
  assert (R24 : rdn SEGS (O23LeptCmap2.FR5 m s ret regs) (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)))
    by (unfold O23LeptCmap2.FR5; rdn_solve).
  assert (R32 : rdn SEGS (O23LeptCmap2.FR5 m s ret regs) (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 18)))
    by (unfold O23LeptCmap2.FR5; rdn_solve).
  assert (R40 : rdn SEGS (O23LeptCmap2.FR5 m s ret regs) (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 19)))
    by (unfold O23LeptCmap2.FR5; rdn_solve).
  set (M1 := O23LeptCmap2.FR5 m s ret regs) in *.
  destruct (pcn_N al_rom r1 M1 s pixd ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia)
              (W_sev_got C A M1 md HW1) (W_sev C A M1 md HW1) R8 R16 R24 R32 R40 Q2 Q8)
    as (r2 & RUN2 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & AG2).
  rzs HW1 RUN2.
  apply (returnErrorPtr_W C A M1 md r2 s 0x10355 0x18bc4 16 7 ret (Z_to_bv 64 pixd) S CK HW1 V2 Hs16 ltac:(unfold LSF; lia) Hhi
           V1 Hret V10 V11 V12 str_cn_msg str_pc_proc).
  intros m' r' HW' OUT' GR' CS' V10'.
  apply (HK m' r' HW').
  - eapply cs_kept_trans; [| exact CS']. apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM1 |].
    eapply (POSTM_range C A M1 md m'); [exact CK | exact HW1 | exact OUT' | unfold LSF; lia | lia | lia].
  - exact V10'.
Qed.

End CloseN.
