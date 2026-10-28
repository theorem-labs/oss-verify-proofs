(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith LeptRecs LeptSel LeptSlots.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23LeptErr V23LeptDilSegs V23LeptDilW V23LeptEroSegs V23LeptEroW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptPma1G.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPma1 O23LeptPma1G.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition frD (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
  [(s - 8, ret); (s - 16, getr r0 8); (s - 24, getr r0 9); (s - 32, getr r0 18); (s - 40, getr r0 19); (s - 48, getr r0 20);
   (s - 56, getr r0 21); (s - 64, getr r0 22); (s - 72, getr r0 23); (s - 80, getr r0 24); (s - 88, getr r0 25);
   (s - 96, getr r0 26)]%Z.

Section MorphN.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
Ltac pc_as RUN :=
  lazymatch type of RUN with msteps _ (mkst _ ?pc _ _) _ =>
  lazymatch goal with |- realizes _ (mkCfg (mkst _ ?gpc _ _) _) _ => replace gpc with pc by (apply bv_eq; reflexivity) end end.

Lemma frD_FRD : forall m s ret regs, (96 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FRD m s ret regs) (frD s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold frD, FRD. cbn [cellsZ]. repeat split; rdn_solve. Qed.

Lemma frD_FRE : forall m s ret regs, (96 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FRE m s ret regs) (frD s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold frD, FRE. cbn [cellsZ]. repeat split; rdn_solve. Qed.

Lemma frD_out : forall m m' (lo hi s : Z) ret r0, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) ->
  (0 <= hi)%Z -> (hi <= s - 96)%Z -> (s < 2 ^ 64)%Z -> cellsZ m (frD s ret r0) -> cellsZ m' (frD s ret r0).
Proof.
  intros m m' lo hi s ret r0 OUT H0 H1 H2. apply (cellsZ_out m m' lo hi _ OUT).
  unfold frD. repeat constructor; cbn [fst]; lia.
Qed.

Lemma frD_frm : forall C s' m m' s ret r0, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 96)%Z ->
  (s < 2 ^ 64)%Z -> cellsZ m (frD s ret r0) -> cellsZ m' (frD s ret r0).
Proof.
  intros C s' m m' s ret r0 CK F H1 H2 H3. apply (cellsZ_frm C s' m m' _ CK F H1).
  unfold frD. repeat constructor; cbn [fst]; lia.
Qed.

Lemma str_ero_proc : str16 0x1deb2 8.
Proof. str16_tac. Qed.     (* [comment removed for export] *)

(* [comment removed for export] *)
Theorem pixDilate_null_W : forall C A m md regs (s sel : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + DIL_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 sel ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa1968 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s sel ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold DIL_STACK in Hlo.
  destruct (dl_A al_rom regs m s 0 0 sel ret ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 144) 144 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q9 & Q18 & Q13 & Q10 & Q11 & Q12 & AG1).
  rzs HW RUN1.
  assert (WP1 : W C A (FRD m s ret regs) md /\ POSTM C A s m (FRD m s ret regs)) by (unfold FRD; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (frD_FRD m s ret regs ltac:(lia) ltac:(lia)) as CE1.
  set (M1 := FRD m s ret regs) in *.
  apply (pma1_nullpixs_W C A M1 md r1 (s - 144) 0 (s - 128) _ S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold O23LeptPma1G.PMA1N_STACK, O23LeptBase.LSF; lia) ltac:(lia)
           Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q13 ltac:(lia) ltac:(lia)
           ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) ltac:(lia)).
  intros m2 r2 HW2 CS2 PM2 V10.
  destruct (dl_N al_rom r2 m2 s ltac:(lia) ltac:(lia) (W_sev_got C A m2 md HW2) (W_sev C A m2 md HW2) ltac:(csr; reflexivity) V10)
    as (r3 & RUN3 & V2 & V1 & W10 & W11 & W12 & AG3).
  pc_as RUN3. rzs HW2 RUN3.
  apply (returnErrorPtr_W C A m2 md r3 (s - 144) _ _ 24 9 _ (Z_to_bv 64 0) S CK HW2 V2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
           V1 ltac:(red; apply bv_eq; reflexivity) W10 W11 W12 str_dil_msg str_dil_proc).
  intros m4 r4 HW4 OUT4 GR4 CS4 A10.
  assert (CE4 : cellsZ m4 (frD s ret regs)).
  { apply (frD_out m2 m4 (s - 144 - (16 + LSF)) (s - 144) s ret regs OUT4); [unfold LSF; lia | lia | lia |].
    apply (frD_frm C (s - 144) (O23LeptPma1.null_mem M1 (s - 128)) m2 s ret regs CK (proj1 PM2)); [lia | lia | lia |].
    apply (frD_out M1 _ (s - 128) (s - 128 + 8) s ret regs); [| lia | lia | lia | exact CE1].
    intros x Hx. unfold O23LeptPma1.null_mem.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  cbn [cellsZ frD] in CE4. destruct CE4 as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & _).
  destruct (dl_Nz al_rom r4 m4 s 0 ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
              (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) ltac:(lia) ltac:(lia) ltac:(lia) Hret
              R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 ltac:(csr; reflexivity) A10)
    as (r5 & RUN5 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & AG5).
  pc_as RUN5. rzs HW4 RUN5.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM1 |].
    eapply POSTM_trans;
      [exact (POSTM_wbytes_win C A M1 md (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0)) s CK HW1
                ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia) Hhi) |].
    eapply POSTM_trans; [exact (POSTM_mono C A (s - 144) s _ _ ltac:(lia) PM2) |].
    exact (POSTM_range C A m2 md m4 _ _ s CK HW2 OUT4 ltac:(unfold LSF; lia) ltac:(lia) Hhi).
  - exact Z10.
Qed.

(* [comment removed for export] *)
Theorem pixErode_null_W : forall C A m md regs (s sel : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ERO_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 sel ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa1d7c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s sel ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold ERO_STACK in Hlo.
  destruct (er_A al_rom regs m s 0 0 sel ret ltac:(lia) ltac:(lia)
              (W_sok_win C A m md (s - 160) 160 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q9 & Q18 & Q13 & Q10 & Q11 & Q12 & AG1).
  rzs HW RUN1.
  assert (WP1 : W C A (FRE m s ret regs) md /\ POSTM C A s m (FRE m s ret regs)) by (unfold FRE; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (frD_FRE m s ret regs ltac:(lia) ltac:(lia)) as CE1.
  set (M1 := FRE m s ret regs) in *.
  apply (pma1_nullpixs_W C A M1 md r1 (s - 160) 0 (s - 144) _ S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold O23LeptPma1G.PMA1N_STACK, O23LeptBase.LSF; lia) ltac:(lia)
           Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q13 ltac:(lia) ltac:(lia)
           ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) ltac:(lia)).
  intros m2 r2 HW2 CS2 PM2 V10.
  destruct (er_N al_rom r2 m2 s ltac:(lia) ltac:(lia) (W_sev_got C A m2 md HW2) (W_sev C A m2 md HW2) ltac:(csr; reflexivity) V10)
    as (r3 & RUN3 & V2 & V1 & W10 & W11 & W12 & AG3).
  pc_as RUN3. rzs HW2 RUN3.
  apply (returnErrorPtr_W C A m2 md r3 (s - 160) _ _ 24 8 _ (Z_to_bv 64 0) S CK HW2 V2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
           V1 ltac:(red; apply bv_eq; reflexivity) W10 W11 W12 str_dil_msg str_ero_proc).
  intros m4 r4 HW4 OUT4 GR4 CS4 A10.
  assert (CE4 : cellsZ m4 (frD s ret regs)).
  { apply (frD_out m2 m4 (s - 160 - (16 + LSF)) (s - 160) s ret regs OUT4); [unfold LSF; lia | lia | lia |].
    apply (frD_frm C (s - 160) (O23LeptPma1.null_mem M1 (s - 144)) m2 s ret regs CK (proj1 PM2)); [lia | lia | lia |].
    apply (frD_out M1 _ (s - 144) (s - 144 + 8) s ret regs); [| lia | lia | lia | exact CE1].
    intros x Hx. unfold O23LeptPma1.null_mem.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  cbn [cellsZ frD] in CE4. destruct CE4 as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & _).
  destruct (er_Nz al_rom r4 m4 s 0 ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
              (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) ltac:(lia) ltac:(lia) ltac:(lia) Hret
              R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 ltac:(csr; reflexivity) A10)
    as (r5 & RUN5 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & AG5).
  pc_as RUN5. rzs HW4 RUN5.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM1 |].
    eapply POSTM_trans;
      [exact (POSTM_wbytes_win C A M1 md (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 0)) s CK HW1
                ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia) Hhi) |].
    eapply POSTM_trans; [exact (POSTM_mono C A (s - 160) s _ _ ltac:(lia) PM2) |].
    exact (POSTM_range C A m2 md m4 _ _ s CK HW2 OUT4 ltac:(unfold LSF; lia) ltac:(lia) Hhi).
  - exact Z10.
Qed.

End MorphN.
