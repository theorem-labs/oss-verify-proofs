(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptPixHdrT2 V23LeptPixCreateT2 V23_code_frontB_pixw0.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma str_msg_w0 : str16 0x103ad 17.
Proof. str16_tac. Qed.          (* [comment removed for export] *)

Section PixCreateW0.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Lemma ph_W0 : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x6dc64 : word) m rom) (mkst regs' (0x6ddc0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x103ad /\ getr regs' 11 = Z_to_bv 64 0x15a48
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_6dc64 D_6dc64 ltac:(condZ).
      sn F_6dcd8 D_6dcd8.
      stepLD F_6dcdc D_6dcdc (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_6dce0 D_6dce0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_6dce4 D_6dce4.
      stepb_ft F_6dce8 D_6dce8 ltac:(condZ).
      sn F_6dcec D_6dcec. sn F_6dcf0 D_6dcf0. sn F_6dcf4 D_6dcf4. sn F_6dcf8 D_6dcf8.
      sn F_6dcfc D_6dcfc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
Lemma pixCreateHeader_w0_W : forall C A m md regs (s h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d -> dval d ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6dc28 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 DV HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (dval_range d DV) as Hd32.
  assert (RR0 : forall x, In x cs_rest -> getr regs x = getr regs x) by (intros; reflexivity).
  destruct (ph_A al_rom regs m s 0 h d ret ltac:(lia) ltac:(lia) ltac:(lia) DV SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (V23LeptPixHdrT2.FR6 m s ret regs) md /\ POSTM C A s m (V23LeptPixHdrT2.FR6 m s ret regs)) by (unfold V23LeptPixHdrT2.FR6; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := V23LeptPixHdrT2.FR6 m s ret regs) in *.
  pose proof (cells6_FR6 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  destruct (ph_W0 al_rom r1 M1 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1) Q10) as (r2 & RUN2 & P10 & P11 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  assert (RR2 : forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr regs x) by (unfold cs_rest in RR0; rest_solve).
  destruct CE1 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
  destruct (ph_H al_rom r2 M1 s 0x103ad ret _ _ _ _ _ ltac:(lia) ltac:(lia) Z1 Z2 Z3 Z4 Z5 Z6 ltac:(csr; reflexivity) P10 P11)
    as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & V20 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
  apply (returnErrorPtr_W C A M1 md r3 s 0x103ad 0x15a48 17 15 ret (Z_to_bv 64 0) S CK HW1 V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
           V10 V11 V12 str_msg_w0 str_pixCreateHeader).
  intros m2 r4 HW2 OUT2 GR2 CS2 A10. unfold LSF in OUT2.
  apply (HK m2 r4 HW2).
  - apply cs_kept_of_rest; [csr; reflexivity | csr; reflexivity | csr; reflexivity |]. rest_solve.
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 md m2); [exact CK | exact HW1 | exact OUT2 | lia | lia | lia].
  - exact A10.
Qed.

(* [comment removed for export] *)
Lemma pixCreateNoInit_w0_W : forall C A m md regs (s h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d -> dval d ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6dae0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 DV HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pn_A al_rom regs m s 0 h d ret ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (V23LeptPixCreateT2.FR4 m s ret regs) md /\ POSTM C A s m (V23LeptPixCreateT2.FR4 m s ret regs)) by (unfold V23LeptPixCreateT2.FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := V23LeptPixCreateT2.FR4 m s ret regs) in *.
  pose proof (cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  apply (pixCreateHeader_w0_W C A M1 md r1 (s - 32) h d (Z_to_bv 64 0x6daf8) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 DV).
  intros m1 r2 HWa CSa PMa Hres0.
  replace (Z_to_bv 64 0x6daf8) with (0x6daf8 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (cells4_frm C (s - 32) M1 m1 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  destruct CE2 as (Z1 & Z2 & Z3).
  destruct (pn_F1 al_rom r2 m1 s ret _ _ ltac:(lia) ltac:(lia) (W_sev_got C A m1 _ HWa) (W_sev C A m1 _ HWa) Z1 Z2 Z3 E2 Hres0)
    as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  apply (returnErrorPtr_W C A m1 md r3 s 0x126da 0x13c81 13 15 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
           V10 V11 V12 str_msg_pixd str_pixCreateNoInit).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; try reflexivity.
  - eapply POSTM_trans; [exact PMa'|]. eapply (POSTM_range C A m1 md m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.

(* [comment removed for export] *)
Theorem pixCreate_w0_W : forall C A m md regs (s h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d -> dval d ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6da3c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 DV HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pk_A al_rom regs m s ret ltac:(lia) ltac:(lia) SOK H2 H1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  rewrite H10 in Q10. rewrite H11 in Q11. rewrite H12 in Q12.
  apply (pixCreateNoInit_w0_W C A M1 md r1 (s - 16) h d (Z_to_bv 64 0x6da4c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 DV).
  intros m1 r2 HWa CSa PMa Hres0.
  replace (Z_to_bv 64 0x6da4c) with (0x6da4c : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (R8 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R16 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct (pk_F al_rom r2 m1 s ret (getr regs 8) ltac:(lia) ltac:(lia) (W_sev_got C A m1 _ HWa) (W_sev C A m1 _ HWa) R8 R16 E2 Hres0)
    as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  apply (returnErrorPtr_W C A m1 md r3 s 0x126da 0x1521c 13 9 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
           V10 V11 V12 str_msg_pixd str_pixCreate).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; try reflexivity.
  - eapply POSTM_trans; [exact PMa'|]. eapply (POSTM_range C A m1 md m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.
End PixCreateW0.
