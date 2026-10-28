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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptPixHdrT2 V23LeptPixCreateT2 V23_code_frontB_pixbig.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCreateBig.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section PixCreateBig.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Lemma ph_Bx : forall regs m (w h d : Z),
    (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 410000000)%Z -> dval d ->
    getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x6dc64 : word) m rom) (mkst regs' (0x6ddec : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (4 * (wpl_of w d * h)) /\ getr regs' 14 = Z_to_bv 64 0x4000001 /\ getr regs' 20 = Z_to_bv 64 (wpl_of w d)
      /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [20; 13; 14]%list) regs regs'.
  Proof.
    intros regs m w h d Hw Hh Hwh DV H10 H11 H12. pose proof (dval_range d DV). pose proof (wpl_of_range w d Hw DV) as Hwpl.
    assert (Hdw : (0 <= d * w <= 32 * 1000000)%Z) by nia.
    pose proof (O23LeptPixCreateBig.big_size_lt w h d Hw Hh Hwh DV) as Hsz.
    eexists. split.
    - stepb_ft F_6dc64 D_6dc64 ltac:(condZ).
      stepb_ft F_6dc68 D_6dc68 ltac:(condZ).
      zv F_6dc6c D_6dc6c (Z_to_bv 64 (d * w)).
      sn F_6dc70 D_6dc70. sn F_6dc74 D_6dc74.
      stepb_tk F_6dc78 D_6dc78 ltac:(condZ).
      zv F_6dd28 D_6dd28 (Z_to_bv 64 (d * w + 31)).
      sn F_6dd2c D_6dd2c. fixv (Z_to_bv 64 (wpl_of w d)) ltac:(unfold wpl_of; rewrite zbv_srli by lia; f_equal; change (2 ^ 5)%Z with 32%Z; f_equal; lia).
      zv F_6dd30 D_6dd30 (Z_to_bv 64 (wpl_of w d * h)).
      stepiv F_6dd34 D_6dd34 (Z_to_bv 64 (4 * (wpl_of w d * h))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_6dd38 D_6dd38. fixv (Z_to_bv 64 0) ltac:(rewrite zbv_srli by lia; f_equal; apply Z.div_small; lia).
      stepb_tk F_6dd3c D_6dd3c ltac:(condZ).
      sn F_6dde4 D_6dde4. sn F_6dde8 D_6dde8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
Lemma ph_lerror0_W : forall C A m M md regs r (s fmt : Z) kf (ret : word) (S : TSet),
  Cok C -> W C A M md -> POSTM C A s m M ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  cells6 M s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 1 = Z_to_bv 64 0x6de78 -> getr r 10 = Z_to_bv 64 fmt -> getr r 11 = Z_to_bv 64 0x15a48 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r x = getr regs x) ->
  In fmt (SSP.ls_fmts1 LU16) -> str16 fmt kf ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  getr regs 2 = Z_to_bv 64 s ->
  realizes SEGS (mkCfg (mkst r (0x636a4 : word) M al_rom) md) S.
Proof.
  intros C A m M md regs r s fmt kf ret S CK HW PM Hs16 Hlo Hhi Hret CE R2 R1 R10 R11 RR Hin Sf HK H2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  apply (lept_stderr1_W C A M md r (s - 48) fmt 0x15a48 kf 15 (Z_to_bv 64 0x6de78) S CK HW R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) R1 ltac:(red; apply bv_eq; reflexivity)
           R10 R11 Hin Sf str_pixCreateHeader).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  replace (Z_to_bv 64 0x6de78) with (0x6de78 : word) by (apply bv_eq; reflexivity).
  assert (PM2 : POSTM C A s m m2).
  { eapply POSTM_trans; [exact PM|]. eapply (POSTM_range C A M md m2); [exact CK | exact HW | exact OUT2 | lia | lia | lia]. }
  destruct (cells6_frm C (s - 48) M m2 s _ _ _ _ _ _ CK ltac:(intros a _ _ _ _ H5; apply OUT2; unfold scratch in H5; lia) ltac:(lia) ltac:(lia) ltac:(lia) CE)
    as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  destruct (ph_R0 al_rom r2 m2 s ret _ _ _ _ _ ltac:(lia) ltac:(lia) Hret Q1 Q2 Q3 Q4 Q5 Q6 ltac:(csr; reflexivity))
    as (r3 & RUN3 & V2 & V10 & V1 & V8 & V9 & V18 & V19 & V230 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  apply (HK m2 r3 HW2).
  - apply cs_kept_of_rest; [rewrite V2, H2; reflexivity | exact V8 | exact V9 |].
    rest_solve.
  - exact PM2.
  - exact V10.
Qed.

(* [comment removed for export] *)
Lemma pixCreateHeader_big_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 410000000)%Z -> dval d -> (20000 < w \/ 20000 < h)%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6dc28 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 Hw Hh Hwh DV HBIG HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (RR0 : forall x, In x cs_rest -> getr regs x = getr regs x) by (intros; reflexivity).
  pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof (O23LeptPixCreateBig.big_size_lt w h d Hw Hh Hwh DV) as Hsz.
  destruct (ph_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) ltac:(lia) DV SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (V23LeptPixHdrT2.FR6 m s ret regs) md /\ POSTM C A s m (V23LeptPixHdrT2.FR6 m s ret regs)) by (unfold V23LeptPixHdrT2.FR6; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := V23LeptPixHdrT2.FR6 m s ret regs) in *.
  pose proof (cells6_FR6 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  destruct (ph_Bx al_rom r1 M1 w h d Hw Hh Hwh DV Q10 Q11 Q12) as (r2 & RUN2 & P13 & P14 & P8 & P10 & P11 & P12 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  assert (RR2 : forall x, In x [3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr regs x) by (unfold cs_rest in RR0; rest_solve).
  assert (P2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  destruct (Z_lt_ge_dec 67108864 (4 * (wpl_of w d * h))) as [BIG|SMALL].
  { destruct (ph_Cbad al_rom r2 M1 (4 * (wpl_of w d * h)) ltac:(lia) P13 P14 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r3 & RUN3 & V10 & V11 & V1 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
    apply (ph_lerror0_W C A m M1 md regs r3 s 0x11fa6 47 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
             ltac:(csr; reflexivity) V1 V10 V11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_64mb HK H2). }
  destruct (ph_C al_rom r2 M1 (4 * (wpl_of w d * h)) ltac:(lia) P13 P14) as (r3 & RUN3 & V13 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
  assert (RR3 : forall x, In x [3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r3 x = getr regs x) by rest_solve.
  assert (V10 : getr r3 10 = Z_to_bv 64 w) by (csr; reflexivity).
  assert (V11 : getr r3 11 = Z_to_bv 64 h) by (csr; reflexivity).
  destruct (Z_lt_ge_dec 20000 w) as [WBIG|WOK].
  { destruct (ph_Dbad al_rom r3 M1 w ltac:(lia) V10 V13 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r4 & RUN4 & X10 & X11 & X1 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
    apply (ph_lerror0_W C A m M1 md regs r4 s 0x1c850 51 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
             ltac:(csr; reflexivity) X1 X10 X11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_w20k HK H2). }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (ph_D al_rom r3 M1 w ltac:(lia) V10 V13) |].
  destruct (ph_Ebad al_rom r3 M1 h ltac:(lia) V11 V13 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r4 & RUN4 & X10 & X11 & X1 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
  apply (ph_lerror0_W C A m M1 md regs r4 s 0x18b8f 52 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
           ltac:(csr; reflexivity) X1 X10 X11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_h20k HK H2).
Qed.

(* [comment removed for export] *)
Lemma pixCreateNoInit_big_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 410000000)%Z -> dval d -> (20000 < w \/ 20000 < h)%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6dae0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 Hw Hh Hwh DV HBIG HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pn_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (V23LeptPixCreateT2.FR4 m s ret regs) md /\ POSTM C A s m (V23LeptPixCreateT2.FR4 m s ret regs)) by (unfold V23LeptPixCreateT2.FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := V23LeptPixCreateT2.FR4 m s ret regs) in *.
  pose proof (cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  apply (pixCreateHeader_big_W C A M1 md r1 (s - 32) w h d (Z_to_bv 64 0x6daf8) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Hw Hh Hwh DV HBIG).
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
Theorem pixCreate_big_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 410000000)%Z -> dval d -> (20000 < w \/ 20000 < h)%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6da3c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 Hw Hh Hwh DV HBIG HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pk_A al_rom regs m s ret ltac:(lia) ltac:(lia) SOK H2 H1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  rewrite H10 in Q10. rewrite H11 in Q11. rewrite H12 in Q12.
  apply (pixCreateNoInit_big_W C A M1 md r1 (s - 16) w h d (Z_to_bv 64 0x6da4c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Hw Hh Hwh DV HBIG).
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

(* [comment removed for export] *)
Corollary pixCreate_big_Wv : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 410000000)%Z -> dval d -> (20000 < w \/ 20000 < h)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 0 -> (forall q, live A' q = live A q) -> A' = A -> vm' = m_vmmaps md ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6da3c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 Hw Hh Hwh DV HBIG HK.
  apply (pixCreate_big_W C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 Hw Hh Hwh DV HBIG).
  intros m' regs' HW' CS' PM' A10.
  rewrite <- (with_vmmaps_same md).
  apply (HK A m' (m_vmmaps md) regs'); [rewrite with_vmmaps_same; exact HW' | exact CS' | exact PM' | exact A10 | intros q; reflexivity | reflexivity | reflexivity].
Qed.
End PixCreateBig.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
