(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5BDetailK L5BDetailG L5BCstrP Bo0_code_8e368_8f368
     AsanPlanCore AsanPlanSound Bo0PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5ArithSpecsB0 L5ParseSpecsBB0 L5BStkSh.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ACST.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5PSA. Import L5ASB. Import L5PSB. Import L5ACSP. Import L5ADK. Import L5ADH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Lemma CSCR_EQ : CSTR_SCRB = 4912. Proof. reflexivity. Qed.
Lemma TSCR_EQ : TOBIG_SCRB = 4880. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land252_div4 fb : 0 <= fb < 256 -> Z.land fb 252 = 4 * (fb / 4).
Proof.
  intros Hfb. pose proof (byte_cases (fun fb => Z.land fb 252 =? 4 * (fb / 4)) ltac:(vm_compute; reflexivity) fb Hfb) as X. cbn beta in X.
  apply Z.eqb_eq. exact X.
Qed.
Lemma land252_facts fb : 0 <= fb < 256 -> 0 <= Z.land fb 252 < 256 /\ Z.land (Z.land fb 252) 3 = 0 /\ Z.testbit (Z.land fb 252) 0 = false.
Proof.
  intros Hfb. split. rewrite land252_div4 by exact Hfb. pose proof (Z.div_pos fb 4 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound fb 4 64 ltac:(lia) ltac:(lia)). lia.
  split. rewrite <- Z.land_assoc. change (Z.land 252 3) with 0. apply Z.land_0_r.
  rewrite Z.land_spec. change (Z.testbit 252 0) with false. apply Bool.andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma rdn_img M lo hi : L5.img_clear M lo hi -> forall (k : nat) a, lo <= a -> a + Z.of_nat k <= hi -> 0 <= a -> hi <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) k = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) k.
Proof.
  intros IC. induction k as [|k IH]; intros a H1 H2 H3 H4. reflexivity.
  cbn [rdn]. rewrite (IC a) by lia.
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_unsigned 1) with (1 mod 2 ^ 64).
      rewrite <- Z.add_mod by lia. reflexivity. }
  rewrite (IH (a + 1)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition alit_buf : list byte := map (Z_to_bv 8) (alit_digits ++ [0; 0]).
Lemma alit_rdn M : L5.img_clear M 0x10000 0x3c000 -> rdn RSEGS M (Z_to_bv 64 ALIT) 40 = Some alit_buf.
Proof. intros IC. rewrite (rdn_img M 0x10000 0x3c000 IC 40 ALIT) by (unfold ALIT; lia). vm_compute. reflexivity. Qed.
Lemma alit_bytes M : L5.img_clear M 0x10000 0x3c000 -> L5.bytes_at RSEGS M ALIT alit_digits.
Proof.
  intros IC i Hi. unfold L5.u8_at. rewrite (rdn_img M 0x10000 0x3c000 IC 1 (ALIT + Z.of_nat i)) by (unfold ALIT; cbn in Hi; lia).
  cbn in Hi. unfold ALIT. do 38 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma alit_facts : Z.of_nat (length alit_digits) = 38 /\ split_sign alit_digits = (false, alit_digits) /\ Forall (fun c => 0 <= c < 256) alit_digits /\ digits_ok alit_digits
                   /\ nwords (dec alit_digits) = 2%nat /\ wlist (dec alit_digits) 2 = [A0; A1].
Proof.
  split. reflexivity. split. reflexivity.
  split. { unfold alit_digits. repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
  split. { unfold digits_ok, alit_digits. repeat (apply Forall_cons; [lia|]). apply Forall_nil. }
  split. vm_compute. reflexivity. vm_compute. reflexivity.
Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Let LY2 : as0_layout2 L := as0_layout2_of L C LY.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Local Abbreviation statics_vis := (L5ADH.statics_vis L ar C HI LY HIok).
Local Abbreviation apure := (L5ADH.apure L ar C HI LY HIok).

Theorem cstr_ok : tobig4_specB L ar IL HI -> cstr_specB L ar IL HI.
Proof.
  intros TB4 fx R M model K LB FF LK cr A o sp r fbo HH AM HK G10 G11 CR G1 RA G2 A32 G4 STK SSH FFR FFR2 FFRS IMG0 UFB FBO AOB SZ KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). rewrite CSCR_EQ in SLO, DSCR.
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487200 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof alit_facts as (AL & ASP & AR & ADG & ANW & AWL).
  pose proof (land252_facts fbo FBO) as (FB1 & FB3 & FBT).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp CSTR_SCRB HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (W32 : L5.writable RSEGS MV (sp - 32) 32).
  { apply (proj2 (writable_vis H M (sp - 32) 32 (VIS (sp - 32) 32 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. rewrite CSCR_EQ; clear; lia. clear; lia. clear; lia. }
  assert (ALS : aligned sp 16) by exact A16.
  assert (ALO : aligned o 8) by (unfold aligned; clear - OR; lia).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  assert (OR0 : 0 <= o < 2 ^ 64 /\ 4096 <= o <= 140737488355296) by (clear - OR; lia). destruct OR0 as [OR0 OR1].
  assert (OZv : L5KA.zeros_at MV (o / 8 + 2147450880) 4). { apply (proj2 (zeros_at_vis H M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OWv : L5.writable RSEGS MV o 32). { apply (proj2 (writable_vis H M o 32 OVIS ltac:(clear - OR; lia) ltac:(clear - OR; lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. clear - OR; lia. clear - OR; lia. }
  assert (OFRM : sp - 32 + 32 <= o \/ o + 32 <= sp - 32) by (clear - OR SLO; lia).
  assert (UFBv : L5.u8_at RSEGS MV o fbo). { apply (proj2 (u8_at_vis H M o fbo ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact UFB. }
  assert (FBO' : 0 <= fbo <= 255 /\ 0 <= fbo < 2 ^ 64) by (clear - FBO; lia). destruct FBO' as [FBO' FBO''].
  assert (ALR : 0 <= ALIT < 2 ^ 64) by (unfold ALIT; clear; lia).
  (* [comment removed for export] *)
  pose proof (csA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => ALIT | 35%nat => U R 12 | 36%nat => fbo | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r2; exact G2) | (rewrite <- r10; exact G10) | (rewrite <- r11; exact G11)]).
  destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR18 & aU8 & aC32 & aC24 & aC16 & aC8)).
  set (W1 := fun a => sp - 32 <= a < sp \/ o <= a < o + 1).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R CSTR R1 0x5e7f0 M1v W1 K HH AM aMS MG1).
  { intros a Ha Hna. apply aFZ. exact Ha. all: clear - Hna; subst W1; cbn beta in Hna; lia. }
  { intros a Ha Wa. subst W1; cbn beta in Wa. destruct Wa as [Wa|Wa].
    - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
    - split. apply (obj_client L ar LB FF 0 0 o 32 a AOB). clear - Wa; lia. clear - Wa OR; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (ASTK1 : astk ar M1 sp CSTR_SCRB) by (eapply astk_grows; [exact STK | exact MGM1]).
  assert (NCS : forall a, sp - 32 <= a < sp -> ~ aclient L ar LB FF sp CSTR_SCRB a).
  { intros a X Hc. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp CSTR_SCRB a HH SPT Hc) as [Y|Y]. rewrite CSCR_EQ in Y. clear - X Y; lia. clear - X Y SLO; lia. }
  assert (EK1 : ek L ar LB FF sp CSTR_SCRB [(o, 32)] M M1).
  { apply (ek_piece L ar LB FF sp CSTR_SCRB [(o, 32)] M M1 W1 FRM1). intros a Ha Hc Ho X. subst W1; cbn beta in X. destruct X as [X|X]. exact (NCS a X Hc).
    apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia. }
  assert (DK1 : dk L ar LB FF sp CSTR_SCRB M M1) by (apply dk_grows; exact MGM1).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHO : forall j, 0 <= j < 4 -> 2147450880 <= o / 8 + 2147450880 + j < 17594333528064 /\ ~ (o <= o / 8 + 2147450880 + j < o + 32)) by (intros j Hj; clear - Hj OR OBIG; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SZ1 : shadow_zero M1 o 4).
  { intros j Hj. unfold byte_at. rewrite FRM1. apply SZ. exact Hj. unfold S, SB. destruct (SHO j Hj) as [X _]. clear - X; lia.
    subst W1; cbn beta. unfold S, SB. destruct (SHO j Hj) as [X X']. clear - X X' SPR. lia. }
  assert (IMG1 : L5.img_clear M1 0x10000 0x3c000).
  { intros i Hi. rewrite FRM1. apply IMG0. exact Hi. clear - Hi; lia. subst W1; cbn beta. clear - Hi OR SLO. lia. }
  assert (UFB1 : L5.u8_at RSEGS M1 o (Z.land fbo 252)).
  { apply (proj1 (u8_at_vis (ahid A model) M1 o _ ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))).
    rewrite VIS1. rewrite land252_div4 by exact FBO. exact aU8. }
  (* [comment removed for export] *)
  pose proof (aio_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (aly_segs L C LY), (aly_memset L C LY), (aly_scr_mem L C LY) in MS.
  assert (U21 : bv_unsigned (getr R1 2%bv) = sp - 32). { rewrite r2, aR2. apply L5.unsigned_lit. clear - SPR; lia. }
  assert (SA32 : (sp - 32) mod 16 = 0 /\ (sp - 32) mod 32 = 0).
  { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  eapply (MS fx1 R1 M1 model1 LB FF LK cr A (o + 8) 0 24 K); clear MS.
  { split. exact HH1. split. exact (proj1 AM1). split. exact (proj2 AM1).
    split. rewrite r10. exact aR10. split. rewrite r12. exact aR12. split. clear; lia.
    split. rewrite r4, (aKS 4%nat) by inl. rewrite <- r4. exact G4.
    split. rewrite r1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
    split. { rewrite U21. apply (astack_ok_of_astk L ar C LY M M1 sp CSTR_SCRB 32 2560 STK MGM1). clear; lia. clear; lia. rewrite CSCR_EQ; clear; lia. exact (proj1 SA32). }
    split. { eapply aacc_of_zero. exact SZ1. clear - OR; lia. clear - OR; lia. clear; lia. clear; lia. }
    split. { intros i Hi. rewrite U21. apply (obj_client L ar LB FF _ _ o 32 (o + 8 + i) AOB). clear - Hi; lia. }
    split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M1 (o + 8) 24). 2: clear - OR; lia. 2: clear - OR; lia. 2: exact Hi. 2: exact Hm.
             eapply L5.defined_grows. exact MGM1. intros j Hj. replace (o + 8 + j) with (o + (8 + j)) by (clear; lia). apply ODEF. clear - Hj; lia. }
    split. exact HK. apply (app_rng_aobj L ar C HI HIok LB FF LK cr A M1 _ o 32 (o + 8) 24 HH1 AOB); clear; lia. }
  { rewrite r11. exact aR11. }
  intros R6 M6 model6 mR10 RP6 ZB PRES6 SDEF6 RT6 MI6 HH6. rewrite U21 in PRES6, SDEF6. rewrite r1, aR1.
  assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 AM1). }
  assert (ASTK6 : astk ar M6 sp CSTR_SCRB).
  { apply (astk_after_eq L ar C HI HIok LB FF LK cr A M1 M1 M6 _ sp _ (sp - 32) 2560 HH1 ASTK1 (mem_grows_refl M1)).
    intros a Ha Hs Hns. apply PRES6. exact Ha. apply stack_client. exact Hs. exact Hns. clear - Hs OR; lia. exact SDEF6.
    rewrite CSCR_EQ; clear; lia. clear; lia. rewrite CSCR_EQ; clear; lia. }
  assert (EK6 : ek L ar LB FF sp CSTR_SCRB [(o, 32)] M M6).
  { eapply ek_trans. exact EK1. apply (ek_mem L ar LB FF sp CSTR_SCRB (sp - 32) 2560 (fun a => o + 8 <= a < o + 8 + 24) [(o, 32)] M1 M6 PRES6).
    - rewrite CSCR_EQ; clear; lia.
    - clear; lia.
    - intros a _ Ho X. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia. }
  assert (DK6 : dk L ar LB FF sp CSTR_SCRB M M6).
  { eapply dk_trans. exact DK1. apply (dk_mem L ar LB FF sp CSTR_SCRB (sp - 32) 2560 (fun a => o + 8 <= a < o + 8 + 24) M1 M6 PRES6 SDEF6).
    - intros a Da. destruct (ZB (a - (o + 8)) ltac:(clear - Da; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (o + 8 + (a - (o + 8))) with a in Bv by (clear; lia). rewrite Bv. discriminate.
    - intros a. destruct (rng_dec a (o + 8) (o + 8 + 24)); [left|right]; assumption.
    - rewrite CSCR_EQ; clear; lia.
    - clear; lia. }
  assert (OCL6 : forall a, o <= a < o + 32 -> aclient L ar LB FF (sp - 32) 2560 a) by (intros a Ha; apply (obj_client L ar LB FF _ _ o 32 a AOB Ha)).
  assert (UFB6 : L5.u8_at RSEGS M6 o (Z.land fbo 252)).
  { eapply L5C.u8_at_agree. 4: exact UFB1. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply PRES6. clear - Hi OR; lia. apply OCL6. clear - Hi; lia. clear - Hi; lia. }
  assert (Z6 : L5KA.zeros_at M6 (o + 8) 24). { intros i Hi. destruct (ZB i Hi) as (v & Ev & Bv). subst v. exact Bv. }
  assert (BIG6 : L5.big_at RSEGS M6 o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0))).
  { unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st Z.of_nat]. split. exact UFB6. split. exact FB1.
    split. { apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z6. clear; lia. clear; lia. clear - OR; lia. clear - OR; lia. }
    split. exact FBT.
    split. { apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z6. clear; lia. clear; lia. clear - OR; lia. clear - OR; lia. }
    split. { apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z6. clear; lia. clear; lia. clear - OR; lia. clear - OR; lia. }
    clear; lia. }
  assert (SZ6 : shadow_zero M6 o 4).
  { intros j Hj. unfold byte_at. rewrite PRES6. apply SZ1. exact Hj. unfold S, SB. destruct (SHO j Hj) as [X _]. clear - X; lia.
    replace (S o + j) with (o / 8 + SB + j) by reflexivity. apply (aclient_narrow L ar LB FF sp CSTR_SCRB). apply OCLSH. exact Hj.
    unfold SB. destruct (SHO j Hj) as [X _]. clear - X SPR. lia.
    unfold S, SB. destruct (SHO j Hj) as [X X']. clear - X X'. lia. }
  assert (IMG6 : L5.img_clear M6 0x10000 0x3c000).
  { intros i Hi. rewrite PRES6. apply IMG1. exact Hi. clear - Hi; lia. apply (img_client L ar C LY LY2). clear - Hi; lia. clear - Hi OR. lia. }
  (* [comment removed for export] *)
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M6 model6 HH6) as (_ & VIS6 & _).
  pose proof (statics_vis LB FF LK cr A M6 model6 HH6) as (IMGC6 & CSB6 & CUAR6).
  set (H6 := ahid A model6) in *. set (MV6 := mrestrict H6 M6) in *.
  assert (W32f : L5.writable RSEGS MV6 (sp - 32) 32).
  { apply (proj2 (writable_vis H6 M6 (sp - 32) 32 (VIS6 (sp - 32) 32 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M6 sp). exact ASTK6. rewrite CSCR_EQ; clear; lia. clear; lia. clear; lia. }
  pose proof (csB_conc fx1 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => ALIT | 35%nat => U R 12 | 48%nat => U R6 1 | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc ]).
  destruct P as (fx7 & R7 & M7v & _ & bFR & _ & (bMS & bKS & bR1 & bR10)).
  assert (E7 : M7v = MV6) by (apply mem_eq_of_agree; intros a Ha; apply bFR). subst M7v.
  apply (apure LB FF LK cr A M6 model6 fx1 fx7 R6 583936 R7 0x4de30 K HH6 (conj Hh6 MI6) bMS).
  intros model7 HH7 AM7 RT7 AH7.
  (* [comment removed for export] *)
  pose proof (aic_strlen _ _ _ _ _ ICok) as SL. unfold astrlen_spec in SL. cbv zeta in SL.
  rewrite (aly_segs L C LY), (aicl_strlen IL ILY), (aicl_scr_strlen IL ILY), (aicl_ro_lo IL ILY), (aicl_ro_hi IL ILY) in SL.
  assert (U27 : bv_unsigned (getr R7 2%bv) = sp - 32). { rewrite r2. replace (getr R7 (reg 2)) with (Z_to_bv 64 (sp - 32)) by (symmetry; rk). apply L5.unsigned_lit. clear - SPR; lia. }
  assert (ASRC : forall Mx, asrc IL LB FF Mx ALIT 39).
  { intros Mx. right; right; left. exists 0x22960, 39. split. rewrite (aicl_globals IL ILY). left; reflexivity. unfold ALIT. clear; lia. }
  eapply (SL fx7 R7 M6 model7 LB FF LK cr A ALIT 38 alit_buf K HH7 (proj1 AM7) (proj2 AM7)); clear SL.
  - rewrite r10. exact bR10.
  - rewrite r4. rk.
  - rewrite r1, bR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U27. apply (astack_ok_of_astk L ar C LY M6 M6 sp CSTR_SCRB 32 2304 ASTK6 (mem_grows_refl M6)). clear; lia. clear; lia. rewrite CSCR_EQ; clear; lia. exact (proj1 SA32).
  - unfold ALIT; clear; lia.
  - change (Z.of_nat (length alit_buf)) with 40. unfold ALIT; clear; lia.
  - clear; lia.
  - change (length alit_buf) with 40%nat. apply alit_rdn. exact IMG6.
  - change (Z.of_nat (length alit_buf)) with 40. unfold ALIT. reflexivity.
  - reflexivity.
  - intros j Hj. change (Z.to_nat 38) with 38%nat in Hj. do 38 (destruct j as [|j]; [intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E|]). exfalso. clear - Hj. lia.
  - intros i Hi. left. rewrite (aly_img_lo L C LY), (aly_img_hi L C LY). change (Z.of_nat (length alit_buf)) with 40 in Hi. unfold ALIT. clear - Hi. lia.
  - intros a Ha. apply IMG6. clear - Ha; lia.
  - change (38 + 1) with 39. apply (asrc_aacc L ar C IL HI ILY HIok ICok LB FF LK cr A M6 _ ALIT 39 HH7 (ASRC M6)).
  - apply app_rng_img. exact (proj1 SPT). unfold ALIT; clear; lia. unfold ALIT; clear; lia.
  - exact HK.
  - intros R8 M8 model8 sR10 RP8 PRES8 SDEF8 GROW8 RT8 MI8 HH8. rewrite U27 in PRES8, SDEF8. rewrite r1, bR1.
    assert (Hh8 : m_halted model8 = None). { rewrite (L5LZ.model_rt_halted _ _ RT8). exact (proj1 AM7). }
    assert (ASTK8 : astk ar M8 sp CSTR_SCRB).
    { apply (astk_after_eq L ar C HI HIok LB FF LK cr A M6 M6 M8 _ sp _ (sp - 32) 2304 HH6 ASTK6 (mem_grows_refl M6)).
      intros a Ha Hs Hns. apply PRES8. exact Ha. apply stack_client. exact Hs. exact Hns. exact SDEF8.
      rewrite CSCR_EQ; clear; lia. clear; lia. rewrite CSCR_EQ; clear; lia. }
    assert (PRES8' : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 32) 2304 a -> ~ False -> M8 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)) by (intros a Ha Hc _; apply PRES8; assumption).
    assert (EK8 : ek L ar LB FF sp CSTR_SCRB [(o, 32)] M M8).
    { eapply ek_trans. exact EK6. apply (ek_mem L ar LB FF sp CSTR_SCRB (sp - 32) 2304 (fun _ => False) [(o, 32)] M6 M8 PRES8').
      - rewrite CSCR_EQ; clear; lia.
      - clear; lia.
      - intros a _ _ X. exact X. }
    assert (DK8 : dk L ar LB FF sp CSTR_SCRB M M8).
    { eapply dk_trans. exact DK6. intros a Ha _ X. apply GROW8. exact X. }
    assert (OCL8 : forall a, o <= a < o + 32 -> aclient L ar LB FF (sp - 32) 2304 a) by (intros a Ha; apply (obj_client L ar LB FF _ _ o 32 a AOB Ha)).
    assert (BIG8 : L5.big_at RSEGS M8 o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0))).
    { eapply L5C.big_at_agree. 4: exact BIG6. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply PRES8. clear - Hi OR; lia. apply OCL8. exact Hi. }
    assert (SZ8 : shadow_zero M8 o 4).
    { intros j Hj. unfold byte_at. rewrite PRES8. apply SZ6. exact Hj. unfold S, SB. destruct (SHO j Hj) as [X _]. clear - X; lia.
      replace (S o + j) with (o / 8 + SB + j) by reflexivity. apply (aclient_narrow L ar LB FF sp CSTR_SCRB). apply OCLSH. exact Hj.
      unfold SB. destruct (SHO j Hj) as [X _]. clear - X SPR. lia. }
    assert (IMG8 : L5.img_clear M8 0x10000 0x3c000).
    { intros i Hi. rewrite PRES8. apply IMG6. exact Hi. clear - Hi; lia. apply (img_client L ar C LY LY2). clear - Hi; lia. }
    (* [comment removed for export] *)
    pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M8 model8 HH8) as (_ & VIS8 & _).
    pose proof (statics_vis LB FF LK cr A M8 model8 HH8) as (IMGC8 & CSB8 & CUAR8).
    set (H8 := ahid A model8) in *. set (MV8 := mrestrict H8 M8) in *.
    assert (W32h : L5.writable RSEGS MV8 (sp - 32) 32).
    { apply (proj2 (writable_vis H8 M8 (sp - 32) 32 (VIS8 (sp - 32) 32 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M8 sp). exact ASTK8. rewrite CSCR_EQ; clear; lia. clear; lia. clear; lia. }
    assert (R38 : 0 <= 38 < 2 ^ 64) by (clear; lia).
    pose proof (csC_conc fx7 R8 MV8 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => ALIT | 35%nat => U R 12 | 48%nat => U R8 1 | 49%nat => 38 | _ => 0 end)) as P. cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r10; exact sR10)]).
    destruct P as (fx9 & R9 & M9v & _ & cFR & _ & (cMS & cKS & cR1 & cR10 & cR11 & cR12 & cR13)).
    assert (E9 : M9v = MV8) by (apply mem_eq_of_agree; intros a Ha; apply cFR). subst M9v.
    apply (apure LB FF LK cr A M8 model8 fx7 fx9 R8 583944 R9 TOBIG4 K HH8 (conj Hh8 MI8) cMS).
    intros model9 HH9 AM9 RT9 AH9.
    apply (TB4 fx9 R9 M8 model9 K LB FF LK cr A ALIT o (sp - 32) 583964 (Z.land fbo 252) false alit_digits HH9 AM9 HK).
    + rewrite r10. exact cR10.
    + rewrite r11. exact cR11.
    + intros X. discriminate X.
    + rewrite r12. exact cR12.
    + cbn [length alit_digits]. clear; lia.
    + rewrite ASP. cbn [snd]. exact CR.
    + rewrite r1. exact cR1.
    + split. clear; lia. reflexivity.
    + rewrite r2. rk.
    + exact (proj2 SA32).
    + rewrite r4. rk.
    + apply (astk_sub ar M8 M8 sp CSTR_SCRB 32 TOBIG_SCRB ASTK8 (mem_grows_refl M8)). clear; lia. rewrite TSCR_EQ; clear; lia. rewrite TSCR_EQ, CSCR_EQ; clear; lia. exact (proj1 SA32).
    + (* [comment removed for export] *)
      pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as WF0.
      assert (TOP : ar_stack_top ar <= 2 ^ 47). { clear - WF0. decompose [and] WF0. assumption. } clear WF0.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      assert (M8a : (sp - CSTR_SCRB) mod 8 = 0 /\ (sp - 32 - TOBIG_SCRB) mod 8 = 0) by (rewrite TSCR_EQ, CSCR_EQ; clear - A32; Lia.lia).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      apply (L5BSS.stksh_ek L ar LB FF sp CSTR_SCRB [(o, 32)] M M8 (sp - CSTR_SCRB) (sp - 32 - TOBIG_SCRB) SSH);
        [ rewrite TSCR_EQ, CSCR_EQ; clear; lia | exact (proj1 M8a) | exact (proj2 M8a) | rewrite CSCR_EQ; clear - SLO; lia | rewrite CSCR_EQ; clear - SLO SPR; lia
        | exact TOP | clear - SPT; lia | exact EK8 | ].
      intros a SX. apply (L5BSS.shadow_outside1 ar o 32 a); [ clear - SPT; lia | exact OBIG | exact SX ].
    + exact FFR.
    + exact FFR2.
    + apply (ffrs_le FF sp). exact FFRS. clear; lia.
    + exact BIG8.
    + exact FB3.
    + exact AOB.
    + exact SZ8.
    + apply alit_bytes. exact IMG8.
    + exact AR.
    + rewrite AL. exact (asrc_sub IL LB FF M8 ALIT 39 ALIT 38 (ASRC M8) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
    + left. rewrite AL. unfold ALIT. clear - OR. lia.
    + intros fx10 R10 M10 model10 LB10 cr10 LK10 A10 POST RT10 IA10 AM10 LKI10 HH10.
      unfold tobig_postB in POST. rewrite ASP in POST. cbn [fst snd] in POST. destruct POST as (RP10 & PC).
      destruct PC as [(PAR & R10_11 & PP)|(NP & _ & _)].
      2:{ exfalso. destruct NP as [NP|NP]. rewrite ASP in NP. cbn in NP. discriminate NP. apply NP. rewrite ASP. cbn [snd]. exact ADG. }
      unfold parse_post in PP. cbv zeta in PP. rewrite ANW, AWL in PP. destruct PP as (st' & OB10 & OL10 & ST10 & CR10 & AH10).
      destruct st' as [v0 v1|cap q]. 2:{ exfalso. destruct ST10 as (X & _). clear - X. lia. }
      destruct ST10 as (_ & ELB). subst LB10.
      destruct OL10 as (_ & _ & WL). cbn [L5.bo_st L5.bo_len firstn] in WL. injection WL as <- <-.
      replace (res_fb (Z.land fbo 252) 2 false) with (Z.land fbo 252) in OB10 by (unfold res_fb; cbn; clear; lia).
      assert (ASTK10 : astk ar M10 sp CSTR_SCRB).
      { apply (astk_after L ar C HI HIok LB FF LK cr A M8 M8 M10 _ sp _ (sp - 32) TOBIG_SCRB _ HH9 ASTK8 (mem_grows_refl M8) AH10).
        rewrite TSCR_EQ, CSCR_EQ; clear; lia. clear; lia. rewrite CSCR_EQ; clear; lia. }
      assert (EK10 : ek L ar LB FF sp CSTR_SCRB [(o, 32)] M M10).
      { eapply ek_trans. exact EK8. apply (ek_callee L ar LB [] FF [] sp CSTR_SCRB (sp - 32) TOBIG_SCRB [(o, 32)] [(o, 32)] M8 M10 AH10).
        rewrite TSCR_EQ, CSCR_EQ; clear; lia. clear; lia. intros a _ X. exact X. }
      assert (DK10 : dk L ar LB FF sp CSTR_SCRB M M10).
      { eapply dk_trans. exact DK8. apply (dk_callee L ar LB [] FF [] sp CSTR_SCRB (sp - 32) TOBIG_SCRB [(o, 32)] M8 M10 AH10). rewrite TSCR_EQ, CSCR_EQ; clear; lia. clear; lia. }
      (* [comment removed for export] *)
      assert (SAVED : forall a v, sp - 32 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M10 a v).
      { intros a v Ha1 Ha2 Hc.
        assert (C1 : L5.u64_at RSEGS M1 a v).
        { apply (proj1 (u64_at_vis (ahid A model) M1 a v (VIS a 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SPR; lia)) ltac:(clear - Ha1 SPR; lia) ltac:(clear - Ha2 SPR; lia))). rewrite VIS1. exact Hc. }
        eapply L5C.u64_at_agree. 4: exact C1. 2: clear - Ha1 SPR; lia. 2: clear - Ha2 SPR; lia. intros i Hi.
        assert (SC : forall scr, aclient L ar LB FF (sp - 32) scr i) by (intros scr; apply stack_client; [clear - Hi Ha1 Ha2 SLO SHI SPT; lia | clear - Hi Ha1; lia]).
        rewrite (proj1 AH10 i). 2:{ split. clear - Hi Ha1 Ha2 SPR; lia. split. apply SC. intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Hi Ha1 Ha2 OR SLO. lia. }
        rewrite (PRES8 i ltac:(clear - Hi Ha1 Ha2 SPR; lia) (SC _)).
        apply (PRES6 i ltac:(clear - Hi Ha1 Ha2 SPR; lia) (SC _)). clear - Hi Ha1 Ha2 OR SLO. lia. }
      (* [comment removed for export] *)
      pose proof (vis_pack L ar C HI LY HIok LB FF LK10 cr10 A10 M10 model10 HH10) as (_ & VIS10 & _).
      pose proof (statics_vis LB FF LK10 cr10 A10 M10 model10 HH10) as (IMGC10 & CSB10 & CUAR10).
      set (H10 := ahid A10 model10) in *. set (MV10 := mrestrict H10 M10) in *.
      assert (SV10 : avis H10 (sp - 32) 32) by (apply (VIS10 (sp - 32) 32); [clear - SLO; lia | clear - SPR; lia]).
      assert (W32j : L5.writable RSEGS MV10 (sp - 32) 32).
      { apply (proj2 (writable_vis H10 M10 (sp - 32) 32 SV10 ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
        eapply (astk_writable ar M10 sp). exact ASTK10. rewrite CSCR_EQ; clear; lia. clear; lia. clear; lia. }
      assert (SVv : forall a v, sp - 32 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV10 a v).
      { intros a v Ha1 Ha2 Hc. apply (proj2 (u64_at_vis H10 M10 a v ltac:(eapply avis_sub; [exact SV10 | clear - Ha1; lia | clear - Ha2; lia]) ltac:(clear - Ha1 SPR; lia) ltac:(clear - Ha2 SPR; lia))).
        apply SAVED; assumption. }
      pose proof (SVv (sp - 8) (U R 1) ltac:(clear; lia) ltac:(clear; lia) aC8) as D8. pose proof (SVv (sp - 16) (U R 8) ltac:(clear; lia) ltac:(clear; lia) aC16) as D16.
      pose proof (SVv (sp - 24) (U R 9) ltac:(clear; lia) ltac:(clear; lia) aC24) as D24. pose proof (SVv (sp - 32) (U R 18) ltac:(clear; lia) ltac:(clear; lia) aC32) as D32.
      pose proof (csD_conc fx10 R10 MV10 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => ALIT | 35%nat => U R 12 | 41%nat => U R 1 | 42%nat => U R 8 | 43%nat => U R 9 | 44%nat => U R 18
                    | 48%nat => U R10 1 | 61%nat => U R10 10 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r11; exact R10_11)]).
      destruct P as (fx11 & R11 & M11v & MG11 & dFR & dFZ & (dMS & dKS & dR1 & dR2 & dR8 & dR9 & dR18)).
      pose proof (ret_to fx11 R11 M11v 0x8e938 W_8e938 r F_8e938 eq_refl D_8e938 ltac:(rewrite dR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
      apply (apiece_ro L ar C HI LY HIok LB FF LK10 cr10 A10 M10 model10 fx10 fx11 R10 583964 R11 r M11v K HH10 AM10 (msteps_trans _ _ _ _ dMS RET) MG11 dFZ).
      intros M11 model11 HH11 AM11 RT11 AH11 VIS11 MGM11 FRM11.
      assert (E11 : M11 = M10) by (apply mem_eq_of_agree; exact FRM11). subst M11.
      apply (KONT fx11 R11 M10 model11 cr10 LK10 A10).
      * split.
        { apply preserved_by_index. intros k Hk. unfold cs_all in Hk. cbn [In] in Hk.
          destruct Hk as [<-|Hk]. { rewrite dR2. rewrite <- r2, G2. reflexivity. }
          destruct Hk as [<-|Hk]. { rk. }
          destruct Hk as [<-|Hk]. { rk. }
          destruct Hk as [<-|Hk]. { rewrite dR8. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite dR9. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite dR18. symmetry. apply U_to. }
          repeat (destruct Hk as [<-|Hk]; [rk|]). destruct Hk. }
        split. exact OB10. split. exact CR10.
        apply ahpres_of. exact EK10. eapply astk_defined. exact ASTK10. clear; lia. clear; lia. exact DK10.
      * eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT6. eapply L5LZ.model_rt_trans. exact RT7. eapply L5LZ.model_rt_trans. exact RT8.
        eapply L5LZ.model_rt_trans. exact RT9. eapply L5LZ.model_rt_trans. exact RT10. exact RT11.
      * exact IA10.
      * exact AM11.
      * exact LKI10.
      * exact HH11.
Qed.
End WithIface.
End SCFG_1.
End L5ACST.
