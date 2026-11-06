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
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5CoreBB0 L5ParseSpecsAB0 L5AChk L5BChkAs0 L5ArithSpecsB0 L5ParseSpecsBB0 L5BDetailP L5BDetailK L5BDetailZ L5BDetailH L5BDetailM Bo0_code_8e368_8f368
     AsanPlanCore AsanPlanSound Bo0PlanKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ADET.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5PSA. Import L5ADTP. Import L5ADK. Import L5ADH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
(* [comment removed for export] *)
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Let LY2 : as0_layout2 L := as0_layout2_of L C LY.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Local Abbreviation statics_vis := (L5ADH.statics_vis L ar C HI LY HIok).
Local Abbreviation ek_bytes := (L5ADH.ek_bytes L ar C IL LY ILY).
Local Abbreviation ek_src := (L5ADH.ek_src L ar C IL HI LY HIok).
Local Abbreviation ek_obj := (L5ADH.ek_obj L ar C HI LY HIok).
Local Abbreviation stack_rt := (L5ADH.stack_rt L ar).
Local Abbreviation stack_callee := (L5ADH.stack_callee L ar).
Local Abbreviation own_rt := (L5ADH.own_rt L ar).
Local Abbreviation own_callee := (L5ADH.own_callee L ar).
Local Abbreviation own_mem := (L5ADH.own_mem L ar).

Lemma defined_byte_d M a : L5.defined M a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> exists b, 0 <= b < 256 /\ L5.u8_at RSEGS M a b.
Proof.
  intros D Ha H1. unfold L5.u8_at. cbn [rdn].
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E.
  2:{ exfalso. apply (D 0). lia. rewrite Z.add_0_r. exact E. }
  exists (bv_unsigned b). split. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
  cbn. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Theorem detail_ok : assign_spec L ar HI -> reserve_spec L ar HI -> L5ASB.mul10_specB L ar HI -> L5ASB.addd_specB L ar HI -> opdel_sized_spec L ar HI -> L5PSB.detail_specB L ar IL HI.
Proof.
  unfold L5PSB.detail_specB, L5PSB.parser_spec_atB.
  intros Hasg Hres Hmul Hadd Hdel fx R M model K LB FF LK cr A p o sp r fb neg s HH AM HK G10 G11 G12 G13 LEN CR G1 RA G2 A32 G4 STK SSH FFR FFR2 FFRS BIG FB3 AOB SZ BYTES BR SRC APART KONT.
  specialize (G12 eq_refl).
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). rewrite DSCR_EQ in SLO, DSCR.
  set (sb := sp - 16).
  assert (SA : aligned sb 32 /\ (sb - 192) mod 16 = 0).
  { subst sb. unfold aligned. clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SA as (SA32 & SA16).
  assert (SPR : 0 <= sb < 2 ^ 64 /\ 140735332487520 <= sb <= 140737488355312) by (subst sb; clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (W176 : L5.writable RSEGS MV (sb - 192) 208).
  { apply (proj2 (writable_vis H M (sb - 192) 208 (VIS (sb - 192) 208 ltac:(subst sb; clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. rewrite DSCR_EQ. subst sb; clear; lia. subst sb; clear; lia. clear; lia. }
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp L5PSB.DETAIL_SCRB HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  assert (OR0 : 0 <= o < 2 ^ 64) by (clear - OR; lia).
  assert (NR : 0 <= (if neg then 1 else 0) < 2 ^ 64) by (destruct neg; clear; lia).
  assert (LR : 0 <= Z.of_nat (length s) < 2 ^ 64) by (clear - LEN; lia).
  (* [comment removed for export] *)
  pose proof (dtA_conc fx R MV (fun j => match j with 2%nat => sb | 33%nat => U R 10 | 34%nat => Z.of_nat (length s) | 35%nat => (if neg then 1 else 0) | 36%nat => o | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | subst sb; sc | (rewrite <- r10; exact G10) | (rewrite <- r11; exact G11) | (rewrite <- r12; exact G12) | (rewrite <- r13; exact G13)]).
  destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR18 & aR20 & aR22 & aR23 & aR26 & aQ_V2nat & aQ_V2nat_1 & aQ_V2nat_2 & aQ_V2nat_3 & aQ_V2nat_4 & aQ_V2nat_5 & aQ_V2nat_6 & aQ_V2nat_7 & aQ_V2nat_8 & aQ_V2nat_9 & aQ_V2nat_10 & aQ_V2nat_11 & aQ_V2nat_12 & aQ_V2nat_13)).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R DETAIL R1 SM2 M1v (fun a => sb - 192 <= a < sb + 16) K HH AM aMS MG1).
  { intros a Ha Hna. apply aFZ. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. subst sb; clear - Wa SLO SHI SPT; lia. clear; lia. subst sb; clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  (* [comment removed for export] *)
  pose proof (aio_stack_malloc _ _ _ _ _ HIok 2 ltac:(right; left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LY), (aly_sm2 L C LY), (aly_scr_sm L C LY) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = sb - 192). { rewrite r2, aR2. apply L5.unsigned_lit. clear - SPR; lia. }
  eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
  - rewrite r4, (aKS 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite r1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U2. replace (sb - 192) with (sp - 208) by (subst sb; clear; lia).
    apply (astack_ok_of_astk L ar C LY M M1 sp L5PSB.DETAIL_SCRB 208 512 STK MGM1). clear; lia. clear; lia. rewrite DSCR_EQ; clear; lia.
    replace (sp - 208) with (sb - 192) by (subst sb; clear; lia). exact SA16.
  - apply (ffrk_room 2 FF LK 2 FFR2). clear; lia.
  - intros f Hf. rewrite U2. specialize (FFRS f Hf). subst sb; clear - FFRS. lia.
  - exact HK.
  - (* [comment removed for export] *)
    intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
    rewrite U2 in FLNC. rewrite U2 in PRES2. rewrite U2 in HH2. rewrite ?U2. rewrite r1, aR1.
    pose proof (sm_facts L ar C HI LY HIok LB FF LK2 cr A M2 model2 F 2 (sb - 192 + 32) fl HH2 ltac:(right; left; reflexivity) FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
      as (FR & FFL & F32 & F8 & _ & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
    change (ff_bytes 2) with 256 in *. change (256 / 8) with 32 in *.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    assert (ASTK2 : astk ar M2 sp L5PSB.DETAIL_SCRB).
    { apply (astk_after_rt L ar C HI HIok LB FF LK cr A M M1 M2 _ sp _ (sb - 192) 512 HH STK MGM1 PRES2). rewrite DSCR_EQ; subst sb; clear; lia. subst sb; clear; lia. rewrite DSCR_EQ; clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & _).
    pose proof (statics_vis LB _ LK2 cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
    (* [comment removed for export] *)
    assert (AG2 : forall a, sb - 192 <= a < sb + 16 -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ha. unfold MV2. rewrite (mrestrict_visible H2 M2). 2:{ replace a with ((sb - 192) + (a - (sb - 192))) by (clear; lia). apply (VIS2 (sb - 192) 208). subst sb; clear - SLO; lia. clear - SPR; lia. clear - Ha; lia. }
      rewrite (proj1 PRES2 a). 2:{ clear - Ha SPR; lia. } 2:{ apply stack_client. subst sb; clear - Ha SLO SHI SPT; lia. clear - Ha; lia. }
      rewrite <- VIS1. symmetry. apply mrestrict_visible. replace a with ((sb - 192) + (a - (sb - 192))) by (clear; lia). apply (VIS (sb - 192) 208). subst sb; clear - SLO; lia. clear - SPR; lia. clear - Ha; lia. }
    assert (W176b : L5.writable RSEGS MV2 (sb - 192) 208).
    { eapply (L5C.writable_agree RSEGS M1v MV2). intros j Hj. apply AG2. clear - Hj; lia. clear - SPR; lia. clear - SPR; lia. eapply L5.writable_grows. exact MG1. exact W176. }
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 2 _ fl sp 0 (sb - 192) 208 HH2 SPT ltac:(right; left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC
                  ltac:(intros i Hi; apply stack_client; subst sb; clear - Hi SLO SHI SPT; lia) ltac:(clear; lia)) as (SF & SFSH & SFL).
    change (ff_bytes 2) with 256 in SF. change (ff_bytes 2 / 8) with 32 in SFSH.
    assert (XC : forall a v, sb - 184 <= a <= sb + 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hc. xfer AG2 Hc. }
    assert (FRK1v : frk sb R M1v). { unfold frk, U. repeat split; assumption. }
    assert (SVIS : forall a, sb - 192 <= a < sb + 16 -> H (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((sb - 192) + (a - (sb - 192))) by (clear; lia). apply (VIS (sb - 192) 208). subst sb; clear - SLO; lia. clear - SPR; lia. clear - Ha; lia. }
    assert (FRK2 : frk sb R M2).
    { apply (frk_agree sb R M1v M2 FRK1v). 2: clear - SPR; lia. 2: clear - SPR; lia. intros a Ha.
      rewrite (stack_rt LB FF (sb - 192) 512 M1 M2 a PRES2 ltac:(clear - Ha SPR; lia) ltac:(subst sb; clear - Ha SLO SHI SPT; lia) ltac:(clear - Ha; lia)).
      apply EQ1. apply SVIS. clear - Ha; lia. }
    assert (FLCv' : L5.u64_at RSEGS MV2 (F + 248) fl). { replace (F + 248) with (F + 256 - 8) by (clear; lia). exact FLCv. }
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 2 _ fl sp L5PSB.DETAIL_SCRB o 32 HH2 SPT ltac:(right; left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC OCL ltac:(clear; lia)) as (OF & OFSH & OFL).
    change (ff_bytes 2) with 256 in OF. change (ff_bytes 2 / 8) with 32 in OFSH.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (FQ31 : (F + 256 - 1) / 8 = F / 8 + 31 /\ F mod 8 = 0) by (clear - F8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (NCF : forall a, (F <= a < F + 256 \/ S F <= a <= S (F + 256 - 1)) -> ~ aclient L ar LB FF sp L5PSB.DETAIL_SCRB a).
    { intros a Ha. apply (fresh_frame_not_client L ar C HI LY HIok LB FF LK cr A M _ sp L5PSB.DETAIL_SCRB F 256 a HH SPT).
      clear - FR; lia. exact FCEIL. exact FAPP. exact (proj2 FQ31). clear; lia. reflexivity.
      eapply fframes_apart_incl. exact FAPART. intros g0 Hg; apply in_or_app; left; exact Hg. exact FBLK. exact Ha. }
    assert (NCS : forall a, sb - 192 <= a < sb + 16 -> ~ aclient L ar LB FF sp L5PSB.DETAIL_SCRB a).
    { intros a X Hc. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp L5PSB.DETAIL_SCRB a HH SPT Hc) as [Y|Y]. rewrite DSCR_EQ in Y. subst sb; clear - X Y; lia. subst sb; clear - X Y SLO; lia. }
    assert (EK2 : ek L ar LB FF sp L5PSB.DETAIL_SCRB [] M M2).
    { eapply ek_trans. { apply (ek_piece L ar LB FF sp L5PSB.DETAIL_SCRB [] M M1 (fun a => sb - 192 <= a < sb + 16) FRM1). intros a Ha Hc _ X. exact (NCS a X Hc). }
      apply (ek_rt L ar LB FF [] sp L5PSB.DETAIL_SCRB (sb - 192) 512 [] M1 M2 PRES2). rewrite DSCR_EQ; subst sb; clear; lia. subst sb; clear; lia. }
    assert (DK2 : dk L ar LB FF sp L5PSB.DETAIL_SCRB M M2).
    { eapply dk_trans. apply dk_grows. exact MGM1. apply (dk_rt L ar LB FF [] sp L5PSB.DETAIL_SCRB (sb - 192) 512 M1 M2 PRES2). rewrite DSCR_EQ; subst sb; clear; lia. subst sb; clear; lia. }
    destruct s as [|c0 t].
    { (* [comment removed for export] *)
      cbn [length Z.of_nat] in *.
      pose proof (dtB0_conc fx1 R2 MV2 (fun j => match j with 2%nat => sb | 33%nat => U R 10 | 35%nat => (if neg then 1 else 0) | 36%nat => o | 40%nat => F | 41%nat => fl
                    | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                    | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 54%nat => U R 27 | 58%nat => U R2 1 | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (apply XC; [clear; lia | unfold U; sc]) ]).
      destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR1 & bR2 & bR8 & bR9 & bR10 & bR11 & bR12 & bR13 & bR18 & bR19 & bR20 & bR21 & bR22 & bR23 & bR24 & bR25 & bR26 & bR27 & bFL0 & BSH)).
      assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
      pose proof (ret_to fx3 R3 M3v 0x8f210 W_8f210 r F_8f210 eq_refl D_8f210 ltac:(rewrite bR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
      pose proof (msteps_trans _ _ _ _ bMS RET) as MS4. clear bMS RET.
      set (W3 := fun a => (sb - 136 <= a < sb - 104 \/ F <= a < F + 24 \/ F / 8 + SB <= a < F / 8 + SB + 32) \/ a = fl).
      apply (apiece_retire L ar C HI LY HIok LB FF LK2 cr A M2 model2 fx1 fx3 R2 0x8eda4 R3 r M3v W3 F 2 (sb - 192 + 32) fl K HH2 (conj Hh2 MI2)).
      { exact FLC. }
      { exact FLNC. }
      { exact VFL. }
      { clear - FLR; lia. }
      { exact MS4. }
      { exact MG3. }
      { intros a Ha Hna. apply bFZ. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; unfold SB in *; lia. }
      { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [[Wa|[Wa|Wa]]|Wa].
        - right. apply stack_client. subst sb; clear - Wa SLO SHI SPT; lia. clear; lia.
        - right. apply (fframe_client L ar LB _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Wa; lia.
        - right. apply (fframe_shadow_client L ar LB _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256.
          unfold in_shadow_of, S. clear - Wa F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        - left; exact Wa. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      { intros a. subst W3; cbn beta. repeat match goal with X : _ |- _ => clear X end.
        destruct (rng_dec a (sb - 136) (sb - 104)); [left; tauto|]. destruct (rng_dec a F (F + 24)); [left; tauto|].
        destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + 32)); [left; tauto|]. destruct (Z.eq_dec a fl); [left; tauto|]. right; tauto. }
      { exact bFL0. }
      intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
      assert (ASTK3 : astk ar M3 sp L5PSB.DETAIL_SCRB). { eapply astk_grows. exact ASTK2. exact MGM3. }
      assert (OFR : forall a, o <= a < o + 32 -> ~ (sb - 192 <= a < sb + 16)) by (intros a Ha; subst sb; clear - Ha OR SLO; lia).
      apply (KONT fx3 R3 M3 model3 LB cr LK2 A).
      - split.
        { apply preserved_by_index. intros k Hk. cbn in Hk.
          destruct Hk as [<-|Hk]. { rewrite bR2. rewrite <- r2, G2. f_equal. subst sb; clear; lia. }
          destruct Hk as [<-|Hk]. { rewrite (bKS 3%nat) by inl. rewrite (cs_of_preserved R1 R2 3 RP2) by inl. apply aKS. inl. }
          destruct Hk as [<-|Hk]. { rewrite (bKS 4%nat) by inl. rewrite (cs_of_preserved R1 R2 4 RP2) by inl. apply aKS. inl. }
          repeat (destruct Hk as [<-|Hk]; [first [rewrite bR8 | rewrite bR9 | rewrite bR18 | rewrite bR19 | rewrite bR20 | rewrite bR21 | rewrite bR22 | rewrite bR23
                                                 | rewrite bR24 | rewrite bR25 | rewrite bR26 | rewrite bR27]; symmetry; apply U_to |]). destruct Hk. }
        right. split. left; reflexivity. split. rewrite r11. exact bR11.
        split. reflexivity.
        split. { eapply L5C.big_at_agree. 4: exact BIG. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi.
                 rewrite FRM3. 2: clear - Hi OR; lia. 2:{ subst W3; cbn beta. clear - Hi OF OFSH OFL OFR. specialize (OFR i Hi). unfold SB in *. lia. }
                 rewrite (proj1 PRES2 i). 2: clear - Hi OR; lia. 2:{ apply (aclient_narrow L ar LB FF sp L5PSB.DETAIL_SCRB). replace i with (o + (i - o)) by (clear; lia). apply (OCL (i - o)). clear - Hi; lia. subst sb; clear - Hi OR SLO; lia. }
                 apply FRM1. clear - Hi OR; lia. exact (OFR i Hi). }
        split. { unfold parse_debit. eapply credit_le_trans. apply adebit_le. exact LY2. apply vblk_pos. apply adebit_le. exact LY2. apply vblk_pos. }
        apply ahpres_of.
        + eapply ek_trans. exact EK2.
          intros a (Ha & Hc & Ho). apply FRM3. exact Ha. subst W3; cbn beta. intros [[X|[X|X]]|X].
          * apply (NCS a). clear - X; lia. exact Hc.
          * apply (NCF a). left; clear - X; lia. exact Hc.
          * apply (NCF a). right. unfold S. rewrite (proj1 FQ31). clear - X. unfold SB in X |- *. lia. exact Hc.
          * subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc.
        + eapply astk_defined. exact ASTK3. clear; lia. clear; lia.
        + eapply dk_trans. exact DK2.
          apply dk_grows. exact MGM3.
      - eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT3.
      - apply incl_refl.
      - exact AM3.
      - exact LKI2.
      - exact HH3. }
    (* [comment removed for export] *)
    set (n := Z.of_nat (length (c0 :: t))) in *.
    assert (HVN : 1 <= n <= 4999) by (subst n; cbn [length] in *; clear - LEN; lia).
    pose proof (asrc_range L ar C IL HI LY ILY HIok LB FF LK cr A M _ p n HH SRC ltac:(clear - HVN; lia)) as [P0 P1].
    assert (PRG : 4096 <= p <= 140737479966720 /\ p + n <= 140737479966720) by (clear - P0 P1 SPT HVN; lia).
    assert (UP : U R 10 = p). { apply (U_of R 10 p). rewrite <- r10. exact G10. clear - PRG; lia. }
    rewrite UP in *.
    pose proof (dtB1_conc fx1 R2 MV2 (fun j => match j with 2%nat => sb | 33%nat => p | 34%nat => n | 35%nat => (if neg then 1 else 0) | 36%nat => o | 40%nat => F | 41%nat => fl | 58%nat => U R2 1 | _ => 0 end)) as P.
    cbn beta iota in P.
    assert (HVN' : 1 <= n <= 67108863) by (clear - HVN; lia).
    feed P ltac:(first [apply UR | apply U_to | sc ]).
    destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR10 & bR11 & bR12 & bR13 & bR14 & bR19 & bR21 & bR24 & bR25 & bCEND & bC152 & bC144 & bC160 & bC168 & bB_V40nat & bB_V40nat_1 & bB_V40nat_2 & bB_V40nat_3 & bB_V40nat_4 & bB_V40nat_5 & bB_V40nat_6 & bB_V40nat_7 & bB_V40nat_8 & bB_V40nat_9 & bB_V40nat_10 & bB_V40nat_11 & bB_V40nat_12 & bB_V40nat_13 & bB_V40nat_14 & bB_V40nat_15 & bB_V40nat_16 & bB_V40nat_17 & bB_V40nat_18 & bB_V40nat_19 & bQ_V40nat & bQ_V40nat_1 & bQ_V40nat_2 & bC112 & bDF)).
    set (W3 := fun a => sb - 168 <= a < sb - 104 \/ F <= a < F + 24 \/ F / 8 + SB <= a < F / 8 + SB + 20).
    apply (apiece L ar C HI LY HIok LB _ LK2 cr A M2 model2 fx1 fx3 R2 0x8eda4 R3 0x8eeb4 M3v W3 K HH2 (conj Hh2 MI2) bMS MG3).
    { intros a Ha Hna. apply bFZ. exact Ha. all: clear - Hna; subst W3; cbn beta in Hna; unfold SB in *; lia. }
    { intros a Ha Wa. subst W3; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
      - split. apply stack_client. subst sb; clear - Wa SLO SHI SPT; lia. clear; lia. subst sb; clear - Wa SLO SPT; lia.
      - split. apply (fframe_client L ar LB _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Wa; lia. clear - Wa FR; lia.
      - split. apply (fframe_shadow_client L ar LB _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. unfold in_shadow_of, S. clear - Wa F8. unfold SB in *.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        clear - Wa FR; unfold SB in Wa; lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    set (FF' := (F, 2, sb - 192 + 32) :: FF) in *.
    assert (ASTK3 : astk ar M3 sp L5PSB.DETAIL_SCRB). { eapply astk_grows. exact ASTK2. exact MGM3. }
    assert (EK3 : ek L ar LB FF sp L5PSB.DETAIL_SCRB [] M M3).
    { eapply ek_trans. exact EK2. apply (ek_piece L ar LB FF sp L5PSB.DETAIL_SCRB [] M2 M3 W3 FRM3). intros a Ha Hc _ X. subst W3; cbn beta in X. destruct X as [X|[X|X]].
      - apply (NCS a). clear - X; lia. exact Hc.
      - apply (NCF a). left; clear - X; lia. exact Hc.
      - apply (NCF a). right. unfold S. rewrite (proj1 FQ31). clear - X. unfold SB in X |- *. lia. exact Hc. }
    assert (DK3 : dk L ar LB FF sp L5PSB.DETAIL_SCRB M M3). { eapply dk_trans. exact DK2. apply dk_grows. exact MGM3. }
    (* [comment removed for export] *)
    assert (BY3 : L5.bytes_at RSEGS M3 p (c0 :: t)). { apply (ek_bytes LB FF sp L5PSB.DETAIL_SCRB M M3 p (c0 :: t) EK3 SRC). clear - PRG; lia. fold n. clear - PRG; lia. exact BYTES. }
    assert (SRC3 : asrc IL LB FF' M3 p n). { apply (ek_src LB FF LK cr A sp L5PSB.DETAIL_SCRB M model M3 LB FF' p n HH EK3 SRC). apply incl_refl. apply incl_tl. apply incl_refl. }
    pose proof (asrc_vis L ar C IL HI LY ILY HIok LB FF' LK2 cr A M3 model3 p n HH3 SRC3) as PVIS3.
    assert (MV3E : mrestrict (ahid A model3) M3 = M3v) by (rewrite AH3; exact VIS3).
    assert (BY3v : L5.bytes_at RSEGS M3v p (c0 :: t)).
    { rewrite <- MV3E. eapply L5C.bytes_at_agree. 4: exact BY3. 2: clear - PRG; lia. 2: fold n; clear - PRG; lia.
      intros i Hi. apply mrestrict_visible. replace i with (p + (i - p)) by (clear; lia). apply PVIS3. fold n in Hi. clear - Hi; lia. }
    assert (ACC3v : aacc M3v p n).
    { rewrite <- MV3E. apply (aacc_vis (ahid A model3) M3 p n). apply (asrc_aacc L ar C IL HI ILY HIok ICok LB FF' LK2 cr A M3 _ p n HH3 SRC3).
      intros a Ha. apply (asrc_shadow_vis L ar C IL HI LY ILY HIok ICok LB FF' LK2 cr A M3 model3 p n a HH3 SRC3 Ha). }
    assert (W176c : L5.writable RSEGS M3v (sb - 192) 208) by (eapply L5.writable_grows; [exact MG3 | exact W176b]).
    assert (SVIS3 : forall a, sb - 192 <= a < sb + 16 -> ahid A model2 (Z_to_bv 64 a) = false).
    { intros a Ha. replace a with ((sb - 192) + (a - (sb - 192))) by (clear; lia). apply (VIS2 (sb - 192) 208). subst sb; clear - SLO; lia. clear - SPR; lia. clear - Ha; lia. }
    assert (FRK3 : frk sb R M3). { apply (frk_agree sb R M2 M3 FRK2). 2: clear - SPR; lia. 2: clear - SPR; lia. intros a Ha. apply FRM3. clear - Ha SPR; lia.
      subst W3; cbn beta. clear - Ha SF SFSH. unfold SB in *. lia. }
    assert (SPK3 : spk sb F (if neg then 1 else 0) M3).
    { apply (spk_agree sb F _ M3v M3). unfold spk. split. exact bC112. split. exact bC144. split. exact bC152. exact bC168. 2: clear - SPR; lia. 2: clear - SPR; lia.
      intros a Ha _. apply EQ3. apply SVIS3. clear - Ha; lia. }
    assert (SBC : ahl_ceil ar + 4096 <= sb - 192) by (subst sb; clear - SLO; lia).
    assert (FRR : 4096 <= F /\ F + 256 <= 2 ^ 47 /\ (F / 8) * 8 = F) by (clear - FR F8; lia).
    assert (OWN3 : own sb F R (if neg then 1 else 0) M3).
    { split. exact FRK3. split. exact SPK3. eapply L5.defined_grows. exact MGM3. intros i Hi. unfold shadow_zero, byte_at, S in FSH. rewrite (FSH i Hi). discriminate. }
    pose proof (statics_vis LB FF' LK2 cr A M3 model3 HH3) as ST3. cbv zeta in ST3. rewrite MV3E in ST3. destruct ST3 as (IMGC3 & CSB3 & CUAR3).
    (* [comment removed for export] *)
    destruct (L5ADZ.zskip_run sb F p (c0 :: t) M3v ltac:(clear - SPR; lia) SA32 W176c bCEND IMGC3 CSB3 CUAR3 ltac:(clear - FR; lia) ltac:(fold n; clear - PRG; lia) BY3v BR ACC3v LEN
                (length (c0 :: t)) 0%nat fx3 R3 ltac:(clear; lia) ltac:(cbn [length]; clear; lia) ltac:(intros i Hi; exfalso; clear - Hi; lia))
      as (fx4 & R4 & z & MSz & KSz & zR11 & ZL & ZZ & ZN).
    { unfold L5ADZ.zhead. change (Z.of_nat 0) with 0. rewrite !Z.add_0_r. fold n. repeat split; sc. }
    rewrite <- MV3E in MSz.
    apply (apiece_ro L ar C HI LY HIok LB FF' LK2 cr A M3 model3 fx3 fx4 R3 0x8eeb4 R4 0x8eee8 (mrestrict (ahid A model3) M3) K HH3 AM3 MSz (mem_grows_refl _) (fun a _ => eq_refl)).
    intros M4 model4 HH4 AM4 RT4 AH4 VIS4 MGM4 FRM4.
    assert (E43 : M4 = M3) by (apply mem_eq_of_agree; exact FRM4). subst M4. clear FRM4 MGM4.
    assert (MV4E : mrestrict (ahid A model4) M3 = M3v) by (rewrite AH4; exact MV3E).
    (* [comment removed for export] *)
    assert (FDEF3 : L5.defined M3v F 256) by (eapply L5.defined_grows; [exact MG3 | exact FDEFv]).
    assert (FW3 : L5.writable RSEGS M3v F 256) by (eapply L5.writable_grows; [exact MG3 | exact FWv]).
    assert (FSHW3 : L5.writable RSEGS M3v (F / 8 + SB) 32) by (eapply L5.writable_grows; [exact MG3 | exact FSHW]).
    assert (FLW3 : L5.writable RSEGS M3v fl 1) by (eapply L5.writable_grows; [exact MG3 | exact FLWv]).
    assert (FLC3 : L5.u64_at RSEGS M3v (F + 248) fl).
    { eapply L5C.u64_at_agree. 4: exact FLCv'. 2: clear - FR; lia. 2: clear - FR; lia. intros j Hj. apply bFZ. clear - Hj FR; lia.
      all: clear - Hj FR F8 SF FBIG; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). all: lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (XM3 : forall a v, sb - 192 <= a -> a + 8 <= sb + 16 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS M3 a v).
    { intros a v Xa Xb X. eapply L5C.u64_at_agree. 4: exact X. 2: clear - SPR Xa; lia. 2: clear - SPR Xb; lia. intros i Hi. apply EQ3. apply SVIS3. clear - Hi Xa Xb; lia. }
    assert (CEL3 : L5.u64_at RSEGS M3 (sb - 136) (p + n) /\ L5.u64_at RSEGS M3 (sb - 160) o).
    { split. apply XM3. clear; lia. clear; lia. exact bCEND. apply XM3. clear; lia. clear; lia. exact bC160. }
    assert (CELX : forall Ma Mb, (forall a, sb - 160 <= a < sb - 128 -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
              L5.u64_at RSEGS Ma (sb - 136) (p + n) /\ L5.u64_at RSEGS Ma (sb - 160) o -> L5.u64_at RSEGS Mb (sb - 136) (p + n) /\ L5.u64_at RSEGS Mb (sb - 160) o).
    { intros Ma Mb AG [X1 X2]. split.
      - eapply L5C.u64_at_agree. 4: exact X1. 2: clear - SPR; lia. 2: clear - SPR; lia. intros i Hi. apply AG. clear - Hi; lia.
      - eapply L5C.u64_at_agree. 4: exact X2. 2: clear - SPR; lia. 2: clear - SPR; lia. intros i Hi. apply AG. clear - Hi; lia. }
    destruct (Nat.eq_dec z (length (c0 :: t))) as [ZALL|ZNOT].
    { (* [comment removed for export] *)
      assert (zE : getr R4 (reg 11) = Z_to_bv 64 (p + n)). { rewrite zR11. f_equal. subst n. rewrite ZALL. reflexivity. }
      destruct (defined_byte_d M3v (F + 32)) as (jT & JTR & JTB).
      { intros j Hj. replace (F + 32 + j) with (F + (32 + j)) by (clear; lia). apply FDEF3. clear - Hj; lia. }
      clear - FR; lia. clear - FR; lia.
      assert (JTR' : 0 <= jT <= 255 /\ 0 <= jT < 2 ^ 64) by (clear - JTR; lia). destruct JTR' as [JTR1 JTR2].
      set (fT := L5ADM.fbWj jT false).
      assert (FT0 : Z.testbit fT 0 = false) by exact (L5ADM.fbNj_bit0 jT false false JTR).
      assert (FTR : 0 <= fT <= 255 /\ 0 <= fT < 2 ^ 64) by (pose proof (L5ADM.fbNj_range jT false false JTR) as X; unfold L5ADM.fbNj in X; fold fT in X; clear - X; lia).
      destruct FTR as [FTR1 FTR2].
      pose proof (dtQz_conc fx4 R4 M3v (fun j => match j with 2%nat => sb | 40%nat => F | 41%nat => fl | 55%nat => p + n | 58%nat => U R4 1 | 60%nat => jT | _ => 0 end)) as P.
      cbn beta iota in P.
      assert (PNR : 0 <= p + n < 2 ^ 64 /\ 4096 <= p + n <= 140737488355327) by (clear - PRG HVN; lia).
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx5 & R5 & M5v & MG5 & qFR & qFZ & (qMS & qKS & qR1 & qR10 & qR11 & qR12 & qR18 & qT0 & qS7 & qS6 & qS5 & qS4 & qDF & qDF1)).
      rewrite (L5ADM.fbWj_div4 jT JTR) in qT0. fold fT in qT0.
      rewrite <- MV4E in qMS, MG5, qFZ.
      set (W5 := fun a => F + 32 <= a < F + 33 \/ F / 8 + SB + 4 <= a < F / 8 + SB + 8).
      apply (apiece L ar C HI LY HIok LB FF' LK2 cr A M3 model4 fx4 fx5 R4 0x8eee8 R5 0x5e7f0 M5v W5 K HH4 AM4 qMS MG5).
      { intros a Ha Hna. apply qFZ. exact Ha. all: clear - Hna; subst W5; cbn beta in Hna; unfold SB in *; lia. }
      { intros a Ha Wa. subst W5; cbn beta in Wa. destruct Wa as [Wa|Wa].
        - split. apply (fframe_client L ar LB _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Wa; lia. clear - Wa FR; lia.
        - split. apply (fframe_shadow_client L ar LB _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. unfold in_shadow_of, S. clear - Wa F8. unfold SB in *.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
          clear - Wa FR; unfold SB in Wa; lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      intros M5 model5 HH5 AM5 RT5 AH5 VIS5 MGM5 FRM5 EQ5.
      assert (ASTK5 : astk ar M5 sp L5PSB.DETAIL_SCRB). { eapply astk_grows. exact ASTK3. exact MGM5. }
      pose proof (vis_pack L ar C HI LY HIok LB FF' LK2 cr A M5 model5 HH5) as (_ & VIS5s & _ & VFS5 & _ & _ & VFSSH5 & _).
      (* [comment removed for export] *)
      pose proof (aio_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
      rewrite (aly_segs L C LY), (aly_memset L C LY), (aly_scr_mem L C LY) in MS.
      assert (U25 : bv_unsigned (getr R5 2%bv) = sb - 192). { rewrite r2. replace (getr R5 (reg 2)) with (Z_to_bv 64 (sb - 192)) by (symmetry; rk). apply L5.unsigned_lit. clear - SPR; lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      assert (FSH4 : (F + 32) / 8 = F / 8 + 4 /\ (F + 32) mod 8 = 0 /\ (F + 96) / 8 = F / 8 + 12 /\ (F + 96) mod 8 = 0) by (clear - F8; lia).
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (SHV5 : forall a, F / 8 + SB <= a < F / 8 + SB + 32 -> ahid A model5 (Z_to_bv 64 a) = false).
      { intros a Ha. rewrite AH5, AH4, AH3. replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply VSH. clear - Ha; lia. }
      assert (T1Z5 : shadow_zero M5 (F + 32) 4).
      { intros j Hj. unfold byte_at, S. rewrite (proj1 FSH4).
        assert (X : L5.u8_at RSEGS M5v (F / 8 + 4 + SB + j) 0).
        { assert (J : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by (clear - Hj; lia). unfold SB. destruct J as [J|[J|[J|J]]]; subst j; gmem. }
        rewrite EQ5. apply (byte_of_u8 M5v _ 0 X). right. clear - Hj FR F8; unfold SB; lia. clear - Hj FR F8; unfold SB; lia.
        rewrite <- AH5. apply SHV5. clear - Hj; lia. }
      eapply (MS fx5 R5 M5 model5 LB FF' LK2 cr A (F + 40) 0 16 K); clear MS.
      { split. exact HH5. split. exact (proj1 AM5). split. exact (proj2 AM5).
        split. rewrite r10. exact qR10. split. rewrite r12. exact qR12. split. clear; lia.
        split. rewrite r4. rk. split. rewrite r1, qR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
        split. { rewrite U25. replace (sb - 192) with (sp - 208) by (subst sb; clear; lia).
                 apply (astack_ok_of_astk L ar C LY M3 M5 sp L5PSB.DETAIL_SCRB 208 2560 ASTK3 MGM5). clear; lia. clear; lia. rewrite DSCR_EQ; clear; lia.
                 replace (sp - 208) with (sb - 192) by (subst sb; clear; lia). exact SA16. }
        split. { eapply aacc_of_zero. exact T1Z5. exact (proj1 (proj2 FSH4)). clear - FR; lia. clear; lia. clear; lia. }
        split. { intros i Hi. rewrite U25. apply (fframe_client L ar LB _ _ _ F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Hi; lia. }
        split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M5 (F + 40) 16). 2: clear - FR; lia. 2: clear - FR; lia. 2: exact Hi. 2: exact Hm.
                 eapply L5.defined_grows. exact MGM5. eapply L5.defined_grows. exact MGM3. intros j Hj. replace (F + 40 + j) with (F + (40 + j)) by (clear; lia). apply FDEF. change (ff_bytes 2) with 256. clear - Hj; lia. }
        split. exact HK. apply (app_rng_fs L ar C HI HIok _ _ _ _ _ _ _ (F + 40) 16 HH5). clear - FS1; lia. pose proof FS2 as FS2'. change (ff_bytes 2) with 256 in FS2'. clear - FS2'; lia. }
      { rewrite r11. exact qR11. }
      intros R6 M6 model6 mR10 RP6 ZB PRES6 SDEF6 RT6 MI6 HH6. rewrite U25 in PRES6, SDEF6. rewrite r1, qR1.
      assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 AM5). }
      assert (ASTK6 : astk ar M6 sp L5PSB.DETAIL_SCRB).
      { apply (astk_after_eq L ar C HI HIok LB FF' LK2 cr A M5 M5 M6 _ sp _ (sb - 192) 2560 HH5 ASTK5 (mem_grows_refl M5)).
        intros a Ha Hs Hns. apply PRES6. exact Ha. apply stack_client. exact Hs. exact Hns. clear - Hs FR FCEIL; lia. exact SDEF6.
        rewrite DSCR_EQ; subst sb; clear; lia. subst sb; clear; lia. rewrite DSCR_EQ; clear; lia. }
      pose proof (vis_pack L ar C HI LY HIok LB FF' LK2 cr A M6 model6 HH6) as (_ & VIS6 & _ & VFS6 & _ & _ & VFSSH6 & _).
      pose proof (statics_vis LB FF' LK2 cr A M6 model6 HH6) as (IMGC6 & CSB6 & CUAR6).
      set (H6 := ahid A model6) in *. set (MV6 := mrestrict H6 M6) in *.
      assert (W176f : L5.writable RSEGS MV6 (sb - 192) 208).
      { apply (proj2 (writable_vis H6 M6 (sb - 192) 208 (VIS6 (sb - 192) 208 ltac:(subst sb; clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
        eapply (astk_writable ar M6 sp). exact ASTK6. rewrite DSCR_EQ. subst sb; clear; lia. subst sb; clear; lia. clear; lia. }
      (* [comment removed for export] *)
      assert (OWN5 : own sb F R (if neg then 1 else 0) M5).
      { apply (own_piece sb F R _ (proj2 SPR) M3 M5 W5 OWN3 FRM5 MGM5). intros a Ha _. subst W5; cbn beta. clear - Ha SF SFSH. unfold SB in *. lia. }
      assert (OWN6 : own sb F R (if neg then 1 else 0) M6).
      { apply (own_mem sb F (sb - 192 + 32) R _ (proj2 SPR) SBC FRR LB FF' (sb - 192) 2560 (fun a => F + 40 <= a < F + 40 + 16) M5 M6 OWN5 PRES6). left; reflexivity. clear; lia.
        intros a Da. clear - Da FR FCEIL FBIG. unfold SB. lia. }
      assert (CEL5 : L5.u64_at RSEGS M5 (sb - 136) (p + n) /\ L5.u64_at RSEGS M5 (sb - 160) o).
      { apply (CELX M3 M5). 2: exact CEL3. intros a Ha. apply FRM5. clear - Ha SPR; lia. subst W5; cbn beta. clear - Ha SF SFSH. unfold SB in *. lia. }
      assert (CEL6 : L5.u64_at RSEGS M6 (sb - 136) (p + n) /\ L5.u64_at RSEGS M6 (sb - 160) o).
      { apply (CELX M5 M6). 2: exact CEL5. intros a Ha. apply PRES6. clear - Ha SPR; lia. apply stack_client. subst sb; clear - Ha SLO SHI SPT; lia. clear - Ha; lia. clear - Ha SF; lia. }
      assert (SV6 : avis H6 (sb - 192) 208). { apply (VIS6 (sb - 192) 208). subst sb; clear - SLO; lia. clear - SPR; lia. }
      assert (SHV6 : avis H6 (F / 8 + SB) 32).
      { apply (VFSSH6 (F / 8 + SB) 32). intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      assert (FV6 : avis H6 F 256) by (apply (VFS6 F 256 FS1 FS2)).
      assert (OWN6v : own sb F R (if neg then 1 else 0) MV6) by (apply (own_vis sb F R _ (proj2 SPR) H6 M6 OWN6 SV6 SHV6)).
      destruct OWN6v as (_ & (T112 & T144 & T152 & T168) & FSD6).
      assert (OSP6v : L5.u64_at RSEGS MV6 (sb - 160) o).
      { apply (proj2 (u64_at_vis H6 M6 (sb - 160) o ltac:(eapply avis_sub; [exact SV6 | clear; lia | clear; lia]) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))). exact (proj2 CEL6). }
      pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (_ & WF6 & _).
      assert (FDEF6 : L5.defined MV6 F 256). { apply (proj2 (defined_vis H6 M6 F 256 FV6)). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF6 _ (or_introl eq_refl))))))). }
      assert (FW6 : L5.writable RSEGS MV6 F 256). { apply (L5C.writable_of_defined RSEGS). exact FDEF6. clear - FR; lia. clear - FR; lia. }
      assert (FSHW6 : L5.writable RSEGS MV6 (F / 8 + SB) 32). { apply (L5C.writable_of_defined RSEGS). exact FSD6. clear - FR F8; unfold SB; lia. clear - FR F8; unfold SB; lia. }
      pose proof (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model6 F 2 _ _ fl HH2 HH6 (or_introl eq_refl) (or_introl eq_refl) (or_intror (or_introl eq_refl)) FLC) as [FLC6 FL6].
      change (ff_bytes 2) with 256 in FLC6, FL6. replace (F + 256 - 8) with (F + 248) in FL6 by (clear; lia).
      pose proof (fl_writable L ar C HI LY HIok _ FF' LK2 _ A M6 _ fl HH6 FLP) as [FLD6 FLW6].
      pose proof (fl_vis L ar C HI LY HIok _ FF' LK2 _ A M6 model6 fl HH6 FLP) as FLV6.
      assert (FLW6v : L5.writable RSEGS MV6 fl 1). { apply (proj2 (writable_vis H6 M6 fl 1 FLV6 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW6. }
      (* [comment removed for export] *)
      pose proof (dtAZ2_conc fx5 R6 MV6 (fun j => match j with 2%nat => sb | 36%nat => o | 40%nat => F | 41%nat => fl | 58%nat => U R6 1 | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx7 & R7 & M7v & MG7 & yFR & yFZ & (yMS & yKS & yR1 & yR10 & yR11 & yR19 & yR24 & yC56 & _)).
      set (W7 := fun a => F + 56 <= a < F + 64).
      apply (apiece L ar C HI LY HIok LB FF' LK2 cr A M6 model6 fx5 fx7 R6 0x8ef30 R7 ASSIGN M7v W7 K HH6 (conj Hh6 MI6) yMS MG7).
      { intros a Ha Hna. apply yFZ. exact Ha. clear - Hna; subst W7; cbn beta in Hna; lia. }
      { intros a Ha Wa. subst W7; cbn beta in Wa. split. apply (fframe_client L ar LB _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Wa; lia. clear - Wa FR; lia. }
      intros M7 model7 HH7 AM7 RT7 AH7 VIS7 MGM7 FRM7 EQ7.
      assert (AG7 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 56 <= a < F + 64) -> M7 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
      { intros a Ha Hn. apply FRM7. exact Ha. exact Hn. }
      assert (ASTK7 : astk ar M7 sp L5PSB.DETAIL_SCRB). { eapply astk_grows. exact ASTK6. exact MGM7. }
      assert (OWN7 : own sb F R (if neg then 1 else 0) M7).
      { apply (own_piece sb F R _ (proj2 SPR) M6 M7 W7 OWN6 FRM7 MGM7). intros a Ha _. subst W7; cbn beta. clear - Ha SF. lia. }
      assert (CEL7 : L5.u64_at RSEGS M7 (sb - 136) (p + n) /\ L5.u64_at RSEGS M7 (sb - 160) o).
      { apply (CELX M6 M7). 2: exact CEL6. intros a Ha. apply AG7. clear - Ha SPR; lia. clear - Ha SF; lia. }
      (* [comment removed for export] *)
      assert (EK5 : ek L ar LB FF sp L5PSB.DETAIL_SCRB [] M M5).
      { eapply ek_trans. exact EK3. apply (ek_piece L ar LB FF sp L5PSB.DETAIL_SCRB [] M3 M5 W5 FRM5). intros a Ha Hc _ X. subst W5; cbn beta in X. destruct X as [X|X].
        - apply (NCF a). left; clear - X; lia. exact Hc.
        - apply (NCF a). right. unfold S. rewrite (proj1 FQ31). clear - X. unfold SB in X |- *. lia. exact Hc. }
      assert (EK6 : ek L ar LB FF sp L5PSB.DETAIL_SCRB [] M M6).
      { eapply ek_trans. exact EK5. apply (ek_mem L ar LB FF sp L5PSB.DETAIL_SCRB (sb - 192) 2560 (fun a => F + 40 <= a < F + 56) [] M5 M6).
        - intros a Ha Hc ND. apply PRES6. exact Ha. apply aclient_cons. exact Hc. clear - ND; lia.
        - rewrite DSCR_EQ; subst sb; clear; lia.
        - subst sb; clear; lia.
        - intros a Hc _ X. apply (NCF a). left; clear - X; lia. exact Hc. }
      assert (EK7 : ek L ar LB FF sp L5PSB.DETAIL_SCRB [] M M7).
      { eapply ek_trans. exact EK6. apply (ek_piece L ar LB FF sp L5PSB.DETAIL_SCRB [] M6 M7 W7 FRM7). intros a Ha Hc _ X. subst W7; cbn beta in X.
        apply (NCF a). left; clear - X; lia. exact Hc. }
      assert (DK6 : dk L ar LB FF sp L5PSB.DETAIL_SCRB M M6).
      { eapply dk_trans. exact DK3. eapply dk_trans. apply dk_grows. exact MGM5.
        apply (dk_mem L ar LB FF sp L5PSB.DETAIL_SCRB (sb - 192) 2560 (fun a => F + 40 <= a < F + 56) M5 M6).
        - intros a Ha Hc ND. apply PRES6. exact Ha. apply aclient_cons. exact Hc. clear - ND; lia.
        - exact SDEF6.
        - intros a Da. destruct (ZB (a - (F + 40)) ltac:(clear - Da; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (F + 40 + (a - (F + 40))) with a in Bv by (clear; lia). rewrite Bv. discriminate.
        - intros a. destruct (rng_dec a (F + 40) (F + 56)); [left|right]; assumption.
        - rewrite DSCR_EQ; subst sb; clear; lia.
        - subst sb; clear; lia. }
      assert (DK7 : dk L ar LB FF sp L5PSB.DETAIL_SCRB M M7). { eapply dk_trans. exact DK6. apply dk_grows. exact MGM7. }
      destruct (ek_obj LB FF LK cr A sp L5PSB.DETAIL_SCRB M model M7 o HH EK7 AOB) as [OEQ7 OSH7].
      assert (BIG7 : L5.big_at RSEGS M7 o (L5.BO fb 0 (L5.BInl 0 0))). { eapply L5C.big_at_agree. 4: exact BIG. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply OEQ7. exact Hi. }
      assert (SZ7 : shadow_zero M7 o 4). { intros j Hj. unfold byte_at. rewrite OSH7 by exact Hj. apply SZ. exact Hj. }
      (* [comment removed for export] *)
      assert (FCL6 : forall a, F + 32 <= a < F + 248 -> aclient L ar LB FF' (sb - 192) 2560 a).
      { intros a Ha. apply (fframe_client L ar LB _ _ _ F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Ha; lia. }
      assert (T1F5 : L5.u8_at RSEGS M5 (F + 32) fT).
      { apply (proj1 (u8_at_vis (ahid A model5) M5 (F + 32) fT ltac:(eapply avis_sub; [exact (VFS5 F 256 FS1 FS2) | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))).
        rewrite AH5, VIS5. exact qT0. }
      assert (T1F6 : L5.u8_at RSEGS M6 (F + 32) fT).
      { eapply L5C.u8_at_agree. 4: exact T1F5. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply PRES6. clear - Hi FR; lia. apply FCL6. clear - Hi; lia. clear - Hi; lia. }
      assert (Z6 : L5KA.zeros_at M6 (F + 40) 16). { intros i Hi. destruct (ZB i Hi) as (v & Ev & Bv). subst v. exact Bv. }
      assert (T1C7 : L5.u64_at RSEGS M7 (F + 56) 0).
      { apply (proj1 (u64_at_vis H6 M7 (F + 56) 0 ltac:(eapply avis_sub; [exact FV6 | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). unfold H6. rewrite VIS7. exact yC56. }
      assert (T1BIG7 : L5.big_at RSEGS M7 (F + 32) (L5.BO fT 0 (L5.BInl 0 0))).
      { unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. change (Z.of_nat 0) with 0.
        split. { eapply L5C.u8_at_agree. 4: exact T1F6. 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply AG7. clear - Hi FR; lia. clear - Hi; lia. }
        split. clear - FTR1; lia.
        split. { replace (F + 32 + 8) with (F + 40) by (clear; lia). eapply L5C.u64_at_agree. 2: clear - FR; lia. 2: clear - FR; lia.
                 2:{ apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z6. clear; lia. clear; lia. clear - FR; lia. clear - FR; lia. }
                 intros i Hi. apply AG7. clear - Hi FR; lia. clear - Hi; lia. }
        split. exact FT0.
        split. { replace (F + 32 + 16) with (F + 48) by (clear; lia). eapply L5C.u64_at_agree. 2: clear - FR; lia. 2: clear - FR; lia.
                 2:{ apply u64_of_zeros_at. eapply L5KA.zeros_at_sub. exact Z6. clear; lia. clear; lia. clear - FR; lia. clear - FR; lia. }
                 intros i Hi. apply AG7. clear - Hi FR; lia. clear - Hi; lia. }
        split. { replace (F + 32 + 24) with (F + 56) by (clear; lia). exact T1C7. }
        split. clear; lia. split; clear; lia. }
      assert (T1Z6 : shadow_zero M6 (F + 32) 4).
      { intros j Hj. unfold byte_at. rewrite PRES6. apply T1Z5. exact Hj. unfold S, SB. rewrite (proj1 FSH4). clear - Hj FR; lia.
        apply (fframe_shadow_client L ar LB _ _ _ F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. unfold in_shadow_of, S. rewrite (proj1 FSH4), (proj1 FQ31). clear - Hj; lia.
        unfold S. rewrite (proj1 FSH4). clear - Hj FR FBIG; unfold SB; lia. }
      assert (T1Z7 : shadow_zero M7 (F + 32) 4).
      { intros j Hj. unfold byte_at. rewrite AG7. apply T1Z6. exact Hj. unfold S, SB. rewrite (proj1 FSH4). clear - Hj FR; lia.
        unfold S, SB. rewrite (proj1 FSH4). clear - Hj FR FBIG; lia. }
      assert (AOT1 : aobj FF' (F + 32) 32).
      { exists (F, 2, sb - 192 + 32). split. left; reflexivity. cbn [ff_addr ff_class fst snd]. change (ff_bytes 2) with 256. split. clear; lia. split. clear; lia. exact (proj1 (proj2 FSH4)). }
      pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as WF2.
      assert (ND2 : NoDup (map ff_addr (FF' ++ LK2))). { clear - WF2. decompose [and] WF2. assumption. }
      (* [comment removed for export] *)
      apply (Hasg fx7 R7 M7 model7 K LB FF' LK2 cr A o (F + 32) (sb - 192) 585552 (L5.BO fb 0 (L5.BInl 0 0)) (L5.BO fT 0 (L5.BInl 0 0)) [] HH7 AM7 HK).
      - rewrite r10. exact yR10.
      - rewrite r11. exact yR11.
      - cbn [L5.bo_len]. clear; lia.
      - intros X. exfalso. unfold L5.bo_dyn in X; cbn [L5.bo_fb] in X. destruct BIG as (_ & _ & _ & BT & _). cbn [L5.bo_st L5.bo_fb] in BT. rewrite BT in X. discriminate X.
      - cbn [L5.bo_len]. intros X. exfalso. clear - X. lia.
      - rewrite r1. exact yR1.
      - split. clear; lia. reflexivity.
      - rewrite r2. rk.
      - clear - SA32. unfold aligned in SA32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). rewrite r4. rk.
      - replace (sb - 192) with (sp - 208) by (subst sb; clear; lia). apply (astk_sub ar M7 M7 sp L5PSB.DETAIL_SCRB 208 ASSIGN_SCR ASTK7 (mem_grows_refl M7)). clear; lia. rewrite ASG_EQ; clear; lia.
        rewrite ASG_EQ, DSCR_EQ; clear; lia. replace (sp - 208) with (sb - 192) by (subst sb; clear; lia). exact SA16.
      - apply (ffr_push FF LK LK2 (F, 2, sb - 192 + 32) 5 4 FFR LKI2 ND2). clear; lia. clear; lia.
      - apply (ffrs_push FF sp). exact FFRS. clear; lia. subst sb; clear; lia.
      - exact BIG7.
      - apply aobj_cons. exact AOB.
      - exact SZ7.
      - exact T1BIG7.
      - unfold L5C.obj_limbs; cbn. repeat split. constructor.
      - exact AOT1.
      - exact T1Z7.
      - intros cap q X. discriminate X.
      - intros cap q X. discriminate X.
      - clear - OF. lia.
      - intros c q c' q' X. discriminate X.
      - intros fx8 R8 M8 model8 g LB8 cr8 LK8 A8 POST RT8 IA8 AM8 LKI8 HH8.
        destruct POST as (RP8 & R8_10 & G). cbn [L5.bo_len L5.bo_fb L5.bo_st] in G.
        destruct g as [|q8 cap8]. 2:{ exfalso. destruct G as (_ & X & _). clear - X; lia. }
        destruct G as (_ & -> & -> & (st8 & OB8 & OL8 & ST8) & AH8). unfold assign_fb in OB8, OL8. cbn [Nat.eqb] in OB8, OL8.
        assert (OWN8 : own sb F R (if neg then 1 else 0) M8).
        { apply (own_callee sb F (sb - 192 + 32) R _ (proj2 SPR) SBC FRR LB FF' (sb - 192) ASSIGN_SCR _ M7 M8 OWN7 AH8). left; reflexivity. clear; lia.
          intros rr [<-|[<-|[]]]; cbn [fst snd L5.bo_data L5.bo_st]; clear - OR; lia. }
        assert (ASTK8 : astk ar M8 sp L5PSB.DETAIL_SCRB).
        { apply (astk_after L ar C HI HIok LB FF' LK2 cr A M7 M7 M8 _ sp _ (sb - 192) ASSIGN_SCR _ HH7 ASTK7 (mem_grows_refl M7) AH8).
          rewrite ASG_EQ, DSCR_EQ; subst sb; clear; lia. subst sb; clear; lia. rewrite DSCR_EQ; clear; lia. }
        pose proof (vis_pack L ar C HI LY HIok LB FF' LK8 cr A8 M8 model8 HH8) as (_ & VIS8 & _ & VFS8 & _ & _ & VFSSH8 & _).
        pose proof (statics_vis LB FF' LK8 cr A8 M8 model8 HH8) as (IMGC8 & CSB8 & CUAR8).
        set (H8 := ahid A8 model8) in *. set (MV8 := mrestrict H8 M8) in *.
        assert (SV8 : avis H8 (sb - 192) 208). { apply (VIS8 (sb - 192) 208). subst sb; clear - SLO; lia. clear - SPR; lia. }
        assert (FV8 : avis H8 F 256) by (apply (VFS8 F 256 FS1 FS2)).
        assert (SHV8 : avis H8 (F / 8 + SB) 32).
        { apply (VFSSH8 (F / 8 + SB) 32). intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        assert (W176h : L5.writable RSEGS MV8 (sb - 192) 208).
        { apply (proj2 (writable_vis H8 M8 (sb - 192) 208 SV8 ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
          eapply (astk_writable ar M8 sp). exact ASTK8. rewrite DSCR_EQ. subst sb; clear; lia. subst sb; clear; lia. clear; lia. }
        assert (OWN8v : own sb F R (if neg then 1 else 0) MV8) by (apply (own_vis sb F R _ (proj2 SPR) H8 M8 OWN8 SV8 SHV8)).
        destruct OWN8v as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13) & (S112 & S144 & S152 & S168) & FSD8).
        pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH8) as (_ & WF8 & _).
        assert (FDEF8 : L5.defined MV8 F 256). { apply (proj2 (defined_vis H8 M8 F 256 FV8)). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF8 _ (or_introl eq_refl))))))). }
        assert (FW8 : L5.writable RSEGS MV8 F 256). { apply (L5C.writable_of_defined RSEGS). exact FDEF8. clear - FR; lia. clear - FR; lia. }
        assert (FSHW8 : L5.writable RSEGS MV8 (F / 8 + SB) 32). { apply (L5C.writable_of_defined RSEGS). exact FSD8. clear - FR F8; unfold SB; lia. clear - FR F8; unfold SB; lia. }
        pose proof (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model8 F 2 _ _ fl HH2 HH8 (or_introl eq_refl) (or_introl eq_refl) (or_intror (or_introl eq_refl)) FLC) as [FLC8 FL8].
        change (ff_bytes 2) with 256 in FLC8, FL8. replace (F + 256 - 8) with (F + 248) in FL8 by (clear; lia).
        pose proof (fl_writable L ar C HI LY HIok _ FF' LK8 _ A8 M8 _ fl HH8 FLP) as [FLD8 FLW8].
        pose proof (fl_vis L ar C HI LY HIok _ FF' LK8 _ A8 M8 model8 fl HH8 FLP) as FLV8.
        assert (FLW8v : L5.writable RSEGS MV8 fl 1). { apply (proj2 (writable_vis H8 M8 fl 1 FLV8 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW8. }
        assert (CEL8 : L5.u64_at RSEGS M8 (sb - 136) (p + n) /\ L5.u64_at RSEGS M8 (sb - 160) o).
        { apply (CELX M7 M8). 2: exact CEL7. intros a Ha. apply (stack_callee LB FF' (sb - 192) ASSIGN_SCR _ M7 M8 a AH8).
          intros rr [<-|[<-|[]]]; cbn [fst snd L5.bo_data L5.bo_st]; clear - OR; lia. clear - Ha SPR; lia. subst sb; clear - Ha SLO SHI SPT; lia. clear - Ha; lia. }
        assert (END8v : L5.u64_at RSEGS MV8 (sb - 136) (p + n)).
        { apply (proj2 (u64_at_vis H8 M8 (sb - 136) (p + n) ltac:(eapply avis_sub; [exact SV8 | clear; lia | clear; lia]) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))). exact (proj1 CEL8). }
        assert (T1F8v : L5.u8_at RSEGS MV8 (F + 32) fT).
        { apply (proj2 (u8_at_vis H8 M8 (F + 32) fT ltac:(eapply avis_sub; [exact FV8 | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))).
          eapply L5C.u8_at_agree. 4: exact (proj1 T1BIG7). 2: clear - FR; lia. 2: clear - FR; lia. intros i Hi. apply (proj1 AH8). split. clear - Hi FR; lia. split.
          apply (fframe_client L ar LB _ _ _ F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Hi; lia.
          intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd L5.bo_data L5.bo_st]; clear - Hi OF; lia. }
        (* [comment removed for export] *)
        pose proof (dtAZ3_conc fx8 R8 MV8 (fun j => match j with 2%nat => sb | 35%nat => (if neg then 1 else 0) | 40%nat => F | 41%nat => fl
                      | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 18 | 46%nat => U R 19 | 47%nat => U R 20 | 48%nat => U R 21
                      | 49%nat => U R 22 | 50%nat => U R 23 | 51%nat => U R 24 | 52%nat => U R 25 | 53%nat => U R 26 | 54%nat => U R 27 | 57%nat => p + n | 58%nat => U R8 1 | 60%nat => fT | _ => 0 end)) as P.
        cbn beta iota in P.
        feed P ltac:(first [apply UR | apply U_to | sc ]).
        destruct P as (fx9 & R9 & M9v & MG9 & wFR & wFZ & (wMS & wKS & wR1 & wR2 & wR8 & wR9 & wR10 & wR11 & wR18 & wR19 & wR20 & wR21 & wR22 & wR23 & wR24 & wR25 & wR26 & wR27 & wFL0 & WSH)).
        assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
        pose proof (ret_to fx9 R9 M9v 0x8f210 W_8f210 r F_8f210 eq_refl D_8f210 ltac:(rewrite wR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
        pose proof (msteps_trans _ _ _ _ wMS RET) as MS10. clear wMS RET.
        set (W9 := fun a => (F <= a < F + 8 \/ F / 8 + SB <= a < F / 8 + SB + 32) \/ a = fl).
        assert (FLNC8 : ~ aclient L ar LB FF' 0 0 fl) by exact FLNC.
        apply (apiece_retire L ar C HI LY HIok LB FF LK8 cr A8 M8 model8 fx8 fx9 R8 0x8ef50 R9 r M9v W9 F 2 (sb - 192 + 32) fl K HH8 AM8).
        { exact FLC8. }
        { exact FLNC8. }
        { exact FLV8. }
        { clear - FLR; lia. }
        { exact MS10. }
        { exact MG9. }
        { intros a Ha Hna. apply wFZ. exact Ha. all: clear - Hna; subst W9; cbn beta in Hna; unfold SB in *; lia. }
        { intros a Ha Wa. subst W9; cbn beta in Wa. destruct Wa as [[Wa|Wa]|Wa].
          - right. apply (fframe_client L ar LB _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256. clear - Wa; lia.
          - right. apply (fframe_shadow_client L ar LB _ 0 0 F 2 (sb - 192 + 32)). left; reflexivity. change (ff_bytes 2) with 256.
            unfold in_shadow_of, S. clear - Wa F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
          - left; exact Wa. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        { intros a. subst W9; cbn beta. repeat match goal with X : _ |- _ => clear X end.
          destruct (rng_dec a F (F + 8)); [left; tauto|]. destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + 32)); [left; tauto|]. destruct (Z.eq_dec a fl); [left; tauto|]. right; tauto. }
        { exact wFL0. }
        intros M9 model9 HH9 AM9 RT9 AH9 VIS9 MGM9 FRM9 EQ9.
        assert (ASTK9 : astk ar M9 sp L5PSB.DETAIL_SCRB). { eapply astk_grows. exact ASTK8. exact MGM9. }
        assert (ALLZ : Forall (fun c => c = 48) (c0 :: t)).
        { apply Forall_forall. intros x Hx. destruct (In_nth _ x 0 Hx) as (i & Hi & <-). apply ZZ. rewrite ZALL. exact Hi. }
        assert (DEC0 : dec (c0 :: t) = 0). { unfold dec. rewrite (dec_acc_zeros 0 _ ALLZ). clear; lia. }
        assert (OK9 : forall a, o <= a < o + 32 -> M9 (Z_to_bv 64 a) = M8 (Z_to_bv 64 a)).
        { intros a Ha. apply FRM9. clear - Ha OR; lia. subst W9; cbn beta. clear - Ha OF OFSH OFL. unfold SB in *. lia. }
        apply (KONT fx9 R9 M9 model9 LB cr LK8 A8).
        -- split.
          { apply preserved_by_index. intros k Hk. cbn in Hk.
            destruct Hk as [<-|Hk]. { rewrite wR2. rewrite <- r2, G2. f_equal. subst sb; clear; lia. }
            destruct Hk as [<-|Hk]. { rk. }
            destruct Hk as [<-|Hk]. { rk. }
            repeat (destruct Hk as [<-|Hk]; [first [rewrite wR8 | rewrite wR9 | rewrite wR18 | rewrite wR19 | rewrite wR20 | rewrite wR21 | rewrite wR22 | rewrite wR23
                                                   | rewrite wR24 | rewrite wR25 | rewrite wR26 | rewrite wR27]; symmetry; apply U_to |]). destruct Hk. }
          left. split. cbn [length]; clear; lia. split. { eapply Forall_impl. 2: exact ALLZ. cbn beta. intros a ->. clear; lia. }
          split. rewrite r11. exact wR11.
          unfold parse_post. rewrite DEC0. cbv zeta. rewrite nwords_0. change (wlist 0 0) with (@nil Z).
          assert (RFB : res_fb fb 0 neg = fb). { unfold res_fb. cbn [Nat.leb]. rewrite Bool.andb_false_r. clear; lia. } rewrite RFB.
          exists st8. split. { eapply L5C.big_at_agree. 4: exact OB8. 2: clear - OR; lia. 2: clear - OR; lia. intros i Hi. apply OK9. exact Hi. }
          split. { destruct OL8 as (L1 & L2 & L3). split. exact L1. split. exact L2. cbn [L5.bo_st] in L3 |- *. destruct st8 as [u0 u1|c8 q8]. exact L3. exfalso. exact ST8. }
          split. { destruct st8 as [u0 u1|c8 q8]. split. clear; lia. reflexivity. exfalso. exact ST8. }
          split. { unfold parse_debit. eapply credit_le_trans. apply adebit_le. exact LY2. apply vblk_pos. apply adebit_le. exact LY2. apply vblk_pos. }
          apply ahpres_of.
          + eapply ek_trans. { apply (ek_W L ar LB FF sp L5PSB.DETAIL_SCRB [(o, 32)] [] M M7 EK7). intros a _ rr []. }
            eapply ek_trans. { apply (ek_callee L ar LB [] FF [(F, 2, sb - 192 + 32)] sp L5PSB.DETAIL_SCRB (sb - 192) ASSIGN_SCR [(o, 32)] _ M7 M8 AH8).
              rewrite ASG_EQ, DSCR_EQ; subst sb; clear; lia. subst sb; clear; lia.
              intros a _ Ho rr [<-|[<-|[]]]. apply Ho. left; reflexivity. unfold L5.in_rng; cbn [fst snd L5.bo_data L5.bo_st]. clear; lia. }
            intros a (Ha & Hc & Ho). apply FRM9. exact Ha. subst W9; cbn beta. intros [[X|X]|X].
            * apply (NCF a). left; clear - X; lia. exact Hc.
            * apply (NCF a). right. unfold S. rewrite (proj1 FQ31). clear - X. unfold SB in X |- *. lia. exact Hc.
            * subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc.
          + eapply astk_defined. exact ASTK9. clear; lia. clear; lia.
          + eapply dk_trans. exact DK7. eapply dk_trans. apply (dk_callee L ar LB [] FF [(F, 2, sb - 192 + 32)] sp L5PSB.DETAIL_SCRB (sb - 192) ASSIGN_SCR _ M7 M8 AH8).
            rewrite ASG_EQ, DSCR_EQ; subst sb; clear; lia. subst sb; clear; lia. apply dk_grows. exact MGM9.
        -- eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3. eapply L5LZ.model_rt_trans. exact RT4.
          eapply L5LZ.model_rt_trans. exact RT5. eapply L5LZ.model_rt_trans. exact RT6. eapply L5LZ.model_rt_trans. exact RT7. eapply L5LZ.model_rt_trans. exact RT8. exact RT9.
        -- exact IA8.
        -- exact AM9.
        -- intros x Hx. apply LKI2. apply LKI8. exact Hx.
        -- exact HH9. }

    (* [comment removed for export] *)
    assert (ZLT : (z < length (c0 :: t))%nat) by (clear - ZL ZNOT; lia).
    assert (CTXm : mctx L ar IL HI R M model K LB FF LK cr A p o sp r fb neg (c0 :: t) F fl LK2 M2 model2).
    { refine (MCTX L ar IL HI R M model K LB FF LK cr A p o sp r fb neg (c0 :: t) F fl LK2 M2 model2 HK RA _ _ _ LEN HVN CR SLO SHI SPT SA32 SA16 SPR FFR FFRS HH BIG FB3 AOB SZ BYTES BR SRC APART
                PRG OR OBIG FS1 FS2 FAPP FCEIL FAPART FBLK LKI2 FLP FLNC FLA HH2 FLC FR F32 F8 FBIG FLR FLBIG SF SFSH SFL OF OFSH OFL FQ31 NCF NCS SSH KONT).
      - apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia.
      - rewrite <- r2. exact G2.
      - rewrite <- r4. exact G4. }
    assert (BI4 : L5ADH.binv L ar HI R M model LB FF LK A sp neg F [] [] M3 model4 LK2 cr A).
    { unfold L5ADH.binv. split. exact HH4. split. exact AM4.
      split. { eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3. exact RT4. }
      split. apply incl_refl. split. exact LKI2. split. exact ASTK3. split. exact EK3. split. exact DK3. exact OWN3. }
    assert (RI4 : L5ADH.rinv R sp F R4).
    { unfold L5ADH.rinv. split. rk. split. rk. split. rk. split. rk. split. rk. split. rk. rk. }
    destruct (defined_byte_d M3 (F + 96)) as (jv & JVR & JVB).
    { eapply L5.defined_grows. exact MGM3. intros j Hj. replace (F + 96 + j) with (F + (96 + j)) by (clear; lia). apply FDEF. clear - Hj; lia. }
    clear - FR; lia. clear - FR; lia.
    apply (L5ADM.main_path L ar C IL HI LY ILY HIok ICok Hasg Hres Hmul Hadd Hdel R M model K LB FF LK cr A p o sp r fb neg (c0 :: t) F fl LK2 M2 model2 CTXm jv JVR fx4 R4 M3 model4 LK2 A z ZLT (ZN ZLT) BI4 RI4).
    + exact zR11.
    + rk.
    + rk.
    + rk.
    + exact (proj1 CEL3).
    + exact (proj2 CEL3).
    + exact JVB.
Qed.
End WithIface.
End SCFG_1.
End L5ADET.
