(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue BigModel BigFactsRun BigFactsDigits L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ParseSpecsA L5ADetailK L5ADetailH L5ACstr L5AStrctorP As0_code_8e368_8f368
     AsanPlanCore AsanPlanSound As0PlanKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ASC.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5PSA. Import L5ASCP. Import L5ADK. Import L5ADH.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac blia := keep_arith; first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia
                                     | match goal with H : _ \/ _ |- _ => clear_disj_but H; destruct H; lia end ].
Local Ltac asm := match goal with H : ?T |- ?G => constr_eq T G; exact H end.
Local Ltac sc := first [ asm | rk | gmem | (arith_goal; first [asm | blia]) | assumption ].
Lemma TSCR_EQ : TOBIG_SCR = 4848. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STRCTOR : Z := 0x8e71c.
Definition STRCTOR_THROW : Z := 0x8e810.        (* [comment removed for export] *)
Definition STRCTOR_N_SCR : Z := 32 + Z.max TOBIG_SCR 2560.      (* [comment removed for export] *)

Definition strctor_post (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF LKq : list fframe) (cr : credit) (M M' : word -> option byte)
           (R R' : bvmap 5 word) (o sp fbo : Z) (s : list Z) (SCR : Z) (LB' : list (Z * Z)) (cr' : credit) : Prop :=
  let neg := fst (split_sign s) in let ds := snd (split_sign s) in
  regs_preserved R R' /\ parses s /\ parse_post L ar LB FF LKq cr M M' o sp (Z.land fbo 252) neg ds SCR LB' cr'.

(* [comment removed for export] *)
Definition strctor_throw_state (L : asan_layout) (ar : asan_run) (LB : list (Z * Z)) (FF : list fframe) (cr : credit) (M M' : word -> option byte)
           (R R' : bvmap 5 word) (o sp fbo : Z) (s : list Z) (SCR : Z) (cr' : credit) : Prop :=
  no_parse s /\
  getr R' (reg 2) = Z_to_bv 64 (sp - 32) /\ getr R' (reg 8) = Z_to_bv 64 o /\ getr R' (reg 9) = Z_to_bv 64 22 /\
  getr R' (reg 18) = Z_to_bv 64 SB /\                       (* [comment removed for export] *)
  (forall i, In i [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg i) = getr R (reg i)) /\
  L5.u64_at RSEGS M' (sp - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M' (sp - 16) (bv_unsigned (getr R (reg 8))) /\
  L5.u64_at RSEGS M' (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M' (sp - 32) (bv_unsigned (getr R (reg 18))) /\
  L5.big_at RSEGS M' o (L5.BO (Z.land fbo 252) 0 (L5.BInl 0 0)) /\ shadow_zero M' o 4 /\
  credit_le (parse_debit L cr (length (snd (split_sign s)))) cr' /\
  astk ar M' sp SCR /\
  ahpres L ar LB FF sp SCR [(o, 32)] M M'.

Definition strctor_norm_spec (L : asan_layout) (ar : asan_run) (IL : icpt_layout) (HI : asan_iface) (SCR : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (o so sp r fbo : Z) (s : list Z),
    ri_inv HI LB FF LK cr A M (vml_of model) -> amodel_ok A model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 so ->
    (length s <= 4999)%nat -> Forall (fun c => 0 <= c < 256) s ->
    parse_credit L cr (length (snd (split_sign s))) ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> sp mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M sp SCR ->
    ffr FF LK 5 -> ffrk 2 FF LK 2 -> ffrs FF sp ->
    (* [comment removed for export] *)
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 -> aobj FF o 32 -> shadow_zero M o 4 ->
    (* [comment removed for export] *)
    aobj FF so 24 -> shadow_zero M so 3 -> (o + 32 <= so \/ so + 24 <= o) ->
    ( L5.lstr_short RSEGS M so s
      \/ (exists w0 pd, L5.lstr_long RSEGS M so s w0 pd /\ In (pd, w0 - 1) LB /\ Z.of_nat (length s) + 1 <= w0 - 1 /\ 0 <= w0 < 2 ^ 64) ) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr' (LK' : list fframe) (A' : list (Z * Z)),
        strctor_post L ar LB FF LK' cr M M' R R' o sp fbo s SCR LB' cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB' FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    (* [comment removed for export] *)
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) cr' (LK' : list fframe) (A' : list (Z * Z)),
        strctor_throw_state L ar LB FF cr M M' R R' o sp fbo s SCR cr' ->
        model_rt model model' -> incl A A' -> amodel_ok A' model' -> incl LK' LK ->
        ri_inv HI LB FF LK' cr' A' M' (vml_of model') ->
        srealizes RSEGS SCFG (cfg R' STRCTOR_THROW M' model') K) ->
    srealizes RSEGS SCFG (cfg R STRCTOR M model) K.

(* [comment removed for export] *)
Lemma rdn_head M a (k : nat) b rest : rdn RSEGS M a (Datatypes.S k) = Some (b :: rest) -> rdn RSEGS M a 1 = Some [b].
Proof.
  cbn [rdn]. destruct (match M a with Some b0 => Some b0 | None => seg_rom RSEGS a end) as [b0|]; [|discriminate].
  destruct (rdn RSEGS M (a + 1)%bv k) as [r0|]; [|discriminate]. intros E. injection E as -> _. reflexivity.
Qed.
Lemma u8_of_u64_lo M a v : L5.u64_at RSEGS M a v -> L5.u8_at RSEGS M a (v mod 256).
Proof.
  unfold L5.u64_at, L5.u8_at. intros HU. unfold word_to_le_bytes in HU. change 8%nat with (Datatypes.S 7) in HU. cbn [Z_to_le_bytes] in HU.
  rewrite (rdn_head M (Z_to_bv 64 a) 7 _ _ HU). f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. change (2 ^ 64) with (256 * 72057594037927936).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. rewrite Z.mod_mod by lia. reflexivity.
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

Theorem strctor_norm_ok SCR : 4880 <= SCR -> tobig3_spec L ar IL HI -> strctor_norm_spec L ar IL HI SCR.
Proof.
  intros HSCR TB3 fx R M model K LB FF LK cr A o so sp r fbo s HH AM HK G10 G11 LEN BR CR G1 RA G2 A32 G4 STK FFR FFR2 FFRS UFB FBO AOB SZ AOS SZS APOS STR KONT KTHROW.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487200 <= sp <= 140737488355328) by (clear - SLO SHI SPT HSCR; lia).
  pose proof (L5ACST.land252_facts fbo FBO) as (FB1 & FB3 & FBT).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp SCR HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model so 24 sp SCR HH AOS ltac:(clear; lia) ltac:(reflexivity))
    as (SOR & SOBIG & SODEF & SOVIS & SOVSH & SOCL & SOCLSH). change (24 / 8) with 3 in SOVSH, SOCLSH.
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (W32 : L5.writable RSEGS MV (sp - 32) 32).
  { apply (proj2 (writable_vis H M (sp - 32) 32 (VIS (sp - 32) 32 ltac:(clear - SLO HSCR; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. clear - HSCR; lia. clear; lia. clear; lia. }
  assert (ALS : aligned sp 16) by exact A16.
  assert (ALO : aligned o 8) by (unfold aligned; clear - OR; lia).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  assert (OR0 : 0 <= o < 2 ^ 64 /\ 4096 <= o <= 140737488355296) by (clear - OR; lia). destruct OR0 as [OR0 OR1].
  assert (SOR0 : 0 <= so < 2 ^ 64 /\ 4096 <= so <= 140737488355304) by (clear - SOR; lia). destruct SOR0 as [SOR0 SOR1].
  assert (OZv : L5KA.zeros_at MV (o / 8 + 2147450880) 4). { apply (proj2 (zeros_at_vis H M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OWv : L5.writable RSEGS MV o 32). { apply (proj2 (writable_vis H M o 32 OVIS ltac:(clear - OR; lia) ltac:(clear - OR; lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. clear - OR; lia. clear - OR; lia. }
  assert (OFRM : sp - 32 + 32 <= o \/ o + 32 <= sp - 32) by (clear - OR SLO HSCR; lia).
  assert (UFBv : L5.u8_at RSEGS MV o fbo). { apply (proj2 (u8_at_vis H M o fbo ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact UFB. }
  assert (FBO' : 0 <= fbo <= 255 /\ 0 <= fbo < 2 ^ 64) by (clear - FBO; lia). destruct FBO' as [FBO' FBO''].
  (* [comment removed for export] *)
  pose proof (scA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => so | 36%nat => fbo | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r2; exact G2) | (rewrite <- r10; exact G10) | (rewrite <- r11; exact G11)]).
  destruct P as (fx1 & R1 & M1v & MG1 & aFR & aFZ & (aMS & aKS & aR1 & aR2 & aR8 & aR9 & aR10 & aR11 & aR12 & aR18 & aU8 & aC32 & aC24 & aC16 & aC8)).
  set (W1 := fun a => sp - 32 <= a < sp \/ o <= a < o + 1).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R STRCTOR R1 0x5e570 M1v W1 K HH AM aMS MG1).
  { intros a Ha Hna. apply aFZ. exact Ha. all: clear - Hna; subst W1; cbn beta in Hna; lia. }
  { intros a Ha Wa. subst W1; cbn beta in Wa. destruct Wa as [Wa|Wa].
    - split. apply stack_client. clear - Wa SLO SHI SPT HSCR; lia. clear; lia. clear - Wa SLO SPT HSCR; lia.
    - split. apply (obj_client L ar LB FF 0 0 o 32 a AOB). clear - Wa; lia. clear - Wa OR; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (ASTK1 : astk ar M1 sp SCR) by (eapply astk_grows; [exact STK | exact MGM1]).
  assert (NCS : forall a, sp - 32 <= a < sp -> ~ aclient L ar LB FF sp SCR a).
  { intros a X Hc. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp SCR a HH SPT Hc) as [Y|Y]. clear - X Y HSCR; lia. clear - X Y SLO HSCR; lia. }
  assert (EK1 : ek L ar LB FF sp SCR [(o, 32)] M M1).
  { apply (ek_piece L ar LB FF sp SCR [(o, 32)] M M1 W1 FRM1). intros a Ha Hc Ho X. subst W1; cbn beta in X. destruct X as [X|X]. exact (NCS a X Hc).
    apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia. }
  assert (DK1 : dk L ar LB FF sp SCR M M1) by (apply dk_grows; exact MGM1).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHO : forall j, 0 <= j < 4 -> 2147450880 <= o / 8 + 2147450880 + j < 17594333528064 /\ ~ (o <= o / 8 + 2147450880 + j < o + 32)) by (intros j Hj; clear - Hj OR OBIG; lia).
  assert (SA32 : (sp - 32) mod 16 = 0 /\ (sp - 32) mod 32 = 0) by (clear - A32; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SZ1 : shadow_zero M1 o 4).
  { intros j Hj. unfold byte_at. rewrite FRM1. apply SZ. exact Hj. unfold S, SB. destruct (SHO j Hj) as [X _]. clear - X; lia.
    subst W1; cbn beta. unfold S, SB. destruct (SHO j Hj) as [X X']. clear - X X' SPR. lia. }
  assert (UFB1 : L5.u8_at RSEGS M1 o (Z.land fbo 252)).
  { apply (proj1 (u8_at_vis (ahid A model) M1 o _ ltac:(eapply avis_sub; [exact OVIS | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))).
    rewrite VIS1. rewrite L5ACST.land252_div4 by exact FBO. exact aU8. }
  (* [comment removed for export] *)
  pose proof (aio_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (aly_segs L C LY), (aly_memset L C LY), (aly_scr_mem L C LY) in MS.
  assert (U21 : bv_unsigned (getr R1 2%bv) = sp - 32). { rewrite r2, aR2. apply L5.unsigned_lit. clear - SPR; lia. }
  eapply (MS fx1 R1 M1 model1 LB FF LK cr A (o + 8) 0 24 K); clear MS.
  { split. exact HH1. split. exact (proj1 AM1). split. exact (proj2 AM1).
    split. rewrite r10. exact aR10. split. rewrite r12. exact aR12. split. clear; lia.
    split. rewrite r4, (aKS 4%nat) by inl. rewrite <- r4. exact G4.
    split. rewrite r1, aR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
    split. { rewrite U21. apply (astack_ok_of_astk L ar C LY M M1 sp SCR 32 2560 STK MGM1). clear; lia. clear; lia. clear - HSCR; lia. exact (proj1 SA32). }
    split. { eapply aacc_of_zero. exact SZ1. clear - OR; lia. clear - OR; lia. clear; lia. clear; lia. }
    split. { intros i Hi. rewrite U21. apply (obj_client L ar LB FF _ _ o 32 (o + 8 + i) AOB). clear - Hi; lia. }
    split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M1 (o + 8) 24). 2: clear - OR; lia. 2: clear - OR; lia. 2: exact Hi. 2: exact Hm.
             eapply L5.defined_grows. exact MGM1. intros j Hj. replace (o + 8 + j) with (o + (8 + j)) by (clear; lia). apply ODEF. clear - Hj; lia. }
    split. exact HK. apply (app_rng_aobj L ar C HI HIok LB FF LK cr A M1 _ o 32 (o + 8) 24 HH1 AOB); clear; lia. }
  { rewrite r11. exact aR11. }
  intros R6 M6 model6 mR10 RP6 ZB PRES6 SDEF6 RT6 MI6 HH6. rewrite U21 in PRES6, SDEF6. rewrite r1, aR1.
  assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 AM1). }
  assert (ASTK6 : astk ar M6 sp SCR).
  { apply (astk_after_eq L ar C HI HIok LB FF LK cr A M1 M1 M6 _ sp _ (sp - 32) 2560 HH1 ASTK1 (mem_grows_refl M1)).
    intros a Ha Hs Hns. apply PRES6. exact Ha. apply stack_client. exact Hs. exact Hns. clear - Hs OR; lia. exact SDEF6.
    clear - HSCR; lia. clear; lia. clear - HSCR; lia. }
  assert (EK6 : ek L ar LB FF sp SCR [(o, 32)] M M6).
  { eapply ek_trans. exact EK1. apply (ek_mem L ar LB FF sp SCR (sp - 32) 2560 (fun a => o + 8 <= a < o + 8 + 24) [(o, 32)] M1 M6 PRES6).
    - clear - HSCR; lia.
    - clear; lia.
    - intros a _ Ho X. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia. }
  assert (DK6 : dk L ar LB FF sp SCR M M6).
  { eapply dk_trans. exact DK1. apply (dk_mem L ar LB FF sp SCR (sp - 32) 2560 (fun a => o + 8 <= a < o + 8 + 24) M1 M6 PRES6 SDEF6).
    - intros a Da. destruct (ZB (a - (o + 8)) ltac:(clear - Da; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (o + 8 + (a - (o + 8))) with a in Bv by (clear; lia). rewrite Bv. discriminate.
    - intros a. destruct (rng_dec a (o + 8) (o + 8 + 24)); [left|right]; assumption.
    - clear - HSCR; lia.
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
    replace (S o + j) with (o / 8 + SB + j) by reflexivity. apply (aclient_narrow L ar LB FF sp SCR). apply OCLSH. exact Hj.
    unfold SB. destruct (SHO j Hj) as [X _]. clear - X SPR. lia.
    unfold S, SB. destruct (SHO j Hj) as [X X']. clear - X X'. lia. }
  (* [comment removed for export] *)
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WFB & WFF & _).
  assert (OFS : ar_fs ar <= o /\ o + 32 <= ar_fs ar + FS_BYTES).
  { destruct AOB as (f & Hf & F1 & F2 & _). destruct (WFF f Hf) as (X1 & X2 & _). clear - F1 F2 X1 X2. lia. }
  assert (KEEP6 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp SCR a -> ~ (o <= a < o + 32) -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc Ho. apply EK6. split. exact Ha. split. exact Hc. intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. exact Ho. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (SHS : forall j, 0 <= j < 3 -> 2147450880 <= so / 8 + 2147450880 + j < 17594333495296) by (intros j Hj; clear - Hj SOR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SOK6 : L5C.agree_on M M6 so 24).
  { intros i Hi. apply KEEP6. clear - Hi SOR; lia. replace i with (so + (i - so)) by (clear; lia). apply SOCL. clear - Hi; lia. clear - Hi APOS; lia. }
  assert (SZS6 : shadow_zero M6 so 3).
  { intros j Hj. unfold byte_at. rewrite KEEP6. apply SZS. exact Hj. unfold S, SB. pose proof (SHS j Hj) as X. clear - X; lia.
    replace (S so + j) with (so / 8 + SB + j) by reflexivity. apply SOCLSH. exact Hj.
    unfold S, SB. pose proof (SHS j Hj) as X. clear - X OBIG. lia. }
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M6 model6 so 24 sp SCR HH6 AOS ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & SOVIS6 & SOVSH6 & _). change (24 / 8) with 3 in SOVSH6.
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M6 model6 HH6) as (_ & VIS6 & _).
  pose proof (statics_vis LB FF LK cr A M6 model6 HH6) as (IMGC6 & CSB6 & CUAR6).
  set (H6 := ahid A model6) in *. set (MV6 := mrestrict H6 M6) in *.
  assert (W32f : L5.writable RSEGS MV6 (sp - 32) 32).
  { apply (proj2 (writable_vis H6 M6 (sp - 32) 32 (VIS6 (sp - 32) 32 ltac:(clear - SLO HSCR; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M6 sp). exact ASTK6. clear - HSCR; lia. clear; lia. clear; lia. }
  assert (SZSv : L5KA.zeros_at MV6 (so / 8 + 2147450880) 3). { apply (proj2 (zeros_at_vis H6 M6 _ 3 SOVSH6)). intros i Hi. unfold shadow_zero, byte_at, S in SZS6. apply SZS6. exact Hi. }
  assert (ALSO : aligned so 8) by (unfold aligned; clear - SOR; lia).
  assert (SFRM : sp - 32 + 32 <= so \/ so + 24 <= sp - 32) by (clear - SOR SLO HSCR; lia).
  assert (CELL8 : forall a v, so <= a -> a + 8 <= so + 24 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV6 a v).
  { intros a v Ha1 Ha2 Hc. apply (proj2 (u64_at_vis H6 M6 a v ltac:(eapply avis_sub; [exact SOVIS6 | clear - Ha1; lia | clear - Ha2; lia]) ltac:(clear - Ha1 SOR; lia) ltac:(clear - Ha2 SOR; lia))).
    eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha1 SOR; lia. 2: clear - Ha2 SOR; lia. eapply L5C.agree_on_sub. exact SOK6. exact Ha1. exact Ha2. }
  assert (CELL1 : forall v, L5.u8_at RSEGS M so v -> L5.u8_at RSEGS MV6 so v).
  { intros v Hc. apply (proj2 (u8_at_vis H6 M6 so v ltac:(eapply avis_sub; [exact SOVIS6 | clear; lia | clear; lia]) ltac:(clear - SOR; lia) ltac:(clear - SOR; lia))).
    eapply L5C.u8_at_agree. 4: exact Hc. 2: clear - SOR; lia. 2: clear - SOR; lia. eapply L5C.agree_on_sub. exact SOK6. clear; lia. clear; lia. }
  set (n := Z.of_nat (length s)) in *.
  assert (NR : 0 <= n <= 4999 /\ 0 <= n < 2 ^ 64) by (subst n; clear - LEN; lia). destruct NR as [NR NR'].
  (* [comment removed for export] *)
  assert (EXB : exists fx7 R7 pp, msteps RSEGS (st fx1 R6 583536 MV6) (st fx7 R7 TOBIG3 MV6)
              /\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R7 (reg x) = getr R6 (reg x))
              /\ getr R7 (reg 1) = Z_to_bv 64 583632 /\ getr R7 (reg 10) = Z_to_bv 64 pp /\ getr R7 (reg 11) = Z_to_bv 64 n /\ getr R7 (reg 12) = Z_to_bv 64 o
              /\ L5.bytes_at RSEGS M6 pp s /\ asrc IL LB FF M6 pp n /\ (pp + n <= o \/ o + 32 <= pp)).
  { destruct STR as [(L22 & SB0 & SBY & _)|(w0 & pd & (LT0 & LW0 & LLEN & LPD & LBY & _) & LIN & LCAP & LW0R)].
    - (* [comment removed for export] *)
      assert (B0R : 0 <= 2 * n <= 255 /\ 0 <= 2 * n < 2 ^ 64) by (subst n; clear - L22; lia). destruct B0R as [B0R B0R'].
      assert (B0T : Z.testbit (2 * n) 0 = false) by (apply Z.testbit_even_0).
      pose proof (CELL1 _ SB0) as SB0v.
      pose proof (scBs_conc fx1 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => so | 37%nat => 2 * n | 48%nat => U R6 1 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx7 & R7 & M7v & _ & bFR & _ & (bMS & bKS & bR1 & bR10 & bR11 & bR12)).
      assert (E7 : M7v = MV6) by (apply mem_eq_of_agree; intros a Ha; apply bFR). subst M7v.
      exists fx7, R7, (so + 1). split. exact bMS.
      split. { intros x Hx. apply bKS. revert Hx. apply (L5K.incl_b _ KS_scBs). vm_compute; reflexivity. }
      split. exact bR1. split. exact bR10. split. { rewrite bR11. f_equal. rewrite Z.mul_comm. apply Z.div_mul. clear; lia. } split. exact bR12.
      split. { eapply L5C.bytes_at_agree. 4: exact SBY. 2: clear - SOR; lia. 2: fold n; clear - SOR NR; lia. eapply L5C.agree_on_sub. exact SOK6. clear; lia. fold n. subst n; clear - L22; lia. }
      split. { right; right; right. exists so. split. exact AOS. split. clear; lia. split. subst n; clear - L22; lia. exact SZS6. }
      subst n; clear - APOS L22. lia.
    - (* [comment removed for export] *)
      assert (B0R : 0 <= w0 mod 256 <= 255 /\ 0 <= w0 mod 256 < 2 ^ 64) by (pose proof (Z.mod_pos_bound w0 256 ltac:(clear; lia)); clear - H0; lia). destruct B0R as [B0R B0R'].
      assert (B0T : Z.testbit (w0 mod 256) 0 = true). { change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by (clear; lia). exact LT0. }
      pose proof (CELL1 _ (u8_of_u64_lo M so w0 LW0)) as SB0v.
      pose proof (CELL8 (so + 8) _ ltac:(clear; lia) ltac:(clear; lia) LLEN) as LLENv. pose proof (CELL8 (so + 16) _ ltac:(clear; lia) ltac:(clear; lia) LPD) as LPDv.
      destruct (WFB (pd, w0 - 1) LIN) as ((Q0 & _ & _ & _ & Q4 & (_ & _ & Q6)) & _ & _ & _ & _ & _ & QFS). cbn [fst snd] in *.
      assert (PDR : 0 <= pd < 2 ^ 64) by (clear - Q0 Q6 LCAP; lia).
      pose proof (scBl_conc fx1 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => so | 37%nat => w0 mod 256 | 38%nat => n | 39%nat => pd | 48%nat => U R6 1 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc ]).
      destruct P as (fx7 & R7 & M7v & _ & bFR & _ & (bMS & bKS & bR1 & bR10 & bR11 & bR12)).
      assert (E7 : M7v = MV6) by (apply mem_eq_of_agree; intros a Ha; apply bFR). subst M7v.
      assert (PAP : pd + n <= o \/ o + 32 <= pd) by (clear - QFS OFS LCAP; lia).
      exists fx7, R7, pd. split. exact bMS.
      split. { intros x Hx. apply bKS. revert Hx. apply (L5K.incl_b _ KS_scBl). vm_compute; reflexivity. }
      split. exact bR1. split. exact bR10. split. exact bR11. split. exact bR12.
      split. { eapply L5C.bytes_at_agree. 4: exact LBY. 2: clear - PDR; lia. 2: fold n; clear - Q6 LCAP; lia. intros i Hi. fold n in Hi. apply KEEP6. clear - Hi PDR Q6 LCAP; lia.
               apply (block_client L ar LB FF sp SCR pd (w0 - 1) i LIN). clear - Hi LCAP; lia. clear - Hi PAP; lia. }
      split. { right; left. exists pd, (w0 - 1). split. exact LIN. split. clear; lia. clear - LCAP; lia. }
      exact PAP. }
  destruct EXB as (fx7 & R7 & pp & bMS & bKS & bR1 & bR10 & bR11 & bR12 & BY6 & SRC6 & PAP).
  apply (apure LB FF LK cr A M6 model6 fx1 fx7 R6 583536 R7 TOBIG3 K HH6 (conj Hh6 MI6) bMS).
  intros model7 HH7 AM7 RT7 AH7.
  assert (J2 : getr R7 (reg 2) = Z_to_bv 64 (sp - 32)). { rewrite (bKS 2%nat) by inl. rk. }
  assert (J4 : getr R7 (reg 4) = Z_to_bv 64 (hl_tp L)). { rewrite (bKS 4%nat) by inl. rewrite (cs_of_preserved R1 R6 4 RP6) by inl. rewrite (aKS 4%nat) by inl. rewrite <- r4. exact G4. }
  (* [comment removed for export] *)
  apply (TB3 fx7 R7 M6 model7 K LB FF LK cr A pp o (sp - 32) 583632 (Z.land fbo 252) false s HH7 AM7 HK).
  - rewrite r10. exact bR10.
  - rewrite r11. exact bR11.
  - intros X. discriminate X.
  - rewrite r12. exact bR12.
  - exact LEN.
  - exact CR.
  - rewrite r1. exact bR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact J2.
  - exact (proj2 SA32).
  - rewrite r4. exact J4.
  - apply (astk_sub ar M6 M6 sp SCR 32 TOBIG_SCR ASTK6 (mem_grows_refl M6)). clear; lia. rewrite TSCR_EQ; clear; lia. rewrite TSCR_EQ; clear - HSCR; lia. exact (proj1 SA32).
  - exact FFR.
  - exact FFR2.
  - apply (ffrs_le FF sp). exact FFRS. clear; lia.
  - exact BIG6.
  - exact FB3.
  - exact AOB.
  - exact SZ6.
  - exact BY6.
  - exact BR.
  - exact SRC6.
  - exact PAP.
  - intros fx10 R10 M10 model10 LB10 cr10 LK10 A10 POST RT10 IA10 AM10 LKI10 HH10.
    unfold tobig_post in POST. destruct POST as (RP10 & PC).
    (* [comment removed for export] *)
    assert (COMMON : forall Wt, ahpres L ar LB FF (sp - 32) TOBIG_SCR Wt M6 M10 -> (forall a, L5.outside [(o, 32)] a -> L5.outside Wt a) ->
               astk ar M10 sp SCR /\ ek L ar LB FF sp SCR [(o, 32)] M M10 /\ dk L ar LB FF sp SCR M M10
               /\ (forall a v, sp - 32 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M10 a v)).
    { intros Wt AH10 WSUB.
      split. { apply (astk_after L ar C HI HIok LB FF LK cr A M6 M6 M10 _ sp _ (sp - 32) TOBIG_SCR _ HH7 ASTK6 (mem_grows_refl M6) AH10).
               rewrite TSCR_EQ; clear - HSCR; lia. clear; lia. clear - HSCR; lia. }
      split. { eapply ek_trans. exact EK6. apply (ek_callee L ar LB [] FF [] sp SCR (sp - 32) TOBIG_SCR [(o, 32)] Wt M6 M10 AH10).
               rewrite TSCR_EQ; clear - HSCR; lia. clear; lia. intros a _ X. apply WSUB. exact X. }
      split. { eapply dk_trans. exact DK6. apply (dk_callee L ar LB [] FF [] sp SCR (sp - 32) TOBIG_SCR Wt M6 M10 AH10). rewrite TSCR_EQ; clear - HSCR; lia. clear; lia. }
      intros a v Ha1 Ha2 Hc.
      assert (C1 : L5.u64_at RSEGS M1 a v).
      { apply (proj1 (u64_at_vis (ahid A model) M1 a v (VIS a 8 ltac:(clear - Ha1 SLO HSCR; lia) ltac:(clear - Ha2 SPR; lia)) ltac:(clear - Ha1 SPR; lia) ltac:(clear - Ha2 SPR; lia))). rewrite VIS1. exact Hc. }
      eapply L5C.u64_at_agree. 4: exact C1. 2: clear - Ha1 SPR; lia. 2: clear - Ha2 SPR; lia. intros i Hi.
      assert (SC : forall scr, aclient L ar LB FF (sp - 32) scr i) by (intros scr; apply stack_client; [clear - Hi Ha1 Ha2 SLO SHI SPT HSCR; lia | clear - Hi Ha1; lia]).
      rewrite (proj1 AH10 i). 2:{ split. clear - Hi Ha1 Ha2 SPR; lia. split. apply SC. apply WSUB. intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Hi Ha1 Ha2 OR SLO HSCR. lia. }
      apply (PRES6 i ltac:(clear - Hi Ha1 Ha2 SPR; lia) (SC _)). clear - Hi Ha1 Ha2 OR SLO HSCR. lia. }
    destruct PC as [(PAR & R10_11 & PP)|(NP & R10_11 & NPP)].
    + (* [comment removed for export] *)
      unfold parse_post in PP. cbv zeta in PP. destruct PP as (st' & OB10 & OL10 & ST10 & CR10 & AH10).
      destruct (COMMON _ AH10 ltac:(intros a X; exact X)) as (ASTK10 & EK10 & DK10 & SAVED).
      pose proof (vis_pack L ar C HI LY HIok LB10 FF LK10 cr10 A10 M10 model10 HH10) as (_ & VIS10 & _).
      pose proof (statics_vis LB10 FF LK10 cr10 A10 M10 model10 HH10) as (IMGC10 & CSB10 & CUAR10).
      set (H10 := ahid A10 model10) in *. set (MV10 := mrestrict H10 M10) in *.
      assert (SV10 : avis H10 (sp - 32) 32) by (apply (VIS10 (sp - 32) 32); [clear - SLO HSCR; lia | clear - SPR; lia]).
      assert (W32j : L5.writable RSEGS MV10 (sp - 32) 32).
      { apply (proj2 (writable_vis H10 M10 (sp - 32) 32 SV10 ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
        eapply (astk_writable ar M10 sp). exact ASTK10. clear - HSCR; lia. clear; lia. clear; lia. }
      assert (SVv : forall a v, sp - 32 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV10 a v).
      { intros a v Ha1 Ha2 Hc. apply (proj2 (u64_at_vis H10 M10 a v ltac:(eapply avis_sub; [exact SV10 | clear - Ha1; lia | clear - Ha2; lia]) ltac:(clear - Ha1 SPR; lia) ltac:(clear - Ha2 SPR; lia))).
        apply SAVED; assumption. }
      pose proof (SVv (sp - 8) (U R 1) ltac:(clear; lia) ltac:(clear; lia) aC8) as D8. pose proof (SVv (sp - 16) (U R 8) ltac:(clear; lia) ltac:(clear; lia) aC16) as D16.
      pose proof (SVv (sp - 24) (U R 9) ltac:(clear; lia) ltac:(clear; lia) aC24) as D24. pose proof (SVv (sp - 32) (U R 18) ltac:(clear; lia) ltac:(clear; lia) aC32) as D32.
      assert (K2 : getr R10 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (cs_of_preserved R7 R10 2 RP10) by inl; exact J2).
      assert (K8 : getr R10 (reg 8) = Z_to_bv 64 o). { rewrite (cs_of_preserved R7 R10 8 RP10) by inl. rewrite (bKS 8%nat) by inl. rk. }
      assert (K9 : getr R10 (reg 9) = Z_to_bv 64 so). { rewrite (cs_of_preserved R7 R10 9 RP10) by inl. rewrite (bKS 9%nat) by inl. rk. }
      assert (K18 : getr R10 (reg 18) = Z_to_bv 64 2147450880). { rewrite (cs_of_preserved R7 R10 18 RP10) by inl. rewrite (bKS 18%nat) by inl. rk. }
      pose proof (scD_conc fx10 R10 MV10 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => so | 41%nat => U R 1 | 42%nat => U R 8 | 43%nat => U R 9 | 44%nat => U R 18
                    | 48%nat => U R10 1 | 61%nat => U R10 10 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r11; exact R10_11)]).
      destruct P as (fx11 & R11 & M11v & MG11 & dFR & dFZ & (dMS & dKS & dR1 & dR2 & dR8 & dR9 & dR18)).
      pose proof (ret_to fx11 R11 M11v 0x8e7ec W_8e7ec r F_8e7ec eq_refl D_8e7ec ltac:(rewrite dR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
      apply (apiece_ro L ar C HI LY HIok LB10 FF LK10 cr10 A10 M10 model10 fx10 fx11 R10 583632 R11 r M11v K HH10 AM10 (msteps_trans _ _ _ _ dMS RET) MG11 dFZ).
      intros M11 model11 HH11 AM11 RT11 AH11 VIS11 MGM11 FRM11.
      assert (E11 : M11 = M10) by (apply mem_eq_of_agree; exact FRM11). subst M11.
      apply (KONT fx11 R11 M10 model11 LB10 cr10 LK10 A10).
      * split.
        { apply preserved_by_index. intros k Hk. unfold cs_all in Hk. cbn [In] in Hk.
          destruct Hk as [<-|Hk]. { rewrite dR2. rewrite <- r2, G2. reflexivity. }
          destruct Hk as [<-|Hk]. { rewrite (dKS 3%nat) by inl. rewrite (cs_of_preserved R7 R10 3 RP10) by inl. rewrite (bKS 3%nat) by inl. rk. }
          destruct Hk as [<-|Hk]. { rewrite (dKS 4%nat) by inl. rewrite (cs_of_preserved R7 R10 4 RP10) by inl. rewrite (bKS 4%nat) by inl. rk. }
          destruct Hk as [<-|Hk]. { rewrite dR8. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite dR9. symmetry. apply U_to. }
          destruct Hk as [<-|Hk]. { rewrite dR18. symmetry. apply U_to. }
          repeat (destruct Hk as [<-|Hk]; [rewrite (dKS _) by inl; rewrite (cs_of_preserved R7 R10 _ RP10) by inl; rewrite (bKS _) by inl; rk|]). destruct Hk. }
        split. exact PAR.
        unfold parse_post. cbv zeta. exists st'. split. exact OB10. split. exact OL10. split. exact ST10. split. exact CR10.
        apply ahpres_of. exact EK10. eapply astk_defined. exact ASTK10. clear; lia. clear; lia. exact DK10.
      * eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT6. eapply L5LZ.model_rt_trans. exact RT7. eapply L5LZ.model_rt_trans. exact RT10. exact RT11.
      * exact IA10.
      * exact AM11.
      * exact LKI10.
      * exact HH11.
    + (* [comment removed for export] *)
      destruct NPP as (ELB & OB10 & CR10 & AH10). subst LB10.
      destruct (COMMON _ AH10 ltac:(intros a _ rr [])) as (ASTK10 & EK10 & DK10 & SAVED).
      pose proof (vis_pack L ar C HI LY HIok LB FF LK10 cr10 A10 M10 model10 HH10) as (_ & VIS10 & _).
      pose proof (statics_vis LB FF LK10 cr10 A10 M10 model10 HH10) as (IMGC10 & CSB10 & CUAR10).
      set (H10 := ahid A10 model10) in *. set (MV10 := mrestrict H10 M10) in *.
      assert (W32j : L5.writable RSEGS MV10 (sp - 32) 32).
      { apply (proj2 (writable_vis H10 M10 (sp - 32) 32 (VIS10 (sp - 32) 32 ltac:(clear - SLO HSCR; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
        eapply (astk_writable ar M10 sp). exact ASTK10. clear - HSCR; lia. clear; lia. clear; lia. }
      assert (K2 : getr R10 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (cs_of_preserved R7 R10 2 RP10) by inl; exact J2).
      assert (K8 : getr R10 (reg 8) = Z_to_bv 64 o). { rewrite (cs_of_preserved R7 R10 8 RP10) by inl. rewrite (bKS 8%nat) by inl. rk. }
      assert (K9 : getr R10 (reg 9) = Z_to_bv 64 so). { rewrite (cs_of_preserved R7 R10 9 RP10) by inl. rewrite (bKS 9%nat) by inl. rk. }
      assert (K18 : getr R10 (reg 18) = Z_to_bv 64 2147450880). { rewrite (cs_of_preserved R7 R10 18 RP10) by inl. rewrite (bKS 18%nat) by inl. rk. }
      pose proof (scT_conc fx10 R10 MV10 (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => so | 48%nat => U R10 1 | 61%nat => U R10 10 | _ => 0 end)) as P. cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc | (rewrite <- r11; exact R10_11)]).
      destruct P as (fx11 & R11 & M11v & _ & tFR & _ & (tMS & tKS & tR9)).
      assert (E11 : M11v = MV10) by (apply mem_eq_of_agree; intros a Ha; apply tFR). subst M11v.
      apply (apure LB FF LK10 cr10 A10 M10 model10 fx10 fx11 R10 583632 R11 STRCTOR_THROW K HH10 AM10 tMS).
      intros model11 HH11 AM11 RT11 AH11.
      apply (KTHROW fx11 R11 M10 model11 cr10 LK10 A10).
      * unfold strctor_throw_state. split. exact NP.
        split. { rewrite (tKS 2%nat) by inl. exact K2. } split. { rewrite (tKS 8%nat) by inl. exact K8. } split. exact tR9.
        split. { rewrite (tKS 18%nat) by inl. exact K18. }
        split. { intros i Hi. cbn [In] in Hi.
                 repeat (destruct Hi as [<-|Hi]; [rewrite (tKS _) by inl; rewrite (cs_of_preserved R7 R10 _ RP10) by inl; rewrite (bKS _) by inl; rk|]). destruct Hi. }
        split. exact (SAVED (sp - 8) (U R 1) ltac:(clear; lia) ltac:(clear; lia) aC8). split. exact (SAVED (sp - 16) (U R 8) ltac:(clear; lia) ltac:(clear; lia) aC16).
        split. exact (SAVED (sp - 24) (U R 9) ltac:(clear; lia) ltac:(clear; lia) aC24). split. exact (SAVED (sp - 32) (U R 18) ltac:(clear; lia) ltac:(clear; lia) aC32).
        split. exact OB10.
        split. { intros j Hj. unfold byte_at. rewrite (proj1 AH10). apply SZ6. exact Hj. split. unfold S, SB. destruct (SHO j Hj) as [X _]. clear - X; lia.
                 split. replace (S o + j) with (o / 8 + SB + j) by reflexivity. apply (aclient_narrow L ar LB FF sp SCR). apply OCLSH. exact Hj.
                 rewrite TSCR_EQ. unfold SB. destruct (SHO j Hj) as [X _]. clear - X SPR. lia. intros rr []. }
        split. exact CR10. split. exact ASTK10.
        apply ahpres_of. exact EK10. eapply astk_defined. exact ASTK10. clear; lia. clear; lia. exact DK10.
      * eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT6. eapply L5LZ.model_rt_trans. exact RT7. eapply L5LZ.model_rt_trans. exact RT10. exact RT11.
      * exact IA10.
      * exact AM11.
      * exact LKI10.
      * exact HH11.
Qed.
End WithIface.
End SCFG_1.
End L5ASC.
