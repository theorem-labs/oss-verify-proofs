(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PeSpecsAmc PmModelFactsA PmStep PeStepAB0 PeStepB2 XIcptAs0B0 PeBLocIslandP PeBLocP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_rfba54_fba58 Eb0_code_rfbaf0_fbaf4.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.asan Require Import XIcptAB0S9 XIcptAs0KitB0S9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PMBLOC.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Lemma wseg_loc1 : wseg_ok RSEGS (Z_to_bv 64 6785458) (Z.to_nat 1854) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_loc2 : wseg_ok RSEGS (Z_to_bv 64 6789144) (Z.to_nat 88) = true. Proof. vm_compute. reflexivity. Qed.
Lemma writable_img M a n : wseg_ok RSEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 < n -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof.
  intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
  eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (Datatypes.S k)).
  - rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
  - apply store_ok_wseg. exact W.
  - rewrite !L5.unsigned_lit by lia. lia.
  - rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma stack_zeros M sp : shadow_zero M (sp - 16384) 2048 -> sp mod 16 = 0 -> L5KA.zeros_at M (sp / 8 + 2147450368) 512.
Proof.
  intros SZ S16 i Hi. pose proof (SZ (1536 + i) ltac:(Lia.lia)) as X. unfold byte_at, S, SB in X.
  replace (sp / 8 + 2147450368 + i) with ((sp - 16384) / 8 + 2147450880 + (1536 + i)) by Lia.lia. exact X.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis MCC : PMAMC.mcmp_cells_b C.
Let LYa := PMB.ly_as0 L C LY.

Lemma ccell LB FF LK cr Aw M V a w v : ri_inv HI LB FF LK cr Aw M V -> In (a, w, v) (asc_cells C) -> cell_is RSEGS M a (Z.to_nat w) v.
Proof.
  intros HH Hin. pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (L5A.aly_segs L C LYa) in CS.
  rewrite Forall_forall in CS. exact (CS (a, w, v) Hin).
Qed.
Lemma d4cell LB FF LK cr Aw M V a w v : ri_inv HI LB FF LK cr Aw M V -> In (a, w, v) L5A.AS0_ALY_CELLS_D4 -> cell_is RSEGS M a (Z.to_nat w) v.
Proof. intros HH Hin. exact (ccell LB FF LK cr Aw M V a w v HH (L5A.aly_cells L C LYa _ Hin)). Qed.

Lemma loc_foot_static a : (6785458 <= a < 6787312 \/ 6789144 <= a < 6789232) -> ~ hl_rt_static L a.
Proof.
  intros Ha. apply (PMB.ly_static L C LY). unfold PMST.dep, pm_foot, pm_initc.
  cbn [pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit pa_canary pa_need_locks pa_locale_lock PMB.AD ADDR_A app].
  left. destruct Ha as [Ha|Ha]; [exists (0x6789b2, 0x6790f0)| exists (0x679818, 0x679870)]; split; cbn; [tauto| lia| tauto| lia].
Qed.

Theorem locale_ctor_ok : PMB.locale_ctor_spec L ar HI.
Proof.
  unfold PMB.locale_ctor_spec, PMSPA.locale_ctor_spec.
  intros fx R M model K LB FF LK Aw cr o sp r b HH AM K0 ENT FRM FRS A10 AO O8 ODEF BASE LOC KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10.
  change (PMSPA.pm_scr 2) with 16384 in *. change (16384 / 8) with 2048 in STKSH.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332491264 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (PMKB.aobj_of_aobjA FF o 8 AO O8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model o 8 sp 16384 HH AOB ltac:(lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF' & OVIS & OVSH & OCL & OCLSH).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (VU8 : forall x v0, 0x10000 <= x < 0x69c000 -> L5.u8_at RSEGS M x v0 -> L5.u8_at RSEGS MV x v0).
  { intros x v0 Hx X. apply (proj2 (L5A.u8_at_vis H M x v0 (VIMG x 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (VU32 : forall x v0, 0x10000 <= x -> x + 4 <= 0x69c000 -> L5.u32_at RSEGS M x v0 -> L5.u32_at RSEGS MV x v0).
  { intros x v0 Hx Hx' X. apply (proj2 (L5A.u32_at_vis H M x v0 (VIMG x 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (VU64 : forall x v0, 0x10000 <= x -> x + 8 <= 0x69c000 -> L5.u64_at RSEGS M x v0 -> L5.u64_at RSEGS MV x v0).
  { intros x v0 Hx Hx' X. apply (proj2 (L5A.u64_at_vis H M x v0 (VIMG x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (OWv : L5.writable RSEGS MV o 8).
  { apply (proj2 (L5A.writable_vis H M o 8 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  unfold PMSPA.cfg. cbn [pa_locale_ctor PMB.AD ADDR_A].
  destruct b.
  -
    destruct LOC as (G & P0). cbn [pa_glocale pa_classic_imp PMB.AD ADDR_A] in G, P0.
    assert (Gv : L5.u8_at RSEGS MV 6785968 1) by (apply VU8; [lia| exact G]).
    assert (Pv : L5.u64_at RSEGS MV 6785960 6787008) by (apply VU64; [lia| lia| exact P0]).
    assert (W32 : L5.writable RSEGS MV (sp - 32) 32).
    { apply (proj2 (L5A.writable_vis H M (sp - 32) 32 (VIS (sp - 32) 32 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5SAR.astk_writable ar M sp 16384); [exact ASTK| lia| lia| lia]. }
    assert (FRO : sp - 32 + 32 <= o \/ o + 8 <= sp - 32) by lia.
    pose proof (PMBLOCP.aliB_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | _ => 0 end)) as P.
    cbn beta iota in P. L5SAR.feed P ltac:(first [assumption | unfold PMBLOCP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & B10 & B11 & CO).
    assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0x1051f0 W_1051a0 r F_1051a0 eq_refl D_1051a0 R1ra ltac:(lia) Hr2) as MS2.
    set (W1 := fun a => sp - 32 <= a < sp - 32 + 32 \/ o + 0 <= a < o + 0 + 8).
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0x105194 R1 r M1v W1 K HH AM).
    { eapply msteps_trans; [exact MS1| exact MS2]. }
    { exact MG1. }
    { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha [Wa|Wa].
      - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - split; [apply (L5SAR.obj_client L ar LB FF 0 0 o 8 a AOB); lia| lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK : L5SAR.ek L ar LB FF sp 16384 [(o, 8)] M M1).
    { apply (L5SAR.ek_piece L ar LB FF sp 16384 [(o, 8)] M M1 W1 FR1). intros a Ha Hc Ho [X|X].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 16384 a HH SPT Hc) as [Z1|Z1]; lia.
      - apply (Ho (o, 8)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. lia. }
    apply (KONT fx1 R1 M1 model1 LK Aw).
    + apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
    + cbn [pa_classic_imp PMB.AD ADDR_A]. rewrite <- VIS1 in CO. exact (proj1 (L5A.u64_at_vis H M1 o 6787008 OVIS ltac:(lia) ltac:(lia)) CO).
    + cbn [PMST.loc_ok pa_glocale pa_classic_imp PMB.AD ADDR_A]. split.
      * apply (L5C.u8_at_agree RSEGS M M1); [| lia| lia| exact G]. intros i Hi. apply FR1; [lia|]. intros [X|X]; lia.
      * apply (L5C.u64_at_agree RSEGS M M1); [| lia| lia| exact P0]. intros i Hi. apply FR1; [lia|]. intros [X|X]; lia.
    + apply (L5SAR.ahpres_of L ar LB FF sp 16384 [(o, 8)] M M1 EK).
      * intros i Hi. apply MGM1. apply SDEF. exact Hi.
      * apply (L5SAR.dk_grows L ar LB FF sp 16384 M M1 MGM1).
    + exact MRT1.
    + intros x Hx. exact Hx.
    + intros x Hx. exact Hx.
    + exact AM1.
    + exact HH1.
  -
    cbn [PMST.loc_ok] in LOC. unfold PMST.img_clear_l in LOC. cbn [pa_loc_foot PMB.AD ADDR_A] in LOC.
    assert (C1 : L5.img_clear M 6785458 6787312) by (apply (LOC (0x6789b2, 0x6790f0)); cbn; auto).
    assert (C2 : L5.img_clear M 6789144 6789232) by (apply (LOC (0x679818, 0x679870)); cbn; auto).
    destruct BASE as (RO0 & (can & Hcan & CAN) & NL & LL). cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PMB.AD ADDR_A] in RO0, CAN, NL, LL.
    assert (V0 : L5.img_clear MV 65536 1306624) by (apply L5A.img_clear_mrestrict; exact RO0).
    assert (V1 : L5.u64_at RSEGS MV 1335544 2147450880) by (apply VU64; [lia| lia| exact CSB]).
    assert (V2 : L5.u32_at RSEGS MV 1335552 1) by (apply VU32; [lia| lia| exact CUAR]).
    assert (VC1 : L5.img_clear MV 6785458 6787312) by (apply L5A.img_clear_mrestrict; exact C1).
    assert (VC2 : L5.img_clear MV 6789144 6789232) by (apply L5A.img_clear_mrestrict; exact C2).
    assert (WC1 : L5.writable RSEGS MV 6785458 1854).
    { apply (proj2 (L5A.writable_vis H M 6785458 1854 (VIMG 6785458 1854 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      exact (writable_img M 6785458 1854 wseg_loc1 ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (WC2 : L5.writable RSEGS MV 6789144 88).
    { apply (proj2 (L5A.writable_vis H M 6789144 88 (VIMG 6789144 88 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      exact (writable_img M 6789144 88 wseg_loc2 ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (VNL : L5.u8_at RSEGS MV 6923283 0) by (apply VU8; [lia| exact NL]).
    assert (VLL : L5.u32_at RSEGS MV 6923504 0) by (apply VU32; [lia| lia| exact LL]).
    assert (VCAN : L5.u64_at RSEGS MV 6922688 can) by (apply VU64; [lia| lia| exact CAN]).
    assert (W4096 : L5.writable RSEGS MV (sp - 4096) 4096).
    { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
      apply (L5SAR.astk_writable ar M sp 16384); [exact ASTK| lia| lia| lia]. }
    assert (FRO : sp - 4096 + 4096 <= o \/ o + 8 <= sp - 4096) by lia.

    assert (XC1 : L5.u64_at RSEGS MV 1300680 1335544) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1300680 8 1335544 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 4 right; left; reflexivity))]).
    assert (XC2 : L5.u64_at RSEGS MV 1300688 1338856) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1300688 8 1338856 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 5 right; left; reflexivity))]).
    assert (XC3 : L5.u64_at RSEGS MV 1338856 0) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1338856 8 0 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 6 right; left; reflexivity))]).
    assert (XC4 : L5.u64_at RSEGS MV 1300696 1338864) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1300696 8 1338864 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 7 right; left; reflexivity))]).
    assert (XC5 : L5.u64_at RSEGS MV 1338864 0) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1338864 8 0 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 8 right; left; reflexivity))]).
    assert (XC6 : L5.u64_at RSEGS MV 1300704 1338848) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1300704 8 1338848 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 9 right; left; reflexivity))]).
    assert (XC7 : L5.u64_at RSEGS MV 1338848 140737488355327) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1338848 8 140737488355327 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 10 right; left; reflexivity))]).
    assert (XC8 : L5.u64_at RSEGS MV 1303600 1338841) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1303600 8 1338841 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 11 right; left; reflexivity))]).
    assert (XC9 : L5.u8_at RSEGS MV 1338841 1) by (apply VU8; [lia| exact (d4cell _ _ _ _ _ _ _ 1338841 1 1 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 12 right; left; reflexivity))]).
    assert (XC10 : L5.u64_at RSEGS MV 1308888 1245236) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1308888 8 1245236 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 2 right; left; reflexivity))]).
    assert (XC11 : L5.u64_at RSEGS MV 1308880 1244208) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1308880 8 1244208 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 13 right; left; reflexivity))]).
    destruct MCC as (MC1 & MC2 & MC3 & MC4).
    assert (MX1 : L5.u8_at RSEGS MV 1338840 1) by (apply VU8; [lia| exact (ccell _ _ _ _ _ _ _ 1338840 1 1 HH MC1)]).
    assert (MX2 : L5.u64_at RSEGS MV 1308416 1244160) by (apply VU64; [lia| lia| exact (ccell _ _ _ _ _ _ _ 1308416 8 1244160 HH MC2)]).
    assert (MX3 : L5.u8_at RSEGS MV 1932582 1) by (apply VU8; [lia| exact (ccell _ _ _ _ _ _ _ 1932582 1 1 HH MC3)]).
    assert (MX4 : L5.u8_at RSEGS MV 1932583 1) by (apply VU8; [lia| exact (ccell _ _ _ _ _ _ _ 1932583 1 1 HH MC4)]).

    assert (IMGZ : forall lo n, 65536 <= lo -> lo + n <= 0x69c000 -> 0 < n -> (lo + n <= 0x232e0 \/ 0x23ca0 <= lo) -> (lo + n <= 0x1380e8 \/ 0x138188 <= lo) ->
                   (lo + n <= 0x1423d0 \/ 0x142a10 <= lo) -> forall a k, SB + lo / 8 <= a -> a + k <= SB + (lo + n - 1) / 8 + 1 -> L5KA.zeros_at MV a k).
    { intros lo n Hlo Hn Hn0 P1 P2 P3 a k Ha Hk.
      destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH lo n) as (ZB & SA).
      - rewrite (L5A.aly_img_lo L C LYa). lia. - rewrite (L5A.aly_img_hi L C LYa). lia. - lia.
      - rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; clear - P1 P2 P3; lia|]). apply Forall_nil.
      - intros i Hi. assert (AV : L5A.avis H (a + i) 1).
        { apply (L5A.avis_of_shadow_allowed Aw model lo n). exact SA. intros j Hj. unfold in_shadow_of, S, SB in *. lia. }
        pose proof (ZB (a + i) ltac:(unfold in_shadow_of, S, SB in *; lia)) as Z1. unfold byte_at in Z1.
        unfold MV. rewrite (AsanAcct.mrestrict_visible H M); [exact Z1|]. pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (SHZ1 : L5KA.zeros_at MV 2148299054 248) by (apply (IMGZ (6785458 - 64) (1854 + 128)); try unfold SB; lia).
    assert (SHZ2 : L5KA.zeros_at MV 2148299515 27) by (apply (IMGZ (6789144 - 64) (88 + 128)); try unfold SB; lia).
    assert (SHZ3 : L5KA.zeros_at MV 2147473165 78) by (apply (IMGZ 0x2b86c 616); try unfold SB; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (STZ : L5KA.zeros_at MV (sp / 8 + 2147450368) 512).
    { intros i Hi. unfold MV. rewrite (AsanAcct.mrestrict_visible H M). apply (stack_zeros M sp STKSH A16). exact Hi.
      assert (AV : L5A.avis H (sp / 8 + 2147450368 + i) 1).
      { apply (VSTSH (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
    assert (CR : 0 <= can < 2 ^ 64) by exact Hcan.
    pose proof (PMBLIP.aliA_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => can | _ => 0 end)) as P.
    cbn beta iota in P. L5SAR.feed P ltac:(first [assumption | unfold PMBLIP.aligned; lia | lia]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & B10 & B11 & CO & CG & CP).
    assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    pose proof (PMK.ret_to RSEGS fx1 R1 M1v 0x1051f0 W_1051a0 r F_1051a0 eq_refl D_1051a0 R1ra ltac:(lia) Hr2) as MS2.
    set (W1 := fun a => (sp - 4096 <= a < sp - 4096 + 4096 \/ o + 0 <= a < o + 0 + 8) \/ (0 + 6785458 <= a < 0 + 6785458 + 1854 \/ 0 + 6789144 <= a < 0 + 6789144 + 88)).
    apply (PMKB2.apiece_img L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0x105194 R1 r M1v W1 K HH AM).
    { eapply msteps_trans; [exact MS1| exact MS2]. }
    { exact MG1. }
    { intros a Ha N. apply FZ1; [exact Ha| | | |]; intros X; apply N; [left; left|left; right|right; left|right; right]; exact X. }
    { intros a Ha [[Wa|Wa]|[Wa|Wa]].
      - split; [|intros X; pose proof (PMB.ly_ro L C LY a X); lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
      - split; [apply (L5SAR.obj_client L ar LB FF 0 0 o 8 a AOB); lia| apply (PMKB2.rt_ro_bss L C a LY); lia].
      - split; [|apply (PMKB2.rt_ro_bss L C a LY); lia]. unfold aclientw, aclient_g. right; right; left.
        split; [rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); lia|]. intros [X|X]; [exact (loc_foot_static a ltac:(lia) X)| exact (PMKB2.rt_ro_bss L C a LY ltac:(lia) X)].
      - split; [|apply (PMKB2.rt_ro_bss L C a LY); lia]. unfold aclientw, aclient_g. right; right; left.
        split; [rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa); lia|]. intros [X|X]; [exact (loc_foot_static a ltac:(lia) X)| exact (PMKB2.rt_ro_bss L C a LY ltac:(lia) X)]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    set (WL := (o, 8) :: PMSPA.loc_W PMB.AD).
    assert (EK : L5SAR.ek L ar LB FF sp 16384 WL M M1).
    { apply (L5SAR.ek_piece L ar LB FF sp 16384 WL M M1 W1 FR1). intros a Ha Hc Ho [[X|X]|[X|X]].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 16384 a HH SPT Hc) as [Z1|Z1]; lia.
      - apply (Ho (o, 8)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. lia.
      - apply (Ho (0x6789b2, 0x6790f0 - 0x6789b2)). right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. lia.
      - apply (Ho (0x679818, 0x679870 - 0x679818)). right; right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. lia. }
    apply (KONT fx1 R1 M1 model1 LK Aw).
    + apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
    + cbn [pa_classic_imp PMB.AD ADDR_A]. rewrite <- VIS1 in CO. exact (proj1 (L5A.u64_at_vis H M1 o 6787008 OVIS ltac:(lia) ltac:(lia)) CO).
    + cbn [PMST.loc_ok pa_glocale pa_classic_imp PMB.AD ADDR_A]. rewrite <- VIS1 in CG, CP. split.
      * exact (proj1 (L5A.u8_at_vis H M1 6785968 1 (VIMG 6785968 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) CG).
      * exact (proj1 (L5A.u64_at_vis H M1 6785960 6787008 (VIMG 6785960 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) CP).
    + apply (L5SAR.ahpres_of L ar LB FF sp 16384 WL M M1 EK).
      * intros i Hi. apply MGM1. apply SDEF. exact Hi.
      * apply (L5SAR.dk_grows L ar LB FF sp 16384 M M1 MGM1).
    + exact MRT1.
    + intros x Hx. exact Hx.
    + intros x Hx. exact Hx.
    + exact AM1.
    + exact HH1.
Qed.

Theorem locale_dtor_ok : PMB.locale_dtor_spec L ar HI.
Proof.
  unfold PMB.locale_dtor_spec, PMSPA.locale_dtor_spec.
  intros fx R M model K LB FF LK Aw cr o sp r HH AM K0 ENT FRM FRS A10 AO CELL KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. cbn [pa_classic_imp PMB.AD ADDR_A] in CELL.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  destruct AO as (f & Hf & O1 & O2).
  pose proof (WF f Hf) as (Y1 & Y2 & _ & Y4 & _).
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
  assert (HB : 0 < ff_bytes (ff_class f) <= 2048).
  { clear - Y4. destruct Y4 as [E|[E|[E|[E|[E|[E|[]]]]]]]; rewrite <- E;
      [change (ff_bytes 0) with 64 | change (ff_bytes 1) with 128 | change (ff_bytes 2) with 256 | change (ff_bytes 3) with 512 | change (ff_bytes 4) with 1024 | change (ff_bytes 5) with 2048]; lia. }
  assert (OR : 6930432 <= o <= 140737488355320) by (clear - O1 O2 Y1 Y2 FSIMG FSAPP HB; lia).
  assert (OVIS : L5A.avis H o 8) by (apply VFS; clear - O1 O2 Y1 Y2 HB; lia).
  assert (CV : L5.u64_at RSEGS MV o 6787008) by (apply (proj2 (L5A.u64_at_vis H M o 6787008 OVIS ltac:(lia) ltac:(lia))); exact CELL).
  change (PMSPA.pm_scr 0) with 12288 in *.
  assert (SPR : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia).
  pose proof (PMBLOCP.aliD_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R MV (fun j => match j with 2%nat => sp | 33%nat => o | _ => 0 end)) as P.
  cbn beta iota in P. L5SAR.feed P ltac:(first [assumption | unfold PMBLOCP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & FA1 & FZ1 & MS1 & KS1 & _).
  assert (E1 : M1v = MV) by (apply L5SAR.mem_eq_of_agree; exact FZ1). subst M1v.
  assert (R1ra : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx1 R1 MV 0x10528c W_10523c r F_10523c eq_refl D_10523c R1ra ltac:(lia) Hr2) as MS2.
  unfold PMSPA.cfg. cbn [pa_locale_dtor PMB.AD ADDR_A].
  apply (L5SAR.apiece_ro L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0x10526c R1 r MV K HH AM (msteps_trans _ _ _ _ MS1 MS2) (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E2 : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  apply (KONT fx1 R1 model1).
  - apply L5SAR.preserved_by_index. intros k Hk. apply KS1. unfold L5SAR.cs_all in Hk. repeat (destruct Hk as [<-|Hk]; [inl|]). destruct Hk.
  - exact MRT1.
  - exact AM1.
  - exact HH1.
Qed.

End Stage.
End PMBLOC.
