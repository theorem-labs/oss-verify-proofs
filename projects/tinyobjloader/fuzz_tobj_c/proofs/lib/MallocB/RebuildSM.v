(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "div"; "pow"; "eqb"; "to_nat"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_fs_hint"; "aa_live"; "ag_fsb"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_frames"; "ageom"; "fs_alloc"; "aa_fs_busy"; "ag_ctx"; "ag_dtls"; "ag_thread"; "topG"; "@Corelib.Init.Datatypes"; "bool"; "list"; "pair"; "prod"; "app"; "cons"; "true"; "Some"; "length"; "false"; "fst"; "nat"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "enc_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "view"; "G0"; "RTC_A"; "cells_footb"; "in_rangesZ"; "rtc_cells_img"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_busy"; "busyb"; "fs_inv"; "geom_ok"; "live_sep"; "nthZ"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "fs_flags"; "fs_frame"; "fs_frame_size"; "fs_num_iter"; "HIGH_SHADOW_END"; "IMG_HI"; "SHADOW_OFF"; "fs_hint_cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "client_addrA"; "client_shadowA"; "frame_flag"; "mem_keptA"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM.R"; "rt_zone"; "@Stdlib.Lists.List"; "In"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma busyb_of_split : ltac2:(tb__ "0|2|
SeS0S1fS21S0S0A2M0A1M1S0S0G1S2G1S35R6R5A2S22G0R4S23G0S20S0S0R3R2A4R1A3A3A3S2S1eS36R7R6R4A3S24A3F_;Fv;Ff;Fpos;Fu;Fc;FA;").
Proof.
  intros A c u pos f v E. unfold busyb. rewrite E, existsb_app. cbn [existsb fst]. rewrite Z.eqb_refl. cbn. apply orb_true_r.
Qed.

Lemma busyb_true_split : ltac2:(tb__ "0|2|
SeS0S0S2S1eS36R3R2R1A3S24A3S4S1fS21S0S0A2M0A1M1G1S4S0S0S4G1G1S1S2G1S35R7R6A2S22G0R3S23G0S20S0S0R5R2A4R1A3A3A3S5S4cS0R5S4dG0S0S28S0S0A2R3A4A3A1A2Lv;A2Lf;A2Lu;A2F_;Fpos;Fc;FA;").
Proof.
  intros A c pos H. unfold busyb in H. apply existsb_exists in H as ([p f] & Hin & E). cbn in E. apply Z.eqb_eq in E. subst p.
  revert Hin. generalize (fs_busy A c) as l. induction l as [|[p g] l IH]; intros Hin; [destruct Hin|].
  destruct (Z.eq_dec p pos) as [->|Hne].
  - exists [], g, l. split; [reflexivity | intros []].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; congruence|].
    destruct (IH Hin) as (u & f' & v & -> & Hn). exists ((p, g) :: u), f', v. split; [reflexivity|].
    cbn. intros [E|E]; [apply Hne; exact E | exact (Hn E)].
Qed.

Lemma fs_busy_alloc : ltac2:(tb__ "0|3|
SeS0S0S0S0S0S6Z0M0R5A2S6G0R2A2S3bScR7A1S26S1fS21S0S0A2M1A1M2S19R8A1A2A2S2G2S35S18R9R8R7R6R5A5R4A2S1eG2L_;SbR4R8A2S23G1S20S0S0R7R6A4S35R9R8A2A3S35R9R4A2X1ex2A3F_;F_;F_;Fc0;Fh;Ff;Fpos;Fc;FA;").
Proof.
  intros A c pos f h c0 Hc Hc0 Hlen. unfold fs_busy, nthZ, fs_alloc. cbn [aa_fs_busy].
  destruct (Z.eqb_spec c0 c).
  - subst c0. rewrite nth_list_upd_same by exact Hlen. reflexivity.
  - rewrite nth_list_upd_other; [reflexivity|]. intros E'. apply n. lia.
Qed.

Lemma fs_hint_alloc : ltac2:(tb__ "0|1|
SeS0S0S0S0S0S6Z0M0R5A2S6G0R2A2S3bScR7A1S26S0S10R8A1A2A2S2S0S3aS0S10S18R9R8R7R6R5A5A1R4G0A4S1eS0L_;SbR4R8A2R5S3aS0S10R9A1R4G0A4X1ex2A3F_;F_;F_;Fc0;Fh;Ff;Fpos;Fc;FA;").
Proof.
  intros A c pos f h c0 Hc Hc0 Hlen. unfold nthZ, fs_alloc. cbn [aa_fs_hint].
  destruct (Z.eqb_spec c0 c).
  - subst c0. rewrite nth_list_upd_same by exact Hlen. reflexivity.
  - rewrite nth_list_upd_other; [reflexivity|]. intros E'. apply n. lia.
Qed.

Section R.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Lemma client_addr_cases : ltac2:(tb__ "0|5|
SeS0S2eS37R1R3A2S45VCST;R4R3A3S12SfR5A1A1S0S3S1S6S1dSfR6A1A1R5A2S7R5SaZ2Z2fA2A2A2S3S4S0S0S4S0S0S1S4cS21S0S0A2S20S0S0R2R1A4S11R8A1A3S1S6R2R7A2S7R7S8R2R1A2A2A2A2Ln;A2Lb;A2S3S4S0S0S4S0S0S1S1S6Z0M0R2A2S7R2ZbA2A2M1S1S1S6G0R1A2S7R1S40R2A1A2A2M2S1S2S1eS36R8R2R1A3S24A3M3S1S6S3eR3R2R1A3M4R7A2S7R7S8G4S3fR2A1A2A2A2A2A2A2Lp;A2Lc;A2S3S33VCST;R5A2S4S0S0S4S0S0S1G1S1G2S1G3S2S0R7S8S3dR3R2A2R1A2A3A2A2A2Lp;A2Lc;A2A2A2A2A2TF;F_;F_;Fm;Fa;FA;").
Proof.
  intros A a m HF Hcl F.
  destruct Hcl as [[S|[L|[FR|C]]]|FL].
  - left. exact S.
  - right; left. exact L.
  - right; right; left. destruct FR as (f & s & Hin & Ha).
    destruct (aa_frames_fact _ A _ _ HF Hin) as (c & p & u & v & Hc & -> & Eb & _ & Hp & -> & _).
    exists c, p. split; [exact Hc|]. split; [exact Hp|]. split; [eapply busyb_of_split; exact Eb | exact Ha].
  - right; right; right; left. exact C.
  - right; right; right; right. destruct FL as ([f s] & Hin & ->).
    destruct (aa_frames_fact _ A _ _ HF Hin) as (c & p & u & v & Hc & Hs & Eb & _ & Hp & Hf & _). cbn [fst snd] in Hs, Hf.
    exists c, p. split; [exact Hc|]. split; [exact Hp|]. split; [eapply busyb_of_split; exact Eb |].
    unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. rewrite Hs, fs_class_of_size_ok by lia. fold F. rewrite Hf, fs_pos_frame by lia. reflexivity.
Qed.

Lemma client_addr_bounds : ltac2:(tb__ "0|0|
SeS0S2eS38SfR3A1A1S37R2R4A2S39R5A1S45VCST;R6R5A3S1S1S6Z0R6A2S7R6SaZ2Z2fA2A2A2S3S7R6Z7fff7000A2S6S8Z10007fff8000Z10A2R6A2A2A2F_;F_;F_;F_;Fm;Fa;FA;").
Proof.
  intros A a m HG HF Hsep Hcl.
  pose proof (geom_nums _ HG) as (F1 & F2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG). rewrite FS_total_val in F2.
  pose proof (proj1 (geom_bands _ HG)) as WB. rewrite FS_total_val in WB.
  unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  destruct (client_addr_cases A a m HF Hcl) as [S|[L|[FR|[C|FL]]]].
  - clear WB. lia.
  - clear WB. destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & S3 & _ & _ & _ & _ & S8).
    unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
  - destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold IMG_HI in M. lia.
  - clear WB. destruct (HCST _ C) as [X _]. unfold IMG_LO, IMG_HI in *. lia.
  - destruct FL as (c & p & Hc & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *.
    unfold IMG_HI in M. lia.
Qed.

Lemma client_shadow_bounds : ltac2:(tb__ "0|0|
SeS0S2eS38SfR3A1A1S37R2R4A2S39R5A1S46VCST;VXGL;R6R5A4S1S6S43R6A2S7R6S41A2A2F_;F_;F_;F_;Fm;Fa;FA;").
Proof.
  intros A a m HG HF Hsep [(x & Hx & ->)|(x & Hx & ->)].
  - destruct (client_addr_bounds A x m HG HF Hsep Hx) as [B _]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. lia.
  - destruct (HXGL x Hx). unfold Sh, SHADOW_OFF, HIGH_SHADOW_END, IMG_HI in *. lia.
Qed.

Definition rt_zone (G : ageom) (a : Z) : Prop := ltac2:(tb__ "0|5|
S3S1S1S6Z0Va;A2S7Va;S42A2A2S2S1eS32S34S31S30A2Va;A2S24A3A2S3S1S6S1cVG;A1M0Va;A2S7Va;S8G0Z1000M1A2A2A2S3S1S6S1aVG;A1M2Va;A2S7Va;S8G2G1A2A2A2S3S1S6S1bVG;A1M3Va;A2S7Va;S8G3G1A2A2A2S1S6S12VG;A1M4Va;A2S7Va;S8G4Z61A2A2A2A2A2A2A2").

Lemma client_not_rt : ltac2:(tb__ "0|0|
SeS0S2eS38SfR3A1A1S37R2R4A2S39R5A1S45VCST;R6R5A3S5S4bSfR7A1R6A2A1F_;F_;F_;F_;Fm;Fa;FA;").
Proof.

  intros A a m HG HF Hsep Hcl Hrt.
  pose proof (geom_nums _ HG) as (F1 & F2 & F0 & T1 & T2 & T0 & C1 & C2 & D1 & D2 & SP1 & SP2 & SP0 & TG).
  rewrite FS_total_val, kSpaceSize_val in *. unfold IMG_HI in F1.
  unfold rt_zone, IMG_HI in Hrt.
  destruct (client_addr_cases A a m HF Hcl) as [S|[L|[FR|[C|FL]]]].
  - lia.
  - destruct L as (b & n & Hbn & Hx). destruct (Hsep b n Hbn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & _). rewrite FS_total_val in S4.
    unfold IMG_HI in S2. lia.
  - destruct FR as (c & p & Hc & Hp & _ & Hx). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M.
    pose proof (geom_seps _ HG) as (Q1 & Q2 & Q3 & _). rewrite FS_total_val in Q1, Q2, Q3. lia.
  - destruct (HCST _ C) as [X Y]. unfold IMG_LO, IMG_HI in X. destruct Hrt as [[_ R]|R]; [rewrite R in Y; discriminate|].
    pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & DI). unfold IMG_LO, IMG_HI in TI, CI, DI. lia.
  - destruct FL as (c & p & Hc & Hp & _ & ->). pose proof (fs_geom_nums (aa_geom A) c p HG Hc Hp) as M. cbn zeta in M.
    rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. unfold fs_flags in *. rewrite FS_kFlagsOffset_val in *.
    pose proof (geom_seps _ HG) as (Q1 & Q2 & Q3 & _). rewrite FS_total_val in Q1, Q2, Q3. lia.
Qed.

Lemma sm_rebuild : ltac2:(tb__ "0|11|
S0SeS2cS2cS1fS4aQ40M0A1M1A1S4fS0G1S1S6Z0M2R8A2S7R8ZbA2A2VAInv;R8R7R5R4A4S1S6G2R4A2S7R4S40RaA1A2A2S2S1eS36RaRbR5A3S27A3SfRbA1S17S12R1A1S0S3eR1ReR8A3S0S8S3dR2RfA2R9A2S0S3fR10A1S0S44R4R11A2S0S2fVsegs;S2bRfA1A2S2eS2fVsegs;S2bR11A1A2S2eS2S2aS4aQ8M3A1M4A1M5R2R5A1S25G4S49G3Z1A2A2A3S0S1S6S3cR8A1M6R1A2S7R1S8G6S9R6Z8M7A2A2A2A2S2G5R5R2A1S25G4S49G3G2A2M8A2A3F_;Fz;S29S3bR1U8M9A2S2G5R6S8R7SdR2A1A2A1S25G4S4eG4R2S2dG9R11A2G8A4A2A3F_;Fj;S0S5S3S1S6R7R1A2S7R1S8R7G7A2A2A2S3S2S0R1R9A3S1S6S3cRaA1MaR1A2S7R1S8GaS9R8G7A2A2A2A2A2A2A1S2G5R7R2A1R6R2A1A3F_;Fz;S0S1S6G2R1A2S7R1SaZ2Z40A2A2A2S5S3S1S6R9R2A2S7R2S8R9G7A2A2A2S3S2S0R2RbA3S1S6S3cRcA1MbR2A2S7R2S8GbS9RaG7A2A2A2A2A2A2A1S5S4bRfR3A2A1S2G5S2bR19S49G0R4A2McA2S2bR1aGcA2A3F_;F_;F_;Fa;S4SeSeS4S1fS21S0S0A2MdA1MeGeS4GeGeS1VAInv;R3R19R18R17A4S1S2GeS11R3A1S11R1bA1A3S1S2GeS16R1bA1S22GdR2R1A3A3S1S2GeS16R3A1S22GdR2S23GdS20S0S0ReRcA4MfR1A3A3A3S1S2S0RdS47SfR1bA1M10GfA2A3S1S2S0S15R3A1S15R1bA1A3S1S2S0S14R3A1S14R1bA1A3S1S2S0S13R3A1S13R1bA1A3S1S2S17SfR3A1G10A3S48VCST;VXGL;R1bR3S2bR1aA1S2bR19A1A6A2A2A2A2A2A2A2A2A2Ll2;A2Ll1;A2LA';A2F_;F_;F_;F_;F_;TvE;Tv3;Thc;TS;Tfl;Tff;TF;TG;F_;F_;F_;F_;Fhw;Fpos;Fmd;Ftp;Frho3;FrhoE;FA;Fc;").
Proof.
  intros c A rhoE rho3 tp md pos hw Hc HA Hpos Hfree G F ff fl S hc v3 vE VF VS VH VO RMO.
  subst G.
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof (fs_geom_nums (aa_geom A) c pos HG Hc Hpos) as NUM. cbn zeta in NUM. fold F ff S in NUM.
  destruct NUM as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10). fold fl in N6, N7.
  pose proof (topG_range (aa_geom A)) as TG. pose proof (proj1 (geom_bands _ HG)) as WB. fold F in WB.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in *. unfold IMG_HI in N8. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB.
  assert (SZ8 : 0 <= S / 8) by (apply Z.div_pos; lia).
  assert (ShF : Sh (F + 36864) <= Sh ff) by (apply Sh_mono; lia).
  assert (ShE : Sh ff + S / 8 <= Sh (F + 11571200)).
  { unfold Sh. replace (ff / 8 + SHADOW_OFF + S / 8) with ((ff + S) / 8 + SHADOW_OFF).
    - apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
    - replace ff with (ff / 8 * 8) at 1 by (pose proof (Z.div_mod ff 8); pose proof (Z.mod_divide ff 64); lia).
      rewrite Z.div_add_l by lia. lia. }
  assert (ShLo : 0x800b7600 <= Sh (F + 36864)) by (unfold Sh, SHADOW_OFF; lia).
  assert (ShHi : Sh (F + 11571200) < 17594333495296) by (unfold Sh, SHADOW_OFF; lia).
  assert (HCR : F <= hc /\ hc + 8 <= F + 88) by (unfold hc, fs_hint_cell; fold F; lia).

  assert (SHRT : forall a, 2147450880 <= a < 17594333495296 -> ~ rt_zone (aa_geom A) a).
  { intros a Ha. pose proof (geom_bands _ HG) as (BF & BT & BC & BD & _). fold F in BF.
    rewrite FS_total_val in BF. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in BF, BT, BC, BD.
    unfold rt_zone, IMG_HI. fold F. intros [R|[R|[R|[R|R]]]]; [clear -Ha R; lia | clear -Ha R BT; lia | clear -Ha R BC; lia | clear -Ha R BD; lia | clear -Ha R BF; lia]. }
  destruct HF as (Flen & Fcls & Fhint & Fflags & Ffree & Fsh).
  fold F vE in Fhint, Fflags, Ffree, Fsh. rewrite FS_frames_off_val, FS_total_val in Fsh.
  assert (Hlenc : (Z.to_nat c < length (aa_fs_busy A))%nat) by (rewrite Flen; lia).
  assert (Hlenh : (Z.to_nat c < length (aa_fs_hint A))%nat) by (rewrite (proj1 Fhint); lia).

  set (h := bv_unsigned hw). pose proof (urange hw) as Hh. fold h in Hh.
  set (A' := fs_alloc A c pos ff h).
  assert (HB : nth_error (aa_fs_busy A) (Z.to_nat c) = Some (fs_busy A c)).
  { unfold fs_busy, nthZ. apply nth_error_nth'. exact Hlenc. }
  destruct (frames_of_insert (aa_fs_busy A) 0 (Z.to_nat c) (fs_busy A c) pos ff HB) as (l1 & l2 & E1 & E2).
  rewrite Z.add_0_l, Z2Nat.id in E2 by lia.
  assert (EBc : forall c0, 0 <= c0 -> fs_busy A' c0 = if c0 =? c then (pos, ff) :: fs_busy A c else fs_busy A c0).
  { intros c0 Hc0. apply fs_busy_alloc; lia. }
  assert (EBB : forall c0 p0, 0 <= c0 -> busyb A' c0 p0 = busyb A c0 p0 || ((c0 =? c) && (p0 =? pos))).
  { intros c0 p0 Hc0. unfold busyb. rewrite EBc by lia. destruct (Z.eqb_spec c0 c).
    - subst c0. cbn [existsb fst]. rewrite (Z.eqb_sym pos p0). destruct (p0 =? pos); cbn; [rewrite orb_true_r|rewrite orb_false_r]; reflexivity.
    - cbn [andb]. rewrite orb_false_r. reflexivity. }
  assert (Hnotin : ~ In pos (map fst (fs_busy A c))).
  { intros Hin. apply in_map_iff in Hin as ([p g] & E & Hin). cbn in E. subst p.
    unfold busyb in Hfree. assert (X : existsb (fun pf : Z * Z => fst pf =? pos) (fs_busy A c) = true); [|rewrite X in Hfree; discriminate].
    apply existsb_exists. exists (pos, g). split; [exact Hin | cbn; apply Z.eqb_refl]. }

  assert (HF' : fs_inv (restrictv (fs_footb (aa_geom A)) v3) A').
  { split; [|split; [|split; [|split; [|split]]]].
    - unfold A', fs_alloc. cbn [aa_fs_busy]. rewrite length_list_upd. exact Flen.
    - intros c0 Hc0. change (aa_geom A') with (aa_geom A). fold F. rewrite EBc by lia. destruct (Z.eqb_spec c0 c).
      + subst c0. destruct (Fcls c Hc) as [Hnd Hpf]. split.
        * cbn [map fst]. constructor; [exact Hnotin | exact Hnd].
        * intros pf [<-|Hin]; [cbn [fst snd]; split; [exact Hpos | reflexivity] | exact (Hpf pf Hin)].
      + exact (Fcls c0 Hc0).
    - change (aa_geom A') with (aa_geom A). fold F. destruct Fhint as [Hhl Fhint]. split.
      + unfold A', fs_alloc. cbn [aa_fs_hint]. rewrite length_list_upd. exact Hhl.
      + intros c0 Hc0. unfold A'. rewrite fs_hint_alloc by (unfold FS_NCLASSES in Hc0; lia). unfold FS_NCLASSES in Hc0.
        destruct (Z.eqb_spec c0 c).
        * subst c0. split; [exact Hh|]. intros k Hk. cbn [c_addr c_w c_val] in Hk |- *. fold hc.
          unfold restrictv. rewrite fs_footb_true1 by (fold F; lia). rewrite (VH k Hk). unfold h. rewrite Z_to_bv_bv_unsigned. reflexivity.
        * destruct (Fhint c0 Hc0) as [Hhr Hhc]. split; [exact Hhr|]. intros k Hk. specialize (Hhc k Hk).
          cbn [c_addr c_w c_val] in Hk, Hhc |- *. unfold fs_hint_cell in *.
          unfold restrictv in Hhc |- *. rewrite fs_footb_true1 in Hhc by (fold F; lia). rewrite fs_footb_true1 by (fold F; lia).
          rewrite VO by (unfold hc, fs_hint_cell; unfold Sh, SHADOW_OFF in *; lia). exact Hhc.
    - change (aa_geom A') with (aa_geom A). fold F. intros c0 p0 Hc0 Hp0. rewrite EBB by lia.
      pose proof (fs_geom_nums (aa_geom A) c0 p0 HG Hc0 Hp0) as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. destruct M as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
      unfold restrictv. rewrite fs_footb_true2 by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia).
      destruct (Z.eqb_spec c0 c); [destruct (Z.eqb_spec p0 pos)|].
      + subst c0 p0. rewrite Hfree. cbn [andb orb]. fold fl. exact VF.
      + cbn [andb]. rewrite orb_false_r.
        assert (fs_flags F c0 + p0 <> fl) by (intros E; destruct (fs_flags_inj F c0 p0 c pos Hc0 Hp0 Hc Hpos E); lia).
        rewrite VO by (unfold Sh, SHADOW_OFF in *; lia).
        specialize (Fflags c0 p0 Hc0 Hp0). unfold restrictv in Fflags.
        rewrite fs_footb_true2 in Fflags by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). exact Fflags.
      + cbn [andb]. rewrite orb_false_r.
        assert (fs_flags F c0 + p0 <> fl) by (intros E; destruct (fs_flags_inj F c0 p0 c pos Hc0 Hp0 Hc Hpos E); lia).
        rewrite VO by (unfold Sh, SHADOW_OFF in *; lia).
        specialize (Fflags c0 p0 Hc0 Hp0). unfold restrictv in Fflags.
        rewrite fs_footb_true2 in Fflags by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). exact Fflags.
    - change (aa_geom A') with (aa_geom A). fold F. intros c0 p0 Hc0 Hp0 Hfree0 z Hz. rewrite EBB in Hfree0 by lia.
      apply orb_false_elim in Hfree0 as [Hfree0 Hne].
      pose proof (fs_geom_nums (aa_geom A) c0 p0 HG Hc0 Hp0) as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. destruct M as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & _).
      unfold restrictv. rewrite fs_footb_true2 by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia).
      rewrite VO by (unfold Sh, SHADOW_OFF in *; lia).
      specialize (Ffree c0 p0 Hc0 Hp0 Hfree0 z Hz). unfold restrictv in Ffree.
      rewrite fs_footb_true2 in Ffree by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). exact Ffree.
    - change (aa_geom A') with (aa_geom A). fold F. rewrite FS_frames_off_val, FS_total_val. intros z Hz.
      unfold restrictv. rewrite fs_footb_true3 by (fold F; rewrite FS_frames_off_val, FS_total_val; lia).
      destruct (Z_le_dec (Sh ff) z); [destruct (Z_lt_dec z (Sh ff + S / 8))|].
      1: exists (Z_to_bv 8 0); apply VS; lia.
      all: rewrite VO by (unfold Sh, SHADOW_OFF in *; lia); specialize (Fsh z Hz); unfold restrictv in Fsh;
           rewrite fs_footb_true3 in Fsh by (fold F; rewrite FS_frames_off_val, FS_total_val; lia); exact Fsh. }
  assert (HA' : AInv A' rho3 tp md).
  { apply (AInvA_fs_update segs A A' rhoE rho3 tp md HA).
    - unfold A', fs_alloc, same_but_fs. cbn. repeat split; reflexivity.
    - intros z Hz. fold v3 vE. apply VO. intros [X|[X|X]].
      + rewrite fs_footb_true1 in Hz by (fold F; lia). discriminate.
      + rewrite fs_footb_true2 in Hz by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). discriminate.
      + rewrite fs_footb_true3 in Hz by (fold F; rewrite FS_frames_off_val, FS_total_val; lia). discriminate.
    - exact HF'. }
  assert (Efl : fl = frame_flag (aa_geom A) (ff, S)).
  { unfold frame_flag. cbn [fst snd]. unfold fs_flag_addr. unfold S. rewrite fs_class_of_size_ok by lia. fold F. unfold ff. rewrite fs_pos_frame by lia. reflexivity. }
  exists A', l1, l2.
  split; [exact HA'|]. split; [reflexivity|]. split; [exact E1|]. split; [unfold aa_frames; unfold A', fs_alloc; cbn [aa_fs_busy]; exact E2|].
  split; [exact Efl|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].

  pose proof (conj Flen (conj Fcls (conj Fhint (conj Fflags (conj Ffree Fsh))))) as HF.
  destruct HRest as (Hsep & _).
  assert (Hsep' : live_sep A') by exact Hsep.
  assert (HG' : geom_ok (aa_geom A')) by exact HG.
  assert (NOCL : forall x, ff <= x < ff + S -> ~ client_addrA CST A x).
  { intros x Hx Hcl. destruct (client_addr_cases A x _ HF Hcl) as [X|[L|[FR|[C|FL]]]].
    - lia.
    - destruct L as (b & n & Hbn & Hx'). destruct (Hsep b n Hbn) as (S1 & S2 & S3 & S4 & _). fold F in S4. rewrite FS_total_val in S4. unfold IMG_HI in S2. lia.
    - destruct FR as (c' & p' & Hc'' & Hp' & Hb' & Hx'). fold F in Hx'.
      assert (Hne : c' <> c \/ p' <> pos) by (destruct (Z.eq_dec c' c) as [->|]; [right; intros ->; rewrite Hfree in Hb'; discriminate | left; assumption]).
      destruct (fs_frames_disjoint F c' p' c pos Hc'' Hp' Hc Hpos Hne) as [D|D]; fold ff in D; [lia|].
      pose proof (fs_frame_size_pos c' ltac:(lia)). lia.
    - destruct (HCST x C) as [X _]. unfold IMG_LO, IMG_HI in X. lia.
    - destruct FL as (c' & p' & Hc'' & Hp' & _ & ->). fold F in Hx.
      pose proof (fs_geom_nums (aa_geom A) c' p' HG Hc'' Hp') as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. lia. }
  assert (NOFL : ~ client_addrA CST A fl).
  { intros Hcl. destruct (client_addr_cases A fl _ HF Hcl) as [X|[L|[FR|[C|FL]]]].
    - lia.
    - destruct L as (b & n & Hbn & Hx'). destruct (Hsep b n Hbn) as (S1 & S2 & S3 & S4 & _). fold F in S4. rewrite FS_total_val in S4. unfold IMG_HI in S2. lia.
    - destruct FR as (c' & p' & Hc'' & Hp' & Hb' & Hx'). fold F in Hx'.
      pose proof (fs_geom_nums (aa_geom A) c' p' HG Hc'' Hp') as M. cbn zeta in M. fold F in M.
      rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in M. lia.
    - destruct (HCST fl C) as [X _]. unfold IMG_LO, IMG_HI in X. lia.
    - destruct FL as (c' & p' & Hc'' & Hp' & Hb' & E). fold F in E.
      destruct (fs_flags_inj F c' p' c pos Hc'' Hp' Hc Hpos ltac:(unfold fl in E; lia)) as [-> ->]. rewrite Hfree in Hb'. discriminate. }
  assert (CHG_nocl : forall a, (hc <= a < hc + 8 \/ a = fl \/ Sh ff <= a < Sh ff + S / 8) -> client_addrA CST A a -> False).
  { intros a Ha Hcl. destruct Ha as [Ha|[->|Ha]]; [| exact (NOFL Hcl) |].
    - apply (client_not_rt A a _ HG HF Hsep Hcl). right; right; right; right. fold F. lia.
    - destruct (client_addr_bounds A a _ HG HF Hsep Hcl) as [B1 B2]. clear WB. unfold Sh, SHADOW_OFF in *. lia. }
  assert (CHG_nosh : forall a, (hc <= a < hc + 8 \/ a = fl \/ Sh ff <= a < Sh ff + S / 8) -> client_shadowA CST XGL A a -> False).
  { intros a Ha Hcs. pose proof (client_shadow_bounds A a _ HG HF Hsep Hcs) as B. unfold HIGH_SHADOW_END, SHADOW_OFF in B.
    destruct Ha as [Ha|[->|Ha]]; [lia|lia|].
    destruct Hcs as [(x & Cx & Ex)|(x & Gx & Ex)].
    - assert (ff <= x < ff + S).
      { subst a. unfold Sh in Ha. destruct (client_addr_bounds A x _ HG HF Hsep Cx) as [Bx _].
        pose proof (Z.div_mod ff 8). pose proof (Z.div_mod x 8). pose proof (Z.mod_pos_bound x 8). pose proof (Z.mod_pos_bound ff 8).
        assert (ff mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply (Z.divide_trans _ 64); [exists 8; reflexivity| apply Z.mod_divide; lia]).
        split; [first [ clear - Ha Bx H H0 H1 H2 H3; nia | nia ] |].
        destruct (Z_lt_dec x (ff + S)); [lia|].
        assert (Y : (ff + S) / 8 <= x / 8) by (apply Z.div_le_mono; lia).
        replace ff with (ff / 8 * 8) in Y at 1 by lia. rewrite Z.div_add_l in Y by lia. lia. }
      exact (NOCL x H Cx).
    - destruct (HXGL x Gx). unfold IMG_HI in *. subst a. unfold Sh, SHADOW_OFF in Ha. lia. }
  split.
  - intros a Ha Hcl.
    apply RMO; [exact Ha| |].
    + intros X. destruct Hcl as [[C1 _]|[C1 _]]; [exact (CHG_nocl a X C1) | exact (CHG_nosh a X C1)].
    + destruct Hcl as [[C1 _]|[C1 _]]; [exact (client_not_rt A a _ HG HF Hsep C1)|].
      pose proof (client_shadow_bounds A a _ HG HF Hsep C1) as B. unfold SHADOW_OFF, HIGH_SHADOW_END in B.
      exact (SHRT a B).
  - intros x j Hx Hj Hdef.
    assert (Bx : 0 <= x < 2 ^ 47 /\ SHADOW_OFF <= Sh x < HIGH_SHADOW_END).
    { destruct Hx as [[C1 C2]|GX].
      - destruct (client_addr_bounds A x _ HG HF Hsep C1) as [B _]. split; [exact B|]. unfold Sh, SHADOW_OFF, HIGH_SHADOW_END. lia.
      - destruct (HXGL x GX). unfold IMG_HI, Sh, SHADOW_OFF, HIGH_SHADOW_END in *. lia. }
    destruct Bx as [Bx SB]. unfold SHADOW_OFF, HIGH_SHADOW_END in SB.
    destruct (word_byte_range (Sh x) j ltac:(lia) Hj) as (W1 & W2 & W3).
    set (a := Sh x / 8 * 8 + j) in *.
    assert (A8 : (Sh x / 8 * 8) mod 8 = 0) by (apply Z_mod_mult).
    destruct (Z_le_dec (Sh ff) a); [destruct (Z_lt_dec a (Sh ff + S / 8))|].
    +
      pose proof (VS a ltac:(lia)) as X. unfold v3 in X. rewrite view_in in X by lia.
      assert (BW : 0x643000 <= a < 2 ^ 64) by (clear -W1 SB Hj; lia).
      pose proof (rd_off_image (rm rho3) _ _ BW X) as M.
      unfold word_byte. fold a. rewrite M. discriminate.
    + unfold word_byte. fold a. rewrite RMO; [exact Hdef | lia | | ].
      * intros [X|[X|X]]; [lia| lia | lia].
      * apply SHRT. lia.
    + unfold word_byte. fold a. rewrite RMO; [exact Hdef | lia | | ].
      * intros [X|[X|X]]; [lia| lia | lia].
      * apply SHRT. lia.
Qed.
End R.
