(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumC.v, with its module paths and module names changed; 1178 of its 1252 lines of code are new or changed and 854 lines of the source are left out. *)
(* CR-Z (a Theorem Labs lane's internal file PART7-ROWS.md row Z; image A', harness fix #102 pins): check_reject_clean_starved's segment Z,
   A' 0x82510 (+944) .. 0x8254c / 0x82410 / ABORT, stated against the frozen kit CrsKitAp.v. The walk:
     +944  bnez s7          -> ABORT refuted (s7 = 0, the injected pretty write's NULL);
     +948  jal fuzz_alloc_live; +952 bne a0, s6 -> ABORT refuted (a0 = lsum Lam = s6, crs_lsum_perm);
     +956  jal fuzz_alloc_count; +960 mv s7, a0 (= crs_cnt2); +964 mv a0, s3 (doc); +968 mv a1, zero;
     +972  jal pj_write (doc, 0): the compact whole write (HW_exact's call text crs_wcall, float form; its entry run
           events by crs_run_split + PRH_Supply.prhWriter_pjw_evs_w_evs, its consumer window prh_cons_from by the
           kit's crs_cons_sub; its post's prh_granted keeps g_ran_out at 0 (crs_ran_of_granted) and leaves the writer
           not failed (crs_wfull), so q is the text block; its exact advance under ran' = 0);
     +976  jal fuzz_free (q): q is the text block (tfuzz_free_specX: its fixed trace admitted by admits_ct_fix, its
           budgeted post read back by fpost_of_fpostb_fix; post-implication: its position step applied at the writer's
           exact advance with the run event from the kit's crs_room_evs_of_run; its p <> 0 class-24 bound from
           crs_cnt24_Z; its hull budget from the run's count, drv_cf_hull_ok_at_call_A); every call meets fpre's
           frm_zero (FRM0-ENTRY) from the boundary's crs_baseR; the walk runs at the re-hiding relation wle';
     +980  jal fuzz_alloc_count; +984 beq a0, s7 -> R refuted (the write made kk >= 1 calls, crs_kfull);
     +988  lbu a0, 540(s8): g_own_ran_out = 0, the boundary ledger's own cell (prh_ledger_own, kit v3);
           +992 bnez a0 -> R not taken;
     +996  jal fuzz_alloc_ran_out; +1000 bnez a0: a0 = g_ran_out = c_ran C = 0, so the RAN arm (to R) is refuted;
           -> H3 (+1004, crs_from_H3).
   The closing lemma crs_seg_Z takes the callee texts (with the interim crs_free0), the kit's CrsKeep, HB_took, HW_exact,
   the named premise crs_cnt24_Z, and the continuations crs_from_R / crs_from_H3, in a Theorem Labs lane's premise order. On the
   walk's kit no route of Z reaches R or a NULL free (nothing is refused), so the proof uses neither crs_free0 nor
   crs_from_R; the statement keeps both (the kit's lane shape Z: crs_from_R -> crs_from_H3 -> crs_from_Z).
   Inputs: pin A' asan sha256 1be0f53d96cb9d6c... (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1);
   listing lib/A/Listing_prog.v blob 7ed1529926bd + lib/A/PAImg_prog.v blob 505a51ff7d08 (a Theorem Labs lane's #102 listings
   v3; entry 0x82160 = slot 736); the kit cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) by path, as on the walk's kit preset-tree-at-2026-10-30T06-59-32Z.tsv (sha256 09adbeae147a; internal record):
   PRH_FnCheck.v blob c40cf3fdcd2a (tcheck_reject_clean_starved_specX), PRH_FnAlloc.v 4d8aeba047e5, PRH_FnWriter.v
   d89d3c67b78c, PRH_Base.v ef7c8ca98529, PRH_Supply.v e9069249fade; kit CrsKitAp.v blob 4c07b375a294, CrsWexAp.v
   blob 8b5e3d0e730f (HW_exact), CrsFree0Ap.v blob 79d50622a638 (crs_free0), PRW_CrsModel.v blob 4d1e0e7dbb38. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvHullA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Supply.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_WalkEnv PRW_CrsModel PRW_CrcGen CrsKitAp CrsWexAp CrsFree0Ap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B PST ARx).
(* the walk's world relation: a free or a realloc of a live block may hide shadow again (wle' at the zone RZ_cf) *)
#[local] Notation WR := (wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_A) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_A)).

Definition DZ_SPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma dz_regs_ok_set : forall regs0 regsc (r : bv 5) e,
  sv_denot (TE regs0 regsc []) e = getr regsc r ->
  regs_ok (TE regs0 regsc []) (sr_set cur_atoms r e) regsc.
Proof.
intros regs0 regsc r e He r'.
destruct (bv_eqb r 0) eqn:Hr0.
- apply bv_eqb_eq in Hr0. subst r. unfold sr_set. rewrite bv_eqb_refl. apply te_regs_ok.
- destruct (bv_eqb r' r) eqn:Hrr.
  + apply bv_eqb_eq in Hrr. subst r'. rewrite sr_get_set_same by exact Hr0. symmetry. exact He.
  + assert (Hne : r' <> r) by (intros ->; rewrite bv_eqb_refl in Hrr; discriminate).
    rewrite sr_get_set_other by exact Hne. apply te_regs_ok.
Qed.

Lemma dz_seat : forall regs0 regsc pc sr (Wc : world SEGS) memc (fxk : YK11.FPState),
  regs_ok (TE regs0 regsc []) sr regsc ->
  @st_ok_pi SEGS VAL fxk (TE regs0 regsc []) (mkSS pc sr [] None (mkFacts [] [] []))
    (restrict (w_H Wc) (@YK11.mkst fxk regsc (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))).
Proof.
intros regs0 regsc pc sr Wc memc fxk Hr.
apply (@ts_st_ok fxk rc regs0 regsc [] pc sr [] (mkFacts [] [] []) Wc memc Hr).
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.

(* a run that writes no region leaves the whole memory as it was *)
Lemma dz_mem_nil : forall E (m m' : word -> option byte), frame_of E [] m m' -> m' = m.
Proof. intros E m m' H. apply functional_extensionality. intros x. apply H. intros (r & Hr & _). destruct Hr. Qed.

(* the read-only view at any state of the function's journal is the entry's (image clause, FP = []) *)
Lemma dz_rod : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly S Hp W mem md k,
  crs_pre B ARx CTX0 C -> crs_JR (SK := SK) B ARx R C ly S Hp W mem md k ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem).
Proof.
intros R CTX0 C ly S Hp W mem md k HP HJ.
destruct HP as ((_ & HROD0 & _) & _).
unfold crs_JR in HJ. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
intros a Hro Hown Herr. rewrite (Himg a); [apply HROD0; assumption | | exact Hown | exact Herr | |].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
- intros Hpst. exact (S1ImgA.pst_not_ro_A a Hpst Hro).
- intros (r & Hr & _). destruct Hr.
Qed.

(* a frame-pointer chain read through a reader that agrees on [bp - 16, top) *)
Lemma dz_fpchain_agree : forall (rd rd' : reader) top ch bp,
  fpchain (rdword rd) bp top ch ->
  (forall a, bp - 16 <= a < top -> rd' a = rd a) ->
  bp < top ->
  fpchain (rdword rd') bp top ch.
Proof.
intros rd rd' top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc Hag Hbt.
- destruct Hc as (r & Hr & Hr0). exists r. split; [|exact Hr0].
  unfold rdword in Hr |- *. rewrite !Hag by lia. exact Hr.
- cbn [fpchain] in Hc |- *. destruct Hc as (-> & Hal & Hra & Hnfp & H4096 & Hrest).
  assert (Ew : forall x, bp - 16 <= x -> x + 8 <= bp -> rdword rd' x = rdword rd x)
    by (intros x Hx1 Hx2; unfold rdword; rewrite !Hag by lia; reflexivity).
  split; [reflexivity|]. split; [exact Hal|]. split; [rewrite Ew by lia; exact Hra|].
  split; [rewrite Ew by lia; exact Hnfp|]. split; [exact H4096|].
  destruct (bad_next bp top nfp) eqn:Hb; [exact Hrest|].
  unfold bad_next in Hb. apply orb_false_iff in Hb as [Hb H3]. apply orb_false_iff in Hb as [H1 H2].
  apply Z.leb_gt in H1. apply Z.leb_gt in H2.
  apply IH; [exact Hrest | intros a Ha; apply Hag; lia | lia].
Qed.

(* the chain at a call from the body: s0 = the entry sp, whose record holds the entry ra and s0 (the prologue's saves),
   then the entry chain *)
Definition dz_ch (C : crsC) (ly : alayout) : list (Z * Z * Z) :=
  if spZ (c_regs C) <? ly_top ly - 16 then (spZ (c_regs C), raZ (c_regs C), s0Z (c_regs C)) :: c_ch C else [].

Lemma dz_chain : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly S Hp W mem md k sp2,
  crs_pre B ARx CTX0 C -> crs_JR (SK := SK) B ARx R C ly S Hp W mem md k -> crs_saved C W mem ->
  sp2 + 128 <= spZ (c_regs C) ->
  achain ly (aview SEGS (w_H W) mem) sp2 (spZ (c_regs C)) (dz_ch C ly).
Proof.
intros R CTX0 C ly S Hp W mem md k sp2 HP HJ HSV Hsp2.
pose proof asan_consts as (C1 & _).
destruct HP as (((HAR0 & Hra0 & Hra4 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & _) & _) & _).
unfold crs_JR in HJ.
destruct HJ as (_ & Hle & _ & _ & _ & _ & _ & _ & Hkeep & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Etop : ly_top ly = ly_top (c_ly C)) by (destruct Hle as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
assert (HSTKv : @STK_check_reject_clean_starved prh_img_A = 27312) by (vm_compute; reflexivity).
unfold dz_ch. set (sp0 := spZ (c_regs C)) in *.
destruct (Z.ltb_spec sp0 (ly_top ly - 16)) as [Hlt|Hge].
2: { left. split; [right; left; lia | reflexivity]. }
unfold crs_saved, CRS_SAVED in HSV.
inversion HSV as [|? ? Hsra HSV1]; subst. inversion HSV1 as [|? ? Hss0 _]; subst.
cbn [fst snd] in Hsra, Hss0. fold sp0 in Hsra, Hss0.
replace (sp0 - 128 + 120) with (sp0 - 8) in Hsra by lia.
replace (sp0 - 128 + 112) with (sp0 - 16) in Hss0 by lia.
right. split; [lia|]. split; [exact Hlt|]. split; [rewrite Z.mod_divide by lia; rewrite Z.mod_divide in Hal16 by lia; destruct Hal16 as [q Hq]; exists (2 * q); lia|].
split.
- cbn [fpchain]. split; [reflexivity|]. split; [rewrite Z.mod_divide by lia; rewrite Z.mod_divide in Hal16 by lia; destruct Hal16 as [q Hq]; exists (2 * q); lia|].
  split; [exact Hsra|]. split; [exact Hss0|]. split; [exact Hra4|].
  destruct (bad_next sp0 (ly_top ly) (s0Z (c_regs C))) eqn:Hb.
  + destruct Hch0 as [(Hc & ->) | (H1 & H2 & H3 & H4 & H5)]; [reflexivity|].
    exfalso. unfold bad_next in Hb. rewrite Etop in Hb.
    apply orb_true_iff in Hb as [Hb | Hb]; [apply orb_true_iff in Hb as [Hb | Hb]|].
    * apply Z.leb_le in Hb. fold sp0 in H1. lia.
    * apply Z.leb_le in Hb. lia.
    * rewrite H3 in Hb. discriminate.
  + unfold bad_next in Hb. apply orb_false_iff in Hb as [Hb H3]. apply orb_false_iff in Hb as [H1 H2].
    apply Z.leb_gt in H1. apply Z.leb_gt in H2. apply negb_false_iff in H3. apply Z.eqb_eq in H3.
    destruct Hch0 as [(Hc & Hnil) | (G1 & G2 & G3 & G4 & G5)].
    * exfalso. rewrite Etop in H2. fold sp0 in H1. destruct Hc as [Hc | [Hc | Hc]]; lia.
    * rewrite Etop. apply (dz_fpchain_agree (aview SEGS (w_H (c_W C)) (c_mem C))); [exact G4| |lia].
      intros a Ha. apply Hkeep; [|fold sp0 in G1; lia]. split; [fold sp0 in G1; lia | lia].
- constructor; [cbn [fst]; lia|].
  destruct Hch0 as [(_ & ->) | (G1 & G2 & G3 & G4 & G5)]; [constructor|].
  eapply Forall_impl; [|exact G5]. intros r Hr. cbv beta in Hr. fold sp0 in Hr. lia.
Qed.

(* the registers a call keeps (aregs_preserved: sp, gp, tp, s0 - s11) *)
Lemma dz_regsat_pres : forall regs regs2 (l : list (bv 5 * Z)),
  crs_regsat regs l -> aregs_preserved regs regs2 ->
  forallb (fun p => let r := bv_unsigned (fst p) in
    (r =? 2) || (r =? 3) || (r =? 4) || (r =? 8) || (r =? 9) || ((18 <=? r) && (r <=? 27))) l = true ->
  crs_regsat regs2 l.
Proof.
intros regs regs2 l H HP Hl. unfold crs_regsat in *. rewrite Forall_forall in H |- *.
rewrite forallb_forall in Hl. intros [r v] Hin. pose proof (H (r, v) Hin) as Hrv. cbn [fst snd] in Hrv |- *.
rewrite <- Hrv. specialize (Hl (r, v) Hin). cbv beta in Hl. cbn [fst] in Hl.
pose proof (HP (bv_unsigned r)) as E. rewrite Z_to_bv_bv_unsigned in E. apply E.
unfold acallee_saved. repeat rewrite orb_true_iff in Hl. rewrite andb_true_iff, !Z.eqb_eq, Z.leb_le, Z.leb_le in Hl. lia.
Qed.

(* the flat_map of a chain's return addresses is the flat_map of its spine *)
Lemma dz_fm_spine : forall pc0 (ch : list (Z * Z * Z)),
  flat_map (fun r => match r with (_, ra, _) => if ra =? pc0 then [] else [ra] end) ch =
  flat_map (fun ra => if ra =? pc0 then [] else [ra]) (spine ch).
Proof. intros pc0 ch. induction ch as [|[[fp ra] nfp] rest IH]; [reflexivity|]. cbn [flat_map spine map fst snd]. rewrite IH. reflexivity. Qed.

(* the trace of Z's fuzz_free call (return site +980) is in the universe: prh_univ_closure at the function's observed
   context (crs_pre's prh_ctx), or its literal / entry traces when the chain is empty *)
Lemma dz_trace_free : forall CTX0 C ly regs,
  crs_pre B ARx CTX0 C ->
  s0Z regs = spZ (c_regs C) -> raZ regs = BASE + CRS_PC_Z + 36 ->
  In (call_trace ly (pc_free_ra0 (as_code B)) regs (dz_ch C ly)) (as_universe B).
Proof.
intros CTX0 C ly regs HP Hs0 Hra.
destruct HP as (_ & _ & HU & HCTX & _).
assert (Hr : In (raZ regs) (@pi_ret_sites prh_img_A F_check_reject_clean_starved RT_fuzz_free))
  by (rewrite Hra; vm_compute; right; right; left; reflexivity).
assert (Hfp : @pi_fp prh_img_A F_check_reject_clean_starved = true) by (vm_compute; reflexivity).
unfold call_trace. destruct (frame0_ok ly regs).
- unfold dz_ch. destruct (spZ (c_regs C) <? ly_top ly - 16).
  + replace (unwind_of_chain (pc_free_ra0 (as_code B))
      ((spZ regs, raZ regs, s0Z regs) :: (spZ (c_regs C), raZ (c_regs C), s0Z (c_regs C)) :: c_ch C))
      with (prh_trace (prh_pc0 B RT_fuzz_free) (raZ regs) (raZ (c_regs C) :: spine (c_ch C))).
    * exact (prh_univ_closure_site B CTX0 F_check_reject_clean_starved _ RT_fuzz_free (raZ regs) HU HCTX Hfp Hr).
    * unfold unwind_of_chain, prh_trace. cbn [prh_pc0]. rewrite (dz_fm_spine _ ((_, _, _) :: (_, _, _) :: c_ch C)).
      reflexivity.
  + replace (unwind_of_chain (pc_free_ra0 (as_code B)) [(spZ regs, raZ regs, s0Z regs)])
      with (prh_trace (prh_pc0 B RT_fuzz_free) (raZ regs) []) by reflexivity.
    exact (prh_univ_closure_lit B CTX0 F_check_reject_clean_starved RT_fuzz_free (raZ regs) HU Hr).
- destruct HU as (H1 & _). exact (H1 RT_fuzz_free).
Qed.

(* ONE CALL FROM THE BODY (aj_call_x_spR at the function's journal over a world relation R): the call state is the
   run's st_ok at the callee's entry; the callee's text is consumed through its fpre at the frame-pointer chain dz_ch,
   its run and its post's journal at a relation Rc inside R (wle for a text whose post keeps the plain journal); the
   continuation receives the journal composed to the post state, the callee's own journal, the kept registers and
   the text's Q *)
Lemma dz_call : forall (R : world SEGS -> world SEGS -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall (Rc : world SEGS -> world SEGS -> Prop), (forall W W', Rc W W' -> R W W') ->
  forall CTX0 C (fxk : YK11.FPState) (W : world SEGS) E ss ms mdc ly S Hp k sp2 retk STK1 FP1
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Qn : world SEGS -> config -> Prop),
  crs_pre (fx := fx) B ARx CTX0 C ->
  @st_ok SEGS fxk E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  crs_JR (SK := SK) B ARx R C ly S Hp W (ms_mem ms) mdc k ->
  crs_saved C W (ms_mem ms) ->
  spZ (ms_regs ms) = sp2 -> spZ (c_regs C) - CRS_FRAME <= sp2 -> sp2 <= spZ (c_regs C) - 128 -> sp2 mod 32 = 0 ->
  frm_zero (@YK11.fp_csr fxk) ->
  getr (ms_regs ms) 3 = getr (c_regs C) 3 -> getr (ms_regs ms) 4 = getr (c_regs C) 4 ->
  getr (ms_regs ms) 8 = w64 (spZ (c_regs C)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= STK1 -> STK1 + CRS_FRAME <= STK ->
  (fpre (PA := PA) B ARx STK1 ly S Hp W (ms_regs ms) (ms_mem ms) mdc (dz_ch C ly) ->
   SRrG SEGS Rc W (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
     (@apost_base_xR fxk rc SK SEGS B PST ARx Rc STK1 FP1 (ms_regs ms) ly S Hp W (ms_mem ms) mdc Q)) ->
  fp_sub_x B STK (spZ (c_regs C)) [] FP1 (c_ly C) (c_S C) [(CRS_CID, c_fpos C)] ly S ->
  (forall W2 ly2 S2 Hp2 regs2 mem2 md2 k1, R W W2 ->
     crs_JR (SK := SK) B ARx R C ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
     AJR R STK1 sp2 FP1 ly S Hp W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG SEGS R W2 (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + retk)) mem2 (YK11.seg_rom SEGS)) md2) Qn) ->
  SRrG SEGS R W (mkCfg ms mdc) Qn.
Proof.
intros R Rr Rt Rc HRc CTX0 C fxk W E ss ms mdc ly S Hp k sp2 retk STK1 FP1 Q Qn HP HS Hrv HJ HSV Hsp Hlo Hhi Hal Hfz0
  Hgp Htp Hs0 Hra Hrk Hrk2 HSTK1 HSTK1b Hcallee HF Hk.
pose proof asan_consts as (C1 & _).
assert (EB : BASE = 529888) by (vm_compute; reflexivity).
assert (EF : CRS_FRAME = 144) by (vm_compute; reflexivity).
assert (ES : @STK_check_reject_clean_starved prh_img_A = 27312) by (vm_compute; reflexivity).
pose proof HP as HP'. destruct HP' as (((_ & _ & _ & Hgp0 & Htp0 & _) & _) & _).
pose proof HJ as HJ'. unfold crs_JR in HJ'.
destruct HJ' as (_ & Hle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (Ehi : ly_stk_hi ly = ly_stk_hi (c_ly C))
  by (destruct Hle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi0 & _); exact Ehi0).
assert (Hs0Z : s0Z (ms_regs ms) = spZ (c_regs C))
  by (unfold s0Z; rewrite Hs0; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (HraZ : raZ (ms_regs ms) = BASE + retk) by (unfold raZ; rewrite Hra; rewrite unsigned_lit_small by lia; reflexivity).
eapply (SRrG_bind SEGS R Rt).
{ apply (aj_call_x_spR (fx := fxk) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) R Rr Rt W E ss ms STK (spZ (c_regs C)) []
    (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C) (c_W C) (c_mem C) (c_md C) [(CRS_CID, c_fpos C)] ly S Hp mdc k
    STK1 FP1
    (sp2 - spZ (c_regs C)) (Z_to_bv 64 (BASE + retk)) (dz_ch C ly) Q HS Hrv HJ).
  - rewrite Hsp. lia.
  - lia.
  - lia.
  - exact HSTK1.
  - lia.
  - rewrite Hgp. exact Hgp0.
  - rewrite Htp. exact Htp0.
  - exact Hra.
  - apply (ret_ok_codeptr_v (PI := PA)); [exact Hrk | exact Hrk2].
  - rewrite unsigned_lit_small by lia. lia.
  - rewrite Hs0Z. replace (spZ (c_regs C) + (sp2 - spZ (c_regs C))) with sp2 by lia.
    exact (dz_chain R CTX0 C ly S Hp W (ms_mem ms) mdc k sp2 HP HJ HSV ltac:(lia)).
  - (* the callee's run and its post's journal at Rc lift to R *)
    intros HPRE1 HI T HK. refine (Hcallee _ HI T _).
    + split; [exact HPRE1|]. split; [exact (dz_rod R CTX0 C ly S Hp W (ms_mem ms) mdc k HP HJ)|].
      split; [rewrite Hsp, Ehi; lia|]. split; [rewrite HraZ; lia | exact Hfz0].
    + intros W' c' Hr HI' (ly' & S' & Hp' & regs' & mem' & md' & k' & Hc & HJ1 & Hpr & HQ).
      apply (HK W' c' (HRc _ _ Hr) HI'). exists ly', S', Hp', regs', mem', md', k'. split; [exact Hc|].
      split; [exact (ajournal_xwR_mono (SK := SK) SEGS B PST ARx Rc R HRc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] HJ1)|].
      split; [exact Hpr | exact HQ].
  - exact HF. }
cbv beta. intros W2 c2 Hle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HPr & HQ).
replace (spZ (c_regs C) + (sp2 - spZ (c_regs C))) with sp2 in HJc by lia.
exact (Hk W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle2 HJ2 HJc HPr HQ).
Qed.

(* dz_call for a callee whose text posts in the FLOAT form (apost_base_xFR: pj_write reaches put_string's snprintf,
   PRH_FnWriter.v's header): aj_call_xF_spR; the continuation runs at the callee's float state fx' (frm back to 0,
   fs0-fs11 kept) *)
Lemma dz_callF : forall (R : world SEGS -> world SEGS -> Prop), (forall W, R W W) ->
  (forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
  forall (Rc : world SEGS -> world SEGS -> Prop), (forall W W', Rc W W' -> R W W') ->
  forall CTX0 C (fxk : YK11.FPState) (W : world SEGS) E ss ms mdc ly S Hp k sp2 retk STK1 FP1
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Qn : world SEGS -> config -> Prop),
  crs_pre (fx := fx) B ARx CTX0 C ->
  @st_ok SEGS fxk E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  crs_JR (SK := SK) B ARx R C ly S Hp W (ms_mem ms) mdc k ->
  crs_saved C W (ms_mem ms) ->
  spZ (ms_regs ms) = sp2 -> spZ (c_regs C) - CRS_FRAME <= sp2 -> sp2 <= spZ (c_regs C) - 128 -> sp2 mod 32 = 0 ->
  frm_zero (@YK11.fp_csr fxk) ->
  getr (ms_regs ms) 3 = getr (c_regs C) 3 -> getr (ms_regs ms) 4 = getr (c_regs C) 4 ->
  getr (ms_regs ms) 8 = w64 (spZ (c_regs C)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  0 <= STK1 -> STK1 + CRS_FRAME <= STK ->
  (fpre (PA := PA) B ARx STK1 ly S Hp W (ms_regs ms) (ms_mem ms) mdc (dz_ch C ly) ->
   SRrG SEGS Rc W (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
     (@apost_base_xFR fxk rc SK SEGS B PST ARx Rc STK1 FP1 (ms_regs ms) ly S Hp W (ms_mem ms) mdc Q)) ->
  fp_sub_x B STK (spZ (c_regs C)) [] FP1 (c_ly C) (c_S C) [(CRS_CID, c_fpos C)] ly S ->
  (forall (fx' : YK11.FPState) W2 ly2 S2 Hp2 regs2 mem2 md2 k1, R W W2 ->
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     crs_JR (SK := SK) B ARx R C ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
     AJR R STK1 sp2 FP1 ly S Hp W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG SEGS R W2 (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (YK11.seg_rom SEGS)) md2) Qn) ->
  SRrG SEGS R W (mkCfg ms mdc) Qn.
Proof.
intros R Rr Rt Rc HRc CTX0 C fxk W E ss ms mdc ly S Hp k sp2 retk STK1 FP1 Q Qn HP HS Hrv HJ HSV Hsp Hlo Hhi Hal Hfz0
  Hgp Htp Hs0 Hra Hrk Hrk2 HSTK1 HSTK1b Hcallee HF Hk.
pose proof asan_consts as (C1 & _).
assert (EB : BASE = 529888) by (vm_compute; reflexivity).
assert (EF : CRS_FRAME = 144) by (vm_compute; reflexivity).
assert (ES : @STK_check_reject_clean_starved prh_img_A = 27312) by (vm_compute; reflexivity).
pose proof HP as HP'. destruct HP' as (((_ & _ & _ & Hgp0 & Htp0 & _) & _) & _).
pose proof HJ as HJ'. unfold crs_JR in HJ'.
destruct HJ' as (_ & Hle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (Ehi : ly_stk_hi ly = ly_stk_hi (c_ly C))
  by (destruct Hle as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi0 & _); exact Ehi0).
assert (Hs0Z : s0Z (ms_regs ms) = spZ (c_regs C))
  by (unfold s0Z; rewrite Hs0; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (HraZ : raZ (ms_regs ms) = BASE + retk) by (unfold raZ; rewrite Hra; rewrite unsigned_lit_small by lia; reflexivity).
eapply (SRrG_bind SEGS R Rt).
{ apply (aj_call_xF_spR (fx := fxk) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) R Rr Rt W E ss ms STK (spZ (c_regs C)) []
    (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C) (c_W C) (c_mem C) (c_md C) [(CRS_CID, c_fpos C)] ly S Hp mdc k
    STK1 FP1
    (sp2 - spZ (c_regs C)) (Z_to_bv 64 (BASE + retk)) (dz_ch C ly) Q HS Hrv HJ).
  - rewrite Hsp. lia.
  - lia.
  - lia.
  - exact HSTK1.
  - lia.
  - rewrite Hgp. exact Hgp0.
  - rewrite Htp. exact Htp0.
  - exact Hra.
  - apply (ret_ok_codeptr_v (PI := PA)); [exact Hrk | exact Hrk2].
  - rewrite unsigned_lit_small by lia. lia.
  - rewrite Hs0Z. replace (spZ (c_regs C) + (sp2 - spZ (c_regs C))) with sp2 by lia.
    exact (dz_chain R CTX0 C ly S Hp W (ms_mem ms) mdc k sp2 HP HJ HSV ltac:(lia)).
  - (* the callee's run and its post's journal at Rc lift to R *)
    intros HPRE1 HI T HK. refine (Hcallee _ HI T _).
    + split; [exact HPRE1|]. split; [exact (dz_rod R CTX0 C ly S Hp W (ms_mem ms) mdc k HP HJ)|].
      split; [rewrite Hsp, Ehi; lia|]. split; [rewrite HraZ; lia | exact Hfz0].
    + intros W' c' Hr HI' (fx1 & ly' & S' & Hp' & regs' & mem' & md' & k' & Hc & Hz & Hkf & HJ1 & Hpr & HQ).
      apply (HK W' c' (HRc _ _ Hr) HI'). exists fx1, ly', S', Hp', regs', mem', md', k'. split; [exact Hc|].
      split; [exact Hz|]. split; [exact Hkf|].
      split; [exact (ajournal_xwR_mono (SK := SK) SEGS B PST ARx Rc R HRc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [] HJ1)|].
      split; [exact Hpr | exact HQ].
  - exact HF. }
cbv beta. intros W2 c2 Hle2 (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ2 & HJc & HPr & HQ).
replace (spZ (c_regs C) + (sp2 - spZ (c_regs C))) with sp2 in HJc by lia.
exact (Hk fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hle2 HFZ HFK HJ2 HJc HPr HQ).
Qed.

(* the boundary at another float state: the rounding mode back at 0 and the callee-saved f registers kept *)
Lemma dz_base_fx : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C (fxk fxk' : YK11.FPState) ly S Hp W regs mem md
  k sp2,
  crs_baseR (fx := fx) (SK := SK) B ARx R CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  frm_zero (@YK11.fp_csr fxk') -> fregs_kept_x fxk fxk' ->
  crs_baseR (fx := fx) (SK := SK) B ARx R CTX0 C fxk' ly S Hp W regs mem md k sp2.
Proof.
intros R CTX0 C fxk fxk' ly S Hp W regs mem md k sp2 HB Hz Hk.
destruct HB as (HP & _ & Hfk & HR). split; [exact HP|]. split; [exact Hz|]. split; [|exact HR].
intros r Hr. rewrite (Hk r Hr). exact (Hfk r Hr).
Qed.

(* the hull of the 56-byte local at F + 32 lies in the frame's 16 shadow bytes (F 32-aligned, SHADOW_OFF 8-aligned) *)
Lemma dz_hull_arith : forall F s, F mod 32 = 0 ->
  shadow_addr (F + 32) / 8 * 8 <= s < shadow_addr (F + 32 + 56 - 1) / 8 * 8 + 8 ->
  shadow_addr F <= s < shadow_addr F + 16.
Proof.
intros F s HF Hs. unfold shadow_addr, SHADOW_OFF in *.
rewrite Z.mod_divide in HF by lia. destruct HF as [q ->].
assert (E1 : (q * 32 + 32) / 8 = 4 * q + 4)
  by (replace (q * 32 + 32) with ((4 * q + 4) * 8) by lia; apply Z.div_mul; lia).
assert (E2 : (q * 32 + 32 + 56 - 1) / 8 = 4 * q + 10)
  by (replace (q * 32 + 32 + 56 - 1) with ((4 * q + 10) * 8 + 7) by lia; rewrite Z.div_add_l by lia; change (7 / 8) with 0; lia).
assert (E3 : q * 32 / 8 = 4 * q) by (replace (q * 32) with ((4 * q) * 8) by lia; apply Z.div_mul; lia).
rewrite E1, E2 in Hs. rewrite E3.
pose proof (Z.div_mod (2147450880 + (4 * q + 4)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (2147450880 + (4 * q + 4)) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (2147450880 + (4 * q + 10)) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (2147450880 + (4 * q + 10)) 8 ltac:(lia)) as D4.
lia.
Qed.

(* THE BOUNDARY AFTER A CALL: the frame, the saved words and the local's shadow are kept by the callee's journal (its
   footprint misses the frame and its shadow), the read-only view by the function's own journal; the registers by
   aregs_preserved, memnorm by the callee's m-form post *)
Lemma dz_keep : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C (fxk : YK11.FPState) ly S Hp W regs mem md k sp2
  STK1 FP1 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 k1,
  crs_baseR (fx := fx) (SK := SK) B ARx R CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_JR (SK := SK) B ARx R C ly2 S2 Hp2 W2 mem2 md2 k2 ->
  AJR R STK1 sp2 FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, cF C <= a < cF C + 128 \/ shadow_addr (cF C) <= a < shadow_addr (cF C) + 16 -> ~ inFP FP1 a) ->
  aregs_preserved regs regs2 ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  crs_baseR (fx := fx) (SK := SK) B ARx R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 sp2.
Proof.
intros R CTX0 C fxk ly S Hp W regs mem md k sp2 STK1 FP1 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 k1
  HB HJ2 HJc HFP HPr HMN2.
pose proof asan_consts as (C1 & _).
assert (ES : @STK_check_reject_clean_starved prh_img_A = 27312) by (vm_compute; reflexivity).
assert (EF : CRS_FRAME = 144) by (vm_compute; reflexivity).
destruct HB as (HP & Hfz & Hfk & HJ & HFR & HSV & HSL & HROD & HMN & Hg3 & Hg4 & Hs1 & Hs2 & Hs3 & HDPk).
destruct (crs_cF_keepR B ARx LAWS R CTX0 C ly S Hp W mem md k HP HJ) as [EcF Efl].
destruct (crs_cF_keepR B ARx LAWS R CTX0 C ly2 S2 Hp2 W2 mem2 md2 k2 HP HJ2) as [EcF2 Efl2].
pose proof HJ as HJ'. unfold crs_JR in HJ'. destruct HJ' as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
destruct HJc as (HAR2 & _ & _ & _ & _ & Hfr1 & _ & _ & Hk9 & _ & _ & Hk12 & _).
destruct HFR as (Hfrm & Hflag & Hpres).
assert (Hin : In (CRS_CID, c_fpos C) (frames S)) by (rewrite Hfrm; left; reflexivity).
pose proof LAWS as HFRL. apply alx_frames in HFRL.
assert (Hal32 : cF C mod 32 = 0).
{ destruct (HFRL ly S Hp W mem md CRS_CID (c_fpos C) HAR Hin) as (H32 & _). rewrite EcF in H32. exact H32. }
assert (EFB : fs_frame_bytes CRS_CID = 128) by reflexivity.
(* the frame and its shadow are kept *)
assert (Kfr : forall a, cF C <= a < cF C + 128 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (Hk12 CRS_CID (c_fpos C) a Hin); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EcF, EFB; lia|].
  apply HFP. left. exact Ha. }
assert (Ksh : forall a, shadow_addr (cF C) <= a < shadow_addr (cF C) + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (Hk12 CRS_CID (c_fpos C) a Hin); [right; unfold in_zr; cbn [fst snd]; rewrite EcF, EFB; change (128 / 8) with 16; lia|].
  apply HFP. right. exact Ha. }
(* the saved words lie in the function's own real-stack window, above the callee's *)
assert (Ksv : forall a, spZ (c_regs C) - 128 <= a < spZ (c_regs C) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply Hk9; lia).
split; [exact HP|]. split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ2|].
split.
{ split; [rewrite Hfr1; exact Hfrm|]. split.
  - rewrite Efl2, <- Efl. rewrite EFB in Hflag |- *. rewrite <- Hflag. unfold rdword. rewrite !Kfr by lia. reflexivity.
  - intros a Ha. rewrite EFB in Ha.
    assert (Hin2 : In (CRS_CID, c_fpos C) (frames S2)) by (rewrite Hfr1; exact Hin).
    destruct (HFRL ly2 S2 Hp2 W2 mem2 md2 CRS_CID (c_fpos C) HAR2 Hin2) as (_ & _ & Hp2' & _).
    rewrite EcF2, EFB in Hp2'. exact (proj1 (Hp2' a Ha)). }
split.
{ unfold crs_saved in HSV |- *. rewrite Forall_forall in HSV |- *. intros [off r] Hin3. pose proof (HSV _ Hin3) as Hr.
  cbn [fst snd] in Hr |- *. rewrite <- Hr. unfold rdword.
  assert (Hoff : 24 <= off <= 120).
  { unfold CRS_SAVED in Hin3. repeat (destruct Hin3 as [Hin3 | Hin3]; [injection Hin3 as <- _; lia|]). destruct Hin3. }
  rewrite !Ksv by lia. reflexivity. }
split.
{ destruct HSL as (HRA & HHV). unfold cOut, CRS_OFF_DOC in *.
  pose proof (Z.div_mod (cF C) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (cF C) 8 ltac:(lia)) as D2.
  assert (D3 : (cF C) mod 8 = 0) by (rewrite Z.mod_divide in Hal32 |- * by lia; destruct Hal32 as [q Hq]; exists (4 * q); lia).
  split.
  - intros x Hx. rewrite (Ksh (shadow_of_addr SHADOW_OFF x)); [exact (HRA x Hx)|].
    pose proof (Z.div_mod x 8 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D5.
    unfold cOut, CRS_OFF_DOC in Hx. unfold shadow_of_addr, shadow_addr. lia.
  - intros s Hs. rewrite Ksh; [exact (HHV s Hs)|]. exact (dz_hull_arith (cF C) s Hal32 Hs). }
split; [exact (dz_rod R CTX0 C ly2 S2 Hp2 W2 mem2 md2 k2 HP HJ2)|].
split; [exact (HMN2 HMN)|].
assert (E3 : Z_to_bv 5 3 = (3%bv : bv 5)) by (apply bv_eq; reflexivity).
assert (E4 : Z_to_bv 5 4 = (4%bv : bv 5)) by (apply bv_eq; reflexivity).
split; [rewrite <- Hg3, <- E3; apply HPr; unfold acallee_saved; lia|].
split; [rewrite <- Hg4, <- E4; apply HPr; unfold acallee_saved; lia|].
split; [exact Hs1|]. split; [exact Hs2 | split; [exact Hs3 | exact HDPk]].
Qed.

Lemma dz_regsat_in : forall regs l r v, crs_regsat regs l -> In (r, v) l -> getr regs r = w64 v.
Proof. intros regs l r v H Hin. unfold crs_regsat in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.

(* a register the run did not write (its symbolic value is still its current atom) keeps its value *)
Lemma dz_regsat_run : forall regs0 regsc ss (H : word -> bool) ms (l : list (bv 5 * Z)) (fxk : YK11.FPState),
  @st_ok SEGS fxk (TE regs0 regsc []) ss (restrict H ms) ->
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (SOff (32 + Z.to_nat (bv_unsigned (fst p))) 0)) l = true ->
  crs_regsat regsc l -> crs_regsat (ms_regs ms) l.
Proof.
intros regs0 regsc ss H ms l fxk HS Hl Hr. unfold crs_regsat in *. rewrite Forall_forall in Hr |- *.
rewrite forallb_forall in Hl. intros [r v] Hin.
cbn [fst snd]. rewrite (ts_reg_kept_c regs0 regsc [] ss H ms r r HS (sv_eqb_eq _ _ (Hl _ Hin))). exact (Hr _ Hin).
Qed.

(* the boundary over a run that wrote no memory: the run's journal, the gp / tp it kept *)
Lemma dz_base_run : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C (fxk : YK11.FPState) ly S Hp W regs regs' mem
  md md' k sp2,
  crs_baseR (fx := fx) (SK := SK) B ARx R CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_JR (SK := SK) B ARx R C ly S Hp W mem md' k ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  crs_baseR (fx := fx) (SK := SK) B ARx R CTX0 C fxk ly S Hp W regs' mem md' k sp2.
Proof.
intros R CTX0 C fxk ly S Hp W regs regs' mem md md' k sp2 HB HJ H3 H4.
destruct HB as (HP & Hfz & Hfk & _ & HFR & HSV & HSL & HROD & HMN & Hg3 & Hg4 & Hs).
repeat (split; [eassumption|]). split; [rewrite H3; exact Hg3|]. split; [rewrite H4; exact Hg4|]. exact Hs.
Qed.

(* THE TREE at a later state with the same harness list: its node's bytes (in an entry fake frame) and its blocks'
   bytes (entry harness blocks) are the entry's at both states (the function's journal, FP = []); its visibility and
   its object home from the kit's record *)
Lemma dz_tree_keep : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly S Hp W mem md k ly' S' Hp' W' mem' md' k'
  Lam peak' cnt' fail' ran' most' own',
  crs_pre (fx := fx) B ARx CTX0 C -> CrsKeep (SK := SK) B ARx ->
  crs_JR (SK := SK) B ARx R C ly S Hp W mem md k ->
  crs_JR (SK := SK) B ARx R C ly' S' Hp' W' mem' md' k' ->
  Permutation (ablocks B ly S) (ablocks B (c_ly C) (c_S C)) ->
  Permutation (ablocks B ly' S') (ablocks B (c_ly C) (c_S C)) ->
  LEDGER ly' S' Hp' W' mem' Lam peak' cnt' fail' ran' most' own' ->
  crs_tree C ly S Lam W mem -> crs_tree C ly' S' Lam W' mem'.
Proof.
intros R CTX0 C ly S Hp W mem md k ly' S' Hp' W' mem' md' k' Lam peak' cnt' fail' ran' most' own' HP HK HJ HJ' HpermA
  Hperm HLED' HT Hdoc.
destruct (HT Hdoc) as (Hnode & HDL & _ & _).
pose proof HP as HP'.
destruct HP' as ((HPRE0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdoc0 & HLED0 & _).
destruct Hdoc0 as [Hd0 | (_ & Htok0 & _)]; [exfalso; exact (Hdoc Hd0)|].
destruct Htok0 as (_ & HDL0 & _ & Hhome0).
pose proof HPRE0 as (HAR0 & _).
pose proof HJ as HJc. unfold crs_JR in HJc. destruct HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbk & _ & Hfk & _).
pose proof HJ' as HJc'. unfold crs_JR in HJc'.
destruct HJc' as (HAR' & Hle' & _ & _ & _ & Hfr' & _ & _ & _ & Hbk' & _ & Hfk' & _).
pose proof LAWS as HBL. apply alx_blocks in HBL. pose proof LAWS as HFRL. apply alx_frames in HFRL.
pose proof cf_head_nonneg as CH0.
assert (Hfoot : forall x, pj_footR (c_doc C) (c_D C) x ->
  aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x /\ apresent (w_H W') mem' x).
{ intros x [Hx | ((ba & bk) & Hb & Hx)].
  - destruct Hhome0 as (_ & (cid & pos & Hin & Hlo & Hhi) & _).
    assert (Hfa : in_zr x (frame_rng (c_ly C) (cid, pos))) by (unfold in_zr, frame_rng; cbn [fst snd]; lia).
    split.
    + rewrite (Hfk' cid pos x Hin), (Hfk cid pos x Hin); [reflexivity | left; exact Hfa | intros (r & Hr & _); destruct Hr
        | left; exact Hfa | intros (r & Hr & _); destruct Hr].
    + assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfr'; apply in_or_app; right; exact Hin).
      destruct (crs_ly_keep B ARx LAWS _ _ _ _ _ _ ly' cid pos HAR0 Hle') as [Efa _].
      destruct (HFRL ly' S' Hp' W' mem' md' cid pos HAR' Hin') as (_ & _ & Hpr & _).
      apply (Hpr x). rewrite Efa. lia.
  - unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    assert (HBK0 := HLED0). destruct HBK0 as [_ (_ & HBK0 & _)]. rewrite Forall_forall in HBK0.
    destruct (HBK0 (ba, bk) (HDL0 _ Hb)) as (Hk0 & Hab & _ & _). cbn [fst snd] in Hk0, Hab.
    assert (Hab' : In (ba - cf_head, bk + cf_head) (ablocks B ly' S')) by exact (Permutation_in _ (Permutation_sym Hperm) Hab).
    assert (Hab'' : In (ba - cf_head, bk + cf_head) (ablocks B ly S)) by exact (Permutation_in _ (Permutation_sym HpermA) Hab).
    assert (Hrs : bk + cf_head <= req_size (bk + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (bk + cf_head) 0); lia).
    replace x with ((ba - cf_head) + (x - (ba - cf_head))) by lia.
    split.
    + rewrite (Hbk' _ _ _ Hab Hab'), (Hbk _ _ _ Hab Hab''); [reflexivity | lia | intros (r & Hr & _); destruct Hr | lia
        | intros (r & Hr & _); destruct Hr].
    + destruct (HBL ly' S' Hp' W' mem' md' _ _ HAR' Hab') as (_ & _ & _ & _ & Hpr & _).
      assert (Hxx : ba - cf_head <= ba - cf_head + (x - (ba - cf_head)) < ba - cf_head + req_size (bk + cf_head)).
      { clear -CH0 Hx Hk0 Hrs. set (rq := req_size (bk + cf_head)) in *. set (ch := cf_head) in *. lia. }
      exact (proj1 (Hpr (ba - cf_head + (x - (ba - cf_head))) Hxx)). }
split.
- apply (pj_nodeR_frame SEGS (c_t C) (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') _ _ _ Hnode).
  intros x Hx. destruct (Hfoot x Hx) as [E Hpr]. split; [exact (mbyte_of_aview SEGS _ _ _ _ x E)|].
  intros _. exact (apresent_writable SEGS _ _ x Hpr).
- split; [exact HDL|]. split; [exact (kp_tree_vis B ARx HK ly' S' Hp' W' mem' md' Lam peak' cnt' fail' ran' most' own' (c_D C) HAR' HLED' HDL)|].
  exact (crs_obj_keep_dpR B ARx LAWS R STK (spZ (c_regs C)) (c_ly C) (c_S C) (c_dp C) (c_Hp C) (c_W C) (c_mem C) (c_md C)
    [(CRS_CID, c_fpos C)] ly' S' Hp' W' mem' md' k' (c_doc C) HAR0 HJ' Hhome0).
Qed.

(* a byte the function's journal keeps from the entry (FP = []) in an entry allocator block present at the state *)
Lemma dz_blk_entry : forall (R : world SEGS -> world SEGS -> Prop) C ly S Hp W mem md k p n x,
  crs_JR (SK := SK) B ARx R C ly S Hp W mem md k ->
  In (p, n) (ablocks B (c_ly C) (c_S C)) -> In (p, n) (ablocks B ly S) -> p <= x < p + n ->
  aview SEGS (w_H W) mem x = aview SEGS (w_H (c_W C)) (c_mem C) x.
Proof.
intros R C ly S Hp W mem md k p n x HJ H0 H1 Hx. unfold crs_JR in HJ.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbk & _).
assert (Hrs : n <= req_size n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
replace x with (p + (x - p)) by lia. apply (Hbk p n (x - p) H0 H1); [lia | intros (r & Hr & _); destruct Hr].
Qed.
(* a read-only image byte the function's journal keeps from the entry *)
Lemma dz_ro_entry : forall (R : world SEGS -> world SEGS -> Prop) C ly S Hp W mem md k a,
  crs_JR (SK := SK) B ARx R C ly S Hp W mem md k ->
  in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W) mem a = aview SEGS (w_H (c_W C)) (c_mem C) a.
Proof.
intros R C ly S Hp W mem md k a HJ Hro Hown Herr. unfold crs_JR in HJ.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
apply Himg; [| exact Hown | exact Herr | | ].
- destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
- intros Hpst. exact (S1ImgA.pst_not_ro_A a Hpst Hro).
- intros (r & Hr & _). destruct Hr.
Qed.

(* THE INPUT at a later state: its bytes are kept from the entry at both states (by its home at entry: a harness
   block, a registered read-only global, an allocator block), its home moves with the ledger and gives its shadow
   (the kit's record) *)
Lemma dz_dat_keep : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly S Hp W mem md k ly' S' Hp' W' mem' md' k'
  LamA peakA cntA failA ranA mostA ownA Lam peak' cnt' fail' ran' most' own',
  crs_pre (fx := fx) B ARx CTX0 C -> CrsKeep (SK := SK) B ARx ->
  crs_JR (SK := SK) B ARx R C ly S Hp W mem md k ->
  crs_JR (SK := SK) B ARx R C ly' S' Hp' W' mem' md' k' ->
  Permutation (ablocks B ly S) (ablocks B (c_ly C) (c_S C)) ->
  Permutation (ablocks B ly' S') (ablocks B (c_ly C) (c_S C)) ->
  LEDGER ly S Hp W mem LamA peakA cntA failA ranA mostA ownA ->
  LEDGER ly' S' Hp' W' mem' Lam peak' cnt' fail' ran' most' own' ->
  Permutation Lam LamA ->
  crs_dat B C ly S Hp W mem LamA -> crs_dat B C ly' S' Hp' W' mem' Lam.
Proof.
intros R CTX0 C ly S Hp W mem md k ly' S' Hp' W' mem' md' k' LamA peakA cntA failA ranA mostA ownA
  Lam peak' cnt' fail' ran' most' own' HP HK HJ HJ' HpermA Hperm HLA HLB HpL HD.
destruct HD as (Hby & Hhome & _ & _).
pose proof HP as HP'.
destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hd0 & Hds & Hsrc & Hhome0 & _ & _ & HLED0 & _).
destruct Hsrc as (_ & H4096 & Hceil & _).
pose proof HJ' as HJc'. unfold crs_JR in HJc'. destruct HJc' as (HAR' & _).
pose proof cf_head_nonneg as CH0.
assert (Hag : forall x, c_data C <= x < c_data C + cSize C ->
  aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x).
{ intros x Hx. destruct Hhome0 as [[(b & m & Hin & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hin & _ & Hb1 & Hb2)].
  - assert (HBK0 := HLED0). destruct HBK0 as [_ (_ & HBK0 & _)]. rewrite Forall_forall in HBK0.
    destruct (HBK0 (b, m) Hin) as (Hm0 & Hab & _ & _). cbn [fst snd] in Hm0, Hab.
    rewrite (dz_blk_entry R C ly' S' Hp' W' mem' md' k' _ _ x HJ' Hab (Permutation_in _ (Permutation_sym Hperm) Hab)),
      (dz_blk_entry R C ly S Hp W mem md k _ _ x HJ Hab (Permutation_in _ (Permutation_sym HpermA) Hab)); [reflexivity| |];
      clear -CH0 Hx Hb1 Hb2 Hm0; set (ch := cf_head) in *; unfold cSize in *; lia.
  - destruct (Hro x ltac:(unfold cSize in *; lia)) as (H1 & H2 & H3).
    rewrite (dz_ro_entry R C ly' S' Hp' W' mem' md' k' x HJ' H1 H2 H3), (dz_ro_entry R C ly S Hp W mem md k x HJ H1 H2 H3).
    reflexivity.
  - destruct (Hro x ltac:(unfold cSize in *; lia)) as (H1 & H2 & H3 & _).
    rewrite (dz_ro_entry R C ly' S' Hp' W' mem' md' k' x HJ' H1 H2 H3), (dz_ro_entry R C ly S Hp W mem md k x HJ H1 H2 H3).
    reflexivity.
  - rewrite (dz_blk_entry R C ly' S' Hp' W' mem' md' k' _ _ x HJ' Hin (Permutation_in _ (Permutation_sym Hperm) Hin)),
      (dz_blk_entry R C ly S Hp W mem md k _ _ x HJ Hin (Permutation_in _ (Permutation_sym HpermA) Hin)); [reflexivity| |];
      unfold cSize in *; lia. }
assert (Hhome' : PRH_FnReader.prhReader_home B ly' S' Hp' Lam (c_data C) (cSize C))
  by exact (kp_home_move B ARx HK ly S Hp W mem LamA peakA cntA failA ranA mostA ownA ly' S' Hp' W' mem' Lam peak'
              cnt' fail' ran' most' own' (c_data C) (cSize C) HLA HLB HpL
              (Permutation_trans Hperm (Permutation_sym HpermA)) Hhome).
split.
- unfold PRH_Base.bytes_at in Hby |- *. apply (garr8R_frame SEGS _ _ _ _ Hby).
  intros x Hx. apply (mbyte_of_aview SEGS). apply Hag. unfold cSize. exact Hx.
- split; [exact Hhome'|].
  destruct (Z_lt_le_dec 0 (cSize C)) as [Hn|Hn].
  + destruct (kp_home_sh B ARx HK ly' S' Hp' W' mem' md' Lam peak' cnt' fail' ran' most' own' (c_data C) (cSize C) HAR' HLB Hhome'
      Hn ltac:(lia) ltac:(unfold cSize in *; lia)) as [HRA HHV].
    split; [exact HRA | intros _; exact HHV].
  + split; [intros x Hx; lia | intros Hc; lia].
Qed.

(* a run over regions with no write window leaves the whole memory as it was *)
Lemma dz_mem_nowr : forall E rs (m m' : word -> option byte), (forall a, ~ in_wrange E rs a) -> frame_of E rs m m' -> m' = m.
Proof. intros E rs m m' Hn H. apply functional_extensionality. intros x. apply H. apply Hn. Qed.

(* a current-register atom of the segment environment *)
Lemma dz_sv_cur : forall regs0 regsc (r : bv 5) n, n = (32 + Z.to_nat (bv_unsigned r))%nat ->
  sv_denot (TE regs0 regsc []) (SOff n 0) = getr regsc r.
Proof.
intros regs0 regsc r n ->. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite (te_cur regs0 regsc [] r (Z.to_nat (bv_unsigned r))) by (pose proof (u5_range r); lia).
apply Z_to_bv_bv_unsigned.
Qed.

(* g_count at Z's end: the compact whole write made kk <= N0 calls after crs_cnt2 *)
Lemma dz_cnt_arith : forall CTX0 C, crs_pre (fx := fx) B ARx CTX0 C -> c_doc C <> 0 -> c_took C <= 2 ^ 28 ->
  0 <= c_cnt C /\ c_cnt C <= crs_cnt2 C /\ crs_cnt2 C + cN0 C < 2 ^ 62 /\ 1 <= cN0 C /\
  (forall kk, kk <= cN0 C -> crs_cnt2 C + kk <= c_cnt C + ck_crcs_max (c_tb C) (c_took C) (c_doc C) (c_t C)).
Proof.
intros CTX0 C HP Hdoc Htk.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htook & Hd & HLED0 & Hcnt & _).
destruct Hd as [H0 | (_ & _ & Hwf & Hwt & _)]; [contradiction|].
assert (Hc0 : 0 <= c_cnt C) by (destruct (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED0) as (_ & _ & Hcn & _); lia).
pose proof (crs_wN_pos (c_t C) true) as P1. pose proof (crs_wN_pos (c_t C) false) as P0.
pose proof (crs_wN_le (c_t C) true ltac:(lia)) as L1. pose proof (crs_wN_le (c_t C) false ltac:(lia)) as L0.
unfold crs_cnt2, crs_cnt1, crs_first, cN1, cN0, ck_crcs_max, PjWriteHyp.wcalls in *.
set (N1 := Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces (c_t C) true))))) in *.
set (N0 := Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces (c_t C) false))))) in *.
assert (HN1 : 1 <= N1) by lia. assert (HN0 : 1 <= N0) by lia.
pose proof (crs_pick_lt (c_tb C) N1 ltac:(lia)) as Pk1.
rewrite (proj2 (Z.eqb_neq (c_doc C) 0) Hdoc).
destruct (Z.eqb_spec (c_took C) 0) as [T0|T1].
- split; [exact Hc0|]. split; [lia|]. split; [lia|]. split; [lia|]. intros kk Hkk. lia.
- pose proof (crs_pick_lt (c_tb C) (c_took C) ltac:(lia)) as Pkt.
  split; [exact Hc0|]. split; [lia|]. split; [lia|]. split; [lia|]. intros kk Hkk. lia.
Qed.

(* ---- the writer's model: a run with no failure is the plain run, its capacity the last grow ---- *)
Lemma dz_pw_ok : forall P ok st, WriterApp.w_failed (prhWriter_putN ok st P) = 0 ->
  prhWriter_putN ok st P = WriterApp.putN st P.
Proof.
induction P as [|b P IH]; intros ok st Hf; [reflexivity|].
cbn [prhWriter_putN] in Hf |- *. rewrite WriterApp.putN_cons.
destruct (prhWriter_grows st b) eqn:Hg.
- destruct (hd true ok) eqn:Hh.
  + rewrite crs_put1_true in Hf |- *. apply IH. exact Hf.
  + exfalso. unfold prhWriter_put1 in Hf. rewrite Hg in Hf.
    destruct (WriterApp.w_cnt st =? WriterApp.w_fail st);
      (rewrite crs_pw_failed in Hf by (cbn [WriterApp.w_failed]; lia); cbn [WriterApp.w_failed] in Hf; lia).
- apply IH. exact Hf.
Qed.
Lemma dz_last_cons : forall (l : list Z) a d, last (a :: l) d = last l a.
Proof. induction l as [|b l IH]; intros a d; [reflexivity|]. change (last (b :: l) d = last (b :: l) a). rewrite !IH. reflexivity. Qed.
Lemma dz_gcap_last : forall ls x c, WriterSpec.grow_cap x c ls = last (WriterSpec.grow_calls x c ls) c.
Proof.
induction ls as [|l ls IH]; intros x c; [reflexivity|].
cbn [WriterSpec.grow_cap WriterSpec.grow_calls]. destruct (c <? x + l + 1); [rewrite dz_last_cons|]; apply IH.
Qed.
(* the whole write's text capacity, when nothing failed, is the model's last request (PresetReqAt.wcaps) *)
Lemma dz_wcap_full : forall t p ok cnt, 0 <= cnt ->
  cnt + Z.of_nat (length (PresetReqAt.wcaps t p)) + 1 < 2 ^ 64 ->
  WriterApp.w_failed (prhWriter_putN ok (WriterApp.w0 cnt SIZE_MAXZ) (WriterValue.wdpieces t p)) = 0 ->
  WriterApp.w_cap (prhWriter_putN ok (WriterApp.w0 cnt SIZE_MAXZ) (WriterValue.wdpieces t p)) =
  last (PresetReqAt.wcaps t p) 0.
Proof.
intros t p ok cnt Hc Hb Hf. rewrite (dz_pw_ok _ _ _ Hf).
unfold PresetReqAt.wcaps in *. unfold WriterApp.w0.
rewrite WriterAppFacts.putN_ok.
- cbn [WriterApp.w_cap WriterApp.w_text length]. change (Z.of_nat 0) with 0. apply dz_gcap_last.
- reflexivity.
- exact Hc.
- cbn [WriterApp.w_cnt WriterApp.w_text WriterApp.w_cap length]. change (Z.of_nat 0) with 0. lia.
- right. cbn [WriterApp.w_cnt WriterApp.w_text WriterApp.w_cap WriterApp.w_fail length]. change (Z.of_nat 0) with 0.
  unfold SIZE_MAXZ. lia.
Qed.

(* two entries of a pairwise relation over l1 ++ l2, one from each side *)
Lemma dz_pairwise_app : forall (X : Type) (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z l1 IH]; intros l2 x y H Hx Hy; [destruct Hx|].
cbn [app pairwise] in H. destruct H as [Hz Hp]. destruct Hx as [<-|Hx].
- rewrite Forall_forall in Hz. apply Hz. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Hp Hx Hy).
Qed.
(* a live block lies apart from a live fake frame and from that frame's shadow *)
Lemma dz_blk_frame_apart : forall ly S Hp W mem md p n cid pos a,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) -> p <= a < p + req_size n ->
  ~ (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid) /\
  ~ (shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8).
Proof.
intros ly S Hp W mem md p n cid pos a HAR Hb Hf Ha.
pose proof LAWS as HBL. apply alx_blocks in HBL. pose proof LAWS as HFRL. apply alx_frames in HFRL.
pose proof LAWS as HSEP. apply alx_sep in HSEP.
destruct (HBL ly S Hp W mem md p n HAR Hb) as (_ & _ & _ & Happ & _).
destruct (HFRL ly S Hp W mem md cid pos HAR Hf) as (_ & Happf & _).
destruct (HSEP ly S Hp W mem md HAR) as [Hpw _].
pose proof (dz_pairwise_app _ _ _ _ (p, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid) Hpw
  (in_map (fun b => (fst b, req_size (snd b))) _ _ Hb)
  (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ _ Hf)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (fs_frame_bytes_nonneg cid) as Hfb.
unfold in_app in Happ, Happf. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, ASAN_CEIL in *.
split; [lia|].
pose proof (Z.div_mod (frame_addr ly cid pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (frame_addr ly cid pos) 8 ltac:(lia)).
pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)).
lia.
Qed.

(* the freed text block was the head of the harness list: what the free leaves is the list before the write *)
Lemma dz_nodup_head : forall (L l1 l2 : list (Z * Z)) q c c',
  NoDup (map fst ((q, c) :: L)) -> (q, c) :: L = l1 ++ (q, c') :: l2 -> l1 ++ l2 = L.
Proof.
intros L l1 l2 q c c' Hnd E. destruct l1 as [|x l1].
- cbn [app] in E. injection E as _ <-. reflexivity.
- cbn [app] in E. injection E as Ex E. exfalso. cbn [map] in Hnd. inversion Hnd as [|? ? Hn _]; subst.
  apply Hn. apply list_elem_of_In. cbn [fst]. rewrite map_app. apply in_or_app. right. left. reflexivity.
Qed.

Lemma dz_dbl_ge : forall f c n, 0 <= c -> c <= WriterSpec.dbl f c n.
Proof. induction f as [|f IH]; intros c n Hc; cbn [WriterSpec.dbl]; [lia|]. destruct (n <=? c); [lia|]. pose proof (IH (2 * c) n ltac:(lia)). lia. Qed.
Lemma dz_live_w_nonneg : forall t p, 0 <= LIVE_pj_write t p.
Proof.
intros t p. unfold LIVE_pj_write, WriterSpec.newcap. cbn [Z.eqb].
pose proof (dz_dbl_ge 64 4096 (Z.of_nat (length (WriterValue.wdoc t p)) + 1) ltac:(lia)). pose proof cf_head_nonneg. lia.
Qed.
Lemma dz_hpeak_nonneg : forall tr, 0 <= hpeakR tr.
Proof. intros [|e r]; cbn [hpeakR]; lia. Qed.
Lemma dz_live_p_nonneg : forall x, 0 <= PRH_FnPj.LIVE_pj_parse x.
Proof.
intros x. unfold PRH_FnPj.LIVE_pj_parse. pose proof (dz_hpeak_nonneg (PRH_FnPj.prhPj_ptrace x)). pose proof cf_head_nonneg.
assert (0 <= cf_head * (Z.of_nat (PjGrammar.calls (PRH_FnPj.prhPj_ptrace x)) + 1)) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma dz_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof.
intros l l' H. induction H as [|x l1 l2 H IH|x y l|l1 l2 l3 H1 IH1 H2 IH2]; cbn [bsum fold_right] in *; try lia.
unfold bsum in *. lia.
Qed.

(* the compact whole write's size, request and room premises, from crs_pre *)
Lemma dz_pjw_facts : forall CTX0 C, crs_pre (fx := fx) B ARx CTX0 C -> c_doc C <> 0 ->
  (PjTree.depth (c_t C) <= DOC_D)%nat /\ Z.of_nat (PjTree.depth (c_t C)) <= 2 ^ 31 - 1 /\
  Z.of_nat (length (WriterValue.wdoc (c_t C) false)) + 1 <= prhWriter_WMAX /\
  prhWriter_WMAX + cf_head < cf_malloc_max /\
  (forall ly S, Permutation (ablocks B ly S) (ablocks B (c_ly C) (c_S C)) ->
     blocks_bytes S + LIVE_pj_write (c_t C) false <= LIVE_MAX) /\
  (forall S, frames S = (CRS_CID, c_fpos C) :: frames (c_S C) -> Z.of_nat (length (frames S)) < fs_frames 0).
Proof.
intros CTX0 C HP Hdoc.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & _ & _ & _ & _ & _ & _ & HLIVE & HRQ & HFR & _).
destruct Hd as [H0 | (_ & _ & Hwf & _ & Hdep)]; [contradiction|].
assert (ED : DOC_D = 33%nat) by reflexivity.
split; [rewrite ED; lia|]. split; [lia|].
split; [unfold PjWriteHyp.wlen in Hwf; unfold prhWriter_WMAX; lia|].
split; [unfold RQ_crcs, zmaxl in HRQ; cbn [fold_right] in HRQ; lia|].
split.
- intros ly S Hperm. rewrite (blocks_bytes_bsum B ly S), (dz_bsum_perm _ _ Hperm), <- (blocks_bytes_bsum B (c_ly C) (c_S C)).
  unfold LIVE_check_reject_clean_starved in HLIVE.
  pose proof (dz_live_p_nonneg (c_tb C)). pose proof (dz_live_w_nonneg (c_t C) true). lia.
- intros S E. exact (proj2 (proj2 (crs_cap_callee (c_S C) S (c_fpos C) E HFR))).
Qed.

(* seat a register as another register's current atom (their values agree) *)
Lemma dz_regs_ok_alias : forall regs0 regsc (r r' : bv 5), getr regsc r = getr regsc r' ->
  regs_ok (TE regs0 regsc []) (sr_set cur_atoms r (SOff (32 + Z.to_nat (bv_unsigned r')) 0)) regsc.
Proof.
intros regs0 regsc r r' H. apply dz_regs_ok_set. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite (te_cur regs0 regsc [] r' (Z.to_nat (bv_unsigned r'))) by (pose proof (u5_range r'); lia).
rewrite Z_to_bv_bv_unsigned. symmetry. exact H.
Qed.

Lemma dz_regsat_app : forall regs l1 l2, crs_regsat regs (l1 ++ l2) <-> crs_regsat regs l1 /\ crs_regsat regs l2.
Proof.
intros regs l1 l2. unfold crs_regsat. split.
- intros H. split; [apply Forall_forall; intros x Hx; apply (proj1 (Forall_forall _ _) H); apply in_or_app; left; exact Hx|].
  apply Forall_forall; intros x Hx; apply (proj1 (Forall_forall _ _) H); apply in_or_app; right; exact Hx.
- intros [H1 H2]. apply Forall_forall. intros x Hx. apply in_app_or in Hx as [Hx|Hx];
  [exact (proj1 (Forall_forall _ _) H1 x Hx) | exact (proj1 (Forall_forall _ _) H2 x Hx)].
Qed.

(* a register of a boundary list *)
Local Ltac dz_reg H :=
  apply (dz_regsat_in _ _ _ _ H); cbn [crs_rbase crs_rsh crs_rargs crs_rlive crs_rro app In];
  repeat (first [left; reflexivity | right]).

(* ==== THE NAMED PREMISE OF Z ==== *)
(* tfuzz_free_specX's entry bound on the class-24 count at the free site (+976), in h-pre-b1's
   PresetCfnA.counts_of_room_pos_rl shape (h-w6u-rep's premise order: crs_cnt24_<SEG>) *)
Definition crs_cnt24_Z (C : crsC) : Prop :=
  forall (i : nat) (hist : list YG00.chunk) (S : astate),
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) i (c_rp_H0 C) hist S ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.

(* HI_hull, the hull's instance fact: fuzz_free's hull budget at a non-NULL free (hull_budget S []) bounds the two
   meters by the CfParams caps cf_kmax / cf_T_max, and the run's count at Z's position bounds them by A17's caps
   (drv_cf_hull_ok_at_call_A, a run of at most 4 calls: crs_pre); the two caps agree at preset's CfParams (2 ^ 17 and
   2 ^ 36), as HI_head's head does *)
Lemma crs_seg_Z : forall CTX0 C
  (HI_head : @cf_head cp = PresetReqAt.HEAD)
  (HI_hull : PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax cp /\ PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max cp)
  (HT_fuzz_alloc_count : forall fx' : YK11.FPState,
     tfuzz_alloc_count_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) B ARx SK)
  (HT_fuzz_alloc_live : forall fx' : YK11.FPState,
     tfuzz_alloc_live_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) B ARx SK)
  (HT_fuzz_alloc_ran_out : forall fx' : YK11.FPState,
     tfuzz_alloc_ran_out_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) B ARx SK)
  (HT_fuzz_free : forall fx' : YK11.FPState,
     tfuzz_free_specX (fx := fx') (PI := prh_img_A) (RL := RL) (PA := PA) B ARx SK)
  (HT_fuzz_free0 : forall fx' : YK11.FPState, crs_free0 (fx := fx') (SK := SK) B ARx)
  (HK : CrsKeep (SK := SK) B ARx)
  (HB_took : c_took C <= 2 ^ 28)
  (HW_exact : forall fx' : YK11.FPState, crs_wexact (fx := fx') (SK := SK) B ARx CTX0 C)
  (HC24 : crs_cnt24_Z C)
  (HR : crs_from_R (fx := fx) (SK := SK) B ARx CTX0 C)
  (HH3 : crs_from_H3 (fx := fx) (SK := SK) B ARx CTX0 C),
  crs_from_Z (fx := fx) (SK := SK) B ARx CTX0 C.
Proof.
intros CTX0 C HI_head HI_hull HT_fuzz_alloc_count HT_fuzz_alloc_live HT_fuzz_alloc_ran_out HT_fuzz_free HT_fuzz_free0
  HK HB_took HW_exact HC24 HR HH3.
unfold crs_from_Z. intros fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 Hdoc HB HRS HL HD HT.
pose proof (wle'_refl SEGS YGcfRehidePost.RZ_cf) as WRr. pose proof (wle'_trans SEGS YGcfRehidePost.RZ_cf) as WRt.
pose proof (wle_wle' SEGS YGcfRehidePost.RZ_cf) as WRw.
pose proof asan_consts as (C1 & _).
assert (EB : BASE = 529888) by (vm_compute; reflexivity).
assert (EZ : CRS_PC_Z = 3888) by (vm_compute; reflexivity).
pose proof HB as HB'.
destruct HB' as (HP & Hfz & Hfk & HJ & HFR & HSV & HSL & HROD & HMN & Hg3 & Hg4 & Hs1 & Hs2 & Hs3 & HDPk).
assert (EF : CRS_FRAME = 144) by (vm_compute; reflexivity).
assert (ES : @STK_check_reject_clean_starved prh_img_A = 27312) by (vm_compute; reflexivity).
assert (Hsp0 : YM05.alloc_ceiling + 27312 <= spZ (c_regs C) <= 2 ^ 47).
{ pose proof HJ as HJa. unfold crs_JR in HJa.
  destruct HJa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). rewrite ES in Hslo. lia. }
assert (HRG : crs_regsat regs3 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro)).
{ pose proof HRS as Hx. apply dz_regsat_app in Hx as [A1 Hx]. apply dz_regsat_app in Hx as [A2 Hx].
  apply dz_regsat_app in Hx as [A3 Hx]. apply dz_regsat_app in Hx as [A4 Hx]. apply dz_regsat_app in Hx as [A5 _].
  apply dz_regsat_app; split; [exact A1|]. apply dz_regsat_app; split; [exact A2|].
  apply dz_regsat_app; split; [exact A3|]. apply dz_regsat_app; split; [exact A4 | exact A5]. }
assert (R23 : getr regs3 23 = w64 0).
{ apply (dz_regsat_in _ _ _ _ HRS). cbn [crs_rbase crs_rsh crs_rargs crs_rlive crs_rro app In].
  repeat (first [left; reflexivity | right]). }
assert (R2 : getr regs3 2 = w64 sp2) by dz_reg HRG.
assert (R8 : getr regs3 8 = w64 (spZ (c_regs C))) by dz_reg HRG.
assert (R22 : getr regs3 22 = w64 (Ledger.lsum (c_Lam C))) by dz_reg HRG.
assert (R19 : getr regs3 19 = w64 (c_doc C)) by dz_reg HRG.
destruct HL as [HCORE HPERM]. pose proof HCORE as (HLED & Hpk & Hrn & Hck & Hcl & Hroom & Hpos).
(* ---- +944 .. +948: bnez s7 (s7 = 0: the ABORT arm is not taken), jal fuzz_alloc_live ---- *)
pose proof (dz_seat (c_regs C) regs3 CRS_PC_Z (sr_set cur_atoms 23%bv (SLit 0)) W3 mem3 fxk) as HS.
specialize (HS ltac:(apply dz_regs_ok_set; rewrite R23; reflexivity)).
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (c_regs C) regs3 []) (mrestrict (w_H W3) mem3)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (c_regs C) regs3 [])) by apply te_env.
unfold crs_cfg. change (w64 (BASE + CRS_PC_Z)) with (Z_to_bv 64 (BASE + CRS_PC_Z)).
pose proof HJ as HJr. unfold crs_JR in HJr.
pose (RUN := @paj_run_xR fxk rc SK A_prog_listing PL PA B PST ARx cf_head LAWS WR WRr WRt).
paj_run_tok_x RUN HS HJr SHOK DZ_SPAN; [cbn [ss_mem]; apply awr_ok_nil|].
cbn [ss_mem] in HF. apply dz_mem_nil in HF. subst mem3. clear HFr HG.
prreg HS (1%bv : bv 5) Q1.
pose proof (ts_reg_kept_c (c_regs C) regs3 [] _ _ ms 3%bv 3%bv HS ltac:(vm_compute; reflexivity)) as Q3.
pose proof (ts_reg_kept_c (c_regs C) regs3 [] _ _ ms 4%bv 4%bv HS ltac:(vm_compute; reflexivity)) as Q4.
assert (HRG1 : crs_regsat (ms_regs ms) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_run _ _ _ _ _ _ fxk HS); [vm_compute; reflexivity | exact HRG]).
prreg HS (23%bv : bv 5) Q23.
assert (Qsp : spZ (ms_regs ms) = sp2) by (unfold spZ; rewrite (dz_regsat_in _ _ 2%bv sp2 HRG1) by (cbn; left; reflexivity);
  unfold w64; rewrite unsigned_lit_small by (clear -Hs1 Hs2 Hsp0 EF C1; lia); reflexivity).
assert (Qs0 : getr (ms_regs ms) 8 = w64 (spZ (c_regs C))) by dz_reg HRG1.
assert (HBc : crs_baseR (fx := fx) (SK := SK) B ARx WR CTX0 C fxk ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md3) mat md3) k sp2) by exact (dz_base_run WR CTX0 C fxk _ _ _ _ _ _ _ _ _ _ _ HB HJr Q3 Q4).
eapply (dz_call WR WRr WRt (@wle SEGS) WRw CTX0 C fxk W3 _ _ ms _ ly3 S3 Hp3 k sp2 (CRS_PC_Z + 8) 0 [] _ _ HP HS eq_refl HJr
  HSV Qsp Hs1 Hs2 Hs3 (proj1 (proj2 HBc)));
  [ rewrite Q3; exact Hg3 | rewrite Q4; exact Hg4 | exact Qs0 | rewrite Q1, EZ; reflexivity | rewrite EZ; lia
  | rewrite EZ; reflexivity | lia | rewrite EF, ES; lia
  | intros HF0; exact (HT_fuzz_alloc_live fxk ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ (dz_ch C ly3) Lam3 peak3
      (crs_cnt2 C) SIZE_MAXZ 0 (c_most C) 0 HF0 HLED)
  | intros a (r & Hr & _); destruct Hr | ].
intros W4 ly4 S4 Hp4 regs4 mem4 md4 k1 Hle4 HJ4 HJc4 HPr4 (HQ4 & HMN4).
destruct HQ4 as (Hrm4 & Ha04 & -> & -> & Hab4 & HLED4).
pose proof (dz_keep WR CTX0 C fxk ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ k sp2 0 [] ly4 S3 Hp3 W4 regs4 mem4 md4
  (k + k1) k1 HBc HJ4 HJc4 ltac:(intros a _ (r & Hr & _); destruct Hr) HPr4 HMN4) as HB4.
assert (HRG4 : crs_regsat regs4 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_pres _ _ _ HRG1 HPr4); vm_compute; reflexivity).
clear HS SHOK HEI HJr HBc HRG1 Q1 Q3 Q4 Q23 Qsp Qs0 HJc4 HPr4 HMN4 Hrm4.
(* ---- +952 .. +956: bne a0, s6 (a0 = fuzz_alloc_live () = s6: the ABORT arm is not taken), jal fuzz_alloc_count ---- *)
assert (Hsz : getr regs4 10 = getr regs4 22).
{ rewrite Ha04, (dz_regsat_in _ _ 22%bv _ HRG4) by (cbn [crs_rbase crs_rsh crs_rargs crs_rlive crs_rro app In];
    repeat (first [left; reflexivity | right])).
  f_equal. apply crs_lsum_perm. exact (proj1 HPERM). }
pose proof (dz_seat (c_regs C) regs4 (CRS_PC_Z + 8) _ W4 mem4 fxk (dz_regs_ok_alias _ _ 10%bv 22%bv Hsz)) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (c_regs C) regs4 []) (mrestrict (w_H W4) mem4)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (c_regs C) regs4 [])) by apply te_env.
pose proof HB4 as HB4'. destruct HB4' as (_ & _ & _ & HJr & _). unfold crs_JR in HJr.
paj_run_tok_x RUN HS HJr SHOK DZ_SPAN; [cbn [ss_mem]; apply awr_ok_nil|].
cbn [ss_mem] in HF. apply dz_mem_nil in HF. subst mem4. clear HFr HG.
prreg HS (1%bv : bv 5) Q1.
pose proof (ts_reg_kept_c (c_regs C) regs4 [] _ _ ms0 3%bv 3%bv HS ltac:(vm_compute; reflexivity)) as Q3.
pose proof (ts_reg_kept_c (c_regs C) regs4 [] _ _ ms0 4%bv 4%bv HS ltac:(vm_compute; reflexivity)) as Q4.
assert (HRG1 : crs_regsat (ms_regs ms0) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_run _ _ _ _ _ _ fxk HS); [vm_compute; reflexivity | exact HRG4]).
assert (Qsp : spZ (ms_regs ms0) = sp2) by (unfold spZ; rewrite (dz_regsat_in _ _ 2%bv sp2 HRG1) by (cbn; left; reflexivity);
  unfold w64; rewrite unsigned_lit_small by (clear -Hs1 Hs2 Hsp0 EF C1; lia); reflexivity).
assert (Qs0 : getr (ms_regs ms0) 8 = w64 (spZ (c_regs C))) by dz_reg HRG1.
assert (HBc := dz_base_run WR CTX0 C fxk _ _ _ _ _ _ _ _ _ _ _ HB4 HJr Q3 Q4).
pose proof HBc as HBc'. destruct HBc' as (_ & _ & _ & _ & _ & HSVc & _ & _ & _ & Hg3c & Hg4c & _).
eapply (dz_call WR WRr WRt (@wle SEGS) WRw CTX0 C fxk W4 _ _ ms0 _ ly4 S3 Hp3 (k + k1) sp2 (CRS_PC_Z + 16) 0 [] _ _ HP
  HS eq_refl HJr HSVc Qsp Hs1 Hs2 Hs3 (proj1 (proj2 HBc)));
  [ exact Hg3c | exact Hg4c | exact Qs0 | rewrite Q1, EZ; reflexivity | rewrite EZ; lia
  | rewrite EZ; reflexivity | lia | rewrite EF, ES; lia
  | intros HF0; exact (HT_fuzz_alloc_count fxk ly4 S3 Hp3 W4 (ms_regs ms0) (ms_mem ms0) _ (dz_ch C ly4) Lam3 peak3
      (crs_cnt2 C) SIZE_MAXZ 0 (c_most C) 0 HF0 HLED4)
  | intros a (r & Hr & _); destruct Hr | ].
intros W5 ly5 S5 Hp5 regs5 mem5 md5 k2 Hle5 HJ5 HJc5 HPr5 (HQ5 & HMN5).
destruct HQ5 as (Hrm5 & Ha05 & -> & -> & Hab5 & HLED5).
pose proof (dz_keep WR CTX0 C fxk ly4 S3 Hp3 W4 (ms_regs ms0) (ms_mem ms0) _ (k + k1) sp2 0 [] ly5 S3 Hp3 W5 regs5 mem5
  md5 (k + k1 + k2) k2 HBc HJ5 HJc5 ltac:(intros a _ (r & Hr & _); destruct Hr) HPr5 HMN5) as HB5.
assert (HRG5 : crs_regsat regs5 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_pres _ _ _ HRG1 HPr5); vm_compute; reflexivity).
clear HS SHOK HEI HJr HBc HSVc Hg3c Hg4c HRG1 Q1 Q3 Q4 Qsp Qs0 HJc5 HPr5 HMN5 Hrm5.
(* ---- +960 .. +972: mv s7, a0 (the count before the whole compact write); a0 = doc; a1 = 0; jal pj_write ---- *)
pose proof (dz_seat (c_regs C) regs5 (CRS_PC_Z + 16) cur_atoms W5 mem5 fxk (te_regs_ok _ _ _)) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (c_regs C) regs5 []) (mrestrict (w_H W5) mem5)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (c_regs C) regs5 [])) by apply te_env.
pose proof HB5 as HB5'. destruct HB5' as (_ & _ & _ & HJr & _). unfold crs_JR in HJr.
paj_run_tok_x RUN HS HJr SHOK DZ_SPAN; [cbn [ss_mem]; apply awr_ok_nil|].
cbn [ss_mem] in HF. apply dz_mem_nil in HF. subst mem5. clear HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (11%bv : bv 5) Q11.
pose proof (ts_reg_kept_c (c_regs C) regs5 [] _ _ ms1 3%bv 3%bv HS ltac:(vm_compute; reflexivity)) as Q3.
pose proof (ts_reg_kept_c (c_regs C) regs5 [] _ _ ms1 4%bv 4%bv HS ltac:(vm_compute; reflexivity)) as Q4.
pose proof (ts_reg_kept_c (c_regs C) regs5 [] _ _ ms1 10%bv 19%bv HS ltac:(vm_compute; reflexivity)) as Q10.
pose proof (ts_reg_kept_c (c_regs C) regs5 [] _ _ ms1 23%bv 10%bv HS ltac:(vm_compute; reflexivity)) as Q23.
assert (HRG1 : crs_regsat (ms_regs ms1) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_run _ _ _ _ _ _ fxk HS); [vm_compute; reflexivity | exact HRG5]).
rewrite (dz_regsat_in _ _ 19%bv (c_doc C) HRG5) in Q10 by (cbn [crs_rbase crs_rsh crs_rargs crs_rlive crs_rro app In];
  repeat (first [left; reflexivity | right])).
rewrite Ha05 in Q23.
assert (Qsp : spZ (ms_regs ms1) = sp2) by (unfold spZ; rewrite (dz_regsat_in _ _ 2%bv sp2 HRG1) by (cbn; left; reflexivity);
  unfold w64; rewrite unsigned_lit_small by (clear -Hs1 Hs2 Hsp0 EF C1; lia); reflexivity).
assert (Qs0 : getr (ms_regs ms1) 8 = w64 (spZ (c_regs C))) by dz_reg HRG1.
assert (HBc := dz_base_run WR CTX0 C fxk _ _ _ _ _ _ _ _ _ _ _ HB5 HJr Q3 Q4).
pose proof HBc as HBc'. destruct HBc' as (_ & _ & _ & _ & HFRc & HSVc & _ & _ & _ & Hg3c & Hg4c & _).
assert (Hperm5 : Permutation (ablocks B ly5 S3) (ablocks B (c_ly C) (c_S C))) by (rewrite Hab5, Hab4; exact (proj2 HPERM)).
pose proof (dz_tree_keep WR CTX0 C ly3 S3 Hp3 W3 (ms_mem ms) md3 k ly5 S3 Hp3 W5 (ms_mem ms1) _ (k + k1 + k2) Lam3 peak3
  (crs_cnt2 C) SIZE_MAXZ 0 (c_most C) 0 HP HK HJ HJr (proj2 HPERM) Hperm5 HLED5 HT Hdoc) as (Hnode & HDL & Hvis & Hhome).
destruct Hhome as (_ & Hinfr & HRAd).
destruct (dz_pjw_facts CTX0 C HP Hdoc) as (Pd1 & Pd2 & Pw & Pm & Pl & Pf).
destruct (Hpos eq_refl) as (hZ & HposZ).
pose proof HP as HP'. destruct HP' as (_ & _ & HU & _).
destruct (dz_cnt_arith CTX0 C HP Hdoc HB_took) as (Hcc0 & Hcc1 & Hcc2 & Hcc3 & _).
(* the call's run events, the text's entry premise: the kit's crs_ev_w C false at Z's prefix (crs_run_split;
   PRH_Supply.prhWriter_pjw_evs_w_evs: no call of the whole write is the chosen failure, g_fail_at = SIZE_MAX) *)
assert (Esp : crs_evs C = crs_evs_at_Z C ++ (crs_ev_w C false ++ crs_ev_wf C false ++ crs_ev_ws C false)).
{ rewrite (crs_evs_doc C Hdoc). unfold crs_evs_at_X3, crs_evs_at_H3. rewrite <- !app_assoc. reflexivity. }
assert (EpjwZ : prhWriter_pjw_evs [] (crs_cnt2 C) SIZE_MAXZ (WriterValue.wdpieces (c_t C) (negb (0 =? 0))) =
  crs_ev_w C false).
{ change (negb (0 =? 0)) with false.
  assert (EW : Z.of_nat (PresetReqAt.wcalls (c_t C) false) = cN0 C) by reflexivity.
  apply (PRH_Supply.prhWriter_pjw_evs_w_evs (c_t C) false (crs_cnt2 C) SIZE_MAXZ HI_head ltac:(lia)).
  intros j Hj. rewrite Z.mod_small by lia. unfold SIZE_MAXZ. lia. }
assert (HrunZ : prh_run_at ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C + length (crs_evs_at_Z C))%nat
  (prhWriter_pjw_evs [] (crs_cnt2 C) SIZE_MAXZ (WriterValue.wdpieces (c_t C) (negb (0 =? 0))))).
{ destruct (crs_run_split C _ _ Esp (crs_run_of_pre B ARx CTX0 C HP)) as [_ Hr2].
  apply prh_run_at_app_iff in Hr2. destruct Hr2 as [Hr2 _]. rewrite EpjwZ. exact Hr2. }
(* the call's consumer window (crs_wcall's prh_cons_from): its events lie inside crs_evs, crs_pre's window *)
assert (HconsZ : PRH_Base.prh_cons_from ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C)
  (c_rp_i C + length (crs_evs_at_Z C))%nat
  (length (prhWriter_pjw_evs [] (crs_cnt2 C) SIZE_MAXZ (WriterValue.wdpieces (c_t C) (negb (0 =? 0)))))).
{ eapply (crs_cons_sub (fx := fx) B ARx CTX0 C); [|exact HP]. rewrite EpjwZ, Esp, !length_app. lia. }
(* pj_write (doc, 0) can realloc its buffer: its text's post is at the re-hiding relation (crs_wcall's fpostFm) *)
eapply (dz_callF WR WRr WRt WR (fun _ _ H => H) CTX0 C fxk W5 _ _ ms1 _ ly5 S3 Hp3 (k + k1 + k2) sp2 (CRS_PC_Z + 32)
  (@STK_pj_write prh_img_A DOC_D) []
  _ _ HP HS eq_refl HJr HSVc Qsp Hs1 Hs2 Hs3 (proj1 (proj2 HBc)));
  [ exact Hg3c | exact Hg4c | exact Qs0 | rewrite Q1, EZ; reflexivity | rewrite EZ; lia
  | rewrite EZ; reflexivity | vm_compute; discriminate | rewrite EF, ES; vm_compute; discriminate
  | intros HF0;
    exact (proj1 (proj2 (proj2 (HW_exact fxk))) hZ ly5 S3 Hp3 W5 (ms_regs ms1) (ms_mem ms1) _ (dz_ch C ly5)
      Lam3 peak3 (crs_cnt2 C) SIZE_MAXZ 0 eq_refl eq_refl Hcl HF0 HU Hroom HposZ HconsZ Q10 Q11 ltac:(lia) HLED5 HrunZ
      Hnode (or_intror (or_intror Hinfr)) HRAd Hvis (fun a kk => HDL (a, kk)) Pd1 Pd2 (Pf S3 (proj1 HFRc)) Pw Pm
      (Pl ly5 S3 Hperm5))
  | intros a (r & Hr & _); destruct Hr | ].
intros fxw W6 ly6 S6 Hp6 regs6 mem6 md6 k3 Hle6 Hfzw Hfkw HJ6 HJc6 HPr6 (HQ6 & HMN6).
destruct HQ6 as (ok & ran6 & q & Lam6 & peak6 & Hoks & Hq & Hrm6 & Hgr & _ & Hnode6 & Hvis6 & HLED6 & Harms & Hexact).
pose proof (dz_base_fx WR CTX0 C fxk fxw _ _ _ _ _ _ _ _ _
  (dz_keep WR CTX0 C fxk ly5 S3 Hp3 W5 (ms_regs ms1) (ms_mem ms1) _ (k + k1 + k2) sp2 _ [] ly6 S6 Hp6 W6 regs6 mem6
     md6 (k + k1 + k2 + k3) k3 HBc HJ6 HJc6 ltac:(intros a _ (r & Hr & _); destruct Hr) HPr6 HMN6) Hfzw Hfkw) as HB6.
assert (HRG6 : crs_regsat regs6 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_pres _ _ _ HRG1 HPr6); vm_compute; reflexivity).
assert (R23_6 : getr regs6 23 = w64 (crs_cnt2 C)).
{ rewrite <- Q23. assert (E23 : Z_to_bv 5 23 = (23%bv : bv 5)) by (apply bv_eq; reflexivity).
  rewrite <- E23. apply HPr6. unfold acallee_saved. lia. }
clear HS SHOK HEI HJr HBc HFRc HSVc Hg3c Hg4c HRG1 Q1 Q3 Q4 Q10 Q11 Q23 Qsp Qs0 HJc6 HPr6 HMN6.
(* from here on the walk runs at pj_write's float state *)
clear RUN HB HB4 HB5 Hfz Hfk Hfzw Hfkw. clear fxk. rename fxw into fxk.
pose (RUN := @paj_run_xR fxk rc SK A_prog_listing PL PA B PST ARx cf_head LAWS WR WRr WRt).
change (negb (0 =? 0)) with false in *.
(* ---- the compact whole write's outcome (PRW_CrsModel.crs_wfull) ---- *)
assert (Hc0 : 0 <= crs_cnt2 C) by lia.
assert (HN0 : Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces (c_t C) false))))
  < 2 ^ 24).
{ destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & _).
  destruct Hd as [H0 | (_ & _ & Hwf & _)]; [contradiction|].
  pose proof (crs_wN_le (c_t C) false ltac:(lia)). lia. }
destruct (crs_wfull (WriterValue.wdpieces (c_t C) false) (crs_cnt2 C) ok (crs_wdpieces_ne _ _) Hc0 ltac:(lia))
  as (Hk1 & Hwc & Hwf & Hfail0 & Hall & _).
set (st6 := prhWriter_putN ok (WriterApp.w0 (crs_cnt2 C) SIZE_MAXZ) (WriterValue.wdpieces (c_t C) false)) in *.
set (k6 := prhWriter_k ok (WriterApp.w0 (crs_cnt2 C) SIZE_MAXZ) (WriterValue.wdpieces (c_t C) false)) in *.
(* nothing is refused (the post's prh_granted, DEAD-PJWRITE): g_ran_out stays at the entry's 0
   (crs_ran_of_granted), and every allocation of the write was granted, so the write did not fail *)
assert (R6 : ran6 = 0) by exact (crs_ran_of_granted _ _ _ _ _ _ _ _ Hoks Hgr).
assert (Hok0 : WriterApp.w_failed st6 = 0).
{ apply Hall. intros i Hi. destruct (nth i ok true) eqn:En; [reflexivity|].
  exfalso. pose proof (Hgr i Hi En) as Ei. unfold SIZE_MAXZ in Ei. lia. }
(* the write's text block (the failed arm, q = NULL, is refuted by Hok0) *)
assert (Hpk6 : peak3 <= peak6)
  by (destruct Harms as [(_ & _ & _ & _ & -> & _) | (Hf1 & _)]; [lia | exfalso; exact (Hf1 Hok0)]).
assert (Harm : exists cap0, q <> 0 /\ Lam6 = (q, cap0) :: Lam3 /\
  Permutation (ablocks B ly6 S6) ((q - cf_head, cap0 + cf_head) :: ablocks B ly5 S3) /\
  ~ In (q - cf_head, cap0 + cf_head) (ablocks B ly5 S3) /\ cap0 = last (PresetReqAt.wcaps (c_t C) false) 0).
{ destruct Harms as [(_ & Hq0 & Hnin & -> & _ & Hpb & _) | (Hf1 & _)]; [|exfalso; exact (Hf1 Hok0)].
  exists (WriterApp.w_cap st6). split; [exact Hq0|]. split; [reflexivity|]. split; [exact Hpb|].
  split; [exact Hnin|]. apply dz_wcap_full; [exact Hc0 | unfold PresetReqAt.wcaps; lia | exact Hok0]. }
destruct Harm as (cap0 & Hq0 & ELam & Hpb & Hnin & Ecap).
(* ---- +976: jal fuzz_free (a0 = q). Nothing is refused, so q is the whole text, freed by tfuzz_free_specX at the
   writer's exact advance (its event from the kit's crs_room_evs_of_run; its fixed trace admitted by admits_ct_fix,
   its budgeted post read back by fpost_of_fpostb_fix) ---- *)
pose proof (dz_seat (c_regs C) regs6 (CRS_PC_Z + 32) cur_atoms W6 mem6 fxk (te_regs_ok _ _ _)) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (c_regs C) regs6 []) (mrestrict (w_H W6) mem6)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (c_regs C) regs6 [])) by apply te_env.
pose proof HB6 as HB6'. destruct HB6' as (_ & _ & _ & HJr & _). unfold crs_JR in HJr.
paj_run_tok_x RUN HS HJr SHOK DZ_SPAN; [cbn [ss_mem]; apply awr_ok_nil|].
cbn [ss_mem] in HF. apply dz_mem_nil in HF. subst mem6. clear HFr HG.
prreg HS (1%bv : bv 5) Q1.
pose proof (ts_reg_kept_c (c_regs C) regs6 [] _ _ ms2 3%bv 3%bv HS ltac:(vm_compute; reflexivity)) as Q3.
pose proof (ts_reg_kept_c (c_regs C) regs6 [] _ _ ms2 4%bv 4%bv HS ltac:(vm_compute; reflexivity)) as Q4.
pose proof (ts_reg_kept_c (c_regs C) regs6 [] _ _ ms2 10%bv 10%bv HS ltac:(vm_compute; reflexivity)) as Q10.
pose proof (ts_reg_kept_c (c_regs C) regs6 [] _ _ ms2 23%bv 23%bv HS ltac:(vm_compute; reflexivity)) as Q23.
rewrite Hq in Q10. rewrite R23_6 in Q23.
assert (HRG1 : crs_regsat (ms_regs ms2) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_run _ _ _ _ _ _ fxk HS); [vm_compute; reflexivity | exact HRG6]).
assert (Qsp : spZ (ms_regs ms2) = sp2) by (unfold spZ; rewrite (dz_regsat_in _ _ 2%bv sp2 HRG1) by (cbn; left; reflexivity);
  unfold w64; rewrite unsigned_lit_small by (clear -Hs1 Hs2 Hsp0 EF C1; lia); reflexivity).
assert (Qs0 : getr (ms_regs ms2) 8 = w64 (spZ (c_regs C))) by dz_reg HRG1.
assert (HBc := dz_base_run WR CTX0 C fxk _ _ _ _ _ _ _ _ _ _ _ HB6 HJr Q3 Q4).
pose proof HBc as HBc'. destruct HBc' as (_ & _ & _ & _ & HFRc & HSVc & _ & _ & _ & Hg3c & Hg4c & _).
assert (Hs0Z : s0Z (ms_regs ms2) = spZ (c_regs C)) by (unfold s0Z; rewrite Qs0; unfold w64;
  rewrite unsigned_lit_small by (clear -Hsp0 C1; lia); reflexivity).
assert (HraZ : raZ (ms_regs ms2) = BASE + CRS_PC_Z + 36) by (unfold raZ; rewrite Q1, EZ, EB; reflexivity).
pose proof (proj1 HJr) as HAR6. cbv beta in HAR6.
destruct (crs_cF_keepR B ARx LAWS WR CTX0 C ly6 S6 Hp6 W6 (ms_mem ms2) _ (k + k1 + k2 + k3) HP HJr) as [EcF6 _].
assert (Hfr6 : In (CRS_CID, c_fpos C) (frames S6)) by (rewrite (proj1 HFRc); left; reflexivity).
(* what the walk keeps of the free's post (its p <> 0 arm) *)
set (Qf := fun (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS) (regs' : bvmap 5 word)
             (mem' : word -> option byte) (md' : Model) =>
  room_live_cf S' /\
  (ran6 = 0 -> exists h, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C)
     (c_rp_i C + length (crs_evs_at_H3 C))%nat (c_rp_H0 C) h S') /\
  Hp' = remove Z.eq_dec (q - cf_head) Hp6 /\
  (exists b1 b2, ablocks B ly6 S6 = b1 ++ (q - cf_head, cap0 + cf_head) :: b2 /\ ablocks B ly' S' = b1 ++ b2) /\
  exists l1 l2, Lam6 = l1 ++ (q, cap0) :: l2 /\
  LEDGER ly' S' Hp' W' mem' (l1 ++ l2) peak6 (WriterApp.w_cnt st6) (WriterApp.w_fail st6) ran6 (c_most C) 0).
(* the free's text runs at the re-hiding relation and posts its journal there *)
eapply (dz_call WR WRr WRt WR (fun _ _ H => H) CTX0 C fxk W6 _ _ ms2 _ ly6 S6 Hp6 (k + k1 + k2 + k3) sp2 (CRS_PC_Z + 36)
  (@STK_fuzz_free prh_img_A)
  (if q =? 0 then [] else ablocks_fp [(q - cf_head, cap0 + cf_head)])
  (fun ly' S' Hp' W' regs' mem' md' => Qf ly' S' Hp' W' regs' mem' md' /\
     (YAkMemnorm.memnorm SEGS (ms_mem ms2) -> YAkMemnorm.memnorm SEGS mem'))
  _ HP HS eq_refl HJr HSVc Qsp Hs1 Hs2 Hs3 (proj1 (proj2 HBc)));
  [ exact Hg3c | exact Hg4c | exact Qs0 | rewrite Q1, EZ; reflexivity | rewrite EZ; lia
  | rewrite EZ; reflexivity | vm_compute; discriminate | rewrite EF, ES; vm_compute; discriminate | | | ].
{ intros HF0.
  (* the text block, at the writer's exact advance *)
  destruct (Hexact R6) as (h0 & Hp0).
  set (iZ := (c_rp_i C + length (crs_evs_at_Z C) + length (crs_ev_w C false))%nat) in Hp0.
  destruct (crs_room_evs_of_run C Hdoc (crs_run_of_pre B ARx CTX0 C HP)) as [_ Hev].
  rewrite length_app, Nat.add_assoc in Hev. fold iZ in Hev. rewrite <- Ecap, <- HI_head in Hev.
  assert (HinL : In (q, cap0) Lam6) by (rewrite ELam; left; reflexivity).
  pose proof (dz_trace_free CTX0 C ly6 (ms_regs ms2) HP Hs0Z HraZ) as Htr.
  (* the hull budget at the free (q <> 0): the run's count at the writer's exact advance, a run of at most 4 calls
     (crs_pre), within the instance's caps *)
  assert (HULL6 : @PresetHullBudget.hull_budget cp S6 []).
  { pose proof HP as HPh.
    destruct HPh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & Hos & _).
    destruct (PresetDrvHullA.drv_cf_hull_ok_at_call_A _ _ _ _ _ _ S6 Hos Hp0) as [Nh Th].
    rewrite PresetRoomPos.rp_nsec_layer in Nh. destruct HI_hull as [Kn Kt].
    unfold PresetHullBudget.hull_budget. change (Z.of_nat (PresetSecTotal.nsec [])) with 0.
    change (PresetSecTotal.tsec []) with 0. split; lia. }
  eapply (SRrG_mono SEGS WR).
  { exact (HT_fuzz_free fxk (c_most C) 0 ly6 S6 Hp6 W6 (ms_regs ms2) (ms_mem ms2) _ (dz_ch C ly6) q cap0 Lam6 peak6 _ _
      ran6 HF0 (fun _ => Hrm6) (fun _ => HC24 iZ h0 S6 Hp0) (fun _ => HULL6) (admits_ct_fix _ _ _ _ _ _ Htr) Q10
      (or_intror HinL) HLED6). }
  intros W' c' _ Hpost.
  unfold fpostbm in Hpost. eapply fpost_of_fpostb_fix in Hpost; [|exact Htr].
  destruct Hpost as (ly' & S' & Hp' & regs' & mem' & md' & kq & Hc & HJq & Hpr & (Hqt & Hmn)).
  exists ly', S', Hp', regs', mem', md', kq. split; [exact Hc|]. split; [exact HJq|]. split; [exact Hpr|].
  split; [|exact Hmn].
  destruct Hqt as (Hrmq & _ & _ & Hpnz & _ & _ & Harmq).
  split; [exact (Hrmq Hq0)|]. split.
  + intros _.
    destruct (Hpnz Hq0 ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) iZ (c_rp_H0 C) h0 Hp0
      (proj2 (prh_run_at_one _ _ _ _ _) Hev)) as (h & Hh). exists h.
    replace (c_rp_i C + length (crs_evs_at_H3 C))%nat with (iZ + length [PresetReqAt.HFr (cap0 + cf_head)])%nat;
      [exact Hh|].
    cbn [length]. unfold iZ, crs_evs_at_H3, crs_ev_wf, PresetReqAt.w_free. rewrite !length_app. cbn [length]. lia.
  + destruct Harmq as [(Hz & _) | (_ & A2 & _ & A4)]; [contradiction | exact (conj A2 A4)]. }
{ intros a Ha. destruct (Z.eqb_spec q 0) as [Eq0|Nq0]; [destruct Ha as (r & Hr & _); destruct Hr|].
  destruct Ha as (r & [<- | []] & Ha). cbn [fst snd] in Ha. right. left.
  exists (q - cf_head), (cap0 + cf_head). split; [exact (Permutation_in _ (Permutation_sym Hpb) (or_introl eq_refl))|].
  split; [|lia]. intros Hin. apply Hnin. apply (Permutation_in _ (Permutation_sym Hperm5)). exact Hin. }
intros W7 ly7 S7 Hp7 regs7 mem7 md7 k4 Hle7 HJ7 HJc7 HPr7 (HQ7 & HMN7).
destruct HQ7 as (Hrm7 & Hpos7 & Harms7).
assert (HFPx : forall a, cF C <= a < cF C + 128 \/ shadow_addr (cF C) <= a < shadow_addr (cF C) + 16 ->
  ~ inFP (if q =? 0 then [] else ablocks_fp [(q - cf_head, cap0 + cf_head)]) a).
{ intros a Ha (r & Hr & Hra). destruct (Z.eqb_spec q 0) as [Eq0|Nq0]; [destruct Hr|].
  destruct Hr as [<- | []]. cbn [fst snd] in Hra.
  destruct (dz_blk_frame_apart ly6 S6 Hp6 W6 (ms_mem ms2) _ (q - cf_head) (cap0 + cf_head) CRS_CID (c_fpos C) a HAR6
    (Permutation_in _ (Permutation_sym Hpb) (or_introl eq_refl)) Hfr6 Hra) as [N1 N2].
  rewrite EcF6 in N1, N2. change (fs_frame_bytes CRS_CID) with 128 in N1, N2. change (128 / 8) with 16 in N2.
  destruct Ha as [Ha|Ha]; [exact (N1 Ha) | exact (N2 Ha)]. }
pose proof (dz_keep WR CTX0 C fxk ly6 S6 Hp6 W6 (ms_regs ms2) (ms_mem ms2) _ (k + k1 + k2 + k3) sp2 _ _ ly7 S7 Hp7 W7
  regs7 mem7 md7 (k + k1 + k2 + k3 + k4) k4 HBc HJ7 HJc7 HFPx HPr7 HMN7) as HB7.
assert (HRG7 : crs_regsat regs7 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_pres _ _ _ HRG1 HPr7); vm_compute; reflexivity).
assert (R23_7 : getr regs7 23 = w64 (crs_cnt2 C)).
{ rewrite <- Q23. assert (E23 : Z_to_bv 5 23 = (23%bv : bv 5)) by (apply bv_eq; reflexivity).
  rewrite <- E23. apply HPr7. unfold acallee_saved. lia. }
(* the list and the blocks are back to Z's entry's *)
assert (HL7 : LEDGER ly7 S7 Hp7 W7 mem7 Lam3 peak6 (WriterApp.w_cnt st6) (WriterApp.w_fail st6) ran6 (c_most C) 0 /\
  Permutation (ablocks B ly7 S7) (ablocks B (c_ly C) (c_S C))).
{ destruct Harms7 as (_ & (b1 & b2 & Eb6 & Eb7) & l1 & l2 & EL & HLED7).
  pose proof (prh_ledger_nodup B _ _ _ _ _ _ _ _ _ _ _ _ HLED6) as Hnd. rewrite ELam in Hnd, EL.
  rewrite (dz_nodup_head Lam3 l1 l2 q cap0 _ Hnd EL) in HLED7. split; [exact HLED7|].
  rewrite Eb7. rewrite Eb6 in Hpb. apply Permutation_sym in Hpb. apply Permutation_cons_app_inv in Hpb.
  exact (Permutation_trans (Permutation_sym Hpb) Hperm5). }
destruct HL7 as [HLED7 Hperm7].
clear HS SHOK HEI HJr HBc HFRc HSVc Hg3c Hg4c HRG1 Q1 Q3 Q4 Q10 Q23 Qsp Qs0 HJc7 HPr7 HMN7.
(* ---- +980: jal fuzz_alloc_count (the count after the whole compact write) ---- *)
pose proof (dz_seat (c_regs C) regs7 (CRS_PC_Z + 36) cur_atoms W7 mem7 fxk (te_regs_ok _ _ _)) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (c_regs C) regs7 []) (mrestrict (w_H W7) mem7)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (c_regs C) regs7 [])) by apply te_env.
pose proof HB7 as HB7'. destruct HB7' as (_ & _ & _ & HJr & _). unfold crs_JR in HJr.
paj_run_tok_x RUN HS HJr SHOK DZ_SPAN; [cbn [ss_mem]; apply awr_ok_nil|].
cbn [ss_mem] in HF. apply dz_mem_nil in HF. subst mem7. clear HFr HG.
prreg HS (1%bv : bv 5) Q1.
pose proof (ts_reg_kept_c (c_regs C) regs7 [] _ _ ms3 3%bv 3%bv HS ltac:(vm_compute; reflexivity)) as Q3.
pose proof (ts_reg_kept_c (c_regs C) regs7 [] _ _ ms3 4%bv 4%bv HS ltac:(vm_compute; reflexivity)) as Q4.
pose proof (ts_reg_kept_c (c_regs C) regs7 [] _ _ ms3 23%bv 23%bv HS ltac:(vm_compute; reflexivity)) as Q23.
rewrite R23_7 in Q23.
assert (HRG1 : crs_regsat (ms_regs ms3) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_run _ _ _ _ _ _ fxk HS); [vm_compute; reflexivity | exact HRG7]).
assert (Qsp : spZ (ms_regs ms3) = sp2) by (unfold spZ; rewrite (dz_regsat_in _ _ 2%bv sp2 HRG1) by (cbn; left; reflexivity);
  unfold w64; rewrite unsigned_lit_small by (clear -Hs1 Hs2 Hsp0 EF C1; lia); reflexivity).
assert (Qs0 : getr (ms_regs ms3) 8 = w64 (spZ (c_regs C))) by dz_reg HRG1.
assert (HBc := dz_base_run WR CTX0 C fxk _ _ _ _ _ _ _ _ _ _ _ HB7 HJr Q3 Q4).
pose proof HBc as HBc'. destruct HBc' as (_ & _ & _ & _ & HFRc & HSVc & _ & _ & _ & Hg3c & Hg4c & _).
eapply (dz_call WR WRr WRt (@wle SEGS) WRw CTX0 C fxk W7 _ _ ms3 _ ly7 S7 Hp7 (k + k1 + k2 + k3 + k4) sp2 (CRS_PC_Z + 40)
  0 [] _ _ HP HS eq_refl HJr HSVc Qsp Hs1 Hs2 Hs3 (proj1 (proj2 HBc)));
  [ exact Hg3c | exact Hg4c | exact Qs0 | rewrite Q1, EZ; reflexivity | rewrite EZ; lia
  | rewrite EZ; reflexivity | lia | rewrite EF, ES; lia
  | intros HF0; exact (HT_fuzz_alloc_count fxk ly7 S7 Hp7 W7 (ms_regs ms3) (ms_mem ms3) _ (dz_ch C ly7) Lam3 peak6
      _ _ ran6 (c_most C) 0 HF0 HLED7)
  | intros a (r & Hr & _); destruct Hr | ].
intros W8 ly8 S8 Hp8 regs8 mem8 md8 k5 Hle8 HJ8 HJc8 HPr8 (HQ8 & HMN8).
destruct HQ8 as (Hrm8 & Ha08 & -> & -> & Hab8 & HLED8).
pose proof (dz_keep WR CTX0 C fxk ly7 S7 Hp7 W7 (ms_regs ms3) (ms_mem ms3) _ (k + k1 + k2 + k3 + k4) sp2 0 [] ly8 S7 Hp7
  W8 regs8 mem8 md8 (k + k1 + k2 + k3 + k4 + k5) k5 HBc HJ8 HJc8 ltac:(intros a _ (r & Hr & _); destruct Hr) HPr8 HMN8)
  as HB8.
assert (HRG8 : crs_regsat regs8 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_pres _ _ _ HRG1 HPr8); vm_compute; reflexivity).
assert (R23_8 : getr regs8 23 = w64 (crs_cnt2 C)).
{ rewrite <- Q23. assert (E23 : Z_to_bv 5 23 = (23%bv : bv 5)) by (apply bv_eq; reflexivity).
  rewrite <- E23. apply HPr8. unfold acallee_saved. lia. }
clear HS SHOK HEI HJr HBc HFRc HSVc Hg3c Hg4c HRG1 Q1 Q3 Q4 Q23 Qsp Qs0 HJc8 HPr8 HMN8.
(* ---- the boundary at +984: the compact write's count and flag, the list and blocks back, the position ---- *)
set (kk := Z.of_nat k6) in *.
assert (HN0e : cN0 C = Z.of_nat (length (WriterSpec.grow_calls 0 0
  (WriterSpec.piece_lens (WriterValue.wdpieces (c_t C) false))))) by reflexivity.
assert (HKF : crs_kfull C false kk ran6).
{ split; [unfold kk, PjWriteHyp.wcalls; lia|]. intros _. unfold kk, PjWriteHyp.wcalls. rewrite (Hfail0 Hok0). reflexivity. }
assert (Hwc' : WriterApp.w_cnt st6 = crs_cnt2 C + kk) by exact Hwc.
rewrite Hwc', Hwf in HLED8. rewrite Hwc' in Ha08.
assert (Hab8' : Permutation (ablocks B ly8 S7) (ablocks B (c_ly C) (c_S C))) by (rewrite Hab8; exact Hperm7).
assert (Hran0 : c_ran C = 0) by (destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Hr0 & _); exact Hr0).
assert (HLV8 : crs_live B C ly8 S7 Hp7 W8 mem8 Lam3 peak6 (crs_cnt2 C + kk) ran6 (crs_evs_at_H3 C)).
{ split; [|split; [exact (proj1 HPERM) | exact Hab8']].
  split; [exact HLED8|]. split; [lia|]. split; [rewrite R6, Hran0; reflexivity|].
  split; [lia|]. split; [lia|]. split; [exact Hrm7|]. exact Hpos7. }
(* ---- +984 .. +996: beq a0, s7 -> R refuted (kk >= 1); lbu a0, 540(s8) reads g_own_ran_out, which the boundary's
   ledger holds at 0 (prh_ledger_own, kit v3): the OWN arm `bnez a0` (+992) is not taken; jal fuzz_alloc_ran_out ---- *)
destruct (prh_ledger_own B _ _ _ _ _ _ _ _ _ _ _ _ HLED8) as [HOV _].
assert (R24 : getr regs8 24 = w64 CRS_RO) by dz_reg HRG8.
assert (ERO : CRS_RO = 6148900) by (vm_compute; reflexivity).
set (rown := YP09.mkRegion (Some 56%nat) 540 541 0 0 [YP09.mkChunk 540 (CVal 1 (SLit 0))]).
assert (HS : @st_ok_pi SEGS VAL fxk (TE (c_regs C) regs8 []) (mkSS (CRS_PC_Z + 40) cur_atoms [rown] None (mkFacts [] [] []))
  (restrict (w_H W8) (@YK11.mkst fxk regs8 (Z_to_bv 64 (BASE + (CRS_PC_Z + 40))) mem8 (YK11.seg_rom SEGS)))).
{ apply (@ts_st_ok fxk rc (c_regs C) regs8 [] (CRS_PC_Z + 40) cur_atoms [rown] (mkFacts [] [] []) W8 mem8 (te_regs_ok _ _ _)).
  - vm_compute. reflexivity.
  - constructor; [|constructor]. apply (ts_rok _ _ 56%nat CRS_RO).
    + change 56%nat with (32 + 24)%nat. rewrite (te_cur (c_regs C) regs8 [] 24%bv 24 eq_refl), R24.
      unfold w64. rewrite unsigned_lit_small by (rewrite ERO; lia). reflexivity.
    + rewrite ERO. lia.
    + rewrite ERO. lia.
    + intros o Ho. lia.
    + constructor; [|constructor]. apply (ts_chunk _ _ CRS_RO 540 1%N (SLit 0) 0); [reflexivity | lia | lia |].
      replace (CRS_RO + 540) with (@pi_g_own_ran_out prh_img_A) by (unfold CRS_RO, CRS_OFF_OWN; lia).
      exact HOV.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (c_regs C) regs8 []) (mrestrict (w_H W8) mem8)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (c_regs C) regs8 [])) by apply te_env.
pose proof HB8 as HB8'. destruct HB8' as (_ & _ & _ & HJr & _). unfold crs_JR in HJr.
paj_run_tok_x RUN HS HJr SHOK DZ_SPAN.
{ cbn [ss_mem]. intros a (r & Hr & Ha). destruct Hr as [<- | []]. unfold rown in Ha.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
assert (Hnw : forall a, ~ in_wrange (TE (c_regs C) regs8 []) [rown] a).
{ intros a (r & Hr & Ha). destruct Hr as [<- | []]. unfold rown in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
cbn [ss_mem] in HF. apply (dz_mem_nowr _ _ _ _ Hnw) in HF. subst mem8. clear HFr HG.
pose (BR := paj_branchR (fx := fxk) (rc := rc) (L := A_prog_listing) (PI := PA) WR).
psrr_branch_tok RUN BR HS SHOK DZ_SPAN.
{ (* count == before (+984): the compact write made kk >= 1 calls *)
  exfalso. rewrite (dz_sv_cur _ _ 10%bv 42 eq_refl), (dz_sv_cur _ _ 23%bv 55 eq_refl) in Hc.
  cbn [branch_taken] in Hc. rewrite Ha08, R23_8 in Hc. apply bv_eqb_eq in Hc. apply (f_equal bv_unsigned) in Hc.
  unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia. destruct HKF as [HK1 _]. lia. }
paj_run_tok_x RUN HS HJr SHOK DZ_SPAN.
{ cbn [ss_mem add_cond]. intros a (r & Hr & Ha). destruct Hr as [<- | []]. unfold rown in Ha.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
cbn [ss_mem add_cond] in HF. apply (dz_mem_nowr _ _ _ _ Hnw) in HF. rewrite <- HF in *. clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1.
pose proof (ts_reg_kept_c (c_regs C) regs8 [] _ _ ms5 3%bv 3%bv HS ltac:(vm_compute; reflexivity)) as Q3.
pose proof (ts_reg_kept_c (c_regs C) regs8 [] _ _ ms5 4%bv 4%bv HS ltac:(vm_compute; reflexivity)) as Q4.
pose proof (ts_reg_kept_c (c_regs C) regs8 [] _ _ ms5 23%bv 23%bv HS ltac:(vm_compute; reflexivity)) as Q23.
rewrite R23_8 in Q23.
assert (HRG1 : crs_regsat (ms_regs ms5) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_run _ _ _ _ _ _ fxk HS); [vm_compute; reflexivity | exact HRG8]).
assert (Qsp : spZ (ms_regs ms5) = sp2) by (unfold spZ; rewrite (dz_regsat_in _ _ 2%bv sp2 HRG1) by (cbn; left; reflexivity);
  unfold w64; rewrite unsigned_lit_small by (clear -Hs1 Hs2 Hsp0 EF C1; lia); reflexivity).
assert (Qs0 : getr (ms_regs ms5) 8 = w64 (spZ (c_regs C))) by dz_reg HRG1.
assert (HBc := dz_base_run WR CTX0 C fxk _ _ _ _ _ _ _ _ _ _ _ HB8 HJr Q3 Q4).
pose proof HBc as HBc'. destruct HBc' as (_ & _ & _ & _ & HFRc & HSVc & _ & _ & _ & Hg3c & Hg4c & _).
eapply (dz_call WR WRr WRt (@wle SEGS) WRw CTX0 C fxk W8 _ _ ms5 _ ly8 S7 Hp7 (k + k1 + k2 + k3 + k4 + k5) sp2
  (CRS_PC_Z + 56) 0 [] _ _ HP HS eq_refl HJr HSVc Qsp Hs1 Hs2 Hs3 (proj1 (proj2 HBc)));
  [ exact Hg3c | exact Hg4c | exact Qs0 | rewrite Q1, EZ; reflexivity | rewrite EZ; lia
  | rewrite EZ; reflexivity | lia | rewrite EF, ES; lia
  | intros HF0; exact (HT_fuzz_alloc_ran_out fxk ly8 S7 Hp7 W8 (ms_regs ms5) (ms_mem ms5) _ (dz_ch C ly8) Lam3 peak6
      _ _ ran6 (c_most C) 0 HF0 HLED8)
  | intros a (r & Hr & _); destruct Hr | ].
intros W9 ly9 S9 Hp9 regs9 mem9 md9 k6' Hle9 HJ9 HJc9 HPr9 (HQ9 & HMN9).
destruct HQ9 as (Hrm9 & Ha09 & -> & -> & Hab9 & HLED9).
pose proof (dz_keep WR CTX0 C fxk ly8 S7 Hp7 W8 (ms_regs ms5) (ms_mem ms5) _ (k + k1 + k2 + k3 + k4 + k5) sp2 0 [] ly9 S7
  Hp7 W9 regs9 mem9 md9 (k + k1 + k2 + k3 + k4 + k5 + k6') k6' HBc HJ9 HJc9 ltac:(intros a _ (r & Hr & _); destruct Hr)
  HPr9 HMN9)
  as HB9.
assert (HRG9 : crs_regsat regs9 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
  by (apply (dz_regsat_pres _ _ _ HRG1 HPr9); vm_compute; reflexivity).
assert (R23_9 : getr regs9 23 = w64 (crs_cnt2 C)).
{ rewrite <- Q23. assert (E23 : Z_to_bv 5 23 = (23%bv : bv 5)) by (apply bv_eq; reflexivity).
  rewrite <- E23. apply HPr9. unfold acallee_saved. lia. }
clear HS SHOK HEI HJr HBc HFRc HSVc Hg3c Hg4c HRG1 Q1 Q3 Q4 Q23 Qsp Qs0 HJc9 HPr9 HMN9.
(* ---- the boundary facts at +1000 that both exits share: the input and the tree, the list and blocks ---- *)
pose proof HB9 as HB9'. destruct HB9' as (_ & _ & _ & HJ9c & _).
assert (Hperm9 : Permutation (ablocks B ly9 S7) (ablocks B (c_ly C) (c_S C))) by (rewrite Hab9; exact Hab8').
pose proof (dz_dat_keep WR CTX0 C ly3 S3 Hp3 W3 (ms_mem ms) md3 k ly9 S7 Hp7 W9 mem9 md9 (k + k1 + k2 + k3 + k4 + k5 + k6')
  Lam3 peak3 (crs_cnt2 C) SIZE_MAXZ 0 (c_most C) 0 Lam3 peak6 (crs_cnt2 C + kk) SIZE_MAXZ ran6 (c_most C) 0 HP HK HJ
  HJ9c (proj2 HPERM) Hperm9 HLED HLED9 (Permutation_refl _) HD) as HD9.
pose proof (dz_tree_keep WR CTX0 C ly3 S3 Hp3 W3 (ms_mem ms) md3 k ly9 S7 Hp7 W9 mem9 md9 (k + k1 + k2 + k3 + k4 + k5 + k6')
  Lam3 peak6 (crs_cnt2 C + kk) SIZE_MAXZ ran6 (c_most C) 0 HP HK HJ HJ9c (proj2 HPERM) Hperm9 HLED9 HT) as HT9.
pose proof HLV8 as ((_ & Hpk8 & _ & _ & _ & Hrm8' & Hps8) & _).
(* ---- +1000: bnez a0 (a0 = g_ran_out = ran6 = 0): the RAN arm (to R, +688) is refuted; H3 (+1004) ---- *)
try clear Hc.
pose proof (dz_seat (c_regs C) regs9 (CRS_PC_Z + 56) cur_atoms W9 mem9 fxk (te_regs_ok _ _ _)) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (c_regs C) regs9 []) (mrestrict (w_H W9) mem9)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (c_regs C) regs9 [])) by apply te_env.
pose proof HB9 as HB9''. destruct HB9'' as (_ & _ & _ & HJr & _). unfold crs_JR in HJr.
pose (RUNTO := @paj_run_to_xR fxk rc SK A_prog_listing PL PA B PST ARx _ LAWS WR WRr WRt).
psrr_branch_tok RUN BR HS SHOK DZ_SPAN.
- (* g_ran_out <> 0: the RAN arm (to R) is refuted, a0 = g_ran_out = ran6 = 0 *)
  exfalso. rewrite (dz_sv_cur _ _ 10%bv 42 eq_refl) in Hc. cbn [branch_taken sv_denot] in Hc. rewrite Ha09, R6 in Hc.
  vm_compute in Hc. discriminate.
- (* g_ran_out = 0: nothing was refused, to H3 *)
  clear Hc.
  paj_run_to_tok_x RUNTO HS HJr SHOK DZ_SPAN CRS_PC_H3.
  { apply awr_ok_nil. }
  cbn [ss_mem add_cond] in HF. apply dz_mem_nil in HF.
  pose proof (ts_reg_kept_c (c_regs C) regs9 [] _ _ ms6 3%bv 3%bv HS ltac:(vm_compute; reflexivity)) as Q3.
  pose proof (ts_reg_kept_c (c_regs C) regs9 [] _ _ ms6 4%bv 4%bv HS ltac:(vm_compute; reflexivity)) as Q4.
  pose proof (ts_reg_kept_c (c_regs C) regs9 [] _ _ ms6 23%bv 23%bv HS ltac:(vm_compute; reflexivity)) as Q23.
  rewrite R23_9 in Q23.
  assert (HRG1 : crs_regsat (ms_regs ms6) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
    by (apply (dz_regsat_run _ _ _ _ _ _ fxk HS); [vm_compute; reflexivity | exact HRG9]).
  rewrite HF in HJr.
  assert (HBH := dz_base_run WR CTX0 C fxk _ _ _ _ _ _ _ _ _ _ _ HB9 HJr Q3 Q4).
  pmkst HS. rewrite HF.
  lazymatch goal with |- SRrG _ _ _ (mkCfg (YK11.mkst _ (Z_to_bv 64 ?p) _ _) _) _ =>
    replace p with (BASE + CRS_PC_H3) by (vm_compute; reflexivity) end.
  subst ran6.
  assert (Ekk : kk = cN0 C) by (pose proof HKF as (_ & HK2); rewrite HN0e; unfold PjWriteHyp.wcalls in HK2;
    rewrite (HK2 eq_refl); reflexivity).
  rewrite Ekk in HLED9.
  apply (HH3 fxk ly9 S7 Hp7 W9 (ms_regs ms6) mem9 _ (k + k1 + k2 + k3 + k4 + k5 + k6') sp2 Lam3 peak6 Hdoc HBH).
  + pose proof HRG1 as Hx. apply dz_regsat_app in Hx as [A1 Hx]. apply dz_regsat_app in Hx as [A2 Hx].
    apply dz_regsat_app in Hx as [A3 Hx]. apply dz_regsat_app in Hx as [A4 A5].
    apply dz_regsat_app; split; [exact A1|]. apply dz_regsat_app; split; [exact A2|].
    apply dz_regsat_app; split; [exact A3|]. apply dz_regsat_app; split; [exact A4|].
    apply dz_regsat_app; split; [exact A5|]. constructor; [exact Q23 | constructor].
  + split; [|split; [exact (proj1 HPERM) | exact Hperm9]].
    split; [exact HLED9|]. split; [exact Hpk8|]. split; [exact (eq_sym Hran0)|]. split; [lia|]. split; [lia|].
    split; [exact (Hrm9 Hrm8')|]. exact Hps8.
  + exact HD9.
  + exact HT9.
Qed.

End f.
End d.

(* the closing lemma, elaborated (the class position of each kit predicate holds the entry fx; fxk is crs_cfg's
   explicit current state) and its assumptions *)
Set Printing Implicit.
Unset Printing Notations.
About crs_seg_Z.
Print crs_cnt24_Z.
Set Printing Notations.
Unset Printing Implicit.
Print Assumptions crs_seg_Z.
