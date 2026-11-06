(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PvB_NA.v, with its module paths and module names changed; 845 of its 924 lines of code are new or changed and 880 lines of the source are left out. *)
(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c, segment D (the DISPATCH): the CONTAINER
   CALL ARM. From parse_items' entry (`jal parse_items` at B 0x86628, a0 = q, a1 = v, a2 = 1 for '{' / 0 for '[') to
   the shared exit 0x8664c: the kit's parse_items text (lib/A/PRH_FnParse.v tparse_items_specX d CTX CTX0 CW at the batch kit's tip
   at CTX := [the callee's own context]; BUDGETED: post fpostWFbm at wbudget CW 0) through YCbqGwild.v's
   aj_call_xWFbR at wle' segs RZ_cf from the C1 journal at the empty budget (the float state after the call is the callee's),
   then one engine stretch from a FRESH symbolic state at the return 0x8662c (`j 86648`, `mv s5, a0`) to the exit on
   the caller's journal REBASED at the post-call depot, and the exit cut pv_at_exit (pv_body_x: the journal unbased at
   the callee's budget WS1) with pv_Qm by PvB_D_Items.v pvD_Qm_items (carried to the run's pointwise-equal memory by
   pvi_Qm_ext). The wild-room form's call premises: prh_cw_entry at the CALL registers (the s0 - 8 words q - 8 / q + 8
   are the entry's: pv_pre's prh_cw_entry, pvi_cw_call) and wild_room .. CW 0 at the call depot (pv_pre's at entry
   across the C1 journal, ajournal_xw_room).
   KIT: parse_items' text is the post-implication form (PRH_FnParse.v blob 105eb463e190): it takes memnorm at the
   call memory (pvd_cs), the #102 ledger statics most / own (kept), fpre with
   frm_zero at the entry float state (parse_value's fx0 before strtod: rd_pre's first conjunct), and the two live-count
   premises over the all-granted events rd_hevs (prhPi_gtrace ..) at the call state (PvB_D_Items.v pvi_counts:
   pv_pre's over parse_value's granted run, which at the opener IS parse_items', carried to the call state by
   pv_reader0's room keep); its m-form post (fpostWFbm) gives the live list and the run position moved by rd_hevs tr,
   which pvD_Qm_items composes with the keep from entry into pv_Qm's room post (PvB_Room.v rp_call), and the memnorm
   keep, carried across the exit stretch by YC1fPx.v's paj_run_to_x_invR at wle' segs RZ_cf. fpre's return-address
   bound at the call is the jal's return slot (PvB_D_Kit.v pvd_ret_lt_ceil).
   The text's call-state premises: the cursor words the free trace reads (prh_cur_entry's s0 - 16 word and
   prh_cw_entry's s0 - 8 word at the CALL registers, whose sp is below q - 16, so they read the call view at
   q - 16 .. q + 8: q's p word is p1 < alloc_ceiling by pj_in_okR, the others are parse_value's saved ra / s0 or the
   entry view by pv_body's window clause, pvi_kw); the cursor chain at q
   (q = sp0 is parse_value's own record, pv_chain; q = sp0 + 8 is one record whose next frame word is the saved ra,
   below alloc_ceiling by prh_cur_entry; q >= sp0 + 16 is the entry chain from q with q's p word patched); the chain at
   prh_s0 F_parse_items q = q + 16 (one record: ra = the end word text + len, next = the p word p1, so it stops).
   prh_cur_entry's chain conjunct at the CALL registers (the kit's PRH_Base.v (sha256 586b1b19f7ad; internal record): no call-view chain
   from (sp, s0) keeps a record at fp = q + 8): parse_value is a frame-pointer function, so the call's s0 is the entry
   sp sp0 and the chain's first record is parse_value's own (fp = sp0 <= q); its next frame word is the entry s0, which
   is >= sp0 + 16 (the entry chain of afn_pre_x exists, and the entry window puts q + 24 below the stack top; q = sp0
   with s0 = sp0 + 8 is excluded by prh_cur_entry's word at q - 16); from there the chain reads only words at or above
   sp0, the entry view's but for q's p word, so a record at q + 8 would be one of an entry-view chain cut at the layout
   top q + 32 (pvi_fpchain_q8), which the entry's own chain conjunct excludes.
   Numerals: 20320 / 20352 listing offsets (PvB_D_Call AF_pv_items_ret, PvB_Defs AF_pv_exit); 176 / 144 parse_value's
   / parse_items' frame (PRH_Img pi_frame), 320 / 16560 DERIVED (their sum, LEAF_pv_pi of prh_img_B); 16 / 24 / 56 /
   4 / 8 / 64 the cursor, node and class-0 frame layout (LENGTH); 2 ^ 44 .. 2 ^ 64, 4096 ranges (LENGTH).
   Rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjTree PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_D_Kit PvB_D_Call PvB_D_Items.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Instance PIB : PrhImg := prh_img_B.

(* ---- the stretch's symbolic state at parse_items' return (B 0x8662c): every register its own atom, no region, no
   fact (the two instructions read no memory); no shadow entry, so the shadow span is the point (0, 0) ---- *)
Definition PVI_Bx : sv := SLit SHADOW_OFF.
Definition PVI_Bspan : Z * Z := (0, 0).

(* ---- pure helpers ---- *)
Lemma pvi_nth_error_skipn : forall (l : list Z) k b rest, skipn k l = b :: rest -> nth_error l k = Some b.
Proof.
induction l as [|x l IH]; intros [|k] b rest H; cbn in H |- *; try discriminate.
- congruence.
- exact (IH k b rest H).
Qed.
(* a kept register (aregs_preserved's `Z_to_bv 5 r` form) read at its literal index (PvB_A.v pva_getr_lit) *)
Lemma pvi_getr_lit : forall (regs regs' : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z ->
  getr regs' (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z) -> getr regs' r = getr regs r.
Proof. intros regs regs' r z Hr H. subst z. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac pvi_keep P rlit z := exact (pvi_getr_lit _ _ rlit z eq_refl (P z ltac:(unfold acallee_saved; lia))).
(* the chain start of the two cursor functions on image B: s0 = q (parse_string), s0 = q + 16 (parse_items) *)
Lemma pvi_s0_ps : forall q, prh_s0 F_parse_string q = q.
Proof.
intros q. unfold prh_s0. destruct (pi_s0cur F_parse_string) as [kk|] eqn:E; vm_compute in E;
  first [discriminate E | injection E as E; lia | lia].
Qed.
Lemma pvi_s0_pi : forall q, prh_s0 F_parse_items q = q + 16.
Proof.
intros q. unfold prh_s0. destruct (pi_s0cur F_parse_items) as [kk|] eqn:E; vm_compute in E;
  first [discriminate E | injection E as E; lia | lia].
Qed.
(* a frame-pointer chain under a view that changed ONE 8-aligned word X (PvB_A.v pva_fpchain_patch /
   pva_achain_patch, restated here: PvB_A.v was under edit) *)
Lemma pvi_fpchain_patch : forall (rd rd' : reader) X L top ch bp,
  fpchain (rdword rd) bp top ch -> L + 16 <= bp -> bp + 16 <= top -> bp mod 8 = 0 -> X mod 8 = 0 ->
  (forall a, L <= a -> a + 8 <= top -> a mod 8 = 0 -> a <> X -> rdword rd' a = rdword rd a) ->
  (exists w, rdword rd' X = Some w /\ 4096 <= w < L) ->
  (exists w0, rdword rd X = Some w0 /\ 4096 <= w0) ->
  exists ch', fpchain (rdword rd') bp top ch' /\ Forall (fun r => bp <= fst (fst r)) ch'.
Proof.
intros rd rd' X L top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc HL Htop Hb8 HX8 Hag Hw' Hw0.
- destruct Hc as (r & Hr & Hr4).
  assert (Hne : bp - 8 <> X).
  { intros E. destruct Hw0 as (w0 & Hw0 & H4). rewrite <- E, Hr in Hw0. injection Hw0 as Ew. lia. }
  exists []. split; [|constructor]. exists r. split; [|exact Hr4]. rewrite (Hag (bp - 8)) by lia. exact Hr.
- destruct Hc as (Efp & Hal & Hra & Hnfp & Hra4 & Hrest). subst fp.
  assert (Hra' : exists ra', rdword rd' (bp - 8) = Some ra' /\ 4096 <= ra').
  { destruct (Z.eq_dec (bp - 8) X) as [E8 | N8].
    - destruct Hw' as (w & Hw & Hw4 & _). exists w. rewrite E8. split; [exact Hw | exact Hw4].
    - exists ra. rewrite (Hag (bp - 8)) by lia. split; [exact Hra | exact Hra4]. }
  destruct Hra' as (ra' & Hra'1 & Hra'2).
  destruct (Z.eq_dec (bp - 16) X) as [E16 | N16].
  + destruct Hw' as (w & Hw & Hwlo & Hwhi). exists [(bp, ra', w)].
    split; [|constructor; [cbn; lia | constructor]].
    cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'1|].
    split; [rewrite E16; exact Hw|]. split; [exact Hra'2|].
    replace (bad_next bp top w) with true; [reflexivity|]. unfold bad_next. symmetry.
    apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
  + assert (Hn' : rdword rd' (bp - 16) = Some nfp) by (rewrite (Hag (bp - 16)) by lia; exact Hnfp).
    destruct (bad_next bp top nfp) eqn:Hbad.
    * exists [(bp, ra', nfp)]. split; [|constructor; [cbn; lia | constructor]].
      cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'1|]. split; [exact Hn'|].
      split; [exact Hra'2|]. rewrite Hbad. reflexivity.
    * pose proof Hbad as Hbad'. unfold bad_next in Hbad'.
      apply Bool.orb_false_iff in Hbad' as [Hb12 Hb3]. apply Bool.orb_false_iff in Hb12 as [Hb1 Hb2].
      apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply Bool.negb_false_iff, Z.eqb_eq in Hb3.
      change (fpchain (rdword rd) nfp top rest) in Hrest.
      destruct (IH nfp Hrest ltac:(lia) ltac:(lia) Hb3 HX8 Hag Hw' Hw0) as (ch' & Hc' & Hf').
      exists ((bp, ra', nfp) :: ch'). split.
      -- cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'1|]. split; [exact Hn'|].
         split; [exact Hra'2|]. rewrite Hbad. exact Hc'.
      -- constructor; [cbn; lia|]. eapply Forall_impl; [|exact Hf']. intros r Hr. cbn beta in Hr |- *. lia.
Qed.

(* the call view's chain from bp keeps no record at fp = q + 8 when no entry-view chain from bp at the layout top
   q + 32 keeps one: the two views agree on the words below q from L up, and the entry view's word at q is >= 4096, so
   a call-view record at q + 8 (reached through records below q, read the same) is one of an entry-view chain, which
   bad_next stops right after it at that top *)
Lemma pvi_fpchain_q8 : forall (rd rd' : reader) q L top ch bp,
  fpchain (rdword rd') bp top ch -> L + 16 <= bp -> bp mod 8 = 0 -> q mod 8 = 0 ->
  (forall a, L <= a -> a + 8 <= q -> rdword rd' a = rdword rd a) ->
  (exists w, rdword rd q = Some w /\ 4096 <= w) ->
  (forall ch0, fpchain (rdword rd) bp (q + 32) ch0 -> Forall (fun r => fst (fst r) <> q + 8) ch0) ->
  Forall (fun r => fst (fst r) <> q + 8) ch.
Proof.
intros rd rd' q L top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc HL Hb8 Hq8 Hag Hw0 HE;
  [constructor|].
pose proof (fpchain_fps_increase _ _ _ _ Hc) as Hinc.
destruct (Z_lt_le_dec (q + 8) bp) as [Hgt | Hle].
{ eapply Forall_impl; [|exact Hinc]. intros r Hr. cbn beta in Hr |- *. lia. }
destruct Hc as (Efp & Hal & Hra & Hnfp & Hra4 & Hrest). subst fp.
destruct (Z.eq_dec bp (q + 8)) as [Eb | Nb].
- (* a record at q + 8: the entry view has it too, and stops right after it at the top q + 32 *)
  exfalso. subst bp. destruct Hw0 as (w0 & Hw0 & Hw4).
  assert (Hn0 : rdword rd (q + 8 - 16) = Some nfp) by (rewrite <- (Hag (q + 8 - 16)) by lia; exact Hnfp).
  assert (Hb : bad_next (q + 8) (q + 32) nfp = true).
  { unfold bad_next. destruct (Z_le_gt_dec nfp (q + 8)) as [H1 | H1].
    - apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. exact H1.
    - destruct (Z.eq_dec (nfp mod 8) 0) as [H2 | H2].
      + apply orb_true_intro. left. apply orb_true_intro. right. apply Z.leb_le. lia.
      + apply orb_true_intro. right. apply negb_true_iff, Z.eqb_neq. exact H2. }
  assert (Hc0 : fpchain (rdword rd) (q + 8) (q + 32) [(q + 8, w0, nfp)]).
  { cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|].
    split; [replace (q + 8 - 8) with q by lia; exact Hw0|]. split; [exact Hn0|]. split; [exact Hw4|].
    rewrite Hb. reflexivity. }
  pose proof (Forall_inv (HE _ Hc0)) as Hh. cbn [fst] in Hh. exact (Hh eq_refl).
- (* bp <= q: the record reads below q, the same word in both views *)
  assert (Hbq : bp <= q) by lia.
  constructor; [cbn [fst]; lia|].
  destruct (bad_next bp top nfp) eqn:Hbad; [subst rest; constructor|].
  pose proof Hbad as Hbad'. unfold bad_next in Hbad'.
  apply Bool.orb_false_iff in Hbad' as [Hb12 Hb3]. apply Bool.orb_false_iff in Hb12 as [Hb1 Hb2].
  apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply Bool.negb_false_iff, Z.eqb_eq in Hb3.
  change (fpchain (rdword rd') nfp top rest) in Hrest.
  destruct (Z_lt_le_dec (q + 8) nfp) as [Hng | Hnl].
  { pose proof (fpchain_fps_increase _ _ _ _ Hrest) as Hinc'.
    eapply Forall_impl; [|exact Hinc']. intros r Hr. cbn beta in Hr |- *. lia. }
  apply (IH nfp Hrest ltac:(lia) Hb3 Hq8 Hag Hw0).
  intros ch0 Hc0.
  assert (Hra0 : rdword rd (bp - 8) = Some ra) by (rewrite <- (Hag (bp - 8)) by lia; exact Hra).
  assert (Hn0 : rdword rd (bp - 16) = Some nfp) by (rewrite <- (Hag (bp - 16)) by lia; exact Hnfp).
  assert (Hb' : bad_next bp (q + 32) nfp = false).
  { unfold bad_next. apply Bool.orb_false_iff. split; [apply Bool.orb_false_iff; split; apply Z.leb_gt; lia|].
    apply Bool.negb_false_iff, Z.eqb_eq. exact Hb3. }
  assert (Hc1 : fpchain (rdword rd) bp (q + 32) ((bp, ra, nfp) :: ch0)).
  { cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra0|]. split; [exact Hn0|].
    split; [exact Hra4|]. rewrite Hb'. exact Hc0. }
  exact (Forall_inv_tail (HE _ Hc1)).
Qed.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation PSTX := (@prh_pst prh_img_B).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Lemma pvi_achain_patch : forall ly (rd rd' : reader) sp v ch X,
  achain ly rd sp v ch -> X mod 8 = 0 ->
  (forall a, sp <= a -> a + 8 <= ly_top ly -> a mod 8 = 0 -> a <> X -> rdword rd' a = rdword rd a) ->
  (exists w, rdword rd' X = Some w /\ 4096 <= w < sp) -> (exists w0, rdword rd X = Some w0 /\ 4096 <= w0) ->
  exists ch', achain ly rd' sp v ch'.
Proof.
intros ly rd rd' sp v ch X [(Hb & ->) | (H1 & H2 & H3 & H4 & H5)] HX Hag Hw' Hw0.
- exists []. left. split; [exact Hb | reflexivity].
- destruct (pvi_fpchain_patch rd rd' X sp (ly_top ly) ch v H4 ltac:(lia) ltac:(lia) H3 HX Hag Hw' Hw0)
    as (ch' & Hc' & Hf').
  exists ch'. right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact Hc'|].
  eapply Forall_impl; [|exact Hf']. intros r Hr. cbn beta in Hr. lia.
Qed.

(* ---- engine-free byte helpers (PvB_A.v's pva_rdword_of_val / pva_val_lit / pva_wr_keep / pva_ro_img, restated:
   PvB_A.v was under edit) ---- *)
Lemma pvi_rdword_of_val : forall H mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (YG0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (YO0f.le_byte v 8 k) with (YG0f.le_byte v 8 k). unfold YG0f.le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma pvi_val_lit : forall m a (n : nat) regs (r : bv 5) z, bv_unsigned r = z ->
  val_mem SEGS m a n (bv_unsigned (getr regs (Z_to_bv 5 z))) -> val_mem SEGS m a n (bv_unsigned (getr regs r)).
Proof. intros m a n regs r z Hr H. subst z. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma pvi_wr_keep : forall (m m' : word -> option byte) x, writable_at SEGS m x -> mbyte SEGS m' x = mbyte SEGS m x ->
  0 <= x < 2 ^ 64 -> ~ in_img SEGS x -> writable_at SEGS m' x.
Proof.
intros m m' x Hw Hb Hx Hn. unfold writable_at, wview in *. unfold mbyte in Hb.
destruct (m' (Z_to_bv 64 x)) as [b'|]; [discriminate|].
destruct (m (Z_to_bv 64 x)) as [b|]; [|exact Hw].
rewrite (seg_rom_none SEGS x Hx Hn) in Hb. discriminate Hb.
Qed.
Lemma pvi_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* a word of 8 visible bytes is read, and it is not negative *)
Lemma pvi_rdword_some : forall H mem a, (forall i, 0 <= i < 8 -> aview SEGS H mem (a + i) <> None) ->
  exists w, rdword (aview SEGS H mem) a = Some w /\ 0 <= w.
Proof.
intros H mem a Hv.
assert (B8 : forall i, 0 <= i < 8 -> exists b, aview SEGS H mem (a + i) = Some b /\ 0 <= b < 256).
{ intros i Hi. specialize (Hv i Hi). unfold aview in *.
  destruct (mbyte SEGS (mrestrict H mem) (a + i)) as [b|]; [|exfalso; apply Hv; reflexivity].
  exists (bv_unsigned b). split; [reflexivity|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. cbn in Hb. lia. }
destruct (B8 0 ltac:(lia)) as (b0 & E0 & R0). destruct (B8 1 ltac:(lia)) as (b1 & E1 & R1).
destruct (B8 2 ltac:(lia)) as (b2 & E2 & R2). destruct (B8 3 ltac:(lia)) as (b3 & E3 & R3).
destruct (B8 4 ltac:(lia)) as (b4 & E4 & R4). destruct (B8 5 ltac:(lia)) as (b5 & E5 & R5).
destruct (B8 6 ltac:(lia)) as (b6 & E6 & R6). destruct (B8 7 ltac:(lia)) as (b7 & E7 & R7).
rewrite Z.add_0_r in E0.
unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7.
eexists. split; [reflexivity | lia].
Qed.
(* pv_frame carried to another world and memory that show the same bytes on the frame and keep it present *)
Lemma pvi_frame_x : forall regs0 sp0 Y fa fl shb (W W' : world SEGS) mem mem',
  (forall a, (Y <= a < sp0 \/ fa <= a < fa + 64 \/ SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, (Y <= a < sp0 \/ fa <= a < fa + 64) -> apresent (w_H W') mem' a) ->
  pv_frame regs0 sp0 Y fa fl shb W mem -> pv_frame regs0 sp0 Y fa fl shb W' mem'.
Proof.
intros regs0 sp0 Y fa fl shb W W' mem mem' HK HP (HYr & HY32 & HPR & Vsav & V48 & Vm & Vd & Vp & Vf & HPf & Hl & G).
assert (HKb : forall a, (Y <= a < sp0 \/ fa <= a < fa + 64 \/ SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) ->
  mbyte SEGS (rdW W' mem') a = mbyte SEGS (rdW W mem) a)
  by (intros a Ha; exact (mbyte_of_aview SEGS _ _ _ _ _ (HK a Ha))).
assert (VT : forall a n v, (forall kk, (kk < n)%nat -> Y <= a + Z.of_nat kk < sp0 \/ fa <= a + Z.of_nat kk < fa + 64) ->
  val_mem SEGS (rdW W mem) a n v -> val_mem SEGS (rdW W' mem') a n v).
{ intros a n v Hr Hv kk Hk. rewrite HKb; [exact (Hv kk Hk)|]. destruct (Hr kk Hk) as [H1|H1]; [left|right; left]; exact H1. }
unfold pv_frame. split; [exact HYr|]. split; [exact HY32|].
split; [intros a Ha; apply HP; left; exact Ha|].
split.
{ rewrite Forall_forall in Vsav |- *. intros [o r] Hin. apply VT; [|exact (Vsav _ Hin)].
  intros kk Hk. left. cbn [fst].
  assert (Ho : -104 <= o <= -8).
  { unfold pv_saved in Hin. repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]). destruct Hin. }
  lia. }
split; [apply VT; [intros kk Hk; left; lia | exact V48]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vm]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vd]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vp]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vf]|].
split; [intros a Ha; apply HP; right; exact Ha|].
split; [exact Hl|].
intros j Hj. destruct (G j Hj) as [Gv Gr]. split; [|exact Gr].
intros kk Hk. rewrite HKb; [exact (Gv kk Hk)|]. right; right. rewrite Hl in Hj. cbn in Hk. lia.
Qed.

Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* ---- Section hypotheses ---- *)
(* the kit rule: YCbqG's 16-field record at the harness head length (the instance's AR_laws_x_xs) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the callee text, parse_items's (lib/A/PRH_FnParse.v tparse_items_specX), is NOT a Section hypothesis: it is
   pvd_items_goal's premise at the entry's depth pe_d en (PvB_D_Call.v), taken at CTX := [the callee's own context] *)
(* MARKED image fact, discharged at PI_prog_B: no read-only byte is one of alloc.c's statics (S1ImgB.v pst_not_ro_B) *)
Hypothesis RONP : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) PSTX.

(* ---- where the node lies: in an allocator block or a fake frame of the entry state (rd_pre's prhReader_at; its
   window case is excluded by rd_pre's window clause) ---- *)
Lemma pvi_vloc : forall en, pv_pre B ARx en ->
  (exists b m, In (b, m) (ablocks B (pe_ly en) (pe_S en)) /\ b <= pe_v en /\ pe_v en + 56 <= b + req_size m) \/
  (exists cid p, In (cid, p) (frames (pe_S en)) /\ frame_addr (pe_ly en) cid p <= pe_v en /\
     pe_v en + 56 <= frame_addr (pe_ly en) cid p + fs_frame_bytes cid).
Proof.
intros en HPRE.
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
pose proof HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & Hvwin & HLED0 & _).
pose proof Hnode as (_ & _ & _ & _ & Hvat & _).
pose proof (@cf_head_nonneg cp) as Hch.
destruct Hvat as [(a0 & kk & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & p & Hin & H1 & H2) | (H1 & H2)]]].
- left. pose proof HLED0 as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF (a0, kk) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  exists (a0 - cf_head), (kk + cf_head). split; [exact Hab|].
  assert (Hkc : 0 <= kk + cf_head) by lia. pose proof (req_size_pos (kk + cf_head) Hkc). lia.
- left. exists b, m. split; [exact Hin|]. destruct (Z_lt_le_dec m 0); [lia|].
  pose proof (req_size_pos m ltac:(lia)). lia.
- right. exists cid, p. auto.
- exfalso. destruct Hvwin; lia.
Qed.

(* the node at the call state: off the runtime's bytes and the image, apart from parse_value's fake frame and its
   shadow, below alloc_ceiling *)
Lemma pvi_vcall : forall en lyc Sc Hpc W mem mdc pos,
  pv_pre B ARx en -> ARx lyc Sc Hpc W mem mdc ->
  frames Sc = (0, pos) :: frames (pe_S en) -> ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en) ->
  (forall cid p, frame_addr lyc cid p = frame_addr (pe_ly en) cid p) ->
  (forall x, pe_v en <= x < pe_v en + 56 -> ~ aowned B lyc Sc x /\ ~ in_img SEGS x /\
     ~ (frame_addr lyc 0 pos <= x < frame_addr lyc 0 pos + 64) /\
     ~ (SHADOW_OFF + frame_addr lyc 0 pos / 8 <= x < SHADOW_OFF + frame_addr lyc 0 pos / 8 + 8)) /\
  pe_v en + 56 <= YM05.alloc_ceiling.
Proof.
intros en lyc Sc Hpc W mem mdc pos HPRE HAR Hfrs Eab EFr.
assert (Hin0 : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc W mem mdc 0 pos HAR Hin0) as (_ & Hfapp & _).
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Efb in Hfapp.
pose proof ASAN_CEIL_range as (HAC & _).
destruct (pvi_vloc en HPRE) as [(b & m & Hb & H1 & H2) | (cid & p & Hcp & H1 & H2)].
- rewrite <- Eab in Hb.
  destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & Hb4096 & Hbc & Hbapp & Hbown & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc W mem mdc b m 0 pos HAR Hb Hin0) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite Efb in Hdj.
  split; [|lia].
  intros x Hx. split; [exact (proj2 (Hbown x ltac:(lia)))|].
  split.
  { apply (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ x HAR). left. exists b, m. split; [exact Hb | lia]. }
  split; [lia|].
  clear - Hx H1 H2 Hbapp Hfapp HAC. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
- assert (Hcp' : In (cid, p) (frames Sc)) by (rewrite Hfrs; right; exact Hcp).
  rewrite <- EFr in H1, H2.
  destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc W mem mdc cid p HAR Hcp') as (_ & Hcapp & Hcown & _).
  destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc W mem mdc cid p HAR Hcp') as (_ & Hcc & _).
  destruct (in_split _ _ Hcp) as (l2 & l3 & Hl).
  pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc Hpc W mem mdc (0, pos) (cid, p) [] l2 l3 HAR
    ltac:(rewrite Hfrs, Hl; reflexivity)) as Hdj.
  unfold zdisjoint, frame_rng in Hdj. cbn [fst snd] in Hdj. rewrite Efb in Hdj.
  split; [|lia].
  intros x Hx. split; [exact (proj2 (Hcown x ltac:(lia)))|].
  split.
  { apply (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ x HAR). right. left. exists cid, p. split; [exact Hcp' | lia]. }
  split; [lia|].
  clear - Hx H1 H2 Hcapp Hfapp HAC. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* ---- the call view against the entry view: every byte at or above the entry sp but q's p word ---- *)
Lemma pvi_kv : forall en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1,
  pv_pre B ARx en ->
  pv_body (SK := SK) B ARx en Y fa fl pos shb lyc Sc Hpc W' mem mdc k ->
  pj_in_okR SEGS (rdW W' mem) (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) ->
  forall a, pe_sp en <= a < 2 ^ 64 -> ~ (pe_q en <= a < pe_q en + 8) ->
    aview SEGS (w_H W') mem a = aview SEGS (w_H (pe_W en)) (pe_mem en) a.
Proof.
intros en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 HPRE HBODY HIN a Ha Hq.
assert (HFPRE : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en)
  (pe_ch en)) by (unfold pv_pre in HPRE; tauto).
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
pose proof HFPRE as (HAFN & _). pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & HSTK0 & Hceil & Hslo & _).
pose proof HRDP as (_ & _ & _ & _ & Hcur0 & Hwin & Hqlo & Hqhi & _ & _ & _ & _ & _ & _ & _ & Hvwin & _).
pose proof HBODY as (_ & _ & _ & _ & HJ & HWIN).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & _).
change (spZ (pe_regs en)) with (pe_sp en) in *.
destruct (Z_lt_le_dec a (pe_sp en + pe_e en)) as [Hlt | Hge].
- destruct (Z_lt_le_dec a (pe_q en + 16)) as [H1 | H1]; [|destruct (Z_lt_le_dec a (pe_q en + 20)) as [H2 | H2]].
  + apply HWIN; [lia|]. unfold pe_FP. intros (r & Hr & Hin). cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hin; lia.
  + destruct Hcur0 as (_ & _ & V3e & _). destruct HIN as (_ & _ & V3c & _).
    unfold aview. replace a with (pe_q en + 16 + Z.of_nat (Z.to_nat (a - (pe_q en + 16)))) by lia.
    rewrite (V3c (Z.to_nat (a - (pe_q en + 16))) ltac:(lia)), (V3e (Z.to_nat (a - (pe_q en + 16))) ltac:(lia)).
    reflexivity.
  + apply HWIN; [lia|]. unfold pe_FP. intros (r & Hr & Hin). cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hin; lia.
- apply J1; lia.
Qed.

(* ---- the cursor chain the text asks at the call view (prh_s0 F_parse_string q = q), from the call sp Y ---- *)
Lemma pvi_qchain : forall en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1,
  pv_pre B ARx en ->
  pv_body (SK := SK) B ARx en Y fa fl pos shb lyc Sc Hpc W' mem mdc k ->
  pv_chain en lyc W' mem Y ->
  pj_in_okR SEGS (rdW W' mem) (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) ->
  exists ch, achain lyc (aview SEGS (w_H W') mem) Y (pe_q en) ch.
Proof.
intros en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 HPRE HBODY HCHAIN HIN.
pose proof (pvi_kv en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 HPRE HBODY HIN) as KV.
assert (HFPRE : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en)
  (pe_ch en)) by (unfold pv_pre in HPRE; tauto).
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
assert (HCUR0 : prh_cur_entry (pe_W en) (pe_mem en) (pe_regs en) (pe_q en))
  by (unfold pv_pre in HPRE; tauto).
assert (HQCH : (pe_sp en <= pe_q en < pe_sp en + 16) \/
   (pe_sp en + 16 <= pe_q en /\
    exists ch', achain (pe_ly en) (aview SEGS (w_H (pe_W en)) (pe_mem en)) (spZ (pe_regs en))
      (prh_s0 F_parse_string (pe_q en)) ch')) by (unfold pv_pre in HPRE; tauto).
pose proof HFPRE as (HAFN & _). pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & Htop2 & Htop).
(* the frame size, positive: src_rd's `text + len <= alloc_ceiling` (SRC-CEIL, no `+ 8`) and astk_ok put the
   cursor at most sp0 - STK, strictly below sp0 *)
assert (HSTKe : pe_STK en = Z.of_nat (S (PjGrammar.MAXD - pe_d en)) * 320 + 16560) by reflexivity.
pose proof HRDP as (_ & _ & _ & _ & Hcur0 & Hwin & Hqlo & Hqhi & _ & Hsrc & _).
pose proof Hwin as (He0 & _ & _ & Hepres).
pose proof Hsrc as (_ & Htx4096 & Htxceil & _).
pose proof Hcur0 as (Vp0 & _ & _ & _ & Hq8 & _ & _ & Hpr & _).
pose proof HIN as (Vp1 & _ & _ & _ & _ & _ & _ & Hp1r & Htblen & _).
pose proof HBODY as (HFRM & _ & _ & _ & HJ & _).
pose proof HFRM as (HYr & _ & _ & Vsav & _).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
change (spZ (pe_regs en)) with (pe_sp en) in *.
destruct (HCHAIN (aview SEGS (w_H W') mem) (fun a _ => eq_refl)) as (ch1 & Hch1).
destruct HQCH as [Hq1 | (Hq2 & che & Hche)].
- assert (Hqc : pe_q en = pe_sp en \/ pe_q en = pe_sp en + 8) by (clear - Hq1 Hq8 Hsp16; lia).
  destruct Hqc as [Eq | Eq].
  + rewrite Eq. exists ch1. exact Hch1.
  + (* q = sp0 + 8: one record, at fp = q, whose next frame word is parse_value's saved ra *)
    destruct (Z_lt_le_dec (pe_q en) (ly_top lyc - 16)) as [Ht | Ht];
      [| exists []; left; split; [right; left; lia | reflexivity]].
    assert (Hra_lo : raZ (pe_regs en) < YM05.alloc_ceiling).
    { apply (proj2 HCUR0 F_parse_string (or_introl eq_refl)). unfold prh_word_entry.
      rewrite pvi_s0_ps. replace (pe_q en - 16 =? spZ (pe_regs en) - 8) with true; [reflexivity|].
      symmetry. apply Z.eqb_eq. change (spZ (pe_regs en)) with (pe_sp en). lia. }
    assert (Hpw : forall i, 0 <= i < 8 -> aview SEGS (w_H W') mem (pe_sp en + i) <> None).
    { intros i Hi. rewrite (KV (pe_sp en + i) ltac:(lia) ltac:(lia)).
      apply aview_some_of_apresent. apply Hepres. lia. }
    destruct (pvi_rdword_some (w_H W') mem (pe_sp en) Hpw) as (r & Hr & Hr0).
    assert (Hs8 : rdword (aview SEGS (w_H W') mem) (pe_sp en - 8) = Some (raZ (pe_regs en))).
    { rewrite Forall_forall in Vsav. replace (pe_sp en - 8) with (pe_sp en + -8) by lia.
      apply pvi_rdword_of_val; [apply (pvi_val_lit _ _ _ _ (1%bv : bv 5) 1 eq_refl);
        exact (Vsav (-8, 1) ltac:(unfold pv_saved; cbn [In]; tauto)) | apply bv_unsigned_in_range]. }
    destruct (Z_lt_le_dec r 4096) as [Hr4 | Hr4].
    * exists []. right. split; [lia|]. split; [lia|]. split; [lia|].
      split; [|constructor]. cbn [fpchain]. exists r. split; [|lia].
      replace (pe_q en - 8) with (pe_sp en) by lia. exact Hr.
    * exists [(pe_q en, r, raZ (pe_regs en))]. right. split; [lia|]. split; [lia|]. split; [lia|]. split.
      -- cbn [fpchain]. split; [reflexivity|]. split; [lia|].
         split; [replace (pe_q en - 8) with (pe_sp en) by lia; exact Hr|].
         split; [replace (pe_q en - 16) with (pe_sp en - 8) by lia; exact Hs8|].
         split; [lia|].
         replace (bad_next (pe_q en) (ly_top lyc) (raZ (pe_regs en))) with true; [reflexivity|].
         unfold bad_next. symmetry. apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
      -- constructor; [cbn; lia | constructor].
- (* q >= sp0 + 16: the entry chain at q, with q's p word patched (skip_ws rewrote it) *)
  rewrite pvi_s0_ps in Hche.
  assert (Hag : forall a, pe_sp en <= a -> a + 8 <= ly_top (pe_ly en) -> a mod 8 = 0 -> a <> pe_q en ->
    rdword (aview SEGS (w_H W') mem) a = rdword (aview SEGS (w_H (pe_W en)) (pe_mem en)) a).
  { intros a Ha Hat Ha8 Haq. apply rdword_ext. intros i Hi. apply KV; lia. }
  assert (Hw1 : exists w, rdword (aview SEGS (w_H W') mem) (pe_q en) = Some w /\ 4096 <= w < pe_sp en).
  { exists p1. split; [apply pvi_rdword_of_val; [exact Vp1 | lia] | lia]. }
  assert (Hw0 : exists w0, rdword (aview SEGS (w_H (pe_W en)) (pe_mem en)) (pe_q en) = Some w0 /\ 4096 <= w0).
  { exists (pe_p en). split; [apply pvi_rdword_of_val; [exact Vp0 | lia] | lia]. }
  destruct (pvi_achain_patch (pe_ly en) _ _ (pe_sp en) (pe_q en) che (pe_q en) Hche Hq8 Hag Hw1 Hw0) as (chc & Hchc).
  exists chc. apply (achain_ly_top (pe_ly en) lyc); [exact Etop|].
  apply (achain_lower _ _ (pe_sp en)); [exact Hchc | lia].
Qed.

(* ---- the chain parse_items' own free reads (s0 = q + 16): one record, ra = the end word, next = the p word ---- *)
Lemma pvi_ichain : forall en lyc (W' : world SEGS) mem Y p1,
  pv_pre B ARx en -> Y <= pe_q en ->
  pj_in_okR SEGS (rdW W' mem) (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) ->
  exists ch, achain lyc (aview SEGS (w_H W') mem) (Y - pi_frame F_parse_items) (prh_s0 F_parse_items (pe_q en)) ch.
Proof.
intros en lyc W' mem Y p1 HPRE HYq HIN.
assert (HFPRE : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en)
  (pe_ch en)) by (unfold pv_pre in HPRE; tauto).
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
pose proof HFPRE as (HAFN & _). pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof HRDP as (_ & _ & _ & _ & _ & _ & Hqlo & _ & _ & Hsrc & _).
pose proof Hsrc as (_ & Htx4096 & Htxceil & _).
pose proof HIN as (Vp1 & Vend1 & _ & _ & Hq8 & _ & _ & Hp1r & Htblen & _).
change (spZ (pe_regs en)) with (pe_sp en) in *.
pose proof (pi_frame_nonneg F_parse_items) as Hpf.
rewrite pvi_s0_pi.
destruct (Z_lt_le_dec (pe_q en + 16) (ly_top lyc - 16)) as [Ht | Ht];
  [| exists []; left; split; [right; left; lia | reflexivity]].
exists [(pe_q en + 16, pe_text en + pe_len en, p1)]. right.
split; [lia|]. split; [lia|]. split; [lia|]. split.
- cbn [fpchain]. split; [reflexivity|]. split; [lia|].
  split; [replace (pe_q en + 16 - 8) with (pe_q en + 8) by lia; apply pvi_rdword_of_val; [exact Vend1 | lia]|].
  split; [replace (pe_q en + 16 - 16) with (pe_q en) by lia; apply pvi_rdword_of_val; [exact Vp1 | lia]|].
  split; [lia|].
  replace (bad_next (pe_q en + 16) (ly_top lyc) p1) with true; [reflexivity|].
  unfold bad_next. symmetry. apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
- constructor; [cbn; lia | constructor].
Qed.

(* ---- the cursor words named at the CALL registers (spZ regs = Y < q - 16, so every word is read at the call
   view): q's p word is p1 (pj_in_okR), the others are the saved ra / s0 or the entry view; and the chain conjunct at
   the call registers (s0Z regs = sp0, parse_value's frame pointer): the first record is parse_value's own at sp0, the
   rest an entry-view chain from the entry s0 but for q's p word (pvi_fpchain_q8). prh_cur_entry (the batch kit) states the
   chain conjunct and the s0 - 16 word's bound; the s0 - 8 word's trace is prh_cw_entry's (pvi_cw_call below) ---- *)
(* a word of the call view at or above sp0 - 16, apart from q's p word, is the word the entry form names *)
Lemma pvi_kw : forall en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1,
  pv_pre B ARx en ->
  pv_body (SK := SK) B ARx en Y fa fl pos shb lyc Sc Hpc W' mem mdc k ->
  pj_in_okR SEGS (rdW W' mem) (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) ->
  forall a w, rdword (aview SEGS (w_H W') mem) a = Some w -> pe_sp en - 16 <= a -> a + 8 <= pe_q en + 16 ->
  a mod 8 = 0 -> (a + 8 <= pe_q en \/ pe_q en + 8 <= a) -> prh_word_entry (pe_W en) (pe_mem en) (pe_regs en) a w.
Proof.
intros en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 HPRE HBODY HIN.
pose proof (pvi_kv en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 HPRE HBODY HIN) as KV.
assert (HFPRE : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en)
  (pe_ch en)) by (unfold pv_pre in HPRE; tauto).
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
pose proof HFPRE as (HAFN & _). pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
pose proof HRDP as (_ & _ & _ & _ & Hcur0 & Hwin & Hqlo & Hqhi & _).
pose proof Hwin as (He0 & _ & Hetop & _).
pose proof Hcur0 as (_ & _ & _ & _ & Hq8 & _).
pose proof HBODY as (HFRM & _).
pose proof HFRM as (HYr & _ & _ & Vsav & _).
change (spZ (pe_regs en)) with (pe_sp en) in *.
rewrite Forall_forall in Vsav.
assert (Hs8 : rdword (aview SEGS (w_H W') mem) (pe_sp en - 8) = Some (raZ (pe_regs en))).
{ replace (pe_sp en - 8) with (pe_sp en + -8) by lia.
  apply pvi_rdword_of_val; [apply (pvi_val_lit _ _ _ _ (1%bv : bv 5) 1 eq_refl);
    exact (Vsav (-8, 1) ltac:(unfold pv_saved; cbn [In]; tauto)) | apply bv_unsigned_in_range]. }
assert (Hs16 : rdword (aview SEGS (w_H W') mem) (pe_sp en - 16) = Some (s0Z (pe_regs en))).
{ replace (pe_sp en - 16) with (pe_sp en + -16) by lia.
  apply pvi_rdword_of_val; [apply (pvi_val_lit _ _ _ _ (8%bv : bv 5) 8 eq_refl);
    exact (Vsav (-16, 8) ltac:(unfold pv_saved; cbn [In]; tauto)) | apply bv_unsigned_in_range]. }
intros a w Hw Ha Hah Ha8 Haq. unfold prh_word_entry. change (spZ (pe_regs en)) with (pe_sp en).
destruct (Z.eqb_spec a (pe_sp en - 8)) as [E8 | N8].
- subst a. rewrite Hs8 in Hw. injection Hw as <-. reflexivity.
- destruct (Z.eqb_spec a (pe_sp en - 16)) as [E16 | N16].
  + subst a. rewrite Hs16 in Hw. injection Hw as <-. reflexivity.
  + cbv iota. rewrite <- Hw. apply rdword_ext. intros i Hi. symmetry. apply KV; lia.
Qed.

Lemma pvi_cur_call : forall en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 regs,
  pv_pre B ARx en ->
  pv_body (SK := SK) B ARx en Y fa fl pos shb lyc Sc Hpc W' mem mdc k ->
  pj_in_okR SEGS (rdW W' mem) (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) ->
  (* the cursor at the opener lies before the end: q's p word p1 < text + len <= alloc_ceiling (src_rd's ceiling,
     SRC-CEIL, has no `+ 8`) *)
  p1 < pe_text en + pe_len en ->
  spZ regs = Y -> s0Z regs = pe_sp en ->
  prh_cur_entry W' mem regs (pe_q en).
Proof.
intros en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 regs HPRE HBODY HIN Hp1end HspY Hs0r.
pose proof (pvi_kv en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 HPRE HBODY HIN) as KV.
assert (HFPRE : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en)
  (pe_ch en)) by (unfold pv_pre in HPRE; tauto).
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
assert (HCUR0 : prh_cur_entry (pe_W en) (pe_mem en) (pe_regs en) (pe_q en))
  by (unfold pv_pre in HPRE; tauto).
pose proof HFPRE as (HAFN & _). pose proof HAFN as (_ & _ & _ & _ & _ & Hstk0 & _ & Hchain0 & _).
pose proof Hstk0 as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
pose proof HRDP as (_ & _ & _ & _ & Hcur0 & Hwin & Hqlo & Hqhi & _ & Hsrc & _).
pose proof Hwin as (He0 & _ & Hetop & _).
pose proof Hsrc as (_ & Htx4096 & Htxceil & _).
pose proof Hcur0 as (Vp0 & _ & _ & _ & Hq8 & _ & _ & Hpr & _).
pose proof HIN as (Vp1 & _ & _ & _ & _ & _ & _ & Hp1r & Htblen & _).
pose proof HBODY as (HFRM & _).
pose proof HFRM as (HYr & _ & _ & Vsav & _).
change (spZ (pe_regs en)) with (pe_sp en) in *.
rewrite Forall_forall in Vsav.
assert (Hs16 : rdword (aview SEGS (w_H W') mem) (pe_sp en - 16) = Some (s0Z (pe_regs en))).
{ replace (pe_sp en - 16) with (pe_sp en + -16) by lia.
  apply pvi_rdword_of_val; [apply (pvi_val_lit _ _ _ _ (8%bv : bv 5) 8 eq_refl);
    exact (Vsav (-16, 8) ltac:(unfold pv_saved; cbn [In]; tauto)) | apply bv_unsigned_in_range]. }
pose proof (pvi_kw en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 HPRE HBODY HIN) as KW.
split.
{ (* the chain conjunct at the call registers *)
  intros ly ch' Hch. rewrite HspY, Hs0r in Hch.
  destruct Hch as [(_ & ->) | (H1 & H2 & H3 & H4 & _)]; [constructor|].
  destruct ch' as [|[[fp ra] nfp] rest]; [constructor|].
  cbn [fpchain] in H4. destruct H4 as (Efp & Hal & Hra & Hnfp & Hra4 & Hrest). subst fp.
  rewrite Hs16 in Hnfp. injection Hnfp as <-.
  (* parse_value's own record, at sp0 <= q *)
  constructor; [cbn [fst]; lia|].
  destruct (bad_next (pe_sp en) (ly_top ly) (s0Z (pe_regs en))) eqn:Hbad; [subst rest; constructor|].
  pose proof Hbad as Hbad'. unfold bad_next in Hbad'.
  apply Bool.orb_false_iff in Hbad' as [Hb12 Hb3]. apply Bool.orb_false_iff in Hb12 as [Hb1 Hb2].
  apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply Bool.negb_false_iff, Z.eqb_eq in Hb3.
  change (fpchain (rdword (aview SEGS (w_H W') mem)) (s0Z (pe_regs en)) (ly_top ly) rest) in Hrest.
  (* the entry s0 is at least sp0 + 16: s0 = sp0 + 8 starts no entry chain below the stack top, which lies above
     q + 24 (the entry window), and q = sp0 puts s0 below alloc_ceiling (prh_cur_entry's word at q - 16) *)
  assert (Hs0lo : pe_sp en + 16 <= s0Z (pe_regs en)).
  { destruct (Z_lt_le_dec (s0Z (pe_regs en)) (pe_sp en + 16)) as [Hlt | Hge]; [exfalso | exact Hge].
    destruct Hchain0 as [(Hb & _) | (Hc1 & _)]; [|lia].
    destruct Hb as [Hb | [Hb | Hb]]; [lia | | lia].
    assert (Eqs : pe_q en = pe_sp en) by lia.
    pose proof (proj2 HCUR0 F_parse_string (or_introl eq_refl)) as C2.
    assert (Hlow : s0Z (pe_regs en) < YM05.alloc_ceiling).
    { apply C2. unfold prh_word_entry. rewrite pvi_s0_ps, Eqs.
      change (spZ (pe_regs en)) with (pe_sp en).
      replace (pe_sp en - 16 =? pe_sp en - 8) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (pe_sp en - 16 =? pe_sp en - 16) with true by (symmetry; apply Z.eqb_eq; lia).
      reflexivity. }
    lia. }
  destruct (Z_lt_le_dec (pe_q en + 8) (s0Z (pe_regs en))) as [Hng | Hnl].
  { pose proof (fpchain_fps_increase _ _ _ _ Hrest) as Hinc.
    eapply Forall_impl; [|exact Hinc]. intros r Hr. cbn beta in Hr |- *. lia. }
  apply (pvi_fpchain_q8 (aview SEGS (w_H (pe_W en)) (pe_mem en)) (aview SEGS (w_H W') mem) (pe_q en) (pe_sp en)
    (ly_top ly) rest (s0Z (pe_regs en)) Hrest ltac:(lia) Hb3 Hq8).
  - intros a Ha Haq. apply rdword_ext. intros i Hi. apply KV; lia.
  - exists (pe_p en). split; [apply pvi_rdword_of_val; [exact Vp0 | lia] | lia].
  - (* an entry-view chain from s0 at the layout top q + 32 is an entry chain of a layout with that top *)
    intros ch0 Hc0.
    apply (proj1 HCUR0 (ALayout 0 0 0 0 0 0 0 0 (pe_q en + 32) 0 0 0 [] [] 0 [] (0, 0) (fun _ => 0)) ch0).
    right. cbn [ly_top]. change (spZ (pe_regs en)) with (pe_sp en).
    split; [lia|]. split; [lia|]. split; [exact Hb3|]. split; [exact Hc0|].
    pose proof (fpchain_fps_increase _ _ _ _ Hc0) as Hinc.
    eapply Forall_impl; [|exact Hinc]. intros r Hr. cbn beta in Hr |- *. lia. }
intros F HF. destruct HF as [EF | EF]; subst F.
- pose proof (proj2 HCUR0 F_parse_string (or_introl eq_refl)) as C2.
  rewrite pvi_s0_ps in C2 |- *.
  intros w Hw. unfold prh_word_entry in Hw. rewrite HspY in Hw.
  replace (pe_q en - 16 =? Y - 8) with false in Hw by (symmetry; apply Z.eqb_neq; lia).
  replace (pe_q en - 16 =? Y - 16) with false in Hw by (symmetry; apply Z.eqb_neq; lia).
  cbv iota in Hw. apply C2. apply (KW _ _ Hw); lia.
- rewrite pvi_s0_pi.
  intros w Hw. unfold prh_word_entry in Hw. rewrite HspY in Hw.
  replace (pe_q en + 16 - 16 =? Y - 8) with false in Hw by (symmetry; apply Z.eqb_neq; lia).
  replace (pe_q en + 16 - 16 =? Y - 16) with false in Hw by (symmetry; apply Z.eqb_neq; lia).
  cbv iota in Hw. replace (pe_q en + 16 - 16) with (pe_q en) in Hw by lia.
  rewrite (pvi_rdword_of_val _ _ _ _ Vp1 ltac:(lia)) in Hw. injection Hw as <-. lia.
Qed.

(* ---- the s0 - 8 word of each cursor function at the CALL registers (q - 8 for parse_string, q + 8 for parse_items,
   both read at the call view and the entry's by pvi_kw), its free trace in CW: pv_pre's prh_cw_entry ---- *)
Lemma pvi_cw_call : forall en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 regs,
  pv_pre B ARx en ->
  pv_body (SK := SK) B ARx en Y fa fl pos shb lyc Sc Hpc W' mem mdc k ->
  pj_in_okR SEGS (rdW W' mem) (pe_q en) (pe_text en) (pe_len en) p1 (Z.of_nat (pe_d en)) (pe_tb en) ->
  spZ regs = Y ->
  prh_cw_entry B (pe_CW en) W' mem regs (pe_q en).
Proof.
intros en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 regs HPRE HBODY HIN HspY.
pose proof (pvi_kw en Y fa fl pos shb lyc Sc Hpc W' mem mdc k p1 HPRE HBODY HIN) as KW.
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
assert (HCWE : prh_cw_entry B (pe_CW en) (pe_W en) (pe_mem en) (pe_regs en) (pe_q en))
  by (unfold pv_pre in HPRE; tauto).
pose proof HRDP as (_ & _ & _ & _ & Hcur0 & _ & Hqlo & _).
pose proof Hcur0 as (_ & _ & _ & _ & Hq8 & _).
pose proof HBODY as (HFRM & _).
pose proof HFRM as (HYr & _).
change (spZ (pe_regs en)) with (pe_sp en) in *.
intros F r w HF Hr Hw. destruct HF as [EF | EF]; subst F.
- apply (HCWE F_parse_string r w (or_introl eq_refl) Hr).
  rewrite pvi_s0_ps in Hw |- *.
  unfold prh_word_entry in Hw. rewrite HspY in Hw.
  replace (pe_q en - 8 =? Y - 8) with false in Hw by (symmetry; apply Z.eqb_neq; lia).
  replace (pe_q en - 8 =? Y - 16) with false in Hw by (symmetry; apply Z.eqb_neq; lia).
  cbv iota in Hw. apply (KW _ _ Hw); lia.
- apply (HCWE F_parse_items r w (or_intror eq_refl) Hr).
  rewrite pvi_s0_pi in Hw |- *.
  unfold prh_word_entry in Hw. rewrite HspY in Hw.
  replace (pe_q en + 16 - 8 =? Y - 8) with false in Hw by (symmetry; apply Z.eqb_neq; lia).
  replace (pe_q en + 16 - 8 =? Y - 16) with false in Hw by (symmetry; apply Z.eqb_neq; lia).
  cbv iota in Hw. apply (KW _ _ Hw); lia.
Qed.

(* ---- THE ARM ---- *)
Lemma pvd_call_items : pvd_items_goal B ARx.
Proof.
unfold pvd_items_goal.
intros en c y Y fa fl pos lyc Sc k W' regs mem mdc HPRE TPI Hsk Hc HCS R10 R11 R12 KX.
unfold pvd_kxR, YA0nH.SRr' in KX. unfold YA0nH.SRr'.
destruct HCS as (HKR & R9 & R19 & R20 & R24 & R1 & HBODY & HCHAIN & HRD0 & _ & _ & HMNc).
pose proof HKR as (R2 & R8 & R18 & R26 & R27 & R23 & R3 & R4).
pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
pose proof HFRM as (HYr & HY32 & HPR0 & Vsav & Vfa48 & Vmagic & Vdesc & Vpc & Vfl & HPRfa & Hshlen & Gsh).
pose proof HRD0 as (Hfrs & Habl & Hbb & HROOMc & HCUR & HSRC & HHOME & HVEQ & HVRA & HLEDc & HRPc & HSECc).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs.
pose proof (ajx_wle HJ) as Hwle. pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs'.
pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk0. pose proof (ajx_hi HJ) as J1.
pose proof (ajx_blk HJ) as J2. pose proof (ajx_img HJ) as J3. pose proof (ajx_frm HJ) as J4.
pose proof (ajx_gone HJ) as Jgone. pose proof (ajx_pres HJ) as Hpres. pose proof (ajx_stk HJ) as Hstk.
pose proof (ajx_extra HJ) as J5. pose proof (ajx_qt HJ) as HQT.
(* pv_pre's parts by type *)
assert (HFPRE : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en)
  (pe_ch en)) by (unfold pv_pre in HPRE; tauto).
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
assert (HUNIV : prh_univ_closure B (pe_CTX0 en)) by (unfold pv_pre in HPRE; tauto).
assert (HWR0 : YCbqGwild.wild_room (as_universe B) (pe_CW en) 0 (st_depot (pe_S en)))
  by (unfold pv_pre in HPRE; tauto).
assert (HFRB : Z.of_nat (length (frames (pe_S en))) + Z.of_nat (Nat.succ (PjGrammar.MAXD - pe_d en)) <= fs_frames 0)
  by (unfold pv_pre in HPRE; tauto).
pose proof HFPRE as (HAFN & HRO & Hhi64 & _).
pose proof HAFN as (HAR0 & Hra_ok & Hra4 & Hgp & Htp & Hstk0 & Hpres0 & Hchain & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop20 & Htop0).
pose proof HRDP as (Hfrm0 & Hmuniv & Hruniv1 & Hruniv2 & Hcur0 & Hwin & Hqlo & Hqhi & Hqra & Hsrc & Hhome &
  Hmaxrun & Hnode & Hqv & Htv & Hvwin & HLED0 & Hdmax & Hcntb & Htxc).
pose proof Hwin as (He0 & He16 & Hetop & Hepres).
pose proof Hnode as (Hv4096 & Hv8 & Hvrw & Hvz & Hvat & Hvam & Hvown & Hvra).
pose proof Hcur0 as (Vp0 & _ & _ & _ & _ & _ & _ & Hp0r & Htblen0 & _).
pose proof HCUR as (Vp1 & Vend & Vdep & Hqrw & Hq8 & Htx0 & Htx62 & Hp1r & Htblen & Gtb & Hqt & Hd32).
pose proof Hstk as (Hsp16 & HSTK1 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & EF4 & _ & _ & Etop & Eslo & Eshi & _).
assert (EF : forall c p, frame_addr lyc c p = frame_addr (pe_ly en) c p)
  by (intros; unfold frame_addr; rewrite EF4; reflexivity).
pose proof ASAN_CEIL_range as HAC. unfold ASAN_CEIL in HAC.
pose proof Hsrc as (Hsbytes & Htx4096 & Htxceil & Htxam & Htxra & Hsrcrest).
change (spZ (pe_regs en)) with (pe_sp en) in *.
set (p1 := pe_text en + pe_len en - Z.of_nat (length (c :: y))) in *.
assert (HSTKe : pe_STK en = Z.of_nat (S (PjGrammar.MAXD - pe_d en)) * 320 + 16560) by reflexivity.
assert (HSTKi : STK_parse_items (pe_d en) = 144 + Z.of_nat (PjGrammar.MAXD - pe_d en) * 320 + 16560) by reflexivity.
assert (HSTK : 16880 <= pe_STK en) by (rewrite HSTKe; nia).
assert (Hsp_lo : YM05.alloc_ceiling + 4272 <= pe_sp en) by (clear - Hceil0 Hslo0 HSTK; lia).
(* the opener: o = true for '{' *)
set (o := c =? 123) in *.
assert (Eo : (if o then 123 else 91) = c) by (unfold o; destruct Hc as [E | E]; rewrite E; reflexivity).
assert (Hsk' : PjGrammar.skip (pe_rest en) = (if o then 123 else 91) :: y) by (rewrite Eo; exact Hsk).
(* the cursor at the opener *)
pose proof (pvm_skip_rest (pe_tb en) (pe_text en) (pe_len en) (pe_p en) Htblen0 Hp0r) as [Hrest1 _].
change (rest_atR (pe_tb en) (pe_text en) (pe_p en)) with (pe_rest en) in Hrest1.
rewrite Hsk in Hrest1. change (pe_text en + pe_len en - Z.of_nat (length (c :: y))) with p1 in Hrest1.
assert (Ep1 : p1 = pe_text en + pe_len en - Z.of_nat (length (PjGrammar.skip (pe_rest en))))
  by (unfold p1; rewrite Hsk; reflexivity).
assert (Hp1end : p1 < pe_text en + pe_len en) by (unfold p1; cbn [length]; lia).
assert (Hnth : nth_error (pe_tb en) (Z.to_nat (p1 - pe_text en)) = Some (if o then 123 else 91)).
{ rewrite Eo. pose proof Hrest1 as H. unfold rest_atR in H. exact (pvi_nth_error_skipn _ _ _ _ H). }
assert (Egt : prhPi_gtrace (pe_d en) o (rest_atR (pe_tb en) (pe_text en) p1) = pe_gt en).
{ unfold prhPi_gtrace, pe_gt, prhPv_gtrace.
  rewrite (pvi_model prh_jr_strtod (pe_d en) (pe_rest en) o y [] Hsk'), Hrest1, Eo. reflexivity. }
(* parse_items' hull budget at the call state: pv_pre's over parse_value's events, which at the opener ARE parse_items'
   (Egt), the meters kept from entry (pv_reader0's secs_same) *)
assert (HHB0 : PresetHullBudget.hull_budget (pe_S en) (PresetReqAt.rd_hevs (pe_gt en)))
  by (unfold pv_pre in HPRE; tauto).
assert (HHULL1 : PresetHullBudget.hull_budget Sc
    (PresetReqAt.rd_hevs (prhPi_gtrace (pe_d en) o (rest_atR (pe_tb en) (pe_text en) p1))))
  by (rewrite Egt; exact (PresetHullBudget.hull_budget_same (pe_S en) Sc _ HSECc HHB0)).
(* parse_items' two live-count premises at the call state (the text's, over rd_hevs (prhPi_gtrace ..)): pv_pre's over
   parse_value's granted run, which at the opener IS parse_items', at the call state by pv_reader0's room keep
   (PvB_D_Items.v pvi_counts) *)
destruct (pvi_counts B ARx en o y Sc HPRE Hsk' HRPc) as (HPKS1 & HPK241).
rewrite Eo, <- Hrest1 in HPKS1, HPK241.
(* the node at the call state *)
destruct (pvi_vcall en lyc Sc (pe_Hp en) W' mem mdc pos HPRE HAR Hfrs Habl EF) as (HVC & Hvlow).
rewrite <- Efa in HVC.
(* the frame and the stack bounds *)
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc (pe_Hp en) W' mem mdc 0 pos HAR HinF) as (Hfa0 & Hfac & _).
rewrite <- Efa, Efb in Hfac.
assert (HspY : spZ regs = Y) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = pe_sp en) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; lia).
destruct (HCHAIN (aview SEGS (w_H W') mem) (fun a _ => eq_refl)) as (ch1 & Hch1).
(* the read-only view at the call memory (the journal's image clause; read-only bytes are not alloc.c's statics) *)
assert (Hspares : forall a, fp_spares (pe_FP en) a).
{ intros a. apply fp_spares_closed. apply sink_closed_pos. unfold pe_FP.
  repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. }
assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem)).
{ intros a Hr Ho Her. rewrite (J3 a (pvi_ro_img a Hr) Ho Her (RONP a Hr) (Hspares a)). exact (HRO a Hr Ho Her). }
(* fpre's return-address bound at the call: the jal's return slot BASE + 0x8613c *)
assert (Hra1 : raZ regs < YM05.alloc_ceiling).
{ destruct (plookup (@pl_tpi _ PL_prog_B) AF_pv_items_ret) as [e|] eqn:Hk; [|vm_compute in Hk; discriminate Hk].
  exact (pvd_ret_lt_ceil regs AF_pv_items_ret e R1 ltac:(unfold AF_pv_items_ret; lia) Hk). }
(* the wild room at the call state: pv_pre's at entry, across the C1 journal (the empty budget: no wild trace stored
   since entry, YCbqGwild.ajournal_xw_room at WS = []) *)
assert (HWRc : YCbqGwild.wild_room (as_universe B) (pe_CW en) 0 (st_depot Sc))
  by exact (YCbqGwild.ajournal_xw_room SEGS B PSTX ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) W' mem mdc k []
    (pe_CW en) 0%nat HJ HWR0 (le_n 0)).
(* ---- the call: parse_items' BUDGETED text at the callee's entry, in its relation wle' segs RZ_cf (its text concludes
   YA0nH.SRr' segs RZ_cf: it frees), by YCbqGwild.aj_call_xWFbR at that relation from the C1 journal lifted to it
   (YA0nH.wle_wle'), at the empty budget, window [Y, sp0 + e) ---- *)
assert (HJR : ajournal_xwR (SK := SK) SEGS B PSTX ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)
    (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en)
    (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) W' mem mdc k [])
  by (eapply (ajournal_xwR_mono (SK := SK) SEGS B PSTX ARx (@wle SEGS));
      [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact HJ]).
eapply (YA0nH.SRrG_bind SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (YCbqGwild.aj_call_xWFbR SEGS B PSTX ARx LAWS (@pa_segs_low _ _ PA) (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W' regs mem
    (SIGMA AS_parse_items)
    (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en)
    (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) mdc k [] (STK_parse_items (pe_d en)) (pe_sp en + pe_e en - Y)
    (rd_fp (pe_q en) (pe_v en)) (Y - (pe_sp en + pe_e en)) (Z_to_bv 64 (BASE + AF_pv_items_ret)) ch1 _ _ HJR).
  - rewrite HspY. lia.
  - clear - HY32 Hal16 He16. lia.
  - clear - He0 HYr. lia.
  - rewrite HSTKi. lia.
  - rewrite HSTKi, HSTKe, Nat2Z.inj_succ. clear - HYr He0. lia.
  - clear - He0 HYr. lia.
  - clear - HY32 Hal16 He16. lia.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [unfold AF_pv_items_ret; lia | reflexivity].
  - pose proof (@pa_B_ok _ B_prog_listing PA) as HBok. rewrite unsigned_lit_small; unfold AF_pv_items_ret; lia.
  - replace (pe_sp en + pe_e en + (Y - (pe_sp en + pe_e en))) with Y by lia. rewrite Hs0. exact Hch1.
  - intros HAFN1 HWIN1.
    pose proof HAFN1 as (_ & _ & _ & _ & _ & Hstk1 & _ & Hch1' & _).
    pose proof Hstk1 as (_ & _ & Hceil1 & Hslo1 & _).
    assert (HFP1 : fpre B ARx (STK_parse_items (pe_d en)) lyc Sc (pe_Hp en) W' regs mem mdc ch1).
    { split; [exact HAFN1|]. split; [exact HROc|]. split; [rewrite HspY, Eshi; clear - Hhi64 HYr; lia|].
      split; [exact Hra1 | exact Hfrm0]. }
    assert (HCUR1 : prh_cur_entry W' mem regs (pe_q en))
      by exact (pvi_cur_call en Y fa fl pos pv_shadow_live lyc Sc (pe_Hp en) W' mem mdc k p1 regs HPRE HBODY HCUR Hp1end
        HspY Hs0).
    assert (HCW1 : prh_cw_entry B (pe_CW en) W' mem regs (pe_q en))
      by exact (pvi_cw_call en Y fa fl pos pv_shadow_live lyc Sc (pe_Hp en) W' mem mdc k p1 regs HPRE HBODY HCUR HspY).
    assert (HPART : (spZ regs <= pe_q en < spZ regs + 16) \/
      (spZ regs + 16 <= pe_q en /\
       exists ch', achain lyc (aview SEGS (w_H W') mem) (spZ regs) (prh_s0 F_parse_string (pe_q en)) ch')).
    { right. rewrite HspY, pvi_s0_ps. split; [clear - HYr Hqlo; lia|].
      exact (pvi_qchain en Y fa fl pos pv_shadow_live lyc Sc (pe_Hp en) W' mem mdc k p1 HPRE HBODY HCHAIN HCUR). }
    assert (HICH : exists ch, achain lyc (aview SEGS (w_H W') mem) (spZ regs - pi_frame F_parse_items)
      (prh_s0 F_parse_items (pe_q en)) ch).
    { rewrite HspY. exact (pvi_ichain en lyc W' mem Y p1 HPRE ltac:(clear - HYr Hqlo; lia) HCUR). }
    assert (HNODE1 : prhPv_node B (STK_parse_items (pe_d en)) (pe_sp en + pe_e en - Y) lyc Sc W' regs mem
      (pe_Lam en) (pe_v en)).
    { split; [exact Hv4096|]. split; [exact Hv8|].
      split.
      { split; [exact Hv8|]. intros x Hx.
        destruct (HVC x Hx) as (_ & Hni & _).
        apply (pvi_wr_keep _ _ x (proj2 Hvrw x Hx)); [| lia | exact Hni].
        apply (mbyte_of_aview SEGS). exact (HVEQ x Hx). }
      split.
      { apply (pj_zeroR_frame SEGS _ _ _ Hvz). intros x Hx. apply (mbyte_of_aview SEGS). exact (HVEQ x Hx). }
      split.
      { destruct Hvat as [H | [H | [(cid & p & Hin & H1 & H2) | (H1 & H2)]]].
        - left. exact H.
        - right. left. rewrite Habl. exact H.
        - right. right. left. exists cid, p. rewrite !EF. split; [rewrite Hfrs; right; exact Hin | lia].
        - exfalso. change (spZ (pe_regs en)) with (pe_sp en) in H1, H2. clear - Hvwin H1 H2. destruct Hvwin; lia. }
      split; [exact Hvam|].
      split.
      { intros x Hx. destruct (HVC x Hx) as (Hno & _). split; [exact Hno|]. rewrite HspY.
        clear - Hx Hvlow Hceil1 Hslo1 HspY. rewrite HspY in Hslo1. lia. }
      exact HVRA. }
    assert (HRD1 : rd_pre (fx := fx0) B (STK_parse_items (pe_d en)) lyc Sc (pe_Hp en) W' regs mem (pe_Lam en)
      (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_sp en + pe_e en - Y) (pe_q en)
      (pe_text en) (pe_len en)
      p1 (pe_d en) (pe_tb en) (pe_v en)).
    { split; [exact Hfrm0|]. split; [exact Hmuniv|]. split; [exact Hruniv1|]. split; [exact Hruniv2|].
      split; [exact HCUR|]. split; [exact HWIN1|].
      split; [rewrite HspY; clear - HYr Hqlo; lia|]. split; [rewrite HspY; clear - Hqhi; lia|].
      split.
      { apply (pvd_stack_ra B ARx LAWS lyc Sc (pe_Hp en) W' mem mdc (pe_q en) 24 HAR); [rewrite Eslo | rewrite Eshi];
          clear - Hslo Hqlo Hqhi Hshi HSTK He0; lia. }
      split; [exact HSRC|]. split; [exact HHOME|]. split; [exact Hmaxrun|].
      split; [exact HNODE1|]. split; [exact Hqv|]. split; [exact Htv|].
      split; [left; rewrite HspY; clear - Hvlow Hsp_lo HYr; lia|].
      split; [exact HLEDc|]. split; [exact Hdmax|]. split.
      { rewrite Hrest1, <- Hsk. pose proof (PjGrammar.skip_len (pe_rest en)) as Hsl.
        change (rest_atR (pe_tb en) (pe_text en) (pe_p en)) with (pe_rest en) in Hcntb. clear - Hcntb Hsl. lia. }
      (* The batch kit's appended conjunct (the same text window as the caller's) *)
      exact Htxc. }
    assert (HFRB1 : Z.of_nat (length (frames Sc)) + Z.of_nat (PjGrammar.MAXD - pe_d en) <= fs_frames 0).
    { rewrite Hfrs. cbn [length]. rewrite Nat2Z.inj_succ. rewrite Nat2Z.inj_succ in HFRB. clear - HFRB. lia. }
    assert (HROOM1 : rd_room Sc (prhPi_gtrace (pe_d en) o (rest_atR (pe_tb en) (pe_text en) p1)))
      by (rewrite Egt; exact HROOMc).
    exact (TPI [raZ regs :: spine ch1] (pe_CTX0 en) (pe_CW en) lyc Sc (pe_Hp en) W' regs mem mdc ch1
      (pe_sp en + pe_e en - Y) (pe_q en) (pe_text en) (pe_len en) p1 (pe_tb en) (pe_v en) o (pe_Lam en) (pe_peak en)
      (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en)
      HFP1 HMNc (or_introl eq_refl) HUNIV HCUR1 HCW1 (ex_intro _ ch1 (conj Hch1' eq_refl))
      HPART R10 R11 R12 HRD1 Hp1end Hnth HROOM1 HWRc HPKS1 HPK241 HHULL1 HICH HFRB1).
  - intros a Ha. left. exact Ha. }
(* ---- back at 0x8662c: the callee's post, the float state fx' ---- *)
cbv beta.
intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & Ec2 & HFZ & HFK & HPW & HJ2w & HJc & HXw & HP2
  & HK).
subst c2. cbv beta delta [fQmn] in HK. destruct HK as (HK & HMK2).
assert (HMN2 : YAkMemnorm.memnorm SEGS mem2) by exact (HMK2 HMNc).
(* the caller's journal after the call is BUDGETED, at the callee's WS1 (wbudget CW 0: the callee post's P), and at the
   re-hiding relation: the stretch to the exit runs on it REBASED at the post-call depot (YCbqGwild.ajournal_xw_rebaseR);
   the exit cut unbases it (ajournal_xw_unbase0R with ajxR_wild, the post-call depot's wild part within the entry's and WS1) *)
pose proof (ajxR_wild HJ2w) as HWILD.
assert (HJ2 : ajournal_xR (SK := SK) SEGS B PSTX ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)
    (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en) (pe_ly en)
    (set_depot (st_depot S2) (pe_S en)) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] ly2 S2 Hp2 W2 mem2 md2
    (k + k1))
  by (eapply YCbqGwild.ajournal_xw_rebaseR; exact HJ2w).
clear HJ2w.
(* the room post at the return is inside parse_items' post (the live list and the position moved by its events),
   which pvD_Qm_items composes with pv_reader0's keep *)
pose proof HJc as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & M1 & M2 & M3 & M4 & _ & Hpres2 & _ & _ & _).
cbn [app] in Hfrs2.
pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _ & _ & _ & _ & _ & _).
assert (EF2' : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
  by (intros; unfold frame_addr; rewrite EF2; reflexivity).
assert (EFl2 : forall c p, flag_addr ly2 c p = flag_addr lyc c p)
  by (intros; unfold flag_addr; rewrite EF2; reflexivity).
assert (HinF2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; exact HinF).
assert (HXw' : forall a, Y <= a < pe_sp en + pe_e en -> ~ inFP (rd_fp (pe_q en) (pe_v en)) a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W') mem a).
{ intros a Ha Hn. apply HXw; [lia | exact Hn]. }
(* the frame's bytes lie outside the callee's footprint *)
assert (NFP : forall a, (fa <= a < fa + 64 \/ SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8 \/
  Y <= a < pe_sp en) -> ~ inFP (rd_fp (pe_q en) (pe_v en)) a).
{ intros a Ha (r & Hr & Hin). unfold rd_fp in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hin.
  - clear - Ha Hin Hfac Hqlo Hsp_lo HAC. unfold SHADOW_OFF in *. lia.
  - clear - Ha Hin Hfac Hqlo Hsp_lo HAC. unfold SHADOW_OFF in *. lia.
  - destruct (HVC a Hin) as (_ & _ & H1 & H2). clear - Ha Hin H1 H2 Hvlow Hsp_lo HYr. lia. }
(* the frame at the callee's return, at its memory *)
assert (KFR : forall a, (Y <= a < pe_sp en \/ fa <= a < fa + 64 \/ SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W') mem a).
{ intros a [Ha | [Ha | Ha]].
  - apply HXw'; [clear - Ha He0; lia|]. apply NFP. right; right; exact Ha.
  - apply (M4 0 pos a HinF); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- Efa, Efb; lia|].
    apply NFP. left; exact Ha.
  - apply (M4 0 pos a HinF); [right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- Efa, Efb;
      change (64 / 8) with 8; lia|].
    apply NFP. right; left; exact Ha. }
assert (PFR : forall a, (Y <= a < pe_sp en \/ fa <= a < fa + 64) -> apresent (w_H W2) mem2 a).
{ intros a [Ha | Ha].
  - apply Hpres2. rewrite HSTKi. clear - Ha He0 HYr. lia.
  - destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 0 pos HAR2 HinF2) as (_ & _ & Hfb & _).
    rewrite EF2', <- Efa, Efb in Hfb. exact (proj1 (Hfb a Ha)). }
(* the result code a0, from the post's result arm read through its record (lib/A/PRH_FnParse.v tpiP_R) *)
assert (HKQ : tpiP_Q B (pe_d en) lyc Sc (pe_q en) (pe_text en) (pe_len en) p1 (pe_tb en) (pe_v en) o (pe_Lam en)
    (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) ly2 S2 Hp2 W2 regs2 mem2 md2)
  by exact HK.
assert (Hcode : exists code, -1 <= code <= 0 /\ getr regs2 10 = w64 code).
{ pose proof HKQ as HKQR. apply tpiP_R_of in HKQR.
  destruct HKQR as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HR).
  pose proof (tpiP_arm HR) as Hres.
  destruct res as [[t r]|].
  - exists 0. split; [lia | exact (tpiPs_ret (tpiP_RSome_of Hres))].
  - exists (-1). split; [lia | exact (tpiPn_ret (tpiP_RNone_of Hres))]. }
destruct Hcode as (code & Hcb & Hc10).
assert (Q2 : getr regs2 2 = getr regs 2) by pvi_keep HP2 (2%bv : bv 5) 2.
assert (Q3 : getr regs2 3 = getr regs 3) by pvi_keep HP2 (3%bv : bv 5) 3.
assert (Q4 : getr regs2 4 = getr regs 4) by pvi_keep HP2 (4%bv : bv 5) 4.
assert (Q8 : getr regs2 8 = getr regs 8) by pvi_keep HP2 (8%bv : bv 5) 8.
assert (Q18 : getr regs2 18 = getr regs 18) by pvi_keep HP2 (18%bv : bv 5) 18.
assert (Q23 : getr regs2 23 = getr regs 23) by pvi_keep HP2 (23%bv : bv 5) 23.
assert (Q26 : getr regs2 26 = getr regs 26) by pvi_keep HP2 (26%bv : bv 5) 26.
assert (Q27 : getr regs2 27 = getr regs 27) by pvi_keep HP2 (27%bv : bv 5) 27.
(* ---- B 0x8662c `j 86648`, 0x86648 `mv s5, a0`: a fresh symbolic state at the return, run to the exit ---- *)
set (E := Eimg (Ereg regs2 [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs2 []) E).
{ unfold E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (HS : st_ok_pi (fx := fx') SEGS VAL E (mkSS AF_pv_items_ret sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + AF_pv_items_ret)) mem2 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - unfold E. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - exact I.
  - exact (conj I (conj I I)). }
assert (SHOK : sh_ok SEGS PVI_Bx [] E (mrestrict (w_H W2) mem2)) by constructor.
pose (RUNTO := paj_run_to_x_invR (fx := fx') (SK := SK) (PL := PL_prog_B) (PI := PA) B PSTX ARx LAWS
  (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS) (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
paj_run_to_tok_x_inv RUNTO HS HJ2 SHOK HMN2 PVI_Bspan AF_pv_exit; [pvd_awr0|].
rewrite ?wvb_collapse in HJ2.
lazymatch goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
lazymatch goal with H : frame_of _ _ _ _ |- _ => rename H into HFr0 end.
lazymatch goal with H : mem_grows _ _ |- _ => rename H into HG0 end.
assert (EQ : forall x, mrestrict (w_H W2) (ms_mem msf) x = mrestrict (w_H W2) mem2 x).
{ apply (pvd_nowin E []); [pvd_awr0 | exact HFr0]. }
assert (AVF : forall a, aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem2 a)
  by (intros a; apply aview_eq_of; apply EQ).
assert (GRF : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msf) a)
  by (intros a Ha; exact (apresent_grows (w_H W2) mem2 (ms_mem msf) a HG0 Ha)).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (HAEf : env_agree 32 (Ereg regs2 []) Ex) by ((pvd_agree HAE)) end.
assert (KRF : forall r, In r [2; 3; 4; 8; 10; 18; 23; 26; 27]%bv -> getr (ms_regs msf) r = getr regs2 r)
  by (intros r Hr; (exact (regs_kept_of_st_ok_pi _ _ _ regs2 []
        [2; 3; 4; 8; 10; 18; 23; 26; 27]%bv HS HAEf ltac:(vm_compute; reflexivity) r Hr))).
(pvd_reg HS (21%bv : bv 5) R21). (pvd_reg HS (10%bv : bv 5) RA0).
assert (R21' : getr (ms_regs msf) 21 = getr regs2 10).
{ rewrite R21, <- RA0. apply KRF. cbn; tauto. }
(pmkst HS). apply KX. unfold pv_at_exit.
exists fx', (ms_regs msf), (ms_mem msf), Y, fa, fl, pos, ly2, S2, Hp2. eexists. exists code.
split; [first [reflexivity | repeat f_equal; try (vm_compute; reflexivity)]|].
split; [exact HFZ|]. split; [exact HFK|].
split.
{ unfold pv_keep_regs. rewrite !KRF by (cbn; tauto).
  rewrite Q2, Q8, Q18, Q26, Q27, Q23, Q3, Q4. exact HKR. }
split; [rewrite R21'; exact Hc10|].
split.
{ (* pv_body_x: the journal unbased from the post-call depot at the callee's budget WS1 (its wbudget CW 0 is the
     callee post's P) *)
  exists WS1. split; [|exact HPW].
  split; [|split; [exact HinF2 | split; [rewrite EF2'; exact Efa | split; [rewrite EFl2; exact Efl |
    split; [eapply YCbqGwild.ajournal_xw_unbase0R; [exact HJ2 | exact HWILD]|]]]]].
  - apply (pvi_frame_x (pe_regs en) (pe_sp en) Y fa fl pv_shadow_live W' W2 mem (ms_mem msf)); [| | exact HFRM].
    + intros a Ha. rewrite AVF. exact (KFR a Ha).
    + intros a Ha. apply GRF. exact (PFR a Ha).
  - intros a Ha Hn. rewrite AVF, (HXw' a ltac:(clear - Ha HYr; lia) Hn). exact (HWIN a Ha Hn). }
(* the exit cut's last conjunct: the memory normal form *)
split; [|exact HMN2].
apply (pvi_Qm_ext B en _ code ly2 S2 Hp2 W2 mem2 (ms_mem msf) EQ).
apply (pvD_Qm_items B ARx en pos p1 code o y lyc Sc W' mem ly2 S2 Hp2 W2 regs2 mem2 md2 HPRE Ep1 Hsk' HRD0 HKQ Hc10
  Hcb).
Qed.

End c.
