(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths and module names changed; 233 of its 265 lines of code are new or changed and 320 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_fuzz_malloc_lem.v (a working branch 7a6aa01e779), relocated by
   b_reloc.py (mal; revcheck report (internal path)); the code table covers B's
   fuzz_malloc 0x81b88 and the outlined own 0x81bfc it tail-calls (one table, 91 words).
   Journal steps for the walk of fuzz_malloc (B/FMW_fuzz_malloc.v): a stretch of code that writes only the caller's
   stack window and fuzz/alloc.c's statics (FM_PSTAT_FP), and the call of __asan_poison_memory_region (b, 16) through
   Poison's contract (A/FMpoisonS.v apoison16_realizes, image-generic), each extending the donor journal (YCbq.v ajournal). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0s YG0d YG0p YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0m YF0x YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMpoisonS.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_fuzz_alloc_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* fuzz_malloc 0x81b88 .. 0x81bfc (29 words) and own 0x81bfc .. 0x81cf4 (62 words): 91 words *)
Definition tbl_fmm : ctable := Eval vm_compute in build_table tfibsegs A_fuzz_malloc 91 TEmpty.
Lemma tbl_fmm_eq : tbl_fmm = build_table tfibsegs A_fuzz_malloc 91 TEmpty.
Proof. vm_cast_no_check (eq_refl tbl_fmm). Qed.
Lemma tbl_fmm_ok : table_ok tfibsegs tbl_fmm.
Proof. rewrite tbl_fmm_eq. apply build_table_ok0. unfold A_fuzz_malloc. lia. Qed.

Lemma fmm_pstat_range : forall a, inFP FM_PSTAT_FP a -> 0x99000 <= a < 0x5f7000.
Proof.
intros a (r & Hr & Ha). cbv [FM_PSTAT_FP] in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia.
Qed.

Lemma in_ush_one : forall h s, in_ush [(h, 16)] s = true <-> shadow_addr h <= s < shadow_addr h + 2.
Proof.
intros h s. unfold in_ush. cbn [existsb fst snd]. rewrite Bool.orb_false_r. change (16 / 8) with 2.
rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

(* the bytes a stretch of fuzz_malloc may write besides blocks: its 32-byte frame below the entry sp, and the statics *)
Definition fmm_cell (a : Z) : Prop :=
  G_FAIL <= a < G_FAIL + 8 \/ G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/ G_COUNT <= a < G_COUNT + 8.
Definition fmm_winA (sp0 a : Z) : Prop :=
  (sp0 - 32 <= a < sp0) \/ G_FAIL <= a < G_FAIL + 8 \/ G_COUNT <= a < G_COUNT + 8.
Definition fmm_winC (sp0 a : Z) : Prop :=
  (sp0 - 32 <= a < sp0) \/ G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8.
Lemma fmm_cell_inFP : forall a, fmm_cell a -> inFP FM_PSTAT_FP a.
Proof.
intros a Ha. unfold fmm_cell, G_FAIL, G_LIVE, G_PEAK, G_COUNT in Ha.
destruct Ha as [H|[H|[H|H]]]; [exists (0x9e260, 0x9e268) | exists (0x5d4700, 0x5d4708)
  | exists (0x5d4720, 0x5d4728) | exists (0x5d4740, 0x5d4748)]; (split; [vm_compute; tauto | cbn [fst snd]; lia]).
Qed.
(* the write windows of a concrete region list are inside fmm_win *)
Ltac win_solve Usp :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hw := fresh "Hw" in
  intros a (r & Hin & Hw);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; try rewrite Usp in Hw|]);
  try destruct Hin;
  unfold fmm_winA, fmm_winC, fmm_cell, G_FAIL, G_LIVE, G_PEAK, G_COUNT; lia.

(* the plain symbolic run (YA0o.v SRr_run_gen) that also hands on what msteps keeps: the visible memory grows and
   the hidden bytes do not change *)
Section r. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Hypothesis Hwx : wx_segs_nowrap segs.
Definition run_postG (W : world segs) (E : env) (ss ss' : sstate) (st : run_status)
  (ms : machine_state) (model : Model) (Q : world segs -> config -> Prop) : Prop :=
  forall ms' mat',
  match st with RS_ecall => st_ok_ecall segs E ss' (restrict (w_H W) ms')
  | _ => st_ok segs E ss' (restrict (w_H W) ms') end ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  (forall x, w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
  SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy model) mat' model)) Q.
Lemma SRr_chainG : forall W E ss ss' st ms msr' model Q,
  msteps segs (restrict (w_H W) ms) msr' ->
  match st with RS_ecall => st_ok_ecall segs E ss' msr' | _ => st_ok segs E ss' msr' end ->
  frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
  run_postG W E ss ss' st ms model Q ->
  SRr segs W (mkCfg ms model) Q.
Proof.
intros W E ss ss' st ms msr' model Q Hms HS' Hfr Hk.
apply (SRr_msteps segs Hwx W ms msr' model Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb model model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
- intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
Qed.
Lemma SRr_run_genG : forall W n E ss ss' st ms model Q,
  st_ok segs E ss (restrict (w_H W) ms) -> sym_runN segs tbl n ss = (ss', st) ->
  run_postG W E ss ss' st ms model Q -> SRr segs W (mkCfg ms model) Q.
Proof.
intros W n E ss ss' st ms model Q HS Hrun Hk.
destruct (msteps_run_gen segs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
exact (SRr_chainG W E ss ss' st ms msr' model Q Hms HS' Hfr Hk).
Qed.
End r.

Ltac srr_runG_with tblok HS :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of tblok with
    | table_ok _ ?tbl =>
      let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
        let HWX := lazymatch goal with HWX : wx_segs_nowrap segs |- _ => HWX end in
        eapply (SRr_run_genG segs tbl tblok HWX W FUEL E ss ss' st ms _ _ HS Hrun);
        clear Hrun HS;
        let ms' := fresh "ms" in let mat' := fresh "mat" in
        let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in let HH := fresh "HH" in
        intros ms' mat' HS HF HFr HG HH;
        cbn [ms_mem mkst] in HF, HFr, HG, HH;
        srr_norm_model
      end
    end
  end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis TL : TfibLib B.
#[local] Notation LAWS := (AR_laws_ok tfibsegs B).

(* fuzz_malloc_spec's second disjunct (FMH_Fn.v:146-154): the granted allocation *)
Definition fmm_post2 (regs : bvmap 5 word) ly S (W : world tfibsegs) mem md (n live peak cnt fail : Z)
  : world tfibsegs -> config -> Prop :=
  fun W' c' =>
    cnt <> fail /\ exists res, apost_baseU tfibsegs B STK_fuzz_malloc FM_PSTAT_FP regs ly S W mem md 1 [] [(res - HEAD, HEAD)]
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 res /\ 4096 + HEAD <= res /\
         ablocks B ly' S' = ablocks B ly S ++ [(res - HEAD, n + HEAD)] /\
         fm_rblock tfibsegs B ly' S' W' mem' res n /\
         range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF res n /\
         (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W') mem') res n) /\
         fm_glob tfibsegs W' mem' (live + n) (Z.max peak (live + n)) (cnt + 1) fail) W' c'.

Lemma fmm_env : api_env tfibsegs B.
Proof. exact (tl_env B TL). Qed.

Lemma fmm_pstat_not_owned : forall ly S (W : world tfibsegs) mem md a,
  AR tfibsegs B ly S W mem md -> inFP FM_PSTAT_FP a -> ~ aowned B ly S a.
Proof.
intros ly S W mem md a HAR (r & Hr & Ha). cbv [FM_PSTAT_FP] in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha.
- apply (fma_pstat_not_owned B HB ly S W mem md 0x9e260 a HAR); [vm_compute; tauto | lia].
- apply (fma_pstat_not_owned B HB ly S W mem md 0x5d4700 a HAR); [vm_compute; tauto | lia].
- apply (fma_pstat_not_owned B HB ly S W mem md 0x5d4720 a HAR); [vm_compute; tauto | lia].
- apply (fma_pstat_not_owned B HB ly S W mem md 0x5d4740 a HAR); [vm_compute; tauto | lia].
Qed.

(* a stretch that writes only the caller's stack window [sp0 - STK, sp0) and alloc.c's statics extends the journal:
   the statics are in FP (the image clause exempts them), no runtime-owned byte changes, so AR holds by al_frame *)
Lemma ajournal_stk_pstat : forall STK sp0 FP ly S (W : world tfibsegs) mem md own lyc Sc (Wc : world tfibsegs)
  memc mdc k memc' mdc',
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  (forall a, inFP FM_PSTAT_FP a -> inFP FP a) ->
  (forall x : word, ~ (sp0 - STK <= bv_unsigned x < sp0) -> ~ inFP FM_PSTAT_FP (bv_unsigned x) ->
     mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
  mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
  (forall x : word, w_H Wc x = true -> memc' x = memc x) ->
  same_but_materialized mdc mdc' ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' HJ HFP Hfr Hgr Hhid Hsame.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) -> ~ inFP FM_PSTAT_FP a ->
  aview tfibsegs (w_H Wc) memc' a = aview tfibsegs (w_H Wc) memc a).
{ intros a Ha Hs Hp. apply aview_eq_of. apply Hfr; rewrite unsigned_lit_small by lia; assumption. }
pose proof (same_but_materialized_wvb mdc mdc' Hsame) as Emd.
assert (HAR' : AR tfibsegs B lyc Sc Wc memc' mdc').
{ apply (al_frame _ _ LAWS lyc Sc Wc memc mdc memc' mdc' HAR).
  - intros a Ha Ho. apply Heqw; [exact Ha | |].
    + intros Hs. apply (al_stack _ _ LAWS lyc Sc Wc memc mdc a HAR); [rewrite Eslo, Eshi; lia | exact Ho].
    + intros Hp. exact (fmm_pstat_not_owned lyc Sc Wc memc mdc a HAR Hp Ho).
  - intros a Hv. eapply (aview_keeps_vis tfibsegs); [exact Hgr | exact Hv].
  - rewrite Emd. destruct mdc; reflexivity.
  - rewrite Emd. destruct mdc; reflexivity.
  - rewrite Emd. destruct mdc; reflexivity.
  - intros a _ Hh. exact (Hhid _ Hh). }
split; [exact HAR'|].
split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split.
{ intros a Ha Hs. rewrite <- (F1 a Ha Hs).
  apply Heqw; [lia | exact Hs | intros Hp; pose proof (fmm_pstat_range a Hp); lia]. }
split.
{ intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & _ & _ & _).
  apply Heqw; [lia | lia |].
  intros Hp. apply (blk_img tfibsegs B LAWS lyc Sc Wc memc mdc p n (p + i) HAR H2 ltac:(lia)).
  apply fma_in_img. exact (fmm_pstat_range _ Hp). }
split.
{ intros a Hi Hns He Hps Hsp. rewrite <- (F3 a Hi Hns He Hps Hsp). pose proof (fma_segs_low a Hi) as Hl.
  unfold kLowMemEnd in Hl. apply Heqw; [lia | lia | intros Hp; exact (Hps (HFP a Hp))]. }
split.
{ intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (frames_bounds tfibsegs B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & _).
  assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite <- Efa in Hr.
  pose proof (fs_frame_bytes_nonneg cid) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
  destruct Hr as [Hr | Hr].
  - apply Heqw; [lia | lia |].
    intros Hp. exact (frm_img tfibsegs B LAWS lyc Sc Wc memc mdc cid pos a HAR HinC Hr (fma_in_img a (fmm_pstat_range a Hp))).
  - apply Heqw; [lia | lia | intros Hp; pose proof (fmm_pstat_range a Hp); lia]. }
split; [exact Hgone|].
split; [intros a Ha; eapply apresent_grows; [exact Hgr | apply Hpres, Ha]|].
split; [exact Hstatic|]. split; [|exact HQT].
intros a HXa He. rewrite <- (F5 a HXa He).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (YG0p.AR_extra_law_ok tfibsegs B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp.
apply Heqw; [lia | intros Hs; apply Xs; rewrite Eslo, Eshi; lia |].
intros Hp. exact (Xi (fma_in_img a (fmm_pstat_range a Hp))).
Qed.

(* the call of __asan_poison_memory_region (h, 16): its post (apoison16_realizes) read with the user-poisoned head as
   the allocator made it (unpoison) extends the caller's journal (call_effect_journal, then ajournal_sub) *)
Lemma ajournal_poison16 : forall STK sp0 FP ly S (W : world tfibsegs) mem md own lyc Sc (Wc : world tfibsegs)
  memc mdc k regsP o h mem3 md3,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  spZ regsP = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  ARU tfibsegs B lyc Sc [(h, 16)] Wc mem3 md3 -> same_but_materialized mdc md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsP - PO_WIN <= a < spZ regsP) -> ~ (shadow_addr h <= a < shadow_addr h + 2) ->
     aview tfibsegs (w_H Wc) mem3 a = aview tfibsegs (w_H Wc) memc a) ->
  (forall a, spZ regsP - ESTACK <= a < spZ regsP -> apresent (w_H Wc) mem3 a) ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc (unpoison [(h, 16)] mem3) md3 k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k regsP o h mem3 md3 HJ Hsp Hal Hneg Hbud HARU Hsame Heq Hpres3.
pose proof (ajournal_sub_init tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ESTACK (spZ regsP) [] o
  HJ Hsp Hal Hneg ltac:(unfold ESTACK; lia) Hbud) as J0.
pose proof J0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
assert (J1 : ajournal tfibsegs B ESTACK (spZ regsP) [] lyc Sc Wc memc mdc [] lyc Sc Wc (unpoison [(h, 16)] mem3) md3 0).
{ apply (call_effect_journal tfibsegs B LAWS fma_segs_low fmm_env ESTACK lyc Sc Wc regsP memc mdc lyc Sc Wc
    (unpoison [(h, 16)] mem3) md3 (fun _ => False) [] [] 0).
  - exact (ARU_AR tfibsegs B lyc Sc [(h, 16)] Wc mem3 md3 HARU).
  - apply layout_le_refl.
  - apply wle_refl.
  - apply same_io_materialized, Hsame.
  - intros a Ha Ho _ Hsc _.
    destruct (in_ush [(h, 16)] (bv_unsigned (Z_to_bv 64 a))) eqn:Eu.
    + exfalso. apply Ho. rewrite unsigned_lit_small in Eu by lia.
      exact (proj1 (ush_facts tfibsegs B lyc Sc [(h, 16)] Wc mem3 md3 _ HARU Eu)).
    + rewrite aview_unpoison_out by exact Eu.
      rewrite unsigned_lit_small in Eu by lia.
      apply Heq; [exact Ha | intros Hw; apply Hsc; left; unfold PO_WIN, ESTACK in *; lia |].
      intros Hsh. rewrite (proj2 (in_ush_one h a) Hsh) in Eu. discriminate.
  - intros a Ha. destruct (Hpres3 a Ha) as [Hh [b Hb]]. split; [exact Hh|]. unfold unpoison.
    destruct (in_ush [(h, 16)] (bv_unsigned (Z_to_bv 64 a))); [eexists; reflexivity | exists b; exact Hb].
  - exact HAR.
  - exact Hstk1.
  - reflexivity.
  - lia.
  - lia.
  - apply Nat.le_refl.
  - intros a [].
  - intros p n i H1 H2. exfalso. exact (H2 H1).
  - exact HQT. }
pose proof (ajournal_sub tfibsegs B LAWS fma_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ESTACK
  (spZ regsP) [] [] lyc Sc Wc (unpoison [(h, 16)] mem3) md3 0 HJ J1 ltac:(unfold ESTACK in *; lia) ltac:(lia)
  ltac:(intros a (r & [] & _))) as J2.
rewrite Z.add_0_r in J2. exact J2.
Qed.

End c.
