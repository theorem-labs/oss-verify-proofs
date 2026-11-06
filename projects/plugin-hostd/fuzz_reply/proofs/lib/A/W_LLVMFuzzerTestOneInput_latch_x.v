(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: SEG_LATCH of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput over a generic allocator
   relation ARx (a Theorem Labs lane's route (b)): the ARx conversion of lib/A/W_LLVMFuzzerTestOneInput_latch.v's lf_seg_latch
   (W8's, Qed at a working branch 44de651f71b), stated as the Section hypothesis SEG_LATCH of
   lib/A/W_LLVMFuzzerTestOneInput_cut_x.v Section w.  The AR file is NOT edited.
   - Cited from the AR file (they do not mention AR): the keep windows (lt_keep_lo, lt_keep_hi, lt_akept_of_low,
     lt_akept_rng, lt_akept_of_rng), the frame, ROM and jump-table transport (lt_aframe_kept, lt_sv8_kept, lt_rom_kept,
     lt_jt_kept, lt_aframe_false), the table-byte lemmas (lt_nth_bzs, lt_nth_concat, lt_nth_used, lt_nth_cap, lt_eb_len,
     lt_le8_byte, RE0), the two entry states (lt_entry, lt_entry2), the register
     lemmas (lt_pres, lt_fin_regs, lt_addiw_U, lt_sv_of_U) and the definitions they use.
   - Converted here (their AR statements read AR): the transport kit's block bounds (lt_blk_x .. lt_aout_x,
     lt_amodel_kept_x, lt_ainput_kept_x), lt_cb_entry_x, and the call site's afn_pre (lt_afn_pre_at_x), over ARx with
     AR_laws_x; the walk, over cut_x's generic invariants (Hp after cx, Hp3 after S3) and W_journal_x's chain.
     One step differs in form: AR_laws_x's alx_blocks has no size bound `0 <= n` (cgif's al_blocks had it), so
     lt_blk_x takes it as a premise and each caller passes it from the block's own text (every block the model names
     has a positive size there).
   - Section hypotheses beyond cut_x's Section w header: W1_check_bounded (check_bounded's contract,
     W_contract_x.cb_spec_x; its post aleafx_post_x carries the kept clause the AR file added as cbk_spec) and
     ERRNO_LOW (the AR file's, verbatim).
   - Route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0, a Theorem Labs lane's brief-lfR): Section wR's lf_seg_latch_xR is cut_x Section wR's
     SEG_LATCH_R (lib/A/W_LLVMFuzzerTestOneInput_cut_x.v:466) at a world relation R containing wle.  check_bounded is a leaf that calls no allocator,
     so it keeps the STRICT W1_check_bounded; the segment is the strict walk over the cut's R journal, lifted to R at
     its head (cut_x's lf_seg_jt_xR form).  Section chkR checks it in SEG_LATCH_R's text and argument position. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_cut_x W_LLVMFuzzerTestOneInput_latch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
(* the zify flag as the AR file's proofs expect it, whatever a Required file leaves (as cut_x.v:55) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------
   The transport kit's block bounds over ARx (_latch.v:49-243, Section kit; :445 lt_ainput_kept, :329 lt_amodel_kept,
   :538 lt_cb_entry).  The proofs are the AR file's, with lt_blk's bound read off AR_laws_x's alx_blocks. *)
Section kit_x.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* _latch.v:60 lt_low, a Section-local Ltac of the AR file (dropped at its End kit), restated *)
Ltac lt_low :=
  cbn [fst snd gfp]; unfold CEIL8 in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof lt_ceil_lo; lia.

(* :83 lt_blk: a live block's bytes, and the 7 bytes of alignment slack a key's text may carry past them.  The size
   bound 0 <= n is a premise: alx_blocks does not carry it. *)
Lemma lt_blk_x : forall ly S Hp (W : world segs) mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S Hp W mem md p n HAR Hin Hn.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H1 & H2 & _).
  pose proof (req_size_pos n Hn) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.

(* :108 struct list *)
Lemma lt_alist_x : forall ly S Hp (W : world segs) mem md LA l lines,
  ARx ly S Hp W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= CEIL8 ->
  lt_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : lt_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (lt_blk_x ly S Hp W mem md _ _ HAR K1 ltac:(lia)) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; lia|]. apply lt_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(unfold AREC; lia)) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
    cbn [gfp fst snd]. rewrite lt_bzs_len, length_app, lt_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* :138 struct source *)
Lemma lt_asrc_x : forall ly S Hp (W : world segs) mem md HA h,
  ARx ly S Hp W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= CEIL8 ->
  lt_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (lt_alist_x ly S Hp W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                       ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (lt_alist_x ly S Hp W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                       ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (lt_alist_x ly S Hp W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                       ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hpb ltac:(unfold APARTIAL; lia)) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply lt_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite lt_bzs_len, Hpj. unfold APARTIAL, CEIL8 in *. lia.
    + apply lt_fp_low_app; [exact A1|]. apply lt_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* :164 one source_t of the relay's table *)
Lemma lt_aentry_x : forall ly S Hp (W : world segs) mem md e,
  ARx ly S Hp W mem md -> aentry_ok B ly S W mem e ->
  lt_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : lt_fp_low (map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (lt_blk_x ly S Hp W mem md _ _ HAR M1 ltac:(lia)) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply lt_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
      apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
      cbn [gfp snd]. rewrite lt_bzs_len, length_app. unfold CEIL8 in *. lia.
    + apply lt_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _ & Hk8 & _)]; [lia|].
        destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite lt_bzs_len, lt_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold CEIL8. pose proof lt_ceil_lo. lia. }
        destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* :203 the relay's table, at fuzz_reply.asan's globals *)
Lemma lt_arelay_x : forall ly S Hp (W : world segs) mem md G es,
  ARx ly S Hp W mem md -> arelay_at B fr_globals ly S W mem G es ->
  lt_fp_low (arelay_fp fr_globals G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (lt_blk_x ly S Hp W mem md _ _ HAR R8 ltac:(unfold ATABLE; lia)) as (P1 & P2 & P3).
  assert (HE : lt_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (lt_aentry_x ly S Hp W mem md e HAR (R10 e He)) as [F1 _].
      rewrite lt_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (lt_aentry_x ly S Hp W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* :227 the controller's stream *)
Lemma lt_aout_x : forall ly S Hp (W : world segs) mem md c O mx no cap out,
  ARx ly S Hp W mem md -> aout_at B fr_globals ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  lt_fp_low (aout_fp B fr_globals cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S Hp W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply lt_fp_low_cons; [lt_low | lt_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | cbn; unfold CEIL8 in *; lia | apply lt_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* :329 the model *)
Lemma lt_amodel_kept_x : forall ly S Hp (W : world segs) mem md (W' : world segs) mem' m,
  ARx ly S Hp W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S Hp W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= CEIL8)
      by (unfold fr_RG, CEIL8; cbn; unfold ASRC; pose proof lt_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (lt_asrc_x ly S Hp W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (lt_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (lt_arelay_x ly S Hp W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_globals ly S W mem ly S W' mem' _ _ M3
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (lt_aout_x ly S Hp W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_globals ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_globals W mem W' mem' _ M5).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_globals W mem W' mem' _ M6).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_globals W mem W' mem' M7).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, CEIL8 in *. pose proof lt_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, CEIL8 in *. pose proof lt_ceil_lo. lia.
Qed.

(* :445 the input block *)
Lemma lt_ainput_kept_x : forall cx ly S Hp (W : world segs) mem md (W' : world segs) mem',
  ARx ly S Hp W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S Hp W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hpe) | (Hn & Hin)]; [lia|].
  destruct (lt_blk_x ly S Hp W mem md _ _ HAR Hin ltac:(lia)) as (P1 & P2 & P3).
  unfold CEIL8. lia.
Qed.

(* :538 reading one entry's used and cap out of the relay's table (check_bounded's pre); the relation is not read *)
Lemma lt_cb_entry_x : forall ly S Hp (W : world segs) mem md G es j,
  ARx ly S Hp W mem md -> arelay_at B fr_globals ly S W mem G es ->
  0 <= j < Z.of_nat (length es) -> cb_entry_ok W mem G j.
Proof.
  intros ly S Hp W mem md G es j HAR HR Hj.
  pose proof HR as (_ & _ & _ & _ & _ & _ & Hlen16 & Hblk & (tail & T1 & T2 & T3) & HF & _).
  set (jn := Z.to_nat j).
  assert (Hjn : (jn < length es)%nat) by (unfold jn; lia).
  set (e := nth jn es RE0).
  assert (He : In e es) by (unfold e; apply nth_In; exact Hjn).
  rewrite Forall_forall in HF.
  pose proof (HF e He) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HLall : forall x, In x es -> length (entry_bytes x) = 56%nat).
  { intros x Hx. destruct (HF x Hx) as (_ & _ & P1 & P2 & _). exact (lt_eb_len x P1 P2). }
  assert (Hcl : length (concat (map entry_bytes es)) = (56 * length es)%nat).
  { clear - HLall. induction es as [|x xs IH]; [reflexivity|].
    cbn [map concat]. rewrite length_app, (HLall x ltac:(left; reflexivity)).
    rewrite IH by (intros y Hy; apply HLall; right; exact Hy). cbn [length]. lia. }
  (* the byte at index 56*jn + o of the table is the entry's byte at o *)
  assert (HB : forall o, (o < 56)%nat ->
    mbyte segs (arm W mem) (G + Z.of_nat (56 * jn + o)) =
    Some (Z_to_bv 8 (bz (nth o (entry_bytes e) (Z_to_bv 8 0))))).
  { intros o Ho.
    assert (Hlt : (56 * jn + o < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
    { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
    rewrite (garr8_mbyte segs (arm W mem) G _ (56 * jn + o)%nat T3 Hlt). f_equal.
    rewrite (lt_nth_bzs _ (56 * jn + o)%nat ltac:(rewrite length_app, Hcl; lia)).
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite (lt_nth_concat es jn o (Z_to_bv 8 0) HLall Hjn Ho). reflexivity. }
  exists (re_used e), (re_cap e).
  assert (Hused : val_mem segs (arm W mem) (G + 56 * j + 24) 8 (re_used e)).
  { intros k Hk.
    replace (G + 56 * j + 24 + Z.of_nat k) with (G + Z.of_nat (56 * jn + (24 + k))) by (unfold jn; lia).
    rewrite (HB (24 + k)%nat ltac:(lia)). f_equal.
    rewrite (lt_nth_used e k (Z_to_bv 8 0) Hk K3).
    apply lt_le8_byte; [exact Hk | lia]. }
  assert (Hcap : val_mem segs (arm W mem) (G + 56 * j + 32) 8 (re_cap e)).
  { intros k Hk.
    replace (G + 56 * j + 32 + Z.of_nat k) with (G + Z.of_nat (56 * jn + (32 + k))) by (unfold jn; lia).
    rewrite (HB (32 + k)%nat ltac:(lia)). f_equal.
    rewrite (lt_nth_cap e k (Z_to_bv 8 0) Hk K3).
    apply lt_le8_byte; [exact Hk | lia]. }
  split; [exact Hused|]. split; [exact Hcap|].
  assert (Hle : re_used e <= re_cap e).
  { destruct K10 as [(Hc & _ & Hu) | (Hc & _ & Hjk & _)]; lia. }
  unfold APARTIAL in K8. split; [lia|]. split; [lia | lia].
Qed.
End kit_x.

(* ------------------------------------------------------------------------------------------------
   The walk, in cut_x's Section w (its header, verbatim), plus the AR file's two Section hypotheses converted. *)
Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* _latch.v:298 W1_check_bounded, converted: check_bounded's contract over ARx, W_contract_x.v:163
   cb_spec_x B PST ARx (BASE + AF_fr_check_bounded), whose post (:106 aleafx_post_x) carries the kept clause the AR
   file's cbk_spec added (W1Verify's pb_check_bounded_x, a working branch be8158006bd, proves it). *)
Hypothesis W1_check_bounded : cb_spec_x B PST ARx (BASE + AF_fr_check_bounded).
(* _latch.v:302 ERRNO_LOW, verbatim *)
Hypothesis ERRNO_LOW : 0 <= as_errno B /\ as_errno B + 4 <= CEIL8.

Let RUN := paj_run_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).
(* _latch.v:595-601, 793 Section-local Ltacs of the AR file (dropped at its End w), restated *)
Ltac lt_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Ltac lt_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
Ltac lt_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac lt_prreg_raw HS r Hr :=
  lazymatch type of HS with st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict] in Hr end.

(* :632 lt_afn_pre_at: check_bounded's afn_pre at sp = F, over the generic pre and journal (YCbqG.afn_pre_x_at,
   W_frame_x.aview_above_of_journal_x, W_journal_x.ajournal_gx_inner_x) *)
Lemma lt_afn_pre_at_x : forall cx Hp full ly3 S3 Hp3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 Hp3 W regs mem md ch.
Proof.
  intros cx Hp full ly3 S3 Hp3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ0) as HAB.
    pose proof HFR as (HSV & _).
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* :799 lf_seg_latch over ARx: cut_x Section w's SEG_LATCH (W_LLVMFuzzerTestOneInput_cut_x.v:562) *)
Theorem lf_seg_latch_x : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_K_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp t W c ->
  SRr segs W c (fun W' c' =>
    INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp (t + 1) W' c' \/ INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp W' c').
Proof.
  intros cx Hp t W c HB HK.
  destruct HK as (regs & mem & md & -> & HROM & HC).
  pose proof HC as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  destruct (lt_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs lt_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs lt_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_latch)) with (Z_to_bv 64 (BASE + AF_LLVM_latch)).
  paj_run_to_tok_x RUNTO HS HJ SHOK LBspan AF_fr_check_bounded.
  { apply awr_ok_x_nil. }
  pmkst HS.
  lt_mem HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs lt_extra lt_kept HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof HR as ((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Rt & R22 & R144 & Rk).
  (* the frame's numbers: F is 320..351 below the entry sp, which is 32768 above ly_stk_lo >= alloc_ceiling *)
  pose proof HB as (HAI0 & HPRE0).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hn26 : c_n cx < 2 ^ 26)
    by (unfold fr_lib_pre_cf_x in HPRE0; destruct HPRE0 as (_ & _ & _ & _ & [(H0 & _) | (H0 & _)] & _); lia).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : CEIL8 + 32000 <= lf_F cx) by (unfold CEIL8, LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= sp0) by lia.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold CEIL8 in *. lia. }
  (* check_bounded's afn_pre *)
  destruct (lt_afn_pre_at_x cx Hp true ly3 S3 Hp3 fpos k W mem mdc (ms_regs ms) CB_STK HB HJ HFR Hsp1)
    as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CB_STK. lia. }
  { unfold CB_STK, LLVMF_STK. lia. }
  (* its functional premises, from the relay's table *)
  pose proof HJ as (_ & _ & (memS & HJi & Hag) & _).
  pose proof (proj1 HJi) as HAR.
  pose proof HMOD as (_ & _ & HREL & _).
  pose proof HREL as (Rs1 & _ & Rs3 & _ & _ & _ & Rs7 & Rs8 & _).
  destruct (lt_blk_x B ARx LAWS ly3 S3 Hp3 W mem mdc _ _ HAR Rs8 ltac:(unfold ATABLE; lia)) as (PG1 & PG2 & PG3).
  set (n := Z.of_nat (length (lm_es m))).
  assert (Pn : - 2 ^ 31 <= n < 2 ^ 31) by (unfold n; lia).
  assert (Pns : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nsrc) 4 (n mod 2 ^ 32)).
  { replace (VAL A_g_nsrc) with (rg_nsrc fr_RG) by (vm_compute; reflexivity).
    rewrite Z.mod_small by (unfold n; lia). exact Rs3. }
  assert (Psr : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_src) 8 (lm_G m)).
  { replace (VAL A_g_src) with (rg_src fr_RG) by (vm_compute; reflexivity). exact Rs1. }
  assert (PP : 0 <= lm_G m < 2 ^ 64) by lia.
  assert (Pblk : 0 < n -> In (lm_G m, ATABLE) (ablocks B ly3 S3) /\ 56 * n <= req_size ATABLE).
  { intros _. split; [exact Rs8|]. unfold req_size, ATABLE, n. cbn. lia. }
  assert (Pent : forall j, 0 <= j < n -> cb_entry_ok W mem (lm_G m) j)
    by (intros j Hj; exact (lt_cb_entry_x B ARx ly3 S3 Hp3 W mem mdc (lm_G m) (lm_es m) j HAR HREL Hj)).
  eapply SRr_bind.
  { exact (W1_check_bounded W ly3 S3 Hp3 (ms_regs ms) mem mdc ch n (lm_G m) ATABLE HPREc Pn Pns Psr PP Pblk Pent). }
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HKEEP & _).
  rewrite Hsp1 in HJc, HKEEP. unfold CB_STK in HKEEP.
  clear HS SHOK HF HFr.
  (* check_bounded's journal inside this function's: W2's ajournal_gx_sub_x at G_fr, the callee's lifted from G = [] *)
  assert (HJc' : ajournal_gx_x segs B PST ARx G_fr 0 [] CB_STK (lf_F cx) [] ly3 S3 Hp3 W mem mdc [] ly3 S3 Hp3 W2 mem2 md2 0).
  { refine (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] CB_STK (lf_F cx) [] ly3 S3 Hp3 W mem mdc [] ly3 S3 Hp3
              W2 mem2 md2 0 _ HJc).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem mdc k
     CB_STK (lf_F cx) 0 [] [] [] ly3 S3 Hp3 W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CB_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  (* every fact of the cut, kept across the call *)
  assert (HLO : CEIL8 <= lf_F cx - 16) by lia.
  pose proof (lt_keep_lo W W2 mem mem2 (lf_F cx) HKEEP HLO) as KL.
  pose proof (lt_keep_hi W W2 mem mem2 (lf_F cx) HKEEP ltac:(unfold CEIL8 in *; lia)) as KH.
  assert (Hin1 : In (1, fpos) (frames S3)).
  { pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem mdc 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  replace (fs_frame_bytes 1) with 128 in HFF1 by reflexivity.
  pose proof (lt_aframe_kept cx true (frame_addr ly3 1 fpos) W W2 mem mem2 HFR HKEEP HLO HFhi
     ltac:(lia) ltac:(lia) ltac:(unfold CEIL8; lia) ltac:(unfold SB; lia) ltac:(unfold SB, CEIL8; lia)) as HFR2.
  (* the fake frame's flag word (lcut_x's conjunct after aframe_at), kept like the fake frame's other words *)
  pose proof (lt_sv8_kept W W2 mem mem2 (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)
     (fun x Hx => KL x ltac:(unfold CEIL8 in *; lia)) HFL) as HFL2.
  pose proof (lt_amodel_kept_x B ARx LAWS ly3 S3 Hp3 W mem mdc W2 mem2 m HAR HMOD
     (proj1 ERRNO_LOW) (proj2 ERRNO_LOW) KL) as HMOD2.
  pose proof (lt_ainput_kept_x B ARx LAWS cx ly3 S3 Hp3 W mem mdc W2 mem2 HAR HIN (eq_sym HlenP) KL) as HIN2.
  pose proof (lt_rom_kept W W2 mem mem2 HRV KL) as HRV2.
  pose proof (lt_jt_kept W W2 mem mem2 HROM KL) as HROM2.
  set (nl := c_n cx - lm_k m) in *.
  assert (R144b : sv8 W2 mem2 (lf_F cx + 144) nl).
  { apply (lt_sv8_kept W W2 mem mem2); [|exact R144]. intros x Hx. apply KH. lia. }
  (* the registers check_bounded keeps *)
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r lt_kept -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (lt_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  assert (H9b : getr regs2 9 = w64 (lf_F cx))
    by (rewrite (RR 9%bv ltac:(lt_cs) ltac:(unfold lt_kept; lt_in)); exact R9).
  assert (Hnl : 0 <= nl <= 2 ^ 26) by (unfold nl; lia).
  destruct (lt_entry2 W2 regs2 mem2 (lf_F cx) nl H9b ltac:(lia) ltac:(lia) Hnl R144b) as [HSb SHOKb].
  (* the two cut points the walk ends at, from the facts kept across the call: the shutdown block X after
     t + 1 operations, and the loop head H of operation t + 1 *)
  assert (XFIN : forall c, (exists rf mdf, c = cfg_at segs (fr_B0 + AF_LLVM_exit) rf mem2 mdf /\
      (forall r, In r lt_saved -> getr rf r = getr regs r) /\
      ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp
        (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W2 mem2 mdf k) ->
      INV_X_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp W2 c).
  { intros c (rf & mdf & -> & KX & HJf).
    exists rf, mem2, mdf, (t + 1). split; [reflexivity|]. split; [exact HROM2|].
    exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
    split; [exact HJf|]. split; [reflexivity|]. split; [exact (lt_aframe_false _ _ _ _ HFR2)|]. split; [exact HFL2|].
    split; [exact HMOD2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
    split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    unfold lregs_X.
    repeat split;
      first [ match goal with |- getr rf ?r = _ => rewrite (KX r ltac:(unfold lt_saved; lt_in)) end; assumption
            | lia ]. }
  assert (HFIN : forall c, (exists rf mdf, c = cfg_at segs (fr_B0 + AF_LLVM_head) rf mem2 mdf /\
      (forall r, In r lt_saved -> getr rf r = getr regs r) /\
      getr rf 6 = w64 4 /\ getr rf 7 = w64 1 /\ getr rf 21 = w64 nl /\ getr rf 27 = w64 (t + 1) /\
      ajournal_gx_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp
        (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W2 mem2 mdf k) ->
      t <= 510 -> nl <> 0 -> INV_H_x B NP G_fr fr_FP PST ARx LSx RINV cx Hp (t + 1) W2 c).
  { intros c (rf & mdf & -> & KX & Q6 & Q7 & Q21 & Q27 & HJf) Ht Hn.
    assert (Hk1 : lm_k m < c_n cx) by (unfold nl in Hn; lia).
    exists rf, mem2, mdf. split; [reflexivity|]. split; [exact HROM2|].
    exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
    split; [exact HJf|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|].
    split; [exact HMOD2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
    split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    unfold lregs_H, lregs_common.
    repeat split;
      first [ exact Q6 | exact Q7 | exact Q21 | exact Q27
            | match goal with |- getr rf ?r = _ => rewrite (KX r ltac:(unfold lt_saved; lt_in)) end; assumption
            | unfold OPS_MAX in *; lia ]. }
  rewrite Q1.
  change (Z_to_bv 64 (BASE + 8616)) with (Z_to_bv 64 (BASE + AF_LLVM_latch4)).
  remember (Eimg (Ereg regs2 (lt2_extra nl))) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 (lt2_extra nl)) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E27 : ew Eb 27 = Z_to_bv 64 t).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 27 27%bv eq_refl).
    rewrite (RR 27%bv ltac:(lt_cs) ltac:(unfold lt_kept; lt_in)). exact R27. }
  assert (E32 : ew Eb 32 = Z_to_bv 64 nl)
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  clear HEb.
  paj_run_tok_x RUN HSb HJ2 SHOKb LBspan.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lt_mem HF Em2. clear HF HFr.
  assert (Rt' : 0 <= t < 512) by (unfold OPS_MAX in Rt; exact Rt).
  (* bltu a0(510), s11(t): after operation 511 the loop is left *)
  psrr_branch_tok RUN BR HSb SHOKb LBspan.
  - assert (Ht511 : t = 511).
    { rewrite branch_ltu_U, (U_lit Eb 510), (U_atom Eb 27 t E27) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
    paj_run_to_tok_x RUNTO HSb HJ2 SHOKb LBspan AF_LLVM_exit.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    lt_mem HF Em3.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (lt2_extra nl) lt2_kept HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply SRr_ret. right. apply XFIN.
    lazymatch goal with |- exists _ _, {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} = _ /\ _ => exists r, d end.
    split; [reflexivity|]. split; [exact (lt_fin_regs regs regs2 _ KR2 RR)|]. exact HJ2.
  - assert (Ht510 : t <= 510).
    { rewrite branch_ltu_U, (U_lit Eb 510), (U_atom Eb 27 t E27) in Hc by lia. apply Z.ltb_ge in Hc. lia. }
    (* addiw s11,s11,1 *)
    paj_run_tok_x RUN HSb HJ2 SHOKb LBspan.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    lt_mem HF Em3. clear HF HFr Hc.
    (* bnez s5(in.n): the next operation, or the shutdown *)
    psrr_branch_tok RUN BR HSb SHOKb LBspan.
    + assert (Hn0 : nl <> 0).
      { rewrite branch_ne_U, (U_atom Eb 32 nl E32), U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
        exact Hc. }
      paj_run_to_tok_x RUNTO HSb HJ2 SHOKb LBspan AF_LLVM_head.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      lt_mem HF Em4.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (lt2_extra nl) lt2_kept HSb HAEb
        ltac:(vm_compute; reflexivity)) as KR2.
      cbn [ms_regs restrict] in KR2.
      prreg HSb (6%bv : bv 5) Q6. prreg HSb (7%bv : bv 5) Q7. prreg HSb (21%bv : bv 5) Q21.
      lt_prreg_raw HSb (27%bv : bv 5) Q27.
      rewrite ?E32 in Q21.
      rewrite (lt_sv_of_U Eb _ (t + 1) (lt_addiw_U Eb t E27 ltac:(lia)) ltac:(lia)) in Q27.
      pmkst HSb.
      rewrite Em4 in *. rewrite Em3 in *. rewrite Em2 in *.
      apply SRr_ret. left. apply HFIN; [|exact Ht510|exact Hn0].
      lazymatch goal with |- exists _ _, {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} = _ /\ _ => exists r, d end.
      split; [reflexivity|]. split; [exact (lt_fin_regs regs regs2 _ KR2 RR)|].
      split; [exact Q6|]. split; [exact Q7|]. split; [exact Q21|]. split; [exact Q27|]. exact HJ2.
    + (* j 0x84bf8 *)
      paj_run_to_tok_x RUNTO HSb HJ2 SHOKb LBspan AF_LLVM_exit.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      lt_mem HF Em4.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (lt2_extra nl) lt2_kept HSb HAEb
        ltac:(vm_compute; reflexivity)) as KR2.
      cbn [ms_regs restrict] in KR2.
      pmkst HSb.
      rewrite Em4 in *. rewrite Em3 in *. rewrite Em2 in *.
      apply SRr_ret. right. apply XFIN.
      lazymatch goal with |- exists _ _, {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} = _ /\ _ => exists r, d end.
      split; [reflexivity|]. split; [exact (lt_fin_regs regs regs2 _ KR2 RR)|]. exact HJ2.
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): SEG_LATCH at a world relation R containing wle, cut_x Section wR's SEG_LATCH_R
   (W_LLVMFuzzerTestOneInput_cut_x.v:466).  The segment's one call, check_bounded, is a leaf that calls no allocator,
   so it frees nothing and re-hides no shadow: its STRICT contract W1_check_bounded is kept (top_x passes the strict
   pb_check_bounded_x), its wle step stays a wle step, and its strict journal lifts to R (ajournal_gx_xR_mono, WLE_R).
   So the segment is the strict walk of lf_seg_latch_x over the cut's R journal (paj_run_x_xR, ajournal_gx_sub_xR
   with R_trans), lifted to SRrG at its head by SRr_SRrG (cut_x's lf_seg_jt_xR form).  At R := wle the texts are
   lf_seg_latch_x's; the strict proofs above are kept unchanged.  lf_seg_latch_xR takes all three laws (top_x's one
   bullet shape `.. R R_refl R_trans WLE_R`, a Theorem Labs lane's ruling): R_refl is unused, and named once in its proof so
   that the Section abstracts it. *)
Section wR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Let RUNR := paj_run_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].
Let RUNTOR := paj_run_to_x_xR (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 [].

(* lt_afn_pre_at_x over the R journal (ajournal_gx_inner_xR, aview_above_of_journal_xR, afn_pre_x_atR) *)
Lemma lt_afn_pre_at_xR : forall cx Hp full ly3 S3 Hp3 fpos k (W : world segs) mem md regs STK1,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k ->
  aframe_at cx full (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre_x segs B ARx STK1 ly3 S3 Hp3 W regs mem md ch.
Proof.
  intros cx Hp full ly3 S3 Hp3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite Z.mod_mod_divide by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem md k HJ0) as HAB.
    pose proof HFR as (HSV & _).
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 Hp3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* lib/A/W_LLVMFuzzerTestOneInput_cut_x.v:466 SEG_LATCH_R: lf_seg_latch_x's walk over the cut's R journal *)
Theorem lf_seg_latch_xR : forall cx Hp t W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp t W c ->
  SRrG segs R W c (fun W' c' =>
    INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp (t + 1) W' c' \/
    INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp W' c').
Proof.
  intros cx Hp t W c HB HK.
  (* R_refl: in the signature only (the one bullet shape) *)
  pose proof R_refl as HRrefl. clear HRrefl.
  (* the segment's world moves only by check_bounded's wle step: the strict walk lifts to R *)
  apply (SRr_SRrG segs R WLE_R).
  destruct HK as (regs & mem & md & -> & HROM & HC).
  pose proof HC as (own & ly3 & S3 & Hp3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HNP & HRI & HR).
  destruct (lt_entry W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs lt_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs lt_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  unfold cfg_at. change (w64 (fr_B0 + AF_LLVM_latch)) with (Z_to_bv 64 (BASE + AF_LLVM_latch)).
  paj_run_to_tok_x RUNTOR HS HJ SHOK LBspan AF_fr_check_bounded.
  { apply awr_ok_x_nil. }
  pmkst HS.
  lt_mem HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs lt_extra lt_kept HS HAE ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1.
  cbn [ms_regs restrict] in KR.
  rewrite Em in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof HR as ((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Rt & R22 & R144 & Rk).
  (* the frame's numbers: F is 320..351 below the entry sp, which is 32768 above ly_stk_lo >= alloc_ceiling *)
  pose proof HB as (HAI0 & HPRE0).
  assert (HPREE : afn_pre_x segs B ARx LLVMF_STK (c_ly cx) (c_S cx) Hp (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf_x in HPRE0; tauto).
  assert (Hn26 : c_n cx < 2 ^ 26)
    by (unfold fr_lib_pre_cf_x in HPRE0; destruct HPRE0 as (_ & _ & _ & _ & [(H0 & _) | (H0 & _)] & _); lia).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (HFlo : CEIL8 + 32000 <= lf_F cx) by (unfold CEIL8, LLVMF_STK in *; lia).
  assert (HFhi : lf_F cx + 320 <= sp0) by lia.
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold CEIL8 in *. lia. }
  (* check_bounded's afn_pre *)
  destruct (lt_afn_pre_at_xR cx Hp true ly3 S3 Hp3 fpos k W mem mdc (ms_regs ms) CB_STK HB HJ HFR Hsp1)
    as (ch & HPREc).
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3. }
  { rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4. }
  { rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8. }
  { unfold CB_STK. lia. }
  { unfold CB_STK, LLVMF_STK. lia. }
  (* its functional premises, from the relay's table *)
  pose proof HJ as (_ & _ & (memS & HJi & Hag) & _).
  pose proof (proj1 HJi) as HAR.
  pose proof HMOD as (_ & _ & HREL & _).
  pose proof HREL as (Rs1 & _ & Rs3 & _ & _ & _ & Rs7 & Rs8 & _).
  destruct (lt_blk_x B ARx LAWS ly3 S3 Hp3 W mem mdc _ _ HAR Rs8 ltac:(unfold ATABLE; lia)) as (PG1 & PG2 & PG3).
  set (n := Z.of_nat (length (lm_es m))).
  assert (Pn : - 2 ^ 31 <= n < 2 ^ 31) by (unfold n; lia).
  assert (Pns : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_nsrc) 4 (n mod 2 ^ 32)).
  { replace (VAL A_g_nsrc) with (rg_nsrc fr_RG) by (vm_compute; reflexivity).
    rewrite Z.mod_small by (unfold n; lia). exact Rs3. }
  assert (Psr : val_mem segs (mrestrict (w_H W) mem) (VAL A_g_src) 8 (lm_G m)).
  { replace (VAL A_g_src) with (rg_src fr_RG) by (vm_compute; reflexivity). exact Rs1. }
  assert (PP : 0 <= lm_G m < 2 ^ 64) by lia.
  assert (Pblk : 0 < n -> In (lm_G m, ATABLE) (ablocks B ly3 S3) /\ 56 * n <= req_size ATABLE).
  { intros _. split; [exact Rs8|]. unfold req_size, ATABLE, n. cbn. lia. }
  assert (Pent : forall j, 0 <= j < n -> cb_entry_ok W mem (lm_G m) j)
    by (intros j Hj; exact (lt_cb_entry_x B ARx ly3 S3 Hp3 W mem mdc (lm_G m) (lm_es m) j HAR HREL Hj)).
  eapply SRr_bind.
  { exact (W1_check_bounded W ly3 S3 Hp3 (ms_regs ms) mem mdc ch n (lm_G m) ATABLE HPREc Pn Pns Psr PP Pblk Pent). }
  intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HKEEP & _).
  rewrite Hsp1 in HJc, HKEEP. unfold CB_STK in HKEEP.
  clear HS SHOK HF HFr.
  (* check_bounded's journal inside this function's: lifted from G = [] to G_fr, and from wle to R *)
  assert (HJc' : ajournal_gx_xR segs B PST ARx R G_fr 0 [] CB_STK (lf_F cx) [] ly3 S3 Hp3 W mem mdc [] ly3 S3 Hp3
                   W2 mem2 md2 0).
  { refine (ajournal_gx_xR_mono segs B PST ARx (@wle segs) R WLE_R G_fr 0 [] CB_STK (lf_F cx) [] ly3 S3 Hp3 W mem mdc []
              ly3 S3 Hp3 W2 mem2 md2 0 _).
    refine (ajournal_gx_G_mono_x segs B PST ARx [] G_fr 0 [] CB_STK (lf_F cx) [] ly3 S3 Hp3 W mem mdc [] ly3 S3 Hp3
              W2 mem2 md2 0 _ HJc).
    intros a Ha. exfalso. exact (inG_nil a Ha). }
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W mem mdc k
     CB_STK (lf_F cx) 0 [] [] [] ly3 S3 Hp3 W2 mem2 md2 0 HJ HJc'
     ltac:(unfold CB_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  (* every fact of the cut, kept across the call *)
  assert (HLO : CEIL8 <= lf_F cx - 16) by lia.
  pose proof (lt_keep_lo W W2 mem mem2 (lf_F cx) HKEEP HLO) as KL.
  pose proof (lt_keep_hi W W2 mem mem2 (lf_F cx) HKEEP ltac:(unfold CEIL8 in *; lia)) as KH.
  assert (Hin1 : In (1, fpos) (frames S3)).
  { pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs. left. reflexivity. }
  destruct (frames_bounds_x segs B ARx LAWS ly3 S3 Hp3 W mem mdc 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  replace (fs_frame_bytes 1) with 128 in HFF1 by reflexivity.
  pose proof (lt_aframe_kept cx true (frame_addr ly3 1 fpos) W W2 mem mem2 HFR HKEEP HLO HFhi
     ltac:(lia) ltac:(lia) ltac:(unfold CEIL8; lia) ltac:(unfold SB; lia) ltac:(unfold SB, CEIL8; lia)) as HFR2.
  (* the fake frame's flag word (lcut_xR's conjunct after aframe_at), kept like the fake frame's other words *)
  pose proof (lt_sv8_kept W W2 mem mem2 (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos)
     (fun x Hx => KL x ltac:(unfold CEIL8 in *; lia)) HFL) as HFL2.
  pose proof (lt_amodel_kept_x B ARx LAWS ly3 S3 Hp3 W mem mdc W2 mem2 m HAR HMOD
     (proj1 ERRNO_LOW) (proj2 ERRNO_LOW) KL) as HMOD2.
  pose proof (lt_ainput_kept_x B ARx LAWS cx ly3 S3 Hp3 W mem mdc W2 mem2 HAR HIN (eq_sym HlenP) KL) as HIN2.
  pose proof (lt_rom_kept W W2 mem mem2 HRV KL) as HRV2.
  pose proof (lt_jt_kept W W2 mem mem2 HROM KL) as HROM2.
  set (nl := c_n cx - lm_k m) in *.
  assert (R144b : sv8 W2 mem2 (lf_F cx + 144) nl).
  { apply (lt_sv8_kept W W2 mem mem2); [|exact R144]. intros x Hx. apply KH. lia. }
  (* the registers check_bounded keeps *)
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r lt_kept -> getr regs2 r = getr regs r)
    by (intros r H1 H2; rewrite (lt_pres (ms_regs ms) regs2 r HP2 H1); exact (KR r H2)).
  assert (H9b : getr regs2 9 = w64 (lf_F cx))
    by (rewrite (RR 9%bv ltac:(lt_cs) ltac:(unfold lt_kept; lt_in)); exact R9).
  assert (Hnl : 0 <= nl <= 2 ^ 26) by (unfold nl; lia).
  destruct (lt_entry2 W2 regs2 mem2 (lf_F cx) nl H9b ltac:(lia) ltac:(lia) Hnl R144b) as [HSb SHOKb].
  (* the two cut points the walk ends at, over the R journal: the shutdown block X after t + 1 operations, and the
     loop head H of operation t + 1 *)
  assert (XFIN : forall c, (exists rf mdf, c = cfg_at segs (fr_B0 + AF_LLVM_exit) rf mem2 mdf /\
      (forall r, In r lt_saved -> getr rf r = getr regs r) /\
      ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp
        (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W2 mem2 mdf k) ->
      INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp W2 c).
  { intros c (rf & mdf & -> & KX & HJf).
    exists rf, mem2, mdf, (t + 1). split; [reflexivity|]. split; [exact HROM2|].
    exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
    split; [exact HJf|]. split; [reflexivity|]. split; [exact (lt_aframe_false _ _ _ _ HFR2)|]. split; [exact HFL2|].
    split; [exact HMOD2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
    split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    unfold lregs_X.
    repeat split;
      first [ match goal with |- getr rf ?r = _ => rewrite (KX r ltac:(unfold lt_saved; lt_in)) end; assumption
            | lia ]. }
  assert (HFIN : forall c, (exists rf mdf, c = cfg_at segs (fr_B0 + AF_LLVM_head) rf mem2 mdf /\
      (forall r, In r lt_saved -> getr rf r = getr regs r) /\
      getr rf 6 = w64 4 /\ getr rf 7 = w64 1 /\ getr rf 21 = w64 nl /\ getr rf 27 = w64 (t + 1) /\
      ajournal_gx_xR segs B PST ARx R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) Hp
        (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 Hp3 W2 mem2 mdf k) ->
      t <= 510 -> nl <> 0 -> INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R cx Hp (t + 1) W2 c).
  { intros c (rf & mdf & -> & KX & Q6 & Q7 & Q21 & Q27 & HJf) Ht Hn.
    assert (Hk1 : lm_k m < c_n cx) by (unfold nl in Hn; lia).
    exists rf, mem2, mdf. split; [reflexivity|]. split; [exact HROM2|].
    exists [(1, fpos)], ly3, S3, Hp3, k, m, fpos.
    split; [exact HJf|]. split; [reflexivity|]. split; [exact HFR2|]. split; [exact HFL2|].
    split; [exact HMOD2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
    split; [exact HLS|]. split; [exact HNP|]. split; [exact HRI|].
    unfold lregs_H, lregs_common.
    repeat split;
      first [ exact Q6 | exact Q7 | exact Q21 | exact Q27
            | match goal with |- getr rf ?r = _ => rewrite (KX r ltac:(unfold lt_saved; lt_in)) end; assumption
            | unfold OPS_MAX in *; lia ]. }
  rewrite Q1.
  change (Z_to_bv 64 (BASE + 8616)) with (Z_to_bv 64 (BASE + AF_LLVM_latch4)).
  remember (Eimg (Ereg regs2 (lt2_extra nl))) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs2 (lt2_extra nl)) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E27 : ew Eb 27 = Z_to_bv 64 t).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs2 _ 27 27%bv eq_refl).
    rewrite (RR 27%bv ltac:(lt_cs) ltac:(unfold lt_kept; lt_in)). exact R27. }
  assert (E32 : ew Eb 32 = Z_to_bv 64 nl)
    by (subst Eb; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
  clear HEb.
  paj_run_tok_x RUNR HSb HJ2 SHOKb LBspan.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  lt_mem HF Em2. clear HF HFr.
  assert (Rt' : 0 <= t < 512) by (unfold OPS_MAX in Rt; exact Rt).
  (* bltu a0(510), s11(t): after operation 511 the loop is left *)
  psrr_branch_tok RUNR BR HSb SHOKb LBspan.
  - assert (Ht511 : t = 511).
    { rewrite branch_ltu_U, (U_lit Eb 510), (U_atom Eb 27 t E27) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
    paj_run_to_tok_x RUNTOR HSb HJ2 SHOKb LBspan AF_LLVM_exit.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    lt_mem HF Em3.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (lt2_extra nl) lt2_kept HSb HAEb
      ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    pmkst HSb.
    rewrite Em3 in *. rewrite Em2 in *.
    apply SRr_ret. right. apply XFIN.
    lazymatch goal with |- exists _ _, {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} = _ /\ _ => exists r, d end.
    split; [reflexivity|]. split; [exact (lt_fin_regs regs regs2 _ KR2 RR)|]. exact HJ2.
  - assert (Ht510 : t <= 510).
    { rewrite branch_ltu_U, (U_lit Eb 510), (U_atom Eb 27 t E27) in Hc by lia. apply Z.ltb_ge in Hc. lia. }
    (* addiw s11,s11,1 *)
    paj_run_tok_x RUNR HSb HJ2 SHOKb LBspan.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    lt_mem HF Em3. clear HF HFr Hc.
    (* bnez s5(in.n): the next operation, or the shutdown *)
    psrr_branch_tok RUNR BR HSb SHOKb LBspan.
    + assert (Hn0 : nl <> 0).
      { rewrite branch_ne_U, (U_atom Eb 32 nl E32), U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
        exact Hc. }
      paj_run_to_tok_x RUNTOR HSb HJ2 SHOKb LBspan AF_LLVM_head.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      lt_mem HF Em4.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (lt2_extra nl) lt2_kept HSb HAEb
        ltac:(vm_compute; reflexivity)) as KR2.
      cbn [ms_regs restrict] in KR2.
      prreg HSb (6%bv : bv 5) Q6. prreg HSb (7%bv : bv 5) Q7. prreg HSb (21%bv : bv 5) Q21.
      lt_prreg_raw HSb (27%bv : bv 5) Q27.
      rewrite ?E32 in Q21.
      rewrite (lt_sv_of_U Eb _ (t + 1) (lt_addiw_U Eb t E27 ltac:(lia)) ltac:(lia)) in Q27.
      pmkst HSb.
      rewrite Em4 in *. rewrite Em3 in *. rewrite Em2 in *.
      apply SRr_ret. left. apply HFIN; [|exact Ht510|exact Hn0].
      lazymatch goal with |- exists _ _, {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} = _ /\ _ => exists r, d end.
      split; [reflexivity|]. split; [exact (lt_fin_regs regs regs2 _ KR2 RR)|].
      split; [exact Q6|]. split; [exact Q7|]. split; [exact Q21|]. split; [exact Q27|]. exact HJ2.
    + (* j 0x84bf8 *)
      paj_run_to_tok_x RUNTOR HSb HJ2 SHOKb LBspan AF_LLVM_exit.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      lt_mem HF Em4.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs2 (lt2_extra nl) lt2_kept HSb HAEb
        ltac:(vm_compute; reflexivity)) as KR2.
      cbn [ms_regs restrict] in KR2.
      pmkst HSb.
      rewrite Em4 in *. rewrite Em3 in *. rewrite Em2 in *.
      apply SRr_ret. right. apply XFIN.
      lazymatch goal with |- exists _ _, {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} = _ /\ _ => exists r, d end.
      split; [reflexivity|]. split; [exact (lt_fin_regs regs regs2 _ KR2 RR)|]. exact HJ2.
Qed.
End wR.
End w.

(* ------------------------------------------------------------------------------------------------
   THE CHECK, in cut_x's scope: Section w of W_LLVMFuzzerTestOneInput_cut_x.v with its Section hypotheses, SEG_LATCH
   restated in its text (cut_x.v:312, the Section-local names applied as cut_x's End w generalizes them) and closed
   by `exact` from lf_seg_latch_x; and the theorem in SEG_LATCH's argument position of cut_x's
   lf_contract_of_segments_x (the other thirteen segments as hypotheses in cut_x's text). *)
Section chk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> world segs -> (word -> option byte) -> alayout -> astate -> world segs ->
  (word -> option byte) -> Prop.
Variable LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis HG : gx_ok segs B G_fr.
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Hypothesis W1_check_bounded : cb_spec_x B PST ARx (BASE + AF_fr_check_bounded).
Hypothesis ERRNO_LOW : 0 <= as_errno B /\ as_errno B + 4 <= CEIL8.
(* cut_x's Section-local names, as its End w generalizes them (the forms top_x.v:92-98 uses) *)
Local Notation BASEx cx Hp := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp).
Local Notation IH := (INV_H_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation ID := (INV_D_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation IA := (INV_A_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation IK := (INV_K_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation IX := (INV_X_x B NP G_fr fr_FP PST ARx LSx RINV).
Local Notation POST := (lf_post_x B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx).
(* cut_x.v:312 SEG_LATCH, its text *)
Lemma lf_seg_latch_x_check : forall cx Hp t W c, BASEx cx Hp -> IK cx Hp t W c ->
  SRr segs W c (fun W' c' => IH cx Hp (t + 1) W' c' \/ IX cx Hp W' c').
Proof.
  exact (lf_seg_latch_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx LAWS HG
           LSx RINV W1_check_bounded ERRNO_LOW).
Qed.
(* cut_x.v:297-319, the other segments *)
Hypothesis SEG_PRO : forall cx Hp, BASEx cx Hp ->
  SRr segs (c_W cx) (lf_entry cx) (fun W' c' => IH cx Hp 0 W' c' \/ IX cx Hp W' c').
Hypothesis SEG_HEAD : forall cx Hp t W c, BASEx cx Hp -> IH cx Hp t W c ->
  SRr segs W c (fun W' c' => (exists op, 0 <= op <= 9 /\ ID cx Hp t op W' c') \/ IA 1 cx Hp t W' c' \/
    IH cx Hp (t + 1) W' c' \/ IX cx Hp W' c').
Hypothesis ARM_add : forall cx Hp t W c, BASEx cx Hp -> IA 0 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Hypothesis ARM_write : forall cx Hp t W c, BASEx cx Hp -> IA 1 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Hypothesis ARM_drain : forall cx Hp t W c, BASEx cx Hp -> IA 2 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Hypothesis ARM_close : forall cx Hp t W c, BASEx cx Hp -> IA 3 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Hypothesis ARM_remove : forall cx Hp t W c, BASEx cx Hp -> IA 4 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Hypothesis ARM_gone : forall cx Hp t W c, BASEx cx Hp -> IA 5 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Hypothesis ARM_eintr : forall cx Hp t W c, BASEx cx Hp -> IA 6 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Hypothesis ARM_event : forall cx Hp t W c, BASEx cx Hp -> IA 7 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Hypothesis ARM_sendmax : forall cx Hp t W c, BASEx cx Hp -> IA 8 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Hypothesis ARM_default : forall cx Hp t W c, BASEx cx Hp -> IA 9 cx Hp t W c -> SRr segs W c (IK cx Hp t).
Hypothesis SEG_EXIT : forall cx Hp W c, BASEx cx Hp -> IX cx Hp W c -> SRr segs W c (POST cx Hp).
Lemma lf_seg_latch_x_plugs :
  @fr_lib_contract_cf_x fx rc checksum_shape B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr
    fr_FP PST ARx.
Proof.
  exact (lf_contract_of_segments_x B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST
    ARx LAWS HG LSx RINV SEG_PRO SEG_HEAD ARM_add ARM_write ARM_drain ARM_close ARM_remove ARM_gone ARM_eintr
    ARM_event ARM_sendmax ARM_default lf_seg_latch_x_check SEG_EXIT).
Qed.
(* ---- route R: lib/A/W_LLVMFuzzerTestOneInput_cut_x.v:466 SEG_LATCH_R restated in its text at a world relation R (cut_x Section wR's Section-local
   names, as its End w generalizes them: the forms lib/A/W_LLVMFuzzerTestOneInput_top_x.v Section topxR uses), closed by `exact` from lf_seg_latch_xR;
   and the theorem in SEG_LATCH_R's argument position of cut_x's lf_contract_of_segments_xR (the other thirteen steps
   as hypotheses in cut_x.v:451-473's text; SEG_JT is walked inside cut_x). *)
Section chkR.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Local Notation IHR := (INV_H_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation IDR := (INV_D_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation IAR := (INV_A_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation IKR := (INV_K_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation IXR := (INV_X_xR B NP G_fr fr_FP PST ARx LSx RINV R).
Local Notation POSTR := (lf_post_xR B MT XN_LIB fr_live_post fr_surv NP G_fr fr_FP PST ARx R).
(* lib/A/W_LLVMFuzzerTestOneInput_cut_x.v:466 SEG_LATCH_R, its text *)
Lemma lf_seg_latch_xR_check : forall cx Hp t W c, BASEx cx Hp -> IKR cx Hp t W c ->
  SRrG segs R W c (fun W' c' => IHR cx Hp (t + 1) W' c' \/ IXR cx Hp W' c').
Proof.
  exact (lf_seg_latch_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST ARx LAWS
           HG LSx RINV W1_check_bounded ERRNO_LOW R R_refl R_trans WLE_R).
Qed.
(* cut_x.v:451-473, the other steps at R *)
Hypothesis SEG_PRO_R : forall cx Hp, BASEx cx Hp ->
  SRrG segs R (c_W cx) (lf_entry cx) (fun W' c' => IHR cx Hp 0 W' c' \/ IXR cx Hp W' c').
Hypothesis SEG_HEAD_R : forall cx Hp t W c, BASEx cx Hp -> IHR cx Hp t W c ->
  SRrG segs R W c (fun W' c' => (exists op, 0 <= op <= 9 /\ IDR cx Hp t op W' c') \/ IAR 1 cx Hp t W' c' \/
    IHR cx Hp (t + 1) W' c' \/ IXR cx Hp W' c').
Hypothesis ARM_add_R : forall cx Hp t W c, BASEx cx Hp -> IAR 0 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Hypothesis ARM_write_R : forall cx Hp t W c, BASEx cx Hp -> IAR 1 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Hypothesis ARM_drain_R : forall cx Hp t W c, BASEx cx Hp -> IAR 2 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Hypothesis ARM_close_R : forall cx Hp t W c, BASEx cx Hp -> IAR 3 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Hypothesis ARM_remove_R : forall cx Hp t W c, BASEx cx Hp -> IAR 4 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Hypothesis ARM_gone_R : forall cx Hp t W c, BASEx cx Hp -> IAR 5 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Hypothesis ARM_eintr_R : forall cx Hp t W c, BASEx cx Hp -> IAR 6 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Hypothesis ARM_event_R : forall cx Hp t W c, BASEx cx Hp -> IAR 7 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Hypothesis ARM_sendmax_R : forall cx Hp t W c, BASEx cx Hp -> IAR 8 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Hypothesis ARM_default_R : forall cx Hp t W c, BASEx cx Hp -> IAR 9 cx Hp t W c -> SRrG segs R W c (IKR cx Hp t).
Hypothesis SEG_EXIT_R : forall cx Hp W c, BASEx cx Hp -> IXR cx Hp W c -> SRrG segs R W c (POSTR cx Hp).
Lemma lf_seg_latch_xR_plugs :
  @fr_lib_contract_cf_xR fx rc checksum_shape B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP
    G_fr fr_FP PST ARx R.
Proof.
  exact (lf_contract_of_segments_xR B MT XM_LIB XN_LIB RLO RHI fr_live_pre fr_live_post fr_surv LIBROOM NP G_fr fr_FP PST
    ARx LAWS HG LSx RINV R R_refl R_trans WLE_R SEG_PRO_R SEG_HEAD_R ARM_add_R ARM_write_R ARM_drain_R ARM_close_R
    ARM_remove_R ARM_gone_R ARM_eintr_R ARM_event_R ARM_sendmax_R ARM_default_R lf_seg_latch_xR_check SEG_EXIT_R).
Qed.
End chkR.
End chk.
