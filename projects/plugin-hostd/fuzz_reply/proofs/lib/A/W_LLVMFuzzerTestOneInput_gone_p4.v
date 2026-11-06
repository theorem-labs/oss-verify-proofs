(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput
   (fuzz_reply.asan 0x845e4-0x84610 and 0x846e0-0x84980, fuzz_reply.c:633-655 and :718-720), in the form of the cgif
   entry walk's arms (proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v: a segment is an SRr from one cut point's invariant to
   the next) over the cut invariants of W_LLVMFuzzerTestOneInput_cut.v.
   PHASE p4 of the arm (W_LLVMFuzzerTestOneInput_gone.v GP4): GC1 q -> GT0, 0x84848 -> 0x84864, the check_no_loss_read
   loop of fuzz_reply.c:643-645 `for (k...) if (reads[k]) check_no_loss_read(&g_s[k])`:
     0x84848 lw a0,0(s4); 0x8484c beqz a0,84858; 0x84850 mv a0,s5; 0x84854 jal check_no_loss_read;
     0x84858 addi s4,s4,4; 0x8485c addi s5,s5,96; 0x84860 bne s4,s6,84848.
   The loop is gp4_loopX, by induction on the slots left: one trip is gp4_head (0x84848 -> 0x84858, the call or not)
   and gp4_tail (0x84858 -> 0x84848 or 0x84864).  check_no_loss_read is taken by W3's contract (W_contract.v:483
   cnlr_spec on the W8 lane head a3c72093c22: Section hypothesis CNLR), whose post aleaf_post keeps the donor
   journal's bytes, presence and errno's view; the loop's post keeps those bytes (gp4_kcls, gp4_keep), and gp4_c1_t0
   carries GC1's facts to GT0 with it (the model's cells through GN_HGcells, the read-only image through
   GN_ROM_PIN). *)
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
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the transport kit.  The blocks a representation names are live (the blocks halves of
   W_LLVMFuzzerTestOneInput_latch.v lt_alist / lt_asrc / lt_aentry / lt_arelay / lt_aout); every byte a
   representation reads lies in one of its cells or one of its blocks (lib/A/W_LLVMFuzzerTestOneInput_gone_p5.v
   Section cov, copied gp5_ -> gp4k_: the p5 lane owns that file, so it is not imported); and the model is kept when
   its blocks, its cells (the base's gn_cells) and errno are ---- *)
Ltac gp4k_inl := cbn [In gn_cells]; repeat (first [left; reflexivity | right]).
Section gp4k_kit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.

(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_bzs_len *)
Lemma gp4k_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_text_rec_len *)
Lemma gp4k_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_concat_len *)
Lemma gp4k_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, gp4k_text_rec_len, IH. cbn [length]. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_key_ptrs_len *)
Lemma gp4k_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.

(* ---- the blocks a representation names are live ---- *)
Lemma gp4k_alist_blks : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). rewrite Forall_forall in H9.
  unfold alist_blks. intros b Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
  - apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)).
Qed.
Lemma gp4k_asrc_blks : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h HS.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ &
                    _ & Hexp & Hheld & _).
  pose proof (gp4k_alist_blks ly S W mem (HA + 16) (hs_pending h) false Hpend) as A2.
  pose proof (gp4k_alist_blks ly S W mem (HA + 64) (hs_expected h) true Hexp) as E2.
  pose proof (gp4k_alist_blks ly S W mem (HA + 80) (hs_held h) true Hheld) as H2.
  unfold asrc_blks. intros b [<- | Hb]; [exact Hpb|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.
Lemma gp4k_aentry_blks : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  rewrite Forall_forall in K15.
  unfold aentry_blks. intros b Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
    destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
  - apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)).
Qed.
Lemma gp4k_arelay_blks : forall RG ly S (W : world segs) mem G es,
  arelay_at B RG ly S W mem G es -> forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros RG ly S W mem G es (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11). rewrite Forall_forall in R10.
  unfold arelay_blks. intros b [<- | Hb]; [exact R8|].
  apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
  exact (gp4k_aentry_blks ly S W mem e (R10 e He) b Hb).
Qed.
Lemma gp4k_aout_blks : forall RG ly S (W : world segs) mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
  intros RG ly S W mem c O mx no cap out HO.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_blks. intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
  destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- every byte a representation reads lies in one of its cells or one of its blocks (p5's Section cov) ---- *)
Section cov.
Variable KEEP : Z -> Prop.
Definition gp4k_bkeep (bl : list (Z * Z)) : Prop :=
  forall p n i, In (p, n) bl -> 0 <= i < req_size n -> KEEP (p + i).
Definition gp4k_fkeep (fp : list (Z * Z)) : Prop := forall r, In r fp -> forall a, fst r <= a < snd r -> KEEP a.
Lemma gp4k_bkeep_sub : forall bl bl', gp4k_bkeep bl -> (forall b, In b bl' -> In b bl) -> gp4k_bkeep bl'.
Proof. intros bl bl' H Hs p n i Hin Hi. exact (H p n i (Hs _ Hin) Hi). Qed.
Lemma gp4k_brng : forall bl p n a, gp4k_bkeep bl -> In (p, n) bl -> 0 <= n -> p <= a < p + n -> KEEP a.
Proof.
  intros bl p n a H Hin Hn Ha. pose proof (req_size_pos n Hn) as [_ Hr].
  replace a with (p + (a - p)) by lia. apply (H p n); [exact Hin | lia].
Qed.
Lemma gp4k_alist_cov : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> (forall a, LA <= a < LA + 16 -> KEEP a) -> gp4k_bkeep (alist_blks l) ->
  gp4k_fkeep (alist_fp LA l).
Proof.
  intros ly S W mem LA l lines (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL HB r Hr a Ha.
  unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [cbn in Ha; apply HL; lia|].
  apply in_app_or in Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hr|].
    destruct Hr as [<- | []]. destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    cbn [gfp fst snd] in Ha. rewrite gp4k_bzs_len, length_app, gp4k_concat_len in Ha. unfold hl_n in Hj.
    apply (gp4k_brng (alist_blks l) (hl_v l) (AREC * hl_cap l)); [exact HB | | unfold AREC; lia | unfold AREC in *; lia].
    unfold alist_blks. apply in_or_app. left. destruct (Z.eqb_spec (hl_cap l) 0); [lia | left; reflexivity].
  - apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd] in Ha. rewrite gp4k_bzs_len, length_app in Ha.
    cbn [length] in Ha.
    apply (gp4k_brng (alist_blks l) (fst x) (Z.of_nat (length (snd x)) + 1)); [exact HB | | lia | lia].
    unfold alist_blks. apply in_or_app. right. apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))). exact Hx.
Qed.
Lemma gp4k_asrc_cov : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> (forall a, HA <= a < HA + ASRC -> KEEP a) -> gp4k_bkeep (asrc_blks h) ->
  gp4k_fkeep (asrc_fp HA h).
Proof.
  intros ly S W mem HA h HS HL HB.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  intros r Hr a Ha. unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
  - apply HL. cbn in Ha. lia.
  - cbn [gfp fst snd] in Ha. rewrite gp4k_bzs_len, Hpj in Ha.
    apply (gp4k_brng (asrc_blks h) (hs_partial h) APARTIAL); [exact HB | left; reflexivity | unfold APARTIAL; lia | lia].
  - apply in_app_or in Hr as [Hr | Hr]; [|apply in_app_or in Hr as [Hr | Hr]].
    + refine (gp4k_alist_cov ly S W mem (HA + 16) _ _ Hpend _ _ r Hr a Ha);
        [intros x Hx; apply HL; unfold ASRC; lia |].
      apply (gp4k_bkeep_sub _ _ HB). intros b Hb. right. apply in_or_app. left. exact Hb.
    + refine (gp4k_alist_cov ly S W mem (HA + 64) _ _ Hexp _ _ r Hr a Ha);
        [intros x Hx; apply HL; unfold ASRC; lia |].
      apply (gp4k_bkeep_sub _ _ HB). intros b Hb. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
    + refine (gp4k_alist_cov ly S W mem (HA + 80) _ _ Hheld _ _ r Hr a Ha);
        [intros x Hx; apply HL; unfold ASRC; lia |].
      apply (gp4k_bkeep_sub _ _ HB). intros b Hb. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma gp4k_aentry_cov : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> gp4k_bkeep (aentry_blks e) -> gp4k_fkeep (aentry_fp e).
Proof.
  intros ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15) HB r Hr a Ha.
  unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
  - destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|]. destruct Hr as [<- | []].
    destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
    cbn [gfp fst snd] in Ha. rewrite gp4k_bzs_len, length_app in Ha.
    apply (gp4k_brng (aentry_blks e) (re_buf e) (re_cap e)); [exact HB | | lia | lia].
    unfold aentry_blks. apply in_or_app. left. destruct (Z.eqb_spec (re_cap e) 0); [lia | left; reflexivity].
  - destruct Hr as [<- | Hr].
    + cbn [gfp fst snd] in Ha. rewrite gp4k_bzs_len, gp4k_key_ptrs_len in Ha.
      destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      * rewrite Hks in Ha. cbn [length] in Ha. lia.
      * unfold re_nheld in Hk1.
        apply (gp4k_brng (aentry_blks e) (re_hp e) (re_kh e)); [exact HB | | lia | lia].
        unfold aentry_blks. apply in_or_app. right. apply in_or_app. left.
        destruct (Z.eqb_spec (re_hp e) 0); [lia | left; reflexivity].
    + apply in_map_iff in Hr as (x & <- & Hx). cbn [gfp fst snd] in Ha. rewrite gp4k_bzs_len, length_app in Ha.
      cbn [length] in Ha.
      apply (gp4k_brng (aentry_blks e) (gestures_end_b_c.key_addr x)
        (Z.of_nat (length (gestures_end_b_c.key_text x)) + 1)); [exact HB | | lia | lia].
      unfold aentry_blks. apply in_or_app. right. apply in_or_app. right.
      apply (in_map (fun k => (gestures_end_b_c.key_addr k, Z.of_nat (length (gestures_end_b_c.key_text k)) + 1))).
      exact Hx.
Qed.
Lemma gp4k_arelay_cov : forall RG ly S (W : world segs) mem G es,
  arelay_at B RG ly S W mem G es ->
  (forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4 ->
     KEEP a) ->
  gp4k_bkeep (arelay_blks G es) -> gp4k_fkeep (arelay_fp RG G es).
Proof.
  intros RG ly S W mem G es (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) HC HB r Hr a Ha.
  unfold arelay_fp in Hr. destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
  - apply HC. lia.
  - apply HC. lia.
  - apply HC. lia.
  - apply (gp4k_brng (arelay_blks G es) G ATABLE); [exact HB | left; reflexivity | unfold ATABLE; lia | lia].
  - apply in_concat in Hr as (f & Hf & Hr). apply in_map_iff in Hf as (e & <- & He).
    rewrite Forall_forall in R10.
    refine (gp4k_aentry_cov ly S W mem e (R10 e He) _ r Hr a Ha).
    apply (gp4k_bkeep_sub _ _ HB). intros b Hb. right. apply in_concat. exists (aentry_blks e).
    split; [apply in_map; exact He | exact Hb].
Qed.
Lemma gp4k_aout_cov : forall RG ly S (W : world segs) mem c O mx no cap out,
  aout_at B RG ly S W mem c O mx no cap out ->
  (forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> KEEP a) ->
  gp4k_bkeep (aout_blks cap out) -> gp4k_fkeep (aout_fp B RG cap out).
Proof.
  intros RG ly S W mem c O mx no cap out HO HC HB r Hr a Ha.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp in Hr.
  do 9 (destruct Hr as [<- | Hr];
    [refine (HC _ a _ Ha); unfold aout_fp; cbn [In]; repeat (first [left; reflexivity | right]) |]).
  destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  apply (gp4k_brng (aout_blks cap out) out cap); [exact HB | | lia | lia].
  unfold aout_blks. destruct (Z.eqb_spec cap 0); [lia | left; reflexivity].
Qed.
End cov.

(* a byte of one of the model's cells (p5's gp5_cell) *)
Lemma gp4k_cell : forall lo n a, In (lo, n) gn_cells -> lo <= a < lo + n -> inG gn_cells a.
Proof. intros lo n a Hin Ha. unfold inG. apply Exists_exists. exists (lo, n). split; [exact Hin | unfold in_zr; cbn; lia]. Qed.
(* the model, kept when its blocks, its cells and errno are (in place of W_LLVMFuzzerTestOneInput_latch.v
   lt_amodel_kept, which took every byte below alloc_ceiling + 8) *)
Lemma gp4k_amodel_kept : forall ly S (W : world segs) mem (W' : world segs) mem' m,
  amodel_at B ly S W mem m ->
  (forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> abyte_kept W mem W' mem' (p + i)) ->
  (forall a, inG gn_cells a -> abyte_kept W mem W' mem' a) ->
  (forall i, 0 <= i < 4 -> abyte_kept W mem W' mem' (as_errno B + i)) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem W' mem' m (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) KB KC KE.
  assert (KBk : forall bl, (forall b, In b bl -> In b (ablocks B ly S)) -> gp4k_bkeep (abyte_kept W mem W' mem') bl)
    by (intros bl Hbl p n i Hin Hi; exact (KB p n i (Hbl _ Hin) Hi)).
  assert (K1 : forall lo n x, In (lo, n) gn_cells -> lo <= x < lo + n -> abyte_kept W mem W' mem' x)
    by (intros lo n x Hin Hx; apply KC; exact (gp4k_cell lo n x Hin Hx)).
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (KS : forall x, rg_s fr_RG + ASRC * Z.of_nat i <= x < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
        abyte_kept W mem W' mem' x)
      by (intros x Hx; apply (K1 (rg_s fr_RG) (4 * ASRC)); [gp4k_inl | unfold ASRC in *; lia]).
    destruct (nth i (lm_hs m) None) as [h|].
    - pose proof (gp4k_asrc_blks ly S W mem _ h M2) as F2.
      apply (asrc_at_kept B ly S W mem ly S W' mem' _ h M2); [|exact F2].
      exact (gp4k_asrc_cov (abyte_kept W mem W' mem') ly S W mem _ h M2 KS (KBk _ F2)).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx. apply KS. unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. exact KS. }
  split.
  { pose proof (gp4k_arelay_blks _ ly S W mem (lm_G m) (lm_es m) M3) as F2.
    apply (arelay_at_kept B fr_RG ly S W mem ly S W' mem' _ _ M3); [|exact F2].
    apply (gp4k_arelay_cov (abyte_kept W mem W' mem') fr_RG ly S W mem _ _ M3); [|exact (KBk _ F2)].
    intros a Ha. destruct Ha as [Ha | [Ha | Ha]]; refine (K1 _ _ a _ Ha); gp4k_inl. }
  split.
  { pose proof (gp4k_aout_blks _ ly S W mem _ _ _ _ _ _ M4) as F2.
    apply (aout_at_kept B fr_RG ly S W mem ly S W' mem' _ _ _ _ _ _ M4); [|exact F2].
    apply (gp4k_aout_cov (abyte_kept W mem W' mem') fr_RG ly S W mem _ _ _ _ _ _ M4); [|exact (KBk _ F2)].
    intros r a Hr Ha. unfold aout_fp in Hr. cbn [Z.eqb] in Hr.
    do 8 (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; refine (K1 _ _ a _ Ha); gp4k_inl |]).
    destruct Hr as [<- | []]. cbn [fst snd] in Ha. replace a with (as_errno B + (a - as_errno B)) by lia.
    apply KE. lia. }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' _ M5). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (K1 (rg_gone fr_RG) 1); [gp4k_inl | lia]. }
  split.
  { apply (alock_at_kept fr_RG W mem W' mem' _ M6). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (K1 (rg_lock fr_RG) 12); [gp4k_inl | lia]. }
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (K1 (rg_wake fr_RG + 4) 4); [gp4k_inl | lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply (K1 AG_NFD 4); [gp4k_inl | lia]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply (K1 AG_NFD 4); [gp4k_inl | lia]. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply (K1 AG_THREAD_UP 1); [gp4k_inl | lia]. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply (K1 AG_LISTEN 4); [gp4k_inl | lia]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply (K1 AG_LISTEN 4); [gp4k_inl | lia].
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_sv8_kept *)
Lemma gp4k_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
(* writability survives a step that keeps presence and hides no more (copied from W_list_drop.v writable_kept_w) *)
Lemma gp4k_wr_kept : forall (W W' : world segs) (m m' : word -> option byte) a,
  (apresent (w_H W) m a -> apresent (w_H W') m' a) -> wle W W' ->
  writable_at segs (mrestrict (w_H W) m) a -> writable_at segs (mrestrict (w_H W') m') a.
Proof.
  intros W W' m m' a Hp Hh Hw. unfold writable_at, wview, mrestrict in Hw |- *.
  destruct (w_H W' (Z_to_bv 64 a)) eqn:EH'.
  - rewrite (Hh _ EH') in Hw. exact Hw.
  - destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
    + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
    + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
      * destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
      * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* the jump table lies in the read-only image (p5's gp5_inromb / gp5_jt_in_rom) *)
Definition gp4k_inromb (a : Z) : bool :=
  existsb (fun sg => (negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
                      (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool) segs.
Lemma gp4k_inromb_ok : forall a, gp4k_inromb a = true -> in_rom segs a.
Proof.
  intros a H. unfold gp4k_inromb in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.
Lemma gp4k_jt_in_rom : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Proof.
  intros a Ha. apply gp4k_inromb_ok.
  assert (K : forallb (fun i => gp4k_inromb (fr_jtab + Z.of_nat i)) (seq 0 36) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in K. replace a with (fr_jtab + Z.of_nat (Z.to_nat (a - fr_jtab))) by lia.
  apply K. apply in_seq. lia.
Qed.
End gp4k_kit.

(* ================================================================== phase p4 *)
Section gp4.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* g_s lies in the instance's zero-shadow ranges: check_no_loss_read's shadow check of &g_s[k] *)
Hypothesis HZS : GN_HZS B.
(* the slots the loop calls check_no_loss_read on have no pending record (relay_instance_gone drained them) *)
Hypothesis RIR : GN_RI_read RINV.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* check_no_loss_read (0x85904): W_contract.v cnlr_spec (:454) on the W8 lane head a3c72093c22, verbatim
   (lf_arm_gone's CNLR; _remove.v:405 takes the same text) *)
Hypothesis CNLR : cnlr_spec B (BASE + AF_fr_check_no_loss_read).
(* what carries the model and the read-only image across that call, as p5 takes them (base :687-709): the model's
   cells are bytes of G_fr, so by gx_ok image bytes that are no allocator static, which check_no_loss_read's journal
   keeps (Reusable/YCbq.v:363); and the allocator's own read-only bytes are pinned in every AR state *)
Hypothesis HGcells : GN_HGcells G_fr.
Hypothesis HROMPIN : GN_ROM_PIN B.
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

Definition AF_gp4_mid : Z := 0x256c.    (* 0x84858: after the call (or its skip) *)
(* the callee-saved registers; and those of them the tail keeps (all but s4, s5) *)
Definition GP4_CS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition GP4_K2 : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 26; 27]%bv.
Definition gp4_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* 0x84848: the cell reads[q] at s4, its value the extra atom 32 *)
Definition gp4_c1_region : YP09.region := YP09.mkRegion (Some 20%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition gp4_c1_facts : facts := mkFacts [ (32%nat, mkAF 0 1 0); (33%nat, mkAF SB SB 0) ] [] [].
Definition ss_gp4_c1 : sstate := mkSS AF_gn_c1 sr_atoms [gp4_c1_region] None gp4_c1_facts.
Definition gp4_c1_Bx : sv := SOff 33 0.
Definition gp4_c1_extra (rd : Z) : list word := map (Z_to_bv 64) [rd; SB].
(* 0x84858: no memory read *)
Definition gp4_md_facts : facts := mkFacts [ (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_gp4_md : sstate := mkSS AF_gp4_mid sr_atoms [] None gp4_md_facts.
Definition gp4_md_Bx : sv := SOff 32 0.
Definition gp4_md_extra : list word := map (Z_to_bv 64) [SB].

(* the walk's facts, by name *)
Definition gp4_jr (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk.
(* the bytes check_no_loss_read's post keeps at its call sp = s1 (aleaf_post, W_contract.v:128: the donor journal's
   view clauses, Reusable/YCbq.v:359-367, and errno's view): the stack from alloc_ceiling up but the callee's 16-byte
   frame below s1, every live block, the image bytes that are no allocator static, errno, and every frame of S with
   its shadow *)
Definition gp4_kcls (cx : lfcx) (ly : alayout) (S : astate) (a : Z) : Prop :=
  (alloc_ceiling <= a < 2 ^ 64 /\ ~ (lf_F cx - 16 <= a < lf_F cx)) \/
  (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
  (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B)) \/
  (as_errno B <= a < as_errno B + 4) \/
  (exists cid pos, In (cid, pos) (frames S) /\
     (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8))).
Definition gp4_keep (cx : lfcx) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
    (W' : world segs) (mem' : word -> option byte) : Prop :=
  forall a, gp4_kcls cx ly S a -> abyte_kept W mem W' mem' a.
Definition gp4_saved (cx : lfcx) (W : world segs) (mem : word -> option byte) : Prop :=
  forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r))).
(* g_s[j].pending.n, as check_no_loss_read's functional premise takes it *)
Definition gp4_vok (W : world segs) (mem : word -> option byte) (j : nat) : Prop :=
  exists v, val_mem segs (mrestrict (w_H W) mem) (rg_s fr_RG + ASRC * Z.of_nat j + 24) 4 v /\
    0 <= v < 2 ^ 32 /\ (v = 0 \/ 2 ^ 31 <= v).
(* the cells reads[j] the loop has still to read, and the slot behind each set one *)
Definition gp4_cells (cx : lfcx) (W : world segs) (mem : word -> option byte) (q : nat) : Prop :=
  forall j, (q <= j < 4)%nat -> exists rd, gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) rd /\
    (rd = 0 \/ (rd = 1 /\ gp4_vok W mem j)).

(* ---- small facts ---- *)
Lemma gp4_abk_refl : forall (W : world segs) mem a, abyte_kept W mem W mem a.
Proof. intros W mem a. split; [reflexivity | intros H; exact H]. Qed.
Lemma gp4_abk_trans : forall (W1 W2 W3 : world segs) m1 m2 m3 a,
  abyte_kept W1 m1 W2 m2 a -> abyte_kept W2 m2 W3 m3 a -> abyte_kept W1 m1 W3 m3 a.
Proof. intros W1 W2 W3 m1 m2 m3 a [A1 A2] [B1 B2]. split; [rewrite B1; exact A1 | intros H; exact (B2 (A2 H))]. Qed.
Lemma gp4_keep_trans : forall cx ly S (W1 W2 W3 : world segs) m1 m2 m3,
  gp4_keep cx ly S W1 m1 W2 m2 -> gp4_keep cx ly S W2 m2 W3 m3 -> gp4_keep cx ly S W1 m1 W3 m3.
Proof. intros cx ly S W1 W2 W3 m1 m2 m3 K1 K2 a Ha. exact (gp4_abk_trans _ _ _ _ _ _ a (K1 a Ha) (K2 a Ha)). Qed.
(* a byte of the model's cells is one of the kept image bytes (GN_HGcells, gx_ok) *)
Lemma gp4_cls_cell : forall cx ly S a, inG gn_cells a -> gp4_kcls cx ly S a.
Proof. intros cx ly S a Ha. right; right; left. exact (conj (proj1 (HG a (HGcells a Ha))) (proj1 (proj2 (HG a (HGcells a Ha))))). Qed.
(* copied from W_LLVMFuzzerTestOneInput_small.v azs_sub *)
Lemma gp4_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof.
  intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|].
  split; [exact H8|]. split; lia.
Qed.
Lemma gp4_reads01 : forall m j, gn_reads m j = 0 \/ gn_reads m j = 1.
Proof.
  intros m j. unfold gn_reads. destruct (nth j (lm_hs m) None) as [h|]; [|left; reflexivity].
  destruct (gn_src m (hs_fd h)) as [i|]; [|left; reflexivity].
  destruct (_ =? 0); [right | left]; reflexivity.
Qed.
(* a closed slot is 96 zero bytes: its pending.n reads 0 *)
Lemma gp4_zero4 : forall (mm : word -> option byte) a o,
  garr8 segs mm a (repeat 0 (Z.to_nat ASRC)) -> 0 <= o -> o + 4 <= ASRC -> val_mem segs mm (a + o) 4 0.
Proof.
  intros mm a o HZ Ho1 Ho2 k Hk.
  assert (Hj : (Z.to_nat o + k < length (repeat 0 (Z.to_nat ASRC)))%nat) by (rewrite repeat_length; unfold ASRC in *; lia).
  pose proof (garr8_mbyte segs mm a _ _ HZ Hj) as Hb. rewrite nth_repeat in Hb.
  replace (a + Z.of_nat (Z.to_nat o + k)) with (a + o + Z.of_nat k) in Hb by lia.
  rewrite Hb. f_equal.
  destruct k as [|[|[|[|k]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
Qed.
(* a callee-saved register across the call (W_LLVMFuzzerTestOneInput_latch.v lt_pres) *)
Lemma gp4_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma gp4_cs_pres : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r, In r GP4_CS -> getr regs' r = getr regs r.
Proof.
  intros regs regs' HP r Hr. apply gp4_pres; [exact HP|]. unfold GP4_CS in Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?r] =>
       let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia |]).
  destruct Hr.
Qed.
Lemma gp4_k2_cs : forall r, In r GP4_K2 -> In r GP4_CS.
Proof.
  intros r Hr. unfold GP4_K2 in Hr. unfold GP4_CS. cbn [In] in Hr |- *.
  repeat (destruct Hr as [<- | Hr]; [repeat (first [left; reflexivity | right]) |]). destruct Hr.
Qed.
Ltac gp4_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* a run over read-only regions leaves the memory as it was *)
Ltac gp4_mem HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.

(* ---- the frame, the fake frame (shadow sh) and the prefix, kept (W_LLVMFuzzerTestOneInput_latch.v lt_aframe_kept,
   over the base's gframe) ---- *)
Lemma gp4_gframe_kept : forall cx sh FF (W W' : world segs) mem mem',
  gframe cx sh FF W mem -> length sh = 16%nat ->
  (forall a, FF <= a < FF + 128 \/ SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  (forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a) ->
  lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  gframe cx sh FF W' mem'.
Proof.
  intros cx sh FF W W' mem mem' HFR Hlen KF KH HF1 HF2.
  unfold gframe in *. cbv zeta in *.
  destruct HFR as (A1 & REST).
  split.
  { intros o r Hin. apply (gp4k_sv8_kept W W' mem mem'); [|exact (A1 o r Hin)].
    intros x Hx. apply KH.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
    lia. }
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with
  | |- _ /\ _ => split
  | |- sv8 W' mem' _ _ =>
      apply (gp4k_sv8_kept W W' mem mem'); [intros x Hx; first [apply KH; lia | apply KF; lia] | assumption]
  | |- awr W' mem' _ _ =>
      apply (akept_awr W mem); [intros x Hx; first [apply KH; lia | apply KF; lia] | assumption]
  | |- garr8 _ _ _ _ =>
      apply (akept_garr8 W mem); [intros x Hx; rewrite Hlen in Hx; cbn in Hx; apply KF; lia | assumption]
  end.
Qed.
Lemma gp4_prefix_kept : forall cx m (W W' : world segs) mem mem' FF,
  gn_prefix_at cx m W mem FF -> (forall a, FF + 32 <= a < FF + 80 -> abyte_kept W mem W' mem' a) ->
  gn_prefix_at cx m W' mem' FF.
Proof.
  intros cx m W W' mem mem' FF (P1 & P2 & P3 & P4 & P5) HK.
  split; [intros i Hi; rewrite (proj1 (HK (FF + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
  split; [rewrite (proj1 (HK (FF + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia))); exact P2|].
  split; [intros a Ha; rewrite (proj1 (HK a Ha)); exact (P3 a Ha)|].
  split; [exact P4 | exact P5].
Qed.

(* ---- check_no_loss_read's afn_pre at sp = F: W_LLVMFuzzerTestOneInput_latch.v lt_afn_pre_at, with the saved
   registers of the frame in place of aframe_at (the only conjunct of it that lemma reads) ---- *)
Lemma gp4_afn_pre_at : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  gp4_jr cx fpos ly3 S3 W mem md k -> gp4_saved cx W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  unfold gp4_jr in HJ. unfold gp4_saved in HSV.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
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
  - pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
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
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

(* ---- the entry states of the two runs ---- *)
Lemma gp4_entry_c1 : forall (W : world segs) regs mem a rd,
  getr regs 20 = w64 a -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  0 <= rd <= 1 -> val_mem segs (mrestrict (w_H W) mem) a 4 rd ->
  st_ok_pi segs VAL (Eimg (Ereg regs (gp4_c1_extra rd))) ss_gp4_c1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_c1)) mem (seg_rom segs)))
  /\ sh_ok segs gp4_c1_Bx [] (Eimg (Ereg regs (gp4_c1_extra rd))) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem a rd H20 Ha0 Ha1 Hrd HV. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (gp4_c1_extra rd))).
  assert (E20 : ew E 20 = Z_to_bv 64 a)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E32 : ew E 32 = Z_to_bv 64 rd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (VB20 : base_val E (Some 20%nat) = a) by (cbn [base_val]; rewrite E20; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gp4_c1. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, gp4_c1_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite VB20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ a 0 4 (SOff 32 0) rd);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact HV].
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [gp4_c1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, E33, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
Lemma gp4_entry_md : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (Ereg regs gp4_md_extra)) ss_gp4_md
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gp4_mid)) mem (seg_rom segs)))
  /\ sh_ok segs gp4_md_Bx [] (Eimg (Ereg regs gp4_md_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs gp4_md_extra)).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - unfold ss_gp4_md. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_nil.
    + cbn. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [gp4_md_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.

(* ---- 0x84848 -> 0x84858: reads[q], and check_no_loss_read(&g_s[q]) when it is set ---- *)
Definition gp4_head_post (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gp4_mid) regs' mem' md' /\
    gp4_jr cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_CS -> getr regs' r = getr regs r) /\
    gp4_keep cx ly S W mem W' mem'.
Lemma gp4_head : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat) rd,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  gp4_jr cx fpos ly S W mem md kk -> gp4_saved cx W mem -> (q < 4)%nat ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) -> getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat q) rd -> (rd = 0 \/ (rd = 1 /\ gp4_vok W mem q)) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_head_post cx fpos ly S W regs mem).
Proof.
  intros cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R20 R21 HRD Hrd.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx _ ly S W mem md kk fpos HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (Hrd01 : 0 <= rd <= 1) by (destruct Hrd as [-> | (-> & _)]; lia).
  unfold gp4_jr in HJ.
  destruct (gp4_entry_c1 W regs mem (lf_F cx + 192 + 4 * Z.of_nat q) rd R20 ltac:(unfold LLVMF_STK in *; lia) ltac:(unfold LLVMF_STK in *; lia)
    Hrd01 HRD) as [HS SHOK].
  remember (Eimg (Ereg regs (gp4_c1_extra rd))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (gp4_c1_extra rd)) E)
    by (rewrite HE; split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 rd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_c1)) with (Z_to_bv 64 (BASE + AF_gn_c1)).
  paj_run_tok RUN HS HJ SHOK gp4_Bspan.
  { apply awr_ok_x_cons; [intros x Hx; cbn in Hx; lia | apply awr_ok_x_nil]. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp4_Bspan.
  - (* reads[q] = 0: no call *)
    paj_run_to_tok RUNTO HS HJ SHOK gp4_Bspan AF_gp4_mid.
    { apply awr_ok_x_cons; [intros x Hx; cbn in Hx; lia | apply awr_ok_x_nil]. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_CS HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_head_post.
    lazymatch goal with |- exists _ _ _ _, {| cfg_ms := mkst ?r _ ?mm _; cfg_model := ?d |} = _ /\ _ =>
      exists r, mm, d, kk end.
    split; [reflexivity|]. split; [exact HJ|]. split; [exact KR|].
    intros x _. apply gp4_abk_refl.
  - (* reads[q] = 1: check_no_loss_read(&g_s[q]) *)
    assert (Hrd1 : rd = 1 /\ gp4_vok W mem q).
    { destruct Hrd as [-> | H]; [|exact H]. exfalso.
      rewrite branch_eq_U, (U_atom E 32 0 E32), U_lit in Hc by lia. discriminate Hc. }
    destruct Hrd1 as (-> & v & Mv & Rv & Hsign).
    paj_run_to_tok RUNTO HS HJ SHOK gp4_Bspan AF_fr_check_no_loss_read.
    { apply awr_ok_x_cons; [intros x Hx; cbn in Hx; lia | apply awr_ok_x_nil]. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_CS HS HAE ltac:(vm_compute; reflexivity)) as KR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |} _ =>
      set (rc0 := r) in *; set (mdc := d) in * end.
    assert (Hsp1 : spZ rc0 = lf_F cx).
    { unfold spZ. rewrite (KR 2%bv ltac:(gp4_in)), R2. unfold w64. apply unsigned_lit_small.
      unfold LLVMF_STK in *. lia. }
    destruct (gp4_afn_pre_at cx ly S fpos kk W mem mdc rc0 CNLR_STK HB HJ HSV Hsp1) as (ch & HPREc).
    { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
    { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
    { rewrite (KR 3%bv ltac:(gp4_in)). exact R3. }
    { rewrite (KR 4%bv ltac:(gp4_in)). exact R4. }
    { rewrite (KR 8%bv ltac:(gp4_in)). exact R8. }
    { unfold CNLR_STK. lia. }
    { unfold CNLR_STK, LLVMF_STK. lia. }
    (* check_no_loss_read's premises at p = &g_s[q] *)
    assert (Hgs : rg_s fr_RG = 6129888) by (vm_compute; reflexivity).
    assert (Hv0 : VAL (A_OBJ 0) = 645584) by (vm_compute; reflexivity).
    assert (Hv32 : VAL (A_OBJ 32) = 680120) by (vm_compute; reflexivity).
    set (p := rg_s fr_RG + ASRC * Z.of_nat q) in *.
    assert (H10 : getr rc0 10 = w64 p) by (rewrite Q10, (EEo 21%nat 21%bv eq_refl); exact R21).
    assert (Hp16 : p mod 16 = 0).
    { unfold p. rewrite Hgs. unfold ASRC.
      replace (6129888 + 96 * Z.of_nat q) with ((383118 + 6 * Z.of_nat q) * 16) by lia. apply Z_mod_mult. }
    assert (Hp0 : 0x10000 <= p) by (unfold p, ASRC; lia).
    assert (Hp1 : p + 28 <= 0x5fb000) by (unfold p, ASRC; lia).
    assert (Hzs : azs B p 28) by (apply (gp4_azs_sub _ _ _ _ HZS); unfold p, ASRC; lia).
    assert (Hd0 : p + 28 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= p) by (right; rewrite Hv0; unfold p, ASRC; lia).
    assert (Hd32 : p + 28 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= p) by (right; rewrite Hv32; unfold p, ASRC; lia).
    eapply SRr_bind.
    { exact (CNLR W ly S rc0 mem mdc ch p v HPREc H10 Hp16 Hp0 Hp1 Hzs Hd0 Hd32 Mv Rv Hsign). }
    intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & HPR2 & HEV).
    rewrite Hsp1 in HJc.
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & JH & JB & JI & JF & _).
    (* check_no_loss_read's journal inside this function's: W2's ajournal_gx_sub at G_fr, lifted from the donor's
       journal (G = []) *)
    assert (HJc0 : ajournal_gx segs B [] 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0)
      by (apply ajournal_gx_nil; exact HJc).
    assert (HJc' : ajournal_gx segs B G_fr 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0).
    { refine (ajournal_gx_G_mono segs B [] G_fr 0 [] CNLR_STK (lf_F cx) [] ly S W mem mdc [] ly S W2 mem2 md2 0 _ HJc0).
      intros a Ha. exfalso. exact (inG_nil a Ha). }
    pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 [] (lf_FP fr_FP cx)
       (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem mdc kk
       CNLR_STK (lf_F cx) 0 [] [] [] ly S W2 mem2 md2 0 HJ HJc'
       ltac:(unfold CNLR_STK, LLVMF_STK in *; lia) ltac:(lia) ltac:(lia)
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
       ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
    cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
    apply SRr_ret. unfold gp4_head_post.
    exists regs2, mem2, md2, kk.
    split; [unfold cfg_at; rewrite Q1; reflexivity|].
    split; [exact HJ2|].
    split; [intros r Hr; rewrite (gp4_cs_pres rc0 regs2 HP2 r Hr); exact (KR r Hr)|].
    (* the kept bytes: aleaf_post's view clauses and errno's view; writability from presence and wle *)
    intros a Kc. split; [|exact (gp4k_wr_kept W W2 mem mem2 a (HPR2 a) Hwle2)].
    destruct Kc as [(Kh1 & Kh2) | [(pb & nb & Kin & Kr) | [(Ki & Ko) | [Ke | (cid & pos & Kin & Kr)]]]].
    + apply JH; [exact Kh1 | unfold CNLR_STK; lia].
    + replace a with (pb + (a - pb)) by lia.
      apply (JB pb nb (a - pb)); [exact Kin | exact Kin | lia | intros Kf; exact (inFP_nil _ Kf)].
    + destruct (Z_le_dec (as_errno B) a) as [Ke1|Ke1]; [destruct (Z_lt_dec a (as_errno B + 4)) as [Ke2|Ke2]|].
      * replace a with (as_errno B + (a - as_errno B)) by lia. apply HEV. lia.
      * apply JI; [exact Ki | exact Ko | lia | apply fp_spares_closed; exact sink_closed_nil].
      * apply JI; [exact Ki | exact Ko | lia | apply fp_spares_closed; exact sink_closed_nil].
    + replace a with (as_errno B + (a - as_errno B)) by lia. apply HEV. lia.
    + apply (JF cid pos a Kin Kr). intros Kf. exact (inFP_nil _ Kf).
Qed.

(* ---- 0x84858 -> 0x84848 (q + 1 < 4) or 0x84864 (q = 3) ---- *)
Definition gp4_tail_post (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (q : nat) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' md' kk', gp4_jr cx fpos ly S W mem md' kk' /\
    (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    ((((q + 1) < 4)%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_c1) regs' mem md' /\
      getr regs' 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat (q + 1)) /\
      getr regs' 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat (q + 1))) \/
     ((q + 1)%nat = 4%nat /\ c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem md')).
Lemma gp4_tail : forall cx fpos ly S kk (W : world segs) regs mem md (q : nat),
  gp4_jr cx fpos ly S W mem md kk -> (q < 4)%nat -> 0 <= lf_F cx -> lf_F cx + 256 <= 2 ^ 64 ->
  getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) -> getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gp4_mid) regs mem md) (gp4_tail_post cx fpos ly S W regs mem q).
Proof.
  intros cx fpos ly S kk W regs mem md q HJ Hq HF0 HF1 R20 R21 R22.
  unfold gp4_jr in HJ.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  assert (Hgs : rg_s fr_RG = 6129888) by (vm_compute; reflexivity).
  destruct (gp4_entry_md W regs mem) as [HS SHOK].
  remember (Eimg (Ereg regs gp4_md_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs gp4_md_extra) E)
    by (rewrite HE; split; [intros x Hx; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E20 : ew E 20 = Z_to_bv 64 (lf_F cx + 192 + 4 * Z.of_nat q)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 (rg_s fr_RG + ASRC * Z.of_nat q)) by (rewrite (EEo 21%nat 21%bv eq_refl); exact R21).
  assert (E22 : ew E 22 = Z_to_bv 64 (lf_F cx + 208)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gp4_mid)) with (Z_to_bv 64 (BASE + AF_gp4_mid)).
  paj_run_tok RUN HS HJ SHOK gp4_Bspan. { apply awr_ok_x_nil. }
  gp4_mem HF Em1. clear HF HFr HG0.
  psrr_branch_tok RUN BR HS SHOK gp4_Bspan.
  - (* s4 <> s6: back to the head *)
    rewrite branch_ne_U, (U_atom_off E 20 _ 4 E20), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq1 : ((q + 1) < 4)%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [discriminate Hc | lia]. }
    paj_run_to_tok RUNTO HS HJ SHOK gp4_Bspan AF_gn_c1. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_tail_post. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. left.
    split; [exact Hq1|]. split; [reflexivity|].
    split.
    + rewrite Q20, E20, unsigned_lit_small by lia. unfold w64. f_equal. lia.
    + rewrite Q21, E21, unsigned_lit_small by (unfold ASRC; lia). unfold w64. f_equal. unfold ASRC. lia.
  - (* s4 = s6: the loop is done *)
    rewrite branch_ne_U, (U_atom_off E 20 _ 4 E20), (U_atom E 22 _ E22) in Hc by lia.
    assert (Hq4 : (q + 1)%nat = 4%nat).
    { destruct (Z.eqb_spec (lf_F cx + 192 + 4 * Z.of_nat q + 4) (lf_F cx + 208)) as [He | He];
        [lia | discriminate Hc]. }
    paj_run_to_tok RUNTO HS HJ SHOK gp4_Bspan AF_gn_t0. { apply awr_ok_x_nil. }
    gp4_mem HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ GP4_K2 HS HAE ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite Em2 in *. rewrite Em1 in *.
    apply SRr_ret. unfold gp4_tail_post. split; [reflexivity|].
    lazymatch goal with |- context [{| cfg_ms := mkst ?r _ _ _; cfg_model := ?d |}] => exists r, d, kk end.
    split; [exact HJ|]. split; [exact KR|]. right.
    split; [exact Hq4 | reflexivity].
Qed.

(* ---- the loop, by induction on the slots left ---- *)
Definition gp4_loop_post (cx : lfcx) (fpos : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) : world segs -> config -> Prop :=
  fun W' c' => exists regs' mem' md' kk', c' = cfg_at segs (fr_B0 + AF_gn_t0) regs' mem' md' /\
    gp4_jr cx fpos ly S W' mem' md' kk' /\ (forall r, In r GP4_K2 -> getr regs' r = getr regs r) /\
    gp4_keep cx ly S W mem W' mem'.
Lemma gp4_loopX : forall (k : nat) cx fpos ly S (q : nat) kk (W : world segs) regs mem md,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> k = (4 - q)%nat -> (q < 4)%nat ->
  gp4_jr cx fpos ly S W mem md kk -> gp4_saved cx W mem -> gp4_cells cx W mem q ->
  getr regs 2 = w64 (lf_F cx) -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 8 = getr (c_regs cx) 2 ->
  getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) -> getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
  getr regs 22 = w64 (lf_F cx + 208) ->
  SRr segs W (cfg_at segs (fr_B0 + AF_gn_c1) regs mem md) (gp4_loop_post cx fpos ly S W regs mem).
Proof.
  induction k as [|k IH]; intros cx fpos ly S q kk W regs mem md HB Hk Hq HJ HSV HCL R2 R3 R4 R8 R20 R21 R22; [lia|].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx _ ly S W mem md kk fpos HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx - 16) by (unfold LLVMF_STK in *; lia).
  destruct (HCL q ltac:(lia)) as (rd & HRD & Hrd).
  eapply SRr_bind; [exact (gp4_head cx fpos ly S kk W regs mem md q rd HB HJ HSV Hq R2 R3 R4 R8 R20 R21 HRD Hrd)|].
  intros W1 c1 Hwle1 (regs1 & mem1 & md1 & kk1 & -> & HJ1 & KR1 & KP1).
  eapply SRr_bind.
  { apply (gp4_tail cx fpos ly S kk1 W1 regs1 mem1 md1 q HJ1 Hq); [lia | lia | | |].
    - rewrite (KR1 20%bv ltac:(gp4_in)). exact R20.
    - rewrite (KR1 21%bv ltac:(gp4_in)). exact R21.
    - rewrite (KR1 22%bv ltac:(gp4_in)). exact R22. }
  intros W2 c2 Hwle2 (-> & regs2 & md2 & kk2 & HJ2 & KR2 & [(Hq1 & -> & Q20 & Q21) | (Hq4 & ->)]).
  - (* the next slot *)
    assert (KRR : forall r, In r GP4_K2 -> getr regs2 r = getr regs r)
      by (intros r Hr; rewrite (KR2 r Hr); exact (KR1 r (gp4_k2_cs r Hr))).
    eapply SRr_mono.
    { apply (IH cx fpos ly S (q + 1)%nat kk2 W1 regs2 mem1 md2 HB ltac:(lia) Hq1 HJ2).
      - intros o r Hin. apply (gp4k_sv8_kept W W1 mem mem1); [|exact (HSV o r Hin)].
        intros x Hx.
        assert (Ho : 8 <= o <= 104).
        { cbn in Hin. repeat (destruct Hin as [E | Hin]; [inversion E; lia|]). destruct Hin. }
        apply KP1. left. split; lia.
      - intros j Hj. destruct (HCL j ltac:(lia)) as (rj & Hcj & Hrj). exists rj. split.
        + apply (akept_vm W mem); [|exact Hcj]. intros x Hx. apply KP1. left. split; lia.
        + destruct Hrj as [Hr0 | (Hr1 & vj & Mvj & Rvj & Hsj)]; [left; exact Hr0|]. right. split; [exact Hr1|].
          exists vj. split; [|split; [exact Rvj | exact Hsj]].
          apply (akept_vm W mem); [|exact Mvj]. intros x Hx. apply KP1. apply gp4_cls_cell.
          apply (gp4k_cell (rg_s fr_RG) (4 * ASRC)); [gp4k_inl | unfold ASRC in *; lia].
      - rewrite (KRR 2%bv ltac:(gp4_in)). exact R2.
      - rewrite (KRR 3%bv ltac:(gp4_in)). exact R3.
      - rewrite (KRR 4%bv ltac:(gp4_in)). exact R4.
      - rewrite (KRR 8%bv ltac:(gp4_in)). exact R8.
      - exact Q20.
      - exact Q21.
      - rewrite (KRR 22%bv ltac:(gp4_in)). exact R22. }
    intros W' c' Hwle (regs' & mem' & md' & kk' & -> & HJ' & KR' & KP').
    exists regs', mem', md', kk'. split; [reflexivity|]. split; [exact HJ'|].
    split; [intros r Hr; rewrite (KR' r Hr); exact (KRR r Hr)|].
    exact (gp4_keep_trans cx ly S W W1 W' mem mem1 mem' KP1 KP').
  - (* the last slot: 0x84864 *)
    apply SRr_ret. exists regs2, mem1, md2, kk2. split; [reflexivity|]. split; [exact HJ2|].
    split; [intros r Hr; rewrite (KR2 r Hr); exact (KR1 r (gp4_k2_cs r Hr))|]. exact KP1.
Qed.

(* ================================================================== GP4 *)
Lemma gp4_c1_t0 : forall q cx t m m1 W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> GC1 B MT G_fr fr_FP LS RINV cx t m m1 q W c ->
  SRr segs W c (GT0 B MT G_fr fr_FP LS RINV cx t m m1).
Proof.
  intros q cx t m m1 W c HB HC.
  destruct HC as (regs & mem & md & ly & S & kk & fpos & -> & HGST & HGD & HLS & HKR & R20 & R21 & R22 & Hq & HCL &
    HAWR & H208 & HPF).
  pose proof HGST as ((HJ & HFR & H40 & H144 & HIN & HRV & HJT & HFL) & HMOD & HSEP).
  pose proof HKR as (R2 & R8 & R9 & R18 & R19 & R23 & R24 & R25 & R26 & R3 & R4 & R27).
  pose proof HGD as (hs & qs & c2 & O2 & cap2 & out2 & Hpairs & Hafter & Hrok & HRI & Hop & Hkeys).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx _ ly S W mem md kk fpos HB HJ eq_refl) as HN.
  cbv zeta in HN. destruct HN as (Hal & Hsp0 & HF32 & HFb & HFF0 & HFF1 & HFFa & Hfrs & HAR).
  assert (Hq4 : (q < 4)%nat) by exact Hq.
  (* the cells reads[j] and the slots behind them *)
  assert (HCL' : gp4_cells cx W mem q).
  { intros j Hj. exists (gn_reads m j). split; [exact (HCL j ltac:(lia))|].
    destruct (gp4_reads01 m j) as [H0 | H1]; [left; exact H0 | right; split; [exact H1|]].
    exists 0. split; [|split; [lia | left; reflexivity]].
    pose proof HMOD as (_ & HSL & _). specialize (HSL j ltac:(lia)). unfold aslot in HSL.
    destruct (nth j (lm_hs m1) None) as [h|] eqn:Hnth.
    - destruct (RIR cx t m hs qs c2 O2 cap2 out2 m1 j h HRI Hpairs Hafter Hrok ltac:(lia) H1 Hnth) as [Hpe _].
      destruct HSL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hn & _) & _).
      unfold hl_n in Hn. rewrite Hpe in Hn. cbn [length Z.of_nat] in Hn.
      replace (rg_s fr_RG + ASRC * Z.of_nat j + 24) with (rg_s fr_RG + ASRC * Z.of_nat j + 16 + 8) by lia. exact Hn.
    - destruct HSL as [HZ _]. exact (gp4_zero4 _ _ 24 HZ ltac:(lia) ltac:(unfold ASRC; lia)). }
  eapply SRr_mono.
  { exact (gp4_loopX (4 - q) cx fpos ly S q kk W regs mem md HB eq_refl Hq4 HJ (proj1 HFR) HCL'
      R2 R3 R4 R8 R20 R21 R22). }
  intros W' c' Hwle (regs' & mem' & md' & kk' & -> & HJ' & KR & KP).
  (* what the loop kept (gp4_kcls): every byte from s1 up, the fake frame and its shadow, the live blocks, the
     model's cells, errno; and the read-only image, the allocator's own bytes pinned in both states *)
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx).
  { destruct HB as (_ & HPRE0). unfold fr_lib_pre_cf in HPRE0. symmetry. tauto. }
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx - 16) by (unfold LLVMF_STK in *; lia).
  assert (KH : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KP; left; split; lia).
  assert (KF : forall a, frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + 128 \/
      SB + frame_addr ly 1 fpos / 8 <= a < SB + frame_addr ly 1 fpos / 8 + 16 -> abyte_kept W mem W' mem' a).
  { intros a Ha. apply KP. right; right; right; right. exists 1, fpos. split; [rewrite Hfrs; left; reflexivity|].
    unfold in_zr, frame_rng, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1) with 128.
    change (128 / 8) with 16. unfold SB in Ha. unfold SHADOW_OFF. lia. }
  assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < req_size n -> abyte_kept W mem W' mem' (p + i))
    by (intros p n i Hin Hi; apply KP; right; left; exists p, n; split; [exact Hin | lia]).
  assert (KC : forall a, inG gn_cells a -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KP; apply gp4_cls_cell; exact Ha).
  assert (KE : forall i, 0 <= i < 4 -> abyte_kept W mem W' mem' (as_errno B + i))
    by (intros i Hi; apply KP; right; right; right; left; lia).
  assert (HAR' : AR segs B ly S W' mem' md') by (eapply ajournal_gx_AR; exact HJ').
  assert (ROMK : forall a, in_rom segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a).
  { intros a Ha.
    assert (Him : in_img segs a) by (destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
    destruct (Exists_dec (in_zr a) (as_owned_static B)) as [Ho|Ho].
    { intros r. unfold in_zr. destruct (Z_le_dec (fst r) a); destruct (Z_lt_dec a (fst r + snd r));
        [left; lia | right; lia | right; lia | right; lia]. }
    - pose proof (HROMPIN a Ha Ho) as Hp.
      rewrite (rom_pinned_view segs B ly S W' mem' md' a HAR' Hp), (rom_pinned_view segs B ly S W mem md a HAR Hp).
      reflexivity.
    - refine (proj1 (KP a _)). right; right; left. split; [exact Him | exact Ho]. }
  assert (HFR' : gframe cx fake_shadow_open (frame_addr ly 1 fpos) W' mem')
    by (apply (gp4_gframe_kept cx fake_shadow_open (frame_addr ly 1 fpos) W W' mem mem' HFR eq_refl KF KH); lia).
  pose proof (gp4k_amodel_kept B ly S W mem W' mem' m1 HMOD KB KC KE) as HMOD'.
  assert (HIN' : ainput_at B cx ly S W' mem').
  { destruct HIN as (I1 & I2). split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
    intros x Hx. rewrite length_map, HlenP in Hx.
    destruct I1 as [(Hn0 & _) | (Hn & Hin)]; [exfalso; lia|].
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hr].
    replace x with (c_p cx + (x - c_p cx)) by lia. apply (KB _ _ _ Hin). lia. }
  assert (HRV' : rom_view segs W' mem') by (intros a Ha; rewrite (ROMK a Ha); exact (HRV a Ha)).
  assert (HJT' : jt_rom W' mem').
  { intros i Hi. apply (val_mem_kept segs (w_H W) (w_H W') mem mem'); [|exact (HJT i Hi)].
    intros j Hj. apply ROMK. apply gp4k_jt_in_rom. cbn in Hj. lia. }
  (* the fake frame's flag word: FF + 120 lies in the fake frame, kept like gframe's FF words *)
  assert (HFL' : sv8 W' mem' (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos)).
  { apply (gp4k_sv8_kept W W' mem mem'); [|exact HFL]. intros x Hx. apply KF. lia. }
  exists regs', mem', md', ly, S, kk', fpos. split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD' | exact HSEP]].
    split; [exact HJ'|]. split; [exact HFR'|].
    split; [apply (gp4k_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H40]|].
    split; [apply (gp4k_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H144]|].
    split; [exact HIN'|]. split; [exact HRV'|]. split; [exact HJT' | exact HFL']. }
  split; [exact HGD|]. split; [exact HLS|].
  split.
  { unfold gn_kregs. repeat split; rewrite KR; first [assumption | unfold GP4_K2; gp4_in]. }
  split; [apply (akept_awr W mem); [intros x Hx; apply KH; lia | exact HAWR]|].
  split; [apply (gp4k_sv8_kept W W' mem mem'); [intros x Hx; apply KH; lia | exact H208]|].
  apply (gp4_prefix_kept cx m W W' mem mem' _ HPF). intros a Ha. apply KF. lia.
Qed.
End gp4.
