(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its module names and numbers changed; 1163 of its 1272 lines of code are new or changed and 1247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/FSW_put_string.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put_string.v; 159 of its 221 lines of code are new or changed and 1210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/ZZpssep.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* SCRATCH (a Theorem Labs lane): put_string's SEPARATION facts, image B (fs.asan-ubsan). Folded into FSW_put_string.v.
   ps_put_call takes that put's footprint FS_PSTAT_FP ++ wbuf_fp buf cap misses the caller's class-0 fake frame and its
   shadow; psl_iter takes that the scanned string misses that frame and its shadow. Both come from put_string_spec's
   premises alone (wout_ok, cstr_ok, wsrc_kept) and AR at the state where the frame is live. No Section hypothesis is
   taken beyond the Context and B; fs_img_facts is not needed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v FSH_Base FSH_Rt FSPstat FSW_put_string.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer.
(* the image's four loaded segments by name (YB1v's tfibsegs is AsanUbsan.M.loaded_segments); Required, not Imported *)
From OSSVerify.omx_clap_core.fuzz_state.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= closed arithmetic (lia only here, never in a walk context) ================= *)
(* the image hull, inlined: AD1y.in_img_hull is the same fact over 0x10000 .. 0x5fd000, but AD1y imports YCe5, whose
   names (blk_img, frm_img, sep_block_frame, ...) are YCbq's, and its .vo is not in this file's dependency cone *)
Lemma pss_img_seg0 : forall a, 0x10000 <= a < 0x30000 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (E : tfibsegs = [AsanUbsan.AsanUbsan_segment_000; AsanUbsan.AsanUbsan_segment_001;
  AsanUbsan.AsanUbsan_segment_002; AsanUbsan.AsanUbsan_segment_003]) by reflexivity.
rewrite E. exists AsanUbsan.AsanUbsan_segment_000. split; [cbn; tauto | cbn; lia].
Qed.
Lemma pss_img_seg3 : forall a, 0xa1000 <= a < 0x5fd000 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (E : tfibsegs = [AsanUbsan.AsanUbsan_segment_000; AsanUbsan.AsanUbsan_segment_001;
  AsanUbsan.AsanUbsan_segment_002; AsanUbsan.AsanUbsan_segment_003]) by reflexivity.
rewrite E. exists AsanUbsan.AsanUbsan_segment_003. split; [cbn; tauto | cbn; lia].
Qed.

(* FS_PSTAT_FP (FSPstat.v:18) lies in [0xa41c0, 0x5dab08) *)
Lemma pss_pstat_rng : forall a, inFP FS_PSTAT_FP a -> 0xa41c0 <= a < 0x5dab08.
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha; lia.
Qed.

(* FS_RO_STRS (FSH_Rt.v:38), every literal with its terminating zero, lies in [0x20ea0, 0x21303) *)
Lemma pss_ro_rng : forall s l, In (s, l) FS_RO_STRS -> 0x20ea0 <= s /\ s + Z.of_nat (length l) + 1 <= 0x21303.
Proof.
intros s l Hin.
assert (H : forallb (fun e => (0x20ea0 <=? fst e) && (fst e + Z.of_nat (length (snd e)) + 1 <=? 0x21303))
              FS_RO_STRS = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (s, l) Hin). cbn [fst snd] in H.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. split; assumption.
Qed.

Lemma pss_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

Lemma pss_fb0 : fs_frame_bytes 0 = 64.
Proof. reflexivity. Qed.

Lemma pss_len0 : forall bs : list Z, Z.of_nat (length (bs ++ [0])) = Z.of_nat (length bs) + 1.
Proof. intros bs. rewrite length_app. cbn [length]. lia. Qed.

(* a byte of a frame's shadow: SHADOW_OFF + F / 8 .. + fb / 8, inside the shadow band [kLowMemEnd, kHighShadowEnd) *)
Lemma pss_sh_rng : forall F fb a, 4096 <= F -> 0 <= fb -> F + fb <= 0x7fffff800000 ->
  0x7fff8000 + F / 8 <= a < 0x7fff8000 + F / 8 + fb / 8 -> 0x7fff8000 <= a < 0x10007fff8000.
Proof.
intros F fb a H1 H2 H3 H4.
pose proof (Z.div_mod F 8 ltac:(discriminate)). pose proof (Z.mod_pos_bound F 8 ltac:(reflexivity)).
pose proof (Z.div_mod fb 8 ltac:(discriminate)). pose proof (Z.mod_pos_bound fb 8 ltac:(reflexivity)).
lia.
Qed.

(* application memory (in_app's two arms) misses the shadow band *)
Lemma pss_app_out : forall p r a C, 4096 <= p -> (p + r <= 0x7fff7000 \/ (0x10007fff8000 <= p /\ p + r <= C)) ->
  0x7fff8000 <= a < 0x10007fff8000 -> ~ (p <= a < p + r).
Proof. intros p r a C H1 H2 H3. lia. Qed.

Lemma pss_disj_out : forall b r F fb a, (b + r <= F \/ F + fb <= b) -> F <= a < F + fb -> ~ (b <= a < b + r).
Proof. intros b r F fb a H1 H2. lia. Qed.

Lemma pss_sh_pstat : forall a, 0x7fff8000 <= a < 0x10007fff8000 -> ~ (0xa41c0 <= a < 0x5dab08).
Proof. intros a H1 H2. lia. Qed.

Lemma pss_wbuf_in : forall buf cap a, buf - HEAD <= a < buf + cap -> buf - HEAD <= a < buf - HEAD + req_size (cap + HEAD).
Proof. intros buf cap a H. pose proof (pss_req_ge (cap + HEAD)). unfold HEAD in *. lia. Qed.

Lemma pss_neq_head : forall p buf, p <> buf -> p - HEAD <> buf - HEAD.
Proof. intros p buf H. unfold HEAD. lia. Qed.

Lemma pss_in_blk : forall p k s x n, p <= s -> s + (n + 1) <= p + k -> s <= x < s + n + 1 -> p <= x < p + req_size k.
Proof. intros p k s x n H1 H2 H3. pose proof (pss_req_ge k). lia. Qed.

Lemma pss_in_rblk : forall p k s x n, p <= s -> s + (n + 1) <= p + k -> s <= x < s + n + 1 ->
  p - HEAD <= x < p - HEAD + req_size (k + HEAD).
Proof. intros p k s x n H1 H2 H3. pose proof (pss_req_ge (k + HEAD)). unfold HEAD in *. lia. Qed.

(* a byte of a prefix of an fs read-only literal (wsrc_kept's fourth arm) lies in the image's first segment *)
Lemma pss_ro_x : forall s l (bs : list Z) x, In (s, l) FS_RO_STRS -> (length (bs ++ [0%Z]) <= Nat.succ (length l))%nat ->
  s <= x < s + Z.of_nat (length bs) + 1 -> 0x10000 <= x < 0x30000.
Proof.
intros s l bs x Hin Hlen Hx. destruct (pss_ro_rng s l Hin) as [H1 H2].
rewrite length_app in Hlen. cbn [length] in Hlen. rewrite Nat.add_1_r in Hlen. apply le_S_n in Hlen.
apply Nat2Z.inj_le in Hlen. lia.
Qed.

(* the frame's shadow granule test: F 32-aligned, so x's shadow byte is among F's eight iff x is in [F, F + 64) *)
Lemma pss_sh8 : forall F x, F mod 32 = 0 ->
  SHADOW_OFF + F / 8 <= SHADOW_OFF + x / 8 < SHADOW_OFF + F / 8 + 8 -> F <= x < F + 64.
Proof.
intros F x HF Hx.
pose proof (Z.div_mod F 32 ltac:(discriminate)). pose proof (Z.div_mod F 8 ltac:(discriminate)).
pose proof (Z.mod_pos_bound F 8 ltac:(reflexivity)).
pose proof (Z.div_mod x 8 ltac:(discriminate)). pose proof (Z.mod_pos_bound x 8 ltac:(reflexivity)).
lia.
Qed.

(* cstr_ok's amem_range: the string and its terminating zero are application memory, not the shadow band *)
Lemma pss_amem_out : forall s n x, amem_range s (n + 8) -> s <= x < s + n + 1 ->
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof. intros s n x H1 H2. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. Qed.

(* the blocks that are not the writer's buffer survive a bswap (put's post), so a string block of the entry state
   is a block of every later state of put_string's walk *)
Lemma pss_bswap_keep : forall A A' buf buf' cap cap' p n,
  FSH_Fn_writer.bswap A A' buf buf' cap cap' -> In (p, n) A -> p <> buf - HEAD -> In (p, n) A'.
Proof.
intros A A' buf buf' cap cap' p n Hsw Hin Hne.
destruct Hsw as [(_ & _ & ->) | [(_ & C1 & C2 & -> & EC) | (A1 & A2 & C1 & C2 & EA & -> & EC)]].
- exact Hin.
- rewrite <- EC in Hin. apply in_app_or in Hin as [Hin | Hin]; apply in_or_app; [left | right; right]; exact Hin.
- rewrite EA in Hin. apply in_app_or in Hin as [Hin | [Ehd | Hin]].
  + assert (H : In (p, n) (C1 ++ C2)) by (rewrite EC; apply in_or_app; left; exact Hin).
    apply in_app_or in H as [H | H]; apply in_or_app; [left | right; right]; exact H.
  + exfalso. apply Hne. injection Ehd as E1 E2. exact (eq_sym E1).
  + assert (H : In (p, n) (C1 ++ C2)) by (rewrite EC; apply in_or_app; right; exact Hin).
    apply in_app_or in H as [H | H]; apply in_or_app; [left | right; right]; exact H.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ================= 1. the statics are image bytes ================= *)
Lemma pss_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a HP. apply pss_img_seg3. destruct (pss_pstat_rng a HP) as [H1 H2]. split; lia.
Qed.

(* ================= 2. a live fake frame and its shadow miss the statics ================= *)
Lemma pss_fr_off_pstat : forall ly S (W : world tfibsegs) mem md cid pos a,
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) ->
  (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
  ~ inFP FS_PSTAT_FP a.
Proof.
intros ly S W mem md cid pos a HAR Hin Hr HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct Hr as [Hr | Hr].
- exact (frm_img tfibsegs B LAWS ly S W mem md cid pos a HAR Hin Hr (pss_pstat_img a HP)).
- destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (HF0 & HFc & _).
  pose proof asan_consts as (C1 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  unfold shadow_addr, SHADOW_OFF in Hr.
  exact (pss_sh_pstat a (pss_sh_rng _ _ a HF0 Hfb (Z.le_trans _ _ _ HFc (proj2 C1)) Hr) (pss_pstat_rng a HP)).
Qed.

(* ================= 3. a live fake frame and its shadow miss every live block ================= *)
Lemma pss_fr_off_blk : forall ly S (W : world tfibsegs) mem md cid pos p m a,
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) -> In (p, m) (ablocks B ly S) ->
  (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
  ~ (p <= a < p + req_size m).
Proof.
intros ly S W mem md cid pos p m a HAR Hin Hblk Hr.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct Hr as [Hr | Hr].
- pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md p m cid pos HAR Hblk Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  exact (pss_disj_out p (req_size m) (frame_addr ly cid pos) (fs_frame_bytes cid) a Hd Hr).
- destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hblk) as (_ & H4096 & _ & Happ & _).
  destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (HF0 & HFc & _).
  pose proof asan_consts as (C1 & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  unfold shadow_addr, SHADOW_OFF in Hr.
  pose proof (pss_sh_rng _ _ a HF0 Hfb (Z.le_trans _ _ _ HFc (proj2 C1)) Hr) as Ha.
  unfold in_app, kLowShadowBeg, kHighMemBeg in Happ.
  exact (pss_app_out p (req_size m) a _ H4096 (proj2 Happ) Ha).
Qed.

(* ================= 4. put's footprint misses the caller's fake frame and its shadow ================= *)
(* wout_ok's memory is free (memw): ps_put_call has ARU over memc, so AR over `unpoison U memc` (ARU_AR), and
   wout_ok over memc itself; only wout_ok's block membership is read, which no memory enters. *)
Lemma pss_fr_off_fp : forall ly S (W : world tfibsegs) mem md cid pos buf cap a memw o failed (text : list Z),
  AR tfibsegs B ly S W mem md -> In (cid, pos) (frames S) -> 0 <= cid ->
  FSH_Fn_writer.wout_ok B tfibsegs ly S W memw o buf cap failed text ->
  (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
  ~ inFP (FS_PSTAT_FP ++ FSH_Fn_writer.wbuf_fp buf cap) a.
Proof.
intros ly S W mem md cid pos buf cap a memw o failed text HAR Hin Hc0 HOUT Hr.
unfold FSH_Fn_writer.wbuf_fp. destruct (Z.eqb_spec cap 0) as [E | E]; intros HP.
- rewrite app_nil_r in HP. exact (pss_fr_off_pstat ly S W mem md cid pos a HAR Hin Hr HP).
- destruct HP as (r & Hr' & Ha). apply in_app_or in Hr' as [Hr' | Hr'].
  + exact (pss_fr_off_pstat ly S W mem md cid pos a HAR Hin Hr (ex_intro _ r (conj Hr' Ha))).
  + destruct Hr' as [<- | []]. cbn [fst snd] in Ha.
    unfold FSH_Fn_writer.wout_ok in HOUT.
    destruct HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [(E0 & _) | (_ & HRB & _)]);
      [exact (E E0)|].
    destruct HRB as (Hblk & _).
    exact (pss_fr_off_blk ly S W mem md cid pos (buf - HEAD) (cap + HEAD) a HAR Hin Hblk Hr
             (pss_wbuf_in buf cap a Ha)).
Qed.

(* ================= 5. the scanned string misses put_string's own fake frame ================= *)
(* The string's home is read off wsrc_kept at the ENTRY state (ly, S); the frame is live at a LATER state (lyc, Sc)
   (it is granted after the entry). The one link is that every block of the entry state other than the writer's
   buffer is still a block at (lyc, Sc): the frame grant keeps ablocks, and put's post gives bswap, which keeps every
   non-buffer block (pss_bswap_keep). *)
Lemma pss_str_off_fr : forall ly S U (W : world tfibsegs) mem buf s (bs : list Z)
    lyc Sc (Wc : world tfibsegs) memc mdc pos x,
  cstr_ok tfibsegs W mem s bs ->
  FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem buf s (bs ++ [0]) ->
  AR tfibsegs B lyc Sc Wc memc mdc -> In (0, pos) (frames Sc) ->
  (forall p n, In (p, n) (ablocks B ly S) -> p <> buf - HEAD -> In (p, n) (ablocks B lyc Sc)) ->
  s <= x < s + Z.of_nat (length bs) + 1 ->
  ~ (frame_addr lyc 0 pos <= x < frame_addr lyc 0 pos + 64) /\
  ~ (shadow_addr (frame_addr lyc 0 pos) <= shadow_addr x < shadow_addr (frame_addr lyc 0 pos) + 8) /\
  ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Proof.
intros ly S U W mem buf s bs lyc Sc Wc memc mdc pos x Hcs Hsk HAR Hin Hkeep Hx.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
(* where x lives: in a block of (lyc, Sc), or in the image *)
assert (Hloc : (exists p k, In (p, k) (ablocks B lyc Sc) /\ p <= x < p + req_size k) \/ in_img tfibsegs x).
{ unfold FSH_Fn_writer.wsrc_kept in Hsk.
  destruct Hsk as [(E & _) | [(p & k & Hne & HRB & Hp & Hk) | [(p & k & Hne & Hblk & Hp & Hk & _) | (l & Hl & Hlen)]]].
  - exfalso. destruct bs; discriminate E.
  - destruct HRB as (Hblk & _). left. exists (p - HEAD), (k + HEAD). split.
    + exact (Hkeep _ _ Hblk (pss_neq_head p buf Hne)).
    + rewrite pss_len0 in Hk. exact (pss_in_rblk p k s x _ Hp Hk Hx).
  - left. exists p, k. split.
    + exact (Hkeep _ _ Hblk Hne).
    + rewrite pss_len0 in Hk. exact (pss_in_blk p k s x _ Hp Hk Hx).
  - right. exact (pss_img_seg0 x (pss_ro_x s l bs x Hl Hlen Hx)). }
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 0 pos HAR Hin) as (Hal & _).
assert (Ha : ~ (frame_addr lyc 0 pos <= x < frame_addr lyc 0 pos + 64)).
{ intros Hf.
  assert (Hf' : frame_addr lyc 0 pos <= x < frame_addr lyc 0 pos + fs_frame_bytes 0) by (rewrite pss_fb0; exact Hf).
  destruct Hloc as [(p & k & Hblk & Hpk) | Himg].
  - exact (pss_fr_off_blk lyc Sc Wc memc mdc 0 pos p k x HAR Hin Hblk (or_introl Hf') Hpk).
  - exact (frm_img tfibsegs B LAWS lyc Sc Wc memc mdc 0 pos x HAR Hin Hf' Himg). }
split; [exact Ha|]. split.
- intros Hs. apply Ha. unfold shadow_addr in Hs. exact (pss_sh8 _ x Hal Hs).
- destruct Hcs as (_ & _ & _ & _ & Hamem & _). exact (pss_amem_out s _ x Hamem Hx).
Qed.

End W.
