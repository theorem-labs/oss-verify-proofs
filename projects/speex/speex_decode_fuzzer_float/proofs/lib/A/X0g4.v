(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0j1 X0gi X0hr X0j3 X0hi
X0hn X0j0 X0hh X0hb X0il X0gp X0h2 X0j4 X0hf X0fy X0fg X0da.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X173 X18c X19m X183 X188 X19k X182 X17w X196 X17a X17n X19n X180 X16j X161 X13v.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X182 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v.
Import ListNotations.
Open Scope Z_scope.

Lemma dsj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
induction W as [|[lo hi] W IH]; intros a n a' n' H H1 H2; cbn in *; [exact I|].
destruct H as [H3 H4]. split; [lia|]. exact (IH _ _ _ _ H4 H1 H2).
Qed.

Lemma dsj_app : forall W1 W2 a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a n H1 H2; cbn in *; [exact H2|]. split; [exact (proj1 H1)| exact (IH _ _ _ (proj2 H1) H2)]. Qed.

Lemma dsj_app_inv : forall W1 W2 a n, disjoint_from (W1 ++ W2) a n -> disjoint_from W1 a n /\ disjoint_from W2 a n.
Proof.
induction W1 as [|[lo hi] W1 IH]; intros W2 a n H; cbn in *; [split; [exact I | exact H]|].
destruct H as [H1 H2]. destruct (IH _ _ _ H2) as [X Y]. split; [split; [exact H1 | exact X]| exact Y].
Qed.

Lemma dsj_of_outside : forall W a n, 0 < n -> Forall (fun p => fst p < snd p) W ->
(forall x, a <= x < a + n -> outside W x) -> disjoint_from W a n.
Proof.
induction W as [|[lo hi] W IH]; intros a n Hn HW H; cbn in *; [exact I|]. apply Forall_cons_iff in HW as [Hlh HW]. cbn [fst snd] in Hlh.
split.
- destruct (Z_le_dec (a + n) lo) as [X|X]; [left; exact X|]. destruct (Z_le_dec hi a) as [Y|Y]; [right; exact Y|].
exfalso. destruct (Z_le_dec lo a) as [Z2|Z2].
+ destruct (H a ltac:(lia)) as [U _]. apply U. lia.
+ destruct (H lo ltac:(lia)) as [U _]. apply U. lia.
- apply IH; [exact Hn | exact HW|]. intros x Hx. exact (proj2 (H x Hx)).
Qed.

Lemma outside_app : forall W1 W2 x, outside W1 x -> outside W2 x -> outside (W1 ++ W2) x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x H1 H2; cbn in *; [exact H2|]. split; [exact (proj1 H1)| exact (IH _ _ (proj2 H1) H2)]. Qed.

Lemma bytes_at_nil_any : forall (m : mem) a, 0 <= a <= 2 ^ 64 -> bytes_at bsegs m a [].
Proof. intros m a Ha. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma farun_len : forall k, Z.of_nat (length (farun k)) = Z.max 0 k.
Proof. intros k. unfold farun. rewrite repeat_length. lia. Qed.
Lemma fdrun_len : forall k, Z.of_nat (length (fdrun k)) = Z.max 0 k.
Proof. intros k. unfold fdrun. rewrite repeat_length. lia. Qed.

Ltac cs_size := cbn [cells_size csize Nat.add length] in *.

Definition reg_avoid (W : list ivl) (SB c : Z) (r : regst) : Prop :=
let auser := ClassSize c * Z.of_nat (length (r_st r)) in
disjoint_from W (rinfo (RIS_of SB) c) 120 /\ disjoint_from W (fa SB c) (r_mfa r)
/\ disjoint_from W (shad (rb SB c + auser)) (Z.max 0 ((r_muser r - auser) / 8)).

Lemma reg_rep_transport : forall W SB c r (m m' : mem), reg_rep SB c r m -> munch W m m' -> wmono bsegs m m' ->
reg_avoid W SB c r -> reg_rep SB c r m'.
Proof.
intros W SB c r m m' H MU WM (A1 & A2 & A3).
destruct H as (L & C & (rand & exh & pad & nal & nfr & r0 & r1 & r2 & r3 & T) & (ws & F & Hws & Hpre) & S1 & B & S2).
unfold ri_lock, ri_core, ri_tail in *.
split; [apply (rw_cells_transport bsegs W m m' _ _ L MU WM); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
split; [apply (rw_cells_transport bsegs W m m' _ _ C MU WM); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
split; [exists rand, exh, pad, nal, nfr, r0, r1, r2, r3; apply (rw_cells_transport bsegs W m m' _ _ T MU WM); cs_size;
eapply dsj_sub; [exact A1| |]; lia|].
split; [exists ws; split; [|split; [exact Hws | exact Hpre]]; unfold fl_arr in *;
apply (u32arr_transport bsegs W m m' _ _ F MU WM); rewrite Hws; exact A2|].
split; [exact (stk_wmono m m' _ _ S1 WM)|].
split; [apply (bytes_at_transport bsegs W m m' _ _ B MU); rewrite farun_len; exact A3|].
exact (stk_wmono m m' _ _ S2 WM).
Qed.

Definition pclass_avoid (W : list ivl) (T c : Z) : Prop := disjoint_from W (pc_addr T c) 80.

Lemma pclass_rep_transport : forall W T c init l (m m' : mem), pclass_rep T c init l m -> munch W m m' -> wmono bsegs m m' ->
pclass_avoid W T c -> pclass_rep T c init l m'.
Proof.
intros W T c init l m m' (P & chs & U & Hl & Hp) MU WM A. unfold pc_cells in *.
split; [apply (rw_cells_transport bsegs W m m' _ _ P MU WM); cs_size; eapply dsj_sub; [exact A| |]; lia|].
exists chs. split; [|split; [exact Hl | exact Hp]]. apply (u32arr_transport bsegs W m m' _ _ U MU WM). rewrite Hl.
eapply dsj_sub; [exact A| |]; lia.
Qed.

Definition pchunk_avoid (W : list ivl) (SB c : Z) (i : nat) (st : ckst) : Prop :=
let AB := p_abeg SB c i in let S := ClassSize c in
match st with
| CkIdle | CkBatch => disjoint_from W (shad AB) (Z.max 0 (S / 8))
| CkAlloc n =>
disjoint_from W (AB + rz_size n - 16) 16 /\ (16 < rz_size n -> disjoint_from W AB 16)
/\ disjoint_from W (shad AB) (Z.of_nat (length (farun (rz_size n / 8) ++ ushadow n)))
/\ disjoint_from W (shad (AB + rz_size n + ru8 n)) (Z.max 0 ((S - rz_size n - ru8 n) / 8))
| CkQuar n =>
disjoint_from W (AB + rz_size n - 16) 24 /\ (16 < rz_size n -> disjoint_from W AB 16)
/\ disjoint_from W (shad AB) (Z.of_nat (length (farun (rz_size n / 8) ++ fdrun (ru8 n / 8) ++ farun ((S - rz_size n - ru8 n) / 8))))
end.

Lemma ahdr_transport : forall W (m m' : mem) M n, ahdr m M n -> munch W m m' -> wmono bsegs m m' -> disjoint_from W M 16 -> ahdr m' M n.
Proof.
intros W m m' M n (b1 & ctx & Hb & H) MU WM A. exists b1, ctx. split; [exact Hb|].
apply (rw_cells_transport bsegs W m m' _ _ H MU WM). cs_size. exact A.
Qed.
Lemma qhdr3_transport : forall W (m m' : mem) M n, qhdr3 m M n -> munch W m m' -> wmono bsegs m m' -> disjoint_from W M 24 -> qhdr3 m' M n.
Proof.
intros W m m' M n (b1 & ctx & fid & Hb & H) MU WM A. exists b1, ctx, fid. split; [exact Hb|].
apply (rw_cells_transport bsegs W m m' _ _ H MU WM). cs_size. exact A.
Qed.
Lemma lch_transport : forall W (m m' : mem) AB M, lch m AB M -> munch W m m' -> wmono bsegs m m' -> disjoint_from W AB 16 -> lch m' AB M.
Proof. intros W m m' AB M H MU WM A. apply (rw_cells_transport bsegs W m m' _ _ H MU WM). cs_size. exact A. Qed.

Lemma pchunk_transport : forall W SB c i st (m m' : mem), pchunk SB c i st m -> munch W m m' -> wmono bsegs m m' ->
pchunk_avoid W SB c i st -> pchunk SB c i st m'.
Proof.
intros W SB c i st m m' H MU WM A. unfold pchunk, pchunk_avoid in *. destruct st as [|n|n|].
- destruct H as [S B]. split; [exact (stk_wmono m m' _ _ S WM)|]. unfold pshadow_idle in *.
apply (bytes_at_transport bsegs W m m' _ _ B MU). rewrite farun_len. exact A.
- destruct H as (Wr & Hh & Hl & B1 & B2). destruct A as (A1 & A2 & A3 & A4).
split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (ahdr_transport W m m' _ _ Hh MU WM A1)|].
split; [intros Hr; exact (lch_transport W m m' _ _ (Hl Hr) MU WM (A2 Hr))|].
split; [apply (bytes_at_transport bsegs W m m' _ _ B1 MU); exact A3|].
apply (bytes_at_transport bsegs W m m' _ _ B2 MU). rewrite farun_len. exact A4.
- destruct H as (Wr & Hh & Hl & B1). destruct A as (A1 & A2 & A3).
split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (qhdr3_transport W m m' _ _ Hh MU WM A1)|].
split; [intros Hr; exact (lch_transport W m m' _ _ (Hl Hr) MU WM (A2 Hr))|].
unfold pshadow_quar in *. apply (bytes_at_transport bsegs W m m' _ _ B1 MU). exact A3.
- unfold pshadow_idle in *. apply (bytes_at_transport bsegs W m m' _ _ H MU). rewrite farun_len. exact A.
Qed.

Definition schunk_avoid (W : list ivl) (s : secst) : Prop :=
let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
disjoint_from W mb 32 /\ disjoint_from W AB 16 /\ disjoint_from W M (if s_quar s then 24 else 16)
/\ disjoint_from W (shad mb) (Z.max 0 ((4096 + 2048) / 8))
/\ disjoint_from W (shad (AB + 2048)) (Z.of_nat (length (if s_quar s then fdrun (ru8 n / 8) else ushadow n)))
/\ disjoint_from W (shad (AB + 2048 + ru8 n)) (Z.max 0 ((msz - 4096 - 2048 - ru8 n) / 8)).

Lemma schunk_transport : forall W k s (m m' : mem), schunk k s m -> munch W m m' -> wmono bsegs m m' ->
schunk_avoid W s -> schunk k s m'.
Proof.
intros W k s m m' H MU WM (A1 & A2 & A3 & A4 & A5 & A6). unfold schunk in *.
destruct H as (Hs & Wr & Hl & Hh & S & B1 & B2 & B3).
split; [unfold shdr in *; apply (rw_cells_transport bsegs W m m' _ _ Hs MU WM); cs_size; exact A1|].
split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (lch_transport W m m' _ _ Hl MU WM A2)|].
split; [destruct (s_quar s); [exact (qhdr3_transport W m m' _ _ Hh MU WM A3) | exact (ahdr_transport W m m' _ _ Hh MU WM A3)]|].
split; [exact (stk_wmono m m' _ _ S WM)|].
split; [apply (bytes_at_transport bsegs W m m' _ _ B1 MU); rewrite farun_len; exact A4|].
split; [apply (bytes_at_transport bsegs W m m' _ _ B2 MU); exact A5|].
apply (bytes_at_transport bsegs W m m' _ _ B3 MU). rewrite farun_len. exact A6.
Qed.

Definition dsjl (W : list ivl) (l : list (Z * Z)) : Prop := Forall (fun r => disjoint_from W (fst r) (snd r)) l.
Lemma dsjl_in : forall W l a n, dsjl W l -> In (a, n) l -> disjoint_from W a n.
Proof. intros W l a n H Hin. exact (proj1 (Forall_forall _ _) H (a, n) Hin). Qed.
Ltac in_lit := repeat (first [ left; reflexivity | right ]).

Ltac dsj_lit H := match goal with |- disjoint_from ?W ?a ?n => eapply (dsj_sub W a _ a n); [eapply (dsjl_in _ _ a _ H); in_lit | lia | lia] end.
Ltac rwc_lit H := eapply rw_cells_transport; [eassumption | eassumption | eassumption |]; cs_size; dsj_lit H.

Ltac rwc_litX H X := eapply (rw_cells_transport bsegs _ _ _ _ _ X); [eassumption | eassumption |]; cs_size; dsj_lit H.

Definition sec_lits : list (Z * Z) :=
[(i_sec_chunks, 8); (i_sec_nres, 16); (i_sec_mutex, 1); (i_sec_mutex + 1, 3); (i_sec_page, 8); (i_sec_range, 8); (i_sec_sorted, 40);
(i_sec_bylog, 512); (i_gstat_alloc, 16); (0xfc100, 8); (0xfe078, 8)].
Definition sec_avoid (W : list ivl) (Σ : rtsA) : Prop := dsjl W sec_lits /\ disjoint_from W (l_PAB (lay Σ)) (8 * sec_nres Σ).

Lemma sec_rep_transport : forall W Σ (m m' : mem), sec_rep Σ m -> munch W m m' -> wmono bsegs m m' -> sec_avoid W Σ -> sec_rep Σ m'.
Proof.
intros W Σ m m' H MU WM (A & AP). unfold sec_rep, sec_core, sec_pad, sec_page, sec_range, sec_junk, name_cells in *.
destruct H as ((C1 & C2 & C3) & P & (ws & U & Hl & Hf) & G & R & ((b & j & w1 & w2 & w3 & w4 & J1) & (bl & Hbl & J2) & (ga & gm & J3)) & N1 & N2).
split; [split; [rwc_lit A | split; [rwc_lit A | rwc_lit A]]|].
split; [rwc_lit A|].
split; [exists ws; split; [|split; [exact Hl | exact Hf]]; apply (u64arr_transport bsegs W m m' _ _ U MU WM); rewrite Hl; exact AP|].
split; [rwc_lit A|]. split; [rwc_lit A|].
split; [split; [exists b, j, w1, w2, w3, w4; rwc_lit A | split; [exists bl; split; [exact Hbl|] | exists ga, gm; rwc_lit A]]|].
- apply (u64arr_transport bsegs W m m' _ _ J2 MU WM). rewrite Hbl. dsj_lit A.
- split; rwc_lit A.
Qed.

Definition quar_avoid (W : list ivl) (Σ : rtsA) : Prop :=
disjoint_from W (qcacheT (l_T (lay Σ))) 32 /\ dsjl W [(i_q_global, 32); (i_q_cmutex, 4)]
/\ Forall (fun b => disjoint_from W (fst b) 8192) (ql Σ ++ qg Σ).

Lemma qchain_transport : forall W (m m' : mem) bs, qchain m bs -> munch W m m' -> wmono bsegs m m' ->
Forall (fun b => disjoint_from W (fst b) 8192) bs -> qchain m' bs.
Proof.
intros W m m' bs. induction bs as [|[b ents] bs IH]; intros H MU WM A; [exact I|].
apply Forall_cons_iff in A as [A1 A2]. cbn [fst] in A1. destruct H as [(H1 & (ws & U & Hl & Hf) & Hn) H2].
split; [|exact (IH H2 MU WM A2)]. split; [apply (rw_cells_transport bsegs W m m' _ _ H1 MU WM); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
split; [|exact Hn]. exists ws. split; [|split; [exact Hl | exact Hf]]. apply (u64arr_transport bsegs W m m' _ _ U MU WM).
rewrite Hl. eapply dsj_sub; [exact A1| |]; lia.
Qed.

Lemma quar_rep_transport : forall W Σ (m m' : mem), quar_rep Σ m -> munch W m m' -> wmono bsegs m m' -> quar_avoid W Σ -> quar_rep Σ m'.
Proof.
intros W Σ m m' ((Q1 & C1) & (Q2 & C2) & X) MU WM (A1 & A2 & A3). apply Forall_app in A3 as [A3 A4].
split; [split; [apply (rw_cells_transport bsegs W m m' _ _ Q1 MU WM); cs_size; exact A1 | exact (qchain_transport W m m' _ C1 MU WM A3)]|].
split; [split; [rwc_lit A2 | exact (qchain_transport W m m' _ C2 MU WM A4)]|]. rwc_lit A2.
Qed.

Definition dep_avoid (W : list ivl) (L : layoutA) : Prop :=
dsjl W [(0x1e7998, 0x5e7998 + 4 - 0x1e7998); (0x5e79a8, 8); (0x1d7988, 8); (0x1d7998, 0x1d79a0 + 4 - 0x1d7998)]
/\ disjoint_from W (l_DNB L) (2 ^ 20) /\ disjoint_from W (l_SSB L) (2 ^ 23).

Lemma dep_rep_transport : forall W L d (m m' : mem), dep_rep L d m -> depot_ok d (l_DNB L) (l_SSB L) (l_ACEIL L) ->
munch W m m' -> wmono bsegs m m' -> dep_avoid W L -> dep_rep L d m'.
Proof.
intros W L d m m' H OK MU WM (A & A5 & A6). unfold dep_rep in *.
apply (depot_rep_frame d _ _ _ _ W m m' H OK MU WM); [exact (dsjl_in _ _ 0x1e7998 _ A ltac:(in_lit)) | exact (dsjl_in _ _ 0x5e79a8 _ A ltac:(in_lit)) | exact A5
| exact (dsjl_in _ _ 0x1d7988 _ A ltac:(in_lit)) | exact (dsjl_in _ _ 0x1d7998 _ A ltac:(in_lit)) | exact A6].
Qed.

Definition fs_lits : list (Z * Z) :=
[(tpA, 8); (0x106798, 1); (g_real_tls_get_addr, 8); (g_dtv_ptr, 8); (g_dtv1, 8); (g_got_common_flags, 8);
(g_intercept_tls_get_addr, 1); (g_got_verbosity, 8); (g_current_verbosity, 4); (g_tls_index, 16); (g_got_dtls_off, 8);
(g_tls_dtls, 8)].
Definition fs_cls_avoid (W : list ivl) (FSB c : Z) (f : fsst) : Prop :=
disjoint_from W (FSB + 8 * c) 8 /\ disjoint_from W (fl_base FSB c) (Z.of_nat (length (fss_flags f)))
/\ (forall p, 0 <= p < NF c -> nth (Z.to_nat p) (fss_flags f) 1 = 0 ->
disjoint_from W (frame_addr FSB c p) (fsz c) /\ disjoint_from W (shad (frame_addr FSB c p)) (fsz c / 8)).
Definition fs_avoid (W : list ivl) (Σ : rtsA) : Prop :=
let L := lay Σ in
disjoint_from W (l_FSB L + 0x58) 9 /\ fs_cls_avoid W (l_FSB L) 0 (fs0 Σ) /\ fs_cls_avoid W (l_FSB L) 2 (fs2 Σ)
/\ (fs_cls_avoid W (l_FSB L) 4 (fs4 Σ) /\ fs_cls_avoid W (l_FSB L) 5 (fsc Σ 5%nat) /\ fs_cls_avoid W (l_FSB L) 8 (fsc Σ 8%nat)) /\ dsjl W fs_lits /\ disjoint_from W (l_DTV L + 24) 8 /\ disjoint_from W (l_T L + 48) 16
/\ Forall (fun fk => disjoint_from W (fst fk + fs_size (snd fk) - 8) 8) (frames Σ).

Lemma fs_cls_rep_transport : forall W FSB c f (m m' : mem), fs_cls_rep FSB c f m -> munch W m m' -> wmono bsegs m m' ->
fs_cls_avoid W FSB c f -> fs_cls_rep FSB c f m'.
Proof.
intros W FSB c f m m' (H1 & H2 & H3) MU WM (A1 & A2 & A3). unfold fs_hint, fs_flags in *.
split; [apply (rw_cells_transport bsegs W m m' _ _ H1 MU WM); cs_size; exact A1|].
split; [apply (u8arr_transport bsegs W m m' _ _ H2 MU WM); rewrite length_map; exact A2|].
exact (fs_free_frames_transport FSB c m m' _ W H3 MU WM A3).
Qed.

Lemma fs_rep_transport : forall W Σ (m m' : mem), fs_rep Σ m -> munch W m m' -> wmono bsegs m m' -> fs_avoid W Σ -> fs_rep Σ m'.
Proof.
intros W Σ m m' H MU WM (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold fs_rep, fs_const, tga_cells, dtls_cells, ttls_cells in *.
destruct H as (F1 & F2 & F3 & F4 & T & (dtvbeg & Hdb & (G1 & G2 & G3 & G4 & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8))) & (tb & te & TT) & FB).
split; [apply (rw_cells_transport bsegs W m m' _ _ F1 MU WM); cs_size; exact A1|].
split; [exact (fs_cls_rep_transport W _ _ _ m m' F2 MU WM A2)|].
split; [exact (fs_cls_rep_transport W _ _ _ m m' F3 MU WM A3)|].
split; [destruct F4 as (F4a & F4b & F4c); destruct A4 as (A4a & A4b & A4c);
split; [exact (fs_cls_rep_transport W _ _ _ m m' F4a MU WM A4a)|
split; [exact (fs_cls_rep_transport W _ _ _ m m' F4b MU WM A4b)| exact (fs_cls_rep_transport W _ _ _ m m' F4c MU WM A4c)]]|].
split; [rwc_lit A5|].
split; [exists dtvbeg; split; [exact Hdb|]|split; [exists tb, te; apply (rw_cells_transport bsegs W m m' _ _ TT MU WM); cs_size; exact A7|]].
2: { unfold fs_busy in *. apply Forall_forall. intros fk Hfk. destruct (proj1 (Forall_forall _ _) FB fk Hfk) as (p & Hp & W1 & W2 & Cw).
exists p. split; [exact Hp|]. split; [exact (wr_at_wmono m m' _ _ W1 WM)|]. split; [exact (wr_at_wmono m m' _ _ W2 WM)|].
apply (rw_cells_transport bsegs W m m' _ _ Cw MU WM). cs_size. exact (proj1 (Forall_forall _ _) A8 fk Hfk). }
split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|].
split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|].
split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|].
apply (rw_cells_transport bsegs W m m' _ _ D8 MU WM); cs_size; exact A6.
Qed.

Definition ia_lits : list (Z * Z) :=
[(g_ia_word, 4); (IAP, 1); (IAP + 8, 0x40000); (IAP + 0x40040, 0xd80); (IAP + 0x40dc0, 0x40248); (IAP + 0x81008, 40);
(0xfc0f8, 8); (0x195560, 8)].

Lemma ia_rep_transport : forall W Σ (m m' : mem), ia_rep Σ m -> munch W m m' -> wmono bsegs m m' -> dsjl W ia_lits -> ia_rep Σ m'.
Proof.
intros W Σ m m' (b & H) MU WM A. unfold ia_rep, ia_state in *. exists b. destruct b.
- destruct H as (W1 & MAP). split; [rwc_litX A W1|].
apply (u8arr_transport bsegs W m m' _ _ MAP MU WM). rewrite repeat_length. dsj_lit A.
- destruct H as (W1 & (j & J) & (b1 & L1 & B1) & (b2 & L2 & B2) & (b3 & L3 & B3) & (j4 & J4) & G & P).
split; [rwc_litX A W1|]. split; [exists j; rwc_litX A J|].
split; [exists b1; split; [exact L1|]; apply (u8arr_transport bsegs W m m' _ _ B1 MU WM); rewrite L1;
dsj_lit A|].
split; [exists b2; split; [exact L2|]; apply (u8arr_transport bsegs W m m' _ _ B2 MU WM); rewrite L2;
dsj_lit A|].
split; [exists b3; split; [exact L3|]; apply (u8arr_transport bsegs W m m' _ _ B3 MU WM); rewrite L3;
dsj_lit A|].
split; [exists j4; rwc_litX A J4|]. split; [rwc_litX A G | rwc_litX A P].
Qed.

Definition shadow_avoid (W : list ivl) (L : layoutA) : Prop :=
disjoint_from W (shad (l_ACEIL L)) (Z.max 0 ((2 ^ 47 - l_ACEIL L) / 8))

/\ Forall (fun r => disjoint_from W (shad (fst r)) (shad (snd r - 1) + 1 - shad (fst r))) CS_ACC.

Lemma acc_transport : forall W (m m' : mem) a n, acc bsegs m a n -> munch W m m' -> 0 < n ->
disjoint_from W (shad a) (shad (a + n - 1) + 1 - shad a) -> acc bsegs m' a n.
Proof.
intros W m m' a n H MU Hn D i Hi. destruct (H i Hi) as (b & Hb & Ho). exists b. split; [|exact Ho].
apply (bytes_at_transport bsegs W m m' _ _ Hb MU). cbn [length Z.of_nat].
apply (dsj_sub W (shad a) _ _ _ D); unfold shad; [apply Z.add_le_mono_r; apply Z.div_le_mono; lia|].
assert ((a + i) / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma stack_shadow_rep_transport : forall W L P (m m' : mem), stack_shadow_rep L P m -> munch W m m' ->
disjoint_from W (shad (l_ACEIL L)) (Z.max 0 ((2 ^ 47 - l_ACEIL L) / 8)) -> stack_shadow_rep L P m'.
Proof.
intros W L P m m' (M8 & Z0 & AC & WF) MU A. split; [exact M8|]. split; [|split; [|exact WF]].
- intros a Ha Hn. apply (bytes_at_transport bsegs W m m' _ _ (Z0 a Ha Hn) MU). cbn [length Z.of_nat].
apply Z.mod_divide in M8; [|lia]. destruct M8 as [q Hq].
assert (q <= a / 8) by (apply Z.div_le_lower_bound; lia). assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
apply (dsj_sub W (shad (l_ACEIL L)) _ _ _ A); unfold shad; rewrite Hq, ?Z.div_mul by lia; [lia|].
replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) by ring. rewrite Z.div_mul by lia. lia.
- apply Forall_forall. intros [a n] He. pose proof (proj1 (Forall_forall _ _) AC _ He) as X. pose proof (proj1 (Forall_forall _ _) (proj1 WF) _ He) as (W1 & W2 & W3 & W4).
cbn [fst snd] in *. unfold pz_lo, pz_hi in *. cbn [fst snd] in *. pose proof (alloca_rr_bounds a n) as (RB & _).
destruct (Z.eq_dec n 0) as [->|Hn0]; [intros i Hi; lia|].
apply (acc_transport W m m' _ _ X MU ltac:(lia)).
apply Z.mod_divide in M8; [|lia]. destruct M8 as [q Hq].
assert (q <= a / 8) by (apply Z.div_le_lower_bound; lia). assert ((a + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; unfold USTACK_TOP in *; lia).
apply (dsj_sub W (shad (l_ACEIL L)) _ _ _ A); unfold shad; rewrite Hq, ?Z.div_mul by lia; [lia|].
replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) by ring. rewrite Z.div_mul by lia. lia.
Qed.

Lemma shadow_rep_transport : forall W L P (m m' : mem), shadow_rep L P m -> munch W m m' -> wmono bsegs m m' -> shadow_avoid W L -> shadow_rep L P m'.
Proof.
intros W L P m m' (B & S1 & S2 & SA) MU WM (A & AS). split; [|split; [exact (stk_wmono m m' _ _ S1 WM) | split; [exact (stk_wmono m m' _ _ S2 WM)|]]].
- exact (stack_shadow_rep_transport W L P m m' B MU A).
- unfold static_acc in *. apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) SA r Hr) as X.
pose proof (proj1 (Forall_forall _ _) AS r Hr) as D. cbv beta in X, D.
assert (Hlh : fst r < snd r) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
apply (acc_transport W m m' _ _ X MU ltac:(lia)). replace (fst r + (snd r - fst r) - 1) with (snd r - 1) by lia. exact D.
Qed.

Definition consts_avoid (W : list ivl) (L : layoutA) : Prop := Forall (fun r => disjoint_from W (fst r) (snd r - fst r)) (consts_rngs L).

Lemma consts_rep_transport : forall W L (m m' : mem), consts_rep L m -> munch W m m' -> wmono bsegs m m' -> consts_avoid W L -> consts_rep L m'.
Proof.
intros W L m m' H MU WM A. apply (consts_rep_frame L m m' H); [|exact WM].
intros x Hx. apply MU. unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hx). cbv beta in Hx.
exact (disjoint_outside W (fst r) (snd r - fst r) (bv_unsigned x) (proj1 (Forall_forall _ _) A r Hr) ltac:(lia)).
Qed.

Definition art_avoid (W : list ivl) (Σ : rtsA) : Prop :=
consts_avoid W (lay Σ)
/\ (forall c, 1 <= c <= 31 -> reg_avoid W (l_SB (lay Σ)) c (pr Σ c) /\ pclass_avoid W (l_T (lay Σ)) c)
/\ (forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk_avoid W (l_SB (lay Σ)) c i st)
/\ (forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid W s)
/\ sec_avoid W Σ /\ quar_avoid W Σ /\ dep_avoid W (lay Σ) /\ fs_avoid W Σ /\ dsjl W ia_lits /\ shadow_avoid W (lay Σ).

Lemma ART_transport : forall W Σ (m m' : mem), ART_A Σ m -> munch W m m' -> wmono bsegs m m' -> art_avoid W Σ -> ART_A Σ m'.
Proof.
intros W Σ m m' H MU WM (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
pose proof (ART_wf Σ m H) as Hwf.
apply ART_intro; [exact Hwf | | | | | | | | | | |].
- exact (consts_rep_transport W _ m m' (ART_consts Σ m H) MU WM A1).
- intros c Hc. exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m H c Hc) MU WM (proj1 (A2 c Hc))).
- intros c Hc. exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m H c Hc) MU WM (proj2 (A2 c Hc))).
- destruct (ART_chunk Σ m H) as [P S]. split.
+ intros c i st Hc Hn. exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (A3 c i st Hc Hn)).
+ intros k s Hk. exact (schunk_transport W k s m m' (S k s Hk) MU WM (A4 k s Hk)).
- exact (sec_rep_transport W Σ m m' (ART_sec Σ m H) MU WM A5).
- exact (quar_rep_transport W Σ m m' (ART_quar Σ m H) MU WM A6).
- destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _).
exact (dep_rep_transport W _ _ m m' (ART_dep Σ m H) Hdok MU WM A7).
- exact (fs_rep_transport W Σ m m' (ART_fs Σ m H) MU WM A8).
- exact (ia_rep_transport W Σ m m' (ART_ia Σ m H) MU WM A9).
- exact (shadow_rep_transport W _ _ m m' (ART_shadow Σ m H) MU WM A10).
- exact (vis_rep_wmono _ m m' (ART_vis Σ m H) WM).
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma dsj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
induction W as [|[lo hi] W IH]; intros a n a' n' H H1 H2; cbn in *; [exact I|].
destruct H as [H3 H4]. split; [lia|]. exact (IH _ _ _ _ H4 H1 H2).
Qed.

Lemma dsj_app : forall W1 W2 a n, disjoint_from W1 a n -> disjoint_from W2 a n -> disjoint_from (W1 ++ W2) a n.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a n H1 H2; cbn in *; [exact H2|]. split; [exact (proj1 H1)| exact (IH _ _ _ (proj2 H1) H2)]. Qed.

Lemma dsj_app_inv : forall W1 W2 a n, disjoint_from (W1 ++ W2) a n -> disjoint_from W1 a n /\ disjoint_from W2 a n.
Proof.
induction W1 as [|[lo hi] W1 IH]; intros W2 a n H; cbn in *; [split; [exact I | exact H]|].
destruct H as [H1 H2]. destruct (IH _ _ _ H2) as [X Y]. split; [split; [exact H1 | exact X]| exact Y].
Qed.

Lemma dsj_of_outside : forall W a n, 0 < n -> Forall (fun p => fst p < snd p) W ->
(forall x, a <= x < a + n -> outside W x) -> disjoint_from W a n.
Proof.
induction W as [|[lo hi] W IH]; intros a n Hn HW H; cbn in *; [exact I|]. apply Forall_cons_iff in HW as [Hlh HW]. cbn [fst snd] in Hlh.
split.
- destruct (Z_le_dec (a + n) lo) as [X|X]; [left; exact X|]. destruct (Z_le_dec hi a) as [Y|Y]; [right; exact Y|].
exfalso. destruct (Z_le_dec lo a) as [Z2|Z2].
+ destruct (H a ltac:(lia)) as [U _]. apply U. lia.
+ destruct (H lo ltac:(lia)) as [U _]. apply U. lia.
- apply IH; [exact Hn | exact HW|]. intros x Hx. exact (proj2 (H x Hx)).
Qed.

Lemma outside_app : forall W1 W2 x, outside W1 x -> outside W2 x -> outside (W1 ++ W2) x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x H1 H2; cbn in *; [exact H2|]. split; [exact (proj1 H1)| exact (IH _ _ (proj2 H1) H2)]. Qed.

Lemma bytes_at_nil_any : forall (m : mem) a, 0 <= a <= 2 ^ 64 -> bytes_at asegs m a [].
Proof. intros m a Ha. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma farun_len : forall k, Z.of_nat (length (farun k)) = Z.max 0 k.
Proof. intros k. unfold farun. rewrite repeat_length. lia. Qed.
Lemma fdrun_len : forall k, Z.of_nat (length (fdrun k)) = Z.max 0 k.
Proof. intros k. unfold fdrun. rewrite repeat_length. lia. Qed.

Ltac cs_size := cbn [cells_size csize Nat.add length] in *.

Definition reg_avoid (W : list ivl) (SB c : Z) (r : regst) : Prop :=
let auser := ClassSize c * Z.of_nat (length (r_st r)) in
disjoint_from W (rinfo (RIS_of SB) c) 120 /\ disjoint_from W (fa SB c) (r_mfa r)
/\ disjoint_from W (shad (rb SB c + auser)) (Z.max 0 ((r_muser r - auser) / 8)).

Lemma reg_rep_transport : forall W SB c r (m m' : mem), reg_rep SB c r m -> munch W m m' -> wmono asegs m m' ->
reg_avoid W SB c r -> reg_rep SB c r m'.
Proof.
intros W SB c r m m' H MU WM (A1 & A2 & A3).
destruct H as (L & C & (rand & exh & pad & nal & nfr & r0 & r1 & r2 & r3 & T) & (ws & F & Hws & Hpre) & S1 & B & S2).
unfold ri_lock, ri_core, ri_tail in *.
split; [apply (rw_cells_transport asegs W m m' _ _ L MU WM); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
split; [apply (rw_cells_transport asegs W m m' _ _ C MU WM); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
split; [exists rand, exh, pad, nal, nfr, r0, r1, r2, r3; apply (rw_cells_transport asegs W m m' _ _ T MU WM); cs_size;
eapply dsj_sub; [exact A1| |]; lia|].
split; [exists ws; split; [|split; [exact Hws | exact Hpre]]; unfold fl_arr in *;
apply (u32arr_transport asegs W m m' _ _ F MU WM); rewrite Hws; exact A2|].
split; [exact (stk_wmono m m' _ _ S1 WM)|].
split; [apply (bytes_at_transport asegs W m m' _ _ B MU); rewrite farun_len; exact A3|].
exact (stk_wmono m m' _ _ S2 WM).
Qed.

Definition pclass_avoid (W : list ivl) (T c : Z) : Prop := disjoint_from W (pc_addr T c) 80.

Lemma pclass_rep_transport : forall W T c init l (m m' : mem), pclass_rep T c init l m -> munch W m m' -> wmono asegs m m' ->
pclass_avoid W T c -> pclass_rep T c init l m'.
Proof.
intros W T c init l m m' (P & chs & U & Hl & Hp) MU WM A. unfold pc_cells in *.
split; [apply (rw_cells_transport asegs W m m' _ _ P MU WM); cs_size; eapply dsj_sub; [exact A| |]; lia|].
exists chs. split; [|split; [exact Hl | exact Hp]]. apply (u32arr_transport asegs W m m' _ _ U MU WM). rewrite Hl.
eapply dsj_sub; [exact A| |]; lia.
Qed.

Definition pchunk_avoid (W : list ivl) (SB c : Z) (i : nat) (st : ckst) : Prop :=
let AB := p_abeg SB c i in let S := ClassSize c in
match st with
| CkIdle | CkBatch => disjoint_from W (shad AB) (Z.max 0 (S / 8))
| CkAlloc n =>
disjoint_from W (AB + rz_size n - 16) 16 /\ (16 < rz_size n -> disjoint_from W AB 16)
/\ disjoint_from W (shad AB) (Z.of_nat (length (farun (rz_size n / 8) ++ ushadow n)))
/\ disjoint_from W (shad (AB + rz_size n + ru8 n)) (Z.max 0 ((S - rz_size n - ru8 n) / 8))
| CkQuar n =>
disjoint_from W (AB + rz_size n - 16) 24 /\ (16 < rz_size n -> disjoint_from W AB 16)
/\ disjoint_from W (shad AB) (Z.of_nat (length (farun (rz_size n / 8) ++ fdrun (ru8 n / 8) ++ farun ((S - rz_size n - ru8 n) / 8))))
end.

Lemma ahdr_transport : forall W (m m' : mem) M n, ahdr m M n -> munch W m m' -> wmono asegs m m' -> disjoint_from W M 16 -> ahdr m' M n.
Proof.
intros W m m' M n (b1 & ctx & Hb & H) MU WM A. exists b1, ctx. split; [exact Hb|].
apply (rw_cells_transport asegs W m m' _ _ H MU WM). cs_size. exact A.
Qed.
Lemma qhdr3_transport : forall W (m m' : mem) M n, qhdr3 m M n -> munch W m m' -> wmono asegs m m' -> disjoint_from W M 24 -> qhdr3 m' M n.
Proof.
intros W m m' M n (b1 & ctx & fid & Hb & H) MU WM A. exists b1, ctx, fid. split; [exact Hb|].
apply (rw_cells_transport asegs W m m' _ _ H MU WM). cs_size. exact A.
Qed.
Lemma lch_transport : forall W (m m' : mem) AB M, lch m AB M -> munch W m m' -> wmono asegs m m' -> disjoint_from W AB 16 -> lch m' AB M.
Proof. intros W m m' AB M H MU WM A. apply (rw_cells_transport asegs W m m' _ _ H MU WM). cs_size. exact A. Qed.

Lemma pchunk_transport : forall W SB c i st (m m' : mem), pchunk SB c i st m -> munch W m m' -> wmono asegs m m' ->
pchunk_avoid W SB c i st -> pchunk SB c i st m'.
Proof.
intros W SB c i st m m' H MU WM A. unfold pchunk, pchunk_avoid in *. destruct st as [|n|n|].
- destruct H as [S B]. split; [exact (stk_wmono m m' _ _ S WM)|]. unfold pshadow_idle in *.
apply (bytes_at_transport asegs W m m' _ _ B MU). rewrite farun_len. exact A.
- destruct H as (Wr & Hh & Hl & B1 & B2). destruct A as (A1 & A2 & A3 & A4).
split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (ahdr_transport W m m' _ _ Hh MU WM A1)|].
split; [intros Hr; exact (lch_transport W m m' _ _ (Hl Hr) MU WM (A2 Hr))|].
split; [apply (bytes_at_transport asegs W m m' _ _ B1 MU); exact A3|].
apply (bytes_at_transport asegs W m m' _ _ B2 MU). rewrite farun_len. exact A4.
- destruct H as (Wr & Hh & Hl & B1). destruct A as (A1 & A2 & A3).
split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (qhdr3_transport W m m' _ _ Hh MU WM A1)|].
split; [intros Hr; exact (lch_transport W m m' _ _ (Hl Hr) MU WM (A2 Hr))|].
unfold pshadow_quar in *. apply (bytes_at_transport asegs W m m' _ _ B1 MU). exact A3.
- unfold pshadow_idle in *. apply (bytes_at_transport asegs W m m' _ _ H MU). rewrite farun_len. exact A.
Qed.

Definition schunk_avoid (W : list ivl) (s : secst) : Prop :=
let mb := s_mb s in let msz := smsz (s_n s) in let AB := mb + 4096 in let M := AB + 2032 in let n := s_n s in
disjoint_from W mb 32 /\ disjoint_from W AB 16 /\ disjoint_from W M (if s_quar s then 24 else 16)
/\ disjoint_from W (shad mb) (Z.max 0 ((4096 + 2048) / 8))
/\ disjoint_from W (shad (AB + 2048)) (Z.of_nat (length (if s_quar s then fdrun (ru8 n / 8) else ushadow n)))
/\ disjoint_from W (shad (AB + 2048 + ru8 n)) (Z.max 0 ((msz - 4096 - 2048 - ru8 n) / 8)).

Lemma schunk_transport : forall W k s (m m' : mem), schunk k s m -> munch W m m' -> wmono asegs m m' ->
schunk_avoid W s -> schunk k s m'.
Proof.
intros W k s m m' H MU WM (A1 & A2 & A3 & A4 & A5 & A6). unfold schunk in *.
destruct H as (Hs & Wr & Hl & Hh & S & B1 & B2 & B3).
split; [unfold shdr in *; apply (rw_cells_transport asegs W m m' _ _ Hs MU WM); cs_size; exact A1|].
split; [exact (wr_at_wmono m m' _ _ Wr WM)|]. split; [exact (lch_transport W m m' _ _ Hl MU WM A2)|].
split; [destruct (s_quar s); [exact (qhdr3_transport W m m' _ _ Hh MU WM A3) | exact (ahdr_transport W m m' _ _ Hh MU WM A3)]|].
split; [exact (stk_wmono m m' _ _ S WM)|].
split; [apply (bytes_at_transport asegs W m m' _ _ B1 MU); rewrite farun_len; exact A4|].
split; [apply (bytes_at_transport asegs W m m' _ _ B2 MU); exact A5|].
apply (bytes_at_transport asegs W m m' _ _ B3 MU). rewrite farun_len. exact A6.
Qed.

Definition dsjl (W : list ivl) (l : list (Z * Z)) : Prop := Forall (fun r => disjoint_from W (fst r) (snd r)) l.
Lemma dsjl_in : forall W l a n, dsjl W l -> In (a, n) l -> disjoint_from W a n.
Proof. intros W l a n H Hin. exact (proj1 (Forall_forall _ _) H (a, n) Hin). Qed.
Ltac in_lit := repeat (first [ left; reflexivity | right ]).

Ltac dsj_lit H := match goal with |- disjoint_from ?W ?a ?n => eapply (dsj_sub W a _ a n); [eapply (dsjl_in _ _ a _ H); in_lit | lia | lia] end.
Ltac rwc_lit H := eapply rw_cells_transport; [eassumption | eassumption | eassumption |]; cs_size; dsj_lit H.

Ltac rwc_litX H X := eapply (rw_cells_transport asegs _ _ _ _ _ X); [eassumption | eassumption |]; cs_size; dsj_lit H.

Definition sec_lits : list (Z * Z) :=
[(i_sec_chunks, 8); (i_sec_nres, 16); (i_sec_mutex, 1); (i_sec_mutex + 1, 3); (i_sec_page, 8); (i_sec_range, 8); (i_sec_sorted, 40);
(i_sec_bylog, 512); (i_gstat_alloc, 16); (0xf3880, 8); (0xf57f8, 8)].
Definition sec_avoid (W : list ivl) (Σ : rtsA) : Prop := dsjl W sec_lits /\ disjoint_from W (l_PAB (lay Σ)) (8 * sec_nres Σ).

Lemma sec_rep_transport : forall W Σ (m m' : mem), sec_rep Σ m -> munch W m m' -> wmono asegs m m' -> sec_avoid W Σ -> sec_rep Σ m'.
Proof.
intros W Σ m m' H MU WM (A & AP). unfold sec_rep, sec_core, sec_pad, sec_page, sec_range, sec_junk, name_cells in *.
destruct H as ((C1 & C2 & C3) & P & (ws & U & Hl & Hf) & G & R & ((b & j & w1 & w2 & w3 & w4 & J1) & (bl & Hbl & J2) & (ga & gm & J3)) & N1 & N2).
split; [split; [rwc_lit A | split; [rwc_lit A | rwc_lit A]]|].
split; [rwc_lit A|].
split; [exists ws; split; [|split; [exact Hl | exact Hf]]; apply (u64arr_transport asegs W m m' _ _ U MU WM); rewrite Hl; exact AP|].
split; [rwc_lit A|]. split; [rwc_lit A|].
split; [split; [exists b, j, w1, w2, w3, w4; rwc_lit A | split; [exists bl; split; [exact Hbl|] | exists ga, gm; rwc_lit A]]|].
- apply (u64arr_transport asegs W m m' _ _ J2 MU WM). rewrite Hbl. dsj_lit A.
- split; rwc_lit A.
Qed.

Definition quar_avoid (W : list ivl) (Σ : rtsA) : Prop :=
disjoint_from W (qcacheT (l_T (lay Σ))) 32 /\ dsjl W [(i_q_global, 32); (i_q_cmutex, 4)]
/\ Forall (fun b => disjoint_from W (fst b) 8192) (ql Σ ++ qg Σ).

Lemma qchain_transport : forall W (m m' : mem) bs, qchain m bs -> munch W m m' -> wmono asegs m m' ->
Forall (fun b => disjoint_from W (fst b) 8192) bs -> qchain m' bs.
Proof.
intros W m m' bs. induction bs as [|[b ents] bs IH]; intros H MU WM A; [exact I|].
apply Forall_cons_iff in A as [A1 A2]. cbn [fst] in A1. destruct H as [(H1 & (ws & U & Hl & Hf) & Hn) H2].
split; [|exact (IH H2 MU WM A2)]. split; [apply (rw_cells_transport asegs W m m' _ _ H1 MU WM); cs_size; eapply dsj_sub; [exact A1| |]; lia|].
split; [|exact Hn]. exists ws. split; [|split; [exact Hl | exact Hf]]. apply (u64arr_transport asegs W m m' _ _ U MU WM).
rewrite Hl. eapply dsj_sub; [exact A1| |]; lia.
Qed.

Lemma quar_rep_transport : forall W Σ (m m' : mem), quar_rep Σ m -> munch W m m' -> wmono asegs m m' -> quar_avoid W Σ -> quar_rep Σ m'.
Proof.
intros W Σ m m' ((Q1 & C1) & (Q2 & C2) & X) MU WM (A1 & A2 & A3). apply Forall_app in A3 as [A3 A4].
split; [split; [apply (rw_cells_transport asegs W m m' _ _ Q1 MU WM); cs_size; exact A1 | exact (qchain_transport W m m' _ C1 MU WM A3)]|].
split; [split; [rwc_lit A2 | exact (qchain_transport W m m' _ C2 MU WM A4)]|]. rwc_lit A2.
Qed.

Definition dep_avoid (W : list ivl) (L : layoutA) : Prop :=
dsjl W [(0x1df158, 0x5df158 + 4 - 0x1df158); (0x5df168, 8); (0x1cf148, 8); (0x1cf158, 0x1cf160 + 4 - 0x1cf158)]
/\ disjoint_from W (l_DNB L) (2 ^ 20) /\ disjoint_from W (l_SSB L) (2 ^ 23).

Lemma dep_rep_transport : forall W L d (m m' : mem), dep_rep L d m -> depot_ok d (l_DNB L) (l_SSB L) (l_ACEIL L) ->
munch W m m' -> wmono asegs m m' -> dep_avoid W L -> dep_rep L d m'.
Proof.
intros W L d m m' H OK MU WM (A & A5 & A6). unfold dep_rep in *.
apply (depot_rep_frame d _ _ _ _ W m m' H OK MU WM); [exact (dsjl_in _ _ 0x1df158 _ A ltac:(in_lit)) | exact (dsjl_in _ _ 0x5df168 _ A ltac:(in_lit)) | exact A5
| exact (dsjl_in _ _ 0x1cf148 _ A ltac:(in_lit)) | exact (dsjl_in _ _ 0x1cf158 _ A ltac:(in_lit)) | exact A6].
Qed.

Definition fs_lits : list (Z * Z) :=
[(tpA, 8); (0xfdf58, 1); (g_real_tls_get_addr, 8); (g_dtv_ptr, 8); (g_dtv1, 8); (g_got_common_flags, 8);
(g_intercept_tls_get_addr, 1); (g_got_verbosity, 8); (g_current_verbosity, 4); (g_tls_index, 16); (g_got_dtls_off, 8);
(g_tls_dtls, 8)].
Definition fs_cls_avoid (W : list ivl) (FSB c : Z) (f : fsst) : Prop :=
disjoint_from W (FSB + 8 * c) 8 /\ disjoint_from W (fl_base FSB c) (Z.of_nat (length (fss_flags f)))
/\ (forall p, 0 <= p < NF c -> nth (Z.to_nat p) (fss_flags f) 1 = 0 ->
disjoint_from W (frame_addr FSB c p) (fsz c) /\ disjoint_from W (shad (frame_addr FSB c p)) (fsz c / 8)).
Definition fs_avoid (W : list ivl) (Σ : rtsA) : Prop :=
let L := lay Σ in
disjoint_from W (l_FSB L + 0x58) 9 /\ fs_cls_avoid W (l_FSB L) 0 (fs0 Σ) /\ fs_cls_avoid W (l_FSB L) 2 (fs2 Σ)
/\ (fs_cls_avoid W (l_FSB L) 4 (fs4 Σ) /\ fs_cls_avoid W (l_FSB L) 5 (fsc Σ 5%nat) /\ fs_cls_avoid W (l_FSB L) 8 (fsc Σ 8%nat)) /\ dsjl W fs_lits /\ disjoint_from W (l_DTV L + 24) 8 /\ disjoint_from W (l_T L + 48) 16
/\ Forall (fun fk => disjoint_from W (fst fk + fs_size (snd fk) - 8) 8) (frames Σ).

Lemma fs_cls_rep_transport : forall W FSB c f (m m' : mem), fs_cls_rep FSB c f m -> munch W m m' -> wmono asegs m m' ->
fs_cls_avoid W FSB c f -> fs_cls_rep FSB c f m'.
Proof.
intros W FSB c f m m' (H1 & H2 & H3) MU WM (A1 & A2 & A3). unfold fs_hint, fs_flags in *.
split; [apply (rw_cells_transport asegs W m m' _ _ H1 MU WM); cs_size; exact A1|].
split; [apply (u8arr_transport asegs W m m' _ _ H2 MU WM); rewrite length_map; exact A2|].
exact (fs_free_frames_transport FSB c m m' _ W H3 MU WM A3).
Qed.

Lemma fs_rep_transport : forall W Σ (m m' : mem), fs_rep Σ m -> munch W m m' -> wmono asegs m m' -> fs_avoid W Σ -> fs_rep Σ m'.
Proof.
intros W Σ m m' H MU WM (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). unfold fs_rep, fs_const, tga_cells, dtls_cells, ttls_cells in *.
destruct H as (F1 & F2 & F3 & F4 & T & (dtvbeg & Hdb & (G1 & G2 & G3 & G4 & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8))) & (tb & te & TT) & FB).
split; [apply (rw_cells_transport asegs W m m' _ _ F1 MU WM); cs_size; exact A1|].
split; [exact (fs_cls_rep_transport W _ _ _ m m' F2 MU WM A2)|].
split; [exact (fs_cls_rep_transport W _ _ _ m m' F3 MU WM A3)|].
split; [destruct F4 as (F4a & F4b & F4c); destruct A4 as (A4a & A4b & A4c);
split; [exact (fs_cls_rep_transport W _ _ _ m m' F4a MU WM A4a)|
split; [exact (fs_cls_rep_transport W _ _ _ m m' F4b MU WM A4b)| exact (fs_cls_rep_transport W _ _ _ m m' F4c MU WM A4c)]]|].
split; [rwc_lit A5|].
split; [exists dtvbeg; split; [exact Hdb|]|split; [exists tb, te; apply (rw_cells_transport asegs W m m' _ _ TT MU WM); cs_size; exact A7|]].
2: { unfold fs_busy in *. apply Forall_forall. intros fk Hfk. destruct (proj1 (Forall_forall _ _) FB fk Hfk) as (p & Hp & W1 & W2 & Cw).
exists p. split; [exact Hp|]. split; [exact (wr_at_wmono m m' _ _ W1 WM)|]. split; [exact (wr_at_wmono m m' _ _ W2 WM)|].
apply (rw_cells_transport asegs W m m' _ _ Cw MU WM). cs_size. exact (proj1 (Forall_forall _ _) A8 fk Hfk). }
split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|].
split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|].
split; [rwc_lit A5|]. split; [rwc_lit A5|]. split; [rwc_lit A5|].
apply (rw_cells_transport asegs W m m' _ _ D8 MU WM); cs_size; exact A6.
Qed.

Definition ia_lits : list (Z * Z) :=
[(g_ia_word, 4); (IAP, 1); (IAP + 8, 0x40000); (IAP + 0x40040, 0xd80); (IAP + 0x40dc0, 0x40248); (IAP + 0x81008, 40);
(0xf3878, 8); (0x18cd20, 8)].

Lemma ia_rep_transport : forall W Σ (m m' : mem), ia_rep Σ m -> munch W m m' -> wmono asegs m m' -> dsjl W ia_lits -> ia_rep Σ m'.
Proof.
intros W Σ m m' (b & H) MU WM A. unfold ia_rep, ia_state in *. exists b. destruct b.
- destruct H as (W1 & MAP). split; [rwc_litX A W1|].
apply (u8arr_transport asegs W m m' _ _ MAP MU WM). rewrite repeat_length. dsj_lit A.
- destruct H as (W1 & (j & J) & (b1 & L1 & B1) & (b2 & L2 & B2) & (b3 & L3 & B3) & (j4 & J4) & G & P).
split; [rwc_litX A W1|]. split; [exists j; rwc_litX A J|].
split; [exists b1; split; [exact L1|]; apply (u8arr_transport asegs W m m' _ _ B1 MU WM); rewrite L1;
dsj_lit A|].
split; [exists b2; split; [exact L2|]; apply (u8arr_transport asegs W m m' _ _ B2 MU WM); rewrite L2;
dsj_lit A|].
split; [exists b3; split; [exact L3|]; apply (u8arr_transport asegs W m m' _ _ B3 MU WM); rewrite L3;
dsj_lit A|].
split; [exists j4; rwc_litX A J4|]. split; [rwc_litX A G | rwc_litX A P].
Qed.

Definition shadow_avoid (W : list ivl) (L : layoutA) : Prop :=
disjoint_from W (shad (l_ACEIL L)) (Z.max 0 ((2 ^ 47 - l_ACEIL L) / 8))

/\ Forall (fun r => disjoint_from W (shad (fst r)) (shad (snd r - 1) + 1 - shad (fst r))) CS_ACC.

Lemma acc_transport : forall W (m m' : mem) a n, acc asegs m a n -> munch W m m' -> 0 < n ->
disjoint_from W (shad a) (shad (a + n - 1) + 1 - shad a) -> acc asegs m' a n.
Proof.
intros W m m' a n H MU Hn D i Hi. destruct (H i Hi) as (b & Hb & Ho). exists b. split; [|exact Ho].
apply (bytes_at_transport asegs W m m' _ _ Hb MU). cbn [length Z.of_nat].
apply (dsj_sub W (shad a) _ _ _ D); unfold shad; [apply Z.add_le_mono_r; apply Z.div_le_mono; lia|].
assert ((a + i) / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma stack_shadow_rep_transport : forall W L P (m m' : mem), stack_shadow_rep L P m -> munch W m m' ->
disjoint_from W (shad (l_ACEIL L)) (Z.max 0 ((2 ^ 47 - l_ACEIL L) / 8)) -> stack_shadow_rep L P m'.
Proof.
intros W L P m m' (M8 & Z0 & AC & WF) MU A. split; [exact M8|]. split; [|split; [|exact WF]].
- intros a Ha Hn. apply (bytes_at_transport asegs W m m' _ _ (Z0 a Ha Hn) MU). cbn [length Z.of_nat].
apply Z.mod_divide in M8; [|lia]. destruct M8 as [q Hq].
assert (q <= a / 8) by (apply Z.div_le_lower_bound; lia). assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
apply (dsj_sub W (shad (l_ACEIL L)) _ _ _ A); unfold shad; rewrite Hq, ?Z.div_mul by lia; [lia|].
replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) by ring. rewrite Z.div_mul by lia. lia.
- apply Forall_forall. intros [a n] He. pose proof (proj1 (Forall_forall _ _) AC _ He) as X. pose proof (proj1 (Forall_forall _ _) (proj1 WF) _ He) as (W1 & W2 & W3 & W4).
cbn [fst snd] in *. unfold pz_lo, pz_hi in *. cbn [fst snd] in *. pose proof (alloca_rr_bounds a n) as (RB & _).
destruct (Z.eq_dec n 0) as [->|Hn0]; [intros i Hi; lia|].
apply (acc_transport W m m' _ _ X MU ltac:(lia)).
apply Z.mod_divide in M8; [|lia]. destruct M8 as [q Hq].
assert (q <= a / 8) by (apply Z.div_le_lower_bound; lia). assert ((a + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; unfold USTACK_TOP in *; lia).
apply (dsj_sub W (shad (l_ACEIL L)) _ _ _ A); unfold shad; rewrite Hq, ?Z.div_mul by lia; [lia|].
replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) by ring. rewrite Z.div_mul by lia. lia.
Qed.

Lemma shadow_rep_transport : forall W L P (m m' : mem), shadow_rep L P m -> munch W m m' -> wmono asegs m m' -> shadow_avoid W L -> shadow_rep L P m'.
Proof.
intros W L P m m' (B & S1 & S2 & SA) MU WM (A & AS). split; [|split; [exact (stk_wmono m m' _ _ S1 WM) | split; [exact (stk_wmono m m' _ _ S2 WM)|]]].
- exact (stack_shadow_rep_transport W L P m m' B MU A).
- unfold static_acc in *. apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) SA r Hr) as X.
pose proof (proj1 (Forall_forall _ _) AS r Hr) as D. cbv beta in X, D.
assert (Hlh : fst r < snd r) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
apply (acc_transport W m m' _ _ X MU ltac:(lia)). replace (fst r + (snd r - fst r) - 1) with (snd r - 1) by lia. exact D.
Qed.

Definition consts_avoid (W : list ivl) (L : layoutA) : Prop := Forall (fun r => disjoint_from W (fst r) (snd r - fst r)) (consts_rngs L).

Lemma consts_rep_transport : forall W L (m m' : mem), consts_rep L m -> munch W m m' -> wmono asegs m m' -> consts_avoid W L -> consts_rep L m'.
Proof.
intros W L m m' H MU WM A. apply (consts_rep_frame L m m' H); [|exact WM].
intros x Hx. apply MU. unfold in_rngs in Hx. apply Exists_exists in Hx as (r & Hr & Hx). cbv beta in Hx.
exact (disjoint_outside W (fst r) (snd r - fst r) (bv_unsigned x) (proj1 (Forall_forall _ _) A r Hr) ltac:(lia)).
Qed.

Definition art_avoid (W : list ivl) (Σ : rtsA) : Prop :=
consts_avoid W (lay Σ)
/\ (forall c, 1 <= c <= 31 -> reg_avoid W (l_SB (lay Σ)) c (pr Σ c) /\ pclass_avoid W (l_T (lay Σ)) c)
/\ (forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk_avoid W (l_SB (lay Σ)) c i st)
/\ (forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid W s)
/\ sec_avoid W Σ /\ quar_avoid W Σ /\ dep_avoid W (lay Σ) /\ fs_avoid W Σ /\ dsjl W ia_lits /\ shadow_avoid W (lay Σ).

Lemma ART_transport : forall W Σ (m m' : mem), ART_A Σ m -> munch W m m' -> wmono asegs m m' -> art_avoid W Σ -> ART_A Σ m'.
Proof.
intros W Σ m m' H MU WM (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
pose proof (ART_wf Σ m H) as Hwf.
apply ART_intro; [exact Hwf | | | | | | | | | | |].
- exact (consts_rep_transport W _ m m' (ART_consts Σ m H) MU WM A1).
- intros c Hc. exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m H c Hc) MU WM (proj1 (A2 c Hc))).
- intros c Hc. exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m H c Hc) MU WM (proj2 (A2 c Hc))).
- destruct (ART_chunk Σ m H) as [P S]. split.
+ intros c i st Hc Hn. exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (A3 c i st Hc Hn)).
+ intros k s Hk. exact (schunk_transport W k s m m' (S k s Hk) MU WM (A4 k s Hk)).
- exact (sec_rep_transport W Σ m m' (ART_sec Σ m H) MU WM A5).
- exact (quar_rep_transport W Σ m m' (ART_quar Σ m H) MU WM A6).
- destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _).
exact (dep_rep_transport W _ _ m m' (ART_dep Σ m H) Hdok MU WM A7).
- exact (fs_rep_transport W Σ m m' (ART_fs Σ m H) MU WM A8).
- exact (ia_rep_transport W Σ m m' (ART_ia Σ m H) MU WM A9).
- exact (shadow_rep_transport W _ _ m m' (ART_shadow Σ m H) MU WM A10).
- exact (vis_rep_wmono _ m m' (ART_vis Σ m H) WM).
Qed.
