(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the call of send_message in LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, jal at 0x86714, back at 0x86718), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v:122-290 (a program call through cl_callS, the callee's statement applied, the caller's facts carried past it). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s30.v, with its module paths and module names changed; 622 of its 671 lines of code are new or changed and 292 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s20k.v, with its module paths and module names changed; 789 of its 861 lines of code are new or changed and 599 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of segment S06 of the
   walk of the test harness's entry function LLVMFuzzerTestOneInput (0x85208 .. 0x853b8, the inlined m_cross loop
   0x8523c <- 0x85330 with its two m_refuse calls, fuzz_segconf.c:296-310).

   rule 24: proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c
   origin/ossv/recipes@3abc3740de97 origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4
   / the stream's proof index LLVMFuzzerTestOneInput + four-ref git grep; output pasted verbatim in
   the walk's shared brief; checker (fresh, read-only): CONFIRM; none: written new).
   This file holds the parts of the walk that do not run code; LLVMFuzzerTestOneInput_s16.v holds the runs.

   - The model: the loop after i passes holds fold_left m_cross_seg (seq 0 i) of the last turn's m_file result
     (s16_Mi, s16_step); its table keeps its length, gen and overflow, and refused grows by at most one per pass;
     over the drop-in turns of seg_run refused grows by at most 65535 a turn (m_file_c.m_file_refused), so
     m_refuse's room (s16_refuse_room) holds at every pass and K853bc's lt_cnt holds after m_cross (s16_cnt_exit).
   - The memory: the 4-byte fields of m->seg[i] and m->n through the reader (s16_rd_n, s16_rd_role, ...), and
     struct mconf after the loop's `sw zero` stores: model_set = 0 (0x852d4) holds m_upd mc i ms_drop_model,
     role_set = 0 then role = 0 (0x852f8, 0x85304) hold m_upd mc i ms_drop_role (s16_mconf_drop_model,
     s16_mconf_drop_role). The byte-list part follows the plain / UBSan owner's plain lib/Prog/Seg/L02W_mx.v
     (commit 260365aea42b), restated over the reader.
   - The inner cuts of the loop, each a statement over K85208's premises with m holding the model so far
     (s16_inv, or s16_inv0 for K85208's own form): LT16_KH_stmt (0x8523c, the head of pass i), LT16_KL_stmt
     (0x85310, its latch), LT16_KP1_stmt / LT16_KP2_stmt (0x852c0 / 0x852f0, after the two m_refuse calls).
   - The carry of the cut's facts across a state change that writes only m's block, m_refuse's stack window and
     112(s1) (s16_inv_carry0, s16_inv_carry), and the m_refuse(m, 0) call itself through PaFx.v's cl_callSF with
     m_refuse's contract (s16_call; the callee returns at an FP state of its own). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0f YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YN01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_file_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ================================= the model ================================= *)
Lemma s16_in_ok : forall inp, Forall byte_ok (seg_in inp).
Proof.
intros inp. unfold seg_in, zs. apply Forall_map, Forall_forall. intros b _. unfold byte_ok.
pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.
(* every turn's text: NUL-free and at most 65535 bytes (decode_ok; past the last file the default empty file) *)
Lemma s16_txt_ok : forall inp k, nulfree (seg_txt inp k) /\ Z.of_nat (length (seg_txt inp k)) <= 65535.
Proof.
intros inp k. unfold seg_txt, seg_file, seg_files, seg_pay.
destruct (Nat.lt_ge_cases k (length (p_files (decode (seg_in inp))))) as [H|H].
- pose proof (proj1 (decode_ok (seg_in inp) (s16_in_ok inp))) as HF. rewrite Forall_forall in HF.
  destruct (HF _ (nth_In _ (File 0 []) H)) as (Hn & Hl & _). split; assumption.
- rewrite nth_overflow by exact H. cbn [f_text length Z.of_nat]. split; [apply nulfree_nil | lia].
Qed.
(* seg_run's turns are all drop-ins: refused grows by at most a text's length a turn *)
Lemma s16_run_refused : forall inp f, 0 <= mc_refused (seg_mc (seg_run inp f)) <= 65535 * Z.of_nat f.
Proof.
intros inp f. induction f as [|f IH]; [cbn; lia|].
cbn [seg_run]. revert IH. unfold seg_turn_step.
destruct (seg_run inp f) as [[c mc] ret]. cbn [seg_mc fst snd]. intros IH.
destruct (r_parse_file c (seg_txt inp f) (seg_label inp f)) as [c1 n]. cbn [seg_mc fst snd].
destruct (s16_txt_ok inp f) as [Hn Hl].
pose proof (m_file_c.m_file_refused mc (seg_txt inp f) (seg_label inp f) Hn). lia.
Qed.
(* the last turn's m_file result, the model the loop starts from *)
Definition s16_M1 (inp : list byte) (f : nat) : mconf := m_file (seg_mc (seg_run inp f)) (seg_txt inp f) None.
Lemma s16_M1_refused : forall inp f, 0 <= mc_refused (s16_M1 inp f) <= 65535 * Z.of_nat (S f).
Proof.
intros inp f. unfold s16_M1. destruct (s16_txt_ok inp f) as [Hn Hl].
pose proof (m_file_c.m_file_refused (seg_mc (seg_run inp f)) (seg_txt inp f) None Hn).
pose proof (s16_run_refused inp f). lia.
Qed.

(* the passes of m_cross *)
Lemma s16_upd_nth_length : forall {A} i (f : A -> A) l, length (upd_nth i f l) = length l.
Proof. intros A i f l. revert i. induction l as [|x l IH]; intros [|i]; cbn [upd_nth length]; auto. Qed.
Lemma s16_upd_nth_nth : forall {A} i j (f : A -> A) l d, (i < length l)%nat ->
  nth j (upd_nth i f l) d = if Nat.eqb j i then f (nth i l d) else nth j l d.
Proof.
intros A i j f l d. revert i j. induction l as [|x l IH]; intros i j Hi; cbn [length] in Hi; [lia|].
destruct i as [|i], j as [|j]; cbn [upd_nth nth Nat.eqb]; try reflexivity.
apply IH. lia.
Qed.
Lemma s16_seg_cases : forall c i,
  m_cross_seg c i = m_upd (m_refuse c 0 false) i ms_drop_model \/
  m_cross_seg c i = m_upd (m_refuse c 0 false) i ms_drop_role \/ m_cross_seg c i = c.
Proof.
intros c i. unfold m_cross_seg. cbv zeta.
match goal with |- context [if ?b then _ else _] => destruct b end; [left; reflexivity|].
match goal with |- context [if ?b then _ else _] => destruct b end; [right; left; reflexivity|].
right; right; reflexivity.
Qed.
Lemma s16_seg_len : forall c i, length (mc_seg (m_cross_seg c i)) = length (mc_seg c).
Proof.
intros c i. destruct (s16_seg_cases c i) as [E|[E|E]]; rewrite E; cbn [m_upd m_set_segs m_refuse mc_seg];
  rewrite ?s16_upd_nth_length; reflexivity.
Qed.
Lemma s16_seg_cnt : forall c i,
  mc_gen (m_cross_seg c i) = mc_gen c /\ mc_overflow (m_cross_seg c i) = mc_overflow c /\
  mc_refused c <= mc_refused (m_cross_seg c i) <= mc_refused c + 1.
Proof.
intros c i. destruct (s16_seg_cases c i) as [E|[E|E]]; rewrite E; cbn [m_upd m_set_segs m_refuse mc_gen
  mc_overflow mc_refused]; lia.
Qed.
Definition s16_Mi (m1 : mconf) (i : nat) : mconf := fold_left m_cross_seg (seq 0 i) m1.
Lemma s16_step : forall m1 i, s16_Mi m1 (S i) = m_cross_seg (s16_Mi m1 i) i.
Proof. intros m1 i. unfold s16_Mi. rewrite seq_S, fold_left_app. reflexivity. Qed.
Lemma s16_Mi_len : forall m1 i, length (mc_seg (s16_Mi m1 i)) = length (mc_seg m1).
Proof. intros m1 i. induction i as [|i IH]; [reflexivity|]. rewrite s16_step, s16_seg_len. exact IH. Qed.
Lemma s16_Mi_cnt : forall m1 i,
  mc_gen (s16_Mi m1 i) = mc_gen m1 /\ mc_overflow (s16_Mi m1 i) = mc_overflow m1 /\
  mc_refused m1 <= mc_refused (s16_Mi m1 i) <= mc_refused m1 + Z.of_nat i.
Proof.
intros m1 i. induction i as [|i IH]; [cbn; lia|].
rewrite s16_step. pose proof (s16_seg_cnt (s16_Mi m1 i) i). lia.
Qed.
Lemma s16_Mi_all : forall m1, s16_Mi m1 (length (mc_seg m1)) = m_cross m1.
Proof. reflexivity. Qed.
(* the room m_refuse asks at every pass: refused + 1 < 2 ^ 32 *)
Lemma s16_refuse_room : forall inp f i, (f < 4)%nat -> (i <= 32)%nat ->
  mc_refused (s16_Mi (s16_M1 inp f) i) + 1 < 2 ^ 32.
Proof.
intros inp f i Hf Hi. pose proof (s16_M1_refused inp f). pose proof (s16_Mi_cnt (s16_M1 inp f) i). lia.
Qed.
(* K853bc's counters after the whole of m_cross *)
Lemma s16_cnt_exit : forall inp f rc0, (length (mc_seg (s16_M1 inp f)) <= 32)%nat ->
  rc_gen rc0 <= Z.of_nat (S f) /\ rc_refused rc0 <= Z.of_nat (S f) * 2 ^ 20 /\
  rc_overflow rc0 <= Z.of_nat (S f) * 2 ^ 20 /\
  mc_gen (s16_M1 inp f) <= Z.of_nat (S f) /\ mc_refused (s16_M1 inp f) <= Z.of_nat (S f) * 2 ^ 20 /\
  mc_overflow (s16_M1 inp f) <= Z.of_nat (S f) * 2 ^ 20 ->
  rc_gen rc0 <= Z.of_nat (S f) /\ rc_refused rc0 <= Z.of_nat (S f) * 2 ^ 20 /\
  rc_overflow rc0 <= Z.of_nat (S f) * 2 ^ 20 /\
  mc_gen (m_cross (s16_M1 inp f)) <= Z.of_nat (S f) /\
  mc_refused (m_cross (s16_M1 inp f)) <= Z.of_nat (S f) * 2 ^ 20 /\
  mc_overflow (m_cross (s16_M1 inp f)) <= Z.of_nat (S f) * 2 ^ 20.
Proof.
intros inp f rc0 HL (H1 & H2 & H3 & H4 & H5 & H6).
rewrite <- s16_Mi_all. pose proof (s16_Mi_cnt (s16_M1 inp f) (length (mc_seg (s16_M1 inp f)))) as (G & O & R).
pose proof (s16_M1_refused inp f) as RM. rewrite G, O.
repeat split; try lia.
Qed.

(* ============================ struct mconf through the reader ============================ *)
Lemma s16_fld_fld : forall (bs : list byte) a n b k, (b + k <= n)%nat -> fld b k (fld a n bs) = fld (a + b) k bs.
Proof.
intros bs a n b k H. unfold fld. rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
rewrite Nat.min_l by lia. replace (b + a)%nat with (a + b)%nat by lia. reflexivity.
Qed.
Lemma s16_nth_firstn : forall {A} (l : list A) L i d, (i < L)%nat -> nth i (firstn L l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros L i d Hi; destruct L as [|L]; try lia; [destruct i; reflexivity|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma s16_nth_skipn : forall {A} (l : list A) o i d, nth i (skipn o l) d = nth (o + i) l d.
Proof.
intros A l o. revert l. induction o as [|o IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma s16_nth_fld : forall (bs : list byte) a n k d, (k < n)%nat -> nth k (fld a n bs) d = nth (a + k) bs d.
Proof. intros bs a n k d H. unfold fld. rewrite s16_nth_firstn by exact H. apply s16_nth_skipn. Qed.
(* a 4-byte field holding v (u32 or flag encoding) read through the reader *)
Lemma s16_rd32_fld : forall rd p (bs : list byte) o v, sa_bytes rd p bs -> (o + 4 <= length bs)%nat ->
  fld o 4 bs = le4 (Z_to_bv 64 v) -> 0 <= v < 2 ^ 32 -> rd32 rd (p + Z.of_nat o) v.
Proof.
intros rd p bs o v HB Hl Hf Hv k Hk.
replace (p + Z.of_nat o + Z.of_nat k) with (p + Z.of_nat (o + k)) by lia.
rewrite (HB (o + k)%nat) by lia. f_equal.
rewrite <- (s16_nth_fld bs o 4 k ZB0 Hk), Hf. unfold le4.
rewrite (nth_error_nth _ _ _ (YN01.nth_error_Z_to_le_bytes 4 _ k Hk)).
rewrite Z_to_bv_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite (Z.mod_small v (2 ^ 64)) by lia. unfold le_byte.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia). reflexivity.
Qed.
(* m->n and the three fields of m->seg[i] the loop loads (role 0x10, role_set 0x14, model_set 0x20) *)
Lemma s16_rd_n : forall rd p mc, sa_mconf rd p mc -> rd32 rd (p + MC_N) (Z.of_nat (length (mc_seg mc))).
Proof.
intros rd p mc (bs & HB & L & LS & _ & (N0 & N) & _). unfold SEG_M_SIZE in L. unfold fldz, MC_N in N.
change (p + MC_N) with (p + 0x2000). change 0x2000 with (Z.of_nat (Z.to_nat 0x2000)).
apply (s16_rd32_fld rd p bs _ _ HB); [cbn; lia | exact N | exact N0].
Qed.
Lemma s16_rd_seg4 : forall rd p mc i (off : nat) v,
  sa_mconf rd p mc -> (i < length (mc_seg mc))%nat -> (off + 4 <= 256)%nat ->
  (forall bs, mconf_enc mc bs -> fld off 4 (fld (256 * i) 256 bs) = le4 (Z_to_bv 64 v)) -> 0 <= v < 2 ^ 32 ->
  rd32 rd (p + 256 * Z.of_nat i + Z.of_nat off) v.
Proof.
intros rd p mc i off v (bs & HB & E) Hi Ho Hf Hv. pose proof E as (L & LS & _). unfold SEG_M_SIZE in L.
replace (p + 256 * Z.of_nat i + Z.of_nat off) with (p + Z.of_nat (256 * i + off)) by lia.
apply (s16_rd32_fld rd p bs _ _ HB); [lia | | exact Hv].
rewrite <- (s16_fld_fld bs (256 * i) 256 off 4 Ho). exact (Hf bs E).
Qed.
Lemma s16_mseg : forall mc bs i, mconf_enc mc bs -> (i < length (mc_seg mc))%nat ->
  mseg_enc (nth i (mc_seg mc) mseg_d) (fld (256 * i) 256 bs).
Proof. intros mc bs i (_ & _ & SG & _) Hi. exact (SG i Hi). Qed.
Lemma s16_rd_role_set : forall rd p mc i, sa_mconf rd p mc -> (i < length (mc_seg mc))%nat ->
  rd32 rd (p + 256 * Z.of_nat i + 0x14) (b2z (ms_role_set (nth i (mc_seg mc) mseg_d))).
Proof.
intros rd p mc i H Hi. change 0x14 with (Z.of_nat 20).
apply (s16_rd_seg4 rd p mc i 20 _ H Hi ltac:(lia)).
- intros bs E. destruct (s16_mseg mc bs i E Hi) as (_ & _ & _ & RS & _). unfold fldz, MS_ROLE_SET in RS. exact RS.
- unfold b2z. destruct (ms_role_set _); lia.
Qed.
Lemma s16_rd_model_set : forall rd p mc i, sa_mconf rd p mc -> (i < length (mc_seg mc))%nat ->
  rd32 rd (p + 256 * Z.of_nat i + 0x20) (b2z (ms_model_set (nth i (mc_seg mc) mseg_d))).
Proof.
intros rd p mc i H Hi. change 0x20 with (Z.of_nat 32).
apply (s16_rd_seg4 rd p mc i 32 _ H Hi ltac:(lia)).
- intros bs E. destruct (s16_mseg mc bs i E Hi) as (_ & _ & _ & _ & _ & _ & MS & _). unfold fldz, MS_MODEL_SET in MS.
  exact MS.
- unfold b2z. destruct (ms_model_set _); lia.
Qed.
Lemma s16_rd_role : forall rd p mc i, sa_mconf rd p mc -> (i < length (mc_seg mc))%nat ->
  0 <= ms_role (nth i (mc_seg mc) mseg_d) < 2 ^ 31 /\
  rd32 rd (p + 256 * Z.of_nat i + 0x10) (ms_role (nth i (mc_seg mc) mseg_d)).
Proof.
intros rd p mc i H Hi. pose proof H as (bs0 & _ & E0).
destruct (s16_mseg mc bs0 i E0 Hi) as (_ & _ & ((R0 & _) & R31) & _).
split; [lia|]. change 0x10 with (Z.of_nat 16).
apply (s16_rd_seg4 rd p mc i 16 _ H Hi ltac:(lia)); [|lia].
intros bs E. destruct (s16_mseg mc bs i E Hi) as (_ & _ & ((_ & RE) & _) & _). unfold fldz, MS_ROLE in RE. exact RE.
Qed.

(* byte lists: a field of an updated block (the plain / UBSan owner's plain L02W_mx.v mx_nth_upd .. mx_fld_upd_sub) *)
Lemma s16_nth_upd : forall (bs X : list byte) k j, (k + length X <= length bs)%nat ->
  nth_error (upd_bytes bs k X) j =
    if (Nat.leb k j && Nat.ltb j (k + length X))%bool then nth_error X (j - k) else nth_error bs j.
Proof.
intros bs X k j H. destruct (Nat.ltb_spec0 j (length bs)) as [L|L].
- apply upd_bytes_nth; assumption.
- rewrite (proj2 (nth_error_None (upd_bytes bs k X) j)) by (rewrite upd_bytes_length by assumption; lia).
  rewrite (proj2 (nth_error_None bs j)) by lia.
  destruct (Nat.leb_spec0 k j), (Nat.ltb_spec0 j (k + length X)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma s16_nth_error_fld : forall (l : list byte) a n i,
  nth_error (fld a n l) i = if Nat.ltb i n then nth_error l (a + i) else None.
Proof. intros l a n i. unfold fld. rewrite nth_error_firstn, nth_error_skipn. reflexivity. Qed.
Lemma s16_fld_upd_out : forall (bs X : list byte) k a n,
  (k + length X <= length bs)%nat -> (a + n <= k \/ k + length X <= a)%nat ->
  fld a n (upd_bytes bs k X) = fld a n bs.
Proof.
intros bs X k a n H D. apply nth_error_ext. intros i. rewrite !s16_nth_error_fld.
destruct (Nat.ltb_spec0 i n); [|reflexivity]. rewrite (s16_nth_upd bs X k (a + i) H).
destruct (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length X)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma s16_fld_upd_inner : forall (bs X : list byte) k a n,
  (k + length X <= length bs)%nat -> (k <= a)%nat -> (a + n <= k + length X)%nat ->
  fld a n (upd_bytes bs k X) = fld (a - k) n X.
Proof.
intros bs X k a n H1 H2 H3. apply nth_error_ext. intros i. rewrite !s16_nth_error_fld.
destruct (Nat.ltb_spec0 i n); [|reflexivity]. rewrite (s16_nth_upd bs X k (a + i) H1).
destruct (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length X)); cbn [andb]; try lia.
f_equal. lia.
Qed.
Lemma s16_fld_upd_sub : forall (bs X : list byte) k a n,
  (k + length X <= length bs)%nat -> (a <= k)%nat -> (k + length X <= a + n)%nat -> (a + n <= length bs)%nat ->
  fld a n (upd_bytes bs k X) = upd_bytes (fld a n bs) (k - a) X.
Proof.
intros bs X k a n H1 H2 H3 H4.
assert (LF : length (fld a n bs) = n) by (unfold fld; rewrite length_firstn, length_skipn; lia).
apply nth_error_ext. intros i.
rewrite (s16_nth_upd (fld a n bs) X (k - a) i) by lia.
rewrite !s16_nth_error_fld. rewrite (s16_nth_upd bs X k (a + i) H1).
destruct (Nat.ltb_spec0 i n), (Nat.leb_spec0 (k - a) i), (Nat.ltb_spec0 i (k - a + length X)),
         (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length X)); cbn [andb];
  try (exfalso; lia); try reflexivity.
all: f_equal; lia.
Qed.

(* the two edits of m->seg[i], on its 256 bytes *)
Definition Z4 : list byte := le4 (Z_to_bv 64 0).
Lemma s16_Z4_len : length Z4 = 4%nat.
Proof. apply length_le4. Qed.
Lemma s16_mseg_drop_model : forall g f, mseg_enc g f -> mseg_enc (ms_drop_model g) (upd_bytes f 32 Z4).
Proof.
intros g f (L & N & R & RS & I & IS & MS & M & RF & IF & G).
assert (HL : (32 + length Z4 <= length f)%nat) by (rewrite s16_Z4_len; lia).
unfold ms_drop_model, mseg_enc, fldz. cbn [ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set
  ms_model ms_role_file ms_ignore_file ms_gen].
unfold fldz in *. unfold MS_ROLE, MS_ROLE_SET, MS_IGNORE, MS_IGNORE_SET, MS_MODEL_SET, MS_MODEL, MS_ROLE_FILE,
  MS_IGNORE_FILE, MS_GEN in *.
split; [rewrite upd_bytes_length by exact HL; exact L|].
rewrite (s16_fld_upd_inner f Z4 32 (Z.to_nat 32) (Z.to_nat 4)) by (rewrite ?s16_Z4_len; lia).
rewrite !(s16_fld_upd_out f Z4 32) by (rewrite ?s16_Z4_len; lia).
refine (conj N (conj R (conj RS (conj I (conj IS (conj _ (conj M (conj RF (conj IF G))))))))).
reflexivity.
Qed.
Lemma s16_mseg_drop_role : forall g f, mseg_enc g f -> mseg_enc (ms_drop_role g) (upd_bytes f 16 (Z4 ++ Z4)).
Proof.
intros g f (L & N & R & RS & I & IS & MS & M & RF & IF & G).
assert (HL : (16 + length (Z4 ++ Z4) <= length f)%nat) by (rewrite length_app, s16_Z4_len; lia).
unfold ms_drop_role, mseg_enc, fldz. cbn [ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set
  ms_model ms_role_file ms_ignore_file ms_gen].
unfold fldz in *. unfold MS_ROLE, MS_ROLE_SET, MS_IGNORE, MS_IGNORE_SET, MS_MODEL_SET, MS_MODEL, MS_ROLE_FILE,
  MS_IGNORE_FILE, MS_GEN in *.
split; [rewrite upd_bytes_length by exact HL; exact L|].
rewrite (s16_fld_upd_inner f (Z4 ++ Z4) 16 (Z.to_nat 16) (Z.to_nat 4)) by (rewrite ?length_app, ?s16_Z4_len; lia).
rewrite (s16_fld_upd_inner f (Z4 ++ Z4) 16 (Z.to_nat 20) (Z.to_nat 4)) by (rewrite ?length_app, ?s16_Z4_len; lia).
rewrite !(s16_fld_upd_out f (Z4 ++ Z4) 16) by (rewrite ?length_app, ?s16_Z4_len; lia).
refine (conj N (conj _ (conj _ (conj I (conj IS (conj MS (conj M (conj RF (conj IF G))))))))).
- split; [split; [lia | reflexivity] | lia].
- reflexivity.
Qed.
(* the struct: one entry edited in place *)
Lemma s16_mconf_upd : forall mc bs i f X off,
  mconf_enc mc bs -> (i < length (mc_seg mc))%nat -> (off + length X <= 256)%nat ->
  mseg_enc (f (nth i (mc_seg mc) mseg_d)) (upd_bytes (fld (256 * i) 256 bs) off X) ->
  mconf_enc (m_upd mc i f) (upd_bytes bs (256 * i + off) X).
Proof.
intros mc bs i f X off E Hi HX HG.
destruct E as (L & LS & SG & N & O & RF & LK & KP & KN & NK & G & RD).
unfold SEG_M_SIZE in L.
assert (HB : (256 * i + off + length X <= length bs)%nat) by lia.
assert (OUT : forall a n, (256 * 32 <= a)%nat -> fld a n (upd_bytes bs (256 * i + off) X) = fld a n bs)
  by (intros a n Ha; apply s16_fld_upd_out; [exact HB | right; lia]).
unfold mconf_enc, mconf_encp, fldz in *. unfold m_upd, m_set_segs.
cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
unfold MC_N, MC_OVERFLOW, MC_REFUSED, MC_KEPT, MC_KNOCK, MC_NKEPT, MC_GEN, MC_READING in *.
rewrite !s16_upd_nth_length.
split; [rewrite upd_bytes_length by exact HB; exact L|]. split; [exact LS|].
split.
{ intros j Hj. rewrite (s16_upd_nth_nth i j f (mc_seg mc) mseg_d Hi).
  destruct (Nat.eqb_spec j i) as [->|Ne].
  - rewrite (s16_fld_upd_sub bs X (256 * i + off) (256 * i) 256) by lia.
    replace (256 * i + off - 256 * i)%nat with off by lia. exact HG.
  - rewrite (s16_fld_upd_out bs X (256 * i + off) (256 * j) 256) by lia. apply SG. exact Hj. }
rewrite !OUT by lia.
split; [exact N|]. split; [exact O|]. split; [exact RF|]. split; [exact LK|].
split; [intros j Hj; rewrite !OUT by lia; apply KP; exact Hj|].
split; [intros j Hj; rewrite !OUT by lia; apply KN; exact Hj|].
split; [exact NK|]. split; [exact G|exact RD].
Qed.
(* the block's bytes after a store of X at k: the reader shows upd_bytes *)
Lemma s16_bytes_upd : forall (rd rd' : reader) p (bs X : list byte) k,
  sa_bytes rd p bs -> (k + length X <= length bs)%nat ->
  (forall j, (j < length bs)%nat -> ~ (k <= j < k + length X)%nat -> rd' (p + Z.of_nat j) = rd (p + Z.of_nat j)) ->
  (forall j, (j < length X)%nat -> rd' (p + Z.of_nat (k + j)) = Some (bv_unsigned (nth j X ZB0))) ->
  sa_bytes rd' p (upd_bytes bs k X).
Proof.
intros rd rd' p bs X k HB HL Hout Hin j Hj. rewrite upd_bytes_length in Hj by exact HL.
pose proof (s16_nth_upd bs X k j HL) as E.
assert (Hj' : (j < length (upd_bytes bs k X))%nat) by (rewrite upd_bytes_length by exact HL; exact Hj).
rewrite (nth_error_nth' _ ZB0 Hj') in E.
destruct (Nat.leb_spec0 k j), (Nat.ltb_spec0 j (k + length X)); cbn [andb] in E.
- rewrite (nth_error_nth' X ZB0 (ltac:(lia) : (j - k < length X)%nat)) in E. injection E as E. rewrite E.
  replace j with (k + (j - k))%nat at 1 by lia. apply Hin. lia.
- rewrite (nth_error_nth' _ ZB0 Hj) in E. injection E as E. rewrite E, Hout by lia. apply HB. exact Hj.
- rewrite (nth_error_nth' _ ZB0 Hj) in E. injection E as E. rewrite E, Hout by lia. apply HB. exact Hj.
- rewrite (nth_error_nth' _ ZB0 Hj) in E. injection E as E. rewrite E, Hout by lia. apply HB. exact Hj.
Qed.
Lemma s16_Z4_nth : forall j, (j < 4)%nat -> bv_unsigned (nth j Z4 ZB0) = 0.
Proof. intros j Hj. do 4 (destruct j as [|j]; [reflexivity|]). lia. Qed.
Lemma s16_Z8_nth : forall j, (j < 8)%nat -> bv_unsigned (nth j (Z4 ++ Z4) ZB0) = 0.
Proof. intros j Hj. do 8 (destruct j as [|j]; [reflexivity|]). lia. Qed.
(* the stores of 0x852d4 (model_set = 0) and 0x852f8 / 0x85304 (role_set = 0, role = 0) *)
Lemma s16_mconf_drop_model : forall (rd rd' : reader) p mc i, sa_mconf rd p mc -> (i < length (mc_seg mc))%nat ->
  0 <= p -> p + SEG_M_SIZE <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (p + 256 * Z.of_nat i + 0x20 <= a < p + 256 * Z.of_nat i + 0x24) -> rd' a = rd a) ->
  (forall j, 0 <= j < 4 -> rd' (p + 256 * Z.of_nat i + 0x20 + j) = Some 0) ->
  sa_mconf rd' p (m_upd mc i ms_drop_model).
Proof.
intros rd rd' p mc i (bs & HB & E) Hi Hp0 Hp1 Hout Hin. pose proof E as (L & LS & _). unfold SEG_M_SIZE in *.
exists (upd_bytes bs (256 * i + 32) Z4). split.
- apply (s16_bytes_upd rd rd' p bs Z4 (256 * i + 32) HB); rewrite ?s16_Z4_len; [lia | |].
  + intros j Hj Hn. apply Hout; lia.
  + intros j Hj. rewrite s16_Z4_nth by exact Hj.
    replace (p + Z.of_nat (256 * i + 32 + j)) with (p + 256 * Z.of_nat i + 0x20 + Z.of_nat j) by lia.
    apply Hin. lia.
- apply s16_mconf_upd; [exact E | exact Hi | rewrite s16_Z4_len; lia |].
  apply s16_mseg_drop_model. exact (s16_mseg mc bs i E Hi).
Qed.
Lemma s16_mconf_drop_role : forall (rd rd' : reader) p mc i, sa_mconf rd p mc -> (i < length (mc_seg mc))%nat ->
  0 <= p -> p + SEG_M_SIZE <= 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (p + 256 * Z.of_nat i + 0x10 <= a < p + 256 * Z.of_nat i + 0x18) -> rd' a = rd a) ->
  (forall j, 0 <= j < 8 -> rd' (p + 256 * Z.of_nat i + 0x10 + j) = Some 0) ->
  sa_mconf rd' p (m_upd mc i ms_drop_role).
Proof.
intros rd rd' p mc i (bs & HB & E) Hi Hp0 Hp1 Hout Hin. pose proof E as (L & LS & _). unfold SEG_M_SIZE in *.
exists (upd_bytes bs (256 * i + 16) (Z4 ++ Z4)). split.
- apply (s16_bytes_upd rd rd' p bs (Z4 ++ Z4) (256 * i + 16) HB); rewrite ?length_app, ?s16_Z4_len; [lia | |].
  + intros j Hj Hn. apply Hout; lia.
  + intros j Hj. rewrite s16_Z8_nth by exact Hj.
    replace (p + Z.of_nat (256 * i + 16 + j)) with (p + 256 * Z.of_nat i + 0x10 + Z.of_nat j) by lia.
    apply Hin. lia.
- apply s16_mconf_upd; [exact E | exact Hi | rewrite length_app, s16_Z4_len; lia |].
  apply s16_mseg_drop_role. exact (s16_mseg mc bs i E Hi).
Qed.
(* a reader that agrees on the block's bytes shows the same struct *)
Lemma s16_mconf_ext : forall (rd rd' : reader) p mc, sa_mconf rd p mc ->
  (forall a, p <= a < p + SEG_M_SIZE -> rd' a = rd a) -> sa_mconf rd' p mc.
Proof.
intros rd rd' p mc (bs & HB & E) Hk. exists bs. split; [|exact E].
pose proof E as (L & _). intros j Hj. rewrite Hk by (unfold SEG_M_SIZE in *; lia). exact (HB j Hj).
Qed.
Lemma s16_mconf_len : forall rd p mc, sa_mconf rd p mc -> (length (mc_seg mc) <= 32)%nat.
Proof. intros rd p mc (bs & _ & _ & LS & _). exact LS. Qed.

(* ===================================== the walk's statements ===================================== *)
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YC5d YM05 YI16 YG0d_tail.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaCall PaFx m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require LLVMFuzzerTestOneInput_s02.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP03.

(* the inner cut points (offsets from BASE = 0x84d34) *)
Definition LO_KH16 : Z := 0x508.  (* 0x8523c: the loop head, turn i *)
Definition LO_KP1 : Z := 0x58c.   (* 0x852c0: m_refuse returned, seg[i]'s model to drop (0x852bc's call) *)
Definition LO_KP2 : Z := 0x5bc.   (* 0x852f0: m_refuse returned, seg[i]'s role to drop (0x852ec's call) *)
Definition LO_KL16 : Z := 0x5dc.  (* 0x85310: the latch of turn i *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the model the loop starts from (K85208's) and the model after i passes *)
Definition s16_M1c (cx : lcx) (f : nat) : SegModel.mconf := s16_M1 (x_pl cx) f.
Definition s16_Mic (cx : lcx) (f i : nat) : SegModel.mconf := s16_Mi (s16_M1c cx f) i.
(* the s1 slots of K85208 (LT_L and the last turn's four) and of K853bc (with 112(s1), the entry's sd s10) *)
Definition s16_L0 (cx : lcx) (f : nat) (c m : Z) : list (Z * Z) :=
  LT_L cx c m ++
    [(120, seg_spec.b2z (seg_spec.seg_ret (x_st cx f))); (128, Z.of_nat f + 1);
     (136, seg_spec.seg_turn_at (x_pl cx) (x_p cx) f);
     (152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))].
Definition s16_L (cx : lcx) (f : nat) (c m : Z) : list (Z * Z) :=
  LT_L cx c m ++
    [(112, (m + seg_spec.MC_N) / 8); (120, seg_spec.b2z (seg_spec.seg_ret (x_st cx f))); (128, Z.of_nat f + 1);
     (136, seg_spec.seg_turn_at (x_pl cx) (x_p cx) f);
     (152, Z.of_nat (length (seg_spec.seg_turn_tail (x_pl cx) f)))].
(* the loop's registers at its head and latch, turn i: a3 = the shadow base, a4 = m, s4 = s10 = &m->seg[i] + 0x20,
   s8 = SH(&m->seg[i] + 0x14), s9 = i *)
Definition s16_lregs (regs : bvmap 5 word) (m : Z) (i : nat) : Prop :=
  getr regs 13 = w64 SHADOW_OFF /\ getr regs 14 = w64 m /\
  getr regs 20 = w64 (m + 0x20 + 256 * Z.of_nat i) /\ getr regs 24 = w64 (shadow_addr (m + 0x14 + 256 * Z.of_nat i)) /\
  getr regs 25 = w64 (Z.of_nat i) /\ getr regs 26 = w64 (m + 0x20 + 256 * Z.of_nat i).
(* the callee-saved part of them (what an m_refuse call keeps) *)
Definition s16_sregs (regs : bvmap 5 word) (m : Z) (i : nat) : Prop :=
  getr regs 20 = w64 (m + 0x20 + 256 * Z.of_nat i) /\ getr regs 24 = w64 (shadow_addr (m + 0x14 + 256 * Z.of_nat i)) /\
  getr regs 25 = w64 (Z.of_nat i) /\ getr regs 26 = w64 (m + 0x20 + 256 * Z.of_nat i).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* what every point of the segment states beyond its loop registers: K85208's premises, with m holding mc *)
Definition s16_inv (cx : lcx) (f : nat) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z)
  (c m t : Z) (mc : SegModel.mconf) : Prop :=
  Z.of_nat f + 1 = x_nf cx /\
  lt_core B MT cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem) t (x_tn cx f) /\
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) /\ getr regs 23 = w64 t /\
  getr regs 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) /\
  lt_slots cx (rdW W mem) (s16_L cx f c m) /\
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) /\ sa_mconf (rdW W mem) m mc /\
  sa_str (rdW W mem) t (seg_spec.seg_txt (x_pl cx) f) /\
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_st cx f)) (s16_M1c cx f).
(* K85208's premises themselves (no slot 112, no s2), with m holding mc *)
Definition s16_inv0 (cx : lcx) (f : nat) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z)
  (c m t : Z) (mc : SegModel.mconf) : Prop :=
  Z.of_nat f + 1 = x_nf cx /\
  lt_core B MT cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) LFO_L
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem) t (x_tn cx f) /\
  getr regs 23 = w64 t /\ getr regs 27 = w64 (seg_spec.seg_turn_np (x_pl cx) f) /\
  lt_slots cx (rdW W mem) (s16_L0 cx f c m) /\
  sa_rconf (rdW W mem) c (seg_spec.seg_rc (x_st cx f)) /\ sa_mconf (rdW W mem) m mc /\
  sa_str (rdW W mem) t (seg_spec.seg_txt (x_pl cx) f) /\
  lt_cnt (Datatypes.S f) (seg_spec.seg_rc (x_st cx f)) (s16_M1c cx f).
(* 0x8523c: the head of pass i < m->n, m holding the model after passes 0 .. i - 1 *)
Definition LT16_KH_stmt (f i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (s16_M1c cx f)))%nat ->
  s16_inv cx f ly S W regs mem md k acc c m t (s16_Mic cx f i) -> s16_lregs regs m i ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_KH16) regs mem md) (lt_post B MT cx).
(* 0x85310: the latch of pass i, m holding the model after passes 0 .. i *)
Definition LT16_KL_stmt (f i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (s16_M1c cx f)))%nat ->
  s16_inv cx f ly S W regs mem md k acc c m t (s16_Mic cx f (Datatypes.S i)) -> s16_lregs regs m i ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_KL16) regs mem md) (lt_post B MT cx).
(* 0x852c0: after the m_refuse of a model without a box (0x852bc), s3 = &m->seg[i].model_set *)
Definition LT16_KP1_stmt (f i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (s16_M1c cx f)))%nat ->
  SegModel.m_cross_seg (s16_Mic cx f i) i =
    SegModel.m_upd (SegModel.m_refuse (s16_Mic cx f i) 0 false) i SegModel.ms_drop_model ->
  s16_inv cx f ly S W regs mem md k acc c m t (SegModel.m_refuse (s16_Mic cx f i) 0 false) ->
  s16_sregs regs m i -> getr regs 19 = w64 (m + 0x20 + 256 * Z.of_nat i) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_KP1) regs mem md) (lt_post B MT cx).
(* 0x852f0: after the m_refuse of a box without a model (0x852ec), s5 = SH(&m->seg[i] + 0x10) *)
Definition LT16_KP2_stmt (f i : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> (i < length (SegModel.mc_seg (s16_M1c cx f)))%nat ->
  SegModel.m_cross_seg (s16_Mic cx f i) i =
    SegModel.m_upd (SegModel.m_refuse (s16_Mic cx f i) 0 false) i SegModel.ms_drop_role ->
  s16_inv cx f ly S W regs mem md k acc c m t (SegModel.m_refuse (s16_Mic cx f i) 0 false) ->
  s16_sregs regs m i -> getr regs 21 = w64 (shadow_addr (m + 0x10 + 256 * Z.of_nat i)) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_KP2) regs mem md) (lt_post B MT cx).
End e.
End f.
End d.
(* ===================================== facts carried across a state change ===================================== *)
(* the blocks of a permutation are pairwise apart (AR's block law, under any order) *)
Lemma s16_pairwise_perm : forall (l l' : list (Z * Z)), Permutation l l' ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) ->
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l').
Proof.
intros l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' HP1 IH1 HP2 IH2]; intros H.
- exact H.
- cbn [map pairwise] in H |- *. destruct H as [F P]. split; [|exact (IH P)].
  rewrite Forall_forall in F |- *. intros z Hz. apply in_map_iff in Hz as (w & <- & Hw).
  apply F. apply in_map_iff. exists w. split; [reflexivity|]. exact (Permutation_in _ (Permutation_sym HP) Hw).
- cbn [map pairwise] in H |- *. destruct H as [F1 [F2 P]]. inversion F1 as [|? ? Hxy F1']; subst.
  split; [constructor; [unfold zdisjoint in *; lia | exact F2] | split; [exact F1' | exact P]].
- exact (IH2 (IH1 H)).
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.

(* image facts read only image bytes: a reader that agrees on [0x10000, kImgEnd) keeps them *)
Lemma s16_rdword_ext : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
rewrite <- (Z.add_0_r a) at 1. rewrite (H 0) by lia. rewrite (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia.
rewrite Z.add_0_r. reflexivity.
Qed.
Lemma s16_img_rng : forall a n, sa_img SEGS B a n -> forall x, a <= x < a + n -> 0x10000 <= x < kImgEnd.
Proof. intros a n H x Hx. destruct (H x Hx) as (Hi & _). exact (pa_img_range x Hi). Qed.
(* the image range of a reader change: every image byte, the read-only window and the cells SegInstA names *)
Definition s16_imgk (rd rd' : reader) : Prop := forall x, 0x10000 <= x < kImgEnd -> rd' x = rd x.
Lemma s16_lit_kept : forall (W W' : world SEGS) mem mem' a s, s16_imgk (rdW W mem) (rdW W' mem') ->
  sa_lit SEGS B (rdW W mem) a s -> sa_lit SEGS B (rdW W' mem') a s.
Proof.
intros W W' mem mem' a s HK (H0 & ((Hz & Hn) & _) & Hp & Hr & Hi).
split; [exact H0|]. split; [|split; [exact Hp | split; [exact Hr | exact Hi]]].
split; [split; [|exact Hn]|].
- intros j Hj. rewrite HK; [exact (Hz j Hj)|]. rewrite length_app in Hj. cbn [length] in Hj.
  apply (s16_img_rng a (Z.of_nat (length s) + 1) Hi). lia.
- exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr).
Qed.
Lemma s16_himg_kept : forall (W W' : world SEGS) mem mem', s16_imgk (rdW W mem) (rdW W' mem') ->
  seg_himg SEGS B longlA mod40A catA wordsA rolesA gotwA guardA seg_litA_fz seg_litA_rc (rdW W mem) ->
  seg_himg SEGS B longlA mod40A catA wordsA rolesA gotwA guardA seg_litA_fz seg_litA_rc (rdW W' mem').
Proof.
intros W W' mem mem' HK (HM & HMi & HF & HR & (Cp & Ci & Cr) & Ca & (Wp & Wi & Wr) & (Rp & Ri & Rr) & (S1 & S2) & HL).
split; [intros k Hk; rewrite HK; [exact (HM k Hk) | apply (s16_img_rng mod40A 8 HMi); lia]|].
split; [exact HMi|].
split; [intros s Hs; destruct (HF s Hs) as [Hl Ha]; split; [exact (s16_lit_kept W W' mem mem' _ s HK Hl) | exact Ha]|].
split; [intros s Hs; destruct (HR s Hs) as [Hl Ha]; split; [exact (s16_lit_kept W W' mem mem' _ s HK Hl) | exact Ha]|].
split.
{ split; [exact Cp|]. split; [exact Ci|]. intros i Hi. destruct (Cr i Hi) as (tp & Ht & Hl).
  exists tp. split; [|exact (s16_lit_kept W W' mem mem' _ _ HK Hl)].
  rewrite (s16_rdword_ext (rdW W mem) (rdW W' mem')); [exact Ht|].
  intros j Hj. apply HK. apply (s16_img_rng catA pin_spec.CAT_BYTES Ci).
  unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *. lia. }
split; [exact Ca|].
split.
{ split; [exact Wp|]. split; [exact Wi|]. intros i Hi. destruct (Wr i Hi) as (wp & Hw & Hl).
  exists wp. split; [|exact (s16_lit_kept W W' mem mem' _ _ HK Hl)].
  rewrite (s16_rdword_ext (rdW W mem) (rdW W' mem')); [exact Hw|].
  intros j Hj. apply HK. apply (s16_img_rng wordsA 40 Wi). lia. }
split.
{ split; [exact Rp|]. split; [exact Ri|]. intros i Hi k Hk. rewrite HK; [exact (Rr i Hi k Hk)|].
  apply (s16_img_rng rolesA 20 Ri). lia. }
split.
{ unfold sa_ssp. rewrite !(s16_rdword_ext (rdW W mem) (rdW W' mem') gotwA)
    by (intros j Hj; apply HK; unfold gotwA, kImgEnd; lia).
  split; [exact S1|]. destruct S2 as (g & Hg). exists g.
  rewrite (s16_rdword_ext (rdW W mem) (rdW W' mem') guardA); [exact Hg|].
  intros j Hj. apply HK. unfold guardA, kImgEnd. lia. }
exact HL.
Qed.
Lemma s16_img_kept : forall cx (W W' : world SEGS) mem mem', s16_imgk (rdW W mem) (rdW W' mem') ->
  lt_img B cx (rdW W mem) -> lt_img B cx (rdW W' mem').
Proof.
intros cx W W' mem mem' HK (HA & HH & HG). split; [|split].
- intros a Hro Ho He. rewrite HK; [exact (HA a Hro Ho He)|].
  destruct Hro as [(sg & Hs & _ & Hr) | Hr].
  + apply pa_img_range. exists sg. split; [exact Hs | exact Hr].
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
- exact (s16_himg_kept W W' mem mem' HK HH).
- intros j Hj. rewrite HK; [exact (HG j Hj)|]. unfold longlA, A_LONGL, LONGL_W, kImgEnd. lia.
Qed.
(* ---- the harness's real frame: the entry sp and s1 = (sp - 320) & -32 ---- *)
Lemma s16_stk : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 336 <= x_s1 cx <= x_sp0 cx - 320.
Proof.
intros cx (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (H16 & H0 & Hc & Hlo & Hhi & H47 & _).
unfold x_s1, LT_FRAME. unfold x_sp0. set (sp := spZ (x_regs cx)) in *.
pose proof (Z.mod_pos_bound (sp - 320) 32 ltac:(lia)) as M.
assert (Hm : (sp - 320) mod 32 = 0 \/ (sp - 320) mod 32 = 16).
{ pose proof (Z.div_mod (sp - 320) 32 ltac:(lia)) as D. pose proof (Z.div_mod sp 16 ltac:(lia)) as D2.
  rewrite H16 in D2. lia. }
split; [exact H16|]. split; [lia|]. split; [|lia].
replace ((sp - 320) - (sp - 320) mod 32) with (32 * ((sp - 320) / 32))
  by (pose proof (Z.div_mod (sp - 320) 32 ltac:(lia)); lia).
rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
(* sa_bytes / rdword / sa_zs over a range the change keeps *)
Lemma s16_bytes_ext : forall (rd rd' : reader) p (bs : list byte),
  (forall j, 0 <= j < Z.of_nat (length bs) -> rd' (p + j) = rd (p + j)) -> sa_bytes rd p bs -> sa_bytes rd' p bs.
Proof. intros rd rd' p bs Hk H j Hj. rewrite Hk by lia. exact (H j Hj). Qed.
Lemma s16_zs_ext : forall (rd rd' : reader) p (l : list Z),
  (forall j, 0 <= j < Z.of_nat (length l) -> rd' (p + j) = rd (p + j)) -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros rd rd' p l Hk H j Hj. rewrite Hk by lia. exact (H j Hj). Qed.
(* a harness block at a later state: its shadow is AR's there *)
Lemma s16_hblk_kept : forall ly S (rd : reader) ly2 S2 (W2 : world SEGS) mem2 md2 a n,
  AR SEGS B ly2 S2 W2 mem2 md2 -> lt_hblk B ly S rd a n -> In (a, n) (ablocks B ly2 S2) ->
  lt_hblk B ly2 S2 (rdW W2 mem2) a n.
Proof.
intros ly S rd ly2 S2 W2 mem2 md2 a n HAR2 (_ & H4096 & H16 & (Ha0 & Ha63 & Hamem & _)) Hin2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as [_ Hhull].
split; [exact Hin2|]. split; [exact H4096|]. split; [exact H16|].
split; [exact Ha0|]. split; [exact Ha63|]. split; [exact Hamem|].
destruct (Z.eq_dec n 0) as [->|Hn0].
- split; [intros x Hx; lia | intros Hx; lia].
- assert (Hr : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  split.
  + apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 a n a n HAR2 Hin2); lia.
  + intros _. rewrite <- Hr. exact Hhull.
Qed.
(* the blocks of a cut: pairwise apart, and apart from the entry's *)
Lemma s16_blocks_apart : forall cx ly S (W : world SEGS) mem md t tn m c,
  AR SEGS B ly S W mem md -> lt_blocks B cx ly S [(t, tn); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  0 < tn ->
  zdisjoint (t, tn) (m, seg_spec.SEG_M_SIZE) /\ zdisjoint (m, seg_spec.SEG_M_SIZE) (c, seg_spec.SEG_C_SIZE) /\
  zdisjoint (t, tn) (c, seg_spec.SEG_C_SIZE) /\ ~ In (m, seg_spec.SEG_M_SIZE) (x_bl0 B cx).
Proof.
intros cx ly S W mem md t tn m c HAR HP Htn.
assert (Hin : In (t, tn) (ablocks B ly S)) by exact (Permutation_in _ (Permutation_sym HP) (in_eq _ _)).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & Hpw & _).
pose proof (s16_pairwise_perm _ _ HP Hpw) as Hpw'.
assert (Rt : req_size tn = tn) by (unfold req_size; destruct (Z.eqb_spec tn 0); lia).
cbn [map pairwise fst snd app] in Hpw'. rewrite Rt in Hpw'.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hpw'.
change (req_size seg_spec.SEG_C_SIZE) with seg_spec.SEG_C_SIZE in Hpw'.
destruct Hpw' as (F1 & F2 & F3 & _).
apply Forall_cons_iff in F1 as [D1 F1']. apply Forall_cons_iff in F1' as [D2 _].
apply Forall_cons_iff in F2 as [D3 F2'].
split; [exact D1|]. split; [exact D3|]. split; [exact D2|].
intros Hb. rewrite Forall_forall in F2'.
assert (Hin' : In (m, req_size seg_spec.SEG_M_SIZE) (map (fun b => (fst b, req_size (snd b))) (x_bl0 B cx)))
  by (apply in_map_iff; exists (m, seg_spec.SEG_M_SIZE); split; [reflexivity | exact Hb]).
specialize (F2' _ Hin'). unfold zdisjoint in F2'. cbn [fst snd] in F2'.
change (req_size seg_spec.SEG_M_SIZE) with 9236 in F2'. unfold seg_spec.SEG_M_SIZE in F2'. lia.
Qed.
Lemma s16_frame_addr : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity. Qed.
(* the offsets of K85208's slots: 8 .. 184, none in 112(s1)'s word *)
Lemma s16_L0_off : forall cx f c m o v, In (o, v) (s16_L0 cx f c m) -> 8 <= o <= 184 /\ (o + 8 <= 112 \/ 120 <= o).
Proof.
intros cx f c m o v H. unfold s16_L0, LT_L in H. cbn [app In] in H.
repeat (destruct H as [H|H]; [injection H as <- _; lia|]). destruct H.
Qed.
Lemma s16_L_split : forall cx f c m o v, In (o, v) (s16_L cx f c m) ->
  (o = 112 /\ v = (m + seg_spec.MC_N) / 8) \/ In (o, v) (s16_L0 cx f c m).
Proof.
intros cx f c m o v H. unfold s16_L, s16_L0 in *. apply in_app_or in H as [H|H].
- right. apply in_or_app. left. exact H.
- cbn [In] in H. destruct H as [H|H]; [left; injection H as <- <-; split; reflexivity|].
  right. apply in_or_app. right. exact H.
Qed.
(* K85208's premises carried to a state that changes only m's block, the stack below s1 (an m_refuse call's
   window) and 112(s1), with 112(s1) = (m + 0x2000) >> 3 and s2 = SH(m + 0x2000) there: s16_inv *)
Lemma s16_inv_carry0 : forall cx f ly S (W : world SEGS) regs mem md k acc c m t mc
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 mc2,
  lt_base B MT cx -> s16_inv0 B MT cx f ly S W regs mem md k acc c m t mc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  getr regs2 18 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  getr regs2 23 = getr regs 23 -> getr regs2 27 = getr regs 27 ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) -> mo_le MT (x_S cx) S2 acc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (m <= a < m + seg_spec.SEG_M_SIZE) ->
     ~ (x_s1 cx - STK_m_refuse <= a < x_s1 cx) -> ~ (x_s1 cx + 112 <= a < x_s1 cx + 120) ->
     rdW W2 mem2 a = rdW W mem a) ->
  rdword (rdW W2 mem2) (x_s1 cx + 112) = Some ((m + seg_spec.MC_N) / 8) ->
  sa_mconf (rdW W2 mem2) m mc2 ->
  s16_inv B MT cx f ly2 S2 W2 regs2 mem2 md2 k acc c m t mc2.
Proof.
intros cx f ly S W regs mem md k acc c m t mc ly2 S2 W2 regs2 mem2 md2 mc2 HB HI HJ2 E2 E3 E4 E8 E9 R18 E23 E27
  HP2 HMO HK H112 HMC2.
destruct HI as (Hnf & (HFR & HIMG & HBL & HBUD) & Hc & Hm & Ht & R23 & R27 & HSL & HRC & HMC & HSTR & HCNT).
destruct HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFW & H176 & HZS).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ2) as HAR2.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
destruct (s16_stk cx HB) as (Hsp16 & Hsp & Hs1m & Hs1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HSM : STK_m_refuse = 8240) by reflexivity.
pose proof Hc as (HcIn & _). pose proof Hm as (HmIn & Hm4 & _). pose proof Ht as (HtIn & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HmIn) as (_ & Hm0 & Hmc & Hmapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HcIn) as (_ & Hc0 & Hcc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HtIn) as (_ & Ht0 & Htc & _ & _ & _ & Htn).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmc, Hmapp. change (req_size seg_spec.SEG_C_SIZE) with 16616 in Hcc.
assert (Htn1 : 0 < x_tn cx f) by (unfold x_tn, seg_spec.seg_txt_n; lia).
assert (Rt : req_size (x_tn cx f) = x_tn cx f) by (unfold req_size; destruct (Z.eqb_spec (x_tn cx f) 0); lia).
rewrite Rt in Htc.
destruct (s16_blocks_apart cx ly S W mem md t (x_tn cx f) m c HAR HBL Htn1) as (Dtm & Dmc & Dtc & _).
unfold zdisjoint in Dtm, Dmc, Dtc. cbn [fst snd] in Dtm, Dmc, Dtc. unfold seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE in *.
(* what the change keeps *)
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> ~ (x_s1 cx + 112 <= a < x_s1 cx + 120) -> rdW W2 mem2 a = rdW W mem a)
  by (intros a Ha Hn; apply HK; lia).
assert (Hin3 : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (s16_frame_addr _ _ _ _ _ Hly).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR Hin3) as (Hf0 & Hfc & Hfapp).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE LT_FCLS (x_fpos cx) HAR HmIn Hin3) as Dmf.
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
rewrite EF in Hf0, Hfc, Hfapp, Dmf. rewrite F512 in Hfc, Hfapp, Dmf. unfold zdisjoint in Dmf. cbn [fst snd] in Dmf.
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Dmf.
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W mem a) by (intros a Ha; apply HK; lia).
assert (KSH : forall j, 0 <= j < 36 -> rdW W2 mem2 (x_sh cx + j) = rdW W mem (x_sh cx + j)).
{ intros j Hj. unfold x_sh, shadow_addr.
  assert (Q : 0 <= x_fr cx / 8 <= 0xfffffff00000) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  apply HK; unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
assert (KI : s16_imgk (rdW W mem) (rdW W2 mem2)).
{ intros x Hx. pose proof (blk_off_imgP B ly S W mem md m seg_spec.SEG_M_SIZE HAR HmIn) as Hoff.
  unfold off_img in Hoff. change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hoff. unfold seg_spec.SEG_M_SIZE in Hoff.
  apply HK; unfold kImgEnd in *; lia. }
split; [exact Hnf|].
split.
{ split.
  - split; [exact HJ2|]. rewrite E2, E3, E4, E8, E9.
    split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
    split.
    { intros i r Hi. rewrite <- (HSV i r Hi). apply s16_rdword_ext. intros j Hj.
      assert (Hi13 : (i < 13)%nat) by (apply (nth_error_Some LT_SAVED i); rewrite Hi; discriminate).
      apply KS; lia. }
    split; [rewrite <- HH0; apply s16_rdword_ext; intros j Hj; apply KF; lia|].
    split; [rewrite <- HH8; apply s16_rdword_ext; intros j Hj; apply KF; lia|].
    split; [rewrite <- HH16; apply s16_rdword_ext; intros j Hj; apply KF; lia|].
    split; [rewrite <- HFW; apply s16_rdword_ext; intros j Hj; apply KF; unfold LT_FLAGW; lia|].
    split; [rewrite <- H176; apply s16_rdword_ext; intros j Hj; apply KS; lia|].
    apply (s16_zs_ext (rdW W mem)); [|exact HZS]. rewrite lt_fsh_len. intros j Hj. apply KSH. lia.
  - split; [exact (s16_img_kept cx W W2 mem mem2 KI HIMG)|].
    split; [exact (Permutation_trans HP2 HBL)|].
    destruct HBUD as (b1 & b2 & b3 & _ & b5 & b6). exact (conj b1 (conj b2 (conj b3 (conj HMO (conj b5 b6))))). }
split; [exact (s16_hblk_kept _ _ _ _ _ _ _ _ _ _ HAR2 Hc (Permutation_in _ (Permutation_sym HP2) HcIn))|].
split; [exact (s16_hblk_kept _ _ _ _ _ _ _ _ _ _ HAR2 Hm (Permutation_in _ (Permutation_sym HP2) HmIn))|].
split; [exact (s16_hblk_kept _ _ _ _ _ _ _ _ _ _ HAR2 Ht (Permutation_in _ (Permutation_sym HP2) HtIn))|].
rewrite E23, E27. split; [exact R18|]. split; [exact R23|]. split; [exact R27|].
split.
{ intros o v Hov. destruct (s16_L_split cx f c m o v Hov) as [[-> ->] | Hov0]; [exact H112|].
  rewrite <- (HSL o v Hov0). pose proof (s16_L0_off cx f c m o v Hov0).
  apply s16_rdword_ext. intros j Hj. apply KS; lia. }
split.
{ destruct HRC as (bs & Hbs & Henc). exists bs. split; [|exact Henc]. pose proof Henc as (Lc & _).
  unfold seg_spec.SEG_C_SIZE in Lc.
  apply (s16_bytes_ext (rdW W mem) _ c bs); [|exact Hbs]. intros j Hj. apply HK; lia. }
split; [exact HMC2|].
split.
{ destruct HSTR as ((Hz & Hn0) & _). split; [split; [|exact Hn0]|].
  - apply (s16_zs_ext (rdW W mem)); [|exact Hz]. rewrite length_app. cbn [length].
    intros j Hj. apply HK; unfold x_tn, seg_spec.seg_txt_n in *; lia.
  - intros x Hx. apply (AR_block_word_vis SEGS B ly2 S2 W2 mem2 md2 t (x_tn cx f)
      (t + Z.of_nat (length (seg_spec.seg_txt (x_pl cx) f))) x HAR2 (Permutation_in _ (Permutation_sym HP2) HtIn)).
    + rewrite Rt. unfold x_tn, seg_spec.seg_txt_n. lia.
    + lia. }
exact HCNT.
Qed.
(* s16_inv forgets s2 and 112(s1): K85208's form *)
Lemma s16_inv_inv0 : forall cx f ly S (W : world SEGS) regs mem md k acc c m t mc,
  s16_inv B MT cx f ly S W regs mem md k acc c m t mc -> s16_inv0 B MT cx f ly S W regs mem md k acc c m t mc /\
  getr regs 18 = w64 (shadow_addr (m + seg_spec.MC_N)) /\
  rdword (rdW W mem) (x_s1 cx + 112) = Some ((m + seg_spec.MC_N) / 8).
Proof.
intros cx f ly S W regs mem md k acc c m t mc (Hnf & HC & Hc & Hm & Ht & R18 & R23 & R27 & HSL & HRC & HMC & HSTR & HCNT).
split; [|split; [exact R18|]].
- refine (conj Hnf (conj HC (conj Hc (conj Hm (conj Ht (conj R23 (conj R27 (conj _ (conj HRC (conj HMC
    (conj HSTR HCNT))))))))))).
  intros o v Hov. apply HSL. unfold s16_L0, s16_L in *. apply in_app_or in Hov as [Hov|Hov]; apply in_or_app;
    [left; exact Hov | right; right; exact Hov].
- apply HSL. unfold s16_L. apply in_or_app. right. left. reflexivity.
Qed.
(* s16_inv carried to a state that changes only m's block and the stack below s1 (an m_refuse call's window, the
   loop's stores into m) *)
Lemma s16_inv_carry : forall cx f ly S (W : world SEGS) regs mem md k acc c m t mc
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 mc2,
  lt_base B MT cx -> s16_inv B MT cx f ly S W regs mem md k acc c m t mc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 -> getr regs2 18 = getr regs 18 ->
  getr regs2 23 = getr regs 23 -> getr regs2 27 = getr regs 27 ->
  Permutation (ablocks B ly2 S2) (ablocks B ly S) -> mo_le MT (x_S cx) S2 acc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (m <= a < m + seg_spec.SEG_M_SIZE) ->
     ~ (x_s1 cx - STK_m_refuse <= a < x_s1 cx) -> rdW W2 mem2 a = rdW W mem a) ->
  sa_mconf (rdW W2 mem2) m mc2 ->
  s16_inv B MT cx f ly2 S2 W2 regs2 mem2 md2 k acc c m t mc2.
Proof.
intros cx f ly S W regs mem md k acc c m t mc ly2 S2 W2 regs2 mem2 md2 mc2 HB HI HJ2 E2 E3 E4 E8 E9 E18 E23 E27
  HP2 HMO HK HMC2.
destruct (s16_inv_inv0 cx f ly S W regs mem md k acc c m t mc HI) as (HI0 & R18 & H112).
pose proof HI0 as (_ & (HFR & _) & _ & Hm & _).
pose proof HFR as (HJ & _). pose proof (proj1 HJ) as HAR.
pose proof Hm as (HmIn & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HmIn) as (_ & Hm0 & Hmc & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmc.
destruct (s16_stk cx HB) as (Hsp16 & Hsp & Hs1m & Hs1).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
apply (s16_inv_carry0 cx f ly S W regs mem md k acc c m t mc ly2 S2 W2 regs2 mem2 md2 mc2 HB HI0 HJ2 E2 E3 E4 E8 E9
  ltac:(rewrite E18; exact R18) E23 E27 HP2 HMO); [| |exact HMC2].
- intros a Ha H1 H2 _. exact (HK a Ha H1 H2).
- rewrite <- H112. apply s16_rdword_ext. intros j Hj. apply HK; unfold seg_spec.SEG_M_SIZE; lia.
Qed.

(* ===================================== the m_refuse(m, 0) call ===================================== *)
(* m_refuse's contract (lib/A/Prog/m_refuse_c.v) at every FP state, at the listing's entry and window; its
   literal map is fuzz_segconf.c's (m_refuse is that module's function) *)
Hypothesis MREF : forall fx0 : YK11.FPState,
  @m_refuse_contract fx0 rc SK SEGS B (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A seg_litA_fz gotwA guardA.
Hypothesis MTFL : ameter_fs_laws MT.
(* 0x852bc / 0x852ec: jal m_refuse with a0 = m, a1 = 0, through PaFx.v's cl_callSF (the callee returns at some FP
   state fx1, fxrel fx fx1), its contract applied at the call's state; the cut's facts carried past it (the callee
   writes only its stack window and kept[n_kept], n_kept, refused of m, and changes the state by set_fs only) *)
Lemma s16_call : forall cx f ly S (W : world SEGS) regs mem md k acc c m t mc ra,
  lt_base B MT cx -> sa_frm0 ->
  s16_inv B MT cx f ly S W regs mem md k acc c m t mc ->
  getr regs 1 = w64 (BASE + ra) -> 0 <= ra < 2 ^ 40 -> ra mod 2 = 0 ->
  getr regs 10 = w64 m -> getr regs 11 = w64 0 ->
  SegModel.mc_refused mc + 1 < 2 ^ 32 ->
  (forall (fx1 : YK11.FPState) ly2 S2 (W2 : world SEGS) regs2 mem2 md2, fxrel fx fx1 ->
     s16_inv B MT cx f ly2 S2 W2 regs2 mem2 md2 k acc c m t (SegModel.m_refuse mc 0 false) ->
     aregs_preserved regs regs2 ->
     SRr SEGS W2 (mkCfg (@mkst fx1 regs2 (w64 (BASE + ra)) mem2 (seg_rom SEGS)) md2) (lt_post (fx := fx1) B MT cx)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_m_refuse)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros cx f ly S W regs mem md k acc c m t mc ra HB HFRM HI R1 Hra0 Hra2 R10 R11 HROOM HK.
pose proof HI as (Hnf & (HFR & HIMG & HBL & HBUD) & Hc & Hm & Ht & R18 & R23 & R27 & HSL & HRC & HMC & HSTR & HCNT).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof HB as (HPRE0 & HAP0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
destruct (s16_stk cx HB) as (Hsp16 & Hsp & Hs1m & Hs1).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev0 & _).
pose proof HBUD as (Hk0 & Hrem0 & Hkrem & HMO & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HSM : STK_m_refuse = 8240) by reflexivity.
pose proof Hm as (HmIn & Hm4 & Hm16 & HmA).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HmIn) as (_ & Hm0 & Hmc & Hmapp & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmc, Hmapp.
assert (Htn1 : 0 < x_tn cx f) by (unfold x_tn, seg_spec.seg_txt_n; lia).
destruct (s16_blocks_apart cx ly S W mem md t (x_tn cx f) m c HAR HBL Htn1) as (_ & _ & _ & HmN).
(* m_refuse_pre: the block, its bytes, its tail word, the counters, printf's machine facts, the formats *)
pose proof (proj1 HIMG) as HROD.
pose proof (proj1 (proj2 HIMG)) as (_ & _ & HFZ & _ & _ & _ & _ & _ & HSSP & _).
assert (HLITS : forall x, In x M_REFUSE_LITS -> sa_lit SEGS B (rdW W mem) (seg_litA_fz x) x).
{ intros x Hx. exact (proj1 (HFZ x (proj1 (proj2 lits_incl) x Hx))). }
assert (HTAIL : sa_tail (rdW W mem) (m + seg_spec.SEG_M_SIZE - 1)).
{ intros x Hx. apply (AR_block_word_vis SEGS B ly S W mem md m seg_spec.SEG_M_SIZE (m + seg_spec.SEG_M_SIZE - 1) x
    HAR HmIn); change (req_size seg_spec.SEG_M_SIZE) with 9236; unfold seg_spec.SEG_M_SIZE in *; lia. }
(* the frame chain at the call's sp: s0 = SP0, the stack from the call's sp to the top is present *)
assert (HAP : astack_pres ly (w_H W) mem (x_sp0 cx - STK_LLVMFuzzerTestOneInput)).
{ apply (astack_pres_journal SEGS B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAP0).
  intros a (r & Hr & Hlo & Hhi) Ha. unfold ltoi_PG in Hr. cbn [In] in Hr.
  destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi. unfold longlA, A_LONGL, LONGL_N in Hhi.
  exfalso. unfold x_sp0 in *. lia. }
pose proof (astack_rd_of_pres SEGS ly (w_H W) mem (x_s1 cx)
  (astack_pres_mono ly (w_H W) mem (x_sp0 cx - STK_LLVMFuzzerTestOneInput) (x_s1 cx) ltac:(lia) HAP)) as HRD.
destruct (achain_any ly (rdW W mem) (x_s1 cx) (x_sp0 cx) HRD ltac:(right; right; right; lia)) as (ch1 & Hch).
assert (Hsp' : spZ regs = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hal : (x_s1 cx - x_sp0 cx) mod 16 = 0) by lia.
assert (Hch' : achain ly (rdW W mem) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regs) ch1).
{ replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia.
  unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. exact Hch. }
pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBLO.
assert (Hraw : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold w64; apply ret_ok_codeptr_v; [lia | exact Hra2]).
assert (Hra4 : 4096 <= bv_unsigned (getr regs 1)).
{ rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia. }
eapply SRr_bind.
{ apply (cl_callSF B LAWS W regs mem (Z_to_bv 64 (BASE + AF_m_refuse)) STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k
    STK_m_refuse (m_refuse_W m mc) EV_m_refuse (x_s1 cx - x_sp0 cx) (getr regs 1) ch1
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' =>
       sa_mconf (rdW W' mem') m (SegModel.m_refuse mc 0 false) /\
       sa_kept SEGS W mem W' mem' regs STK_m_refuse
         (fun a =>
          (Z.of_nat (length (SegModel.mc_kept mc)) < 8 /\
           seg_spec.kept_addr m (length (SegModel.mc_kept mc)) <= a <
           seg_spec.kept_addr m (length (SegModel.mc_kept mc)) + seg_spec.MC_KEPT_LEN) \/
          (Z.of_nat (length (SegModel.mc_kept mc)) < 8 /\ m + seg_spec.MC_NKEPT <= a < m + seg_spec.MC_NKEPT + 4) \/
          m + seg_spec.MC_REFUSED <= a < m + seg_spec.MC_REFUSED + 4) /\
       sa_noalloc B ly S ly' S')
    HJ Hsp' Hal ltac:(lia) ltac:(rewrite HSM; lia) ltac:(rewrite HSM, HSTK; lia)
    ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0) eq_refl Hraw Hra4 Hch').
  - intros HPRE1. refine (MREF fx ly S W regs mem md ch1 m 0 mc false HPRE1 HROD R10 _ R11 _ _).
    + lia.
    + split; [lia|]. split; [exact Hm16|]. split; [exists m, seg_spec.SEG_M_SIZE; split; [exact HmIn | lia]|].
      split; [exact HmA|]. split; [exact HMC|]. split; [exact HTAIL|]. split; [lia|]. split; [exact HROOM|].
      split; [exact HFRM|]. split; [exact HSSP | exact HLITS].
    + unfold EV_m_refuse. lia.
  - intros a (r & Hr & Hlo & Hhi). right. exists m, seg_spec.SEG_M_SIZE.
    split; [exact HmIn|]. split; [exact HmN|]. change (req_size seg_spec.SEG_M_SIZE) with 9236.
    unfold m_refuse_W in Hr. destruct (Z.of_nat (length (SegModel.mc_kept mc)) <? 8) eqn:EK.
    + apply Z.ltb_lt in EK. cbn [app In] in Hr.
      destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi;
        unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_NKEPT,
          seg_spec.MC_REFUSED in *; lia.
    + cbn [app In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi. unfold seg_spec.MC_REFUSED in *. lia. }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & H01 & -> & HJ2 & _ & HP & (HMC2 & HKP & HNA)).
replace (k + EV_m_refuse) with k in HJ2 by (unfold EV_m_refuse; lia).
destruct HNA as (HP2 & -> & (ff & ->)).
assert (HPr : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr regs r)
  by (intros r z Hz <-; exact (HP z Hz)).
assert (HI2 : s16_inv B MT cx f ly (set_fs ff S) W2 regs2 mem2 md2 k acc c m t (SegModel.m_refuse mc 0 false)).
{ apply (s16_inv_carry cx f ly S W regs mem md k acc c m t mc ly (set_fs ff S) W2 regs2 mem2 md2 _ HB HI HJ2
    (HPr 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))
    (HPr 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))
    (HPr 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))
    (HPr 8%bv 8 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))
    (HPr 9%bv 9 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))
    (HPr 18%bv 18 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))
    (HPr 23%bv 23 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))
    (HPr 27%bv 27 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity))
    HP2 (mo_le_set_fs_r MT MTFL (x_S cx) S ff acc HMO)); [|exact HMC2].
  intros a Ha H1 H2. apply HKP; [exact Ha | rewrite Hsp'; lia |].
  unfold seg_spec.kept_addr, seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_NKEPT, seg_spec.MC_REFUSED,
    seg_spec.SEG_M_SIZE in *. lia. }
rewrite R1. unfold lt_post. eapply srr_apost_baseF_lift; [exact H01|].
exact (HK fx1 ly (set_fs ff S) W2 regs2 mem2 md2 H01 HI2 HP).
Qed.
End k.
