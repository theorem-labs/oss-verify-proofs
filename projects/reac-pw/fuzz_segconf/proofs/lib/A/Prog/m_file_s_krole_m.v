(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 176 of its 201 lines of code are new or changed and 493 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), segment S_MF_KROLE (KDISP 0x86684 -> KMODEL 0x867b8 or KDONE
   0x86cd0; the G2 walk owner's guide/MF-CUTS-A.md section 4, 130 instructions): the inner points of the segment and the
   model facts its pieces use. Statement text and Gallina proofs; no instruction is executed here. The KROLE segment lane
   of the G2 walk owner's G2.

   THE CODE (listing m_file.fuzz_segconf.asan.s):
     0x86684-0x86694 ieq(k, kl, "role"); 0x86698 `beqz a0` -> KMODEL.
     0x8669c-0x866a4 s4 = ln = min(vl, 63); 0x866a8 a7 = 152(s1) = low (FB + 32); 0x866ac `beq s7,s5` (vl = 0) ->
       0x8672c; else 0x866b0-0x866bc a0 = s5 = v, a1 = a2 = low, a3 = ln.
     FOLD 0x866c0-0x8670c (one pass per byte, a3 counted down): the check of v[j] (load1 0x866c8), the check of low[j]
       (store1 0x866d8), a4 = v[j] (0x866dc), low[j] = a4 + 32 * (a4 - 65 <u 26) (0x86700), a0, a1, a2, s5 + 1,
       a3 - 1, `bnez a3` 0x8670c -> 0x866c0; else 0x86710 `j 0x8672c`.
     POST 0x8672c `sd s8,96(s1)` (line + 1), s11 = 0, low[ln] = 0 (0x8673c, no check), s7 = &m_key.role, s5 = s10 =
       80(s1) = WORDS, s8 = 72(s1) = shadow(WORDS).
     WORDS 0x86750-0x86794, pass i = 0 .. 4: the check of words[i] (`lbu a0,0(s8)`, load8, no slow path),
       s6 = words[i] (0x86758), strlen(s6) (0x86760) <> ln -> next (0x86764); bcmp(s6, low, ln) (0x86774) = 0 ->
       HIT 0x868b8; next: s11 - 4, s7 + 4, s5 + 8, s8 + 1, s10 + 8, `bne s11,-20` 0x86794 -> 0x86750; else MISS.
     MISS 0x86798-0x867b4 m_refuse(c = 128(s1), line + 1 = 96(s1)) (0x867a8), s8 = 104(s1), s10 = 120(s1), -> KDONE.
     HIT 0x868b8-0x86938 a0 = &role[i] = m_key.role - s11 (check load4 0x868cc), a4 = cur = 136(s1), the check of
       g->role (store4 0x868e4), a1 = role[i] (0x868e8), s8 = 104(s1), s10 = 120(s1), s5 = 128(s1), g->role = a1
       (0x868fc), the check of g->role_set (store4 0x8690c), s6 = 96(s1), g->role_set = 1 (0x8691c),
       snprintf(g + 60, 96, "%s", 64(s1) = &c->reading) (0x86934), -> KDONE.

   THE INNER POINTS (listing offset = AF_m_file + (pc - 0x85ebc)); each states the KDISP cut's facts (kr_cx, which is
   MF_KAT_stmt's premises less the registers, plus ieq k "role" = true) and the registers the code after it reads:
     KR_FOLD  0x866c0 (+0x804) pass j of the fold, 0 <= j < ln: low[0 .. j) folded
     KR_POST  0x8672c (+0x870) the fold done: low[0 .. ln) = h_fold v 64
     KR_WORDS 0x86750 (+0x894) pass i of the words loop, i < 5: words 0 .. i-1 missed, 96(s1) = line + 1,
                                low[ln] = 0
     KR_HIT   0x868b8 (+0x9fc) word i matched: h_role_word (h_fold v 64) = Some i
     KR_MISS  0x86798 (+0x8dc) no word matched: h_role_word (h_fold v 64) = None
   At KR_WORDS, KR_HIT and KR_MISS s10 is borrowed (s10 = &words[i]) and s8 holds shadow(&words[i]); FAKE and
   shadow(FB) are in 104(s1) / 120(s1) (mf_cells), line + 1 in 96(s1); those points take kr_regs_b, which is
   m_file_m.v's mf_regs_at without its s10 conjunct.

   THE MODEL FACTS (Gallina only): the fold's byte step (lower as the code computes it) and h_fold's prefix, the
   words loop's step over SegModel.word_go, mk_disp's role branch, the sizes a line keeps (so the stores into g lie
   in M_FILE_FP's seg range; the shared lib/A/Prog/m_file_mdl.v gives mf_grows and the m_lines growth). The mconf
   block after the hit's three stores is lib/A/Prog/m_file_s_krole_enc.v. Copied with their sources: lower_bin,
   h_fold_length, h_fold_nth (the plain / image-B owner's lib/Prog/mfp_facts.v:212-231 at dec616e11c2f), renamed kr_* so that no
   name meets another lane's copy. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_mdl.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* image A's pure parameters (lib/A/Prog/SegInstA.v), local names of this file as in m_file_m.v *)
#[local] Notation WORDS := SegInstA.wordsA.
#[local] Notation ROLES := SegInstA.rolesA.

(* ===================================== the inner points ===================================== *)
Definition KR_FOLD : Z := AF_m_file + 0x804.     (* 0x866c0, the fold's loop head *)
Definition KR_POST : Z := AF_m_file + 0x870.     (* 0x8672c, the fold done *)
Definition KR_WORDS : Z := AF_m_file + 0x894.    (* 0x86750, the words loop's head *)
Definition KR_MISS : Z := AF_m_file + 0x8dc.     (* 0x86798, no word matched: m_refuse *)
Definition KR_HIT : Z := AF_m_file + 0x9fc.      (* 0x868b8, word i matched: the role stores *)
(* the fold's length, s4 after 0x866a4: min(vl, 63) *)
Definition kr_ln (vl : nat) : nat := Nat.min vl 63.
(* the folded value, low.i's first ln bytes after the fold (m_key's `h_fold v 64`) *)
Definition kr_low (vv : list Z) : list Z := h_fold vv 64.

(* ===================================== the model facts ===================================== *)
(* lower as the code computes it (0x866e4-0x866fc): c + 32 when (c - 'A') is below 26 as a 64-bit unsigned value
   (mfp_facts.v:212 lower_bin) *)
Lemma kr_lower_bin : forall c, 0 <= c < 256 -> lower c = c + (if (c - 65) mod 2 ^ 64 <? 26 then 32 else 0).
Proof.
  intros c Hc. unfold lower. change (2 ^ 64) with 18446744073709551616.
  destruct (Z.leb_spec 65 c) as [H1|H1].
  - rewrite Z.mod_small by lia.
    destruct (Z.leb_spec c 90), (Z.ltb_spec (c - 65) 26); cbn [andb]; lia.
  - rewrite <- (Z_mod_plus_full (c - 65) 1 18446744073709551616). rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec (c - 65 + 1 * 18446744073709551616) 26); cbn [andb]; lia.
Qed.
Lemma kr_lower_byte : forall c, 0 <= c < 256 -> 0 <= lower c < 256.
Proof. intros c Hc. unfold lower. destruct (Z.leb_spec 65 c), (Z.leb_spec c 90); cbn [andb]; lia. Qed.
(* mfp_facts.v:221 h_fold_length *)
Lemma kr_low_length : forall vv, length (kr_low vv) = kr_ln (length vv).
Proof. intros vv. unfold kr_low, kr_ln, h_fold. rewrite length_map, length_firstn. apply Nat.min_comm. Qed.
(* mfp_facts.v:225 h_fold_nth *)
Lemma kr_low_nth : forall vv j, (j < kr_ln (length vv))%nat -> nth j (kr_low vv) 0 = lower (nth j vv 0).
Proof.
  intros vv j Hj. unfold kr_low, kr_ln, h_fold in *.
  rewrite (@nth_indep Z (map lower (firstn (64 - 1) vv)) j 0 (lower 0))
    by (rewrite length_map, length_firstn; lia).
  rewrite map_nth. f_equal. rewrite nth_firstn. destruct (Nat.ltb_spec j (64 - 1)); [reflexivity|lia].
Qed.
(* a list's first j + 1 items *)
Lemma kr_firstn_snoc : forall (l : list Z) j, (j < length l)%nat -> firstn (S j) l = firstn j l ++ [nth j l 0].
Proof.
  induction l as [|x l IH]; intros j Hj; cbn [length] in Hj; [lia|].
  destruct j as [|j]; [reflexivity|]. cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.
(* one more pass of the fold: the prefix grows by the folded byte j *)
Lemma kr_low_firstn_S : forall vv j, (j < kr_ln (length vv))%nat ->
  firstn (S j) (kr_low vv) = firstn j (kr_low vv) ++ [lower (nth j vv 0)].
Proof.
  intros vv j Hj. rewrite <- (kr_low_nth vv j Hj). apply kr_firstn_snoc. rewrite kr_low_length. exact Hj.
Qed.
Lemma kr_low_firstn_all : forall vv, firstn (kr_ln (length vv)) (kr_low vv) = kr_low vv.
Proof. intros vv. apply firstn_all2. rewrite kr_low_length. lia. Qed.

(* the words loop (0x86750-0x86794) over SegModel.word_go: pass i tests word i of m_key.words *)
Definition kr_wtest (w low : list Z) : bool := (length w =? length low)%nat && leqb (firstn (length low) w) low.
Lemma kr_leqb_eq : forall a b, leqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; cbn [leqb]; split; intros H; try reflexivity; try discriminate.
  - apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst. reflexivity.
  - injection H as -> ->. rewrite Z.eqb_refl. cbn [andb]. apply IH. reflexivity.
Qed.
Lemma kr_wtest_iff : forall w low, kr_wtest w low = true <-> w = low.
Proof.
  intros w low. unfold kr_wtest. rewrite andb_true_iff, Nat.eqb_eq. split.
  - intros [HL HE]. rewrite <- HL, firstn_all in HE. apply kr_leqb_eq. exact HE.
  - intros ->. split; [reflexivity|]. rewrite firstn_all. apply kr_leqb_eq. reflexivity.
Qed.
Lemma kr_word_go_step : forall i low, (i < 5)%nat ->
  word_go (skipn i MF_ROLE_WORDS) low (Z.of_nat i) =
  if kr_wtest (nth i MF_ROLE_WORDS []) low then Some (Z.of_nat i)
  else word_go (skipn (S i) MF_ROLE_WORDS) low (Z.of_nat (S i)).
Proof.
  intros i low Hi. unfold kr_wtest.
  do 5 (destruct i as [|i]; [cbn [skipn nth MF_ROLE_WORDS word_go]; f_equal; lia|]). lia.
Qed.
Lemma kr_word_go_0 : forall low, word_go (skipn 0 MF_ROLE_WORDS) low (Z.of_nat 0) = h_role_word low.
Proof. intros low. reflexivity. Qed.
Lemma kr_word_go_5 : forall low, word_go (skipn 5 MF_ROLE_WORDS) low (Z.of_nat 5) = None.
Proof. intros low. reflexivity. Qed.
(* a role h_role_word answers is a word's index *)
Lemma kr_word_go_range : forall ws low i r, word_go ws low i = Some r -> i <= r < i + Z.of_nat (length ws).
Proof.
  induction ws as [|w ws IH]; intros low i r H; cbn [word_go] in H; [discriminate|].
  destruct ((length w =? length low)%nat && leqb (firstn (length low) w) low).
  - injection H as <-. cbn [length]. lia.
  - apply IH in H. cbn [length]. lia.
Qed.
Lemma kr_role_range : forall low r, h_role_word low = Some r -> 0 <= r < 5.
Proof. intros low r H. apply kr_word_go_range in H. cbn in H. lia. Qed.

(* m_key's role branch (mk_disp with ieq k "role") *)
Lemma kr_mk_disp_role : forall c gi k vv line, ieq k S_role = true ->
  mk_disp c gi k vv line =
  match h_role_word (kr_low vv) with
  | Some r => m_upd c gi (ms_with_role r (snprintf_s 96 F_s [AS (mc_reading c)]))
  | None => m_refuse c line false
  end.
Proof. intros c gi k vv line H. unfold mk_disp. rewrite H. reflexivity. Qed.
(* snprintf(d, 96, "%s", r) stores r itself when r is a C string of at most 95 bytes *)
Lemma kr_cut_nul_id : forall l, ~ In 0 l -> cut_nul l = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. cbn [cut_nul].
  destruct (Z.eqb_spec x 0) as [->|Hx]; [exfalso; apply H; left; reflexivity|].
  f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.
Lemma kr_snprintf_s_reading : forall r, ~ In 0 r -> (length r < 96)%nat -> snprintf_s 96 F_s [AS r] = r.
Proof.
  intros r H0 HL. unfold snprintf_s. change (fmt F_s [AS r]) with (arg_s (AS r) ++ []).
  rewrite app_nil_r. cbn [arg_s]. rewrite kr_cut_nul_id by exact H0.
  apply firstn_all2. change (Z.to_nat (96 - 1)) with 95%nat. lia.
Qed.

(* the role branch keeps seg's length, so the cursor gi stays inside seg *)
Lemma kr_role_seg_len : forall c gi k vv line, ieq k S_role = true ->
  length (mc_seg (mk_disp c gi k vv line)) = length (mc_seg c).
Proof.
  intros c gi k vv line H. rewrite (kr_mk_disp_role c gi k vv line H).
  destruct (h_role_word (kr_low vv)).
  - unfold m_upd, m_set_segs. cbn [mc_seg]. apply upd_nth_length.
  - destruct (m_refuse_sizes c line false) as [E _]. rewrite E. reflexivity.
Qed.
(* what the final model keeps of the state after the role branch: its seg and kept sizes *)
Lemma kr_fin_grows : forall c gi k vv line rest, ieq k S_role = true -> (gi < length (mc_seg c))%nat ->
  mf_grows (mk_disp c gi k vv (line + 1)) (mf_fin (mk_disp c gi k vv (line + 1), Some gi) line rest).
Proof.
  intros c gi k vv line rest H Hgi. unfold mf_fin.
  refine (proj1 (m_lines_ok _ (mk_disp c gi k vv (line + 1), Some gi) (line + 1) _)).
  cbn [fst snd]. unfold mf_cur_ok. rewrite kr_role_seg_len by exact H. exact Hgi.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.

(* m_file_m.v's mf_regs_at without its s10 conjunct (s10 is borrowed from 0x86748 to 0x868f0) *)
Definition kr_regs_b (v : mfv) (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (mf_s1 (mv_sp v)) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (mv_sp v) /\ getr regs1 9 = w64 (mf_s1 (mv_sp v)) /\
getr regs1 18 = w64 SHADOW_OFF /\ getr regs1 19 = w64 0x20 /\ getr regs1 25 = w64 MF_BLANK.
Lemma kr_regs_b_of_at : forall v lyc pos regs1, mf_regs_at B v lyc pos regs1 -> kr_regs_b v regs1.
Proof. intros v lyc pos regs1 (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & _). repeat split; assumption. Qed.

(* the facts of the KDISP cut the whole segment keeps (MF_KAT_stmt's premises less the registers), with ieq k
   "role" = true once 0x86698 has fallen through; memc is the memory of the point (the segment's own writes, 96(s1)
   and low.i, lie outside every byte these facts read) *)
Definition kr_cx (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
(mdc : Model) (pos : Z) (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
(k vv : list Z) : Prop :=
mf_cx B v /\ mf_ls v lyc Sc /\ sa_frm0 /\
mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc /\ mf_cells v lyc pos memc Wc (Some gi) /\
(length rest <= n)%nat /\ rest <> [] /\ mf_loop v Wc memc mcc (Some gi) line p rest /\
mk_kv rest ok kl ov vl k vv /\ mf_fin (mk_disp mcc gi k vv (line + 1), Some gi) line rest = mf_final v /\
mf_np v memc Wc (mf_next p rest) /\ ieq k S_role = true.

(* low.i (FB + 32) holds the bytes l from its first byte *)
Definition kr_low_at (lyc : alayout) (pos : Z) (Wc : world SEGS) (memc : word -> option byte) (l : list Z) : Prop :=
sa_zs (rdW Wc memc) (frame_addr lyc 1 pos + 32) l.
(* 96(s1) holds line + 1 (0x8672c) *)
Definition kr_line_at (v : mfv) (Wc : world SEGS) (memc : word -> option byte) (line : Z) : Prop :=
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 96) 8 (line + 1).

(* 0x866c0, pass j of the fold: a0 = s5 = v + j, a1 = a2 = low + j, a3 = ln - j, s4 = ln, a7 = low, s8 = line + 1 *)
Definition KR_FOLD_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z) (j : nat),
kr_cx n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> mf_regs_at B v lyc pos regs1 ->
(j < kr_ln vl)%nat -> kr_low_at lyc pos Wc memc (firstn j (kr_low vv)) ->
getr regs1 20 = w64 (Z.of_nat (kr_ln vl)) -> getr regs1 24 = w64 (line + 1) ->
getr regs1 17 = w64 (frame_addr lyc 1 pos + 32) ->
getr regs1 21 = w64 (p + Z.of_nat (ov + j)) -> getr regs1 10 = w64 (p + Z.of_nat (ov + j)) ->
getr regs1 11 = w64 (frame_addr lyc 1 pos + 32 + Z.of_nat j) ->
getr regs1 12 = w64 (frame_addr lyc 1 pos + 32 + Z.of_nat j) ->
getr regs1 13 = w64 (Z.of_nat (kr_ln vl - j)) ->
mf_at B v Wc regs1 memc mdc KR_FOLD.

(* 0x8672c, the fold done: s4 = ln, a7 = low, s8 = line + 1 *)
Definition KR_POST_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
kr_cx n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> mf_regs_at B v lyc pos regs1 ->
kr_low_at lyc pos Wc memc (kr_low vv) ->
getr regs1 20 = w64 (Z.of_nat (kr_ln vl)) -> getr regs1 24 = w64 (line + 1) ->
getr regs1 17 = w64 (frame_addr lyc 1 pos + 32) ->
mf_at B v Wc regs1 memc mdc KR_POST.

(* 0x86750, pass i of the words loop: s11 = -4 i, s7 = &role[i], s10 = &words[i], s8 = shadow(&words[i]),
   s4 = ln, 96(s1) = line + 1, low[0 .. ln] = h_fold v 64 and its NUL; the words before i missed *)
Definition KR_WORDS_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z) (i : nat),
kr_cx n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kr_regs_b v regs1 ->
(i < 5)%nat -> kr_low_at lyc pos Wc memc (kr_low vv ++ [0]) -> kr_line_at v Wc memc line ->
word_go (skipn i MF_ROLE_WORDS) (kr_low vv) (Z.of_nat i) = h_role_word (kr_low vv) ->
getr regs1 20 = w64 (Z.of_nat (kr_ln vl)) -> getr regs1 27 = w64 (- (4 * Z.of_nat i)) ->
getr regs1 23 = w64 (ROLES + 4 * Z.of_nat i) -> getr regs1 26 = w64 (WORDS + 8 * Z.of_nat i) ->
getr regs1 24 = w64 (SHADOW_OFF + WORDS / 8 + Z.of_nat i) ->
mf_at B v Wc regs1 memc mdc KR_WORDS.

(* 0x868b8, word i matched: s11 = -4 i, s7 = &role[i], 96(s1) = line + 1 *)
Definition KR_HIT_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z) (i : nat),
kr_cx n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kr_regs_b v regs1 ->
(i < 5)%nat -> kr_line_at v Wc memc line -> h_role_word (kr_low vv) = Some (Z.of_nat i) ->
getr regs1 27 = w64 (- (4 * Z.of_nat i)) -> getr regs1 23 = w64 (ROLES + 4 * Z.of_nat i) ->
mf_at B v Wc regs1 memc mdc KR_HIT.

(* 0x86798, no word matched: 96(s1) = line + 1 *)
Definition KR_MISS_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
kr_cx n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kr_regs_b v regs1 ->
kr_line_at v Wc memc line -> h_role_word (kr_low vv) = None ->
mf_at B v Wc regs1 memc mdc KR_MISS.
End e.
End f.
End d.
