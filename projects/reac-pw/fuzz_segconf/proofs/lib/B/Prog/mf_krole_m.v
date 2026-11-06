(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 158 of its 182 lines of code are new or changed and 494 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KROLE (KDISP 0x86714 ->
   KMODEL 0x86840 or KDONE 0x86c1c; the image-B m_file segment table section 7, the image-B m_file cut map section 4, 101
   instructions owned): the inner points of the segment and the model facts its pieces use. Statement text and
   Gallina proofs; no instruction is executed here. A walk lane of the image-B m_file-family owner's G2B. Adapted from image A's
   lib/A/Prog/m_file_s_krole_m.v (the image-A m_file-family lane, commit e8a825b42b08): the
   model facts are A's text (renamed nothing; this file is the only kr_* writer of image B); the points are image
   B's (B calls fold, A inlines it; B keeps line + 1 in s11, A spills it to 96(s1)).

   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s lines 375-417, 484-523, 696, 723-734, 866-867, 883-885):
     0x86714-0x8671c a2 = 0x21120 "role" (listing object 17), a1 = s5 = kl (a0 = k from 0x866e0)
     0x86720 jal ieq; 0x86724 `beqz a0` -> KMODEL 0x86840 ("role" missed)
     KR_FOLD 0x86728: a0 = 192(s1) = v, a3 = 64, a1 = s10 = vl, a2 = 144(s1) = low (FB + 32); 0x86738 jal fold
       (lib/B/Prog/fold_c.v: low = h_fold v 64 ++ [0], a0 = min(vl, 63)); 0x8673c s10 = ln
     0x86740-0x86754 s4 = 0, s9 = 0x211e0 &m_key.role (object 18), s5 = 80(s1) = WORDS (object 15), s8 = s5,
       s7 = 72(s1) = shadow(WORDS)
     KR_WORDS 0x86758, pass i = 0 .. 4 (s4 = -4 i, s9 = &role[i], s5 = s8 = &words[i], s7 = shadow(&words[i])):
       `lbu a0,0(s7)`, `bnez a0` -> 0x86ec0 (the instrumented 8-byte check of words[i]; no slow path; its error path
       0x86ec4 errpath_load8 with a0 = s5 is not reached); 0x86760 s6 = words[i]; 0x86768 jal strlen(s6);
       0x8676c `bne a0,s10` -> 0x86784; 0x8677c jal bcmp(s6, 144(s1), s10); 0x86780 `beqz a0` -> KR_HIT 0x868c8;
       0x86784-0x86794 s4 - 4, s9 + 4, s5 + 8, s7 + 1, s8 + 8; 0x8679c `bne s4,-20` -> 0x86758, else KR_MISS
     KR_MISS 0x867a0: s9 = 112(s1) = c; 0x867ac jal m_refuse(c, s11 = line + 1); 0x867b0-0x867b8 s7 = 96(s1),
       s8 = 88(s1), s6 = 128(s1); `j` 0x86c18 `li s4,511` -> KDONE 0x86c1c
     KR_HIT 0x868c8: a1 = -s4 = 4 i, a0 = 0x211e0, a2 = ~a0; s7, s8, s6 back from 96 / 88 / 128(s1);
       0x868e4 `bltu a2,a1` (UBSan trap: m_key.role + 4 i wraps; not taken: 4 i <= 16 < ~0x211e0);
       0x868e8-0x868f0 a1 = 136(s1) & 3, `bnez` (UBSan trap: cur & 3; not taken: cur = c + 256 gi, c mod 16 = 0);
       a0 = &role[i]; the check of role[i] (load4 0x86900, slow path 0x86c84-0x86c90, error path 0x86f04);
       a4 = 136(s1) = g; the check of g->role (store4 0x86918, slow path 0x86c94-0x86ca0, error path 0x86f08);
       0x8691c a1 = role[i] (`lw a1,0(s9)`); s4 = 511; 0x86928 g->role = a1; the check of g->role_set (store4
       0x86938, slow path 0x86ca4-0x86cb0, error path 0x86f0c); s9 = 112(s1) = c; 0x86948 g->role_set = 1;
       0x86960 jal snprintf(g + 60, 96, "%s" (object 14), 64(s1) = &c->reading); `j` KDONE 0x86c1c.

   THE INNER POINTS (listing offset = AF_m_file + (pc - 0x86140)); each states the KDISP cut's facts (kr_cx: the
   premises of MF_KAT_stmt less the registers, plus ieq k "role" = true once 0x86724 has fallen through) and the
   registers the code after it reads:
     KR_FOLD  0x86728 (+0x5e8) ieq answered 1: every register of the cut (mf_regs_at, s5 = kl, s10 = vl, s11 =
                               line + 1) and 192(s1) = v
     KR_WORDS 0x86758 (+0x618) pass i of the words loop, i < 5: words 0 .. i-1 missed, low[0 .. ln] = h_fold v 64
                               and its NUL, s10 = ln
     KR_MISS  0x867a0 (+0x660) no word matched: h_role_word (h_fold v 64) = None
     KR_HIT   0x868c8 (+0x788) word i matched: h_role_word (h_fold v 64) = Some i
   From 0x86740 to the restores s6 .. s9 are borrowed (the image-B m_file cut map C.1: s6 c + 0x2000, s7 FAKE, s8 shadow(FB), s9
   c, reloaded from 128 / 96 / 88 / 112(s1), which mf_cells holds); those points take kr_regs_b, mf_regs_at's
   registers less s6 .. s9 (sp, gp, tp, s0, s1, s2 = SHADOW_OFF, s3 = the blank mask).

   THE PIECES (each `<its exits> -> <its entry>`, at the Section's fx; MF_KMODEL_F / MF_KDONE_F at every fx):
     kr_s_disp  : MF_KMODEL_F B n -> KR_FOLD_stmt B n -> MF_KDISP_stmt B n          (ieq)
     kr_s_fold  : KR_WORDS_stmt B n -> KR_FOLD_stmt B n                              (fold, the loop's set-up)
     kr_s_words : KR_HIT_stmt B n -> KR_MISS_stmt B n -> KR_WORDS_stmt B n           (the words loop)
     kr_s_miss  : MF_KDONE_F B n -> KR_MISS_stmt B n                                 (m_refuse)
     kr_s_hit   : MF_KDONE_F B n -> KR_HIT_stmt B n                                  (the role stores, snprintf)

   THE MODEL FACTS (Gallina only, image A's text): h_fold's length, the words loop's step over SegModel.word_go,
   mk_disp's role branch, snprintf_s of a short C string, the sizes the role branch keeps. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_mdl.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* image B's pure parameters (lib/B/Prog/SegInstB.v), local names of this file as in m_file_m.v *)
#[local] Notation WORDS := SegInstB.wordsA.
#[local] Notation ROLES := SegInstB.rolesA.

(* ===================================== the inner points ===================================== *)
Definition KR_FOLD : Z := AF_m_file + 0x5e8.     (* 0x86728, ieq answered 1: the fold call's set-up *)
Definition KR_WORDS : Z := AF_m_file + 0x618.    (* 0x86758, the words loop's head *)
Definition KR_MISS : Z := AF_m_file + 0x660.     (* 0x867a0, no word matched: m_refuse *)
Definition KR_HIT : Z := AF_m_file + 0x788.      (* 0x868c8, word i matched: the role stores *)
(* the fold's length, fold's answer at 0x86738 (fold_c.v fold_out_length with cap 64): min(vl, 63) *)
Definition kr_ln (vl : nat) : nat := Nat.min vl 63.
(* the folded value, low.i's first ln bytes after the fold (m_key's `h_fold v 64`) *)
Definition kr_low (vv : list Z) : list Z := h_fold vv 64.

(* ===================================== the model facts ===================================== *)
(* lower as a 64-bit unsigned compare computes it (the segconf porter's mfp_facts.v:212 lower_bin) *)
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
Lemma kr_ln_le : forall vl, (kr_ln vl <= 63)%nat.
Proof. intros vl. unfold kr_ln. lia. Qed.
(* fold's answer with cap 64 on the bytes zb vv is kr_ln (length vv) and its text kr_low vv (fold_c.v fold_out) *)
Lemma kr_ln_min : forall vl, Z.of_nat (kr_ln vl) = Z.min (Z.of_nat vl) (64 - 1).
Proof. intros vl. unfold kr_ln. lia. Qed.

(* the words loop (0x86758-0x8679c) over SegModel.word_go: pass i tests word i of m_key.words *)
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

(* m_file_m.v's mf_regs_at less s6 .. s9 (borrowed from 0x86740 to the restores 0x867b0-0x867b8 / 0x868d8-0x868e0
   and 0x867a0 / 0x8693c): sp = s1, gp, tp, s0 = sp0, s1, s2 = SHADOW_OFF, s3 = the blank mask *)
Definition kr_regs_b (v : mfv) (regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (mf_s1 (mv_sp v)) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (mv_sp v) /\ getr regs1 9 = w64 (mf_s1 (mv_sp v)) /\
getr regs1 18 = w64 SHADOW_OFF /\ getr regs1 19 = w64 MF_BLANK.
Lemma kr_regs_b_of_at : forall v lyc pos regs1, mf_regs_at B v lyc pos regs1 -> kr_regs_b v regs1.
Proof.
intros v lyc pos regs1 ((R2 & R3 & R4 & R8 & R9 & R18 & _) & R19 & _). repeat split; assumption.
Qed.

(* the facts of the KDISP cut the whole segment keeps (MF_KAT_stmt's premises less the registers), with ieq k
   "role" = true once 0x86724 has fallen through; memc is the memory of the point (the segment's writes before
   the cut KDONE, low.i by fold and the callees' stack windows below s1, lie outside every byte these facts read) *)
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

(* 0x86728, ieq answered 1: the cut's registers (mf_regs_at, s5 = kl, s10 = vl, s11 = line + 1) and 192(s1) = v *)
Definition KR_FOLD_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
kr_cx n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> mf_regs_at B v lyc pos regs1 ->
mf_slot v memc Wc 192 (p + Z.of_nat ov) ->
getr regs1 21 = w64 (Z.of_nat kl) -> getr regs1 26 = w64 (Z.of_nat vl) -> getr regs1 27 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc KR_FOLD.

(* 0x86758, pass i of the words loop: s4 = -4 i, s9 = &role[i], s5 = s8 = &words[i], s7 = shadow(&words[i]),
   s10 = ln, s11 = line + 1; low[0 .. ln] = h_fold v 64 and its NUL; the words before i missed *)
Definition KR_WORDS_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z) (i : nat),
kr_cx n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kr_regs_b v regs1 ->
(i < 5)%nat -> kr_low_at lyc pos Wc memc (kr_low vv ++ [0]) ->
word_go (skipn i MF_ROLE_WORDS) (kr_low vv) (Z.of_nat i) = h_role_word (kr_low vv) ->
getr regs1 26 = w64 (Z.of_nat (kr_ln vl)) -> getr regs1 27 = w64 (line + 1) ->
getr regs1 20 = w64 (- (4 * Z.of_nat i)) -> getr regs1 25 = w64 (ROLES + 4 * Z.of_nat i) ->
getr regs1 21 = w64 (WORDS + 8 * Z.of_nat i) -> getr regs1 24 = w64 (WORDS + 8 * Z.of_nat i) ->
getr regs1 23 = w64 (SHADOW_OFF + WORDS / 8 + Z.of_nat i) ->
mf_at B v Wc regs1 memc mdc KR_WORDS.

(* 0x868c8, word i matched: s4 = -4 i, s9 = &role[i], s11 = line + 1 *)
Definition KR_HIT_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z) (i : nat),
kr_cx n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kr_regs_b v regs1 ->
(i < 5)%nat -> h_role_word (kr_low vv) = Some (Z.of_nat i) ->
getr regs1 20 = w64 (- (4 * Z.of_nat i)) -> getr regs1 25 = w64 (ROLES + 4 * Z.of_nat i) ->
getr regs1 27 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc KR_HIT.

(* 0x867a0, no word matched: s11 = line + 1 *)
Definition KR_MISS_stmt (n : nat) : Prop :=
forall v lyc Sc Wc regs1 memc mdc pos (mcc : mconf) (gi : nat) (line p : Z) (rest : list Z) (ok kl ov vl : nat)
  (k vv : list Z),
kr_cx n v lyc Sc Wc memc mdc pos mcc gi line p rest ok kl ov vl k vv -> kr_regs_b v regs1 ->
h_role_word (kr_low vv) = None -> getr regs1 27 = w64 (line + 1) ->
mf_at B v Wc regs1 memc mdc KR_MISS.
End e.
End f.
End d.
