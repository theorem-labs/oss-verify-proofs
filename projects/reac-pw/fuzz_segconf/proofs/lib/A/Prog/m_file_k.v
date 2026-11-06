(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shape join of check_reply's walk (fuzz_command.asan, 0x86fcc .. 0x86ff8),
   ported from proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's segments and
   their program calls, cl_callS then a fresh seed at the return) at c8557374ad2e.

   From CR_JOIN (a0 = the shape string q) the code re-checks the shadow of g_rec.reply, loads the reply into s3 and
   calls syntax_reply_matches(q, reply) (0x86fdc). A match goes to the epilogue CR_EPI; otherwise it calls
   syntax_reply_matches("resp 0" @ 0x210e0, reply) (0x86ff0), and a second miss would abort, which reply_okA's
   second conjunct refutes (0 <= code: one of the two shapes matches). Each run starts from the mid-walk seed
   (check_reply_sd.v cr_seed) with the frame header read-only, so the run changes no byte the walk reads. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s7.v, with its module paths and module names changed; 1313 of its 1367 lines of code are new or changed and 489 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): the generic keep lemmas of its walk, shared by the segment lanes
   of the G2 walk owner's G2 (the m_file keep-lemma lane; one copy, nobody writes local ones). The cut predicates are
   lib/A/Prog/m_file_m.v's (CHANGE 3, commit 942fb04485a4, unchanged at dd4bb5fb2f90).

   WHAT A STEP KEEPS. Between two cuts the walk writes (mf_rw): the callee windows below s1 (and the unused slots
   s1 + 0 .. s1 + 24), the mconf block, its side-stack frame but the flag pointer at FB + 120, the frame's 16
   shadow bytes, the frame's flag byte, and the spill slots [s1 + 24, s1 + 160) (mf_seed's writable slot region).
   Every other byte a cut predicate reads is outside mf_rw: the saved registers, the flag pointer, the text and the
   two blocks' slack. mf_keep / mf_loop_keep carry mf_core / mf_loop across any step whose reader is unchanged
   outside a set RW inside mf_rw, given the new values of the cells mf_rw may hold (low.i's shadow bytes, 112(s1),
   the mconf block); mf_keep_cells / mf_slot_keep keep the slots when RW touches only 96(s1), 136(s1) and 144(s1)
   of them (mf_rws). The shadow of the two heap blocks is taken again from AR at the new state; a slack byte inside
   the frame, its shadow or the flag byte is mapped by AR at the new state (mf_tail_keep).
   The three step shapes: a run of the symbolic executor (mf_keep_run / mf_keep_run_s / mf_keep_run0, after
   kept_of_frame), a runtime entry (mf_keep_art / mf_keep_art0: aj_art_at / aj_art_own_atF / aj_intrin_atS keep
   every byte outside the entry's window below s1 and its cells E inside the mconf block), a program call
   (mf_keep_call / mf_keep_call0: cl_callS with the callee's sa_kept and sa_noalloc). The *0 forms are those with E
   empty, where the block is kept too.
   The facts at the current state that the entry gives: the frame chain cl_callS asks (mf_chain, mf_chain_at,
   from the entry's achain and the saved ra / s0 at sp0 - 8 / sp0 - 16), the event budget (mf_nev), the literals,
   m_key.words / .role, the catalogue, the ROM view, arodata_okP and the stack-protector cells (mf_lit_now,
   mf_words_now, mf_roles_now, mf_cat_now, mf_rom_now, mf_rod_now, mf_ssp_now: image bytes the runtime does not
   own are kept by the journal's image clause, because M_FILE_FP lies inside the mconf block, mf_fp_in_block,
   which needs the model bounds n <= 32, n_kept <= 8 of the final model, mf_final_bnd).
   mf_loop_next steps the line loop's facts to the next line.
   the TAIL / EXIT segment lane's kit (commit 48a979165341 lib/A/Prog/m_file_s_tail_k.v: mf_win,
   mf_frame_facts, mf_block_apart, mf_stack_apart, mf_ftail_apart, mf_blk_c, mf_blk_t, mf_sp0, mf_tx_*, mf_loop_blk,
   mf_loop_hd, mf_aview_all, mf_regs_at_of, mf_carry_eq, mf_val1_of_aview, mf_cur_range) is taken in unchanged in
   statement: the runs inside mf_win (the frame's header and low.i, its shadow, its flag byte).
   Section hypotheses: the shared list (a) of the G2 walk owner's G2; a lemma takes only those it uses (mf_rod_now RELRO,
   mf_ssp_now SSP). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

(* ============================== the model's bounds (no memory) ============================== *)
(* the model's two counts that fix M_FILE_FP's ends: at most 32 entries and 8 kept refusals *)
Definition mf_bnd (mc : mconf) : Prop := (length (mc_seg mc) <= 32)%nat /\ (length (mc_kept mc) <= 8)%nat.
Lemma mf_upd_nth_length : forall {A} i (f : A -> A) l, length (upd_nth i f l) = length l.
Proof. intros A i f l. revert i. induction l as [|x r IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma mf_bnd_refuse : forall c line k, mf_bnd c -> mf_bnd (m_refuse c line k).
Proof.
intros c line k [H1 H2]. unfold mf_bnd, m_refuse. cbn [mc_seg mc_kept]. split; [exact H1|].
destruct (Z.of_nat (length (mc_kept c)) <? 8) eqn:E; [|exact H2].
apply Z.ltb_lt in E. rewrite length_app. cbn [length]. lia.
Qed.
Lemma mf_bnd_upd : forall c i f, mf_bnd c -> mf_bnd (m_upd c i f).
Proof. intros c i f [H1 H2]. unfold mf_bnd, m_upd, m_set_segs. cbn [mc_seg mc_kept]. rewrite mf_upd_nth_length. auto. Qed.
Lemma mf_bnd_header : forall c l line, mf_bnd c -> mf_bnd (fst (m_header c l line)).
Proof.
intros c l line Hb. unfold m_header. cbv zeta.
destruct (memchr l RBR) as [ci|]; [|cbn [fst]; apply mf_bnd_refuse; exact Hb].
repeat match goal with
| |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E
| |- context [m_find ?a ?b] => destruct (m_find a b)
end.
all: cbn [fst].
all: first
[ apply mf_bnd_refuse; first [exact Hb | destruct Hb as [Hb1 Hb2]; split; cbn [mc_seg mc_kept]; assumption]
| apply mf_bnd_upd; first [exact Hb | apply mf_bnd_refuse; exact Hb]
| lazymatch goal with E : (32 <=? _)%nat = false |- _ =>
    destruct Hb as [Hb1 Hb2]; unfold mf_bnd, m_set_segs; cbn [mc_seg mc_kept]; rewrite length_app; cbn [length];
    apply Nat.leb_gt in E; split; lia end ].
Qed.
Lemma mf_bnd_key : forall c g l line, mf_bnd c -> mf_bnd (m_key c g l line).
Proof.
intros c g l line Hb. unfold m_key. cbv zeta.
destruct (memchr l EQ) as [ei|]; [|apply mf_bnd_refuse; exact Hb].
destruct g as [gi|]; [|apply mf_bnd_refuse; exact Hb].
repeat match goal with
| |- context [if ?b then _ else _] => destruct b
| |- context [h_role_word ?a] => destruct (h_role_word a)
| |- context [cat_row ?a] => destruct (cat_row a)
end.
all: first [apply mf_bnd_refuse; exact Hb | apply mf_bnd_upd; exact Hb].
Qed.
Lemma mf_bnd_line : forall st line l, mf_bnd (fst st) -> mf_bnd (fst (m_line st line l)).
Proof.
intros [c cur] line l Hb. cbn [fst] in Hb. unfold m_line.
destruct (512 <=? length l)%nat; [cbn [fst]; apply mf_bnd_refuse; exact Hb|].
destruct (h_strip (h_cut_comment l)) as [|b s]; [exact Hb|].
destruct (b =? LBR); [apply mf_bnd_header; exact Hb | cbn [fst]; apply mf_bnd_key; exact Hb].
Qed.
Lemma mf_bnd_lines : forall ls st n, mf_bnd (fst st) -> mf_bnd (fst (m_lines st n ls)).
Proof.
induction ls as [|l r IH]; intros st n Hb; cbn [m_lines]; [exact Hb|].
apply IH. apply mf_bnd_line. exact Hb.
Qed.
Lemma mf_bnd_file : forall mc s lab, mf_bnd mc -> mf_bnd (SegModel.m_file mc s lab).
Proof.
intros mc s lab [H1 H2]. unfold SegModel.m_file. cbv zeta. apply mf_bnd_lines. cbn [fst]. split; cbn [mc_seg mc_kept]; assumption.
Qed.

(* ============================== the line's text (no memory) ============================== *)
(* the text after the line is a suffix of the text left, shorter when the text left is not empty *)
Lemma mf_break_snd : forall rest,
(length (snd (break_nl rest)) <= length rest)%nat /\
(rest <> [] -> (length (snd (break_nl rest)) < length rest)%nat) /\
snd (break_nl rest) = skipn (length rest - length (snd (break_nl rest))) rest.
Proof.
induction rest as [|b r IH]; [cbn; split; [lia | split; [intros H; exfalso; exact (H eq_refl) | reflexivity]]|].
cbn [break_nl]. destruct (b =? NL).
- cbn [snd length]. split; [lia|]. split; [intros _; lia|].
  replace (S (length r) - length r)%nat with 1%nat by lia. reflexivity.
- destruct IH as (I1 & _ & I3). destruct (break_nl r) as [l q] eqn:E. cbn [snd length] in *.
  split; [lia|]. split; [intros _; lia|].
  replace (S (length r) - length q)%nat with (S (length r - length q)) by lia. cbn [skipn]. exact I3.
Qed.
Lemma mf_nth_skipn : forall {A} (l : list A) j i d, nth i (skipn j l) d = nth (j + i) l d.
Proof.
intros A l. induction l as [|a l IH]; intros [|j] i d; cbn; [destruct i; reflexivity | destruct i; reflexivity | reflexivity | apply IH].
Qed.
(* the tail of a C string from its j-th byte is a C string, with the same end *)
Lemma mf_str_skipn : forall rd p s j, sa_str rd p s -> (j <= length s)%nat ->
sa_str rd (p + Z.of_nat j) (skipn j s).
Proof.
intros rd p s j ((Hz & Hn) & Ht) Hj. split; [split|].
- intros i Hi. rewrite length_app, length_skipn in Hi. cbn [length] in Hi.
  replace (p + Z.of_nat j + Z.of_nat i) with (p + Z.of_nat (j + i)) by lia.
  rewrite (Hz (j + i)%nat) by (rewrite length_app; cbn [length]; lia).
  replace (skipn j s ++ [0]) with (skipn j (s ++ [0])).
  + rewrite mf_nth_skipn. reflexivity.
  + rewrite skipn_app. replace (j - length s)%nat with 0%nat by lia. reflexivity.
- intros Hin. apply Hn. rewrite <- (firstn_skipn j s). apply in_or_app. right. exact Hin.
- rewrite length_skipn. replace (p + Z.of_nat j + Z.of_nat (length s - j)) with (p + Z.of_nat (length s)) by lia. exact Ht.
Qed.
(* the shadow granule of the shadow byte of a, monotone in a *)
Lemma mf_hull_mono : forall a b, 0 <= a -> a <= b ->
shadow_addr a / 8 * 8 <= shadow_addr b / 8 * 8.
Proof.
intros a b Ha Hab. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
apply shadow_mono. exact Hab.
Qed.
(* sa_addr of a sub-range *)
Lemma mf_addr_sub : forall rd q n q' n', sa_addr rd q n -> q <= q' -> q' + n' <= q + n -> 0 < n' ->
sa_addr rd q' n'.
Proof.
intros rd q n q' n' (A1 & A2 & A3 & A4 & A5) H1 H2 H3.
split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|].
split; [intros x Hx; apply A4; lia|].
intros _ s Hs. apply (A5 ltac:(lia)). pose proof (mf_hull_mono q q' ltac:(lia) H1).
pose proof (mf_hull_mono (q' + n' - 1) (q + n - 1) ltac:(lia) ltac:(lia)). lia.
Qed.
(* the 8-byte word of a byte below an aligned bound ends at or below it *)
Lemma mf_word_below : forall e c, 0 <= e < c -> c mod 4096 = 0 -> e - e mod 8 + 8 <= c.
Proof.
intros e c He Hc. pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
pose proof (Z.div_mod c 4096 ltac:(lia)). rewrite Hc in H1. lia.
Qed.
(* the read span of a C string ends at its NUL's word end *)
Lemma mf_span_end : forall a s, 0 <= a ->
a + seg_spec.cstr_span a s = (a + Z.of_nat (length s)) - (a + Z.of_nat (length s)) mod 8 + 8.
Proof.
intros a s Ha. unfold seg_spec.cstr_span. set (e := a + Z.of_nat (length s)).
pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
pose proof (Z.div_mod (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)).
fold e in H1, H2. lia.
Qed.

(* the bytes a run of S_MF_KDONE / S_MF_TAIL / S_MF_EXIT or of a K piece's fold may write: the frame's header and
   low.i [F, F + 96), its 16 shadow bytes, its flag byte (F = the frame, FL = the flag cell) (the TAIL / EXIT segment lane's kit,
   with low.i added as the KMOD fold sub-lane asked) *)
Definition mf_win (F FL a : Z) : Prop :=
  (F <= a < F + 96) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16) \/ a = FL.

(* the line list of the empty text is empty: the tail's exit arm (plain m_file.v) *)
Lemma mf_lines_nil : forall st line, m_lines st line (lines []) = st.
Proof. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the bytes the walk writes between two cuts, outside which every byte a cut predicate reads lies, except the cells
   given anew at each step (low.i's shadow bytes in the frame's shadow, the spill slots, the mconf block's
   contents): the callee windows below s1 and the unused slots s1 + 0 .. s1 + 24; the mconf block; the side-stack
   frame but its flag pointer FB + 120; the frame's 16 shadow bytes; the frame's flag byte; the spill slots
   [s1 + 24, s1 + 160) (mf_seed's writable slot region) *)
Definition mf_rw (v : mfv) (lyc : alayout) (pos a : Z) : Prop :=
  (mv_sp v - SegInstA.STK_m_file <= a < mf_s1 (mv_sp v) + 24) \/
  (mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) \/
  (frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 120) \/
  (SHADOW_OFF + frame_addr lyc 1 pos / 8 <= a < SHADOW_OFF + frame_addr lyc 1 pos / 8 + 16) \/
  a = flag_addr lyc 1 pos \/
  (mf_s1 (mv_sp v) + 24 <= a < mf_s1 (mv_sp v) + 160).
(* a written set that leaves every spill slot of mf_cells but 136(s1) alone: inside the slots it touches only
   96(s1), 136(s1) and 144(s1) *)
Definition mf_rws (v : mfv) (RW : Z -> Prop) : Prop :=
  forall a, RW a -> mf_s1 (mv_sp v) + 24 <= a < mf_s1 (mv_sp v) + 160 ->
  (mf_s1 (mv_sp v) + 96 <= a < mf_s1 (mv_sp v) + 104) \/ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 152).

(* a 64-bit value through w64 *)
Lemma mf_w64_u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof.
intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
#[local] Notation CX v := (mf_cx B v).
(* the journal from the entry that mf_core carries, at a state *)
#[local] Notation JE v pos ly S W mem md :=
  (ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] ly S W mem md 0).
(* mf_core with the mconf block holding mcc with the pending knock flag knock (seg_spec.mconf_encp): the state
   between m_key's `kept_knock[n_kept] = 1` (0x86b84) and m_refuse (0x86ccc) has knock = true. mf_core is
   mf_corek false by conversion (SegABase.sa_mconf = sa_mconfp false). The *_k lemmas take it as the pre-state;
   each lemma without _k is its _k form at knock := false. *)
Definition mf_corek (knock : bool) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
(memc : word -> option byte) (mdc : Model) (pos lowsh : Z) (mcc : mconf) : Prop :=
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v)
  (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc mdc 0 /\
Permutation (ablocks B lyc Sc) (ablocks B (mv_ly v) (mv_S v)) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (frame_addr lyc 1 pos + 120) 8 (flag_addr lyc 1 pos) /\
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H Wc) memc) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh) /\
mf_saved (mrestrict (w_H Wc) memc) (mv_sp v) (mv_regs v) /\
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + 112) 8 (frame_addr lyc 1 pos) /\
sa_mconfp knock (rdW Wc memc) (mv_c v) mcc /\ sa_addr (rdW Wc memc) (mv_c v) seg_spec.SEG_M_SIZE /\
sa_tail (rdW Wc memc) (mv_c v + seg_spec.SEG_M_SIZE - 1).
Lemma mf_corek_of_core : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_corek false v lyc Sc Wc memc mdc pos lowsh mcc.
Proof. intros v lyc Sc Wc memc mdc pos lowsh mcc H. exact H. Qed.
Lemma mf_core_of_corek : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
mf_corek false v lyc Sc Wc memc mdc pos lowsh mcc -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc.
Proof. intros v lyc Sc Wc memc mdc pos lowsh mcc H. exact H. Qed.

(* ============================== the TAIL / EXIT segment lane's kit ============================== *)
(* the frame (1, pos): placed, app memory, its bytes not the runtime's, its flag cell the runtime's *)
Lemma mf_frame_facts : forall lyc Sc (Wc : world SEGS) memc mdc pos,
AR SEGS B lyc Sc Wc memc mdc -> In (1, pos) (frames Sc) ->
4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling /\
in_app (frame_addr lyc 1 pos) 128 /\
(forall a, frame_addr lyc 1 pos <= a < frame_addr lyc 1 pos + 128 -> ~ aowned B lyc Sc a) /\
aowned B lyc Sc (flag_addr lyc 1 pos) /\ flag_addr lyc 1 pos < alloc_ceiling.
Proof.
intros lyc Sc Wc memc mdc pos HAR Hin.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (F1 & F2 & F3).
destruct (al_frames SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (_ & _ & F4 & _).
destruct (al_flag SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (_ & F5 & _ & F6).
change (fs_frame_bytes 1) with 128 in F2, F3, F4.
refine (conj F1 (conj F2 (conj F3 (conj _ (conj F5 F6))))).
intros a Ha. exact (proj2 (F4 a Ha)).
Qed.

(* the allocator ceiling's bounds and alignment, in the context *)
Ltac mf_ceil := let C1 := fresh "CRlo" in let C2 := fresh "CRhi" in let C3 := fresh "CRal" in
  pose proof (@YG0f.ASAN_CEIL_range rc) as ((C1 & C2) & C3); unfold YG0f.ASAN_CEIL in C1, C2, C3.

(* a byte of a live heap block is outside mf_win *)
Lemma mf_block_apart : forall lyc Sc (Wc : world SEGS) memc mdc pos b m a,
AR SEGS B lyc Sc Wc memc mdc -> In (1, pos) (frames Sc) -> In (b, m) (ablocks B lyc Sc) ->
b <= a < b + req_size m -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a.
Proof.
intros lyc Sc Wc memc mdc pos b m a HAR Hin Hb Ha.
destruct (mf_frame_facts _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR Hb) as (_ & B4096 & Bceil & Bapp & Bpn & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 1 pos HAR Hb Hin) as Hsep.
change (fs_frame_bytes 1) with 128 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
mf_ceil.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
unfold mf_win. intros [Hw | [Hw | Hw]].
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
- apply (proj2 (Bpn a Ha)). rewrite Hw. exact F5.
Qed.

(* a byte at or above the allocator's ceiling (the stack band) is outside mf_win *)
Lemma mf_stack_apart : forall lyc Sc (Wc : world SEGS) memc mdc pos a,
AR SEGS B lyc Sc Wc memc mdc -> In (1, pos) (frames Sc) -> alloc_ceiling <= a ->
~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a.
Proof.
intros lyc Sc Wc memc mdc pos a HAR Hin Ha.
destruct (mf_frame_facts _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
mf_ceil.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
unfold mf_win, SHADOW_OFF. lia.
Qed.

(* the frame's bytes [FB + 96, FB + 128) (the redzone, the flag pointer at FB + 120) are outside mf_win *)
Lemma mf_ftail_apart : forall lyc Sc (Wc : world SEGS) memc mdc pos a,
AR SEGS B lyc Sc Wc memc mdc -> In (1, pos) (frames Sc) ->
frame_addr lyc 1 pos + 96 <= a < frame_addr lyc 1 pos + 128 ->
~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a.
Proof.
intros lyc Sc Wc memc mdc pos a HAR Hin Ha.
destruct (mf_frame_facts _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
mf_ceil.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
unfold mf_win. intros [Hw | [Hw | Hw]].
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
- apply (F4 a ltac:(lia)). rewrite Hw. exact F5.
Qed.

(* the mconf block and the text block at a mid-walk state, from the entry's m_file_pre and mf_core's Permutation *)
Lemma mf_blk_c_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= b + req_size m.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE.
destruct CX0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
destruct HMP as (_ & _ & _ & (b & m & Hin & Hb1 & Hb2) & _).
destruct CORE as (HJ & HPerm & _). pose proof HJ as (HAR & _).
assert (Hin' : In (b, m) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR Hin') as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as Hr.
exists b, m. split; [exact Hin'|]. lia.
Qed.
Lemma mf_blk_c : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= b + req_size m.
Proof. exact (mf_blk_c_k false). Qed.
Lemma mf_blk_t_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= mv_t v /\
mv_t v + Z.of_nat (length (mv_s v)) + 1 <= b + req_size m.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE.
destruct CX0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
destruct HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (b & m & Hin & Hb1 & Hb2) & _).
destruct CORE as (HJ & HPerm & _). pose proof HJ as (HAR & _).
assert (Hin' : In (b, m) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hin).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR Hin') as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as Hr.
exists b, m. split; [exact Hin'|]. lia.
Qed.
Lemma mf_blk_t : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= mv_t v /\
mv_t v + Z.of_nat (length (mv_s v)) + 1 <= b + req_size m.
Proof. exact (mf_blk_t_k false). Qed.

(* the stack numbers of the entry: sp0 is 16-aligned, the 8,560 bytes below it are above the ceiling *)
Lemma mf_sp0 : forall v, CX v ->
alloc_ceiling + SegInstA.STK_m_file <= mv_sp v /\ mv_sp v <= 2 ^ 47 /\ mv_sp v mod 16 = 0.
Proof.
intros v CX0. destruct CX0 as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _). unfold mv_sp. lia.
Qed.

(* a reader that is unchanged outside mf_win keeps the stack words *)
Lemma mf_tx_stack8 : forall lyc Sc (Wc : world SEGS) memc mdc memc' pos a x,
AR SEGS B lyc Sc Wc memc mdc -> In (1, pos) (frames Sc) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a -> rdW Wc memc' a = rdW Wc memc a) ->
alloc_ceiling <= a -> a + 8 <= 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H Wc) memc) a 8 x -> val_mem SEGS (mrestrict (w_H Wc) memc') a 8 x.
Proof.
intros lyc Sc Wc memc mdc memc' pos a x HAR Hin K Ha Hn V.
apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc memc' a a 8 x); [|exact V].
intros k Hk. change (Z.of_nat 8) with 8 in Hk. mf_ceil.
apply K; [lia | apply (mf_stack_apart _ _ _ _ _ _ _ HAR Hin); lia].
Qed.

(* the mconf block's bytes across such a change *)
Lemma mf_tx_mconf : forall v lyc Sc (Wc : world SEGS) memc mdc memc' pos lowsh mcc mc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a -> rdW Wc memc' a = rdW Wc memc a) ->
sa_mconf (rdW Wc memc) (mv_c v) mc -> sa_mconf (rdW Wc memc') (mv_c v) mc.
Proof.
intros v lyc Sc Wc memc mdc memc' pos lowsh mcc mc CX0 CORE K (bs & Hbs & Henc).
destruct (mf_blk_c v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE) as (b & m & Hb & Hb1 & Hb2).
pose proof CORE as (HJ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR Hb) as (_ & B4096 & Bceil & _).
pose proof (proj1 Henc) as Hlen. mf_ceil.
exists bs. split; [|exact Henc].
intros i Hi. unfold seg_spec.SEG_M_SIZE in *.
rewrite K; [apply Hbs; exact Hi | lia |].
apply (mf_block_apart _ _ _ _ _ _ b m _ HAR Hin Hb). lia.
Qed.

(* mf_core across a change that keeps every byte outside mf_win, keeps every mapped byte mapped, has the journal at
   the new memory and gives low.i's 8 shadow bytes their new value *)
Lemma mf_tx_core : forall v lyc Sc (Wc : world SEGS) memc mdc memc' mdc' pos lowsh lowsh' mcc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
JE v pos lyc Sc Wc memc' mdc' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a -> rdW Wc memc' a = rdW Wc memc a) ->
(forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H Wc) memc') (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh') ->
mf_core B v lyc Sc Wc memc' mdc' pos lowsh' mcc.
Proof.
intros v lyc Sc Wc memc mdc memc' mdc' pos lowsh lowsh' mcc CX0 CORE HJ' K G VSH'.
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V112 & Hmc & Hac & Htl).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HJ' as (HAR' & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_sp0 v CX0) as (S1 & S2 & S3).
destruct (mf_blk_c v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE) as (b & m & Hb & Hb1 & Hb2).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR Hb) as (_ & B4096 & Bceil & _).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
mf_ceil.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
split; [exact HJ'|]. split; [exact HPerm|]. split.
{ apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc memc' (frame_addr lyc 1 pos + 120) (frame_addr lyc 1 pos + 120) 8
    (flag_addr lyc 1 pos)); [|exact VFL].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply K; [lia | apply (mf_ftail_apart _ _ _ _ _ _ _ HAR Hin); lia]. }
split; [exact VSH'|]. split.
{ intros j r Hj.
  assert (Hj13 : (j < length mf_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length mf_saved_regs] in Hj13.
  apply (mf_tx_stack8 lyc Sc Wc memc mdc memc' pos _ _ HAR Hin K); [lia | lia | exact (VSV j r Hj)]. }
split.
{ apply (mf_tx_stack8 lyc Sc Wc memc mdc memc' pos _ _ HAR Hin K); [unfold mf_s1; lia | unfold mf_s1; lia | exact V112]. }
split; [exact (mf_tx_mconf v lyc Sc Wc memc mdc memc' pos lowsh mcc mcc CX0 CORE K Hmc)|].
split.
{ destruct Hac as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ b m _ _ HAR' Hb); lia|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ b m _ _ HAR' Hb); unfold seg_spec.SEG_M_SIZE in *; lia. }
intros x Hx. apply G. exact (Htl x Hx).
Qed.

(* the spill slots across the same change *)
Lemma mf_tx_cells : forall v lyc Sc (Wc : world SEGS) memc mdc memc' pos lowsh mcc cur,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a -> rdW Wc memc' a = rdW Wc memc a) ->
mf_cells v lyc pos memc Wc cur -> mf_cells v lyc pos memc' Wc cur.
Proof.
intros v lyc Sc Wc memc mdc memc' pos lowsh mcc cur CX0 CORE K CELLS.
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_sp0 v CX0) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
mf_ceil.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
unfold mf_cells in CELLS |- *.
destruct CELLS as (V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V104 & V120 & V128 & V136 & V152).
repeat split; (apply (mf_tx_stack8 lyc Sc Wc memc mdc memc' pos _ _ HAR Hin K); [unfold mf_s1; lia | unfold mf_s1; lia | assumption]).
Qed.

(* the next line's address in 144(s1) across the same change *)
Lemma mf_tx_np : forall v lyc Sc (Wc : world SEGS) memc mdc memc' pos lowsh mcc np,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
(forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a -> rdW Wc memc' a = rdW Wc memc a) ->
mf_np v memc Wc np -> mf_np v memc' Wc np.
Proof.
intros v lyc Sc Wc memc mdc memc' pos lowsh mcc np CX0 CORE K V.
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_sp0 v CX0) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
mf_ceil.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
unfold mf_np in V |- *.
apply (mf_tx_stack8 lyc Sc Wc memc mdc memc' pos _ _ HAR Hin K); [unfold mf_s1; lia | unfold mf_s1; lia | exact V].
Qed.

(* the text left lies in the text's block *)
Lemma mf_loop_blk_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc mcc' cur line p rest,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcc' cur line p rest ->
exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= p /\ p + Z.of_nat (length rest) + 1 <= b + req_size m /\
mv_t v <= p.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc mcc' cur line p rest CX0 CORE LOOP.
destruct (mf_blk_t_k knock v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE) as (b & m & Hb & Hb1 & Hb2).
pose proof LOOP as (L1 & _ & L3 & _).
rewrite Nat2Z.inj_sub in L3 by exact L1.
exists b, m. split; [exact Hb|]. lia.
Qed.
Lemma mf_loop_blk : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc mcc' cur line p rest,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcc' cur line p rest ->
exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= p /\ p + Z.of_nat (length rest) + 1 <= b + req_size m /\
mv_t v <= p.
Proof. exact (mf_loop_blk_k false). Qed.

(* the line loop's facts across the same change; the text's shadow is taken again from AR at the new state *)
Lemma mf_tx_loop : forall v lyc Sc (Wc : world SEGS) memc mdc memc' mdc' pos lowsh mcc mcc' cur line p rest,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> AR SEGS B lyc Sc Wc memc' mdc' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a -> rdW Wc memc' a = rdW Wc memc a) ->
(forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
mf_loop v Wc memc mcc' cur line p rest -> mf_loop v Wc memc' mcc' cur line p rest.
Proof.
intros v lyc Sc Wc memc mdc memc' mdc' pos lowsh mcc mcc' cur line p rest CX0 CORE HAR' K G LOOP.
destruct (mf_loop_blk v lyc Sc Wc memc mdc pos lowsh mcc mcc' cur line p rest CX0 CORE LOOP)
  as (b & m & Hb & Hb1 & Hb2 & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR Hb) as (_ & B4096 & Bceil & _).
mf_ceil.
destruct LOOP as (L1 & L2 & L3 & ((Lzs & Lnz) & Ltl) & (A1 & A2 & A3 & _ & _) & L6).
split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split.
{ split; [split; [|exact Lnz] | intros x Hx; apply G; exact (Ltl x Hx)].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite K; [apply Lzs; rewrite length_app; cbn [length]; exact Hi | lia |].
  apply (mf_block_apart _ _ _ _ _ _ b m _ HAR Hin Hb). lia. }
split; [|exact L6].
split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ b m _ _ HAR' Hb); lia|].
intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ b m _ _ HAR' Hb); lia.
Qed.

(* the byte at p: the first byte of the text left, 0 exactly when the text left is empty *)
Lemma mf_loop_hd : forall v (Wc : world SEGS) memc mcc cur line p rest,
mf_loop v Wc memc mcc cur line p rest ->
rdW Wc memc p = Some (hd0 rest) /\ (rest = [] <-> hd0 rest = 0).
Proof.
intros v Wc memc mcc cur line p rest LOOP.
destruct LOOP as (_ & _ & _ & ((Lzs & Lnz) & _) & _).
pose proof (Lzs 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as H0.
rewrite Z.add_0_r in H0. rewrite H0.
destruct rest as [|b r]; cbn [app nth hd0].
- split; [reflexivity | tauto].
- split; [reflexivity|]. split; [discriminate|]. intros Hb. exfalso. apply Lnz. rewrite Hb. left; reflexivity.
Qed.

(* readers that agree on [0, 2^64) agree everywhere: a byte address is taken mod 2^64 (fuzz_command's
   check_reply_s7.v cr7_aview_all at origin/ossv/recipes 501c0d516c69) *)
Lemma mf_aview_all : forall (H : word -> bool) (m m' : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' K a.
assert (E : forall mm, aview SEGS H mm a = aview SEGS H mm (a mod 2 ^ 64)).
{ intros mm. unfold aview, mbyte. replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity. }
rewrite !E. apply K. apply Z.mod_pos_bound. lia.
Qed.

(* the registers every cut after the entry names, from nine register equalities *)
Lemma mf_regs_at_of : forall v lyc pos (regs1 regs' : bvmap 5 word),
mf_regs_at B v lyc pos regs1 ->
getr regs' 2 = getr regs1 2 -> getr regs' 3 = getr regs1 3 -> getr regs' 4 = getr regs1 4 ->
getr regs' 8 = getr regs1 8 -> getr regs' 9 = getr regs1 9 -> getr regs' 18 = getr regs1 18 ->
getr regs' 19 = getr regs1 19 -> getr regs' 25 = getr regs1 25 -> getr regs' 26 = getr regs1 26 ->
mf_regs_at B v lyc pos regs'.
Proof.
intros v lyc pos regs1 regs' (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26) E2 E3 E4 E8 E9 E18 E19 E25 E26.
unfold mf_regs_at. rewrite E2, E3, E4, E8, E9, E18, E19, E25, E26.
refine (conj R2 (conj R3 (conj R4 (conj R8 (conj R9 (conj R18 (conj R19 (conj R25 R26)))))))).
Qed.

(* a run that changed no byte (every window of its state empty): the cut facts at the new memory *)
Lemma mf_carry_eq : forall v lyc Sc (Wc : world SEGS) memc mdc memc' mdc' pos lowsh mcc mcc' cur line p rest,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
JE v pos lyc Sc Wc memc' mdc' ->
(forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
mf_loop v Wc memc mcc' cur line p rest ->
mf_core B v lyc Sc Wc memc' mdc' pos lowsh mcc /\ mf_loop v Wc memc' mcc' cur line p rest /\
(forall cur', mf_cells v lyc pos memc Wc cur' -> mf_cells v lyc pos memc' Wc cur') /\
(forall np, mf_np v memc Wc np -> mf_np v memc' Wc np).
Proof.
intros v lyc Sc Wc memc mdc memc' mdc' pos lowsh mcc mcc' cur line p rest CX0 CORE HJ' K0 LOOP.
pose proof (mf_aview_all (w_H Wc) memc memc' K0) as KA.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a ->
  rdW Wc memc' a = rdW Wc memc a) by (intros a _ _; apply KA).
assert (G : forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) by (intros a; rewrite KA; tauto).
pose proof CORE as (_ & _ & _ & VSH & _).
split.
{ apply (mf_tx_core v lyc Sc Wc memc mdc memc' mdc' pos lowsh lowsh mcc CX0 CORE HJ' K G).
  intros i Hi. apply (val_mem_moved SEGS (w_H Wc) (w_H Wc) memc memc' (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i)
    (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh); [|exact (VSH i Hi)].
  intros k _. apply KA. }
split; [exact (mf_tx_loop v lyc Sc Wc memc mdc memc' mdc' pos lowsh mcc mcc' cur line p rest CX0 CORE (proj1 HJ') K G LOOP)|].
split; [intros cur'; exact (mf_tx_cells v lyc Sc Wc memc mdc memc' pos lowsh mcc cur' CX0 CORE K)|].
intros np; exact (mf_tx_np v lyc Sc Wc memc mdc memc' pos lowsh mcc np CX0 CORE K).
Qed.

(* a byte the reader shows, as a one-byte chunk value over the restricted memory *)
Lemma mf_val1_of_aview : forall (H : word -> bool) (m : word -> option byte) a z,
aview SEGS H m a = Some z -> val_mem SEGS (mrestrict H m) a 1 z.
Proof.
intros H m a z Hz. destruct (aview_byte SEGS H m a z Hz) as (b & Hb & -> & Hr).
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
lazymatch goal with |- context [?f (bv_unsigned b) 1%nat 0%nat] => unfold f end.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. rewrite !(Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.

(* the cur cell's value is a 64-bit word: NULL, or an entry of the mconf block (at most 32 entries) *)
Lemma mf_cur_range : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc cur,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cur_ok mcc cur ->
0 <= mf_cur_ptr (mv_c v) cur < 2 ^ 64.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur CX0 CORE Hcur.
destruct cur as [i|]; cbn [mf_cur_ptr mf_cur_ok] in *; [|lia].
destruct (mf_blk_c v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE) as (b & m & Hb & Hb1 & Hb2).
pose proof CORE as (HJ & _ & _ & _ & _ & _ & (bs & _ & Henc) & _).
pose proof HJ as (HAR & _).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR Hb) as (_ & B4096 & Bceil & _).
destruct Henc as (_ & Hlen & _).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((C1 & C2) & _). unfold YG0f.ASAN_CEIL in C1, C2.
unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE in *. lia.
Qed.

(* ============================== the entry's numbers ============================== *)
(* s1 = (sp0 - 288) & -32 is sp0 - 288 or sp0 - 304, 32-aligned; the window below sp0 is above the ceiling *)
Lemma mf_s1_facts : forall v, CX v ->
(mf_s1 (mv_sp v) = mv_sp v - 288 \/ mf_s1 (mv_sp v) = mv_sp v - 304) /\ mf_s1 (mv_sp v) mod 32 = 0 /\
alloc_ceiling + SegInstA.STK_m_file <= mv_sp v.
Proof.
intros v CX0. destruct (mf_sp0 v CX0) as (S1 & S2 & S3).
pose proof (Z.div_mod (mv_sp v - 288) 32 ltac:(lia)) as D32.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (mv_sp v) 16 ltac:(lia)) as D16.
assert (E : (mv_sp v - 288) mod 32 = 0 \/ (mv_sp v - 288) mod 32 = 16) by lia.
unfold mf_s1. split; [lia|]. split; [|exact S1].
replace (mv_sp v - 288 - (mv_sp v - 288) mod 32) with ((mv_sp v - 288) / 32 * 32) by lia. apply Z_mod_mult.
Qed.

(* the final model has at most 32 entries and 8 kept refusals (the entry's block encodes mc, so mc has them) *)
Lemma mf_final_bnd : forall v, CX v ->
(length (mc_seg (mf_final v)) <= 32)%nat /\ (length (mc_kept (mf_final v)) <= 8)%nat.
Proof.
intros v CX0.
destruct CX0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
destruct HMP as (_ & _ & (bs & _ & Henc) & _).
destruct Henc as (_ & H32 & _ & _ & _ & _ & H8 & _).
exact (mf_bnd_file (mv_mc v) (mv_s v) (mv_lab v) (conj H32 H8)).
Qed.

(* every byte of m_file's footprint lies in the mconf block *)
Lemma mf_fp_in_block : forall v a, CX v -> inFP (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) a ->
mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE.
Proof.
intros v a CX0 (r & Hr & Ha). destruct (mf_final_bnd v CX0) as [N1 N2].
unfold M_FILE_FP in Hr. cbn [In] in Hr.
unfold seg_spec.mseg_addr, seg_spec.kept_addr, seg_spec.MSEG_SIZE, seg_spec.MC_N, seg_spec.MC_REFUSED,
  seg_spec.MC_KEPT, seg_spec.MC_KEPT_LEN, seg_spec.MC_KNOCK, seg_spec.MC_NKEPT, seg_spec.MC_READING,
  seg_spec.SEG_M_SIZE in *.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Ha; lia |]). destruct Hr.
Qed.

(* the mconf block at the entry: a live block, its bytes not image bytes *)
Lemma mf_c_entry : forall v, CX v ->
exists b m, In (b, m) (ablocks B (mv_ly v) (mv_S v)) /\ b <= mv_c v /\ mv_c v + seg_spec.SEG_M_SIZE <= b + req_size m /\
4096 <= b /\ b + req_size m <= alloc_ceiling /\
(forall a, b <= a < b + req_size m -> ~ in_img SEGS a).
Proof.
intros v CX0. pose proof CX0 as (HPRE & _). pose proof HPRE as (HAR0 & _).
destruct CX0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
destruct HMP as (_ & _ & _ & (b & m & Hin & Hb1 & Hb2) & _).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR0 Hin) as (_ & B4096 & Bceil & _ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as Hr.
exists b, m. split; [exact Hin|]. split; [lia|]. split; [lia|]. split; [exact B4096|]. split; [exact Bceil|].
intros a Ha. exact (proj2 (al_client_img SEGS B LAWS _ _ _ _ _ a HAR0 (or_introl (ex_intro _ b (ex_intro _ m (conj Hin Ha)))))).
Qed.

(* ============================== the bytes a step may write ============================== *)
(* the facts every mf_rw lemma reads, in the context, under fixed names *)
Ltac mf_geo v lyc Sc pos CX0 CORE :=
  pose proof CORE as (HJg & _); pose proof HJg as (HAR & _ & _ & _ & _ & Hfrs & _);
  assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity);
  destruct (mf_frame_facts _ _ _ _ _ _ HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6);
  destruct (mf_sp0 v CX0) as (Sp1 & Sp2 & Sp3);
  destruct (mf_blk_c_k _ _ _ _ _ _ _ _ _ _ CX0 CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2);
  destruct (al_blocks SEGS B LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Bk1 & Bk2 & Bk3 & Bk4 & _);
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bc mbc 1 pos HAR Hbc Hin) as Hsep;
  change (fs_frame_bytes 1) with 128 in Hsep; unfold zdisjoint in Hsep; cbn [fst snd] in Hsep;
  assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity; rewrite HSTK in Sp1;
  pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32;
  pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8;
  pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8;
  mf_ceil.

(* a byte of the stack band above the spill slots (the saved registers) is outside mf_rw *)
Lemma mf_rw_stack_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc a,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
mf_s1 (mv_sp v) + 160 <= a < mv_sp v -> ~ mf_rw v lyc pos a.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc a CX0 CORE Ha.
mf_geo v lyc Sc pos CX0 CORE.
unfold mf_rw, mf_s1, seg_spec.SEG_M_SIZE, SHADOW_OFF in *.
intros [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]]; lia.
Qed.
Lemma mf_rw_stack : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc a,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
mf_s1 (mv_sp v) + 160 <= a < mv_sp v -> ~ mf_rw v lyc pos a.
Proof. exact (mf_rw_stack_k false). Qed.

(* the frame's last word (the flag pointer) is outside mf_rw *)
Lemma mf_rw_ftail_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc a,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
frame_addr lyc 1 pos + 120 <= a < frame_addr lyc 1 pos + 128 -> ~ mf_rw v lyc pos a.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc a CX0 CORE Ha.
mf_geo v lyc Sc pos CX0 CORE.
unfold mf_rw. intros [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
- lia.
- unfold seg_spec.SEG_M_SIZE in *. lia.
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
- apply (F4 a ltac:(lia)). rewrite Hw. exact F5.
- unfold mf_s1 in *. lia.
Qed.
Lemma mf_rw_ftail : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc a,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
frame_addr lyc 1 pos + 120 <= a < frame_addr lyc 1 pos + 128 -> ~ mf_rw v lyc pos a.
Proof. exact (mf_rw_ftail_k false). Qed.

(* a byte of a live heap block outside the mconf block is outside mf_rw *)
Lemma mf_rw_block_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc b' m' a,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
In (b', m') (ablocks B lyc Sc) -> b' <= a < b' + req_size m' ->
~ (mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) -> ~ mf_rw v lyc pos a.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc b' m' a CX0 CORE Hb' Ha Hnc.
mf_geo v lyc Sc pos CX0 CORE.
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b' m' HAR Hb') as (_ & C1 & C2 & C3 & C4 & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b' m' 1 pos HAR Hb' Hin) as Hsep'.
change (fs_frame_bytes 1) with 128 in Hsep'. unfold zdisjoint in Hsep'. cbn [fst snd] in Hsep'.
unfold mf_rw. intros [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
- lia.
- exact (Hnc Hw).
- lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
- apply (proj2 (C4 a Ha)). rewrite Hw. exact F5.
- unfold mf_s1 in *. lia.
Qed.
Lemma mf_rw_block : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc b' m' a,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
In (b', m') (ablocks B lyc Sc) -> b' <= a < b' + req_size m' ->
~ (mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) -> ~ mf_rw v lyc pos a.
Proof. exact (mf_rw_block_k false). Qed.

(* the slack after a string's NUL (a byte below the ceiling outside the mconf block) is mapped at the new state when
   it was mapped at the old one: kept outside mf_rw, and inside it a byte of the frame, of its shadow or its flag
   byte, which AR at the new state shows *)
Lemma mf_tail_keep_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc S2 (W2 : world SEGS) mem2 md2
  (RW : Z -> Prop) e,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc -> JE v pos lyc S2 W2 mem2 md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mf_rw v lyc pos a) ->
0 <= e < alloc_ceiling ->
(forall x, e < x < e - e mod 8 + 8 -> ~ (mv_c v <= x < mv_c v + seg_spec.SEG_M_SIZE)) ->
sa_tail (rdW Wc memc) e -> sa_tail (rdW W2 mem2) e.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc S2 W2 mem2 md2 RW e CX0 CORE HJ2 K RWok He Hnc HT x Hx Hnone.
mf_geo v lyc Sc pos CX0 CORE.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
assert (Hin2 : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames SEGS B LAWS _ _ _ _ _ 1 pos HAR2 Hin2) as (_ & _ & P1 & P2).
destruct (al_flag SEGS B LAWS _ _ _ _ _ 1 pos HAR2 Hin2) as (P3 & _).
change (fs_frame_bytes 1) with 128 in P1, P2. change (128 / 8) with 16 in P2.
pose proof (mf_word_below e alloc_ceiling He CRal) as Hwe.
assert (D : ~ ~ (RW x \/ ~ RW x)) by tauto.
apply D. intros [HR | HnR].
- pose proof (Hnc x Hx) as Hnc'.
  destruct (RWok x HR) as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
  + lia.
  + exact (Hnc' Hw).
  + exact (aview_some_of_apresent SEGS _ _ _ (proj1 (P1 x ltac:(lia))) Hnone).
  + pose proof (P2 (x - (SHADOW_OFF + frame_addr lyc 1 pos / 8)) ltac:(lia)) as (Pp & _).
    unfold shadow_addr in Pp.
    replace (SHADOW_OFF + frame_addr lyc 1 pos / 8 + (x - (SHADOW_OFF + frame_addr lyc 1 pos / 8))) with x in Pp by lia.
    exact (aview_some_of_apresent SEGS _ _ _ Pp Hnone).
  + rewrite Hw in Hnone. exact (aview_some_of_apresent SEGS _ _ _ P3 Hnone).
  + unfold mf_s1 in *. lia.
- rewrite (K x ltac:(lia) HnR) in Hnone. exact (HT x Hx Hnone).
Qed.
Lemma mf_tail_keep : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc S2 (W2 : world SEGS) mem2 md2
  (RW : Z -> Prop) e,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> JE v pos lyc S2 W2 mem2 md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mf_rw v lyc pos a) ->
0 <= e < alloc_ceiling ->
(forall x, e < x < e - e mod 8 + 8 -> ~ (mv_c v <= x < mv_c v + seg_spec.SEG_M_SIZE)) ->
sa_tail (rdW Wc memc) e -> sa_tail (rdW W2 mem2) e.
Proof. exact (mf_tail_keep_k false). Qed.

(* ============================== the keep lemmas ============================== *)
(* a cell of n bytes outside the written set keeps its value *)
Lemma mf_val_keep : forall (Wc W2 : world SEGS) memc mem2 (RW : Z -> Prop) a n x,
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall k, 0 <= k < Z.of_nat n -> ~ RW (a + k)) ->
val_mem SEGS (mrestrict (w_H Wc) memc) a n x -> val_mem SEGS (mrestrict (w_H W2) mem2) a n x.
Proof.
intros Wc W2 memc mem2 RW a n x K H0 H1 HN V.
apply (val_mem_moved SEGS (w_H Wc) (w_H W2) memc mem2 a a n x); [|exact V].
intros k Hk. apply K; [lia | exact (HN k Hk)].
Qed.

(* the mconf block outside the written set keeps its model *)
Lemma mf_mconf_keep : forall (Wc W2 : world SEGS) memc mem2 (RW : Z -> Prop) c mc,
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) ->
0 <= c -> c + seg_spec.SEG_M_SIZE <= 2 ^ 64 ->
(forall a, c <= a < c + seg_spec.SEG_M_SIZE -> ~ RW a) ->
sa_mconf (rdW Wc memc) c mc -> sa_mconf (rdW W2 mem2) c mc.
Proof.
intros Wc W2 memc mem2 RW c mc K Hc0 Hc1 HN (bs & Hbs & Henc). exists bs. split; [|exact Henc].
pose proof (proj1 Henc) as Hlen.
intros i Hi. rewrite K; [apply Hbs; exact Hi | unfold seg_spec.SEG_M_SIZE in *; lia |].
apply HN. unfold seg_spec.SEG_M_SIZE in *. lia.
Qed.

(* a spill slot of mf_cells other than 136(s1), and 112(s1), keep their value under a written set that touches only
   96(s1), 136(s1) and 144(s1) of the slots (mf_rws) *)
Lemma mf_slot_keep : forall v (Wc W2 : world SEGS) memc mem2 (RW : Z -> Prop) o x,
CX v -> (forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) -> mf_rws v RW ->
24 <= o -> o + 8 <= 96 \/ (104 <= o /\ o + 8 <= 136) \/ (152 <= o /\ o + 8 <= 160) ->
val_mem SEGS (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v) + o) 8 x ->
val_mem SEGS (mrestrict (w_H W2) mem2) (mf_s1 (mv_sp v) + o) 8 x.
Proof.
intros v Wc W2 memc mem2 RW o x CX0 K RWS Ho1 Ho2 V.
destruct (mf_sp0 v CX0) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
mf_ceil.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
apply (mf_val_keep Wc W2 memc mem2 RW _ 8 _ K); [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V].
intros k Hk HR. change (Z.of_nat 8) with 8 in Hk.
destruct (RWS _ HR ltac:(lia)) as [H|H]; lia.
Qed.

(* mf_core across a step whose reader is unchanged outside RW (inside mf_rw), with the journal at the new state,
   the blocks a permutation, low.i's shadow bytes at lowsh', 112(s1) = FB and the mconf block holding mcc' *)
Lemma mf_keep_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc S2 (W2 : world SEGS) mem2 md2
  (RW : Z -> Prop) lowsh' mcc',
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
JE v pos lyc S2 W2 mem2 md2 ->
Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mf_rw v lyc pos a) ->
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H W2) mem2) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh') ->
val_mem SEGS (mrestrict (w_H W2) mem2) (mf_s1 (mv_sp v) + 112) 8 (frame_addr lyc 1 pos) ->
sa_mconf (rdW W2 mem2) (mv_c v) mcc' ->
mf_core B v lyc S2 W2 mem2 md2 pos lowsh' mcc'.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc S2 W2 mem2 md2 RW lowsh' mcc' CX0 CORE HJ2 HP2 K RWok VSH' V112' MC'.
pose proof CORE as (_ & HPerm & VFL & VSH & VSV & V112 & Hmc & Hac & Htl).
mf_geo v lyc Sc pos CX0 CORE.
pose proof HJ2 as (HAR2 & _).
assert (Hbc' : In (bc, mbc) (ablocks B lyc S2)) by (apply (Permutation_in _ (Permutation_sym HP2)); exact Hbc).
split; [exact HJ2|]. split; [exact (perm_trans HP2 HPerm)|]. split.
{ apply (mf_val_keep Wc W2 memc mem2 RW _ 8 _ K); [lia | change (Z.of_nat 8) with 8; lia | | exact VFL].
  intros k Hk HR. change (Z.of_nat 8) with 8 in Hk.
  exact (mf_rw_ftail_k knock v lyc Sc Wc memc mdc pos lowsh mcc (frame_addr lyc 1 pos + 120 + k) CX0 CORE ltac:(lia) (RWok _ HR)). }
split; [exact VSH'|]. split.
{ intros j r Hj.
  assert (Hj13 : (j < length mf_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length mf_saved_regs] in Hj13.
  apply (mf_val_keep Wc W2 memc mem2 RW _ 8 _ K); [lia | change (Z.of_nat 8) with 8; lia | | exact (VSV j r Hj)].
  intros k Hk HR. change (Z.of_nat 8) with 8 in Hk.
  exact (mf_rw_stack_k knock v lyc Sc Wc memc mdc pos lowsh mcc (mv_sp v - 8 - 8 * Z.of_nat j + k) CX0 CORE
    ltac:(unfold mf_s1 in *; lia) (RWok _ HR)). }
split; [exact V112'|].
split; [exact MC'|].
split.
{ destruct Hac as (A1 & A2 & A3 & _ & _). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR2 Hbc'); lia|].
  intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bc mbc _ _ HAR2 Hbc'); unfold seg_spec.SEG_M_SIZE in *; lia. }
apply (mf_tail_keep_k knock v lyc Sc Wc memc mdc pos lowsh mcc S2 W2 mem2 md2 RW _ CX0 CORE HJ2 K RWok); [| | exact Htl].
- unfold seg_spec.SEG_M_SIZE in *. lia.
- intros x Hx. lia.
Qed.
Lemma mf_keep : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc S2 (W2 : world SEGS) mem2 md2
  (RW : Z -> Prop) lowsh' mcc',
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
JE v pos lyc S2 W2 mem2 md2 ->
Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mf_rw v lyc pos a) ->
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H W2) mem2) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh') ->
val_mem SEGS (mrestrict (w_H W2) mem2) (mf_s1 (mv_sp v) + 112) 8 (frame_addr lyc 1 pos) ->
sa_mconf (rdW W2 mem2) (mv_c v) mcc' ->
mf_core B v lyc S2 W2 mem2 md2 pos lowsh' mcc'.
Proof. exact (mf_keep_k false). Qed.

(* the spill slots across a step whose written set touches only 96(s1), 136(s1) and 144(s1) of the slots, with
   136(s1) holding cur' *)
Lemma mf_keep_cells : forall v lyc pos (Wc W2 : world SEGS) memc mem2 (RW : Z -> Prop) cur cur',
CX v ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) -> mf_rws v RW ->
mf_cells v lyc pos memc Wc cur ->
val_mem SEGS (mrestrict (w_H W2) mem2) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur') ->
mf_cells v lyc pos mem2 W2 cur'.
Proof.
intros v lyc pos Wc W2 memc mem2 RW cur cur' CX0 K RWS CELLS V136'.
pose proof (mf_slot_keep v Wc W2 memc mem2 RW) as NS.
unfold mf_cells in CELLS |- *.
destruct CELLS as (V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V104 & V120 & V128 & V136 & V152).
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V24]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V32]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V40]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V48]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V56]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V64]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V72]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V80]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V88]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V104]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V120]|].
split; [apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V128]|].
split; [exact V136'|]. apply NS; [exact CX0 | exact K | exact RWS | lia | lia | exact V152].
Qed.

(* the line loop's facts across a step as in mf_keep: the text's bytes are kept (a heap block's bytes outside the
   mconf block), its slack is mapped (mf_tail_keep), its shadow is taken again from AR at the new state *)
Lemma mf_loop_keep_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc S2 (W2 : world SEGS) mem2 md2
  (RW : Z -> Prop) mc0 cur0 line p rest,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
JE v pos lyc S2 W2 mem2 md2 ->
Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mf_rw v lyc pos a) ->
mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v W2 mem2 mc0 cur0 line p rest.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc S2 W2 mem2 md2 RW mc0 cur0 line p rest CX0 CORE HJ2 HP2 K RWok LOOP.
destruct (mf_loop_blk_k knock v lyc Sc Wc memc mdc pos lowsh mcc mc0 cur0 line p rest CX0 CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & Htp).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
pose proof HJ2 as (HAR2 & _).
assert (Hbt' : In (bt, mt) (ablocks B lyc S2)) by (apply (Permutation_in _ (Permutation_sym HP2)); exact Hbt).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & T4096 & Tceil & _).
pose proof CX0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
destruct HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Ht0 & _) & _ & Hdisj & _).
pose proof (mf_span_end (mv_t v) (mv_s v) Ht0) as Hspan.
assert (Hs1 : Z.of_nat (length (mv_s v)) + 1 <= seg_spec.cstr_span (mv_t v) (mv_s v)).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (mv_t v + Z.of_nat (length (mv_s v)) + 1)) 8 ltac:(lia)). lia. }
mf_ceil.
pose proof LOOP as (L1 & L2 & L3 & L4 & L5 & L6).
assert (Hend : p + Z.of_nat (length rest) = mv_t v + Z.of_nat (length (mv_s v))).
{ rewrite L3, Nat2Z.inj_sub by exact L1. lia. }
destruct L4 as ((Lzs & Lnz) & Ltl). destruct L5 as (A1 & A2 & A3 & _ & _).
unfold sa_disj in Hdisj.
split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split.
{ split; [split; [|exact Lnz] |].
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite K; [apply Lzs; rewrite length_app; cbn [length]; exact Hi | lia |].
    intros HR. apply (mf_rw_block_k knock v lyc Sc Wc memc mdc pos lowsh mcc bt mt (p + Z.of_nat i) CX0 CORE Hbt ltac:(lia)); [|exact (RWok _ HR)].
    intros Hc. lia.
  - apply (mf_tail_keep_k knock v lyc Sc Wc memc mdc pos lowsh mcc S2 W2 mem2 md2 RW _ CX0 CORE HJ2 K RWok); [lia | | exact Ltl].
    intros x Hx Hc. rewrite Hend in Hx. rewrite Hspan in Hdisj. lia. }
split; [|exact L6].
split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
split; [apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bt mt _ _ HAR2 Hbt'); lia|].
intros _. apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ bt mt _ _ HAR2 Hbt'); lia.
Qed.
Lemma mf_loop_keep : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc S2 (W2 : world SEGS) mem2 md2
  (RW : Z -> Prop) mc0 cur0 line p rest,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
JE v pos lyc S2 W2 mem2 md2 ->
Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mf_rw v lyc pos a) ->
mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v W2 mem2 mc0 cur0 line p rest.
Proof. exact (mf_loop_keep_k false). Qed.

(* THE mf_keep_run FAMILY: a run of the symbolic executor (same layout, state and world) whose reader is unchanged
   outside RW (kept_of_frame with Zs := RW), RW inside mf_rw (mf_seed's windows: the slots [s1 + 24, s1 + 160), the
   frame header and low.i, the frame's shadow; the mconf block for the K pieces' stores). The new values of the cells
   a run may change are premises: low.i's shadow bytes, 112(s1) (from the run's final state, or mf_slot_keep), the
   mconf block (mf_mconf_keep when RW misses it); mf_cells and mf_np at the new memory come from the run's final
   state, or from mf_keep_cells / mf_slot_keep / mf_val_keep when RW touches only 96 / 136 / 144 of the slots. *)
Lemma mf_keep_run : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc mem2 md2 (RW : Z -> Prop) lowsh' mcc',
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
JE v pos lyc Sc Wc mem2 md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mf_rw v lyc pos a) ->
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H Wc) mem2) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh') ->
val_mem SEGS (mrestrict (w_H Wc) mem2) (mf_s1 (mv_sp v) + 112) 8 (frame_addr lyc 1 pos) ->
sa_mconf (rdW Wc mem2) (mv_c v) mcc' ->
mf_core B v lyc Sc Wc mem2 md2 pos lowsh' mcc' /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v Wc mem2 mc0 cur0 line p rest).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc mem2 md2 RW lowsh' mcc' CX0 CORE HJ2 K RWok VSH' V112' MC'.
split; [exact (mf_keep v lyc Sc Wc memc mdc pos lowsh mcc Sc Wc mem2 md2 RW lowsh' mcc' CX0 CORE HJ2
  (Permutation_refl _) K RWok VSH' V112' MC')|].
intros mc0 cur0 line p rest LOOP.
exact (mf_loop_keep v lyc Sc Wc memc mdc pos lowsh mcc Sc Wc mem2 md2 RW mc0 cur0 line p rest CX0 CORE HJ2
  (Permutation_refl _) K RWok LOOP).
Qed.

(* the same for a run that touches only 96(s1), 136(s1) and 144(s1) of the slots (mf_rws): 112(s1) and mf_cells are
   kept, 136(s1) holding cur' *)
Lemma mf_keep_run_s : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc cur mem2 md2 (RW : Z -> Prop)
  lowsh' cur' mcc',
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
JE v pos lyc Sc Wc mem2 md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc mem2 a = rdW Wc memc a) ->
(forall a, RW a -> mf_rw v lyc pos a) -> mf_rws v RW ->
(forall i, 4 <= i < 12 ->
 val_mem SEGS (mrestrict (w_H Wc) mem2) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 lowsh') ->
val_mem SEGS (mrestrict (w_H Wc) mem2) (mf_s1 (mv_sp v) + 136) 8 (mf_cur_ptr (mv_c v) cur') ->
sa_mconf (rdW Wc mem2) (mv_c v) mcc' ->
mf_core B v lyc Sc Wc mem2 md2 pos lowsh' mcc' /\ mf_cells v lyc pos mem2 Wc cur' /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v Wc mem2 mc0 cur0 line p rest).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur mem2 md2 RW lowsh' cur' mcc' CX0 CORE CELLS HJ2 K RWok RWS VSH' V136 MC'.
pose proof CORE as (_ & _ & _ & _ & _ & V112 & _).
pose proof (mf_slot_keep v Wc Wc memc mem2 RW 112 _ CX0 K RWS ltac:(lia) ltac:(lia) V112) as V112'.
destruct (mf_keep_run v lyc Sc Wc memc mdc pos lowsh mcc mem2 md2 RW lowsh' mcc' CX0 CORE HJ2 K RWok VSH' V112' MC')
  as (C1 & C2).
split; [exact C1|]. split; [|exact C2].
exact (mf_keep_cells v lyc pos Wc Wc memc mem2 RW cur cur' CX0 K RWS CELLS V136).
Qed.

(* a run that writes nothing the cut predicates read: every cut fact at the new memory *)
Lemma mf_keep_run0 : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc cur mem2 md2,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
JE v pos lyc Sc Wc mem2 md2 ->
(forall a, 0 <= a < 2 ^ 64 -> rdW Wc mem2 a = rdW Wc memc a) ->
mf_core B v lyc Sc Wc mem2 md2 pos lowsh mcc /\ mf_cells v lyc pos mem2 Wc cur /\
(forall np, mf_np v memc Wc np -> mf_np v mem2 Wc np) /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v Wc mem2 mc0 cur0 line p rest).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur mem2 md2 CX0 CORE CELLS HJ2 K0.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (fun _ : Z => False) a -> rdW Wc mem2 a = rdW Wc memc a)
  by (intros a Ha _; exact (K0 a Ha)).
assert (RWok : forall a, (fun _ : Z => False) a -> mf_rw v lyc pos a) by (intros a []).
assert (RWS : mf_rws v (fun _ : Z => False)) by (intros a []).
pose proof CORE as (_ & _ & _ & VSH & _ & _ & Hmc & _).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
pose proof (mf_corek_of_core _ _ _ _ _ _ _ _ _ CORE) as COREk.
mf_geo v lyc Sc pos CX0 COREk.
destruct (mf_keep_run_s v lyc Sc Wc memc mdc pos lowsh mcc cur mem2 md2 (fun _ => False) lowsh cur mcc CX0 CORE CELLS
  HJ2 K RWok RWS) as (C1 & C2 & C3).
- intros i Hi. apply (mf_val_keep Wc Wc memc mem2 (fun _ => False) _ 1 _ K); [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | intros k _ [] | exact (VSH i Hi)].
- apply (mf_val_keep Wc Wc memc mem2 (fun _ => False) _ 8 _ K); [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | intros k _ [] | exact V136].
- apply (mf_mconf_keep Wc Wc memc mem2 (fun _ => False) _ _ K); [lia | unfold seg_spec.SEG_M_SIZE in *; lia | intros a _ [] | exact Hmc].
- split; [exact C1|]. split; [exact C2|]. split; [|exact C3].
  intros np V. unfold mf_np in V |- *.
  apply (mf_val_keep Wc Wc memc mem2 (fun _ => False) _ 8 _ K); [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | intros k _ [] | exact V].
Qed.

(* the window shape: a step whose reader is unchanged outside a window [wlo, whi) below the slots and outside a set
   E of the mconf block's bytes (a runtime entry's scratch window and cells, a callee's window and footprint): every
   cut fact at the new state, with the mconf block holding mcc' *)
Lemma mf_keep_win_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc cur S2 (W2 : world SEGS) mem2 md2
  wlo whi (E : Z -> Prop) mcc',
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
JE v pos lyc S2 W2 mem2 md2 -> Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
mv_sp v - SegInstA.STK_m_file <= wlo -> whi <= mf_s1 (mv_sp v) + 24 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> ~ E a -> rdW W2 mem2 a = rdW Wc memc a) ->
(forall a, E a -> mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) ->
sa_mconf (rdW W2 mem2) (mv_c v) mcc' ->
mf_core B v lyc S2 W2 mem2 md2 pos lowsh mcc' /\ mf_cells v lyc pos mem2 W2 cur /\
(forall np, mf_np v memc Wc np -> mf_np v mem2 W2 np) /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v W2 mem2 mc0 cur0 line p rest).
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc cur S2 W2 mem2 md2 wlo whi E mcc' CX0 CORE CELLS HJ2 HP2 Hlo Hhi KW HE MC'.
set (RW := fun a => (wlo <= a < whi) \/ E a).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW W2 mem2 a = rdW Wc memc a).
{ intros a Ha HR. apply KW; [exact Ha | intros H; apply HR; left; exact H | intros H; apply HR; right; exact H]. }
assert (RWok : forall a, RW a -> mf_rw v lyc pos a).
{ intros a [Hw | He]; unfold mf_rw; [left; lia | right; left; exact (HE a He)]. }
pose proof CORE as (_ & _ & _ & VSH & _ & V112 & _).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
mf_geo v lyc Sc pos CX0 CORE.
assert (NE : forall a, a < alloc_ceiling -> ~ (mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) -> ~ RW a).
{ intros a H1 H2 [Hw | He]; [lia | exact (H2 (HE a He))]. }
assert (NB : forall a, mf_s1 (mv_sp v) + 24 <= a -> ~ RW a).
{ intros a H1 [Hw | He]; [lia | pose proof (HE a He); unfold seg_spec.SEG_M_SIZE in *; unfold mf_s1 in *; lia]. }
assert (RWS : mf_rws v RW) by (intros a HR Ha; exfalso; exact (NB a ltac:(lia) HR)).
split.
{ apply (mf_keep_k knock v lyc Sc Wc memc mdc pos lowsh mcc S2 W2 mem2 md2 RW lowsh mcc' CX0 CORE HJ2 HP2 K RWok); [| |exact MC'].
  - intros i Hi. apply (mf_val_keep Wc W2 memc mem2 RW _ 1 _ K); [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH i Hi)].
    intros k Hk. change (Z.of_nat 1) with 1 in Hk. apply NE.
    + unfold SHADOW_OFF. lia.
    + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, seg_spec.SEG_M_SIZE in *. lia.
  - exact (mf_slot_keep v Wc W2 memc mem2 RW 112 _ CX0 K RWS ltac:(lia) ltac:(lia) V112). }
split.
{ apply (mf_keep_cells v lyc pos Wc W2 memc mem2 RW cur cur CX0 K RWS CELLS).
  apply (mf_val_keep Wc W2 memc mem2 RW _ 8 _ K); [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V136].
  intros k Hk. apply NB. lia. }
split.
{ intros np V. unfold mf_np in V |- *.
  apply (mf_val_keep Wc W2 memc mem2 RW _ 8 _ K); [unfold mf_s1; lia | change (Z.of_nat 8) with 8; unfold mf_s1; lia | | exact V].
  intros k Hk. apply NB. lia. }
intros mc0 cur0 line p rest LOOP.
exact (mf_loop_keep_k knock v lyc Sc Wc memc mdc pos lowsh mcc S2 W2 mem2 md2 RW mc0 cur0 line p rest CX0 CORE HJ2 HP2 K RWok LOOP).
Qed.
Lemma mf_keep_win : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc cur S2 (W2 : world SEGS) mem2 md2
  wlo whi (E : Z -> Prop) mcc',
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
JE v pos lyc S2 W2 mem2 md2 -> Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
mv_sp v - SegInstA.STK_m_file <= wlo -> whi <= mf_s1 (mv_sp v) + 24 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> ~ E a -> rdW W2 mem2 a = rdW Wc memc a) ->
(forall a, E a -> mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) ->
sa_mconf (rdW W2 mem2) (mv_c v) mcc' ->
mf_core B v lyc S2 W2 mem2 md2 pos lowsh mcc' /\ mf_cells v lyc pos mem2 W2 cur /\
(forall np, mf_np v memc Wc np -> mf_np v mem2 W2 np) /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v W2 mem2 mc0 cur0 line p rest).
Proof. exact (mf_keep_win_k false). Qed.

(* the same with E empty: the mconf block keeps mcc *)
Lemma mf_keep_win0 : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc cur S2 (W2 : world SEGS) mem2 md2
  wlo whi,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
JE v pos lyc S2 W2 mem2 md2 -> Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
mv_sp v - SegInstA.STK_m_file <= wlo -> whi <= mf_s1 (mv_sp v) + 24 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> rdW W2 mem2 a = rdW Wc memc a) ->
mf_core B v lyc S2 W2 mem2 md2 pos lowsh mcc /\ mf_cells v lyc pos mem2 W2 cur /\
(forall np, mf_np v memc Wc np -> mf_np v mem2 W2 np) /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v W2 mem2 mc0 cur0 line p rest).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur S2 W2 mem2 md2 wlo whi CX0 CORE CELLS HJ2 HP2 Hlo Hhi KW.
pose proof CORE as (_ & _ & _ & _ & _ & _ & Hmc & _).
pose proof (mf_corek_of_core _ _ _ _ _ _ _ _ _ CORE) as COREk.
mf_geo v lyc Sc pos CX0 COREk.
apply (mf_keep_win v lyc Sc Wc memc mdc pos lowsh mcc cur S2 W2 mem2 md2 wlo whi (fun _ => False) mcc CX0 CORE CELLS
  HJ2 HP2 Hlo Hhi); [intros a Ha Hw _; exact (KW a Ha Hw) | intros a [] |].
apply (mf_mconf_keep Wc W2 memc mem2 (fun a => wlo <= a < whi) _ _); [| lia | unfold seg_spec.SEG_M_SIZE in *; lia | | exact Hmc].
- intros a Ha Hw. exact (KW a Ha Hw).
- intros a Ha Hw. rewrite HSTK in Hlo. unfold seg_spec.SEG_M_SIZE in *. lia.
Qed.

(* ============================== registers and the allocator state ============================== *)
(* the registers mf_regs_at names are callee-saved *)
Lemma mf_regs_keep : forall v lyc pos (regs1 regs2 : bvmap 5 word),
mf_regs_at B v lyc pos regs1 -> aregs_preserved regs1 regs2 -> mf_regs_at B v lyc pos regs2.
Proof.
intros v lyc pos regs1 regs2 RA HP.
assert (G : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact HP.
apply (mf_regs_at_of v lyc pos regs1 regs2 RA);
  first [ exact (G 2 ltac:(unfold acallee_saved; lia)) | exact (G 3 ltac:(unfold acallee_saved; lia))
  | exact (G 4 ltac:(unfold acallee_saved; lia)) | exact (G 8 ltac:(unfold acallee_saved; lia))
  | exact (G 9 ltac:(unfold acallee_saved; lia)) | exact (G 18 ltac:(unfold acallee_saved; lia))
  | exact (G 19 ltac:(unfold acallee_saved; lia)) | exact (G 25 ltac:(unfold acallee_saved; lia))
  | exact (G 26 ltac:(unfold acallee_saved; lia)) ].
Qed.

(* a callee that reaches no allocator entry leaves the layout and the state up to st_fs *)
Lemma mf_ls_keep : forall v lyc Sc ly2 S2, mf_ls v lyc Sc -> sa_noalloc B lyc Sc ly2 S2 -> mf_ls v ly2 S2.
Proof.
intros v lyc Sc ly2 S2 (Ely & f0 & ES) (_ & -> & f & ES2). split; [exact Ely|].
exists f. rewrite ES2, ES. reflexivity.
Qed.

(* ============================== the call steps ============================== *)
(* after a runtime entry stepped by aj_art_at / aj_art_own_atF / aj_intrin_atS at sp = s1 (same layout, state and
   world; the entry writes its window [wlo, whi) below s1 and its cells E, inside the mconf block): every cut fact
   at the return, with the mconf block holding mcc' *)
Lemma mf_keep_art : forall v lyc Sc (Wc : world SEGS) regsc memc mdc pos lowsh mcc cur regs2 mem2 md2 wlo whi
  (E : Z -> Prop) mcc',
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regsc ->
JE v pos lyc Sc Wc mem2 md2 -> aregs_preserved regsc regs2 ->
mv_sp v - SegInstA.STK_m_file <= wlo -> whi <= mf_s1 (mv_sp v) + 24 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> ~ E a -> rdW Wc mem2 a = rdW Wc memc a) ->
(forall a, E a -> mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) ->
sa_mconf (rdW Wc mem2) (mv_c v) mcc' ->
mf_core B v lyc Sc Wc mem2 md2 pos lowsh mcc' /\ mf_cells v lyc pos mem2 Wc cur /\ mf_regs_at B v lyc pos regs2 /\
(forall np, mf_np v memc Wc np -> mf_np v mem2 Wc np) /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v Wc mem2 mc0 cur0 line p rest).
Proof.
intros v lyc Sc Wc regsc memc mdc pos lowsh mcc cur regs2 mem2 md2 wlo whi E mcc' CX0 CORE CELLS RA HJ2 HPR Hlo Hhi KW HE MC'.
destruct (mf_keep_win v lyc Sc Wc memc mdc pos lowsh mcc cur Sc Wc mem2 md2 wlo whi E mcc' CX0 CORE CELLS HJ2
  (Permutation_refl _) Hlo Hhi KW HE MC') as (C1 & C2 & C3 & C4).
split; [exact C1|]. split; [exact C2|]. split; [exact (mf_regs_keep v lyc pos regsc regs2 RA HPR)|].
split; [exact C3 | exact C4].
Qed.

(* the same with E empty: the mconf block keeps mcc *)
Lemma mf_keep_art0 : forall v lyc Sc (Wc : world SEGS) regsc memc mdc pos lowsh mcc cur regs2 mem2 md2 wlo whi,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regsc ->
JE v pos lyc Sc Wc mem2 md2 -> aregs_preserved regsc regs2 ->
mv_sp v - SegInstA.STK_m_file <= wlo -> whi <= mf_s1 (mv_sp v) + 24 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> rdW Wc mem2 a = rdW Wc memc a) ->
mf_core B v lyc Sc Wc mem2 md2 pos lowsh mcc /\ mf_cells v lyc pos mem2 Wc cur /\ mf_regs_at B v lyc pos regs2 /\
(forall np, mf_np v memc Wc np -> mf_np v mem2 Wc np) /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v Wc mem2 mc0 cur0 line p rest).
Proof.
intros v lyc Sc Wc regsc memc mdc pos lowsh mcc cur regs2 mem2 md2 wlo whi CX0 CORE CELLS RA HJ2 HPR Hlo Hhi KW.
destruct (mf_keep_win0 v lyc Sc Wc memc mdc pos lowsh mcc cur Sc Wc mem2 md2 wlo whi CX0 CORE CELLS HJ2
  (Permutation_refl _) Hlo Hhi KW) as (C1 & C2 & C3 & C4).
split; [exact C1|]. split; [exact C2|]. split; [exact (mf_regs_keep v lyc pos regsc regs2 RA HPR)|].
split; [exact C3 | exact C4].
Qed.

(* sp = s1 at a cut *)
Lemma mf_sp_at : forall v lyc pos regsc, CX v -> mf_regs_at B v lyc pos regsc -> spZ regsc = mf_s1 (mv_sp v).
Proof.
intros v lyc pos regsc CX0 (R2 & _). destruct (mf_s1_facts v CX0) as (H1 & _ & H3). destruct (mf_sp0 v CX0) as (_ & S2 & _).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
mf_ceil. unfold spZ. rewrite R2. apply mf_w64_u. lia.
Qed.

(* after a program call stepped by cl_callS at sp = s1 (the caller's journal at k = 0 + EV_callee = 0, the
   callee's post: its sa_kept over its window STK1 below s1 and its write set E inside the mconf block, sa_noalloc,
   aregs_preserved, the block holding mcc'): every cut fact at the return *)
Lemma mf_keep_call : forall v lyc Sc (Wc : world SEGS) regsc memc mdc pos lowsh mcc cur ly2 S2 (W2 : world SEGS)
  regs2 mem2 md2 k STK1 (E : Z -> Prop) mcc',
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regsc ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] ly2 S2 W2 mem2 md2 k -> k = 0 ->
aregs_preserved regsc regs2 -> sa_noalloc B lyc Sc ly2 S2 ->
0 <= STK1 <= SegInstA.STK_fuzz_catalogue_row ->
sa_kept SEGS Wc memc W2 mem2 regsc STK1 E ->
(forall a, E a -> mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE) ->
sa_mconf (rdW W2 mem2) (mv_c v) mcc' ->
ly2 = lyc /\ (mf_ls v lyc Sc -> mf_ls v lyc S2) /\
mf_core B v lyc S2 W2 mem2 md2 pos lowsh mcc' /\ mf_cells v lyc pos mem2 W2 cur /\ mf_regs_at B v lyc pos regs2 /\
(forall np, mf_np v memc Wc np -> mf_np v mem2 W2 np) /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v W2 mem2 mc0 cur0 line p rest).
Proof.
intros v lyc Sc Wc regsc memc mdc pos lowsh mcc cur ly2 S2 W2 regs2 mem2 md2 k STK1 E mcc' CX0 CORE CELLS RA HJ2 Hk
  HPR NOAL HSTK1 KEPT HE MC'.
subst k. pose proof NOAL as (HP2 & -> & _).
pose proof (mf_sp_at v lyc pos regsc CX0 RA) as Hsp.
destruct (mf_s1_facts v CX0) as (H1 & _ & H3).
assert (HS : SegInstA.STK_fuzz_catalogue_row = 8256) by reflexivity.
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
destruct (mf_keep_win v lyc Sc Wc memc mdc pos lowsh mcc cur S2 W2 mem2 md2 (mf_s1 (mv_sp v) - STK1) (mf_s1 (mv_sp v)) E mcc'
  CX0 CORE CELLS HJ2 HP2) as (C1 & C2 & C3 & C4).
- rewrite HSTK. lia.
- lia.
- intros a Ha Hw He. apply KEPT; [exact Ha | rewrite Hsp; exact Hw | exact He].
- exact HE.
- exact MC'.
- split; [reflexivity|]. split; [intros LS; exact (mf_ls_keep v lyc Sc lyc S2 LS NOAL)|].
  split; [exact C1|]. split; [exact C2|]. split; [exact (mf_regs_keep v lyc pos regsc regs2 RA HPR)|].
  split; [exact C3 | exact C4].
Qed.

(* the same for a callee that writes nothing outside its window (sa_kept with E empty): the mconf block keeps mcc *)
Lemma mf_keep_call0 : forall v lyc Sc (Wc : world SEGS) regsc memc mdc pos lowsh mcc cur ly2 S2 (W2 : world SEGS)
  regs2 mem2 md2 k STK1,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
mf_regs_at B v lyc pos regsc ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] ly2 S2 W2 mem2 md2 k -> k = 0 ->
aregs_preserved regsc regs2 -> sa_noalloc B lyc Sc ly2 S2 ->
0 <= STK1 <= SegInstA.STK_fuzz_catalogue_row ->
sa_kept SEGS Wc memc W2 mem2 regsc STK1 (fun _ => False) ->
ly2 = lyc /\ (mf_ls v lyc Sc -> mf_ls v lyc S2) /\
mf_core B v lyc S2 W2 mem2 md2 pos lowsh mcc /\ mf_cells v lyc pos mem2 W2 cur /\ mf_regs_at B v lyc pos regs2 /\
(forall np, mf_np v memc Wc np -> mf_np v mem2 W2 np) /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v W2 mem2 mc0 cur0 line p rest).
Proof.
intros v lyc Sc Wc regsc memc mdc pos lowsh mcc cur ly2 S2 W2 regs2 mem2 md2 k STK1 CX0 CORE CELLS RA HJ2 Hk
  HPR NOAL HSTK1 KEPT.
pose proof CORE as (_ & _ & _ & _ & _ & _ & Hmc & _).
pose proof (mf_sp_at v lyc pos regsc CX0 RA) as Hsp.
destruct (mf_sp0 v CX0) as (S1 & S2' & S3).
destruct (mf_s1_facts v CX0) as (H1 & _ & H3).
destruct (mf_blk_c v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE) as (b & m & Hb & Hb1 & Hb2).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR Hb) as (_ & B4096 & Bceil & _).
assert (HS : SegInstA.STK_fuzz_catalogue_row = 8256) by reflexivity.
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1, H3.
mf_ceil.
apply (mf_keep_call v lyc Sc Wc regsc memc mdc pos lowsh mcc cur ly2 S2 W2 regs2 mem2 md2 k STK1 (fun _ => False) mcc
  CX0 CORE CELLS RA HJ2 Hk HPR NOAL HSTK1 KEPT); [intros a [] |].
apply (mf_mconf_keep Wc W2 memc mem2 (fun a => spZ regsc - STK1 <= a < spZ regsc) _ _); [| lia | unfold seg_spec.SEG_M_SIZE in *; lia | | exact Hmc].
- intros a Ha Hw. exact (KEPT a Ha Hw (fun x => x)).
- intros a Ha Hw. rewrite Hsp in Hw. unfold seg_spec.SEG_M_SIZE in *. lia.
Qed.

(* ============================== the facts at the current state ============================== *)
(* the event budget at a mid-walk state: the journal adds no event, EV_m_file = 0 *)
Lemma mf_nev_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc -> st_nev Sc + 0 <= EV_MAX.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE.
destruct CX0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV).
pose proof CORE as (HJ & _). pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
unfold EV_m_file in HEV. lia.
Qed.
Lemma mf_nev : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> st_nev Sc + 0 <= EV_MAX.
Proof. exact (mf_nev_k false). Qed.

(* the frame chain from s1 with s0 = sp0: the entry's ra and s0 lie at sp0 - 8 and sp0 - 16 (mf_saved), and every
   byte at or above sp0 is the entry's (the journal; M_FILE_FP lies in the mconf block) *)
Lemma mf_chain_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
exists ch1, achain lyc (rdW Wc memc) (mf_s1 (mv_sp v)) (mv_sp v) ch1.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE.
pose proof CX0 as (HPRE & _).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof CORE as (HJ & _ & _ & _ & VSV & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & Kst & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (mf_c_entry v CX0) as (b & m & _ & Hb1 & Hb2 & _ & Bceil & _).
mf_ceil.
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in *.
unfold mv_sp in *. set (sp0 := spZ (mv_regs v)) in *.
pose proof (Z.mod_pos_bound (sp0 - 288) 32 ltac:(lia)) as M32.
destruct (Z_lt_le_dec sp0 (ly_top (mv_ly v) - 16)) as [Hlt|Hge].
- exists ((sp0, raZ (mv_regs v), s0Z (mv_regs v)) :: mv_ch v).
  apply (achain_ly_top (mv_ly v)); [exact Etop|].
  apply (achain_push (mv_ly v) (rdW (mv_W v) (mv_mem v))); [exact Hch0 | lia | | | | exact Hra40 | lia | | lia | unfold mf_s1; lia].
  + intros a Ha. apply Kst; [lia | lia |]. intros HF. pose proof (mf_fp_in_block v a CX0 HF) as Hc.
    unfold seg_spec.SEG_M_SIZE in *. lia.
  + replace (sp0 - 8) with (sp0 - 8 - 8 * Z.of_nat 0) by lia.
    apply (rdword_of_val_mem SEGS); [exact (VSV 0%nat 1 eq_refl)|].
    pose proof (bv_unsigned_in_range 64 (getr (mv_regs v) 1)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
  + replace (sp0 - 16) with (sp0 - 8 - 8 * Z.of_nat 1) by lia.
    apply (rdword_of_val_mem SEGS); [exact (VSV 1%nat 8 eq_refl)|].
    pose proof (bv_unsigned_in_range 64 (getr (mv_regs v) 8)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
  + pose proof (Z.div_mod sp0 16 ltac:(lia)). pose proof (Z.div_mod sp0 8 ltac:(lia)). pose proof (Z.mod_pos_bound sp0 8 ltac:(lia)). lia.
- exists []. unfold achain. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.
Lemma mf_chain : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
exists ch1, achain lyc (rdW Wc memc) (mf_s1 (mv_sp v)) (mv_sp v) ch1.
Proof. exact (mf_chain_k false). Qed.

(* the chain in the form cl_callS asks at a call from a cut state: sp = s1, s0 = sp0 *)
Lemma mf_chain_at : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc regsc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_regs_at B v lyc pos regsc ->
exists ch1, achain lyc (rdW Wc memc) (spZ regsc) (s0Z regsc) ch1.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc regsc CX0 CORE RA.
rewrite (mf_sp_at v lyc pos regsc CX0 RA).
assert (E8 : s0Z regsc = mv_sp v).
{ pose proof RA as (_ & _ & _ & R8 & _). destruct (mf_sp0 v CX0) as (S1 & S2 & _). mf_ceil.
  assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
  unfold s0Z. rewrite R8. apply mf_w64_u. lia. }
rewrite E8. exact (mf_chain v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE).
Qed.

(* the line loop's facts at the next line, for a model mcc' that moved by one line (counters by at most one, kept
   refusals not fewer) and a cur' it names *)
Lemma mf_loop_next : forall v (Wc : world SEGS) memc mcc cur line p rest mcc' cur',
mf_loop v Wc memc mcc cur line p rest -> rest <> [] ->
mc_refused mcc' <= mc_refused mcc + 1 -> mc_overflow mcc' <= mc_overflow mcc + 1 ->
(length (mc_kept mcc) <= length (mc_kept mcc'))%nat -> mf_cur_ok mcc' cur' ->
mf_loop v Wc memc mcc' cur' (line + 1) (mf_next p rest) (mf_rest rest).
Proof.
intros v Wc memc mcc cur line p rest mcc' cur' LOOP Hne Hr Ho Hk Hcur.
destruct LOOP as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11).
destruct (mf_break_snd rest) as (B1 & B2 & B3). specialize (B2 Hne).
unfold mf_next, mf_rest.
assert (Hq : skipn (length rest - length (snd (break_nl rest))) rest = snd (break_nl rest)) by (symmetry; exact B3).
unfold mf_loop.
split; [lia|].
split.
{ transitivity (skipn (length rest - length (snd (break_nl rest))) (skipn (length (mv_s v) - length rest) (mv_s v))).
  - rewrite <- L2. exact B3.
  - rewrite skipn_skipn. f_equal. lia. }
split.
{ rewrite L3.
  pose proof (Nat2Z.inj_sub (length (mv_s v)) (length rest) L1) as E1.
  pose proof (Nat2Z.inj_sub (length rest) (length (snd (break_nl rest))) B1) as E2.
  pose proof (Nat2Z.inj_sub (length (mv_s v)) (length (snd (break_nl rest))) ltac:(lia)) as E3.
  rewrite E1, E2, E3. ring. }
split.
{ pose proof (mf_str_skipn _ _ _ (length rest - length (snd (break_nl rest))) L4 ltac:(lia)) as H4.
  rewrite Hq in H4. exact H4. }
split.
{ pose proof (Nat2Z.inj_sub (length rest) (length (snd (break_nl rest))) B1) as E2. rewrite E2.
  apply (mf_addr_sub _ p (Z.of_nat (length rest) + 1)); [exact L5 | lia | lia | lia]. }
split; [exact Hcur|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* the next line's address is a 64-bit word (inside the text's block) *)
Lemma mf_next_range : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc mc0 cur0 line p rest,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mc0 cur0 line p rest ->
0 <= mf_next p rest < 2 ^ 64.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc mc0 cur0 line p rest CX0 CORE LOOP.
destruct (mf_loop_blk v lyc Sc Wc memc mdc pos lowsh mcc mc0 cur0 line p rest CX0 CORE LOOP)
  as (b & m & Hb & Hb1 & Hb2 & Htp).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ b m HAR Hb) as (_ & B4096 & Bceil & _).
destruct (mf_break_snd rest) as (B1 & _ & _).
unfold mf_next, mf_rest. mf_ceil. rewrite Nat2Z.inj_sub by exact B1. lia.
Qed.

(* an image byte the runtime does not own, not errno, is the entry's: M_FILE_FP lies in the mconf block, whose bytes
   are not image bytes, and does not hold the sink token at 0 *)
Lemma mf_img_now_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc a,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW Wc memc a = rdW (mv_W v) (mv_mem v) a.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc a CX0 CORE Hi Ho He.
pose proof CORE as (HJ & _). pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (mf_c_entry v CX0) as (b & m & _ & Hb1 & Hb2 & B4096 & _ & Hni).
apply F3; [exact Hi | exact Ho | exact He |].
split.
- intros Hopen. exfalso. pose proof (mf_fp_in_block v 0 CX0 Hopen) as Hc. lia.
- intros HF. pose proof (mf_fp_in_block v a CX0 HF) as Hc. exact (Hni a ltac:(lia) Hi).
Qed.
Lemma mf_img_now : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc a,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW Wc memc a = rdW (mv_W v) (mv_mem v) a.
Proof. exact (mf_img_now_k false). Qed.

(* a literal of the entry is a literal of the current state (sa_pinned, sa_romtail, sa_img are state-free) *)
Lemma mf_sa_lit_now_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc a s,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
sa_lit SEGS B (rdW (mv_W v) (mv_mem v)) a s -> sa_lit SEGS B (rdW Wc memc) a s.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc a s CX0 CORE (H0 & ((Hzs & Hnz) & _) & Hpin & Hrom & Himg).
split; [exact H0|]. split; [|split; [exact Hpin | split; [exact Hrom | exact Himg]]].
split; [split; [|exact Hnz] | apply sa_tail_of_romtail; exact Hrom].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
destruct (Himg (a + Z.of_nat i) ltac:(lia)) as (I1 & I2 & I3).
rewrite (mf_img_now_k knock v lyc Sc Wc memc mdc pos lowsh mcc _ CX0 CORE I1 I2 I3).
apply Hzs. rewrite length_app. cbn [length]. lia.
Qed.
Lemma mf_sa_lit_now : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc a s,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
sa_lit SEGS B (rdW (mv_W v) (mv_mem v)) a s -> sa_lit SEGS B (rdW Wc memc) a s.
Proof. exact (mf_sa_lit_now_k false). Qed.

(* m_file's literals at the current state *)
Lemma mf_lit_now_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc x,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc -> In x M_FILE_LITS ->
sa_lit SEGS B (rdW Wc memc) (SegInstA.seg_litA_fz x) x.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc x CX0 CORE Hx.
pose proof CX0 as (_ & _ & _ & HLIT & _).
exact (mf_sa_lit_now_k knock v lyc Sc Wc memc mdc pos lowsh mcc _ _ CX0 CORE (HLIT x Hx)).
Qed.
Lemma mf_lit_now : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc x,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> In x M_FILE_LITS ->
sa_lit SEGS B (rdW Wc memc) (SegInstA.seg_litA_fz x) x.
Proof. exact (mf_lit_now_k false). Qed.

(* m_key.words at the current state *)
Lemma mf_words_now : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
mf_words SEGS B (rdW Wc memc) SegInstA.wordsA.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE.
pose proof CX0 as (_ & _ & _ & _ & (Hpin & Himg & Hw) & _).
split; [exact Hpin|]. split; [exact Himg|].
intros i Hi. destruct (Hw i Hi) as (wp & Hwp & Hl). exists wp. split.
- rewrite <- Hwp. apply rdword_ext. intros k Hk.
  destruct (Himg (SegInstA.wordsA + 8 * Z.of_nat i + k) ltac:(lia)) as (I1 & I2 & I3).
  exact (mf_img_now v lyc Sc Wc memc mdc pos lowsh mcc _ CX0 CORE I1 I2 I3).
- exact (mf_sa_lit_now v lyc Sc Wc memc mdc pos lowsh mcc _ _ CX0 CORE Hl).
Qed.

(* m_key.role at the current state *)
Lemma mf_roles_now : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
mf_roles SEGS B (rdW Wc memc) SegInstA.rolesA.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE.
pose proof CX0 as (_ & _ & _ & _ & _ & (Hpin & Himg & Hr) & _).
split; [exact Hpin|]. split; [exact Himg|].
intros i Hi k Hk. rewrite <- (Hr i Hi k Hk).
destruct (Himg (SegInstA.rolesA + 4 * Z.of_nat i + Z.of_nat k) ltac:(lia)) as (I1 & I2 & I3).
exact (mf_img_now v lyc Sc Wc memc mdc pos lowsh mcc _ CX0 CORE I1 I2 I3).
Qed.

(* the box-model table at the current state *)
Lemma mf_cat_now : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
sa_cat SEGS B (rdW Wc memc) SegInstA.catA.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE.
pose proof CX0 as (_ & _ & _ & _ & _ & _ & (Hpin & Himg & Hc) & _).
split; [exact Hpin|]. split; [exact Himg|].
intros i Hi. destruct (Hc i Hi) as (tp & Htp & Hl). exists tp. split.
- rewrite <- Htp. apply rdword_ext. intros k Hk.
  unfold pin_spec.CAT_N in Hi.
  destruct (Himg (pin_spec.row_addr SegInstA.catA i + k)) as (I1 & I2 & I3).
  { unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia. }
  exact (mf_img_now v lyc Sc Wc memc mdc pos lowsh mcc _ CX0 CORE I1 I2 I3).
- exact (mf_sa_lit_now v lyc Sc Wc memc mdc pos lowsh mcc _ _ CX0 CORE Hl).
Qed.

(* the runtime entries' ROM view at the current state (the ROM half of the entry's arodata_okP) *)
Lemma mf_rom_now : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> RtDefs.rt_rom_view SEGS B Wc memc.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE a Hrom Ho He.
pose proof CX0 as (_ & _ & HRO & _).
assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
rewrite (mf_img_now v lyc Sc Wc memc mdc pos lowsh mcc a CX0 CORE Hi Ho He).
apply HRO; [left; exact Hrom | exact Ho | exact He].
Qed.

(* arodata_okP at the current state *)
Lemma mf_rod_now_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc ->
arodata_okP SEGS SegInstA.RLO_A SegInstA.RHI_A B (rdW Wc memc).
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc CX0 CORE a Hro Ho He.
pose proof CX0 as (_ & _ & HRO & _).
assert (Hi : in_img SEGS a).
{ destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (RELRO a Hr)]. }
rewrite (mf_img_now_k knock v lyc Sc Wc memc mdc pos lowsh mcc a CX0 CORE Hi Ho He).
exact (HRO a Hro Ho He).
Qed.
Lemma mf_rod_now : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
CX v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
arodata_okP SEGS SegInstA.RLO_A SegInstA.RHI_A B (rdW Wc memc).
Proof. exact (mf_rod_now_k false). Qed.

(* the stack-protector cells at the current state *)
Lemma mf_ssp_now_k : forall knock v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
mf_corek knock v lyc Sc Wc memc mdc pos lowsh mcc -> sa_ssp (rdW Wc memc) SegInstA.gotwA SegInstA.guardA.
Proof.
intros knock v lyc Sc Wc memc mdc pos lowsh mcc CORE.
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _). exact (SSP _ _ _ _ _ HAR).
Qed.
Lemma mf_ssp_now : forall v lyc Sc (Wc : world SEGS) memc mdc pos lowsh mcc,
mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> sa_ssp (rdW Wc memc) SegInstA.gotwA SegInstA.guardA.
Proof. exact (mf_ssp_now_k false). Qed.

(* ======================= the same facts from the journal alone (the *_j forms) ======================= *)
(* At the snprintf calls of KROLE (0x86934) and KIGNP (0x86a34) g->role / g->ignore are already stored, so no mconf
   the cut predicates name is in the block; the image facts need only mf_core's journal. *)
Lemma mf_img_now_j : forall v lyc Sc (Wc : world SEGS) memc mdc pos a,
CX v -> JE v pos lyc Sc Wc memc mdc ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rdW Wc memc a = rdW (mv_W v) (mv_mem v) a.
Proof.
intros v lyc Sc Wc memc mdc pos a CX0 HJ Hi Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
destruct (mf_c_entry v CX0) as (b & m & _ & Hb1 & Hb2 & B4096 & _ & Hni).
apply F3; [exact Hi | exact Ho | exact He |].
split.
- intros Hopen. exfalso. pose proof (mf_fp_in_block v 0 CX0 Hopen) as Hc. lia.
- intros HF. pose proof (mf_fp_in_block v a CX0 HF) as Hc. exact (Hni a ltac:(lia) Hi).
Qed.
Lemma mf_sa_lit_now_j : forall v lyc Sc (Wc : world SEGS) memc mdc pos a s,
CX v -> JE v pos lyc Sc Wc memc mdc ->
sa_lit SEGS B (rdW (mv_W v) (mv_mem v)) a s -> sa_lit SEGS B (rdW Wc memc) a s.
Proof.
intros v lyc Sc Wc memc mdc pos a s CX0 HJ (H0 & ((Hzs & Hnz) & _) & Hpin & Hrom & Himg).
split; [exact H0|]. split; [|split; [exact Hpin | split; [exact Hrom | exact Himg]]].
split; [split; [|exact Hnz] | apply sa_tail_of_romtail; exact Hrom].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
destruct (Himg (a + Z.of_nat i) ltac:(lia)) as (I1 & I2 & I3).
rewrite (mf_img_now_j v lyc Sc Wc memc mdc pos _ CX0 HJ I1 I2 I3).
apply Hzs. rewrite length_app. cbn [length]. lia.
Qed.
Lemma mf_lit_now_j : forall v lyc Sc (Wc : world SEGS) memc mdc pos x,
CX v -> JE v pos lyc Sc Wc memc mdc -> In x M_FILE_LITS ->
sa_lit SEGS B (rdW Wc memc) (SegInstA.seg_litA_fz x) x.
Proof.
intros v lyc Sc Wc memc mdc pos x CX0 HJ Hx.
pose proof CX0 as (_ & _ & _ & HLIT & _).
exact (mf_sa_lit_now_j v lyc Sc Wc memc mdc pos _ _ CX0 HJ (HLIT x Hx)).
Qed.
Lemma mf_rod_now_j : forall v lyc Sc (Wc : world SEGS) memc mdc pos,
CX v -> JE v pos lyc Sc Wc memc mdc ->
arodata_okP SEGS SegInstA.RLO_A SegInstA.RHI_A B (rdW Wc memc).
Proof.
intros v lyc Sc Wc memc mdc pos CX0 HJ a Hro Ho He.
pose proof CX0 as (_ & _ & HRO & _).
assert (Hi : in_img SEGS a).
{ destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (RELRO a Hr)]. }
rewrite (mf_img_now_j v lyc Sc Wc memc mdc pos a CX0 HJ Hi Ho He).
exact (HRO a Hro Ho He).
Qed.
Lemma mf_rom_now_j : forall v lyc Sc (Wc : world SEGS) memc mdc pos,
CX v -> JE v pos lyc Sc Wc memc mdc -> RtDefs.rt_rom_view SEGS B Wc memc.
Proof.
intros v lyc Sc Wc memc mdc pos CX0 HJ a Hrom Ho He.
pose proof CX0 as (_ & _ & HRO & _).
assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]).
rewrite (mf_img_now_j v lyc Sc Wc memc mdc pos a CX0 HJ Hi Ho He).
apply HRO; [left; exact Hrom | exact Ho | exact He].
Qed.

End e.
End f.
End d.
