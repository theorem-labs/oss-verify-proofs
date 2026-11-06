(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 311 of its 344 lines of code are new or changed and 485 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of the
   walk of segment S05 of the test harness's entry function LLVMFuzzerTestOneInput (0x85210 .. 0x85334 and
   0x85520 .. 0x8552c). Statement text and pure model facts only: no function of the binary is proved here.

   THE FORM: the image-B twin of image A's kit lib/A/Prog/LLVMFuzzerTestOneInput_s15k.v (image A's S05 commit
   8922f0c88986), with the same names; the inner cut points carry image B's pcs and registers (PLAN-asanubsan-main
   section 11, out/correspond.tsv), and image B's code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s lines
   278-351 and 474-477).

   S05's statement is LLVMFuzzerTestOneInput_defs.v's
     lt_seg_S05_stmt := forall f, LTA_K85338 B MT f -> LTA_K85530 B MT f -> LT_K85210_stmt B MT f.
   The walk of it is cut into five pieces at four inner points; this file states those four points, in the shape
   of the defs file's LT_<cut>_stmt ("from this point of the function to its return, under the entry's context",
   concluding SRr of lt_post at the point's configuration):

     0x85210 K85210 f  --L1-->  0x8526c S5_LB f   (the NULL test, the copy, the trap 0x85230, the NUL (check 7),
                                                   the label's five shadow stores through SH(FR) from 184(s1))
     0x8526c S5_LB f   --L2-->  0x852c8 S5_OTH f  (a turn that is not the last) or
                                0x85324 S5_LST f  (the last turn)
     0x852c8 S5_OTH f  --L4-->  0x852e4 S5_CK f   (m_file and reac_segconf_parse_file)
     0x852e4 S5_CK f   --L5-->  0x85530 K85530 f  (the trap 0x852e8 on s5 = M & 3 = 0, check 8 on m->n, the latch
                                                   of `returned` in 176(s1), the count left, free(text))
     0x85324 S5_LST f  --L3-->  0x85338 K85338 f  (the slot store 144(s1) and m_file(m, text, NULL))

   snprintf (0x8528c) and the two program callees return at an FP state of their own, so S5_OTH, S5_LST and
   S5_CK are taken at every FP state (the LTA form of the defs file). LFO_L is the frame's shadow state after the
   five stores at 0x85254 .. 0x85268 made label[40] usable; it is released at 0x85538, after K85530, so every
   inner cut carries LFO_L.

   Image B's registers at the inner cuts (the code; image A's in brackets): s2 = nfiles [s9], s5 = M & 3 = 0
   [s5 = SH(FR)], s6 = m [m in 168(s1)], s7 = t [s7], s8 = P1 + NP, the cursor past the turn's take [s8 = P1,
   s11 = NP], s9 = f, then f + 1 from 0x852b4 [s2], s10 = lb, then (m + 0x2000) >> 3 from 0x852bc [s10], s3 = the
   label pointer from the label arms on [s4]. returned is 176(s1) [s6]; NP is 152(s1), N1 160(s1).

   The model facts at the end of the file are image A's kit's, word for word (they speak only of SegModel and
   seg_spec), and two more that image B's code needs: the next turn's cursor address and count as P1 + NP and
   N1 - NP (s8 is P1 + NP from K85210 on, and 0x85524 computes s4 = N1 - NP). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================ the inner cut points (offsets from BASE = 0x84dc0) ============================
   each checked: slot LO / 4 of SegList.seg_listing holds the excerpt's word at that pc *)
(* 0x8526c `bltz a0,85294`: the text copied and NUL-terminated, label[40] usable, a0 = lb << 56 (slot 299,
   PW 0x2054463) *)
Definition LO_S5LB : Z := 0x4ac.
(* 0x852c8 `mv a1,s7`: a turn that is not the last, a0 = m, s3 = the label pointer (slot 322, PW 0xb8593) *)
Definition LO_S5OTH : Z := 0x508.
(* 0x852e4 `ld a1,200(s1)`: reac_segconf_parse_file returned (slot 329, PW 0xc84b583) *)
Definition LO_S5CK : Z := 0x524.
(* 0x85324 `sd s8,144(s1)`: the last turn, before m_file(m, text, NULL) (slot 345, PW 0x984b823) *)
Definition LO_S5LST : Z := 0x564.

(* ================================ the turn's text, label and next cursor ================================ *)
Definition s5_txt (pl : list byte) (f : nat) : list Z := seg_spec.seg_txt pl f.
Definition s5_lab (pl : list byte) (f : nat) : option (list Z) := seg_spec.seg_label pl f.
(* the model state m_file leaves at a turn that is not the last, and the reader's answer there *)
Definition s5_mc1 (pl : list byte) (f : nat) : SegModel.mconf :=
  SegModel.m_file (seg_spec.seg_mc (seg_spec.seg_run pl f)) (s5_txt pl f) (s5_lab pl f).
Definition s5_rp (pl : list byte) (f : nat) : SegModel.rconf * Z :=
  SegModel.r_parse_file (seg_spec.seg_rc (seg_spec.seg_run pl f)) (s5_txt pl f) (s5_lab pl f).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the part every inner cut of S05 shares with K85210: the core at turn f with the text block t live, the three
   blocks, and the counters after f turns *)
Definition S5_body (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z) (o : lfo)
  (c m t : Z) (f : nat) : Prop :=
  lt_core B MT cx ly S W regs mem md k acc (5 + 2 * (x_nf cx - Z.of_nat f)) o
    [(t, x_tn cx f); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\
  lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem) t (x_tn cx f) /\
  lt_cnt f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f)).

(* the slots every inner cut states: K85210's (LT_L, 152 NP, 160 N1, 176 returned after f turns) *)
Definition S5_slots (cx : lcx) (c m : Z) (f : nat) : list (Z * Z) :=
  LT_L cx c m ++ [(152, x_np cx f); (160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))].

(* the label the turn built, where it lies and what the two callees need of it (m_file_c.m_file_pre's label
   clauses and reac_segconf_parse_file_c's, at the two blocks m and c). The label is kept apart from the WHOLE
   of each of the two blocks, not only from the reading field each callee's pre names: m_file writes
   M_FILE_FP, which reaches seg[0 .. n'), so a label inside m's unused segment slots would not survive the
   call of m_file at 0x852d0 and reac_segconf_parse_file's label premise could not be given at 0x852e0
   (image A's S05 walk (piece d) found it, 2026-10-30; its S05-d issue note). Block-wide disjointness gives
   each callee's own clause: MC_READING + 96 = SEG_M_SIZE and RC_READING + 96 <= SEG_C_SIZE. *)
Definition S5_label (ly : alayout) (S : astate) (rd : reader) (cx : lcx) (f : nat) (lp c m : Z) : Prop :=
  0 <= lp < 2 ^ 64 /\ sa_ostr rd lp (s5_lab (x_pl cx) f) /\
  match s5_lab (x_pl cx) f with
  | Some l =>
      Z.of_nat (length l) <= 65535 /\
      (sa_heap B ly S lp (Z.of_nat (length l) + 1) \/ sa_fframe ly S lp (Z.of_nat (length l) + 1) \/
       (sa_img SEGS B lp (Z.of_nat (length l) + 1) /\ sa_pinned SEGS B lp (Z.of_nat (length l) + 1) /\
        sa_pinned_tail SEGS B (lp + Z.of_nat (length l)))) /\
      sa_addr rd lp (Z.of_nat (length l) + 1) /\
      sa_disj lp (seg_spec.cstr_span lp l) m seg_spec.SEG_M_SIZE /\
      sa_disj lp (seg_spec.cstr_span lp l) c seg_spec.SEG_C_SIZE
  | None => True
  end.

(* -------------------------- 0x8526c: the copy done, the NUL stored, the label's shadow set --------------------------
   s7 = t and t holds the turn's text as a C string; label[40] usable (LFO_L); a0 = lb << 56, the word the
   `bltz` at 0x8526c tests; s2, s5, s6, s8, s9, s10 as at K85210 *)
Definition S5_LB_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  S5_body cx ly S W regs mem md k acc LFO_L c m t f ->
  lt_cm (rdW W mem) c m (x_st cx f) ->
  sa_str (rdW W mem) t (s5_txt (x_pl cx) f) ->
  getr regs 10 = w64 (Z.shiftl (seg_spec.seg_lb (x_pl cx) f) 56) ->
  getr regs 18 = w64 (x_nf cx) -> getr regs 21 = w64 0 -> getr regs 22 = w64 m -> getr regs 23 = w64 t ->
  getr regs 24 = w64 (x_at cx f + x_np cx f) -> getr regs 25 = w64 (Z.of_nat f) ->
  getr regs 26 = w64 (seg_spec.seg_lb (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (S5_slots cx c m f) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S5LB) regs mem md) (lt_post B MT cx).

(* ----------------------------- 0x852c8: a turn that is not the last, before m_file -----------------------------
   a0 = m, s2 = nfiles, s3 = the label pointer, s5 = 0, s6 = m, s7 = t, s8 = P1 + NP, s9 = f + 1, s10 =
   (m + 0x2000) >> 3 *)
Definition S5_OTH_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t lp : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f + 1 < x_nf cx ->
  S5_body cx ly S W regs mem md k acc LFO_L c m t f ->
  lt_cm (rdW W mem) c m (x_st cx f) ->
  sa_str (rdW W mem) t (s5_txt (x_pl cx) f) ->
  S5_label ly S (rdW W mem) cx f lp c m ->
  getr regs 10 = w64 m ->
  getr regs 18 = w64 (x_nf cx) -> getr regs 19 = w64 lp -> getr regs 21 = w64 0 -> getr regs 22 = w64 m ->
  getr regs 23 = w64 t -> getr regs 24 = w64 (x_at cx f + x_np cx f) -> getr regs 25 = w64 (Z.of_nat f + 1) ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  lt_slots cx (rdW W mem) (S5_slots cx c m f) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S5OTH) regs mem md) (lt_post B MT cx).

(* ------------------------- 0x852e4: reac_segconf_parse_file returned on a non-last turn -------------------------
   a0 = its answer; m holds m_file of the turn, c the reader's state after it; the other registers as at
   S5_OTH *)
Definition S5_CK_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t lp : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f + 1 < x_nf cx ->
  S5_body cx ly S W regs mem md k acc LFO_L c m t f ->
  sa_rconf (rdW W mem) c (fst (s5_rp (x_pl cx) f)) ->
  sa_mconf (rdW W mem) m (s5_mc1 (x_pl cx) f) ->
  lt_cnt (Datatypes.S f) (fst (s5_rp (x_pl cx) f)) (s5_mc1 (x_pl cx) f) ->
  getr regs 10 = w64 (snd (s5_rp (x_pl cx) f)) ->
  getr regs 18 = w64 (x_nf cx) -> getr regs 19 = w64 lp -> getr regs 21 = w64 0 -> getr regs 22 = w64 m ->
  getr regs 23 = w64 t -> getr regs 24 = w64 (x_at cx f + x_np cx f) -> getr regs 25 = w64 (Z.of_nat f + 1) ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  lt_slots cx (rdW W mem) (S5_slots cx c m f) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S5CK) regs mem md) (lt_post B MT cx).

(* ----------------------------------- 0x85324: the last turn, before m_file -----------------------------------
   s5 = 0, s6 = m, s7 = t, s8 = P1 + NP, s9 = f + 1, s10 = (m + 0x2000) >> 3; the slot store 144(s1) at 0x85324
   is still to come *)
Definition S5_LST_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m t : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f + 1 = x_nf cx ->
  S5_body cx ly S W regs mem md k acc LFO_L c m t f ->
  lt_cm (rdW W mem) c m (x_st cx f) ->
  sa_str (rdW W mem) t (s5_txt (x_pl cx) f) ->
  getr regs 21 = w64 0 -> getr regs 22 = w64 m -> getr regs 23 = w64 t ->
  getr regs 24 = w64 (x_at cx f + x_np cx f) -> getr regs 25 = w64 (Z.of_nat f + 1) ->
  getr regs 26 = w64 ((m + seg_spec.MC_N) / 8) ->
  lt_slots cx (rdW W mem) (S5_slots cx c m f) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S5LST) regs mem md) (lt_post B MT cx).

End e.
End f.
End d.

(* the three inner cuts a call may return to at an FP state of its own *)
Section lta5. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Definition S5A_OTH (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, S5_OTH_stmt (fx := fx1) B MT f.
Definition S5A_LST (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, S5_LST_stmt (fx := fx1) B MT f.
Definition S5A_CK (B : asyms) (MT : ameter_ops) (f : nat) : Prop :=
  forall fx1 : YK11.FPState, S5_CK_stmt (fx := fx1) B MT f.
End lta5.

(* ======================================== the pure model facts ========================================
   Every lemma below is about SegModel and seg_spec alone (image A's kit's, word for word, then two of image B). *)

(* a list is the prefix of itself that its NUL cut keeps *)
Lemma s5_cut_nul_firstn : forall l, SegModel.cut_nul l = firstn (length (SegModel.cut_nul l)) l.
Proof.
induction l as [|b l IH]; [reflexivity|]. cbn [SegModel.cut_nul].
destruct (b =? 0); [reflexivity|]. cbn [length firstn]. rewrite <- IH. reflexivity.
Qed.
Lemma s5_cut_nul_len : forall l, (length (SegModel.cut_nul l) <= length l)%nat.
Proof.
induction l as [|b l IH]; [cbn; lia|]. cbn [SegModel.cut_nul].
destruct (b =? 0); cbn [length]; lia.
Qed.
Lemma s5_cut_nul_nulfree : forall l, ~ In 0 (SegModel.cut_nul l).
Proof.
induction l as [|b l IH]; [intros []|]. cbn [SegModel.cut_nul].
destruct (b =? 0) eqn:Hb; [intros []|]. cbn [In]. intros [Hz|Hz]; [|exact (IH Hz)].
apply Z.eqb_neq in Hb. exact (Hb Hz).
Qed.

(* one list is a suffix of another *)
Definition s5_sfx (a b : list Z) : Prop := exists j, (j <= length b)%nat /\ a = skipn j b.
Lemma s5_sfx_refl : forall b, s5_sfx b b.
Proof. intros b. exists 0%nat. split; [lia | reflexivity]. Qed.
Lemma s5_sfx_trans : forall a b c, s5_sfx a b -> s5_sfx b c -> s5_sfx a c.
Proof.
intros a b c (j1 & H1 & ->) (j2 & H2 & ->). exists (j1 + j2)%nat.
rewrite length_skipn in H1. split; [lia|]. rewrite skipn_skipn. reflexivity.
Qed.
Lemma s5_sfx_skipn : forall j b, s5_sfx (skipn j b) b.
Proof.
intros j b. destruct (Nat.le_gt_cases j (length b)) as [H|H].
- exists j. split; [lia | reflexivity].
- exists (length b). split; [lia|]. rewrite (skipn_all2 b) by lia. rewrite skipn_all2 by lia. reflexivity.
Qed.
Lemma s5_sfx_len : forall a b, s5_sfx a b -> (length a <= length b)%nat.
Proof. intros a b (j & H & ->). rewrite length_skipn. lia. Qed.
Lemma s5_sfx_nth : forall a b, s5_sfx a b ->
  forall i, (i < length a)%nat -> nth i a 0 = nth (length b - length a + i) b 0.
Proof.
intros a b (j & Hj & ->) i Hi. rewrite length_skipn in Hi |- *.
rewrite nth_skipn. f_equal. lia.
Qed.

(* the three readers of the payload move only forward *)
Lemma s5_u8_skip : forall l, snd (SegModel.fuzz_u8 l) = skipn 1 l.
Proof. intros [|b l]; reflexivity. Qed.
Lemma s5_u8_sfx : forall l, s5_sfx (snd (SegModel.fuzz_u8 l)) l.
Proof. intros l. rewrite s5_u8_skip. apply s5_sfx_skipn. Qed.
Lemma s5_u16_sfx : forall l, s5_sfx (snd (SegModel.fuzz_u16 l)) l.
Proof.
intros l. unfold SegModel.fuzz_u16.
destruct (SegModel.fuzz_u8 l) as [lo i1] eqn:E1.
destruct (SegModel.fuzz_u8 i1) as [hi i2] eqn:E2. cbn [snd].
apply (s5_sfx_trans i2 i1 l).
- pose proof (s5_u8_sfx i1) as H. rewrite E2 in H. exact H.
- pose proof (s5_u8_sfx l) as H. rewrite E1 in H. exact H.
Qed.
Lemma s5_take_fst : forall l n, fst (SegModel.fuzz_take l n) = firstn (Nat.min (Z.to_nat n) (length l)) l.
Proof. intros l n. reflexivity. Qed.
Lemma s5_take_snd : forall l n, snd (SegModel.fuzz_take l n) = skipn (Nat.min (Z.to_nat n) (length l)) l.
Proof. intros l n. reflexivity. Qed.
Lemma s5_take_sfx : forall l n, s5_sfx (snd (SegModel.fuzz_take l n)) l.
Proof. intros l n. rewrite s5_take_snd. apply s5_sfx_skipn. Qed.
Lemma s5_skip_sfx : forall k l, s5_sfx (seg_spec.seg_skip k l) l.
Proof.
induction k as [|k IH]; intros l; [apply s5_sfx_refl|].
cbn [seg_spec.seg_skip].
destruct (SegModel.fuzz_u8 l) as [b i1] eqn:E1.
destruct (SegModel.fuzz_u16 i1) as [len i2] eqn:E2.
destruct (SegModel.fuzz_take i2 len) as [p i3] eqn:E3.
apply (s5_sfx_trans _ i3); [apply IH|].
apply (s5_sfx_trans i3 i2); [pose proof (s5_take_sfx i2 len) as H; rewrite E3 in H; exact H|].
apply (s5_sfx_trans i2 i1); [pose proof (s5_u16_sfx i1) as H; rewrite E2 in H; exact H|].
pose proof (s5_u8_sfx l) as H. rewrite E1 in H. exact H.
Qed.
(* the turn's tail is a suffix of the input bytes *)
Lemma s5_tail_sfx : forall pl f, s5_sfx (seg_spec.seg_turn_tail pl f) (seg_spec.seg_in pl).
Proof.
intros pl f. unfold seg_spec.seg_turn_tail.
apply (s5_sfx_trans _ (snd (SegModel.fuzz_u8 (seg_spec.seg_cur pl f)))); [apply s5_u16_sfx|].
apply (s5_sfx_trans _ (seg_spec.seg_cur pl f)); [apply s5_u8_sfx|].
unfold seg_spec.seg_cur.
apply (s5_sfx_trans _ (seg_spec.seg_hdr pl)); [apply s5_skip_sfx|].
unfold seg_spec.seg_hdr.
apply (s5_sfx_trans _ (snd (SegModel.fuzz_u8 (snd (SegModel.fuzz_u8 (seg_spec.seg_in pl))))));
  [apply s5_u8_sfx|].
apply (s5_sfx_trans _ (snd (SegModel.fuzz_u8 (seg_spec.seg_in pl)))); [apply s5_u8_sfx | apply s5_u8_sfx].
Qed.

(* the file record a turn reads at a cursor, and the cursor the next turn starts from *)
Definition s5_file_of (l : list Z) : SegModel.file :=
  SegModel.File (fst (SegModel.fuzz_u8 l))
    (SegModel.fuzz_str (fst (SegModel.fuzz_take
       (snd (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 l))))
       (fst (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 l))))))).
Definition s5_next (l : list Z) : list Z :=
  snd (SegModel.fuzz_take
    (snd (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 l))))
    (fst (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 l))))).

Lemma s5_dec_files_length : forall k l, length (SegModel.dec_files k l) = k.
Proof.
induction k as [|k IH]; intros l; [reflexivity|]. cbn [SegModel.dec_files].
destruct (SegModel.fuzz_u8 l) as [lb i1]. cbn [fst snd].
destruct (SegModel.fuzz_u16 i1) as [len i2]. cbn [fst snd].
destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [fst snd length]. rewrite IH. reflexivity.
Qed.

Lemma s5_skip_S : forall k l, seg_spec.seg_skip (Datatypes.S k) l = seg_spec.seg_skip k (s5_next l).
Proof.
intros k l. cbn [seg_spec.seg_skip]. unfold s5_next.
destruct (SegModel.fuzz_u8 l) as [b i1]. cbn [fst snd].
destruct (SegModel.fuzz_u16 i1) as [len i2]. cbn [fst snd].
destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [fst snd]. reflexivity.
Qed.
Lemma s5_skip_S' : forall f h, seg_spec.seg_skip (Datatypes.S f) h = s5_next (seg_spec.seg_skip f h).
Proof.
induction f as [|f IH]; intros h.
- rewrite (s5_skip_S 0 h). cbn [seg_spec.seg_skip]. reflexivity.
- rewrite (s5_skip_S (Datatypes.S f) h), (IH (s5_next h)), <- (s5_skip_S f h). reflexivity.
Qed.

Lemma s5_dec_files_nth : forall k f l, (f < k)%nat ->
  nth f (SegModel.dec_files k l) (SegModel.File 0 []) = s5_file_of (seg_spec.seg_skip f l).
Proof.
induction k as [|k IH]; intros f l Hf; [lia|].
destruct f as [|f].
- cbn [SegModel.dec_files]. unfold s5_file_of. cbn [seg_spec.seg_skip].
  destruct (SegModel.fuzz_u8 l) as [lb i1]. cbn [fst snd].
  destruct (SegModel.fuzz_u16 i1) as [len i2]. cbn [fst snd].
  destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [fst snd nth]. reflexivity.
- cbn [SegModel.dec_files]. rewrite s5_skip_S. unfold s5_next.
  destruct (SegModel.fuzz_u8 l) as [lb i1]. cbn [fst snd].
  destruct (SegModel.fuzz_u16 i1) as [len i2]. cbn [fst snd].
  destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [fst snd nth]. apply IH. lia.
Qed.

(* turn f's record is read at the cursor of turn f *)
Lemma s5_file_eq : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl ->
  seg_spec.seg_file pl f = s5_file_of (seg_spec.seg_cur pl f).
Proof.
intros pl f Hf.
assert (Hlt : (f < length (seg_spec.seg_files pl))%nat) by (unfold seg_spec.seg_nfiles in Hf; lia).
unfold seg_spec.seg_file, seg_spec.seg_cur, seg_spec.seg_hdr, seg_spec.seg_files, seg_spec.seg_pay,
  SegModel.decode, seg_spec.seg_in in *.
destruct (SegModel.fuzz_u8 (seg_spec.zs pl)) as [b0 i1]. cbn [fst snd] in *.
destruct (SegModel.fuzz_u8 i1) as [fl i2]. cbn [fst snd] in *.
destruct (SegModel.fuzz_u8 i2) as [b2 i3]. cbn [fst snd] in *.
cbn [SegModel.p_files] in *. rewrite s5_dec_files_length in Hlt.
apply s5_dec_files_nth. exact Hlt.
Qed.
Lemma s5_lb_eq : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl ->
  seg_spec.seg_lb pl f = fst (SegModel.fuzz_u8 (seg_spec.seg_cur pl f)).
Proof.
intros pl f Hf. unfold seg_spec.seg_lb. rewrite (s5_file_eq pl f Hf).
unfold s5_file_of. cbn [SegModel.f_lb]. reflexivity.
Qed.
Lemma s5_txt_eq : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl ->
  seg_spec.seg_txt pl f = SegModel.cut_nul (fst (SegModel.fuzz_take
    (seg_spec.seg_turn_tail pl f) (seg_spec.seg_turn_len pl f))).
Proof.
intros pl f Hf. unfold seg_spec.seg_txt. rewrite (s5_file_eq pl f Hf).
unfold s5_file_of, SegModel.fuzz_str, seg_spec.seg_turn_tail, seg_spec.seg_turn_len.
cbn [SegModel.f_text]. reflexivity.
Qed.

(* the turn's text is the first seg_txt_n bytes of the turn's tail, and the counts are ordered *)
Lemma s5_txt_firstn : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl ->
  seg_spec.seg_txt pl f = firstn (length (seg_spec.seg_txt pl f)) (seg_spec.seg_turn_tail pl f) /\
  (length (seg_spec.seg_txt pl f) <= Z.to_nat (seg_spec.seg_turn_np pl f))%nat /\
  (Z.to_nat (seg_spec.seg_turn_np pl f) <= length (seg_spec.seg_turn_tail pl f))%nat.
Proof.
intros pl f Hf. pose proof (s5_txt_eq pl f Hf) as Htxt.
assert (Hnp : Z.to_nat (seg_spec.seg_turn_np pl f) =
  Nat.min (Z.to_nat (seg_spec.seg_turn_len pl f)) (length (seg_spec.seg_turn_tail pl f))).
{ unfold seg_spec.seg_turn_np. rewrite s5_take_fst, length_firstn, Nat2Z.id. lia. }
rewrite s5_take_fst in Htxt.
set (q := Nat.min (Z.to_nat (seg_spec.seg_turn_len pl f)) (length (seg_spec.seg_turn_tail pl f))) in *.
set (tl := seg_spec.seg_turn_tail pl f) in *.
assert (Hq : (q <= length tl)%nat) by (unfold q; lia).
assert (Hlen : (length (seg_spec.seg_txt pl f) <= q)%nat).
{ rewrite Htxt. pose proof (s5_cut_nul_len (firstn q tl)) as H. rewrite length_firstn in H. lia. }
split; [|split].
- rewrite Htxt at 1. rewrite (s5_cut_nul_firstn (firstn q tl)) at 1.
  rewrite firstn_firstn. rewrite <- Htxt. f_equal. lia.
- rewrite Hnp. exact Hlen.
- rewrite Hnp. exact Hq.
Qed.

(* the next turn's cursor: the tail past the bytes this turn took *)
Lemma s5_cur_S : forall pl f,
  seg_spec.seg_cur pl (Datatypes.S f) =
  skipn (Z.to_nat (seg_spec.seg_turn_np pl f)) (seg_spec.seg_turn_tail pl f).
Proof.
intros pl f.
unfold seg_spec.seg_turn_np, seg_spec.seg_turn_tail, seg_spec.seg_turn_len, seg_spec.seg_cur.
rewrite s5_skip_S'. unfold s5_next.
rewrite s5_take_snd, s5_take_fst, length_firstn, Nat2Z.id. f_equal. lia.
Qed.

(* the three shapes of a turn's label (SegModel.label_of) *)
Lemma s5_label_cases : forall pl f,
  (Z.land (seg_spec.seg_lb pl f) 128 <> 0 /\ s5_lab pl f = Some SegModel.longl) \/
  (Z.land (seg_spec.seg_lb pl f) 128 = 0 /\ seg_spec.seg_lb pl f = 0 /\ s5_lab pl f = None) \/
  (Z.land (seg_spec.seg_lb pl f) 128 = 0 /\ seg_spec.seg_lb pl f <> 0 /\
   s5_lab pl f = Some (SegModel.snprintf_s 40 SegModel.F_label [SegModel.AI (seg_spec.seg_lb pl f)])).
Proof.
intros pl f. unfold s5_lab, seg_spec.seg_label, SegModel.label_of.
destruct (Z.eqb_spec (Z.land (seg_spec.seg_lb pl f) 128) 0) as [H0|H0]; cbn [negb].
- destruct (Z.eqb_spec (seg_spec.seg_lb pl f) 0) as [Hz|Hz].
  + right; left. split; [exact H0 | split; [exact Hz | reflexivity]].
  + right; right. split; [exact H0 | split; [exact Hz | reflexivity]].
- left. split; [exact H0 | reflexivity].
Qed.
Lemma s5_longl_len : length SegModel.longl = 120%nat.
Proof. vm_compute. reflexivity. Qed.

(* ---- image B: the next turn's cursor as the code keeps it (s8 = P1 + NP from K85210 on; 0x85524 s4 = N1 - NP) ---- *)
(* the take never takes more than the tail holds *)
Lemma s5_np_le : forall pl f,
  (Z.to_nat (seg_spec.seg_turn_np pl f) <= length (seg_spec.seg_turn_tail pl f))%nat.
Proof.
intros pl f. unfold seg_spec.seg_turn_np. rewrite s5_take_fst, length_firstn, Nat2Z.id. lia.
Qed.
Lemma s5_np_nat : forall pl f, seg_spec.seg_turn_np pl f = Z.of_nat (Z.to_nat (seg_spec.seg_turn_np pl f)).
Proof. intros pl f. unfold seg_spec.seg_turn_np. rewrite Nat2Z.id. reflexivity. Qed.
(* the count left after turn f: N1 - NP *)
Lemma s5_cur_n_S : forall pl f,
  seg_spec.seg_cur_n pl (Datatypes.S f) =
  Z.of_nat (length (seg_spec.seg_turn_tail pl f)) - seg_spec.seg_turn_np pl f.
Proof.
intros pl f. unfold seg_spec.seg_cur_n. rewrite s5_cur_S, length_skipn.
pose proof (s5_np_le pl f) as H. pose proof (s5_np_nat pl f) as E.
rewrite Nat2Z.inj_sub by exact H. lia.
Qed.
(* the cursor after turn f: P1 + NP *)
Lemma s5_cur_at_S : forall pl p f,
  seg_spec.seg_cur_at pl p (Datatypes.S f) = seg_spec.seg_turn_at pl p f + seg_spec.seg_turn_np pl f.
Proof.
intros pl p f. unfold seg_spec.seg_cur_at, seg_spec.seg_turn_at. rewrite s5_cur_S, length_skipn.
pose proof (s5_np_le pl f) as H. pose proof (s5_np_nat pl f) as E.
rewrite Nat2Z.inj_sub by exact H. lia.
Qed.
