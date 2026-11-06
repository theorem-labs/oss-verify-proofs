(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module names changed; 85 of its 151 lines of code are new or changed and 3787 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match_lib.v, with its module paths changed; 255 of its 299 lines of code are new or changed and 107 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/Prog/fuzz_catalogue_row.v, with its module paths, module names, addresses and numbers changed; 236 of its 315 lines of code are new or changed and 220 lines of the source are left out. *)
(** ieq (plain build, 0x14c2c): proof of [ieq_contract] (ieq_c.v) from the contract of its callee strlen
    (strlen_c.v). Written new.

    Code (plain binary):
      0x14c2c-0x14c3c  frame of 32: ra s0 s1 s2 at sp+24 .. sp+0
      0x14c40 mv s0,a2 (word); mv s1,a1 (n); mv s2,a0 (s); mv a0,a2; 0x14c50 jal strlen
      0x14c54 bne s1,a0 -> RET0; 0x14c58 a0 = 1; 0x14c5c beqz s1 -> EPI
      LOOP 0x14c60 lbu a1,0(s2); a2 = a1 - 'A'; lbu a3,0(s0); a2 = (a2 <u 26) << 5; a1 += a2 (SegModel.lower)
           0x14c78 bne a1,a3 -> RET0; s1 -= 1; s0 += 1; s2 += 1; 0x14c88 beqz s1 -> EPI; j LOOP
      RET0 0x14c90 mv a0,zero.  EPI 0x14c94 restore ra s0 s1 s2; addi sp,sp,32; ret
    Shape as reac_segconf_find.v: [epi] the shared exit, [loop] an induction on the bytes left (s0 = word + i,
    s1 = n - i, s2 = s + i, a0 = 1), [body] the prologue and the strlen call. strlen gets word's bytes, its NUL and
    the slack to the next 8-byte boundary (cstr_at), cut to exactly that slack so the frame stores cannot touch it.
    The fold `b + 32 (b - 'A' <u 26)` is SegModel.lower on every byte: [ieq_byte_brute] checks the stepped term on all
    256 values by vm_compute. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec strlen_c ieq_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Facts the walk needs *)
Lemma ieq_prefix : forall m a (l1 l2 : list byte), bytes_at rsegs m a (l1 ++ l2) -> bytes_at rsegs m a l1.
Proof. intros m a l1 l2 H. apply bytes_at_app in H. destruct H as [H _]. exact H. Qed.

Lemma ieq_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ieq_eqb_true : forall x y : word, bv_eqb x y = true -> x = y.
Proof. intros x y H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma ieq_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

Lemma ieq_byte_lit : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof.
  intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma ieq_zs_nul : forall bs : list byte, ~ In 0 (zs bs) -> ~ In (Z_to_bv 8 0) bs.
Proof.
  intros bs H Hin. apply H. unfold zs. change 0 with (bv_unsigned (Z_to_bv 8 0)). apply in_map. exact Hin.
Qed.

Lemma ieq_skipn_nth : forall {A} (l : list A) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros A l. induction l as [|y l IH]; intros [|i] x E; cbn [nth_error] in E; try discriminate.
  - injection E as <-. reflexivity.
  - cbn [skipn]. apply IH. exact E.
Qed.

Lemma ieq_skipn_nil : forall {A} (l : list A) k, (length l <= k)%nat -> skipn k l = [].
Proof.
  intros A l. induction l as [|x l IH]; intros [|k] H; cbn [length skipn] in *; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma ieq_zs_skipn : forall (l : list byte) i b, nth_error l i = Some b ->
  skipn i (zs l) = bv_unsigned b :: skipn (S i) (zs l).
Proof.
  unfold zs. induction l as [|y l IH]; intros [|i] b E; cbn [nth_error] in E; try discriminate.
  - injection E as <-. reflexivity.
  - cbn [map skipn]. apply IH. exact E.
Qed.

(** One byte of a block, as `lbu` reads it. *)
Lemma ieq_rd1 : forall m a (bs : list byte) i b, bytes_at rsegs m a bs -> nth_error bs i = Some b ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [b].
Proof.
  intros m a bs i b H E.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; congruence).
  rewrite (bytes_at_ov_read rsegs m a bs i 1 H) by lia.
  rewrite (ieq_skipn_nth bs i b E). reflexivity.
Qed.

Lemma ieq_lower_range : forall c, 0 <= c < 256 -> 0 <= lower c < 256.
Proof.
  intros c Hc. unfold lower.
  destruct (65 <=? c) eqn:E1; destruct (c <=? 90) eqn:E2; cbn [andb];
    rewrite ?Z.leb_le, ?Z.leb_gt in *; lia.
Qed.

Lemma ieq_bv_eqb_comm : forall x y : word, bv_eqb x y = bv_eqb y x.
Proof. intros x y. unfold bv_eqb. apply Z.eqb_sym. Qed.

(** A word function of one byte value, checked on all 256 values. *)
Lemma ieq_wbrute : forall (f g : Z -> word) (c : Z), 0 <= c < 256 ->
  forallb (fun k => bv_eqb (f (Z.of_nat k)) (g (Z.of_nat k))) (seq 0 256) = true -> f c = g c.
Proof.
  intros f g c Hc H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat c) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. apply ieq_eqb_true. exact H.
Qed.

(** A goal [L = R] whose sides depend on the byte b only: abstract bv_unsigned b and check all its values. *)
Ltac ieq_byte_brute b :=
  let Hr := fresh "Hr" in
  pose proof (ieq_byte_range b) as Hr;
  rewrite <- (ieq_byte_lit b);
  revert Hr; generalize (bv_unsigned b);
  let c := fresh "c" in let Hc := fresh "Hc" in
  intros c Hc;
  lazymatch goal with
  | |- ?L = ?R =>
      let F := lazymatch eval pattern c in L with ?F _ => F end in
      let G := lazymatch eval pattern c in R with ?G _ => G end in
      apply (ieq_wbrute F G c Hc); vm_compute; reflexivity
  end.

(** The test `bne` of the loop: the folded byte b of s against the byte x of word. Rewrites the condition to
    [lower (bv_unsigned b) =? bv_unsigned x]. *)
Ltac ieq_fold_cond b x :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      lazymatch c with
      | context [bv_eqb ?X ?Y] =>
          let EX := fresh "EX" in let EY := fresh "EY" in
          first [ assert (EX : X = Z_to_bv 64 (lower (bv_unsigned b))) by ieq_byte_brute b;
                  assert (EY : Y = Z_to_bv 64 (bv_unsigned x)) by ieq_byte_brute x
                | assert (EX : Y = Z_to_bv 64 (lower (bv_unsigned b))) by ieq_byte_brute b;
                  assert (EY : X = Z_to_bv 64 (bv_unsigned x)) by ieq_byte_brute x;
                  rewrite (ieq_bv_eqb_comm X Y)
                | fail 100 "ieq-debug: fold condition" c ];
          rewrite EX, EY; clear EX EY;
          rewrite (ieq_eqb_lit (lower (bv_unsigned b)) (bv_unsigned x))
            by (first [ pose proof (ieq_lower_range _ (ieq_byte_range b)); lia
                      | pose proof (ieq_byte_range x); lia ])
      end
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 100 "ieq-debug: pc" pc
  end.

(** A branch on [x =? y] in the condition: both cases, the hypothesis named H. *)
Ltac ieq_br H :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      lazymatch c with
      | context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) as [H|H]; cbn [negb]; cbv iota
      end
  end.

Section Ieq.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (s n wd Sp lo : Z) (l bw sl : list byte).
Hypothesis HSL : strlen_contract.
Hypothesis HBL : bytes_at rsegs m0 s l.
Hypothesis HLN : Z.of_nat (length l) = n.
Hypothesis Hs : 0 < s < 2^64.
Hypothesis Hsn : s + n <= 2^64.
Hypothesis HsA : s + n <= Sp - 32 \/ Sp <= s.
Hypothesis HBW : bytes_at rsegs m0 wd (bw ++ ZERO :: sl).
Hypothesis HNW : ~ In (Z_to_bv 8 0) bw.
Hypothesis Hsl : (- (wd + Z.of_nat (length bw) + 1)) mod 8 <= Z.of_nat (length sl).
Hypothesis Hwd : 0 < wd < 2^64.
Hypothesis Hwb : wd + Z.of_nat (length bw) + 1 + Z.of_nat (length sl) <= 2^64.
Hypothesis HwA : wd + Z.of_nat (length bw) + 1 + Z.of_nat (length sl) <= Sp - 32 \/ Sp <= wd.
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 32 <= Sp.
Hypothesis HS : Sp < 2^64.

Local Abbreviation Post := (fun ms' : machine_state =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (b2z (ieq (zs l) (zs bw))))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(Sp - 32, Sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp).

(** The frame between the prologue and the epilogue. *)
Definition frm (m : word -> option byte) : Prop :=
  rw_cells rsegs m (Sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (Sp + -32) /\ munch [(Sp - 32, Sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

(** strlen writes nothing. *)
Lemma frm_call : forall m m', frm m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm m'.
Proof.
  intros m m' (FR & ST & MU & WM & _) MU' WM' MI'.
  split; [eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | exact I]|].
  split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]; intros x _; exact I|].
  split; [exact (wmono_trans rsegs _ _ _ WM WM') | exact MI'].
Qed.

Lemma frm_l : forall m, frm m -> bytes_at rsegs m s l.
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HBL | exact MU |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma frm_wfull : forall m, frm m -> bytes_at rsegs m wd (bw ++ ZERO :: sl).
Proof.
  intros m (_ & _ & MU & _ & _). eapply bytes_at_transport; [exact HBW | exact MU |].
  rewrite length_app. cbn [length disjoint_from]. split; [lia | exact I].
Qed.

Lemma frm_w : forall m, frm m -> bytes_at rsegs m wd bw.
Proof. intros m FRM. exact (ieq_prefix _ _ _ _ (frm_wfull m FRM)). Qed.

(** The exit 0x14c94: restore ra and s0-s2, return with a0 = v. *)
Lemma epi : forall m (x1 y0 y1 y2 w8 w9 v z1 z2 z3 z4 z5 z6 z7 w18 u3 u4 u5 u6 : word),
  v = Z_to_bv 64 (b2z (ieq (zs l) (zs bw))) -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -32)) gp tp y0 y1 y2 w8 w9 v z1 z2 z3 z4 z5 z6 z7 w18
             s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x14c94) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 y0 y1 y2 w8 w9 v z1 z2 z3 z4 z5 z6 z7 w18 u3 u4 u5 u6 Ev (FR & ST & MU & WM & MI).
  subst v.
  do 6 step.
  apply evt_done. exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, u3, u4, u5, u6, m.
  split; [unfold mkR; repeat f_equal; lia|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  pose proof (stk_release rsegs m lo (Sp + -32) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  replace (Sp + -32 + Z.of_nat 32) with Sp in R by lia. exact R.
Qed.

(** The loop head 0x14c60 with i bytes agreed and j = n - i left: s0 = word + i, s1 = j, s2 = s + i, a0 = 1. *)
Lemma loop : forall j i m (x1 y0 y1 y2 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 w8 w9 w10 w18 : word),
  w8 = Z_to_bv 64 (wd + Z.of_nat i) -> w9 = Z_to_bv 64 (Z.of_nat j) -> w18 = Z_to_bv 64 (s + Z.of_nat i) ->
  w10 = Z_to_bv 64 1 ->
  (i + j = length l)%nat -> (0 < j)%nat -> length bw = length l ->
  ieq (zs l) (zs bw) = ieq_go (skipn i (zs l)) (skipn i (zs bw)) -> frm m ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -32)) gp tp y0 y1 y2 w8 w9 w10 z1 z2 z3 z4 z5 z6 z7
             w18 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x14c60) fc None m (seg_rom rsegs)).
Proof.
  induction j as [|j IH];
    intros i m x1 y0 y1 y2 z1 z2 z3 z4 z5 z6 z7 u3 u4 u5 u6 w8 w9 w10 w18 E8 E9 E18 E10 Hij Hj Lbw RF FRM;
    [lia|].
  subst w8 w9 w18 w10.
  assert (Hi : (i < length l)%nat) by lia.
  destruct (nth_error l i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  destruct (nth_error bw i) as [x|] eqn:Ex; [|apply nth_error_None in Ex; lia].
  pose proof (ieq_rd1 _ _ _ _ _ (frm_l m FRM) Eb) as RD1.
  pose proof (ieq_rd1 _ _ _ _ _ (frm_w m FRM) Ex) as RD2.
  rewrite (ieq_zs_skipn l i b Eb), (ieq_zs_skipn bw i x Ex) in RF. cbn [ieq_go] in RF.
  (* lbu a1; addi a2; lbu a3; sltiu a2; slli a2; add a1; bne a1,a3 *)
  do 7 step.
  ieq_fold_cond b x.
  destruct (Z.eqb_spec (lower (bv_unsigned b)) (bv_unsigned x)) as [EQ|NE]; cbn [negb]; cbv iota.
  - (* the bytes agree: the next place *)
    try rewrite (proj2 (Z.eqb_eq _ _) EQ) in RF. cbn [andb] in RF.
    do 4 step.
    rewrite ieq_eqb_lit by lia.
    destruct (Z.eqb_spec (Z.of_nat (S j) + -1) 0) as [J0|J0]; cbv iota.
    + (* that was the last place: 1 *)
      assert (j = 0%nat) by lia. subst j.
      rewrite (ieq_skipn_nil (zs l) (S i)), (ieq_skipn_nil (zs bw) (S i)) in RF
        by (unfold zs; rewrite length_map; lia).
      eapply epi; [|exact FRM]. rewrite RF. reflexivity.
    + step.
      eapply (IH (S i));
        [ first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]
        | first [reflexivity | f_equal; lia] | reflexivity | lia | lia | exact Lbw | exact RF | exact FRM ].
  - (* the bytes differ: 0 *)
    try rewrite (proj2 (Z.eqb_neq _ _) NE) in RF. cbn [andb] in RF.
    step.
    eapply epi; [|exact FRM]. rewrite RF. reflexivity.
Qed.

(** The whole function from its entry. *)
Lemma body : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 n) (Z_to_bv 64 wd)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14c2c) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI.
  (* The prologue's stores transport (and so replace) the section hypotheses the lemmas use: take them first. *)
  pose proof (loop (length l) 0) as LP. pose proof epi as EP. pose proof frm_call as FC.
  pose proof frm_wfull as FW.
  pose proof (munch_refl [(Sp - 32, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 32 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 32) with 32 in ST1, FR.
  replace (Sp - 32) with (Sp + -32) in ST1, FR by lia.
  (* addi sp; sd ra, s0, s1, s2; mv s0,a2; mv s1,a1; mv s2,a0; mv a0,a2; jal strlen *)
  do 10 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FRM1 : frm mm) by (refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption);
    pose proof (FW mm FRM1) as HW1
  end.
  eapply evt_cut.
  { eapply HSL with (str := bw) (slack := sl); rewrite ?unsigned_lit by lia.
    - exact HW1.
    - exact HNW.
    - first [exact Hsl | lia].
    - eassumption. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
              MU2 & WM2 & MI2 & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  pose proof (FC _ _ FRM1 MU2 WM2 MI2) as FRM2. clear FRM1 HW1.
  (* 0x14c54 bne s1,a0: n against strlen(word) *)
  step.
  rewrite ieq_eqb_lit by lia.
  ieq_br EN.
  - (* n = strlen(word): a0 = 1; beqz s1 *)
    step. step.
    rewrite ieq_eqb_lit by lia.
    ieq_br Hn0.
    + (* n = 0: both empty, 1 *)
      eapply EP; [|exact FRM2].
      assert (El : l = []) by (apply length_zero_iff_nil; lia).
      assert (Eb : bw = []) by (apply length_zero_iff_nil; lia).
      rewrite El, Eb. reflexivity.
    + eapply LP;
        [ first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]
        | first [reflexivity | f_equal; lia] | reflexivity | lia | lia | lia | | exact FRM2 ].
      unfold ieq.
      replace ((length (zs l) =? length (zs bw))%nat) with true
        by (symmetry; apply Nat.eqb_eq; unfold zs; rewrite !length_map; lia).
      reflexivity.
  - (* n <> strlen(word): mv a0,zero; 0 *)
    step.
    eapply EP; [|exact FRM2].
    unfold ieq.
    replace ((length (zs l) =? length (zs bw))%nat) with false
      by (symmetry; apply Nat.eqb_neq; unfold zs; rewrite !length_map; lia).
    reflexivity.
Qed.

End Ieq.

Theorem ieq_holds : strlen_contract -> ieq_contract.
Proof.
  intros HSL. unfold ieq_contract, ieq_pre, IEQ, IEQ_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo l w
    (Hs0 & HB & HLN & HsA & Hw0 & (bw & sl & HW & HZW & HNW & HSLK) & HwA & (ST & HK & H16 & HR) & MI).
  subst w. clear HR.
  assert (Lzw : length (zs bw) = length bw) by (unfold zs; apply length_map).
  rewrite Lzw in HwA, HSLK. unfold apart in HsA, HwA.
  pose proof (ieq_zs_nul _ HNW) as HNWb. clear HNW.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  change (bv_modulus 64) with (2^64) in Rsp, Ra0, Ra1, Ra2.
  pose proof (bytes_at_bound _ _ _ _ HB) as Bs.
  pose proof (proj1 ST) as Hlo.
  (* the slack strlen reads: exactly the bytes up to the next 8-byte boundary *)
  pose proof (Z.mod_pos_bound (- (bv_unsigned a2 + Z.of_nat (length bw) + 1)) 8 ltac:(lia)) as K8b.
  remember ((- (bv_unsigned a2 + Z.of_nat (length bw) + 1)) mod 8) as K8 eqn:EK.
  assert (SL' : exists sl', bytes_at rsegs m (bv_unsigned a2) (bw ++ ZERO :: sl') /\ Z.of_nat (length sl') = K8).
  { exists (firstn (Z.to_nat K8) sl). split.
    - apply (ieq_prefix _ _ _ (skipn (Z.to_nat K8) sl)).
      rewrite <- app_assoc. cbn [app]. rewrite firstn_skipn. exact HW.
    - rewrite length_firstn. lia. }
  clear HW. destruct SL' as (sl' & HW & Lsl).
  assert (SLK2 : (- (bv_unsigned a2 + Z.of_nat (length bw) + 1)) mod 8 <= Z.of_nat (length sl'))
    by (rewrite <- EK; lia).
  (* word, its NUL and that slack lie apart from the frame [sp - 32, sp) *)
  assert (DW : bv_unsigned a2 + Z.of_nat (length bw) + 1 + Z.of_nat (length sl') <= bv_unsigned sp - 32
               \/ bv_unsigned sp <= bv_unsigned a2).
  { clear - HwA HK H16 Lsl EK. rewrite Lsl. subst K8. destruct HwA as [H|H]; [left | right; exact H].
    Z.div_mod_to_equations. lia. }
  assert (DL : bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)
    by lia.
  pose proof (bytes_at_bound _ _ _ _ HW) as Bw. rewrite length_app in Bw. cbn [length] in Bw.
  clear EK K8b HSLK Lsl HwA HsA H16. clear K8.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  pose proof (Z_to_bv_lit_self a1) as Ea1. pose proof (Z_to_bv_lit_self a2) as Ea2.
  set (Sp := bv_unsigned sp) in *. set (s := bv_unsigned a0) in *. set (n := bv_unsigned a1) in *.
  set (wd := bv_unsigned a2) in *.
  rewrite <- Esp, <- Ea0, <- Ea1, <- Ea2. clearbody Sp s n wd. clear Esp Ea0 Ea1 Ea2.
  eapply evt_mono.
  - eapply (body ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s n wd Sp lo l bw sl');
      first [eassumption | lia].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                -> & MU & WM & MI' & ST').
    unfold ret_post. rewrite unsigned_lit by lia.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST' | exact I].
Qed.
