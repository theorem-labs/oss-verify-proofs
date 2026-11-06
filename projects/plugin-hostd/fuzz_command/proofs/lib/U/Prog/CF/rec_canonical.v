(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Words.
Local Open Scope Z_scope.

Definition sep_start (S : list byte) : Prop := S = [] \/ exists b S', S = b :: S' /\ is_sep b = true.

Lemma words_go_app_sep : forall A cur S, sep_start S ->
  words_go cur (A ++ S) = words_go cur A ++ words_go [] S.
Proof.
  induction A as [|a A IH]; intros cur S HS.
  - cbn [app]. destruct HS as [-> | (b & S' & -> & Hb)].
    + destruct cur; reflexivity.
    + cbn [words_go]. rewrite Hb. destruct cur as [|c cur]; reflexivity.
  - cbn [app words_go]. destruct (is_sep a).
    + destruct cur as [|c cur]; [apply IH; exact HS|]. rewrite IH by exact HS. reflexivity.
    + apply IH. exact HS.
Qed.

Lemma words_go_skip : forall S X, Forall (fun b => is_sep b = true) S -> words_go [] (S ++ X) = words_go [] X.
Proof.
  induction S as [|b S IH]; intros X H; [reflexivity|].
  inversion H as [|? ? Hb HS]; subst. cbn [app words_go]. rewrite Hb. apply IH. exact HS.
Qed.

Lemma words_go_nonsep : forall w cur, Forall (fun b => is_sep b = false) w ->
  words_go cur w = match rev w ++ cur with [] => [] | _ :: _ => [rev (rev w ++ cur)] end.
Proof.
  induction w as [|b w IH]; intros cur H.
  - destruct cur; reflexivity.
  - inversion H as [|? ? Hb Hw]; subst. cbn [words_go]. rewrite Hb. rewrite IH by exact Hw.
    cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma words_go_word : forall w, w <> [] -> Forall (fun b => is_sep b = false) w -> words_go [] w = [w].
Proof.
  intros w Hne H. rewrite words_go_nonsep by exact H. rewrite app_nil_r.
  destruct (rev w) as [|x r] eqn:E.
  - exfalso. apply Hne. apply (f_equal (@rev byte)) in E. rewrite rev_involutive in E. exact E.
  - rewrite <- E, rev_involutive. reflexivity.
Qed.

Lemma rev_cons_ne : forall (c : byte) cur, rev (c :: cur) <> [].
Proof. intros c cur E. apply (f_equal (@length byte)) in E. rewrite length_rev in E. discriminate. Qed.

Lemma words_go_ne : forall T cur, Forall (fun w => w <> []) (words_go cur T).
Proof.
  induction T as [|b T IH]; intros cur.
  - destruct cur as [|c cur]; cbn [words_go]; [constructor|]. constructor; [apply rev_cons_ne | constructor].
  - cbn [words_go]. destruct (is_sep b); [|apply IH].
    destruct cur as [|c cur]; [apply IH|]. constructor; [apply rev_cons_ne | apply IH].
Qed.

Lemma join_sp_cons2 : forall x y X, join_sp (x :: y :: X) = x ++ SPACE :: join_sp (y :: X).
Proof. reflexivity. Qed.

Lemma join_sp_snoc : forall X w,
  join_sp (X ++ [w]) = match X with [] => w | _ :: _ => join_sp X ++ SPACE :: w end.
Proof.
  induction X as [|x X IH]; intros w; [reflexivity|].
  destruct X as [|y X']; [reflexivity|].
  change ((x :: y :: X') ++ [w]) with (x :: y :: (X' ++ [w])).
  rewrite join_sp_cons2. change (y :: (X' ++ [w])) with ((y :: X') ++ [w]). rewrite IH.
  rewrite join_sp_cons2. rewrite <- app_assoc. reflexivity.
Qed.

Lemma join_sp_nil : forall X, Forall (fun w => w <> []) X -> join_sp X = [] -> X = [].
Proof.
  intros X HF E. destruct X as [|x X]; [reflexivity|]. exfalso.
  inversion HF as [|? ? Hx _]; subst.
  destruct X as [|y X]; cbn [join_sp] in E; [exact (Hx E)|].
  destruct x; discriminate.
Qed.

Lemma firstn_add : forall (T : list byte) i d, firstn (i + d) T = firstn i T ++ firstn d (skipn i T).
Proof.
  intros T i. revert T. induction i as [|i IH]; intros T d; [reflexivity|].
  destruct T as [|t T]; [destruct d; reflexivity|]. cbn [Nat.add firstn skipn app]. rewrite IH. reflexivity.
Qed.

Lemma skipn_nth : forall (T : list byte) i b, nth_error T i = Some b -> skipn i T = b :: skipn (S i) T.
Proof.
  induction T as [|t T IH]; intros i b H; [destruct i; discriminate|].
  destruct i as [|i]; cbn in H |- *; [injection H as ->; reflexivity|]. apply IH. exact H.
Qed.

Lemma Forall_seg : forall (P : byte -> Prop) T i d,
  (forall t b, (i <= t < i + d)%nat -> nth_error T t = Some b -> P b) -> Forall P (firstn d (skipn i T)).
Proof.
  intros P T. induction T as [|x T IH]; intros i d H.
  - rewrite skipn_nil, firstn_nil. constructor.
  - destruct i as [|i].
    + destruct d as [|d]; cbn [skipn firstn]; [constructor|]. constructor.
      * apply (H 0%nat); [lia | reflexivity].
      * apply (IH 0%nat d). intros t b Ht Hb. apply (H (S t)); [lia | exact Hb].
    + cbn [skipn]. apply IH. intros t b Ht Hb. apply (H (S t)); [lia | exact Hb].
Qed.

Lemma seg_ne : forall (T : list byte) j d, (j < length T)%nat -> (0 < d)%nat -> firstn d (skipn j T) <> [].
Proof.
  intros T j d Hj Hd. destruct (nth_error T j) as [b|] eqn:E; [|apply nth_error_None in E; lia].
  rewrite (skipn_nth T j b E). destruct d; [lia|]. discriminate.
Qed.

Definition bndry (T : list byte) (i : nat) : Prop :=
  i = 0%nat \/ exists b, nth_error T i = Some b /\ is_sep b = true.

Lemma pass_words : forall T i j k, bndry T i -> (i <= j < k)%nat -> (k <= length T)%nat ->
  (forall t b, (i <= t < j)%nat -> nth_error T t = Some b -> is_sep b = true) ->
  (forall t b, (j <= t < k)%nat -> nth_error T t = Some b -> is_sep b = false) ->
  words (firstn k T) = words (firstn i T) ++ [firstn (k - j) (skipn j T)].
Proof.
  intros T i j k HB Hij Hk HS HW.
  assert (E : firstn k T = firstn i T ++ (firstn (j - i) (skipn i T) ++ firstn (k - j) (skipn j T))).
  { replace k with (i + ((j - i) + (k - j)))%nat at 1 by lia. rewrite firstn_add. f_equal.
    rewrite firstn_add, skipn_skipn. replace (j - i + i)%nat with j by lia. reflexivity. }
  assert (FS : Forall (fun b => is_sep b = true) (firstn (j - i) (skipn i T))).
  { apply Forall_seg. intros t b Ht Hb. apply (HS t b); [lia | exact Hb]. }
  assert (FW : Forall (fun b => is_sep b = false) (firstn (k - j) (skipn j T))).
  { apply Forall_seg. intros t b Ht Hb. apply (HW t b); [lia | exact Hb]. }
  assert (NE : firstn (k - j) (skipn j T) <> []) by (apply seg_ne; lia).
  unfold words. rewrite E. destruct HB as [-> | (b & Eb & Sb)].
  - change (firstn 0 T) with (@nil byte). rewrite app_nil_l. cbn [words_go app].
    rewrite words_go_skip by exact FS. apply words_go_word; assumption.
  - assert (Hji : (i < j)%nat).
    { destruct (Nat.eq_dec i j) as [Eij|]; [|lia]. exfalso. rewrite <- Eij in HW.
      pose proof (HW i b ltac:(lia) Eb) as C. rewrite Sb in C. discriminate. }
    rewrite words_go_app_sep.
    + f_equal. rewrite words_go_skip by exact FS. apply words_go_word; assumption.
    + right. rewrite (skipn_nth T i b Eb). destruct (j - i)%nat as [|d] eqn:Ed; [lia|].
      exists b, (firstn d (skipn (S i) T) ++ firstn (k - j) (skipn j T)). split; [reflexivity | exact Sb].
Qed.

Lemma end_words : forall T i, bndry T i -> (i <= length T)%nat ->
  (forall t b, (i <= t < length T)%nat -> nth_error T t = Some b -> is_sep b = true) ->
  words T = words (firstn i T).
Proof.
  intros T i HB Hi HS.
  assert (FS : Forall (fun b => is_sep b = true) (skipn i T)).
  { assert (E2 : firstn (length T - i) (skipn i T) = skipn i T) by (apply firstn_all2; rewrite length_skipn; lia).
    rewrite <- E2.
    apply Forall_seg. intros t b Ht Hb. apply (HS t b); [lia | exact Hb]. }
  unfold words. rewrite <- (firstn_skipn i T) at 1. destruct HB as [-> | (b & Eb & Sb)].
  - change (firstn 0 T) with (@nil byte). change (skipn 0 T) with T in *. rewrite app_nil_l.
    rewrite <- (app_nil_r T) at 1. rewrite words_go_skip by exact FS. reflexivity.
  - rewrite words_go_app_sep.
    + rewrite <- (app_nil_r (skipn i T)). rewrite words_go_skip by exact FS. apply app_nil_r.
    + right. rewrite (skipn_nth T i b Eb). exists b, (skipn (S i) T). split; [reflexivity | exact Sb].
Qed.

Lemma canon_snoc : forall X w,
  join_sp (words X ++ [w]) = match canon X with [] => w | _ :: _ => canon X ++ SPACE :: w end.
Proof.
  intros X w. rewrite join_sp_snoc. unfold canon.
  destruct (words X) as [|x Y] eqn:E; [reflexivity|].
  destruct (join_sp (x :: Y)) as [|c r] eqn:J; [|reflexivity].
  exfalso. assert (HF : Forall (fun w0 => w0 <> []) (x :: Y)) by (rewrite <- E; apply words_go_ne).
  pose proof (join_sp_nil _ HF J). discriminate.
Qed.

End Words.

Lemma eqb64 : forall x y, (0 <= x < 2 ^ 64)%Z -> (0 <= y < 2 ^ 64)%Z ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma ltu64 : forall x y, (0 <= x < 2 ^ 64)%Z -> (0 <= y < 2 ^ 64)%Z ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8)%Z with 256%Z in R. exact R.
Qed.

Lemma eqb_zxb : forall (b : byte) z, (0 <= z < 2 ^ 64)%Z -> bv_eqb (zxb b) (Z_to_bv 64 z) = Z.eqb (bv_unsigned b) z.
Proof.
  intros b z Hz. pose proof (byte_range b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma read1 : forall m a (T : list byte) i b, bytes_at rsegs m a T -> nth_error T i = Some b ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i + 0)) 1 = Some [b].
Proof.
  intros m a T i b HB E. rewrite <- Z.add_assoc.
  assert (Hi : (i < length T)%nat) by (apply nth_error_Some; rewrite E; discriminate).
  rewrite (bytes_at_read rsegs m a T (Z.of_nat i + 0) 1 HB) by lia.
  rewrite Z.add_0_r, Nat2Z.id, (skipn_nth T i b E). reflexivity.
Qed.

Lemma rc_sltiu : forall (z : Z) (I : Z), (0 < z < 2 ^ 64)%Z -> bv_wrap 64 I = 1%Z ->
  v_sltiu (Z_to_bv 64 z) I = Z_to_bv 64 0.
Proof.
  intros z I Hz HI. unfold v_sltiu. rewrite unsigned_lit by lia. rewrite HI.
  replace (z <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma rc_snez : forall z, (0 < z < 2 ^ 64)%Z -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 z) = Z_to_bv 64 1.
Proof.
  intros z Hz. unfold v_sltu, c_ltu. rewrite ltu64 by lia.
  replace (0 <? z)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma rc_not : forall z, (0 <= z < 2 ^ 64)%Z ->
  Z_to_bv 64 (Z.lxor z 18446744073709551615) = Z_to_bv 64 (18446744073709551615 - z).
Proof.
  intros z Hz. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z. rewrite lnot_mod64 by lia. rewrite Zmod_mod.
  unfold Z.lnot. Z.div_mod_to_equations. lia.
Qed.

Ltac nb :=
  first [ rewrite ltu64 by lia | rewrite eqb64 by lia ];
  first [ match goal with |- context [(?x <? ?y)%Z] => replace (x <? y)%Z with false by (symmetry; apply Z.ltb_ge; lia) end
        | match goal with |- context [(?x =? ?y)%Z] => replace (x =? y)%Z with false by (symmetry; apply Z.eqb_neq; lia) end ];
  cbn [negb]; cbv iota.

Ltac chk :=
  try match goal with |- context [v_sltiu (Z_to_bv 64 ?z) ?I] => rewrite (rc_sltiu z I) by first [lia | reflexivity] end;
  match goal with |- context [bv_eqb ?X ?Y] => replace (bv_eqb X Y) with false by (vm_compute; reflexivity) end;
  cbn [negb]; cbv iota.

Ltac zeq := first [reflexivity | f_equal; lia | (rewrite ?unsigned_lit by lia; f_equal; lia)].

Ltac rcfix :=
  try change (bv_wrap 64 (-1)) with 18446744073709551615%Z;
  repeat match goal with |- context [Z_to_bv 64 (Z.lxor ?u 18446744073709551615)] =>
    rewrite (rc_not u) by (rewrite ?unsigned_lit by lia; lia) end;
  repeat match goal with |- context [v_sltu (Z_to_bv 64 0) (Z_to_bv 64 ?z)] => rewrite (rc_snez z) by lia end;
  rewrite ?unsigned_lit by lia.

Section Loops.
Local Open Scope Z_scope.
Variables (r1 spw r3 r4 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31 : word)
  (F : bvmap 5 word) (fc : bv 32) (text p : Z) (T : list byte) (m0 : word -> option byte)
  (junk : list byte) (s1v s0v rav : word).
Hypothesis TB : 0 < text /\ text + Z.of_nat (length T) <= 2 ^ 64.
Hypothesis PB : 0 < p /\ p + Z.of_nat (length T) + 1 < 2 ^ 64.
Hypothesis SEP : text + Z.of_nat (length T) <= p \/ p + Z.of_nat (length T) + 1 <= text.
Hypothesis FRSEP : p + Z.of_nat (length T) + 1 <= bv_unsigned spw.
Hypothesis LMX : Z.of_nat (length T) <= 8192.

Definition rcst (x5 x6 x7 x12 x13 : word) (pc : Z) (m : word -> option byte) : machine_state :=
  MS (mkR r1 spw r3 r4 x5 x6 x7 (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 text) (Z_to_bv 64 p)
          (Z_to_bv 64 (18446744073709551615 - p)) x12 x13 (Z_to_bv 64 (18446744073709551615 - text))
          (Z_to_bv 64 1) (Z_to_bv 64 32) (Z_to_bv 64 9)
          r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition binv (m : word -> option byte) (out : list byte) : Prop :=
  bytes_at rsegs m text T /\ wr_at rsegs m p (Z.of_nat (length T) + 1) /\ bytes_at rsegs m p out /\
  rw_cells rsegs m (bv_unsigned spw) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] /\
  munch [(p, p + Z.of_nat (length T) + 1)] m0 m /\ wmono rsegs m0 m.

Lemma binv_store : forall m out c a, binv m out -> a = p + Z.of_nat (length out) ->
  Z.of_nat (length out) <= Z.of_nat (length T) ->
  binv (write_to_mem m (Z_to_bv 64 a) [c]) (out ++ [c]).
Proof.
  intros m out c a (HT & HW & HO & HF & HM & HWM) -> Hl.
  pose proof (rw_cells_bound _ _ _ _ HF) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (bytes_at_bound _ _ _ _ HO) as OB.
  change (Z_to_bv 64 (p + Z.of_nat (length out))) with (wa (p + Z.of_nat (length out))).
  assert (L1 : Z.of_nat (length [c]) = 1) by reflexivity.
  split; [|split; [|split; [|split; [|split]]]].
  - apply bytes_at_write_other; [exact HT | lia | try rewrite L1; lia | try rewrite L1; lia].
  - apply wr_at_write. exact HW.
  - apply bytes_at_app. split.
    + apply bytes_at_write_other; [exact HO | lia | try rewrite L1; lia | try rewrite L1; lia].
    + apply bytes_at_write_same; try rewrite L1; lia.
  - apply rw_cells_frame; [exact HF | lia | try rewrite L1; lia | try rewrite L1; lia].
  - apply munch_write; [exact HM | lia | try rewrite L1; lia | cbn [inside]; left; try rewrite L1; lia].
  - apply wmono_write. exact HWM.
Qed.

Lemma rc_skip : forall (d i : nat) x6 x7 x12 m (P : machine_state -> Prop),
  d = (length T - i)%nat -> (i < length T)%nat -> bytes_at rsegs m text T ->
  (forall (j : nat) (y6 y7 : word), (i <= j <= length T)%nat ->
     (forall t b, (i <= t < j)%nat -> nth_error T t = Some b -> is_sep b = true) ->
     (j = length T \/ exists b, nth_error T j = Some b /\ is_sep b = false) ->
     evt rsegs P (rcst (Z_to_bv 64 (Z.of_nat (length T))) y6 y7 x12 (Z_to_bv 64 (Z.of_nat j)) 0x15a04 m)) ->
  evt rsegs P (rcst (Z_to_bv 64 (Z.of_nat (length T))) x6 x7 x12 (Z_to_bv 64 (Z.of_nat i)) 0x159d4 m).
Proof.
  induction d as [|d IH]; intros i x6 x7 x12 m P Hd Hi HB K; [lia|].
  destruct (nth_error T i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  pose proof (read1 m text T i b HB Eb) as RD.
  pose proof (byte_range b) as RB.
  unfold rcst. step. step. nb.
  step. step. step. chk.
  step. nb.
  step. step. rewrite eqb_zxb by lia.
  assert (CONT : forall y7, is_sep b = true ->
    evt rsegs P (MS (mkR r1 spw r3 r4 (Z_to_bv 64 (Z.of_nat (length T))) (zxb b) y7
          (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 text) (Z_to_bv 64 p)
          (Z_to_bv 64 (18446744073709551615 - p)) x12 (Z_to_bv 64 (Z.of_nat i))
          (Z_to_bv 64 (18446744073709551615 - text)) (Z_to_bv 64 1) (Z_to_bv 64 32) (Z_to_bv 64 9)
          r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 0x159f8) fc None m (seg_rom rsegs))).
  { intros y7 Sb. cbv delta [mkR]. step. step. rewrite ltu64 by lia.
    destruct (Z.ltb_spec (Z.of_nat i + 1) (Z.of_nat (length T))) as [Lt|Ge]; cbn [negb].
    - replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
      eapply (IH (S i)); [lia | lia | exact HB |].
      intros j y6 y7' Hj HS Hx. apply K; [lia | | exact Hx].
      intros t c Ht Ec. destruct (Nat.eq_dec t i) as [->|Nt]; [rewrite Eb in Ec; injection Ec as <-; exact Sb|].
      apply (HS t c); [lia | exact Ec].
    - step. apply (K (length T)); [lia | | left; reflexivity].
      intros t c Ht Ec. assert (t = i) by lia. subst t. rewrite Eb in Ec. injection Ec as <-. exact Sb. }
  destruct (Z.eqb_spec (bv_unsigned b) 32) as [E32|N32]; cbn [negb].
  - apply CONT. unfold is_sep. rewrite E32. reflexivity.
  - step. rewrite eqb_zxb by lia.
    destruct (Z.eqb_spec (bv_unsigned b) 9) as [E9|N9]; cbn [negb].
    + apply CONT. unfold is_sep. rewrite E9. apply orb_true_r.
    + apply (K i); [lia | intros t c Ht; lia |].
      right. exists b. split; [exact Eb|]. unfold is_sep.
      apply orb_false_iff. split; apply Z.eqb_neq; assumption.
Qed.

Lemma binv_read : forall m out i b, binv m out -> nth_error T i = Some b ->
  ov_read_bytes rsegs m (wa (text + Z.of_nat i + 0)) 1 = Some [b].
Proof. intros m out i b (HT & _) E. exact (read1 m text T i b HT E). Qed.

Lemma binv_store_ok : forall m out k, binv m out -> 0 <= k <= Z.of_nat (length T) ->
  store_ok rsegs m (wa (p + k)) 1 = true.
Proof. intros m out k (_ & HW & _) Hk. apply (wr_at_store_ok rsegs m p _ k 1 HW); lia. Qed.

Lemma binv_len : forall m out, binv m out -> p + Z.of_nat (length out) <= 2 ^ 64.
Proof. intros m out (_ & _ & HO & _). pose proof (bytes_at_bound _ _ _ _ HO). lia. Qed.

Lemma firstn_snoc_nth : forall (X : list byte) a b, nth_error X a = Some b -> firstn (S a) X = firstn a X ++ [b].
Proof.
  intros X a b E. replace (S a) with (a + 1)%nat by lia. rewrite firstn_add.
  rewrite (skipn_nth X a b E). reflexivity.
Qed.

Lemma rc_copy : forall (d i j : nat) (out0 : list byte) x5 x6 x7 x12 x13 m (P : machine_state -> Prop),
  d = (length T - i)%nat -> (j <= i < length T)%nat -> Z.of_nat (length out0) <= Z.of_nat j ->
  x5 = Z_to_bv 64 (Z.of_nat (length T) + Z.of_nat (length out0) - Z.of_nat j) ->
  x12 = Z_to_bv 64 (Z.of_nat (length out0) + Z.of_nat i - Z.of_nat j) -> x13 = Z_to_bv 64 (Z.of_nat i) ->
  binv m (out0 ++ firstn (i - j) (skipn j T)) ->
  (forall t b, (j <= t < i)%nat -> nth_error T t = Some b -> is_sep b = false) ->
  (forall (k : nat) y5 y6 y7 y12 y13 m', (i <= k < length T)%nat ->
     y12 = Z_to_bv 64 (Z.of_nat (length out0) + Z.of_nat k - Z.of_nat j) -> y13 = Z_to_bv 64 (Z.of_nat k) ->
     (forall t b, (j <= t < k)%nat -> nth_error T t = Some b -> is_sep b = false) ->
     (exists b, nth_error T k = Some b /\ is_sep b = true) ->
     binv m' (out0 ++ firstn (k - j) (skipn j T)) ->
     evt rsegs P (rcst y5 y6 y7 y12 y13 0x159c4 m')) ->
  (forall y5 y6 y7 y12 y13 m',
     y12 = Z_to_bv 64 (Z.of_nat (length T) + Z.of_nat (length out0) - Z.of_nat j) ->
     (forall t b, (j <= t < length T)%nat -> nth_error T t = Some b -> is_sep b = false) ->
     binv m' (out0 ++ skipn j T) ->
     evt rsegs P (rcst y5 y6 y7 y12 y13 0x15a64 m')) ->
  evt rsegs P (rcst x5 x6 x7 x12 x13 0x15a28 m).
Proof.
  induction d as [|d IH]; intros i j out0 x5 x6 x7 x12 x13 m P Hd Hij Ho -> -> -> HB HW KS KE; [lia|].
  destruct (nth_error T i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  pose proof (binv_read m _ i b HB Eb) as RD.
  pose proof (byte_range b) as RB.
  pose proof (binv_len m _ HB) as HL.
  assert (LF : length (firstn (i - j) (skipn j T)) = (i - j)%nat) by (rewrite length_firstn, length_skipn; lia).
  rewrite length_app, LF in HL.
  assert (SEPB : forall y6 y7, is_sep b = true ->
    evt rsegs P (rcst (Z_to_bv 64 (Z.of_nat (length T) + Z.of_nat (length out0) - Z.of_nat j)) y6 y7
       (Z_to_bv 64 (Z.of_nat (length out0) + Z.of_nat i - Z.of_nat j)) (Z_to_bv 64 (Z.of_nat i)) 0x15a58 m)).
  { intros y6 y7 Sb. unfold rcst. step. rewrite ltu64 by lia.
    destruct (Z.ltb_spec (Z.of_nat i) (Z.of_nat (length T))) as [_|C]; [|lia]. cbv iota. cbn [negb].
    apply (KS i); [lia | reflexivity | reflexivity | exact HW | exists b; split; [exact Eb | exact Sb] | exact HB]. }
  unfold rcst. step. nb.
  step. step. step. rewrite eqb_zxb by lia.
  destruct (Z.eqb_spec (bv_unsigned b) 9) as [E9|N9]; cbn [negb].
  { apply SEPB. unfold is_sep. rewrite E9. apply orb_true_r. }
  step. rewrite eqb_zxb by lia.
  destruct (Z.eqb_spec (bv_unsigned b) 32) as [E32|N32]; cbn [negb].
  { apply SEPB. unfold is_sep. rewrite E32. reflexivity. }
  assert (NS : is_sep b = false) by (unfold is_sep; apply orb_false_iff; split; apply Z.eqb_neq; assumption).
  step. nb.
  assert (HS : store_ok rsegs m (wa (p + Z.of_nat (length (out0 ++ firstn (i - j) (skipn j T))))) 1 = true).
  { apply (binv_store_ok m _ _ HB). rewrite length_app, LF. lia. }
  rewrite length_app, LF in HS.
  step. step. step. step. rewrite le1_zxb. unfold wa.
  pose proof (binv_store m _ b (p + Z.of_nat (length out0 + (i - j))) HB
    ltac:(rewrite length_app, LF; reflexivity) ltac:(rewrite length_app, LF; lia)) as HB'.
  rewrite <- app_assoc, <- (firstn_snoc_nth (skipn j T) (i - j) b) in HB'
    by (rewrite nth_error_skipn; replace (j + (i - j))%nat with i by lia; exact Eb).
  set (m' := write_to_mem m _ [b]) in HB' |- *.
  clearbody m'.
  step.
  rewrite eqb64 by lia.
  assert (HW' : forall t c, (j <= t < S i)%nat -> nth_error T t = Some c -> is_sep c = false).
  { intros t c Ht Ec. destruct (Nat.eq_dec t i) as [->|Nt]; [rewrite Eb in Ec; injection Ec as <-; exact NS|].
    apply (HW t c); [lia | exact Ec]. }
  destruct (Z.eqb_spec (Z.of_nat (length T)) (Z.of_nat i + 1)) as [Eq|Ne]; cbn [negb].
  - step. step. apply KE; [reflexivity | |].
    + intros t c Ht Ec. apply (HW' t c); [lia | exact Ec].
    + rewrite firstn_all2 in HB' by (rewrite length_skipn; lia). exact HB'.
  - eapply (IH (S i) j out0); [lia | lia | exact Ho | zeq | zeq | zeq | | exact HW' | | ].
    + replace (S i - j)%nat with (S (i - j)) by lia. exact HB'.
    + intros k y5 y6 y7 y12 y13 m2 Hk E12 E13 HWk Sk HBk.
      apply (KS k); [lia | exact E12 | exact E13 | exact HWk | exact Sk | exact HBk].
    + exact KE.
Qed.

Definition rc_post (ms' : machine_state) : Prop :=
  exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 m',
    ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned spw + 32)) r3 r4 x5 x6 x7 s0v s1v (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17
                  r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (ret_pc rav) fc None m' (seg_rom rsegs) /\
    binv m' (canon T ++ [Z_to_bv 8 0]).

Lemma rc_fin : forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 m,
  x12 = Z_to_bv 64 (p + Z.of_nat (length (canon T))) -> binv m (canon T) ->
  evt rsegs rc_post (MS (mkR r1 spw r3 r4 x5 x6 x7 (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 text) (Z_to_bv 64 p)
      x11 x12 x13 x14 x15 x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 0x15a6c) fc None m (seg_rom rsegs)).
Proof.
  intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 m -> HB.
  pose proof (canon_length T) as CL.
  assert (HS : store_ok rsegs m (wa (p + Z.of_nat (length (canon T)))) 1 = true) by (apply (binv_store_ok m _ _ HB); lia).
  step.
  replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by (vm_compute; reflexivity).
  pose proof (binv_store m _ (Z_to_bv 8 0) (p + Z.of_nat (length (canon T))) HB eq_refl ltac:(lia)) as HB'.
  set (m' := write_to_mem m _ [Z_to_bv 8 0]) in HB' |- *. clearbody m'.
  pose proof HB' as (_ & _ & _ & HF & _).
  step. step. step. step. step.
  apply evt_done. unfold rc_post. do 11 eexists. split; [reflexivity | exact HB'].
Qed.

Lemma rc_fin64 : forall x5 x6 x7 x12 x13 m,
  x12 = Z_to_bv 64 (Z.of_nat (length (canon T))) -> binv m (canon T) ->
  evt rsegs rc_post (rcst x5 x6 x7 x12 x13 0x15a64 m).
Proof.
  intros x5 x6 x7 x12 x13 m -> HB. pose proof (canon_length T) as CL.
  unfold rcst. step. nb. step.
  apply rc_fin; [zeq | exact HB].
Qed.

Lemma canon_step : forall i j k out out0, bndry T i -> (i <= j < k)%nat -> (k <= length T)%nat ->
  (forall t b, (i <= t < j)%nat -> nth_error T t = Some b -> is_sep b = true) ->
  (forall t b, (j <= t < k)%nat -> nth_error T t = Some b -> is_sep b = false) ->
  out = canon (firstn i T) ->
  out0 = match out with [] => [] | _ :: _ => out ++ [SPACE] end ->
  canon (firstn k T) = out0 ++ firstn (k - j) (skipn j T).
Proof.
  intros i j k out out0 HB Hij Hk HS HW Ho Ho0. unfold canon at 1. rewrite (pass_words T i j k) by assumption.
  rewrite canon_snoc. subst out out0.
  destruct (canon (firstn i T)); [reflexivity|]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma rc_outer : forall (d i : nat) x5 x6 x7 x12 x13 m out,
  d = (length T - i)%nat -> (i < length T)%nat -> bndry T i -> out = canon (firstn i T) ->
  x12 = Z_to_bv 64 (Z.of_nat (length out)) -> x13 = Z_to_bv 64 (Z.of_nat i) ->
  binv m out ->
  evt rsegs rc_post (rcst x5 x6 x7 x12 x13 0x159c4 m).
Proof.
  intros d. induction d as [d IH] using (well_founded_induction Wf_nat.lt_wf).
  intros i x5 x6 x7 x12 x13 m out Hd Hi HBd Hout -> -> HB.
  pose proof (canon_length (firstn i T)) as CLi. rewrite length_firstn, <- Hout in CLi.
  assert (SK : forall y6 y7, evt rsegs rc_post (rcst (Z_to_bv 64 (Z.of_nat (length T))) y6 y7
                 (Z_to_bv 64 (Z.of_nat (length out))) (Z_to_bv 64 (Z.of_nat i)) 0x159d4 m)).
  { intros y6 y7. apply (rc_skip (length T - i) i); [reflexivity | exact Hi | exact (proj1 HB) |].
    intros j z6 z7 Hj HS Hx.
    unfold rcst. step. rewrite eqb64 by lia.
    destruct (Z.eqb_spec (Z.of_nat j) (Z.of_nat (length T))) as [Ej|Nj]; cbv iota.
    { assert (CT : canon T = out).
      { rewrite Hout. unfold canon. f_equal. apply (end_words T i HBd); [lia|].
        intros t b Ht Eb. apply (HS t b); [lia | exact Eb]. }
      apply rc_fin64; [rewrite CT; reflexivity | rewrite CT; exact HB]. }
    destruct Hx as [Hx|(bj & Ebj & Sbj)]; [lia|].
    assert (Hjn : (j < length T)%nat) by lia.
    assert (CP : forall out0 y5 y12 m1, out0 = match out with [] => [] | _ :: _ => out ++ [SPACE] end ->
      y12 = Z_to_bv 64 (Z.of_nat (length out0)) -> binv m1 out0 ->
      evt rsegs rc_post (rcst y5 z6 z7 y12 (Z_to_bv 64 (Z.of_nat j)) 0x15a1c m1)).
    { intros out0 y5 y12 m1 Ho0 -> HB1.
      assert (LO : Z.of_nat (length out0) <= Z.of_nat j).
      { destruct out as [|c r] eqn:Eo; subst out0; [cbn; lia|].
        destruct HBd as [-> | (bi & Ebi & Sbi)]; [discriminate Hout|].
        assert (j <> i) by (intros ->; rewrite Ebi in Ebj; injection Ebj as <-; rewrite Sbi in Sbj; discriminate).
        rewrite length_app. cbn [length] in *. lia. }
      unfold rcst. step.
      rewrite ltu64 by lia. destruct (Z.ltb_spec (Z.of_nat j) (Z.of_nat (length T))) as [_|C]; [|lia]. cbv iota. cbn [negb].
      step. step.
      pose proof (binv_len m1 _ HB1) as HL1.
      eapply (rc_copy (length T - j) j j out0); [reflexivity | lia | exact LO | zeq | zeq | zeq | | | |].
      - rewrite Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. exact HB1.
      - intros t b Ht; lia.
      - intros k w5 w6 w7 w12 w13 m2 Hk E12 E13 HWk (bk & Ebk & Sbk) HBk.
        assert (Hkj : (j < k)%nat).
        { destruct (Nat.eq_dec k j) as [->|]; [|lia]. rewrite Ebk in Ebj. injection Ebj as <-.
          rewrite Sbk in Sbj. discriminate. }
        assert (CK : canon (firstn k T) = out0 ++ firstn (k - j) (skipn j T)).
        { apply (canon_step i j k out out0); [exact HBd | lia | lia | exact HS | exact HWk | exact Hout | exact Ho0]. }
        apply (IH (length T - k)%nat ltac:(lia) k w5 w6 w7 w12 w13 m2 (out0 ++ firstn (k - j) (skipn j T)));
          [reflexivity | lia | right; exists bk; split; assumption | symmetry; exact CK | | exact E13 | exact HBk].
        rewrite E12, length_app, length_firstn, length_skipn. f_equal. lia.
      - intros w5 w6 w7 w12 w13 m2 E12 HWe HBe.
        assert (CT : canon T = out0 ++ skipn j T).
        { rewrite <- (firstn_all T) at 1.
          rewrite (canon_step i j (length T) out out0); [| exact HBd | lia | lia | exact HS | exact HWe | exact Hout | exact Ho0].
          f_equal. apply firstn_all2. rewrite length_skipn. lia. }
        apply rc_fin64; [rewrite E12, CT, length_app, length_skipn; f_equal; lia | rewrite CT; exact HBe]. }
    step. rewrite eqb64 by lia.
    destruct (Z.eqb_spec (Z.of_nat (length out)) 0) as [E0|N0]; cbv iota.
    - eapply (CP []); [ | rewrite E0; reflexivity | ].
      + destruct out as [|c r]; [reflexivity | cbn in E0; lia].
      + destruct out as [|c r]; [exact HB | cbn in E0; lia].
    - step. nb.
      assert (HSo : store_ok rsegs m (wa (p + Z.of_nat (length out))) 1 = true) by (apply (binv_store_ok m _ _ HB); lia).
      step. step. step.
      replace (le1 (Z_to_bv 64 32)) with [SPACE] by (vm_compute; reflexivity).
      pose proof (binv_store m out SPACE (p + Z.of_nat (length out)) HB eq_refl ltac:(lia)) as HB'.
      set (m' := write_to_mem m _ [SPACE]) in HB' |- *. clearbody m'.
      eapply (CP (out ++ [SPACE])); [ | rewrite length_app; cbn [length]; f_equal; lia | exact HB'].
      destruct out as [|c r]; [cbn in N0; lia | reflexivity]. }
  unfold rcst. step. step. step.
  rewrite ltu64 by lia. destruct (Z.ltb_spec (Z.of_nat i + 1) (Z.of_nat (length T))) as [Lt|Ge]; cbv iota.
  - exact (SK _ _).
  - step. replace (Z_to_bv 64 (Z.of_nat i + 1)) with (Z_to_bv 64 (Z.of_nat (length T))) by (f_equal; lia).
    exact (SK _ _).
Qed.

Lemma rc_run2 : forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 m, binv m [] ->
  evt rsegs rc_post (MS (mkR r1 spw r3 r4 x5 x6 x7 (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 text) (Z_to_bv 64 p)
      x11 x12 x13 x14 x15 x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 r30 r31) F (Z_to_bv 64 0x159a0) fc None m (seg_rom rsegs)).
Proof.
  intros x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 m HB.
  step. step. rewrite eqb64 by lia.
  destruct (Z.eqb_spec (Z.of_nat (length T)) 0) as [E0|N0]; cbv iota.
  - assert (TN : T = []) by (destruct T; [reflexivity | cbn in E0; lia]).
    apply rc_fin; [rewrite TN; replace (Z.of_nat (length (canon []))) with 0 by reflexivity; zeq | rewrite TN; exact HB].
  - do 7 step.
    rcfix.
    apply (rc_outer (length T - 0) 0 _ _ _ _ _ m []); [reflexivity | lia | left; reflexivity | reflexivity | reflexivity | reflexivity | exact HB].
Qed.

End Loops.

Definition rc_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (text : Z) (T : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR (Z_to_bv 64 0x159a0) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2
                  (Z_to_bv 64 (Z.of_nat (length T))) (Z_to_bv 64 text) a0 a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x15a88) fc None m' (seg_rom rsegs)
    /\ a0 = Z_to_bv 64 (Z.of_nat (length T) + 1)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp - 32)%Z [CB 8 junk; C8 s1; C8 s0; C8 ra]
    /\ bytes_at rsegs m' text T.

Lemma rc_run1 : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (text lo : Z) (T : list byte),
  bytes_at rsegs m text T ->
  (Z.of_nat (length T) <= 8192)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z ->
  (text + Z.of_nat (length T) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= text)%Z ->
  mem_inv rsegs m ->
  evt rsegs (rc_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc text T m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 text) (Z_to_bv 64 (Z.of_nat (length T))) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15980) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m text lo T BS LMX ST LO DISJ MI.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 8 step.
  apply evt_done. unfold rc_mid.
  do 17 eexists. split; [reflexivity|].
  split.
  { apply bv_eq. rewrite ?Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
    rewrite ?Zmod_0_l, ?Z.add_0_r, ?Zmod_mod. first [reflexivity | f_equal; lia]. }
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB xmalloc_c rec_canonical_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Local Open Scope Z_scope.

Section X.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis XM : xmalloc_contract B API.

Theorem rec_canonical_holds : rec_canonical_contract B API.
Proof using SEGS ERRNO_LOW GOTG XM.
  unfold rec_canonical_contract, rec_canonical_ret.
  intros L A regs mem md text T b PRE A0 A1 SRC TNZ NONUL LMX DISJ HOME RES ROOM RA.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  pose proof XM as XMC. unfold xmalloc_contract in XMC. rewrite SEGS in XMC.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold REC_CANONICAL_K, XMALLOC_K, XMALLOC, REC_CANONICAL, LMAX in *. change ALLOC_STACK with 8192 in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (Nat2Z.is_nonneg (length T)) as L0.
  set (l := Z.of_nat (length T)) in *.
  assert (XS : xmalloc_size (l + 1) = l + 1) by (unfold xmalloc_size; destruct (Z.eqb_spec (l + 1) 0); lia).
  rewrite SEGS in RA, HWS, HERR, SRC.
  rename SRC into BS.
  pose proof (bytes_at_bound _ _ _ _ BS) as SB.
  pose proof (bytes_at_normalize rsegs mem text _ RA BS) as BSN.
  assert (ST : stk rsegs (normalize rsegs mem) (bv_unsigned sp - 8240) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E].
    assert (NE : normalize rsegs mem (wa a) = mem (wa a)) by (apply normalize_rw; unfold wa; apply ro_addr_hi; lia).
    unfold wview, mrd. rewrite NE. unfold wa. rewrite E. split; [discriminate | exists bb; reflexivity]. }
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 text) by exact A0.
    assert (R11 : reg_get regs 11 = Z_to_bv 64 l) by exact A1.
    rewrite R10, R11.
    eapply (evt_normalize rsegs); [exact WX | exact RA |].
    eapply rc_run1; [exact BSN | exact LMX | exact ST | lia | lia | apply mem_inv_normalize]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1n & junk
    & -> & -> & MU1n & WM1n & MI1n & FR1n & BS1n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same rsegs _ _ RA RO1) as RA1.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR1r FR1n) as FR1.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR1r) BS1n) as BS1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x159a0) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 l) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_9 : getr R1 9 = Z_to_bv 64 text) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (l + 1)) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 32 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 32, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  eapply SR_bind.
  { eapply (XMC L A R1 m1 md (l + 1) b); [ | exact E1_10 | lia | exact RES | rewrite XS; exact ROOM | exact RA1].
    split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
    split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP1; replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP1; lia|].
    split; [rewrite SP1; lia|].
    split; [intros a Ha; rewrite SP1 in Ha; rewrite SEGS; apply WM1; apply HWS; lia|].
    split; [rewrite E1_4; exact HTP|].
    split; [intros a Ha; rewrite SEGS; apply WM1; apply HERR; exact Ha|].
    intros HI. specialize (HAUX HI). rewrite SP1.
    destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
    exists av, ar.
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk.
      assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
      destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | apply OUT1; lia]. }
    split.
    { intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
      split; [lia | apply OUT1; lia]. }
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia | apply OUT1; lia]. }
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia | apply OUT1; lia]. }
    lia. }
  intros c2 RET.
  destruct RET as (L' & A' & R2 & m2 & md2 & d & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & RA2 & GK2 & UB2
    & INIT & REG2 & RES').
  rewrite XS in *.
  try rewrite SEGS in RA2.
  destruct POST as (HMR' & HWF' & HBD' & HLE & HSTAB & HPRES & HVM & HFRAME & HBLKS & HSCR).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh2 & Hl2 & Hmat2).
  destruct BLK as (b1 & b2 & BLK1 & BLK2).
  pose proof FRESH as (FR_lo & FR_hi & FR_img).
  unfold str_home in HOME. rewrite SEGS in HOME.
  assert (INB : In (d, l + 1) (blocks L' A')) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
  assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho;
      [destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho) | destruct (owned_low B _ LAWS _ _ _ _ _ HMR' Ho)]; lia. }
  assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8240 <= a < bv_unsigned sp - 32) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs. destruct (NOWN a (proj1 Ha)) as [N1 N2].
    apply HFRAME; [left; exact Ha | exact N1 | exact N2 | | intros F; exact F].
    unfold scratch_k. rewrite SP1. intros [H|H]; lia. }
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
    by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 l) by exact (eq_trans (HPRES 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 text) by exact (eq_trans (HPRES 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 d) by exact A0'.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32)
                  [CB 8 junk; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    rewrite <- SEGS. destruct (HI2 (bv_unsigned sp - 32 + i) ltac:(lia) ltac:(lia)) as [E W].
    split; [exact E | apply W]. }
  assert (KEEP : forall i, 0 <= i < l -> mbyte rsegs m2 (text + i) = mbyte rsegs m1 (text + i)).
  { intros i Hi. destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - rewrite <- SEGS. exact (proj1 (HI2 (text + i) ltac:(lia) ltac:(lia))).
    - pose proof (KEPT q k (text + i - q) Hq (fun F => F) ltac:(lia)) as E.
      replace (q + (text + i - q)) with (text + i) in E by ring. rewrite <- SEGS. exact E.
    - rewrite (mbyte_ro_agree _ _ _ RA2 (H3 i Hi)), (mbyte_ro_agree _ _ _ RA1 (H3 i Hi)). reflexivity. }
  assert (SRC2 : bytes_at rsegs m2 text T).
  { apply (bytes_at_transfer rsegs m1); [exact BS1|]. intros i Hi. apply KEEP. lia. }
  destruct (present_rw_cells rsegs (normalize rsegs m2) d (S (length T))) as [junk2 DST2]; [lia | lia | |].
  { intros i Hi. destruct (proj1 (block_facts B _ LAWS _ _ _ _ _ _ i HMR' INB ltac:(lia))) as [bb E].
    exists bb. rewrite normalize_rw; [exact E|]. apply (ro_addr_out B SEGS); [lia | apply FR_img; lia]. }
  assert (SEP2 : text + l <= d \/ d + l + 1 <= text).
  { destruct HOME as [(H1 & H2) | [(q & k & Hq & H1 & H2) | (H1 & H2 & H3)]].
    - right. lia.
    - rewrite BLK2 in Hq. pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 Hq) as Dj. lia.
    - destruct (Z_le_gt_dec (text + l) d) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec (d + l + 1) text) as [D'|D']; [right; exact D'|]. exfalso.
      apply (FR_img (Z.max text d - d)); [lia|].
      replace (d + (Z.max text d - d)) with (text + (Z.max text d - text)) by lia.
      apply (ro_in_img B SEGS); [lia | apply H3; lia]. }
  assert (FR2n : rw_cells rsegs (normalize rsegs m2) (bv_unsigned sp - 32)
                   [CB 8 junk; C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply rw_cells_normalize; [exact RA2 | exact FR2 |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  pose proof (bytes_at_normalize rsegs m2 text _ RA2 SRC2) as SRC2n.
  assert (USPW : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 32)) = bv_unsigned sp - 32) by (apply unsigned_lit; lia).
  assert (HB0 : binv (Z_to_bv 64 (bv_unsigned sp - 32)) text d T (normalize rsegs m2) junk
                  (reg_get regs 9) (reg_get regs 8) (reg_get regs 1) (normalize rsegs m2) []).
  { split; [exact SRC2n|]. split.
    { destruct DST2 as [_ HW]. destruct HW as (HW1 & HW2 & HW3). split; [lia|]. split; [lia|].
      intros i Hi. apply HW3. cbn [cells_size csize]. lia. }
    split; [apply bytes_at_nil; lia|]. split; [rewrite USPW; exact FR2n|].
    split; [apply munch_refl | apply wmono_refl]. }
  rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2_2, E2_8, E2_9, E2_10, SEGS.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply rc_run2; [lia | lia | lia | rewrite USPW; lia | exact LMX | exact HB0]. }

  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3). unfold rc_post in Q3.
  destruct Q3 as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & m3n & -> & HB3).
  destruct HB3 as (TX3n & WR3n & DST3n & FR3n & MU3n & WM3n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 MU3n) as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 WM3n) as WM3.
  pose proof (ro_agree_same rsegs _ _ RA2 RO3) as RA3.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR3r) DST3n) as DST3.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ MR3r) TX3n) as SRC3.
  pose proof (wr_at_rel rsegs _ _ _ _ MR3r WR3n) as WR3.
  rewrite USPW in EQ3.
  replace (Z_to_bv 64 (bv_unsigned sp - 32 + 32)) with sp in EQ3
    by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RP.
  assert (OUT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + l + 1) -> outside [(d, d + l + 1)] a)
    by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR3 : aa_MR API L' A' m3 md2).
  { eapply (mr_frame B _ LAWS L' A' m2 m3 md2 md2 HMR').
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR' Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU3 | lia | apply OUT3; [lia|]]. intros Hin.
      apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - d) HMR' INB ltac:(lia))))).
      replace (d + (a - d)) with a by ring. exact Ho.
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR' Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU3 | lia | apply OUT3; [lia|] | exact Hp]. intros Hin.
      apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - d) HMR' INB ltac:(lia))))).
      replace (d + (a - d)) with a by ring. exact Ho.
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L' A' m2 md2 p n i HMR' Hin Hi) as (Hp & H4 & Hc & _).
      destruct (Z_le_gt_dec d (ptr_addr L' p + i)) as [D1|D1];
        [destruct (Z_lt_ge_dec (ptr_addr L' p + i) (d + l + 1)) as [D2|D2]|].
      + apply (present_of_writable_out B SEGS m3 (ptr_addr L' p + i) ltac:(lia)).
        * replace (ptr_addr L' p + i) with (d + (ptr_addr L' p + i - d)) by ring. apply FR_img. lia.
        * pose proof WR3 as (_ & _ & W).
          specialize (W (ptr_addr L' p + i - d) ltac:(lia)).
          replace (d + (ptr_addr L' p + i - d)) with (ptr_addr L' p + i) in W by ring. exact W.
      + eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
      + eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
    - reflexivity.
    - exact Hh2.
    - exact Hl2.
    - exact Hmat2. }
  apply SR_ret.
  exists L', A', R3, m3, md2, d.
  split; [reflexivity|].
  split.
  { split; [exact MR3|]. split; [exact HWF'|]. split; [exact HBD'|]. split; [exact HLE|]. split; [exact HSTAB|].
    split.
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9)) regs R1 R2 R3 _ _ X1 HPRES X3).
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; reflexivity]|]).
        subst r. split; reflexivity.
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
        subst r. discriminate O. }
    split; [exact HVM|].
    split.
    { intros a HA NO1 NO2 NS NE. cbn beta in NE.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct HA as [HA|HA]; [lia | pose proof (in_img_low B SEGS a HA); lia]).
      assert (NSP : ~ (bv_unsigned sp - 8240 <= a < bv_unsigned sp)).
      { intro H. apply NS. left. unfold spZ. change (getr regs 2) with sp. lia. }
      assert (NER : ~ (errno_addr B <= a < errno_addr B + 4)) by (intro H; apply NS; right; exact H).
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as E01.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU1 AR (OUT1 a AR ltac:(lia))) as W01.
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFRAME; [exact HA | exact NO1 | exact NO2 | | intros F; exact F].
        unfold scratch_k. rewrite SP1. intros [H|H]; [lia | exact (NER H)]. }
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU3 AR (OUT3 a AR ltac:(lia))) as E23.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU3 AR (OUT3 a AR ltac:(lia))) as W23.
      split; [rewrite E23, (proj1 H12), E01; reflexivity | rewrite W01, (proj2 H12), W23; tauto]. }
    split.
    { intros p n i Hin Hin' Hi.
      destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
      assert (INA : In (ptr_addr L p, n) (b1 ++ b2)).
      { rewrite <- BLK2. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hin). }
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 INA) as Dj.
      rewrite (munch_mbyte _ _ _ _ (ptr_addr L p + i) MU3 ltac:(lia) (OUT3 (ptr_addr L p + i) ltac:(lia) ltac:(lia))).
      rewrite (HBLKS p n i Hin Hin' Hi).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    rewrite SEGS. apply WM3. rewrite <- SEGS.
    destruct Ha as [Ha|Ha].
    - destruct (Z_lt_ge_dec a (bv_unsigned sp - 32)) as [D|D].
      + apply HSCR. unfold scratch_k. rewrite SP1. left. lia.
      + destruct (NOWN a ltac:(lia)) as [N1 N2].
        apply (proj1 (proj2 (HFRAME a ltac:(left; lia) N1 N2 ltac:(unfold scratch_k; rewrite SP1;
                 intros [H|H]; lia) (fun F => F)))).
        rewrite SEGS. apply WM1. apply HWS. lia.
    - apply HSCR. right. exact Ha. }
  split; [rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity|].
  split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|].
  split; [exists b1, b2; split; [exact BLK1 | exact BLK2]|].
  split.
  { intros q k i Hq _ Hi.
    destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hq Hi) as (_ & Hlo & Hhi & _).
    assert (Hq' : In (q, k) (b1 ++ b2)) by (rewrite <- BLK2; exact Hq).
    pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR' BLK1 Hq') as Dj.
    rewrite (munch_mbyte _ _ _ _ (q + i) MU3 ltac:(lia) (OUT3 (q + i) ltac:(lia) ltac:(lia))).
    rewrite (KEPT q k i Hq (fun F => F) Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact UB2|].
  split; [exact DST3|].
  split; [exact SRC3|].
  split; [exact RA3|].
  split.
  { intros i Hi. rewrite GOTG.
    assert (IMG : in_img B (0x22d40 + i)).
    { apply (in_img_found B SEGS); [lia|].
      assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
      repeat (destruct C as [C|C]; [subst i; intro F; vm_compute in F; discriminate F|]).
      subst i. intro F. vm_compute in F. discriminate F. }
    rewrite SEGS.
    rewrite (munch_mbyte _ _ _ _ (0x22d40 + i) MU3 ltac:(lia)).
    2: { apply OUT3; [lia|]. intros Hin. apply (FR_img (0x22d40 + i - d)); [lia|].
         replace (d + (0x22d40 + i - d)) with (0x22d40 + i) by ring. exact IMG. }
    pose proof (GK2 i Hi) as G. rewrite GOTG, SEGS in G. rewrite G.
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact INIT|]. split; [exact REG2|]. exact RES'.
Qed.

End X.
