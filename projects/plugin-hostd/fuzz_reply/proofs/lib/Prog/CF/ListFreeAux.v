From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayFrame HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lf_ndf : forall {X Y} (l : list (X * Y)) x a b, List.NoDup (map fst l) -> In (x, a) l -> In (x, b) l -> a = b.
Proof.
  intros X Y l x a b ND. induction l as [|[y c] l IH]; intros Ha Hb; [destruct Ha|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND as [Hy ND].
  destruct Ha as [Ea|Ha]; destruct Hb as [Eb|Hb].
  - inversion Ea; inversion Eb; subst; reflexivity.
  - inversion Ea; subst. exfalso. apply Hy. exact (in_map fst _ _ Hb).
  - inversion Eb; subst. exfalso. apply Hy. exact (in_map fst _ _ Ha).
  - exact (IH ND Ha Hb).
Qed.

Lemma lf_nz : forall r, callee_saved r -> bv_eqb (Z_to_bv 5 r) 0 = false.
Proof.
  intros r Hr. unfold callee_saved in Hr. unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia.
Qed.

Lemma lf_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs (Z_to_bv 5 1)) (getr regs (Z_to_bv 5 2)) (getr regs (Z_to_bv 5 3)) (getr regs (Z_to_bv 5 4))
      (getr regs (Z_to_bv 5 5)) (getr regs (Z_to_bv 5 6)) (getr regs (Z_to_bv 5 7)) (getr regs (Z_to_bv 5 8))
      (getr regs (Z_to_bv 5 9)) (getr regs (Z_to_bv 5 10)) (getr regs (Z_to_bv 5 11)) (getr regs (Z_to_bv 5 12))
      (getr regs (Z_to_bv 5 13)) (getr regs (Z_to_bv 5 14)) (getr regs (Z_to_bv 5 15)) (getr regs (Z_to_bv 5 16))
      (getr regs (Z_to_bv 5 17)) (getr regs (Z_to_bv 5 18)) (getr regs (Z_to_bv 5 19)) (getr regs (Z_to_bv 5 20))
      (getr regs (Z_to_bv 5 21)) (getr regs (Z_to_bv 5 22)) (getr regs (Z_to_bv 5 23)) (getr regs (Z_to_bv 5 24))
      (getr regs (Z_to_bv 5 25)) (getr regs (Z_to_bv 5 26)) (getr regs (Z_to_bv 5 27)) (getr regs (Z_to_bv 5 28))
      (getr regs (Z_to_bv 5 29)) (getr regs (Z_to_bv 5 30)) (getr regs (Z_to_bv 5 31)).
Proof. reflexivity. Qed.

Lemma lf_get : forall R R' (r : bv 5) v, Regs6ss.xregs_eqv R R' -> bv_eqb r 0 = false -> Sem.reg_get R r = v ->
  getr R' r = v.
Proof. intros R R' r v X NZ E. unfold getr. rewrite NZ. rewrite <- E. symmetry. apply X. exact NZ. Qed.

Lemma lf_ok4 : YK0s.ret_ok (Z_to_bv 64 0x14ba4).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma lf_ok8 : YK0s.ret_ok (Z_to_bv 64 0x14bd8).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma lf_skipn_cons : forall {X} (l : list X) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] d H; cbn in *; [lia | lia | reflexivity | apply IH; lia]. Qed.

Lemma lf_split_nth : forall {X} (l : list X) k d, (k < length l)%nat -> l = firstn k l ++ nth k l d :: skipn (S k) l.
Proof. intros X l k d H. rewrite <- (lf_skipn_cons l k d H). symmetry. apply firstn_skipn. Qed.

Lemma lf_firstn_S : forall {X} (l : list X) k x, In x (firstn k l) -> In x (firstn (S k) l).
Proof.
  induction l as [|y l IH]; intros [|k] x H; cbn in *;
    [destruct H | destruct H | destruct H | destruct H as [H|H]; [left; exact H | right; apply IH; exact H]].
Qed.

Lemma lf_nth_firstn : forall {X} (l : list X) k d, (k < length l)%nat -> In (nth k l d) (firstn (S k) l).
Proof.
  induction l as [|y l IH]; intros [|k] d H; cbn in *; [lia | lia | left; reflexivity | right; apply IH; lia].
Qed.

Lemma lf_in_mid : forall {X} (b1 b2 : list X) x y, In y (b1 ++ x :: b2) -> y <> x -> In y (b1 ++ b2).
Proof.
  intros X b1 b2 x y H Ne. apply in_app_or in H. apply in_or_app.
  destruct H as [H|[H|H]]; [left; exact H | congruence | right; exact H].
Qed.

Lemma lf_in_mid2 : forall {X} (b1 b2 : list X) x y, In y (b1 ++ b2) -> In y (b1 ++ x :: b2).
Proof.
  intros X b1 b2 x y H. apply in_app_or in H. apply in_or_app.
  destruct H as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma lf_nd_mid : forall (b1 b2 : list (Z * Z)) q n q' n', List.NoDup (map fst (b1 ++ (q, n) :: b2)) ->
  In (q', n') (b1 ++ b2) -> q' <> q.
Proof.
  intros b1 b2 q n q' n' ND H E. subst q'. rewrite map_app in ND. cbn [map fst] in ND.
  apply List.NoDup_remove_2 in ND. apply ND. rewrite <- map_app. exact (in_map fst _ (q, n') H).
Qed.

Lemma lf_fst_ne : forall (recs : list (Z * list byte)) k r', (k < length recs)%nat -> List.NoDup (map fst recs) ->
  In r' (firstn k recs) -> fst r' <> fst (nth k recs (0, [])).
Proof.
  intros recs k r' Hk ND H E. rewrite (lf_split_nth recs k (0, []) Hk) in ND. rewrite map_app in ND. cbn [map] in ND.
  apply List.NoDup_remove_2 in ND. apply ND. apply in_or_app. left. rewrite <- E. apply in_map. exact H.
Qed.

Lemma lf_text_rec : forall r, text_rec r = le8 (Z_to_bv 64 (fst r)) ++ le8 (Z_to_bv 64 (Z.of_nat (length (snd r)))).
Proof. reflexivity. Qed.

Lemma lf_text_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. rewrite lf_text_rec, length_app, !length_le8. reflexivity. Qed.

Lemma lf_texts_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, lf_text_len, IH. lia.
Qed.

Lemma lf_sub : forall sg m a n (X Y : list byte) c, rw_cells sg m a [CB n (X ++ cbytes c ++ Y)] -> cell_wf c ->
  rw_cells sg m (a + Z.of_nat (length X)) [c].
Proof.
  intros sg m a n X Y c H Wc.
  assert (H2 : rw_cells sg m a ([CB (length X) X] ++ [c; CB (length Y) Y])).
  { apply (rw_cells_retype sg m a _ _ H).
    - cbn [app cells_wf cell_wf]. split; [reflexivity|]. split; [exact Wc|]. split; [reflexivity | exact I].
    - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. reflexivity. }
  destruct (hg_cut sg m a _ _ H2) as [_ H3]. cbn [cells_size csize] in H3. rewrite Nat.add_0_r in H3.
  exact (proj1 (hg_cut sg m _ [c] [CB (length Y) Y] H3)).
Qed.

Lemma lf_slot : forall sg m V n recs junk j, (j < length recs)%nat ->
  rw_cells sg m V [CB n (concat (map text_rec recs) ++ junk)] ->
  rw_cells sg m (V + 16 * Z.of_nat j) [C8 (Z_to_bv 64 (fst (nth j recs (0, []))))].
Proof.
  intros sg m V n recs junk j Hj H.
  assert (E : concat (map text_rec recs) ++ junk =
      concat (map text_rec (firstn j recs)) ++ cbytes (C8 (Z_to_bv 64 (fst (nth j recs (0, []))))) ++
      (le8 (Z_to_bv 64 (Z.of_nat (length (snd (nth j recs (0, [])))))) ++
       concat (map text_rec (skipn (S j) recs)) ++ junk)).
  { rewrite (lf_split_nth recs j (0, []) Hj) at 1. rewrite map_app, concat_app. cbn [map concat cbytes].
    rewrite (lf_text_rec (nth j recs (0, []))). rewrite <- !app_assoc. reflexivity. }
  rewrite E in H.
  pose proof (lf_sub sg m V n _ _ _ H I) as H2.
  rewrite lf_texts_len, firstn_length_le in H2 by lia.
  replace (V + Z.of_nat (16 * j)) with (V + 16 * Z.of_nat j) in H2 by lia. exact H2.
Qed.

Lemma lf_u8 : forall sg m a n bs, rw_cells sg m a [CB n bs] -> u8arr sg m a bs.
Proof.
  intros sg m a n bs [[[Wf _] Bt] Wr]. cbn [cells_bytes cbytes cells_size csize cell_wf] in Wf, Bt, Wr.
  rewrite app_nil_r in Bt. rewrite Nat.add_0_r in Wr. split; [exact Bt|]. rewrite Wf. exact Wr.
Qed.

Lemma lf_cb_len : forall sg m a n bs, rw_cells sg m a [CB n bs] -> length bs = n.
Proof. intros sg m a n bs [[[Wf _] _] _]. exact Wf. Qed.
