(* The count half of LS v3, part 1: the list lemmas of the counts and their bridge to the allocator's counts
   (design: B1c's count design note, COUNTS-DESIGN in a Theorem Labs lane's B1c claim; a Theorem Labs lane's check 00:23Z).
   The counts themselves (Psec, cnt_sec, cnt_cls, cnt24) have ONE definition, in ReplyCnt.v; this file proves the
   lemmas LS uses over them, and the event weights w_sec / w_cls with the cnt_after lemmas (the counts of a block
   list move by the weight of each allocator event exactly).
   A Theorem Labs lane's counts (cfdriver Reusable/YGcfRoomLive.v at 46f1762ad5a / a working branch 8071b92028b):
     sec_cnt S := length (filter rl_sec_req (map snd (blocks S))), rl_sec_req n := negb (PresetRoom.is_primary n)
       (:1172-1173), which is ReplyCnt.Psec;
     ccnt24 S := PresetRoom.ccnt kBatchClass (map snd (blocks S)) (:1145);
     the per-class primary counts ccnt_c c S (rl_prim_ok, a Theorem Labs lane 00:28Z) := PresetRoom.ccnt c (map snd (blocks S)).
   All three read only map snd (blocks S), and ablocks B ly S = map (fun b => (addr, snd b)) (blocks S)
   (Reusable/YG0d.v:433), so each is the same count of LS's block list (ablocks_snd).  PresetRoom is this tree's
   lib/Spec/PresetRoom.v (the allocator class map). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt ReplyTrPeakW.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================== the counts' list lemmas *)
Lemma cnt_sec_app : forall l1 l2, cnt_sec (l1 ++ l2) = cnt_sec l1 + cnt_sec l2.
Proof. intros. unfold cnt_sec. rewrite acnt_app. lia. Qed.
Lemma cnt_cls_app : forall c l1 l2, cnt_cls c (l1 ++ l2) = cnt_cls c l1 + cnt_cls c l2.
Proof. intros. unfold cnt_cls. rewrite acnt_app. lia. Qed.
Lemma perm_filter_l {A : Type} (f : A -> bool) : forall l l', Permutation l l' ->
  Permutation (List.filter f l) (List.filter f l').
Proof.
  intros l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn [List.filter].
  - constructor.
  - destruct (f x); [apply perm_skip|]; exact IH.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - exact (perm_trans IH1 IH2).
Qed.
Lemma cnt_sec_perm : forall l l', Permutation l l' -> cnt_sec l = cnt_sec l'.
Proof. intros l l' H. unfold cnt_sec. rewrite (acnt_perm _ _ _ H). reflexivity. Qed.
Lemma cnt_cls_perm : forall c l l', Permutation l l' -> cnt_cls c l = cnt_cls c l'.
Proof. intros c l l' H. unfold cnt_cls. rewrite (acnt_perm _ _ _ H). reflexivity. Qed.
Lemma cnt_sec_nonneg : forall l, 0 <= cnt_sec l.
Proof. intros. unfold cnt_sec. lia. Qed.
Lemma cnt_cls_nonneg : forall c l, 0 <= cnt_cls c l.
Proof. intros. unfold cnt_cls. lia. Qed.
Lemma cnt_sec_cons : forall a n l, cnt_sec ((a, n) :: l) = (if Psec n then 1 else 0) + cnt_sec l.
Proof. intros. unfold cnt_sec, acnt. cbn [map List.filter snd]. destruct (Psec n); cbn [length]; lia. Qed.
Lemma cnt_cls_cons : forall c a n l, cnt_cls c ((a, n) :: l) = (if PresetRoom.in_cls c n then 1 else 0) + cnt_cls c l.
Proof.
  intros. unfold cnt_cls, acnt, Pcls. cbn [map List.filter snd].
  destruct (PresetRoom.in_cls c n); cbn [length]; lia.
Qed.
Lemma cnt_sec_nil : cnt_sec [] = 0.
Proof. reflexivity. Qed.
Lemma cnt_cls_nil : forall c, cnt_cls c [] = 0.
Proof. reflexivity. Qed.

(* ================================================================== the bridge to the allocator's counts *)
Section bridge.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma ablocks_snd : forall ly S, map snd (ablocks B ly S) = map snd (blocks S).
Proof. intros ly S. unfold ablocks. rewrite map_map. cbn. reflexivity. Qed.
(* a Theorem Labs lane's sec_cnt / ccnt24 / ccnt_c, unfolded at their definitions, are these counts of ablocks *)
Lemma sec_cnt_bridge : forall ly S,
  Z.of_nat (length (List.filter Psec (map snd (blocks S)))) = cnt_sec (ablocks B ly S).
Proof. intros. unfold cnt_sec, acnt. rewrite ablocks_snd. reflexivity. Qed.
Lemma ccnt_bridge : forall c ly S, Z.of_nat (PresetRoom.ccnt c (map snd (blocks S))) = cnt_cls c (ablocks B ly S).
Proof. intros. rewrite cnt_cls_ccnt, ablocks_snd. reflexivity. Qed.
End bridge.

(* ================================================================== which sizes are secondary *)
(* a request is secondary exactly when it is at least 64,513 bytes (needed0 > 64 KiB) *)
Lemma is_sec_iff : forall n, 0 <= n -> Psec n = (64513 <=? n).
Proof.
  intros n Hn. unfold Psec, PresetRoom.is_primary, PresetRoom.needed0, PresetRoom.rounded_size, PresetRoom.rup,
    PresetRoom.rz_size, PresetRoom.rz_log, PresetRoom.K_MAX_SIZE.
  assert (R : forall x, 0 <= x -> x <= (x + 8 - 1) / 8 * 8 <= x + 7).
  { intros x Hx. pose proof (Z.div_mod (x + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 8 - 1) 8 ltac:(lia)).
    lia. }
  pose proof (R (Z.max n 8) ltac:(lia)) as Hr.
  destruct (Z.leb_spec n 48); [rewrite (Z.shiftl_mul_pow2 16 0) by lia|];
  repeat match goal with
  | |- context [if ?x <=? ?y then _ else _] => destruct (Z.leb_spec x y)
  end; cbn [Z.shiftl Z.pow Z.pow_pos]; try rewrite Z.shiftl_mul_pow2 by lia;
  cbn [Z.pow Z.pow_pos Pos.iter Z.mul];
  repeat match goal with
  | |- context [?x <=? ?y] => destruct (Z.leb_spec x y)
  end; cbn [negb]; try reflexivity; lia.
Qed.

(* ================================================================== the event weights *)
Definition w_sec (n : Z) : Z := if Psec n then 1 else 0.
Definition w_cls (c : Z) (n : Z) : Z := if PresetRoom.in_cls c n then 1 else 0.

(* the counts move by the events' weights exactly (W_journal.v posts: malloc :790, free :812, realloc0 :863,
   realloc :864, free(NULL) :833) *)
Section moves.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma cnt_sec_snoc : forall l a n, cnt_sec (l ++ [(a, n)]) = cnt_sec l + w_sec n.
Proof. intros. rewrite cnt_sec_app, cnt_sec_cons, cnt_sec_nil. unfold w_sec. lia. Qed.
Lemma cnt_cls_snoc : forall c l a n, cnt_cls c (l ++ [(a, n)]) = cnt_cls c l + w_cls c n.
Proof. intros. rewrite cnt_cls_app, cnt_cls_cons, cnt_cls_nil. unfold w_cls. lia. Qed.
Lemma cnt_after_malloc : forall ly S ly2 S2 res n,
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n)] ->
  cnt_sec (ablocks B ly2 S2) = cnt_sec (ablocks B ly S) + w_sec n /\
  forall c, cnt_cls c (ablocks B ly2 S2) = cnt_cls c (ablocks B ly S) + w_cls c n.
Proof. intros ly S ly2 S2 res n E. rewrite E. split; [apply cnt_sec_snoc | intros c; apply cnt_cls_snoc]. Qed.
Lemma cnt_after_free : forall ly S ly2 S2 pa n,
  (exists l1 l2, ablocks B ly S = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) ->
  cnt_sec (ablocks B ly2 S2) = cnt_sec (ablocks B ly S) - w_sec n /\
  forall c, cnt_cls c (ablocks B ly2 S2) = cnt_cls c (ablocks B ly S) - w_cls c n.
Proof.
  intros ly S ly2 S2 pa n (l1 & l2 & E1 & E2). rewrite E1, E2. unfold w_sec, w_cls.
  split; [rewrite !cnt_sec_app, cnt_sec_cons; lia | intros c; rewrite !cnt_cls_app, cnt_cls_cons; lia].
Qed.
Lemma cnt_after_realloc0 : forall ly S ly2 S2 res n,
  Permutation (ablocks B ly2 S2) ((res, n) :: ablocks B ly S) ->
  cnt_sec (ablocks B ly2 S2) = cnt_sec (ablocks B ly S) + w_sec n /\
  forall c, cnt_cls c (ablocks B ly2 S2) = cnt_cls c (ablocks B ly S) + w_cls c n.
Proof.
  intros ly S ly2 S2 res n HP. unfold w_sec, w_cls.
  split; [rewrite (cnt_sec_perm _ _ HP), cnt_sec_cons; lia | intros c; rewrite (cnt_cls_perm _ _ _ HP), cnt_cls_cons; lia].
Qed.
Lemma cnt_after_realloc : forall ly S ly2 S2 p n0 res n,
  (exists l1 l2, ablocks B ly S = l1 ++ (p, n0) :: l2 /\ Permutation (ablocks B ly2 S2) ((res, n) :: l1 ++ l2)) ->
  cnt_sec (ablocks B ly2 S2) = cnt_sec (ablocks B ly S) - w_sec n0 + w_sec n /\
  forall c, cnt_cls c (ablocks B ly2 S2) = cnt_cls c (ablocks B ly S) - w_cls c n0 + w_cls c n.
Proof.
  intros ly S ly2 S2 p n0 res n (l1 & l2 & E1 & HP). rewrite E1. unfold w_sec, w_cls.
  split; [rewrite (cnt_sec_perm _ _ HP), cnt_sec_cons, !cnt_sec_app, cnt_sec_cons; lia
         | intros c; rewrite (cnt_cls_perm _ _ _ HP), cnt_cls_cons, !cnt_cls_app, cnt_cls_cons; lia].
Qed.
Lemma cnt_after_free_null : forall ly S ly2 S2,
  Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  cnt_sec (ablocks B ly2 S2) = cnt_sec (ablocks B ly S) /\
  forall c, cnt_cls c (ablocks B ly2 S2) = cnt_cls c (ablocks B ly S).
Proof. intros ly S ly2 S2 HP. split; [apply cnt_sec_perm | intros c; apply cnt_cls_perm]; exact HP. Qed.
End moves.
