(* The count names of the ROOM round, one definition each (a Theorem Labs lane 02:00Z: defined here, taken by pin by W8Entry-2's
   AddX; names exactly as ROOM-TEXTS (0.3) and (c) use them).  Definitions and the generic list lemmas ROOM-TEXTS (0.3)
   asks for beside acnt; no spec is proved here.
   - acnt P l: the number of blocks of l whose size satisfies P (ROOM-TEXTS (0.3) :51, nat).
   - The top_x instance of the count Variables (ROOM-TEXTS :65-66): Psec (secondary: needed0 n > 64 KiB, i.e. n >= 64,513;
     a Theorem Labs lane's rl_sec_req n := negb (PresetRoom.is_primary n)), Pcls (the primary class map PresetRoom.in_cls),
     P24 := Pcls kBatchClass (kBatchClass = PresetRoom.K_BATCH_CLASS = 24), Lsec := 1024 (RL_SEC), L24 := 2^15 (RL_C24),
     LPRIM c := Z.to_nat (RL_PRIM c), RL_PRIM c := 2^31 / PresetRoom.size_of_class c (a Theorem Labs lane's rl_prim_ok).
   - tr_peakP P tr: the maximum over all prefixes of a trace of the running net count of requests satisfying P, a realloc's
     new block counted before its old one is freed (ROOM-TEXTS :133); it is tr_peak_w (ReplyTrPeakW.v) at the weight
     (if P n then 1 else 0) (tr_peakP_w); Z-valued, as the kit's. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyTrPeakW.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require gestures_end_b_c.
Import ListNotations.
Open Scope Z_scope.

Definition acnt (P : Z -> bool) (l : list (Z * Z)) : nat := length (List.filter P (map snd l)).

(* the top_x instance of the count Variables *)
Definition kBatchClass : Z := PresetRoom.K_BATCH_CLASS.
Definition Psec (n : Z) : bool := negb (PresetRoom.is_primary n).
Definition Pcls (c n : Z) : bool := PresetRoom.in_cls c n.
Definition P24 : Z -> bool := Pcls kBatchClass.
Definition Lsec : nat := 1024.
Definition L24 : nat := Z.to_nat (2 ^ 15).
Definition RL_PRIM (c : Z) : Z := 2 ^ 31 / PresetRoom.size_of_class c.
Definition LPRIM (c : Z) : nat := Z.to_nat (RL_PRIM c).

(* the count peak of a trace, for any predicate: the room kit's own text (W_contract_x.v:249-256 at 67327a6003d), Z-valued,
   kept here as the one definition; tr_peakP_w below checks it event by event against tr_peak_w (ReplyTrPeakW.v) *)
Definition zb (b : bool) : Z := if b then 1 else 0.
Fixpoint tr_peakP {X : Type} (P : Z -> bool) (tr : list (RelayRunT.rev X)) : Z :=
  match tr with
  | [] => 0
  | RelayRunT.RMalloc n :: r => Z.max 0 (zb (P n) + tr_peakP P r)
  | RelayRunT.RFree k _ :: r => Z.max 0 (tr_peakP P r - zb (P k))
  | RelayRunT.RRealloc k n _ :: r => Z.max (zb (P n)) (zb (P n) - zb (P k) + tr_peakP P r)
  end.

(* ------------------------------------------------------------------ the generic list lemmas (ROOM-TEXTS (0.3) :70-75) *)
Lemma perm_filter_acnt {A : Type} (f : A -> bool) : forall l l', Permutation l l' ->
  Permutation (List.filter f l) (List.filter f l').
Proof.
  intros l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn [List.filter].
  - constructor.
  - destruct (f x); [apply perm_skip|]; exact IH.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - exact (perm_trans IH1 IH2).
Qed.
Lemma acnt_app : forall P l1 l2, acnt P (l1 ++ l2) = (acnt P l1 + acnt P l2)%nat.
Proof. intros. unfold acnt. rewrite map_app, List.filter_app, length_app. reflexivity. Qed.
Lemma acnt_perm : forall P l l', Permutation l l' -> acnt P l = acnt P l'.
Proof. intros P l l' H. unfold acnt. apply Permutation_length, perm_filter_acnt, Permutation_map, H. Qed.
Lemma acnt_snoc_le : forall P l b, (acnt P (l ++ [b]) <= acnt P l + 1)%nat.
Proof.
  intros P l [a n]. rewrite acnt_app. unfold acnt at 2. cbn [map List.filter snd].
  destruct (P n); cbn [length]; lia.
Qed.
Lemma acnt_del_le : forall P l1 l2 b, (acnt P (l1 ++ l2) <= acnt P (l1 ++ b :: l2))%nat.
Proof.
  intros P l1 l2 [a n]. rewrite !acnt_app. unfold acnt at 2 4. cbn [map List.filter snd].
  destruct (P n); cbn [length]; lia.
Qed.
(* the instance names unfold to a Theorem Labs lane's counts: one fact each, no spec *)
Lemma P24_cls : P24 = PresetRoom.in_cls PresetRoom.K_BATCH_CLASS.
Proof. reflexivity. Qed.
(* the event-by-event check (a Theorem Labs lane 02:02Z (3)): the kit's tr_peakP is tr_peak_w at the weight zb (P n) *)
Lemma tr_peakP_w : forall (X : Type) (P : Z -> bool) (tr : list (RelayRunT.rev X)),
  tr_peakP P tr = ReplyTrPeakW.tr_peak_w (fun n => zb (P n)) tr.
Proof.
  intros X P tr. induction tr as [|[n|k x|k n x] r IH]; [reflexivity| | |];
    cbn [tr_peakP]; unfold ReplyTrPeakW.tr_peak_w; cbn [fold_right]; fold (ReplyTrPeakW.tr_peak_w (fun n0 => zb (P n0)) r);
    rewrite IH; [reflexivity | reflexivity |].
  assert (Z0 : 0 <= zb (P n)) by (unfold zb; destruct (P n); lia). lia.
Qed.
Lemma tr_peakP_nonneg : forall (X : Type) (P : Z -> bool) (tr : list (RelayRunT.rev X)), 0 <= tr_peakP P tr.
Proof. intros. rewrite tr_peakP_w. apply ReplyTrPeakW.tr_peak_w_nonneg. Qed.

(* ------------------------------------------------------------------ the cut counts and the entry contract's count bound *)
(* a Theorem Labs lane 02:02Z (2) / 02:16Z: one place for every counting name.  cnt_sec / cnt_cls / cnt24 are the Z counts LS
   states (ReplyLSCntL.v proves their list lemmas over these definitions); SEC0 / CLS0 the bounds on the blocks one
   call keeps for the next; C240 is ROOM-TEXTS (c)'s name for class 24's, which is CLS0 (one bound for every class,
   a Theorem Labs lane 02:13Z). *)
Definition cnt_sec (l : list (Z * Z)) : Z := Z.of_nat (acnt Psec l).
Definition cnt_cls (c : Z) (l : list (Z * Z)) : Z := Z.of_nat (acnt (Pcls c) l).
Definition cnt24 (l : list (Z * Z)) : Z := cnt_cls kBatchClass l.
Definition SEC0 : Z := 64.
Definition CLS0 : Z := 64.
Definition C240 : Z := CLS0.

(* P24 is the predicate a Theorem Labs lane's ccnt24 counts (ccnt24 S := PresetRoom.ccnt kBatchClass (map snd (blocks S))) *)
Lemma acnt_P24_ccnt : forall l, acnt P24 l = PresetRoom.ccnt PresetRoom.K_BATCH_CLASS (map snd l).
Proof. reflexivity. Qed.
(* the ccnt form of a class count (a Theorem Labs lane's ccnt_c), for the proofs that walk PresetRoom.ccnt *)
Lemma cnt_cls_ccnt : forall c l, cnt_cls c l = Z.of_nat (PresetRoom.ccnt c (map snd l)).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ the model's size facts *)
(* texts_ok / msz_ok collect the sizes amodel_at gives, over the FIELD LISTS (the entries and the slots), so that
   this file does not need the cut's lmod: a list's records are lines (<= APARTIAL bytes), an entry's line buffer is
   at most 16,384 bytes and its keys are lines.  ReplyLSCntM.v's count bounds take them. *)
Definition texts_ok (l : hlist) : Prop :=
  Forall (fun r => Z.of_nat (length (snd r)) <= W_rep.APARTIAL) (hl_recs l).
Definition msz_ok (es : list rentry) (hs : list (option hsrc)) : Prop :=
  Forall (fun e => 0 <= re_cap e <= 16384 /\
    Forall (fun k => Z.of_nat (length (gestures_end_b_c.key_text k)) <= W_rep.APARTIAL) (re_keys e)) es /\
  Forall (fun o => match o with Some h => texts_ok (hs_expected h) /\ texts_ok (hs_held h) | None => True end) hs.

(* xcnt_ok (a Theorem Labs lane 02:13Z, W8Entry-2 adopted): the entry's blocks other than the input block inp, the relay's table when
   there is one (T0 <> 0) and g_out (cap, out) hold at most SEC0 secondary requests and at most CLS0 of each class.  The
   contract supplies inp := input_blks cx, T0 from arelay_at, (cap, out) from aout_at.  The exit post re-establishes it with
   the exit value equal to the entry value at every call, the first included (ReplyLS3w.fr_LS3c_exit_cnt). *)
Section xc.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Definition xcnt_kept (inp : list (Z * Z)) (T0 cap out : Z) : list (Z * Z) :=
  inp ++ (if T0 =? 0 then [] else [(T0, W_rep.ATABLE)]) ++ W_rep.aout_blks cap out.
Definition xcnt_ok (S : astate) (ly : alayout) (inp : list (Z * Z)) (T0 cap out : Z) : Prop :=
  cnt_sec (ablocks B ly S) - cnt_sec (xcnt_kept inp T0 cap out) <= SEC0 /\
  (forall c, 1 <= c <= 30 -> cnt_cls c (ablocks B ly S) - cnt_cls c (xcnt_kept inp T0 cap out) <= CLS0).
End xc.
