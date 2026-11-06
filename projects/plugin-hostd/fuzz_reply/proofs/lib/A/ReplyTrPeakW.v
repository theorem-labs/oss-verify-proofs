(* The count half of LS v3, part 2: the per-call count premise inside a callee, as a weighted peak over its trace.
   room_live_call_keep (a Theorem Labs lane; cfdriver Reusable/YGcfRoomLive.v:1399) needs, at the PRE of every allocator call,
   sec_cnt S <= 1,024 /\ ccnt24 S <= 2^15 /\ the per-class primary counts <= RL_PRIM c.  Inside a callee the state at
   its k-th call is the callee's start state plus the trace's first k events, so the callee's premise is
   `cnt S + tr_peak_w w tr <= LIM`, with w the event's count weight (1 when the request is secondary / in the class,
   0 otherwise; a realloc counts its new block before the old one is freed, a Theorem Labs lane 00:23Z: "the max over all PREFIXES
   of the trace, including realloc's transient new-before-old").  tr_peak_w with w := fun n => n is ReplyTrPeak.v's
   byte peak; every composition lemma there holds for any weight.
   The weights w_sec / w_cls and the fact that a block list's counts move by w of each event exactly (the cnt_after
   lemmas) are in ReplyLSCntL.v, over ReplyCnt.v's count definitions; this file is the weight-generic half, so that
   ReplyCnt.v can take tr_peak_w for tr_peakP_w.  The callee premise gives each inner call's count premise in order
   (trw_room). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require PresetRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT.
Import ListNotations.
Open Scope Z_scope.


Section w.
Variable w : Z -> Z.
Context {P : Type}.
Local Notation rv := (RelayRunT.rev P).

Definition tr_peak_w (tr : list rv) : Z :=
  fold_right (fun ev acc =>
    match ev with
    | RelayRunT.RMalloc n => Z.max 0 (w n + acc)
    | RelayRunT.RFree k _ => Z.max 0 (acc - w k)
    | RelayRunT.RRealloc k n _ => Z.max 0 (Z.max (w n) (w n - w k + acc))
    end) 0 tr.
Definition tr_net_w (tr : list rv) : Z :=
  fold_right (fun ev acc =>
    match ev with
    | RelayRunT.RMalloc n => w n
    | RelayRunT.RFree k _ => - w k
    | RelayRunT.RRealloc k n _ => w n - w k
    end + acc) 0 tr.
(* every inner call finds its count premise: the count bb at its point plus its new block's weight within LIM *)
Fixpoint trw_room (LIM bb : Z) (tr : list rv) : Prop :=
  match tr with
  | [] => True
  | RelayRunT.RMalloc n :: r => bb + w n <= LIM /\ trw_room LIM (bb + w n) r
  | RelayRunT.RFree k _ :: r => trw_room LIM (bb - w k) r
  | RelayRunT.RRealloc k n _ :: r => bb + w n <= LIM /\ trw_room LIM (bb - w k + w n) r
  end.

Lemma tr_peak_w_nonneg : forall tr, 0 <= tr_peak_w tr.
Proof. destruct tr as [|[n|k x|k n x] r]; cbn; lia. Qed.
Lemma tr_peak_w_app : forall a b, tr_peak_w (a ++ b) = Z.max (tr_peak_w a) (tr_net_w a + tr_peak_w b).
Proof.
  induction a as [|ev a IH]; intros b; cbn [app].
  - unfold tr_net_w; cbn [fold_right]. change (tr_peak_w []) with 0. pose proof (tr_peak_w_nonneg b). lia.
  - unfold tr_peak_w, tr_net_w in *; cbn [fold_right]. rewrite IH.
    pose proof (tr_peak_w_nonneg a) as Ha. pose proof (tr_peak_w_nonneg b) as Hb. unfold tr_peak_w in Ha, Hb.
    destruct ev as [n|k x|k n x]; lia.
Qed.
Lemma tr_net_w_app : forall a b, tr_net_w (a ++ b) = tr_net_w a + tr_net_w b.
Proof. induction a as [|ev a IH]; intros b; cbn [app]; [reflexivity|]. unfold tr_net_w in *; cbn [fold_right]. rewrite IH. lia. Qed.
Lemma tr_peak_w_mid : forall a v b, tr_net_w a + tr_peak_w v <= tr_peak_w (a ++ v ++ b).
Proof. intros. rewrite !tr_peak_w_app. pose proof (tr_peak_w_nonneg b). lia. Qed.
(* a callee inside a caller's trace: the caller's count premise gives the callee's at its start count *)
Lemma tr_peak_w_callee : forall a v b bb bi LIM,
  bi <= bb + tr_net_w a -> bb + tr_peak_w (a ++ v ++ b) <= LIM -> bi + tr_peak_w v <= LIM.
Proof. intros. pose proof (tr_peak_w_mid a v b). lia. Qed.
(* the callee premise gives each inner call's premise, in order *)
Lemma tr_peak_w_room : forall tr bb LIM, bb + tr_peak_w tr <= LIM -> trw_room LIM bb tr.
Proof.
  induction tr as [|[n|k x|k n x] r IH]; intros bb LIM H; cbn [trw_room]; [exact I| | |].
  - unfold tr_peak_w in H; cbn [fold_right] in H. fold (tr_peak_w r) in H.
    split; [pose proof (tr_peak_w_nonneg r); lia|]. apply IH. lia.
  - unfold tr_peak_w in H; cbn [fold_right] in H. fold (tr_peak_w r) in H. apply IH. lia.
  - unfold tr_peak_w in H; cbn [fold_right] in H. fold (tr_peak_w r) in H.
    split; [lia|]. apply IH. lia.
Qed.
End w.
