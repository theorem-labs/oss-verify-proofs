(* C3, the conditions a Theorem Labs lane set (00:22Z) for option (a) (tr_peak everywhere), which W8 has landed: the kit's
   gesture_end / gestures_end rooms ge_room / gse_room (lib/A/W_contract.v:1525, :1586) are the peak forms this file
   first stated, and the lemmas below are stated over them.
   (1) the composition, proved: a caller's peak premise gives each callee's peak premise at the callee's start state
       (tr_peak_callee, with address independence of the callee traces' sizes, so the callee premise can name its
       trace at the canonical addresses as the contracts do); the peak forms of send_line's and list_push's rooms
       (sl_room_p, lp_room_p: sl_spec / lp_spec state them inline, with no name), gse_room's unfolding from one peak
       over the whole key run (gse_room_p_of_peak) and ge_room's sends;
       the SUM forms are NOT implied, proved on concrete traces (catch_abstract: 3 requests, peak 60 / sum 70;
       catch_gse: 8 held keys of 14 bytes from g_capout 0, peak 331 / sum 530, against the kit's former sum-form rooms,
       kept here as the local ge_room_sum / gse_room_sum_form);
   (2) free(NULL) (W_journal.v:820-840 afree_null_cf_rule: the blocks are kept up to Permutation):
       tr_peak_after_free_null, and tr_peak_free0 for a trace that records it as RFree 0. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_drain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_write.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_event.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyRINV.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyLSArms.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayKeys RelayModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
  RelayRunT ListTr drain_b_c send_line_b_c gesture_end_b_c gestures_end_b_c relay_remove_b_c RelayCap SlotInv
  SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
  ReplyLSDrainPre ReplyLSRemove3 ReplyLSRrPre ReplyLSDrain3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyTrPeak.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================== sizes only *)
Definition ev_sz {A : Type} (ev : RelayRunT.rev A) : Z * Z * Z :=
  match ev with
  | RelayRunT.RMalloc n => (0, 0, n)
  | RelayRunT.RFree k _ => (1, k, 0)
  | RelayRunT.RRealloc k n _ => (2, k, n)
  end.
Definition tr_sz {A : Type} (tr : list (RelayRunT.rev A)) : list (Z * Z * Z) := map ev_sz tr.

Section sz.
Context {A A' : Type}.
Lemma tr_sz_app : forall (a b : list (RelayRunT.rev A)), tr_sz (a ++ b) = tr_sz a ++ tr_sz b.
Proof. intros a b. unfold tr_sz. apply map_app. Qed.
Lemma tr_sz_measures : forall (t1 : list (RelayRunT.rev A)) (t2 : list (RelayRunT.rev A')), tr_sz t1 = tr_sz t2 ->
  tr_peak t1 = tr_peak t2 /\ tr_net t1 = tr_net t2 /\ tr_max t1 = tr_max t2 /\ tr_alloc t1 = tr_alloc t2.
Proof.
  induction t1 as [|e1 r1 IH]; intros [|e2 r2] H; cbn in H; try discriminate H.
  - repeat split; reflexivity.
  - injection H as He Hr. destruct (IH r2 Hr) as (P1 & N1 & M1 & A1).
    destruct e1, e2; cbn in He; try discriminate He; injection He as ?; subst;
      cbn [tr_peak tr_net tr_max tr_alloc fold_right] in *;
      unfold tr_peak, tr_net, tr_max, tr_alloc in *; cbn [fold_right];
      rewrite ?P1, ?N1, ?M1, ?A1; repeat split; lia.
Qed.
End sz.

(* send_line's requests do not depend on the addresses it is started at *)
Lemma sl_run_sz : forall f mx no cap rem j o j' o',
  tr_sz (fst (send_line_b_c.sl_run f mx no cap rem j o)) = tr_sz (fst (send_line_b_c.sl_run f mx no cap rem j' o')).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o j' o'; [reflexivity|].
  cbn [send_line_b_c.sl_run].
  destruct (rem <=? 0); [reflexivity|].
  destruct (cap <? no + _); [|apply IH].
  cbn [fst]. unfold tr_sz in *. cbn [map]. f_equal.
  - destruct (cap =? 0); reflexivity.
  - apply IH.
Qed.
Lemma send_line_tr_sz : forall live mx no cap len j o j' o',
  tr_sz (send_line_b_c.send_line_tr live mx no cap len j o) = tr_sz (send_line_b_c.send_line_tr live mx no cap len j' o').
Proof. intros. unfold send_line_b_c.send_line_tr. destruct live; [apply sl_run_sz | reflexivity]. Qed.
Lemma gesture_end_tr_sz : forall live mx no cap XL j o j' o',
  tr_sz (gesture_end_b_c.gesture_end_tr live mx no cap XL j o) =
  tr_sz (gesture_end_b_c.gesture_end_tr live mx no cap XL j' o').
Proof.
  intros. unfold gesture_end_b_c.gesture_end_tr. rewrite !tr_sz_app. f_equal; apply send_line_tr_sz.
Qed.
Lemma list_push_tra_sz : forall v v' N CAP n,
  tr_sz (ListTr.list_push_tra v N CAP n) = tr_sz (ListTr.list_push_tra v' N CAP n).
Proof.
  intros. unfold ListTr.list_push_tra. rewrite !tr_sz_app. f_equal.
  destruct (N =? CAP); [destruct (CAP =? 0)|]; reflexivity.
Qed.

(* ================================================================== (1) the composition *)
Section comp.
Context {P : Type}.
Local Notation rv := (RelayRunT.rev P).
(* a callee whose trace w runs after the prefix a of the caller's trace: its start live bytes bi are at most the
   caller's start bb plus a's net change (the allocator rules' posts move the live bytes exactly, step lemmas of
   ReplyTrPeak.v), so the caller's peak premise gives the callee's *)
Lemma tr_peak_callee : forall (a w b : list rv) bb bi L,
  bi <= bb + tr_net a -> bb + tr_peak (a ++ w ++ b) <= L -> bi + tr_peak w <= L.
Proof. intros a w b bb bi L H1 H2. pose proof (tr_peak_mid a w b). lia. Qed.
Lemma tr_max_callee : forall (a w b : list rv) M, tr_max (a ++ w ++ b) < M -> tr_max w < M.
Proof. intros a w b M H. rewrite !tr_max_app' in H. lia. Qed.
End comp.

(* the exact moves of the live bytes, one rule each (W_journal.v posts: malloc :790, free :812, realloc0 :863,
   realloc :864, strndup :892, free(NULL) :833) *)
Section moves.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Lemma bb_after_malloc : forall ly S ly2 S2 res n,
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, n)] -> blocks_bytes S2 = blocks_bytes S + n.
Proof. intros. rewrite (tp_bb_app B ly S ly2 S2 [(res, n)] H). cbn [bsum fold_right map snd]. unfold bsum. cbn. lia. Qed.
Lemma bb_after_free : forall ly S ly2 S2 pa n,
  (exists l1 l2, ablocks B ly S = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) ->
  blocks_bytes S2 = blocks_bytes S - n.
Proof.
  intros ly S ly2 S2 pa n (l1 & l2 & E1 & E2).
  rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), E1, E2, !bsum_app, bsum_cons. cbn [snd]. lia.
Qed.
Lemma bb_after_realloc0 : forall ly S ly2 S2 res n,
  Permutation (ablocks B ly2 S2) ((res, n) :: ablocks B ly S) -> blocks_bytes S2 = blocks_bytes S + n.
Proof.
  intros. rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ H), bsum_cons, <- (blocks_bytes_bsum B ly S).
  cbn [snd]. lia.
Qed.
Lemma bb_after_realloc : forall ly S ly2 S2 p n0 res n,
  (exists l1 l2, ablocks B ly S = l1 ++ (p, n0) :: l2 /\ Permutation (ablocks B ly2 S2) ((res, n) :: l1 ++ l2)) ->
  blocks_bytes S2 = blocks_bytes S - n0 + n.
Proof.
  intros ly S ly2 S2 p n0 res n (l1 & l2 & E1 & HP).
  rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HP), (blocks_bytes_bsum B ly S), E1, bsum_cons, !bsum_app,
    bsum_cons. cbn [snd]. lia.
Qed.
(* (2) free(NULL): the blocks are kept, so the live bytes and the premise are *)
Lemma bb_after_free_null : forall ly S ly2 S2,
  Permutation (ablocks B ly2 S2) (ablocks B ly S) -> blocks_bytes S2 = blocks_bytes S.
Proof. intros. rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ H), <- (blocks_bytes_bsum B ly S). reflexivity. Qed.
Lemma tr_peak_after_free_null : forall {P : Type} ly S ly2 S2 (r : list (RelayRunT.rev P)),
  blocks_bytes S + tr_peak r <= LIVE_MAX -> Permutation (ablocks B ly2 S2) (ablocks B ly S) ->
  blocks_bytes S2 + tr_peak r <= LIVE_MAX.
Proof. intros P ly S ly2 S2 r H HP. rewrite (bb_after_free_null ly S ly2 S2 HP). exact H. Qed.
End moves.
Lemma tr_peak_free0 : forall {P : Type} x (r : list (RelayRunT.rev P)), tr_peak (RelayRunT.RFree 0 x :: r) = tr_peak r.
Proof. intros P x r. rewrite tr_peak_free. pose proof (tr_peak_nonneg r). lia. Qed.

(* ================================================================== the peak forms of the callee rooms *)
(* send_line (sl_spec's room, W_contract.v:903-904 / :913 in sum form) *)
Definition sl_room_p (MMAX bb : Z) (c : ctl) (mx no cap len : Z) : Prop :=
  sl_maxr c mx no cap len < MMAX /\
  bb + tr_peak (send_line_b_c.send_line_tr (sl_live c len) mx no cap len 0 RelayRunF.adr0) <= LIVE_MAX.
(* list_push (lp_spec's room, W_contract.v:390 in its own form; lp_spec keeps its request bound lp_vbytes < MMAX as a
   separate premise, so this room form carries none, unlike sl_room_p / ge_room) *)
Definition lp_room_p (bb : Z) (l : hlist) (n : Z) : Prop :=
  bb + tr_peak (ListTr.list_push_tra RelayRunF.adr0 (hl_n l) (hl_cap l) n) <= LIVE_MAX.
(* gestures_end's key run: each key's gesture_end, then free (key) (relay.c:132-142); gse_room's threading *)
Fixpoint gse_tr (c : ctl) (mx no cap : Z) (xs : list (list byte)) : list (RelayRunT.rev YO0i.sptr) :=
  match xs with
  | [] => []
  | x :: xs' => ge_tr c mx no cap (Z.of_nat (length x)) ++
      RelayRunT.RFree (Z.of_nat (length x) + 1) RelayRunF.adr0 ::
      gse_tr (ge_ctl c (Z.of_nat (length x))) mx (ge_no c no (Z.of_nat (length x)))
        (ge_cap c mx no cap (Z.of_nat (length x))) xs'
  end.
(* one peak over the whole key run gives gse_room (W_contract.v:1586), key by key *)
Lemma gse_room_p_of_peak : forall MMAX xs bb c mx no cap,
  tr_max (gse_tr c mx no cap xs) < MMAX -> bb + tr_peak (gse_tr c mx no cap xs) <= LIVE_MAX ->
  gse_room MMAX bb c mx no cap xs.
Proof.
  intros MMAX xs. induction xs as [|x xs IH]; intros bb c mx no cap HM HP; [exact I|].
  cbn [gse_tr] in HM, HP. cbn [gse_room].
  rewrite tr_max_app', tr_max_cons' in HM. rewrite tr_peak_app, tr_peak_free in HP.
  split; [split; lia|]. apply IH; lia.
Qed.
(* each send of gesture_end, from ge_room (W_contract.v:1525) at its start (gesture_end_tr = two send_line runs) *)
Lemma ge_room_p_sends : forall MMAX bb c mx no cap XL,
  ge_room MMAX bb c mx no cap XL ->
  bb + tr_peak (send_line_b_c.send_line_tr (sl_live c XL) mx no cap XL 0 RelayRunF.adr0) <= LIVE_MAX.
Proof.
  intros MMAX bb c mx no cap XL (_ & HP). unfold ge_tr, gesture_end_b_c.gesture_end_tr in HP.
  rewrite tr_peak_app in HP. lia.
Qed.
(* a callee send_line / list_push / gesture_end inside a caller's trace, at any addresses: the caller's peak gives the
   callee's peak premise at its canonical trace *)
Lemma sl_peak_callee : forall (a b : list (RelayRunT.rev YO0i.sptr)) bb bi live mx no cap len j o L,
  bi <= bb + tr_net a ->
  bb + tr_peak (a ++ send_line_b_c.send_line_tr live mx no cap len j o ++ b) <= L ->
  bi + tr_peak (send_line_b_c.send_line_tr live mx no cap len 0 RelayRunF.adr0) <= L.
Proof.
  intros. destruct (tr_sz_measures _ _ (send_line_tr_sz live mx no cap len j o 0 RelayRunF.adr0)) as (E & _).
  rewrite <- E. exact (tr_peak_callee a _ b bb bi L H H0).
Qed.
Lemma lp_peak_callee : forall (a b : list (RelayRunT.rev YO0i.sptr)) bb bi v N CAP n L,
  bi <= bb + tr_net a ->
  bb + tr_peak (a ++ ListTr.list_push_tra v N CAP n ++ b) <= L ->
  bi + tr_peak (ListTr.list_push_tra RelayRunF.adr0 N CAP n) <= L.
Proof.
  intros. destruct (tr_sz_measures _ _ (list_push_tra_sz v RelayRunF.adr0 N CAP n)) as (E & _).
  rewrite <- E. exact (tr_peak_callee a _ b bb bi L H H0).
Qed.
Lemma ge_peak_callee : forall (a b : list (RelayRunT.rev YO0i.sptr)) bb bi live mx no cap XL j o L,
  bi <= bb + tr_net a ->
  bb + tr_peak (a ++ gesture_end_b_c.gesture_end_tr live mx no cap XL j o ++ b) <= L ->
  bi + tr_peak (gesture_end_b_c.gesture_end_tr live mx no cap XL 0 RelayRunF.adr0) <= L.
Proof.
  intros. destruct (tr_sz_measures _ _ (gesture_end_tr_sz live mx no cap XL j o 0 RelayRunF.adr0)) as (E & _).
  rewrite <- E. exact (tr_peak_callee a _ b bb bi L H H0).
Qed.
(* every request of gesture_end (both sends: the key's bytes, then " end") finds room, in order *)
Lemma ge_room_p_room : forall MMAX bb c mx no cap XL,
  ge_room MMAX bb c mx no cap XL -> tr_room bb (ge_tr c mx no cap XL).
Proof. intros MMAX bb c mx no cap XL (_ & HP). exact (tr_peak_room _ bb HP). Qed.
(* the second send's own peak premise, at the live bytes after the first send *)
Lemma ge_room_p_second : forall MMAX bb c mx no cap XL,
  ge_room MMAX bb c mx no cap XL ->
  let live := sl_live c XL in
  let t1 := send_line_b_c.send_line_tr live mx no cap XL 0 RelayRunF.adr0 in
  (bb + tr_net t1) + tr_peak (send_line_b_c.send_line_tr live mx (no + XL)
     (send_line_b_c.send_line_cap live mx no cap XL) 5 0 RelayRunF.adr0) <= LIVE_MAX.
Proof.
  intros MMAX bb c mx no cap XL (_ & HP). cbv zeta. unfold ge_tr, gesture_end_b_c.gesture_end_tr in HP.
  pose proof (sl_peak_callee (send_line_b_c.send_line_tr (sl_live c XL) mx no cap XL 0 RelayRunF.adr0) []
    bb (bb + tr_net (send_line_b_c.send_line_tr (sl_live c XL) mx no cap XL 0 RelayRunF.adr0))
    (sl_live c XL) mx (no + XL) (send_line_b_c.send_line_cap (sl_live c XL) mx no cap XL) 5
    (0 + RelayRunF.nretF (send_line_b_c.send_line_tr (sl_live c XL) mx no cap XL 0 RelayRunF.adr0))
    (send_line_b_c.send_line_out (sl_live c XL) mx no cap XL 0 RelayRunF.adr0) LIVE_MAX ltac:(lia)) as H.
  rewrite app_nil_r in H. exact (H HP).
Qed.
(* the peak premise gives every request's live-bytes premise in order (the callee walk's use) *)
Lemma sl_room_p_room : forall MMAX bb c mx no cap len,
  sl_room_p MMAX bb c mx no cap len ->
  tr_room bb (send_line_b_c.send_line_tr (sl_live c len) mx no cap len 0 RelayRunF.adr0).
Proof. intros MMAX bb c mx no cap len (_ & H). exact (tr_peak_room _ bb H). Qed.
Lemma lp_room_p_room : forall bb l n,
  lp_room_p bb l n -> tr_room bb (ListTr.list_push_tra RelayRunF.adr0 (hl_n l) (hl_cap l) n).
Proof. intros bb l n H. exact (tr_peak_room _ bb H). Qed.

(* ================================================================== the sum forms are not implied *)
Lemma catch_abstract :
  let tr := [RelayRunT.RMalloc (P := YO0i.sptr) 10; RelayRunT.RRealloc 10 20 RelayRunF.adr0;
             RelayRunT.RRealloc 20 40 RelayRunF.adr0] in
  (LIVE_MAX - 60) + tr_peak tr <= LIVE_MAX /\ ~ ((LIVE_MAX - 60) + tr_alloc tr <= LIVE_MAX).
Proof. cbv zeta. replace (tr_peak _) with 60 by (vm_compute; reflexivity).
  replace (tr_alloc _) with 70 by (vm_compute; reflexivity). lia. Qed.

(* the kit's former SUM-form rooms of gesture_end / gestures_end, renamed: bb9dae5d905 lib/A/W_contract.v:1498-1499
   ge_room and :1557-1563 gse_room (MMAX was that Section's Variable).  Kept only to record C3's finding *)
Definition ge_room_sum (MMAX bb : Z) (c : ctl) (mx no cap XL : Z) : Prop :=
  tr_max (ge_tr c mx no cap XL) < MMAX /\ bb + tr_alloc (ge_tr c mx no cap XL) <= LIVE_MAX.
Fixpoint gse_room_sum_form (MMAX bb : Z) (c : ctl) (mx no cap : Z) (xs : list (list byte)) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => ge_room_sum MMAX bb c mx no cap (Z.of_nat (length x)) /\
      gse_room_sum_form MMAX (bb + tr_alloc (ge_tr c mx no cap (Z.of_nat (length x)))) (ge_ctl c (Z.of_nat (length x)))
        mx (ge_no c no (Z.of_nat (length x))) (ge_cap c mx no cap (Z.of_nat (length x))) xs'
  end.

Definition ctl_live : ctl := CTL 3 0 0 0 0.
Definition k14 : list byte := repeat (Z_to_bv 8 97) 14.
Definition keys8 : list (list byte) := [k14; k14; k14; k14; k14; k14; k14; k14].
(* the sum form's sum, the amount its threaded bb reaches above the start *)
Fixpoint gse_sum (c : ctl) (mx no cap : Z) (xs : list (list byte)) : Z :=
  match xs with
  | [] => 0
  | x :: xs' => tr_alloc (ge_tr c mx no cap (Z.of_nat (length x))) +
      gse_sum (ge_ctl c (Z.of_nat (length x))) mx (ge_no c no (Z.of_nat (length x)))
        (ge_cap c mx no cap (Z.of_nat (length x))) xs'
  end.
(* the sum form at bb needs bb + gse_sum <= LIVE_MAX at its last key *)
Lemma gse_room_sum : forall MMAX xs bb c mx no cap, gse_room_sum_form MMAX bb c mx no cap xs -> xs <> [] ->
  bb + gse_sum c mx no cap xs <= LIVE_MAX.
Proof.
  intros MMAX xs. induction xs as [|x xs IH]; intros bb c mx no cap H Hne; [contradiction|].
  cbn [gse_room_sum_form] in H. destruct H as ((_ & H1) & H2). cbn [gse_sum].
  destruct xs as [|x' xs'].
  - cbn [gse_sum]. lia.
  - specialize (IH _ _ _ _ _ H2 ltac:(discriminate)). lia.
Qed.
(* 8 held keys of 14 bytes, g_capout 0, live controller: the kit's (peak) gse_room holds, the sum form does not *)
Lemma catch_gse :
  gse_room WR_MMAX (LIVE_MAX - 331) ctl_live 0 0 0 keys8 /\
  ~ gse_room_sum_form WR_MMAX (LIVE_MAX - 331) ctl_live 0 0 0 keys8.
Proof.
  assert (EP : tr_peak (gse_tr ctl_live 0 0 0 keys8) = 331) by (vm_compute; reflexivity).
  assert (EM : tr_max (gse_tr ctl_live 0 0 0 keys8) = 294) by (vm_compute; reflexivity).
  assert (ES : gse_sum ctl_live 0 0 0 keys8 = 530) by (vm_compute; reflexivity).
  assert (HW : WR_MMAX = 1072693248) by reflexivity.
  split.
  - apply gse_room_p_of_peak; lia.
  - intros H. pose proof (gse_room_sum _ _ _ _ _ _ _ H ltac:(discriminate)). lia.
Qed.
