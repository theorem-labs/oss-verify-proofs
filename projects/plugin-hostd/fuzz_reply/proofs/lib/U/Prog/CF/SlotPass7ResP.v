From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT AllocPack AllocPack3
  AllocPack3Room AllocBound SlotKept AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotInv SlotSteps SlotRes SlotMove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c relay_event_b_c SlotOp7R3 SlotPass7RV SlotPass7Res SlotRun3 SlotRI3P.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma op7_ch_peak M : M <= NMAX -> forall cap a j tr cap' a', op7_ch M cap a j tr cap' a' ->
  forall Bd, 2 * M - cap <= Bd -> tr_peak tr Bd.
Proof.
  intros HM. induction 1 as [cap a j|cap a j c tr cap' a' Hc HcM Hch IH]; intros Bd HB; [apply tr_peak_nil|].
  destruct (Z.eqb_spec cap 0) as [E0|E0]; apply tr_peak_cons; cbv beta iota; cbn [ev_db];
    (split; [lia|apply IH; lia]).
Qed.

Lemma op7_peak EL live mx CAP o : 0 <= EL -> 2 * (EL + 1) <= NMAX -> 0 <= mx -> 0 <= CAP <= NMAX ->
  tr_peak (op7_trT EL live mx CAP o) (5 * (EL + 1)).
Proof.
  intros HE HN Hmx HC. unfold op7_trT. apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|].
  apply tr_peak_app; [|apply tr_peak_free].
  apply (op7_ch_peak (2 * (EL + 1)) HN CAP o 1 _ _ _ (op7_T_ch live mx CAP EL o Hmx HE ltac:(lia))); lia.
Qed.

Lemma p7p_room1 (F : ResFormT) (p : sptr) qr (tr : trF) (bc : rt_R F) : wf_from sptr 0 tr -> length qr = nretF tr ->
  room_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) (rt_room F) (p :: qr) bc 1
    (shift_tr sptr 1 tr) ->
  roomF F qr bc tr.
Proof.
  intros W Hl H.
  pose proof (room_shift (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) (rt_room F) [p] qr [] tr bc 1 0
    W ltac:(lia) eq_refl) as E.
  rewrite app_nil_r in E. exact (proj1 E H).
Qed.

Theorem op7_res3P OK RM E K K' V L A EL live mx CAP OUT :
  RMH RM -> RI3P OK E K V L A -> K <= K' ->
  0 <= EL -> 2 * (EL + 1) <= NMAX -> 0 <= mx -> 0 <= CAP <= NMAX ->
  List.NoDup (map fst (blocks L A)) ->
  (0 < CAP -> In (OUT, CAP) (blocks L A)) -> (CAP = 0 -> forall m, ~ In (OUT, m) (blocks L A)) ->
  exists bnd, rt_ok (pack3P OK RM) A bnd /\
    (forall qs, length qs = nretF (op7_trT EL live mx CAP (known_at L A OUT)) ->
       roomF (pack3P OK RM) qs bnd (op7_trT EL live mx CAP (known_at L A OUT))) /\
    forall L' A' qs, length qs = nretF (op7_trT EL live mx CAP (known_at L A OUT)) ->
      rt_ok (pack3P OK RM) A' (runF (pack3P OK RM) qs bnd (op7_trT EL live mx CAP (known_at L A OUT))) ->
      forall V', (length (rv_nc V') <= NC_MAX)%nat ->
        (forall c, 0 <= c < 49 -> nc_cnt V L A c + op7_dl CAP (op7_capT live mx CAP EL) c <= nc_cnt V' L' A' c) ->
        ncs V L A + (op7_capT live mx CAP EL - CAP) <= ncs V' L' A' -> ncs V' L' A' <= rv_wt V' -> rv_wt V' <= rv_wt V ->
        rv_pend V' = rv_pend V -> rv_ek V' = rv_ek V -> List.NoDup (map fst (blocks L' A')) ->
        (forall p n, In (p, n) (user_blocks A) -> ptr_addr L p <> OUT \/ live = false -> ptr_addr L' p = ptr_addr L p) ->
        (forall a m, In a (rv_nc V) -> In (a, m) (blocks L A) -> a <> OUT \/ live = false -> In a (rv_nc V')) ->
        (live = true -> In (ptr_addr L' (resolveF qs (op7_outT live mx CAP EL (known_at L A OUT)))) (rv_nc V')) ->
        RI3P OK E K' V' L' A'.
Proof.
  intros HRM ((b & al & alb & HR & HL) & HOK) Hk HEL HN Hmx HCAP HND HO HO0.
  exists b. split; [split; [exact HR|exact HOK]|]. split.
  - intros qs Hq. apply (proj2 (roomF_pack3P OK RM qs b (op7_trT EL live mx CAP (known_at L A OUT)))). split.
    + exact (op7_room3 rv_wt (ss_pl E) K V L A b al alb EL live mx CAP (known_at L A OUT) HL HEL HN Hmx HCAP qs Hq).
    + pose proof HL as (HCs & HMc & _). pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as HBy.
      apply (RMrun_of_peak RM (ss_pl E) b _ (5 * (EL + 1)) HRM HCs HMc).
      * assert (X : 2 * PB3_MAX + 5 * NMAX <= 2 * CF_MAX) by (apply Z.leb_le; vm_compute; reflexivity). lia.
      * exact (op7_peak EL live mx CAP (known_at L A OUT) HEL HN Hmx HCAP).
  - intros L' A' qs Hq (HR' & HOK') V' HN' HC' HB' HW1' HW' HP' HEK HND' HK HV HLast.
    split; [|exact HOK']. rewrite runF_pack3P in HR'.
    exists (runF pack3_form qs b (op7_trT EL live mx CAP (known_at L A OUT))), al, alb. split; [exact HR'|].
    apply (op7_ledger3 rv_wt (ss_pl E) K K' V L A b al alb EL live mx CAP OUT qs V' L' A'); try assumption.
    apply (op7_nc_step rv_wt (ss_pl E) K K' V L A b al alb V' L' A'); assumption.
Qed.

Theorem op7_res_s_RI3P OK RM : RMH RM -> op7_res_s (pack3P OK RM) (RI3P OK).
Proof.
  intros HRM E K K' L A EL live mx CAP G out es hj HRI HK1 HKK HnE HEL Hmx HCAP HND HO HO0.
  assert (HnE' : ss_n E < 67108864) by exact HnE.
  assert (HC' : CAP <= 536870912) by exact (proj2 HCAP).
  assert (HN : 2 * (EL + 1) <= 536879104) by lia.
  assert (HC2 : 0 <= CAP <= 536879104) by lia.
  destruct (op7_res3P OK RM E K K' (view_of G out es hj) L A EL live mx CAP out HRM HRI ltac:(lia) (proj1 HEL) HN
    (proj1 Hmx) HC2 HND HO HO0) as (b & HR & ROOM & POST).
  unfold op7_S1, op7_S2, op7_S3, op7_RV_s.
  set (o := known_at L A out) in *.
  pose proof (p7r_rel_wf live mx CAP EL o I) as W.
  assert (F1 : relay_event_tr live mx 0 CAP EL 1 o = shift_tr sptr 1 (relay_event_tr live mx 0 CAP EL 0 o)).
  { rewrite (op7_shift_tr live mx 0 CAP EL 1 o). reflexivity. }
  assert (F2 : nretF (op7_trT EL live mx CAP o) = S (nretF (relay_event_tr live mx 0 CAP EL 0 o))).
  { unfold op7_trT. rewrite p7r_nret_cons, nret_app, F1, nret_shift. cbn [rets nret fold_right]. lia. }
  hnf. exists b. split; [exact HR|]. split.
  - intros qs _.
    pose proof (ROOM (List.repeat (SP 0 0) (nretF (op7_trT EL live mx CAP o))) ltac:(apply List.repeat_length))
      as R0.
    unfold roomF, room_run, op7_trT in R0. cbn [room_from] in R0.
    exact (conj (proj1 R0) I).
  - intros L1 A1 qm _ Hok1. hnf. exists (pb3_malloc b (EL + 1)). split; [exact Hok1|]. split.
    + intros qr Hqr.
      pose proof (ROOM (SP 0 0 :: qr) ltac:(cbn [length]; rewrite F2, Hqr; reflexivity)) as R1.
      unfold roomF, room_run, op7_trT in R1. cbn [room_from] in R1. destruct R1 as [_ R1].
      apply room_from_app in R1. destruct R1 as [R1 _]. rewrite F1 in R1.
      exact (p7p_room1 (pack3P OK RM) (SP 0 0) qr _ (pb3_malloc b (EL + 1)) W Hqr R1).
    + intros L2 A2 qr Hqr Hok2 p. hnf.
      exists (runF (pack3P OK RM) qr (pb3_malloc b (EL + 1)) (relay_event_tr live mx 0 CAP EL 0 o)).
      split; [exact Hok2|]. split; [intros qf _; exact I|].
      intros L3 A3 qf _ Hok3 out' Hlv es' Hes' Hhj Hmv HlF Hpa HND3 Hwt1 Hwt2.
      pose proof (op7_move_count _ _ _ _ _ _ out CAP out' _ live Hmv HlF (proj1 HCAP)) as (MC1 & MC2 & MC3).
      apply (POST L3 A3 (p :: qr)).
      * cbn [length]; rewrite F2, Hqr; reflexivity.
      * rewrite runF_pack3P, op7_run_eq. cbn [nth]. rewrite F1, p7r_run1 by assumption. exact Hok3.
      * exact (op7_view_len G out' es' hj Hes' Hhj).
      * exact MC1.
      * exact MC2.
      * exact Hwt1.
      * change (nc_wt es' hj <= nc_wt es hj). lia.
      * reflexivity.
      * reflexivity.
      * exact HND3.
      * exact Hpa.
      * exact MC3.
      * intros Hl. destruct (Hlv Hl) as [_ Ha].
        assert (F3 : op7_outT live mx CAP EL o = shift_addr sptr 1 (relay_event_out live mx 0 CAP EL 0 o)).
        { unfold op7_outT. rewrite op7_shift_out. reflexivity. }
        rewrite F3, p7r_resolve1, Ha. cbn [rv_nc view_of In]. right. left. reflexivity.
Qed.
