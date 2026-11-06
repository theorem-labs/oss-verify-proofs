From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack
  AllocPackRoom AllocBound AllocGS FrameSlotP AllocPack3 AllocPack3Room ContractT AllocPack3Ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotEntryRun SlotPass0 SlotPass1w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import TrModel ListRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept SlotInv SlotSteps SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotParse SlotCaps3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_add_b_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_finish_b_c SlotMove SlotNcMove3 SlotRun3 SlotOp7R3 SlotResR3 SlotResReply SlotExitFinRes SlotExitMove SlotRI3P.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rp_bytes_room : PB3_MAX + 2 * NMAX <= CF_MAX.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma rp_frees_lift OK RM (P : layout -> astate -> list sptr -> Prop) A tr : OK A -> Forall ev_free tr ->
  res_tr pack3_form P A tr -> res_tr (pack3P OK RM) (fun L' A' qs => P L' A' qs /\ OK A') A tr.
Proof.
  intros HOK Hf (bnd & HR & _ & HP). exists bnd. split; [split; [exact HR|exact HOK]|]. split.
  - intros qs _. apply roomF_frees. exact Hf.
  - intros L' A' qs Hq (HR' & HOK'). split; [exact (HP L' A' qs Hq HR')|exact HOK'].
Qed.

Lemma rp_exit_RV OK E k L A G out es hj dels adds L' A' qs :
  exit_RV_s RI3_reply E k L A G out es hj dels adds L' A' qs -> OK A' ->
  exit_RV_s (RI3P OK) E k L A G out es hj dels adds L' A' qs.
Proof. intros H HO. unfold exit_RV_s in *. intros. split; [eapply H; eassumption|exact HO]. Qed.

Lemma rp_reset_RV OK E k L A G out es hj h L' A' qs :
  reset_RV_s RI3_reply E k L A G out es hj h L' A' qs -> OK A' ->
  reset_RV_s (RI3P OK) E k L A G out es hj h L' A' qs.
Proof. intros H HO. unfold reset_RV_s in *. intros. split; [eapply H; eassumption|exact HO]. Qed.

Lemma rp_fin_RV OK E k L A G out es hj live mx CAP L' A' qs :
  fin_RV_d RI3_reply E k L A G out es hj live mx CAP L' A' qs -> OK A' ->
  fin_RV_d (RI3P OK) E k L A G out es hj live mx CAP L' A' qs.
Proof. intros H HO. unfold fin_RV_d in *. intros. split; [eapply H; eassumption|exact HO]. Qed.

Lemma rp_mallocs_peak ns : Forall (fun n => 0 <= n <= NMAX) ns -> (length ns <= 2)%nat ->
  tr_peak (map RMalloc ns) (2 * NMAX).
Proof.
  intros Hns Hlen. destruct ns as [|n1 [|n2 [|n3 ns]]]; cbn [map]; [apply tr_peak_nil| | |cbn [length] in Hlen; lia].
  - apply Forall_cons_iff in Hns as [H1 _]. apply tr_peak_cons. cbv beta iota. cbn [ev_db].
    split; [lia|apply tr_peak_nil].
  - apply Forall_cons_iff in Hns as [H1 Hns]. apply Forall_cons_iff in Hns as [H2 _].
    apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|].
    apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|apply tr_peak_nil].
Qed.

Lemma rp_fch_peak M cap a j tr cap' a' : fch M cap a j tr cap' a' -> M <= NMAX ->
  forall Bd, 2 * M - cap <= Bd -> tr_peak tr Bd.
Proof.
  intros H HM. induction H as [cap a j|cap a j c tr cap' a' Hc HcM Hch IH|cap a j n x tr cap' a' Hn Hch IH];
    intros Bd HB; [apply tr_peak_nil| |].
  - destruct (Z.eqb_spec cap 0) as [E0|E0]; apply tr_peak_cons; cbv beta iota; cbn [ev_db];
      (split; [lia|apply IH; lia]).
  - apply tr_peak_cons. cbv beta iota. split; [exact I|]. cbn [ev_db]. apply IH. lia.
Qed.

Theorem rp_mallocs_res3 OK RM E k k' V L A ns : RMH RM -> RI3P OK E k V L A ->
  Forall (fun n => 0 <= n <= NMAX) ns -> (length ns <= 2)%nat ->
  res_tr (pack3P OK RM) (fun L' A' qs => forall V' adds, map snd adds = ns -> nc_move V L A V' L' A' [] adds ->
      List.NoDup (map fst (blocks L' A')) -> ptr_keep [] V L A V' L' A' -> (length (rv_nc V') <= NC_MAX)%nat ->
      ncs V' L' A' <= rv_wt V' -> rv_wt V' <= rv_wt V + DATA_PER * (cdat (ss_pl E) k' - cdat (ss_pl E) k) ->
      cred3 (ss_pl E) k k' V V' [] -> Forall (fun n => 0 <= n) (rv_ek V') -> RI3P OK E k' V' L' A')
    A (map RMalloc ns).
Proof.
  intros HRM ((b & al & alb & HR & HL) & HOK) Hns Hlen. pose proof HL as (HCs & HMc & _ & HlL & _).
  pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL) as HBy. pose proof rp_bytes_room as X.
  assert (Hns0 : Forall (fun n => 0 <= n) ns)
    by (rewrite Forall_forall in *; intros n Hn; pose proof (Hns n Hn); lia).
  exists b. split; [split; [exact HR|exact HOK]|]. split.
  - intros qs _. apply (proj2 (roomF_pack3P OK RM qs b _)). split.
    + rewrite roomF3. exact (mallocs_room _ _ _ _ _ _ b al alb qs ns HL Hns Hlen).
    + apply (RMrun_of_peak RM (ss_pl E) b _ (2 * NMAX) HRM HCs HMc); [lia|exact (rp_mallocs_peak ns Hns Hlen)].
  - intros L' A' qs _ (HA' & HOK') V' adds Hsnd HM HND HK HN' HW1 HW HCR HE'. split; [|exact HOK'].
    rewrite runF_pack3P, runF3 in HA'.
    destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
    apply (step3 E k k' V L A b al alb V' L' A' (run3 qs b 0 (map RMalloc ns)) [] (dl_of [] adds) (db_of [] adds)
      [] (inplace qs 0 (map RMalloc ns)) HL HR (Forall_nil _) HA'); try assumption.
    + apply run3_cap.
    + apply run3_mcap.
    + rewrite run3_len. exact HlL.
    + intros c Hc. rewrite (run3_live qs b 0 _ c HlL (mallocs_ok ns Hns0) Hc), tr_dl_mallocs, dl_adds, Hsnd.
      change (bcnt c []) with 0. lia.
    + rewrite run3_bytes, tr_db_mallocs, db_adds, Hsnd, zsum_nil. lia.
    + intros e He. exact (mis_nil_D qs b 0 _ L e He).
    + intros p Hp. exfalso. exact (mallocs_inplace qs 0 ns p Hp).
    + change (zlen []) with 0. lia.
Qed.

Theorem rp_push_res3 OK RM E k k' V L A l (x : list Z) : RMH RM ->
  RI3P OK E k V L A -> List.NoDup (map fst (blocks L A)) -> 0 <= hl_n l <= hl_cap l -> hl_cap l <= 2 * OPS_MAX ->
  1 <= Z.of_nat (length x) <= WRITE_MAX ->
  res_tr (pack3P OK RM) (fun L' A' qs => forall V' q1,
      (hl_n l = hl_cap l -> ptr_addr L' (resolveF qs (Ret 0)) = q1) ->
      nc_move V L A V' L' A' (grow_dels (hl_v l) (hl_n l) (hl_cap l)) (grow_adds q1 (hl_n l) (hl_cap l)) ->
      List.NoDup (map fst (blocks L' A')) -> ptr_keep (grow_dels (hl_v l) (hl_n l) (hl_cap l)) V L A V' L' A' ->
      (length (rv_nc V') <= NC_MAX)%nat ->
      ncs V' L' A' <= rv_wt V' ->
      rv_wt V' <= rv_wt V + NC_PER * zlen [Z.of_nat (length x) + 1] +
        DATA_PER * (cdat (ss_pl E) k' - cdat (ss_pl E) k) ->
      cred3 (ss_pl E) k k' V V' [Z.of_nat (length x) + 1] -> Forall (fun n => 0 <= n) (rv_ek V') ->
      RI3P OK E k' V' L' A')
    A (list_push_tr (sh_of (known_at L A) l) x).
Proof.
  intros HRM ((b & al & alb & HR & HL) & HOK) HND0 HN HC Hx. pose proof HL as (HCs & HMc & _ & HlL & _).
  assert (Hn1 : 0 <= Z.of_nat (length x) + 1 <= NMAX) by (unfold NMAX, WRITE_MAX in *; lia).
  assert (Hks : Forall (fun n => 0 <= n) [Z.of_nat (length x) + 1]) by (repeat constructor; lia).
  assert (HBd : p3_bytes b + 2 * NMAX <= CF_MAX)
    by (pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL); pose proof rp_bytes_room; lia).
  assert (HNM : 128 <= NMAX) by (unfold NMAX; lia).
  rewrite push_tr. exists b. split; [split; [exact HR|exact HOK]|].
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [ENC|ENC]; [destruct (Z.eqb_spec (hl_cap l) 0) as [EC0|EC0]|];
    cbn [app].
  - split.
    + intros qs _. apply (proj2 (roomF_pack3P OK RM qs b _)). split.
      * rewrite roomF3. cbn [room_from].
        split; [apply (room3_rIv _ _ _ _ _ _ b al alb b 128 HL (rIv_refl b)); unfold NMAX; lia|].
        split; [|exact I]. apply (room3_rIv _ _ _ _ _ _ b al alb (pb3_malloc b 128) _ HL); [|exact Hn1].
        apply rIv_malloc; [exact HlL|unfold NMAX; lia].
      * apply (RMrun_of_peak RM (ss_pl E) b _ (2 * NMAX) HRM HCs HMc HBd).
        apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|].
        apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|apply tr_peak_nil].
    + intros L' A' qs _ (HA' & HOK') V' q1 Hlink HM HND HK HN' HW1 HW HCR HE'. split; [|exact HOK'].
      rewrite runF_pack3P, runF3 in HA'.
      assert (ED : grow_dels (hl_v l) (hl_n l) (hl_cap l) = []) by (unfold grow_dels; rewrite ENC, EC0; reflexivity).
      assert (EA : grow_adds q1 (hl_n l) (hl_cap l) = [(q1, 128)])
        by (unfold grow_adds; rewrite ENC, EC0; reflexivity).
      rewrite ED, EA in HM. rewrite ED in HK. destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
      apply (step3 E k k' V L A b al alb V' L' A' _ [Z.of_nat (length x) + 1] (dl_of [] [(q1, 128)])
        (db_of [] [(q1, 128)]) [] (inplace qs 0 [RMalloc 128; RMalloc (Z.of_nat (length x) + 1)]) HL HR Hks HA');
        try assumption.
      * apply run3_cap.
      * apply run3_mcap.
      * rewrite run3_len. exact HlL.
      * intros c Hc. rewrite (run3_live qs b 0 _ c HlL) by (first [exact Hc | repeat constructor; cbn [ev_ok]; lia]).
        unfold tr_dl, dl_of, bcnt. rewrite !zsum_cons, !zsum_nil. cbn [ev_dl snd]. lia.
      * rewrite run3_bytes. unfold tr_db, db_of. rewrite !zsum_cons, !zsum_nil. cbn [ev_db snd]. lia.
      * intros e He. exact (mis_nil_D qs b 0 _ L e He).
      * intros p Hp. cbn [inplace] in Hp. contradiction.
  - assert (H32 : 0 <= 32 * hl_cap l <= NMAX) by (unfold NMAX, OPS_MAX in *; lia).
    split.
    + intros qs _. apply (proj2 (roomF_pack3P OK RM qs b _)). split.
      * rewrite roomF3. cbn [room_from].
        split; [exact (room3_rIv _ _ _ _ _ _ b al alb b _ HL (rIv_refl b) H32)|].
        split; [|exact I]. apply (room3_rIv _ _ _ _ _ _ b al alb _ _ HL); [|exact Hn1].
        apply rIv_realloc; [exact HlL|lia|unfold NMAX, OPS_MAX in *; lia].
      * apply (RMrun_of_peak RM (ss_pl E) b _ (2 * NMAX) HRM HCs HMc HBd).
        apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|].
        apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|apply tr_peak_nil].
    + intros L' A' qs _ (HA' & HOK') V' q1 Hlink HM HND HK HN' HW1 HW HCR HE'. split; [|exact HOK'].
      rewrite runF_pack3P, runF3 in HA'.
      assert (ED : grow_dels (hl_v l) (hl_n l) (hl_cap l) = [(hl_v l, 16 * hl_cap l)]).
      { unfold grow_dels. rewrite ENC, Z.eqb_refl, (proj2 (Z.eqb_neq (hl_cap l) 0) EC0). reflexivity. }
      assert (EA : grow_adds q1 (hl_n l) (hl_cap l) = [(q1, 32 * hl_cap l)]).
      { unfold grow_adds. rewrite ENC, Z.eqb_refl, (proj2 (Z.eqb_neq (hl_cap l) 0) EC0). reflexivity. }
      rewrite ED, EA in HM. rewrite ED in HK. destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
      apply (step3 E k k' V L A b al alb V' L' A' _ [Z.of_nat (length x) + 1]
        (dl_of [(hl_v l, 16 * hl_cap l)] [(q1, 32 * hl_cap l)]) (db_of [(hl_v l, 16 * hl_cap l)] [(q1, 32 * hl_cap l)])
        [(hl_v l, 16 * hl_cap l)]
        (inplace qs 0 [RRealloc (16 * hl_cap l) (32 * hl_cap l) (known_at L A (hl_v l)); RMalloc (Z.of_nat (length x) + 1)])
        HL HR Hks HA'); try assumption.
      * apply run3_cap.
      * apply run3_mcap.
      * rewrite run3_len. exact HlL.
      * intros c Hc. rewrite (run3_live qs b 0 _ c HlL) by (first [exact Hc | repeat constructor; cbn [ev_ok]; lia]).
        unfold tr_dl, dl_of, bcnt. rewrite !zsum_cons, !zsum_nil. cbn [ev_dl snd]. lia.
      * rewrite run3_bytes. unfold tr_db, db_of. rewrite !zsum_cons, !zsum_nil. cbn [ev_db snd]. lia.
      * intros e He. apply (mis_D L A qs b 0 _ [(hl_v l, 16 * hl_cap l)] e HR); [|exact He].
        apply (touched_at L A qs _ _ HND0). intros y [Ey|[]]. cbn [fst] in Ey. subst y.
        exact (touched_realloc qs _ (16 * hl_cap l) (32 * hl_cap l) (known_at L A (hl_v l)) (in_eq _ _)).
      * intros p Hp. cbn [inplace] in Hp. destruct Hp as [(_ & Ep)|[]]. rewrite Ep.
        change (nth 0 qs (SP 0 0)) with (resolveF qs (Ret 0)). rewrite (Hlink ENC).
        apply (nc_move_adds_in _ _ _ _ _ _ _ _ (q1, 32 * hl_cap l) HM). left. reflexivity.
  - split.
    + intros qs _. apply (proj2 (roomF_pack3P OK RM qs b _)). split.
      * rewrite roomF3. cbn [room_from]. split; [|exact I].
        exact (room3_rIv _ _ _ _ _ _ b al alb b _ HL (rIv_refl b) Hn1).
      * apply (RMrun_of_peak RM (ss_pl E) b _ (2 * NMAX) HRM HCs HMc HBd).
        apply tr_peak_cons. cbv beta iota. cbn [ev_db]. split; [lia|apply tr_peak_nil].
    + intros L' A' qs _ (HA' & HOK') V' q1 Hlink HM HND HK HN' HW1 HW HCR HE'. split; [|exact HOK'].
      rewrite runF_pack3P, runF3 in HA'.
      assert (ED : grow_dels (hl_v l) (hl_n l) (hl_cap l) = [])
        by (unfold grow_dels; rewrite (proj2 (Z.eqb_neq _ _) ENC); reflexivity).
      assert (EA : grow_adds q1 (hl_n l) (hl_cap l) = [])
        by (unfold grow_adds; rewrite (proj2 (Z.eqb_neq _ _) ENC); reflexivity).
      rewrite ED, EA in HM. rewrite ED in HK. destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
      apply (step3 E k k' V L A b al alb V' L' A' _ [Z.of_nat (length x) + 1] (dl_of [] []) (db_of [] [])
        [] (inplace qs 0 [RMalloc (Z.of_nat (length x) + 1)]) HL HR Hks HA'); try assumption.
      * apply run3_cap.
      * apply run3_mcap.
      * rewrite run3_len. exact HlL.
      * intros c Hc. rewrite (run3_live qs b 0 _ c HlL) by (first [exact Hc | repeat constructor; cbn [ev_ok]; lia]).
        unfold tr_dl, dl_of, bcnt. rewrite !zsum_cons, !zsum_nil. cbn [ev_dl snd]. lia.
      * rewrite run3_bytes. unfold tr_db, db_of. rewrite !zsum_cons, !zsum_nil. cbn [ev_db snd]. lia.
      * intros e He. exact (mis_nil_D qs b 0 _ L e He).
      * intros p Hp. cbn [inplace] in Hp. contradiction.
Qed.

Theorem rp_fin_res3 OK RM E k L A G out es hj live mx CAP : RMH RM ->
  RI3P OK E k (view_of G out es hj) L A -> List.NoDup (map fst (blocks L A)) -> 0 <= mx -> 0 <= CAP ->
  Forall (fun e => 0 <= re_cap e /\ (re_hp e <> 0 -> 0 <= re_kh e)) es -> entries_total es < INPUT_MAX ->
  res_tr (pack3P OK RM) (fin_RV_d (RI3P OK) E k L A G out es hj live mx CAP) A
    (relay_finish_tr (known_at L A) live mx 0 CAP es 0 (known_at L A out)).
Proof.
  intros HRM ((b & al & alb & HR & HL) & HOK) HND0 Hmx HC He Htot.
  pose proof HL as (HCs & HMc & _ & HlL & _).
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HU & _) & _).
  pose proof (fch_finish (known_at L A) live mx CAP es (known_at L A out) Hmx HC He) as Hch.
  assert (HMx : 2 * entries_total es <= NMAX) by (unfold INPUT_MAX, NMAX in *; pose proof (entries_total_nonneg es); lia).
  assert (HBd : p3_bytes b + 2 * NMAX <= CF_MAX)
    by (pose proof (ledger3_bytes _ _ _ _ _ _ _ _ _ HL); pose proof rp_bytes_room; lia).
  exists b. split; [split; [exact HR|exact HOK]|]. split.
  - intros qs _. apply (proj2 (roomF_pack3P OK RM qs b _)). split.
    + rewrite roomF3.
      refine (fch_room qs b CAP (2 * entries_total es) room_pack3 _ _ _ _ _ _ _ Hch b [] (fI_init qs b CAP _ HC HlL)).
      intros bc cap0 a0 t0 c HI Hc HcM. apply (room3_rIv _ _ _ _ _ _ b al alb bc c HL); [|lia].
      apply (fI_rIv qs b CAP bc cap0 a0 t0 HI). lia.
    + apply (RMrun_of_peak RM (ss_pl E) b _ (2 * NMAX) HRM HCs HMc HBd).
      apply (rp_fch_peak _ _ _ _ _ _ _ Hch); lia.
  - intros L' A' qs _ (HA' & HOK'). rewrite runF_pack3P, runF3 in HA'. apply rp_fin_RV; [|exact HOK']. hnf.
    intros G' out' es' hj' Hcov Hp Hek Hes Hhj q1 Hq1 Hlink HM HND HK HWs HWg.
    pose proof (fch_run qs b CAP _ _ _ _ _ _ _ Hch b [] (fI_init qs b CAP _ HC HlL)) as HI. cbn [app] in HI.
    destruct HI as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9).
    destruct (nc_move_grow3 _ _ _ _ _ _ _ _ HM) as (G1 & G2).
    pose proof (out_db3 out CAP q1 (relay_finish_cap live mx 0 CAP es)) as OB.
    pose proof (fin_dels (fun n => n) (known_at L A) live mx (fun x Hx => Hx) es 0 CAP 0 (known_at L A out) He) as FB.
    cbv beta in FB. change (zsum (fun t => snd t) (ent_dels es)) with (zsum snd (ent_dels es)) in FB.
    apply (step3 E k k _ L A b al alb _ L' A' _ []
      (dl_of (out_move_dels out CAP q1 (relay_finish_cap live mx 0 CAP es) ++ ent_dels es)
        (out_move_adds out CAP q1 (relay_finish_cap live mx 0 CAP es)))
      (db_of (out_move_dels out CAP q1 (relay_finish_cap live mx 0 CAP es) ++ ent_dels es)
        (out_move_adds out CAP q1 (relay_finish_cap live mx 0 CAP es)))
      (out_move_dels out CAP q1 (relay_finish_cap live mx 0 CAP es) ++ ent_dels es)
      (fun p => live = true /\ out_same out CAP q1 (relay_finish_cap live mx 0 CAP es) = false /\
         p = resolveF qs (relay_finish_out (known_at L A) live mx 0 CAP es 0 (known_at L A out)))
      HL HR (Forall_nil _) HA' I1 I2 I3).
    + intros c Hc. rewrite (I4 c Hc). change (bcnt c []) with 0.
      pose proof (out_dl3 c out CAP q1 (relay_finish_cap live mx 0 CAP es)) as OD.
      pose proof (fin_dels (fun n => one_if c (band n)) (known_at L A) live mx (fun x _ => proj1 (one_if_b c (band x)))
        es 0 CAP 0 (known_at L A out) He) as FD.
      unfold dl_of. rewrite zsum_app. unfold bcnt, relay_finish_tr. cbv beta in FD. lia.
    + rewrite I5. unfold db_of. rewrite zsum_app. unfold relay_finish_tr. rewrite zsum_nil. lia.
    + intros e He'.
      assert (UC : In e (p3_mis b) ->
          ~ touched qs (relay_finish_tr (known_at L A) live mx 0 CAP es 0 (known_at L A out)) (fst e) ->
          (In e (p3_mis b) /\ ~ In (ptr_addr L (fst e))
             (map fst (out_move_dels out CAP q1 (relay_finish_cap live mx 0 CAP es) ++ ent_dels es))) \/
          (live = true /\ out_same out CAP q1 (relay_finish_cap live mx 0 CAP es) = false /\
           fst e = resolveF qs (relay_finish_out (known_at L A) live mx 0 CAP es 0 (known_at L A out)))).
      { intros Hm Hu.
        destruct (in_dec Z.eq_dec (ptr_addr L (fst e)) (map fst (out_move_dels out CAP q1
          (relay_finish_cap live mx 0 CAP es) ++ ent_dels es))) as [Hx|Hx]; [|left; split; assumption].
        destruct (HU e Hm) as (_ & n & Hn). pose proof (sptr_of_at L A (fst e) n HND0 Hn) as Es.
        rewrite map_app, in_app_iff in Hx. destruct Hx as [Hx|Hx].
        - unfold out_move_dels in Hx. revert Hx.
          destruct (out_same out CAP q1 (relay_finish_cap live mx 0 CAP es)) eqn:Os; cbn [orb]; [intros []|].
          destruct (Z.eqb_spec CAP 0) as [C0|C0]; cbn [map fst]; [intros []|]. intros [Ex|[]].
          destruct live eqn:Lv; subst live.
          + right. split; [reflexivity|]. split; [reflexivity|].
            destruct (Z.eq_dec (relay_finish_cap true mx 0 CAP es) CAP) as [Ec|Ec].
            * rewrite (fch_nogrow _ _ _ _ _ _ _ Hch Ec). cbn [resolve known_at]. rewrite Ex. symmetry. exact Es.
            * exfalso. destruct (fch_first _ _ _ _ _ _ _ Hch C0 Ec) as (c & Hin). apply Hu.
              rewrite <- Es, <- Ex. exact (touched_realloc qs _ _ _ _ Hin).
          + exfalso. rewrite (Hq1 eq_refl), fin_cap_off in Os. unfold out_same in Os.
            rewrite !Z.eqb_refl in Os. discriminate Os.
        - exfalso. destruct (fin_free_at (known_at L A) live mx es 0 CAP 0 (known_at L A out) _ Hx) as (m & Hin).
          apply Hu. rewrite <- Es. exact (touched_free qs _ _ _ Hin). }
      destruct (I9 e He') as [(Hc0 & Ef & Hcc)|(Hm & Hu)]; [|exact (UC Hm Hu)].
      destruct (Z.eq_dec (relay_finish_cap live mx 0 CAP es) CAP) as [Ec|Ec].
      * destruct (Hcc Ec) as (Hm & Hu). exact (UC Hm Hu).
      * right. destruct live eqn:Lv; subst live; [|exfalso; exact (Ec (fin_cap_off mx es 0 CAP))].
        split; [reflexivity|]. split; [|exact Ef]. unfold out_same. rewrite (proj2 (Z.eqb_neq _ _) Ec).
        apply andb_false_r.
    + intros p (Hlv & Hos & ->). rewrite (proj2 (Hlink Hlv)).
      apply (nc_move_adds_in _ _ _ _ _ _ _ _ (q1, relay_finish_cap live mx 0 CAP es) HM).
      unfold out_move_adds. rewrite Hos. left. reflexivity.
    + exact HND.
    + exact HK.
    + exact (nc_len G' out' es' hj' Hes Hhj).
    + exact G1.
    + exact G2.
    + exact HWs.
    + rewrite !wt_view. change (zlen []) with 0. lia.
    + exact (cred_same E k G out es hj G' out' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
Qed.

Theorem entry_res_reply_RI3P OK RM : RMH RM -> entry_add_resources_s (pack3P OK RM) (RI3P OK).
Proof.
  intros HRM E L A C G OUT HRI HC.
  assert (CR : forall G' OUT' es' hj', pend_view hj' = [[]] -> ek_view hj' = [] ->
      cred3 (ss_pl E) 0 0 (RV [] [G; OUT] NC_FIX []) (view_of G' OUT' es' hj') []).
  { intros G' OUT' es' hj' Hp Hek. split.
    - intros c Hc. rewrite ek_view_c, Hek. change (rv_pend (view_of G' OUT' es' hj')) with (pend_view hj'). rewrite Hp.
      change (bcnt c []) with 0. change (prom_c [[]] c) with 0. change (ek_c (RV [] [G; OUT] NC_FIX []) c) with 0.
      change (prom_c (rv_pend (RV [] [G; OUT] NC_FIX [])) c) with 0. rewrite zsum_nil. lia.
    - rewrite ek_view_b, Hek. change (rv_pend (view_of G' OUT' es' hj')) with (pend_view hj'). rewrite Hp.
      change (promb [[]]) with 0. change (ek_b (RV [] [G; OUT] NC_FIX [])) with 0.
      change (promb (rv_pend (RV [] [G; OUT] NC_FIX []))) with 0. rewrite !zsum_nil. lia. }
  destruct HC as [-> | ->].
  - change (op_add_tr (Some 0%nat) FIRST_FD 0 0 (known_at L A G)) with (map (@RMalloc sptr) [PARTIAL_BYTES; SRC_TABLE]).
    apply (res_tr_weaken _ _ _ _ _ (rp_mallocs_res3 OK RM E 0 0 _ L A [PARTIAL_BYTES; SRC_TABLE] HRM HRI
      ltac:(repeat constructor; unfold PARTIAL_BYTES, SRC_TABLE, SRC_ENTRY, NMAX; lia) ltac:(cbn; lia))).
    intros L' A' qs HP q g _ _ G' OUT' es' hj' Hcov Hp Hek Hes HM HND HK HWs HWg.
    apply (HP (view_of G' OUT' es' hj') (entry_adds q g 0) eq_refl HM HND HK
      (nc_len G' OUT' es' hj' Hes (pend_len hj' Hp)) HWs).
    + change (rv_wt (view_of G' OUT' es' hj')) with (nc_wt es' hj'). change (rv_wt (RV [] [G; OUT] NC_FIX [])) with NC_FIX.
      lia.
    + exact (CR G' OUT' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
  - change (op_add_tr (Some 0%nat) FIRST_FD 0 16 (known_at L A G)) with (map (@RMalloc sptr) [PARTIAL_BYTES]).
    apply (res_tr_weaken _ _ _ _ _ (rp_mallocs_res3 OK RM E 0 0 _ L A [PARTIAL_BYTES] HRM HRI
      ltac:(repeat constructor; unfold PARTIAL_BYTES, NMAX; lia) ltac:(cbn; lia))).
    intros L' A' qs HP q g _ _ G' OUT' es' hj' Hcov Hp Hek Hes HM HND HK HWs HWg.
    apply (HP (view_of G' OUT' es' hj') (entry_adds q g 16) eq_refl HM HND HK
      (nc_len G' OUT' es' hj' Hes (pend_len hj' Hp)) HWs).
    + change (rv_wt (view_of G' OUT' es' hj')) with (nc_wt es' hj'). change (rv_wt (RV [] [G; OUT] NC_FIX [])) with NC_FIX.
      lia.
    + exact (CR G' OUT' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
Qed.

Theorem push_res_reply_RI3P OK RM : RMH RM -> push_resources_s (pack3P OK RM) (RI3P OK).
Proof.
  intros HRM E k k' L A l tx G out es hj HRI HND0 HN HNo HC Hn Hk' Hkn.
  assert (Hlx : length (bzs tx) = length tx) by (unfold bzs; apply length_map).
  pose proof (rp_push_res3 OK RM E k k' (view_of G out es hj) L A l (bzs tx) HRM HRI HND0 HN HC
    ltac:(rewrite Hlx; exact Hn)) as R.
  rewrite Hlx in R. apply (res_tr_weaken _ _ _ _ _ R).
  intros L' A' qs HP. hnf.
  intros l' Hreal _ G' out' es' hj' Hcov (p1 & xx & p2 & txt & Hp & Hp' & Hxx & Ht & Hin) Hek Hes Hhj HM HND HK
    HWs HWg.
  assert (Hz : zlen (plz txt) = Z.of_nat (length tx)) by (unfold zlen, plz; rewrite length_map; exact Ht).
  assert (Hend : k < ck_end (CK 1 (k' - Z.of_nat (length tx)) (plz txt)) <= k')
    by (unfold ck_end; cbn [ck_at ck_data]; lia).
  apply (HP (view_of G' out' es' hj') (hl_v l') (fun EN => push_link L' qs (known_at L A) l (bzs tx) l' EN Hreal)
    HM HND HK (nc_len G' out' es' hj' Hes Hhj) HWs).
  - change (rv_wt (view_of G' out' es' hj')) with (nc_wt es' hj'). change (rv_wt (view_of G out es hj)) with (nc_wt es hj).
    pose proof (cdat_chunk (ss_pl E) k k' _ Hin eq_refl Hend) as CD. cbn [ck_data] in CD. rewrite Hz in CD.
    change (zlen [Z.of_nat (length tx) + 1]) with 1. unfold NC_PER, DATA_PER in *. lia.
  - split.
    + intros c Hc. rewrite !ek_view_c, Hek. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
      change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp', prom_c_push, <- Hp.
      pose proof (cons_chunk (ss_pl E) k k' _ c Hin eq_refl Hend) as C1. rewrite ckw_push, Hz in C1.
      rewrite bcnt_cons. change (bcnt c []) with 0. lia.
    + rewrite !ek_view_b, Hek. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
      change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp', promb_push, <- Hp.
      pose proof (consb_chunk (ss_pl E) k k' _ Hin eq_refl Hend) as C2. rewrite cmass_push, Hz in C2.
      rewrite zsum_cons, zsum_nil. lia.
  - exact (ek_view_nonneg hj').
Qed.

Definition op0_res_sP (F : ResFormT) (RI : res_inv) : Prop :=
  forall E k L A i FD N G out es hj, RI E k (view_of G out es hj) L A -> 0 < k <= ss_n E ->
    op_at E (k - 1) = 0 -> (i <> None -> 0 <= N < 4) ->
    res_tr F (op0_RV_s RI E k L A G out es hj i FD N) A (op_add_tr i FD N 16 (known_at L A G)).

Theorem op0_res_reply_RI3P OK RM : RMH RM -> op0_res_sP (pack3P OK RM) (RI3P OK).
Proof.
  intros HRM E k L A i FD N G out es hj HRI Hk Hop HN.
  assert (CR : forall G' out' es' hj', pend_view hj' = pend_view hj ++ op0_pend i -> ek_view hj' = ek_view hj ->
      cred3 (ss_pl E) k k (view_of G out es hj) (view_of G' out' es' hj') []).
  { intros G' out' es' hj' Hp Hek.
    assert (Z0 : forall c, prom_c (op0_pend i) c = 0) by (intros c; destruct i; reflexivity).
    assert (Z1 : promb (op0_pend i) = 0) by (destruct i; reflexivity).
    split.
    - intros c Hc. rewrite !ek_view_c, Hek. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
      change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp, prom_c_app, Z0.
      change (bcnt c []) with 0. lia.
    - rewrite !ek_view_b, Hek. change (rv_pend (view_of G' out' es' hj')) with (pend_view hj').
      change (rv_pend (view_of G out es hj)) with (pend_view hj). rewrite Hp, promb_app, Z1, zsum_nil. lia. }
  rewrite (op0_tr i FD N (known_at L A G) HN). destruct i as [i0|].
  - change [RMalloc PARTIAL_BYTES] with (map (@RMalloc sptr) [PARTIAL_BYTES]).
    apply (res_tr_weaken _ _ _ _ _ (rp_mallocs_res3 OK RM E k k _ L A [PARTIAL_BYTES] HRM HRI
      ltac:(repeat constructor; unfold PARTIAL_BYTES, NMAX; lia) ltac:(cbn; lia))).
    intros L' A' qs HP q _. hnf. intros G' out' es' hj' Hcov Hp Hek Hes Hhj HM HND HK HWs HWg.
    apply (HP (view_of G' out' es' hj') (op0_adds q (Some i0)) eq_refl HM HND HK (nc_len G' out' es' hj' Hes Hhj) HWs).
    + change (rv_wt (view_of G' out' es' hj')) with (nc_wt es' hj'). change (rv_wt (view_of G out es hj)) with (nc_wt es hj).
      lia.
    + exact (CR G' out' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
  - apply (res_tr_weaken _ _ _ _ _ (rp_mallocs_res3 OK RM E k k _ L A [] HRM HRI (Forall_nil _) ltac:(cbn; lia))).
    intros L' A' qs HP q _. hnf. intros G' out' es' hj' Hcov Hp Hek Hes Hhj HM HND HK HWs HWg.
    apply (HP (view_of G' out' es' hj') (op0_adds q None) eq_refl HM HND HK (nc_len G' out' es' hj' Hes Hhj) HWs).
    + change (rv_wt (view_of G' out' es' hj')) with (nc_wt es' hj'). change (rv_wt (view_of G out es hj)) with (nc_wt es hj).
      lia.
    + exact (CR G' out' es' hj' Hp Hek).
    + exact (ek_view_nonneg hj').
Qed.

Theorem exit_res_ends_RI3P OK RM : RMH RM -> exit_res_ends_s (pack3P OK RM) (RI3P OK) CS_reply.
Proof.
  intros _ B API LS SH SK ra empty rc fx j E HF k L A gone rs d G out es hj (HRI & HOK) Hg Hrs Hnd.
  apply (res_tr_weaken _ _ _ _ _ (rp_frees_lift OK RM _ A _ HOK (proj1 (ends_free (known_at L A) gone [] rs d))
    (exit_res_ends_reply_s B API LS SH SK ra empty rc fx j E HF k L A gone rs d G out es hj HRI Hg Hrs Hnd))).
  intros L' A' qs (H & HO). apply rp_exit_RV; assumption.
Qed.

Theorem exit_res_reset_RI3P OK RM : RMH RM -> exit_res_reset_s (pack3P OK RM) (RI3P OK) CS_reply.
Proof.
  intros _ B API LS SH SK ra empty rc fx j E HF k L A G out es hj (HRI & HOK) HND0.
  destruct (exit_res_reset_reply_s B API LS SH SK ra empty rc fx j E HF k L A G out es hj HRI HND0) as (H1 & H2).
  split.
  - apply (res_tr_weaken _ _ _ _ _ (rp_frees_lift OK RM _ A _ HOK (Forall_nil _) H1)).
    intros L' A' qs (H & HO). apply rp_exit_RV; assumption.
  - intros mem HA h Hsrc.
    apply (res_tr_weaken _ _ _ _ _ (rp_frees_lift OK RM _ A _ HOK (reset_free (known_at L A) h) (H2 mem HA h Hsrc))).
    intros L' A' qs (H & HO). apply rp_reset_RV; assumption.
Qed.

Theorem exit_res_fin_RI3P OK RM : RMH RM -> exit_res_fin_d (pack3P OK RM) (RI3P OK) CS_reply.
Proof.
  intros HRM B API LS SH SK ra empty rc fx j E HF k L A cl br dd G mx cap out es hj HRI HND Hes Htot.
  pose proof (bv_unsigned_in_range _ cap) as [HCAP _]. pose proof (bv_unsigned_in_range _ mx) as [HMX _].
  exact (rp_fin_res3 OK RM E k L A G (bv_unsigned out) es hj _ (bv_unsigned mx) (bv_unsigned cap) HRM HRI HND HMX HCAP
    Hes Htot).
Qed.
