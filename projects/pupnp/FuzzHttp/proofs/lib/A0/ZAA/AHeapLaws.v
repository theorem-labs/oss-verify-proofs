(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_quar_P AQuarT AQuarU F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null ALedger F_alloc_env AHeap2 F_sec_B AFsEnv AFteF.
Import ListNotations.
Open Scope Z_scope.

Section LAWS.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Hypothesis AO : alayout_ok AL.
Notation L := (al_thread AL).

#[using="AO"] Lemma law_stack_ok : alloc_ceiling - 160 <= at_bottom L < alloc_ceiling + 4096 /\ at_bottom L + 2^23 = at_top L /\ at_top L <= 2^47 /\ at_top L mod 4096 = 0.
Proof. pose proof AO as (_ & _ & _ & TLO & _). unfold thread_layout_ok in TLO. tauto. Qed.

#[using="Type"] Lemma law_heap_perm : forall s LB LB' m, RHEAP_B AL E s LB m -> Permutation LB LB' -> RHEAP_B AL E s LB' m.
Proof.
  intros s LB LB' m R P. unfold RHEAP_B in *. cbv zeta in *. destruct R as (R1 & R2). split; [| exact R2].
  eapply Permutation_trans; [apply Permutation_sym; exact P| exact R1].
Qed.

Ltac rheapB R :=
  unfold RHEAP_B in R; cbv zeta in R;
  destruct R as (R_PERM & R_LR & R_AO & R_DR & R_QL & R_GQ & R_QC & R_MTX & R_QE & R_QWF & R_DEP & R_DOK
                 & R_WF & R_REP & R_HK & R_SECP & R_COV & R_TE2 & R_HE & R_TRE & R_AENV & R_IA & R_CLS & R_QCLS & R_SLK & R_BUD & R_FTE).

#[using="Type"] Lemma live_of_block : forall s LB m b, RHEAP_B AL E s LB m -> In b LB ->
  exists r, In r (bs_live s) /\ b = blk_ofB AL r /\ lr_ok r /\ qchunk_wf (fst r) /\ lchunk_rep AL m (fst r) /\ held_kind (bs_X s) (fst r) /\ ch_cls_ok (fst r).
Proof.
  intros s LB m b R HIN. rheapB R.
  pose proof (Permutation_in _ R_PERM HIN) as HM. apply in_map_iff in HM as (r & <- & HR). exists r.
  assert (HL : In (fst r) (live_chunks s)) by (unfold live_chunks; apply in_map; exact HR).
  split; [exact HR|]. split; [reflexivity|]. split; [exact (proj1 (Forall_forall _ _) R_LR r HR)|].
  split; [exact (proj1 (Forall_forall _ _) R_WF _ HL)|]. split; [exact (proj1 (Forall_forall _ _) R_REP _ HL)|].
  split; [exact (proj1 (Forall_forall _ _) R_HK _ HL)| exact (proj1 (Forall_forall _ _) R_CLS _ HL)].
Qed.

Definition lsec_slack (ch : qchunk) : Prop :=
  match qc_kind ch with QPrim _ _ => True | QSec _ => qc_rz ch + rup8 (qc_n ch) + 16 <= qc_bsize ch end.

Variable FI : fs_if.
Hypothesis FSBE : FSB FI = al_fsb AL.

#[using="AO FSBE"] Lemma live_geo : forall X (m : mem) ch, RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch -> qchunk_wf ch -> lsec_slack ch ->
  let A := lc_user AL ch in let n := qc_n ch in
  0 < A /\ A mod 16 = 0 /\ A + n + 16 <= alloc_ceiling /\ 0x609000 <= A
  /\ (A + n + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= A)
  /\ (A + n <= FSB FI \/ FSB FI + A0_FS_SIZE <= A)
  /\ qc_blk AL ch + 16 <= A /\ A + rup8 n <= qc_blk AL ch + qc_bsize ch.
Proof.
  intros X m ch RP RS HK WF SL A n. destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  pose proof AO as (_ & _ & SP16 & _).
  layout_apart_fact AO 0%nat 4%nat AP04.
  destruct WF as (W1 & W2 & W3 & W4 & W5).
  assert (RU : n <= rup8 n < n + 8) by (unfold rup8; Z.div_mod_to_equations; lia).
  subst A n. unfold lc_user, qc_hdr in *. rewrite FSBE.
  destruct ch as [[c v|sc] rz n]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold lsec_slack in SL; cbn [qc_kind qc_rz qc_n] in SL; unfold qc_blk, qc_bsize in *; cbn [qc_kind qc_rz qc_n] in *.
  - pose proof (held_geo AL (fst X) AO WF0 c v HK) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CS & _).
    pose proof (region_range AL c Hc) as [RR1 RR2].
    assert (RG : region AL c = al_space AL + c * K_REGION) by reflexivity.
    assert (M16 : (region AL c + 16 * v + rz - 16 + 16) mod 16 = 0) by (rewrite RG; clear - SP16 W2; Z.div_mod_to_equations; lia).
    clear SP16 SPM W2. split; [lia|]. split; [exact M16|]. clear M16. split; [lia|]. split; [lia|]. split; [right; lia|]. split; [lia|]. lia.
  - pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & D3 & D4 & _).
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _ & _ & _ & _ & _ & CK7).
    unfold al_regions in CK7. do 4 apply Forall_cons_iff in CK7 as [_ CK7]. apply Forall_cons_iff in CK7 as [CFS _]. cbn [fst snd] in CFS. unfold apart in CFS.
    assert (M16 : (sc_beg sc + 4096 + rz - 16 + 16) mod 16 = 0) by (clear - CK1 W2; Z.div_mod_to_equations; lia).
    assert (LOW : sc_beg sc + sc_msize sc < 2147450880 -> sc_beg sc + sc_msize sc <= 2147446784) by (clear - CK1 CM2; Z.div_mod_to_equations; lia).
    clear CK1 CM2 W2 SP16 SPM. split; [lia|]. split; [exact M16|]. clear M16. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

#[using="Type"] Lemma SLACK : forall s LB m, RHEAP_B AL E s LB m -> Forall lsec_slack (live_chunks s).
Proof. intros s LB m R. rheapB R. exact R_SLK. Qed.

#[using="Type"] Lemma live_of_block2 : forall s LB m b, RHEAP_B AL E s LB m -> In b LB ->
  exists r, In r (bs_live s) /\ b = blk_ofB AL r /\ lr_ok r /\ qchunk_wf (fst r) /\ lchunk_rep AL m (fst r) /\ held_kind (bs_X s) (fst r)
            /\ lsec_slack (fst r) /\ RPRIM AL (bs_prim s) m /\ RSEC AL (bs_sec s) m.
Proof.
  intros s LB m b R HIN. pose proof (SLACK s LB m R) as SLK.
  destruct (live_of_block s LB m b R HIN) as (r & HR & EB & LR & WF & REP & HK & _). exists r.
  rheapB R. destruct R_DR as (RP & _ & RS & _).
  assert (HL : In (fst r) (live_chunks s)) by (unfold live_chunks; apply in_map; exact HR).
  repeat (split; [assumption|]). split; [exact (proj1 (Forall_forall _ _) SLK _ HL)|]. split; assumption.
Qed.

#[using="AO FSBE"] Lemma law_block_range : forall s LB m b, RHEAP_B AL E s LB m -> In b LB ->
  0 < blk_addr b /\ blk_addr b mod 16 = 0 /\ 0 <= blk_size b /\ blk_addr b + blk_size b + 16 <= alloc_ceiling
  /\ 0x609000 <= blk_addr b
  /\ (blk_addr b + blk_size b + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= blk_addr b)
  /\ (blk_addr b + blk_size b <= FSB FI \/ FSB FI + A0_FS_SIZE <= blk_addr b).
Proof.
  intros s LB m b R HIN. destruct (live_of_block2 s LB m b R HIN) as (r & HR & -> & LR & WF & REP & HK & SL & RP & RS).
  pose proof (live_geo (bs_X s) m (fst r) RP RS HK WF SL) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  destruct WF as (_ & _ & W3 & _). unfold blk_ofB, blk_addr, blk_size. cbn [fst snd]. unfold lr_ok in LR.
  split; [exact G1|]. split; [exact G2|]. split; [lia|]. split; [lia|]. split; [exact G4|]. split; lia.
Qed.

Definition chunk_apart (c1 c2 : qchunk) : Prop :=
  qc_blk AL c1 + qc_bsize c1 <= qc_blk AL c2 \/ qc_blk AL c2 + qc_bsize c2 <= qc_blk AL c1.

#[using="Type"] Lemma fop_nodup_map : forall (A B : Type) (f : A -> B) (l : list A), ForallOrdPairs (fun x y => f x <> f y) l -> List.NoDup (map f l).
Proof.
  intros A B f l H. induction H as [|a l HA _ IH]; cbn [map]; constructor; [| exact IH].
  intros HIN. apply in_map_iff in HIN as (y & EQ & Hy). exact (proj1 (Forall_forall _ _) HA y Hy (eq_sym EQ)).
Qed.

#[using="AO"] Lemma live_sep : forall (P : prim) (S : asec) l,
  (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls P c)) -> Forall (chunk_ok AL) (se_chunks S) ->
  List.NoDup (flat_map prim_of l) -> Forall (held1 P) (flat_map prim_of l) ->
  chunks_sep (flat_map sec_of l) -> incl (flat_map sec_of l) (se_chunks S) ->
  ForallOrdPairs chunk_apart l.
Proof.
  intros P S l WF0 SOK. induction l as [|ch l IH]; intros ND HH CS INC; [constructor|].
  cbn [flat_map] in ND, HH, CS, INC.
  assert (NDl : List.NoDup (flat_map prim_of l)) by (apply NoDup_app_remove_l in ND; exact ND).
  assert (HHl : Forall (held1 P) (flat_map prim_of l)) by (apply Forall_app in HH; tauto).
  assert (CSl : chunks_sep (flat_map sec_of l)).
  { clear - CS. induction (sec_of ch) as [|x xs IHx]; [exact CS|]. cbn [app] in CS. inversion CS; subst. auto. }
  assert (INCl : incl (flat_map sec_of l) (se_chunks S)) by (intros x Hx; apply INC; apply in_or_app; right; exact Hx).
  constructor; [| exact (IH NDl HHl CSl INCl)].
  apply Forall_forall. intros ch' Hch'. unfold chunk_apart.
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _).
  assert (INP : forall cv, In cv (prim_of ch') -> In cv (flat_map prim_of l)) by (intros cv Hcv; apply in_flat_map; exists ch'; split; assumption).
  assert (INS : forall x, In x (sec_of ch') -> In x (flat_map sec_of l)) by (intros x Hx; apply in_flat_map; exists ch'; split; assumption).
  clear Hch'.
  destruct ch as [[c v|sc] rz n]; destruct ch' as [[c' v'|sc'] rz' n']; unfold qc_blk, qc_bsize; cbn [qc_kind prim_of sec_of app] in *.
  -
    assert (IN' : In (c', v') (flat_map prim_of l)) by (apply INP; left; reflexivity).
    inversion ND as [|x xs NIN _]; subst. inversion HH as [|x xs H1 _]; subst.
    assert (NE : (c, v) <> (c', v')) by (intros EQ; apply NIN; rewrite EQ; exact IN').
    exact (proj1 (held_pair_apart AL P c v c' v' AO WF0 H1 (proj1 (Forall_forall _ _) HHl _ IN') NE)).
  -
    inversion HH as [|x xs H1 _]; subst.
    pose proof (held_geo AL P AO WF0 c v H1) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CSZ & _).
    pose proof (region_range AL c Hc) as [RR1 RR2].
    assert (IN' : In sc' (se_chunks S)) by (apply INCl; apply INS; left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) SOK sc' IN') as CK. destruct CK as (_ & _ & _ & _ & _ & _ & CK7).
    unfold al_regions in CK7. apply Forall_cons_iff in CK7 as [CSP _]. cbn [fst snd] in CSP. unfold apart in CSP. clear - CSP G1 G2 G3 RR1 RR2. lia.
  -
    assert (IN' : In (c', v') (flat_map prim_of l)) by (apply INP; left; reflexivity).
    pose proof (held_geo AL P AO WF0 c' v' (proj1 (Forall_forall _ _) HHl _ IN')) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CSZ & _).
    pose proof (region_range AL c' Hc) as [RR1 RR2].
    assert (INs : In sc (se_chunks S)) by (apply INC; left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) SOK sc INs) as CK. destruct CK as (_ & _ & _ & _ & _ & _ & CK7).
    unfold al_regions in CK7. apply Forall_cons_iff in CK7 as [CSP _]. cbn [fst snd] in CSP. unfold apart in CSP. clear - CSP G1 G2 G3 RR1 RR2. lia.
  -
    inversion CS as [|x xs FA _]; subst.
    assert (IN' : In sc' (flat_map sec_of l)) by (apply INS; left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) FA sc' IN') as AP. unfold apart_chunks in AP. clear - AP. lia.
Qed.

#[using="Type"] Lemma apart_chunks_sym : forall c d, apart_chunks c d -> apart_chunks d c.
Proof. unfold apart_chunks. intros c d H. lia. Qed.

#[using="Type"] Lemma chunks_sep_perm : forall l l', Permutation l l' -> chunks_sep l -> chunks_sep l'.
Proof.
  intros l l' P. induction P as [| x l l' P IH | x y l | l1 l2 l3 P1 IH1 P2 IH2]; intros H.
  - exact H.
  - inversion H as [|c0 l0 FA CS]; subst. constructor; [eapply Permutation_Forall; eassumption| exact (IH CS)].
  - inversion H as [|c0 l0 FA CS]; subst. inversion CS as [|c1 l1 FA1 CS1]; subst. inversion FA as [|c2 l2 AXY FA2]; subst.
    constructor; [constructor; [apply apart_chunks_sym; exact AXY| exact FA1]|]. constructor; [exact FA2| exact CS1].
  - exact (IH2 (IH1 H)).
Qed.

#[using="Type"] Lemma chunks_sep_app_r : forall l1 l2, chunks_sep (l1 ++ l2) -> chunks_sep l2.
Proof. induction l1 as [|x l1 IH]; intros l2 H; [exact H|]. cbn [app] in H. inversion H; subst. auto. Qed.

#[using="AO"] Lemma live_fop : forall s LB m, RHEAP_B AL E s LB m -> ForallOrdPairs chunk_apart (live_chunks s).
Proof.
  intros s LB m R. rheapB R. destruct R_DR as (RP & _ & RS & _ & _ & _ & _ & _ & _ & (HND & HFA) & _).
  destruct (clear_ctx AL (bs_X s) m RP RS) as (WF0 & SOK & SSEP). cbn [bs_X fst snd] in *.
  apply (live_sep (bs_prim s) (bs_sec s)); [exact WF0| exact SOK| | | |].
  - apply NoDup_app_remove_l in HND. apply NoDup_app_remove_l in HND. exact HND.
  - apply Forall_app in HFA as [_ HFA]. apply Forall_app in HFA as [_ HFA]. exact HFA.
  - eapply chunks_sep_app_r. eapply chunks_sep_perm; [exact R_SECP| exact SSEP].
  - intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact R_SECP|]. apply in_or_app. right. exact Hx.
Qed.

#[using="Type"] Lemma fop_map_in : forall (A B : Type) (R : B -> B -> Prop) (f : A -> B) (l : list A) x y,
  ForallOrdPairs R (map f l) -> In x l -> In y l -> x <> y -> R (f x) (f y) \/ R (f y) (f x).
Proof.
  intros A B R f l x y. induction l as [|a l IH]; intros H Hx Hy NE; [destruct Hx|].
  cbn [map] in H. inversion H as [|a0 l0 FA FOP]; subst.
  destruct Hx as [->|Hx]; destruct Hy as [->|Hy].
  - exfalso; apply NE; reflexivity.
  - left. exact (proj1 (Forall_forall _ _) FA (f y) (in_map f _ _ Hy)).
  - right. exact (proj1 (Forall_forall _ _) FA (f x) (in_map f _ _ Hx)).
  - exact (IH FOP Hx Hy NE).
Qed.

#[using="Type"] Lemma chunk_apart_users : forall c1 c2, qchunk_wf c1 -> qchunk_wf c2 -> chunk_apart c1 c2 ->
  lc_user AL c1 + qc_n c1 <= lc_user AL c2 \/ lc_user AL c2 + qc_n c2 <= lc_user AL c1.
Proof.
  intros c1 c2 (W1 & _ & W3 & W4 & _) (V1 & _ & V3 & V4 & _) AP. unfold chunk_apart in AP. unfold lc_user, qc_hdr.
  assert (RU1 : qc_n c1 <= rup8 (qc_n c1)) by (unfold rup8; Z.div_mod_to_equations; lia).
  assert (RU2 : qc_n c2 <= rup8 (qc_n c2)) by (unfold rup8; Z.div_mod_to_equations; lia). lia.
Qed.

#[using="AO"] Lemma law_blocks_disjoint : forall s LB m b1 b2, RHEAP_B AL E s LB m -> In b1 LB -> In b2 LB -> b1 <> b2 ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
  intros s LB m b1 b2 R H1 H2 NE. pose proof (live_fop s LB m R) as FOP.
  destruct (live_of_block s LB m b1 R H1) as (r1 & HR1 & -> & LR1 & WF1 & _).
  destruct (live_of_block s LB m b2 R H2) as (r2 & HR2 & -> & LR2 & WF2 & _).
  assert (NR : r1 <> r2) by (intros ->; apply NE; reflexivity).
  unfold live_chunks in FOP.
  assert (AP : lc_user AL (fst r1) + qc_n (fst r1) <= lc_user AL (fst r2) \/ lc_user AL (fst r2) + qc_n (fst r2) <= lc_user AL (fst r1)).
  { destruct (fop_map_in _ _ chunk_apart fst (bs_live s) r1 r2 FOP HR1 HR2 NR) as [K|K].
    - exact (chunk_apart_users _ _ WF1 WF2 K).
    - destruct (chunk_apart_users _ _ WF2 WF1 K) as [K'|K']; [right| left]; exact K'. }
  destruct WF1 as (_ & _ & W3 & _). destruct WF2 as (_ & _ & V3 & _).
  unfold blk_ofB, blk_addr, blk_size, lr_ok in *. cbn [fst snd]. lia.
Qed.

#[using="AO"] Lemma law_blocks_nodup : forall s LB m, RHEAP_B AL E s LB m -> NoDup (map (@blk_id Z) LB).
Proof.
  intros s LB m R. pose proof (live_fop s LB m R) as FOP. pose proof R as R0. rheapB R.
  apply NoDup_ListNoDup. eapply Permutation_NoDup; [apply Permutation_sym; apply Permutation_map; exact R_PERM|].
  rewrite map_map. unfold blk_ofB, blk_id. cbn [fst snd].
  apply fop_nodup_map. unfold live_chunks in FOP.
  assert (WFS : Forall (fun r => qchunk_wf (fst r)) (bs_live s)) by (apply Forall_forall; intros r Hr; exact (proj1 (Forall_forall _ _) R_WF (fst r) (in_map fst _ _ Hr))).
  clear - FOP WFS AO. induction (bs_live s) as [|r l IH]; [constructor|].
  cbn [map] in FOP. inversion FOP as [|a0 l0 FA FOP']; subst. inversion WFS as [|a1 l1 WR WL]; subst.
  constructor; [| exact (IH FOP' WL)]. apply Forall_forall. intros r' Hr'.
  pose proof (proj1 (Forall_forall _ _) FA (fst r') (in_map fst _ _ Hr')) as AP.
  pose proof (proj1 (Forall_forall _ _) WL r' Hr') as WR'. cbv beta in WR'.
  destruct (chunk_apart_users _ _ WR WR' AP) as [K|K]; destruct WR as (_ & _ & W3 & _); destruct WR' as (_ & _ & V3 & _); lia.
Qed.

#[using="Type"] Lemma rw_cells_mrd : forall (m : mem) B cs a, rw_cells asegs m B cs -> B <= a < B + Z.of_nat (cells_size cs) -> exists v, mrd asegs m (wa a) = Some v.
Proof.
  intros m B cs a [[WF (B0 & B1 & BY)] _] Ha. rewrite cells_bytes_length in BY, B1 by exact WF.
  specialize (BY (Z.to_nat (a - B)) ltac:(lia)). replace (B + Z.of_nat (Z.to_nat (a - B))) with a in BY by lia.
  destruct (nth_error (cells_bytes cs) (Z.to_nat (a - B))) as [v|] eqn:EN; [exists v; exact BY|].
  apply nth_error_None in EN. rewrite cells_bytes_length in EN by exact WF. lia.
Qed.

#[using="Type"] Lemma law_block_shadow : forall s LB m b, RHEAP_B AL E s LB m -> In b LB ->
  rw_cells asegs m (sh (blk_addr b)) (shadow_cells (block_shadow (blk_size b))).
Proof.
  intros s LB m b R HIN. destruct (live_of_block s LB m b R HIN) as (r & HR & -> & LR & WF & REP & _).
  destruct REP as (_ & _ & _ & _ & _ & SHU & _). unfold blk_ofB, blk_addr, blk_size. cbn [fst snd].
  change (qc_hdr AL (fst r) + 16) with (lc_user AL (fst r)) in SHU.
  destruct LR as [->|[-> N1]]; [exact SHU|]. rewrite N1 in SHU.
  destruct SHU as [[_ (B0 & B1 & _)] (W0 & W1 & _)]. change (shadow_cells (block_shadow 0)) with (@nil cell).
  split; [split; [exact I|]|]; (split; [exact B0|]); (split; [cbn; lia|]); intros i Hi; cbn in Hi; lia.
Qed.

#[using="AO FI FSBE"] Lemma law_block_slack : forall s LB m b a, RHEAP_B AL E s LB m -> In b LB ->
  blk_addr b - 16 <= a < round_up8 (blk_addr b + blk_size b) -> exists v, mrd asegs m (wa a) = Some v.
Proof.
  intros s LB m b a R HIN Ha. destruct (live_of_block2 s LB m b R HIN) as (r & HR & -> & LR & WF & REP & HK & SL & RP & RS).
  pose proof (live_geo (bs_X s) m (fst r) RP RS HK WF SL) as G. cbv zeta in G. destruct G as (_ & G2 & _).
  destruct REP as ((bits & actx & _ & HDR) & _ & (ub & USR) & (j & JNK) & _).
  destruct WF as (W1 & _ & W3 & W4 & _). unfold lr_ok in LR.
  unfold blk_ofB, blk_addr, blk_size in Ha. cbn [fst snd] in Ha.
  change (qc_hdr AL (fst r) + 16) with (lc_user AL (fst r)) in USR, JNK.
  assert (EH : qc_hdr AL (fst r) = lc_user AL (fst r) - 16) by (unfold lc_user; lia). rewrite EH in HDR.
  set (A := lc_user AL (fst r)) in *. set (n := qc_n (fst r)) in *.
  assert (RU : round_up8 (A + n) = A + rup8 n) by (unfold round_up8, rup8; clear - G2; Z.div_mod_to_equations; lia).
  assert (RU0 : round_up8 (A + 0) = A) by (unfold round_up8; clear - G2; Z.div_mod_to_equations; lia).
  assert (RN : n <= rup8 n) by (unfold rup8; Z.div_mod_to_equations; lia).
  assert (HA : a < A \/ (A <= a < A + n) \/ (A + n <= a < A + rup8 n)).
  { destruct LR as [EQ|[EQ N1]]; rewrite EQ in Ha; [rewrite RU in Ha| rewrite RU0 in Ha]; lia. }
  destruct HA as [HA|[HA|HA]].
  - apply (rw_cells_mrd m (A - 16) _ a HDR). cbn [cells_size csize]. lia.
  - apply (rw_cells_mrd m A _ a USR). cbn [cells_size csize]. lia.
  - apply (rw_cells_mrd m (A + n) _ a JNK). cbn [cells_size csize]. lia.
Qed.

Definition cw_class (LB : list (block Z)) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (exists lo hi, a0_static lo hi /\ lo <= fst iv /\ snd iv <= hi /\ a0_wsafe (fst iv) (snd iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
  \/ (FSB FI <= fst iv /\ snd iv <= FSB FI + A0_FS_SIZE)
  \/ (sh (FSB FI) <= fst iv /\ snd iv <= sh (FSB FI) + A0_FS_SHSIZE).

Definition img_w (iv : Z * Z) : Prop :=
  (0x10000 <= fst iv /\ snd iv <= 0xa9000) \/ (0xabde8 <= fst iv /\ snd iv <= 0xabde8)
  \/ (0xae6c0 <= fst iv /\ snd iv <= 0xaedc0)
  \/ (0x5d5f40 <= fst iv /\ snd iv <= 0x5e5fa0) \/ (0x5e5fc0 <= fst iv /\ snd iv <= 0x5e6060)
  \/ (0x5e68c8 <= fst iv /\ snd iv <= 0x5e68d0)
  \/ (0x6069b0 <= fst iv /\ snd iv <= 0x6069b0) \/ (0x6069b8 <= fst iv /\ snd iv <= 0x6069b8)
  \/ (0x6069c0 <= fst iv /\ snd iv <= 0x606be0)
  \/ (0x1457a0 <= fst iv /\ snd iv <= 0x1457a1)
  \/ (0x606be0 <= fst iv /\ snd iv <= 0x606be4) \/ (0x606c00 <= fst iv /\ snd iv <= 0x606c08) \/ (0x606fc0 <= fst iv /\ snd iv <= 0x607480).

Definition S6LO : Z := sh alloc_ceiling - sh alloc_ceiling mod 8.

Definition cw_zone (live : list (qchunk * Z)) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ img_w iv
  \/ (0x7fffa000 <= fst iv /\ snd iv <= 0x800b9200)
  \/ (S6LO <= fst iv /\ snd iv <= 0x10007fff8000)
  \/ (exists r, In r live /\ lc_user AL (fst r) <= fst iv /\ snd iv <= lc_user AL (fst r) + snd r)
  \/ (al_fsb AL <= fst iv /\ snd iv <= al_fsb AL + A0_FS_SIZE)
  \/ (sh (al_fsb AL) <= fst iv /\ snd iv <= sh (al_fsb AL) + A0_FS_SHSIZE).

#[using="FSBE"] Lemma cw_zone_of_class : forall s LB m iv, RHEAP_B AL E s LB m -> cw_class LB iv -> cw_zone (bs_live s) iv.
Proof.
  intros s LB m iv R [H|[(lo & hi & ST & H1 & H2 & WS1 & WS2)|[(b & HIN & H1 & H2)|[H|H]]]].
  - left. exact H.
  - destruct ST as (LH & ST). unfold cw_zone, img_w, S6LO.
    destruct ST as [B|[B|[B|[B|[B|[B|[B|[B|[B|[B|[B|[B|B]]]]]]]]]]]]; try (right; left; lia).
    + right; right; left. lia.
    + right; right; right; left. lia.
  - destruct (live_of_block s LB m b R HIN) as (r & HR & -> & _). unfold blk_ofB, blk_addr, blk_size in H1, H2. cbn [fst snd] in H1, H2.
    right; right; right; right; left. exists r. split; [exact HR|]. split; assumption.
  - rewrite FSBE in H. right; right; right; right; right; left. exact H.
  - rewrite FSBE in H. right; right; right; right; right; right. exact H.
Qed.

Definition img_gap (A n : Z) : Prop :=
  0 <= n /\
  ( (0xa9000 <= A /\ A + n <= 0xabde8) \/ (0xabde8 <= A /\ A + n <= 0xae6c0) \/ (0xaedc0 <= A /\ A + n <= 0x1457a0)
  \/ (0x1457a1 <= A /\ A + n <= 0x5d5f40) \/ (0x5e5fa0 <= A /\ A + n <= 0x5e5fc0) \/ (0x5e6060 <= A /\ A + n <= 0x5e68c8)
  \/ (0x5e68d0 <= A /\ A + n <= 0x6069b0) \/ (0x6069b0 <= A /\ A + n <= 0x6069b8) \/ (0x6069b8 <= A /\ A + n <= 0x6069c0)
  \/ (0x606be4 <= A /\ A + n <= 0x606c00) \/ (0x606c08 <= A /\ A + n <= 0x606fc0) \/ (0x607480 <= A /\ A + n <= 0x609000) ).

#[using="Type"] Lemma img_gap_w : forall A n iv, img_gap A n -> img_w iv -> A + n <= fst iv \/ snd iv <= A.
Proof. intros A n [x y] (Hn & G) Wv. unfold img_w in Wv. cbn [fst snd] in *. lia. Qed.

Definition lgeo (X : pstate) (r : qchunk * Z) : Prop :=
  let ch := fst r in let A := lc_user AL ch in
  qchunk_wf ch /\ lr_ok r /\ held_kind X ch /\ lsec_slack ch
  /\ 0 < A /\ A mod 16 = 0 /\ A + qc_n ch + 16 <= alloc_ceiling /\ 0x609000 <= A
  /\ (A + qc_n ch + 16 <= 0x7fff7000 \/ 0x10007fff8000 <= A)
  /\ (A + qc_n ch <= al_fsb AL \/ al_fsb AL + A0_FS_SIZE <= A)
  /\ qc_blk AL ch + 16 <= A /\ A + rup8 (qc_n ch) <= qc_blk AL ch + qc_bsize ch.

#[using="AO FI FSBE"] Lemma live_lgeo : forall s LB m, RHEAP_B AL E s LB m -> forall r, In r (bs_live s) -> lgeo (bs_X s) r.
Proof.
  intros s LB m R r HR. pose proof (SLACK s LB m R) as SLK. pose proof R as R0. rheapB R. destruct R_DR as (RP & _ & RS & _).
  assert (HL : In (fst r) (live_chunks s)) by (unfold live_chunks; apply in_map; exact HR).
  pose proof (proj1 (Forall_forall _ _) R_LR r HR) as LR. pose proof (proj1 (Forall_forall _ _) R_WF _ HL) as WF.
  pose proof (proj1 (Forall_forall _ _) R_HK _ HL) as HK. pose proof (proj1 (Forall_forall _ _) SLK _ HL) as SL.
  pose proof (live_geo (bs_X s) m (fst r) RP RS HK WF SL) as G. cbv zeta in G. rewrite FSBE in G.
  unfold lgeo. cbv zeta. tauto.
Qed.

#[using="AO"] Lemma zone_facts : 0x10007fff8000 <= alloc_ceiling /\ 0x800b9200 <= S6LO /\ S6LO <= sh alloc_ceiling /\ S6LO mod 8 = 0
  /\ ((0 < al_fsb AL /\ al_fsb AL + A0_FS_SIZE <= 0x10000) \/ (0x609000 <= al_fsb AL /\ al_fsb AL + A0_FS_SIZE <= 0x7fff7000) \/ 0x10007fff8000 <= al_fsb AL)
  /\ al_fsb AL + A0_FS_SIZE <= alloc_ceiling /\ al_fsb AL mod 4096 = 0
  /\ 0x7fff8000 <= sh (al_fsb AL) /\ sh (al_fsb AL) + A0_FS_SHSIZE <= 0x10007fff8000.
Proof.
  pose proof AO as (_ & _ & _ & TLO & _). destruct TLO as ((_ & HA) & _).
  layout_facts AO 4%nat F4. destruct F4 as ((F1 & _) & F2 & F3 & _ & F5 & _).
  unfold S6LO, sh, SHADOW_OFF in *. repeat split; try lia; try (Z.div_mod_to_equations; lia).
Qed.

#[using="AO"] Lemma zone_dj_img : forall X live W A n, (forall r, In r live -> lgeo X r) -> Forall (cw_zone live) W -> img_gap A n -> disjoint_from W A n.
Proof.
  intros X live W A n LG F G. apply disjoint_from_of_Forall. eapply Forall_impl; [| exact F]. intros iv Z0.
  destruct zone_facts as (ZA & ZS & _ & _ & ZF & _ & _ & ZFS & _).
  assert (GB : 0xa9000 <= A /\ A + n <= 0x609000) by (destruct G as (Hn & G); lia).
  destruct Z0 as [Z0|[Z0|[Z0|[Z0|[(r & HR & Z1 & Z2)|[Z0|Z0]]]]]].
  - lia.
  - exact (img_gap_w A n iv G Z0).
  - lia.
  - lia.
  - pose proof (LG r HR) as LGr. unfold lgeo in LGr. cbv zeta in LGr. destruct LGr as (_ & _ & _ & _ & _ & _ & _ & L8 & _). lia.
  - lia.
  - lia.
Qed.

Definition off_obj (live : list (qchunk * Z)) (A n : Z) : Prop :=
  0 <= n
  /\ ((0 < A /\ A + n <= 0x10000) \/ (0x609000 <= A /\ A + n <= 0x7fff7000) \/ 0x10007fff8000 <= A)
  /\ A + n <= alloc_ceiling
  /\ (A + n <= al_fsb AL \/ al_fsb AL + A0_FS_SIZE <= A)
  /\ (forall r, In r live -> A + n <= lc_user AL (fst r) \/ lc_user AL (fst r) + snd r <= A).

#[using="AO"] Lemma zone_dj_obj : forall live W A n, Forall (cw_zone live) W -> off_obj live A n -> disjoint_from W A n.
Proof.
  intros live W A n F (Hn & PL & CE & FS & LV). apply disjoint_from_of_Forall. eapply Forall_impl; [| exact F]. intros iv Z0.
  destruct zone_facts as (ZA & ZS & _ & _ & ZF & _ & _ & ZFS & ZFE).
  destruct Z0 as [Z0|[Z0|[Z0|[Z0|[(r & HR & Z1 & Z2)|[Z0|Z0]]]]]].
  - lia.
  - unfold img_w in Z0. lia.
  - lia.
  - lia.
  - specialize (LV r HR). lia.
  - lia.
  - lia.
Qed.

Definition off_shobj (B k : Z) : Prop :=
  0 <= k /\ B mod 8 = 0 /\ 0x609000 <= B
  /\ (B + 8 * k <= 0x7fff7000 \/ 0x10007fff8000 <= B)
  /\ (B + 8 * k + 64 <= alloc_ceiling \/ ((B + 8 * k) mod 64 = 0 /\ B + 8 * k <= alloc_ceiling))
  /\ (B + 8 * k <= al_fsb AL \/ al_fsb AL + A0_FS_SIZE <= B).

#[using="AO"] Lemma zone_dj_shobj : forall X live W B k, (forall r, In r live -> lgeo X r) -> Forall (cw_zone live) W -> off_shobj B k -> disjoint_from W (sh B) k.
Proof.
  intros X live W B k LG F (Hk & B8 & BI & BM & BC & BF). apply disjoint_from_of_Forall. eapply Forall_impl; [| exact F]. intros iv Z0.
  destruct zone_facts as (ZA & ZS & ZS2 & ZS3 & ZF & ZFC & ZFM & ZFS & ZFE).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (SHB : 0x800b9200 <= sh B /\ sh B + k <= 0x10007fff8000) by (unfold sh, SHADOW_OFF; split; Z.div_mod_to_equations; lia).
  destruct Z0 as [Z0|[Z0|[Z0|[Z0|[(r & HR & Z1 & Z2)|[Z0|Z0]]]]]].
  - lia.
  - unfold img_w in Z0. lia.
  - lia.
  - left. assert (sh B + k <= S6LO); [| lia]. unfold S6LO, sh, SHADOW_OFF in *. clear - Hk B8 BC ACR. Z.div_mod_to_equations. lia.
  - pose proof (LG r HR) as LGr. unfold lgeo in LGr. cbv zeta in LGr. destruct LGr as (_ & LR & _ & _ & L5 & _ & _ & L8 & L9 & _). unfold lr_ok in LR. lia.
  - lia.
  - assert (FSH : sh (al_fsb AL) + A0_FS_SHSIZE = sh (al_fsb AL + A0_FS_SIZE)) by (unfold sh, SHADOW_OFF; clear - ZFM; Z.div_mod_to_equations; lia).
    assert (SBK : sh B + k = sh (B + 8 * k)) by (unfold sh, SHADOW_OFF; clear - B8; Z.div_mod_to_equations; lia).
    destruct BF as [BF|BF].
    + left. rewrite SBK. pose proof (sh_le (B + 8 * k) (al_fsb AL) BF). lia.
    + right. pose proof (sh_le (al_fsb AL + A0_FS_SIZE) B BF). lia.
Qed.

#[using="AO"] Lemma prim_clear_of_zone : forall X (m : mem) live W, RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  (forall r, In r live -> lgeo X r) -> Forall (cw_zone live) W -> prim_clear AL (fst X) W.
Proof.
  intros X m live W RP RS LG F. destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  unfold prim_clear. eapply Forall_impl; [| exact F]. intros iv Z0.
  destruct zone_facts as (ZA & ZS & ZS2 & ZS3 & ZF & ZFC & ZFM & ZFS & ZFE).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & SP16 & TLO & _). destruct TLO as (_ & _ & (T3 & _) & T4 & _ & _ & T7 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & SP7).
  layout_apart_fact AO 0%nat 3%nat LP03. layout_apart_fact AO 0%nat 4%nat LP04. layout_apart_fact AO 3%nat 4%nat LP34.
  set (SE := al_space AL + K_SPACE + 4096) in *.
  assert (SHS : 0x2008fff7000 <= sh (al_space AL) /\ sh SE <= S6LO /\ sh SE <= 0x10007fff8000).
  { unfold S6LO, sh, SHADOW_OFF, SE in *. clear - SP1 SP2 SPM ACR. repeat split; Z.div_mod_to_equations; lia. }
  destruct SHS as (SH1 & SH2 & SH3).
  destruct Z0 as [Z0|[Z0|[Z0|[Z0|[(r & HR & Z1 & Z2)|[Z0|Z0]]]]]].
  - left. unfold prim_out. fold SE. lia.
  - left. unfold prim_out. fold SE. unfold img_w in Z0. lia.
  - left. unfold prim_out. fold SE. lia.
  - left. unfold prim_out. fold SE. lia.
  - pose proof (LG r HR) as LGr. unfold lgeo in LGr. cbv zeta in LGr.
    destruct LGr as (WF & LR & HK & SL & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12). unfold lr_ok in LR.
    assert (RU : qc_n (fst r) <= rup8 (qc_n (fst r))) by (unfold rup8; Z.div_mod_to_equations; lia).
    destruct WF as (_ & _ & W3 & _).
    destruct (fst r) as [[c v|sc] rz n] eqn:ECH; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_blk, qc_bsize in L11, L12; cbn [qc_kind qc_n] in *.
    + right. exists c, v. split; [exact HK|]. left. unfold chunk_iv. lia.
    + left. pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. destruct CK as (_ & _ & _ & _ & _ & _ & CK7).
      unfold al_regions in CK7. apply Forall_cons_iff in CK7 as [CSP CK7]. do 2 apply Forall_cons_iff in CK7 as [_ CK7]. apply Forall_cons_iff in CK7 as [CTH _].
      cbn [fst snd] in CSP, CTH. unfold apart in CSP, CTH. unfold prim_out. fold SE. lia.
  - left. unfold prim_out. fold SE. assert (FSH : forall a, 0 <= a < 2^47 -> sh a < al_fsb AL \/ al_fsb AL + A0_FS_SIZE <= sh a).
    { layout_facts AO 4%nat F4. destruct F4 as (_ & _ & _ & _ & _ & _ & F7). exact F7. }
    pose proof (FSH (al_space AL) ltac:(lia)) as FS1. pose proof (FSH SE ltac:(unfold SE; lia)) as FS2.
    pose proof (sh_le (al_space AL) SE ltac:(unfold SE; lia)) as SLE. lia.
  - left. unfold prim_out. fold SE.
    assert (FSH : sh (al_fsb AL) + A0_FS_SHSIZE = sh (al_fsb AL + A0_FS_SIZE)) by (unfold sh, SHADOW_OFF; clear - ZFM; Z.div_mod_to_equations; lia).
    assert (SD : sh (al_fsb AL + A0_FS_SIZE) <= sh (al_space AL) \/ sh SE <= sh (al_fsb AL)).
    { destruct LP04 as [K|K]; [right; apply sh_le; unfold SE; lia| left; apply sh_le; lia]. }
    lia.
Qed.

Definition img_out_c (iv : Z * Z) : Prop := snd iv <= 0x10000 \/ 0x609000 <= fst iv \/ img_w iv.

#[using="AO"] Lemma zone_img_out : forall X live W, (forall r, In r live -> lgeo X r) -> Forall (cw_zone live) W -> Forall img_out_c W.
Proof.
  intros X live W LG F. eapply Forall_impl; [| exact F]. intros iv Z0. unfold img_out_c.
  destruct zone_facts as (ZA & ZS & _ & _ & ZF & _ & _ & ZFS & _).
  destruct Z0 as [Z0|[Z0|[Z0|[Z0|[(r & HR & Z1 & Z2)|[Z0|Z0]]]]]].
  - right; left. lia.
  - right; right. exact Z0.
  - right; left. lia.
  - right; left. lia.
  - pose proof (LG r HR) as LGr. unfold lgeo in LGr. cbv zeta in LGr. destruct LGr as (_ & _ & _ & _ & _ & _ & _ & L8 & _). right; left. lia.
  - lia.
  - right; left. lia.
Qed.

Ltac frame_cell_c C MU WM F :=
  eapply rw_cells_transport; [exact C| exact MU| exact WM|
    apply disjoint_from_of_Forall; eapply Forall_impl; [| exact F]; intros [lo' hi'] Hiv'; unfold img_out_c, img_w in Hiv'; cbn in Hiv' |- *; lia].

#[using="Type"] Lemma poison_env_frame_c : forall W m m', poison_env E m -> munch W m m' -> wmono asegs m m' -> Forall img_out_c W -> poison_env E m'.
Proof.
  intros W m m' PE MU WM F. pe_split PE. unfold poison_env.
  repeat match goal with |- _ /\ _ => split end; try lia.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell_c C MU WM F end.
Qed.

Definition thread_clear_c (W : list (Z * Z)) : Prop :=
  Forall (fun iv : Z * Z => img_out_c iv
     /\ (at_ctx L + 160 <= fst iv \/ snd iv <= at_ctx L + 152)
     /\ (at_thr L + 24 <= fst iv \/ snd iv <= at_thr L + 8)
     /\ (at_thr L + 41 <= fst iv \/ snd iv <= at_thr L + 40)
     /\ (at_thr L + 3169 <= fst iv \/ snd iv <= at_thr L + 3168)) W.

#[using="Type"] Lemma thread_env_frame_c : forall W m m', thread_env L m -> munch W m m' -> wmono asegs m m' -> thread_clear_c W -> thread_env L m'.
Proof.
  intros W m m' TE MU WM F. unfold thread_clear_c in F. te_split TE. unfold thread_env.
  repeat match goal with |- _ /\ _ => split end.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell_c C MU WM F end.
Qed.

#[using="Type"] Lemma RSEC_frame_but_c : forall S W m m',
  RSEC AL S m -> munch W m m' -> wmono_but W m m' -> Forall img_out_c W ->
  0 <= al_parr AL -> disjoint_from W (al_parr AL) (2^23) ->
  Forall (fun d => disjoint_from W (sc_beg d) 32) (se_chunks S) -> RSEC AL S m'.
Proof.
  intros S W m m' (WF & (ENV & ENV2 & ENV3) & VARS & PR & HD) MU WB F P0 DP DH.
  destruct VARS as ((j24 & j32 & j40 & jsb & jpad & na & nf & cur & mx & VC) & (bsl & BSL & LBSL) & MTX & (g16 & g24 & GST)).
  destruct PR as (ws & PARRu & LWS & FWS).
  pose proof WF as (W0 & _ & W2 & _).
  assert (DI : forall A n, img_gap A n -> disjoint_from W A n).
  { intros A n G. apply dj_of_Forall. eapply Forall_impl; [| exact F]. intros [lo' hi'] Hiv. destruct G as (Hn & G).
    unfold img_out_c in Hiv. destruct Hiv as [Hiv|[Hiv|Hiv]]; [cbn in Hiv |- *; lia| cbn in Hiv |- *; lia|].
    exact (img_gap_w A n (lo', hi') (conj Hn G) Hiv). }
  unfold RSEC. split; [exact WF|]. split; [| split; [| split]].
  - split; [| split]; (eapply rw_cells_transport_but; [exact MU| exact WB| eassumption| apply DI; unfold img_gap; cbn; lia]).
  - unfold sec_vars. split; [| split; [| split]].
    + exists j24, j32, j40, jsb, jpad, na, nf, cur, mx. eapply rw_cells_transport_but; [exact MU| exact WB| exact VC| apply DI; unfold img_gap; cbn; lia].
    + exists bsl. split; [| exact LBSL]. eapply u64arr_transport_but; [exact MU| exact WB| exact BSL|]. rewrite LBSL. apply DI; unfold img_gap; cbn; lia.
    + eapply rw_cells_transport_but; [exact MU| exact WB| exact MTX| apply DI; unfold img_gap; cbn; lia].
    + exists g16, g24. eapply rw_cells_transport_but; [exact MU| exact WB| exact GST| apply DI; unfold img_gap; cbn; lia].
  - exists ws. split; [| split; [exact LWS| exact FWS]].
    eapply u64arr_transport_but; [exact MU| exact WB| exact PARRu|].
    eapply ATac.disjoint_from_sub; [exact DP| lia| lia].
  - intros j d Hj. eapply rw_cells_transport_but; [exact MU| exact WB| exact (HD j d Hj)|].
    cbn. exact (proj1 (Forall_forall _ _) DH d (nth_error_In _ _ Hj)).
Qed.

#[using="Type"] Lemma bytes_at_of_mrd : forall (m : mem) n a, 0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall i, (i < n)%nat -> exists v, mrd asegs m (wa (a + Z.of_nat i)) = Some v) ->
  exists bs, length bs = n /\ bytes_at asegs m a bs.
Proof.
  intros m n. induction n as [|n IH]; intros a H0 H1 H.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as [v0 Hv0]. rewrite Z.add_0_r in Hv0.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & LB & (_ & _ & B)).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as [v Hv]. exists v. rewrite <- Hv. f_equal. f_equal. lia. }
    exists (v0 :: bs). split; [cbn; lia|]. split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hv0.
    + rewrite <- (B i) by (cbn in Hi; lia). f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma user_bytes_frame : forall (m m' : mem) A n ub, rw_cells asegs m A [CB (Z.to_nat n) ub] -> wmono asegs m m' -> 0x609000 <= A -> 0 <= n ->
  exists ub', rw_cells asegs m' A [CB (Z.to_nat n) ub'].
Proof.
  intros m m' A n ub [[WF (B0 & B1 & _)] WR] WM HA Hn. cbn [cells_wf cell_wf] in WF. destruct WF as [LU _].
  cbn [cells_bytes cbytes] in B1. rewrite app_nil_r, LU, Z2Nat.id in B1 by lia.
  pose proof (wr_at_transport asegs m m' A _ WR WM) as WR'. cbn [cells_size csize] in WR, WR'. rewrite Nat.add_0_r, Z2Nat.id in WR' by lia.
  destruct (bytes_at_of_mrd m' (Z.to_nat n) A ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (ub' & LU' & BA').
  { intros i Hi. destruct WR' as (_ & _ & WV). specialize (WV (Z.of_nat i) ltac:(lia)).
    rewrite wview_high in WV by (rewrite wa_unsigned by lia; lia). unfold mrd. destruct (m' (wa (A + Z.of_nat i))) as [b|]; [exists b; reflexivity| contradiction]. }
  exists ub'. split; [split; [cbn [cells_wf cell_wf]; split; [exact LU'| exact I]|]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BA'.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact WR'.
Qed.

#[using="AO"] Lemma held_hull_geo : forall X (m : mem) ch, RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch ->
  let B := qc_blk AL ch in let n := qc_bsize ch in
  B mod 8 = 0 /\ n mod 8 = 0 /\ 32 <= n /\ 0x609000 <= B /\ B + n <= alloc_ceiling
  /\ (B + n <= 0x7fff7000 \/ 0x10007fff8000 <= B)
  /\ (B + n + 64 <= alloc_ceiling \/ (B + n) mod 64 = 0)
  /\ (B + n <= al_fsb AL \/ al_fsb AL + A0_FS_SIZE <= B - 4096)
  /\ match qc_kind ch with QPrim _ _ => True | QSec sc => B = sc_beg sc + 4096 /\ 0x609000 <= sc_beg sc /\ sc_beg sc mod 4096 = 0 end.
Proof.
  intros X m ch RP RS HK B n. destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_apart_fact AO 0%nat 4%nat AP04.
  subst B n. destruct ch as [[c v|sc] rz n]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_blk, qc_bsize; cbn [qc_kind].
  - pose proof (held_geo AL (fst X) AO WF0 c v HK) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CS & _).
    pose proof (region_range AL c Hc) as [RR1 RR2]. pose proof (class_size_mod16 c Hc) as CM.
    assert (RG : region AL c = al_space AL + c * K_REGION) by reflexivity.
    split; [rewrite RG; clear - SPM; Z.div_mod_to_equations; lia|]. split; [clear - CM; Z.div_mod_to_equations; lia|].
    clear SPM CM. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; lia|]. split; [left; lia|]. split; [lia| exact I].
  - pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & D3 & D4 & _).
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _ & _ & _ & _ & _ & CK7).
    unfold al_regions in CK7. do 4 apply Forall_cons_iff in CK7 as [_ CK7]. apply Forall_cons_iff in CK7 as [CFS _]. cbn [fst snd] in CFS. unfold apart in CFS.
    split; [clear - CK1; Z.div_mod_to_equations; lia|]. split; [clear - CM2; Z.div_mod_to_equations; lia|].
    assert (LOW : sc_beg sc + sc_msize sc < 2147450880 -> sc_beg sc + sc_msize sc <= 2147446784) by (clear - CK1 CM2; Z.div_mod_to_equations; lia).
    assert (M64 : (sc_beg sc + 4096 + (sc_msize sc - 4096)) mod 64 = 0) by (clear - CK1 CM2; Z.div_mod_to_equations; lia).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; exact M64|]. split; [lia|]. split; [reflexivity|]. split; [lia| exact CK1].
Qed.

Definition hullb (ch : qchunk) : Z := match qc_kind ch with QPrim c v => region AL c + 16 * v | QSec sc => sc_beg sc end.
Definition hulln (ch : qchunk) : Z := match qc_kind ch with QPrim c v => class_size c | QSec sc => sc_msize sc end.
Definition hull_apart (c1 c2 : qchunk) : Prop := hullb c1 + hulln c1 <= hullb c2 \/ hullb c2 + hulln c2 <= hullb c1.

#[using="AO"] Lemma pair_hull_apart : forall (P : prim) (S : asec) c1 c2,
  (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls P c)) -> Forall (chunk_ok AL) (se_chunks S) -> chunks_sep (se_chunks S) ->
  held_kind (P, S) c1 -> held_kind (P, S) c2 ->
  (forall cv, In cv (prim_of c1) -> ~ In cv (prim_of c2)) -> (forall sc, In sc (sec_of c1) -> ~ In sc (sec_of c2)) ->
  hull_apart c1 c2.
Proof.
  intros P S c1 c2 WF0 SOK SSEP H1 H2 NP NS. unfold hull_apart, hullb, hulln.
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _).
  destruct c1 as [[c v|sc] rz n]; destruct c2 as [[c' v'|sc'] rz' n']; unfold held_kind in H1, H2; cbn [qc_kind prim_of sec_of fst snd] in *.
  - assert (NE : (c, v) <> (c', v')) by (intros EQ; apply (NP (c, v)); [left; reflexivity| left; exact (eq_sym EQ)]).
    exact (proj1 (held_pair_apart AL P c v c' v' AO WF0 H1 H2 NE)).
  - pose proof (held_geo AL P AO WF0 c v H1) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CSZ & _).
    pose proof (region_range AL c Hc) as [RR1 RR2].
    pose proof (proj1 (Forall_forall _ _) SOK sc' H2) as CK. destruct CK as (_ & _ & _ & _ & _ & _ & CK7).
    unfold al_regions in CK7. apply Forall_cons_iff in CK7 as [CSP _]. cbn [fst snd] in CSP. unfold apart in CSP. clear - CSP G1 G2 G3 RR1 RR2. lia.
  - pose proof (held_geo AL P AO WF0 c' v' H2) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CSZ & _).
    pose proof (region_range AL c' Hc) as [RR1 RR2].
    pose proof (proj1 (Forall_forall _ _) SOK sc H1) as CK. destruct CK as (_ & _ & _ & _ & _ & _ & CK7).
    unfold al_regions in CK7. apply Forall_cons_iff in CK7 as [CSP _]. cbn [fst snd] in CSP. unfold apart in CSP. clear - CSP G1 G2 G3 RR1 RR2. lia.
  - destruct (F_sec_B.chunks_sep_In2 _ SSEP sc sc' H1 H2) as [EQ|[AP|AP]].
    + exfalso. apply (NS sc); [left; reflexivity| left; exact (eq_sym EQ)].
    + unfold apart_chunks in AP. lia.
    + unfold apart_chunks in AP. lia.
Qed.

#[using="AO"] Lemma hull_parts : forall X (m : mem) ch A n, RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch -> qc_hull AL ch A n ->
  (hullb ch <= A /\ A + n <= hullb ch + hulln ch /\ 0 <= n)
  \/ (sh (hullb ch) <= A /\ A + n <= sh (hullb ch) + hulln ch / 8 /\ 0 <= n).
Proof.
  intros X m ch A n RP RS HK HU. pose proof (held_hull_geo X m ch RP RS HK) as G. cbv zeta in G.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold hullb, hulln, qc_hull in *.
  destruct ch as [[c v|sc] rz k]; unfold qc_blk, qc_bsize in *; cbn [qc_kind] in *.
  - destruct HU as [[-> ->]|[[-> ->]|[]]]; [left; lia| right]. split; [lia|]. split; [lia|]. Z.div_mod_to_equations; lia.
  - destruct G9 as (_ & S1 & S2).
    assert (SH4 : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - S2; Z.div_mod_to_equations; lia).
    assert (DV : sc_msize sc / 8 = (sc_msize sc - 4096) / 8 + 512) by (clear - G2; Z.div_mod_to_equations; lia).
    destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
    + left. lia.
    + right. rewrite SH4, DV. assert (0 <= (sc_msize sc - 4096) / 8) by (Z.div_mod_to_equations; lia). lia.
    + left. lia.
    + right. rewrite DV. assert (0 <= (sc_msize sc - 4096) / 8) by (Z.div_mod_to_equations; lia). lia.
Qed.

#[using="AO"] Lemma hull_geo : forall X (m : mem) ch, RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch ->
  let B := hullb ch in let n := hulln ch in
  B mod 8 = 0 /\ n mod 8 = 0 /\ 32 <= n /\ 0x609000 <= B /\ B + n <= alloc_ceiling
  /\ (B + n <= 0x7fff7000 \/ 0x10007fff8000 <= B)
  /\ (B + n + 64 <= alloc_ceiling \/ (B + n) mod 64 = 0)
  /\ (B + n <= al_fsb AL \/ al_fsb AL + A0_FS_SIZE <= B)
  /\ B <= qc_blk AL ch /\ qc_blk AL ch + qc_bsize ch = B + n.
Proof.
  intros X m ch RP RS HK B n. pose proof (held_hull_geo X m ch RP RS HK) as G. cbv zeta in G.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  subst B n. unfold hullb, hulln. destruct ch as [[c v|sc] rz k]; unfold held_kind in HK; unfold qc_blk, qc_bsize in *; cbn [qc_kind] in *.
  - repeat (split; [first [assumption | lia]|]). lia.
  - destruct G9 as (_ & S1 & S2). pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & D3 & D4 & _).
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2].
    assert (LOW : sc_beg sc + sc_msize sc < 2147450880 -> sc_beg sc + sc_msize sc <= 2147446784) by (clear - S2 CM2; Z.div_mod_to_equations; lia).
    assert (M64 : (sc_beg sc + sc_msize sc) mod 64 = 0) by (clear - S2 CM2; Z.div_mod_to_equations; lia).
    split; [clear - S2; Z.div_mod_to_equations; lia|]. split; [clear - CM2; Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; exact M64|]. split; [lia|]. split; lia.
Qed.

#[using="AO"] Lemma zone_hull_dj : forall X (m : mem) live W ch, RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch ->
  (forall r, In r live -> lgeo X r) -> Forall (cw_zone live) W ->
  (forall r, In r live -> hull_apart ch (fst r)) ->
  forall A n, qc_hull AL ch A n -> disjoint_from W A n.
Proof.
  intros X m live W ch RP RS HK LG F AP A n HU.
  pose proof (hull_geo X m ch RP RS HK) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  destruct (hull_parts X m ch A n RP RS HK HU) as [(P1 & P2 & P3)|(P1 & P2 & P3)].
  - eapply ATac.disjoint_from_sub; [| exact P1| exact P2]. apply (zone_dj_obj live W). { exact F. }
    unfold off_obj. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    intros r HR. pose proof (AP r HR) as APr. pose proof (LG r HR) as LGr. unfold lgeo in LGr. cbv zeta in LGr.
    destruct LGr as (WFr & LR & HKr & _ & _ & _ & _ & _ & _ & _ & L11 & L12).
    pose proof (hull_geo X m (fst r) RP RS HKr) as Gr. cbv zeta in Gr. destruct Gr as (_ & _ & _ & _ & _ & _ & _ & _ & R9 & R10).
    assert (RU : qc_n (fst r) <= rup8 (qc_n (fst r))) by (unfold rup8; Z.div_mod_to_equations; lia).
    destruct WFr as (_ & _ & W3 & _). unfold hull_apart in APr. unfold lr_ok in LR. lia.
  - eapply ATac.disjoint_from_sub; [| exact P1| exact P2]. apply (zone_dj_shobj X live W); [exact LG| exact F|].
    unfold off_shobj. assert (E8 : 8 * (hulln ch / 8) = hulln ch) by (clear - G2; Z.div_mod_to_equations; lia). rewrite E8.
    split; [Z.div_mod_to_equations; lia|]. split; [exact G1|]. split; [exact G4|]. split; [exact G6|]. split; [| exact G8].
    destruct G7 as [G7|G7]; [left; exact G7| right; split; [exact G7| exact G5]].
Qed.

Ltac demodt H z :=
  unfold id in H;
  lazymatch type of H with
  | ?a mod ?b = 0 => apply (proj1 (Z.mod_divide a b ltac:(lia))) in H; unfold Z.divide in H; destruct H as [z H]
  end.

#[using="Type"] Lemma lchunk_rep_frame_u : forall W (m m' : mem) ch,
  lchunk_rep AL m ch -> qchunk_wf ch -> qc_blk AL ch mod 8 = 0 -> qc_bsize ch mod 8 = 0 -> munch W m m' ->
  disjoint_from W (qc_blk AL ch) (qc_rz ch) ->
  disjoint_from W (qc_blk AL ch + qc_rz ch + qc_n ch) (qc_bsize ch - qc_rz ch - qc_n ch) ->
  (exists ub', rw_cells asegs m' (qc_blk AL ch + qc_rz ch) [CB (Z.to_nat (qc_n ch)) ub']) ->
  disjoint_from W (sh (qc_blk AL ch)) (qc_bsize ch / 8) ->
  match qc_kind ch with
  | QPrim _ _ => True
  | QSec sc => disjoint_from W (sc_beg sc + 32) 4064 /\ disjoint_from W (sh (sc_beg sc)) 512
  end ->
  lchunk_rep AL m' ch.
Proof.
  intros W m m' ch R WF B8 S8 MU DL DR UB' DS DK. unfold lchunk_rep in *. cbv zeta in *.
  destruct WF as (RZ16 & RZM & NR & RZN & _).
  set (B := qc_blk AL ch) in *. set (bs := qc_bsize ch) in *. set (rz := qc_rz ch) in *. set (n := qc_n ch) in *.
  assert (EH : qc_hdr AL ch = B + rz - 16) by reflexivity. rewrite EH in *. clear EH.
  assert (N8 : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
  demodt B8 kb. demodt S8 ks. demodt RZM kr. destruct N8 as [N8 N8m]. demodt N8m kn.
  assert (SHX : forall k, 0 <= k -> sh (B + 8 * k) = sh B + k) by (intros k Hk; unfold sh; rewrite B8; clear - Hk; Z.div_mod_to_equations; lia).
  assert (DV : rz / 8 = 2 * kr /\ rup8 n / 8 = kn /\ bs / 8 = ks /\ (bs - rz - rup8 n) / 8 = ks - 2 * kr - kn)
    by (rewrite RZM, N8m, S8; clear; Z.div_mod_to_equations; lia).
  destruct DV as (DV1 & DV2 & DV3 & DV4). rewrite DV3 in DS.
  assert (TRL : forall A cs, rw_cells asegs m A cs -> B <= A -> A + Z.of_nat (cells_size cs) <= B + rz -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply ATac.disjoint_from_sub; [exact DL| exact H1| exact H2]. }
  assert (TRR : forall A cs, rw_cells asegs m A cs -> B + rz + n <= A -> A + Z.of_nat (cells_size cs) <= B + bs -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply ATac.disjoint_from_sub; [exact DR| exact H1| lia]. }
  assert (TRS : forall A cs, rw_cells asegs m A cs -> sh B <= A -> A + Z.of_nat (cells_size cs) <= sh B + ks -> rw_cells asegs m' A cs).
  { intros A cs X H1 H2. eapply rw_cells_transport_m; [exact X| exact MU|]. eapply ATac.disjoint_from_sub; [exact DS| exact H1| exact H2]. }
  destruct R as ((bits & actx & BITS & R1) & R2 & (ub & R3) & (j4 & R4) & R5 & R6 & R7 & R8).
  split. { exists bits, actx. split; [exact BITS|]. apply TRL; [exact R1| clear - RZ16; lia| cbn [cells_size csize Nat.add]; clear; lia]. }
  split.
  { intros RZ32. destruct (R2 RZ32) as [R2a (j2 & R2b)]. split.
    - apply TRL; [exact R2a| clear; lia| cbn [cells_size csize Nat.add]; clear - RZ32 RZM; lia].
    - exists j2. apply TRL; [exact R2b| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ32 RZM; lia). clear. lia. }
  split. { destruct UB' as (ub' & U'). exists ub'. replace (B + rz - 16 + 16) with (B + rz) by (clear; lia). exact U'. }
  split. { exists j4. apply TRR; [exact R4| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZN N8 NR; lia). clear. lia. }
  split. { apply TRS; [exact R5| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV1, Z2Nat.id by (clear - RZ16 RZM; lia). clear - RZN RZM N8m S8 N8 NR. lia. }
  split.
  { replace (B + rz - 16 + 16) with (B + 8 * (2 * kr)) in * by (clear - RZM; lia). rewrite (SHX (2 * kr)) in * by (clear - RZ16 RZM; lia).
    pose proof (block_shadow_len n ltac:(clear - NR; lia)) as BL. rewrite DV2 in BL.
    apply TRS; [exact R6| clear - RZ16 RZM; lia|]. rewrite cells_size_shadow, BL. clear - RZN RZM N8m S8. lia. }
  split.
  { replace (B + rz - 16 + 16 + rup8 n) with (B + 8 * (2 * kr + kn)) in * by (clear - RZM N8m; lia).
    rewrite (SHX (2 * kr + kn)) in * by (clear - RZ16 RZM N8 NR N8m; lia).
    apply TRS; [exact R7| clear - RZ16 RZM N8 NR N8m; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV4, Z2Nat.id by (clear - RZN RZM N8m S8; lia). clear. lia. }
  destruct (qc_kind ch) as [c v| sc]; [exact I|]. destruct DK as [DK1 DK2]. destruct R8 as [(j7 & R7a) R7b]. split.
  - exists j7. eapply rw_cells_transport_m; [exact R7a| exact MU| cbn [cells_size csize Nat.add]; exact DK1].
  - eapply rw_cells_transport_m; [exact R7b| exact MU| cbn [cells_size csize Nat.add]; exact DK2].
Qed.

#[using="AO"] Lemma zone_hullsh_dj : forall X (m : mem) live W ch, RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch ->
  (forall r, In r live -> lgeo X r) -> Forall (cw_zone live) W ->
  forall A n, sh (hullb ch) <= A -> A + n <= sh (hullb ch) + hulln ch / 8 -> disjoint_from W A n.
Proof.
  intros X m live W ch RP RS HK LG F A n P1 P2.
  pose proof (hull_geo X m ch RP RS HK) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  eapply ATac.disjoint_from_sub; [| exact P1| exact P2]. apply (zone_dj_shobj X live W); [exact LG| exact F|].
  unfold off_shobj. assert (E8 : 8 * (hulln ch / 8) = hulln ch) by (clear - G2; Z.div_mod_to_equations; lia). rewrite E8.
  split; [Z.div_mod_to_equations; lia|]. split; [exact G1|]. split; [exact G4|]. split; [exact G6|]. split; [| exact G8].
  destruct G7 as [G7|G7]; [left; exact G7| right; split; [exact G7| exact G5]].
Qed.

#[using="AO"] Lemma live_part_dj : forall X (m : mem) live W r0, RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  (forall r, In r live -> lgeo X r) -> Forall (cw_zone live) W -> In r0 live ->
  (forall r, In r live -> r = r0 \/ hull_apart (fst r0) (fst r)) ->
  forall A n, 0 <= n -> hullb (fst r0) <= A -> A + n <= hullb (fst r0) + hulln (fst r0) ->
    (A + n <= lc_user AL (fst r0) \/ lc_user AL (fst r0) + qc_n (fst r0) <= A) -> disjoint_from W A n.
Proof.
  intros X m live W r0 RP RS LG F HR0 CASES A n Hn P1 P2 OUT.
  pose proof (LG r0 HR0) as LG0. unfold lgeo in LG0. cbv zeta in LG0. destruct LG0 as (WF0 & LR0 & HK0 & _).
  pose proof (hull_geo X m (fst r0) RP RS HK0) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  apply (zone_dj_obj live W); [exact F|]. unfold off_obj. split; [exact Hn|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros r HR. destruct (CASES r HR) as [->|APr].
  - destruct WF0 as (_ & _ & W3 & _). unfold lr_ok in LR0. lia.
  - pose proof (LG r HR) as LGr. unfold lgeo in LGr. cbv zeta in LGr.
    destruct LGr as (WFr & LR & HKr & _ & _ & _ & _ & _ & _ & _ & L11 & L12).
    pose proof (hull_geo X m (fst r) RP RS HKr) as Gr. cbv zeta in Gr. destruct Gr as (_ & _ & _ & _ & _ & _ & _ & _ & R9 & R10).
    assert (RU : qc_n (fst r) <= rup8 (qc_n (fst r))) by (unfold rup8; Z.div_mod_to_equations; lia).
    destruct WFr as (_ & _ & W3 & _). unfold hull_apart in APr. unfold lr_ok in LR. lia.
Qed.

#[using="AO"] Lemma hull_sh_blk : forall X (m : mem) ch, RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch ->
  sh (hullb ch) <= sh (qc_blk AL ch) /\ sh (qc_blk AL ch) + qc_bsize ch / 8 <= sh (hullb ch) + hulln ch / 8
  /\ match qc_kind ch with QPrim _ _ => True
     | QSec sc => hullb ch = sc_beg sc /\ qc_blk AL ch = sc_beg sc + 4096 /\ 512 <= hulln ch / 8 /\ 4096 <= hulln ch end.
Proof.
  intros X m ch RP RS HK. pose proof (held_hull_geo X m ch RP RS HK) as G. cbv zeta in G.
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold hullb, hulln in *.
  destruct ch as [[c v|sc] rz k]; unfold qc_blk, qc_bsize in *; cbn [qc_kind] in *.
  - split; [lia|]. split; [lia| exact I].
  - destruct G9 as (_ & S1 & S2).
    assert (SH4 : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - S2; Z.div_mod_to_equations; lia).
    assert (DV : sc_msize sc / 8 = (sc_msize sc - 4096) / 8 + 512) by (clear - G2; Z.div_mod_to_equations; lia).
    assert (0 <= (sc_msize sc - 4096) / 8) by (Z.div_mod_to_equations; lia).
    rewrite SH4, DV. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; lia.
Qed.

#[using="AO"] Lemma live_chunk_frame : forall X (m m' : mem) live W r0, RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  (forall r, In r live -> lgeo X r) -> Forall (cw_zone live) W -> In r0 live ->
  (forall r, In r live -> r = r0 \/ hull_apart (fst r0) (fst r)) ->
  lchunk_rep AL m (fst r0) -> munch W m m' -> wmono asegs m m' -> lchunk_rep AL m' (fst r0).
Proof.
  intros X m m' live W r0 RP RS LG F HR0 CASES R MU WM.
  pose proof (LG r0 HR0) as LG0. unfold lgeo in LG0. cbv zeta in LG0.
  destruct LG0 as (WF0 & LR0 & HK0 & _ & _ & _ & _ & L8 & _).
  pose proof (held_hull_geo X m (fst r0) RP RS HK0) as G. cbv zeta in G. destruct G as (G1 & G2 & G3 & _).
  pose proof (hull_geo X m (fst r0) RP RS HK0) as HG. cbv zeta in HG. destruct HG as (_ & _ & _ & _ & _ & _ & _ & _ & H9 & H10).
  pose proof (hull_sh_blk X m (fst r0) RP RS HK0) as (S1 & S2 & S3).
  pose proof WF0 as (W1 & W2 & W3 & W4 & _).
  assert (RU : qc_n (fst r0) <= rup8 (qc_n (fst r0))) by (unfold rup8; Z.div_mod_to_equations; lia).
  assert (EU : lc_user AL (fst r0) = qc_blk AL (fst r0) + qc_rz (fst r0)) by (unfold lc_user, qc_hdr; lia).
  pose proof R as R0. destruct R0 as (_ & _ & (ub & USR) & _).
  change (qc_hdr AL (fst r0) + 16) with (lc_user AL (fst r0)) in USR. rewrite EU in USR, L8.
  eapply (lchunk_rep_frame_u W m m'); [exact R| exact WF0| exact G1| exact G2| exact MU| | | | |].
  - apply (live_part_dj X m live W r0 RP RS LG F HR0 CASES); [lia| exact H9| lia| left; lia].
  - apply (live_part_dj X m live W r0 RP RS LG F HR0 CASES); [lia| lia| lia| right; lia].
  - exact (user_bytes_frame m m' _ _ ub USR WM L8 ltac:(lia)).
  - exact (zone_hullsh_dj X m live W (fst r0) RP RS HK0 LG F _ _ S1 S2).
  - destruct (qc_kind (fst r0)) as [c v|sc] eqn:EK; [exact I|]. destruct S3 as (E1 & E2 & E3 & E4). split.
    + apply (live_part_dj X m live W r0 RP RS LG F HR0 CASES); [lia| lia| lia| left; lia].
    + apply (zone_hullsh_dj X m live W (fst r0) RP RS HK0 LG F); [rewrite E1; lia| rewrite E1; lia].
Qed.

#[using="Type"] Lemma nodup_app_l3 : forall (A : Type) (l1 l2 l3 : list A) x, List.NoDup (l1 ++ l2 ++ l3) -> In x l3 -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A l1 l2 l3 x ND H3. split; intros HX.
  - induction l1 as [|a l1 IH]; [destruct HX|]. cbn [app] in ND. inversion ND as [|a0 l0 NIN ND']; subst.
    destruct HX as [->|HX]; [apply NIN; apply in_or_app; right; apply in_or_app; right; exact H3| exact (IH ND' HX)].
  - apply NoDup_app_remove_l in ND. induction l2 as [|a l2 IH]; [destruct HX|]. cbn [app] in ND. inversion ND as [|a0 l0 NIN ND']; subst.
    destruct HX as [->|HX]; [apply NIN; apply in_or_app; right; exact H3| exact (IH ND' HX)].
Qed.

#[using="Type"] Lemma chunks_sep_app_apart : forall l1 l2 x y, chunks_sep (l1 ++ l2) -> In x l1 -> In y l2 -> apart_chunks x y.
Proof.
  induction l1 as [|a l1 IH]; intros l2 x y CS H1 H2; [destruct H1|]. cbn [app] in CS. inversion CS as [|c0 l0 FA CS']; subst.
  destruct H1 as [->|H1]; [| exact (IH l2 x y CS' H1 H2)].
  exact (proj1 (Forall_forall _ _) FA y (in_or_app _ _ _ (or_intror H2))).
Qed.

Definition bchunk (b : qbatch) : qchunk := mkQC (QPrim K_BCLASS (qb_v b)) 16 1.

#[using="AO FI FSBE"] Lemma quar_apart_live : forall s LB m, RHEAP_B AL E s LB m ->
  (forall ch r, In ch (flat_map qb_chunks (bs_gl s)) -> In r (bs_live s) -> hull_apart ch (fst r))
  /\ (forall b r, In b (bs_gl s) -> In r (bs_live s) -> held_kind (bs_X s) (bchunk b) /\ hull_apart (bchunk b) (fst r)).
Proof.
  intros s LB m R. pose proof (live_lgeo s LB m R) as LG. rheapB R.
  destruct R_DR as (RP & _ & RS & _ & _ & _ & WFS & _ & HKS & (HND & HFA) & _).
  destruct (clear_ctx AL (bs_X s) m RP RS) as (WF0 & SOK & SSEP). cbn [bs_X fst snd] in WF0, SOK, SSEP.
  assert (CSA : chunks_sep (flat_map sec_of (flat_map qb_chunks (bs_gl s)) ++ flat_map sec_of (live_chunks s))) by (eapply chunks_sep_perm; [exact R_SECP| exact SSEP]).
  assert (INS : forall sc, In sc (flat_map sec_of (flat_map qb_chunks (bs_gl s)) ++ flat_map sec_of (live_chunks s)) -> In sc (se_chunks (bs_sec s))).
  { intros sc Hsc. eapply Permutation_in; [apply Permutation_sym; exact R_SECP| exact Hsc]. }
  assert (LIVEP : forall r cv, In r (bs_live s) -> In cv (prim_of (fst r)) -> In cv (heldB s)).
  { intros r cv HR Hcv. unfold heldB, live_chunks. apply in_flat_map. exists (fst r). split; [apply in_map; exact HR| exact Hcv]. }
  assert (LIVES : forall r sc, In r (bs_live s) -> In sc (sec_of (fst r)) -> In sc (flat_map sec_of (live_chunks s))).
  { intros r sc HR Hsc. unfold live_chunks. apply in_flat_map. exists (fst r). split; [apply in_map; exact HR| exact Hsc]. }
  split.
  - intros ch r HCH HR. pose proof (LG r HR) as LGr. unfold lgeo in LGr. cbv zeta in LGr. destruct LGr as (_ & _ & HKr & _).
    pose proof (proj1 (Forall_forall _ _) HKS ch HCH) as HKc.
    apply (pair_hull_apart (bs_prim s) (bs_sec s) ch (fst r) WF0 SOK SSEP HKc HKr).
    + intros cv H1 H2. destruct (nodup_app_l3 _ _ _ _ cv HND (LIVEP r cv HR H2)) as [_ N2]. apply N2. apply in_flat_map. exists ch. split; assumption.
    + intros sc H1 H2. assert (I1 : In sc (flat_map sec_of (flat_map qb_chunks (bs_gl s)))) by (apply in_flat_map; exists ch; split; assumption).
      pose proof (chunks_sep_app_apart _ _ sc sc CSA I1 (LIVES r sc HR H2)) as AP. unfold apart_chunks in AP.
      pose proof (proj1 (Forall_forall _ _) SOK sc (INS sc (in_or_app _ _ _ (or_introl I1)))) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 _]. lia.
  - intros b r HB HR. pose proof (LG r HR) as LGr. unfold lgeo in LGr. cbv zeta in LGr. destruct LGr as (_ & _ & HKr & _).
    assert (HKb : held_kind (bs_X s) (bchunk b)).
    { unfold held_kind, bchunk. cbn [qc_kind bs_X fst]. apply (proj1 (Forall_forall _ _) HFA). apply in_or_app. left. apply in_map_iff. exists b. split; [reflexivity| exact HB]. }
    split; [exact HKb|].
    apply (pair_hull_apart (bs_prim s) (bs_sec s) (bchunk b) (fst r) WF0 SOK SSEP HKb HKr).
    + intros cv H1 H2. destruct (nodup_app_l3 _ _ _ _ cv HND (LIVEP r cv HR H2)) as [N1 _]. apply N1.
      unfold bchunk in H1. cbn [prim_of qc_kind] in H1. destruct H1 as [<-|[]]. apply in_map_iff. exists b. split; [reflexivity| exact HB].
    + intros sc H1 _. unfold bchunk in H1. cbn [sec_of qc_kind] in H1. destruct H1.
Qed.

#[using="Type"] Lemma dj_pt : forall W A n, disjoint_from W A n -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) W.
Proof. induction W as [|[lo hi] W IH]; intros A n D; [constructor|]. cbn in D. destruct D as [D1 D2]. constructor; [exact D1| exact (IH A n D2)]. Qed.

#[using="AO"] Lemma live_region_apart : forall X (m : mem) r i, RPRIM AL (fst X) m -> RSEC AL (snd X) m -> lgeo X r -> (1 <= i < 8)%nat ->
  let rg := nth i (al_regions AL) (0, 0) in
  lc_user AL (fst r) + snd r <= fst rg \/ fst rg + snd rg <= lc_user AL (fst r).
Proof.
  intros X m r i RP RS LGr Hi rg. unfold lgeo in LGr. cbv zeta in LGr.
  destruct LGr as (WFr & LR & HKr & _ & _ & _ & _ & _ & _ & _ & L11 & L12).
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  assert (RU : qc_n (fst r) <= rup8 (qc_n (fst r))) by (unfold rup8; Z.div_mod_to_equations; lia).
  destruct WFr as (_ & _ & W3 & _). unfold lr_ok in LR.
  pose proof (layout_apart AL 0 i AO ltac:(lia) ltac:(lia)) as AP0. fold rg in AP0. cbn [nth al_regions fst snd] in AP0. unfold apart in AP0.
  destruct (fst r) as [[c v|sc] rz n] eqn:ECH; unfold held_kind in HKr; cbn [qc_kind] in HKr; unfold qc_blk, qc_bsize in L11, L12; cbn [qc_kind qc_n] in *.
  - pose proof (held_geo AL (fst X) AO WF0 c v HKr) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CSZ & _).
    pose proof (region_range AL c Hc) as [RR1 RR2]. lia.
  - pose proof (proj1 (Forall_forall _ _) SOK sc HKr) as CK. destruct CK as (_ & _ & _ & _ & _ & _ & CK7).
    pose proof (proj1 (Forall_nth _ (al_regions AL)) CK7 i (0, 0) ltac:(cbn; lia)) as CKi. fold rg in CKi. unfold apart in CKi. lia.
Qed.

#[using="AO"] Lemma zone_dj_region : forall X (m : mem) live W i A n, RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  (forall r, In r live -> lgeo X r) -> Forall (cw_zone live) W -> (1 <= i < 8)%nat -> i <> 4%nat ->
  let rg := nth i (al_regions AL) (0, 0) in 0 <= n -> fst rg <= A -> A + n <= fst rg + snd rg -> disjoint_from W A n.
Proof.
  intros X m live W i A n RP RS LG F Hi N4 rg Hn P1 P2.
  eapply ATac.disjoint_from_sub; [| exact P1| exact P2]. apply (zone_dj_obj live W); [exact F|].
  pose proof (region_facts AL i AO ltac:(lia)) as RF. cbv zeta in RF. fold rg in RF. destruct RF as ((RF1 & _) & RF2 & _ & _ & _ & _ & _).
  assert (SZ : 0 <= snd rg).
  { subst rg. do 8 (destruct i as [|i]; [cbn; lia|]). lia. }
  assert (FSA : fst rg + snd rg <= al_fsb AL \/ al_fsb AL + A0_FS_SIZE <= fst rg).
  { destruct (Nat.lt_ge_cases i 4) as [LT|GE].
    - pose proof (layout_apart AL i 4 AO LT ltac:(lia)) as AP. fold rg in AP. cbn [nth al_regions fst snd] in AP. unfold apart in AP. cbn [nth al_regions fst snd]. lia.
    - pose proof (layout_apart AL 4 i AO ltac:(lia) ltac:(lia)) as AP. fold rg in AP. cbn [nth al_regions fst snd] in AP. unfold apart in AP. lia. }
  unfold off_obj. split; [exact SZ|]. split; [lia|]. split; [exact RF2|]. split; [exact FSA|].
  intros r HR. pose proof (live_region_apart X m r i RP RS (LG r HR) Hi) as LA. cbv zeta in LA. fold rg in LA. lia.
Qed.

Section FRAME.
Variables (X : pstate) (m m' : mem) (live : list (qchunk * Z)) (W : list (Z * Z)).
Hypothesis RP : RPRIM AL (fst X) m.
Hypothesis RS : RSEC AL (snd X) m.
Hypothesis LG : forall r, In r live -> lgeo X r.
Hypothesis F : Forall (cw_zone live) W.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.

#[using="HC AO X m live RP RS LG F"] Lemma fr_ctx : forall A n, 0 <= n -> at_ctx L <= A -> A + n <= at_ctx L + 4096 -> disjoint_from W A n.
Proof. intros A n Hn P1 P2. exact (zone_dj_region X m live W 2 A n RP RS LG F ltac:(lia) ltac:(lia) Hn P1 P2). Qed.
#[using="HC AO X m live RP RS LG F"] Lemma fr_thr : forall A n, 0 <= n -> at_thr L <= A -> A + n <= at_thr L + 4096 -> disjoint_from W A n.
Proof. intros A n Hn P1 P2. exact (zone_dj_region X m live W 3 A n RP RS LG F ltac:(lia) ltac:(lia) Hn P1 P2). Qed.

#[using="HC AO X m live RP RS LG F"] Lemma fr_thread_clear : thread_clear_c W.
Proof.
  unfold thread_clear_c. pose proof (zone_img_out X live W LG F) as IO.
  pose proof (dj_pt W _ _ (fr_ctx (at_ctx L + 152) 8 ltac:(lia) ltac:(lia) ltac:(lia))) as D1.
  pose proof (dj_pt W _ _ (fr_thr (at_thr L + 8) 16 ltac:(lia) ltac:(lia) ltac:(lia))) as D2.
  pose proof (dj_pt W _ _ (fr_thr (at_thr L + 40) 1 ltac:(lia) ltac:(lia) ltac:(lia))) as D3.
  pose proof (dj_pt W _ _ (fr_thr (at_thr L + 3168) 1 ltac:(lia) ltac:(lia) ltac:(lia))) as D4.
  clear - IO D1 D2 D3 D4. induction W as [|iv W' IH]; [constructor|].
  inversion IO; subst. inversion D1; subst. inversion D2; subst. inversion D3; subst. inversion D4; subst.
  constructor; [| apply IH; assumption]. repeat split; try assumption; lia.
Qed.

#[using="HC AO X live W RP RS LG F MU WM"] Lemma fr_thread_env : thread_env L m -> thread_env L m'.
Proof. intros TE. exact (thread_env_frame_c W m m' TE MU WM fr_thread_clear). Qed.

#[using="HC AL AO X live W LG F MU WM"] Lemma fr_poison_env : poison_env E m -> poison_env E m'.
Proof. intros PE. exact (poison_env_frame_c W m m' PE MU WM (zone_img_out X live W LG F)). Qed.

#[using="HC AO X live W RP RS LG F MU"] Lemma fr_thread_env2 : thread_env2 AL m -> thread_env2 AL m'.
Proof.
  intros TE2. eapply thread_env2_frame_m; [exact TE2| exact MU| |].
  - apply fr_thr; lia.
  - apply fr_ctx; lia.
Qed.

#[using="HC AO m live W RP RS LG F MU"] Lemma fr_rprim : RPRIM AL (fst X) m'.
Proof. exact (RPRIM_frame_m AL AO (fst X) W m m' RP MU (prim_clear_of_zone X m live W RP RS LG F)). Qed.

#[using="HC AL AO m live RP RS LG F"] Lemma fr_mapping_hdr : forall d A n, In d (se_chunks (snd X)) -> 0 <= n -> sc_beg d <= A -> A + n <= sc_beg d + 4096 -> disjoint_from W A n.
Proof.
  intros d A n HD Hn P1 P2. destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  pose proof (sec_geo AL (snd X) SOK d HD) as (D1 & D2 & D3 & D4 & _).
  pose proof (proj1 (Forall_forall _ _) SOK d HD) as CK. pose proof (chunk_ok_msize AL d CK) as [CM1 CM2]. destruct CK as (CK1 & _ & _ & _ & _ & _ & CK7).
  pose proof CK7 as CK7'. unfold al_regions in CK7'. apply Forall_cons_iff in CK7' as [CSP CK7']. do 3 apply Forall_cons_iff in CK7' as [_ CK7']. apply Forall_cons_iff in CK7' as [CFS _].
  cbn [fst snd] in CSP, CFS. unfold apart in CSP, CFS.
  assert (LOW : sc_beg d + sc_msize d < 2147450880 -> sc_beg d + sc_msize d <= 2147446784) by (clear - CK1 CM2; Z.div_mod_to_equations; lia).
  apply (zone_dj_obj live W); [exact F|]. unfold off_obj. split; [exact Hn|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros r HR. pose proof (LG r HR) as LGr. unfold lgeo in LGr. cbv zeta in LGr.
  destruct LGr as (WFr & LR & HKr & _ & _ & _ & _ & _ & _ & _ & L11 & L12).
  assert (RU : qc_n (fst r) <= rup8 (qc_n (fst r))) by (unfold rup8; Z.div_mod_to_equations; lia).
  destruct WFr as (_ & _ & W3 & _). unfold lr_ok in LR.
  destruct (fst r) as [[c v|sc] rz k] eqn:ECH; unfold held_kind in HKr; cbn [qc_kind] in HKr; unfold qc_blk, qc_bsize in L11, L12; cbn [qc_kind qc_n] in *.
  - pose proof (held_geo AL (fst X) AO WF0 c v HKr) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CSZ & _).
    pose proof (region_range AL c Hc) as [RR1 RR2]. lia.
  - destruct (F_sec_B.chunks_sep_In2 _ SSEP d sc HD HKr) as [->|[AP|AP]]; unfold apart_chunks in *; lia.
Qed.

#[using="AO m live W RP RS LG F MU WM"] Lemma fr_rsec : RSEC AL (snd X) m'.
Proof.
  eapply (RSEC_frame_but_c (snd X) W m m' RS MU (wmono_but_of_wmono _ _ _ WM) (zone_img_out X live W LG F)).
  - pose proof (region_facts AL 1 AO ltac:(lia)) as RF. cbv zeta in RF. cbn [nth al_regions fst snd] in RF. destruct RF as ((RF1 & _) & _). lia.
  - apply (zone_dj_region X m live W 1 (al_parr AL) (2^23) RP RS LG F); cbn [nth al_regions fst snd]; lia.
  - apply Forall_forall. intros d HD. apply (fr_mapping_hdr d); [exact HD| lia| lia| lia].
Qed.

Variables (WC : list qchunk) (WB : list qbatch).
Hypothesis HKC : Forall (held_kind X) WC.
Hypothesis WFC : Forall qchunk_wf WC.
Hypothesis APC : forall ch r, In ch WC -> In r live -> hull_apart ch (fst r).
Hypothesis APB : forall b r, In b WB -> In r live -> held_kind X (bchunk b) /\ hull_apart (bchunk b) (fst r).
Hypothesis HKB : forall b, In b WB -> held_kind X (bchunk b).

#[using="HC AO X live W RP RS LG F MU HKC WFC APC"] Lemma fr_qchunks : Forall (qchunk_rep AL m) WC -> Forall (qchunk_rep AL m') WC.
Proof.
  intros REPS. apply Forall_forall. intros ch HCH.
  pose proof (proj1 (Forall_forall _ _) REPS ch HCH) as R. pose proof (proj1 (Forall_forall _ _) HKC ch HCH) as HK.
  pose proof (proj1 (Forall_forall _ _) WFC ch HCH) as WF.
  pose proof (held_hull_geo X m ch RP RS HK) as G. cbv zeta in G. destruct G as (G1 & G2 & _).
  assert (HU : forall A n, qc_hull AL ch A n -> disjoint_from W A n) by (exact (zone_hull_dj X m live W ch RP RS HK LG F (fun r HR => APC ch r HCH HR))).
  eapply (qchunk_rep_frame_m AL W m m' ch R WF G1 G2 MU).
  - apply HU. left. split; reflexivity.
  - apply HU. right; left. split; reflexivity.
  - destruct (qc_kind ch) as [c v|sc] eqn:EK; [exact I|]. split; apply HU; right; right; rewrite EK; [left| right]; split; reflexivity.
Qed.

#[using="HC AO X live W RP RS LG F MU APB HKB"] Lemma fr_qbatch : forall b nx, In b WB -> qbatch_rep AL m b nx -> qbatch_rep AL m' b nx.
Proof.
  intros b nx HB R.
  assert (HU : forall A n, qc_hull AL (bchunk b) A n -> disjoint_from W A n)
    by (exact (zone_hull_dj X m live W (bchunk b) RP RS (HKB b HB) LG F (fun r HR => proj2 (APB b r HB HR)))).
  eapply (qbatch_rep_frame_m AL W m m' b nx R MU).
  - apply (HU (qb_addr AL b) 8192). left. split; reflexivity.
  - apply (HU (sh (qb_addr AL b)) 1024). right; left. split; reflexivity.
Qed.

#[using="HC AO X live W RP RS LG F MU APB HKB"] Lemma fr_qlist : forall l nxt, incl l WB -> qlist_rep AL m l nxt -> qlist_rep AL m' l nxt.
Proof.
  induction l as [|b l IH]; intros nxt INC QL; [exact I|]. cbn [qlist_rep] in *. destruct QL as [RB QL].
  split; [apply fr_qbatch; [apply INC; left; reflexivity| exact RB]| apply IH; [intros x Hx; apply INC; right; exact Hx| exact QL]].
Qed.

#[using="HC AO X live W RP RS LG F MU APB HKB"] Lemma fr_qbatches : Forall (fun b => exists nx, qbatch_rep AL m b nx) WB -> Forall (fun b => exists nx, qbatch_rep AL m' b nx) WB.
Proof.
  intros BR. apply Forall_forall. intros b HB. destruct (proj1 (Forall_forall _ _) BR b HB) as (nx & R). exists nx. exact (fr_qbatch b nx HB R).
Qed.

#[using="HC AO X live W RP RS LG F MU WM APB HKB"] Lemma fr_qcache : forall l, incl l WB -> qcache_rep AL m (at_thr L + TQ_OFF) l -> qcache_rep AL m' (at_thr L + TQ_OFF) l.
Proof.
  intros l INC [C QL]. split; [| exact (fr_qlist l 0 INC QL)].
  eapply rw_cells_transport; [exact C| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. apply fr_thr; lia.
Qed.

#[using="HC AL AO X live LG F"] Lemma fr_img : forall A n, img_gap A n -> disjoint_from W A n.
Proof. intros A n G. exact (zone_dj_img X live W A n LG F G). Qed.

Ltac fr_cell C := eapply rw_cells_transport; [exact C| exact MU| exact WM| apply fr_img; unfold img_gap; cbn; lia].

#[using="HC AO X live W RP RS LG F MU WM"] Lemma fr_depot : forall hs total, RDEPOT (al_depot AL) hs total m -> RDEPOT (al_depot AL) hs total m'.
Proof.
  intros hs total RD. eapply RDEPOT_frame; [exact RD| exact MU| exact WM|]. unfold depot_apart.
  pose proof AO as (_ & _ & _ & _ & DLO & SWB). destruct DLO as (_ & _ & _ & _ & _ & _ & SW0 & _).
  pose proof (dj_pt W _ _ (fr_img SSA (DM1 + 8 - SSA) ltac:(unfold img_gap; lia))) as D1.
  pose proof (dj_pt W _ _ (zone_dj_region X m live W 5 (DN0 (al_depot AL)) (2^20) RP RS LG F ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia))) as D2.
  pose proof (dj_pt W _ _ (zone_dj_region X m live W 6 (SS0 (al_depot AL)) (SWIN (al_depot AL)) RP RS LG F ltac:(lia) ltac:(lia) SW0 ltac:(cbn; lia) ltac:(cbn; lia))) as D3.
  clear - D1 D2 D3. induction W as [|iv W' IH]; [constructor|].
  inversion D1; subst. inversion D2; subst. inversion D3; subst. constructor; [| apply IH; assumption]. repeat split; lia.
Qed.

#[using="HC AL AO X live W LG F MU WM"] Lemma fr_quar_env : quar_env m -> quar_env m'.
Proof. intros (C1 & C2). split; [fr_cell C1| fr_cell C2]. Qed.
#[using="HC AL AO X live W LG F MU WM"] Lemma fr_hooks_env : hooks_env m -> hooks_env m'.
Proof. intros C. unfold hooks_env in *. fr_cell C. Qed.
#[using="HC AL AO X live W LG F MU WM"] Lemma fr_trace_env : trace_env m -> trace_env m'.
Proof. intros (C1 & C2 & C3). split; [fr_cell C1| split; [fr_cell C2| fr_cell C3]]. Qed.
#[using="HC AL AO X live W LG F MU WM"] Lemma fr_alloc_env : alloc_env m -> alloc_env m'.
Proof. intros AE. ae_split AE. unfold alloc_env. repeat match goal with |- _ /\ _ => split end; match goal with C : rw_cells _ m ?A _ |- rw_cells _ m' ?A _ => fr_cell C end. Qed.

#[using="HC AO X m live RP RS LG F"] Lemma fr_dtls : forall A n, 0 <= n -> al_dtls AL <= A -> A + n <= al_dtls AL + 4096 -> disjoint_from W A n.
Proof. intros A n Hn P1 P2. exact (zone_dj_region X m live W 7 A n RP RS LG F ltac:(lia) ltac:(lia) Hn P1 P2). Qed.
#[using="AO X live W RP RS LG F MU"] Lemma fr_fte : fs_tls_env (at_thr L) A0_DTV A0_TLSB (al_dtls AL) (al_fsb AL) m -> fs_tls_env (at_thr L) A0_DTV A0_TLSB (al_dtls AL) (al_fsb AL) m'.
Proof.
  intros FTE. eapply (fs_tls_env_frame_m _ _ _ _ _ W m m' FTE MU). unfold fte_apart.
  repeat match goal with |- _ /\ _ => split end;
    first [ apply fr_img; unfold img_gap; cbn; lia | apply fr_dtls; lia | apply fr_thr; lia ].
Qed.
#[using="HC AL AO X live W LG F MU WM"] Lemma fr_mtx : rw_cells asegs m QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]] -> rw_cells asegs m' QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]].
Proof. intros C. fr_cell C. Qed.

#[using="HC AO X live W LG F MU WM"] Lemma fr_gq : forall l, rw_cells asegs m QUAR_GQ (qcells AL l) -> rw_cells asegs m' QUAR_GQ (qcells AL l).
Proof. intros l C. unfold qcells in *. fr_cell C. Qed.

#[using="HC AL AO X live W LG F MU WM"] Lemma fr_ia : forall inited, ia_cells 262144 262728 inited m -> ia_cells 262144 262728 inited m'.
Proof.
  intros inited (C1 & (j0 & C2) & (j2 & C3 & Z3) & (j3 & C4) & (j4 & C5) & (j1 & C6)).
  assert (TR : forall A N j, 0 <= N -> rw_cells asegs m A [CB (Z.to_nat N) j] -> img_gap A N -> rw_cells asegs m' A [CB (Z.to_nat N) j]).
  { intros A N j HN C G. eapply rw_cells_transport; [exact C| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact HN. exact (fr_img A N G). }
  split. { unfold ia_flag in *. fr_cell C1. }
  split. { exists j0. fr_cell C2. }
  split. { exists j2. split; [| exact Z3]. apply TR; [lia| exact C3| unfold img_gap; lia]. }
  split. { exists j3. fr_cell C4. }
  split. { exists j4. apply TR; [lia| exact C5| unfold img_gap; lia]. }
  exists j1. fr_cell C6.
Qed.

#[using="HC AO X W RP RS LG F MU WM"] Lemma fr_live : (forall r0 r, In r0 live -> In r live -> r = r0 \/ hull_apart (fst r0) (fst r)) ->
  Forall (lchunk_rep AL m) (map fst live) -> Forall (lchunk_rep AL m') (map fst live).
Proof.
  intros CASES REPS. apply Forall_forall. intros ch HCH. apply in_map_iff in HCH as (r0 & <- & HR0).
  pose proof (proj1 (Forall_forall _ _) REPS (fst r0) (in_map fst _ _ HR0)) as R.
  exact (live_chunk_frame X m m' live W r0 RP RS LG F HR0 (fun r HR => CASES r0 r HR0 HR) R MU WM).
Qed.
End FRAME.

#[using="AO"] Lemma live_sep_hull : forall (P : prim) (S : asec) l,
  (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls P c)) -> Forall (chunk_ok AL) (se_chunks S) -> chunks_sep (se_chunks S) ->
  Forall (held_kind (P, S)) l ->
  List.NoDup (flat_map prim_of l) -> chunks_sep (flat_map sec_of l) -> incl (flat_map sec_of l) (se_chunks S) ->
  ForallOrdPairs hull_apart l.
Proof.
  intros P S l WF0 SOK SSEP. induction l as [|ch l IH]; intros HK ND CS INC; [constructor|].
  cbn [flat_map] in ND, CS, INC. inversion HK as [|x xs HKc HKl]; subst.
  assert (NDl : List.NoDup (flat_map prim_of l)) by (apply NoDup_app_remove_l in ND; exact ND).
  assert (CSl : chunks_sep (flat_map sec_of l)) by (exact (chunks_sep_app_r _ _ CS)).
  assert (INCl : incl (flat_map sec_of l) (se_chunks S)) by (intros x Hx; apply INC; apply in_or_app; right; exact Hx).
  constructor; [| exact (IH HKl NDl CSl INCl)].
  apply Forall_forall. intros ch' Hch'. pose proof (proj1 (Forall_forall _ _) HKl ch' Hch') as HK'.
  apply (pair_hull_apart P S ch ch' WF0 SOK SSEP HKc HK').
  - intros cv H1 H2. assert (IN' : In cv (flat_map prim_of l)) by (apply in_flat_map; exists ch'; split; assumption).
    exact (proj2 (nodup_app_l3 _ [] (prim_of ch) (flat_map prim_of l) cv ND IN') H1).
  - intros sc H1 H2. assert (IN' : In sc (flat_map sec_of l)) by (apply in_flat_map; exists ch'; split; assumption).
    pose proof (chunks_sep_app_apart _ _ sc sc CS H1 IN') as AP. unfold apart_chunks in AP.
    pose proof (proj1 (Forall_forall _ _) SOK sc (INCl sc IN')) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 _]. lia.
Qed.

#[using="AO"] Lemma live_fop_hull : forall s LB m, RHEAP_B AL E s LB m -> ForallOrdPairs hull_apart (live_chunks s).
Proof.
  intros s LB m R. rheapB R. destruct R_DR as (RP & _ & RS & _ & _ & _ & _ & _ & _ & (HND & HFA) & _).
  destruct (clear_ctx AL (bs_X s) m RP RS) as (WF0 & SOK & SSEP). cbn [bs_X fst snd] in *.
  apply (live_sep_hull (bs_prim s) (bs_sec s)); [exact WF0| exact SOK| exact SSEP| exact R_HK| | |].
  - apply NoDup_app_remove_l in HND. apply NoDup_app_remove_l in HND. exact HND.
  - eapply chunks_sep_app_r. eapply chunks_sep_perm; [exact R_SECP| exact SSEP].
  - intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact R_SECP|]. apply in_or_app. right. exact Hx.
Qed.

#[using="Type"] Lemma fop_map_cases : forall (A B : Type) (R : B -> B -> Prop) (f : A -> B) (l : list A) x y,
  (forall a b, R a b -> R b a) -> ForallOrdPairs R (map f l) -> In x l -> In y l -> x = y \/ R (f x) (f y).
Proof.
  intros A B R f l x y SYM. induction l as [|a l IH]; intros H Hx Hy; [destruct Hx|].
  cbn [map] in H. inversion H as [|a0 l0 FA FOP]; subst.
  destruct Hx as [->|Hx]; destruct Hy as [->|Hy].
  - left; reflexivity.
  - right. exact (proj1 (Forall_forall _ _) FA (f y) (in_map f _ _ Hy)).
  - right. apply SYM. exact (proj1 (Forall_forall _ _) FA (f x) (in_map f _ _ Hx)).
  - exact (IH FOP Hx Hy).
Qed.

#[using="AO"] Lemma live_cases : forall s LB m, RHEAP_B AL E s LB m ->
  forall r0 r, In r0 (bs_live s) -> In r (bs_live s) -> r = r0 \/ hull_apart (fst r0) (fst r).
Proof.
  intros s LB m R r0 r H0 H1. pose proof (live_fop_hull s LB m R) as FOP. unfold live_chunks in FOP.
  destruct (fop_map_cases _ _ hull_apart fst (bs_live s) r0 r ltac:(unfold hull_apart; intros a b K; lia) FOP H0 H1) as [->|K]; [left; reflexivity| right; exact K].
Qed.

#[using="AO FSBE"] Lemma law_heap_frame : forall s LB m m' W,
  RHEAP_B AL E s LB m -> munch W m m' -> wmono asegs m m' -> Forall (cw_class LB) W -> RHEAP_B AL E s LB m'.
Proof.
  intros s LB m m' W R MU WM FC.
  assert (F : Forall (cw_zone (bs_live s)) W) by (eapply Forall_impl; [| exact FC]; intros iv Hiv; exact (cw_zone_of_class s LB m iv R Hiv)).
  pose proof (live_lgeo s LB m R) as LG. pose proof (live_cases s LB m R) as CASES.
  destruct (quar_apart_live s LB m R) as [APC APB]. pose proof R as R0. rheapB R.
  destruct R_DR as (RP & POK & RS & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
  assert (HKB : forall b, In b (bs_gl s) -> held_kind (bs_X s) (bchunk b)).
  { intros b HB. unfold held_kind, bchunk. cbn [qc_kind]. destruct HOK as [_ HFA]. apply (proj1 (Forall_forall _ _) HFA). apply in_or_app. left.
    apply in_map_iff. exists b. split; [reflexivity| exact HB]. }
  assert (GLG : incl (q_glob (bs_quar s)) (bs_gl s)) by (intros b Hb; unfold bs_gl; apply in_or_app; left; exact Hb).
  assert (GLL : incl (q_loc (bs_quar s)) (bs_gl s)) by (intros b Hb; unfold bs_gl; apply in_or_app; right; exact Hb).
  unfold RHEAP_B. cbv zeta.
  split; [exact R_PERM|]. split; [exact R_LR|]. split; [exact R_AO|].
  split.
  { unfold dr_invB.
    split; [exact (fr_rprim (bs_X s) m m' (bs_live s) W RP RS LG F MU)|]. split; [exact POK|].
    split; [exact (fr_rsec (bs_X s) m m' (bs_live s) W RP RS LG F MU WM)|].
    split; [exact (fr_poison_env (bs_X s) m m' (bs_live s) W LG F MU WM PE)|].
    split; [exact (fr_thread_env (bs_X s) m m' (bs_live s) W RP RS LG F MU WM TE)|].
    split; [exact (shvis_wmono _ m m' SV WM)|]. split; [exact WFS|].
    split; [exact (fr_qchunks (bs_X s) m m' (bs_live s) W RP RS LG F MU _ HKS WFS APC REPS)|].
    split; [exact HKS|]. split; [exact HOK|]. split; [exact NDS|]. split; [exact BWF|].
    exact (fr_qbatches (bs_X s) m m' (bs_live s) W RP RS LG F MU _ APB HKB BREP). }
  split; [exact (fr_qlist (bs_X s) m m' (bs_live s) W RP RS LG F MU _ APB HKB _ 0 GLG R_QL)|].
  split; [exact (fr_gq (bs_X s) m m' (bs_live s) W LG F MU WM _ R_GQ)|].
  split; [exact (fr_qcache (bs_X s) m m' (bs_live s) W RP RS LG F MU WM _ APB HKB _ GLL R_QC)|].
  split; [exact (fr_mtx (bs_X s) m m' (bs_live s) W LG F MU WM R_MTX)|].
  split; [exact (fr_quar_env (bs_X s) m m' (bs_live s) W LG F MU WM R_QE)|]. split; [exact R_QWF|].
  split; [exact (fr_depot (bs_X s) m m' (bs_live s) W RP RS LG F MU WM _ _ R_DEP)|]. split; [exact R_DOK|].
  split; [exact R_WF|].
  split; [exact (fr_live (bs_X s) m m' (bs_live s) W RP RS LG F MU WM CASES R_REP)|].
  split; [exact R_HK|]. split; [exact R_SECP|]. split; [exact R_COV|].
  split; [exact (fr_thread_env2 (bs_X s) m m' (bs_live s) W RP RS LG F MU R_TE2)|].
  split; [exact (fr_hooks_env (bs_X s) m m' (bs_live s) W LG F MU WM R_HE)|].
  split; [exact (fr_trace_env (bs_X s) m m' (bs_live s) W LG F MU WM R_TRE)|].
  split; [exact (fr_alloc_env (bs_X s) m m' (bs_live s) W LG F MU WM R_AENV)|].
  split; [destruct R_IA as (inited & IA); exists inited; exact (fr_ia (bs_X s) m m' (bs_live s) W LG F MU WM inited IA)|].
  split; [exact R_CLS|]. split; [exact R_QCLS|]. split; [exact R_SLK|]. split; [exact R_BUD|].
  exact (fr_fte (bs_X s) m m' (bs_live s) W RP RS LG F MU R_FTE).
Qed.

Definition shrd (m : mem) (lo hi : Z) : Prop := forall a, lo <= a < hi -> exists v, mrd asegs m (wa a) = Some v.

#[using="Type"] Lemma shrd_cells : forall (m : mem) A cs, rw_cells asegs m A cs -> shrd m A (A + Z.of_nat (cells_size cs)).
Proof. intros m A cs C a Ha. exact (rw_cells_mrd m A cs a C Ha). Qed.
#[using="Type"] Lemma shrd_app : forall (m : mem) a b c, shrd m a b -> shrd m b c -> shrd m a c.
Proof. intros m a b c H1 H2 x Hx. destruct (Z_lt_ge_dec x b) as [LT|GE]; [apply H1; lia| apply H2; lia]. Qed.
#[using="Type"] Lemma shrd_sub : forall (m : mem) a b a' b', shrd m a b -> a <= a' -> b' <= b -> shrd m a' b'.
Proof. intros m a b a' b' H H1 H2 x Hx. apply H. lia. Qed.
#[using="Type"] Lemma shrd_cb : forall (m : mem) A N j, 0 <= N -> rw_cells asegs m A [CB (Z.to_nat N) j] -> shrd m A (A + N).
Proof. intros m A N j HN C. pose proof (shrd_cells m A _ C) as S. cbn [cells_size csize] in S. rewrite Nat.add_0_r, Z2Nat.id in S by exact HN. exact S. Qed.

#[using="Type"] Lemma sh_parts : forall B bs rz n, B mod 8 = 0 -> bs mod 8 = 0 -> rz mod 16 = 0 -> 16 <= rz -> 1 <= n -> rz + rup8 n <= bs ->
  sh (B + rz - 16 + 16) = sh B + rz / 8 /\ sh (B + rz - 16 + 16 + rup8 n) = sh B + rz / 8 + rup8 n / 8
  /\ rz / 8 + rup8 n / 8 + (bs - rz - rup8 n) / 8 = bs / 8 /\ 0 <= rz / 8 /\ 0 <= rup8 n / 8 /\ 0 <= (bs - rz - rup8 n) / 8.
Proof.
  intros B bs rz n B8 S8 RZM RZ16 N1 RZN.
  assert (N8 : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
  destruct N8 as [N8 N8m]. unfold sh, SHADOW_OFF. repeat split; Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma qchunk_shrd : forall (m : mem) ch, qchunk_rep AL m ch -> qchunk_wf ch -> qc_blk AL ch mod 8 = 0 -> qc_bsize ch mod 8 = 0 ->
  shrd m (sh (qc_blk AL ch)) (sh (qc_blk AL ch) + qc_bsize ch / 8).
Proof.
  intros m ch R (RZ16 & RZM & NR & RZN & _) B8 S8. unfold qchunk_rep in R. cbv zeta in R.
  destruct R as (_ & _ & _ & R4 & R5 & R6 & _). unfold qc_hdr in R5, R6.
  destruct (sh_parts _ _ _ _ B8 S8 RZM RZ16 (proj1 NR) RZN) as (E1 & E2 & E3 & P1 & P2 & P3). rewrite E1 in R5. rewrite E2 in R6. rewrite <- E3.
  pose proof (shrd_cb m _ _ _ P1 R4) as S1. pose proof (shrd_cb m _ _ _ P2 R5) as S2. pose proof (shrd_cb m _ _ _ P3 R6) as S3.
  eapply shrd_app; [exact S1|]. eapply shrd_app; [exact S2|]. eapply shrd_sub; [exact S3| lia| lia].
Qed.

#[using="Type"] Lemma lchunk_shrd : forall (m : mem) ch, lchunk_rep AL m ch -> qchunk_wf ch -> qc_blk AL ch mod 8 = 0 -> qc_bsize ch mod 8 = 0 ->
  shrd m (sh (qc_blk AL ch)) (sh (qc_blk AL ch) + qc_bsize ch / 8).
Proof.
  intros m ch R (RZ16 & RZM & NR & RZN & _) B8 S8. unfold lchunk_rep in R. cbv zeta in R.
  destruct R as (_ & _ & _ & _ & R4 & R5 & R6 & _). unfold qc_hdr in R5, R6.
  destruct (sh_parts _ _ _ _ B8 S8 RZM RZ16 (proj1 NR) RZN) as (E1 & E2 & E3 & P1 & P2 & P3). rewrite E1 in R5. rewrite E2 in R6. rewrite <- E3.
  pose proof (shrd_cb m _ _ _ P1 R4) as S1. pose proof (shrd_cells m _ _ R5) as S2. rewrite cells_size_shadow, (block_shadow_len (qc_n ch) ltac:(lia)) in S2.
  pose proof (shrd_cb m _ _ _ P3 R6) as S3.
  eapply shrd_app; [exact S1|]. eapply shrd_app; [exact S2|]. eapply shrd_sub; [exact S3| lia| lia].
Qed.

#[using="AO"] Lemma prim_class_shrd : forall s LB m c, RHEAP_B AL E s LB m -> 1 <= c <= 31 ->
  shrd m (sh (region AL c)) (sh (region AL c + p_mu (get_cls (bs_prim s) c))).
Proof.
  intros s LB m c R Hc a Ha. rheapB R.
  destruct R_DR as (RP & POK & RS & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
  pose proof RP as (_ & _ & CLS & _). destruct (CLS c Hc) as (WFk & _ & _ & _ & TAIL & FREE). cbn [bs_X fst] in *.
  pose proof (class_size_pos c Hc) as CS. pose proof (class_size_mod16 c Hc) as CM.
  destruct WFk as (_ & _ & _ & _ & _ & _ & AU & MUF & MUM & AUM & _).
  set (k := get_cls (bs_prim s) c) in *. set (csz := class_size c) in *.
  pose proof AO as (_ & _ & SP16 & _). layout_facts AO 0%nat SPF. destruct SPF as (SP1 & _).
  assert (RG : region AL c = al_space AL + c * K_REGION) by reflexivity.
  assert (RG64 : region AL c mod 64 = 0) by (rewrite RG; clear - SP16; Z.div_mod_to_equations; lia).
  assert (RGP : 0 <= region AL c) by (rewrite RG; lia).
  set (RGN := region AL c) in *.
  assert (SHR : forall y, 0 <= y -> y mod 8 = 0 -> sh (RGN + y) = sh RGN + y / 8) by (intros y Y0 Y8; unfold sh; clear - RG64 Y0 Y8; Z.div_mod_to_equations; lia).
  assert (MU8 : p_mu k mod 8 = 0) by (clear - MUM; Z.div_mod_to_equations; lia).
  assert (AU8 : p_au k mod 8 = 0) by (clear - AUM CM; Z.div_mod_to_equations; lia).
  rewrite (SHR (p_mu k) ltac:(lia) MU8) in Ha.
  set (d := a - sh RGN) in *. assert (Hd : 0 <= d < p_mu k / 8) by (unfold d; lia).
  destruct (Z_lt_ge_dec (8 * d) (p_au k)) as [CARVED|TAILC].
  -
    set (i := (8 * d) / csz). set (q := csz / 16).
    assert (QE : csz = 16 * q) by (unfold q; clear - CM; Z.div_mod_to_equations; lia).
    assert (IR : i * csz <= 8 * d < i * csz + csz) by (unfold i; clear - CS Hd; Z.div_mod_to_equations; lia).
    assert (I0 : 0 <= i) by (unfold i; apply Z.div_pos; lia).
    set (v := i * q).
    assert (V16 : 16 * v = i * csz) by (unfold v; rewrite QE; ring).
    assert (VAU : 16 * v + csz <= p_au k).
    { rewrite V16. clear - IR CARVED AUM CS I0. apply Z.mod_divide in AUM; [| lia]. destruct AUM as [t Ht]. rewrite Ht in *.
      assert (IT : i < t) by nia. nia. }
    assert (VM : (16 * v) mod csz = 0) by (rewrite V16; apply Z.mod_mul; lia).
    assert (V0 : 0 <= v) by (unfold v; nia).
    assert (INB : sh (RGN + 16 * v) <= a < sh (RGN + 16 * v) + csz / 8).
    { rewrite (SHR (16 * v) ltac:(lia) ltac:(clear; Z.div_mod_to_equations; lia)). unfold d in IR. rewrite V16. clear - IR CM CS. Z.div_mod_to_equations. lia. }
    destruct (R_COV c v Hc V0 VAU VM) as [FR|HELD].
    + destruct (FREE v FR) as [_ SHC]. fold RGN csz in SHC. assert (C8 : 0 <= csz / 8) by (clear - CS; Z.div_mod_to_equations; lia). apply (shrd_cb m _ (csz / 8) _ C8 SHC). exact INB.
    + unfold allheld, F_quar_DR.tc_of in HELD. apply in_app_or in HELD as [HELD|HELD]; [apply in_app_or in HELD as [HELD|HELD]|].
      * apply in_map_iff in HELD as (b & EB & HB). unfold bpair in EB. injection EB as EC EV. subst c.
        destruct (proj1 (Forall_forall _ _) BREP b HB) as (nx & (_ & _ & SHB)). unfold qb_addr in SHB. fold RGN in SHB. rewrite EV in SHB.
        pose proof (shrd_cb m _ 1024 _ ltac:(lia) SHB) as S. apply S. change (class_size K_BCLASS) with 8192 in csz. subst csz. change (8192 / 8) with 1024 in INB. exact INB.
      * apply in_flat_map in HELD as (ch & HCH & HP). destruct ch as [[c' v'|sc] rz n]; cbn [prim_of qc_kind] in HP; [| destruct HP].
        destruct HP as [EQ|[]]. injection EQ as -> ->.
        pose proof (proj1 (Forall_forall _ _) REPS _ HCH) as RC. pose proof (proj1 (Forall_forall _ _) WFS _ HCH) as WC. pose proof (proj1 (Forall_forall _ _) HKS _ HCH) as HK.
        pose proof (held_hull_geo (bs_X s) m _ RP RS HK) as G. cbv zeta in G. destruct G as (G1 & G2 & _).
        exact (qchunk_shrd m _ RC WC G1 G2 a INB).
      * unfold heldB in HELD. apply in_flat_map in HELD as (ch & HCH & HP). destruct ch as [[c' v'|sc] rz n]; cbn [prim_of qc_kind] in HP; [| destruct HP].
        destruct HP as [EQ|[]]. injection EQ as -> ->.
        pose proof (proj1 (Forall_forall _ _) R_REP _ HCH) as RC. pose proof (proj1 (Forall_forall _ _) R_WF _ HCH) as WC. pose proof (proj1 (Forall_forall _ _) R_HK _ HCH) as HK.
        pose proof (held_hull_geo (bs_X s) m _ RP RS HK) as G. cbv zeta in G. destruct G as (G1 & G2 & _).
        exact (lchunk_shrd m _ RC WC G1 G2 a INB).
  -
    destruct TAIL as [_ SHT]. fold RGN k in SHT. rewrite (SHR (p_au k) ltac:(lia) AU8) in SHT.
    assert (T8 : 0 <= (p_mu k - p_au k) / 8) by (clear - AU; Z.div_mod_to_equations; lia). apply (shrd_cb m _ ((p_mu k - p_au k) / 8) _ T8 SHT). unfold d in *. clear - TAILC Hd AU8 MU8 AU. Z.div_mod_to_equations. lia.
Qed.

#[using="AO FI FSBE"] Lemma law_block_shread : forall s LB m b, RHEAP_B AL E s LB m -> In b LB -> sh_readable m (blk_addr b) (blk_size b).
Proof.
  intros s LB m b R HIN. destruct (live_of_block2 s LB m b R HIN) as (r & HR & -> & LR & WF & REP & HK & SL & RP & RS).
  unfold blk_ofB, blk_addr, blk_size, sh_readable. cbn [fst snd]. intros Hn a Ha.
  pose proof (live_geo (bs_X s) m (fst r) RP RS HK WF SL) as G. cbv zeta in G. destruct G as (G1 & G2 & _ & _ & _ & _ & G7 & G8).
  destruct LR as [EN|[EN _]]; [| lia]. rewrite EN in *.
  assert (RU : qc_n (fst r) <= rup8 (qc_n (fst r))) by (unfold rup8; Z.div_mod_to_equations; lia).
  pose proof (held_hull_geo (bs_X s) m (fst r) RP RS HK) as HG. cbv zeta in HG. destruct HG as (H1 & H2 & H3 & H4 & _ & _ & _ & _ & H9).
  set (A := lc_user AL (fst r)) in *. set (n := qc_n (fst r)) in *.
  destruct (fst r) as [[c v|sc] rz k] eqn:ECH; unfold held_kind in HK; cbn [qc_kind] in HK, H9; unfold qc_blk, qc_bsize in *; cbn [qc_kind] in *.
  -
    destruct (clear_ctx AL (bs_X s) m RP RS) as (WF0 & _ & _). cbn [bs_X fst] in *.
    pose proof (held_geo AL (bs_prim s) AO WF0 c v HK) as HGE. cbv zeta in HGE. destruct HGE as (Hc & E1 & E2 & _).
    destruct (WF0 c Hc) as (_ & _ & _ & _ & _ & _ & AU & MUF & MUM & _).
    pose proof AO as (_ & _ & SP16 & _). layout_facts AO 0%nat SPF. destruct SPF as (SP1 & _).
    assert (RG : region AL c = al_space AL + c * K_REGION) by reflexivity.
    apply (prim_class_shrd s LB m c R Hc).
    set (RGN := region AL c) in *. set (pmu := p_mu (get_cls (bs_prim s) c)) in *.
    assert (RG64 : RGN mod 64 = 0) by (rewrite RG; clear - SP16; Z.div_mod_to_equations; lia).
    assert (RGP : 0x609000 <= RGN) by (rewrite RG; lia).
    unfold sh, SHADOW_OFF in *. clear - Ha Hn G7 G8 RU E1 E2 AU MUM RG64 RGP. Z.div_mod_to_equations. lia.
  -
    destruct H9 as (_ & S1 & S2). pose proof REP as REP0. destruct REP0 as (_ & _ & _ & _ & _ & _ & _ & (_ & SHH)).
    pose proof (lchunk_shrd m _ REP WF H1 H2) as SB. unfold qc_blk, qc_bsize in SB. cbn [qc_kind] in SB.
    pose proof (shrd_cb m _ 512 _ ltac:(lia) SHH) as SH0.
    assert (SH4 : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - S2; Z.div_mod_to_equations; lia).
    rewrite SH4 in SB. pose proof (shrd_app m _ _ _ SH0 SB) as SALL. apply SALL.
    destruct (clear_ctx AL (bs_X s) m RP RS) as (_ & SOK & _).
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2].
    unfold sh, SHADOW_OFF in *. clear - Ha Hn G7 G8 RU S1 S2 CM1 CM2. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma law_fsenv : forall (FI0 : fs_if),
  (forall m, thread_env (al_thread AL) m -> fs_tls_env (at_thr (al_thread AL)) A0_DTV A0_TLSB (al_dtls AL) (al_fsb AL) m -> FSENV FI0 m) ->
  forall s LB m, RHEAP_B AL E s LB m -> FSENV FI0 m.
Proof.
  intros FI0 FSEI s LB m R. rheapB R. destruct R_DR as (_ & _ & _ & _ & TE & _). exact (FSEI m TE R_FTE).
Qed.

End LAWS.
