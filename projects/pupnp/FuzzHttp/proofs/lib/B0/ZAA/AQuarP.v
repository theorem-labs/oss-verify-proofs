(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD F_sec_A F_sec_C AQuar F_quar_Ep F_quar_E AQuarM AHeap AFoot AQuarR AQuarS.
Import ListNotations.
Open Scope Z_scope.

Lemma outside_In_p : forall W x iv, outside W x -> In iv W -> ~ (fst iv <= x < snd iv).
Proof.
  induction W as [|[lo hi] W IH]; intros x iv O Hin; [destruct Hin|]. cbn [outside] in O. destruct O as [O1 O2].
  destruct Hin as [<-|Hin]; [exact O1| exact (IH x iv O2 Hin)].
Qed.
Lemma sub_fp_of_incl : forall W1 W2, incl W1 W2 -> sub_fp W1 W2.
Proof.
  intros W1 W2 I12 x O. induction W1 as [|[lo hi] W1 IH]; cbn [outside]; [exact I|].
  split; [exact (outside_In_p W2 x (lo, hi) O (I12 _ (or_introl eq_refl)))| apply IH; intros iv Hiv; apply I12; right; exact Hiv].
Qed.

Lemma q_enq_chunks : forall l ch v, flat_map qb_chunks (q_enq l ch v) = flat_map qb_chunks l ++ [ch].
Proof.
  intros l ch v. destruct l as [|b0 l0] using rev_ind; [reflexivity|]. rewrite q_enq_snoc.
  destruct (qb_count b0 =? Q_BATCH).
  - rewrite flat_map_app. reflexivity.
  - rewrite !flat_map_app. cbn [flat_map qb_chunks]. rewrite !app_nil_r, app_assoc. reflexivity.
Qed.
Lemma q_enq_vs : forall l ch v, map qb_v (q_enq l ch v) = map qb_v l ++ (if need_batch l then [v] else []).
Proof.
  intros l ch v. destruct l as [|b0 l0] using rev_ind; [reflexivity|]. rewrite q_enq_snoc, need_batch_snoc.
  destruct (qb_count b0 =? Q_BATCH).
  - rewrite map_app. reflexivity.
  - rewrite !map_app. cbn [map qb_v]. rewrite app_nil_r. reflexivity.
Qed.
Lemma q_enq_bytes : forall l ch v, qbytes (q_enq l ch v) = qbytes l + qc_n ch + (if need_batch l then Q_BBYTES else 0).
Proof.
  intros l ch v. destruct l as [|b0 l0] using rev_ind; [cbn; lia|]. rewrite q_enq_snoc, need_batch_snoc.
  destruct (qb_count b0 =? Q_BATCH); rewrite !qbytes_app; cbn [qbytes fold_right qb_size]; lia.
Qed.
Lemma q_enq_wf : forall l ch v, Forall qbatch_wf l -> qchunk_wf ch -> (need_batch l = true -> 0 <= v /\ (16 * v) mod Q_BBYTES = 0) ->
  Forall qbatch_wf (q_enq l ch v).
Proof.
  intros l ch v FW CW NV.
  assert (NEWB : need_batch l = true -> qbatch_wf (mkQB v (qc_n ch + Q_BBYTES) [ch])).
  { intros NB. destruct (NV NB) as [V0 VA]. unfold qbatch_wf, qb_count. cbn [qb_v qb_size qb_chunks length fold_right Z.of_nat Pos.of_succ_nat].
    split; [exact V0|]. split; [exact VA|]. split; [lia|]. split; [lia| constructor; [exact CW| constructor]]. }
  destruct l as [|b0 l0] using rev_ind; [rewrite q_enq_nil; constructor; [apply NEWB; reflexivity| constructor]|].
  rewrite q_enq_snoc. rewrite need_batch_snoc in NEWB, NV. apply Forall_app in FW as [FW0 FWb]. apply Forall_cons_iff in FWb as [(B1 & B2 & B3 & B4 & B5) _].
  destruct (Z.eqb_spec (qb_count b0) Q_BATCH) as [EQ|NE].
  - apply Forall_app. split; [apply Forall_app; split; [exact FW0| constructor; [exact (conj B1 (conj B2 (conj B3 (conj B4 B5))))| constructor]]| constructor; [apply NEWB; reflexivity| constructor]].
  - apply Forall_app. split; [exact FW0|]. constructor; [| constructor].
    unfold qbatch_wf, qb_count in *. cbn [qb_v qb_size qb_chunks]. rewrite length_app, Nat2Z.inj_add. cbn [length Z.of_nat Pos.of_succ_nat].
    split; [exact B1|]. split; [exact B2|]. split; [lia|]. split; [| apply Forall_app; split; [exact B5| constructor; [exact CW| constructor]]].
    rewrite B4, fold_right_app. cbn [fold_right].
    assert (FR : forall (l1 : list qchunk) a, fold_right (fun c acc => qc_n c + acc) a l1 = fold_right (fun c acc => qc_n c + acc) 0 l1 + a)
      by (induction l1 as [|x l1 IHl]; intros a; cbn [fold_right]; [lia| rewrite IHl; lia]).
    rewrite (FR (qb_chunks b0) (qc_n ch + 0)). lia.
Qed.

Section PC.
Context {HC : HasCeiling}.
Variable AL : alayout.

Definition pchunk_rep (m : mem) (ch : qchunk) : Prop :=
  let B := qc_blk AL ch in let M := qc_hdr AL ch in let n := qc_n ch in let rz := qc_rz ch in
  (exists bits actx, rw_cells asegs m M [CB 4 [Z_to_bv 8 3; bits; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (wz n); C8 actx])
  /\ (16 < rz -> rw_cells asegs m B [C8 (wz CHUNK_MAGIC); C8 (wz M)] /\ exists j, rw_cells asegs m (B + 16) [CB (Z.to_nat (rz - 32)) j])
  /\ (exists j, rw_cells asegs m (M + 16) [CB (Z.to_nat (qc_bsize ch - rz)) j])
  /\ rw_cells asegs m (sh B) [CB (Z.to_nat (rz / 8)) (fa_bytes (rz / 8))]
  /\ (exists sj, rw_cells asegs m (sh (M + 16)) [CB (Z.to_nat (rup8 n / 8)) sj])
  /\ rw_cells asegs m (sh (M + 16 + rup8 n)) [CB (Z.to_nat ((qc_bsize ch - rz - rup8 n) / 8)) (fa_bytes ((qc_bsize ch - rz - rup8 n) / 8))]
  /\ match qc_kind ch with
     | QPrim _ _ => True
     | QSec sc => (exists j, rw_cells asegs m (sc_beg sc + 32) [CB 4064 j]) /\ rw_cells asegs m (sh (sc_beg sc)) [CB 512 (fa_bytes 512)]
     end.

#[using="Type"] Lemma pchunk_poisoned : forall W (m m' : mem) ch,
  pchunk_rep m ch -> munch W m m' -> wmono asegs m m' ->
  rw_cells asegs m' (sh (qc_hdr AL ch + 16)) [CB (Z.to_nat (rup8 (qc_n ch) / 8)) (fd_bytes (rup8 (qc_n ch) / 8))] ->
  16 <= qc_rz ch -> 0 <= qc_bsize ch - qc_rz ch -> 0 <= rup8 (qc_n ch) -> 0 <= (qc_bsize ch - qc_rz ch - rup8 (qc_n ch)) / 8 ->
  disjoint_from W (qc_blk AL ch) (qc_bsize ch) ->
  disjoint_from W (sh (qc_blk AL ch)) (qc_rz ch / 8) ->
  disjoint_from W (sh (qc_hdr AL ch + 16 + rup8 (qc_n ch))) ((qc_bsize ch - qc_rz ch - rup8 (qc_n ch)) / 8) ->
  match qc_kind ch with QPrim _ _ => True | QSec sc => disjoint_from W (sc_beg sc + 32) 4064 /\ disjoint_from W (sh (sc_beg sc)) 512 end ->
  qchunk_rep AL m' ch.
Proof.
  intros W m m' ch (HD & LCH & REST & SHL & _ & SHR & SEC) MU WM FD RZ16 BS0 RU0 TL0 DB DSL DSR DSEC.
  unfold qchunk_rep. cbv zeta. unfold qc_hdr in *.
  split.
  { destruct HD as (bits & actx & HD). exists bits, actx. eapply rw_cells_transport; [exact HD| exact MU| exact WM|].
    cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact DB| lia| lia]. }
  split.
  { intros R16. destruct (LCH R16) as (L1 & j & L2). split.
    - eapply rw_cells_transport; [exact L1| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact DB| lia| lia].
    - exists j. eapply rw_cells_transport; [exact L2| exact MU| exact WM|]. cbn [cells_size csize].
      eapply disjoint_from_sub; [exact DB| lia| lia]. }
  split.
  { destruct REST as (j & R). exists j. eapply rw_cells_transport; [exact R| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
    eapply disjoint_from_sub; [exact DB| lia| lia]. }
  split.
  { eapply rw_cells_transport; [exact SHL| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia). exact DSL. }
  split; [exact FD|].
  split.
  { eapply rw_cells_transport; [exact SHR| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact DSR. }
  destruct (qc_kind ch) as [c v|sc]; [exact I|]. destruct SEC as [(j & S1) S2]. destruct DSEC as [D1 D2]. split.
  - exists j. eapply rw_cells_transport; [exact S1| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. exact D1.
  - eapply rw_cells_transport; [exact S2| exact MU| exact WM|]. cbn [cells_size csize Nat.add]. exact D2.
Qed.

Definition qc_hull (ch : qchunk) (A n : Z) : Prop :=
  (A = qc_blk AL ch /\ n = qc_bsize ch) \/ (A = sh (qc_blk AL ch) /\ n = qc_bsize ch / 8)
  \/ match qc_kind ch with QPrim _ _ => False | QSec sc => (A = sc_beg sc + 32 /\ n = 4064) \/ (A = sh (sc_beg sc) /\ n = 512) end.

#[using="Type"] Lemma qchunk_rep_other_g : forall X (m m' : mem) lo q Ws W tc tsc ch',
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  munch (Ws ++ W) m m' -> Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
  (forall A n, qc_hull ch' A n -> disjoint_from Ws A n) ->
  qchunk_wf ch' -> qchunk_rep AL m ch' -> held_kind X ch' ->
  (forall cv, In cv (prim_of ch') -> ~ In cv tc) -> (forall sc, In sc (sec_of ch') -> ~ In sc tsc) ->
  qchunk_rep AL m' ch'.
Proof.
  intros X m m' lo q Ws W tc tsc ch' AO LOH CLO RP RS TCH TSI MU FW HD WF R HK NP NS.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  assert (DJ : forall A n, qc_hull ch' A n -> disjoint_from W A n -> disjoint_from (Ws ++ W) A n)
    by (intros A n HU D; apply disjoint_from_app; split; [exact (HD A n HU)| exact D]).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _).
  destruct ch' as [[c v|sc] rz n]; unfold held_kind in HK; cbn [qc_kind] in HK.
  - destruct (atouch_clear_prim AL lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK TSI W c v FW HK
                (NP (c, v) ltac:(cbn; left; reflexivity))) as [DA DS].
    pose proof HK as (Hc & _). cbn [fst] in Hc. pose proof (class_size_mod16 c Hc) as CM.
    eapply qchunk_rep_frame_m; [exact R| exact WF| | | exact MU| | | exact I].
    + unfold qc_blk. cbn [qc_kind]. unfold region. clear - SPM. Z.div_mod_to_equations. lia.
    + unfold qc_bsize. cbn [qc_kind]. clear - CM. Z.div_mod_to_equations. lia.
    + apply DJ; [left; split; reflexivity| exact DA].
    + apply DJ; [right; left; split; reflexivity| exact DS].
  - destruct (atouch_clear_sec AL lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK SSEP TSI W sc FW HK
                (NS sc ltac:(cbn; left; reflexivity))) as [DA DS].
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2].
    destruct CK as (CK1 & _).
    assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
    assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
    eapply qchunk_rep_frame_m; [exact R| exact WF| | | exact MU| | |].
    + unfold qc_blk. cbn [qc_kind]. clear - CK1. Z.div_mod_to_equations. lia.
    + unfold qc_bsize. cbn [qc_kind]. clear - CM2. Z.div_mod_to_equations. lia.
    + apply DJ; [left; split; reflexivity|]. unfold qc_blk, qc_bsize. cbn [qc_kind]. eapply disjoint_from_sub; [exact DA| clear; lia| clear; lia].
    + apply DJ; [right; left; split; reflexivity|]. unfold qc_blk, qc_bsize. cbn [qc_kind]. rewrite SHB, DV. eapply disjoint_from_sub; [exact DS| clear; lia| clear; lia].
    + cbn [qc_kind]. split; [apply DJ; [right; right; cbn [qc_kind]; left; split; reflexivity|]; eapply disjoint_from_sub; [exact DA| clear; lia| clear - CM1; lia]
                            | apply DJ; [right; right; cbn [qc_kind]; right; split; reflexivity|]; eapply disjoint_from_sub; [exact DS| clear; lia| clear - CM1 CM2; Z.div_mod_to_equations; lia]].
Qed.

#[using="Type"] Lemma qbatch_rep_other_g : forall X (m m' : mem) lo q Ws W tc tsc b nx,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  munch (Ws ++ W) m m' -> Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
  disjoint_from Ws (qb_addr AL b) 8192 -> disjoint_from Ws (sh (qb_addr AL b)) 1024 ->
  qbatch_rep AL m b nx -> held1 (fst X) (bpair b) -> ~ In (bpair b) tc ->
  qbatch_rep AL m' b nx.
Proof.
  intros X m m' lo q Ws W tc tsc b nx AO LOH CLO RP RS TCH TSI MU FW D1 D2 R HK NP.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  destruct (atouch_clear_prim AL lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK TSI W K_BCLASS (qb_v b) FW HK NP) as [DA DS].
  change (class_size K_BCLASS) with 8192 in DA, DS. change (8192 / 8) with 1024 in DS.
  eapply qbatch_rep_frame_m; [exact R| exact MU| |]; apply disjoint_from_app; split; assumption.
Qed.

#[using="Type"] Lemma qlist_rep_other_g : forall X (m m' : mem) lo q Ws W tc tsc l nxt,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  munch (Ws ++ W) m m' -> Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
  qlist_rep AL m l nxt ->
  Forall (fun b => held1 (fst X) (bpair b) /\ ~ In (bpair b) tc /\ disjoint_from Ws (qb_addr AL b) 8192 /\ disjoint_from Ws (sh (qb_addr AL b)) 1024) l ->
  qlist_rep AL m' l nxt.
Proof.
  intros X m m' lo q Ws W tc tsc l nxt AO LOH CLO RP RS TCH TSI MU FW. induction l as [|b l IH]; intros QL FB; [exact I|].
  cbn [qlist_rep] in *. destruct QL as [RB QL]. apply Forall_cons_iff in FB as [(HB & NB & D1 & D2) FB]. split; [| exact (IH QL FB)].
  exact (qbatch_rep_other_g X m m' lo q Ws W tc tsc b _ AO LOH CLO RP RS TCH TSI MU FW D1 D2 RB HB NB).
Qed.
End PC.

Section PI.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation THR := (at_thr (al_thread AL)).
Notation TQ := (at_thr (al_thread AL) + TQ_OFF).

#[using="Type"] Lemma held_sh_geo : forall X (m : mem) ch, alayout_ok AL -> RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch -> qchunk_wf ch ->
  2147450880 <= sh (qc_blk AL ch) /\ sh (qc_blk AL ch) + qc_bsize ch / 8 <= 17594333495296
  /\ (forall lo q A n, sh (qc_blk AL ch) <= A -> A + n <= sh (qc_blk AL ch) + qc_bsize ch / 8 ->
        atouch AL lo q (fst X) (snd X) (prim_of ch) (sec_of ch) (A, A + n)).
Proof.
  intros X m ch AO RP RS HK WF. destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  destruct ch as [[c v|sc] rz n]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_blk, qc_bsize; cbn [qc_kind prim_of sec_of].
  - pose proof (held_geo AL (fst X) AO WF0 c v HK) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CS & G5 & G6 & G7). rewrite G5 in G7.
    split; [exact G6|]. split; [exact G7|]. intros lo q A n0 HA HN. right; right; right; right; left. exists (c, v). split; [left; reflexivity|].
    right. unfold chunk_sh_iv. cbn [fst snd]. lia.
  - pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _).
    assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
    assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
    rewrite SHB, DV. split; [lia|]. split; [lia|]. intros lo q A n0 HA HN. right; right; right; right; right; left. exists sc. split; [left; reflexivity|].
    right. unfold sub_iv. cbn [fst snd]. lia.
Qed.

#[using="Type"] Lemma pchunk_geo : forall X (m : mem) ch, alayout_ok AL -> RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch ->
  qc_blk AL ch mod 8 = 0 /\ qc_bsize ch mod 8 = 0 /\ 32 <= qc_bsize ch
  /\ 6328320 <= qc_blk AL ch /\ qc_blk AL ch + qc_bsize ch <= alloc_ceiling
  /\ (qc_blk AL ch + qc_bsize ch < 2147450880 \/ 17594333495296 <= qc_blk AL ch - 4096).
Proof.
  intros X m ch AO RP RS HK. destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _).
  destruct ch as [[c v|sc] rz n]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_blk, qc_bsize; cbn [qc_kind].
  - pose proof (held_geo AL (fst X) AO WF0 c v HK) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CS & _).
    pose proof (region_range AL c Hc) as [RR1 RR2]. pose proof (class_size_mod16 c Hc) as CM.
    split; [unfold region; clear - SPM; Z.div_mod_to_equations; lia|]. split; [clear - CM; Z.div_mod_to_equations; lia|]. split; [lia|].
    split; [clear - G1 RR1 SP1; lia|]. split; [clear - G2 G3 RR2 SP2; lia|]. right. assert (RG : region AL c = al_space AL + c * K_REGION) by reflexivity. clear - G1 RG Hc SP1. lia.
  - pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & D3 & D4 & _).
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _).
    split; [clear - CK1; Z.div_mod_to_equations; lia|]. split; [clear - CM2; Z.div_mod_to_equations; lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. clear - D4 CM1. lia.
Qed.

#[using="Type"] Lemma dr_inv_poison : forall X H (m m' : mem) WB WC hrest ch lo q sa sb A n,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  dr_inv AL E X H m WB WC (prim_of ch ++ hrest) -> held_kind X ch -> qchunk_wf ch ->
  (forall sc, In sc (sec_of ch) -> ~ In sc (flat_map sec_of WC)) ->
  munch [(sa, sb); (A, A + n)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  lo <= sa -> sb <= q -> sh (qc_blk AL ch) <= A -> A + n <= sh (qc_blk AL ch) + qc_bsize ch / 8 ->
  dr_inv AL E X H m' WB WC (prim_of ch ++ hrest).
Proof.
  intros X H m m' WB WC hrest ch lo q sa sb A n AO LOH CLO INV HK WF NSC MU WM MI' LQ1 Q1Q HA HN.
  destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
  destruct (held_sh_geo X m ch AO RP RS HK WF) as (SG1 & SG2 & SGC).
  assert (TCH : Forall (held1 (fst X)) (prim_of ch)).
  { destruct ch as [[c v|sc] rz n0]; cbn [prim_of qc_kind]; [| constructor]. constructor; [exact HK| constructor]. }
  assert (TSI : incl (sec_of ch) (se_chunks (snd X))).
  { destruct ch as [[c v|sc] rz n0]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HK. }
  assert (FWa : Forall (atouch AL lo q (fst X) (snd X) (prim_of ch) (sec_of ch)) [(sa, sb); (A, A + n)]).
  { constructor; [left; unfold sub_iv; cbn [fst snd]; lia|]. constructor; [exact (SGC lo q A n HA HN)| constructor]. }
  destruct HOK as [ND FH].
  unfold dr_inv.
  split.
  { apply (RPRIM_frame AL AO (fst X) _ m m' RP MU WM). unfold prim_clear. constructor; [| constructor; [| constructor]].
    - left. unfold prim_out. cbn [fst snd]. clear - LQ1 LOH CLO ACR T3 T4 SP2 SHS. repeat split; lia.
    - destruct ch as [[c v|sc] rz n0]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_blk, qc_bsize in HA, HN; cbn [qc_kind] in HA, HN.
      + right. exists c, v. split; [exact HK|]. right. unfold chunk_sh_iv. cbn [fst snd]. lia.
      + left. destruct (clear_ctx AL X m RP RS) as (_ & SOK & _).
        pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
        pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _).
        assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
        assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
        rewrite SHB, DV in HN. rewrite SHB in HA. unfold qc_blk, qc_bsize in SG1, SG2. cbn [qc_kind] in SG1, SG2.
        unfold prim_out. cbn [fst snd]. split; [left; clear - SG2 HN SP1 SHB DV; lia|]. split.
        { destruct D5 as [D5|D5]; [left; pose proof (sh_le _ _ D5) as SL; rewrite D8 in SL; clear - SL HN; lia| right; pose proof (sh_le _ _ D5) as SL; clear - SL HA; replace (al_space AL + K_SPACE + 4096) with (al_space AL + (K_SPACE + 4096)) by lia; lia]. }
        split; [clear - HA HN SG1 SG2 SHB DV T3; lia| right; clear - HA SG1 SHB; lia]. }
  split; [exact POK|].
  split.
  { eapply (RSEC_frame_pzone AL (snd X) _ m m' lo AO LOH CLO RS MU WM). constructor; [| constructor; [| constructor]]; unfold pzone; cbn [fst snd].
    - right; right; right. lia.
    - right; left. lia. }
  split; [exact MI'|].
  split. { eapply poison_env_frame; [exact PE| exact MU| exact WM|]. unfold above_img. constructor; [| constructor; [| constructor]]; cbn [fst snd]; lia. }
  split. { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. unfold thread_clear. constructor; [| constructor; [| constructor]]; cbn [fst snd].
           - clear - LQ1 LOH CLO ACR T1 T2 T3 T4 T5. repeat split; lia.
           - clear - HA HN SG1 SG2 T1 T3. repeat split; lia. }
  split; [eapply shvis_wmono; [exact SV| exact WM]|].
  split; [exact WFS|].
  split.
  { apply Forall_forall. intros ch' Hin.
    eapply (qchunk_rep_other AL X m m' lo q _ (prim_of ch) (sec_of ch) ch' AO LOH CLO RP RS TCH TSI MU FWa).
    - exact (proj1 (Forall_forall _ _) WFS ch' Hin).
    - exact (proj1 (Forall_forall _ _) REPS ch' Hin).
    - exact (proj1 (Forall_forall _ _) HKS ch' Hin).
    - intros cv Hcv Hc. apply NoDup_app_remove_l in ND. apply (NoDup_app_disj_s _ _ cv ND); [apply in_flat_map; exists ch'; split; assumption|].
      apply in_or_app. left. exact Hc.
    - intros sc Hsc Hc. apply (NSC sc Hc). apply in_flat_map. exists ch'. split; assumption. }
  split; [exact HKS|]. split; [exact (conj ND FH)|]. split; [exact NDS|]. split; [exact BWF|].
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) BREP b Hb) as [nx RB]. exists nx.
  eapply (qbatch_rep_other AL X m m' lo q _ (prim_of ch) (sec_of ch) b nx AO LOH CLO RP RS TCH TSI MU FWa RB).
  - apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb.
  - intros Hc. apply (NoDup_app_disj_s _ _ (bpair b) ND); [apply in_map; exact Hb|]. apply in_or_app. right. apply in_or_app. left. exact Hc.
Qed.

#[using="Type"] Lemma q_enq_wf0 : forall l ch v, Forall qbatch_wf0 l -> qchunk_wf ch -> (need_batch l = true -> 0 <= v /\ (16 * v) mod Q_BBYTES = 0) ->
  Forall qbatch_wf0 (q_enq l ch v).
Proof.
  intros l ch v FW CW NV.
  assert (NEWB : need_batch l = true -> qbatch_wf0 (mkQB v (qc_n ch + Q_BBYTES) [ch])).
  { intros NB. destruct (NV NB) as [V0 VA]. unfold qbatch_wf0, qb_count. cbn [qb_v qb_size qb_chunks length Z.of_nat Pos.of_succ_nat].
    split; [exact V0|]. split; [exact VA|]. split; [lia| constructor; [exact CW| constructor]]. }
  destruct l as [|b0 l0] using rev_ind; [rewrite q_enq_nil; constructor; [apply NEWB; reflexivity| constructor]|].
  rewrite q_enq_snoc. rewrite need_batch_snoc in NEWB, NV. apply Forall_app in FW as [FW0 FWb]. pose proof FWb as FWb'. apply Forall_cons_iff in FWb' as [(B1 & B2 & B3 & B5) _].
  destruct (Z.eqb_spec (qb_count b0) Q_BATCH) as [EQ|NE].
  - apply Forall_app. split; [apply Forall_app; split; [exact FW0| exact FWb]| constructor; [apply NEWB; reflexivity| constructor]].
  - apply Forall_app. split; [exact FW0|]. constructor; [| constructor].
    unfold qbatch_wf0, qb_count in *. cbn [qb_v qb_size qb_chunks]. rewrite length_app, Nat2Z.inj_add. cbn [length Z.of_nat Pos.of_succ_nat].
    split; [exact B1|]. split; [exact B2|]. split; [lia| apply Forall_app; split; [exact B5| constructor; [exact CW| constructor]]].
Qed.

#[using="Type"] Lemma qlist_rep_each : forall l nxt (mm : mem), qlist_rep AL mm l nxt -> Forall (fun b => exists nx, qbatch_rep AL mm b nx) l.
Proof.
  induction l as [|b l IHl]; intros nxt mm QLl; [constructor|]. cbn [qlist_rep] in QLl. destruct QLl as [RB QLl].
  constructor; [eexists; exact RB| exact (IHl nxt mm QLl)].
Qed.

#[using="Type"] Lemma held_pair_apart : forall P c1 v1 c2 v2, alayout_ok AL -> (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls P c)) ->
  held1 P (c1, v1) -> held1 P (c2, v2) -> (c1, v1) <> (c2, v2) ->
  let B1 := region AL c1 + 16 * v1 in let B2 := region AL c2 + 16 * v2 in
  (B1 + class_size c1 <= B2 \/ B2 + class_size c2 <= B1)
  /\ (sh B1 + class_size c1 / 8 <= sh B2 \/ sh B2 + class_size c2 / 8 <= sh B1).
Proof.
  intros P c1 v1 c2 v2 AO WF0 H1 H2 NE B1 B2.
  pose proof (held_geo AL P AO WF0 c1 v1 H1) as G1. pose proof (held_geo AL P AO WF0 c2 v2 H2) as G2. cbv zeta in G1, G2. fold B1 in G1. fold B2 in G2.
  destruct G1 as (Hc1 & A1 & A2 & A3 & CS1 & A5 & _). destruct G2 as (Hc2 & C1 & C2 & C3 & CS2 & C5 & _).
  assert (BL : B1 + class_size c1 <= B2 \/ B2 + class_size c2 <= B1).
  { destruct (Z.eq_dec c1 c2) as [EC|NC].
    - subst c2. assert (NV : v1 <> v2) by (intros ->; apply NE; reflexivity).
      destruct H1 as (_ & _ & _ & M1 & _). destruct H2 as (_ & _ & _ & M2 & _). cbn [fst snd] in M1, M2.
      destruct (chunks_apart c1 v1 v2 Hc1 M1 M2 NV) as [K|K]; unfold B1, B2; lia.
    - assert (RG : forall c, region AL c = al_space AL + c * K_REGION) by reflexivity. unfold B1, B2 in *. rewrite !RG in *.
      clear - A1 A2 A3 C1 C2 C3 NC. lia. }
  split; [exact BL|]. destruct BL as [K|K]; [left; rewrite <- A5; apply sh_le; exact K| right; rewrite <- C5; apply sh_le; exact K].
Qed.

#[using="Type"] Lemma hull_tq_dj : forall X (m : mem) ch A n, alayout_ok AL -> RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch ->
  qc_hull AL ch A n -> disjoint_from [(TQ, TQ + 32)] A n.
Proof.
  intros X m ch A n AO RP RS HK HU. destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _).
  layout_apart_fact AO 0%nat 3%nat AP03.
  cbn [disjoint_from]. split; [| exact I].
  destruct ch as [[c v|sc] rz n0]; unfold held_kind in HK; cbn [qc_kind] in HK; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind] in HU.
  - pose proof (held_geo AL (fst X) AO WF0 c v HK) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & _ & G5 & G6 & G7). rewrite G5 in G7.
    pose proof (region_range AL c Hc) as [RR1 RR2].
    destruct HU as [[-> ->]|[[-> ->]|[]]]; [clear - G1 G2 G3 RR1 RR2 AP03; lia| clear - G6 G7 T3; lia].
  - pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _).
    assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
    assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
    destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
    + clear - D7 CM1. lia.
    + rewrite SHB, DV. clear - D9 D10 T3 CM1. lia.
    + clear - D7 CM1. lia.
    + clear - D9 D10 T3 CM1 CM2. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma held_tq_dj : forall X (m : mem) c v, alayout_ok AL -> RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held1 (fst X) (c, v) ->
  disjoint_from [(TQ, TQ + 32)] (region AL c + 16 * v) (class_size c) /\ disjoint_from [(TQ, TQ + 32)] (sh (region AL c + 16 * v)) (class_size c / 8).
Proof.
  intros X m c v AO RP RS HE. split.
  - apply (hull_tq_dj X m (mkQC (QPrim c v) 16 1) _ _ AO RP RS HE). left. split; reflexivity.
  - apply (hull_tq_dj X m (mkQC (QPrim c v) 16 1) _ _ AO RP RS HE). right. left. split; reflexivity.
Qed.

#[using="Type"] Lemma dr_inv_enqueue : forall X H H1 (mP m1 : mem) glob loc ch hrest lo q,
  let P := fst X in let PN := fst (enq_prim P loc) in let VN := snd (enq_prim P loc) in let loc' := q_enq loc ch VN in
  let hs := map bpair (glob ++ loc) ++ flat_map prim_of (flat_map qb_chunks (glob ++ loc)) ++ prim_of ch ++ hrest in
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q ->
  dr_inv AL E X H mP (glob ++ loc) (flat_map qb_chunks (glob ++ loc)) (prim_of ch ++ hrest) ->
  held_kind X ch -> qchunk_wf ch -> qchunk_rep AL mP ch ->
  (forall sc, In sc (sec_of ch) -> ~ In sc (flat_map sec_of (flat_map qb_chunks (glob ++ loc)))) ->
  qlist_rep AL mP glob 0 ->
  munch (enq_W AL q lo P loc) mP m1 -> wmono asegs mP m1 -> mem_inv asegs m1 -> poison_env E m1 -> thread_env L m1 -> shvis H1 m1 ->
  RPRIM AL PN m1 -> prim_ok PN -> held_ok PN (if need_batch loc then (K_BCLASS, VN) :: hs else hs) ->
  qcache_rep AL m1 TQ loc' -> (need_batch loc = true -> pclass_wf K_BCLASS (get_cls (enq_P1 P) K_BCLASS)) ->
  dr_inv AL E (PN, snd X) H1 m1 (glob ++ loc') (flat_map qb_chunks (glob ++ loc')) hrest /\ qlist_rep AL m1 glob 0.
Proof.
  intros X H H1 mP m1 glob loc ch hrest lo q P PN VN loc' hs AO LOH CLO LQ INV HK WFC REPC NSC QLG MU WM MI1 PE1 TE1 SV1 RPN POKN HOKN QC1 WFK.
  destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
  destruct (clear_ctx AL X mP RP RS) as (WF0 & SOK & SSEP). fold P in WF0.
  pose proof RPN as (_ & _ & CLSN & _). assert (WFN : forall c, 1 <= c <= 31 -> pclass_wf c (get_cls PN c)) by (intros c Hc; exact (proj1 (CLSN c Hc))).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  set (W1 := if need_batch loc then prim_W AL lo q K_BCLASS (get_cls P K_BCLASS) (get_cls (enq_P1 P) K_BCLASS) else [(lo, q)]).
  set (NBI := if need_batch loc then [(region AL K_BCLASS + 16 * VN, region AL K_BCLASS + 16 * VN + Q_BBYTES)] else @nil (Z * Z)).
  assert (EW : enq_W AL q lo P loc = W1 ++ [(TQ, TQ + 32)] ++ qlast_iv AL loc ++ NBI) by reflexivity.

  assert (HBL : forall b, In b (glob ++ loc) -> held1 P (bpair b)).
  { intros b Hb. destruct HOK as [_ FH]. apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb. }
  assert (TCH : Forall (held1 (fst X)) (map bpair loc)).
  { apply Forall_forall. intros cv Hcv. apply in_map_iff in Hcv as (b & <- & Hb). apply HBL. apply in_or_app. right. exact Hb. }

  assert (FW1 : Forall (atouch AL lo q (fst X) (snd X) (map bpair loc) []) (W1 ++ qlast_iv AL loc)).
  { apply Forall_app. split.
    - unfold W1. destruct (need_batch loc) eqn:NB.
      + pose proof (WF0 K_BCLASS ltac:(lia)) as (K1 & _ & _ & _ & K5 & _ & K7 & K8 & _).
        pose proof (WFK eq_refl) as (D1 & _ & _ & _ & D5 & _ & D7 & D8 & _).
        apply atouch_prim_W; [lia| fold P; lia| lia| lia| lia| lia| lia| fold P; lia].
      + constructor; [left; unfold sub_iv; cbn [fst snd]; lia| constructor].
    - unfold qlast_iv. destruct (rev loc) as [|bz r] eqn:ER; [constructor|]. constructor; [| constructor].
      assert (INz : In bz loc) by (apply in_rev; rewrite ER; left; reflexivity).
      right; right; right; right; left. exists (bpair bz). split; [apply in_map; exact INz|]. left.
      unfold chunk_iv, qb_addr, bpair. cbn [fst snd]. change (class_size K_BCLASS) with 8192. lia. }

  assert (MUg : munch (([(TQ, TQ + 32)] ++ NBI) ++ (W1 ++ qlast_iv AL loc)) mP m1).
  { eapply munch_weaken; [| exact MU]. rewrite EW. apply sub_fp_of_incl. intros iv Hiv.
    apply in_app_or in Hiv as [Hiv|Hiv]; [apply in_or_app; right; apply in_or_app; left; exact Hiv|].
    apply in_app_or in Hiv as [Hiv|Hiv]; [apply in_or_app; left; apply in_or_app; left; exact Hiv|].
    apply in_app_or in Hiv as [Hiv|Hiv]; [apply in_or_app; right; apply in_or_app; right; exact Hiv| apply in_or_app; left; apply in_or_app; right; exact Hiv]. }

  assert (HSN : forall cv, In cv hs -> held1 PN cv).
  { intros cv Hcv. destruct HOKN as [_ FHN]. apply (proj1 (Forall_forall _ _) FHN). destruct (need_batch loc); [right; exact Hcv| exact Hcv]. }
  assert (NBG : need_batch loc = true -> held1 PN (K_BCLASS, VN) /\ ~ In (K_BCLASS, VN) hs).
  { intros NB. rewrite NB in HOKN. destruct HOKN as [NDN FHN]. split; [exact (Forall_inv FHN)| apply NoDup_cons_iff in NDN as [NI _]; exact NI]. }
  assert (DJP : forall c v, In (c, v) hs -> held1 P (c, v) ->
            disjoint_from NBI (region AL c + 16 * v) (class_size c) /\ disjoint_from NBI (sh (region AL c + 16 * v)) (class_size c / 8)).
  { intros c v Hin HE. unfold NBI. destruct (need_batch loc) eqn:NB; [| split; exact I]. destruct (NBG eq_refl) as [HN NI].
    assert (NEQ : (c, v) <> (K_BCLASS, VN)) by (intros C; apply NI; rewrite <- C; exact Hin).
    destruct (held_pair_apart PN c v K_BCLASS VN AO WFN (HSN _ Hin) HN NEQ) as [BL _]. change (class_size K_BCLASS) with 8192 in BL.
    pose proof (held_geo AL P AO WF0 c v HE) as G. cbv zeta in G. destruct G as (_ & _ & _ & _ & _ & G5 & G6 & G7). rewrite G5 in G7.
    pose proof (held_geo AL PN AO WFN K_BCLASS VN HN) as GN. cbv zeta in GN. destruct GN as (_ & N1 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 _].
    cbn [disjoint_from]. split; (split; [| exact I]); [clear - BL; lia| clear - G7 N1 RN1 SP1; lia]. }
  assert (DJS : forall sc, In sc (se_chunks (snd X)) -> forall A n, (sc_beg sc <= A /\ A + n <= sc_beg sc + sc_msize sc) \/ (sh (sc_beg sc) <= A /\ A + n <= sh (sc_beg sc) + sc_msize sc / 8) ->
            disjoint_from NBI A n).
  { intros sc Hsc A n HA. unfold NBI. destruct (need_batch loc) eqn:NB; [| exact I]. destruct (NBG eq_refl) as [HN _].
    pose proof (held_geo AL PN AO WFN K_BCLASS VN HN) as GN. cbv zeta in GN. destruct GN as (_ & N1 & N2 & N3 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2].
    change (class_size K_BCLASS) with 8192 in N2.
    pose proof (sec_geo AL (snd X) SOK sc Hsc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
    cbn [disjoint_from]. split; [| exact I]. destruct HA as [[A1 A2]|[A1 A2]]; [clear - A1 A2 D5 N1 N2 N3 RN1 RN2; lia| clear - A1 A2 D10 N1 RN1 SP1; lia]. }
  assert (DJH : forall ch', held_kind X ch' -> qchunk_wf ch' -> (forall cv, In cv (prim_of ch') -> In cv hs) ->
            forall A n, qc_hull AL ch' A n -> disjoint_from ([(TQ, TQ + 32)] ++ NBI) A n).
  { intros ch' HK' WF' INH A n HU. apply disjoint_from_app. split; [exact (hull_tq_dj X mP ch' A n AO RP RS HK' HU)|].
    destruct ch' as [[c v|sc] rz n0]; unfold held_kind in HK'; cbn [qc_kind] in HK'; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind] in HU.
    - destruct (DJP c v (INH (c, v) ltac:(cbn; left; reflexivity)) HK') as [DB DS]. destruct HU as [[-> ->]|[[-> ->]|[]]]; assumption.
    - pose proof (proj1 (Forall_forall _ _) SOK sc HK') as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _).
      assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
      assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
      apply (DJS sc HK'). destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; [left; lia| right; rewrite SHB, DV; lia| left; lia| right; clear - CM1 CM2; Z.div_mod_to_equations; lia]. }

  assert (QLG1 : qlist_rep AL m1 glob 0).
  { eapply (qlist_rep_other_g AL X mP m1 lo q _ _ (map bpair loc) [] glob 0 AO LOH CLO RP RS TCH ltac:(intros d []) MUg FW1 QLG).
    apply Forall_forall. intros b Hb. assert (HBb : held1 P (bpair b)) by (apply HBL; apply in_or_app; left; exact Hb).
    assert (INb : In (bpair b) hs) by (unfold hs; apply in_or_app; left; apply in_map; apply in_or_app; left; exact Hb).
    split; [exact HBb|]. split.
    { intros Hc. destruct HOK as [ND _]. rewrite map_app in ND. apply NoDup_app_remove_r in ND.
      apply (NoDup_app_disj_s _ _ (bpair b) ND); [apply in_map; exact Hb| exact Hc]. }
    destruct (DJP K_BCLASS (qb_v b) INb HBb) as [DB DS]. change (class_size K_BCLASS) with 8192 in DB, DS. change (8192 / 8) with 1024 in DS. fold (qb_addr AL b) in DB, DS.
    destruct (held_tq_dj X mP K_BCLASS (qb_v b) AO RP RS HBb) as [TB TS]. change (class_size K_BCLASS) with 8192 in TB, TS. change (8192 / 8) with 1024 in TS. fold (qb_addr AL b) in TB, TS.
    split; apply disjoint_from_app; split; assumption. }

  assert (INCH : forall ch', In ch' (flat_map qb_chunks (glob ++ loc)) -> forall cv, In cv (prim_of ch') -> In cv hs).
  { intros ch' Hch cv Hcv. unfold hs. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists ch'. split; assumption. }
  assert (REP1 : forall ch', held_kind X ch' -> qchunk_wf ch' -> qchunk_rep AL mP ch' -> (forall cv, In cv (prim_of ch') -> In cv hs) ->
            (forall cv, In cv (prim_of ch') -> ~ In cv (map bpair loc)) -> qchunk_rep AL m1 ch').
  { intros ch' HK' WF' R' INH NP'.
    eapply (qchunk_rep_other_g AL X mP m1 lo q _ _ (map bpair loc) [] ch' AO LOH CLO RP RS TCH ltac:(intros d []) MUg FW1 (DJH ch' HK' WF' INH) WF' R' HK' NP').
    intros sc _ []. }
  assert (NDH : List.NoDup hs) by (destruct HOKN as [NDN _]; destruct (need_batch loc); [apply NoDup_cons_iff in NDN as [_ NDN]; exact NDN| exact NDN]).
  assert (NPB : forall cv, In cv (flat_map prim_of (flat_map qb_chunks (glob ++ loc)) ++ prim_of ch ++ hrest) -> ~ In cv (map bpair loc)).
  { intros cv Hcv Hb. unfold hs in NDH. apply (NoDup_app_disj_s _ _ cv NDH); [rewrite map_app; apply in_or_app; right; exact Hb| exact Hcv]. }
  assert (ECH : flat_map qb_chunks (glob ++ loc') = flat_map qb_chunks (glob ++ loc) ++ [ch]).
  { rewrite !flat_map_app. unfold loc'. rewrite q_enq_chunks, app_assoc. reflexivity. }
  assert (EBP : map bpair (glob ++ loc') = map bpair (glob ++ loc) ++ (if need_batch loc then [(K_BCLASS, VN)] else [])).
  { unfold bpair. rewrite <- !(map_map qb_v (fun v => (K_BCLASS, v))). rewrite !map_app. unfold loc'. rewrite q_enq_vs, map_app, app_assoc.
    destruct (need_batch loc); reflexivity. }
  split; [| exact QLG1].
  unfold dr_inv. cbn [fst snd]. rewrite ECH.
  split; [exact RPN|]. split; [exact POKN|].
  split.
  { eapply (RSEC_frame_pzone AL (snd X) _ mP m1 lo AO LOH CLO RS MU WM). rewrite EW.
    apply Forall_app. split.
    { unfold W1. destruct (need_batch loc) eqn:NB.
      - pose proof (WF0 K_BCLASS ltac:(lia)) as (K1 & _ & _ & _ & K5 & _ & K7 & K8 & _).
        pose proof (WFK eq_refl) as (D1 & _ & _ & _ & D5 & _ & D7 & D8 & _).
        apply pzone_prim_W; [exact AO| lia| lia| lia| lia| lia| lia| lia].
      - constructor; [| constructor]. unfold pzone. cbn [fst snd]. right; right; right. lia. }
    apply Forall_app. split; [constructor; [| constructor]; unfold pzone; cbn [fst snd]; right; right; left; lia|].
    apply Forall_app. split.
    { unfold qlast_iv. destruct (rev loc) as [|bz r] eqn:ER; [constructor|]. constructor; [| constructor].
      assert (INz : In bz (glob ++ loc)) by (apply in_or_app; right; apply in_rev; rewrite ER; left; reflexivity).
      pose proof (held_geo AL P AO WF0 K_BCLASS (qb_v bz) (HBL bz INz)) as G. cbv zeta in G. destruct G as (_ & G1 & G2 & G3 & _).
      pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2]. change (class_size K_BCLASS) with 8192 in G2.
      unfold pzone, qb_addr. cbn [fst snd]. left. clear - G1 G2 G3 R1 R2. lia. }
    unfold NBI. destruct (need_batch loc) eqn:NB; [| constructor]. constructor; [| constructor]. destruct (NBG eq_refl) as [HN _].
    pose proof (held_geo AL PN AO WFN K_BCLASS VN HN) as GN. cbv zeta in GN. destruct GN as (_ & N1 & N2 & N3 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2].
    change (class_size K_BCLASS) with 8192 in N2. unfold pzone. cbn [fst snd]. left. clear - N1 N2 N3 RN1 RN2. lia. }
  split; [exact MI1|]. split; [exact PE1|]. split; [exact TE1|]. split; [exact SV1|].
  split; [apply Forall_app; split; [exact WFS| constructor; [exact WFC| constructor]]|].
  split.
  { apply Forall_app. split.
    - apply Forall_forall. intros ch' Hin.
      apply (REP1 ch' (proj1 (Forall_forall _ _) HKS ch' Hin) (proj1 (Forall_forall _ _) WFS ch' Hin) (proj1 (Forall_forall _ _) REPS ch' Hin) (INCH ch' Hin)).
      intros cv Hcv. apply NPB. apply in_or_app. left. apply in_flat_map. exists ch'. split; assumption.
    - constructor; [| constructor]. apply (REP1 ch HK WFC REPC).
      + intros cv Hcv. unfold hs. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. exact Hcv.
      + intros cv Hcv. apply NPB. apply in_or_app. right. apply in_or_app. left. exact Hcv. }
  split.
  { apply Forall_app. split.
    - apply Forall_forall. intros ch' Hin. pose proof (proj1 (Forall_forall _ _) HKS ch' Hin) as HK'.
      destruct ch' as [[c v|sc] rz n0]; unfold held_kind in *; cbn [qc_kind fst snd] in *; [| exact HK'].
      apply HSN. apply (INCH _ Hin). cbn. left. reflexivity.
    - constructor; [| constructor]. destruct ch as [[c v|sc] rz n0]; unfold held_kind in *; cbn [qc_kind fst snd] in *; [| exact HK].
      apply HSN. unfold hs. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. cbn. left. reflexivity. }
  split.
  { rewrite EBP, flat_map_app. cbn [flat_map]. rewrite app_nil_r.
    assert (PM : Permutation ((map bpair (glob ++ loc) ++ (if need_batch loc then [(K_BCLASS, VN)] else [])) ++ (flat_map prim_of (flat_map qb_chunks (glob ++ loc)) ++ prim_of ch) ++ hrest)
                             (if need_batch loc then (K_BCLASS, VN) :: hs else hs)).
    { unfold hs. destruct (need_batch loc).
      - rewrite <- !app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
      - rewrite app_nil_r, <- ?app_assoc. apply Permutation_refl. }
    destruct HOKN as [NDN FHN]. split; [eapply Permutation_NoDup; [apply Permutation_sym; exact PM| exact NDN]| eapply Permutation_Forall; [apply Permutation_sym; exact PM| exact FHN]]. }
  split.
  { rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r. apply List.NoDup_app; [exact NDS| | ].
    - destruct ch as [[c v|sc] rz n0]; cbn [sec_of qc_kind]; [constructor| constructor; [intros []| constructor]].
    - intros sc Hsc Hc. exact (NSC sc Hc Hsc). }
  split.
  { apply Forall_app in BWF as [BWFg BWFl]. apply Forall_app. split; [exact BWFg|]. apply q_enq_wf0; [exact BWFl| exact WFC|].
    intros NB. destruct (NBG NB) as [(_ & V0 & _ & VAL & _) _]. cbn [fst snd] in V0, VAL. change (class_size K_BCLASS) with 8192 in VAL. split; assumption. }
  apply Forall_app. split; [exact (qlist_rep_each glob 0 m1 QLG1)|]. destruct QC1 as [_ QL1]. exact (qlist_rep_each loc' 0 m1 QL1).
Qed.

Definition enq_nb_iv (P : prim) (loc : list qbatch) (iv : Z * Z) : Prop :=
  need_batch loc = true /\ iv = (region AL K_BCLASS + 16 * snd (enq_prim P loc), region AL K_BCLASS + 16 * snd (enq_prim P loc) + Q_BBYTES).

#[using="Type"] Lemma enq_W_class : forall X (m : mem) loc lo q,
  alayout_ok AL -> lo <= q -> RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  (forall b, In b loc -> held1 (fst X) (bpair b)) ->
  (need_batch loc = true -> pclass_wf K_BCLASS (get_cls (enq_P1 (fst X)) K_BCLASS)) ->
  Forall (fun iv => atouch AL lo q (fst X) (snd X) (map bpair loc) [] iv \/ iv = (TQ, TQ + 32) \/ enq_nb_iv (fst X) loc iv) (enq_W AL q lo (fst X) loc).
Proof.
  intros X m loc lo q AO LQ RP RS HBL WFK. destruct (clear_ctx AL X m RP RS) as (WF0 & _).
  unfold enq_W. apply Forall_app. split.
  { destruct (need_batch loc) eqn:NB.
    - pose proof (WF0 K_BCLASS ltac:(lia)) as (K1 & _ & _ & _ & K5 & _ & K7 & K8 & _).
      pose proof (WFK eq_refl) as (D1 & _ & _ & _ & D5 & _ & D7 & D8 & _).
      eapply Forall_impl; [intros iv A; left; exact A|].
      apply atouch_prim_W; [lia| lia| lia| lia| lia| lia| lia| lia].
    - constructor; [left; left; unfold sub_iv; cbn [fst snd]; lia| constructor]. }
  apply Forall_app. split; [constructor; [right; left; reflexivity| constructor]|].
  apply Forall_app. split.
  { unfold qlast_iv. destruct (rev loc) as [|bz r] eqn:ER; [constructor|]. constructor; [| constructor].
    assert (INz : In bz loc) by (apply in_rev; rewrite ER; left; reflexivity).
    left. right; right; right; right; left. exists (bpair bz). split; [apply in_map; exact INz|]. left.
    unfold chunk_iv, qb_addr, bpair. cbn [fst snd]. change (class_size K_BCLASS) with 8192. lia. }
  destruct (need_batch loc) eqn:NB; [| constructor]. constructor; [| constructor]. right; right. split; [exact NB| reflexivity].
Qed.

#[using="Type"] Lemma enq_class_dj : forall X (m : mem) loc lo q W PN A k,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q -> RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  (forall b, In b loc -> held1 (fst X) (bpair b)) ->
  (need_batch loc = true -> held1 PN (K_BCLASS, snd (enq_prim (fst X) loc)) /\ (forall c, 1 <= c <= 31 -> pclass_wf c (get_cls PN c))) ->
  Forall (fun iv => atouch AL lo q (fst X) (snd X) (map bpair loc) [] iv \/ iv = (TQ, TQ + 32) \/ enq_nb_iv (fst X) loc iv) W ->
  (GSTATS_A + 16 <= A /\ A + k <= 6328320) \/ q <= A -> disjoint_from W A k.
Proof.
  intros X m loc lo q W PN A k AO LOH CLO LQ RP RS HBL NBH FW HA.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _).
  assert (TCH : Forall (held1 (fst X)) (map bpair loc)) by (apply Forall_forall; intros cv Hcv; apply in_map_iff in Hcv as (b & <- & Hb); exact (HBL b Hb)).
  induction FW as [|iv W HIV FW IH]; cbn [disjoint_from]; [exact I|]. destruct iv as [a b]. split; [| exact IH].
  destruct HIV as [AT|[EQ|[NB EQ]]].
  - destruct HA as [[HA1 HA2]|HA].
    + pose proof (atouch_img_dj AL X m lo q [(a, b)] (map bpair loc) [] A k AO LOH CLO RP RS TCH ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) HA1 HA2) as D.
      cbn [disjoint_from] in D. exact (proj1 D).
    + pose proof (atouch_above AL X m lo q [(a, b)] (map bpair loc) [] A k AO LOH CLO LQ RP RS TCH ltac:(intros d []) ltac:(constructor; [exact AT| constructor]) HA) as D.
      cbn [disjoint_from] in D. exact (proj1 D).
  - inversion EQ; subst a b. clear - HA T3 T4 CLO LQ. lia.
  - inversion EQ; subst a b. destruct (NBH NB) as [HN WFN].
    pose proof (held_geo AL PN AO WFN K_BCLASS _ HN) as GN. cbv zeta in GN. destruct GN as (_ & N1 & N2 & N3 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [RN1 RN2].
    change (class_size K_BCLASS) with 8192 in N2. clear - HA N1 N2 N3 RN1 RN2 SP1 SP2 CLO LQ. lia.
Qed.

Definition enq_W1 (lo q : Z) (P : prim) (loc : list qbatch) : list (Z * Z) :=
  if need_batch loc then prim_W AL lo q K_BCLASS (get_cls P K_BCLASS) (get_cls (enq_P1 P) K_BCLASS) else [(lo, q)].
Definition enq_NBI (P : prim) (loc : list qbatch) : list (Z * Z) :=
  if need_batch loc then [(region AL K_BCLASS + 16 * snd (enq_prim P loc), region AL K_BCLASS + 16 * snd (enq_prim P loc) + Q_BBYTES)] else [].
#[using="Type"] Lemma enq_W_eq : forall lo q P loc, enq_W AL q lo P loc = enq_W1 lo q P loc ++ [(TQ, TQ + 32)] ++ qlast_iv AL loc ++ enq_NBI P loc.
Proof. reflexivity. Qed.
#[using="Type"] Lemma enq_W_parts : forall X (m : mem) loc lo q,
  alayout_ok AL -> lo <= q -> RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  (forall b, In b loc -> held1 (fst X) (bpair b)) ->
  (need_batch loc = true -> pclass_wf K_BCLASS (get_cls (enq_P1 (fst X)) K_BCLASS)) ->
  Forall (atouch AL lo q (fst X) (snd X) (map bpair loc) []) (enq_W1 lo q (fst X) loc ++ qlast_iv AL loc)
  /\ Forall (fun iv => need_batch loc = true /\ chunk_iv AL K_BCLASS (snd (enq_prim (fst X) loc)) iv) (enq_NBI (fst X) loc).
Proof.
  intros X m loc lo q AO LQ RP RS HBL WFK. pose proof (enq_W_class X m loc lo q AO LQ RP RS HBL WFK) as FC. rewrite enq_W_eq in FC.
  destruct (clear_ctx AL X m RP RS) as (WF0 & _).
  split.
  - apply Forall_app. split.
    + unfold enq_W1. destruct (need_batch loc) eqn:NB.
      * pose proof (WF0 K_BCLASS ltac:(lia)) as (K1 & _ & _ & _ & K5 & _ & K7 & K8 & _).
        pose proof (WFK eq_refl) as (D1 & _ & _ & _ & D5 & _ & D7 & D8 & _).
        apply atouch_prim_W; [lia| lia| lia| lia| lia| lia| lia| lia].
      * constructor; [left; unfold sub_iv; cbn [fst snd]; lia| constructor].
    + unfold qlast_iv. destruct (rev loc) as [|bz r] eqn:ER; [constructor|]. constructor; [| constructor].
      assert (INz : In bz loc) by (apply in_rev; rewrite ER; left; reflexivity).
      right; right; right; right; left. exists (bpair bz). split; [apply in_map; exact INz|]. left.
      unfold chunk_iv, qb_addr, bpair. cbn [fst snd]. change (class_size K_BCLASS) with 8192. lia.
  - unfold enq_NBI. destruct (need_batch loc) eqn:NB; [| constructor]. constructor; [| constructor]. split; [reflexivity|].
    unfold chunk_iv. cbn [fst snd]. change (class_size K_BCLASS) with 8192. lia.
Qed.

#[using="Type"] Lemma enq_prim_au : forall P loc c, length (pr_cls P) = 32%nat -> (forall c0, 1 <= c0 <= 31 -> pclass_wf c0 (get_cls P c0)) -> 1 <= c <= 31 ->
  (need_batch loc = true -> pclass_wf K_BCLASS (get_cls (enq_P1 P) K_BCLASS)) ->
  p_au (get_cls P c) <= p_au (get_cls (fst (enq_prim P loc)) c).
Proof.
  intros P loc c LEN WF0 Hc WFK. unfold enq_prim. destruct (need_batch loc) eqn:NB; [| cbn [fst]; lia]. specialize (WFK eq_refl).
  pose proof (WF0 K_BCLASS ltac:(lia)) as (_ & _ & _ & _ & _ & _ & K7 & _).
  assert (E1 : p_au (get_cls P c) <= p_au (get_cls (enq_P1 P) c)).
  { unfold enq_P1. destruct (p_cnt (get_cls P K_BCLASS) =? 0); [| lia]. unfold refill_prim. destruct P as [cls ini ca cm]. cbn [pr_cls pr_inited pr_calloc pr_cmapped] in *.
    destruct (Z.eq_dec c K_BCLASS) as [->|NE].
    - rewrite get_cls_set_same by (try exact LEN; lia). apply refill_au; lia.
    - rewrite (get_cls_set_other cls true ca _ K_BCLASS c) by lia. unfold get_cls. cbn [pr_cls]. lia. }
  eapply Z.le_trans; [exact E1|]. set (P1 := enq_P1 P) in *.
  assert (LEN1 : length (pr_cls P1) = 32%nat).
  { unfold P1, enq_P1. destruct (p_cnt (get_cls P K_BCLASS) =? 0); [| exact LEN]. unfold refill_prim. cbn [pr_cls]. rewrite set_nth_length. exact LEN. }
  unfold cache_alloc. destruct (cache_alloc_cls (get_cls P1 K_BCLASS) K_BCLASS) as [k1 v] eqn:EC. cbn [fst].
  destruct P1 as [cls1 ini1 ca1 cm1] eqn:EP1. cbn [pr_cls pr_inited pr_calloc pr_cmapped] in *.
  destruct (Z.eq_dec c K_BCLASS) as [->|NE].
  - rewrite get_cls_set_same by (try exact LEN1; lia). unfold cache_alloc_cls in EC. injection EC as <- _. cbn [p_au].
    destruct (p_cnt (get_cls (mkPRIM cls1 ini1 ca1 cm1) K_BCLASS) =? 0) eqn:EZ; [| lia]. apply refill_au; [lia|].
    destruct WFK as (_ & _ & _ & _ & _ & _ & D7 & _). exact (proj2 D7).
  - rewrite (get_cls_set_other cls1 true _ _ K_BCLASS c) by lia. unfold get_cls. cbn [pr_cls]. lia.
Qed.

#[using="Type"] Lemma atouch_split : forall (Q : Prop) lo q P0 S0 tc tsc lo1 q1 P1 S1 tc1 tsc1 cvn iv,
  lo <= lo1 -> q1 <= q ->
  (forall c, 1 <= c <= 31 -> p_au (get_cls P0 c) <= p_au (get_cls P1 c)) ->
  incl (se_chunks S1) (se_chunks S0) -> (forall cv, In cv tc1 -> In cv tc \/ (Q /\ cv = cvn)) -> incl tsc1 tsc ->
  atouch AL lo1 q1 P1 S1 tc1 tsc1 iv ->
  atouch AL lo q P0 S0 tc tsc iv \/ (Q /\ (chunk_iv AL (fst cvn) (snd cvn) iv \/ chunk_sh_iv AL (fst cvn) (snd cvn) iv)).
Proof.
  intros Q lo q P0 S0 tc tsc lo1 q1 P1 S1 tc1 tsc1 cvn iv HL HQ HP HS HT HTS A. unfold atouch, sub_iv in *.
  destruct A as [A|[A|[A|[A|[A|[A|[A|A]]]]]]].
  - left. left. lia.
  - left. right; left. exact A.
  - left. right; right; left. exact A.
  - left. right; right; right; left. destruct A as (c & Hc & A). exists c. split; [exact Hc|]. specialize (HP c Hc).
    destruct A as [A|[A|A]]; [left; exact A| right; left; lia| right; right].
    pose proof (sh_le (region AL c + p_au (get_cls P0 c)) (region AL c + p_au (get_cls P1 c)) ltac:(lia)). lia.
  - destruct A as (cv & Hin & A). destruct (HT cv Hin) as [Hc|[HQ' Hc]].
    + left. right; right; right; right; left. exists cv. split; [exact Hc| exact A].
    + right. subst cv. split; [exact HQ'| exact A].
  - left. right; right; right; right; right; left. destruct A as (sc & Hin & A). exists sc. split; [apply HTS; exact Hin| exact A].
  - left. right; right; right; right; right; right; left. destruct A as (sc & Hin & A). exists sc. split; [apply HS; exact Hin| exact A].
  - left. right; right; right; right; right; right; right. exact A.
Qed.
End PI.
