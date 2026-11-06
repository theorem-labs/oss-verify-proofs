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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD F_sec_A F_sec_C AQuar F_quar_Ep F_quar_E AQuarM AHeap AFoot AQuarR AQuarS AQuarP AFrameG.
Import ListNotations.
Open Scope Z_scope.

Section QG.
Context {HC : HasCeiling}.
Variable AL : alayout.

  Ltac demodz H z :=
    unfold id in H;
    lazymatch type of H with
    | ?a mod ?b = 0 => apply (proj1 (Z.mod_divide a b ltac:(lia))) in H; unfold Z.divide in H; destruct H as [z H]
    end.

  #[using="Type"] Lemma qchunk_rep_frame_g : forall W (m m' : mem) ch,
    qchunk_rep AL m ch -> qchunk_wf ch -> qc_blk AL ch mod 8 = 0 -> qc_bsize ch mod 8 = 0 -> gmw W m m' ->
    disjoint_from W (qc_blk AL ch) (qc_bsize ch) -> disjoint_from W (sh (qc_blk AL ch)) (qc_bsize ch / 8) ->
    match qc_kind ch with
    | QPrim _ _ => True
    | QSec sc => disjoint_from W (sc_beg sc + 32) 4064 /\ disjoint_from W (sh (sc_beg sc)) 512
    end ->
    qchunk_rep AL m' ch.
  Proof.
    intros W m m' ch R WF B8 S8 MU DA DS DK. unfold qchunk_rep in *. cbv zeta in *.
    destruct WF as (RZ16 & RZM & NR & RZN & _).
    set (B := qc_blk AL ch) in *. set (bs := qc_bsize ch) in *. set (rz := qc_rz ch) in *. set (n := qc_n ch) in *.
    assert (EH : qc_hdr AL ch = B + rz - 16) by reflexivity. rewrite EH in *. clear EH.
    assert (N8 : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; clear; Z.div_mod_to_equations; lia).
    demodz B8 kb. demodz S8 ks. demodz RZM kr. destruct N8 as [N8 N8m]. demodz N8m kn.
    assert (SHX : forall k, 0 <= k -> sh (B + 8 * k) = sh B + k) by (intros k Hk; unfold sh; rewrite B8; clear - Hk; Z.div_mod_to_equations; lia).
    assert (DV : rz / 8 = 2 * kr /\ rup8 n / 8 = kn /\ bs / 8 = ks /\ (bs - rz - rup8 n) / 8 = ks - 2 * kr - kn)
      by (rewrite RZM, N8m, S8; clear; Z.div_mod_to_equations; lia).
    destruct DV as (DV1 & DV2 & DV3 & DV4). rewrite DV3 in DS.
    assert (TRA : forall A cs, rw_cells asegs m A cs -> B <= A -> A + Z.of_nat (cells_size cs) <= B + bs -> rw_cells asegs m' A cs).
    { intros A cs X H1 H2. eapply rw_cells_transport_g; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DA| exact H1| exact H2]. }
    assert (TRS : forall A cs, rw_cells asegs m A cs -> sh B <= A -> A + Z.of_nat (cells_size cs) <= sh B + ks -> rw_cells asegs m' A cs).
    { intros A cs X H1 H2. eapply rw_cells_transport_g; [exact X| exact MU|]. eapply disjoint_from_sub; [exact DS| exact H1| exact H2]. }
    destruct R as ((bits & actx & R1) & R2 & (j3 & R3) & R4 & R5 & R6 & R7).
    split. { exists bits, actx. apply TRA; [exact R1| clear - RZ16; lia| cbn [cells_size csize Nat.add]; clear - RZ16 RZN N8 NR; lia]. }
    split.
    { intros RZ32. destruct (R2 RZ32) as [R2a (j2 & R2b)]. split.
      - apply TRA; [exact R2a| clear; lia| cbn [cells_size csize Nat.add]; clear - RZ32 RZM RZN N8 NR; lia].
      - exists j2. apply TRA; [exact R2b| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZ32 RZM; lia). clear - RZ32 RZM RZN N8 NR. lia. }
    split. { exists j3. apply TRA; [exact R3| clear - RZ16; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - RZN N8 NR; lia). clear. lia. }
    split. { apply TRS; [exact R4| clear; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV1, Z2Nat.id by (clear - RZ16 RZM; lia). clear - RZN RZM N8m S8 N8 NR. lia. }
    split.
    { replace (B + rz - 16 + 16) with (B + 8 * (2 * kr)) in * by (clear - RZM; lia). rewrite (SHX (2 * kr)) in * by (clear - RZ16 RZM; lia).
      apply TRS; [exact R5| clear - RZ16 RZM; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV2, Z2Nat.id by (clear - N8 NR N8m; lia). clear - RZN RZM N8m S8. lia. }
    split.
    { replace (B + rz - 16 + 16 + rup8 n) with (B + 8 * (2 * kr + kn)) in * by (clear - RZM N8m; lia).
      rewrite (SHX (2 * kr + kn)) in * by (clear - RZ16 RZM N8 NR N8m; lia).
      apply TRS; [exact R6| clear - RZ16 RZM N8 NR N8m; lia|]. cbn [cells_size csize]. rewrite Nat.add_0_r, DV4, Z2Nat.id by (clear - RZN RZM N8m S8; lia). clear. lia. }
    destruct (qc_kind ch) as [c v| sc]; [exact I|]. destruct DK as [DK1 DK2]. destruct R7 as [(j7 & R7a) R7b]. split.
    - exists j7. eapply rw_cells_transport_g; [exact R7a| exact MU| cbn [cells_size csize Nat.add]; exact DK1].
    - eapply rw_cells_transport_g; [exact R7b| exact MU| cbn [cells_size csize Nat.add]; exact DK2].
  Qed.

  #[using="Type"] Lemma qbatch_rep_frame_g : forall W (m m' : mem) b nx,
    qbatch_rep AL m b nx -> gmw W m m' ->
    disjoint_from W (qb_addr AL b) 8192 -> disjoint_from W (sh (qb_addr AL b)) 1024 -> qbatch_rep AL m' b nx.
  Proof.
    intros W m m' b nx (R1 & (ws & R2 & LW & FW) & R3) MU DA DS. unfold qbatch_rep.
    split. { eapply rw_cells_transport_g; [exact R1| exact MU|]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact DA| lia| lia]. }
    split. { exists ws. split; [| split; [exact LW| exact FW]]. eapply u64arr_transport_g; [exact R2| exact MU|]. rewrite LW.
             eapply disjoint_from_sub; [exact DA| lia| lia]. }
    eapply rw_cells_transport_g; [exact R3| exact MU|]. cbn [cells_size csize Nat.add]. exact DS.
  Qed.

#[using="Type"] Lemma qchunk_rep_other_gg : forall X (m m' : mem) lo q Ws W tc tsc ch',
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  gmw (Ws ++ W) m m' -> Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
  (forall A n, qc_hull AL ch' A n -> disjoint_from Ws A n) ->
  qchunk_wf ch' -> qchunk_rep AL m ch' -> held_kind X ch' ->
  (forall cv, In cv (prim_of ch') -> ~ In cv tc) -> (forall sc, In sc (sec_of ch') -> ~ In sc tsc) ->
  qchunk_rep AL m' ch'.
Proof.
  intros X m m' lo q Ws W tc tsc ch' AO LOH CLO RP RS TCH TSI MU FW HD WF R HK NP NS.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  assert (DJ : forall A n, qc_hull AL ch' A n -> disjoint_from W A n -> disjoint_from (Ws ++ W) A n)
    by (intros A n HU D; apply disjoint_from_app; split; [exact (HD A n HU)| exact D]).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _).
  destruct ch' as [[c v|sc] rz n]; unfold held_kind in HK; cbn [qc_kind] in HK.
  - destruct (atouch_clear_prim AL lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK TSI W c v FW HK
                (NP (c, v) ltac:(cbn; left; reflexivity))) as [DA DS].
    pose proof HK as (Hc & _). cbn [fst] in Hc. pose proof (class_size_mod16 c Hc) as CM.
    eapply qchunk_rep_frame_g; [exact R| exact WF| | | exact MU| | | exact I].
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
    eapply qchunk_rep_frame_g; [exact R| exact WF| | | exact MU| | |].
    + unfold qc_blk. cbn [qc_kind]. clear - CK1. Z.div_mod_to_equations. lia.
    + unfold qc_bsize. cbn [qc_kind]. clear - CM2. Z.div_mod_to_equations. lia.
    + apply DJ; [left; split; reflexivity|]. unfold qc_blk, qc_bsize. cbn [qc_kind]. eapply disjoint_from_sub; [exact DA| clear; lia| clear; lia].
    + apply DJ; [right; left; split; reflexivity|]. unfold qc_blk, qc_bsize. cbn [qc_kind]. rewrite SHB, DV. eapply disjoint_from_sub; [exact DS| clear; lia| clear; lia].
    + cbn [qc_kind]. split; [apply DJ; [right; right; cbn [qc_kind]; left; split; reflexivity|]; eapply disjoint_from_sub; [exact DA| clear; lia| clear - CM1; lia]
                            | apply DJ; [right; right; cbn [qc_kind]; right; split; reflexivity|]; eapply disjoint_from_sub; [exact DS| clear; lia| clear - CM1 CM2; Z.div_mod_to_equations; lia]].
Qed.

#[using="Type"] Lemma qbatch_rep_other_gg : forall X (m m' : mem) lo q Ws W tc tsc b nx,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  gmw (Ws ++ W) m m' -> Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
  disjoint_from Ws (qb_addr AL b) 8192 -> disjoint_from Ws (sh (qb_addr AL b)) 1024 ->
  qbatch_rep AL m b nx -> held1 (fst X) (bpair b) -> ~ In (bpair b) tc ->
  qbatch_rep AL m' b nx.
Proof.
  intros X m m' lo q Ws W tc tsc b nx AO LOH CLO RP RS TCH TSI MU FW D1 D2 R HK NP.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  destruct (atouch_clear_prim AL lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK TSI W K_BCLASS (qb_v b) FW HK NP) as [DA DS].
  change (class_size K_BCLASS) with 8192 in DA, DS. change (8192 / 8) with 1024 in DS.
  eapply qbatch_rep_frame_g; [exact R| exact MU| |]; apply disjoint_from_app; split; assumption.
Qed.

#[using="Type"] Lemma qlist_rep_other_gg : forall X (m m' : mem) lo q Ws W tc tsc l nxt,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  gmw (Ws ++ W) m m' -> Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
  qlist_rep AL m l nxt ->
  Forall (fun b => held1 (fst X) (bpair b) /\ ~ In (bpair b) tc /\ disjoint_from Ws (qb_addr AL b) 8192 /\ disjoint_from Ws (sh (qb_addr AL b)) 1024) l ->
  qlist_rep AL m' l nxt.
Proof.
  intros X m m' lo q Ws W tc tsc l nxt AO LOH CLO RP RS TCH TSI MU FW. induction l as [|b l IH]; intros QL FB; [exact I|].
  cbn [qlist_rep] in *. destruct QL as [RB QL]. apply Forall_cons_iff in FB as [(HB & NB & D1 & D2) FB]. split; [| exact (IH QL FB)].
  exact (qbatch_rep_other_gg X m m' lo q Ws W tc tsc b _ AO LOH CLO RP RS TCH TSI MU FW D1 D2 RB HB NB).
Qed.
End QG.
