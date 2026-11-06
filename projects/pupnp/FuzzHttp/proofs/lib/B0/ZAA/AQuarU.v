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
                        APrimDealloc ASec ASecD F_sec_A F_sec_B F_sec_C AQuar F_quar_Ep F_quar_E AQuarM AHeap AFoot AQuarR AQuarS AQuarP AQuarT.
Import ListNotations.
Open Scope Z_scope.

Section DU.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation THR := (at_thr (al_thread AL)).
Notation D := (al_depot AL).

#[using="Type"] Lemma hull_izone_dj : forall X (m : mem) lo W ch A n,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> held_kind X ch -> Forall (izone AL lo) W ->
  qc_hull AL ch A n -> disjoint_from W A n.
Proof.
  intros X m lo W ch A n AO LOH CLO RP RS HK' FZ HU.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  layout_apart_fact AO 0%nat 3%nat A03.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  assert (DJZ : forall A n, 0 <= n -> 6328320 <= A -> A + n <= alloc_ceiling -> (A + n <= THR \/ THR + 4096 <= A) -> disjoint_from W A n).
  { intros A1 n1 N0 HA HN HT. apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[[[Z1 Z2]|[Z1 Z2]]|ZE]]; cbn [fst snd] in *; [lia| lia| lia|].
    inversion ZE; subst a b. lia. }
  assert (DJS : forall A n, 0 <= n -> 2147450880 <= A -> A + n <= 17594333495296 -> disjoint_from W A n).
  { intros A1 n1 N0 HA HN. apply dj_of_Forall. eapply Forall_impl; [| exact FZ]. intros [a b] [Z1|[[[Z1 Z2]|[Z1 Z2]]|ZE]]; cbn [fst snd] in *; [clear - Z1 HN LOH; lia| lia| lia|].
    inversion ZE; subst a b. clear - HA HN T3 N0. lia. }
  destruct ch as [[c v|sc] rz n0]; unfold held_kind in HK'; cbn [qc_kind] in HK'; unfold qc_hull, qc_blk, qc_bsize in HU; cbn [qc_kind] in HU.
  - pose proof (held_geo AL (fst X) AO WF0 c v HK') as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & CS & G5 & G6 & G7). rewrite G5 in G7.
    pose proof (region_range AL c Hc) as [RR1 RR2].
    destruct HU as [[-> ->]|[[-> ->]|[]]].
    + apply DJZ; [clear - CS; lia| clear - G1 RR1 SP1; lia| clear - G2 G3 RR2 SP2; lia| clear - G1 G2 G3 RR1 RR2 A03; lia].
    + apply DJS; [apply Z.div_pos; [clear - CS; lia| lia]| exact G6| exact G7].
  - pose proof (sec_geo AL (snd X) SOK sc HK') as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
    pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
    pose proof (proj1 (Forall_forall _ _) COK sc HK') as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2]. destruct CK as (CK1 & _ & _ & _ & _ & _ & D7').
    unfold al_regions in D7'. do 3 (apply Forall_cons_iff in D7' as [_ D7']). apply Forall_cons_iff in D7' as [DTH _].
    cbn [fst snd] in DTH. unfold apart in DTH.
    assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
    assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
    destruct HU as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
    + apply DJZ; [lia| lia| lia| clear - DTH CM1; lia].
    + rewrite SHB, DV. apply DJS; [clear - CM1 CM2; Z.div_mod_to_equations; lia| lia| lia].
    + apply DJZ; [lia| lia| lia| clear - DTH CM1; lia].
    + apply DJS; [lia| lia| clear - D10 CM1 CM2; Z.div_mod_to_equations; lia].
Qed.

#[using="Type"] Lemma qlist_rep_frame_i : forall X (m m' : mem) (lo : Z) W l nxt,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (izone AL lo) W -> munch W m m' ->
  qlist_rep AL m l nxt -> Forall (fun b => held1 (fst X) (bpair b)) l -> qlist_rep AL m' l nxt.
Proof.
  intros X m m' lo W l nxt AO LOH CLO RP RS FZ MU QL FB.
  assert (MU0 : munch (W ++ []) m m') by (rewrite app_nil_r; exact MU).
  eapply (qlist_rep_other_g AL X m m' lo lo W [] [] [] l nxt AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) MU0 ltac:(constructor) QL).
  eapply Forall_impl; [| exact FB]. intros b HB. split; [exact HB|]. split; [intros []|].
  pose proof (hull_izone_dj X m lo W (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) _ _ AO LOH CLO RP RS HB FZ ltac:(unfold qc_hull, qc_blk, qc_bsize; cbn [qc_kind]; left; split; reflexivity)) as D1.
  pose proof (hull_izone_dj X m lo W (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) _ _ AO LOH CLO RP RS HB FZ ltac:(unfold qc_hull, qc_blk, qc_bsize; cbn [qc_kind]; right; left; split; reflexivity)) as D2.
  unfold qc_blk, qc_bsize in D1, D2. cbn [qc_kind] in D1, D2. change (class_size K_BCLASS) with 8192 in D1, D2. change (8192 / 8) with 1024 in D2. split; assumption.
Qed.
End DU.
