(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sf_bytes_ro_C8 : forall (m : mem) a (w : word), bytes_at rsegs m a (le8 w) -> ro_cells rsegs m a [C8 w].
Proof. intros m a w B. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B. Qed.
Lemma sf_bytes_ro_C1 : forall (m : mem) a (b : byte), bytes_at rsegs m a [b] -> ro_cells rsegs m a [C1 b].
Proof. intros m a b B. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. exact B. Qed.
Lemma sf_mapped_wr_at : forall (m : mem) a n, mapped m a n -> 0 <= a -> a + n <= 2^64 -> wr_at rsegs m a n.
Proof.
  intros m a n M Ha Hn. split; [lia|]. split; [lia|]. intros i Hi. unfold wview, wa.
  destruct (m (Z_to_bv 64 (a + i))) eqn:E; [discriminate|]. exfalso. exact (M i Hi E).
Qed.
Lemma sf_ro_rw : forall (m : mem) a cs, ro_cells rsegs m a cs -> mapped m a (Z.of_nat (cells_size cs)) -> rw_cells rsegs m a cs.
Proof.
  intros m a cs R M. pose proof (bytes_at_bound _ _ _ _ (proj2 R)) as B. destruct R as [WF0 BA].
  rewrite (cells_bytes_length cs WF0) in B. split; [exact (conj WF0 BA)| apply sf_mapped_wr_at; [exact M| lia| lia]].
Qed.
(* [comment removed for export] *)
Lemma sf_mapped_CB : forall (m : mem) a n, mapped m a (Z.of_nat n) -> 0 <= a -> (a + Z.of_nat n <= 0x10000 \/ 0x60a000 <= a) -> a + Z.of_nat n <= 2^64 ->
  exists bs, length bs = n /\ rw_cells rsegs m a [CB n bs].
Proof.
  intros m a n M H0 H1 H2.
  (first [ pose proof ((junk_at_of_mapped rsegs m a (Z.of_nat n) ltac:(lia) ltac:(lia) ltac:(lia) M)) as dR_1; dex1 dR_1 as bs; destruct dR_1 as [L B] | pose proof ((junk_at_of_mapped rsegs m a (Z.of_nat n) ltac:(lia) ltac:(lia) ltac:(lia) M)) as dR_1; dand3 dR_1 as bs L B | destruct (junk_at_of_mapped rsegs m a (Z.of_nat n) ltac:(lia) ltac:(lia) ltac:(lia) M) as (bs & L & B) ]).
  exists bs. split; [lia|]. split; [split; [cbn; split; [lia| exact I] |]|].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. apply sf_mapped_wr_at; [exact M| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FsFrame.
  Context {Clg : Ceiling} {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (ff : Z) (age : nat).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis FF : as_fframe A ff = Some (7, age).
  Let v := aview_of (pa_hull A) m.
  Let W : WF AL_pboth A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  (* [comment removed for export] *)
  Definition sf_pos : Z := ff_pos (a_fhint A 7) 7 age.
  Definition sf_fl : Z := fflag_addr (a_fs A) 7 sf_pos.

  Lemma sf_f : exists f, a_fframes A !! ff = Some f /\ ff_class f = 7 /\ ff_age f = age.
  Proof.
    unfold as_fframe, as_fframe_ in FF. destruct (a_fframes A !! ff) as [f|] eqn:E; [| discriminate]. cbn in FF.
    injection FF as E1 E2. exists f. split; [reflexivity| split; [exact E1| exact E2]].
  Qed.

  (* [comment removed for export] *)
  Lemma sf_geom :
    ff = fframe_addr (a_fs A) 7 sf_pos /\ ff mod 8 = 0 /\ aobj ff (fsize 7) /\ ff + fsize 7 <= alloc_ceiling /\
    aobj sf_fl 1 /\ sf_fl + 1 <= alloc_ceiling /\
    (sf_fl + 1 <= ff \/ ff + fsize 7 <= sf_fl) /\ (sf_fl + 1 <= sh ff \/ sh ff + fsize 7 / 8 <= sf_fl) /\
    a_fs A + kFakeFramesOffset <= ff /\ ff + fsize 7 <= a_fs A + kFakeStackBytes /\
    a_fs A + kFakeFlagsOffset <= sf_fl < a_fs A + kFakeFramesOffset - 16 /\
    0x7fff8200 <= sh ff /\ sh ff + fsize 7 / 8 <= kHighMemBeg /\ 0x60a000 <= ff.
  Proof.
    (first [ dex1 sf_f as f; dand3 sf_f as Hf K7 AG | dand4 sf_f as f Hf K7 AG | destruct sf_f as (f & Hf & K7 & AG) ]). pose proof alloc_ceiling_val as CE.
    pose proof (frame_facts A m md ff f AI Hf) as X. cbv zeta in X. rewrite K7, AG in X.
    (first [ dand15 X as K E AGE R1 R2 FS1 FS2 FSM SZ M64 AL S1 S2 SR1 SR2 | destruct X as (K & E & AGE & R1 & R2 & FS1 & FS2 & FSM & SZ & M64 & AL & S1 & S2 & SR1 & SR2) ]).
    (first [ pose proof ((app_facts _ _ FS1)) as dR_4; dand5 dR_4 as G1 G2 G3 G4 G5 | pose proof (app_facts _ _ FS1) as (G1 & G2 & G3 & G4 & G5) ]).
    pose proof (ff_pos_range (a_fhint A 7) 7 age ltac:(lia)) as PR. fold sf_pos in PR, E.
    pose proof (fflag_addr_range (a_fs A) 7 sf_pos ltac:(lia) PR) as FR. fold sf_fl in FR.
    assert (F7 : fsize 7 = 8192) by reflexivity.
    unfold kFakeFramesOffset, kFakeFlagsOffset, kFakeStackBytes in *.
    assert (OBJ : aobj ff (fsize 7)).
    { apply (proj1 (aobj_app_rangeA _ _)). eapply app_rangeA_sub; [exact FS1| lia| lia| lia]. }
    assert (OBJF : aobj sf_fl 1).
    { apply (proj1 (aobj_app_rangeA _ _)). eapply app_rangeA_sub; [exact FS1| lia| lia| lia]. }
    assert (SHA : sf_fl + 1 <= sh ff \/ sh ff + fsize 7 / 8 <= sf_fl).
    { (* [comment removed for export] *)
      destruct G5 as [LO|HI].
      - left. unfold kLowShadowMapBeg in LO. lia.
      - right. unfold kHighMemBeg in *. lia. }
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sf_SFP : ro_cells rsegs v (saved_flag_ptr ff 7) [C8 (wz sf_fl)].
  Proof.
    (first [ dex1 sf_f as f; dand3 sf_f as Hf K7 AG | dand4 sf_f as f Hf K7 AG | destruct sf_f as (f & Hf & K7 & AG) ]).
    pose proof (ar_fsptrs _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) ff f Hf) as B. fold v in B. rewrite K7, AG in B.
    unfold sf_fl, sf_pos, a_fs. exact (sf_bytes_ro_C8 _ _ _ B).
  Qed.

  (* [comment removed for export] *)
  Lemma sf_FLG : rw_cells rsegs v sf_fl [C1 (Z_to_bv 8 1)].
  Proof.
    (first [ dex1 sf_f as f; dand3 sf_f as Hf K7 AG | dand4 sf_f as f Hf K7 AG | destruct sf_f as (f & Hf & K7 & AG) ]). (first [ dand12 sf_geom as E _ _ _ _ _ _ _ R1 R2 FR _ | destruct sf_geom as (E & _ & _ & _ & _ & _ & _ & _ & R1 & R2 & FR & _) ]).
    pose proof (ff_pos_range (a_fhint A 7) 7 age ltac:(lia)) as PR. fold sf_pos in PR.
    (first [ pose proof ((ar_fsflags _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) 7 sf_pos ltac:(lia) PR)) as dR_8; dex1 dR_8 as b; destruct dR_8 as [U CASES] | pose proof ((ar_fsflags _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) 7 sf_pos ltac:(lia) PR)) as dR_8; dand3 dR_8 as b U CASES | pose proof (ar_fsflags _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) 7 sf_pos ltac:(lia) PR) as (b & U & CASES) ]). fold v in U.
    assert (LIVE : slot_live_ (a_fhint A) (a_fframes A) 7 sf_pos) by (exists ff, f; split; [exact Hf| split; [exact K7| unfold sf_pos; rewrite AG; reflexivity]]).
    destruct CASES as [[-> _]|[_ NL]]; [| exfalso; exact (NL LIVE)].
    change (fflag_addr (p_fs (a_pl A)) 7 sf_pos) with sf_fl in U.
    apply sf_ro_rw; [exact (sf_bytes_ro_C1 _ _ _ U)|]. cbn [cells_size csize Nat.add].
    (first [ pose proof ((ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_9; dand5 dR_9 as _ _ _ M _ | pose proof (ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & _ & M & _) ]). fold v in M.
    intros i Hi. unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *.
    replace (sf_fl + i) with (p_fs (a_pl A) + (sf_fl + i - p_fs (a_pl A))) by lia. apply M. unfold a_fs in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sf_SHC : forall sz, 0 <= sz <= fsize 7 -> exists old, rw_cells rsegs v (sh ff) [CB (Z.to_nat (sz / 8)) old].
  Proof.
    intros sz Hsz. (first [ dand14 sf_geom as E M8 OBJ CEf _ _ _ _ R1 R2 FR SH1 SH2 NB | destruct sf_geom as (E & M8 & OBJ & CEf & _ & _ & _ & _ & R1 & R2 & FR & SH1 & SH2 & NB) ]).
    (first [ pose proof ((ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_11; dand5 dR_11 as _ _ _ _ MS | pose proof (ar_fsbase _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & _ & _ & MS) ]). fold v in MS.
    assert (F7 : fsize 7 = 8192) by reflexivity.
    pose proof (Z_div_mod_eq_full sz 8) as D1. pose proof (Z.mod_pos_bound sz 8 ltac:(lia)) as D2.
    (first [ pose proof ((sf_mapped_CB v (sh ff) (Z.to_nat (sz / 8)))) as dR_12; dex1 dR_12 as bs; destruct dR_12 as [L RW] | pose proof ((sf_mapped_CB v (sh ff) (Z.to_nat (sz / 8)))) as dR_12; dand3 dR_12 as bs L RW | destruct (sf_mapped_CB v (sh ff) (Z.to_nat (sz / 8))) as (bs & L & RW) ]).
    - intros i Hi. pose proof (frame_facts A m md ff) as X.
      (first [ dex1 sf_f as f; dand3 sf_f as Hf K7 AG | dand4 sf_f as f Hf K7 AG | destruct sf_f as (f & Hf & K7 & AG) ]). specialize (X f AI Hf). cbv zeta in X. rewrite K7 in X.
      (first [ dand14 X as _ _ _ _ _ _ _ _ _ _ _ S1 S2 _ | destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _) ]).
      replace (sh ff + i) with (sh (p_fs (a_pl A)) + (sh ff + i - sh (p_fs (a_pl A)))) by lia. apply MS. unfold a_fs in *. lia.
    - unfold kHighMemBeg in *. lia.
    - right. lia.
    - unfold kHighMemBeg in *. lia.
    - exists bs. exact RW.
  Qed.

  (* [comment removed for export] *)
  Lemma sf_fl_owned : pa_owned A sf_fl.
  Proof.
    (first [ dand12 sf_geom as E _ _ _ _ _ _ _ R1 R2 FR _ | destruct sf_geom as (E & _ & _ & _ & _ & _ & _ & _ & R1 & R2 & FR & _) ]).
    (first [ pose proof ((bm_nth_fixed A)) as dR_16; dand8 dR_16 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
    eapply (owned_rt A sf_fl (a_fs A) kFakeStackBytes); [apply rt_fixed_in; cbn; tauto| unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia| |].
    - eapply (fixed_bm_no_live_user A 6); [exact W| lia| exact E6| unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia].
    - intros LF. pose proof (live_frame_zone A sf_fl W LF). unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset in *. lia.
  Qed.
  Lemma sf_tail_owned : forall a, ff + fsize 7 - 8 <= a < ff + fsize 7 -> pa_owned A a.
  Proof.
    intros a Ha. (first [ dand12 sf_geom as E _ _ _ _ _ _ _ R1 R2 FR _ | destruct sf_geom as (E & _ & _ & _ & _ & _ & _ & _ & R1 & R2 & FR & _) ]).
    (first [ pose proof ((bm_nth_fixed A)) as dR_18; dand8 dR_18 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]). assert (F7 : fsize 7 = 8192) by reflexivity.
    eapply (owned_rt A a (a_fs A) kFakeStackBytes); [apply rt_fixed_in; cbn; tauto| unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia| |].
    - eapply (fixed_bm_no_live_user A 6); [exact W| lia| exact E6| unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia].
    - ((first [ intro dR_22; dex2 dR_22 as g f'; destruct dR_22 as [Hg Hr] | intro dR_22; dand4 dR_22 as g f' Hg Hr | intros (g & f' & Hg & Hr) ])).
      destruct (Z.eq_dec g ff) as [->|NE].
      + (first [ dex1 sf_f as f; dand3 sf_f as Hf K7 _ | dand4 sf_f as f Hf K7 _ | destruct sf_f as (f & Hf & K7 & _) ]). rewrite Hf in Hg. injection Hg as <-. rewrite K7 in Hr. lia.
      + pose proof (asI_frame_disjoint A m md ff 7 age g (ff_class f') (ff_age f') AI FF
                      ltac:(unfold as_fframe, as_fframe_; rewrite Hg; reflexivity) ltac:(congruence)) as D.
        pose proof (fsize_pos (ff_class f')) as FP.
        (first [ pose proof ((wfF A W)) as dR_20; dand3 dR_20 as F1 _ _ | destruct (wfF A W) as (F1 & _ & _) ]). (first [ pose proof ((F1 g f' Hg)) as dR_21; dand3 dR_21 as K' _ _ | destruct (F1 g f' Hg) as (K' & _ & _) ]). cbv zeta in K'. specialize (FP K'). lia.
  Qed.
End FsFrame.
