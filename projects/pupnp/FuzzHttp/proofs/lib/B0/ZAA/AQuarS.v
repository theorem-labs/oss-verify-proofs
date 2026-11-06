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
                        APrimDealloc ASec ASecD F_sec_A F_sec_C AQuar AQuarM AHeap AFoot AQuarR.
Import ListNotations.
Open Scope Z_scope.

Definition qstat (iv : Z * Z) : Prop := QUAR_MTX <= fst iv /\ snd iv <= QUAR_GQ + 32.

Definition dstat (iv : Z * Z) : Prop := 1598472 <= fst iv /\ snd iv <= 5858360.

Definition iastat (iv : Z * Z) : Prop := (743232 <= fst iv /\ snd iv <= 1271664) \/ (1327048 <= fst iv /\ snd iv <= 1327052).
Definition img_out_q (iv : Z * Z) : Prop := snd iv <= 0x10000 \/ 0x609000 <= fst iv \/ qstat iv \/ (dstat iv \/ iastat iv).

Ltac frame_cell_q C MU WM F :=
  eapply rw_cells_transport; [exact C| exact MU| exact WM|
    apply disjoint_from_of_Forall; eapply Forall_impl; [| exact F]; intros [lo' hi'] Hiv'; unfold img_out_q, qstat, dstat, iastat in Hiv'; cbn in Hiv' |- *; lia].

Lemma poison_env_frame_q : forall E W m m',
  poison_env E m -> munch W m m' -> wmono asegs m m' -> Forall img_out_q W -> poison_env E m'.
Proof.
  intros E W m m' PE MU WM F. pe_split PE. unfold poison_env.
  repeat match goal with |- _ /\ _ => split end; try lia.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell_q C MU WM F end.
Qed.

Section T.
Context {HC : HasCeiling}.

Definition thread_clear_q (L : athread) (W : list (Z * Z)) : Prop :=
  Forall (fun iv : Z * Z => img_out_q iv
     /\ (at_ctx L + 160 <= fst iv \/ snd iv <= at_ctx L + 152)
     /\ (at_thr L + 24 <= fst iv \/ snd iv <= at_thr L + 8)
     /\ (at_thr L + 41 <= fst iv \/ snd iv <= at_thr L + 40)
     /\ (at_thr L + 3169 <= fst iv \/ snd iv <= at_thr L + 3168)) W.

#[using="Type"] Lemma thread_env_frame_q : forall L W m m',
  thread_env L m -> munch W m m' -> wmono asegs m m' -> thread_clear_q L W -> thread_env L m'.
Proof.
  intros L W m m' TE MU WM F. unfold thread_clear_q in F. te_split TE. unfold thread_env.
  repeat match goal with |- _ /\ _ => split end.
  all: match goal with C : rw_cells asegs _ ?A ?cs |- rw_cells asegs _ ?A ?cs => frame_cell_q C MU WM F end.
Qed.
End T.

Section FR.
Context {HC : HasCeiling}.
Variable AL : alayout.
Notation PARR := (al_parr AL).
Notation THR := (at_thr (al_thread AL)).

#[using="Type"] Lemma RSEC_frame_but_q : forall S W m m',
  RSEC AL S m -> munch W m m' -> wmono_but W m m' -> Forall img_out_q W ->
  0 <= PARR -> disjoint_from W PARR (2^23) ->
  Forall (fun d => disjoint_from W (sc_beg d) 32) (se_chunks S) -> RSEC AL S m'.
Proof.
  intros S W m m' (WF & (ENV & ENV2 & ENV3) & VARS & PR & HD) MU WB F P0 DP DH.
  destruct VARS as ((j24 & j32 & j40 & jsb & jpad & na & nf & cur & mx & VC) & (bsl & BSL & LBSL) & MTX & (g16 & g24 & GST)).
  destruct PR as (ws & PARRu & LWS & FWS).
  pose proof WF as (W0 & _ & W2 & _).
  assert (DI : forall A n, 0x10000 <= A -> A + n <= 0x609000 -> (A + n <= QUAR_MTX \/ QUAR_GQ + 32 <= A) -> (A + n <= 1598472 \/ 5858360 <= A) -> A + n <= 743232 -> disjoint_from W A n).
  { intros A n HA HN HQ HD' HI'. apply dj_of_Forall. eapply Forall_impl; [| exact F]. intros [lo' hi'] Hiv; unfold img_out_q, qstat, dstat, iastat in Hiv; cbn in Hiv |- *. lia. }
  unfold RSEC. split; [exact WF|]. split; [| split; [| split]].
  - split; [| split]; (eapply rw_cells_transport_but; [exact MU| exact WB| eassumption| apply DI; cbn; lia]).
  - unfold sec_vars. split; [| split; [| split]].
    + exists j24, j32, j40, jsb, jpad, na, nf, cur, mx. eapply rw_cells_transport_but; [exact MU| exact WB| exact VC| apply DI; cbn; lia].
    + exists bsl. split; [| exact LBSL]. eapply u64arr_transport_but; [exact MU| exact WB| exact BSL|]. rewrite LBSL. apply DI; cbn; lia.
    + eapply rw_cells_transport_but; [exact MU| exact WB| exact MTX| apply DI; cbn; lia].
    + exists g16, g24. eapply rw_cells_transport_but; [exact MU| exact WB| exact GST| apply DI; cbn; lia].
  - exists ws. split; [| split; [exact LWS| exact FWS]].
    eapply u64arr_transport_but; [exact MU| exact WB| exact PARRu|].
    eapply disjoint_from_sub; [exact DP| lia| lia].
  - intros j d Hj. eapply rw_cells_transport_but; [exact MU| exact WB| exact (HD j d Hj)|].
    cbn. exact (proj1 (Forall_forall _ _) DH d (nth_error_In _ _ Hj)).
Qed.

Definition pzone_q (lo : Z) (iv : Z * Z) : Prop := pzone AL lo iv \/ qstat iv.

#[using="Type"] Lemma RSEC_frame_pzone_q : forall S W (m m' : mem) lo,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RSEC AL S m -> munch W m m' -> wmono asegs m m' -> Forall (pzone_q lo) W -> RSEC AL S m'.
Proof.
  intros S W m m' lo AO LOH CLO RS MU WM ZW.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _).
  pose proof RS as (SWF & _). pose proof SWF as (_ & _ & _ & _ & _ & COK & _).
  layout_facts AO 1%nat LPARR. layout_apart_fact AO 0%nat 1%nat LP01. layout_apart_fact AO 1%nat 3%nat LP13.
  destruct LPARR as (P1 & P2 & _ & _ & _ & _ & _).
  eapply (RSEC_frame_but_q S _ m m' RS MU (wmono_but_of_wmono _ _ _ WM)).
  + eapply Forall_impl; [| exact ZW]. unfold pzone_q, pzone, img_out_q, qstat. intros iv Z0. clear - Z0 SP1 T3 LOH. lia.
  + clear - P1. lia.
  + apply dj_of_Forall. eapply Forall_impl; [| exact ZW]. unfold pzone_q, pzone, qstat. intros iv Z0. clear - Z0 P1 P2 LP01 LP13 CLO. lia.
  + apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) COK d Hd) as (_ & D2 & _ & _ & D5' & D6 & D7').
    pose proof (chunk_ok_msize AL d (proj1 (Forall_forall _ _) COK d Hd)) as [DM _].
    unfold al_regions in D7'. apply Forall_cons_iff in D7' as [DSP D7']. apply Forall_cons_iff in D7' as [_ D7'].
    apply Forall_cons_iff in D7' as [_ D7']. apply Forall_cons_iff in D7' as [DTH _]. cbn [fst snd] in DSP, DTH. unfold apart in DSP, DTH.
    apply dj_of_Forall. eapply Forall_impl; [| exact ZW]. unfold pzone_q, pzone, qstat. intros iv Z0. clear - Z0 D2 D5' D6 DM DSP DTH CLO. lia.
Qed.
End FR.

Lemma disjoint_from_app : forall W1 W2 a n, disjoint_from (W1 ++ W2) a n <-> disjoint_from W1 a n /\ disjoint_from W2 a n.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a n; cbn [app disjoint_from]; [tauto|]. rewrite IH. tauto. Qed.
Lemma dj_qstat : forall Ws A n, Forall qstat Ws -> QUAR_GQ + 32 <= A -> disjoint_from Ws A n.
Proof. intros Ws A n F HA. apply dj_of_Forall. eapply Forall_impl; [| exact F]. intros [lo' hi'] [Q1 Q2]. cbn [fst snd] in *. lia. Qed.

Lemma NoDup_app_disj_s : forall {T} (l1 l2 : list T) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND H1; [destruct H1|]. cbn [app] in ND. apply NoDup_cons_iff in ND as [NI ND].
  destruct H1 as [->|H1]; [intros H2; apply NI; apply in_or_app; right; exact H2| exact (IH l2 x ND H1)].
Qed.

Section QS.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation THR := (at_thr (al_thread AL)).

Definition qpriv (iv : Z * Z) : Prop := qstat iv \/ sub_iv (THR + TQ_OFF) (THR + TQ_OFF + 32) iv.
#[using="Type"] Lemma dj_qpriv : forall Ws A n, Forall qpriv Ws -> QUAR_GQ + 32 <= A -> (A + n <= THR + TQ_OFF \/ THR + TQ_OFF + 32 <= A) -> disjoint_from Ws A n.
Proof.
  intros Ws A n F HA HT. apply dj_of_Forall. eapply Forall_impl; [| exact F]. intros [lo' hi'] [[Q1 Q2]|[Q1 Q2]]; cbn [fst snd] in *; lia.
Qed.

#[using="Type"] Lemma qchunk_rep_other_s : forall X (m m' : mem) lo q Ws W tc tsc ch',
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  munch (Ws ++ W) m m' -> Forall qpriv Ws -> Forall (atouch AL lo q (fst X) (snd X) tc tsc) W ->
  qchunk_wf ch' -> qchunk_rep AL m ch' -> held_kind X ch' ->
  (forall cv, In cv (prim_of ch') -> ~ In cv tc) -> (forall sc, In sc (sec_of ch') -> ~ In sc tsc) ->
  qchunk_rep AL m' ch'.
Proof.
  intros X m m' lo q Ws W tc tsc ch' AO LOH CLO RP RS TCH TSI MU FS FW WF R HK NP NS.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  assert (DJ : forall A n, QUAR_GQ + 32 <= A -> (A + n <= THR + TQ_OFF \/ THR + TQ_OFF + 32 <= A) -> disjoint_from W A n -> disjoint_from (Ws ++ W) A n)
    by (intros A n HA HT D; apply disjoint_from_app; split; [apply dj_qpriv; assumption| exact D]).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_apart_fact AO 0%nat 3%nat AP03.
  destruct ch' as [[c v|sc] rz n]; unfold held_kind in HK; cbn [qc_kind] in HK.
  - destruct (atouch_clear_prim AL lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK TSI W c v FW HK
                (NP (c, v) ltac:(cbn; left; reflexivity))) as [DA DS].
    pose proof (held_geo AL (fst X) AO WF0 c v HK) as G. cbv zeta in G. destruct G as (Hc & G1 & G2 & G3 & _ & G5 & G6 & G7).
    pose proof (region_range AL c Hc) as [RR1 RR2]. pose proof (class_size_mod16 c Hc) as CM. rewrite G5 in G7.
    eapply qchunk_rep_frame_m; [exact R| exact WF| | | exact MU| | | exact I].
    + unfold qc_blk. cbn [qc_kind]. unfold region. clear - SPM. Z.div_mod_to_equations. lia.
    + unfold qc_bsize. cbn [qc_kind]. clear - CM. Z.div_mod_to_equations. lia.
    + unfold qc_blk, qc_bsize. cbn [qc_kind]. apply DJ; [clear - G1 RR1 SP1; lia| clear - G1 G2 G3 RR1 RR2 AP03; lia| exact DA].
    + unfold qc_blk, qc_bsize. cbn [qc_kind]. apply DJ; [clear - G6; lia| clear - G6 G7 T3; lia| exact DS].
  - destruct (atouch_clear_sec AL lo q (fst X) (snd X) tc tsc AO WF0 LOH CLO TCH SOK SSEP TSI W sc FW HK
                (NS sc ltac:(cbn; left; reflexivity))) as [DA DS].
    pose proof (sec_geo AL (snd X) SOK sc HK) as (D1 & D2 & _ & _ & _ & _ & D7 & D8 & D9 & D10). rewrite D8 in D10.
    pose proof (proj1 (Forall_forall _ _) SOK sc HK) as CK. pose proof (chunk_ok_msize AL sc CK) as [CM1 CM2].
    destruct CK as (CK1 & _).
    assert (SHB : sh (sc_beg sc + 4096) = sh (sc_beg sc) + 512) by (unfold sh; clear - CK1; Z.div_mod_to_equations; lia).
    assert (DV : (sc_msize sc - 4096) / 8 = sc_msize sc / 8 - 512) by (clear - CM2; Z.div_mod_to_equations; lia).
    eapply qchunk_rep_frame_m; [exact R| exact WF| | | exact MU| | |].
    + unfold qc_blk. cbn [qc_kind]. clear - CK1. Z.div_mod_to_equations. lia.
    + unfold qc_bsize. cbn [qc_kind]. clear - CM2. Z.div_mod_to_equations. lia.
    + unfold qc_blk, qc_bsize. cbn [qc_kind]. apply DJ; [clear - D1; lia| clear - D7; lia|]. eapply disjoint_from_sub; [exact DA| clear; lia| clear; lia].
    + unfold qc_blk, qc_bsize. cbn [qc_kind]. rewrite SHB, DV. apply DJ; [clear - D9; lia| clear - D9 D10 T3 CM1; lia|]. eapply disjoint_from_sub; [exact DS| clear; lia| clear; lia].
    + cbn [qc_kind]. split; [apply DJ; [clear - D1; lia| clear - D7 CM1; lia|]; eapply disjoint_from_sub; [exact DA| clear; lia| clear - CM1; lia]
                            | apply DJ; [clear - D9; lia| clear - D9 D10 T3 CM1 CM2; Z.div_mod_to_equations; lia|]; eapply disjoint_from_sub; [exact DS| clear; lia| clear - CM1 CM2; Z.div_mod_to_equations; lia]].
Qed.

#[using="Type"] Lemma dr_inv_requeue : forall X H (m m' : mem) WB WB' WC hrest lo q Ws W,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  dr_inv AL E X H m WB WC hrest ->
  munch (Ws ++ W) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  Forall qpriv Ws -> Forall (fun iv => sub_iv lo q iv \/ exists b, In b WB /\ chunk_iv AL K_BCLASS (qb_v b) iv) W ->
  Permutation (map bpair WB') (map bpair WB) ->
  Forall qbatch_wf0 WB' -> Forall (fun b => exists nx, qbatch_rep AL m' b nx) WB' ->
  dr_inv AL E X H m' WB' WC hrest.
Proof.
  intros X H m m' WB WB' WC hrest lo q Ws W AO LOH CLO INV MU WM MI' FS FW PM BWF' BREP'.
  destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
  assert (SHL : 2147450880 <= sh (al_space AL)) by (unfold sh, SHADOW_OFF; clear - SP1; Z.div_mod_to_equations; lia).
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  assert (HB : forall b, In b WB -> held1 (fst X) (bpair b)).
  { intros b Hb. destruct HOK as [_ FH]. apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb. }
  assert (BGEO : forall b iv, In b WB -> chunk_iv AL K_BCLASS (qb_v b) iv -> al_space AL <= fst iv /\ snd iv <= al_space AL + K_SPACE).
  { intros b iv Hb [C1 C2]. pose proof (held_geo AL (fst X) AO WF0 K_BCLASS (qb_v b) (HB b Hb)) as G. cbv zeta in G.
    destruct G as (_ & G1 & G2 & G3 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2]. change (class_size K_BCLASS) with 8192 in *.
    clear - C1 C2 G1 G2 G3 R1 R2. lia. }
  assert (TCH : Forall (held1 (fst X)) (map bpair WB)) by (apply Forall_forall; intros cv Hcv; apply in_map_iff in Hcv as (b & <- & Hb); exact (HB b Hb)).
  assert (FWa : Forall (atouch AL lo q (fst X) (snd X) (map bpair WB) []) W).
  { eapply Forall_impl; [| exact FW]. intros iv [S1|(b & Hb & CI)]; [left; exact S1|].
    right; right; right; right; left. exists (bpair b). split; [apply in_map; exact Hb| left; exact CI]. }
  unfold dr_inv.
  split.
  { apply (RPRIM_frame AL AO (fst X) _ m m' RP MU WM). unfold prim_clear. apply Forall_app. split.
    - eapply Forall_impl; [| exact FS]. intros iv [[Q1 Q2]|[Q1 Q2]]; left; unfold prim_out.
      + clear - Q1 Q2 SP1 SHL T3. repeat split; lia.
      + layout_apart_fact AO 0%nat 3%nat AP03. clear - Q1 Q2 T3 T4 AP03 SHL SHS SP1. repeat split; lia.
    - eapply Forall_impl; [| exact FW]. intros iv [[S1 S2]|(b & Hb & CI)].
      + left. unfold prim_out. clear - S1 LOH CLO ACR T3 T4 SP2 SHS. repeat split; lia.
      + right. exists K_BCLASS, (qb_v b). split; [exact (HB b Hb)| left; exact CI]. }
  split; [exact POK|].
  split.
  { eapply (RSEC_frame_pzone_q AL (snd X) _ m m' lo AO LOH CLO RS MU WM). apply Forall_app. split.
    - eapply Forall_impl; [| exact FS]. intros iv [Q|[Q1 Q2]]; [right; exact Q| left; unfold pzone; right; right; left; clear - Q1 Q2; lia].
    - eapply Forall_impl; [| exact FW]. intros iv [[S1 S2]|(b & Hb & CI)]; left; unfold pzone.
      + right; right; right. exact S1.
      + left. pose proof (BGEO b iv Hb CI). lia. }
  split; [exact MI'|].
  assert (IOQ : Forall img_out_q (Ws ++ W)).
  { apply Forall_app. split.
    - eapply Forall_impl; [| exact FS]. intros iv [Q|[Q1 Q2]]; [right; right; left; exact Q| unfold img_out_q; clear - Q1 Q2 T3; lia].
    - eapply Forall_impl; [| exact FW]. intros iv [[S1 S2]|(b & Hb & CI)]; right; left; [clear - S1 LOH; lia| pose proof (BGEO b iv Hb CI) as BG; clear - BG SP1; lia]. }
  split; [exact (poison_env_frame_q E _ m m' PE MU WM IOQ)|].
  split.
  { eapply (thread_env_frame_q L _ m m' TE MU WM). unfold thread_clear_q. apply Forall_app. split.
    - eapply Forall_impl; [| exact FS]. intros iv [Q|[Q1 Q2]].
      + split; [right; right; left; exact Q|]. destruct Q as [Q1 Q2]. clear - Q1 Q2 T1 T3. lia.
      + split; [unfold img_out_q; clear - Q1 Q2 T3; lia|]. clear - Q1 Q2 T5. lia.
    - eapply Forall_impl; [| exact FW]. intros iv [[S1 S2]|(b & Hb & CI)].
      + split; [right; left; clear - S1 LOH; lia|]. clear - S1 CLO T2 T4. lia.
      + pose proof (BGEO b iv Hb CI) as BG. split; [right; left; clear - BG SP1; lia|].
        layout_apart_fact AO 0%nat 2%nat AP02. layout_apart_fact AO 0%nat 3%nat AP03. clear - BG AP02 AP03. lia. }
  split; [eapply shvis_wmono; [exact SV| exact WM]|].
  split; [exact WFS|].
  split.
  { apply Forall_forall. intros ch' Hin.
    eapply (qchunk_rep_other_s X m m' lo q Ws W (map bpair WB) [] ch' AO LOH CLO RP RS TCH ltac:(intros d []) MU FS FWa).
    - exact (proj1 (Forall_forall _ _) WFS ch' Hin).
    - exact (proj1 (Forall_forall _ _) REPS ch' Hin).
    - exact (proj1 (Forall_forall _ _) HKS ch' Hin).
    - intros cv Hcv Hb. destruct HOK as [ND _]. apply (NoDup_app_disj_s (map bpair WB) (flat_map prim_of WC ++ hrest) cv ND Hb).
      apply in_or_app. left. apply in_flat_map. exists ch'. split; assumption.
    - intros sc _ []. }
  split; [exact HKS|].
  split.
  { destruct HOK as [ND FH]. split.
    - eapply Permutation_NoDup; [| exact ND]. apply Permutation_app_tail. apply Permutation_sym. exact PM.
    - eapply Permutation_Forall; [| exact FH]. apply Permutation_app_tail. apply Permutation_sym. exact PM. }
  split; [exact NDS|]. split; [exact BWF'| exact BREP'].
Qed.

#[using="Type"] Lemma atouch_qstat_dj : forall X (m : mem) lo q W tc tsc A n,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  Forall (atouch AL lo q (fst X) (snd X) tc tsc) W -> QUAR_MTX <= A -> A + n <= QUAR_GQ + 32 -> disjoint_from W A n.
Proof.
  intros X m lo q W tc tsc A n AO LOH CLO RP RS TCH TSI FW QA QN.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
  assert (RGE : forall c0, region AL c0 = al_space AL + c0 * K_REGION) by reflexivity.
  assert (SHL : forall x, 0 <= x -> 2147450880 <= sh x) by (intros x Hx; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros iv AT. unfold atouch, sub_iv in AT.
  destruct AT as [AT|[AT|[AT|[AT|[AT|[AT|[AT|AT]]]]]]].
  - left. clear - AT QN LOH. lia.
  - right. clear - AT QA. lia.
  - clear - AT QA QN T3. lia.
  - destruct AT as (c0 & Hc0 & [AT|[AT|AT]]).
    + left. unfold ri_addr, RIB in AT. clear - AT QN SP1 Hc0. lia.
    + left. pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & _). rewrite !RGE in *. clear - AT QN SP1 Hc0 K1. lia.
    + left. pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & _).
      pose proof (SHL (region AL c0 + p_au (get_cls (fst X) c0)) ltac:(rewrite RGE; clear - SP1 Hc0 K1; lia)) as SHX. clear - AT QN SHX. lia.
  - destruct AT as ([c1 v1] & Hin & AT). cbn [fst snd] in AT.
    pose proof (proj1 (Forall_forall _ _) TCH _ Hin) as HE1. pose proof (held_geo AL (fst X) AO WF0 c1 v1 HE1) as G'. cbv zeta in G'.
    destruct G' as (Hc1 & H1 & H2 & H3 & CS1 & H5 & H6 & H7). pose proof (region_range AL c1 Hc1) as [Q1 Q2]. rewrite RGE in *.
    left. unfold chunk_iv, chunk_sh_iv in AT. rewrite RGE in AT. destruct AT as [AT|AT]; [clear - AT QN H1 SP1 Hc1; lia| clear - AT QN H6; lia].
  - destruct AT as (sc & Hin & AT). pose proof (sec_geo AL (snd X) SOK sc (TSI sc Hin)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
    left. destruct AT as [AT|AT]; [clear - AT QN D1; lia| clear - AT QN D9; lia].
  - destruct AT as (d & Hin & AT). pose proof (sec_geo AL (snd X) SOK d Hin) as (D1 & _). left. clear - AT QN D1. lia.
  - clear - AT QA QN P1. lia.
Qed.

#[using="Type"] Lemma atouch_img_dj : forall X (m : mem) lo q W tc tsc A n,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  Forall (atouch AL lo q (fst X) (snd X) tc tsc) W -> GSTATS_A + 16 <= A -> A + n <= 6328320 -> disjoint_from W A n.
Proof.
  intros X m lo q W tc tsc A n AO LOH CLO RP RS TCH TSI FW QA QN.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
  assert (RGE : forall c0, region AL c0 = al_space AL + c0 * K_REGION) by reflexivity.
  assert (SHL : forall x, 0 <= x -> 2147450880 <= sh x) by (intros x Hx; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros iv AT. unfold atouch, sub_iv in AT.
  destruct AT as [AT|[AT|[AT|[AT|[AT|[AT|[AT|AT]]]]]]].
  - left. clear - AT QN LOH. lia.
  - right. clear - AT QA. lia.
  - clear - AT QA QN T3. lia.
  - destruct AT as (c0 & Hc0 & [AT|[AT|AT]]).
    + left. unfold ri_addr, RIB in AT. clear - AT QN SP1 Hc0. lia.
    + left. pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & _). rewrite !RGE in *. clear - AT QN SP1 Hc0 K1. lia.
    + left. pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & _).
      pose proof (SHL (region AL c0 + p_au (get_cls (fst X) c0)) ltac:(rewrite RGE; clear - SP1 Hc0 K1; lia)) as SHX. clear - AT QN SHX. lia.
  - destruct AT as ([c1 v1] & Hin & AT). cbn [fst snd] in AT.
    pose proof (proj1 (Forall_forall _ _) TCH _ Hin) as HE1. pose proof (held_geo AL (fst X) AO WF0 c1 v1 HE1) as G'. cbv zeta in G'.
    destruct G' as (Hc1 & H1 & H2 & H3 & CS1 & H5 & H6 & H7). pose proof (region_range AL c1 Hc1) as [Q1 Q2]. rewrite RGE in *.
    left. unfold chunk_iv, chunk_sh_iv in AT. rewrite RGE in AT. destruct AT as [AT|AT]; [clear - AT QN H1 SP1 Hc1; lia| clear - AT QN H6; lia].
  - destruct AT as (sc & Hin & AT). pose proof (sec_geo AL (snd X) SOK sc (TSI sc Hin)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
    left. destruct AT as [AT|AT]; [clear - AT QN D1; lia| clear - AT QN D9; lia].
  - destruct AT as (d & Hin & AT). pose proof (sec_geo AL (snd X) SOK d Hin) as (D1 & _). left. clear - AT QN D1. lia.
  - clear - AT QA QN P1. lia.
Qed.

#[using="Type"] Lemma atouch_tq_dj : forall X (m : mem) lo q W tc tsc A n,
  alayout_ok AL -> 0x10007fff8000 <= lo -> alloc_ceiling <= lo ->
  RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
  Forall (atouch AL lo q (fst X) (snd X) tc tsc) W -> THR + TQ_OFF <= A -> A + n <= THR + TQ_OFF + 32 -> disjoint_from W A n.
Proof.
  intros X m lo q W tc tsc A n AO LOH CLO RP RS TCH TSI FW QA QN.
  destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
  layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
  pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (_ & _ & T3 & T4 & _).
  layout_facts AO 1%nat LPARR. destruct LPARR as (P1 & P2 & _).
  layout_apart_fact AO 0%nat 3%nat AP03. layout_apart_fact AO 1%nat 3%nat AP13.
  assert (RGE : forall c0, region AL c0 = al_space AL + c0 * K_REGION) by reflexivity.
  assert (SHR : forall x, 0 <= x <= 2^47 -> 2147450880 <= sh x <= 17594333495296) by (intros x Hx; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros iv AT. unfold atouch, sub_iv in AT.
  destruct AT as [AT|[AT|[AT|[AT|[AT|[AT|[AT|AT]]]]]]].
  - left. clear - AT QN T4 CLO. lia.
  - clear - AT QA QN T3. lia.
  - left. clear - AT QN. lia.
  - destruct AT as (c0 & Hc0 & [AT|[AT|AT]]).
    + unfold ri_addr, RIB in AT. clear - AT QA QN AP03 Hc0. lia.
    + pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & K2 & _). rewrite !RGE in *. clear - AT QA QN AP03 Hc0 K1 K2 Q2. lia.
    + pose proof (region_range AL c0 Hc0) as [Q1 Q2]. pose proof (WF0 c0 Hc0) as (_ & _ & _ & _ & _ & _ & K1 & K2 & _).
      pose proof (SHR (region AL c0 + p_au (get_cls (fst X) c0)) ltac:(rewrite RGE in *; clear - SP1 SP5 Hc0 K1 K2 Q2; lia)) as SH1.
      pose proof (SHR (region AL (c0 + 1)) ltac:(rewrite RGE in *; clear - SP1 SP5 Hc0 Q2; lia)) as SH2. clear - AT QA QN SH1 SH2 T3. lia.
  - destruct AT as ([c1 v1] & Hin & AT). cbn [fst snd] in AT.
    pose proof (proj1 (Forall_forall _ _) TCH _ Hin) as HE1. pose proof (held_geo AL (fst X) AO WF0 c1 v1 HE1) as G'. cbv zeta in G'.
    destruct G' as (Hc1 & H1 & H2 & H3 & CS1 & H5 & H6 & H7). pose proof (region_range AL c1 Hc1) as [Q1 Q2]. rewrite H5 in H7. rewrite RGE in *.
    unfold chunk_iv, chunk_sh_iv in AT. rewrite RGE in AT. destruct AT as [AT|AT]; [clear - AT QA QN H1 H2 H3 Q2 AP03 Hc1; lia| clear - AT QA QN H6 H7 T3; lia].
  - destruct AT as (sc & Hin & AT). pose proof (sec_geo AL (snd X) SOK sc (TSI sc Hin)) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite D8 in D10.
    destruct AT as [AT|AT]; [clear - AT QA QN D7; lia| clear - AT QA QN D9 D10 T3; lia].
  - destruct AT as (d & Hin & AT). pose proof (sec_geo AL (snd X) SOK d Hin) as (D1 & D2 & _ & _ & _ & _ & D7 & _). clear - AT QA QN D2 D7. lia.
  - clear - AT QA QN AP13. lia.
Qed.
End QS.
