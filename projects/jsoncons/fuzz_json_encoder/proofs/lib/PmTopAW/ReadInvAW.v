(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core PmHeapIfaceA PmIcptIfaceA
  PmLibDefs PmLibDefsA PmLibSpecsA PmEncSpecs PmLibSpecsXA PmLibSpecsW PmLibSpecsXAW PmRef PmRefFacts PmRefFacts2 PmRefAllow PmRefNonneg PmRefRead PmRefXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopSpecsXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopAW Require Import TopSpecsAW ReadKitXAW ReadRoomAW PsKitAW.
Import ListNotations. Import PMRR.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RIAW.
Local Strategy expand [TPSAW.chunk_of TPSAW.rest_of TPSAW.chunk_w].
Section S.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variables (IS : Z) (rep : PML.srep) (P : Z) (CL : Z) (eg0 : PMES.eghost).
Abbreviation segs := (hl_segs L).
Abbreviation mem := PMSA.mem.
Let txt := PML.srep_chars rep.
Let D := PML.srep_data (IS + 80) rep.
Definition rsof := RKAW.rsof IS rep.
Definition wstA := PKAW.wstA L.

(* [comment removed for export] *)
Definition egacc (eg : PMES.eghost) (evs : list PMW.evk) (al : Z) : Prop :=
  PMES.g_es eg = PMW.es_run (PMES.g_es eg0) evs /\ exists pay, 0 <= pay <= al /\ PMES.g_len eg = PMES.g_len eg0 + PMW.ind_run (PMES.g_es eg0) evs + pay.
Definition RW0 (gp rdst : Z) (bof : bool) (eg : PMES.eghost) : Prop := egacc eg [] 0 /\ gp = D /\ rdst = 0 /\ bof = true.
Definition rinvA (M : mem) (ps : PML.pstate) (gp rdst : Z) (bof : bool) (eg : PMES.eghost) : Prop :=
  exists c w evs al F', wstA M P ps c w /\ egacc eg evs al /\ RKAW.accA rep evs al F' (rsof c w gp bof rdst).
Definition rinv6 (M : mem) (ps : PML.pstate) (gp rdst code : Z) (bof : bool) (eg : PMES.eghost) (p k : Z) : Prop :=
  exists c evs al F' gp0 bof0 rdst0 w1, wstA M P ps c [] /\ egacc eg evs al /\ RKAW.accA rep evs al F' (rsof c [] gp0 bof0 rdst0) /\ PMR.c_more c = true /\ PMRN.SIq c /\
    PMR.refill (rsof c [] gp0 bof0 rdst0) = (rsof c w1 gp bof rdst, code) /\ Z.of_nat (length w1) = k /\ (0 < k -> L5.bytes_at segs M p w1) /\
    Forall (fun b => 0 <= b <= 255) w1 /\ (code <> 0 -> w1 = []).
(* [comment removed for export] *)
Definition rinvP (M : mem) (ps : PML.pstate) (gp rdst : Z) (bof : bool) (eg : PMES.eghost) (c : PMR.ctrl) (w : list Z) : Prop :=
  wstA M P ps c w /\ PMRN.SIq c /\ PMR.c_more c = true /\
  exists evs al F' w0 gp0 bof0 rdst0, egacc eg evs al /\ RKAW.accA rep evs al F' (rsof c w0 gp0 bof0 rdst0) /\ PMR.refill (rsof c w0 gp0 bof0 rdst0) = (rsof c w gp bof rdst, 0) /\
    (w0 = [] -> rdst0 = 2 -> w = []).
Definition rinvQ (empty : bool) (M : mem) (ps : PML.pstate) (gp rdst code : Z) (bof : bool) (eg : PMES.eghost) : Prop :=
  exists c w evs al F' w0 gp0 bof0 rdst0, let q := PMR.parse_some c w in
    egacc eg (evs ++ PMR.q_evs q) (al + PMR.q_al q) /\ RKAW.accA rep evs al F' (rsof c w0 gp0 bof0 rdst0) /\ PMR.c_more c = true /\
    PMR.refill (rsof c w0 gp0 bof0 rdst0) = (rsof c w gp bof rdst, 0) /\ (w0 = [] -> rdst0 = 2 -> w = []) /\ code = PMR.q_code q /\
    (code = 0 -> wstA M P ps (PMR.q_c q) (PMR.q_w q)) /\ (if empty then w = [] else w <> []) /\
    (empty = true -> code = 0 -> PML.ps_more ps = true -> rankz c = 1 /\ rankz (PMR.q_c q) = 0).

(* [comment removed for export] *)
Lemma egacc_nil : egacc eg0 [] 0.
Proof. split; [reflexivity | exists 0; split; [clear; lia | cbn; clear; lia]]. Qed.
Lemma egacc_app : forall eg eg2 evs al evs2 al2, egacc eg evs al -> PMES.g_es eg2 = PMW.es_run (PMES.g_es eg) evs2 ->
  (exists pay, 0 <= pay <= al2 /\ PMES.g_len eg2 = PMES.g_len eg + PMW.ind_run (PMES.g_es eg) evs2 + pay) -> egacc eg2 (evs ++ evs2) (al + al2).
Proof.
  intros eg eg2 evs al evs2 al2 (E1 & p1 & P1 & L1) E2 (p2 & P2 & L2). split.
  - rewrite PMW.es_run_app, <- E1. exact E2.
  - exists (p1 + p2). split; [clear - P1 P2; lia|]. rewrite PMW.ind_run_app, <- E1. clear - L1 L2. lia.
Qed.
Lemma RW0_intro : forall gp, gp = D -> RW0 gp 0 true eg0.
Proof. intros gp ->. split; [exact egacc_nil | repeat split; reflexivity]. Qed.
(* [comment removed for export] *)
Lemma rinvA_reset : forall M ps gp rdst bof eg, RW0 gp rdst bof eg -> PML.ps_win ps = None -> rinvA M (TPSA.ps_reset ps) gp rdst bof eg.
Proof.
  intros M ps gp rdst bof eg (EG & -> & -> & ->) HW. exists PMR.ctrl0, [], [], 0, (PMR.rfuel txt).
  split; [exact (PKAW.wstA_reset L M P ps HW)|]. split; [exact EG|]. unfold rsof, D. rewrite (RKAW.rsof_init IS rep). exact (RKAW.accA_init IS rep).
Qed.

(* [comment removed for export] *)
Section Ag.
Variables (M M' : mem) (S : Z -> Prop).
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Abbreviation out := (PTA.out S).
Definition wout (ps : PML.pstate) : Prop := forall p e, PML.ps_win ps = Some (p, e) -> out p (e - p).
Lemma rinvA_ag : forall ps gp rdst bof eg, out (P + 148) 8 -> out (P + 220) 1 -> wout ps -> rinvA M ps gp rdst bof eg -> rinvA M' ps gp rdst bof eg.
Proof.
  intros ps gp rdst bof eg O1 O2 OW (c & w & evs & al & F' & WS & EG & ACC). exists c, w, evs, al, F'.
  split; [exact (PKAW.wstA_ag L M M' S AG P ps c w O1 O2 OW WS) | split; [exact EG | exact ACC]].
Qed.
Lemma rinv6_ag : forall ps gp rdst code bof eg p k, out (P + 148) 8 -> out (P + 220) 1 -> (0 < k -> out p k) ->
  rinv6 M ps gp rdst code bof eg p k -> rinv6 M' ps gp rdst code bof eg p k.
Proof.
  intros ps gp rdst code bof eg p k O1 O2 OP (c & evs & al & F' & gp0 & bof0 & rdst0 & w1 & WS & EG & ACC & CM & SI & RF & LEN & BY & FA & WN).
  exists c, evs, al, F', gp0, bof0, rdst0, w1. split; [exact (PKAW.wstA_ag_exh L M M' S AG P ps c O1 O2 WS)|].
  split; [exact EG|]. split; [exact ACC|]. split; [exact CM|]. split; [exact SI|]. split; [exact RF|]. split; [exact LEN|].
  split; [| split; [exact FA | exact WN]]. intros Hk. apply (PTA.bytes_ag segs M M' S AG); [rewrite LEN; exact (OP Hk) | exact (BY Hk)].
Qed.
Lemma rinvQ_ag : forall empty ps gp rdst code bof eg, out (P + 148) 8 -> out (P + 220) 1 -> wout ps ->
  rinvQ empty M ps gp rdst code bof eg -> rinvQ empty M' ps gp rdst code bof eg.
Proof.
  intros empty ps gp rdst code bof eg O1 O2 OW (c & w & evs & al & F' & w0 & gp0 & bof0 & rdst0 & X). cbv zeta in X. destruct X as (EG & ACC & CM & RF & RW & HC & WS & EM & RK).
  exists c, w, evs, al, F', w0, gp0, bof0, rdst0. cbv zeta. split; [exact EG|]. split; [exact ACC|]. split; [exact CM|]. split; [exact RF|]. split; [exact RW|]. split; [exact HC|].
  split; [| split; [exact EM | exact RK]]. intros Z0. exact (PKAW.wstA_ag L M M' S AG P ps _ _ O1 O2 OW (WS Z0)).
Qed.
End Ag.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rinvP_direct : forall M ps gp rdst bof eg, rinvA M ps gp rdst bof eg -> PML.wf_ps ps -> PML.ps_more ps = true -> ~ PMSA.win_exhausted ps ->
  exists c w, rinvP M ps gp rdst bof eg c w /\ w <> [].
Proof.
  intros M ps gp rdst bof eg (c & w & evs & al & F' & WS & EG & ACC) WF MO NE. pose proof (PKAW.wstA_cons L M P ps c w WS NE) as WNE.
  exists c, w. split; [|exact WNE]. split; [exact WS|]. split; [exact (PKAW.wstA_SIq L M P ps c w WS WF MO)|].
  split; [rewrite (proj1 (proj2 (PKAW.wstA_core L M P ps c w WS))); exact MO|].
  exists evs, al, F', w, gp, bof, rdst. split; [exact EG|]. split; [exact ACC|]. split; [| intros X; exfalso; exact (WNE X)].
  apply RKAW.refill_same. left. unfold rsof. rewrite RKAW.r_w_rsof. exact WNE.
Qed.
(* [comment removed for export] *)
Lemma rinv6_of_chunk : forall M M' ps gp rdst bof eg ch p k gp' rdst' code bof',
  rinvA M ps gp rdst bof eg -> PML.wf_ps ps -> PML.ps_more ps = true -> PMSA.win_exhausted ps ->
  D <= gp <= D + Z.of_nat (length txt) -> (rdst = 0 \/ rdst = 2) -> Forall (fun b => 0 <= b <= 255) txt ->
  (rdst = 2 -> k = 0 /\ gp' = gp /\ rdst' = 2 /\ bof' = bof /\ code = 0) -> (rdst = 0 -> TPSAW.chunk_w L M' IS rep gp bof ch p k gp' rdst' code bof') ->
  (forall c, wstA M P ps c [] -> wstA M' P ps c []) ->      (* [comment removed for export] *)
  rinv6 M' ps gp' rdst' code bof' eg p k.
Proof.
  intros M M' ps gp rdst bof eg ch p k gp' rdst' code bof' (c & w & evs & al & F' & WS & EG & ACC) WF MO EX Hgp Hrd HB WE WC TR.
  pose proof (PKAW.wstA_nil L M P ps c w WS EX) as ->.
  pose proof (PKAW.wstA_SIq L M P ps c [] WS WF MO) as SI. pose proof (proj1 (proj2 (PKAW.wstA_core L M P ps c [] WS))) as CMO. rewrite MO in CMO.
  destruct Hrd as [-> | ->].
  - destruct (RKAW.refill_of_chunk_w L IS rep M' c gp bof ch p k gp' rdst' code bof' Hgp (WC eq_refl)) as (s & j & cd & b' & Hs & EC & RF & G' & RD & RD' & C0 & C1).
    assert (FS : Forall (fun b => 0 <= b <= 255) s) by (rewrite <- Hs; unfold TPSAW.chunk_of, TPSAW.rest_of; apply Forall_firstn; apply Forall_skipn; exact HB).
    exists c, evs, al, F', gp, bof, 0, (if code =? 0 then skipn j s else []).
    split; [exact (TR c WS)|]. split; [exact EG|]. split; [exact ACC|]. split; [exact CMO|]. split; [exact SI|]. split; [exact RF|].
    destruct (Z.eqb_spec code 0) as [Z0|NZ].
    + destruct (C0 Z0) as (K1 & JL & KP). split; [rewrite length_skipn, Nat2Z.inj_sub by exact JL; clear - K1; lia|]. split; [intros Hk; exact (proj2 (KP Hk))|].
      split; [apply Forall_skipn; exact FS | intros X; exfalso; exact (X Z0)].
    + pose proof (C1 NZ) as K0. split; [cbn; clear - K0; lia|]. split; [intros Hk; exfalso; clear - Hk K0; lia|]. split; [constructor | intros _; reflexivity].
  - destruct (WE eq_refl) as (-> & -> & -> & -> & ->). exists c, evs, al, F', gp, bof, 2, [].
    split; [exact (TR c WS)|]. split; [exact EG|]. split; [exact ACC|]. split; [exact CMO|]. split; [exact SI|]. split; [apply (RKAW.refill_at_eof IS rep)|].
    split; [reflexivity|]. split; [intros Hk; exfalso; clear - Hk; lia|]. split; [constructor | intros _; reflexivity].
Qed.
(* [comment removed for export] *)
Lemma rinvP_of_6_nil : forall M M' ps gp rdst bof eg p, rinv6 M ps gp rdst 0 bof eg p 0 -> (forall c, wstA M P ps c [] -> wstA M' P ps c []) ->
  exists c, rinvP M' ps gp rdst bof eg c [].
Proof.
  intros M M' ps gp rdst bof eg p (c & evs & al & F' & gp0 & bof0 & rdst0 & w1 & WS & EG & ACC & CM & SI & RF & LEN & _ & _ & _) TR.
  assert (W1 : w1 = []) by (destruct w1; [reflexivity | cbn [length] in LEN; lia]). subst w1.
  exists c. split; [exact (TR c WS)|]. split; [exact SI|]. split; [exact CM|]. exists evs, al, F', [], gp0, bof0, rdst0.
  split; [exact EG|]. split; [exact ACC|]. split; [exact RF | intros _ _; reflexivity].
Qed.
Lemma rinvP_of_6_win : forall M M' ps gp rdst bof eg p k, rinv6 M ps gp rdst 0 bof eg p k -> 0 < k ->
  (forall c, PMRXA.rm_matchA L c M P ps -> PMRXA.rm_matchA L c M' P ps) -> (forall w, L5.bytes_at segs M p w -> Z.of_nat (length w) = k -> L5.bytes_at segs M' p w) ->
  exists c w, rinvP M' (PML.ps_set_win ps (Some (p, p + k))) gp rdst bof eg c w /\ w <> [].
Proof.
  intros M M' ps gp rdst bof eg p k (c & evs & al & F' & gp0 & bof0 & rdst0 & w1 & WS & EG & ACC & CM & SI & RF & LEN & BY & FA & _) Hk TRM TRB.
  exists c, w1. split; [| intros ->; cbn [length] in LEN; clear - LEN Hk; lia].
  split; [exact (PKAW.wstA_set_win L M' P ps c w1 p k (TRM c (PKAW.wstA_rm L M P ps c [] WS)) (TRB w1 (BY Hk) LEN) LEN FA)|].
  split; [exact SI|]. split; [exact CM|]. exists evs, al, F', [], gp0, bof0, rdst0. split; [exact EG|]. split; [exact ACC|]. split; [exact RF|].
  intros _ E2. subst rdst0. unfold rsof in RF. rewrite (RKAW.refill_at_eof IS rep) in RF.
  pose proof (f_equal (fun pr => PMR.r_w (fst pr)) RF) as X. cbn [fst PMR.r_w RKAW.rsof] in X. symmetry. exact X.
Qed.

(* [comment removed for export] *)
Lemma psome_room : forall M ps gp rdst bof eg c w, rinvP M ps gp rdst bof eg c w -> PMXAW.wroom CL eg0 (PMR.K txt) (PMR.ALLOW txt) ->
  PMXAW.wroomr (PMRXA.the_rmA L) CL eg (PMW.rm_step (PMRXA.the_rmA L) PMW.FParseSome c w).
Proof.
  intros M ps gp rdst bof eg c w (WS & SI & CM & evs & al & F' & w0 & gp0 & bof0 & rdst0 & EG & ACC & RF & _) W0.
  rewrite PMXAW.wroomr_eq. change (PMW.r_evs (PMW.rm_step (PMRXA.the_rmA L) PMW.FParseSome c w)) with (PMR.q_evs (PMR.parse_some c w)).
  change (PMW.r_allow (PMW.rm_step (PMRXA.the_rmA L) PMW.FParseSome c w)) with (PMR.q_al (PMR.parse_some c w)).
  destruct EG as [EGes EGlen].
  apply (RRAW.round_room IS rep CL eg0 eg evs al F' (rsof c w0 gp0 bof0 rdst0) (rsof c w gp bof rdst) (PMR.parse_some c w) ACC); [unfold rsof; rewrite RKAW.r_c_rsof; exact CM | exact RF | reflexivity | unfold rsof; rewrite RKAW.r_c_rsof; exact SI | exact W0 | exact EGes | exact EGlen].
Qed.

(* [comment removed for export] *)
Lemma rinvQ_of_post : forall M M2 ps ps' gp rdst bof eg eg2 c w code,
  rinvP M ps gp rdst bof eg c w ->
  (let rr := PMW.rm_step (PMRXA.the_rmA L) PMW.FParseSome c w in
   code = PMW.r_code rr /\ PMES.g_es eg2 = PMW.es_run (PMES.g_es eg) (PMW.r_evs rr) /\
   (exists pay, 0 <= pay <= PMW.r_allow rr /\ PMES.g_len eg2 = PMES.g_len eg + PMW.ind_run (PMES.g_es eg) (PMW.r_evs rr) + pay) /\
   (code = 0 -> PMW.rm_match (PMRXA.the_rmA L) (PMW.r_ctrl rr) M2 P ps' /\ PMW.r_used rr = PML.winlen ps - PML.winlen ps' /\ PMXAW.win_bytesA L M2 ps' (PMW.w_after (PMRXA.the_rmA L) rr w))) ->
  (PMSA.win_exhausted ps -> code = 0 -> PML.ps_more ps' = true -> In (PML.ps_st ps) [PML.ST_NUMBER; PML.ST_CR] /\ ~ In (PML.ps_st ps') [PML.ST_NUMBER; PML.ST_CR]) ->
  rinvQ (match w with [] => true | _ => false end) M2 ps' gp rdst code bof eg2.
Proof.
  intros M M2 ps ps' gp rdst bof eg eg2 c w code (WS & SI & CM & evs & al & F' & w0 & gp0 & bof0 & rdst0 & EG & ACC & RF & RW) W3 REL3.
  cbv zeta in W3. destruct W3 as (HC & HES & HPAY & HW).
  change (PMW.r_code (PMW.rm_step (PMRXA.the_rmA L) PMW.FParseSome c w)) with (PMR.q_code (PMR.parse_some c w)) in HC.
  change (PMW.r_evs (PMW.rm_step (PMRXA.the_rmA L) PMW.FParseSome c w)) with (PMR.q_evs (PMR.parse_some c w)) in HES, HPAY.
  change (PMW.r_allow (PMW.rm_step (PMRXA.the_rmA L) PMW.FParseSome c w)) with (PMR.q_al (PMR.parse_some c w)) in HPAY.
  change (PMW.r_ctrl (PMW.rm_step (PMRXA.the_rmA L) PMW.FParseSome c w)) with (PMR.q_c (PMR.parse_some c w)) in HW.
  exists c, w, evs, al, F', w0, gp0, bof0, rdst0. cbv zeta.
  split; [exact (egacc_app eg eg2 evs al _ _ EG HES HPAY)|]. split; [exact ACC|]. split; [exact CM|]. split; [exact RF|]. split; [exact RW|]. split; [exact HC|].
  split.
  { intros Z0. destruct (HW Z0) as (RM & _ & WB). split; [exact RM|].
    change (PMW.w_after (PMRXA.the_rmA L) (PMW.rm_step (PMRXA.the_rmA L) PMW.FParseSome c w) w) with (PMW.w_after PMR.the_rm (PMR.rstep PMW.FParseSome c w) w) in WB.
    rewrite (RKAW.parse_some_after c w) in WB. exact WB. }
  split; [destruct w; [reflexivity | intros X; discriminate X]|].
  intros EM Z0 MO. pose proof (PKAW.wstA_core L M P ps c w WS) as (Cst & _ & _).
  assert (EX : PMSA.win_exhausted ps) by (destruct w; [exact (PKAW.wstA_exh L M P ps c WS) | discriminate EM]).
  destruct (REL3 EX Z0 MO) as [I1 I2]. destruct (HW Z0) as (RM & _ & _). pose proof RM as ((Cst2 & _) & _).
  split.
  - unfold rankz. rewrite Cst. destruct I1 as [<-|[<-|[]]]; reflexivity.
  - unfold rankz. rewrite Cst2. destruct (Z.eqb_spec (PML.ps_st ps') PML.ST_NUMBER) as [X|X]; [exfalso; apply I2; left; symmetry; exact X|].
    destruct (Z.eqb_spec (PML.ps_st ps') PML.ST_CR) as [Y|Y]; [exfalso; apply I2; right; left; symmetry; exact Y | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma rinvA_of_Q_cont : forall M ps gp rdst bof eg, rinvQ false M ps gp rdst 0 bof eg -> PML.ps_more ps = true -> PMSA.win_exhausted ps -> rinvA M ps gp rdst bof eg.
Proof.
  intros M ps gp rdst bof eg (c & w & evs & al & F' & w0 & gp0 & bof0 & rdst0 & X) MO EX. cbv zeta in X. destruct X as (EG & ACC & CM & RF & RW & HC & WS & WNE & _).
  specialize (WS eq_refl). set (q := PMR.parse_some c w) in *.
  pose proof (PKAW.wstA_core L M P ps _ _ WS) as (Cst2 & Cmo2 & Cdn2). pose proof (PKAW.wstA_nil L M P ps _ _ WS EX) as QW.
  destruct (RKAW.roundA_cont IS rep evs al F' _ _ q ACC ltac:(unfold rsof; rewrite RKAW.r_c_rsof; exact CM) RF eq_refl (eq_sym HC)) as [F'' ACC2].
  - left. unfold rsof. rewrite RKAW.weof_rsof. destruct w; [exfalso; exact (WNE eq_refl) | reflexivity].
  - exact QW.
  - rewrite Cmo2. exact MO.
  - unfold rsof. rewrite RKAW.r_w_rsof, RKAW.r_eof_rsof. intros W00 E0. apply Z.eqb_eq in E0. exfalso. exact (WNE (RW W00 E0)).
  - exists (PMR.q_c q), (PMR.q_w q), (evs ++ PMR.q_evs q), (al + PMR.q_al q), F''. split; [exact WS|]. split; [exact EG|].
    unfold rsof. rewrite <- (RKAW.rs_after_rsof IS rep q c w gp bof rdst). exact ACC2.
Qed.
Lemma rinvA_of_Q_eof : forall M ps gp rdst bof eg, rinvQ true M ps gp rdst 0 bof eg -> PML.ps_more ps = true -> PMSA.win_exhausted ps ->
  PML.ps_st ps <> PML.ST_START -> (PML.ps_st ps = PML.ST_ACCEPT \/ PML.ps_done ps = true) -> rinvA M ps gp rdst bof eg.
Proof.
  intros M ps gp rdst bof eg (c & w & evs & al & F' & w0 & gp0 & bof0 & rdst0 & X) MO EX N1 OR2. cbv zeta in X. destruct X as (EG & ACC & CM & RF & RW & HC & WS & -> & RK).
  specialize (WS eq_refl). set (q := PMR.parse_some c []) in *.
  pose proof (PKAW.wstA_core L M P ps _ _ WS) as (Cst2 & Cmo2 & Cdn2). pose proof (PKAW.wstA_nil L M P ps _ _ WS EX) as QW.
  destruct (RKAW.roundA_cont IS rep evs al F' _ _ q ACC ltac:(unfold rsof; rewrite RKAW.r_c_rsof; exact CM) RF eq_refl (eq_sym HC)) as [F'' ACC2].
  - right. rewrite Cst2, Cdn2. split; [exact N1 | exact OR2].
  - exact QW.
  - rewrite Cmo2. exact MO.
  - intros _ _. exact (RK eq_refl eq_refl MO).
  - exists (PMR.q_c q), (PMR.q_w q), (evs ++ PMR.q_evs q), (al + PMR.q_al q), F''. split; [exact WS|]. split; [exact EG|].
    unfold rsof. rewrite <- (RKAW.rs_after_rsof IS rep q c [] gp bof rdst). exact ACC2.
Qed.
End S.
End RIAW.
