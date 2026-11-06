(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm8PlanKit Pm8L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutShA CutShB CutShC.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_casan_T Cut_psome_casan_D Cut_psome_casan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsoInstCA PsoSemA PsoSemCA PsoKnCA PsoBaseCA ParseSomeChkCA PsoLeafCA PsoAuxCA PsoXiCA PsoLinkCA PsoFrmCA PsoStCA PsoGotoCA PsoGxCA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_casan.

Module PSOCS.

Definition term_ok (c : CC.cutpoint) (cells : list kentry) (l : PSO.pv) : bool :=
  (negb (PSO.has_bufbyte (CC.cp_F c)) || PSO.has cells (KWord (SA (APC.eadd (PSO.v_size l) (PSO.v_bptr l)) 0) 1 (ELit 0)))%bool.
Definition p213_ok (c : CC.cutpoint) (cells : list kentry) : bool :=
  (PSO.has cells (KWord (SA PE 213) 1 (ELit 1)) || negb (existsb (PSO.region_eqb (PE, 200, ELit 16)) (CC.cp_F c)))%bool.

Definition rw_leaf (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (r : CSLR.row) : bool :=
  let cells := SR.ps_cells ps in
  match PSO.pview (CC.cp_know c), PSO.pview cells, nth_error G.CPS (CSLR.r_j r) with
  | Some t, Some l, Some _ =>
      let d := PSO.mkdelta cells t l in
      (PSO.is_same (PSO.d_st d) && PSO.is_same (PSO.d_sst d) && PSO.is_same (PSO.d_nst d) && PSO.is_same (PSO.d_more d) && PSO.is_same (PSO.d_done d)
       && PSO.is_same (PSO.d_wptr d) && PSO.frame_same d && PSO.view_ok (CC.cp_nx c) (CC.cp_know c) t && PSO.view_ok (CC.cp_nx c) cells l
       && term_ok c cells l
       && ((PSO.is_same (PSO.d_size d) && negb (PSO.has_bufbyte (CC.cp_F c)))
           || (fd_eqb (PSO.d_size d) (PSO.Lit 0) && PSO.size_ok c cells l d && match PSO.tst c cells t with Some z => negb (Z.eqb z 17) && byteb z | None => false end))
       && p213_ok c cells && PSO.is_loopk (PSO.kind_of i) && PSO.kind_eqb (PSO.kind_of (CSLR.r_j r)) PSO.KCsl && negb (CSLR.r_tab r)
       && negb (PSO.curk (PSO.kind_of i)) && expr_eqb (CC.slook (CSLR.r_sid r) 60) FLE && Nat.ltb (CSLR.r_j r) PSO.NCUT

       && implb (fd_eqb (PSO.d_size d) (PSO.Lit 0)) (PSO.rng_in (CC.cp_know c) (PSO.v_more t) 1 255))%bool
  | _, _, _ => false
  end.

Definition dd_leaf (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (pc : Z) : bool :=
  (PSO.kind_eqb (PSO.kind_of i) PSO.KDead ||
   match PSO.pview (CC.cp_know c) with
   | Some t =>
       let cells := SR.ps_cells ps in
       let more_ok := ((PSO.rng_in cells (PSO.v_more t) 1 255 || PSO.rng_in (CC.cp_know c) (PSO.v_more t) 1 255 || PSO.kind_eqb (PSO.kind_of i) PSO.KSm)
                       && PSO.view_ok (CC.cp_nx c) (CC.cp_know c) t)%bool in
       (Z.eqb pc DEAD && more_ok && (PSO.is_loopk (PSO.kind_of i) || PSO.kind_eqb (PSO.kind_of i) PSO.KSm)
        && ((match PSO.tst c cells t with Some z => negb (PSO.handledb z) && byteb z | None => false end)
            || (PSO.rng_in cells (PSO.v_st t) 0 255 && PSO.has cells (KRange (EAlu Instr.ALU_SLTU (ELit 27) (EAlu Instr.ALU_ADD (PSO.v_st t) (ELit (-1)))) 1 1))))
       || (PSO.kind_eqb (PSO.kind_of i) PSO.KHQ && PSO.hq_dead cells && more_ok
           && match PSO.tst c cells t with
              | Some z => negb (PSO.inb z QSTATES) && byteb z && (negb (Z.eqb z 17) || (expr_eqb (PSO.v_wptr t) PSO.CURH && PSO.lo_ge (CC.cp_know c) (EVar JV) 1))
              | None => false end)
   | None => false
   end)%bool.
Definition cs_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (tg : CC.tag) : bool :=
  match tg with
  | CC.TOther pc =>
      if PSO.dead_chk i ps pc then dd_leaf i c ps pc
      else if (Z.eqb pc RET || Z.eqb pc SETSH || Z.eqb pc SM4 || PSO.inb pc PSO.CALLEES)%bool then true
      else match CSLR.find_row PSO.ROWS i (SR.ps_pc ps) with Some r => rw_leaf i c ps r | None => true end
  | CC.TGoto _ _ => true
  end.
Lemma CS_all : CH2.leaves_all G.CPS G.TAGS cs_chk = true. Proof. vmc_refl. Qed.
Lemma U0CSL_all : forallb (fun i => implb (PSO.kind_eqb (PSO.kind_of i) PSO.KCsl) (negb (PSO.u0 i))) (seq 0 PSO.NCUT) = true. Proof. vmc_refl. Qed.

Lemma rchk_tab : forall NF d CPS BLS FFS CPF SBz kv SE ENDE LENB KZB TLO TG K1 K2 i c ps r, CSLR.r_tab r = false ->
  CSLR.row_chk NF d CPS BLS FFS CPF SBz kv SE ENDE LENB KZB TLO TG K1 i c ps r = CSLR.row_chk NF d CPS BLS FFS CPF SBz kv SE ENDE LENB KZB TLO TG K2 i c ps r.
Proof. intros. unfold CSLR.row_chk. rewrite H. reflexivity. Qed.

Lemma handledb_of : forall x, PML.handled x -> PSO.handledb x = true.
Proof.
  intros x H. unfold PSO.handledb. unfold PML.handled in H.
  repeat (rewrite ?Bool.orb_true_iff, ?Bool.andb_true_iff). rewrite ?Z.leb_le, ?Z.eqb_eq. lia.
Qed.

Section RWS.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation E := (PSOI.iE I).     Local Abbreviation B := (PSOI.iB I).
Local Abbreviation M := (PSOI.iM I).     Local Abbreviation model := (PSOI.imodel I). Local Abbreviation ps := (PSOI.ips I).
Local Abbreviation HIok := (PSOI.iHIok I). Local Abbreviation E0 := (PSOI.E0 I).
Local Abbreviation WW := (WW I).            Local Abbreviation Cred := (PSOX.Cred I).

Variables (i : nat) (c : CC.cutpoint) (ps0 : SR.post_spec) (r : CSLR.row) (t l : PSO.pv) (cj : CC.cutpoint).
Local Abbreviation cells := (SR.ps_cells ps0).
Local Abbreviation d := (PSO.mkdelta (SR.ps_cells ps0) t l).
Local Abbreviation j := (CSLR.r_j r).
Hypothesis Hci : nth_error G.CPS i = Some c.
Hypothesis Ht : PSO.pview (CC.cp_know c) = Some t.
Hypothesis Hl : PSO.pview cells = Some l.
Hypothesis Hcj : nth_error G.CPS j = Some cj.
Hypothesis HRW : rw_leaf i c ps0 r = true.
Hypothesis HBL : CH2.blocks_eqb (CH2.bsubst GT.NF (CSLR.r_sid r) (nth j G.BLS [])) (nth i G.BLS []) = true.
Variables (Ec : env) (Rc : bvmap 5 word) (El : env) (Rl : bvmap 5 word) (A1 : list (Z * Z)) (Mc : mem) (mc : Model) (Ml : mem) (ml : Model).
Hypothesis HAt : CCA.AtV (hl_segs L) c Ec Rc A1 Mc mc.
Hypothesis HA : AAMB I i Ec A1 Mc mc.
Hypothesis Hag : env_agree (CC.cp_nx c) Ec El.
Hypothesis HLF : CCA.leaf_factsA (hl_segs L) c ps0 El Rl A1 Mc mc Ml ml.
Hypothesis HXI : PSOX.XI I i Ec A1 Mc mc.
Local Abbreviation Ej := (CC.env_over GT.NF (CSLR.r_sid r) El).

Record RWR : Prop := MKRWR {
  w_st : PSO.is_same (PSO.d_st d) = true; w_sst : PSO.is_same (PSO.d_sst d) = true; w_nst : PSO.is_same (PSO.d_nst d) = true;
  w_more : PSO.is_same (PSO.d_more d) = true; w_done : PSO.is_same (PSO.d_done d) = true; w_wptr : PSO.is_same (PSO.d_wptr d) = true;
  w_fs : PSO.frame_same d = true; w_vt : PSO.view_ok (CC.cp_nx c) (CC.cp_know c) t = true; w_vl : PSO.view_ok (CC.cp_nx c) cells l = true;
  w_term : term_ok c cells l = true;
  w_size : ((PSO.is_same (PSO.d_size d) && negb (PSO.has_bufbyte (CC.cp_F c)))
            || (fd_eqb (PSO.d_size d) (PSO.Lit 0) && PSO.size_ok c cells l d && match PSO.tst c cells t with Some z => negb (Z.eqb z 17) && byteb z | None => false end))%bool = true;
  w_213 : p213_ok c cells = true; w_loop : PSO.is_loopk (PSO.kind_of i) = true; w_kj : PSO.kind_eqb (PSO.kind_of j) PSO.KCsl = true; w_tab : negb (CSLR.r_tab r) = true;
  w_cur : negb (PSO.curk (PSO.kind_of i)) = true; w_fl : expr_eqb (CC.slook (CSLR.r_sid r) 60) FLE = true; w_jn : Nat.ltb j PSO.NCUT = true;
  w_m1 : implb (fd_eqb (PSO.d_size d) (PSO.Lit 0)) (PSO.rng_in (CC.cp_know c) (PSO.v_more t) 1 255) = true }.
Lemma RWB : RWR.
Proof.
  pose proof HRW as X. unfold rw_leaf in X. rewrite Ht, Hl, Hcj in X. cbv zeta in X.
  repeat match type of X with (_ && _)%bool = true => apply andb_prop in X as [X ?] end. constructor; assumption.
Qed.
Lemma Hi : (2 <= i < PSO.NCUT)%nat.
Proof. apply (ge2_of_kind i c _ Hci eq_refl). intros X. pose proof (w_loop RWB) as Y. rewrite X in Y. discriminate Y. Qed.
Lemma Hj : (j < PSO.NCUT)%nat. Proof. apply Nat.ltb_lt. exact (w_jn RWB). Qed.
Lemma KN : know_ok (hl_segs L) El (CCA.vis A1 ml Ml) cells.
Proof. unfold know_ok. apply Forall_forall. intros X HX. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX). Qed.
Lemma KT : know_ok (hl_segs L) Ec (CCA.vis A1 mc Mc) (CC.cp_know c). Proof. destruct HAt as [_ HK]. exact HK. Qed.
Lemma FLFc : PSOX.FLF I Ec. Proof. exact (PSOX.xi_flf _ _ _ _ HXI (proj1 Hi)). Qed.

Lemma AGVl : forall a, PSOI.iV I + 8 <= a < PSOI.iV I + 48 -> Ml (Z_to_bv 64 a) = Mc (Z_to_bv 64 a).
Proof. exact (PSOST.AGV I i c ps0 Ec A1 Mc mc El Rl Ml ml Hi Hci HA FLFc Hag HLF). Qed.
Lemma MORE1T : forall mw ps1 code g1, PSOX.CORE I i Ec Mc mw ps1 code g1 -> PSO.rng_in (CC.cp_know c) (PSO.v_more t) 1 255 = true -> PML.ps_more ps1 = true.
Proof.
  intros mw ps1 code g1 CO X. pose proof (PSOST.tv_more _ _ _ _ (PSOST.TVAL I i c Ec Rc A1 Mc mc mw ps1 code g1 t Hci Hi HAt HA CO Ht)) as TM. unfold PSO.rng_in in X.
  destruct (CX.range3 (CC.cp_know c) (PSO.v_more t)) as [[lo hi]|] eqn:HR; [|discriminate X]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
  pose proof (CX.range3_sound _ _ _ _ _ _ _ KT HR) as RG. pose proof (PSOGX.b2z_of _ _ TM ltac:(unfold CL5A.uv; lia)) as BZ.
  destruct (PML.ps_more ps1); [reflexivity|]. cbn in BZ. unfold CL5A.uv in BZ. lia.
Qed.
Lemma FLFj : PSOX.FLF I Ej.
Proof.
  pose proof FLFc as F. unfold PSOX.FLF in *. pose proof (w_fl RWB) as XF. apply expr_eqb_eq in XF.
  assert (EQ : CL5A.uv Ej FLE = CL5A.uv Ec FLE).
  { unfold CL5A.uv, FLE, FLV. cbn [edenot CC.env_over ev]. replace (Nat.ltb 60 GT.NF) with false by reflexivity. rewrite XF. unfold FLE, FLV. cbn [edenot].
    rewrite <- (proj1 Hag 60%nat) by (pose proof (PSOST.nx66 i c Hi Hci); lia). reflexivity. }
  rewrite EQ. exact F.
Qed.
Lemma RBLK : PSOX.bptrI j Ej = PSOX.bptrI i El /\ PSOX.bcapI j Ej = PSOX.bcapI i El /\ PSOX.sbI j Ej = PSOX.sbI i El /\ PSOX.scapI j Ej = PSOX.scapI i El.
Proof.
  pose proof HBL as X. apply CH2.blocks_eqb_eq in X.
  pose proof (CH2.den_bsubst GT.NF (CSLR.r_sid r) El (nth j G.BLS [])) as D. rewrite X in D.
  rewrite (bls_i i (proj2 Hi)), (bls_i j Hj) in D.
  unfold PSOX.bptrI, PSOX.bcapI, PSOX.sbI, PSOX.scapI, CL5A.uv. destruct (PSO.blk0 i) as [b0 c0]; destruct (PSO.blk1 i) as [b1 c1]; destruct (PSO.blk0 j) as [b0' c0']; destruct (PSO.blk1 j) as [b1' c1'].
  unfold CH2.den in D. cbn [map fst snd] in D |- *. injection D as D1 D2 D3 D4. rewrite D1, D2, D3, D4. repeat split; reflexivity.
Qed.
Lemma BLKj : PSOX.bptrI j Ej = PSOX.bptrI i Ec /\ PSOX.bcapI j Ej = PSOX.bcapI i Ec /\ PSOX.sbI j Ej = PSOX.sbI i Ec /\ PSOX.scapI j Ej = PSOX.scapI i Ec.
Proof.
  destruct RBLK as (G1 & G2 & G3 & G4). destruct (BLKAG i c Ec El Hci Hag) as (A1' & A2 & A3 & A4).
  rewrite G1, G2, G3, G4, A1', A2, A3, A4. repeat split; reflexivity.
Qed.
Lemma U0j : PSO.u0 j = false.
Proof.
  pose proof (proj1 (forallb_forall _ _) U0CSL_all j ltac:(apply in_seq; pose proof Hj; lia)) as X. cbv beta in X.
  rewrite (w_kj RWB) in X. cbn [implb] in X. destruct (PSO.u0 j); [discriminate X | reflexivity].
Qed.
Lemma KJ : PSO.kind_of j = PSO.KCsl. Proof. apply PSO.kind_eqb_eq. exact (w_kj RWB). Qed.

Lemma vt_st : APC.expr_vars_lt (CC.cp_nx c) (PSO.v_st t) = true.
Proof. pose proof (w_vt RWB) as X. unfold PSO.view_ok in X. cbn [forallb] in X. repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end. assumption. Qed.
Lemma RW_XI : PSOX.XI I j Ej A1 Ml ml.
Proof.
  pose proof RWB as RW. destruct (PSOX.xi_loop _ _ _ _ HXI (w_loop RW)) as (ps1 & g1 & CO & WF & SO & _).
  pose proof (PSOGX.LOOPU0 i (proj2 Hi) (w_loop RW)) as U0.
  assert (RK : PSOX.retk (PSO.kind_of i) = false /\ PSOX.wlk (PSO.kind_of i) = true) by (pose proof (w_loop RW) as X; destruct (PSO.kind_of i); try discriminate X; split; reflexivity).
  pose proof (PSOST.STRETCH_same I i c ps0 Ec Rc A1 Mc mc El Rl Ml ml _ ps1 0 g1 t l Hci Hi HAt HA Hag HLF CO Ht (w_vt RW)) as SM.
  pose proof (PSOST.TVAL I i c Ec Rc A1 Mc mc _ ps1 0 g1 t Hci Hi HAt HA CO Ht) as TV.
  destruct RW as [S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 S12 S13 S14 S15 S16 S17 S18 S19].
  apply PSOST.is_same_eq in S1, S2, S3, S4, S5, S6.
  pose proof (PSOX.c_win _ _ _ _ _ _ _ _ CO) as WN. unfold PSOX.WIN in WN.
  assert (WL : PSOI.wlo (PML.ps_win ps1) = CL5A.uv El (PSO.v_wptr l) /\ match PML.ps_win ps1 with Some (p, e) => p <= e | None => PML.ps_win ps1 = None end).
  { pose proof (WINF I) as (WI0 & WI1 & WI2 & _ & _ & _ & WIC & _).
    rewrite (PSOST.s_wptr _ _ _ _ _ _ SM S6). destruct (PML.ps_win ps) as [[p0 e0]|] eqn:Hw.
    - destruct WN as (p1 & -> & R1). pose proof (PSOI.WSOME I p0 e0 Hw) as (WP0E & WE0E & _). cbn [PSOI.wlo].
      unfold PSOI.wlen in WIC, WI1, WI2. split; [rewrite Z.mod_small by lia; reflexivity | lia].
    - rewrite WN. split; reflexivity. }
  assert (SZ : PSO.size_ok c cells l d = true).
  { apply orb_prop in S11 as [X|X]; [apply andb_prop in X as [X _]; apply PSOST.is_same_eq in X; unfold PSO.size_ok; rewrite X; reflexivity
                                  | apply andb_prop in X as [X _]; apply andb_prop in X as [_ X]; exact X]. }
  assert (TERM : PSO.has_bufbyte (CC.cp_F c) = false \/ PSO.has cells (KWord (SA (APC.eadd (PSO.v_size l) (PSO.v_bptr l)) 0) 1 (ELit 0)) = true).
  { unfold term_ok in S10. apply orb_prop in S10 as [T|T]; [left; apply negb_true_iff in T; exact T | right; exact T]. }
  assert (X213 : PSO.has cells (KWord (SA PE 213) 1 (ELit 1)) = true \/ existsb (PSO.region_eqb (PE, 200, ELit 16)) (CC.cp_F c) = false).
  { unfold p213_ok in S12. apply orb_prop in S12 as [T|T]; [left; exact T | right; apply negb_true_iff in T; exact T]. }
  destruct (PSOST.STRETCH I i c ps0 Ec Rc A1 Mc mc El Rl Ml ml _ ps1 0 g1 t l Hci Hi HAt HA Hag HLF FLFc CO Ht Hl S8 S7 SZ TERM X213
              (PML.ps_st ps1) (PML.ps_sst ps1) (PML.ps_nst ps1) (PML.ps_more ps1) (PML.ps_done ps1) (PML.ps_win ps1)
              (PSOST.s_st _ _ _ _ _ _ SM S1) (PSOST.s_sst _ _ _ _ _ _ SM S2) (PSOST.s_nst _ _ _ _ _ _ SM S3) (PSOST.s_more _ _ _ _ _ _ SM S4) (PSOST.s_done _ _ _ _ _ _ SM S5)
              (proj1 WL) eq_refl ltac:(destruct (PML.ps_win ps1) as [[p e]|]; [exact (proj2 WL) | reflexivity])) as (buf2 & MEM & B1 & B2).

  assert (BUF : (buf2 = PML.ps_buf ps1 \/ buf2 = []) /\ (buf2 <> PML.ps_buf ps1 -> PML.ps_more ps1 = true /\ PML.ps_st ps1 <> PML.ST_NUMBER)).
  { apply orb_prop in S11 as [X|X].
    - apply andb_prop in X as [X X']. apply PSOST.is_same_eq in X. apply negb_true_iff in X'. destruct (B1 X) as (_ & EQ). rewrite (EQ X').
      split; [left; reflexivity | intros N; exfalso; exact (N eq_refl)].
    - apply andb_prop in X as [X X3]. apply andb_prop in X as [X _]. apply fd_eqb_eq in X.
      split; [right; apply B2; rewrite X; intros Y; discriminate Y|].
      assert (HM : PML.ps_more ps1 = true) by (rewrite X in S19; cbn [fd_eqb Z.eqb implb] in S19; exact (MORE1T _ _ _ _ CO S19)).
      intros _. split; [exact HM|]. intros HS. destruct (PSO.tst c cells t) as [z|] eqn:TS; [|discriminate X3]. apply andb_prop in X3 as [Z1 Z2]. apply negb_true_iff in Z1. apply Z.eqb_neq in Z1.
      unfold byteb in Z2. apply andb_prop in Z2 as [Z2 Z3]. apply Z.leb_le in Z2, Z3.
      pose proof (PSOGX.st_lit_sound (hl_segs L) Ec El (CCA.vis A1 mc Mc) (CCA.vis A1 ml Ml) cells (CC.cp_know c) (CC.cp_nx c) (PSO.v_st t) z KN KT Hag vt_st TS) as Y.
      rewrite (PSOST.va_st _ _ _ (PSOST.view_agree _ _ _ Ec El S8 Hag)), (PSOST.tv_st _ _ _ _ TV), HS in Y.
      pose proof (PSOGX.bv8_eq _ _ Y ltac:(unfold PML.ST_NUMBER; lia) ltac:(lia)) as Y'. unfold PML.ST_NUMBER in Y'. lia. }
  set (ps2 := PSOST.ps_upd ps1 (PML.ps_st ps1) (PML.ps_sst ps1) (PML.ps_nst ps1) (PML.ps_more ps1) (PML.ps_done ps1) buf2 (PML.ps_win ps1)) in *.
  assert (WF2 : PMCUR.wf_c ps2).
  { destruct BUF as ([EQ|EQ] & NN).
    - subst ps2. rewrite EQ. destruct ps1; exact WF.
    - destruct (list_eq_dec Z.eq_dec buf2 (PML.ps_buf ps1)) as [EQ'|NE]; [subst ps2; rewrite EQ'; destruct ps1; exact WF|].
      subst ps2. rewrite EQ. split.
      + apply (PSSA.wf_buf ps1 (PML.ps_bcap ps1) (PML.ps_bptr ps1) [] (proj1 WF)). intros HM HS. exfalso. exact (proj2 (NN NE) HS).
      + exact (PSSC.lvl_same ps1 _ (proj2 WF) eq_refl eq_refl eq_refl eq_refl). }
  assert (CJ : PSOX.CORE I j Ej Ml (PML.ps_win ps2) ps2 0 g1).
  { pose proof (PSOX.c_bb _ _ _ _ _ _ _ _ CO) as (BB1 & BB2). destruct BLKj as (BJ1 & BJ2 & BJ3 & BJ4).
    constructor.
    - exact (PSOST.m_pa _ _ _ _ _ _ MEM).
    - left. split; [rewrite KJ; reflexivity | reflexivity].
    - exact (PSOST.m_sh _ _ _ _ _ _ MEM).
    - exact (PSOX.c_win _ _ _ _ _ _ _ _ CO).
    - split; [|exact BB2]. unfold PML.winlen, PML.buf_need in *. subst ps2. cbn [PSOST.ps_upd PML.ps_buf PML.ps_win PML.ps_more PML.ps_st PML.ps_sst] in *.
      destruct BUF as ([-> | ->] & _); cbn [length] in *; lia.
    - exact (PSOST.m_ec _ _ _ _ _ _ MEM).
    - exact (PSOST.m_ls _ _ _ _ _ _ MEM).
    - exact (PSOX.c_g _ _ _ _ _ _ _ _ CO).
    - intros Hm. exact (PSOX.c_lv _ _ _ _ _ _ _ _ CO Hm).
    - rewrite BJ1, BJ2, BJ3, BJ4. rewrite <- (PSOX.c_blk _ _ _ _ _ _ _ _ CO). reflexivity.
    - intros _ _. exact (PSOX.c_na _ _ _ _ _ _ _ _ CO U0 (proj1 RK)).
    - intros _ _. exact (PSOX.c_wl _ _ _ _ _ _ _ _ CO U0 (proj2 RK)).
    - intros Hu. rewrite U0j in Hu. discriminate Hu. }
  unfold PSOX.XI. pose proof KJ as HK.
  constructor; try (intros Hk; exfalso; rewrite HK in Hk; discriminate Hk); try (intros [Hk|Hk]; exfalso; rewrite HK in Hk; discriminate Hk);
    try (intros pc0 Hk; exfalso; rewrite HK in Hk; discriminate Hk).
  - intros _. exact FLFj.
  - intros _. exists ps2, g1. split; [exact CJ|]. split; [exact WF2|]. split.
    +
      destruct (list_eq_dec Z.eq_dec buf2 (PML.ps_buf ps1)) as [EQ'|NE].
      * subst ps2. rewrite EQ'. pose proof (STOPOK_agV I Mc Ml AGVl ps1 SO) as SO'. destruct ps1; exact SO'.
      * intros X. subst ps2. cbn [PSOST.ps_upd PML.ps_more] in X. rewrite (proj1 (proj2 BUF NE)) in X. discriminate X.
    + intros HQ. exfalso. unfold PSO.isQcut in HQ. rewrite HK in HQ. discriminate HQ.
Qed.
End RWS.

Section DDS.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation E := (PSOI.iE I).
Local Abbreviation M := (PSOI.iM I).     Local Abbreviation model := (PSOI.imodel I). Local Abbreviation ps := (PSOI.ips I).
Local Abbreviation HIok := (PSOI.iHIok I). Local Abbreviation E0 := (PSOI.E0 I).
Local Abbreviation WW := (WW I).            Local Abbreviation Cred := (PSOX.Cred I).
Variables (i : nat) (c : CC.cutpoint) (ps0 : SR.post_spec) (pc : Z) (t : PSO.pv).
Local Abbreviation cells := (SR.ps_cells ps0).
Hypothesis Hci : nth_error G.CPS i = Some c.
Hypothesis Ht : PSO.pview (CC.cp_know c) = Some t.
Hypothesis HDD : dd_leaf i c ps0 pc = true.
Variables (Ec : env) (Rc : bvmap 5 word) (El : env) (Rl : bvmap 5 word) (A1 : list (Z * Z)) (Mc : mem) (mc : Model) (Ml : mem) (ml : Model).
Hypothesis HAt : CCA.AtV (hl_segs L) c Ec Rc A1 Mc mc.
Hypothesis HA : AAMB I i Ec A1 Mc mc.
Hypothesis Hag : env_agree (CC.cp_nx c) Ec El.
Hypothesis HLF : CCA.leaf_factsA (hl_segs L) c ps0 El Rl A1 Mc mc Ml ml.
Hypothesis HXI : PSOX.XI I i Ec A1 Mc mc.

Lemma KN' : know_ok (hl_segs L) El (CCA.vis A1 ml Ml) cells.
Proof. unfold know_ok. apply Forall_forall. intros X HX. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX). Qed.
Lemma KT' : know_ok (hl_segs L) Ec (CCA.vis A1 mc Mc) (CC.cp_know c). Proof. destruct HAt as [_ HK]. exact HK. Qed.

Lemma DSRC : forall mw ps1 g1, PSOX.CORE I i Ec Mc mw ps1 0 g1 -> (PSO.kind_of i = PSO.KSm -> PML.ps_more ps1 = true) -> PSO.view_ok (CC.cp_nx c) (CC.cp_know c) t = true ->
  (PSO.rng_in cells (PSO.v_more t) 1 255 || PSO.rng_in (CC.cp_know c) (PSO.v_more t) 1 255 || PSO.kind_eqb (PSO.kind_of i) PSO.KSm)%bool = true ->
  (2 <= i < PSO.NCUT)%nat -> PML.ps_more ps1 = true.
Proof.
  intros mw ps1 g1 CO HSM VT X Hi. pose proof (PSOST.TVAL I i c Ec Rc A1 Mc mc mw ps1 0 g1 t Hci Hi HAt HA CO Ht) as TV. pose proof (PSOST.tv_more _ _ _ _ TV) as TM.
  apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]|].
  - unfold PSO.rng_in in X. destruct (CX.range3 cells (PSO.v_more t)) as [[lo hi]|] eqn:HR; [|discriminate X]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1, X2.
    pose proof (CX.range3_sound _ _ _ _ _ _ _ KN' HR) as RG. change (bv_unsigned (edenot El (PSO.v_more t))) with (CL5A.uv El (PSO.v_more t)) in RG.
    rewrite (PSOST.va_more _ _ _ (PSOST.view_agree _ _ _ Ec El VT Hag)) in RG.
    pose proof (PSOGX.b2z_of _ _ TM ltac:(lia)) as BZ. destruct (PML.ps_more ps1); [reflexivity|]. cbn in BZ. lia.
  - unfold PSO.rng_in in X. destruct (CX.range3 (CC.cp_know c) (PSO.v_more t)) as [[lo hi]|] eqn:HR; [|discriminate X]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1, X2.
    pose proof (CX.range3_sound _ _ _ _ _ _ _ KT' HR) as RG. pose proof (PSOGX.b2z_of _ _ TM ltac:(unfold CL5A.uv; lia)) as BZ.
    destruct (PML.ps_more ps1); [reflexivity|]. cbn in BZ. unfold CL5A.uv in BZ. lia.
  - apply PSO.kind_eqb_eq in X. exact (HSM X).
Qed.
Lemma vt_st' : PSO.view_ok (CC.cp_nx c) (CC.cp_know c) t = true -> APC.expr_vars_lt (CC.cp_nx c) (PSO.v_st t) = true.
Proof. intros X. unfold PSO.view_ok in X. cbn [forallb] in X. repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end. assumption. Qed.
Lemma STZ : forall mw ps1 g1 z, PSOX.CORE I i Ec Mc mw ps1 0 g1 -> (2 <= i < PSO.NCUT)%nat -> PSO.view_ok (CC.cp_nx c) (CC.cp_know c) t = true ->
  PSO.tst c cells t = Some z -> 0 <= z < 256 -> 0 <= PML.ps_st ps1 < 256 -> PML.ps_st ps1 = z.
Proof.
  intros mw ps1 g1 z CO Hi VT TS R1 R2. pose proof (PSOST.TVAL I i c Ec Rc A1 Mc mc mw ps1 0 g1 t Hci Hi HAt HA CO Ht) as TV.
  pose proof (PSOGX.st_lit_sound (hl_segs L) Ec El (CCA.vis A1 mc Mc) (CCA.vis A1 ml Ml) cells (CC.cp_know c) (CC.cp_nx c) (PSO.v_st t) z KN' KT' Hag (vt_st' VT) TS) as X.
  rewrite (PSOST.va_st _ _ _ (PSOST.view_agree _ _ _ Ec El VT Hag)), (PSOST.tv_st _ _ _ _ TV) in X. exact (PSOGX.bv8_eq _ _ X R2 R1).
Qed.

Lemma DDF : False.
Proof.
  pose proof HDD as X. unfold dd_leaf in X. apply orb_prop in X as [X|X].
  - apply PSO.kind_eqb_eq in X. exact (PSOX.xi_dead _ _ _ _ HXI X).
  - rewrite Ht in X. cbv zeta in X.
    assert (NE : PSO.kind_of i <> PSO.KEntry -> (2 <= i < PSO.NCUT)%nat) by (intros N; exact (ge2_of_kind i c _ Hci eq_refl N)).
    apply orb_prop in X as [X|X].
    +
      apply andb_prop in X as [X XS]. apply andb_prop in X as [X XK]. apply andb_prop in X as [X XM]. apply andb_prop in XM as [XM VT].
      assert (SRC : exists mw ps1 g1, PSOX.CORE I i Ec Mc mw ps1 0 g1 /\ PML.wf_ps ps1 /\ (PSO.kind_of i = PSO.KSm -> PML.ps_more ps1 = true)).
      { apply orb_prop in XK as [XK|XK].
        - destruct (PSOX.xi_loop _ _ _ _ HXI XK) as (ps1 & g1 & CO & WF & _). exists (PML.ps_win ps1), ps1, g1. split; [exact CO|]. split; [exact (proj1 WF)|].
          intros HK. rewrite HK in XK. discriminate XK.
        - apply PSO.kind_eqb_eq in XK. exists (PML.ps_win ps), ps, (PSOI.ig I). split; [exact (PSOX.xi_sm _ _ _ _ HXI XK)|]. split; [exact (proj1 (PSOI.iHWF I)) | intros _; exact (PSOI.iHMORE I)]. }
      destruct SRC as (mw & ps1 & g1 & CO & WF & HSM).
      assert (Hi : (2 <= i < PSO.NCUT)%nat).
      { apply NE. intros HE. apply orb_prop in XK as [XK|XK]; rewrite HE in XK; discriminate XK. }
      pose proof (DSRC mw ps1 g1 CO HSM VT XM Hi) as HM. pose proof (PSSA.wf_more ps1 WF HM) as (_ & HH & _).
      assert (HR : 1 <= PML.ps_st ps1 <= 28) by (unfold PML.handled in HH; lia).
      apply orb_prop in XS as [XS|XS].
      * destruct (PSO.tst c cells t) as [z|] eqn:TS; [|discriminate XS]. apply andb_prop in XS as [XS XB]. apply negb_true_iff in XS.
        unfold byteb in XB. apply andb_prop in XB as [XB1 XB2]. apply Z.leb_le in XB1, XB2.
        pose proof (STZ mw ps1 g1 z CO Hi VT TS ltac:(lia) ltac:(lia)) as S1. rewrite S1 in HH. rewrite (handledb_of _ HH) in XS. discriminate XS.
      * apply andb_prop in XS as [XR XF]. pose proof (PSOST.TVAL I i c Ec Rc A1 Mc mc mw ps1 0 g1 t Hci Hi HAt HA CO Ht) as TV.
        unfold PSO.rng_in in XR. destruct (CX.range3 cells (PSO.v_st t)) as [[lo hi]|] eqn:HRg; [|discriminate XR]. apply andb_prop in XR as [X1 X2]. apply Z.leb_le in X1, X2.
        pose proof (CX.range3_sound _ _ _ _ _ _ _ KN' HRg) as RG. change (bv_unsigned (edenot El (PSO.v_st t))) with (CL5A.uv El (PSO.v_st t)) in RG.
        pose proof (PSOST.tv_st _ _ _ _ TV) as TS. rewrite <- (PSOST.va_st _ _ _ (PSOST.view_agree _ _ _ Ec El VT Hag)) in TS.
        pose proof (PSOGX.bv8_eq _ _ TS ltac:(lia) ltac:(lia)) as SV.
        apply CC.has_cell_In in XF. pose proof (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ XF) as K. cbn [kentry_ok edenot] in K.
        rewrite u_sltu64, u_add64, u_lit64a, u_lit64a in K. fold (CL5A.uv El (PSO.v_st t)) in K. rewrite SV in K.
        assert (M27 : 27 mod 2 ^ 64 = 27) by reflexivity. rewrite M27 in K.
        assert (MV : (PML.ps_st ps1 + (-1) mod 2 ^ 64) mod 2 ^ 64 = PML.ps_st ps1 - 1).
        { rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
        rewrite MV in K. destruct (27 <? PML.ps_st ps1 - 1) eqn:LT; [apply Z.ltb_lt in LT; lia | lia].
    +
      apply andb_prop in X as [X XT]. apply andb_prop in X as [X XM]. apply andb_prop in XM as [XM VT]. apply andb_prop in X as [XK _]. apply PSO.kind_eqb_eq in XK.
      assert (Hi : (2 <= i < PSO.NCUT)%nat) by (apply NE; rewrite XK; intros Y; discriminate Y).
      destruct (PSOX.xi_loop _ _ _ _ HXI ltac:(rewrite XK; reflexivity)) as (ps1 & g1 & CO & WF & _ & QO).
      pose proof (DSRC _ ps1 g1 CO ltac:(rewrite XK; intros Y; discriminate Y) VT XM Hi) as HM. pose proof (PSSA.wf_more ps1 (proj1 WF) HM) as (_ & HH & _).
      assert (HR : 1 <= PML.ps_st ps1 <= 28) by (unfold PML.handled in HH; lia).
      destruct (PSO.tst c cells t) as [z|] eqn:TS; [|discriminate XT]. apply andb_prop in XT as [XT XW]. apply andb_prop in XT as [XQ XB]. apply negb_true_iff in XQ.
      unfold byteb in XB. apply andb_prop in XB as [XB1 XB2]. apply Z.leb_le in XB1, XB2.
      pose proof (STZ _ ps1 g1 z CO Hi VT TS ltac:(lia) ltac:(lia)) as S1.
      destruct (QO ltac:(unfold PSO.isQcut; rewrite XK; reflexivity) HM) as [Q1|(Q1 & Q2)].
      * rewrite S1 in Q1. unfold PSO.inb in XQ. assert (Y : existsb (Z.eqb z) QSTATES = true) by (apply existsb_exists; exists z; split; [exact Q1 | apply Z.eqb_refl]).
        rewrite Y in XQ. discriminate XQ.
      *
        rewrite S1 in Q1. unfold PML.ST_NUMBER in Q1. rewrite Q1 in XW. cbn [Z.eqb negb orb] in XW. apply andb_prop in XW as [XW1 XW2]. apply expr_eqb_eq in XW1.
        pose proof (PSOST.TVAL I i c Ec Rc A1 Mc mc _ ps1 0 g1 t Hci Hi HAt HA CO Ht) as TV. pose proof (PSOST.tv_wptr _ _ _ _ TV) as TW.
        pose proof (PSOX.c_mw _ _ _ _ _ _ _ _ CO) as MW. destruct MW as [(_ & MW)|[(CK & _)|(CK & _)]]; [| rewrite XK in CK; discriminate CK | rewrite XK in CK; discriminate CK]. try rewrite MW in TW.
        rewrite XW1, PSOGX.uv_CURH in TW.
        assert (UL : CL5A.uv Ec WLEN = PSOI.wlen I /\ CL5A.uv Ec WP0 = PSOI.wp0 I).
        { pose proof HA as (_ & _ & _ & HE & _). pose_U I. unfold CL5A.uv, WLEN, WP0, WLENV, WP0V. cbn [edenot].
          rewrite <- (proj1 HE 32%nat) by (unfold GT.NF, Cut_psome_casan_T.NF; lia). rewrite <- (proj1 HE 36%nat) by (unfold GT.NF, Cut_psome_casan_T.NF; lia). split; [exact U32 | exact U36]. }
        destruct UL as (UL & UP). rewrite UL, UP in TW.
        unfold PSO.lo_ge in XW2. destruct (CX.range3 (CC.cp_know c) (EVar JV)) as [[lo hi]|] eqn:HRj; [|discriminate XW2]. apply Z.leb_le in XW2.
        pose proof (CX.range3_sound _ _ _ _ _ _ _ KT' HRj) as RJ. change (bv_unsigned (edenot Ec (EVar JV))) with (CL5A.uv Ec (EVar JV)) in RJ.
        pose proof (UVR Ec (EVar JV)) as RJ2.
        pose proof (PSOX.c_win _ _ _ _ _ _ _ _ CO) as WN. unfold PSOX.WIN in WN. pose proof (WINF I) as (WI0 & WI1 & WI2 & _ & _ & _ & WIC & _).
        unfold PMSA.win_exhausted in Q2. destruct (PML.ps_win ps) as [[p0 e0]|] eqn:Hw.
        -- destruct WN as (p1 & W1 & W2). rewrite W1 in Q2, TW. subst p1. cbn [PSOI.wlo] in TW. pose proof (PSOI.WSOME I p0 e0 Hw) as (WP0E & WE0E & _).
           rewrite (Z.mod_small e0) in TW by lia.
           destruct (Z_le_gt_dec (CL5A.uv Ec (EVar JV)) (PSOI.wlen I + PSOI.wp0 I)) as [LE|GT].
           ++ rewrite Z.mod_small in TW by lia. lia.
           ++ rewrite <- (Z.mod_add _ 1 (2 ^ 64)) in TW by lia. rewrite Z.mod_small in TW by lia. lia.
        -- rewrite WN in Q2. pose proof (PSOI.WNONE I Hw) as (_ & _ & WLN & _).
           pose proof (PSOX.c_wl _ _ _ _ _ _ _ _ CO (PSOGX.LOOPU0 i (proj2 Hi) ltac:(rewrite XK; reflexivity)) ltac:(rewrite XK; reflexivity)) as W1. lia.
Qed.
End DDS.

Lemma L_DEAD {SCFG_P : ScfgP} (I : PSOI.inst) : forall i c k ps0 pc, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.dead_chk i ps0 pc = true ->
  CCA.leaf_ok (hl_segs (PSOI.iL I)) G.CPS (AMBX I) (PSOI.iK I) PMSA.fp_ok i c ps0.
Proof.
  intros i c k ps0 pc IL DC. pose proof (CH2.leaves_all_sound _ _ _ CS_all _ _ _ _ _ IL) as X. cbn [cs_chk] in X. rewrite DC in X.
  assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
  intros fx' E' R A M model E'' R' M1 model1 HAt [HA HXI] HFP Hag HLF HIH. exfalso.
  destruct (PSO.pview (CC.cp_know c)) as [t|] eqn:Ht.
  - exact (DDF I i c ps0 pc t Hci Ht X E' R E'' R' A M model M1 model1 HAt HA Hag HLF HXI).
  - unfold dd_leaf in X. rewrite Ht in X. rewrite orb_false_r in X. apply PSO.kind_eqb_eq in X. exact (PSOX.xi_dead _ _ _ _ HXI X).
Qed.

Lemma L_CSL {SCFG_P : ScfgP} (I : PSOI.inst) : forall i c k ps0 pc, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.dead_chk i ps0 pc = false ->
  pc <> RET -> pc <> SETSH -> pc <> SM4 -> PSO.inb pc PSO.CALLEES = false ->
  CCA.leaf_ok (hl_segs (PSOI.iL I)) G.CPS (AMBX I) (PSOI.iK I) PMSA.fp_ok i c ps0.
Proof.
  intros i c k ps0 pc IL DC N1 N2 N3 N4.
  assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
  pose proof (PSOL.LEAFOK_all i c k ps0 _ IL) as X. cbn [PSO.leaf_chk] in X. rewrite DC in X.
  rewrite (proj2 (Z.eqb_neq pc RET) N1), (proj2 (Z.eqb_neq pc SETSH) N2), (proj2 (Z.eqb_neq pc SM4) N3), N4 in X.
  destruct (CSLR.find_row PSO.ROWS i (SR.ps_pc ps0)) as [rw|] eqn:Hr; [|discriminate X].
  pose proof (CH2.leaves_all_sound _ _ _ CS_all _ _ _ _ _ IL) as Y. cbn [cs_chk] in Y. rewrite DC in Y.
  rewrite (proj2 (Z.eqb_neq pc RET) N1), (proj2 (Z.eqb_neq pc SETSH) N2), (proj2 (Z.eqb_neq pc SM4) N3), N4 in Y. cbn [orb] in Y. rewrite Hr in Y.
  destruct (CSLR.find_row_In _ _ _ _ Hr) as (Hin & Hri & Hrpc).
  pose proof Y as Y'. unfold rw_leaf in Y'.
  destruct (PSO.pview (CC.cp_know c)) as [t|] eqn:Ht; [|discriminate Y']. destruct (PSO.pview (SR.ps_cells ps0)) as [l|] eqn:Hl; [|discriminate Y'].
  destruct (nth_error G.CPS (CSLR.r_j rw)) as [cj|] eqn:Hcj; [|discriminate Y'].
  pose proof (RWB i c ps0 rw t l cj Ht Hl Hcj Y) as RW.

  pose proof X as XR. unfold CSLR.row_chk in XR. rewrite Hcj in XR.
  apply andb_prop in XR as [XR _]. apply andb_prop in XR as [XR XG]. unfold CHA.goto_amb_chk in XG. apply andb_prop in XG as [XG _]. apply andb_prop in XG as [_ HBL].
  pose proof (w_loop _ _ _ _ _ _ RW) as WLP.
  pose_facts I. pose_U I.
  destruct (PML.ps_win (PSOI.ips I)) as [[p0 e0]|] eqn:Hw.
  - pose_win I Hw.
    assert (RT : CSLR.r_tab rw = false) by (pose proof (w_tab _ _ _ _ _ _ RW) as Z; apply negb_true_iff in Z; exact Z).
    unfold AMBX.
    refine (CSLR.rows_leaf (PSOI.iL I) (PSOI.iar I) (PSOI.iC I) (PSOI.iHI I) (PSOI.iHIok I) (LYI I) (LYR I) (LYB I) (LYN I) GT.NF (PSOI.E0 I) (PSOI.iM I) (PSOI.imodel I) (PSOI.iA I)
              (PSOI.iLBo I) (PSOI.iFF I) (PSOI.iLK I) (PSOI.isp I) G.HDECL (WW I) (Wo I) G.BLS PSO.FFS (PSOX.Cred I) 6 (STKF I) SCRP NF32 U2 (WINC I) (WOKo I) (WRS_OK I)
              G.CPS (PSOI.iK I) PMSA.fp_ok (PSOX.XI I) (CC.cp_F c) SBz JV WP0 WE CH CHG (PSOI.wp0 I) (PSOI.wlen I) (PSOI.ich I) (PSOI.chg I) 32768 0 0 SBz _ _ _ _
              i c ps0 rw _ ltac:(rewrite LS; exact (CSLR.sites_ok_In _ _ rw PSOA.sites Hin)) _ _).
    + vm_compute. reflexivity.
    + unfold WE, WP0, WLEN, CH, CHG, WLENV, WP0V, CHV, CHGV. cbn [edenot]. rewrite u_add64, U36, U32, U34, U35. rewrite Z.mod_small by (unfold PSOI.wp0, PSOI.wlen, PSOI.we0 in *; lia).
      repeat split; reflexivity.
    + rewrite CHGE. unfold PSOI.wp0, PSOI.wlen, PSOI.we0 in *.
      split; [exact KC8|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
    + unfold SBz. repeat split; try lia; reflexivity.
    + rewrite <- (rchk_tab GT.NF G.HDECL G.CPS G.BLS PSO.FFS (CC.cp_F c) SBz JV WP0 WE 32768 (CSLR.KZB SBz CH CHG) 0 0 PSO.KZT _ i c ps0 rw RT). exact X.
    +   intros E1 E' R1 R' A1 M1 m1 M' m' HAt HA HXI Hag HLF. try rewrite Hri in *.
      exact (RW_XI I i c ps0 rw t l cj Hci Ht Hl Hcj Y HBL E1 R1 E' R' A1 M1 m1 M' m' HAt HA Hag HLF HXI).
    +   intros E1 E' R' M1 M' cr1 Hag0 Hag HLF HC. try rewrite Hri in *.
      pose proof HBL as HB. apply CH2.blocks_eqb_eq in HB.
      pose proof (CH2.den_bsubst GT.NF (CSLR.r_sid rw) E' (nth (CSLR.r_j rw) G.BLS [])) as D. rewrite HB in D.
      assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
      assert (Hj : (CSLR.r_j rw < PSO.NCUT)%nat) by (apply Nat.ltb_lt; exact (w_jn _ _ _ _ _ _ RW)).
      rewrite (bls_i i Hi), (bls_i (CSLR.r_j rw) Hj) in D.
      destruct (BLKAG i c E1 E' Hci Hag) as (B1 & B2 & B3 & B4).
      unfold PSOX.Cred in *. unfold PSOX.bcapI, PSOX.scapI in *. unfold CL5A.uv in *.
      destruct (PSO.blk0 i) as [b0 c0]; destruct (PSO.blk1 i) as [b1 c1]; destruct (PSO.blk0 (CSLR.r_j rw)) as [b0' c0']; destruct (PSO.blk1 (CSLR.r_j rw)) as [b1' c1'].
      unfold CH2.den in D. cbn [map fst snd] in D, B2, B4 |- *. injection D as D1 D2 D3 D4. rewrite <- D2, <- D4, B2, B4. exact HC.
  -
    intros fx' E1 R1 A1 M1 m1 E' R' M' m' HAt [HA HXI] HFP Hag HLF HIH. exfalso.
    destruct (PSOX.xi_loop _ _ _ _ HXI WLP) as (ps1 & g1 & CO & _).
    assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
    assert (RK : PSOX.wlk (PSO.kind_of i) = true) by (destruct (PSO.kind_of i); try discriminate WLP; reflexivity).
    pose proof (PSOX.c_wl _ _ _ _ _ _ _ _ CO (PSOGX.LOOPU0 i Hi WLP) RK) as W1. pose proof (PSOI.WNONE I Hw) as (_ & _ & WLN & _). lia.
Qed.

End PSOCS.
