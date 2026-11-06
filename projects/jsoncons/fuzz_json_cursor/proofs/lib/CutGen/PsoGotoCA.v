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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_casan_T Cut_psome_casan_D Cut_psome_casan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsoInstCA PsoSemA PsoSemCA PsoKnCA PsoBaseCA ParseSomeChkCA PsoLeafCA PsoAuxCA PsoXiCA PsoLinkCA PsoFrmCA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.

Definition ec0 (nx : nat) (cells : list kentry) (t : PSO.pv) : bool := match PSO.v_ec t with Some e => (PSO.rng_is cells e 0 && APC.expr_vars_lt nx e)%bool | None => false end.
Definition more0 (cells : list kentry) (l : PSO.pv) : bool := match PSO.v_more l with ELit 0 => true | e => PSO.rng_is cells e 0 end.
Definition pin1728 (cells : list kentry) : bool := match PSO.st0pin cells with Some z => PSO.inb z [17; 28] | None => false end.
Definition code0k (k : PSO.kind) : bool := match k with PSO.KRetx => false | _ => true end.
Definition byteb (z : Z) : bool := (Z.leb 0 z && Z.leb z 255)%bool.

Definition fd_eqb (a b : PSO.fd) : bool :=
  match a, b with PSO.Same, PSO.Same | PSO.Other, PSO.Other => true | PSO.Lit x, PSO.Lit y => Z.eqb x y | PSO.Var x, PSO.Var y => Nat.eqb x y | _, _ => false end.
Lemma fd_eqb_eq : forall a b, fd_eqb a b = true -> a = b.
Proof. intros [|x|x|] [|y|y|] H; cbn in H; try discriminate H; try reflexivity; [apply Z.eqb_eq in H | apply Nat.eqb_eq in H]; subst; reflexivity. Qed.
Definition oz_eqb (a b : option Z) : bool := match a, b with Some x, Some y => Z.eqb x y | None, None => true | _, _ => false end.
Lemma oz_eqb_eq : forall a b, oz_eqb a b = true -> a = b.
Proof. intros [x|] [y|] H; cbn in H; try discriminate H; try reflexivity. apply Z.eqb_eq in H. subst. reflexivity. Qed.
Definition ob_eqb (a b : option bool) : bool := match a, b with Some x, Some y => Bool.eqb x y | None, None => true | _, _ => false end.
Lemma ob_eqb_eq : forall a b, ob_eqb a b = true -> a = b.
Proof. intros [x|] [y|] H; cbn in H; try discriminate H; try reflexivity. apply Bool.eqb_prop in H. subst. reflexivity. Qed.

Definition gcx (i : nat) (c : CC.cutpoint) (cells : list kentry) (t l : PSO.pv) (d : PSO.delta) (g : PSO.gcase) : bool :=
  match g with
  | PSO.GSame => ob_eqb (PSO.morek (PSO.d_more d)) (Some true) && fd_eqb (PSO.d_st d) PSO.Same && fd_eqb (PSO.d_more d) PSO.Same && fd_eqb (PSO.d_sst d) PSO.Same
                 && fd_eqb (PSO.d_nst d) PSO.Same && fd_eqb (PSO.d_done d) PSO.Same
  | PSO.GStop => ob_eqb (PSO.morek (PSO.d_more d)) (Some false) && negb (fd_eqb (PSO.d_st d) PSO.Other)
  | PSO.GAccept => ob_eqb (PSO.morek (PSO.d_more d)) (Some false) && fd_eqb (PSO.d_st d) (PSO.Lit 29) && oz_eqb (PSO.tst c cells t) (Some 2) && fd_eqb (PSO.d_done d) (PSO.Lit 1)
  | PSO.GStep s1 s2 => ob_eqb (PSO.morek (PSO.d_more d)) (Some true) && PSO.more1 c cells t l && oz_eqb (PSO.tst c cells t) (Some s1)
                       && PSO.step_ok (PSO.lo_ge cells (EVar LEVELV) 1) s1 s2 && ((fd_eqb (PSO.d_st d) PSO.Same && Z.eqb s2 s1) || fd_eqb (PSO.d_st d) (PSO.Lit s2))
  | PSO.GPop v => ob_eqb (PSO.morek (PSO.d_more d)) (Some true) && fd_eqb (PSO.d_st d) (PSO.Var v) && PSO.kind_eqb (PSO.kind_of i) PSO.KPop
                  && Nat.eqb v (CC.cp_nx c - APC.NCS - 2) && PSO.more1 c cells t l && fd_eqb (PSO.d_sst d) PSO.Same && fd_eqb (PSO.d_nst d) PSO.Same
  | PSO.GPush s1 s2 => ob_eqb (PSO.morek (PSO.d_more d)) (Some true) && fd_eqb (PSO.d_st d) (PSO.Lit s2) && PSO.more1 c cells t l && PSO.kind_eqb (PSO.kind_of i) PSO.KVpush
                       && oz_eqb (PSO.tst c cells t) (Some s1)
  end%bool.
Definition rxok2 (i : nat) (nx : nat) (cells : list kentry) (t l : PSO.pv) : bool :=
  (more0 cells l || PSO.rng_is cells (APC.esub WE (PSO.v_wptr l)) 0 || PSO.has cells (KRange (EAlu Instr.ALU_SLTU (PSO.v_wptr l) (PSO.v_wend l)) 0 0)
   || match PSO.ecvar t with Some v => (PSO.rng_in cells (EVar v) 1 (2 ^ 32 - 1) && Nat.ltb v nx)%bool | None => false end || PSO.kind_eqb (PSO.kind_of i) PSO.KSetec)%bool.
Definition gx_leaf (i : nat) (c : CC.cutpoint) (ps : SR.post_spec) (j : nat) (s : CC.subst) : bool :=
  let cells := SR.ps_cells ps in
  match PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some t, Some l =>
      let d := PSO.mkdelta cells t l in
      match PSO.gclass i c cells t l d with
      | Some g =>
          (
           gcx i c cells t l d g &&

           match g with
           | PSO.GPush s1 s2 => ((Z.eqb s2 3 && PSO.expectb s1 && Z.eqb (PSOX.vpx i) s1) || (Z.eqb s2 28 && Z.eqb s1 5 && Z.eqb (PSOX.vpx i) 5)) && byteb s1
           | PSO.GStep s1 s2 => byteb s1 && byteb s2
           | _ => true end

           && implb (PSO.is_ptk (PSO.kind_of i) && code0k (PSO.kind_of j)) (ec0 (CC.cp_nx c) cells t)

           && implb (PSO.kind_eqb (PSO.kind_of i) PSO.KSetec && match g with PSO.GSame => true | _ => false end) (more0 cells l)

           && implb (PSO.kind_eqb (PSO.kind_of i) PSO.KSm && PSO.kind_eqb (PSO.kind_of j) PSO.KSe) (PSO.ne_acc cells)
           && implb (PSO.kind_eqb (PSO.kind_of i) PSO.KSm && PSO.kind_eqb (PSO.kind_of j) PSO.KRetx && match g with PSO.GSame => true | _ => false end) (PSO.lo_ge cells (EVar JV) 1)

           && implb (PSO.u0 i && PSO.kind_eqb (PSO.kind_of j) PSO.KRetx && (PSO.is_ptk (PSO.kind_of i) || PSO.kind_eqb (PSO.kind_of i) PSO.KPop)) (pin1728 cells)

           && implb (Z.eqb (PSO.d_adv d) 1) (expr_eqb (PSO.v_wptr t) PSO.CURH)

           && implb (PSO.has_bufbyte (CC.cp_F c)) match g with PSO.GStop | PSO.GAccept | PSO.GPush _ _ => true | _ => false end

           && match g with
              | PSO.GStep _ _ => (PSO.is_same (PSO.d_more d) && PSO.rng_in cells (PSO.v_more l) 1 255) || PSO.rng_in (CC.cp_know c) (PSO.v_more t) 1 255
                                 || PSO.kind_eqb (PSO.kind_of i) PSO.KErrh
              | PSO.GAccept => PSO.rng_in (CC.cp_know c) (PSO.v_more t) 1 255
              | _ => true end

           && match g with PSO.GStep _ 7 => expr_eqb (PSO.v_level t) (EVar LEVELV) && PSO.rng_in cells (EVar LEVELV) 1 (2 ^ 32 - 1) | _ => true end

           && implb (match g with PSO.GStop => true | _ => false end && PSO.kind_eqb (PSO.kind_of j) PSO.KRetx)
                    (PSO.kind_eqb (PSO.kind_of i) PSO.KSetec || (PSO.kind_eqb (PSO.kind_of i) PSO.KSm && match PSO.st0pin cells with Some 29 => true | _ => false end))

           && (PSO.has cells (KWord (SA PE 213) 1 (ELit 1)) || negb (existsb (PSO.region_eqb (PE, 200, ELit 16)) (CC.cp_F c)))

           && implb (PSO.curk (PSO.kind_of i)) (expr_eqb (PSO.v_wptr l) (nth 10 (CC.cp_regs c) (ELit 0)))

           && expr_eqb (CC.slook s 60) FLE

           && implb ((PSO.kind_eqb (PSO.kind_of j) PSO.KHQ || PSO.kind_eqb (PSO.kind_of j) PSO.KLQ) && match g with PSO.GSame => true | _ => false end) (negb (Z.eqb (PSO.d_adv d) 1))

           && implb (PSO.u0 i) (PSO.kind_eqb (PSO.kind_of j) PSO.KRetx || PSO.kind_eqb (PSO.kind_of j) PSO.KSe || PSO.kind_eqb (PSO.kind_of i) PSO.KSm)

           && implb (PSO.is_ptk (PSO.kind_of i) && (PSO.kind_eqb (PSO.kind_of j) PSO.KLQ || PSO.kind_eqb (PSO.kind_of j) PSO.KLZ)) (PSO.kind_eqb (PSO.kind_of i) (PSO.KPt PNUMBER))
           && implb (PSO.u0 i && PSO.is_ptk (PSO.kind_of i)) (PSO.kind_eqb (PSO.kind_of i) (PSO.KPt ENDINT) || PSO.kind_eqb (PSO.kind_of i) (PSO.KPt ENDFRAC))

           && implb (match g with PSO.GSame => true | _ => false end) (negb (PSO.kind_eqb (PSO.kind_of i) PSO.KPop || PSO.kind_eqb (PSO.kind_of i) PSO.KVpush))

           && implb (PSO.u0 i && PSO.kind_eqb (PSO.kind_of j) PSO.KRetx)
                    (PSO.kind_eqb (PSO.kind_of i) PSO.KSm || PSO.kind_eqb (PSO.kind_of i) PSO.KSetec || PSO.is_ptk (PSO.kind_of i) || PSO.kind_eqb (PSO.kind_of i) PSO.KPop)

           && implb (PSO.u0 i && PSO.kind_eqb (PSO.kind_of j) PSO.KSe) (PSO.kind_eqb (PSO.kind_of i) PSO.KSm)
           && implb (match g with PSO.GAccept => true | _ => false end) (PSO.kind_eqb (PSO.kind_of i) PSO.KH || PSO.kind_eqb (PSO.kind_of i) PSO.KHQ || PSO.kind_eqb (PSO.kind_of i) PSO.KSm)
           && implb (match g with PSO.GStep _ _ => true | _ => false end) (negb (PSO.kind_eqb (PSO.kind_of i) PSO.KPop || PSO.kind_eqb (PSO.kind_of i) PSO.KVpush))

           && implb (PSO.kind_eqb (PSO.kind_of j) PSO.KRetx) (rxok2 i (CC.cp_nx c) cells t l)

           && negb (PSO.kind_eqb (PSO.kind_of i) PSO.KPushb)

           && match g with PSO.GStep s1 s2 => (negb (PSSC.icsb s2) || PSSC.icsb s1 || Z.eqb s2 7) | _ => true end

           && implb (PSO.kind_eqb (PSO.kind_of i) PSO.KVis)
                    (match g, PSO.tst c cells t, PSO.d_st d with
                     | PSO.GStop, Some s1, PSO.Lit s2 => byteb s1 && byteb s2 &&
                         (negb (Z.eqb s2 7) || (expr_eqb (PSO.v_level t) (EVar LEVELV) && PSO.rng_in cells (EVar LEVELV) 1 (2 ^ 32 - 1)))
                     | _, _, _ => false end)
          )%bool
      | None => false
      end
  | _, _ => false
  end.
Definition gx_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TGoto j s => (PSO.kind_eqb (PSO.kind_of i) PSO.KDead || gx_leaf i c ps j s)%bool | CC.TOther _ => true end.
Lemma GX_all : CH2.leaves_all G.CPS G.TAGS gx_chk = true. Proof. vmc_refl. Qed.
Lemma GX : forall i c k ps0 j s, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> PSO.kind_of i <> PSO.KDead -> gx_leaf i c ps0 j s = true.
Proof.
  intros i c k ps0 j s IL Hnd. pose proof (CH2.leaves_all_sound _ _ _ GX_all _ _ _ _ _ IL) as X. cbn [gx_chk] in X.
  apply orb_prop in X as [X|X]; [apply PSO.kind_eqb_eq in X; contradiction | exact X].
Qed.

Module PSOG.
Section Gx.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation sp := (PSOI.isp I).
Local Abbreviation kx := (PSOI.ikx I).   Local Abbreviation bx := (PSOI.ibx I).
Let E0 := PSOI.E0 I.
Let Cred := PSOX.Cred I.

Lemma GBLK : forall i c k ps0 j s E', CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> (j < PSO.NCUT)%nat ->
  let E'' := CC.env_over GT.NF s E' in
  PSOX.bptrI j E'' = PSOX.bptrI i E' /\ PSOX.bcapI j E'' = PSOX.bcapI i E' /\ PSOX.sbI j E'' = PSOX.sbI i E' /\ PSOX.scapI j E'' = PSOX.scapI i E'.
Proof.
  intros i c k ps0 j s E' IL Hj. cbv zeta.
  assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
  assert (Hi : (i < PSO.NCUT)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hci; discriminate).
  pose proof (CH2.leaves_all_sound _ _ _ PSOA.heap_ok _ _ _ _ _ IL) as X. cbn [CHA.leaf_chkA] in X. unfold CHA.goto_amb_chk in X.
  apply andb_prop in X as [X _]. apply andb_prop in X as [_ X]. apply CH2.blocks_eqb_eq in X.
  pose proof (CH2.den_bsubst GT.NF s E' (nth j G.BLS [])) as D. rewrite X in D.
  rewrite (bls_i i Hi), (bls_i j Hj) in D.
  unfold PSOX.bptrI, PSOX.bcapI, PSOX.sbI, PSOX.scapI, CL5A.uv. destruct (PSO.blk0 i) as [b0 c0]; destruct (PSO.blk1 i) as [b1 c1]; destruct (PSO.blk0 j) as [b0' c0']; destruct (PSO.blk1 j) as [b1' c1'].
  unfold CH2.den in D. cbn [map fst snd] in D |- *. injection D as D1 D2 D3 D4. rewrite D1, D2, D3, D4. repeat split; reflexivity.
Qed.

Lemma G_CRED : forall i c k ps0 j s, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> (j < PSO.NCUT)%nat ->
  forall E1 E' R' M1 M' cr1, env_agree GT.NF E0 E1 -> env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps0 E' R' M1 M' -> Cred i E1 cr1 -> Cred j (CC.env_over GT.NF s E') cr1.
Proof.
  intros i c k ps0 j s IL Hj E1 E' R' M1 M' cr1 Hag0 Hag HLF HC.
  assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
  destruct (GBLK i c k ps0 j s E' IL Hj) as (G1 & G2 & G3 & G4). destruct (BLKAG i c E1 E' Hci Hag) as (A1' & A2 & A3 & A4).
  unfold Cred, PSOX.Cred in *. rewrite G2, G4, A2, A4. exact HC.
Qed.

Lemma GJ : forall i c k ps0 j s, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TGoto j s) -> (j < PSO.NCUT)%nat.
Proof.
  intros i c k ps0 j s IL. pose proof (PSOL.LEAFOK_all i c k ps0 _ IL) as X. cbn [PSO.leaf_chk] in X.
  apply andb_prop in X as [X _]. apply Nat.ltb_lt in X. exact X.
Qed.
End Gx.
End PSOG.
