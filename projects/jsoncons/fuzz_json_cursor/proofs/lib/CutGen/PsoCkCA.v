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
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit CutHeap2 CutL5 CutAutoX CutCertA CutHeapA CutAutoXA CutL5A CutBridgeA CutRtCpsA CutRtA CutRtC CutRtD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibStaticsA PmCurDefs.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA PtKitB.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Cut_psome_casan_T Cut_psome_casan_D Cut_psome_casan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import PsKitA PsoInstCA PsoSemA PsoSemCA PsoKnCA ParseSomeChkCA PsoBaseCA PsoAuxCA PsoXiCA PsoLinkCA PsoFrmCA PsoExitCA PsoStCA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module G := PSO.G.
Module GT := PSO.GT.
Import PSOC.
Abbreviation RSEGS := Pm8PlanKit.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation IC := PMLA.C_casan.

Module PSOCK.

Lemma bv8_eq : forall a b, Z_to_bv 8 a = Z_to_bv 8 b -> 0 <= a < 256 -> 0 <= b < 256 -> a = b.
Proof.
  intros a b H Ra Rb. assert (X : bv_unsigned (Z_to_bv 8 a) = bv_unsigned (Z_to_bv 8 b)) by (rewrite H; reflexivity).
  rewrite !Z_to_bv_unsigned in X. unfold bv_wrap in X. change (bv_modulus 8) with 256 in X. rewrite !Z.mod_small in X by lia. exact X.
Qed.
Lemma bv8_mod : forall a, Z_to_bv 8 (a mod 2 ^ 64) = Z_to_bv 8 a.
Proof.
  intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod_divide; [reflexivity | exists (2 ^ 56); reflexivity].
Qed.
Lemma uv_lit_bv8 : forall Ex z, Z_to_bv 8 (CL5A.uv Ex (ELit z)) = Z_to_bv 8 z.
Proof. intros Ex z. unfold CL5A.uv. cbn [edenot]. rewrite u_lit64a. apply bv8_mod. Qed.
Lemma b2z_rng : forall b, 0 <= PML.b2z b < 256. Proof. intros [|]; cbn; lia. Qed.
Lemma pin_sound : forall segs Ex Ey Mx My cells know nx v z, know_ok segs Ey My cells -> know_ok segs Ex Mx know -> env_agree nx Ex Ey -> (v < nx)%nat ->
  PSO.pin (cells ++ know) v = Some z -> CL5A.uv Ey (EVar v) = z.
Proof.
  intros segs Ex Ey Mx My cells know nx v z HK1 HK2 Hag Hv H. unfold PSO.pin in H.
  destruct (find _ (cells ++ know)) as [X|] eqn:Hf; [|discriminate H].
  apply find_some in Hf as [Hin Hb]. destruct X as [| | | | | [ | v' | | | | | | ] lo hi | | | |]; try discriminate Hb.
  apply andb_prop in Hb as [Hb1 Hb2]. apply Nat.eqb_eq in Hb1. apply Z.eqb_eq in Hb2. subst v' hi. injection H as <-.
  apply in_app_or in Hin as [Hin|Hin].
  - unfold know_ok in HK1. rewrite Forall_forall in HK1. pose proof (HK1 _ Hin) as K. cbn [kentry_ok] in K. unfold CL5A.uv. lia.
  - unfold know_ok in HK2. rewrite Forall_forall in HK2. pose proof (HK2 _ Hin) as K. cbn [kentry_ok] in K.
    unfold CL5A.uv. cbn [edenot] in K |- *. rewrite <- (proj1 Hag v Hv). lia.
Qed.
Lemma st_lit_sound : forall segs Ex Ey Mx My cells know nx e z, know_ok segs Ey My cells -> know_ok segs Ex Mx know -> env_agree nx Ex Ey -> APC.expr_vars_lt nx e = true ->
  PSO.st_lit (cells ++ know) e = Some z -> Z_to_bv 8 (CL5A.uv Ey e) = Z_to_bv 8 z.
Proof.
  intros segs Ex Ey Mx My cells know nx e z HK1 HK2 Hag Hv H.
  destruct e as [z0|v|op a b|op a b|op a b|op a b|sx lo n a|sx kk ii n]; cbn [PSO.st_lit] in H; try discriminate H.
  - injection H as <-. apply uv_lit_bv8.
  - cbn [APC.expr_vars_lt] in Hv. apply Nat.ltb_lt in Hv. rewrite (pin_sound _ _ _ _ _ _ _ _ _ _ HK1 HK2 Hag Hv H). reflexivity.
  - destruct op; try discriminate H. destruct a as [|v| | | | | |]; try discriminate H. destruct b as [kk| | | | | | |]; try discriminate H.
    destruct (PSO.pin (cells ++ know) v) as [z'|] eqn:Hp; [|discriminate H]. injection H as <-.
    cbn [APC.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. apply Nat.ltb_lt in Hv.
    pose proof (pin_sound _ _ _ _ _ _ _ _ _ _ HK1 HK2 Hag Hv Hp) as PV. unfold CL5A.uv in PV |- *. cbn [edenot] in PV |- *.
    rewrite u_add64, PV, u_lit64a. rewrite Zplus_mod_idemp_r. apply bv8_mod.
Qed.
Lemma uv_CURH : forall Ex, CL5A.uv Ex PSO.CURH = (CL5A.uv Ex WLEN + CL5A.uv Ex WP0 - CL5A.uv Ex (EVar JV)) mod 2 ^ 64.
Proof.
  intros Ex. unfold PSO.CURH, CL5A.uv, WLEN, WP0. cbn [edenot]. rewrite !u_add64, u_mul64, u_lit64a.
  rewrite Zmult_mod_idemp_l, Zplus_mod_idemp_r, Z.add_assoc, Zplus_mod_idemp_r. f_equal; lia.
Qed.

Definition more_pin (c : CC.cutpoint) (cells : list kentry) (t : PSO.pv) : option Z :=
  match PSO.v_more t with ELit z => Some z | EVar v => PSO.pin (cells ++ CC.cp_know c) v | _ => None end.

Definition kr_ok (nx : nat) (cells : list kentry) (X : kentry) : bool := match X with KRange e lo hi => (prove_std cells X && APC.expr_vars_lt nx e)%bool | _ => false end.
Definition psame_ok (i : nat) (c : CC.cutpoint) (ps0 : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps0 in
  match PSO.pview (CC.cp_know c), PSO.pview cells with
  | Some t, Some l => let d := PSO.mkdelta cells t l in
      ((negb (PSO.has_bufbyte (CC.cp_F c)) || PSO.has cells (KWord (SA (APC.eadd (PSO.v_size l) (PSO.v_bptr l)) 0) 1 (ELit 0)))
       && (PSO.has cells (KWord (SA PE 213) 1 (ELit 1)) || negb (existsb (PSO.region_eqb (PE, 200, ELit 16)) (CC.cp_F c)))
       && ((negb (PSO.has_bufbyte (CC.cp_F c)) && PSO.is_same (PSO.d_size d)) || match PSO.tst c cells t with Some z => (negb (Z.eqb z 17) && (1 <=? z) && (z <=? 28))%bool | None => false end)
       && implb (Z.eqb (PSO.d_adv d) 1) (expr_eqb (PSO.v_wptr t) PSO.CURH)
       && match more_pin c cells t with Some z => (Z.eqb z 0 || Z.eqb z 1)%bool | None => false end
       && forallb (kr_ok (CC.cp_nx c) cells) (PSOK.MEASNEWS cells)
       && match CAX.cell_at cells (EVar 65) 1016 8 with Some e => expr_eqb e (EVar 60) | None => false end
       && match PSO.pclass i c cells t l d with
          | Some PSO.PSame => (PSO.is_same (PSO.d_st d) && PSO.is_same (PSO.d_sst d) && PSO.is_same (PSO.d_nst d) && PSO.is_same (PSO.d_more d) && PSO.is_same (PSO.d_done d))%bool
          | _ => true end)%bool
  | _, _ => false
  end.

Definition PCALLEES : list Z := [ERRH; SETEC; POPST; PARENT; VPUSH; PUSHB; SKIPSP; PNULL; BOBJ; BARR; EOBJ; EARR; BMEMBER; PTRUE; PFALSE; PSTRING; PNUMBER; ENDINT; ENDFRAC;
                                 VNULL; VBOOL].
Definition ck_chk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with CC.TOther pc => (negb (PSO.inb pc PCALLEES) || PSO.dead_chk i ps pc || psame_ok i c ps)%bool | CC.TGoto _ _ => true end.
Lemma CK_all : CH2.leaves_all G.CPS G.TAGS ck_chk = true. Proof. vmc_refl. Qed.
Lemma CK : forall pc i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> In pc PCALLEES -> PSO.dead_chk i ps0 pc = false -> psame_ok i c ps0 = true.
Proof.
  intros pc i c k ps0 IL Hpc Hd. pose proof (CH2.leaves_all_sound _ _ _ CK_all _ _ _ _ _ IL) as X. cbn [ck_chk] in X.
  assert (Hin : PSO.inb pc PCALLEES = true) by (unfold PSO.inb; apply existsb_exists; exists pc; split; [exact Hpc | apply Z.eqb_refl]).
  rewrite Hin, Hd in X. exact X.
Qed.

Lemma RETS_u0_all : forallb (fun r : nat * nat * nat * Z => let '(j, i, _, _) := r in Bool.eqb (PSO.u0 j) (PSO.u0 i)) G.RETS = true.
Proof. vmc_refl. Qed.
Lemma U0RET : forall i k j, CH2.ret_of G.RETS i k = Some j -> PSO.u0 j = PSO.u0 i.
Proof.
  intros i k j H. unfold CH2.ret_of in H. destruct (find _ G.RETS) as [[[[j' i'] k'] pc]|] eqn:Hf; [|discriminate H]. injection H as <-.
  apply find_some in Hf as [Hin Hb]. apply andb_prop in Hb as [H1 H2]. apply Nat.eqb_eq in H1, H2. subst i' k'.
  pose proof (proj1 (forallb_forall _ _) RETS_u0_all _ Hin) as X. cbv beta iota in X. apply Bool.eqb_prop in X. exact X.
Qed.

Record CU (pc : Z) (xa : CAXA.xsumA) (i : nat) (c : CC.cutpoint) (ps0 : SR.post_spec) (j : nat) (cj : CC.cutpoint) (ci : CH2.cinfo) : Prop := MKCU {
  cu_ci : nth_error G.CPS i = Some c;
  cu_cj : nth_error G.CPS j = Some cj;
  cu_pc : SR.ps_pc ps0 = pc;
  cu_kj : PSO.kind_of j = PSO.ret_kind pc;
  cu_nd : PSO.kind_of i <> PSO.KDead;
  cu_chk : CHA.custom_chk GT.NF G.HDECL GT.SCELLS GT.GLO GT.GHI (CAX.xs_scr (PSOK.x_of xa)) (CAX.xs_ng (PSOK.x_of xa))
             (CAX.xs_keep (PSOK.x_of xa) (CA.ps_reglist ps0) (nth i G.BLS [])) (nth i PSO.FFS []) (CAX.xs_wregs (PSOK.x_of xa) (CA.ps_reglist ps0))
             (PSOK.news_of xa (CA.ps_reglist ps0) (SR.ps_cells ps0) (CH2.ci_nx ci) (CAX.xs_keep (PSOK.x_of xa) (CA.ps_reglist ps0) (nth i G.BLS [])))
             (CAX.xs_a0 (PSOK.x_of xa) (CA.ps_reglist ps0) (CH2.ci_nx ci)) c ps0 cj (nth i G.BLS []) (nth i PSO.FFS []) (nth j G.BLS []) (nth j PSO.FFS []) = Some ci;
  cu_csp : CH2.ci_csp ci = PSO.CSP;
  cu_blk : nth j G.BLS [] = PSOK.blk_of xa (CA.ps_reglist ps0) (SR.ps_cells ps0) (CH2.ci_nx ci) (CAX.xs_keep (PSOK.x_of xa) (CA.ps_reglist ps0) (nth i G.BLS []));
  cu_F : CC.cp_F cj = CAX.xs_F (PSOK.x_of xa) (CC.cp_F c);
  cu_pre : PSO.pre_chk i c ps0 pc = true }.
Lemma CALL_UNPACK : forall pc xa i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> PSO.call_chk i c k ps0 pc = true -> PSO.dead_chk i ps0 pc = false ->
  PSOK.xs_at pc = Some xa -> exists j cj ci, CH2.ret_of G.RETS i k = Some j /\ CU pc xa i c ps0 j cj ci.
Proof.
  intros pc xa i c k ps0 IL CHK HD Hxa.
  assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
  unfold PSO.call_chk in CHK. rewrite Hxa in CHK. unfold PSO.ret_of in CHK.
  destruct (CH2.ret_of G.RETS i k) as [j|] eqn:Hret; [|discriminate CHK]. destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate CHK].
  apply andb_prop in CHK as [CHK YP]. apply andb_prop in CHK as [CHK YX]. apply andb_prop in CHK as [Y0 YK]. apply Z.eqb_eq in Y0. apply PSO.kind_eqb_eq in YK.
  assert (ND : PSO.kind_of i <> PSO.KDead) by (intros X; unfold PSO.dead_chk in HD; rewrite X in HD; discriminate HD).
  replace (PSO.kind_eqb (PSO.kind_of i) PSO.KDead) with false in YK by (destruct (PSO.kind_of i); try reflexivity; contradiction).
  unfold PSO.callee_x, PSO.gof in YX.
  destruct (CHA.common_chk GT.NF G.HDECL (CAX.xs_scr (PSOK.x_of xa)) (CAX.xs_ng (PSOK.x_of xa)) c ps0 cj (nth i G.BLS []) (nth i PSO.FFS [])) as [ci0|] eqn:Hcc.
  - lazymatch type of YX with (match ?t with _ => _ end) = true => destruct t as [ci|] eqn:Hchk; [|discriminate YX] end.
    assert (E : ci = ci0).
    { unfold CHA.custom_chk in Hchk. rewrite Hcc in Hchk. lazymatch type of Hchk with (if ?b then _ else _) = _ => destruct b; [injection Hchk as <-; reflexivity | discriminate Hchk] end. }
    subst ci0. apply andb_prop in YX as [YX YF]. apply andb_prop in YX as [Ycsp YB]. apply Z.eqb_eq in Ycsp. apply CH2.blocks_eqb_eq in YB. apply CBA.regions_eqb_eq in YF.
    exists j, cj, ci. split; [reflexivity|]. constructor; assumption.
  - exfalso. lazymatch type of YX with (match ?t with _ => _ end) = true => destruct t eqn:Hchk; [|discriminate YX] end.
    unfold CHA.custom_chk in Hchk. rewrite Hcc in Hchk. discriminate Hchk.
Qed.

Lemma CK_NEWS : forall pc i c k ps0, CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> In pc PCALLEES -> PSO.dead_chk i ps0 pc = false ->
  forallb (kr_ok (CC.cp_nx c) (SR.ps_cells ps0)) (PSOK.MEASNEWS (SR.ps_cells ps0)) = true /\ CAX.cell_at (SR.ps_cells ps0) (EVar 65) 1016 8 = Some (EVar 60).
Proof.
  intros pc i c k ps0 IL Hpc Hd. pose proof (CK pc i c k ps0 IL Hpc Hd) as SIDE. unfold psame_ok in SIDE.
  destruct (PSO.pview (CC.cp_know c)) as [t|]; [|discriminate SIDE]. destruct (PSO.pview (SR.ps_cells ps0)) as [l|]; [|discriminate SIDE]. cbv zeta in SIDE.
  apply andb_prop in SIDE as [SIDE _]. apply andb_prop in SIDE as [SIDE S8]. apply andb_prop in SIDE as [_ S7]. split; [exact S7|].
  destruct (CAX.cell_at (SR.ps_cells ps0) (EVar 65) 1016 8) as [e|]; [|discriminate S8]. apply expr_eqb_eq in S8. subst e. reflexivity.
Qed.

Section P.
Context {SCFG_P : ScfgP}.
Variable I : PSOI.inst.
Local Abbreviation L := (PSOI.iL I).     Local Abbreviation ar := (PSOI.iar I).    Local Abbreviation C := (PSOI.iC I).     Local Abbreviation HI := (PSOI.iHI I).
Local Abbreviation LBo := (PSOI.iLBo I). Local Abbreviation FF := (PSOI.iFF I).    Local Abbreviation LK := (PSOI.iLK I).   Local Abbreviation A := (PSOI.iA I).
Local Abbreviation sp := (PSOI.isp I).   Local Abbreviation P := (PSOI.iP I).      Local Abbreviation V := (PSOI.iV I).     Local Abbreviation E := (PSOI.iE I).
Local Abbreviation B := (PSOI.iB I).     Local Abbreviation M := (PSOI.iM I).      Local Abbreviation model := (PSOI.imodel I).
Local Abbreviation HIok := (PSOI.iHIok I).
Local Abbreviation E0 := (PSOI.E0 I).      Local Abbreviation WW := (WW I).            Local Abbreviation Cred := (PSOX.Cred I).
Local Abbreviation bptrI := (PSOX.bptrI).  Local Abbreviation bcapI := (PSOX.bcapI). Local Abbreviation sbI := (PSOX.sbI). Local Abbreviation scapI := (PSOX.scapI).

Record PSAMEF (c : CC.cutpoint) (cells : list kentry) (t : PSO.pv) (ps1 ps2 : PML.pstate) : Prop := MKPSF {
  pf_eq : ps2 = PSOST.ps_upd ps1 (PML.ps_st ps1) (PML.ps_sst ps1) (PML.ps_nst ps1) (PML.ps_more ps1) (PML.ps_done ps1) (PML.ps_buf ps2) (PML.ps_win ps2);
  pf_win : match PML.ps_win ps1 with Some (p, e) => exists p', PML.ps_win ps2 = Some (p', e) /\ p <= p' <= p + 1 | None => PML.ps_win ps2 = None end;
  pf_buf : (length (PML.ps_buf ps2) <= length (PML.ps_buf ps1))%nat;
  pf_more : forall z, more_pin c cells t = Some z -> PML.b2z (PML.ps_more ps1) = z;
  pf_st : forall z, PSO.tst c cells t = Some z -> PML.ps_more ps1 = true -> 1 <= z <= 28 -> PML.ps_st ps1 = z }.

Lemma WIN2 : forall i c E1 R1 A1 M1 m1 E' mw ps1 code g1 t l,
  nth_error G.CPS i = Some c -> (2 <= i < PSO.NCUT)%nat -> CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> AAMB I i E1 A1 M1 m1 ->
  PSOX.CORE I i E1 M1 mw ps1 code g1 -> mw = PML.ps_win ps1 ->
  PSO.pview (CC.cp_know c) = Some t ->
  forall dW dA, (dW = true -> CL5A.uv E' (PSO.v_wptr l) = PSOI.wlo mw mod 2 ^ 64) ->
  (dA = true -> CL5A.uv E' (PSO.v_wptr l) = (PSOI.wlo mw + 1) mod 2 ^ 64 /\ PSO.v_wptr t = PSO.CURH /\ PSO.lo_ge (CC.cp_know c) (EVar JV) 1 = true) ->
  (dW || dA)%bool = true ->
  match PML.ps_win ps1 with
  | Some (p1, e) => p1 <= CL5A.uv E' (PSO.v_wptr l) <= p1 + 1 /\ CL5A.uv E' (PSO.v_wptr l) <= e /\ 0 <= p1
  | None => CL5A.uv E' (PSO.v_wptr l) = 0 end.
Proof.
  intros i c E1 R1 A1 M1 m1 E' mw ps1 code g1 t l Hci Hi HAt HA CO Hmw Ht dW dA HdW HdA Hd.
  pose proof (PSOST.TVAL I i c E1 R1 A1 M1 m1 mw ps1 code g1 t Hci Hi HAt HA CO Ht) as TV1.
  pose proof (PSOST.tv_wptr _ _ _ _ TV1) as TW. rewrite Hmw in TW, HdW, HdA.
  assert (KT : know_ok (hl_segs L) E1 (CCA.vis A1 m1 M1) (CC.cp_know c)) by (destruct HAt as [_ HK]; exact HK).
  pose proof (PSOI.WINR I) as (WR1 & WR2). pose_facts I. pose_U I.
  pose proof (FRM I i E1 A1 M1 m1 Hi HA) as (_ & _ & HagE & _).
  assert (U32' : CL5A.uv E1 WLEN = PSOI.wlen I) by (unfold CL5A.uv, WLEN, WLENV; cbn [edenot]; rewrite <- (proj1 HagE 32%nat ltac:(unfold GT.NF, Cut_psome_casan_T.NF; clear; lia)); exact U32).
  assert (U36' : CL5A.uv E1 WP0 = PSOI.wp0 I) by (unfold CL5A.uv, WP0, WP0V; cbn [edenot]; rewrite <- (proj1 HagE 36%nat ltac:(unfold GT.NF, Cut_psome_casan_T.NF; clear; lia)); exact U36).
  assert (WE : PSOI.wlen I + PSOI.wp0 I = PSOI.we0 I) by (unfold PSOI.wlen; clear; lia).

  assert (JV1 : dA = true -> CL5A.uv E1 (PSO.v_wptr t) = (PSOI.we0 I - CL5A.uv E1 (EVar JV)) mod 2 ^ 64 /\ 1 <= CL5A.uv E1 (EVar JV) < 2 ^ 64).
  { intros HA'. destruct (HdA HA') as (_ & CU & LG). unfold PSO.lo_ge in LG. destruct (CX.range3 (CC.cp_know c) (EVar JV)) as [[lo hi]|] eqn:HR; [|discriminate LG]. apply Z.leb_le in LG.
    pose proof (CX.range3_sound _ _ _ _ _ _ _ KT HR) as RG. change (bv_unsigned (edenot E1 (EVar JV))) with (CL5A.uv E1 (EVar JV)) in RG.
    pose proof (CL5A.uv_range E1 (EVar JV)) as RJ. rewrite CU, uv_CURH, U32', U36', WE. split; [reflexivity | clear - LG RG RJ; lia]. }
  unfold PSOX.WIN in *. pose proof (PSOX.c_win _ _ _ _ _ _ _ _ CO) as WN1. unfold PSOX.WIN in WN1.
  destruct (PML.ps_win (PSOI.ips I)) as [[p0 e0]|] eqn:Hw0.
  - destruct WN1 as (p1 & Hp1 & Rp1). rewrite Hp1 in TW, HdW, HdA |- *. cbn [PSOI.wlo] in TW, HdW, HdA.
    pose proof (PSOI.WSOME I p0 e0 Hw0) as (WS1 & WS2 & _). rewrite Z.mod_small in TW by (clear - Rp1 WS1 WS2 WI0 WI1 WE; lia).
    apply orb_prop in Hd as [Hd|Hd].
    + rewrite (HdW Hd), Z.mod_small by (clear - Rp1 WS1 WS2 WI0 WI1 WE; lia). clear - Rp1 WS1 WS2 WI0. lia.
    + destruct (HdA Hd) as (X & _). destruct (JV1 Hd) as (JX & JR). rewrite X, Z.mod_small by (clear - Rp1 WS1 WS2 WI0 WI1 WE; lia).
      rewrite TW in JX. rewrite WS2 in JX.
      destruct (Z_le_gt_dec (CL5A.uv E1 (EVar JV)) e0) as [G|G].
      * rewrite Z.mod_small in JX by (clear - G JR Rp1 WS1 WS2 WI0 WI1 WE; lia). clear - JX JR Rp1 WS1 WS2 WI0. lia.
      * exfalso. replace ((e0 - CL5A.uv E1 (EVar JV)) mod 2 ^ 64) with (e0 - CL5A.uv E1 (EVar JV) + 2 ^ 64) in JX.
        { clear - JX JR Rp1 G. lia. }
        symmetry. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia. apply Z.mod_small. clear - JR G Rp1 WS1 WS2 WI0. lia.
  - rewrite WN1 in TW, HdW, HdA |- *. cbn [PSOI.wlo] in TW, HdW, HdA.
    apply orb_prop in Hd as [Hd|Hd]; [rewrite (HdW Hd); reflexivity|].
    exfalso. destruct (JV1 Hd) as (JX & JR). rewrite TW in JX. pose proof (PSOI.WNONE I) as WN. unfold PSOI.win in WN. specialize (WN Hw0). destruct WN as (W0 & W1 & _).
    rewrite W1 in JX. replace ((0 - CL5A.uv E1 (EVar JV)) mod 2 ^ 64) with (2 ^ 64 - CL5A.uv E1 (EVar JV)) in JX.
    { clear - JX JR. lia. }
    symmetry. rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia. rewrite Z.mod_small by (clear - JR; lia). clear. lia.
Qed.

Lemma PSAME : forall pc i c k ps0 E1 R1 A1 M1 m1 E' R' M' m' mw ps1 code g1 t l,
  CH2.is_leaf G.CPS G.TAGS i c k ps0 (CC.TOther pc) -> In pc PCALLEES -> PSO.dead_chk i ps0 pc = false -> PSO.pre_chk i c ps0 pc = true ->
  PSO.pview (CC.cp_know c) = Some t -> PSO.pview (SR.ps_cells ps0) = Some l ->
  PSO.pclass i c (SR.ps_cells ps0) t l (PSO.mkdelta (SR.ps_cells ps0) t l) = Some PSO.PSame ->
  (2 <= i < PSO.NCUT)%nat -> PSO.curk (PSO.kind_of i) = false ->
  CCA.AtV (hl_segs L) c E1 R1 A1 M1 m1 -> AAMB I i E1 A1 M1 m1 -> env_agree (CC.cp_nx c) E1 E' -> CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' ->
  PSOX.FLF I E1 -> PSOX.CORE I i E1 M1 mw ps1 code g1 -> mw = PML.ps_win ps1 -> PMCUR.wf_c ps1 ->
  exists ps2, PSOX.CORE I i E1 M' (PML.ps_win ps2) ps2 code g1 /\ PMCUR.wf_c ps2 /\ PSAMEF c (SR.ps_cells ps0) t ps1 ps2.
Proof.
  intros pc i c k ps0 E1 R1 A1 M1 m1 E' R' M' m' mw ps1 code g1 t l IL Hpc Hd HPC Ht Hl HCL Hi Hck HAt HA Hag HLF HFL CO Hmw WFc. pose proof (proj1 WFc) as WF.
  assert (Hci : nth_error G.CPS i = Some c) by (destruct IL as (tg & Hc & _); exact Hc).
  pose proof (CK pc i c k ps0 IL Hpc Hd) as SIDE. unfold psame_ok in SIDE. rewrite Ht, Hl in SIDE. cbv zeta in SIDE. rewrite HCL in SIDE.
  apply andb_prop in SIDE as [SIDE S6]. apply andb_prop in SIDE as [SIDE _]. apply andb_prop in SIDE as [SIDE _]. apply andb_prop in SIDE as [SIDE S5]. apply andb_prop in SIDE as [SIDE S4]. apply andb_prop in SIDE as [SIDE S3]. apply andb_prop in SIDE as [S1 S2].
  apply andb_prop in S6 as [S6 D5]. apply andb_prop in S6 as [S6 D4]. apply andb_prop in S6 as [S6 D3]. apply andb_prop in S6 as [D1 D2].
  apply PSOST.is_same_eq in D1, D2, D3, D4, D5.
  unfold PSO.pre_chk in HPC. rewrite Ht, Hl in HPC. cbv zeta in HPC.
  apply andb_prop in HPC as [HPC _]. apply andb_prop in HPC as [HPC P5]. apply andb_prop in HPC as [HPC P4]. apply andb_prop in HPC as [HPC P3]. apply andb_prop in HPC as [P1 P2].
  set (cells := SR.ps_cells ps0) in *. set (d := PSO.mkdelta cells t l) in *.
  pose proof (PSOST.STRETCH_same I i c ps0 E1 R1 A1 M1 m1 E' R' M' m' mw ps1 code g1 t l Hci Hi HAt HA Hag HLF CO Ht P4) as SMF. fold cells d in SMF.
  pose proof (PSOST.TVAL I i c E1 R1 A1 M1 m1 mw ps1 code g1 t Hci Hi HAt HA CO Ht) as TV1.
  pose proof (PSOST.view_agree _ _ _ E1 E' P4 Hag) as VA.
  assert (KL : know_ok (hl_segs L) E' (CCA.vis A1 m' M') cells).
  { unfold know_ok. apply Forall_forall. intros X HX. exact (CC.lf_cells _ _ _ _ _ _ _ (CCA.lfa_vis _ _ _ _ _ _ _ _ _ _ HLF) _ HX). }
  assert (KT : know_ok (hl_segs L) E1 (CCA.vis A1 m1 M1) (CC.cp_know c)) by (destruct HAt as [_ HK]; exact HK).
  assert (P4' := P4). unfold PSO.view_ok in P4'. cbn [forallb] in P4'.
  apply andb_prop in P4' as [V1 P4']. apply andb_prop in P4' as [V2 P4']. apply andb_prop in P4' as [V3 P4']. apply andb_prop in P4' as [V4 P4'].
  apply andb_prop in P4' as [V5 P4']. apply andb_prop in P4' as [V6 P4']. apply andb_prop in P4' as [V7 _].

  assert (PMORE : forall z, more_pin c cells t = Some z -> PML.b2z (PML.ps_more ps1) = z).
  { intros z Hz. pose proof (PSOST.tv_more _ _ _ _ TV1) as TM.
    assert (Zr : z = 0 \/ z = 1) by (rewrite Hz in S5; apply orb_prop in S5 as [S5|S5]; apply Z.eqb_eq in S5; [left | right]; exact S5).
    assert (UZ : Z_to_bv 8 (CL5A.uv E1 (PSO.v_more t)) = Z_to_bv 8 z).
    { pose proof (PSOST.va_more _ _ _ VA) as VM. unfold more_pin in Hz. destruct (PSO.v_more t) as [z0|v| | | | | |] eqn:Hvm; try discriminate Hz.
      - injection Hz as <-. apply uv_lit_bv8.
      - cbn [APC.expr_vars_lt] in V7. apply Nat.ltb_lt in V7.
        rewrite <- VM. rewrite (pin_sound _ _ _ _ _ _ _ _ _ _ KL KT Hag V7 Hz). reflexivity. }
    rewrite TM in UZ. symmetry. apply (bv8_eq z (PML.b2z (PML.ps_more ps1))); [symmetry; exact UZ | destruct Zr as [->| ->]; lia | apply b2z_rng]. }
  assert (PST : forall z, PSO.tst c cells t = Some z -> PML.ps_more ps1 = true -> 1 <= z <= 28 -> PML.ps_st ps1 = z).
  { intros z Hz Hm Hz28. unfold PSO.tst in Hz.
    pose proof (st_lit_sound _ _ _ _ _ _ _ _ _ _ KL KT Hag V4 Hz) as UZ. rewrite (PSOST.va_st _ _ _ VA), (PSOST.tv_st _ _ _ _ TV1) in UZ.
    destruct (PSSA.wf_more ps1 WF Hm) as (_ & HD & _). unfold PML.handled in HD.
    apply (bv8_eq _ _ UZ); [clear - HD; lia | clear - Hz28; lia]. }

  assert (HWIN := WIN2 i c E1 R1 A1 M1 m1 E' mw ps1 code g1 t l Hci Hi HAt HA CO Hmw Ht (PSO.is_same (PSO.d_wptr d)) (Z.eqb (PSO.d_adv d) 1 && PSO.lo_ge (CC.cp_know c) (EVar JV) 1)%bool
                     ltac:(intros X; apply PSOST.is_same_eq in X; exact (PSOST.s_wptr _ _ _ _ _ _ SMF X))
                     ltac:(intros X; apply andb_prop in X as [X1 X2]; apply Z.eqb_eq in X1; split; [exact (PSOST.s_adv _ _ _ _ _ _ SMF X1)|];
                           split; [rewrite X1 in S4; cbn [implb] in S4; apply expr_eqb_eq in S4; exact S4 | exact X2]) P2).
  set (p2 := CL5A.uv E' (PSO.v_wptr l)) in *.
  set (w2 := match PML.ps_win ps1 with Some (p, e) => Some (p2, e) | None => None end).

  assert (HS1 : PSO.has_bufbyte (CC.cp_F c) = false \/ PSO.has cells (KWord (SA (APC.eadd (PSO.v_size l) (PSO.v_bptr l)) 0) 1 (ELit 0)) = true).
  { apply orb_prop in S1 as [S1|S1]; [left; apply negb_true_iff in S1; exact S1 | right; exact S1]. }
  assert (HS2 : PSO.has cells (KWord (SA PE 213) 1 (ELit 1)) = true \/ existsb (PSO.region_eqb (PE, 200, ELit 16)) (CC.cp_F c) = false).
  { apply orb_prop in S2 as [S2|S2]; [left; exact S2 | right; apply negb_true_iff in S2; exact S2]. }
  assert (HWP : PSOI.wlo w2 = p2).
  { unfold w2. destruct (PML.ps_win ps1) as [[p e]|]; [reflexivity | cbn [PSOI.wlo]; symmetry; exact HWIN]. }
  assert (HWE : PSOI.whi w2 = PSOI.whi mw) by (unfold w2; rewrite Hmw; destruct (PML.ps_win ps1) as [[p e]|]; reflexivity).
  assert (HWS : match w2 with Some (p, e) => p <= e | None => mw = None end).
  { unfold w2. rewrite Hmw. destruct (PML.ps_win ps1) as [[p e]|]; [exact (proj1 (proj2 HWIN)) | reflexivity]. }
  destruct (PSOST.STRETCH I i c ps0 E1 R1 A1 M1 m1 E' R' M' m' mw ps1 code g1 t l Hci Hi HAt HA Hag HLF HFL CO Ht Hl P4 P1 P3 HS1 HS2
              (PML.ps_st ps1) (PML.ps_sst ps1) (PML.ps_nst ps1) (PML.ps_more ps1) (PML.ps_done ps1) w2
              (PSOST.s_st _ _ _ _ _ _ SMF D1) (PSOST.s_sst _ _ _ _ _ _ SMF D2) (PSOST.s_nst _ _ _ _ _ _ SMF D3) (PSOST.s_more _ _ _ _ _ _ SMF D4) (PSOST.s_done _ _ _ _ _ _ SMF D5)
              HWP HWE HWS) as (buf2 & MEM2 & BS & BN).
  fold cells d in BS, BN.
  set (ps2 := PSOST.ps_upd ps1 (PML.ps_st ps1) (PML.ps_sst ps1) (PML.ps_nst ps1) (PML.ps_more ps1) (PML.ps_done ps1) buf2 w2).
  assert (LB2 : (length buf2 <= length (PML.ps_buf ps1))%nat).
  { destruct (PSO.d_size d) eqn:DS; [rewrite (proj1 (BS eq_refl)); lia | rewrite (BN ltac:(discriminate)); cbn; lia ..]. }
  assert (HWF : PML.wf_ps ps2).
  { assert (NP : PML.ps_more ps1 = true -> PML.ps_st ps1 = PML.ST_NUMBER -> PML.num_prefix (PML.ps_nst ps1) buf2).
    { intros Hm Hs. apply orb_prop in S3 as [S3|S3].
      - apply andb_prop in S3 as [S3a S3b]. apply negb_true_iff in S3a. apply PSOST.is_same_eq in S3b. rewrite (proj2 (BS S3b) S3a).
        exact (proj2 (proj2 (PSSA.wf_more ps1 WF Hm)) Hs).
      - destruct (PSO.tst c cells t) as [z|] eqn:Hz; [|discriminate S3]. apply andb_prop in S3 as [S3 S3c]. apply andb_prop in S3 as [S3a S3b].
        apply negb_true_iff, Z.eqb_neq in S3a. apply Z.leb_le in S3b, S3c. exfalso. apply S3a. rewrite <- (PST z eq_refl Hm ltac:(lia)). exact Hs. }
    pose proof (PSSA.wf_buf ps1 (PML.ps_bcap ps1) (PML.ps_bptr ps1) buf2 WF NP) as W1. exact (PSSA.wf_win _ w2 W1). }
  exists ps2. split; [|split; [split; [exact HWF | unfold PMCUR.lvl_ok in *; cbn [ps2 PSOST.ps_upd PML.ps_more PML.ps_st PML.ps_stack PML.ps_level]; exact (proj2 WFc)]|]].
  - pose proof (PSOX.c_win _ _ _ _ _ _ _ _ CO) as WN1. pose proof (PSOX.c_bb _ _ _ _ _ _ _ _ CO) as BB1.
    constructor.
    + exact (PSOST.m_pa _ _ _ _ _ _ MEM2).
    + left. split; [exact Hck | reflexivity].
    + exact (PSOST.m_sh _ _ _ _ _ _ MEM2).
    + unfold PSOX.WIN in *. cbn [ps2 PSOST.ps_upd PML.ps_win]. unfold w2.
      destruct (PML.ps_win (PSOI.ips I)) as [[p0 e0]|]; [destruct WN1 as (p1 & Hp1 & Rp1); rewrite Hp1 in HWIN |- *; exists p2; split; [reflexivity | clear - HWIN Rp1; lia] | rewrite WN1; reflexivity].
    + unfold PML.buf_bound, PML.winlen, PML.buf_need in *. cbn [ps2 PSOST.ps_upd PML.ps_win PML.ps_buf PML.ps_more PML.ps_st PML.ps_sst]. unfold w2.
      destruct (PML.ps_win ps1) as [[p1 e1]|].
      * destruct HWIN as (H1 & H2 & H3). clear - BB1 LB2 H1 H2 H3. destruct BB1 as [BB1 BB2]. split; [|exact BB2]. lia.
      * clear - BB1 LB2. destruct BB1 as [BB1 BB2]. split; [|exact BB2]. lia.
    + exact (PSOST.m_ec _ _ _ _ _ _ MEM2).
    + exact (PSOST.m_ls _ _ _ _ _ _ MEM2).
    + exact (PSOX.c_g _ _ _ _ _ _ _ _ CO).
    + cbn [ps2 PSOST.ps_upd PML.ps_more PML.ps_level]. exact (PSOX.c_lv _ _ _ _ _ _ _ _ CO).
    + exact (PSOX.c_blk _ _ _ _ _ _ _ _ CO).
    + exact (PSOX.c_na _ _ _ _ _ _ _ _ CO).
    + exact (PSOX.c_wl _ _ _ _ _ _ _ _ CO).
    + exact (PSOX.c_e0 _ _ _ _ _ _ _ _ CO).
  - constructor.
    + reflexivity.
    + cbn [ps2 PSOST.ps_upd PML.ps_win]. unfold w2. destruct (PML.ps_win ps1) as [[p1 e1]|]; [exists p2; split; [reflexivity | clear - HWIN; lia] | reflexivity].
    + exact LB2.
    + exact PMORE.
    + exact PST.
Qed.

Definition AKAG (Mx : mem) : Prop := forall a, CHA.akept L ar LBo FF sp (CH.hd_scr GT.HDECL) WW a -> Mx (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Lemma akag_of : forall i E1 A1 Mx mx, AAMB I i E1 A1 Mx mx -> AKAG Mx.
Proof. intros i E1 A1 Mx mx HA. pose proof HA as (_ & _ & _ & _ & _ & Hfr & _). exact Hfr. Qed.

Definition DEFG (Mx : mem) : Prop := forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBo FF sp 0 a -> M (Z_to_bv 64 a) <> None -> Mx (Z_to_bv 64 a) <> None.
Lemma defg_of : forall i E1 A1 Mx mx, AAMB I i E1 A1 Mx mx -> DEFG Mx.
Proof. intros i E1 A1 Mx mx HA. pose proof HA as (_ & _ & _ & _ & _ & _ & Hd). exact Hd. Qed.

Lemma STKSH : forall (Mx : mem) scr, AKAG Mx -> 0 <= scr -> scr mod 8 = 0 -> 672 + scr <= 10496 -> PMLA.stksh ar Mx (sp + PSO.CSP) scr.
Proof.
  intros Mx scr Hfr Hs0 Hs8 Hs1. pose_facts I. pose proof (AL8 I) as (A8 & A98 & A32). unfold PSO.CSP.
  apply (PTA.stksh_mono ar Mx sp 10496 (sp + -672) scr); [| exact A98 | | clear - Hs1; lia].
  - apply (PTA.stksh_ag ar M Mx sp 10496); [|exact (PSOI.iHstksh I)]. intros a Ha. exact (Hfr a (KSTK I a Ha)).
  - clear - Hs8 A32. apply Z.mod_divide in Hs8; [|lia]. destruct Hs8 as [q Hq]. apply Z.mod_divide in A32; [|lia]. destruct A32 as [r Hr].
    replace (sp + -672 - scr) with ((4 * r - q) * 8) by lia. apply Z_mod_mult.
Qed.

Lemma FOBJ : forall (Mx : mem) (FFx : list fframe) o n, AKAG Mx -> PMLA.fobj M FF o n -> incl FF FFx -> 0 < n -> o + n <= 2 ^ 47 -> PMLA.fobj Mx FFx o n.
Proof.
  intros Mx FFx o n Hfr (Hin & H8 & Hsh) Hincl Hn Hon. split; [destruct Hin as (f & Hf & F1 & F2); exists f; split; [exact (Hincl f Hf) | split; assumption]|].
  split; [exact H8|]. intros jj Hjj.
  assert (IS : in_shadow_of o n (S o + jj)).
  { apply (CL5A.in_shadow_mono o (8 * (n / 8))); [clear; lia | pose proof (Z.mul_div_le n 8 ltac:(lia)); clear - H; lia | clear - Hjj; lia |].
    apply (CL5A.shreg_in_shadow o (n / 8) _ H8); [clear - Hjj; lia | unfold S; clear - Hjj; lia]. }
  unfold byte_at in *. rewrite (Hfr _ (KSHO I o n _ Hin Hn Hon IS)). exact (Hsh jj Hjj).
Qed.
Lemma VISAT : forall (Mx : mem), AKAG Mx -> DEFG Mx -> PMLA.vis_at (hl_segs L) IC Mx V.
Proof.
  intros Mx Hfr Hdf. pose_facts I. apply (PTA.vis_at_ag (hl_segs L) IC M Mx (fun a => V <= a < V + 8) (fun a Ha => Hfr a (KV I a Ha)) V); [| |exact (PSOI.iHVIS I)].
  - split; [clear - VR3; lia|]. split; [clear - VR6; lia|]. intros y Hy. exact Hy.
  - intros y Hy Hd. apply Hdf; [clear - Hy VR3 VR6; lia | exact (aclientw_client _ _ _ _ _ _ _ (CL5A.infr_clientw L ar LBo FF sp 0 V 48 (V + y) Vfr ltac:(clear - Hy; lia))) | exact Hd].
Qed.

Lemma WINOK : forall (Mx : mem) ps2, AKAG Mx -> PSOX.WIN I ps2 -> PMLA.win_okA Mx LBo ps2.
Proof.
  intros Mx ps2 Hfr HW. pose proof (PSOI.iHWIN I) as W0. unfold PSOX.WIN, PMLA.win_okA in *.
  destruct (PML.ps_win (PSOI.ips I)) as [[p0 e0]|] eqn:Hw0.
  - destruct HW as (p1 & Hp1 & R1). rewrite Hp1. destruct W0 as (ch0 & C1 & C2 & C3 & C4 & C5). exists ch0.
    split; [exact C1|]. split; [clear - C2 R1; lia|]. split; [exact C3|]. split.
    + intros jj Hjj. assert (IR : ch0 <= p1 + jj < ch0 + 16384) by (clear - Hjj C2 C3 R1; lia).
      rewrite (Hfr (p1 + jj) (KLB I ch0 16384 (p1 + jj) C1 (or_introl IR))). replace (p1 + jj) with (p0 + (p1 - p0 + jj)) by lia. apply C4. clear - Hjj R1. lia.
    + destruct (CHA.rf_blk _ _ _ _ (RFO I) (ch0, 16384) C1) as (K0 & _ & K16 & _). cbn [fst snd] in K0, K16.
      apply (PTA.shadow_blk_ag M Mx (fun a => in_shadow_of ch0 16384 a) (fun a Ha => Hfr a (KLB I ch0 16384 a C1 (or_intror Ha))) ch0 16384 ltac:(clear; lia)); [intros a Ha; exact Ha | exact (CHA.mod8_of_16 _ K16) | exact C5].
  - rewrite HW. exact Logic.I.
Qed.

Lemma CORE_RE : forall i j E1 E2 (Mx : mem) mw psx code g1,
  PSOX.CORE I i E1 Mx mw psx code g1 -> PSO.curk (PSO.kind_of j) = false -> mw = PML.ps_win psx ->
  bptrI j E2 = bptrI i E1 -> bcapI j E2 = bcapI i E1 -> sbI j E2 = sbI i E1 -> scapI j E2 = scapI i E1 -> PSO.u0 j = PSO.u0 i ->
  (PSOX.retk (PSO.kind_of j) = false -> PSOX.retk (PSO.kind_of i) = false) -> (PSOX.wlk (PSO.kind_of j) = true -> PSOX.wlk (PSO.kind_of i) = true) ->
  (PSO.u0 i = true -> env_agree 60 E1 E2) -> PSOX.CORE I j E2 Mx mw psx code g1.
Proof.
  intros i j E1 E2 Mx mw psx code g1 CO Hcj Hmw B1 B2 B3 B4 HU Hr Hw He. constructor.
  - exact (PSOX.c_pa _ _ _ _ _ _ _ _ CO).
  - left. split; [exact Hcj | exact Hmw].
  - exact (PSOX.c_sh _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_win _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_bb _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_ec _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_ls _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_g _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_lv _ _ _ _ _ _ _ _ CO).
  - rewrite B1, B2, B3, B4. exact (PSOX.c_blk _ _ _ _ _ _ _ _ CO).
  - intros H0 H1. rewrite HU in H0. exact (PSOX.c_na _ _ _ _ _ _ _ _ CO H0 (Hr H1)).
  - intros H0 H1. rewrite HU in H0. exact (PSOX.c_wl _ _ _ _ _ _ _ _ CO H0 (Hw H1)).
  - intros H0. rewrite HU in H0. exact (CC.env_agree_trans _ _ _ _ (PSOX.c_e0 _ _ _ _ _ _ _ _ CO H0) (He H0)).
Qed.

Lemma SUPP_AHP : forall i E1 A1 M1 m1 (Mx M2 : mem) LBk scr Wc, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 ->
  CHA.ahpres L ar LBk (CHA.curF FF sp PSO.FFS i E1) (sp + PSO.CSP) scr Wc Mx M2 -> incl (CHA.curB LBo G.BLS i E1) LBk -> 672 + scr <= 10496 ->
  forall a, SUPP I (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a -> L5.outside Wc a -> M2 (Z_to_bv 64 a) = Mx (Z_to_bv 64 a).
Proof.
  intros i E1 A1 M1 m1 Mx M2 LBk scr Wc Hi HA HP Hinc Hs1 a Ha HW. destruct (SUPP_geom I i E1 A1 M1 m1 a Hi HA Ha) as (RG & X1 & _ & _ & X4 & _).
  apply (proj1 HP a). split; [exact RG|]. split; [|exact HW].
  apply (CHA.aclient_scr_pt _ _ _ _ _ _ (sp + PSO.CSP) 256); [|unfold PSO.CSP, SCR in *; clear - X1 Hs1; lia].
  exact (CHA.aclient_incl _ _ _ _ _ _ _ _ _ _ _ Hinc (incl_refl _) X4).
Qed.

Lemma NEWS_SI : forall E2 A2 m2 (M2 : mem) LB2 FF2 LK2 cr2, ri_inv HI LB2 FF2 LK2 cr2 A2 M2 (vml_of m2) ->
  Forall (kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2)) PSOK.STATICS_ISH.
Proof.
  intros E2 A2 m2 M2 LB2 FF2 LK2 cr2 HH2. pose_facts I.
  assert (ST : forall X, CHA.static_chk GT.SCELLS GT.GLO GT.GHI X = true -> kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) X).
  { intros X HX. exact (CHA.static_sound L ar C HI HIok (LYI I) GT.NF 0 (NF32) GT.SCELLS GT.GLO GT.GHI (SCOK I) (GOTOK I) _ _ _ _ _ _ _ E2 X HH2 HX). }
  assert (ISHZ : forall slot sh, In slot ISLOTS -> 65536 <= slot -> slot + 8 <= 7024640 -> sh = slot / 8 + SB -> slot mod 8 = 0 ->
            kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) (KZero (SA (ELit 0) sh) (ELit 1))).
  { intros slot sh Hin Hlo Hhi Hsh Hal.
    assert (POIs : Forall (fun r : Z * Z => slot + 8 <= fst r \/ snd r <= slot) (icl_poison (PSOI.iIL I))).
    { apply (Forall_impl (P := fun r : Z * Z => Forall (fun a => a + 8 <= fst r \/ snd r <= a) ISLOTS)); [|exact (PSOI.iPOI I)]. intros r Hr. exact (proj1 (Forall_forall _ _) Hr slot Hin). }
    destruct (PSOI.iISH I _ _ _ _ _ _ _ HH2 slot 8 ltac:(rewrite ILO; clear - Hlo; lia) ltac:(rewrite IHI; clear - Hhi; lia) ltac:(clear; lia) POIs) as [BZ BA].
    assert (ISX : in_shadow_of slot 8 sh) by (unfold in_shadow_of, S; rewrite Hsh; pose proof (Z_div_mod_eq_full slot 8); clear - H Hal; split; [lia|]; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
    assert (SH0 : 0 <= sh < 2 ^ 64) by (rewrite Hsh; unfold SB; clear - Hlo Hhi; split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia | lia] | pose proof (Z.div_le_upper_bound slot 8 1067244 ltac:(lia) ltac:(lia)); lia]).
    eapply CL5A.kzero_intro with (A := sh) (N := 1); [unfold estart; cbn [a_base a_off edenot]; rewrite L5.unsigned_lit by (clear; lia); clear - SH0; lia | reflexivity | clear - SH0; lia | clear - SH0; lia | clear - SH0; lia |].
    intros jj Hjj. replace (sh + jj) with sh by (clear - Hjj; lia). apply CL5A.byte_vis; [apply CHA.vis_allowed; exact (BA _ ISX) | exact (BZ _ ISX)]. }
  unfold PSOK.STATICS_ISH.
  apply Forall_cons; [apply ST; reflexivity|]. apply Forall_cons; [apply ST; reflexivity|]. apply Forall_cons; [apply ST; reflexivity|].
  apply Forall_cons; [apply (ISHZ (VT_FUNC + 48)); [left; reflexivity | unfold VT_FUNC; clear; lia | unfold VT_FUNC; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]|].
  apply Forall_cons; [apply (ISHZ (VT_VISITOR + 56)); [right; left; reflexivity | unfold VT_VISITOR; clear; lia | unfold VT_VISITOR; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]|].
  apply Forall_cons; [apply (ISHZ (VT_VISITOR + 104)); [right; right; left; reflexivity | unfold VT_VISITOR; clear; lia | unfold VT_VISITOR; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]|].
  apply Forall_cons; [apply (ISHZ (VT_VISITOR + 112)); [right; right; right; left; reflexivity | unfold VT_VISITOR; clear; lia | unfold VT_VISITOR; clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]|].
  apply Forall_nil.
Qed.

Lemma NEWS_KR : forall c ps0 E' R' A1 M1 m1 M' m' E2 (My : mem) Xs, CCA.leaf_factsA (hl_segs L) c ps0 E' R' A1 M1 m1 M' m' -> env_agree (CC.cp_nx c) E' E2 ->
  forallb (kr_ok (CC.cp_nx c) (SR.ps_cells ps0)) Xs = true -> Forall (kentry_ok (hl_segs L) E2 My) Xs.
Proof.
  intros c ps0 E' R' A1 M1 m1 M' m' E2 My Xs HLF Hag HX. apply Forall_forall. intros X HXin. rewrite forallb_forall in HX. specialize (HX X HXin). unfold kr_ok in HX.
  destruct X as [| | | | | e lo hi | | | |]; try discriminate HX. apply andb_prop in HX as [HP Hv].
  pose proof (PROVE I prove_std c ps0 E' R' A1 M1 m1 M' m' e lo hi prove_std_ok HLF HP) as RG.
  cbn [kentry_ok]. change (bv_unsigned (edenot E2 e)) with (CL5A.uv E2 e). rewrite (PSOST.uv_agree _ E' E2 e Hag Hv). exact RG.
Qed.

Lemma NEWS_FLAGC : forall i E1 A1 M1 m1 E2 A2 m2 (Mx M2 : mem) mx LB1 LK1 cr1 LB2 LK2 cr2, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 -> PSOX.FLF I E1 ->
  ri_inv HI LB1 (CHA.curF FF sp PSO.FFS i E1) LK1 cr1 A1 Mx (vml_of mx) -> ri_inv HI LB2 (CHA.curF FF sp PSO.FFS i E1) LK2 cr2 A2 M2 (vml_of m2) ->
  L5.u64_at (hl_segs L) Mx (CL5A.uv E1 FE + 1016) (CL5A.uv E1 FLE) -> CL5A.uv E2 FE = CL5A.uv E1 FE -> CL5A.uv E2 FLE = CL5A.uv E1 FLE ->
  Forall (kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2)) [KWord (SA FE 1016) 8 FLE; KWr (SA FLE 0) (ELit 1)].
Proof.
  intros i E1 A1 M1 m1 E2 A2 m2 Mx M2 mx LB1 LK1 cr1 LB2 LK2 cr2 Hi HA HFL HH1 HH2 HFLC T65 T60. pose_facts I.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (_ & HcF & _ & F0 & F1 & F64 & _ & F3 & F4 & _).
  destruct HFL as (FL1 & _).
  set (F := CL5A.uv E1 FE) in *. set (fl := CL5A.uv E1 FLE) in *.
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) as WFb.
  destruct (CHA.rf_fs _ _ _ _ RFx) as ((G0 & _) & G3 & _). unfold FS_BYTES in G3.
  assert (VFS : forall y, ar_fs ar <= y < ar_fs ar + 11571200 -> ahid A2 m2 (Z_to_bv 64 y) = false).
  { intros y Hy. apply (CHA.fs_vis L ar C HI HIok GT.NF 0 NF32 _ _ _ _ _ _ m2 y HH2); [clear - Hy G0 G3 CL SP1; lia | unfold FS_BYTES; exact Hy]. }
  rewrite HcF in HH1, HH2.
  pose proof (PmHeapIfaceA.aio_flagptr _ _ _ _ _ HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 4 (sp + PSO.CSP + 32) (sp + PSO.CSP + 32) fl HH1 HH2 (or_introl eq_refl) (or_introl eq_refl)) as FP.
  change (ff_bytes 4) with 1024 in FP. replace (F + 1024 - 8) with (F + 1016) in FP by (clear; lia). specialize (FP HFLC).
  apply Forall_cons.
  - eapply CL5.kword64_intro with (A := F + 1016) (z := fl); [unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E2 FE)) with (CL5A.uv E2 FE); rewrite T65; reflexivity | clear - F0; lia | clear - F1; lia | |].
    + rewrite <- (Z_to_bv_bv_unsigned _ (edenot E2 FLE)). f_equal. exact T60.
    + apply (CL5A.u64_vis (hl_segs L)); [clear - F0; lia | clear - F1; lia | | exact FP]. intros y Hy. apply VFS. clear - Hy F3 F4. lia.
  - apply Forall_cons; [|apply Forall_nil].
    eapply CL5.kwr_intro with (A := fl) (N := 1); [unfold estart; cbn [a_base a_off]; change (bv_unsigned (edenot E2 FLE)) with (CL5A.uv E2 FLE); rewrite T60; clear; lia | reflexivity | | | |].
    + clear - FL1 G0. lia.
    + clear - FL1 G3 CL SP1. lia.
    + clear - FL1 G3 CL SP1. lia.
    + intros y Hy. unfold CCA.vis. rewrite (CL5A.vis_eq _ M2 _ (VFS (fl + y) ltac:(clear - Hy FL1; lia))).
      pose proof (CHA.wf_fs_def _ _ _ _ _ _ _ _ WFb) as FD. replace (fl + y) with (ar_fs ar + (fl + y - ar_fs ar)) by (clear; lia). apply FD. unfold FS_BYTES. clear - Hy FL1. lia.
Qed.

Lemma NEWS_BSHZ : forall E2 A2 m2 (M2 : mem) LB2 FF2 LK2 cr2 bp bc, ri_inv HI LB2 FF2 LK2 cr2 A2 M2 (vml_of m2) -> In (bp, bc) LB2 ->
  CL5A.uv E2 (EVar 56) = bp -> 264 <= bc -> shadow_blk M2 bp bc ->
  kentry_ok (hl_segs L) E2 (CCA.vis A2 m2 M2) (KZero (SA (CHA.SRL3 (EVar 56)) SB) (ELit 33)).
Proof.
  intros E2 A2 m2 M2 LB2 FF2 LK2 cr2 bp bc HH2 Hin Hbp Hbc [BZ0 _].
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HH2) (bp, bc) Hin) as ((D0 & _ & D16 & D3 & _ & (D5 & _ & D7)) & _ & BSHA & _). cbn [fst snd] in *.
  apply (CL5A.shz_intro (hl_segs L) E2 _ (EVar 56) 33 bp Hbp); [clear; lia | clear - D5 D7 D3; lia |].
  intros jj Hjj. assert (ISX : in_shadow_of bp bc (HeapIfaceA.S bp + jj)).
  { apply (CL5A.in_shadow_mono bp (8 * 33)); [clear; lia | clear - Hbc; lia | clear; lia |]. apply (CL5A.shreg_in_shadow _ 33 _ (CHA.mod8_of_16 _ D16)); [clear; lia | unfold HeapIfaceA.S; clear - Hjj; lia]. }
  apply CL5A.byte_vis; [apply CHA.vis_allowed; exact (BSHA _ ISX) |]. apply BZ0. split; [clear - Hjj; lia|]. apply (Z.lt_le_trans _ 33); [clear - Hjj; lia|]. apply Z.div_le_lower_bound; clear - Hbc; lia.
Qed.

Definition SUPPP (bp bc sbp sc : Z) (a : Z) : Prop :=
  (P <= a < P + 272) \/ (bp <= a < bp + bc) \/ in_shadow_of bp bc a \/ (sbp <= a < sbp + sc) \/ in_shadow_of sbp sc a
  \/ (exists u n, In (u, n) LBo /\ (u <= a < u + n \/ in_shadow_of u n a)).
Lemma SUPPP_SUPP : forall bp bc sbp sc a, SUPPP bp bc sbp sc a -> SUPP I bp bc sbp sc a.
Proof. intros bp bc sbp sc a [H|[H|[H|[H|[H|H]]]]]; [left | do 2 right; left | do 3 right; left | do 4 right; left | do 5 right; left | do 7 right; left]; exact H. Qed.
Section Mvx.
Variables (M1 M2 : mem) (bp bc sbp sc : Z).
Hypothesis AG : forall a, SUPPP bp bc sbp sc a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : mem) (Vx : vml).
Hypothesis HHx : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis INb : In (bp, bc) LBx.
Hypothesis INs : In (sbp, sc) LBx.
Let Sx := SUPPP bp bc sbp sc.
Lemma OUTPx : PTA.out Sx P 272. Proof. pose_facts I. split; [clear - O3; lia|]. split; [clear - O6; lia|]. intros i Hi. left. exact Hi. Qed.
Lemma OUTBx : PTA.out Sx bp bc.
Proof.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) (bp, bc) INb) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D3, D5, D7.
  split; [clear - D5; lia|]. split; [clear - D7; lia|]. intros i Hi. right; left. exact Hi.
Qed.
Lemma OUTSx : PTA.out Sx sbp sc.
Proof.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) (sbp, sc) INs) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D0, D3, D5, D7.
  split; [clear - D5; lia|]. split; [clear - D7; lia|]. intros i Hi. do 3 right; left. exact Hi.
Qed.
Lemma parser_at_mvx : forall psx, PML.ps_bptr psx = bp -> PML.ps_bcap psx = bc -> PML.ps_sb psx = sbp -> PML.ps_scap psx = sc ->
  PMLA.parser_at (hl_segs L) IC M1 P psx -> PMLA.parser_at (hl_segs L) IC M2 P psx.
Proof.
  intros psx Hb Hc Hs Hsc H.
  assert (ST : L5.u8_at (hl_segs L) M2 (P + 208) (PML.ps_st psx)).
  { pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). apply (PTA.u8_ag (hl_segs L) M1 M2 Sx AG); [apply (PTA.out_sub _ _ _ _ _ OUTPx); lia | exact X]. }
  assert (DF : M2 (Z_to_bv 64 (P + 208)) <> None).
  { pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D).
    rewrite (AG (P + 208) ltac:(left; lia)). exact (D 208 ltac:(lia)). }
  pose proof (PTA.parser_at_st (hl_segs L) IC M1 M2 Sx AG P psx (PML.ps_st psx) ltac:(intros k n Hk Hn _; apply (PTA.out_sub _ _ _ _ _ OUTPx); lia)
                ltac:(rewrite Hb, Hc; exact OUTBx) ltac:(rewrite Hs, Hsc; exact OUTSx) H ST DF) as G.
  destruct psx; exact G.
Qed.
Lemma parser_sh_mvx : forall psx, PML.ps_bptr psx = bp -> PML.ps_bcap psx = bc -> PML.ps_sb psx = sbp -> PML.ps_scap psx = sc -> Z.of_nat (length (PML.ps_stack psx)) <= PML.ps_scap psx ->
  PMLA.parser_sh M1 psx -> PMLA.parser_sh M2 psx.
Proof.
  intros psx Hb Hc Hs Hsc Hsl H.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) (bp, bc) INb) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _). cbn [fst snd] in D3, D16.
  destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHx) (sbp, sc) INs) as ((G0 & G1 & G16 & G3 & G4 & (G5 & G6 & G7)) & _). cbn [fst snd] in G3, G16.
  apply (PTA.parser_sh_ag M1 M2 Sx AG psx); [rewrite Hc; clear - D3; lia | clear - Hsl; lia | rewrite Hb; exact (CHA.mod8_of_16 _ D16) | rewrite Hs; exact (CHA.mod8_of_16 _ G16)
    | rewrite Hb, Hc; intros a Ha; do 2 right; left; exact Ha | rewrite Hs, Hsc; intros a Ha; do 4 right; left; exact Ha | exact H].
Qed.
End Mvx.
Lemma CORE_mvx : forall i Ex (M1 M2 : mem) mw psx code g1 code' g' LBx FFx LKx crx Ax Mx Vx,
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (bptrI i Ex, bcapI i Ex) LBx -> In (sbI i Ex, scapI i Ex) LBx ->
  (forall a, SUPPP (bptrI i Ex) (bcapI i Ex) (sbI i Ex) (scapI i Ex) a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  PMLA.ec_at (hl_segs L) IC M2 E code' -> PMLA.ls_ok (hl_segs L) IC g' M2 -> (g' = PSOI.ig I \/ (g' = PML.regJ (PSOI.ig I) /\ code' <> 0)) ->
  PSOX.CORE I i Ex M1 mw psx code g1 -> PSOX.CORE I i Ex M2 mw psx code' g'.
Proof.
  intros i Ex M1 M2 mw psx code g1 code' g' LBx FFx LKx crx Ax Mx Vx HHx INb INs AG HEC HLS HG CO.
  pose proof (PSOX.c_blk _ _ _ _ _ _ _ _ CO) as CB. unfold PML.ps_blocks in CB. injection CB as Ebp Ebc Esb Esc.
  constructor.
  - apply (parser_at_mvx M1 M2 _ _ _ _ AG LBx FFx LKx crx Ax Mx Vx HHx INb INs (PML.ps_set_win psx mw)); try exact (PSOX.c_pa _ _ _ _ _ _ _ _ CO).
    all: destruct psx; cbn [PML.ps_set_win PML.ps_bptr PML.ps_bcap PML.ps_sb PML.ps_scap] in *; first [exact Ebp | exact Ebc | exact Esb | exact Esc].
  - exact (PSOX.c_mw _ _ _ _ _ _ _ _ CO).
  - apply (parser_sh_mvx M1 M2 _ _ _ _ AG LBx FFx LKx crx Ax Mx Vx HHx INb INs psx); try exact (PSOX.c_sh _ _ _ _ _ _ _ _ CO); try first [exact Ebp | exact Ebc | exact Esb | exact Esc].
    pose proof (PTB.pa_slen L IC _ _ _ (PSOX.c_pa _ _ _ _ _ _ _ _ CO)) as SL2. clear - SL2. destruct psx; cbn [PML.ps_set_win PML.ps_scap PML.ps_stack] in *. exact SL2.
  - exact (PSOX.c_win _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_bb _ _ _ _ _ _ _ _ CO).
  - exact HEC.
  - exact HLS.
  - exact HG.
  - exact (PSOX.c_lv _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_blk _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_na _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_wl _ _ _ _ _ _ _ _ CO).
  - exact (PSOX.c_e0 _ _ _ _ _ _ _ _ CO).
Qed.

Lemma GEO2 : forall i E1 A1 M1 m1 a, (2 <= i < PSO.NCUT)%nat -> AAMB I i E1 A1 M1 m1 ->
  SUPPP (bptrI i E1) (bcapI i E1) (sbI i E1) (scapI i E1) a -> ~ (E <= a < E + 16) /\ ~ STATIC a.
Proof.
  intros i E1 A1 M1 m1 a Hi HA Ha. pose_facts I.
  pose proof (PSOI.iAP2 I) as AP2. unfold PMLA.apart in AP2. unfold hid in O5, Q5.
  destruct (FRM I i E1 A1 M1 m1 Hi HA) as (HcB & HcF & _ & _ & _ & _ & _ & _ & _ & _ & (crX & LKX & HHX & _)).
  pose proof (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHX) as WFX.
  assert (NST : forall y, STATIC y -> 65536 <= y < 7024640) by (intros y Hy; exact (proj1 (IMGCL I y Hy))).
  destruct Efr as (fE & HfE & EF1 & EF2).

  assert (BLKX : forall u n LBx FFx LKx crx Ax Mx Vx, ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (u, n) LBx -> In fE FFx ->
            (u <= a < u + n \/ in_shadow_of u n a) -> ~ (E <= a < E + 16) /\ ~ STATIC a).
  { intros u n LBx FFx LKx crx Ax Mx Vx HHy Hun Hf Hx.
    destruct (CHA.wf_blk _ _ _ _ _ _ _ _ (CHA.wf_of L ar C HI HIok _ _ _ _ _ _ _ HHy) (u, n) Hun) as ((D0 & D1 & D16 & D3 & D4 & (D5 & D6 & D7)) & _ & _ & _ & Dfap).
    cbn [fst snd] in *. rewrite ILO, IHI in D1. pose proof (Dfap fE ltac:(apply in_or_app; left; exact Hf)) as DF.
    destruct Hx as [Hx|Hx].
    - split; [clear - DF Hx EF1 EF2; lia|]. intros Hs. pose proof (NST a Hs). clear - H Hx D1. lia.
    - pose proof (SHR u n a ltac:(clear - D5; lia) D3 D7 Hx) as RG. split; [clear - RG Q5; lia|]. intros Hs. pose proof (NST a Hs). clear - H RG. lia. }
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|(u & n & Hun & Ha)]]]]].
  - split; [clear - Ha AP2; lia|]. intros Hs. pose proof (NST a Hs). clear - H Ha O1 FSLO. lia.
  - exact (BLKX _ _ _ _ _ _ _ _ _ HHX (or_introl eq_refl) (or_intror HfE) (or_introl Ha)).
  - exact (BLKX _ _ _ _ _ _ _ _ _ HHX (or_introl eq_refl) (or_intror HfE) (or_intror Ha)).
  - exact (BLKX _ _ _ _ _ _ _ _ _ HHX (or_intror (or_introl eq_refl)) (or_intror HfE) (or_introl Ha)).
  - exact (BLKX _ _ _ _ _ _ _ _ _ HHX (or_intror (or_introl eq_refl)) (or_intror HfE) (or_intror Ha)).
  - exact (BLKX _ _ _ _ _ _ _ _ _ (PSOI.iHH I) ltac:(apply in_or_app; right; exact Hun) HfE Ha).
Qed.

End P.

End PSOCK.
