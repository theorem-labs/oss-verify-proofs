(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u PmCurDefs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseBridges5_u ParseSomeAt_u ParseSomeSem_u ParseSomeSemC_u ParseSomeCurC_u ParseSomeChk_u ParseSomeChk2_u ParseSomeChk3_u ParseSomeChk4_u ParseSomeChk5_u ParseSomeA_u ParseSomeB_u ParseSomeC_u ParseSomeD_u ParseSomeD2_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC.
Module PSF.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Lemma custom_nx : forall NF d scr ng BLk wregs news a0x c ps cj BLi ci, CH2.custom_chk NF d scr ng BLk wregs news a0x c ps cj BLi = Some ci -> CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS - ng)%nat.
Proof.
  intros NF d scr ng BLk wregs news a0x c ps cj BLi ci H. unfold CH2.custom_chk in H. destruct (CH2.common_chk_x NF d scr ng c ps cj BLi) as [ci0|] eqn:Hc; [|discriminate].
  destruct (_ && _)%bool in H; [|discriminate]. injection H as <-. unfold CH2.common_chk_x in Hc.
  repeat match type of Hc with match ?x with _ => _ end = Some _ => destruct x; try discriminate Hc | (if ?b then _ else _) = Some _ => destruct b; try discriminate Hc | (let '_ := ?x in _) = Some _ => destruct x end.
  injection Hc as <-. reflexivity.
Qed.

Lemma rview_facts : forall i c ps j nxj pv lv pe ce d, PSM5.rview i c ps j nxj = Some (pv, lv, pe, ce, d) ->
  PSM2.ldelta i c ps = Some (pv, lv, pe, ce, d) /\ exists pvj, PSM2.vw j = Some (pvj, pe, ce) /\ PSM2.flds pvj = PSM2.flds lv /\ forallb (APC.expr_vars_lt nxj) (pe :: ce :: PSM2.flds lv) = true.
Proof.
  intros i c ps j nxj pv lv pe ce d H. unfold PSM5.rview in H. destruct (PSM2.ldelta i c ps) as [[[[[pv0 lv0] pe0] ce0] d0]|]; [|discriminate]. destruct (PSM2.vw j) as [[[pvj pej] cej]|]; [|discriminate].
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection H as -> -> -> -> ->.
  apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B2, B3. subst pej cej.
  split; [reflexivity|]. exists pvj. split; [reflexivity|]. split; [|exact B4].
  unfold PSM2.flds in *. cbn [combine forallb fst snd] in B1. repeat (let Q := fresh "Q" in apply andb_prop in B1 as [Q B1]; apply expr_eqb_eq in Q; rewrite Q). reflexivity.
Qed.
Lemma flds_inj : forall a b, PSM2.flds a = PSM2.flds b -> a = b.
Proof. intros [] [] H. unfold PSM2.flds in H. cbn in H. injection H as -> -> -> -> -> -> -> -> -> -> -> ->. reflexivity. Qed.

Lemma rviewp_facts : forall i c ps j nxj pv lv pe ce d, PSM5.rviewp i c ps j nxj = Some (pv, lv, pe, ce, d) ->
  PSM2.ldelta i c ps = Some (pv, lv, pe, ce, d) /\ PSM2.vw j = Some (PSM5.set_send lv (APC.eaddz (PB4.pv_send lv) (-1)), pe, ce) /\ forallb (APC.expr_vars_lt nxj) (pe :: ce :: PSM2.flds lv) = true.
Proof.
  intros i c ps j nxj pv lv pe ce d H. unfold PSM5.rviewp in H. destruct (PSM2.ldelta i c ps) as [[[[[pv0 lv0] pe0] ce0] d0]|]; [|discriminate]. destruct (PSM2.vw j) as [[[pvj pej] cej]|]; [|discriminate].
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection H as -> -> -> -> ->.
  apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B2, B3. subst pej cej.
  split; [reflexivity|]. split; [|exact B4]. f_equal. f_equal. f_equal. apply flds_inj.
  unfold PSM2.flds in *. cbn [combine forallb fst snd] in B1. repeat (let Q := fresh "Q" in apply andb_prop in B1 as [Q B1]; apply expr_eqb_eq in Q; rewrite Q). reflexivity.
Qed.
Lemma same_state_facts : forall d, PSM5.same_state d = true -> PSM2.d_st d = None /\ PSM2.d_sst d = None /\ PSM2.d_nst d = None /\ PSM2.d_more d = None /\ PSM2.d_done d = None /\ PSM2.d_clr d = false.
Proof.
  intros d H. unfold PSM5.same_state in H. destruct (PSM2.d_st d); [discriminate|]. destruct (PSM2.d_sst d); [discriminate|]. destruct (PSM2.d_nst d); [discriminate|]. destruct (PSM2.d_more d); [discriminate|].
  destruct (PSM2.d_done d); [discriminate|]. destruct (PSM2.d_clr d); [discriminate|]. repeat split.
Qed.
Lemma bytes_prefix : forall (M : mem) p (s1 s2 : list Z), L5.bytes_at RSEGS M p (s1 ++ s2) -> L5.bytes_at RSEGS M p s1.
Proof. intros M p s1 s2 H q Hq. pose proof (H q ltac:(rewrite length_app; lia)) as X. rewrite app_nth1 in X by exact Hq. exact X. Qed.

Lemma wf_last : forall ps, PML.wf_ps ps -> PML.ps_more ps = true -> exists rest x, PML.ps_stack ps = rest ++ [x] /\ 0 <= x <= 28.
Proof.
  intros ps (_ & _ & _ & _ & C & T & Hs & HC & HM) Hm. destruct (HM Hm) as (_ & _ & _ & HT & _).
  destruct HT as [[-> _]|[[-> _]|[(S & HS & -> & _)|(S & HS & -> & _)]]].
  - rewrite app_nil_r in Hs. induction C as [|y C' _] using rev_ind.
    + exists [], PML.ST_ROOT. split; [exact Hs | unfold PML.ST_ROOT; lia].
    + exists (PML.ST_ROOT :: C'), y. split; [exact Hs|]. apply Forall_app in HC as [_ HC2]. inversion HC2 as [|y' l' Hy _]; subst.
      unfold PML.is_container, PML.ST_OBJECT, PML.ST_ARRAY in Hy. lia.
  - exists (PML.ST_ROOT :: C), PML.ST_MEMBER_NAME. split; [exact Hs | unfold PML.ST_MEMBER_NAME; lia].
  - exists (PML.ST_ROOT :: C), S. split; [exact Hs|]. unfold PML.is_expect in HS. cbn [In] in HS. lia.
  - exists (PML.ST_ROOT :: C ++ [S]), PML.ST_SLASH_STAR. split; [rewrite Hs; cbn [app]; rewrite <- app_assoc; reflexivity | unfold PML.ST_SLASH_STAR; lia].
Qed.

Section F.
Context {SCFG_P : ScfgP}.
Variable I : PSI.inst.
Local Abbreviation L := (PSI.iL I).      Local Abbreviation HI := (PSI.iHI I).    Local Abbreviation LBo := (PSI.iLBo I).  Local Abbreviation cr := (PSI.icr I).
Local Abbreviation sp := (PSI.isp I).    Local Abbreviation r := (PSI.ir I).      Local Abbreviation P := (PSI.iP I).      Local Abbreviation V := (PSI.iV I).      Local Abbreviation E := (PSI.iE I).
Local Abbreviation B := (PSI.iB I).      Local Abbreviation kx := (PSI.ikx I).    Local Abbreviation bx := (PSI.ibx I).    Local Abbreviation g := (PSI.ig I).      Local Abbreviation ps := (PSI.ips I).
Local Abbreviation fx := (PSI.ifx I).    Local Abbreviation R := (PSI.iR I).      Local Abbreviation M := (PSI.iM I).      Local Abbreviation model := (PSI.imodel I).  Local Abbreviation K := (PSI.iK I).
Local Abbreviation HIok := (PSI.iHIok I).  Local Abbreviation LAY := (PSI.iLAY I).
Local Abbreviation E0 := (PSI.E0 I).     Local Abbreviation W := (PSI.W I).       Local Abbreviation Cred := (PSI.Cred I). Local Abbreviation XI := (PSI.XI I).
Local Abbreviation seg := (PSI.seg I).   Local Abbreviation wend := (PSI.wend I). Local Abbreviation wlen := (PSI.wlen I). Local Abbreviation st0 := (PSI.st0 I).
Local Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred).
Local Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred XI).
Local Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.
Hypothesis SETEC_OK : PMS.set_ec_spec L.

Lemma EADDR : estart E0 (SA Eb 0) = E.
Proof. unfold estart. cbn [a_base a_off edenot Eb]. pose proof (PSI.UU I) as (_ & _ & _ & U12 & _). rewrite U12. lia. Qed.
Lemma EOBJ : sp <= E /\ E + 16 <= hl_sptop L /\ E mod 8 = 0.
Proof. exact (PSI.iOE I). Qed.
Lemma SETEC_W_in : forall w a, In w (PB2.SETEC_W E) -> L5.in_rng w a -> exists w', In w' W /\ L5.in_rng w' a.
Proof. intros w a Hw Hin. exists w. split; [|exact Hin]. unfold PB2.SETEC_W in Hw. unfold PSI.W, PMS.W_parc, PML.W_par. cbn [In app] in *. tauto. Qed.

Lemma img_frame : forall i c k ps1 t E1 E' R' (M1 M' Mx : mem) modelx, is_leaf i c k ps1 t -> HAMB i E1 Mx modelx -> env_agree (CC.cp_nx c) E1 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' ->
  forall a, 0x10000 <= a < 0xf8000 -> M' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Proof.
  intros i c k ps1 t E1 E' R' M1 M' Mx modelx IL HA Hag HLF a Ha. destruct (PSB.leaf_nf _ _ _ _ _ IL) as (_ & Hnf & Hfoot). destruct (PSB.bls2' _ _ _ _ _ IL) as (pe & ce & sbe & sce & HBL).
  destruct (PSB.own_blocks I i E1 Mx modelx pe ce sbe sce HA HBL) as ((C0 & C1 & _) & _). pose proof HA as (_ & _ & HagE & _).
  assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | exact Hnf]]).
  pose proof (PSI.SPF I) as (_ & S2 & _). rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in C1.
  apply (PSB.frame_low I i c E1 E' M1 M' pe ce _ Hfoot HBL HagE' Hag (CC.lf_frame _ _ _ _ _ _ _ HLF)); [lia | right; lia].
Qed.

Lemma hpres_blk : forall LBk spc scr Wc (M1 M2 : mem) a n (bs : list Z), L5C.hpres L LBk spc scr Wc M1 M2 -> (exists b, In b LBk /\ fst b <= a /\ a + n <= fst b + snd b) -> Z.of_nat (length bs) <= n ->
  0 <= a -> a + n <= 2 ^ 64 -> (forall w, In w Wc -> forall q, a <= q < a + n -> ~ L5.in_rng w q) -> (forall q, a <= q < a + n -> ~ in_errno L q) -> L5.bytes_at RSEGS M1 a bs -> L5.bytes_at RSEGS M2 a bs.
Proof.
  intros LBk spc scr Wc M1 M2 a n bs HP (b & Hb & Hb1 & Hb2) Hn Ha Ha2 HW HE HB. apply (PSB.bytes_frame M1 M2); [|exact HB]. intros q Hq.
  apply (L5C.hpres_kept _ _ _ _ _ _ _ q HP). split; [lia|]. split; [left; exists b; split; [exact Hb | lia]|]. split; [apply HE; lia | intros w Hw; apply (HW w Hw q); lia].
Qed.

Lemma hpres_def : forall LBk spc scr Wc (M1 M2 : mem) a n, L5C.hpres L LBk spc scr Wc M1 M2 -> L5.defined M1 a n -> hl_ceil L <= a -> a + n <= 2 ^ 64 -> L5.defined M2 a n.
Proof.
  intros LBk spc scr Wc M1 M2 a n HP HD Ha Hn q Hq. pose proof (PmLayout.ly_errno L LAY) as HE. pose proof (PSI.SPF I) as (_ & _ & _ & S4 & _). unfold hl_ceil in *.
  destruct (Z_le_dec (spc - scr) (a + q)) as [G1|G1]; [destruct (Z_lt_dec (a + q) spc) as [G2|G2]|].
  - pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP (a + q - (spc - scr)) ltac:(lia)) as Y. replace (spc - scr + (a + q - (spc - scr))) with (a + q) in Y by lia. exact Y.
  - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + q) HP); [lia | right; left; split; lia | unfold in_errno; lia | exact (HD q Hq)].
  - apply (L5C.hpres_cdef _ _ _ _ _ _ _ (a + q) HP); [lia | right; left; split; lia | unfold in_errno; lia | exact (HD q Hq)].
Qed.

Lemma other_facts : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> (GT.NF <= CC.cp_nx c)%nat /\ CH2.blocks_vars_lt (CC.cp_nx c) (nth i G.BLS []) = true.
Proof.
  intros i c k ps1 pc IL. pose proof (CH2.leaves_all_sound _ _ _ heap_ok3 _ _ _ _ _ IL) as X. cbn [CH2.leaf_chk3] in X.
  unfold CH2.foot_chk in X. apply andb_prop in X as [X F4]. apply andb_prop in X as [X F3]. apply Nat.leb_le in F4. split; assumption.
Qed.

Lemma call_common : forall i c k ps1 pc j, is_leaf i c k ps1 (CC.TOther pc) -> CH2.ret_of G.RETS i k = Some j -> forall E1 E' R' (M1 M' : mem), env_agree GT.NF E0 E' -> CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> XI i E1 M1 ->
  (j <> 0%nat -> st0 <> PML.ST_ACCEPT) /\ (PSM2.in_loop j = true -> 1 <= wlen).
Proof.
  intros i c k ps1 pc j IL Hret E1 E' R' M1 M' HagE' HLF HX. pose proof (CH2.leaves_all_sound _ _ _ callc_ok _ _ _ _ _ IL) as X. unfold PSM5.callc_chk in X. rewrite Hret in X. apply andb_prop in X as [X _]. apply andb_prop in X as [GL GN].
  unfold PSI.XI in HX. destruct HX as (_ & X2 & X3 & _). destruct (PSB.FRZ I E' HagE') as (_ & _ & _ & _ & _ & _ & _ & F8' & _). split.
  - intros _. destruct (Nat.eqb_spec i 0) as [->|Hi]; [|exact (X2 Hi)]. pose proof (PSB.ne_chk_sound E' M' _ _ 2 (PSB.leaf_know I c ps1 E' R' M1 M' HLF) GN ltac:(lia)) as X. rewrite F8' in X. exact X.
  - intros Hj. rewrite Hj in GL. apply X3. exact GL.
Qed.

Lemma call_nf : forall i c k ps1 pc j, is_leaf i c k ps1 (CC.TOther pc) -> CH2.ret_of G.RETS i k = Some j -> (GT.NF <= CC.cp_nx (PSM2.cutn j) - APC.NCS - PSM5.ng_of pc)%nat.
Proof.
  intros i c k ps1 pc j IL Hret. pose proof (CH2.leaves_all_sound _ _ _ callc_ok _ _ _ _ _ IL) as X. unfold PSM5.callc_chk in X. rewrite Hret in X. apply andb_prop in X as [_ X]. apply Nat.leb_le in X. exact X.
Qed.
Lemma setec_code : forall c ps1 cj BLi BLj ci code, PB2.setec_chk GT.NF G.HDECL Eb 0 c ps1 cj BLi BLj = Some ci -> nth 11 (CA.ps_reglist ps1) (ELit 0) = ELit code -> 1 <= code <= 31.
Proof.
  intros c ps1 cj BLi BLj ci code H Hc. unfold PB2.setec_chk in H. destruct (split_lit (nth 10 (CA.ps_reglist ps1) (ELit 0))) as [eb ek]. rewrite Hc in H.
  lazymatch type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end.
  apply andb_prop in Hb as [Hb B5]. apply andb_prop in Hb as [Hb B4]. apply andb_prop in Hb as [Hb B3]. apply Z.leb_le in B3, B4. lia.
Qed.
Lemma ps_of_agree : forall lv pe ce E2 E' bm bd stack buf, (forall x, In x (pe :: ce :: PSM2.flds lv) -> uv E2 x = uv E' x) -> PSI.ps_of lv pe ce E2 bm bd stack buf = PSI.ps_of lv pe ce E' bm bd stack buf.
Proof. intros lv pe ce E2 E' bm bd stack buf H. unfold PSI.ps_of. rewrite !H by (unfold PSM2.flds; cbn [In]; tauto). reflexivity. Qed.

Lemma flds_agree : forall lv pe ce E2 E', (forall x, In x (pe :: ce :: PSM2.flds lv) -> uv E2 x = uv E' x) ->
  uv E2 pe = uv E' pe /\ uv E2 ce = uv E' ce /\ uv E2 (PB4.pv_level lv) = uv E' (PB4.pv_level lv) /\ uv E2 (PB4.pv_wend lv) = uv E' (PB4.pv_wend lv) /\ uv E2 (PB4.pv_wptr lv) = uv E' (PB4.pv_wptr lv) /\
  uv E2 (PB4.pv_st lv) = uv E' (PB4.pv_st lv) /\ uv E2 (PB4.pv_sst lv) = uv E' (PB4.pv_sst lv) /\ uv E2 (PB4.pv_nst lv) = uv E' (PB4.pv_nst lv) /\ uv E2 (PB4.pv_more lv) = uv E' (PB4.pv_more lv) /\
  uv E2 (PB4.pv_done lv) = uv E' (PB4.pv_done lv) /\ uv E2 (PB4.pv_size lv) = uv E' (PB4.pv_size lv) /\ uv E2 (PB4.pv_sb lv) = uv E' (PB4.pv_sb lv) /\ uv E2 (PB4.pv_send lv) = uv E' (PB4.pv_send lv) /\
  uv E2 (PB4.pv_scend lv) = uv E' (PB4.pv_scend lv).
Proof. intros lv pe ce E2 E' H. unfold PSM2.flds in H. repeat split; apply H; cbn [In]; tauto. Qed.

Lemma leaf_setec : forall i c k ps1 j, is_leaf i c k ps1 (CC.TOther SETEC) -> CH2.ret_of G.RETS i k = Some j -> CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 j IL Hret.
  pose proof (CH2.leaves_all_sound _ _ _ struct_ok _ _ _ _ _ IL) as XS. unfold struct_chk in XS. change (is_exit_pc SETEC) with false in XS. cbv iota in XS. unfold call_chk in XS. rewrite Hret in XS.
  destruct (nth_error G.CPS j) as [cj|] eqn:Hcj; [|discriminate]. apply andb_prop in XS as [Hpc XS]. apply Z.eqb_eq in Hpc.
  change (SETEC =? VECPUSH) with false in XS. change (SETEC =? PUSHB) with false in XS. change (SETEC =? POP) with false in XS. change (SETEC =? PARENT) with false in XS. rewrite Z.eqb_refl in XS. cbv iota in XS.
  destruct (PB2.setec_chk GT.NF G.HDECL Eb 0 c ps1 cj (nth i G.BLS []) (nth j G.BLS [])) as [ci|] eqn:Hchk; [|discriminate].
  pose proof (CH2.leaves_all_sound _ _ _ setec2_ok _ _ _ _ _ IL) as X2. unfold PSM5.setec_chk2 in X2. rewrite Z.eqb_refl, Hret in X2.
  assert (Hcutj : PSM2.cutn j = cj) by (unfold PSM2.cutn; exact (nth_error_nth _ _ _ Hcj)). rewrite Hcutj in X2.
  assert (KK : (kind_of i = KInv \/ kind_of i = KParent) /\ kind_of j = KSetEc /\ exists pv lv pe ce d, PSM5.rview i c ps1 j (CC.cp_nx cj - APC.NCS)%nat = Some (pv, lv, pe, ce, d) /\ PSM2.d_sst d = None /\ PSM2.d_nst d = None /\ PSM2.d_clr d = false /\
    match PSM2.d_more d with None => true | Some z => (z =? 0) || (z =? 1) end = true /\ match PSM2.d_done d with None => true | Some z => (z =? 0) || (z =? 1) end = true).
  { destruct (kind_of i); try discriminate; (destruct (kind_of j); try discriminate); (destruct (PSM5.rview i c ps1 j (CC.cp_nx cj - APC.NCS)%nat) as [[[[[pv lv] pe] ce] d]|]; [|discriminate]);
      apply andb_prop in X2 as [X2 D5]; apply andb_prop in X2 as [X2 D4]; apply andb_prop in X2 as [X2 D3]; apply andb_prop in X2 as [D1 D2]; (split; [tauto|]); (split; [reflexivity|]); exists pv, lv, pe, ce, d; (split; [reflexivity|]);
      (destruct (PSM2.d_sst d); [discriminate|]); (destruct (PSM2.d_nst d); [discriminate|]); (destruct (PSM2.d_clr d); [discriminate|]); repeat split; assumption. }
  destruct KK as (K1 & K2 & pv & lv & pe & ce & d & HRV & Dsst & Dnst & Dc & Dmore & Ddone).
  destruct (rview_facts _ _ _ _ _ _ _ _ _ _ HRV) as (HLD & pvj & Hvwj & Hflds & Hvars). apply flds_inj in Hflds. subst pvj.
  pose proof (PSI.iHEC I) as (_ & HEd & _).
  apply (PB5.setec_leaf_ok2 L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.U2 I) (PSI.TP0 I) (PSI.W_OK I) (PSI.CRS_OK I) (PSI.WRS_OK I) (PSI.IMG_OK I) G.CPS G.TAGS G.RETS K (PSI.iHKnil I) XI
           (PSI.DEF0 I) (PSI.KXf I) (PSI.BXf I) (PSI.CRED_EQ I) Eb 0 eq_refl E EADDR EOBJ HEd SETEC_W_in SETEC_OK g (PSI.iHG I) i c k ps1 j cj ci IL Hret Hcj Hpc Hchk).
  -
    intros E1 E' R' M1 M' model1 Hag HLF HA' HX. unfold PSI.XI in HX. destruct HX as (_ & _ & _ & HX). rewrite (PSB.lview_vw _ _ _ _ _ _ _ (PSX.ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX.
    assert (HLSg : PML.ls_ok g M1) by (destruct K1 as [K1|K1]; rewrite K1 in HX; destruct HX as (bm & bd & stack & buf & _ & Q & _); exact Q).
    exact (PSB.ls_frame M1 M' g (img_frame i c k ps1 _ E1 E' R' M1 M' M' model1 IL HA' Hag HLF) (PSI.iHG I) HLSg).
  -
    intros E1 E' R' M1 M' model1 E2 M2 code HagE' Hag HLF HA' HX Hag2 Hcode HEC2 HLS2 HPRES.
    destruct (call_common i c k ps1 _ j IL Hret E1 E' R' M1 M' HagE' HLF HX) as (CM1 & CM2).
    unfold PSI.XI in HX. destruct HX as (X1 & X2' & X3 & HX). rewrite (PSB.lview_vw _ _ _ _ _ _ _ (PSX.ldelta_lview _ _ _ _ _ _ _ _ HLD)) in HX.
    assert (HXc : exists bm bd stack buf, PSI.contents I pv pe ce E1 M1 bm bd stack buf /\ PML.wf_ps (PSI.ps_of pv pe ce E1 bm bd stack buf) /\ PML.buf_bound (PSI.ps_of pv pe ce E1 bm bd stack buf) B).
    { destruct K1 as [K1|K1]; rewrite K1 in HX; destruct HX as (bm & bd & stack & buf & Q1 & _ & Q3 & Q4); exists bm, bd, stack, buf.
      - split; [exact Q1|]. split; [exact Q3 | exact (proj1 Q4)].
      - split; [exact Q1|]. split; [exact Q3 | exact Q4]. }
    destruct HXc as (bm & bd & stack & buf & HC & HW & HB).
    assert (HGR : mem_grows M' M') by (intros x Hx; exact Hx).
    destruct (PSB.leaf_state_g I i c k ps1 _ pv lv pe ce d E1 E' R' M1 M' M' model1 bm bd stack buf IL HLD HA' HGR Hag HLF HC)
      as (_ & HK & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & (AG1 & AG2 & AG3) & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16 & HSB & FR2 & FRI & HPAX & Hden & HEQ).
    rewrite Dsst in L9. rewrite Dnst in L10. rewrite Dc in L13. cbn [PSB.newv] in *.
    pose proof HC as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC6b & HC7 & HC8 & HC9).
    assert (Hnx : CH2.ci_nx ci = (CC.cp_nx cj - APC.NCS)%nat).
    { unfold PB2.setec_chk in Hchk. destruct (split_lit (nth 10 (CA.ps_reglist ps1) (ELit 0))) as [eb ek]. destruct (nth 11 (CA.ps_reglist ps1) (ELit 0)); try discriminate.
      destruct (_ && _)%bool in Hchk; [|discriminate]. rewrite (custom_nx _ _ _ _ _ _ _ _ _ _ _ _ _ Hchk). lia. }
    rewrite Hnx in Hag2.
    assert (AGX : forall x, In x (pe :: ce :: PSM2.flds lv) -> uv E2 x = uv E' x) by (intros x Hx; rewrite forallb_forall in Hvars; exact (PB.uv_agree _ E' E2 x Hag2 (Hvars x Hx))).
    assert (Hbm : exists bm', uv E' (PB4.pv_more lv) = PML.b2z bm').
    { rewrite L11. destruct (PSM2.d_more d) as [z|]; [|exists bm; exact HC8]. cbn [PSB.newv]. apply orb_prop in Dmore as [Q|Q]; apply Z.eqb_eq in Q; subst z; [exists false | exists true]; reflexivity. }
    assert (Hbd : exists bd', uv E' (PB4.pv_done lv) = PML.b2z bd').
    { rewrite L12. destruct (PSM2.d_done d) as [z|]; [|exists bd; exact HC9]. cbn [PSB.newv]. apply orb_prop in Ddone as [Q|Q]; apply Z.eqb_eq in Q; subst z; [exists false | exists true]; reflexivity. }
    destruct Hbm as (bm' & Hbm). destruct Hbd as (bd' & Hbd).

    destruct (other_facts _ _ _ _ _ IL) as (F1 & F2).
    assert (HdenE' : CH2.den E' (nth i G.BLS []) = [(uv E1 pe, uv E1 ce); (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))]) by (rewrite (CH2.den_agree _ E1 E' _ Hag F2); exact Hden).
    destruct (PSB.bls2' _ _ _ _ _ IL) as (pe2 & ce2 & sbe & sce & HBL). destruct (PSB.own_blocks I i E1 M' model1 pe2 ce2 sbe sce HA' HBL) as ((C0 & C1 & C2 & C3 & C4) & (D0 & D1 & D2 & D3 & D4) & _).
    rewrite HBL, !PB.den_cons in Hden. change (CH2.den E1 []) with (@nil (Z * Z)) in Hden. injection Hden as Eb1 Eb2 Eb3 Eb4. rewrite Eb1 in C0, C1, C4. rewrite Eb2 in C1, C4. rewrite Eb3 in D0, D1, D4. rewrite Eb4 in D1, D4.
    pose proof (PSB.CEIL I) as CL. pose proof (PSI.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSI.SPF I) as (_ & S2 & _ & S4 & _).
    rewrite (PmLayout.ly_img_lo L LAY), (PmLayout.ly_img_hi L LAY) in C1, D1. unfold hl_ceil in *.
    assert (KEEP : forall a n (bs : list Z), (a = uv E1 pe /\ n = uv E1 ce) \/ (a = uv E1 (PB4.pv_sb pv) /\ n = uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv)) -> Z.of_nat (length bs) <= n ->
                   L5.bytes_at RSEGS M' a bs -> L5.bytes_at RSEGS M2 a bs).
    { intros a n bs Hab Hn HBs. apply (hpres_blk _ _ _ _ M' M2 a n bs HPRES); [| exact Hn | destruct Hab as [[-> ->]|[-> ->]]; lia | destruct Hab as [[-> ->]|[-> ->]]; lia | | | exact HBs].
      - rewrite HdenE'. destruct Hab as [[-> ->]|[-> ->]]; [exists (uv E1 pe, uv E1 ce) | exists (uv E1 (PB4.pv_sb pv), uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))]; cbn [fst snd]; (split; [cbn [In app]; tauto | lia]).
      - intros w Hw q Hq. unfold PB2.SETEC_W in Hw. unfold L5.in_rng. destruct Hw as [<-|[<-|[<-|[]]]]; cbn [fst snd]; destruct Hab as [[-> ->]|[-> ->]]; lia.
      - intros q Hq. unfold in_errno. rewrite (PmLayout.ly_errno L LAY). destruct Hab as [[-> ->]|[-> ->]]; lia. }
    unfold PSI.XI. rewrite K2, Hvwj.
    split; [rewrite PSI.SCRV in *; apply (hpres_def _ _ _ _ _ _ _ _ HPRES); [apply (PSB.grows_def M1 M'); [exact (CC.lf_grows _ _ _ _ _ _ _ HLF) | replace (sp - 10096) with (sp + - 10096) by lia; exact X1] | lia | lia]|].
    split; [exact CM1|]. split; [exact CM2|].
    destruct (HPAX bm' bd' Hbm Hbd) as (bufm & HPA & Hlen & _). rewrite L13 in Hlen.
    pose proof (PSB.pa_buf _ _ _ HPA) as HBUF. cbn [PSI.ps_of PML.ps_bptr PML.ps_buf] in HBUF. rewrite L6 in HBUF.
    destruct (flds_agree lv pe ce E2 E' AGX) as (Ape & Ace & Alevel & Awend & Awptr & Ast & Asst & Anst & Amore & Adone & Asize & Asb & Asend & Ascend).
    exists bm', bd', stack, bufm. split.
    { unfold PSI.contents. rewrite Ape, Ace, Awend, Awptr, Ast, Amore, Adone, Asize, Asb, Asend, Ascend. rewrite L2, L3, L4, L5, L7, L6, L13, Hbm, Hbd.
      split; [apply (KEEP _ (uv E1 (PB4.pv_scend pv) - uv E1 (PB4.pv_sb pv))); [right; split; reflexivity | exact HC3 | exact HSB]|].
      split; [exact HC2|]. split; [exact HC3|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros _; apply (KEEP _ (uv E1 ce)); [left; split; reflexivity | lia | exact HBUF]|]. split; reflexivity. }
    split; [exact HLS2|].
    rewrite (ps_of_agree lv pe ce E2 E' false bd' stack bufm AGX), (HEQ false bd' bufm), L9, L10.
    set (psc := PSI.ps_of pv pe ce E1 bm bd stack buf) in *.
    assert (Hwl1 : PML.winlen psc = wend - uv E1 (PB4.pv_wptr pv)) by (unfold psc, PSI.ps_of; rewrite HC4; apply PSB.winlen_of; pose proof (PSI.WIN I) as (W0 & _); lia).
    pose proof (PSB.buf_need_range psc HW) as Hbn. destruct HB as [HB1 HB2]. unfold psc at 1, PSI.ps_of in HB1. cbn [PML.ps_buf] in HB1.
    pose proof (PSI.WIN I) as (W0 & W1 & _).
    split; [apply PSS.wf_stop; [exact HW | exact (proj1 HW) | exact (proj1 (proj2 HW))]|].
    split; [unfold PSS.upd; cbn [PML.ps_buf]; rewrite PSB.winlen_of by lia; lia|].
    split; [exact HB2|].
    split; [exists code; split; [exact HEC2 | exact (setec_code _ _ _ _ _ _ _ Hchk Hcode)]|].
    intros Q; discriminate Q.
Qed.
End F.
End PSF.
