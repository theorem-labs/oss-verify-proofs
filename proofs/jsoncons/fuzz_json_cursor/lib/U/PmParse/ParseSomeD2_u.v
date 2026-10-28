(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutL5 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSums_u ParseSums2_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseSpecs_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmParse Require Import ParseBridges_u ParseBridges2_u ParseBridges3_u ParseBridges4_u ParseBridges5_u ParseSomeAt_u ParseSomeSem_u ParseSomeChk_u ParseSomeChk2_u ParseSomeChk3_u ParseSomeA_u ParseSomeB_u ParseSomeC_u ParseSomeD_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Import PSMC. Import PSR.
Module PSR2.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation uv := PB.uv.

Section D.
Context {SCFG_P : ScfgP}.
Variable I : PSI.inst.
Local Abbreviation L := (PSI.iL I).      Local Abbreviation HI := (PSI.iHI I).    Local Abbreviation LBo := (PSI.iLBo I).  Local Abbreviation cr := (PSI.icr I).
Local Abbreviation sp := (PSI.isp I).    Local Abbreviation r := (PSI.ir I).      Local Abbreviation P := (PSI.iP I).      Local Abbreviation V := (PSI.iV I).      Local Abbreviation E := (PSI.iE I).
Local Abbreviation B := (PSI.iB I).      Local Abbreviation kx := (PSI.ikx I).    Local Abbreviation bx := (PSI.ibx I).    Local Abbreviation g := (PSI.ig I).      Local Abbreviation ps := (PSI.ips I).
Local Abbreviation fx := (PSI.ifx I).    Local Abbreviation R := (PSI.iR I).      Local Abbreviation M := (PSI.iM I).      Local Abbreviation model := (PSI.imodel I).  Local Abbreviation K := (PSI.iK I).
Local Abbreviation HIok := (PSI.iHIok I).  Local Abbreviation LAY := (PSI.iLAY I).
Local Abbreviation E0 := (PSI.E0 I).     Local Abbreviation W := (PSI.W I).       Local Abbreviation Cred := (PSI.Cred I). Local Abbreviation XI := (PSI.XI I).
Local Abbreviation seg := (PSI.seg I).   Local Abbreviation wend := (PSI.wend I). Local Abbreviation wlen := (PSI.wlen I). Local Abbreviation st0 := (PSI.st0 I).  Local Abbreviation more0 := (PSI.more0 I).
Local Abbreviation HAMB := (CH2.heap_amb L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred).
Local Abbreviation AMB3 := (CH2.amb3 L HI GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred XI).
Local Abbreviation is_leaf := (CH2.is_leaf G.CPS G.TAGS).
Let LS : hl_segs L = RSEGS := PmLayout.ly_segs L LAY.

Definition hpc (j : nat) : bool := (Nat.eqb j I_HLO || Nat.eqb j I_HHI || Nat.eqb j I_HN)%bool.
Definition strange (j : nat) (st : Z) : Prop := (j = I_HLO -> 0 <= st <= 16) /\ (j = I_HHI -> 18 <= st <= 255) /\ (j = I_HN -> st = 17).
Definition semv (ps2 : PML.pstate) (jv rk line pos : Z) : list word :=
  map (Z_to_bv 64) [jv; rk; PML.ps_level ps2; PML.ps_st ps2; PML.ps_sst ps2; PML.ps_nst ps2; PML.b2z (PML.ps_more ps2); PML.b2z (PML.ps_done ps2); PML.ps_bcap ps2 / 2;
                    Z.of_nat (length (PML.ps_buf ps2)); PML.ps_bptr ps2; PML.ps_sb ps2; Z.of_nat (length (PML.ps_stack ps2)); PML.ps_scap ps2; line; pos; 0].

Definition NUMS (j : nat) (ps2 : PML.pstate) (jv rk : Z) : Prop :=
  jmin j <= jv <= wlen /\ 0 <= rk <= 3 /\ 0 <= PML.ps_level ps2 <= 1025 /\ (0 <= PML.ps_st ps2 <= 255 /\ 0 <= PML.ps_sst ps2 <= 255 /\ 0 <= PML.ps_nst ps2 <= 255) /\
  (Z.of_nat (length (PML.ps_buf ps2)) < 2 ^ 26 /\ PML.ps_bcap ps2 <= 2 ^ 27) /\ (1 <= Z.of_nat (length (PML.ps_stack ps2)) <= 1027 /\ 66 <= PML.ps_scap ps2 <= 1056) /\ strange j (PML.ps_st ps2).
Definition BLKS (M' : mem) (ps2 : PML.pstate) : Prop :=
  (block_range L (PML.ps_bptr ps2) (PML.ps_bcap ps2) /\ L5.defined M' (PML.ps_bptr ps2) (PML.ps_bcap ps2)) /\ (block_range L (PML.ps_sb ps2) (PML.ps_scap ps2) /\ L5.defined M' (PML.ps_sb ps2) (PML.ps_scap ps2)) /\
  (PML.ps_bptr ps2 + PML.ps_bcap ps2 <= PML.ps_sb ps2 \/ PML.ps_sb ps2 + PML.ps_scap ps2 <= PML.ps_bptr ps2) /\
  ((PML.ps_bptr ps2 + PML.ps_bcap ps2 <= seg \/ seg + wlen <= PML.ps_bptr ps2) /\ (PML.ps_sb ps2 + PML.ps_scap ps2 <= seg \/ seg + wlen <= PML.ps_sb ps2)).

Definition MEASV (j : nat) (jv rk : Z) : Z := if Nat.eqb j I_L0 then 1073741824 else if Nat.eqb j I_L then 64 * jv + 8 * rk + 9 else if Nat.eqb j I_L2 then 64 * jv - 24 else 64 * jv + 8 * rk + 8.
Lemma sem_val : forall regs E' R' sem k z, (k < 17)%nat -> nth k sem (Z_to_bv 64 0) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> uv (mkE2 regs E' R' sem) (EVar (49 + k)) = z.
Proof. intros regs E' R' sem k z Hk Hn Hz. unfold PB.uv. cbn [edenot]. rewrite (mkE2_sem regs E' R' sem k Hk), Hn. apply u64_of_Z. exact Hz. Qed.

Lemma wincells_of : forall jv, 0 <= jv -> (wend = 0 -> jv = 0) -> PSA.wincells (PB4.win_of (wend - jv) wend) = (wend - jv, wend).
Proof. intros jv H0 Hz. unfold PB4.win_of. destruct (Z.eqb_spec wend 0) as [X|X]; cbn [PSA.wincells]; [rewrite X, (Hz X); reflexivity | reflexivity]. Qed.

Lemma reent_inh : forall j i c k ps1 pc, tgt j -> is_leaf i c k ps1 (CC.TOther pc) -> pc = CC.cp_pc (PSM2.cutn j) ->
  (forall X, In X FRZ -> PB.has (SR.ps_cells ps1) X = true /\ APC.kentry_vars_lt GT.NF X = true) /\
  (forall n, In n (seq 1 31) -> (hpc j && Nat.eqb n 11)%bool = false -> live_reg_chk (nth n (CC.cp_regs (PSM2.cutn j)) (ELit 0)) (nth n (CA.ps_reglist ps1) (ELit 0)) = true).
Proof.
  intros j i c k ps1 pc Hj IL Hpc. pose proof (CH2.leaves_all_sound _ _ _ reent_ok _ _ _ _ _ IL) as X. unfold reent_chk in X. rewrite Hpc, (tmpl_pc j Hj) in X.
  assert (Hregs : CC.cp_regs (nth (target_of (if Nat.eqb j I_L0 then L0PC else if Nat.eqb j I_L then LPC else if Nat.eqb j I_L2 then L2PC else HPC)) G.CPS CA.dummy_cp) = CC.cp_regs (PSM2.cutn j)).
  { destruct Hj as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; reflexivity. }
  destruct Hj as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [Nat.eqb I_L0 I_L I_L2 I_HLO I_HHI I_HN] in X, Hregs; cbv beta iota in X;
    (lazymatch type of X with (if ?b then _ else _) = true => change b with true in X end); cbv beta iota zeta in X; apply andb_prop in X as [XF XR]; rewrite forallb_forall in XF, XR;
    (split; [intros Y HY; apply andb_prop; exact (XF Y HY) | intros n Hn H11; specialize (XR n Hn); rewrite Hregs in XR]).
  - exact XR.
  - unfold hpc in H11. cbn [Nat.eqb I_HLO I_HHI I_HN orb andb] in H11. change (HPC =? HPC) with true in XR. cbv iota in XR. rewrite H11 in XR. exact XR.
  - unfold hpc in H11. cbn [Nat.eqb I_HLO I_HHI I_HN orb andb] in H11. change (HPC =? HPC) with true in XR. cbv iota in XR. rewrite H11 in XR. exact XR.
  - unfold hpc in H11. cbn [Nat.eqb I_HLO I_HHI I_HN orb andb] in H11. change (HPC =? HPC) with true in XR. cbv iota in XR. rewrite H11 in XR. exact XR.
  - exact XR.
  - exact XR.
Qed.
Lemma hreg11 : forall j, hpc j = true -> nth 11 (CC.cp_regs (PSM2.cutn j)) (ELit 0) = CURJ.
Proof. intros j H. unfold hpc in H. apply orb_prop in H as [H|H]; [apply orb_prop in H as [H|H]|]; apply Nat.eqb_eq in H; subst j; reflexivity. Qed.

Lemma reent_At : forall j i c k ps1 pc E' R' (M' : mem) ps2 jv rk,
  tgt j -> is_leaf i c k ps1 (CC.TOther pc) -> pc = CC.cp_pc (PSM2.cutn j) ->
  env_agree GT.NF E0 E' -> know_ok RSEGS E' M' (SR.ps_cells ps1) -> regs_ok E' (CA.ps_reglist ps1) R' ->
  PML.parser_at M' P ps2 -> PML.ps_win ps2 = PB4.win_of (wend - jv) wend -> NUMS j ps2 jv rk -> BLKS M' ps2 ->
  PML.u32 M' E 0 -> L5.defined M' (sp - 10096) 10096 ->
  (hpc j = true -> getr R' 11%bv = Z_to_bv 64 (wend - jv)) ->
  exists line pos, let E2 := mkE2 (CC.cp_regs (PSM2.cutn j)) E' R' (semv ps2 jv rk line pos) in
    CC.At (hl_segs L) (PSM2.cutn j) E2 R' M' /\ env_agree GT.NF E0 E2 /\
    bv_unsigned (ev E2 49) = jv /\ bv_unsigned (ev E2 50) = rk /\
    PSI.ps_of (PVJ j) PEJ CEJ E2 (PML.ps_more ps2) (PML.ps_done ps2) (PML.ps_stack ps2) (PML.ps_buf ps2) = ps2 /\
    PSI.contents I (PVJ j) PEJ CEJ E2 M' (PML.ps_more ps2) (PML.ps_done ps2) (PML.ps_stack ps2) (PML.ps_buf ps2) /\
    CH2.den E2 (nth j G.BLS []) = PML.ps_blocks ps2 /\ CC.meas (PSM2.cutn j) E2 = MEASV j jv rk.
Proof.
  intros j i c k ps1 pc E' R' M' ps2 jv rk Hj IL Hpc HagE' HKc HRL HPA Hwin HN HBK HEC Hdef H11.
  destruct HN as (N1 & N2 & N3 & N4 & N5 & N6 & N7). destruct HBK as (BK1 & BK2 & BK3 & BK4).
  pose proof (PSB.pa_def _ _ _ HPA) as HdP.
  destruct (PB2.cell_exists M' (P + 160) 8 ltac:(lia)) as (line & Rl & Hl); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  destruct (PB2.cell_exists M' (P + 168) 8 ltac:(lia)) as (pos & Rp & Hp); [eapply (L5.defined_sub _ _ _ _ _ HdP); cbn; lia|].
  exists line, pos. cbv zeta. set (regs := CC.cp_regs (PSM2.cutn j)). set (sem := semv ps2 jv rk line pos). set (E2 := mkE2 regs E' R' sem).
  pose proof (mkE2_agree regs E' R' sem) as Hag2. fold E2 in Hag2.
  assert (HagE2 : env_agree GT.NF E0 E2) by (eapply CC.env_agree_trans; [exact HagE' | exact Hag2]).
  destruct (PSB.FRZ I E2 HagE2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
  pose proof (PSI.WIN I) as (W0 & W1 & W2 & _ & W4). pose proof (PSI.OBJR I) as (O1 & O2 & O3 & O4 & O5 & O6 & O7). pose proof (PSI.SPF I) as (Hsp16 & S2 & S3 & S4 & _).
  destruct BK1 as ((C0 & C1 & C2 & C3 & C4) & Hdb). destruct BK2 as ((D0 & D1 & D2 & D3 & D4) & Hds). pose proof (PSB.CEIL I) as CL. unfold hl_ceil in *.
  destruct N4 as (N4a & N4b & N4c). destruct N5 as (N5a & N5b). destruct N6 as (N6a & N6b).
  assert (Hb2 : 0 <= PML.ps_bcap ps2 / 2) by (apply Z.div_pos; lia).
  assert (Hb2' : PML.ps_bcap ps2 / 2 <= PML.ps_bcap ps2) by (apply Z.div_le_upper_bound; lia).
  assert (Hjv0 : 0 <= jv) by (unfold jmin in N1; destruct (_ || _)%bool; lia).
  assert (V49 : uv E2 (EVar 49) = jv) by (apply (sem_val regs E' R' sem 0); [lia | reflexivity | lia]).
  assert (V50 : uv E2 (EVar 50) = rk) by (apply (sem_val regs E' R' sem 1); [lia | reflexivity | lia]).
  assert (V51 : uv E2 (EVar 51) = PML.ps_level ps2) by (apply (sem_val regs E' R' sem 2); [lia | reflexivity | lia]).
  assert (V52 : uv E2 (EVar 52) = PML.ps_st ps2) by (apply (sem_val regs E' R' sem 3); [lia | reflexivity | lia]).
  assert (V53 : uv E2 (EVar 53) = PML.ps_sst ps2) by (apply (sem_val regs E' R' sem 4); [lia | reflexivity | lia]).
  assert (V54 : uv E2 (EVar 54) = PML.ps_nst ps2) by (apply (sem_val regs E' R' sem 5); [lia | reflexivity | lia]).
  assert (V55 : uv E2 (EVar 55) = PML.b2z (PML.ps_more ps2)) by (apply (sem_val regs E' R' sem 6); [lia | reflexivity | destruct (PML.ps_more ps2); cbn; lia]).
  assert (V56 : uv E2 (EVar 56) = PML.b2z (PML.ps_done ps2)) by (apply (sem_val regs E' R' sem 7); [lia | reflexivity | destruct (PML.ps_done ps2); cbn; lia]).
  assert (V57 : uv E2 (EVar 57) = PML.ps_bcap ps2 / 2) by (apply (sem_val regs E' R' sem 8); [lia | reflexivity | lia]).
  assert (V58 : uv E2 (EVar 58) = Z.of_nat (length (PML.ps_buf ps2))) by (apply (sem_val regs E' R' sem 9); [lia | reflexivity | lia]).
  assert (V59 : uv E2 (EVar 59) = PML.ps_bptr ps2) by (apply (sem_val regs E' R' sem 10); [lia | reflexivity | lia]).
  assert (V60 : uv E2 (EVar 60) = PML.ps_sb ps2) by (apply (sem_val regs E' R' sem 11); [lia | reflexivity | lia]).
  assert (V61 : uv E2 (EVar 61) = Z.of_nat (length (PML.ps_stack ps2))) by (apply (sem_val regs E' R' sem 12); [lia | reflexivity | lia]).
  assert (V62 : uv E2 (EVar 62) = PML.ps_scap ps2) by (apply (sem_val regs E' R' sem 13); [lia | reflexivity | lia]).
  assert (V63 : uv E2 (EVar 63) = line) by (apply (sem_val regs E' R' sem 14); [lia | reflexivity | lia]).
  assert (V64 : uv E2 (EVar 64) = pos) by (apply (sem_val regs E' R' sem 15); [lia | reflexivity | lia]).
  assert (VCUR : uv E2 CURJ = wend - jv).
  { unfold CURJ. rewrite PB.uv_esub, PB.uv_eadd, V49. change (EVar 32) with SEG. change (EVar 33) with WLEN. rewrite F5, F6. unfold PSI.wlen in *. rewrite (Z.mod_small (seg + (wend - seg))) by lia. replace (seg + (wend - seg) - jv) with (wend - jv) by lia. apply Z.mod_small. lia. }
  destruct (reent_inh j i c k ps1 pc Hj IL Hpc) as (INHF & INHR).
  assert (Hc8 : PML.ps_bcap ps2 mod 8 = 0).
  { pose proof HPA as Q. unfold PML.parser_at in Q. destruct Q as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _). destruct Hs as (_ & Q & _). exact Q. }
  assert (Hk2 : 2 * (PML.ps_bcap ps2 / 2) = PML.ps_bcap ps2).
  { pose proof (Z.div_mod (PML.ps_bcap ps2) 8 ltac:(lia)) as D. rewrite Hc8 in D. rewrite D at 1. replace (8 * (PML.ps_bcap ps2 / 8) + 0) with ((4 * (PML.ps_bcap ps2 / 8)) * 2) by lia. rewrite Z.div_mul by lia. lia. }
  assert (Hstx : uv E2 (stx j) = PML.ps_st ps2).
  { unfold stx. destruct (Nat.eqb_spec j I_HN) as [Hj4|_]; [|exact V52]. destruct N7 as (_ & _ & Q). rewrite (Q Hj4). apply PB2.uv_lit. lia. }
  assert (VCE : uv E2 CEJ = PML.ps_bcap ps2) by (unfold CEJ; rewrite PB.uv_escale, V57, Hk2; apply Z.mod_small; lia).
  assert (VSE : uv E2 (APC.eadd (EVar 60) (EVar 61)) = PML.ps_sb ps2 + Z.of_nat (length (PML.ps_stack ps2))) by (rewrite PB.uv_eadd, V60, V61; apply Z.mod_small; lia).
  assert (VSC : uv E2 (APC.eadd (EVar 60) (EVar 62)) = PML.ps_sb ps2 + PML.ps_scap ps2) by (rewrite PB.uv_eadd, V60, V62; apply Z.mod_small; lia).
  assert (Hmv : uv E2 (MEASX j) = MEASV j jv rk).
  { unfold MEASX, MEASV. unfold jmin in N1. unfold PSI.wlen in *. destruct (Nat.eqb j I_L0) eqn:HjL0; [rewrite PB2.uv_lit by lia; reflexivity|].
    destruct (Nat.eqb j I_L) eqn:HjL; [rewrite PB.uv_eaddz, PB.uv_eadd, !PB.uv_escale, V49, V50; rewrite (Z.mod_small (64 * jv)), (Z.mod_small (8 * rk)), (Z.mod_small (64 * jv + 8 * rk)), Z.mod_small by lia; lia|].
    destruct (Nat.eqb j I_L2) eqn:HjL2; [cbn [orb] in N1; rewrite PB.uv_eaddz, PB.uv_escale, V49; rewrite (Z.mod_small (64 * jv)), Z.mod_small by lia; lia|].
    rewrite PB.uv_eaddz, PB.uv_eadd, !PB.uv_escale, V49, V50; rewrite (Z.mod_small (64 * jv)), (Z.mod_small (8 * rk)), (Z.mod_small (64 * jv + 8 * rk)), Z.mod_small by lia; lia. }
  pose proof HPA as HPA0. unfold PML.parser_at in HPA0.
  destruct HPA0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstr & _ & _ & _ & _ & Hstk & Hsl & _).
  split; [|split; [exact HagE2|]].
  2: { split; [exact V49|]. split; [exact V50|].
       split; [unfold PSI.ps_of, PVJ, PEJ; cbn [PB4.pv_st PB4.pv_sst PB4.pv_nst PB4.pv_level PB4.pv_sb PB4.pv_scend PB4.pv_wptr PB4.pv_wend];
               rewrite Hstx, V53, V54, V51, V60, VSC, VCE, V59, VCUR, F7; clear - Hwin; destruct ps2 as [a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13]; cbn [PML.ps_st PML.ps_sst PML.ps_nst PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PML.ps_sb PML.ps_scap PML.ps_bcap PML.ps_bptr PML.ps_buf PML.ps_win] in *; rewrite Hwin; f_equal; lia|].
       split; [unfold PSI.contents, PVJ, PEJ; cbn [PB4.pv_st PB4.pv_sb PB4.pv_send PB4.pv_scend PB4.pv_wptr PB4.pv_wend PB4.pv_size PB4.pv_more PB4.pv_done];
               rewrite Hstx, V60, VSE, VSC, VCUR, F7, V58, VCE, V59, V55, V56;
               split; [exact Hstk|]; split; [reflexivity|]; split; [lia|]; split; [reflexivity|]; split; [unfold PSI.wlen in *; lia|]; split; [reflexivity|];
               split; [destruct Hstr as (_ & _ & Q); exact Q|]; split; [intros _; exact (PSB.pa_buf _ _ _ HPA) | split; reflexivity]|].
       split; [rewrite (proj1 (proj2 (tmpl_vw j Hj))), !PB.den_cons; change (CH2.den E2 []) with (@nil (Z * Z)); unfold PML.ps_blocks; fold (uv E2 PEJ); unfold PEJ; rewrite V59, VCE, V60, V62; reflexivity|].
       unfold CC.meas. rewrite (tmpl_meas j Hj). exact Hmv. }
  split.
  -
    apply (mkE2_regs regs (hpc j) E' R' sem (CA.ps_reglist ps1)); [| exact HRL | exact INHR |].
    + pose proof slots_ok as Q. rewrite forallb_forall in Q. exact (Q j Hj).
    + intros Hh. rewrite (H11 Hh). replace (nth 11 regs (ELit 0)) with CURJ by (symmetry; exact (hreg11 j Hh)). fold E2.
      transitivity (Z_to_bv 64 (uv E2 CURJ)); [f_equal; rewrite VCUR; lia | unfold PB.uv; apply Z_to_bv_bv_unsigned].
  -
    rewrite LS, (tmpl_eq j Hj). unfold PSK.pkn. unfold know_ok. rewrite !Forall_app. split; [split|].
    +
      assert (Hwc : PSA.wincells (PML.ps_win ps2) = (wend - jv, wend)) by (rewrite Hwin; apply wincells_of; unfold PSI.wlen in *; [unfold jmin in N1; destruct (_ || _)%bool; lia | lia]).
      apply (PSA.pkn_sem_ok CONSTS eq_refl eq_refl (conj eq_refl eq_refl) ltac:(cbn; lia) Pb Vb Eb (EVar 2) SEG WLEN (PXJ j) E2 M' P E V sp seg wlen ps2 line pos 0) with (L := PSI.iL I);
        cbn [PSK.x_level PSK.x_wptr PSK.x_st PSK.x_sst PSK.x_nst PSK.x_more PSK.x_done PSK.x_k PSK.x_size PSK.x_p PSK.x_sb PSK.x_slen PSK.x_scap PSK.x_line PSK.x_pos PSK.x_ec PXJ PSK.c_scr CONSTS];
        try assumption; try (rewrite ?Hwc; cbn [fst snd]; first [assumption | unfold PSI.wlen in *; lia]).
      * apply PB2.uv_lit. lia.
      * exact (PSI.iLAY I).
      * split; [repeat split; assumption | exact Hdb].
      * split; [repeat split; assumption | exact Hds].
    +
      apply Forall_forall. intros X HX. destruct (frz_split X HX) as [->|HF].
      * eapply CL5.kunk_intro with (A := sp - 10096) (N := 10000); [unfold estart; cbn [a_base a_off]; fold (uv E2 (EVar 2)); rewrite F4; lia | apply PSA.elen_lit; lia | lia | lia | lia | eapply (L5.defined_sub _ _ _ _ _ Hdef); lia].
      * destruct (INHF X HF) as [Hh Hv]. exact (SGP.kentry_ok_agree1 RSEGS GT.NF E' E2 M' X Hag2 Hv (PB.has_ok E' M' _ _ HKc Hh)).
    +
      unfold EXT. apply Forall_app. split.
      * assert (Hm : 0 <= uv E2 (MEASX j) <= 4611686018427387904).
        { rewrite Hmv. unfold MEASV. unfold jmin in N1. unfold PSI.wlen in *. destruct (Nat.eqb j I_L0); [lia|]. destruct (Nat.eqb j I_L); [lia|]. destruct (Nat.eqb j I_L2); [cbn [orb] in N1; lia | lia]. }
        repeat (apply Forall_cons); [.. | apply Forall_nil]; apply PSA.krange_uv.
        -- rewrite V49. unfold PSI.wlen in *. lia.
        -- rewrite PB.uv_esub, V49. change (EVar 33) with WLEN. rewrite F6. unfold PSI.wlen in *. rewrite Z.mod_small by lia. lia.
        -- rewrite V50. lia.
        -- exact Hm.
      * apply Forall_app. split.
        -- destruct N7 as (Q2 & Q3 & _). destruct (Nat.eqb_spec j I_HLO) as [Hj2|_]; [constructor; [apply PSA.krange_uv; rewrite V52; exact (Q2 Hj2) | constructor]|].
           destruct (Nat.eqb_spec j I_HHI) as [Hj3|_]; [constructor; [apply PSA.krange_uv; rewrite V52; exact (Q3 Hj3) | constructor] | constructor].
        -- assert (YR : 0 <= 4 * (wend - jv) - jv <= 2251799813685248).
           { unfold PSI.wlen in *. destruct W4 as [[W4 W5]|(ch & Hch & Hc1 & Hc2 & (B0 & _))]; lia. }
           constructor; [|constructor]. apply PSA.krange_uv.
           rewrite PB.uv_esub, PB.uv_escale, VCUR, V49. rewrite (Z.mod_small (4 * (wend - jv))) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Definition SEMF (j : nat) (M' : mem) (ps2 : PML.pstate) (rk : Z) : Prop :=
  PML.ls_ok g M' /\ PML.wf_ps ps2 /\ PML.buf_bound ps2 B /\ PSI.CX I ps2 M' /\ PSI.RANK ps2 <= rk /\ (j = I_L0 -> PSI.eofc I ps2) /\
  st0 <> PML.ST_ACCEPT /\ (PSM2.in_loop j = true -> 1 <= wlen).
Lemma reent_leaf : forall i c k ps1 pc, is_leaf i c k ps1 (CC.TOther pc) -> SR.ps_pc ps1 = pc -> CH2.all_regs_chk ps1 = true ->
  (forall E1 R1 E' R' (M1 M' : mem) model1, CC.At (hl_segs L) c E1 R1 M1 -> HAMB i E1 M1 model1 -> HAMB i E1 M' model1 -> XI i E1 M1 -> env_agree (CC.cp_nx c) E1 E' ->
     CC.leaf_facts (hl_segs L) c ps1 E' R' M1 M' -> env_agree GT.NF E0 E' -> know_ok RSEGS E' M' (SR.ps_cells ps1) -> regs_ok E' (CA.ps_reglist ps1) R' ->
     exists j ps2 jv rk, tgt j /\ pc = CC.cp_pc (PSM2.cutn j) /\ PML.parser_at M' P ps2 /\ PML.ps_win ps2 = PB4.win_of (wend - jv) wend /\ NUMS j ps2 jv rk /\
       CH2.den E1 (nth i G.BLS []) = PML.ps_blocks ps2 /\ PML.u32 M' E 0 /\ (hpc j = true -> getr R' 11%bv = Z_to_bv 64 (wend - jv)) /\ SEMF j M' ps2 rk /\ MEASV j jv rk < CC.meas c E1) ->
  CC.leaf_ok (hl_segs L) G.CPS AMB3 K PML.fp_ok i c ps1.
Proof.
  intros i c k ps1 pc IL Hpc Hall USER.
  apply (PB5.reenter_leaf_ok2 L HI HIok LAY GT.NF E0 M model LBo sp G.HDECL W G.BLS Cred (PSI.STKF I) PSI.SCRP PSI.NF32 (PSI.U2 I) (PSI.W_OK I) (PSI.WRS_OK I) G.CPS G.TAGS K XI heap_ok3 i c k ps1 pc IL).
  intros E1 E' R1 R' M1 M' model1 HAt HA HA' HX Hag HLF.
  destruct (PSB.leaf_nf _ _ _ _ _ IL) as (Hc & Hnf & Hfoot). pose proof HA as (_ & _ & HagE & _).
  assert (HagE' : env_agree GT.NF E0 E') by (eapply CC.env_agree_trans; [exact HagE | eapply CC.env_agree_le; [exact Hag | exact Hnf]]).
  pose proof (PSB.leaf_know I c ps1 E' R' M1 M' HLF) as HKc.
  assert (HRL : regs_ok E' (CA.ps_reglist ps1) R') by exact (CH2.leaf_regs_ok L GT.NF sp G.HDECL (PSI.STKF I) PSI.SCRP PSI.NF32 c ps1 E' R' M1 M' Hall HLF).
  destruct (USER E1 R1 E' R' M1 M' model1 HAt HA HA' HX Hag HLF HagE' HKc HRL) as (j & ps2 & jv & rk & Hj & Hpcj & HPA & Hwin & HN & Hden & HEC & H11 & HSEM & Hmeas).
  destruct (PSB.bls2' _ _ _ _ _ IL) as (pe & ce & sbe & sce & HBL).
  destruct (PSB.own_blocks I i E1 M' model1 pe ce sbe sce HA' HBL) as (BR1 & BR2 & BD1 & BD2 & BA & BCH).
  pose proof Hden as Hden0. rewrite HBL, !PB.den_cons in Hden0. change (CH2.den E1 []) with (@nil (Z * Z)) in Hden0. unfold PML.ps_blocks in Hden0. injection Hden0 as Eb1 Eb2 Eb3 Eb4.
  rewrite Eb1, Eb2 in BR1, BD1, BA, BCH. rewrite Eb3, Eb4 in BR2, BD2, BA, BCH.
  assert (HBK : BLKS M' ps2).
  { split; [split; assumption|]. split; [split; assumption|]. split; [exact BA|].
    pose proof (PSI.WIN I) as (W0 & W1 & W2 & _ & [[W4 W5]|(ch & Hch & Hc1 & Hc2 & _)]).
    - destruct BR1 as (? & _), BR2 as (? & _). unfold PSI.wlen. split; right; lia.
    - destruct (BCH ch Hch) as [Q1 Q2]. unfold PSI.wlen. split; lia. }
  destruct HX as (X1 & _). rewrite PSI.SCRV in X1.
  assert (Hdef : L5.defined M' (sp - 10096) 10096) by exact (PSB.grows_def M1 M' _ _ (CC.lf_grows _ _ _ _ _ _ _ HLF) X1).
  destruct (reent_At j i c k ps1 pc E' R' M' ps2 jv rk Hj IL Hpcj HagE' HKc HRL HPA Hwin HN HBK HEC Hdef H11) as (line & pos & Q). cbv zeta in Q.
  set (E2 := mkE2 (CC.cp_regs (PSM2.cutn j)) E' R' (semv ps2 jv rk line pos)) in *.
  destruct Q as (HAt2 & HagE2 & V49 & V50 & Hps & Hcont & Hden2 & Hm2).
  destruct (tmpl_vw j Hj) as (Hvw & HBLj & Hkj & Hcj).
  exists j, (PSM2.cutn j), E2. split; [exact Hcj|]. split; [rewrite <- Hpcj; symmetry; exact Hpc|]. split; [exact HAt2|]. split; [exact HagE2|].
  split; [unfold CH2.cur; rewrite Hden2, Hden; reflexivity|]. split; [intros cr1 HC; apply (PSI.CRED_BLK I i j E1 E2 cr1); [rewrite Hden2, Hden; reflexivity | exact HC]|].
  split; [|rewrite Hm2; exact Hmeas].
  destruct HSEM as (HS1 & HS2 & HS3 & HS4 & HS5 & HS6 & HS7 & HS8).
  unfold PSI.XI. rewrite Hkj, Hvw. split; [rewrite PSI.SCRV; exact Hdef|]. split; [intros _; exact HS7|]. split; [exact HS8|].
  exists (PML.ps_more ps2), (PML.ps_done ps2), (PML.ps_stack ps2), (PML.ps_buf ps2). rewrite Hps. split; [exact Hcont|]. split; [exact HS1|]. split; [exact HS2|]. split; [exact HS3|]. split; [exact HS4|].
  split; [intros _; rewrite V50; exact HS5 | exact HS6].
Qed.
End D.
End PSR2.
