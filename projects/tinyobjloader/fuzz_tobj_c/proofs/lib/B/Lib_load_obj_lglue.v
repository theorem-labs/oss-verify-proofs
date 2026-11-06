(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "batom"; "ASv"; "bd_subst"; "bitem"; "BI"; "@Corelib.Init.Datatypes"; "cons"; "bool"; "true"; "nil"; "list"; "prod"; "pair"; "app"; "false"; "Some"; "option"; "fst"; "None"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "SLit"; "SPUle"; "ss_facts"; "SVar"; "SAlu"; "holds"; "sv_eqb"; "sobj"; "rm"; "sprop_below"; "ss_next"; "ob_base"; "rw"; "swf"; "ob_hi"; "ob_lo"; "obj_range"; "sprop_eqb"; "ss_objs"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "of_nat"; "opp"; "to_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "pI"; "xLD"; "X_bodyN"; "xLK"; "xLC"; "pNX"; "X_latch"; "entA"; "pT0"; "pLNL"; "pPOS"; "rate_factsLo"; "vsP"; "HNEXT"; "K_body"; "K_loop"; "O_ent"; "pE"; "txt"; "pQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vLEN"; "NP"; "vBUF"; "vCFGp"; "vF"; "vFL"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "X_dp"; "K_dpB"; "K_dpt"; "dpB_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "tvL"; "s_body"; "s_loop"; "rateX600"; "X_bodyNc"; "X_latchA"; "frL"; "tblL"; "A1"; "Xl_objs"; "ent_facts600"; "extraLO"; "jL"; "rate_small"; "tblB"; "ldef"; "tblL0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Stdlib.Lists.List"; "forallb"; "In"; "nth_error"; "existsb"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_below"; "ndesc"; "NDA"; "am_eqb"; "am_subst"; "amode"; "JA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "rd64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "FBx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA"; "pinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "bud_le2"; "carve_ent_stateA"; "carve_site_chk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs"; "decodes"; "lines_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "prove_sprop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "state_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "is_shadowZ";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "carve_stateA"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymSoundW
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Export Lib_load_obj_p0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.

Definition frL : list (sv * Z * sv) := ltac2:(tb__ "0|2|
SdS12S12S1dS0A2M0S1dA2M1S13G0S1dS13S1dS0S55Z5A4S56A4S10G1A1A3").

Definition tvL : list (sv * sv) := tv_k (kL vsP).
Definition jL : nat := 18%nat.

Definition extraLO (o : sobj) : bool := ltac2:(tb__ "0|6|
SeSeL_;M0G0S25S2aVo;A1M1S53A2G0S25S2eVo;A1M2S1fZ0A1M3A2M4S25S2dVo;A1M5S51A2S15Xex2S15Xex2SfG0G0S25G1S54A2G0G4S25G5S1fZ90A1A2S15Xex2S15Xex2SfG0S25G1S22P1cA1A2G0S25G2S1fN10A1A2S25G5G3A2S15Xex2S15Xex2Xex2Xex2").

Definition tblL0 (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S4S11S12S0S0A2M0A1M1G1S2S8bS27Vrho;A1S7Vrho;S3eA2R1A3S2S8cR1S7Vrho;S51A2A2S2S3S0S37S1aG0R1A2A1S7Vrho;S41A2A3G0S3S17G0A1S72G0R2S39S7Vrho;S3dA2A1A3S16G0R1A2A3S32S7Vrho;S42A2S18S0S0R2A3A2F_;Fp;A2A2A2LT;A2").
Definition ldef (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S0S2S32S7Vrho;S3eA2M0R1A2S34R1S33G0S35Z10S7Vrho;S40A2A2A2A2A2S6S3S17S74Q8A1M1A1S27Vrho;S75Q40R2A2A2S19G1A1A3A1F_;Fz;").
Definition tblL (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S2S6eVrho;A1S6dVrho;A1A2").
Definition V_L : list positive := ltac2:(tb__ "0|0|
SdS1P1d2SdS1PeSdS1P1d3SdS1P1ccSdS1P1eaSdS1P1d4S10S1A1A3A3A3A3A3A3").

Definition tblB (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S2S65Vrho;A1S2S3S17S0A1M0S82S27Vrho;A1M1S33S7Vrho;S3eA2S35Z10S7Vrho;S3dA2A2A2M2A2S16S0S7Vrho;S47A2A2A3S3G0S82G1S33G2Z8A2A2S16S0S7Vrho;S46A2A2A3A2A2").
Definition V_B : list positive := ltac2:(tb__ "0|0|
SdS1P1d2SdS1PeSdS1P1d3SdS1P1ccSdS1P1eaSdS1P1e0SdS1P1e1SdS1P1d4S10S1A1A3A3A3A3A3A3A3A3").

Ltac rdv HV v e := assert (uval _ e = uval _ e) by (unfold uval, e; cbn [eval]; rewrite <- (HV v%positive) by (cbn; tauto); reflexivity).
Lemma uval_rw : ltac2:(tb__ "0|0|
S1eS1eS1S1dS3S1dR1S22R2A1A3S3S74Q40A1S2bR5R3A2S2bR4R3A2A3S3S0S7R5R3A2S7R6R3A2A3F_;F_;Fe;Fv;Frho';Frho;").
Proof. intros rho rho' v e -> H. unfold uval. cbn [eval]. rewrite H. reflexivity. Qed.

Lemma tblL_reads : phi_reads V_L tblL.
Proof.
  intros rho rho' HV _ HM [(T & H1 & H2 & H3 & H4) HD]. split.
  - exists T.
    rewrite (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 14 vLEN eq_refl ltac:(apply HV; cbn; tauto)),
            (uval_rw rho rho' 467 xLC eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 460 pI eq_refl ltac:(apply HV; cbn; tauto)),
            (uval_rw rho rho' 490 pNX eq_refl ltac:(apply HV; cbn; tauto)).
    split; [|split; [exact H2 | split; [exact H3 | exact H4]]]. eapply decodes_ext; [|exact H1]. intros z _. symmetry. apply HM.
  - intros z Hz. rewrite <- HM. apply HD.
    rewrite <- (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), <- (uval_rw rho rho' 468 xLK eq_refl ltac:(apply HV; cbn; tauto)). exact Hz.
Qed.
Lemma tblB_reads : phi_reads V_B tblB.
Proof.
  intros rho rho' HV HL HM (HT & H1 & H2). split; [|split].
  - eapply tblL_reads; [| exact HL | exact HM | exact HT]. intros v Hv. apply HV. cbn in Hv |- *. tauto.
  - rewrite (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 460 pI eq_refl ltac:(apply HV; cbn; tauto)),
            (uval_rw rho rho' 480 pPOS eq_refl ltac:(apply HV; cbn; tauto)).
    rewrite (rd64_ext (rm rho) (rm rho')); [exact H1|]. intros z _. symmetry. apply HM.
  - rewrite (uval_rw rho rho' 466 xLD eq_refl ltac:(apply HV; cbn; tauto)), (uval_rw rho rho' 460 pI eq_refl ltac:(apply HV; cbn; tauto)),
            (uval_rw rho rho' 481 pLNL eq_refl ltac:(apply HV; cbn; tauto)).
    rewrite (rd64_ext (rm rho) (rm rho')); [exact H2|]. intros z _. symmetry. apply HM.
Qed.

Definition ent_facts600 : list sprop := ltac2:(tb__ "0|3|
SdS1cS20S23S58S22P258A1M0S22P259A1M1A3S51A2SdS1cS20G0S1fZ4000000A1M2A2SdS1cS20G1G2A2SdS1cS20S42G0A2SdS1cS20S1fZ1000A1S3eA2S10S1cA1A3A3A3A3A3").

Definition rateX600 : list sprop := ltac2:(tb__ "0|0|
S48S23S58S23S58S22P258A1S22P259A1A3S1fZ1A1A3S49A2").
Definition rate_small : list sprop := ltac2:(tb__ "0|2|
S14S1cSdS1cS20S42S22P258A1M0A2SdS1cS20G0S1fZ4000000A1M1A2SdS1cS20S22P259A1G1A2S10S1cA1A3A3A3S48S42S49A2A3").
Lemma rateX600_chk : ltac2:(tb__ "0|0|
S3SeS70S1cS8eS6bA1S61A3SfA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma rateX600_sound : ltac2:(tb__ "0|0|
S1eS57S1cS24R1A1S6bA3S57S1cS24R2A1S61A3F_;Frho;").
Proof.
  intros rho HF. apply Forall_forall. intros f Hf. apply (prove_sprop_sound rho rate_small f HF).
  exact (proj1 (forallb_forall _ _) rateX600_chk f Hf).
Qed.
Definition X_bodyNc : axst := Eval vm_compute in ax_add_facts (ent_facts600 ++ rateX600) (carve_ent_stateA X_bodyN (entA pI)).
Definition s_body : wsub := ltac2:(tb__ "0|1|
SdS12S1S1dA2M0S13S1S1dP1e0S22P258A1A4SdG0S13S1S1dP1e1S22P259A1A4S10G0A1A3A3").

Definition Xl_objs : list sobj := Eval vm_compute in removelast (ss_objs (ax_S X_latch)).
Definition X_latchA : axst := Eval vm_compute in drop_lastA X_latch Xl_objs.
Definition s_loop : wsub := ltac2:(tb__ "0|2|
SdS12S1S1dA2M0S13S1S1dP1ccS23S58S3dS1fZ1A1M1A3A4SdG0S13S1S1dP1eaS23S58S4eG1A3A4S10G0A1A3A3").

Definition A1 : Z := 904.
Definition LA (c : Z) : bitem := ltac2:(tb__ "0|1|
ScZ1Z0SdS12S0S8A2M0S13S0S8S66S9S51A1A4SdG0S13S0S8S38S66A1S9S42A1A4S10G0A1A3A3Vc;A4").
Goal bud_le2 (ss_facts (ax_S X_latchA)) (bd_subst s_loop [LA A1]) [LA 0] = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma lglue_checks2 : ltac2:(tb__ "0|0|
S2S3S11S26A1S31S3aS43A1A1S14S26S67SdS26S4dS3dS47S46A3S10S26A1A3A3A3S2S3S3bS95S43S67A2S63A3S2S3SeS3cS63S4cS60A3SfA3S2S3SeS81S60S52A2SfA3S3SeS83S60S5eS5eA3SfA3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma lglue_checks : ltac2:(tb__ "0|3|
S2S3S17S12S1dS1dA2M0A1S72G0S5eS6aA3S16G0S13S1dS1dS3eS76Z10M1S40A2A4A2A3S2S3SeS2cS3aS94S3fS44S3dA1M2S1fG1A1A3A1A1SfA3S2S3SeS88S3fS5eS64S6aS69A5SfA3S2S3SeS3cS62S4bS5fA3SfA3S2S3SeS81S5fS52A2SfA3S2S3SeS83S5fS5eS5eA3SfA3S2S3SeS70S1cS28S29S3aS87S3fG2A2A1A1A1S14S1cS68S61A3A3SfA3S3SeS70S1cS1cS73S1cS30R1A1S21S3aS3fA1A1A3Lf;S48S42S49A2A3SfA3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma ent_addr : ltac2:(tb__ "0|7|
S1eS57S1cS24R1A1S21S3aS3fA1A1A3S2S3S0S7R2S44S3dA1A2S33S7R2S3eA2M0S35Z10M1S7R2S3dA2M2A2A2A3S2S34G2S7R2S41A2M3A2S2S32G3S7R2S40A2M4A2S2S32S35G1G4A2M5ZffffffffA2S2S32G0S36Z2M6Z2fA2A2S2S3S0S7R2S76G1S40A2A2G5A3S32S7R2S51A2S36G6Z1aA2A2A2A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF.
  factz HF (SPUlt pI xLC) H1. factz HF (SPUle xLC xLK) H2. factz HF (SPUle xLK (SLit 4294967295)) H3. factz HF (SPUle (kb 16 xLK) (SLit 4294967295)) H4.
  factz HF (SPUle xLD (SLit 140737488355328)) H5. factz HF (SPUle vLEN (SLit 67108864)) H6.
  rewrite uval_lit in H3, H4, H5, H6 by lia.
  assert (EK : uval r (kb 16 xLK) = 16 * uval r xLK) by (unfold kb; apply uval_mul_lit; lia). rewrite EK in H4.
  assert (EI : uval r (SMd M_MUL (SLit 16) pI) = 16 * uval r pI) by (apply uval_mul_lit; lia).
  unfold entA. rewrite uval_add_small by (rewrite EI; lia). rewrite EI. repeat split; lia.
Qed.

Lemma ent_range : ltac2:(tb__ "0|3|
S1eS57S1cS24R1A1S21S3aS3fA1A1A3S2S32S7R2S3eA2M0S7R2S44S3dA1A2M1A2S32S33G1Z10M2A2S33G0S7R2S76G2S40A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF. destruct (ent_addr r HF) as (E1 & H1 & H2 & H3 & H4 & EK & _). pose proof (uval_range r pI). rewrite E1, EK. lia.
Qed.

Lemma ent_addrX : ltac2:(tb__ "0|7|
S1eS57S1cS24R1A1S21S3aS43A1A1A3S2S3S0S7R2S44S3dA1A2S33S7R2S3eA2M0S35Z10M1S7R2S3dA2M2A2A2A3S2S34G2S7R2S41A2M3A2S2S32G3S7R2S40A2M4A2S2S32S35G1G4A2M5ZffffffffA2S2S32G0S36Z2M6Z2fA2A2S2S3S0S7R2S76G1S40A2A2G5A3S32S7R2S51A2S36G6Z1aA2A2A2A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF.
  factz HF (SPUlt pI xLC) H1. factz HF (SPUle xLC xLK) H2. factz HF (SPUle xLK (SLit 4294967295)) H3. factz HF (SPUle (kb 16 xLK) (SLit 4294967295)) H4.
  factz HF (SPUle xLD (SLit 140737488355328)) H5. factz HF (SPUle vLEN (SLit 67108864)) H6.
  rewrite uval_lit in H3, H4, H5, H6 by lia.
  assert (EK : uval r (kb 16 xLK) = 16 * uval r xLK) by (unfold kb; apply uval_mul_lit; lia). rewrite EK in H4.
  assert (EI : uval r (SMd M_MUL (SLit 16) pI) = 16 * uval r pI) by (apply uval_mul_lit; lia).
  unfold entA. rewrite uval_add_small by (rewrite EI; lia). rewrite EI. repeat split; lia.
Qed.
Lemma ent_rangeX : ltac2:(tb__ "0|3|
S1eS57S1cS24R1A1S21S3aS43A1A1A3S2S32S7R2S3eA2M0S7R2S2aS4dS3dS47S46A3A1A2M1A2S32S33G1Z10M2A2S33G0S7R2S76G2S40A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF. cbn [ob_base O_ent]. destruct (ent_addrX r HF) as (E1 & H1 & H2 & H3 & H4 & EK & _). pose proof (uval_range r pI). rewrite E1, EK. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S97S1eS11S74Q40A1A1S8aOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S96S59VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S89VCST;R1A2S2S32Z0R2A2S34R2S80A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S89VXGL;R1A2S2S32Z0R2A2S34R2S80A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S11S12S12S0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 7 BX.
Variable PA : AA -> Prop.
Let HNP : NP_okA NP := NP_okA_intro NP eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 : ltac2:(tb__ "0|0|
S1eOFr;") := ltac2:(tb__ "0|0|
S8dVCST;VFB;VFF;A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S7dVAInv;VCST;VXGL;S52VKc;Vrho0;VP0;VFB;VFF;VBX;VPA;Vnd;Ac").

Lemma extraLO_sound : ltac2:(tb__ "0|1|
S1eS11S26A1S11S12S1dS1dA2A1S11S12S12S1dS0A2S1dA2A1S26S0S8fS52Vrho0;R6A3VP0;Vrho0;A1S71S26R4R7A3S3SeS69R5A1SfA3S2S32S18S0S0S2fRaR6A2M0A3R5A2S34R5S1bS0S0G0A3A2A2S5S92VCST;Vrho0;S84VFB;RbR9A3S91VFF;RbR8A3R6A5S5S2S32Z0R6A2S34R6S80A2A2S93R6A1A2A2F_;F_;F_;F_;F_;Fa;Fo;Ffr;Ftv';Fobjs;Frho;").
Proof.
  intros rho objs tv' fr o a Hav (P1 & P2 & P3) _ HE Hr. left.
  assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
  { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
  apply (pclMA_mono CST rho0 FB (FBx FB rho tv') FF (FFx FF rho fr) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
  unfold extraLO in HE. apply lazy_orb_prop in HE as [HE|HE]; [|apply lazy_orb_prop in HE as [HE|HE]];
    apply lazy_andb_prop in HE as [Hb HE]; apply lazy_andb_prop in HE as [Hl Hh]; apply sv_eqb_sound in Hb; apply sv_eqb_sound in Hl; apply sv_eqb_sound in Hh;
    unfold obj_range, obj_lo_of, obj_hi_of in Hr; rewrite Hb, Hl, Hh in Hr; cbn [fst snd] in Hr.
  - apply P1. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)).
    rewrite soff_lit_small in Hr by lia. pose proof (uval_range rho vLEN) as RL.
    assert (HL : soff rho vLEN <= uval rho vLEN).
    { unfold soff, uval. rewrite bv_signed_U. destruct (Zsigned_spec (bv_unsigned (eval rho vLEN))) as [[_ X]|[_ X]]; rewrite X; lia. }
    unfold uval in *. lia.
  - apply P2. rewrite <- (AG 15%positive vCFGp eq_refl ltac:(reflexivity)). rewrite !soff_lit_small in Hr by lia. unfold uval in *. lia.
  - apply P3. rewrite <- (AG 28%positive (SVar 28) eq_refl ltac:(reflexivity)). rewrite !soff_lit_small in Hr by lia. unfold uval in *. lia.
Qed.

Lemma nd_below_mono : ltac2:(tb__ "0|0|
S1S1S78S98R3R2A2S3SeS77R4R2A2SfA3S3SeS77R4R3A2SfA3F_;F_;Fnd;Fm;Fn;").
Proof.
  intros n m [tv fr bd am] Hle H. unfold nd_below in *. cbn [nd_tv nd_fr nd_bd nd_am] in *.
  apply andb_prop in H as [H Hlen].
  apply andb_prop in H as [H Ham]. apply andb_prop in H as [H Hbd]. apply andb_prop in H as [Htv Hfr].
  apply andb_true_intro; split; [|exact Hlen].
  repeat (apply andb_true_intro; split).
  - unfold tv_below in *. apply forallb_forall. intros t Ht. pose proof (proj1 (forallb_forall _ _) Htv t Ht) as X.
    apply andb_prop in X as [X1 X2]. apply andb_true_intro. split; eapply sv_below_mono; eauto.
  - unfold fr_below in *. apply forallb_forall. intros t Ht. pose proof (proj1 (forallb_forall _ _) Hfr t Ht) as X.
    apply andb_prop in X as [X1 X2]. apply andb_true_intro. split; eapply sv_below_mono; eauto.
  - unfold bd_below in *. apply forallb_forall. intros it Hit. pose proof (proj1 (forallb_forall _ _) Hbd it Hit) as X.
    apply forallb_forall. intros ca Hca. pose proof (proj1 (forallb_forall _ _) X ca Hca) as Y. eapply sv_below_mono; eauto.
  - destruct am as [|h b|h nx c sl|h g]; cbn [am_below] in *; try reflexivity.
    + eapply sv_below_mono; eauto.
    + apply andb_prop in Ham as [Ham Hsl]. apply andb_prop in Ham as [Ham H3]. apply andb_prop in Ham as [H1 H2].
      repeat (apply andb_true_intro; split); try (eapply sv_below_mono; eauto).
      apply forallb_forall. intros ps Hps. pose proof (proj1 (forallb_forall _ _) Hsl ps Hps) as Y. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro. split; eapply sv_below_mono; eauto.
    + apply andb_prop in Ham as [H1 H2]. apply andb_true_intro. split; eapply sv_below_mono; eauto.
Qed.

Lemma X_bodyNc_eq : ltac2:(tb__ "0|1|
S3S3bS62S7fS87S3fS44S3dA1A2M0S14S1cS14S1cS68S61A3S21S3aG0A1A1A3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma body_carve : ltac2:(tb__ "0|0|
S11SbA1S7cS1eS11S74Q40A1A1S7eS79S5eS64R5R4A4S78S3SeS77S4aR1A2SfA3S3SeS86S21S3aS62A1A1SaS5fR7A2R7A3SfA3S3SeS7aS7bS5fR7A2R7A2SfA3S65R7A1S6fS59VJAv;R5A1S3fR8R7R6A6S4S1eS1eS2S6cR1A1S2S6fS59VJAv;R7A1S4bR1R9R8A6S2S3S0S7R1S41A2S7RaS41A2A3S3S0S7R1S3dA2S7RaS3dA2A3A2A2A2Lrho2;A2F_;F_;F_;F_;F_;Tnd;Fw;Ftp;Frho;Fam;Fbd;").
Proof.
  intros bd am rho tp w nd Hnb Hbud Ham [HT HDEF] HS. destruct w as [tr [ms md]].
  pose proof lglue_checks as (Cnth & Cwf & Csite & Cent & Cid & Ctv & Cfb).
  pose proof (smatchA_facts segs _ _ _ _ (proj1 HS)) as HF.
  destruct (ent_addr rho HF) as (EA & Hi & Hck & Hk32 & Hd47 & EK & HL26).
  destruct HT as (T & HD & HOK & HLEN & HNX).
  pose proof (uval_range rho pI) as RI. pose proof (uval_range rho xLD) as RD.
  destruct (nth_error T (Z.to_nat (uval rho pI))) as [p|] eqn:Ep.
  2: { exfalso. apply nth_error_None in Ep. lia. }
  pose proof (decodes_nth _ _ _ _ _ HD Ep) as [R0 R1]. rewrite Z2Nat.id in R0, R1 by lia. cbn [fst snd] in R0, R1.
  destruct (lines_entry_bounds T _ _ p HOK Ep) as (Q0 & Q1 & QL).
  destruct (JA_carve_ent segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PA HKc HNP tvL frL bd am jL xLD (kb 16 xLK) (entA pI) X_bodyN rho tp tr ms md
              Cnth eq_refl Cwf ltac:(apply (proj1 (Pos.leb_le _ _)); reflexivity) Hnb ent_range) as (rho1 & Hag & V0 & V1 & SP1).
  { apply (carve_site_chk_sound segs AInv CST ALA HCST NP rho0 P0 FB FF X_bodyN tvL frL jL extraLO rho Csite).
    intros Ai tp1 md1 _ HP0 Hav _ _ _ _ _ _ _ _ _ o a Ho HE Hr. exact (extraLO_sound rho _ _ _ o a Hav HP0 Ho HE Hr). }
  { intros z Hz. rewrite EA in Hz. apply (decodes_defined _ _ _ z HD). lia. }
  { exact HS. }
  change (ss_next (ax_S X_bodyN)) with 600%positive in V0, V1, Hag, SP1.
  rewrite EA in V0, V1. rewrite R0 in V0. rewrite R1 in V1. injection V0 as V0. injection V1 as V1.
  change (Pos.succ 600) with 601%positive in V1.
  pose proof Hag as (AGw & AGl & AGm).
  assert (AG : forall v e, e = SVar v -> (v < 600)%positive -> uval rho1 e = uval rho e).
  { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (AGw v Hv). reflexivity. }
  pose proof (uval_range rho1 (SVar 600)) as R600. pose proof (uval_range rho1 (SVar 601)) as R601.

  assert (H4096 : 4096 <= uval rho xLD).
  { pose proof (proj2 HS) as HJ. unfold JAv in HJ.
    assert (Hin : In (xLD, kb 16 xLK) tvL) by (apply (nth_error_In _ _ Cnth)).
    assert (Hnz : tnz rho (xLD, kb 16 xLK)).
    { intro Hd0. destruct HJ as (Ai & kc & HJi). destruct HJi as (_ & _ & _ & _ & _ & _ & (_ & _ & HZ) & _).
      pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as Hz. specialize (Hz ltac:(intros H; exact (H Hd0))).
      unfold tvv in Hz. cbn [snd] in Hz. unfold uval in EK, Hi, Hck, RI. rewrite EK in Hz. lia. }
    pose proof (JA_tv_facts segs AInv CST XGL NP Kc rho0 P0 FB FF BX PA ALA nd rho tp tr md (xLD, kb 16 xLK) eq_refl HJ Hin Hnz) as TF.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail TF)))) as H4. cbn [fst] in H4.
    apply (proj1 (h_ule _ _ _)) in H4. rewrite uval_lit in H4 by lia. exact H4. }

  assert (SP2 : SPA segs (JAv nd) X_bodyNc rho1 tp (tr, mkCfg ms md)).
  { rewrite X_bodyNc_eq. apply (SPA_refacts_JA segs _ rho1 _ _ tp _ SP1).
    - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    - intros tr' md' _ HF1.
      assert (HE : Forall (holds rho1) ent_facts600).
      { unfold ent_facts600.
        constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]; apply (proj2 (h_ule _ _ _)).
        + rewrite uval_add_small by lia. rewrite (AG 14%positive vLEN eq_refl ltac:(reflexivity)). lia.
        + rewrite uval_lit by lia. lia.
        + rewrite uval_lit by lia. lia.
        + rewrite (AG 490%positive pNX eq_refl ltac:(reflexivity)). rewrite <- V0. exact (HNX p eq_refl).
        + rewrite uval_lit by lia. rewrite (AG 466%positive xLD eq_refl ltac:(reflexivity)). exact H4096. }
      apply Forall_app. split; [|exact HF1]. apply Forall_app. split; [exact HE|].
      apply rateX600_sound. unfold rate_small. apply Forall_app. split.
      + constructor; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HE))))|].
        constructor; [exact (Forall_inv (Forall_inv_tail HE))|]. constructor; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HE)))|constructor].
      +
        apply Forall_forall. intros f Hf. apply (proj1 (Forall_forall _ _) HF1).
        pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 lglue_checks))))))) as MEM.
        pose proof (proj1 (forallb_forall _ _) MEM f Hf) as Mf. apply existsb_exists in Mf as (g & Hg & Efg). apply sprop_eqb_sound in Efg. subst g.
        revert Hg. clear. intros Hg. cbn [ax_S carve_ent_stateA]. exact Hg. }
  assert (E466 : uval (rho_sub rho1 s_body) xLD = uval rho1 xLD) by reflexivity.
  assert (E14 : uval (rho_sub rho1 s_body) vLEN = uval rho1 vLEN) by reflexivity.
  assert (E467 : uval (rho_sub rho1 s_body) xLC = uval rho1 xLC) by reflexivity.
  assert (E468 : uval (rho_sub rho1 s_body) xLK = uval rho1 xLK) by reflexivity.
  assert (E460 : uval (rho_sub rho1 s_body) pI = uval rho1 pI) by reflexivity.
  assert (E490 : uval (rho_sub rho1 s_body) pNX = uval rho1 pNX) by reflexivity.
  assert (E480 : uval (rho_sub rho1 s_body) pPOS = uval rho1 (SVar 600)) by reflexivity.
  assert (E481 : uval (rho_sub rho1 s_body) pLNL = uval rho1 (SVar 601)) by reflexivity.
  assert (EM : rm (rho_sub rho1 s_body) = rm rho1) by reflexivity.
  exists (rho_sub rho1 s_body). split; [|split; [|split; [rewrite E467; exact (AG 467%positive xLC eq_refl ltac:(reflexivity)) | rewrite E460; exact (AG 460%positive pI eq_refl ltac:(reflexivity))]]].
  -
    unfold tblB, tblL, tblL0, ldef. rewrite E466, E14, E467, E468, E460, E490, E480, E481, EM.
    rewrite (AG 466%positive xLD eq_refl ltac:(reflexivity)), (AG 14%positive vLEN eq_refl ltac:(reflexivity)), (AG 468%positive xLK eq_refl ltac:(reflexivity)),
            (AG 467%positive xLC eq_refl ltac:(reflexivity)), (AG 460%positive pI eq_refl ltac:(reflexivity)), (AG 490%positive pNX eq_refl ltac:(reflexivity)).
    split; [split|split].
    + exists T. split; [|split; [exact HOK | split; [exact HLEN | intros q Hq; rewrite Ep in Hq; exact (HNX q Hq)]]]. eapply decodes_ext; [|exact HD]. intros z _. symmetry. apply AGm.
    + intros z Hz. rewrite <- AGm. exact (HDEF z Hz).
    + rewrite (rd64_ext (rm rho) (rm rho1)) by (intros z _; symmetry; apply AGm). rewrite R0, V0. reflexivity.
    + rewrite (rd64_ext (rm rho) (rm rho1)) by (intros z _; symmetry; apply AGm). rewrite R1, V1. reflexivity.
  - apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc X_bodyNc K_body s_body nd nd rho1 tp _ Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Ctv | reflexivity | exact Hbud | exact Ham | exact SP2].
    apply (nd_below_mono HNEXT); [apply (proj1 (Pos.leb_le _ _)); reflexivity | exact Hnb].
Qed.

Lemma latch_absorb : ltac2:(tb__ "0|0|
S11SbA1S7cS1eS11S74Q40A1A1S7eS79S5eS64R5R4A4S78S3SeS77S4aR1A2SfA3S3SeS86S21S3aS63A1A1SaS60R7A2R7A3SfA3S3SeS7aS7bS60R7A2R7A2SfA3S6cR7A1S6fS59VJAv;R5A1S43R8R7R6A6S4S1eS1eS2S65R1A1S2S6fS59VJAv;R7A1S4cR1R9R8A6S2S3S0S7R1S41A2S7RaS41A2A3S3S0S7R1S3dA2S7RaS23S58S3dS1fZ1A1A3A2A3A2A2A2Lrho2;A2F_;F_;F_;F_;F_;Tnd;Fw;Ftp;Frho;Fam;Fbd;").
Proof.
  intros bd am rho tp w nd Hnb Hbud Ham ([HT HDEF] & R0 & R1) HS. destruct w as [tr [ms md]].
  pose proof lglue_checks as (Cnth & _). pose proof lglue_checks2 as (Cobjs & Cdrop & Cent & Cid & Ctv).
  pose proof (smatchA_facts segs _ _ _ _ (proj1 HS)) as HF.
  destruct (ent_addrX rho HF) as (EA & Hi & Hck & Hk32 & Hd47 & EK & HL26).
  assert (EB : uval rho (ob_base (O_ent pI pPOS pLNL)) = uval rho xLD + 16 * uval rho pI) by (cbn [ob_base O_ent]; exact EA).
  destruct (JA_absorb_ent_same segs HTOP AInv CST XGL ALA HCST HXGL NP Kc rho0 P0 FB FF BX PA tvL frL bd am jL xLD (kb 16 xLK) X_latch Xl_objs (O_ent pI pPOS pLNL)
              pPOS pLNL rho tp tr ms md Cobjs Cnth eq_refl eq_refl eq_refl ltac:(cbn; auto) ltac:(cbn; auto) ent_rangeX
              ltac:(rewrite EB; exact R0) ltac:(rewrite EB; exact R1) HS) as [SP1 HRM].
  rewrite Cdrop in SP1. set (rho1 := rho_absorb rho [O_ent pI pPOS pLNL] (vms md tp ms)) in *.
  exists (rho_sub rho1 s_loop). split; [|split; [|split; reflexivity]].
  - assert (E466 : uval (rho_sub rho1 s_loop) xLD = uval rho xLD) by reflexivity.
    assert (E14 : uval (rho_sub rho1 s_loop) vLEN = uval rho vLEN) by reflexivity.
    assert (E467 : uval (rho_sub rho1 s_loop) xLC = uval rho xLC) by reflexivity.
    assert (E468 : uval (rho_sub rho1 s_loop) xLK = uval rho xLK) by reflexivity.
    assert (E460 : uval (rho_sub rho1 s_loop) pI = uval rho (SAlu ALU_ADD pI (SLit 1))) by reflexivity.
    assert (E490 : uval (rho_sub rho1 s_loop) pNX = uval rho (SAlu ALU_ADD pE (SLit 1))) by reflexivity.
    assert (EM : rm (rho_sub rho1 s_loop) = rm rho1) by reflexivity.
    unfold tblL, tblL0, ldef. rewrite E466, E14, E467, E468, E460, E490, EM. split; [|intros z Hz; rewrite HRM; exact (HDEF z Hz)].
    destruct HT as (T & HD & HOK & HLEN & HNX).
    pose proof (uval_range rho pI) as RI. pose proof (uval_range rho pPOS) as RP. pose proof (uval_range rho pLNL) as RL.
    destruct (nth_error T (Z.to_nat (uval rho pI))) as [p|] eqn:Ep; [|exfalso; apply nth_error_None in Ep; lia].
    pose proof (decodes_nth _ _ _ _ _ HD Ep) as [Q0 Q1]. rewrite Z2Nat.id in Q0, Q1 by lia. cbn [fst snd] in Q0, Q1.
    rewrite Q0 in R0. rewrite Q1 in R1. injection R0 as R0. injection R1 as R1.
    exists T. split; [|split; [exact HOK | split; [exact HLEN |]]]. { eapply decodes_ext; [|exact HD]. intros z _. apply HRM. }
    intros q Hq. destruct (lines_entry_bounds T _ _ p HOK Ep) as (B0 & B1 & BL).
    assert (EI1 : uval rho (SAlu ALU_ADD pI (SLit 1)) = uval rho pI + 1) by (rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; lia).
    assert (EE1 : uval rho (SAlu ALU_ADD pE (SLit 1)) = uval rho pPOS + uval rho pLNL + 1).
    { unfold pE. rewrite uval_add_small by (rewrite uval_add_small, uval_lit by lia; lia). rewrite uval_add_small by lia. rewrite uval_lit by lia. lia. }
    rewrite EE1. rewrite EI1 in Hq. replace (Z.to_nat (uval rho pI + 1)) with (S (Z.to_nat (uval rho pI))) in Hq by lia.
    pose proof (lines_next_pos T _ _ p q HOK Ep Hq). lia.
  - apply (SPA_entails_JA2 segs AInv CST XGL ALA NP Kc rho0 P0 FB FF BX PA HKc X_latchA K_loop s_loop nd nd rho1 tp _ Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | | exact Ctv | reflexivity | exact Hbud | exact Ham | exact SP1].
    apply (nd_below_mono HNEXT); [apply (proj1 (Pos.leb_le _ _)); reflexivity | exact Hnb].
Qed.

Lemma dp_facts : ltac2:(tb__ "0|4|
S1eS57S1cS24R1A1S21S3aS5aA1A1A3S2S34S7R2S45A2M0S7R2S4eA2M1A2S2S32S7R2S50A2M2G1A2S2S32G0G2A2S2S3S0G1S33S7R2S47A2S7R2S46A2A2A3S2S32G1S7R2S51A2M3A2S32G3S36Z2Z1aA2A2A2A2A2A2A2F_;Fr;").
Proof.
  intros r HF.
  factz HF (SPUlt pT0 pE) H1. factz HF (SPUle pQ pE) H2. factz HF (SPUle pT0 pQ) H3. factz HF (SPUle pE vLEN) H4.
  factz HF (SPUle pPOS (SLit 67108864)) H5. factz HF (SPUle pLNL (SLit 67108864)) H6. factz HF (SPUle vLEN (SLit 67108864)) H7.
  rewrite uval_lit in H5, H6, H7 by lia.
  assert (EE : uval r pE = uval r pPOS + uval r pLNL) by (unfold pE; apply uval_add_small; lia). repeat split; lia.
Qed.

Lemma dp_factsB : ltac2:(tb__ "0|0|
S1eS57S1cS24R1A1S21S3aS5aA1A1A3S32S33S7R2S53A2S7R2S51A2A2Z7fffff800000A2F_;Fr;").
Proof.
  intros r HF. factz HF (SPUle (SAlu ALU_ADD vBUF vLEN) (SLit 140737479966720)) H1. factz HF (SPUle vBUF (SLit 140737479966720)) H2. factz HF (SPUle vLEN (SLit 67108864)) H3.
  rewrite uval_lit in H1, H2, H3 by lia. rewrite uval_add_small in H1 by lia. exact H1.
Qed.

Lemma K_dpt_eq : ltac2:(tb__ "0|2|
S0S3S3bS5cR1A1S7fS85S5aP1d8S23S58S45S1fR1A1A3M0A3M1S14S1cSdS1cS20S4fS45A1S1fZ800000000000A1A2SdS1cS20G0S51A2S10S1cA1A3A3S21S3aG1A1A1A3A2A3Ft;").
Proof. intros t. reflexivity. Qed.
Lemma K_dpB_eq : ltac2:(tb__ "0|0|
S3S3bS5bS7fS5aS14S1cS5dS21S3aS5aA1A1A3A2A3").
Proof. reflexivity. Qed.
Lemma dp_checks : ltac2:(tb__ "0|4|
S2S3SeS90S1SfL_;S3aS5aA1M0A2SfA3S2S3SeS70S0S0S2cS3aS85S5aP1d8S23S58S45S1fR1A1A3M1A3A1M2A1Lt;SdS0Z0SdS0Z1SdS0Z2SdS0Z3SdS0Z4SdS0Z5SdS0Z6S10S0A1A3A3A3A3A3A3A3M3A3SfA3S2S3SeS70S1cS28S29G0A1A1S5dA3SfA3S3SeS70S0S0S70S1cS28S29G2A1A1SdS1cS20S4fS45A1S1fZ800000000000A1A2SdS1cS20G1S51A2S10S1cA1A3A3A3Lt;G3A3SfA3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma dp_split : ltac2:(tb__ "0|0|
S78S1eS11S74Q40A1A1S7eS6fS59VJAv;R4A1S5aR3R2R1A6S5S4S0S0S2S71S0R1SdS0Z0SdS0Z1SdS0Z2SdS0Z3SdS0Z4SdS0Z5SdS0Z6S10S0A1A3A3A3A3A3A3A3A3S6fS59VJAv;R6A1S5cR1A1R5R4R3A6A2Lt;A2S6fS59VJAv;R5A1S5bR4R3R2A6A2F_;Fw;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp w HS. pose proof (smatchA_facts segs _ _ _ _ (proj1 HS)) as HF.
  destruct (dp_facts rho HF) as (H1 & H2 & H3 & EE & H4 & H5). pose proof (dp_factsB rho HF) as HBL. pose proof (uval_range rho vBUF) as RB. pose proof dp_checks as (Cva & Cwf & CfB & Cft).
  pose proof (uval_range rho pT0) as RT.
  destruct (Z_le_dec (uval rho pQ - uval rho pT0) 6) as [LE|GT].
  - left. set (t := uval rho pQ - uval rho pT0).
    assert (Ht : In t [0;1;2;3;4;5;6]) by (cbn; lia).
    exists t. split; [exact Ht|]. rewrite K_dpt_eq.
    assert (Hpin : SPA segs (JAv nd) (pinA X_dp 472 (SAlu ALU_ADD pT0 (SLit t))) rho tp w).
    { apply (SPA_pin segs _ rho tp X_dp 472 _ w); [| exact Cva | | exact HS].
      - exact (proj1 (forallb_forall _ _) Cwf t Ht).
      - apply bv_eq. change (uval rho pQ = uval rho (SAlu ALU_ADD pT0 (SLit t))).
        rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia. }
    apply (SPA_refacts_JA segs _ rho _ _ tp w Hpin).
    + rewrite forallb_app, (proj1 (forallb_forall _ _) Cft t Ht). exact (swf_facts _ (proj1 (forallb_forall _ _) Cwf t Ht)).
    + intros tr md _ HFp. apply Forall_app. split; [|exact HFp]. constructor; [|constructor; [|constructor]]; apply (proj2 (h_ule _ _ _)).
      * unfold txt. rewrite uval_add_small by lia. rewrite uval_lit by lia. lia.
      * rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
  - right. rewrite K_dpB_eq. apply (SPA_refacts_JA segs _ rho _ (dpB_facts ++ ss_facts (ax_S X_dp)) tp w HS); [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc|].
    intros tr md _ HFp. apply Forall_app. split; [|exact HFp]. unfold dpB_facts.
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; apply (proj2 (h_ule _ _ _)).
    + unfold txt. rewrite uval_add_small by lia. rewrite uval_lit by lia. lia.
    + rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
    + rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
    + rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. lia.
Qed.
End Sum.
