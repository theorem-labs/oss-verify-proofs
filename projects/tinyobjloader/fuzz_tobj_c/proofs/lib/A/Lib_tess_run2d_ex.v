(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "eval"; "sv"; "sprop"; "sstate"; "holds"; "SAlu"; "SLit"; "SVar"; "mkVal"; "rl"; "rm"; "soff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "shb"; "@Corelib.Init.Logic"; "eq"; "or"; "and"; "iff"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_run2d_ex_defs"; "LN"; "LP"; "VN"; "rcuts"; "N_Eret"; "N_Xc2"; "N_Xg2"; "N_Xr"; "N_Xr0"; "N_Xrf"; "rexits"; "N_Kr"; "ecutpcs"; "st"; "TEST_r"; "X_r"; "X_r0"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "app"; "prod"; "Some"; "option"; "negb"; "nil"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg"; "rnode"; "rmeas"; "node_okb"; "rn_ghost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "world"; "assn"; "w_cfg"; "w_tr"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "lt"; "add"; "eqb"; "land"; "lxor"; "modulo"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states"; "X_r2"; "FUEL_r2"; "Posts_r2"; "Pre_r2"; "REMP"; "SEL"; "base_facts"; "gW_facts"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_run2d_ex.EX"; "s_xr"; "Xr0a"; "Xr0b"; "XrC"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_run2d_ex"; "rlfix"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "lex_val"; "vdir"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "sv_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymMaterialize"; "materialize_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListCommit"; "commit_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.RingCfgA"; "axof"; "RJ"; "SPfamRA"; "agree_wm"; "check_rcfgA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "cfg_model"; "config"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "mat_equiv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingBuf"; "IX4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.FastChkA"; "check_rcfgA'"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymObj SymMaterialize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue RingBuf Ring RingCfg ListCommit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import RingCfgA ListCommitA FastChkA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_tess_run2d_ex_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e1.Lib_tess_run2d_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_tess_run2d_ex_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import TessRun2dAddr.

Lemma pick_fact : ltac2:(tb__ "0|0|
S2S28S6A1S6S5bS6S8R3A1R2A3S69S6R2R3A3S8R5R3A2F_;F_;Ff;FF;Frho;").
Proof. intros rho F f H Hin. exact (proj1 (Forall_forall _ _) H f Hin). Qed.

Lemma soff_IX4 : ltac2:(tb__ "0|1|
S2S5S45S0Q40M0S4R2R1A2A2S44Z2Z3cA2A2S12S33SfR3S73R2A1A2S4bZ4S0G0S4R3R2A2A2A2A3F_;Fe;Frho;").
Proof.
  intros rho e He. unfold soff. rewrite bv_signed_U. pose proof (U_IX4 rho e ltac:(lia)) as X. rewrite X.
  unfold Zsigned, H63v. pose proof (urange (eval rho e)). destruct (Z.ltb_spec (4 * bv_unsigned (eval rho e)) 9223372036854775808); lia.
Qed.

Lemma lex_val_set_rl : ltac2:(tb__ "0|1|
S2S34S28S1Q8A1A1S28S2cS5eS5A2M0A1S12S29S6aG0G0S2fS60R4S31S5eS5R1A3A2A1Lc;R1A3S2aA3S12S33S5dS5fR5R4R3A3R2A2S5dR5R2A2A3F_;Fcomps;FL;Fl;Frho;").
Proof.
  intros rho l L comps H. induction comps as [|[d e] t IH]; cbn [lex_val]; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2]. rewrite IH by exact H2.
  unfold comp_val, base_val. cbn [fst snd]. rewrite eval_set_rl by (destruct (sv_has_rl l e); [discriminate|reflexivity]). reflexivity.
Qed.

Lemma U_and : ltac2:(tb__ "0|1|
S2S5S5S12S33S0Q40M0S4R3S9S6eR2R1A3A2A2S48S0G0S4R3R2A2A2S0G0S4R3R1A2A2A2A3Fb;Fa;Frho;").
Proof. intros. cbn [ZP ZN eval]. unfold alu64, alu. rewrite bv_and_unsigned. reflexivity. Qed.
Lemma U_xor : ltac2:(tb__ "0|1|
S2S5S5S12S33S0Q40M0S4R3S9S6fR2R1A3A2A2S49S0G0S4R3R2A2A2S0G0S4R3R1A2A2A2A3Fb;Fa;Frho;").
Proof. intros. cbn [ZP ZN eval]. unfold alu64, alu. rewrite bv_xor_unsigned. reflexivity. Qed.

Lemma sel_val : ltac2:(tb__ "0|4|
S2S45S0Q40M0S3R1P7bM1A2A2S0G0S3R1PdM2A2A2A2S43S0G0S3R2G2A2A2S44Z2Z14A2A2S12S33S0G0S4R3S52A2A2S29S33L_;S47S46S0G0S3R3G1A2A2Z1A2M3S0G0S3R3G2A2A2A2Z0G3X29x2A3F_;F_;Frho;").
Proof.
  intros rho HI Hn. unfold SEL, I4, szI. rewrite U_and, !CursorGlue.U_add, U_sltu, U_xor, CursorGlue.U_add, !U_sll_lit, !CursorGlue.U_lit.
  cbn [ZP ZN eval vN]. unfold M64v. change (2 ^ (2 mod 64)) with 4.
  pose proof (urange (rw rho 13%positive)) as R13. pose proof (urange (rw rho 123%positive)) as R123.
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.
  change (1 mod 18446744073709551616) with 1. change ((-1) mod 18446744073709551616) with 18446744073709551615.
  change ((-4) mod 18446744073709551616) with 18446744073709551612.
  rewrite (Z.mod_small (n * 4)) by lia. rewrite (Z.mod_small (I * 4)) by lia. rewrite (Z.mod_small (I + 1)) by lia.
  replace ((n * 4 + 18446744073709551612) mod 18446744073709551616) with (n * 4 - 4).
  2:{ replace (n * 4 + 18446744073709551612) with ((n * 4 - 4) + 1 * 18446744073709551616) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }
  destruct (Z.eqb_spec (I + 1) n) as [E|NE].
  - replace (n * 4 - 4) with (I * 4) by lia. rewrite Z.lxor_nilpotent. cbn. reflexivity.
  - assert (X : Z.lxor (n * 4 - 4) (I * 4) <> 0).
    { intros X. apply Z.lxor_eq in X. lia. }
    pose proof (Z.lxor_nonneg (n * 4 - 4) (I * 4)) as NN.
    destruct (Z.ltb_spec (Z.lxor (n * 4 - 4) (I * 4)) 1); [lia|].
    change ((0 + 18446744073709551615) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma rem_prv_val : ltac2:(tb__ "0|5|
S2S14S43Z5S0Q40M0S3R1PdM1A2A2M2A2S43G2S44Z2Z14A2A2A2S45S0G0S3R2P7bM3A2A2S0G0S3R2G1A2A2A2S12S33S0G0S4R3S51A2A2S4aS4cS46S0G0S3R3G3A2A2S0G0S3R3G1A2A2M4A2Z1A2G4A2A3F_;F_;Frho;").
Proof.
  intros rho Hn HI. unfold REMP. cbn [ZP ZN eval vN]. unfold mul_div.
  set (a := alu64 ALU_ADD (alu64 ALU_ADD (rw rho 13%positive) (Z_to_bv 64 (-1))) (rw rho 123%positive)).
  pose proof (urange (rw rho 13%positive)) as R13. pose proof (urange (rw rho 123%positive)) as R123.
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.
  assert (Ha : bv_unsigned a = n - 1 + I).
  { subst a. rewrite !add_val, lit_unsigned. fold n I. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
    replace ((n + (2 ^ 64 - 1)) mod 2 ^ 64) with (n - 1).
    2:{ replace (n + (2 ^ 64 - 1)) with ((n - 1) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }
    apply Z.mod_small. lia. }
  rewrite !low32_umod. fold n. rewrite (Z.mod_small n) by lia.
  destruct (Z.eqb_spec n 0); [lia|].
  assert (HM : bv_unsigned (bv_modu (low32 a) (low32 (rw rho 13%positive))) = (n - 1 + I) mod n).
  { rewrite bv_modu_unsigned, !low32_umod, Ha. fold n. rewrite (Z.mod_small n) by lia. rewrite (Z.mod_small (n - 1 + I)) by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (n - 1 + I) n ltac:(lia)) as MB.
  rewrite sext64_32_small by (rewrite HM; lia). rewrite HM. f_equal. lia.
Qed.

Lemma test_r : ltac2:(tb__ "0|3|
S2S45S0Q40M0S3R1P7bM1A2A2S0G0S3R1PdM2A2A2A2S43S0G0S3R2G2A2A2S44Z2Z14A2A2S15S8R3S25A2S16S12S33S46S0G0S3R3G1A2A2Z1A2S0G0S3R3G2A2A2A3A1A2F_;F_;Frho;").
Proof.
  intros rho HI Hn. unfold TEST_r, I4, szI. rewrite holds_bne. rewrite CursorGlue.U_add, !U_sll_lit, CursorGlue.U_lit. cbn [ZP ZN eval vN].
  unfold M64v. change (2 ^ (2 mod 64)) with 4. change (4 mod 18446744073709551616) with 4.
  pose proof (urange (rw rho 13%positive)) as R13. pose proof (urange (rw rho 123%positive)) as R123.
  rewrite !Z.mod_small by lia. lia.
Qed.

Lemma init_facts : ltac2:(tb__ "0|1|
S2S28S6A1S5bS6S8R2A1S2bS6R1S2bS6S54S53A3A3A3S14S43Z5S0Q40S3R3PdA2A2M0A2S43G0S44Z2Z14A2A2A2F_;FF;Frho;").
Proof.
  intros rho F HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HB].
  unfold base_facts in HB. apply Forall_cons_iff in HB as [H5 HB]. apply Forall_cons_iff in HB as [H6 _].
  cbn [holds eval vN] in *. rewrite lit_unsigned in H5, H6. change (5 mod 2 ^ 64) with 5 in H5.
  change (two20 mod 2 ^ 64) with (2 ^ 20) in H6. lia.
Qed.

Definition rlfix (rho0 rho : valuation) : valuation := ltac2:(tb__ "0|0|
ScS3Vrho;A1SdVrho0;A1SeVrho;A1A3").

Definition J0f (J : jpredA) (rho0 : valuation) : jpredA := ltac2:(tb__ "0|0|
S2S28S1Q40A1A1S28S56A1S55VJ;S5cVrho0;R4A2R3R2R1A4Lmd;Ltr;Lt;Lr;").

Section EX.
Variable J : jpredA.
Hypothesis HJ : stableA segs NF J.
Variable rho0 : valuation.
Variable tp : list word.
Let J0 : jpredA := J0f J rho0.
Let GH : ltac2:(tb__ "0|0|
S3aS2OFrho;Fnd;") := ltac2:(tb__ "0|0|
S3dS32S19S17S18Vrho0;A5").
Let RJ : ltac2:(tb__ "0|0|
S3aS37Fnd;") := ltac2:(tb__ "0|0|
S65S32S19S17S18VJ0;Vrho0;A6").
Let rnA := rnA X_r2 shb.
Let FAM (bound : Z) : ltac2:(tb__ "0|0|
S3fOF_;") := ltac2:(tb__ "0|0|
S66S10S32S19S17S18S4dS11VJ0;Vrho0;S1aVtp;Vbound;Ac").
Let Q : ltac2:(tb__ "0|0|
S40") := ltac2:(tb__ "0|0|
S36S10VJ;S32Vrho0;Vtp;S4fA6").

Lemma J0_ok : ltac2:(tb__ "0|0|
S2S2S28S1Q40A1A1S28S56A1S55S55S67S32R6R5A3S72S10R5R3R2A4VJ0;R8R6R5R4A4VJ0;R8R7R6R4A4F_;F_;F_;Fmd';Fmd;Ftr;Ft;Fr';Fr;").
Proof using HJ.
  intros r r' t tr md md' [Hw Hm] Hme H. unfold J0, J0f in *. eapply HJ; [| exact Hme | exact H].
  split; [exact Hw|]. split; [intros l; reflexivity | exact Hm].
Qed.

Lemma okb_all : ltac2:(tb__ "0|0|
S12S29S6aS3aS3cS32S19S17S18A4S2bS3aS1aS21A3A3S2aA3").
Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma okb_of : ltac2:(tb__ "0|0|
S3aS69S3aR1S2bS3aS1aS21A3A3S12S29S3cS32S19S17S18R2A5S2aA3F_;FN;").
Proof using . intros N H. exact (proj1 (forallb_forall _ _) okb_all N H). Qed.

Lemma SPA_RJ : ltac2:(tb__ "0|0|
S3aS2S2cS28S56A1S6cA2S38S10R2Vtp;VrnA;R3A1R1A5VJ0;R3Vtp;S42R2A1S6bS41R2A1A1A4VGH;R5R4A2S35S10VRJ;R6A1VrnA;R6A1R5Vtp;R4A6F_;F_;F_;Fw;Frho';FN;").
Proof using . intros N rho' w Hsm HJ0 HG. split; [exact Hsm | split; [exact HJ0 | exact HG]]. Qed.

Lemma J0_relist : ltac2:(tb__ "0|0|
S2S34S28S1Q8A1A1S28S1Q40A1A1S28S56A1S55VJ0;R6R3R2R1A4VJ0;S5fR7R6R5A3R4R3R2A4F_;Fmd;Ftr;Ft;FL;Fl;Fr;").
Proof using HJ.
  intros r l L t tr md H. eapply J0_ok; [| apply mat_equiv_refl | exact H]. split; intros; reflexivity.
Qed.

Lemma ex_Xc2 : ltac2:(tb__ "0|0|
S2VGH;S1cR1A2S3eS10S35S10VRJ;S1cA1VrnA;S1cA1R2Vtp;A5S3fS13VFAM;S3bS17S1cR3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using HJ.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [HsmA [HJ0 _]]. left.
  pose proof (proj1 HsmA) as Hsm. change (smatch segs rho (st X_c2) (tr, mkCfg (vms md tp ms) (vmd md))) in Hsm.
  set (vm := vms md tp ms) in Hsm. set (vd := vmd md) in Hsm.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  assert (F186 : bv_unsigned (rw rho 186%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 186) vN) HF). cbn. tauto. }
  assert (F187 : bv_unsigned (rw rho 187%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 187) vN) HF). cbn. tauto. }
  assert (FR : 3 < bv_unsigned (rw rho 182%positive)).
  { pose proof (pick_fact rho _ (SPBranch BC_LTU (SLit 3) (SVar 182)) HF ltac:(cbn; tauto)) as X.
    apply holds_bltu in X. rewrite CursorGlue.U_lit in X. cbn [ZP ZN eval] in X. unfold M64v in X. rewrite Z.mod_small in X by lia. exact X. }
  assert (FN : bv_unsigned (rw rho 13%positive) <= 2 ^ 20).
  { pose proof (pick_fact rho _ (SPUle vN (SLit two20)) HF ltac:(cbn; tauto)) as X.
    cbn [holds eval] in X. rewrite lit_unsigned in X. exact X. }

  destruct (smatch_nth_obj segs rho (st X_c2) 3 _ tr vm vd Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segs rho (st X_c2) 3 _ LN tr vm vd eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segs rho vm _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho vm vNXT (SLit 0) szI) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.

  destruct (smatch_nth_obj segs rho1 (commit_at (st X_c2) 3 LN) 4 _ tr vm vd Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segs rho1 (commit_at (st X_c2) 3 LN) 4 _ LP tr vm vd eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segs rho1 vm _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 vm vPRV (SLit 0) szI) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.
  change (smatch segs rho2 (st K_c2) (tr, mkCfg vm vd)) in Hsm2.

  assert (HsmA1 : smatchA segs rho1 tp (axof X_r2 shb (commit_at (st X_c2) 3 LN)) (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs rho LN bytesN tp (rnA N_Xc2)); [exact HsmA | exact Hsm1 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity]. }
  assert (HsmA2 : smatchA segs rho2 tp (rnA N_Kc2) (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs rho1 LP bytesP tp (axof X_r2 shb (commit_at (st X_c2) 3 LN))); [exact HsmA1 | exact Hsm2 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity]. }

  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [ZP ZN eval]; lia). cbn [ZP ZN eval] in BN, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (cbn [ZP ZN eval rw rho_set_rl]; subst rho1; cbn [ZP ZN eval rw rho_set_rl]; lia).
  subst rho1. cbn [ZP ZN eval rw rho_set_rl] in BP, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  change szI with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [ZP ZN eval rw rho_set_rl vN]; lia). cbn [ZP ZN eval rw rho_set_rl vN] in BN2, BN3, BP2, BP3.
  rewrite rho_set_rl_other in BP3 by (intros E; discriminate).
  pose proof (urange (rw rho 13%positive)) as U13. pose proof (urange (rw rho 186%positive)) as U186.
  pose proof (urange (rw rho 187%positive)) as U187. pose proof (urange (rw rho 180%positive)) as U180. pose proof (urange (rw rho 182%positive)) as U182.
  set (n := bv_unsigned (rw rho 13%positive)) in *.
  set (prev := bv_unsigned (rw rho 187%positive)) in *. set (next := bv_unsigned (rw rho 186%positive)) in *.

  destruct HG as (Hbase & Halln & _ & Hring). specialize (Halln eq_refl). destruct Halln as [AN AP].
  destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in Bn, AN, AP. fold n in Bn, AN, AP.
  destruct Hring as (HRok & Hroots & Heqs).
  unfold nval, Rn, Uv in HRok, Hroots. cbn [rg_R rg_cur rg_roots rg_eqs eval] in HRok, Hroots. cbn [rg_R rg_cur rg_roots rg_eqs] in Heqs. fold n in HRok, Hroots.
  set (R := Z.to_nat (bv_unsigned (rw rho 182%positive))) in *.
  set (cur := bv_unsigned (rw rho 180%positive)) in *.
  apply Forall_cons_iff in Heqs as [E186 Heqs]. apply Forall_cons_iff in Heqs as [E187 _]. cbn [fst snd] in E186, E187. unfold ZN, ZP in E186, E187.
  assert (Hcur : live R cur (NXf LN rho) cur) by (eapply live_cur; exact HRok).
  pose proof (live_lt _ _ _ _ _ _ HRok Hcur) as Bcur.
  assert (Enext : next = NXf LN rho cur).
  { unfold next. change (rw rho 186%positive) with (eval rho (SVar 186)). rewrite E186. unfold NXT. rewrite U_LD4 by (cbn [ZP ZN eval]; lia). reflexivity. }
  assert (Eprev : prev = PVf LP rho cur).
  { unfold prev. change (rw rho 187%positive) with (eval rho (SVar 187)). rewrite E187. unfold PRV. rewrite U_LD4 by (cbn [ZP ZN eval]; lia). reflexivity. }
  destruct (ring_clip n R cur (NXf LN rho) (PVf LP rho) HRok ltac:(subst R; lia)) as (HR' & LIVE' & NEpc & NEnc & NEpn & Lprev & Lnext).
  rewrite <- Enext, <- Eprev in *.

  assert (NXE : forall x, 0 <= x < n -> NXf LN rho2 x = fupd (NXf LN rho) prev next x).
  { intros x Hx. unfold NXf. subst rho2. rewrite rho_set_rl_other by (intros E; discriminate). rewrite rho_set_rl_at.
    rewrite BN. unfold fupd. replace (Z.to_nat (4 * prev)) with (4 * Z.to_nat prev)%nat by lia.
    destruct (Z.eqb_spec x prev) as [->|Hne].
    - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite bytes_le_to_Z_enc4. fold next. rewrite Z.mod_small by lia. reflexivity.
    - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). reflexivity. }
  assert (PVE : forall x, 0 <= x < n -> PVf LP rho2 x = fupd (PVf LP rho) next prev x).
  { intros x Hx. unfold PVf. subst rho2. rewrite rho_set_rl_at.
    rewrite BP. unfold fupd. replace (Z.to_nat (4 * next)) with (4 * Z.to_nat next)%nat by lia.
    destruct (Z.eqb_spec x next) as [->|Hne].
    - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite bytes_le_to_Z_enc4. fold prev. rewrite Z.mod_small by lia. reflexivity.
    - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). reflexivity. }
  pose proof (ring_ok_ext n (R - 1) next _ _ (NXf LN rho2) (PVf LP rho2) NXE PVE HR') as HR2.

  assert (Erw : forall i, rw rho2 i = rw rho i) by (intros i; reflexivity).
  assert (En2 : nval VN rho2 = n) by reflexivity.
  assert (ER2 : Rn rho2 (mkRG R182m1 ZN [ZN; ZP] []) = (R - 1)%nat).
  { unfold Rn, Uv, R182m1. cbn [rg_R]. rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [ZP ZN eval]. rewrite Erw. unfold M64v. subst R.
    change ((-1) mod 18446744073709551616) with 18446744073709551615.
    replace ((bv_unsigned (rw rho 182%positive) + 18446744073709551615) mod 18446744073709551616) with (bv_unsigned (rw rho 182%positive) - 1); [lia|].
    replace (bv_unsigned (rw rho 182%positive) + 18446744073709551615) with ((bv_unsigned (rw rho 182%positive) - 1) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }

  eapply (reenter_cutA segs NF VN LN LP X_r2 shb J0 rho0 rcuts N_Kc2 rho2 tp).
  - cbn. tauto.
  - apply SPA_RJ; [exact HsmA2 | subst rho2; apply J0_relist; apply J0_relist; exact HJ0 |].

    split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho2. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * rewrite En2. exact Bn.
    + intros _. rewrite En2. split.
      * intros i Hi. change (lget (rl rho2 LN) i) with (NXf LN rho2 i). rewrite NXE by exact Hi. unfold fupd.
        destruct (i =? prev); [lia|]. apply AN. exact Hi.
      * intros i Hi. change (lget (rl rho2 LP) i) with (PVf LP rho2 i). rewrite PVE by exact Hi. unfold fupd.
        destruct (i =? next); [lia|]. apply AP. exact Hi.
    + exact I.
    + split; [|split].
      * rewrite En2, ER2. unfold Uv. cbn [rg_cur eval ZN ZP]. rewrite Erw. fold next. exact HR2.
      * cbn [rg_roots rg_cur]. rewrite ER2. unfold Uv. cbn [ZP ZN eval]. rewrite !Erw. fold next. fold prev.
        assert (LV : forall x, live (R - 1) next (NXf LN rho2) x <-> live (R - 1) next (fupd (NXf LN rho) prev next) x).
        { intros x. unfold live. rewrite (chain_ext (fupd (NXf LN rho) prev next) (NXf LN rho2) next (R - 1)); [tauto|].
          intros j Hj. apply NXE. eapply live_lt; [exact HR'|]. eapply live_iter. exact HR'. }
        constructor; [|constructor; [|constructor]].
        -- apply LV. eapply live_cur. exact HR'.
        -- apply LV. apply (proj2 (LIVE' prev)). split; [exact Lprev | exact NEpc].
      * constructor.
  - apply (rmeas_nonneg NF VN LN LP). apply okb_of. cbn. tauto.
  - eapply (rmeas_lt_sub NF VN LN LP); [apply okb_of; cbn; tauto | apply okb_of; cbn; tauto | reflexivity | | reflexivity].
    cbn [rn_lex N_Kc2 N_Xc2]. subst rho2. rewrite !lex_val_set_rl by reflexivity. reflexivity.
Qed.

Lemma ex_Xg2 : ltac2:(tb__ "0|0|
S2VGH;S1dR1A2S3eS10S35S10VRJ;S1dA1VrnA;S1dA1R2Vtp;A5S3fS13VFAM;S3bS17S1dR3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using HJ.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [HsmA [HJ0 _]]. left.
  pose proof (proj1 HsmA) as Hsm. change (smatch segs rho (st X_g2) (tr, mkCfg (vms md tp ms) (vmd md))) in Hsm.
  set (vm := vms md tp ms) in Hsm. set (vd := vmd md) in Hsm.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  assert (F197 : bv_unsigned (rw rho 197%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 197) vN) HF). cbn. tauto. }
  assert (F196 : bv_unsigned (rw rho 196%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 196) vN) HF). cbn. tauto. }
  assert (FR : 3 < bv_unsigned (rw rho 182%positive)).
  { pose proof (pick_fact rho _ (SPBranch BC_LTU (SLit 3) (SVar 182)) HF ltac:(cbn; tauto)) as X.
    apply holds_bltu in X. rewrite CursorGlue.U_lit in X. cbn [ZP ZN eval] in X. unfold M64v in X. rewrite Z.mod_small in X by lia. exact X. }
  assert (FN : bv_unsigned (rw rho 13%positive) <= 2 ^ 20).
  { pose proof (pick_fact rho _ (SPUle vN (SLit two20)) HF ltac:(cbn; tauto)) as X.
    cbn [holds eval] in X. rewrite lit_unsigned in X. exact X. }

  destruct (smatch_nth_obj segs rho (st X_g2) 3 _ tr vm vd Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segs rho (st X_g2) 3 _ LN tr vm vd eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segs rho vm _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho vm vNXT (SLit 0) szI) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.

  destruct (smatch_nth_obj segs rho1 (commit_at (st X_g2) 3 LN) 4 _ tr vm vd Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segs rho1 (commit_at (st X_g2) 3 LN) 4 _ LP tr vm vd eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segs rho1 vm _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 vm vPRV (SLit 0) szI) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.
  change (smatch segs rho2 (st K_g2) (tr, mkCfg vm vd)) in Hsm2.

  assert (HsmA1 : smatchA segs rho1 tp (axof X_r2 shb (commit_at (st X_g2) 3 LN)) (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs rho LN bytesN tp (rnA N_Xg2)); [exact HsmA | exact Hsm1 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity]. }
  assert (HsmA2 : smatchA segs rho2 tp (rnA N_Kg2) (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs rho1 LP bytesP tp (axof X_r2 shb (commit_at (st X_g2) 3 LN))); [exact HsmA1 | exact Hsm2 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity]. }

  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [ZP ZN eval]; lia). cbn [ZP ZN eval] in BN, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (cbn [ZP ZN eval rw rho_set_rl]; subst rho1; cbn [ZP ZN eval rw rho_set_rl]; lia).
  subst rho1. cbn [ZP ZN eval rw rho_set_rl] in BP, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  change szI with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [ZP ZN eval rw rho_set_rl vN]; lia). cbn [ZP ZN eval rw rho_set_rl vN] in BN2, BN3, BP2, BP3.
  rewrite rho_set_rl_other in BP3 by (intros E; discriminate).
  pose proof (urange (rw rho 13%positive)) as U13. pose proof (urange (rw rho 197%positive)) as U197.
  pose proof (urange (rw rho 196%positive)) as U196. pose proof (urange (rw rho 186%positive)) as U186. pose proof (urange (rw rho 182%positive)) as U182.
  set (n := bv_unsigned (rw rho 13%positive)) in *.
  set (prev := bv_unsigned (rw rho 196%positive)) in *. set (next := bv_unsigned (rw rho 197%positive)) in *.

  destruct HG as (Hbase & Halln & _ & Hring). specialize (Halln eq_refl). destruct Halln as [AN AP].
  destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in Bn, AN, AP. fold n in Bn, AN, AP.
  destruct Hring as (HRok & Hroots & Heqs).
  unfold nval, Rn, Uv in HRok, Hroots. cbn [rg_R rg_cur rg_roots rg_eqs eval] in HRok, Hroots. cbn [rg_R rg_cur rg_roots rg_eqs] in Heqs. fold n in HRok, Hroots.
  set (R := Z.to_nat (bv_unsigned (rw rho 182%positive))) in *.
  set (cur := bv_unsigned (rw rho 186%positive)) in *.
  apply Forall_cons_iff in Heqs as [E196 Heqs]. apply Forall_cons_iff in Heqs as [E197 _]. cbn [fst snd] in E197, E196. unfold ZN, ZP in E196, E197.
  assert (Hcur : live R cur (NXf LN rho) cur) by (eapply live_cur; exact HRok).
  pose proof (live_lt _ _ _ _ _ _ HRok Hcur) as Bcur.
  assert (Enext : next = NXf LN rho cur).
  { unfold next. change (rw rho 197%positive) with (eval rho (SVar 197)). rewrite E197. unfold NXT. rewrite U_LD4 by (cbn [ZP ZN eval]; lia). reflexivity. }
  assert (Eprev : prev = PVf LP rho cur).
  { unfold prev. change (rw rho 196%positive) with (eval rho (SVar 196)). rewrite E196. unfold PRV. rewrite U_LD4 by (cbn [ZP ZN eval]; lia). reflexivity. }
  destruct (ring_clip n R cur (NXf LN rho) (PVf LP rho) HRok ltac:(subst R; lia)) as (HR' & LIVE' & NEpc & NEnc & NEpn & Lprev & Lnext).
  rewrite <- Enext, <- Eprev in *.

  assert (NXE : forall x, 0 <= x < n -> NXf LN rho2 x = fupd (NXf LN rho) prev next x).
  { intros x Hx. unfold NXf. subst rho2. rewrite rho_set_rl_other by (intros E; discriminate). rewrite rho_set_rl_at.
    rewrite BN. unfold fupd. replace (Z.to_nat (4 * prev)) with (4 * Z.to_nat prev)%nat by lia.
    destruct (Z.eqb_spec x prev) as [->|Hne].
    - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite bytes_le_to_Z_enc4. fold next. rewrite Z.mod_small by lia. reflexivity.
    - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). reflexivity. }
  assert (PVE : forall x, 0 <= x < n -> PVf LP rho2 x = fupd (PVf LP rho) next prev x).
  { intros x Hx. unfold PVf. subst rho2. rewrite rho_set_rl_at.
    rewrite BP. unfold fupd. replace (Z.to_nat (4 * next)) with (4 * Z.to_nat next)%nat by lia.
    destruct (Z.eqb_spec x next) as [->|Hne].
    - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite bytes_le_to_Z_enc4. fold prev. rewrite Z.mod_small by lia. reflexivity.
    - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). reflexivity. }
  pose proof (ring_ok_ext n (R - 1) next _ _ (NXf LN rho2) (PVf LP rho2) NXE PVE HR') as HR2.

  assert (Erw : forall i, rw rho2 i = rw rho i) by (intros i; reflexivity).
  assert (En2 : nval VN rho2 = n) by reflexivity.
  assert (ER2 : Rn rho2 (mkRG R182m1 (SVar 197) [SVar 197; SVar 196] []) = (R - 1)%nat).
  { unfold Rn, Uv, R182m1. cbn [rg_R]. rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [ZP ZN eval]. rewrite Erw. unfold M64v. subst R.
    change ((-1) mod 18446744073709551616) with 18446744073709551615.
    replace ((bv_unsigned (rw rho 182%positive) + 18446744073709551615) mod 18446744073709551616) with (bv_unsigned (rw rho 182%positive) - 1); [lia|].
    replace (bv_unsigned (rw rho 182%positive) + 18446744073709551615) with ((bv_unsigned (rw rho 182%positive) - 1) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }

  eapply (reenter_cutA segs NF VN LN LP X_r2 shb J0 rho0 rcuts N_Kg2 rho2 tp).
  - cbn. tauto.
  - apply SPA_RJ; [exact HsmA2 | subst rho2; apply J0_relist; apply J0_relist; exact HJ0 |].

    split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho2. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * rewrite En2. exact Bn.
    + intros _. rewrite En2. split.
      * intros i Hi. change (lget (rl rho2 LN) i) with (NXf LN rho2 i). rewrite NXE by exact Hi. unfold fupd.
        destruct (i =? prev); [lia|]. apply AN. exact Hi.
      * intros i Hi. change (lget (rl rho2 LP) i) with (PVf LP rho2 i). rewrite PVE by exact Hi. unfold fupd.
        destruct (i =? next); [lia|]. apply AP. exact Hi.
    + exact I.
    + split; [|split].
      * rewrite En2, ER2. unfold Uv. cbn [rg_cur eval ZN ZP]. rewrite Erw. fold next. exact HR2.
      * cbn [rg_roots rg_cur]. rewrite ER2. unfold Uv. cbn [ZP ZN eval]. rewrite !Erw. fold next. fold prev.
        assert (LV : forall x, live (R - 1) next (NXf LN rho2) x <-> live (R - 1) next (fupd (NXf LN rho) prev next) x).
        { intros x. unfold live. rewrite (chain_ext (fupd (NXf LN rho) prev next) (NXf LN rho2) next (R - 1)); [tauto|].
          intros j Hj. apply NXE. eapply live_lt; [exact HR'|]. eapply live_iter. exact HR'. }
        constructor; [|constructor; [|constructor]].
        -- apply LV. eapply live_cur. exact HR'.
        -- apply LV. apply (proj2 (LIVE' prev)). split; [exact Lprev | exact NEpc].
      * constructor.
  - apply (rmeas_nonneg NF VN LN LP). apply okb_of. cbn. tauto.
  - eapply (rmeas_lt_sub NF VN LN LP); [apply okb_of; cbn; tauto | apply okb_of; cbn; tauto | reflexivity | | reflexivity].
    cbn [rn_lex N_Kg2 N_Xg2]. subst rho2. rewrite !lex_val_set_rl by reflexivity. reflexivity.
Qed.

Definition XrC : sstate := Eval vm_compute in commit_at (commit_at (st X_r) 3 LN) 4 LP.
Lemma XrC_eq : ltac2:(tb__ "0|0|
S12S7S63S63S24S26A1U3S17A3U4S18A3S5aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition s_xr : wsub := Eval vm_compute in infer_sub NF XrC (st K_r).
Lemma ent_xr : ltac2:(tb__ "0|0|
S12S29S62S64S4dS11S5aA3VrnA;S22A1S57A3S2aA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma s_xr_id : ltac2:(tb__ "0|0|
S12S29S71S57S32A2S2aA3").
Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma s_xr_123 : ltac2:(tb__ "0|1|
S12S5S70S57P7bM0A2S9S6dSbG0A1SaZ1A1A3A3").
Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma ex_Xr : ltac2:(tb__ "0|0|
S2VGH;S1eR1A2S3eS10S35S10VRJ;S1eA1VrnA;S1eA1R2Vtp;A5S3fS13VFAM;S3bS17S1eR3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using HJ.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [HsmA [HJ0 _]]. left.
  pose proof (proj1 HsmA) as Hsm. change (smatch segs rho (st X_r) (tr, mkCfg (vms md tp ms) (vmd md))) in Hsm.
  set (vm := vms md tp ms) in Hsm. set (vd := vmd md) in Hsm.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  pose proof (init_facts rho _ HF) as FN.
  assert (F123 : bv_unsigned (rw rho 123%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 123) vN) HF). cbn. tauto. }
  assert (Fne : bv_unsigned (rw rho 123%positive) + 1 <> bv_unsigned (rw rho 13%positive)).
  { apply (proj1 (test_r rho F123 ltac:(lia))). apply (pick_fact rho _ TEST_r HF). cbn. tauto. }
  pose proof (urange (rw rho 13%positive)) as U13. pose proof (urange (rw rho 123%positive)) as U123.

  destruct (smatch_nth_obj segs rho (st X_r) 3 _ tr vm vd Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segs rho (st X_r) 3 _ LN tr vm vd eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segs rho vm _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho vm vNXT (SLit 0) szI) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.

  destruct (smatch_nth_obj segs rho1 (commit_at (st X_r) 3 LN) 4 _ tr vm vd Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segs rho1 (commit_at (st X_r) 3 LN) 4 _ LP tr vm vd eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segs rho1 vm _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 vm vPRV (SLit 0) szI) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.
  assert (HsmA1 : smatchA segs rho1 tp (axof X_r2 shb (commit_at (st X_r) 3 LN)) (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs rho LN bytesN tp (rnA N_Xr)); [exact HsmA | exact Hsm1 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity]. }
  assert (HsmA2 : smatchA segs rho2 tp (axof X_r2 shb XrC) (tr, mkCfg ms md)).
  { rewrite <- XrC_eq. eapply (smatchA_relist segs rho1 LP bytesP tp (axof X_r2 shb (commit_at (st X_r) 3 LN)));
      [exact HsmA1 | exact Hsm2 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity]. }

  unfold cellN, cellP in BN, BP, BN1, BN2, BP1, BP2. cbn [c_off c_val] in BN, BP, BN1, BN2, BP1, BP2. change I4 with (IX4 (SVar 123)) in BN, BP, BN1, BN2, BP1, BP2.
  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [ZP ZN eval]; lia). cbn [ZP ZN eval] in BN1, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (cbn [ZP ZN eval rw rho_set_rl]; subst rho1; cbn [ZP ZN eval rw rho_set_rl]; lia).
  subst rho1. cbn [ZP ZN eval rw rho_set_rl] in BP1, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  rewrite (eval_set_rl rho LN bytesN REMP) in BP by reflexivity.
  change (eval (rho_set_rl rho LN bytesN) (SVar 123)) with (eval rho (SVar 123)) in BP. cbn [ZP ZN eval] in BN, BP.
  change szI with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [ZP ZN eval rw rho_set_rl vN]; lia). cbn [ZP ZN eval rw rho_set_rl vN] in BN2, BN3, BP2, BP3.
  rewrite rho_set_rl_other in BP3 by (intros E; discriminate).
  pose proof (sel_val rho ltac:(lia) ltac:(lia)) as HVN. pose proof Fne as Fne'. apply Z.eqb_neq in Fne'. rewrite Fne' in HVN.
  pose proof (rem_prv_val rho ltac:(lia) ltac:(lia)) as HVP.
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.

  destruct HG as (Hbase & _ & Hinit & _). destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in Bn. fold n in Bn.
  cbn [rn_init N_Xr] in Hinit. unfold nval, Uv in Hinit. cbn [ZP ZN eval] in Hinit. fold n I in Hinit.

  pose proof (smatchA_entails segs _ (rnA N_Kr) s_xr rho2 tp (tr, mkCfg ms md) ent_xr HsmA2) as HSM3.
  set (rho3 := rho_sub rho2 s_xr) in *.
  assert (Erw : forall i, (i < NF)%positive -> rw rho3 i = rw rho i).
  { intros i Hi. subst rho3. cbn [rw rho_sub]. rewrite (wsub_get_id s_xr NF i s_xr_id Hi). reflexivity. }
  assert (E123 : bv_unsigned (rw rho3 123%positive) = I + 1).
  { subst rho3 rho2. cbn [rw rho_sub]. rewrite s_xr_123.
    rewrite CursorGlue.U_add, CursorGlue.U_lit. cbn [ZP ZN eval rw rho_set_rl]. fold I. unfold M64v. change (1 mod 18446744073709551616) with 1. apply Z.mod_small. lia. }
  eapply (reenter_cutA segs NF VN LN LP X_r2 shb J0 rho0 rcuts N_Kr rho3 tp).
  - cbn. tauto.
  - apply SPA_RJ; [exact HSM3 | |].
    { subst rho3 rho2. eapply (J0_ok (rho_set_rl (rho_set_rl rho LN bytesN) LP bytesP)); [| apply mat_equiv_refl | apply J0_relist; apply J0_relist; exact HJ0].
      split; [| intros a; reflexivity]. intros i Hi. cbn [rw rho_sub]. rewrite (wsub_get_id s_xr NF i s_xr_id Hi). reflexivity. }

    split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw by exact Hi. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho3 rho2. cbn [rl rho_sub]. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * unfold nval. rewrite Erw by reflexivity. exact Bn.
    + intros HX. discriminate HX.
    + cbn [rn_init N_Kr]. unfold nval, Uv. cbn [ZP ZN eval]. rewrite Erw by reflexivity. change (bv_unsigned (rw rho VN)) with n. rewrite E123.
      subst rho3 rho2. cbn [rl rho_sub]. rewrite rho_set_rl_at, rho_set_rl_other, rho_set_rl_at by (intros E; discriminate).
      intros j Hj. rewrite BN, BP.
      replace (Z.to_nat (4 * I)) with (4 * Z.to_nat I)%nat by lia.
      destruct (Z.eq_dec j I) as [->|Hne].
      * rewrite !lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite !bytes_le_to_Z_enc4, HVN, HVP.
        split.
        -- rewrite (Z.mod_small (I + 1) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. reflexivity.
        -- pose proof (Z.mod_pos_bound (I + n - 1) n ltac:(lia)). rewrite Z.mod_small by lia. reflexivity.
      * rewrite !lget_lput_other by (rewrite ?enc_bytes_length; lia). apply Hinit. lia.
    + exact Logic.I.
  - apply (rmeas_nonneg NF VN LN LP). apply okb_of. cbn. tauto.
  - eapply (rmeas_lt_lex NF VN LN LP); [apply okb_of; cbn; tauto | apply okb_of; cbn; tauto | reflexivity |].
    cbn [rn_lex N_Kr N_Xr]. rewrite !lex3_val1. unfold comp_val, base_val. cbn [fst snd eval].
    rewrite E123. fold I. rewrite !lit_unsigned. pose proof (B64_pos 2). pose proof (B64_pos 1). unfold B64 in *. nia.
Qed.

Lemma ex_Xrf : ltac2:(tb__ "0|0|
S2VGH;S20R1A2S3eS10S35S10VRJ;S20A1VrnA;S20A1R2Vtp;A5S3fS13VFAM;S3bS17S20R3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using HJ.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [HsmA [HJ0 _]]. left.
  pose proof (proj1 HsmA) as Hsm. change (smatch segs rho (st X_rf) (tr, mkCfg (vms md tp ms) (vmd md))) in Hsm.
  set (vm := vms md tp ms) in Hsm. set (vd := vmd md) in Hsm.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  pose proof (init_facts rho _ HF) as FN.
  assert (F123 : bv_unsigned (rw rho 123%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 123) vN) HF). cbn. tauto. }
  assert (Feq : bv_unsigned (rw rho 123%positive) = bv_unsigned (rw rho 13%positive) - 1).
  { pose proof (pick_fact rho _ (SPNot TEST_r) HF ltac:(cbn; tauto)) as X. cbn [holds] in X.
    pose proof (test_r rho F123 ltac:(lia)) as T. destruct (Z.eq_dec (bv_unsigned (rw rho 123%positive) + 1) (bv_unsigned (rw rho 13%positive))); [lia|].
    exfalso. apply X. apply (proj2 T). assumption. }
  pose proof (urange (rw rho 13%positive)) as U13. pose proof (urange (rw rho 123%positive)) as U123.

  destruct (smatch_nth_obj segs rho (st X_rf) 3 _ tr vm vd Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segs rho (st X_rf) 3 _ LN tr vm vd eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segs rho vm _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho vm vNXT (SLit 0) szI) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.

  destruct (smatch_nth_obj segs rho1 (commit_at (st X_rf) 3 LN) 4 _ tr vm vd Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segs rho1 (commit_at (st X_rf) 3 LN) 4 _ LP tr vm vd eq_refl eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segs rho1 vm _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 vm vPRV (SLit 0) szI) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.
  change (smatch segs rho2 (st K_f0) (tr, mkCfg vm vd)) in Hsm2.
  assert (HsmA1 : smatchA segs rho1 tp (axof X_r2 shb (commit_at (st X_rf) 3 LN)) (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs rho LN bytesN tp (rnA N_Xrf)); [exact HsmA | exact Hsm1 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity]. }
  assert (HsmA2 : smatchA segs rho2 tp (rnA N_Kf0) (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs rho1 LP bytesP tp (axof X_r2 shb (commit_at (st X_rf) 3 LN)));
      [exact HsmA1 | exact Hsm2 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity]. }

  unfold cellN, cellP in BN, BP, BN1, BN2, BP1, BP2. cbn [c_off c_val] in BN, BP, BN1, BN2, BP1, BP2. change I4 with (IX4 (SVar 123)) in BN, BP, BN1, BN2, BP1, BP2.
  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [ZP ZN eval]; lia). cbn [ZP ZN eval] in BN1, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (cbn [ZP ZN eval rw rho_set_rl]; subst rho1; cbn [ZP ZN eval rw rho_set_rl]; lia).
  subst rho1. cbn [ZP ZN eval rw rho_set_rl] in BP1, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  rewrite (eval_set_rl rho LN bytesN REMP) in BP by reflexivity.
  change (eval (rho_set_rl rho LN bytesN) (SVar 123)) with (eval rho (SVar 123)) in BP. cbn [ZP ZN eval] in BN, BP.
  change szI with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [ZP ZN eval rw rho_set_rl vN]; lia). cbn [ZP ZN eval rw rho_set_rl vN] in BN2, BN3, BP2, BP3.
  rewrite rho_set_rl_other in BP3 by (intros E; discriminate).
  pose proof (sel_val rho ltac:(lia) ltac:(lia)) as HVN.
  replace (bv_unsigned (rw rho 123%positive) + 1 =? bv_unsigned (rw rho 13%positive)) with true in HVN by (symmetry; apply Z.eqb_eq; lia).
  pose proof (rem_prv_val rho ltac:(lia) ltac:(lia)) as HVP.
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.
  assert (EI : I = n - 1) by lia.

  destruct HG as (Hbase & _ & Hinit & _). destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in Bn. fold n in Bn.
  cbn [rn_init N_Xrf] in Hinit. unfold nval, Uv in Hinit. cbn [ZP ZN eval] in Hinit. fold n I in Hinit.

  assert (NXv : forall i, 0 <= i < n -> NXf LN rho2 i = (i + 1) mod n).
  { intros i Hi. unfold NXf. subst rho2. rewrite rho_set_rl_other by (intros E; discriminate). rewrite rho_set_rl_at.
    rewrite BN. replace (Z.to_nat (4 * I)) with (4 * Z.to_nat I)%nat by lia.
    destruct (Z.eq_dec i I) as [->|Hne].
    - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite bytes_le_to_Z_enc4, HVN. rewrite EI.
      replace (n - 1 + 1) with n by lia. rewrite Z.mod_same by lia. reflexivity.
    - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). apply (proj1 (Hinit i ltac:(lia))). }
  assert (PVv : forall i, 0 <= i < n -> PVf LP rho2 i = (i + n - 1) mod n).
  { intros i Hi. unfold PVf. subst rho2. rewrite rho_set_rl_at.
    rewrite BP. replace (Z.to_nat (4 * I)) with (4 * Z.to_nat I)%nat by lia.
    destruct (Z.eq_dec i I) as [->|Hne].
    - rewrite lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite bytes_le_to_Z_enc4, HVP.
      pose proof (Z.mod_pos_bound (I + n - 1) n ltac:(lia)). rewrite Z.mod_small by lia. reflexivity.
    - rewrite lget_lput_other by (rewrite ?enc_bytes_length; lia). apply (proj2 (Hinit i ltac:(lia))). }
  pose proof (ring_init n (NXf LN rho2) (PVf LP rho2) ltac:(lia) NXv PVv) as HR2.
  assert (Erw : forall i, rw rho2 i = rw rho i) by (intros i; reflexivity).
  eapply (reenter_cutA segs NF VN LN LP X_r2 shb J0 rho0 rcuts N_Kf0 rho2 tp).
  - cbn. tauto.
  - apply SPA_RJ; [exact HsmA2 | subst rho2; apply J0_relist; apply J0_relist; exact HJ0 |].

    split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho2. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * unfold nval. rewrite Erw. exact Bn.
    + intros _. unfold nval. rewrite Erw. change (bv_unsigned (rw rho VN)) with n. split.
      * intros i Hi. change (lget (rl rho2 LN) i) with (NXf LN rho2 i). rewrite NXv by exact Hi.
        pose proof (Z.mod_pos_bound (i + 1) n ltac:(lia)). lia.
      * intros i Hi. change (lget (rl rho2 LP) i) with (PVf LP rho2 i). rewrite PVv by exact Hi.
        pose proof (Z.mod_pos_bound (i + n - 1) n ltac:(lia)). lia.
    + exact Logic.I.
    + cbn [rn_ring N_Kf0 RGfull]. split; [|split; [constructor|constructor]].
      unfold nval, Rn, Uv. cbn [rg_R rg_cur eval vN]. rewrite !Erw. change (bv_unsigned (rw rho 13%positive)) with n.
      rewrite lit_unsigned. change (0 mod 2 ^ 64) with 0. exact HR2.
  - apply (rmeas_nonneg NF VN LN LP). apply okb_of. cbn. tauto.
  - apply (rmeas_lt_ph NF VN LN LP); [apply okb_of; cbn; tauto | apply okb_of; cbn; tauto | reflexivity].
Qed.

Definition Xr0a : sstate := Eval vm_compute in match materialize_at (st X_r0) 3 LN with Some X => X | None => st X_r0 end.
Lemma mat_r0_3 : ltac2:(tb__ "0|0|
S12S2eS7A1S61S24S27A1U3S17A3S2dS7S58A2A3").
Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Xr0b : sstate := Eval vm_compute in match materialize_at Xr0a 4 LP with Some X => X | None => Xr0a end.
Lemma mat_r0_4 : ltac2:(tb__ "0|0|
S12S2eS7A1S61S58U4S18A3S2dS7S59A2A3").
Proof using . OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_r0 : ltac2:(tb__ "0|0|
S12S29S62S64S4dS11S59A3VrnA;S22A1S30S2cS34S5A2A1A3S2aA3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ex_Xr0 : ltac2:(tb__ "0|0|
S2VGH;S1fR1A2S3eS10S35S10VRJ;S1fA1VrnA;S1fA1R2Vtp;A5S3fS13VFAM;S3bS17S1fR3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using HJ.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [HsmA [HJ0 _]]. left.
  pose proof (proj1 HsmA) as Hsm. change (smatch segs rho (st X_r0) (tr, mkCfg (vms md tp ms) (vmd md))) in Hsm.
  set (vm := vms md tp ms) in Hsm. set (vd := vmd md) in Hsm.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  assert (F0 : bv_unsigned (rw rho 123%positive) = 0).
  { pose proof (pick_fact rho _ (SPEq (SVar 123) (SLit 0)) HF ltac:(cbn; tauto)) as X. cbn [holds eval] in X.
    rewrite X. rewrite lit_unsigned. reflexivity. }
  pose proof (smatch_materialize segs rho (st X_r0) 3 LN _ tr vm vd _ _ _ _ mat_r0_3 eq_refl Hsm) as Hsm1.
  set (bN := materialized_bytes rho vm _ _ _) in Hsm1. set (rho1 := rho_set_rl rho LN bN) in Hsm1.
  pose proof (smatch_materialize segs rho1 _ 4 LP _ tr vm vd _ _ _ _ mat_r0_4 eq_refl Hsm1) as Hsm2.
  set (bP := materialized_bytes rho1 vm _ _ _) in Hsm2. set (rho2 := rho_set_rl rho1 LP bP) in Hsm2.
  assert (HsmA1 : smatchA segs rho1 tp (axof X_r2 shb Xr0a) (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs rho LN bN tp (rnA N_Xr0)); [exact HsmA | exact Hsm1 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity]. }
  assert (HsmA2 : smatchA segs rho2 tp (axof X_r2 shb Xr0b) (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs rho1 LP bP tp (axof X_r2 shb Xr0a)); [exact HsmA1 | exact Hsm2 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | reflexivity | reflexivity]. }
  pose proof (smatchA_entails segs _ (rnA N_Kr) [] rho2 tp (tr, mkCfg ms md) ent_r0 HsmA2) as HSM3.
  set (rho3 := rho_sub rho2 []) in *.
  assert (Erw : forall i, rw rho3 i = rw rho i) by (intros i; reflexivity).
  destruct HG as (Hbase & _ & _ & _). destruct Hbase as (B1 & B2 & B3 & Bn).
  eapply (reenter_cutA segs NF VN LN LP X_r2 shb J0 rho0 rcuts N_Kr rho3 tp).
  - cbn. tauto.
  - apply SPA_RJ; [exact HSM3 | |].
    { subst rho3 rho2 rho1. eapply (J0_ok (rho_set_rl (rho_set_rl rho LN bN) LP bP)); [| apply mat_equiv_refl | apply J0_relist; apply J0_relist; exact HJ0].
      split; [intros i Hi; reflexivity | intros a; reflexivity]. }
    split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho3 rho2 rho1. cbn [rl rho_sub]. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * unfold nval. rewrite Erw. exact Bn.
    + intros HX. discriminate HX.
    + cbn [rn_init N_Kr]. unfold Uv. cbn [ZP ZN eval]. rewrite Erw, F0. intros j Hj. lia.
    + exact Logic.I.
  - apply (rmeas_nonneg NF VN LN LP). apply okb_of. cbn. tauto.
  - apply (rmeas_lt_ph NF VN LN LP); [apply okb_of; cbn; tauto | apply okb_of; cbn; tauto | reflexivity].
Qed.

Definition arrN : sobj := O_nxt (arrK vN).
Definition arrP : sobj := O_prv (arrK vN).

Lemma rlfix_eta : ltac2:(tb__ "0|0|
S2S12S2S5cR1R1A2R1A3Fr;").
Proof using . intros [a b c]. reflexivity. Qed.

Lemma ex_Eret : ltac2:(tb__ "0|0|
S2VGH;S1bR1A2S3eS10S35S10VRJ;S1bA1VrnA;S1bA1R2Vtp;A5S3fS13VFAM;S3bS17S1bR3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using HJ.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [HsmA [HJ0 _]]. right.
  pose proof (proj1 HsmA) as Hsm. change (smatch segs rho (st E_ret) (tr, mkCfg (vms md tp ms) (vmd md))) in Hsm.
  set (vm := vms md tp ms) in Hsm. set (vd := vmd md) in Hsm.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  assert (FN : 5 <= bv_unsigned (rw rho 13%positive) <= 2 ^ 20).
  { pose proof (pick_fact rho _ (SPUle (SLit 5) vN) HF ltac:(cbn; tauto)) as X1.
    pose proof (pick_fact rho _ (SPUle vN (SLit two20)) HF ltac:(cbn; tauto)) as X2.
    cbn [holds eval vN] in X1, X2. rewrite lit_unsigned in X1, X2. change (5 mod 2 ^ 64) with 5 in X1.
    change (two20 mod 2 ^ 64) with (2 ^ 20) in X2. lia. }
  destruct HG as (Hbase & Halln & _ & _). specialize (Halln eq_refl). destruct Halln as [AN AP].
  destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in AN, AP.

  assert (Hsm1 : smatch segs rho (obj_upd (st E_ret) 3 arrN) (tr, mkCfg vm vd)).
  { eapply smatch_obj_upd; [reflexivity | exact Hsm | reflexivity | reflexivity |].
    intros Hrom Hwf Ho. unfold arrN, O_nxt, arrK, idx_tmpl. eapply (obj_holds_list_arr segs rho vm vNXT _ LN vN _ _ Hrom Hwf Ho).
    - change szI with (IX4 vN). rewrite soff_IX4 by (cbn [ZP ZN eval vN]; lia). reflexivity.
    - reflexivity.
    - exact AN. }
  assert (Hsm2 : smatch segs rho (obj_upd (obj_upd (st E_ret) 3 arrN) 4 arrP) (tr, mkCfg vm vd)).
  { eapply smatch_obj_upd; [reflexivity | exact Hsm1 | reflexivity | reflexivity |].
    intros Hrom Hwf Ho. unfold arrP, O_prv, arrK, idx_tmpl. eapply (obj_holds_list_arr segs rho vm vPRV _ LP vN _ _ Hrom Hwf Ho).
    - change szI with (IX4 vN). rewrite soff_IX4 by (cbn [ZP ZN eval vN]; lia). reflexivity.
    - reflexivity.
    - exact AP. }
  change (smatch segs rho (ax_S P_ret) (tr, mkCfg vm vd)) in Hsm2.

  pose proof (smatch_set_rl segs rho LN (rl rho0 LN) (ax_S P_ret) _ ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hsm2) as Hsm3.
  pose proof (smatch_set_rl segs _ LP (rl rho0 LP) (ax_S P_ret) _ ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) Hsm3) as Hsm4.
  set (rhof := rho_set_rl (rho_set_rl rho LN (rl rho0 LN)) LP (rl rho0 LP)) in *.
  assert (HsmA2 : smatchA segs rho tp P_ret (tr, mkCfg ms md)).
  { eapply (smatchA_reobjs_same segs rho tp (rnA N_Eret) (ax_S P_ret)); [exact HsmA | exact Hsm2 | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc]. }
  assert (HsmA3 : smatchA segs (rho_set_rl rho LN (rl rho0 LN)) tp P_ret (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs rho LN (rl rho0 LN) tp P_ret (ax_S P_ret)); [exact HsmA2 | exact Hsm3 | reflexivity | reflexivity | reflexivity | reflexivity]. }
  assert (HsmA4 : smatchA segs rhof tp P_ret (tr, mkCfg ms md)).
  { eapply (smatchA_relist segs _ LP (rl rho0 LP) tp P_ret (ax_S P_ret)); [exact HsmA3 | exact Hsm4 | reflexivity | reflexivity | reflexivity | reflexivity]. }
  assert (Efix : rlfix rho0 rho = rhof).
  { subst rhof. unfold rlfix, rho_set_rl. cbn [rw rl rm]. f_equal. apply functional_extensionality. intros l.
    destruct (Pos.eqb_spec l LP) as [->|HlP]; [reflexivity|]. destruct (Pos.eqb_spec l LN) as [->|HlN]; [reflexivity|].
    apply B3; assumption. }
  exists (mkLeafA P_ret RsSymJump), rhof. split; [left; reflexivity|]. split; [|split; [exact HsmA4 |]].
  - split; [|split].
    + intros i Hi. rewrite B1 by exact Hi. reflexivity.
    + intros l. rewrite <- Efix. reflexivity.
    + intros a. rewrite B2. reflexivity.
  - rewrite <- Efix. exact HJ0.
Qed.

End EX.

Lemma rchk_A' : ltac2:(tb__ "0|0|
S12S29S74S10S32S19S17S18S4dS11S4eS23S1aS21AbS2aA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma rchk_A : ltac2:(tb__ "0|0|
S12S29S68S10S32S19S17S18S4dS11S4eS23S1aS21AbS2aA3").
Proof. rewrite <- check_rcfgA'_eq. exact rchk_A'. Qed.

Theorem run2d_sum_ex : ltac2:(tb__ "0|0|
S37S2S28S1Q40A1A1S39S10S32R3A3S3eS10S35S10R4S50R3R2A5S36S10R4S32R3R2S4fA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp HJ w Hw.
  assert (Hn : nval VN rho < 2 ^ 32).
  { destruct w as [tr [ms md]]. destruct Hw as [Hsm _]. pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
    pose proof (pick_fact rho _ (SPUle vN (SLit two20)) HF ltac:(cbn; tauto)) as X.
    cbn [holds eval vN] in X. rewrite lit_unsigned in X. change (two20 mod 2 ^ 64) with (2 ^ 20) in X. unfold nval. change (rw rho VN) with (rw rho 13%positive). lia. }
  refine (rcfg_complete_autoA segs NF VN LN LP X_r2 shb (J0f J rho) rho (J0_ok J HJ rho) FUEL_r2 ecutpcs rcuts rexits
            (LQA segs J NF rho tp Posts_r2) tp rchk_A _ N_Pre rho ltac:(cbn; tauto) _ w _).
  - intros E rho' HinE HG.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + apply ex_Xr0; assumption.
    + apply ex_Xr; assumption.
    + apply ex_Xrf; assumption.
    + apply ex_Xc2; assumption.
    + apply ex_Xg2; assumption.
    + apply ex_Eret; assumption.
  - split; [|split; [|split]]; try exact Logic.I.
    + split; [|split; [|split]]; intros; try reflexivity. exact Hn.
    + intros HX. discriminate HX.
  - destruct Hw as [Hsm HJw]. split; [exact Hsm|]. split.
    + unfold J0f. rewrite rlfix_eta. exact HJw.
    + split; [|split; [|split]]; try exact Logic.I.
      * split; [|split; [|split]]; intros; try reflexivity. exact Hn.
      * intros HX. discriminate HX.
Qed.
