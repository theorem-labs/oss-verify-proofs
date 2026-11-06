(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Logic"; "eq"; "or"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "rw"; "sprop"; "eval"; "DUnknown"; "SLit"; "SVar"; "sstate"; "SAlu"; "holds"; "soff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d_ex_defs"; "LN"; "LP"; "VN"; "X_r0"; "rcuts"; "rexits"; "K_r"; "N_Xrf"; "REM_prv"; "X_r"; "E_ret"; "N_Eret"; "N_Xc2"; "N_Xg2"; "N_Xr"; "N_Xr0"; "SEL_nxt"; "X_c2"; "X_g2"; "X_rf"; "ecutpcs"; "@Corelib.Init.Datatypes"; "bool"; "true"; "cons"; "list"; "pair"; "nil"; "prod"; "app"; "Some"; "false"; "option"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs"; "PG_P"; "FUEL_pg"; "pg_cutpcs2"; "K34c"; "Kext"; "Klat"; "Pre_pg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vdir"; "mkLN"; "Vdown"; "lex_val"; "SPfamE"; "enode"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "assn"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "LQ"; "ok_frame"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg"; "rnode"; "rmeas"; "node_okb"; "check_rcfg"; "rn_ghost"; "to_enodeR"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "pow"; "add"; "eqb"; "land"; "modulo"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListCommit"; "listed"; "obj_upd"; "commit_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d"; "R2_P"; "O_nxt"; "O_prv"; "Posts_r2"; "Pre_r2"; "base_facts"; "inv_r"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts"; "elcut"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_ex_nodes"; "lnodes_pg"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymMaterialize"; "materialize_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G3.Lib_tess_run2d_ex.EX"; "s_xr"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rl"; "sv_has_rl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingBuf"; "IX4"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_chk"; "Posts_pg"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymMaterialize.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingBuf.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.Ring.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListCommit.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Lib_tess_run2d_ex.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymMaterialize.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingBuf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.Ring OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ListCommit.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d_ex_defs.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma pick_fact : ltac2:(tb__ "0|0|
S7S2aS9A1S9S68S9S10R3A1R2A3S6fS9R2R3A3S10R5R3A2F_;F_;Ff;FF;Frho;").
Proof. intros rho F f H Hin. exact (proj1 (Forall_forall _ _) H f Hin). Qed.

Lemma soff_IX4 : ltac2:(tb__ "0|1|
S7S6S52S1Q40M0SaR2R1A2A2S53Z2Z3cA2A2S3S49S11R3S74R2A1A2S58Z4S1G0SaR3R2A2A2A2A3F_;Fe;Frho;").
Proof.
  intros rho e He. unfold soff. rewrite bv_signed_U. pose proof (U_IX4 rho e ltac:(lia)) as X. rewrite X.
  unfold Zsigned, H63v. pose proof (urange (eval rho e)). destruct (Z.ltb_spec (4 * bv_unsigned (eval rho e)) 9223372036854775808); lia.
Qed.

Lemma lex_val_set_rl : ltac2:(tb__ "0|1|
S7S4aS2aS2Q8A1A1S2aS2dS3cS6A2M0A1S3S27S70G0G0S32S72R4S33S3cS6R1A3A2A1Lc;R1A3S28A3S3S49S3fS71R5R4R3A3R2A2S3fR5R2A2A3F_;Fcomps;FL;Fl;Frho;").
Proof.
  intros rho l L comps H. induction comps as [|[d e] t IH]; cbn [lex_val]; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2]. rewrite IH by exact H2.
  unfold comp_val, base_val. cbn [fst snd]. rewrite eval_set_rl by (destruct (sv_has_rl l e); [discriminate|reflexivity]). reflexivity.
Qed.

Lemma U_and : ltac2:(tb__ "0|1|
S7S6S6S3S49S1Q40M0SaR3SfS6bR2R1A3A2A2S56S1G0SaR3R2A2A2S1G0SaR3R1A2A2A2A3Fb;Fa;Frho;").
Proof. intros. cbn [eval]. unfold alu64, alu. rewrite bv_and_unsigned. reflexivity. Qed.

Lemma sel_nxt_val : ltac2:(tb__ "0|4|
S7S51Z1M0S1Q40M1S8R1P7cM2A2A2A2S52S1G1S8R2P7bM3A2A2S53Z2Z3eA2A2S3S49S1G1SaR3S22A2A2S27S49L_;S55S1G1S8R3G2A2A2G0A2Z0S54S1G1S8R3G3A2A2G0A2X27x2A3F_;F_;Frho;").
Proof.
  intros rho H124 H123. unfold SEL_nxt. rewrite U_and, !U_add, U_sltu, U_add, !U_lit. cbn [eval]. unfold M64v.
  pose proof (urange (rw rho 124%positive)) as R124. pose proof (urange (rw rho 123%positive)) as R123.
  change ((-1) mod 18446744073709551616) with 18446744073709551615. change (1 mod 18446744073709551616) with 1.
  replace ((bv_unsigned (rw rho 124%positive) + 18446744073709551615) mod 18446744073709551616) with (bv_unsigned (rw rho 124%positive) - 1).
  2:{ replace (bv_unsigned (rw rho 124%positive) + 18446744073709551615) with ((bv_unsigned (rw rho 124%positive) - 1) + 1 * 18446744073709551616) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }
  rewrite (Z.mod_small (bv_unsigned (rw rho 123%positive) + 1)) by lia.
  destruct (Z.eqb_spec (bv_unsigned (rw rho 124%positive)) 1) as [E|NE].
  - rewrite E. cbn. reflexivity.
  - destruct (Z.ltb_spec (bv_unsigned (rw rho 124%positive) - 1) 1); [lia|].
    change ((0 + 18446744073709551615) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma rem_prv_val : ltac2:(tb__ "0|5|
S7S5S51Z5S1Q40M0S8R1PdM1A2A2M2A2S51G2S53Z2Z14A2A2A2S52S1G0S8R2P7bM3A2A2S1G0S8R2G1A2A2A2S3S49S1G0SaR3S1aA2A2S57S59S54S1G0S8R3G3A2A2S1G0S8R3G1A2A2M4A2Z1A2G4A2A3F_;F_;Frho;").
Proof.
  intros rho Hn HI. unfold REM_prv. cbn [eval]. unfold mul_div.
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

Section EX.
Variable K : ltac2:(tb__ "0|0|
S2aS65A1S64OF_;F_;").
Variable rho0 : valuation.
Let c := R2_P.
Let GH : ltac2:(tb__ "0|0|
S4bS7OFrho;Fnd;") := ltac2:(tb__ "0|0|
S4fS34S14S12S13Vrho0;A5").
Let FAM (bound : Z) : ltac2:(tb__ "0|0|
S42OF_;") := ltac2:(tb__ "0|0|
S40S0VK;S69S4bS41S50S34S14S12S13Vrho0;A5S16Vc;A1A4Vbound;A4").
Let Q : ltac2:(tb__ "0|0|
S44") := ltac2:(tb__ "0|0|
S47S0VK;S34Vrho0;S60Vc;A1A5").

Lemma okb_all : ltac2:(tb__ "0|0|
S3S27S70S4bS4dS34S14S12S13A4S2eS4bS16Vc;A1S17Vc;A1A3A3S28A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma okb_of : ltac2:(tb__ "0|0|
S4bS6fS4bR1S2eS4bS16Vc;A1S17Vc;A1A3A3S3S27S4dS34S14S12S13R2A5S28A3F_;FN;").
Proof using . intros N H. exact (proj1 (forallb_forall _ _) okb_all N H). Qed.

Lemma ex_Xc2 : ltac2:(tb__ "0|1|
S7VGH;S1eVc;A1M0R1A2S43S0S46S0VK;S23Vc;A1R2A4S42S4VFAM;S4cS12G0R3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using rho0.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [Hsm HK]. left.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  assert (F186 : bv_unsigned (rw rho 186%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 186) vN) HF). cbn. tauto. }
  assert (F187 : bv_unsigned (rw rho 187%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 187) vN) HF). cbn. tauto. }
  assert (FR : 3 < bv_unsigned (rw rho 182%positive)).
  { pose proof (pick_fact rho _ (SPBranch BC_LTU (SLit 3) (SVar 182)) HF ltac:(cbn; tauto)) as X.
    apply holds_bltu in X. rewrite U_lit in X. cbn [eval] in X. unfold M64v in X. rewrite Z.mod_small in X by lia. exact X. }
  assert (FN : bv_unsigned (rw rho 13%positive) <= 2 ^ 20).
  { pose proof (pick_fact rho _ (SPUle vN (SLit two20)) HF ltac:(cbn; tauto)) as X.
    cbn [holds eval] in X. rewrite lit_unsigned in X. exact X. }

  destruct (smatch_nth_obj segs rho (X_c2 c) 3 _ tr ms md Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segs rho (X_c2 c) 3 _ LN tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segs rho ms _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho ms vNXT (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.

  destruct (smatch_nth_obj segs rho1 (commit_at (X_c2 c) 3 LN) 4 _ tr ms md Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segs rho1 (commit_at (X_c2 c) 3 LN) 4 _ LP tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segs rho1 ms _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 ms vPRV (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.
  change (smatch segs rho2 (K_c2 c) (tr, mkCfg ms md)) in Hsm2.

  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [eval]; lia). cbn [eval] in BN, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (cbn [eval rw rho_set_rl]; subst rho1; cbn; lia).
  subst rho1. cbn [eval rw rho_set_rl] in BP, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  change (SAlu ALU_SLL vN (SLit 2)) with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [eval rw rho_set_rl vN]; lia). cbn [eval rw rho_set_rl vN] in BN2, BN3, BP2, BP3.
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
  apply Forall_cons_iff in Heqs as [E186 Heqs]. apply Forall_cons_iff in Heqs as [E187 _]. cbn [fst snd] in E186, E187.
  assert (Hcur : live R cur (NXf LN rho) cur) by (eapply live_cur; exact HRok).
  pose proof (live_lt _ _ _ _ _ _ HRok Hcur) as Bcur.
  assert (Enext : next = NXf LN rho cur).
  { unfold next. change (rw rho 186%positive) with (eval rho (SVar 186)). rewrite E186. unfold NXT. rewrite U_LD4 by (cbn [eval]; lia). reflexivity. }
  assert (Eprev : prev = PVf LP rho cur).
  { unfold prev. change (rw rho 187%positive) with (eval rho (SVar 187)). rewrite E187. unfold PRV. rewrite U_LD4 by (cbn [eval]; lia). reflexivity. }
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
  assert (ER2 : Rn rho2 (mkRG R182m1 (SVar 186) [SVar 186; SVar 187] []) = (R - 1)%nat).
  { unfold Rn, Uv, R182m1. cbn [rg_R]. rewrite U_add, U_lit. cbn [eval]. rewrite Erw. unfold M64v. subst R.
    change ((-1) mod 18446744073709551616) with 18446744073709551615.
    replace ((bv_unsigned (rw rho 182%positive) + 18446744073709551615) mod 18446744073709551616) with (bv_unsigned (rw rho 182%positive) - 1); [lia|].
    replace (bv_unsigned (rw rho 182%positive) + 18446744073709551615) with ((bv_unsigned (rw rho 182%positive) - 1) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }

  eapply (reenter_cut segs NF VN LN LP K rho0 (rcuts c) (N_Kc2 c) rho2).
  - cbn. tauto.
  -
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
      * rewrite En2, ER2. unfold Uv. cbn [rg_cur eval]. rewrite Erw. fold next. exact HR2.
      * cbn [rg_roots rg_cur]. rewrite ER2. unfold Uv. cbn [eval]. rewrite !Erw. fold next. fold prev.
        assert (LV : forall x, live (R - 1) next (NXf LN rho2) x <-> live (R - 1) next (fupd (NXf LN rho) prev next) x).
        { intros x. unfold live. rewrite (chain_ext (fupd (NXf LN rho) prev next) (NXf LN rho2) next (R - 1)); [tauto|].
          intros j Hj. apply NXE. eapply live_lt; [exact HR'|]. eapply live_iter. exact HR'. }
        constructor; [|constructor; [|constructor]].
        -- apply LV. eapply live_cur. exact HR'.
        -- apply LV. apply (proj2 (LIVE' prev)). split; [exact Lprev | exact NEpc].
      * constructor.
  -   split; [exact Hsm2 | exact HK].
  - apply (rmeas_nonneg NF VN LN LP). apply okb_of. cbn. tauto.
  - eapply (rmeas_lt_sub NF VN LN LP); [apply okb_of; cbn; tauto | apply okb_of; cbn; tauto | reflexivity | | reflexivity].
    cbn [rn_lex N_Kc2 N_Xc2]. subst rho2. rewrite !lex_val_set_rl by reflexivity. reflexivity.
Qed.

Lemma ex_Xg2 : ltac2:(tb__ "0|1|
S7VGH;S1fVc;A1M0R1A2S43S0S46S0VK;S24Vc;A1R2A4S42S4VFAM;S4cS12G0R3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using rho0.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [Hsm HK]. left.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  assert (F197 : bv_unsigned (rw rho 197%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 197) vN) HF). cbn. tauto. }
  assert (F196 : bv_unsigned (rw rho 196%positive) < bv_unsigned (rw rho 13%positive)).
  { apply (pick_fact rho _ (SPUlt (SVar 196) vN) HF). cbn. tauto. }
  assert (FR : 3 < bv_unsigned (rw rho 182%positive)).
  { pose proof (pick_fact rho _ (SPBranch BC_LTU (SLit 3) (SVar 182)) HF ltac:(cbn; tauto)) as X.
    apply holds_bltu in X. rewrite U_lit in X. cbn [eval] in X. unfold M64v in X. rewrite Z.mod_small in X by lia. exact X. }
  assert (FN : bv_unsigned (rw rho 13%positive) <= 2 ^ 20).
  { pose proof (pick_fact rho _ (SPUle vN (SLit two20)) HF ltac:(cbn; tauto)) as X.
    cbn [holds eval] in X. rewrite lit_unsigned in X. exact X. }

  destruct (smatch_nth_obj segs rho (X_g2 c) 3 _ tr ms md Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segs rho (X_g2 c) 3 _ LN tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segs rho ms _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho ms vNXT (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.

  destruct (smatch_nth_obj segs rho1 (commit_at (X_g2 c) 3 LN) 4 _ tr ms md Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segs rho1 (commit_at (X_g2 c) 3 LN) 4 _ LP tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segs rho1 ms _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 ms vPRV (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.
  change (smatch segs rho2 (K_g2 c) (tr, mkCfg ms md)) in Hsm2.

  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [eval]; lia). cbn [eval] in BN, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (cbn [eval rw rho_set_rl]; subst rho1; cbn; lia).
  subst rho1. cbn [eval rw rho_set_rl] in BP, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  change (SAlu ALU_SLL vN (SLit 2)) with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [eval rw rho_set_rl vN]; lia). cbn [eval rw rho_set_rl vN] in BN2, BN3, BP2, BP3.
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
  apply Forall_cons_iff in Heqs as [E196 Heqs]. apply Forall_cons_iff in Heqs as [E197 _]. cbn [fst snd] in E197, E196.
  assert (Hcur : live R cur (NXf LN rho) cur) by (eapply live_cur; exact HRok).
  pose proof (live_lt _ _ _ _ _ _ HRok Hcur) as Bcur.
  assert (Enext : next = NXf LN rho cur).
  { unfold next. change (rw rho 197%positive) with (eval rho (SVar 197)). rewrite E197. unfold NXT. rewrite U_LD4 by (cbn [eval]; lia). reflexivity. }
  assert (Eprev : prev = PVf LP rho cur).
  { unfold prev. change (rw rho 196%positive) with (eval rho (SVar 196)). rewrite E196. unfold PRV. rewrite U_LD4 by (cbn [eval]; lia). reflexivity. }
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
  { unfold Rn, Uv, R182m1. cbn [rg_R]. rewrite U_add, U_lit. cbn [eval]. rewrite Erw. unfold M64v. subst R.
    change ((-1) mod 18446744073709551616) with 18446744073709551615.
    replace ((bv_unsigned (rw rho 182%positive) + 18446744073709551615) mod 18446744073709551616) with (bv_unsigned (rw rho 182%positive) - 1); [lia|].
    replace (bv_unsigned (rw rho 182%positive) + 18446744073709551615) with ((bv_unsigned (rw rho 182%positive) - 1) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity. }

  eapply (reenter_cut segs NF VN LN LP K rho0 (rcuts c) (N_Kg2 c) rho2).
  - cbn. tauto.
  -
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
      * rewrite En2, ER2. unfold Uv. cbn [rg_cur eval]. rewrite Erw. fold next. exact HR2.
      * cbn [rg_roots rg_cur]. rewrite ER2. unfold Uv. cbn [eval]. rewrite !Erw. fold next. fold prev.
        assert (LV : forall x, live (R - 1) next (NXf LN rho2) x <-> live (R - 1) next (fupd (NXf LN rho) prev next) x).
        { intros x. unfold live. rewrite (chain_ext (fupd (NXf LN rho) prev next) (NXf LN rho2) next (R - 1)); [tauto|].
          intros j Hj. apply NXE. eapply live_lt; [exact HR'|]. eapply live_iter. exact HR'. }
        constructor; [|constructor; [|constructor]].
        -- apply LV. eapply live_cur. exact HR'.
        -- apply LV. apply (proj2 (LIVE' prev)). split; [exact Lprev | exact NEpc].
      * constructor.
  -   split; [exact Hsm2 | exact HK].
  - apply (rmeas_nonneg NF VN LN LP). apply okb_of. cbn. tauto.
  - eapply (rmeas_lt_sub NF VN LN LP); [apply okb_of; cbn; tauto | apply okb_of; cbn; tauto | reflexivity | | reflexivity].
    cbn [rn_lex N_Kg2 N_Xg2]. subst rho2. rewrite !lex_val_set_rl by reflexivity. reflexivity.
Qed.

Definition s_xr : wsub := ltac2:(tb__ "0|3|
S29S2dS4aS6A2M0S2bS4aS6P7bM1SfS6aSdG1A1ScZ1A1A3A4S29G0S2bS4aS6P7cM2SfS6aSdG2A1ScN1A1A3A4S29G0S2bS4aS6P6aS1aA4S2cG0A1A3A3A3").
Lemma ent_xr : ltac2:(tb__ "0|0|
S3S27S6cS5cS5cS1bVc;A1U3S12A3U4S13A3S18Vc;A1S6eA3S28A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.
Lemma s_xr_id : ltac2:(tb__ "0|0|
S3S27S73S6eS34A2S28A3").
Proof using . reflexivity. Qed.

Lemma init_facts : ltac2:(tb__ "0|4|
S7S2aS9A1S68S9S10R2A1S2eS9R1S2eS9S63S62A3A3A3S5S3S49S54S1Q40M0S8R3P7cA2A2M1S1G0S8R3P7bA2A2M2A2S1G0S8R3PdA2A2M3A3S5S51Z1G1A2S5S52G2G3A2S5S51Z5G3A2S51G3S53Z2Z14A2A2A2A2A2A2F_;FF;Frho;").
Proof using FAM GH.
  intros rho F HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [HI HB].
  unfold inv_r in HI. apply Forall_cons_iff in HI as [H1 HI]. apply Forall_cons_iff in HI as [H2 HI].
  apply Forall_cons_iff in HI as [H3 HI]. apply Forall_cons_iff in HI as [H4 _].
  unfold base_facts in HB. apply Forall_cons_iff in HB as [H5 HB]. apply Forall_cons_iff in HB as [H6 _].
  cbn [holds eval vN] in *. rewrite lit_unsigned in H2, H5, H6. change (1 mod 2 ^ 64) with 1 in H2. change (5 mod 2 ^ 64) with 5 in H5.
  change (two20 mod 2 ^ 64) with (2 ^ 20) in H6.
  pose proof (urange (rw rho 124%positive)). pose proof (urange (rw rho 123%positive)).
  apply (f_equal bv_unsigned) in H1. rewrite add_val in H1. rewrite Z.mod_small in H1 by lia. lia.
Qed.

Lemma ex_Xr : ltac2:(tb__ "0|1|
S7VGH;S20Vc;A1M0R1A2S43S0S46S0VK;S1bVc;A1R2A4S42S4VFAM;S4cS12G0R3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using rho0.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [Hsm HK]. left.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  destruct (init_facts rho [_] HF) as (Fsum & F124 & F123 & FN).
  assert (Fne : bv_unsigned (rw rho 124%positive) <> 1).
  { pose proof (pick_fact rho _ (SPBranch BC_NE (SAlu ALU_ADD (SVar 124) (SLit (-1))) (SLit 0)) HF ltac:(cbn; tauto)) as X.
    apply holds_bne in X. rewrite U_add, !U_lit in X. cbn [eval] in X. unfold M64v in X. intros E. apply X. rewrite E. reflexivity. }
  pose proof (urange (rw rho 13%positive)) as U13. pose proof (urange (rw rho 123%positive)) as U123. pose proof (urange (rw rho 124%positive)) as U124.

  destruct (smatch_nth_obj segs rho (X_r c) 3 _ tr ms md Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segs rho (X_r c) 3 _ LN tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segs rho ms _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho ms vNXT (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.

  destruct (smatch_nth_obj segs rho1 (commit_at (X_r c) 3 LN) 4 _ tr ms md Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segs rho1 (commit_at (X_r c) 3 LN) 4 _ LP tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segs rho1 ms _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 ms vPRV (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.

  unfold cellN, cellP in BN, BP. cbn [c_off c_val] in BN, BP.
  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [eval]; lia). cbn [eval] in BN1, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (cbn [eval rw rho_set_rl]; subst rho1; cbn; lia).
  subst rho1. cbn [eval rw rho_set_rl] in BP1, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  rewrite (eval_set_rl rho LN bytesN REM_prv) in BP by reflexivity.
  change (eval (rho_set_rl rho LN bytesN) (SVar 123)) with (eval rho (SVar 123)) in BP. cbn [eval] in BN, BP.
  change (SAlu ALU_SLL vN (SLit 2)) with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [eval rw rho_set_rl vN]; lia). cbn [eval rw rho_set_rl vN] in BN2, BN3, BP2, BP3.
  rewrite rho_set_rl_other in BP3 by (intros E; discriminate).
  pose proof (sel_nxt_val rho ltac:(lia) ltac:(lia)) as HVN. apply Z.eqb_neq in Fne. rewrite Fne in HVN.
  pose proof (rem_prv_val rho ltac:(lia) ltac:(lia)) as HVP.
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.

  destruct HG as (Hbase & _ & Hinit & _). destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in Bn. fold n in Bn.
  cbn [rn_init N_Xr] in Hinit. unfold nval, Uv in Hinit. cbn [eval] in Hinit. fold n I in Hinit.

  pose proof (SP_entails segs K _ (K_r c) s_xr rho2 (tr, mkCfg ms md) ent_xr (conj Hsm2 HK)) as HSP.
  set (rho3 := rho_sub rho2 s_xr) in *.
  assert (Erw : forall i, (i < NF)%positive -> rw rho3 i = rw rho i).
  { intros i Hi. subst rho3. cbn [rw rho_sub]. rewrite (wsub_get_id s_xr NF i s_xr_id Hi). reflexivity. }
  assert (E123 : bv_unsigned (rw rho3 123%positive) = I + 1).
  { subst rho3 rho2. cbn [rw rho_sub]. change (wsub_get s_xr 123%positive) with (SAlu ALU_ADD (SVar 123) (SLit 1)).
    rewrite U_add, U_lit. cbn [eval rw rho_set_rl]. fold I. unfold M64v. change (1 mod 18446744073709551616) with 1. apply Z.mod_small. lia. }
  assert (E124 : bv_unsigned (rw rho3 124%positive) = bv_unsigned (rw rho 124%positive) - 1).
  { subst rho3 rho2. cbn [rw rho_sub]. change (wsub_get s_xr 124%positive) with (SAlu ALU_ADD (SVar 124) (SLit (-1))).
    rewrite U_add, U_lit. cbn [eval rw rho_set_rl]. unfold M64v. change ((-1) mod 18446744073709551616) with 18446744073709551615.
    replace (bv_unsigned (rw rho 124%positive) + 18446744073709551615) with ((bv_unsigned (rw rho 124%positive) - 1) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  eapply (reenter_cut segs NF VN LN LP K rho0 (rcuts c) (N_Kr c) rho3).
  - cbn. tauto.
  -
    split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw by exact Hi. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho3 rho2. cbn [rl rho_sub]. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * unfold nval. rewrite Erw by reflexivity. exact Bn.
    + intros HX. discriminate HX.
    + cbn [rn_init N_Kr]. unfold nval, Uv. cbn [eval]. rewrite Erw by reflexivity. fold n. rewrite E123.
      subst rho3 rho2. cbn [rl rho_sub]. rewrite rho_set_rl_at, rho_set_rl_other, rho_set_rl_at by (intros E; discriminate).
      change (bv_unsigned (rw rho VN)) with n. intros j Hj. rewrite BN, BP.
      replace (Z.to_nat (4 * I)) with (4 * Z.to_nat I)%nat by lia.
      destruct (Z.eq_dec j I) as [->|Hne].
      * rewrite !lget_lput_same by (rewrite ?enc_bytes_length; lia). rewrite !bytes_le_to_Z_enc4, HVN, HVP.
        split.
        -- rewrite (Z.mod_small (I + 1) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. reflexivity.
        -- pose proof (Z.mod_pos_bound (I + n - 1) n ltac:(lia)). rewrite Z.mod_small by lia. reflexivity.
      * rewrite !lget_lput_other by (rewrite ?enc_bytes_length; lia). apply Hinit. lia.
    + exact Logic.I.
  - exact HSP.
  - apply (rmeas_nonneg NF VN LN LP). apply okb_of. cbn. tauto.
  - eapply (rmeas_lt_lex NF VN LN LP); [apply okb_of; cbn; tauto | apply okb_of; cbn; tauto | reflexivity |].
    cbn [rn_lex N_Kr N_Xr]. rewrite !lex3_val1. unfold comp_val, base_val. cbn [fst snd eval].
    rewrite E124. rewrite !lit_unsigned. pose proof (B64_pos 2). pose proof (B64_pos 1). nia.
Qed.

Lemma ex_Xrf : ltac2:(tb__ "0|0|
S7VGH;S19R1A2S43S0S46S0VK;S25R2A4S42S4VFAM;S4cS12S19R3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using rho0.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [Hsm HK]. left.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  destruct (init_facts rho [_] HF) as (Fsum & F124 & F123 & FN).
  assert (Feq : bv_unsigned (rw rho 124%positive) = 1).
  { pose proof (pick_fact rho _ (SPNot (SPBranch BC_NE (SAlu ALU_ADD (SVar 124) (SLit (-1))) (SLit 0))) HF ltac:(cbn; tauto)) as X.
    apply holds_nbne in X. rewrite U_add, !U_lit in X. cbn [eval] in X. unfold M64v in X.
    pose proof (urange (rw rho 124%positive)).
    change ((-1) mod 18446744073709551616) with 18446744073709551615 in X. change (0 mod 18446744073709551616) with 0 in X.
    destruct (Z.eq_dec (bv_unsigned (rw rho 124%positive)) 1) as [E|NE]; [exact E|].
    exfalso. replace (bv_unsigned (rw rho 124%positive) + 18446744073709551615) with ((bv_unsigned (rw rho 124%positive) - 1) + 1 * 18446744073709551616) in X by lia.
    rewrite Z.mod_add in X by lia. rewrite Z.mod_small in X by lia. lia. }
  pose proof (urange (rw rho 13%positive)) as U13. pose proof (urange (rw rho 123%positive)) as U123. pose proof (urange (rw rho 124%positive)) as U124.

  destruct (smatch_nth_obj segs rho X_rf 3 _ tr ms md Hsm eq_refl) as (Ho3 & Hwf3 & Hrom).
  pose proof (smatch_commit segs rho X_rf 3 _ LN tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm) as Hsm1.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm1.
  destruct (commit_bytes1 segs rho ms _ _ _ _ LN _ Hrom Hwf3 Ho3) as (BN & BN1 & BN2 & BN3).
  set (bytesN := materialized_bytes rho ms vNXT (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho1 := rho_set_rl rho LN bytesN) in *.

  destruct (smatch_nth_obj segs rho1 (commit_at X_rf 3 LN) 4 _ tr ms md Hsm1 eq_refl) as (Ho4 & Hwf4 & _).
  pose proof (smatch_commit segs rho1 (commit_at X_rf 3 LN) 4 _ LP tr ms md eq_refl eq_refl ltac:(vm_compute; reflexivity) Hsm1) as Hsm2.
  cbn [ob_base ob_lo ob_hi ob_dflt] in Hsm2.
  destruct (commit_bytes1 segs rho1 ms _ _ _ _ LP _ Hrom Hwf4 Ho4) as (BP & BP1 & BP2 & BP3).
  set (bytesP := materialized_bytes rho1 ms vPRV (SLit 0) (SAlu ALU_SLL vN (SLit 2))) in *.
  set (rho2 := rho_set_rl rho1 LP bytesP) in *.
  change (smatch segs rho2 K_f0 (tr, mkCfg ms md)) in Hsm2.

  unfold cellN, cellP in BN, BP. cbn [c_off c_val] in BN, BP.
  rewrite soff_IX4 in BN, BN1, BN2 by (cbn [eval]; lia). cbn [eval] in BN1, BN2.
  rewrite soff_IX4 in BP, BP1, BP2 by (cbn [eval rw rho_set_rl]; subst rho1; cbn; lia).
  subst rho1. cbn [eval rw rho_set_rl] in BP1, BP2. rewrite rho_set_rl_other in BP by (intros E; discriminate).
  rewrite (eval_set_rl rho LN bytesN REM_prv) in BP by reflexivity.
  change (eval (rho_set_rl rho LN bytesN) (SVar 123)) with (eval rho (SVar 123)) in BP. cbn [eval] in BN, BP.
  change (SAlu ALU_SLL vN (SLit 2)) with (IX4 vN) in BN2, BN3, BP2, BP3.
  rewrite soff_IX4 in BN2, BN3, BP2, BP3 by (cbn [eval rw rho_set_rl vN]; lia). cbn [eval rw rho_set_rl vN] in BN2, BN3, BP2, BP3.
  rewrite rho_set_rl_other in BP3 by (intros E; discriminate).
  pose proof (sel_nxt_val rho ltac:(lia) ltac:(lia)) as HVN. pose proof Feq as Feq'. apply Z.eqb_eq in Feq'. rewrite Feq' in HVN.
  pose proof (rem_prv_val rho ltac:(lia) ltac:(lia)) as HVP.
  set (n := bv_unsigned (rw rho 13%positive)) in *. set (I := bv_unsigned (rw rho 123%positive)) in *.
  assert (EI : I = n - 1) by lia.

  destruct HG as (Hbase & _ & Hinit & _). destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in Bn. fold n in Bn.
  cbn [rn_init N_Xrf] in Hinit. unfold nval, Uv in Hinit. cbn [eval] in Hinit. fold n I in Hinit.

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
  eapply (reenter_cut segs NF VN LN LP K rho0 (rcuts c) N_Kf0 rho2).
  - cbn. tauto.
  -
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
  - split; [exact Hsm2 | exact HK].
  - apply (rmeas_nonneg NF VN LN LP). apply okb_of. cbn. tauto.
  - apply (rmeas_lt_ph NF VN LN LP); [apply okb_of; cbn; tauto | apply okb_of; cbn; tauto | reflexivity].
Qed.

Lemma mat_r0_3 : ltac2:(tb__ "0|2|
S3S31SeA1S6dS15Vc;A1M0U3M1S12A3S2fSeS5bG0G1S5aS5eSbA1S12A2A3A2A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma mat_r0_4 : ltac2:(tb__ "0|2|
S3S31SeA1S6dS5bS15Vc;A1U3S5aS5eSbA1S12A2A3M0U4M1S13A3S2fSeS5bG0G1S5aS5fSbA1S13A2A3A2A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma ent_r0 : ltac2:(tb__ "0|0|
S3S27S6cS5bS5bS15Vc;A1U3S5aS5eSbA1S12A2A3U4S5aS5fSbA1S13A2A3S18Vc;A1S2cS2dS4aS6A2A1A3S28A3").
Proof using . vm_cast_no_check (@eq_refl bool true). Qed.

Lemma ex_Xr0 : ltac2:(tb__ "0|1|
S7VGH;S21Vc;A1M0R1A2S43S0S46S0VK;S15Vc;A1R2A4S42S4VFAM;S4cS12G0R3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using rho0.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [Hsm HK]. left.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  assert (F0 : bv_unsigned (rw rho 123%positive) = 0).
  { pose proof (pick_fact rho _ (SPEq (SVar 123) (SLit 0)) HF ltac:(cbn; tauto)) as X. cbn [holds eval] in X.
    rewrite X. rewrite lit_unsigned. reflexivity. }
  pose proof (smatch_materialize segs rho (X_r0 c) 3 LN _ tr ms md _ _ _ _ mat_r0_3 eq_refl Hsm) as Hsm1.
  set (rho1 := rho_set_rl rho LN _) in Hsm1.
  pose proof (smatch_materialize segs rho1 _ 4 LP _ tr ms md _ _ _ _ mat_r0_4 eq_refl Hsm1) as Hsm2.
  set (rho2 := rho_set_rl rho1 LP _) in Hsm2.
  pose proof (SP_entails segs K _ (K_r c) [] rho2 (tr, mkCfg ms md) ent_r0 (conj Hsm2 HK)) as HSP.
  set (rho3 := rho_sub rho2 []) in *.
  assert (Erw : forall i, rw rho3 i = rw rho i) by (intros i; reflexivity).
  destruct HG as (Hbase & _ & _ & _). destruct Hbase as (B1 & B2 & B3 & Bn).
  eapply (reenter_cut segs NF VN LN LP K rho0 (rcuts c) (N_Kr c) rho3).
  - cbn. tauto.
  - split; [|split; [|split]].
    + split; [|split; [|split]].
      * intros i Hi. rewrite Erw. apply B1. exact Hi.
      * exact B2.
      * intros l Hl1 Hl2. subst rho3 rho2 rho1. cbn [rl rho_sub]. rewrite rho_set_rl2_other by assumption. apply B3; assumption.
      * unfold nval. rewrite Erw. exact Bn.
    + intros HX. discriminate HX.
    + cbn [rn_init N_Kr]. unfold Uv. cbn [eval]. rewrite Erw, F0. intros j Hj. lia.
    + exact Logic.I.
  - exact HSP.
  - apply (rmeas_nonneg NF VN LN LP). apply okb_of. cbn. tauto.
  - apply (rmeas_lt_ph NF VN LN LP); [apply okb_of; cbn; tauto | apply okb_of; cbn; tauto | reflexivity].
Qed.

Definition arrN : sobj := O_nxt (arrK vN).
Definition arrP : sobj := O_prv (arrK vN).

Lemma ex_Eret : ltac2:(tb__ "0|1|
S7VGH;S1dVc;A1M0R1A2S43S0S46S0VK;S1cVc;A1R2A4S42S4VFAM;S4cS12G0R3A3R1A2VQ;R1A1A2Lw;A3F_;Frho;").
Proof using rho0.
  intros rho HG. apply etriple_now. intros [tr [ms md]] [Hsm HK]. right.
  pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
  assert (FN : 5 <= bv_unsigned (rw rho 13%positive) <= 2 ^ 20).
  { pose proof (pick_fact rho _ (SPUle (SLit 5) vN) HF ltac:(cbn; tauto)) as X1.
    pose proof (pick_fact rho _ (SPUle vN (SLit two20)) HF ltac:(cbn; tauto)) as X2.
    cbn [holds eval vN] in X1, X2. rewrite lit_unsigned in X1, X2. change (5 mod 2 ^ 64) with 5 in X1.
    change (two20 mod 2 ^ 64) with (2 ^ 20) in X2. lia. }
  destruct HG as (Hbase & Halln & _ & _). specialize (Halln eq_refl). destruct Halln as [AN AP].
  destruct Hbase as (B1 & B2 & B3 & Bn). unfold nval in AN, AP.

  assert (Hsm1 : smatch segs rho (obj_upd (E_ret c) 3 arrN) (tr, mkCfg ms md)).
  { eapply smatch_obj_upd; [reflexivity | exact Hsm | reflexivity | reflexivity |].
    intros Hrom Hwf Ho. unfold arrN, O_nxt, arrK, idx_tmpl. eapply (obj_holds_list_arr segs rho ms vNXT _ LN vN _ _ Hrom Hwf Ho).
    - change (SAlu ALU_SLL vN (SLit 2)) with (IX4 vN). rewrite soff_IX4 by (cbn [eval vN]; lia). reflexivity.
    - reflexivity.
    - exact AN. }
  assert (Hsm2 : smatch segs rho (obj_upd (obj_upd (E_ret c) 3 arrN) 4 arrP) (tr, mkCfg ms md)).
  { eapply smatch_obj_upd; [reflexivity | exact Hsm1 | reflexivity | reflexivity |].
    intros Hrom Hwf Ho. unfold arrP, O_prv, arrK, idx_tmpl. eapply (obj_holds_list_arr segs rho ms vPRV _ LP vN _ _ Hrom Hwf Ho).
    - change (SAlu ALU_SLL vN (SLit 2)) with (IX4 vN). rewrite soff_IX4 by (cbn [eval vN]; lia). reflexivity.
    - reflexivity.
    - exact AP. }
  change (smatch segs rho (P_ret c) (tr, mkCfg ms md)) in Hsm2.

  pose proof (smatch_set_rl segs rho LN (rl rho0 LN) (P_ret c) _ ltac:(vm_compute; reflexivity) Hsm2) as Hsm3.
  pose proof (smatch_set_rl segs _ LP (rl rho0 LP) (P_ret c) _ ltac:(vm_compute; reflexivity) Hsm3) as Hsm4.
  set (rhof := rho_set_rl (rho_set_rl rho LN (rl rho0 LN)) LP (rl rho0 LP)) in *.
  exists (mkLeaf (P_ret c) RsSymJump), rhof. split; [left; reflexivity|]. split; [|split; [exact Hsm4 | exact HK]].
  split; [|split].
  - intros i Hi. rewrite B1 by exact Hi. reflexivity.
  - intros l. subst rhof. destruct (Pos.eq_dec l LP) as [->|HlP]; [rewrite rho_set_rl_at; reflexivity|].
    rewrite rho_set_rl_other by exact HlP.
    destruct (Pos.eq_dec l LN) as [->|HlN]; [rewrite rho_set_rl_at; reflexivity|].
    rewrite rho_set_rl_other by exact HlN. apply B3; assumption.
  - intros a. rewrite B2. reflexivity.
Qed.

End EX.

Lemma rchk_P : ltac2:(tb__ "0|0|
S3S27S4eS0S34S14S12S13U1f4S26S5dA1S16S5dA1S17S5dA1A9S28A3").
Proof. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg.check_rcfg. rewrite <- (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.cuts_edges_fast_eq segs). vm_cast_no_check (@eq_refl bool true). Qed.

Theorem run2d_sum_ex : ltac2:(tb__ "0|0|
S2aS65A1S64OF_;F_;S7S43S0S46S0R2S61S5dA1R1A4S47S0R2S34R1S60S5dA1A5A3Frho;FK;").
Proof.
  intros K rho w Hw.
  assert (Hn : nval VN rho < 2 ^ 32).
  { destruct w as [tr [ms md]]. destruct Hw as [Hsm _]. pose proof (smatch_facts segs _ _ _ _ _ Hsm) as HF.
    pose proof (pick_fact rho _ (SPUle vN (SLit two20)) HF ltac:(cbn; tauto)) as X.
    cbn [holds eval vN] in X. rewrite lit_unsigned in X. change (two20 mod 2 ^ 64) with (2 ^ 20) in X. unfold nval. change (rw rho VN) with (rw rho 13%positive). lia. }
  refine (rcfg_complete_auto segs NF VN LN LP rho 500 (ecutpcs R2_P) (rcuts R2_P) (rexits R2_P) K
            (LQ segs K NF rho (Posts_r2 R2_P)) rchk_P _ (N_Pre R2_P) rho ltac:(cbn; tauto) _ w Hw).
  - intros E rho' HinE HG.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
    + apply ex_Xr0. exact HG.
    + apply ex_Xr. exact HG.
    + apply ex_Xrf. exact HG.
    + apply ex_Xc2. exact HG.
    + apply ex_Xg2. exact HG.
    + apply ex_Eret. exact HG.
  -
    split; [|split; [|split]]; try exact Logic.I.
    + split; [|split; [|split]]; intros; try reflexivity. exact Hn.
    + intros HX. discriminate HX.
Qed.
End Lib_tess_run2d_ex.

Module Lib_tess_polygon.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_chk.

Import ListNotations.
Close Scope bv_scope.
Theorem tess_polygon_sum : ltac2:(tb__ "0|0|
S42OF_;S2aS65A1S64OF_;F_;S7S48S0R3R2A3S45S0R4S46S0R3S3bS35S2cS9A1A2R2A4S47S0R3S34R2S75A5A4F_;Frho;FK;Fok;").
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segs FUEL_pg (pg_cutpcs2 PG_P) NF (pcuts PG_P) (pexits PG_P)
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho Posts_pg) Hok).
  - rewrite pcuts_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_pg.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    + apply exit_post; [left; reflexivity | exact HagE].
    + apply exit_post; [right; left; reflexivity | exact HagE].
    + apply (exit_sc3 ok K Hok rho). exact HagE.
    + apply (exit_sc4 ok K Hok rho). exact HagE.
    + apply (exit_r2 ok K Hok rho). exact HagE.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
End Lib_tess_polygon.

Module Lib_tess_polygon_ex_c1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_ex_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma elc_4 : ltac2:(tb__ "0|2|
S3S27S66S0S36S37S35A1S34S67S35A1U4S3dS39S35A1Z10S29S2dS3cS6A2M0S2bS3cS6S3eS30A1M1SdP7bA1A4S29G0S2bS3cS6G1ScZ1A1A4S2cG0A1A3A3A3A7S28A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma elc_13 : ltac2:(tb__ "0|2|
S3S27S66S0S36S37S35A1S34S67S35A1UdS3dS3aS35A1Z10S29S2dS3cS6A2M0S2bS3cS6S3eS30A1M1SdP7bA1A4S29G0S2bS3cS6G1ScZ0A1A4S2cG0A1A3A3A3A7S28A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_tess_polygon_ex_c1.

Module Lib_tess_polygon_ex_c2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundB OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundL OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymComplete OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G2.Lib_tess_polygon_ex_nodes.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma elc_9 : ltac2:(tb__ "0|0|
S3S27S66S0S36S37S35A1S34S67S35A1U9S3dS38S35A1ZcS2cS2dS3cS6A2A1A3A7S28A3").
Proof. apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.elcut_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
End Lib_tess_polygon_ex_c2.
