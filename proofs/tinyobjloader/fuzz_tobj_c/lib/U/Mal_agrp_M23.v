(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "app"; "true"; "andb"; "false"; "negb"; "pair"; "orb"; "prod"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "lt"; "add"; "ltb"; "land"; "pow"; "eqb"; "modulo"; "even"; "leb"; "opp"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SAlu"; "SVar"; "SPBranch"; "SAluW"; "SPNot"; "swf"; "SMd"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "zeval"; "zholds"; "psupported"; "zsupported"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I"; "zl2"; "zr2"; "ia_sc"; "rho2"; "icnt0"; "icnt1"; "iu"; "ia_req"; "inos"; "isize"; "iszc"; "usg"; "usg2"; "ineeded"; "iplan"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp_M23.Run"; "FM"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkSeg"; "POST"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2"; "F_A"; "F_B"; "F_J"; "SJ3"; "SJA"; "SJB"; "SM23"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M"; "m1_hi"; "m1_lo"; "@Corelib.Lists.ListDef"; "Forall"; "@Stdlib.Lists.List"; "forallb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SLTU"; "ALU_SUB"; "BC_GEU"; "BC_LT"; "BC_LTU"; "BC_NE"; "M_MUL"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "page_round"; "is_bouncing"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W"; "K_ia"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "sprop_vars_all"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink"; "below200"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.TRRulesK"; "tr_rules"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St"; "F_CTX"; "F_G"; "F_M"; "F_M1"; "F_SZ"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymSummary SymCall SymEntail Glue3 ExampleMemcpy.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CallocLib.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLemmasBase MallocWfArith MallocWfGroup MallocLayout MallocIface MallocIfaceI Contract ContractI Glue ReprGlue ObjBytes
  ZEval ZBits WalkArith WalkLink WalkReab ImageDelta AllocGroupPost TRRulesK Zones2 WalkSeg.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_St2 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G1.Mal_agrp_I OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_R OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G4.Mal_agrp_W OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G14.Mal_agrp_M OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rMA OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rMB OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_agrp__G2.Mal_agrp_rMC.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Notation RQ := (SAlu ALU_ADD (SAlu ALU_ADD (SVar 13%positive) (SAlu ALU_AND (SLit 4095) (SAlu ALU_SUB (SLit 18446744073709551596) (SVar 13%positive)))) (SLit 20)) (only parsing).
Notation NEEDED e :=
  (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SVar 191%positive) e) (SAlu ALU_AND (SAlu ALU_SUB (SLit 18446744073709551600) (SMd M_MUL (SVar 191%positive) e)) (SLit 4095))) (SLit 16)) (only parsing).

Lemma if_true {A} (a b : A) : ltac2:(tb__ "0|0|
S0VA;S4VA;L_;S6Va;Vb;X4x2Va;A3"). Proof. reflexivity. Qed.
Lemma if_false {A} (a b : A) : ltac2:(tb__ "0|0|
S0VA;S4VA;L_;S8Va;Vb;X4x2Vb;A3"). Proof. reflexivity. Qed.

Lemma page_round_alt y : ltac2:(tb__ "0|0|
SdZ0Vy;A2S0S3S4dVy;A1S10Vy;S15S18Vy;A1Z1000A2A2A3F_;").
Proof. intros Hy. unfold page_round, PGSZ. Z.to_euclidean_division_equations; lia. Qed.
Lemma land4095 x : ltac2:(tb__ "0|0|
SdZ0Vx;A2S0S3S12Vx;ZfffA2S15Vx;Z1000A2A3F_;").
Proof. intros. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land4095l x : ltac2:(tb__ "0|0|
SdZ0Vx;A2S0S3S12ZfffVx;A2S15Vx;Z1000A2A3F_;").
Proof. intros. rewrite Z.land_comm. apply land4095. lia. Qed.

Section M23.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S52S35VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Let s : astate := ia_s ia. Let L : layout := ia_L ia.
Let sc : Z := ia_sc ia. Let mW : word -> option byte := ia_mW ia. Let vm : VmMaps := ia_vm ia.
Let K := K_ia Kc ia.

Lemma ze_small_lit z : ltac2:(tb__ "0|0|
S1SdZ0Vz;A2SfVz;S13Z2Z40A2A2A2S0S3S22S27Via;A1S26Via;A1S1aVz;A1A3Vz;A3F_;").
Proof using . intros Hz. rewrite (ze_lit ia). apply Z.mod_small. lia. Qed.
Lemma ze_u2 : ltac2:(tb__ "0|0|
S0S3S22S27Via;A1S26Via;A1S1bS43S1cPc4A1S1cPc0A1A3A3S10S31Via;A1S32Via;A1A2A3").
Proof using Hi.
  rewrite (ze_alu ia), (zs196 ia Hi), (zs192 ia Hi). cbn [zalu]. pose proof (ctx_ranges ia Hi). pose proof (usg_bounds ia Hi).
  rewrite Z.mod_small; lia.
Qed.
Lemma ze_sllw_small e k : ltac2:(tb__ "0|5|
S1SdZ0M0S22S27Via;A1M1S26Via;A1M2Ve;A3M3A2SdG3S13Z2M4Z14A2A2A2S1SdG0Vk;A2SdVk;G4A2A2S0S3S22G1G2S1eS45Ve;S1aVk;A1A3A3SeS13G4Vk;A2G3A2A3F_;F_;").
Proof using .
  clear K. intros He Hk. rewrite (ze_aluw ia), (ze_lit ia). cbn [zalu]. set (c := zeval (zr2 ia) (zl2 ia) e) in *.
  rewrite (Z.mod_small k (2 ^ 64)) by lia. rewrite (Z.mod_small k (2 ^ 32)) by lia. rewrite (Z.mod_small c) by lia.
  rewrite (Z.mod_small k 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  assert (P : 2 ^ k <= 4) by (change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia). assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.mod_small by nia. unfold sx32, toS. rewrite (Z.mod_small _ (2 ^ 32)) by nia.
  replace (c * 2 ^ k <? 2 ^ (32 - 1)) with true by (symmetry; apply Z.ltb_lt; nia). rewrite Z.mod_small by nia. lia.
Qed.
Lemma ze_sllw175_1 : ltac2:(tb__ "0|0|
S0S3S22S27Via;A1S26Via;A1S1eS45S1cPafA1S1aZ1A1A3A3SeZ2S2aVia;A1A2A3").
Proof using Hi. rewrite ze_sllw_small by (rewrite ?(zs175 ia Hi); pose proof (icnt0_range ia Hi); lia). rewrite (zs175 ia Hi). reflexivity. Qed.
Lemma ze_sllw175_2 : ltac2:(tb__ "0|0|
S0S3S22S27Via;A1S26Via;A1S1eS45S1cPafA1S1aZ2A1A3A3SeZ4S2aVia;A1A2A3").
Proof using Hi. rewrite ze_sllw_small by (rewrite ?(zs175 ia Hi); pose proof (icnt0_range ia Hi); lia). rewrite (zs175 ia Hi). reflexivity. Qed.
Lemma ze_sllw163_1 : ltac2:(tb__ "0|0|
S0S3S22S27Via;A1S26Via;A1S1eS45S1cPa3A1S1aZ1A1A3A3SeZ2S2bVia;A1A2A3").
Proof using Hi. rewrite ze_sllw_small by (rewrite ?(zs163 ia Hi); pose proof (icnt1_range ia Hi); lia). rewrite (zs163 ia Hi). reflexivity. Qed.
Lemma ze_and12 k : ltac2:(tb__ "0|0|
S1SdZ0Vk;A2SfVk;S13Z2ZcA2A2A2S0S3S22S27Via;A1S26Via;A1S1bS44S1cPcA1S1aVk;A1A3A3S12Vsc;Vk;A2A3F_;").
Proof using Hi.
  intros Hk. rewrite (ze_alu ia), (zs12 ia Hi), (ze_lit ia). cbn [zalu]. pose proof (iok_sc ia Hi). unfold sc. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma ze_rq : ltac2:(tb__ "0|2|
S0S3S22S27Via;A1S26Via;A1S1bS43S1bS43S1cPdA1M0S1bS44S1aZfffA1S1bS47S1aZffffffffffffffecA1G0A3A3A3S1aZ14M1A1A3A3S4dS10S2dVia;A1G1A2A1A3").
Proof using Hi.
  rewrite !(ze_alu ia), (zs13 ia Hi), !(ze_lit ia). cbn [zalu].
  pose proof (iok_req ia Hi) as RQ0. pose proof (class_size_bounds (ia_sc ia) (iok_sc ia Hi)) as CB. unfold IB in RQ0.
  set (r := ia_req ia) in *.
  change (18446744073709551596 mod 2 ^ 64) with (2 ^ 64 - 20). change (4095 mod 2 ^ 64) with 4095. change (20 mod 2 ^ 64) with 20.
  rewrite land4095l by (apply Z.mod_pos_bound; lia).
  replace (((2 ^ 64 - 20 - r) mod 2 ^ 64) mod 4096) with ((- (r + 20)) mod 4096).
  2:{ rewrite (Z.mod_small (2 ^ 64 - 20 - r)) by lia. clear - RQ0 CB. Z.to_euclidean_division_equations. lia. }
  rewrite page_round_alt by lia. pose proof (Z.mod_pos_bound (- (r + 20)) 4096 ltac:(lia)). rewrite !Z.mod_small by lia. lia.
Qed.

Lemma ze_needed e : ltac2:(tb__ "0|5|
S0S4S25Ve;A1S6A3S1SdZ1S22S27Via;A1M0S26Via;A1M1Ve;A3M2A2SdG2Z20A2A2S0S3S22G0G1S1bS43S1bS43S21S4cS1cPbfA1Ve;A3M3S1bS44S1bS47S1aZfffffffffffffff0A1G3A3S1aZfffA1A3A3S1aZ10M4A1A3A3S4dS10SeS2fVia;A1G2A2G4A2A1A3F_;F_;").
Proof using Hi.
  intros He Hr. rewrite !(ze_alu ia), !(ze_mul ia), (zs191 ia Hi), !(ze_lit ia). cbn [zalu].
  pose proof (isize_range ia Hi) as SR. set (c := zeval (zr2 ia) (zl2 ia) e) in *. set (sz := isize ia) in *.
  change (18446744073709551600 mod 2 ^ 64) with (2 ^ 64 - 16). change (4095 mod 2 ^ 64) with 4095. change (16 mod 2 ^ 64) with 16.
  assert (P : 16 <= sz * c <= 131056 * 32) by nia.
  rewrite (Z.mod_small (sz * c)) by lia. rewrite land4095 by (apply Z.mod_pos_bound; lia).
  replace (((2 ^ 64 - 16 - sz * c) mod 2 ^ 64) mod 4096) with ((- (sz * c + 16)) mod 4096).
  2:{ rewrite (Z.mod_small (2 ^ 64 - 16 - sz * c)) by lia. clear - P. Z.to_euclidean_division_equations. lia. }
  rewrite page_round_alt by lia. pose proof (Z.mod_pos_bound (- (sz * c + 16)) 4096 ltac:(lia)). rewrite !Z.mod_small by lia. lia.
Qed.
Lemma ze_cmp10 : ltac2:(tb__ "0|3|
S0S3S22S27Via;A1S26Via;A1S1bS44S1bS46S1bS44S1cPcA1S1aZ3M0A1A3S1aZ1M1A1A3S1bS46S1aZ8000A1S1cPacA1A3A3A3S4S3L_;S7S14S12Vsc;G0A2Z0M2A2S11SeZ8Z1000A2S30Via;A1A2A2G1G2X4x2A3").
Proof using Hi.
  change (8 * 4096) with 32768.
  rewrite (ze_alu ia), (ze_alu ia), ze_and12, (ze_alu ia), (zs172 ia Hi), !(ze_lit ia) by lia. cbn [zalu].
  pose proof (iok_sc ia Hi) as SC. pose proof (iszc_range ia Hi) as ZR.
  assert (L3 : 0 <= Z.land sc 3 <= 3).
  { split; [apply Z.land_nonneg; unfold sc; lia|]. change 3 with (Z.ones 2) at 1. rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound sc (2 ^ 2)). lia. }
  change (32768 mod 2 ^ 64) with 32768. change ((1 mod 2 ^ 64) mod 2 ^ 64) with 1. change (32768 mod 2 ^ 64) with 32768.
  rewrite (Z.mod_small (Z.land sc 3)) by lia. rewrite (Z.mod_small (iszc ia)) by lia.
  destruct (Z.land sc 3 =? 0) eqn:E0; [apply Z.eqb_eq in E0; rewrite E0 | apply Z.eqb_neq in E0; replace (Z.land sc 3 <? 1) with false by (symmetry; apply Z.ltb_ge; lia)];
    cbn [Z.ltb andb]; destruct (32768 <? iszc ia); reflexivity.
Qed.

Lemma nos_t : ltac2:(tb__ "0|0|
S2S0S3S2eVia;A1Z0A3A1S0S4S4eVs;Vsc;A2S6A3F_;").
Proof using . unfold inos. fold s sc. destruct (is_bouncing s sc); [reflexivity | intros H; exfalso; exact (H eq_refl)]. Qed.
Lemma nos_f : ltac2:(tb__ "0|0|
S0S3S2eVia;A1Z0A3S0S4S4eVs;Vsc;A2S8A3F_;").
Proof using . unfold inos. fold s sc. destruct (is_bouncing s sc); [intros H; discriminate H | reflexivity]. Qed.
Lemma even_t : ltac2:(tb__ "0|0|
S0S3S12Vsc;Z1A2Z0A3S0S4S16Vsc;A1S6A3F_;").
Proof using Hi. intros H. change 1 with (Z.ones 1) in H. rewrite Z.land_ones in H by (pose proof (iok_sc ia Hi); unfold sc; lia). rewrite Z.even_spec. exists (sc / 2). change (2 ^ 1) with 2 in H. lia. Qed.
Lemma even_f : ltac2:(tb__ "0|0|
S2S0S3S12Vsc;Z1A2Z0A3A1S0S4S16Vsc;A1S8A3F_;").
Proof using Hi.
  intros H. change 1 with (Z.ones 1) in H. rewrite Z.land_ones in H by (pose proof (iok_sc ia Hi); unfold sc; lia). change (2 ^ 1) with 2 in H.
  destruct (Z.even sc) eqn:E; [|reflexivity]. exfalso. apply Z.even_spec in E as [k Hk]. apply H. rewrite Hk. rewrite Z.mul_comm, Z.mod_mul. reflexivity. lia.
Qed.

Lemma iu_unfold : ltac2:(tb__ "0|1|
S0S3S2cVia;A1S4S3L_;S7S16Vsc;A1S11Vsc;Z20A2A2S10S31Via;A1M0S32Via;A1A2G0X4x2A3").
Proof using . reflexivity. Qed.
Lemma icnt1_unfold : ltac2:(tb__ "0|a|
S0S3S2bVia;A1S4S3L_;M0S7S11S2cVia;A1SeZ4M1S2aVia;A1M2A2A2S9S4eVs;Vsc;A2A1A2G0S7S14S12Vsc;Z3M3A2M4Z1A2S11SeZ8Z1000M5A2S30Via;A1M6A2M7A2Z2M8G0S7S14G4G8A2S11SeG1G5A2G6A2A2G3G0S7S14G4Z0A2M9G7A2G3G0S7G9S11SeG8G5A2G6A2A2Z5G2X4x2X4x2X4x2X4x2G2X4x2A3").
Proof using . reflexivity. Qed.
Lemma iplan_final : ltac2:(tb__ "0|7|
S0ScS3S3A2M0S34Via;A1S4G0L_;M1S7S9S4eVs;Vsc;A2A1S17S2bVia;A1M2Z7A2A2G1SbS11S4dS10S2dVia;A1Z14A2A1M3S10S2fVia;A1M4Z10M5A2A2S7S17SeZ4Z1000A2G3A2S11S2cVia;A1SeZ2G2A2A2A2A2SaS3S3Z1G3A4SaS3S3G2S4dS10SeG4G2A2G5A2A1A4M6X4x2G6X4x2A3").
Proof using . unfold iplan, mmap_plan. replace (ia_req ia + IB + UNIT) with (ia_req ia + 20) by (unfold IB, UNIT; lia). reflexivity. Qed.

Section Facts.
Let zr := zr2 ia. Let zl := zl2 ia.
Lemma R_ltu e1 e2 z1 z2 : ltac2:(tb__ "0|0|
S0S3S22Vzr;Vzl;Ve1;A3Vz1;A3S0S3S22Vzr;Vzl;Ve2;A3Vz2;A3S23Vzr;Vzl;S1dS4aVe1;Ve2;A3A3SfVz1;Vz2;A2F_;F_;F_;").
Proof using ia. cbn [zholds zcond]. intros -> -> H. apply Z.ltb_lt in H. exact H. Qed.
Lemma R_nltu e1 e2 z1 z2 : ltac2:(tb__ "0|0|
S0S3S22Vzr;Vzl;Ve1;A3Vz1;A3S0S3S22Vzr;Vzl;Ve2;A3Vz2;A3S23Vzr;Vzl;S1fS1dS4aVe1;Ve2;A3A1A3SdVz2;Vz1;A2F_;F_;F_;").
Proof using ia. cbn [zholds zcond]. intros -> -> H. destruct (z1 <? z2) eqn:E; [exfalso; exact (H eq_refl) | apply Z.ltb_ge in E; exact E]. Qed.
Lemma R_geu e1 e2 z1 z2 : ltac2:(tb__ "0|0|
S0S3S22Vzr;Vzl;Ve1;A3Vz1;A3S0S3S22Vzr;Vzl;Ve2;A3Vz2;A3S23Vzr;Vzl;S1dS48Ve1;Ve2;A3A3SdVz2;Vz1;A2F_;F_;F_;").
Proof using ia. cbn [zholds zcond]. intros -> -> H. apply negb_true_iff in H. apply Z.ltb_ge in H. exact H. Qed.
Lemma R_ngeu e1 e2 z1 z2 : ltac2:(tb__ "0|0|
S0S3S22Vzr;Vzl;Ve1;A3Vz1;A3S0S3S22Vzr;Vzl;Ve2;A3Vz2;A3S23Vzr;Vzl;S1fS1dS48Ve1;Ve2;A3A1A3SfVz1;Vz2;A2F_;F_;F_;").
Proof using ia. cbn [zholds zcond]. intros -> -> H. destruct (z1 <? z2) eqn:E; [apply Z.ltb_lt in E; exact E | exfalso; apply H; reflexivity]. Qed.
Lemma R_ne e1 e2 z1 z2 : ltac2:(tb__ "0|0|
S0S3S22Vzr;Vzl;Ve1;A3Vz1;A3S0S3S22Vzr;Vzl;Ve2;A3Vz2;A3S23Vzr;Vzl;S1dS4bVe1;Ve2;A3A3S2S0S3Vz1;Vz2;A3A1F_;F_;F_;").
Proof using ia. cbn [zholds zcond]. intros -> -> H. apply negb_true_iff in H. apply Z.eqb_neq in H. exact H. Qed.
Lemma R_nne e1 e2 z1 z2 : ltac2:(tb__ "0|0|
S0S3S22Vzr;Vzl;Ve1;A3Vz1;A3S0S3S22Vzr;Vzl;Ve2;A3Vz2;A3S23Vzr;Vzl;S1fS1dS4bVe1;Ve2;A3A1A3S0S3Vz1;Vz2;A3F_;F_;F_;").
Proof using ia. cbn [zholds zcond]. intros -> -> H. destruct (z1 =? z2) eqn:E; [apply Z.eqb_eq in E; exact E | exfalso; apply H; reflexivity]. Qed.
Lemma R_lt e1 e2 z1 z2 : ltac2:(tb__ "0|2|
S0S3S22Vzr;Vzl;Ve1;A3Vz1;A3S0S3S22Vzr;Vzl;Ve2;A3Vz2;A3S1SdZ0M0Vz1;A2SfVz1;S13Z2Z3fA2M1A2A2S1SdG0Vz2;A2SfVz2;G1A2A2S23Vzr;Vzl;S1dS49Ve1;Ve2;A3A3SfVz1;Vz2;A2F_;F_;F_;F_;F_;").
Proof using sc. cbn [zholds zcond]. intros -> -> H1 H2 H. rewrite !toS_small in H by lia. apply Z.ltb_lt in H. exact H. Qed.
Lemma R_nlt e1 e2 z1 z2 : ltac2:(tb__ "0|2|
S0S3S22Vzr;Vzl;Ve1;A3Vz1;A3S0S3S22Vzr;Vzl;Ve2;A3Vz2;A3S1SdZ0M0Vz1;A2SfVz1;S13Z2Z3fA2M1A2A2S1SdG0Vz2;A2SfVz2;G1A2A2S23Vzr;Vzl;S1fS1dS49Ve1;Ve2;A3A1A3SdVz2;Vz1;A2F_;F_;F_;F_;F_;").
Proof using sc. cbn [zholds zcond]. intros -> -> H1 H2 H. rewrite !toS_small in H by lia. destruct (z1 <? z2) eqn:E; [exfalso; exact (H eq_refl) | apply Z.ltb_ge in E; exact E]. Qed.
End Facts.
End M23.

Lemma if10_ne (b : bool) : ltac2:(tb__ "0|1|
S2S0S3S4S3Lb;Vb;Z1Z0M0X4x2G0A3A1S0S4Vb;S6A3F_;"). Proof. destruct b; [reflexivity | intros H; exfalso; exact (H eq_refl)]. Qed.
Lemma if10_eq (b : bool) : ltac2:(tb__ "0|1|
S0S3S4S3Lb;Vb;Z1Z0M0X4x2G0A3S0S4Vb;S8A3F_;"). Proof. destruct b; [intros H; discriminate H | reflexivity]. Qed.

Ltac ze_tac ia Hi :=
  rewrite ?(ze_u2 ia Hi), ?(ze_cmp10 ia Hi), ?(ze_rq ia Hi), ?(zs_size16 ia Hi);
  rewrite ?(ze_sllw175_1 ia Hi), ?(ze_sllw175_2 ia Hi), ?(ze_sllw163_1 ia Hi); rewrite ?(ze_and12 ia Hi) by lia;
  rewrite ?(zs12 ia Hi), ?(zs172 ia Hi), ?(zs175 ia Hi), ?(zs192 ia Hi), ?(zs198 ia Hi), ?(zs199 ia Hi), ?(zs163 ia Hi);
  repeat match goal with |- context [zeval _ _ (SLit ?z)] => rewrite (ze_small_lit ia z) by lia end;
  reflexivity.

Ltac zread ia Hi H :=
  first [ eapply (R_ltu ia) in H; [| ze_tac ia Hi | ze_tac ia Hi]
        | eapply (R_nltu ia) in H; [| ze_tac ia Hi | ze_tac ia Hi]
        | eapply (R_geu ia) in H; [| ze_tac ia Hi | ze_tac ia Hi]
        | eapply (R_ngeu ia) in H; [| ze_tac ia Hi | ze_tac ia Hi]
        | eapply (R_ne ia) in H; [| ze_tac ia Hi | ze_tac ia Hi]
        | eapply (R_nne ia) in H; [| ze_tac ia Hi | ze_tac ia Hi]
        | eapply (R_lt ia) in H; [| ze_tac ia Hi | ze_tac ia Hi | lia | lia]
        | eapply (R_nlt ia) in H; [| ze_tac ia Hi | ze_tac ia Hi | lia | lia] ];

  try (apply if10_ne in H; let Hb := fresh "F" in apply andb_prop in H as [H Hb]; apply Z.eqb_eq in H; apply Z.ltb_lt in Hb);
  try (apply if10_eq in H).

Section Run.
Variable ia : instA.
Hypothesis Hi : instA_ok ia.

Lemma ineeded_facts : ltac2:(tb__ "0|2|
S1S1SdZ1000M0S33Via;A1M1A2SdG1S13Z2Z17A2A2A2S0S3S15G1G0A2Z0A3A2").
Proof using Hi.
  pose proof (isize_range ia Hi) as SR. pose proof (icnt1_range ia Hi) as CR. pose proof (iok_req ia Hi) as RQ0.
  pose proof (class_size_bounds (ia_sc ia) (iok_sc ia Hi)) as CB. unfold IB in RQ0.
  assert (PR : forall y, 0 < y <= 2 ^ 23 - 4096 -> 4096 <= page_round y <= 2 ^ 23 /\ page_round y mod 4096 = 0).
  { intros y Hy. unfold page_round, PGSZ. Z.to_euclidean_division_equations. lia. }
  unfold ineeded. rewrite (iplan_final ia).
  assert (isize ia * icnt1 ia <= 131056 * 32) by nia.
  destruct (negb _ && _)%bool; [destruct (_ || _)%bool|]; cbn [snd]; apply PR; unfold isize in *; nia.
Qed.
Lemma ZF_A : ltac2:(tb__ "0|0|
S41S19S23S27Via;A1S26Via;A1A2S38A3").
Proof using Hi. unfold F_A. repeat constructor. cbn [zholds zcond]. rewrite (ze199 ia Hi), (ze_lit ia). pose proof (iu_range ia Hi). rewrite Z.mod_small by lia. lia. Qed.
Lemma ZF_B : ltac2:(tb__ "0|0|
S41S19S23S27Via;A1S26Via;A1A2S39A3").
Proof using Hi. unfold F_B. pose proof (icnt1_range ia Hi). repeat constructor; cbn [zholds zcond]; rewrite (ze163 ia Hi), (ze_lit ia); rewrite Z.mod_small by lia; lia. Qed.
Lemma ZF_J : ltac2:(tb__ "0|0|
S41S19S23S27Via;A1S26Via;A1A2S3aA3").
Proof using Hi.
  pose proof (iplan_range ia Hi) as PR. pose proof ineeded_facts as NF. unfold F_J.
  repeat constructor; cbn [zholds zcond]; rewrite ?(ze176 ia Hi), ?(ze177 ia Hi), ?(ze_lit ia); try (rewrite ?Z.mod_small by lia; lia).
  rewrite (zr2_177 ia Hi). change (2 ^ 12) with 4096. rewrite (Z.mod_small (ineeded ia)) by lia. lia.
Qed.
Definition FM (x : m1v) : list sprop := ltac2:(tb__ "0|0|
S5S19S54S5S19S55S5S19S53S5S19S57S56Vx;A1A3A3A3A3").
Lemma ZF_allA x : ltac2:(tb__ "0|1|
S1SdS40Vx;A1S28Via;A1M0A2SdG0S3fVx;A1A2A2S41S19S23S27Via;A1S26Via;A1A2S5S19S36Vx;A1S38A3A3F_;").
Proof using Hi. intros Hx. apply Forall_app. split; [exact (ZF_allM1 ia Hi x Hx) | exact ZF_A]. Qed.
Lemma ZF_allB x : ltac2:(tb__ "0|1|
S1SdS40Vx;A1S28Via;A1M0A2SdG0S3fVx;A1A2A2S41S19S23S27Via;A1S26Via;A1A2S5S19S36Vx;A1S5S19S38S39A3A3A3F_;").
Proof using Hi. intros Hx. apply Forall_app. split; [exact (ZF_allM1 ia Hi x Hx) |]. apply Forall_app. split; [exact ZF_A | exact ZF_B]. Qed.
Lemma ZF_allJ x : ltac2:(tb__ "0|1|
S1SdS40Vx;A1S28Via;A1M0A2SdG0S3fVx;A1A2A2S41S19S23S27Via;A1S26Via;A1A2S5S19S36Vx;A1S3aA3A3F_;").
Proof using Hi. intros Hx. apply Forall_app. split; [exact (ZF_allM1 ia Hi x Hx) | exact ZF_J]. Qed.
Lemma FA_vars x : ltac2:(tb__ "0|0|
S0S4S42S19S50S51A1S5S19S36Vx;A1S38A3A3S6A3"). Proof using . destruct x; reflexivity. Qed.
Lemma FA_sup x : ltac2:(tb__ "0|0|
S0S4S42S19S24S5S19S36Vx;A1S38A3A3S6A3"). Proof using . destruct x; reflexivity. Qed.
Lemma FB_vars x : ltac2:(tb__ "0|0|
S0S4S42S19S50S51A1S5S19S36Vx;A1S5S19S38S39A3A3A3S6A3"). Proof using . destruct x; reflexivity. Qed.
Lemma FB_sup x : ltac2:(tb__ "0|0|
S0S4S42S19S24S5S19S36Vx;A1S5S19S38S39A3A3A3S6A3"). Proof using . destruct x; reflexivity. Qed.
Lemma FJ_vars x : ltac2:(tb__ "0|0|
S0S4S42S19S50S51A1S5S19S36Vx;A1S3aA3A3S6A3"). Proof using . destruct x; reflexivity. Qed.
Lemma FJ_sup x : ltac2:(tb__ "0|0|
S0S4S42S19S24S5S19S36Vx;A1S3aA3A3S6A3"). Proof using . destruct x; reflexivity. Qed.
Lemma SJA_swf x : ltac2:(tb__ "0|0|
S0S4S20S3cVx;A1A1S6A3"). Proof using . destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SJB_swf x : ltac2:(tb__ "0|0|
S0S4S20S3dVx;A1A1S6A3"). Proof using . destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma SJ3_swf x : ltac2:(tb__ "0|0|
S0S4S20S3bVx;A1A1S6A3"). Proof using . destruct x; vm_cast_no_check (@eq_refl bool true). Qed.
End Run.

Ltac batom ia Hi b :=
  first
  [ replace b with false by (symmetry; assumption)
  | replace b with true by (symmetry; assumption)
  | lazymatch b with
    | Z.ltb ?x ?y => first [ replace b with true by (symmetry; apply Z.ltb_lt; lia) | replace b with false by (symmetry; apply Z.ltb_ge; lia) ]
    | Z.leb ?x ?y => first [ replace b with true by (symmetry; apply Z.leb_le; lia) | replace b with false by (symmetry; apply Z.leb_gt; lia) ]
    | Z.eqb ?x ?y => first [ replace b with true by (symmetry; apply Z.eqb_eq; lia) | replace b with false by (symmetry; apply Z.eqb_neq; lia) ]
    | Z.even _ => first [ replace b with true by (symmetry; apply (even_t ia Hi); lia) | replace b with false by (symmetry; apply (even_f ia Hi); lia) ]
    | is_bouncing _ _ => first [ replace b with true by (symmetry; apply (nos_t ia); lia) | replace b with false by (symmetry; apply (nos_f ia); lia) ]
    end ].
Ltac bsimp := cbn [andb orb negb]; rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_r, ?Bool.orb_true_r; rewrite ?if_true, ?if_false.
Ltac bdec ia Hi b :=
  first [ replace b with false by (symmetry; assumption)
        | replace b with true by (symmetry; assumption)
        | lazymatch b with
          | negb ?c => bdec ia Hi c
          | ?c && ?d => first [bdec ia Hi c | bdec ia Hi d]
          | ?c || ?d => first [bdec ia Hi c | bdec ia Hi d]
          | _ => batom ia Hi b
          end ].
Ltac decide_ifs ia Hi :=
  repeat (match goal with |- context [if ?b then _ else _] => bdec ia Hi b; bsimp end).

Ltac arith_only := idtac.
Ltac lits ia :=
  repeat (rewrite (ze_small_lit ia) by lia);
  repeat match goal with |- context [?k mod 2 ^ 64] => rewrite (Z.mod_small k (2 ^ 64)) by lia end.

Ltac finA ia Hi :=
  try rewrite (ze_u2 ia Hi); lits ia; arith_only; rewrite (iu_unfold ia);
  pose proof (iok_sc ia Hi); decide_ifs ia Hi; first [reflexivity | lia | exfalso; lia].

Ltac finB ia Hi :=
  lits ia; arith_only; rewrite (icnt1_unfold ia);
  pose proof (icnt0_range ia Hi); pose proof (iszc_range ia Hi); decide_ifs ia Hi; first [reflexivity | lia | exfalso; lia].

Ltac finC ia Hi :=
  try (rewrite (ze_needed ia Hi) by (first [reflexivity | rewrite ?(zs163 ia Hi); try (rewrite (ze_small_lit ia) by lia); pose proof (icnt1_range ia Hi); lia]));
  try rewrite (ze_rq ia Hi); rewrite ?(zs163 ia Hi); lits ia; arith_only;
  unfold icnt, ineeded; rewrite (iplan_final ia);
  pose proof (icnt1_range ia Hi); pose proof (isize_range ia Hi); decide_ifs ia Hi; cbn [fst snd];
  first [reflexivity | f_equal; lia | lia | exfalso; lia].

Ltac inl := first [ left; reflexivity | right; inl ].
Ltac solve_scratch2 := apply scratch_pair; [reflexivity | cbn; inl | reflexivity].
Ltac solve_pairs2 ia Hi HagX fin :=
  unfold diffs_ok;
  repeat (apply Forall_cons; [cbn [fst snd]; first [ solve_scratch2 | sem ia HagX; zsimp ia Hi; fin ] |]);
  apply Forall_nil.

Ltac read_facts ia Hi K rho' Lf w HagL HSP l :=
  lazymatch l with
  | nil => idtac
  | cons ?p ?t =>
      first [ let H := fresh "F" in
              pose proof (leaf_factw ia _ K rho' Lf w p HagL HSP ltac:(cbn; inl) eq_refl eq_refl) as H; zread ia Hi H
            | idtac ];
      read_facts ia Hi K rho' Lf w HagL HSP t
  end.

Ltac all_leaves tac :=
  lazymatch goal with
  | |- Forall _ (_ :: _) => apply Forall_cons; [tac | all_leaves tac]
  | |- Forall _ [] => apply Forall_nil
  end.

Section Gen.
Variables (Kc : list event -> Model -> Prop) (RF GF : Prop) (TR : Z -> assn -> assn -> Prop).
Hypothesis RR : ltac2:(tb__ "0|0|
S52S35VKc;VRF;VGF;VTR;A5").
Variable kB : Z.
Hypothesis HkB : 0 <= kB.
Variables (Nf Og : Prop).
Variable ia : instA.
Hypothesis Hi : instA_ok ia.
Variable mWc : word -> option byte.
Variable Q : assn.

Ltac one_leaf x Hx S0 ST STswf big bigvars bigsup ZFbig fin CONT rho' HagL :=
  cbn [lf_state];
  lazymatch goal with |- _ (SymSoundR.SP _ ?K ?Lf _) _ =>
    (apply (trr_inh RR); [lia|]); let w := fresh "w" in let HSP := fresh "HSP" in intros w HSP;
    let nfl := eval vm_compute in (List.filter (fun p => negb (existsb (sprop_eqb p) (ss_facts S0))) (ss_facts Lf)) in
    read_facts ia Hi K rho' Lf w HagL HSP nfl; clear HSP;
    let d := eval vm_compute in (match state_diff Lf ST with Some d => d | None => ([], []) end) in
    let sets := eval vm_compute in (scratch_of (fst d)) in
    apply (trr_pre RR (POST segsU K (rho2 ia mWc) ST)); [| exact CONT];
    let w' := fresh "w'" in let HSP' := fresh "HSP'" in intros w' HSP';
    apply (linkp segsU K (rho2 ia mWc) Lf ST sets (fst d) (snd d) rho' w');
    [ vm_compute; reflexivity | reflexivity | apply STswf | vm_compute; reflexivity | exact HagL
    | let HagS := fresh "HagS" in intros HagS _; clear HSP' HagL; try clear CONT; split;
      [ cbn [fst]; solve_pairs2 ia Hi HagS fin
      | exact (nf_of_big ia _ _ (snd d) big HagS eq_refl bigvars bigsup ZFbig) ]
    | exact HSP' ]
  end.

Ltac segment S0lit S0eq runlemma leaves CUTS leaf_tac :=
  lazymatch goal with |- ?TR _ (POST _ ?K (rho2 _ _) _) ?Q =>
  (apply (trr_ex RR); [lia|]); let rhoB := fresh "rhoB" in intros rhoB; (apply (trr_inh RR); [lia|]); let Hag := fresh "Hag" in intros ? [Hag _];
  apply (trr_pre RR (SymSoundR.SP segsU K S0lit rhoB)); [let HSP0 := fresh in intros ? [_ HSP0]; rewrite <- S0eq; exact HSP0|];
  apply ((trr_run RR) kB 500%nat CUTS K S0lit leaves rhoB Q HkB (eq_trans runlemma eq_refl) eq_refl (K_ia_impl Kc ia));
  let Lf := fresh "Lf" in let rho' := fresh "rho'" in let Hin := fresh "Hin" in let Hab := fresh "Hab" in
  intros Lf rho' Hin Hab;
  let HagL := fresh "HagL" in
  assert (HagL : agrees (rho2 ia mWc) rho') by (eapply agrees_below; [exact Hag | exact Hab | cbv; discriminate]);
  clear Hab Hag;
  revert Hin; pattern Lf; match goal with |- (fun l => In l ?LS -> ?P) Lf => change (In Lf LS -> (fun l => P) Lf) end;
  apply (proj1 (Forall_forall _ _)); cbv delta [leaves];
  all_leaves ltac:(leaf_tac rho' HagL)
  end.

Theorem gen_MC x : ltac2:(tb__ "0|3|
S1SdS40Vx;A1S28Via;A1M0A2SdG0S3fVx;A1A2A2VTR;VkB;S37S35S4fVKc;Via;A2M1S29Via;VmWc;A2M2S3bVx;A1A4VQ;A3VTR;VkB;S37S35G1G2S3dVx;A1A4VQ;A3F_;F_;").
Proof using Hi HkB RR.
  intros Hx CONT. set (K := K_ia Kc ia) in *.
  destruct x; cbn [m1_lo m1_hi] in Hx.
  - segment SMC_a SMC_a_eq runMC_a LMC_a CUTS_MC
      ltac:(fun rho' HagL => one_leaf M1a Hx (SJB M1a) (SJ3 M1a) (SJ3_swf M1a) (FM M1a ++ F_J) (FJ_vars M1a) (FJ_sup M1a) (ZF_allJ ia Hi M1a Hx) ltac:(finC ia Hi) CONT rho' HagL).
  - segment SMC_b SMC_b_eq runMC_b LMC_b CUTS_MC
      ltac:(fun rho' HagL => one_leaf M1b Hx (SJB M1b) (SJ3 M1b) (SJ3_swf M1b) (FM M1b ++ F_J) (FJ_vars M1b) (FJ_sup M1b) (ZF_allJ ia Hi M1b Hx) ltac:(finC ia Hi) CONT rho' HagL).
  - segment SMC_c SMC_c_eq runMC_c LMC_c CUTS_MC
      ltac:(fun rho' HagL => one_leaf M1c Hx (SJB M1c) (SJ3 M1c) (SJ3_swf M1c) (FM M1c ++ F_J) (FJ_vars M1c) (FJ_sup M1c) (ZF_allJ ia Hi M1c Hx) ltac:(finC ia Hi) CONT rho' HagL).
  - segment SMC_d SMC_d_eq runMC_d LMC_d CUTS_MC
      ltac:(fun rho' HagL => one_leaf M1d Hx (SJB M1d) (SJ3 M1d) (SJ3_swf M1d) (FM M1d ++ F_J) (FJ_vars M1d) (FJ_sup M1d) (ZF_allJ ia Hi M1d Hx) ltac:(finC ia Hi) CONT rho' HagL).
Qed.

Theorem gen_MB x : ltac2:(tb__ "0|3|
S1SdS40Vx;A1S28Via;A1M0A2SdG0S3fVx;A1A2A2VTR;VkB;S37S35S4fVKc;Via;A2M1S29Via;VmWc;A2M2S3dVx;A1A4VQ;A3VTR;VkB;S37S35G1G2S3cVx;A1A4VQ;A3F_;F_;").
Proof using Hi HkB RR.
  intros Hx CONT. set (K := K_ia Kc ia) in *.
  destruct x; cbn [m1_lo m1_hi] in Hx.
  - segment SMB_a SMB_a_eq runMB_a LMB_a CUTS_MB
      ltac:(fun rho' HagL => one_leaf M1a Hx (SJA M1a) (SJB M1a) (SJB_swf M1a) (FM M1a ++ F_A ++ F_B) (FB_vars M1a) (FB_sup M1a) (ZF_allB ia Hi M1a Hx) ltac:(finB ia Hi) CONT rho' HagL).
  - segment SMB_b SMB_b_eq runMB_b LMB_b CUTS_MB
      ltac:(fun rho' HagL => one_leaf M1b Hx (SJA M1b) (SJB M1b) (SJB_swf M1b) (FM M1b ++ F_A ++ F_B) (FB_vars M1b) (FB_sup M1b) (ZF_allB ia Hi M1b Hx) ltac:(finB ia Hi) CONT rho' HagL).
  - segment SMB_c SMB_c_eq runMB_c LMB_c CUTS_MB
      ltac:(fun rho' HagL => one_leaf M1c Hx (SJA M1c) (SJB M1c) (SJB_swf M1c) (FM M1c ++ F_A ++ F_B) (FB_vars M1c) (FB_sup M1c) (ZF_allB ia Hi M1c Hx) ltac:(finB ia Hi) CONT rho' HagL).
  - segment SMB_d SMB_d_eq runMB_d LMB_d CUTS_MB
      ltac:(fun rho' HagL => one_leaf M1d Hx (SJA M1d) (SJB M1d) (SJB_swf M1d) (FM M1d ++ F_A ++ F_B) (FB_vars M1d) (FB_sup M1d) (ZF_allB ia Hi M1d Hx) ltac:(finB ia Hi) CONT rho' HagL).
Qed.

Theorem gen_MA x : ltac2:(tb__ "0|3|
S1SdS40Vx;A1S28Via;A1M0A2SdG0S3fVx;A1A2A2VTR;VkB;S37S35S4fVKc;Via;A2M1S29Via;VmWc;A2M2S3cVx;A1A4VQ;A3VTR;VkB;S37S35G1G2S3eVx;A1A4VQ;A3F_;F_;").
Proof using Hi HkB RR.
  intros Hx CONT. set (K := K_ia Kc ia) in *.
  destruct x; cbn [m1_lo m1_hi] in Hx.
  - segment SMA_a SMA_a_eq runMA_a LMA_a CUTS_MA
      ltac:(fun rho' HagL => one_leaf M1a Hx (SM23 M1a) (SJA M1a) (SJA_swf M1a) (FM M1a ++ F_A) (FA_vars M1a) (FA_sup M1a) (ZF_allA ia Hi M1a Hx) ltac:(finA ia Hi) CONT rho' HagL).
  - segment SMA_b SMA_b_eq runMA_b LMA_b CUTS_MA
      ltac:(fun rho' HagL => one_leaf M1b Hx (SM23 M1b) (SJA M1b) (SJA_swf M1b) (FM M1b ++ F_A) (FA_vars M1b) (FA_sup M1b) (ZF_allA ia Hi M1b Hx) ltac:(finA ia Hi) CONT rho' HagL).
  - segment SMA_c SMA_c_eq runMA_c LMA_c CUTS_MA
      ltac:(fun rho' HagL => one_leaf M1c Hx (SM23 M1c) (SJA M1c) (SJA_swf M1c) (FM M1c ++ F_A) (FA_vars M1c) (FA_sup M1c) (ZF_allA ia Hi M1c Hx) ltac:(finA ia Hi) CONT rho' HagL).
  - segment SMA_d SMA_d_eq runMA_d LMA_d CUTS_MA
      ltac:(fun rho' HagL => one_leaf M1d Hx (SM23 M1d) (SJA M1d) (SJA_swf M1d) (FM M1d ++ F_A) (FA_vars M1d) (FA_sup M1d) (ZF_allA ia Hi M1d Hx) ltac:(finA ia Hi) CONT rho' HagL).
Qed.

Theorem gen_M23 x : ltac2:(tb__ "0|3|
S1SdS40Vx;A1S28Via;A1M0A2SdG0S3fVx;A1A2A2VTR;VkB;S37S35S4fVKc;Via;A2M1S29Via;VmWc;A2M2S3bVx;A1A4VQ;A3VTR;VkB;S37S35G1G2S3eVx;A1A4VQ;A3F_;F_;").
Proof using Hi HkB RR. intros Hx CONT. apply (gen_MA x Hx). apply (gen_MB x Hx). apply (gen_MC x Hx). exact CONT. Qed.
End Gen.
