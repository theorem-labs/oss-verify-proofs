(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan MainItabBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition AL_STOPS_B : list Z := [556256; 1167232; 1128780; 491820; 482160; 482232].

(* [comment removed for export] *)
Definition KEEP_usage_bs_both : list expr := [(ELit 0); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 2) (EVar 6)))].
Definition KEEP_usage_rs_both : list (Z * Z) := [(66432, 66752); (67648, 67776); (81728, 81856); (83712, 83840); (88960, 89088); (90432, 90560); (109888, 110016); (116672, 116800); (177840, 178096); (1198144, 1199032); (1221176, 1221248); (1221256, 1221312); (1221440, 1221568); (1224384, 1224448); (1224640, 1224696); (1224704, 1224776); (1224904, 1225032); (1228352, 1229320); (1229520, 1229712); (1239824, 1241344); (1244992, 1245056); (1245120, 1245248); (1253248, 1253312); (1255168, 1255296); (1258496, 1258624); (1852032, 1852160); (1852224, 1852288); (1852864, 1852928); (6710784, 6711072); (6842352, 6842408); (6711072, 6711408); (6842408, 6843264); (6842384, 6842408); (6711072, 6711176); (6711368, 6711408); (6842408, 6842496); (6842688, 6842752); (6842944, 6843072); (6844352, 6844480); (2147459072, 2148290560); (2147462144, 2147462272); (2147468672, 2147469120); (2147605922, 2147606048); (2148288928, 2148288992); (17594199277440, 17594199278144)].

(* [comment removed for export] *)
Definition KEEP_operr_bs_both : list expr := [(ELit 0); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6))); (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 2) (EVar 6)))].
Definition KEEP_operr_rs_both : list (Z * Z) := [(66432, 66752); (67648, 67776); (81728, 81856); (83712, 83840); (88960, 89088); (109888, 110016); (116672, 116800); (126912, 127040); (177840, 178096); (1198144, 1199032); (1221176, 1221248); (1221256, 1221312); (1221440, 1221568); (1224384, 1224448); (1224640, 1224696); (1224704, 1224776); (1224904, 1225032); (1228352, 1229320); (1229520, 1229712); (1239824, 1241344); (1244992, 1245056); (1245120, 1245248); (1253248, 1253312); (1255168, 1255296); (1258496, 1258624); (1852032, 1852160); (1852224, 1852288); (1852864, 1852928); (6710784, 6711072); (6842352, 6842408); (6711072, 6711408); (6842408, 6843264); (6842384, 6842408); (6711072, 6711176); (6711368, 6711408); (6842408, 6842496); (6842688, 6842752); (6842944, 6843072); (6844352, 6844480); (2147459072, 2148290560); (2147466688, 2147466816); (2147468672, 2147469120); (2147605922, 2147606048); (2148288928, 2148288992); (17594199277440, 17594199278272)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition usage_0_0_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 0] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 0] 
  (PRun AL_STOPS_B (PExt 2 [ELit 0] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 3 [ELit 0] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition usage_1_63_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 0] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 0] 
  (PRun AL_STOPS_B (PExt 2 [ELit 0] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PExt 3 [ELit 0] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition usage_64_64_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 0] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 0] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 2 [ELit 0] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PExt 3 [ELit 0] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition usage_65_66_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 0] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 0] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 2 [ELit 0] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 3 [ELit 0] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition usage_67_73_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 0] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 0] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 2 [ELit 0] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 3 [ELit 0] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition usage_74_inf_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 0] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 0] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 2 [ELit 0] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition plan_usage_body_both : plan := PSplit (EVar 3) 0 usage_0_0_both (PSplit (EVar 3) 63 usage_1_63_both (PSplit (EVar 3) 64 usage_64_64_both (PSplit (EVar 3) 66 usage_65_66_both (PSplit (EVar 3) 73 usage_67_73_both (usage_74_inf_both))))).
Definition plan_usage_r0_both : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (plan_usage_body_both))).
Definition plan_usage_r1_both : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (plan_usage_body_both))).
(* [comment removed for export] *)
Definition plan_u0_0_0_both : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_0_0_both))).
Definition plan_u1_0_0_both : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_0_0_both))).
Definition plan_u0_1_63_both : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_1_63_both))).
Definition plan_u1_1_63_both : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_1_63_both))).
Definition plan_u0_64_64_both : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_64_64_both))).
Definition plan_u1_64_64_both : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_64_64_both))).
Definition plan_u0_65_66_both : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_65_66_both))).
Definition plan_u1_65_66_both : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_65_66_both))).
Definition plan_u0_67_73_both : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_67_73_both))).
Definition plan_u1_67_73_both : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_67_73_both))).
Definition plan_u0_74_inf_both : plan := PBump HO_NXT (PX XLayout [ELit 0] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_74_inf_both))).
Definition plan_u1_74_inf_both : plan := PBump HO_NXT (PX XLayout [ELit 1] (PKeepOnly KEEP_usage_bs_both KEEP_usage_rs_both (usage_74_inf_both))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition frag_operr0_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 1] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 1] 
  (PRun AL_STOPS_B (PExt 2 [ELit 1] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 3 [ELit 1] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition frag_operr_1_62_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 1] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 1] 
  (PRun AL_STOPS_B (PExt 2 [ELit 1] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PExt 3 [ELit 1] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition frag_operr_63_63_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 1] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 1] 
  (PRun AL_STOPS_B (PExt 2 [ELit 1] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PExt 3 [ELit 1] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition frag_operr_64_64_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 1] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 1] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 2 [ELit 1] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition frag_operr_65_4095_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 1] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 1] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 2 [ELit 1] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

(* [comment removed for export] *)
Definition frag_operr_both : plan := PKeepOnly KEEP_operr_bs_both KEEP_operr_rs_both (PSplit (EVar 7) 62 frag_operr_1_62_both (PSplit (EVar 7) 63 frag_operr_63_63_both (PSplit (EVar 7) 64 frag_operr_64_64_both (frag_operr_65_4095_both)))).
(* [comment removed for export] *)
Definition frag_operr_long_both : plan :=
  PRun AL_STOPS_B 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 0 [ELit 1] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PX XIMemset [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PExt 1 [ELit 1] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 100 [] 
  (PRun AL_STOPS_B (PExt 2 [ELit 1] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PExt 102 [] 
  (PRun AL_STOPS_B (PExt 103 [] 
  (PRun AL_STOPS_B (PX XMemcpy [] 
  (PRun AL_STOPS_B (PEmit 0 [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PX XMemset [] 
  (PRun AL_STOPS_B (PExit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

