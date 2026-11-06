(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
PmLayout PmLayoutU PmModel PmStatics PmSpecs PmSpecsX PmSpecsU PmStep PmTopU PmUHarnessStmts
PmUHarness1 PmUHarness2 PmUHarness3 PmUHarness4 PmUHarness6 PmUHarness7 PmUHarness8 PmUHarness9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMUHT.
Import PMU. Import PMUH.
Section Glue.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMU.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Record harness_deps : Prop := HDEPS {
hd_str_ctor : PMU.str_ctor_spec L HI;
hd_iss_ctor : PMU.iss_ctor_spec L HI;
hd_reader_ctor : PMU.reader_ctor_spec L HI;
hd_syscat : PMU.syscat_spec L HI;
hd_reader_read : PMU.reader_read_spec L HI;
hd_vec_dtor : PMU.vec_dtor_spec L HI;
hd_opdel : PMU.opdel_spec L HI;
hd_src_dtor : PMU.src_dtor_spec L HI;
hd_locale_dtor : PMU.locale_dtor_spec L;
hd_ios_dtor : PMU.ios_dtor_spec L HI
}.
Theorem harness_call_ok : harness_deps -> lib_call_ok (PMTU.TopLay L) SCFG HI PMTU.TopLS.
Proof.
intros [STR ISS RDR SYS RRD VDT OPD SDT LDT IDT].
unfold lib_call_ok. intros fx g LB cr sp ptr ra payload R M model K PRE HH Mh Ml Mm K0 KONT.
unfold lib_cfg in *. cbn [ll_heap ll_entry PMTU.TopLay] in KONT |- *. rewrite (ly_segs L LY) in KONT |- *.
set (n := Z.of_nat (length payload)).
assert (Hn : 0 <= n < 2 ^ 26) by (pose proof (lp_len _ _ _ _ _ _ _ _ _ _ _ PRE) as X; unfold n; lia).
assert (Hcr0 : PMSP.credit_le (512, 2 ^ 29 + 8 * n) cr) by exact (lp_credit _ _ _ _ _ _ _ _ _ _ _ PRE).
assert (Hgp : getr R (reg 3) = Z_to_bv 64 (pa_gp AD)) by (rewrite <- L5K.rl3; exact (lp_gp _ _ _ _ _ _ _ _ _ _ _ PRE)).
assert (Htp : getr R (reg 4) = Z_to_bv 64 (pa_tp AD)).
{ rewrite <- L5K.rl4. pose proof (lp_tp _ _ _ _ _ _ _ _ _ _ _ PRE) as X. cbn [ll_heap PMTU.TopLay] in X. rewrite (ly_tp L LY) in X. exact X. }
assert (Hsp0 : getr R (reg 2) = Z_to_bv 64 sp) by (rewrite <- L5K.rl2; exact (lp_sp _ _ _ _ _ _ _ _ _ _ _ PRE)).
assert (Hra : L5.ra_ok ra) by exact (lp_ra_ok _ _ _ _ _ _ _ _ _ _ _ PRE).
apply (PMUH1.stage1 L HI LY HIok STR fx g LB cr sp ptr ra payload R M model K PRE HH Mh Ml Mm K0). fold n.
intros fx1 R1 M1 model1 cr1 s H1.
apply (PMUH2.stage2 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp ISS fx1 R1 M1 model1 cr1 s K H1 K0).
clear fx1 R1 M1 model1 cr1 H1. intros fx2 R2 M2 model2 cr2 s2 sm H2.
apply (PMUH3.stage3 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp RDR fx2 R2 M2 model2 cr2 s s2 sm K H2 K0).
clear fx2 R2 M2 model2 cr2 H2. intros fx3 R3 M3 model3 cr3 qc b H3.
apply (PMUH4.stage4 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp SYS RRD fx3 R3 M3 model3 cr3 s s2 sm qc b K H3 K0).
clear fx3 R3 M3 model3 cr3 H3. intros fx5 R5 M5 model5 cr5 p sm5 be H5.
apply (PMUH6.stage6 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp VDT fx5 R5 M5 model5 cr5 s s2 p sm5 be K H5 K0).
clear fx5 R5 M5 model5 H5. intros fx6 R6 M6 model6 H6.
apply (PMUH7.stage7 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp OPD SDT fx6 R6 M6 model6 cr5 s s2 (PM.p_tb p) (PM.p_src p) sm5 be K H6 K0).
clear fx6 R6 M6 model6 H6. intros fx7 R7 M7 model7 H7.
apply (PMUH8.stage8 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp OPD LDT IDT fx7 R7 M7 model7 cr5 s s2 sm5 be K H7 K0).
clear fx7 R7 M7 model7 H7. intros fx8 R8 M8 model8 H8.
apply (PMUH9.stage9 L HI LY HIok R M model sp ra n LB cr g Hn Hcr0 Hgp Htp Hsp0 Hra payload eq_refl OPD fx8 R8 M8 model8 cr5 s be K H8 K0).
clear fx8 R8 M8 model8 H8. intros fx9 g9 R9 M9 model9 cr9 POST HH9 MB9.
exact (KONT fx9 g9 R9 M9 model9 cr9 POST HH9 MB9).
Qed.
Theorem harness_iface_ok : harness_deps -> lib_iface_ok (PMTU.TopLay L) SCFG HI PMTU.TopLS.
Proof. intros D. apply (PMTU.top_iface_ok SCFG L HI LY). exact (harness_call_ok D). Qed.
End Glue.
End PMUHT.
