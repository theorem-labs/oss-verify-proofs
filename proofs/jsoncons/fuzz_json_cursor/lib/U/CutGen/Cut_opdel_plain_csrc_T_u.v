(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Rpl.
Ltac2 rplG () : string array := Array.of_list ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.pair"; "Corelib.Numbers.BinNums.Zpos"; "Corelib.Init.Datatypes.nil"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.LibSym.itab_of"; "OssFuzzTheorems.jsoncons.fuzz_json_cursor.images.Ubsan.M.loaded_segments"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen.Cut_opdel_plain_csrc_T_u.ITR"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.HD"; "Corelib.Numbers.BinNums.Z0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.SegPlan.SGP.region"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.callsum"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.stack_reg"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen.Cut_opdel_plain_csrc_T_u.HDECL"; "Corelib.Init.Datatypes.app"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.hd_crs"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.hd_wrs"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.CP"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.expr"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.EVar"; "Corelib.Init.Datatypes.O"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.kentry"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.SegRun.SR.post_spec"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.ELit"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.subst"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cutpoint"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen.Cut_opdel_plain_csrc_T_u.t0"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.tag"; "Corelib.Numbers.BinNums.xH"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.pout"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_pc"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_regs"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_know"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_nx"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_F"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.po_leaves"; "OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_meas"].

Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := ltac2:(Rpl.RP.run_k (rplG ()) 0 "U1;A2;i1;i2;i3;A3;o0;#0;A4;o4;i2;i3;A1;o5;Y18;21c84;N4;A1;o6;#0;").
Definition IT : itab := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A2;k7;k8;k9;").
Definition BF : nat := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;N5000;").
Definition NF : nat := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;N32;").
Definition ENDS : list Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A3;o0;i2;A1;o5;Y19;29004;A1;o6;i2;").
Definition HDECL : CH.hdecl := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S1;A1;o6;k12;A5;o10;o11;A1;o5;Y13;0020;#0;#0;A1;o6;A2;i1;i2;i2;").
Definition CSUMS : list CA.callsum := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A1;o6;i13;").
Definition XSTOPS : list Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A1;o6;i2;").
Definition APART : list (expr * Z * expr) := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A3;o0;k12;A1;k14;k15;A3;k16;k12;A1;k17;k15;A1;k18;k15;").

Definition t0 : CC.cutpoint := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S31;N1;N2;N3;N4;N5;N6;N7;N8;N9;N10;N11;N12;N13;N14;N15;N16;N17;N18;N19;N20;N21;N22;N23;N24;N25;N26;N27;N28;N29;N30;N31;A7;o19;A1;o5;Y18;21c88;A3;o0;i20;A1;o21;o22;A3;o0;i20;A1;o21;#0;A3;o0;i20;A1;o21;#1;A3;o0;i20;A1;o21;#2;A3;o0;i20;A1;o21;#3;A3;o0;i20;A1;o21;#4;A3;o0;i20;A1;o21;#5;A3;o0;i20;A1;o21;#6;A3;o0;i20;A1;o21;#7;A3;o0;i20;A1;o21;#8;A3;o0;i20;A1;o21;#9;A3;o0;i20;A1;o21;#10;A3;o0;i20;A1;o21;#11;A3;o0;i20;A1;o21;#12;A3;o0;i20;A1;o21;#13;A3;o0;i20;A1;o21;#14;A3;o0;i20;A1;o21;#15;A3;o0;i20;A1;o21;#16;A3;o0;i20;A1;o21;#17;A3;o0;i20;A1;o21;#18;A3;o0;i20;A1;o21;#19;A3;o0;i20;A1;o21;#20;A3;o0;i20;A1;o21;#21;A3;o0;i20;A1;o21;#22;A3;o0;i20;A1;o21;#23;A3;o0;i20;A1;o21;#24;A3;o0;i20;A1;o21;#25;A3;o0;i20;A1;o21;#26;A3;o0;i20;A1;o21;#27;A3;o0;i20;A1;o21;#28;A3;o0;i20;A1;o21;#29;A3;o0;i20;A1;o21;#30;A1;o6;i20;A1;o6;i23;N32;A1;o6;k12;A1;o6;i24;A1;o25;A1;o5;Y4;0;").
Definition BL0 : CA.blocks := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A1;o6;A2;i1;i20;i20;").
Definition hints0 : list (nat * CC.subst) := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A1;o6;A2;i1;i3;k26;").
Definition TMPL : list CC.cutpoint := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A3;o0;i27;k28;A1;o6;i27;").
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 20 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := ltac2:(Rpl.RP.run_k (rplG ()) 1 "S0;Lt;Ri29;m29;RNLt;Ri29;A2;i1;i2;i2;r1;2;Lj;Ri3;Ls;Rk26;A4;o4;i2;i2;A1;o5;o30;A1;k31;r2;Lpc;Ri2;A4;o4;i2;i2;A1;o5;Y1;0;r1;").
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint := ltac2:(Rpl.RP.run_k (rplG ()) 2 "U0;Lc;Ri27;Lo;Ri32;A7;o19;A1;k33;r2;A1;k34;r2;A1;k35;r2;A1;k36;r2;A1;k37;r2;A4;k38;A2;i1;i24;i29;i24;A2;k39;i24;i29;A1;k40;r1;A1;k41;r2;").
