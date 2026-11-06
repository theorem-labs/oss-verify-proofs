(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm8PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib Pm8CutKit.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Rpl.
Ltac2 rplG () : string array := Array.of_list ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.pair"; "Corelib.Numbers.BinNums.Zpos"; "Corelib.Init.Datatypes.nil"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.LibSym.itab_of"; "OSSVerify.jsoncons.fuzz_json_cursor.images.Asan.M.loaded_segments"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_opdel_sized_casan_T.ITR"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.HD"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegPlan.SGP.region"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.callsum"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.stack_reg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_opdel_sized_casan_T.HDECL"; "Corelib.Init.Datatypes.app"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.hd_crs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutHeap.CH.hd_wrs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.CP"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.expr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.EVar"; "Corelib.Init.Datatypes.O"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.kentry"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KUnk"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.SA"; "Corelib.Numbers.BinNums.Zneg"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.ELit"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KWr"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KRange"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.AxSymExec3.AX2.KAlign"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.SegRun.SR.post_spec"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.subst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cutpoint"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen.Cut_opdel_sized_casan_T.t0"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.tag"; "Corelib.Numbers.BinNums.xH"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.pout"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_pc"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_regs"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_know"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_nx"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_F"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutAuto.CA.po_leaves"; "OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert.CutCert.CC.cp_meas"].

Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
Definition ITR : list (Z * nat) := ltac2:(Rpl.RP.run_k (rplG ()) 0 "U1;A2;i1;i2;i3;A3;o0;#0;A4;o4;i2;i3;A1;o5;Y19;6e1a4;N3;A1;o6;#0;").
Definition IT : itab := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A2;k7;k8;k9;").
Definition BF : nat := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;N5000;").
Definition NF : nat := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;N33;").
Definition ENDS : list Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A3;o0;i2;A1;o5;Y19;009f4;A1;o6;i2;").
Definition HDECL : CH.hdecl := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S1;A1;o6;k11;A5;o10;A1;o5;Y12;000;A1;o5;Y13;0020;#0;#0;A1;o6;A2;i1;i2;i2;").
Definition SCELLS : list (Z * Z * Z) := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A1;o6;A2;i1;A2;i1;i2;i2;i2;").
Definition GLO : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A1;o5;Y20;530d8;").
Definition GHI : Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A1;o5;Y20;53f60;").
Definition CSUMS : list CA.callsum := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A1;o6;i12;").
Definition XSTOPS : list Z := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A1;o6;i2;").
Definition APART : list (expr * Z * expr) := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A3;o0;k11;A1;k13;k14;A3;k15;k11;A1;k16;k14;A1;k17;k14;").

Definition t0 : CC.cutpoint := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S37;N1;N2;A1;o20;#1;N3;N4;N5;N6;N7;N8;N9;N10;N11;N12;N13;N14;N15;N16;N17;N18;N19;N20;N21;N22;N23;N24;N25;N26;N27;N28;N29;N30;N31;Y12;000;A2;o24;#2;A1;o25;#32;A1;o26;A1;o5;#32;Y4;0;A1;o5;#35;A7;o18;A1;o5;Y19;6e1ac;A3;o0;i19;A1;o20;o21;A3;o0;i19;A1;o20;#0;A3;o0;i19;#2;A3;o0;i19;A1;o20;#3;A3;o0;i19;A1;o20;#4;A3;o0;i19;A1;o20;#5;A3;o0;i19;A1;o20;#6;A3;o0;i19;A1;o20;#7;A3;o0;i19;A1;o20;#8;A3;o0;i19;A1;o20;#9;A3;o0;i19;A1;o20;#10;A3;o0;i19;A1;o20;#11;A3;o0;i19;A1;o20;#12;A3;o0;i19;A1;o20;#13;A3;o0;i19;A1;o20;#14;A3;o0;i19;A1;o20;#15;A3;o0;i19;A1;o20;#16;A3;o0;i19;A1;o20;#17;A3;o0;i19;A1;o20;#18;A3;o0;i19;A1;o20;#19;A3;o0;i19;A1;o20;#20;A3;o0;i19;A1;o20;#21;A3;o0;i19;A1;o20;#22;A3;o0;i19;A1;o20;#23;A3;o0;i19;A1;o20;#24;A3;o0;i19;A1;o20;#25;A3;o0;i19;A1;o20;#26;A3;o0;i19;A1;o20;#27;A3;o0;i19;A1;o20;#28;A3;o0;i19;A1;o20;#29;A3;o0;i19;A1;o20;#30;A3;o0;i19;A1;o20;#31;A1;o6;i19;A3;o0;i22;A2;o23;#33;#34;A3;o0;i22;A2;o27;#33;#34;A3;o0;i22;A3;o28;#2;A1;o5;Y46;3fff7f801000;A1;o5;Y47;000000000000;A3;o0;i22;A2;o29;#2;#36;A1;o6;i22;N33;A1;o6;k11;A1;o6;i30;A1;o26;#36;").
Definition BL0 : CA.blocks := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S2;A2;i1;i19;i19;N10;A3;o0;#0;A4;o4;i19;i19;A1;o20;#1;A1;o20;N32;A1;o6;#0;").
Definition hints0 : list (nat * CC.subst) := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A1;o6;A2;i1;i3;k31;").
Definition TMPL : list CC.cutpoint := ltac2:(Rpl.RP.run_k (rplG ()) 0 "S0;A3;o0;i32;k33;A1;o6;i32;").
Definition EXPL (c : CC.cutpoint) (h : list (nat * CC.subst)) (first : bool) :=
  CA.explore RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BF A0 NF TMPL ENDS CSUMS 0%nat [2%nat; 4%nat] [] XSTOPS (CC.cp_F c) (CC.cp_meas c) h 50 first
    (SS (CC.cp_pc c) (CC.cp_regs c) [] (CC.cp_know c) (CC.cp_nx c)).
Definition tagcode (t : CC.tag) : Z * Z := ltac2:(Rpl.RP.run_k (rplG ()) 1 "S0;Lt;Ri34;m34;RNLt;Ri34;A2;i1;i2;i2;r1;2;Lj;Ri3;Ls;Rk31;A4;o4;i2;i2;A1;o5;o35;A1;k36;r2;Lpc;Ri2;A4;o4;i2;i2;A1;o5;Y1;0;r1;").
Definition mkcp (c : CC.cutpoint) (o : CA.pout) : CC.cutpoint := ltac2:(Rpl.RP.run_k (rplG ()) 2 "U0;Lc;Ri32;Lo;Ri37;A7;o18;A1;k38;r2;A1;k39;r2;A1;k40;r2;A1;k41;r2;A1;k42;r2;A4;k43;A2;i1;i30;i34;i30;A2;k44;i30;i34;A1;k45;r1;A1;k46;r2;").
