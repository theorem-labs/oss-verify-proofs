(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require AxSymExec3 AsanPlan PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require AsanNodesIO AsanMainLib ImgParams MainDefs Img_src13 Cert_common ITab_src13 Segs_src13 HS_src13_pfx1 Sh_src13_4 Sh_src13_1 PlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
(* [comment removed for export] *)
Module Plan_src13_r0c0_1005_1148.   (* [comment removed for export] *)
End Plan_src13_r0c0_1005_1148.

Module Plan_src13_r0c0_1005_1148_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_1005_1148_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?g_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?g_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?g_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_1005_1148_L.

Module Cert_src13_r0c0_1005_1148_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_1005_1148 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_1005_1148_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_1005_1148 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_1005_1148_0 : class := [(QLook,4,4); (QFlen,1011,1154); (QCfgLen,0,0); (QRoom,1005,1148)].
Definition SH_src13_r0c0_1005_1148_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_1005_1148_0 : nat := 3000.
Lemma cert_src13_r0c0_1005_1148_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_1005_1148_0 (hs_of HT_src13_r0c0_1005_1148) HS_src13_pfx1_0 C_src13_r0c0_1005_1148_0 P_src13_r0c0_1005_1148_0 = COk SH_src13_r0c0_1005_1148_0.
Proof. cert_vm (COk SH_src13_r0c0_1005_1148_0). Qed.
End Cert_src13_r0c0_1005_1148_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_10909_12268.   (* [comment removed for export] *)
End Plan_src13_r0c0_10909_12268.

Module Plan_src13_r0c0_10909_12268_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_10909_12268_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?w_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?w_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?w_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?v~?a}N?xq?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_10909_12268_L.

Module Cert_src13_r0c0_10909_12268_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_10909_12268 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_10909_12268_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_10909_12268 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_10909_12268_0 : class := [(QLook,4,4); (QFlen,10915,12274); (QCfgLen,0,0); (QRoom,10909,12268)].
Definition SH_src13_r0c0_10909_12268_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_10909_12268_0 : nat := 3000.
Lemma cert_src13_r0c0_10909_12268_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_10909_12268_0 (hs_of HT_src13_r0c0_10909_12268) HS_src13_pfx1_0 C_src13_r0c0_10909_12268_0 P_src13_r0c0_10909_12268_0 = COk SH_src13_r0c0_10909_12268_0.
Proof. cert_vm (COk SH_src13_r0c0_10909_12268_0). Qed.
End Cert_src13_r0c0_10909_12268_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_109_124.   (* [comment removed for export] *)
End Plan_src13_r0c0_109_124.

Module Plan_src13_r0c0_109_124_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_109_124_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?rcHa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?b?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?b?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_109_124_L.

Module Cert_src13_r0c0_109_124_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_109_124 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_109_124_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX137_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX137.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_109_124 : htab := [(137%nat, (HS_src13_shX137_0, SH_src13_shX137_0))].

Definition C_src13_r0c0_109_124_0 : class := [(QLook,4,4); (QFlen,115,130); (QCfgLen,0,0); (QRoom,109,124)].
Definition SH_src13_r0c0_109_124_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 137).
Definition FUEL_src13_r0c0_109_124_0 : nat := 3000.
Lemma cert_src13_r0c0_109_124_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_109_124_0 (hs_of HT_src13_r0c0_109_124) HS_src13_pfx1_0 C_src13_r0c0_109_124_0 P_src13_r0c0_109_124_0 = COk SH_src13_r0c0_109_124_0.
Proof. cert_vm (COk SH_src13_r0c0_109_124_0). Qed.
End Cert_src13_r0c0_109_124_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_1149_1340.   (* [comment removed for export] *)
End Plan_src13_r0c0_1149_1340.

Module Plan_src13_r0c0_1149_1340_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_1149_1340_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?g_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?g_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?g_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_1149_1340_L.

Module Cert_src13_r0c0_1149_1340_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_1149_1340 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_1149_1340_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_1149_1340 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_1149_1340_0 : class := [(QLook,4,4); (QFlen,1155,1346); (QCfgLen,0,0); (QRoom,1149,1340)].
Definition SH_src13_r0c0_1149_1340_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_1149_1340_0 : nat := 3000.
Lemma cert_src13_r0c0_1149_1340_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_1149_1340_0 (hs_of HT_src13_r0c0_1149_1340) HS_src13_pfx1_0 C_src13_r0c0_1149_1340_0 P_src13_r0c0_1149_1340_0 = COk SH_src13_r0c0_1149_1340_0.
Proof. cert_vm (COk SH_src13_r0c0_1149_1340_0). Qed.
End Cert_src13_r0c0_1149_1340_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_12269_13084.   (* [comment removed for export] *)
End Plan_src13_r0c0_12269_13084.

Module Plan_src13_r0c0_12269_13084_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_12269_13084_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`__?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`__?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`__?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_12269_13084_L.

Module Cert_src13_r0c0_12269_13084_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_12269_13084 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_12269_13084_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_12269_13084 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_12269_13084_0 : class := [(QLook,4,4); (QFlen,12275,13090); (QCfgLen,0,0); (QRoom,12269,13084)].
Definition SH_src13_r0c0_12269_13084_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_12269_13084_0 : nat := 3000.
Lemma cert_src13_r0c0_12269_13084_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_12269_13084_0 (hs_of HT_src13_r0c0_12269_13084) HS_src13_pfx1_0 C_src13_r0c0_12269_13084_0 P_src13_r0c0_12269_13084_0 = COk SH_src13_r0c0_12269_13084_0.
Proof. cert_vm (COk SH_src13_r0c0_12269_13084_0). Qed.
End Cert_src13_r0c0_12269_13084_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_125_140.   (* [comment removed for export] *)
End Plan_src13_r0c0_125_140.

Module Plan_src13_r0c0_125_140_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_125_140_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_125_140_L.

Module Cert_src13_r0c0_125_140_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_125_140 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_125_140_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_125_140 : htab := [(40%nat, (HS_src13_shX40_0, SH_src13_shX40_0))].

Definition C_src13_r0c0_125_140_0 : class := [(QLook,4,4); (QFlen,131,146); (QCfgLen,0,0); (QRoom,125,140)].
Definition SH_src13_r0c0_125_140_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_src13_r0c0_125_140_0 : nat := 3000.
Lemma cert_src13_r0c0_125_140_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_125_140_0 (hs_of HT_src13_r0c0_125_140) HS_src13_pfx1_0 C_src13_r0c0_125_140_0 P_src13_r0c0_125_140_0 = COk SH_src13_r0c0_125_140_0.
Proof. cert_vm (COk SH_src13_r0c0_125_140_0). Qed.
End Cert_src13_r0c0_125_140_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_13085_16364.   (* [comment removed for export] *)
End Plan_src13_r0c0_13085_16364.

Module Plan_src13_r0c0_13085_16364_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_13085_16364_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`__?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`__?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`__?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_13085_16364_L.

Module Cert_src13_r0c0_13085_16364_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_13085_16364 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_13085_16364_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_13085_16364 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_13085_16364_0 : class := [(QLook,4,4); (QFlen,13091,16370); (QCfgLen,0,0); (QRoom,13085,16364)].
Definition SH_src13_r0c0_13085_16364_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_13085_16364_0 : nat := 3000.
Lemma cert_src13_r0c0_13085_16364_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_13085_16364_0 (hs_of HT_src13_r0c0_13085_16364) HS_src13_pfx1_0 C_src13_r0c0_13085_16364_0 P_src13_r0c0_13085_16364_0 = COk SH_src13_r0c0_13085_16364_0.
Proof. cert_vm (COk SH_src13_r0c0_13085_16364_0). Qed.
End Cert_src13_r0c0_13085_16364_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_1341_1628.   (* [comment removed for export] *)
End Plan_src13_r0c0_1341_1628.

Module Plan_src13_r0c0_1341_1628_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_1341_1628_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB??@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?rcDa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?`?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?`?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_1341_1628_L.

Module Cert_src13_r0c0_1341_1628_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_1341_1628 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_1341_1628_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX133_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX133.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_1341_1628 : htab := [(133%nat, (HS_src13_shX133_0, SH_src13_shX133_0))].

Definition C_src13_r0c0_1341_1628_0 : class := [(QLook,4,4); (QFlen,1347,1634); (QCfgLen,0,0); (QRoom,1341,1628)].
Definition SH_src13_r0c0_1341_1628_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 133).
Definition FUEL_src13_r0c0_1341_1628_0 : nat := 3000.
Lemma cert_src13_r0c0_1341_1628_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_1341_1628_0 (hs_of HT_src13_r0c0_1341_1628) HS_src13_pfx1_0 C_src13_r0c0_1341_1628_0 P_src13_r0c0_1341_1628_0 = COk SH_src13_r0c0_1341_1628_0.
Proof. cert_vm (COk SH_src13_r0c0_1341_1628_0). Qed.
End Cert_src13_r0c0_1341_1628_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_13_28.   (* [comment removed for export] *)
End Plan_src13_r0c0_13_28.

Module Plan_src13_r0c0_13_28_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_13_28_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_13_28_L.

Module Cert_src13_r0c0_13_28_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_13_28 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_13_28_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_13_28 : htab := [(40%nat, (HS_src13_shX40_0, SH_src13_shX40_0))].

Definition C_src13_r0c0_13_28_0 : class := [(QLook,4,4); (QFlen,19,34); (QCfgLen,0,0); (QRoom,13,28)].
Definition SH_src13_r0c0_13_28_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_src13_r0c0_13_28_0 : nat := 3000.
Lemma cert_src13_r0c0_13_28_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_13_28_0 (hs_of HT_src13_r0c0_13_28) HS_src13_pfx1_0 C_src13_r0c0_13_28_0 P_src13_r0c0_13_28_0 = COk SH_src13_r0c0_13_28_0.
Proof. cert_vm (COk SH_src13_r0c0_13_28_0). Qed.
End Cert_src13_r0c0_13_28_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_141_156.   (* [comment removed for export] *)
End Plan_src13_r0c0_141_156.

Module Plan_src13_r0c0_141_156_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_141_156_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_141_156_L.

Module Cert_src13_r0c0_141_156_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_141_156 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_141_156_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_141_156 : htab := [(40%nat, (HS_src13_shX40_0, SH_src13_shX40_0))].

Definition C_src13_r0c0_141_156_0 : class := [(QLook,4,4); (QFlen,147,162); (QCfgLen,0,0); (QRoom,141,156)].
Definition SH_src13_r0c0_141_156_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_src13_r0c0_141_156_0 : nat := 3000.
Lemma cert_src13_r0c0_141_156_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_141_156_0 (hs_of HT_src13_r0c0_141_156) HS_src13_pfx1_0 C_src13_r0c0_141_156_0 P_src13_r0c0_141_156_0 = COk SH_src13_r0c0_141_156_0.
Proof. cert_vm (COk SH_src13_r0c0_141_156_0). Qed.
End Cert_src13_r0c0_141_156_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_157_188.   (* [comment removed for export] *)
End Plan_src13_r0c0_157_188.

Module Plan_src13_r0c0_157_188_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_157_188_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_157_188_L.

Module Cert_src13_r0c0_157_188_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_157_188 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_157_188_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_157_188 : htab := [(40%nat, (HS_src13_shX40_0, SH_src13_shX40_0))].

Definition C_src13_r0c0_157_188_0 : class := [(QLook,4,4); (QFlen,163,194); (QCfgLen,0,0); (QRoom,157,188)].
Definition SH_src13_r0c0_157_188_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_src13_r0c0_157_188_0 : nat := 3000.
Lemma cert_src13_r0c0_157_188_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_157_188_0 (hs_of HT_src13_r0c0_157_188) HS_src13_pfx1_0 C_src13_r0c0_157_188_0 P_src13_r0c0_157_188_0 = COk SH_src13_r0c0_157_188_0.
Proof. cert_vm (COk SH_src13_r0c0_157_188_0). Qed.
End Cert_src13_r0c0_157_188_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_1629_2028.   (* [comment removed for export] *)
End Plan_src13_r0c0_1629_2028.

Module Plan_src13_r0c0_1629_2028_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_1629_2028_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB??@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?rcDa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?`?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?`?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_1629_2028_L.

Module Cert_src13_r0c0_1629_2028_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_1629_2028 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_1629_2028_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX133_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX133.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_1629_2028 : htab := [(133%nat, (HS_src13_shX133_0, SH_src13_shX133_0))].

Definition C_src13_r0c0_1629_2028_0 : class := [(QLook,4,4); (QFlen,1635,2034); (QCfgLen,0,0); (QRoom,1629,2028)].
Definition SH_src13_r0c0_1629_2028_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 133).
Definition FUEL_src13_r0c0_1629_2028_0 : nat := 3000.
Lemma cert_src13_r0c0_1629_2028_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_1629_2028_0 (hs_of HT_src13_r0c0_1629_2028) HS_src13_pfx1_0 C_src13_r0c0_1629_2028_0 P_src13_r0c0_1629_2028_0 = COk SH_src13_r0c0_1629_2028_0.
Proof. cert_vm (COk SH_src13_r0c0_1629_2028_0). Qed.
End Cert_src13_r0c0_1629_2028_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_16365_18700.   (* [comment removed for export] *)
End Plan_src13_r0c0_16365_18700.

Module Plan_src13_r0c0_16365_18700_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_16365_18700_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`g_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`g_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`g_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_16365_18700_L.

Module Cert_src13_r0c0_16365_18700_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_16365_18700 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_16365_18700_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_16365_18700 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_16365_18700_0 : class := [(QLook,4,4); (QFlen,16371,18706); (QCfgLen,0,0); (QRoom,16365,18700)].
Definition SH_src13_r0c0_16365_18700_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_16365_18700_0 : nat := 3000.
Lemma cert_src13_r0c0_16365_18700_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_16365_18700_0 (hs_of HT_src13_r0c0_16365_18700) HS_src13_pfx1_0 C_src13_r0c0_16365_18700_0 P_src13_r0c0_16365_18700_0 = COk SH_src13_r0c0_16365_18700_0.
Proof. cert_vm (COk SH_src13_r0c0_16365_18700_0). Qed.
End Cert_src13_r0c0_16365_18700_0.
