(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require AxSymExec3 AsanPlan PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require AsanNodesIO AsanMainLib ImgParams MainDefs Img_src13 Cert_common ITab_src13 Segs_src13 HS_src13_pfx1 Sh_src13_4 Sh_src13_1 PlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
(* [comment removed for export] *)
Module Plan_src13_r0c0_18701_20460.   (* [comment removed for export] *)
End Plan_src13_r0c0_18701_20460.

Module Plan_src13_r0c0_18701_20460_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_18701_20460_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`g_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`g_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`g_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?`f~?a}N?`is?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_18701_20460_L.

Module Cert_src13_r0c0_18701_20460_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_18701_20460 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_18701_20460_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_18701_20460 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_18701_20460_0 : class := [(QLook,4,4); (QFlen,18707,20466); (QCfgLen,0,0); (QRoom,18701,20460)].
Definition SH_src13_r0c0_18701_20460_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_18701_20460_0 : nat := 3000.
Lemma cert_src13_r0c0_18701_20460_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_18701_20460_0 (hs_of HT_src13_r0c0_18701_20460) HS_src13_pfx1_0 C_src13_r0c0_18701_20460_0 P_src13_r0c0_18701_20460_0 = COk SH_src13_r0c0_18701_20460_0.
Proof. cert_vm (COk SH_src13_r0c0_18701_20460_0). Qed.
End Cert_src13_r0c0_18701_20460_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_189_236.   (* [comment removed for export] *)
End Plan_src13_r0c0_189_236.

Module Plan_src13_r0c0_189_236_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_189_236_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_189_236_L.

Module Cert_src13_r0c0_189_236_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_189_236 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_189_236_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_189_236 : htab := [(40%nat, (HS_src13_shX40_0, SH_src13_shX40_0))].

Definition C_src13_r0c0_189_236_0 : class := [(QLook,4,4); (QFlen,195,242); (QCfgLen,0,0); (QRoom,189,236)].
Definition SH_src13_r0c0_189_236_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_src13_r0c0_189_236_0 : nat := 3000.
Lemma cert_src13_r0c0_189_236_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_189_236_0 (hs_of HT_src13_r0c0_189_236) HS_src13_pfx1_0 C_src13_r0c0_189_236_0 P_src13_r0c0_189_236_0 = COk SH_src13_r0c0_189_236_0.
Proof. cert_vm (COk SH_src13_r0c0_189_236_0). Qed.
End Cert_src13_r0c0_189_236_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_1_12.   (* [comment removed for export] *)
End Plan_src13_r0c0_1_12.

Module Plan_src13_r0c0_1_12_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_1_12_0 : AP.plan := PKC.decode_plan "TQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc?TS@?C??SB??@nqhW?@nqo?m@PbNC??g_?@[bO?g_?bPC??g_?@LbQ?cg_?bRC??g_?@RbS?o_?bT@YbUC??g_?@[bV?g_?bWC??g_?@LbX?cg_?bY@WbZ@Xb[?c__?b\?`|g_?b]?f~~z~o___?b^?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mx_WbmxgW??@`lji???N??@`lji?TT@?C??N???SB???SB???SB???SB???Z"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_1_12_L.

Module Cert_src13_r0c0_1_12_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_1_12 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_1_12_L.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition C_src13_r0c0_1_12_0 : class := [(QLook,4,4); (QFlen,7,18); (QCfgLen,0,0); (QRoom,1,12)].
Definition SH_src13_r0c0_1_12_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SExit 0).
Definition FUEL_src13_r0c0_1_12_0 : nat := 3000.
Lemma cert_src13_r0c0_1_12_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_1_12_0 HS_none HS_src13_pfx1_0 C_src13_r0c0_1_12_0 P_src13_r0c0_1_12_0 = COk SH_src13_r0c0_1_12_0.
Proof. cert_vm (COk SH_src13_r0c0_1_12_0). Qed.
End Cert_src13_r0c0_1_12_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_2029_2332.   (* [comment removed for export] *)
End Plan_src13_r0c0_2029_2332.

Module Plan_src13_r0c0_2029_2332_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_2029_2332_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?o_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?o_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?o_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_2029_2332_L.

Module Cert_src13_r0c0_2029_2332_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_2029_2332 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_2029_2332_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_2029_2332 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_2029_2332_0 : class := [(QLook,4,4); (QFlen,2035,2338); (QCfgLen,0,0); (QRoom,2029,2332)].
Definition SH_src13_r0c0_2029_2332_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_2029_2332_0 : nat := 3000.
Lemma cert_src13_r0c0_2029_2332_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_2029_2332_0 (hs_of HT_src13_r0c0_2029_2332) HS_src13_pfx1_0 C_src13_r0c0_2029_2332_0 P_src13_r0c0_2029_2332_0 = COk SH_src13_r0c0_2029_2332_0.
Proof. cert_vm (COk SH_src13_r0c0_2029_2332_0). Qed.
End Cert_src13_r0c0_2029_2332_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_20461_21820.   (* [comment removed for export] *)
End Plan_src13_r0c0_20461_21820.

Module Plan_src13_r0c0_20461_21820_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_20461_21820_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`o_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`o_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`o_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_20461_21820_L.

Module Cert_src13_r0c0_20461_21820_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_20461_21820 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_20461_21820_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_20461_21820 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_20461_21820_0 : class := [(QLook,4,4); (QFlen,20467,21826); (QCfgLen,0,0); (QRoom,20461,21820)].
Definition SH_src13_r0c0_20461_21820_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_20461_21820_0 : nat := 3000.
Lemma cert_src13_r0c0_20461_21820_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_20461_21820_0 (hs_of HT_src13_r0c0_20461_21820) HS_src13_pfx1_0 C_src13_r0c0_20461_21820_0 P_src13_r0c0_20461_21820_0 = COk SH_src13_r0c0_20461_21820_0.
Proof. cert_vm (COk SH_src13_r0c0_20461_21820_0). Qed.
End Cert_src13_r0c0_20461_21820_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_21821_24556.   (* [comment removed for export] *)
End Plan_src13_r0c0_21821_24556.

Module Plan_src13_r0c0_21821_24556_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_21821_24556_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`o_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`o_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`o_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?`n~?a}N?`rd?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_21821_24556_L.

Module Cert_src13_r0c0_21821_24556_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_21821_24556 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_21821_24556_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_21821_24556 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_21821_24556_0 : class := [(QLook,4,4); (QFlen,21827,24562); (QCfgLen,0,0); (QRoom,21821,24556)].
Definition SH_src13_r0c0_21821_24556_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_21821_24556_0 : nat := 3000.
Lemma cert_src13_r0c0_21821_24556_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_21821_24556_0 (hs_of HT_src13_r0c0_21821_24556) HS_src13_pfx1_0 C_src13_r0c0_21821_24556_0 P_src13_r0c0_21821_24556_0 = COk SH_src13_r0c0_21821_24556_0.
Proof. cert_vm (COk SH_src13_r0c0_21821_24556_0). Qed.
End Cert_src13_r0c0_21821_24556_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_2333_2716.   (* [comment removed for export] *)
End Plan_src13_r0c0_2333_2716.

Module Plan_src13_r0c0_2333_2716_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_2333_2716_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?o_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?o_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?o_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_2333_2716_L.

Module Cert_src13_r0c0_2333_2716_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_2333_2716 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_2333_2716_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_2333_2716 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_2333_2716_0 : class := [(QLook,4,4); (QFlen,2339,2722); (QCfgLen,0,0); (QRoom,2333,2716)].
Definition SH_src13_r0c0_2333_2716_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_2333_2716_0 : nat := 3000.
Lemma cert_src13_r0c0_2333_2716_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_2333_2716_0 (hs_of HT_src13_r0c0_2333_2716) HS_src13_pfx1_0 C_src13_r0c0_2333_2716_0 P_src13_r0c0_2333_2716_0 = COk SH_src13_r0c0_2333_2716_0.
Proof. cert_vm (COk SH_src13_r0c0_2333_2716_0). Qed.
End Cert_src13_r0c0_2333_2716_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_237_284.   (* [comment removed for export] *)
End Plan_src13_r0c0_237_284.

Module Plan_src13_r0c0_237_284_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_237_284_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?rcHa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?b?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?b?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_237_284_L.

Module Cert_src13_r0c0_237_284_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_237_284 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_237_284_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX137_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX137.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_237_284 : htab := [(137%nat, (HS_src13_shX137_0, SH_src13_shX137_0))].

Definition C_src13_r0c0_237_284_0 : class := [(QLook,4,4); (QFlen,243,290); (QCfgLen,0,0); (QRoom,237,284)].
Definition SH_src13_r0c0_237_284_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 137).
Definition FUEL_src13_r0c0_237_284_0 : nat := 3000.
Lemma cert_src13_r0c0_237_284_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_237_284_0 (hs_of HT_src13_r0c0_237_284) HS_src13_pfx1_0 C_src13_r0c0_237_284_0 P_src13_r0c0_237_284_0 = COk SH_src13_r0c0_237_284_0.
Proof. cert_vm (COk SH_src13_r0c0_237_284_0). Qed.
End Cert_src13_r0c0_237_284_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_24557_26188.   (* [comment removed for export] *)
End Plan_src13_r0c0_24557_26188.

Module Plan_src13_r0c0_24557_26188_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_24557_26188_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`w_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`w_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`w_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_24557_26188_L.

Module Cert_src13_r0c0_24557_26188_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_24557_26188 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_24557_26188_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_24557_26188 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_24557_26188_0 : class := [(QLook,4,4); (QFlen,24563,26194); (QCfgLen,0,0); (QRoom,24557,26188)].
Definition SH_src13_r0c0_24557_26188_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_24557_26188_0 : nat := 3000.
Lemma cert_src13_r0c0_24557_26188_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_24557_26188_0 (hs_of HT_src13_r0c0_24557_26188) HS_src13_pfx1_0 C_src13_r0c0_24557_26188_0 P_src13_r0c0_24557_26188_0 = COk SH_src13_r0c0_24557_26188_0.
Proof. cert_vm (COk SH_src13_r0c0_24557_26188_0). Qed.
End Cert_src13_r0c0_24557_26188_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_26189_28652.   (* [comment removed for export] *)
End Plan_src13_r0c0_26189_28652.

Module Plan_src13_r0c0_26189_28652_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_26189_28652_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`w_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`w_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`w_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?`v~?a}N?`~~?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_26189_28652_L.

Module Cert_src13_r0c0_26189_28652_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_26189_28652 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_26189_28652_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_26189_28652 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_26189_28652_0 : class := [(QLook,4,4); (QFlen,26195,28658); (QCfgLen,0,0); (QRoom,26189,28652)].
Definition SH_src13_r0c0_26189_28652_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_26189_28652_0 : nat := 3000.
Lemma cert_src13_r0c0_26189_28652_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_26189_28652_0 (hs_of HT_src13_r0c0_26189_28652) HS_src13_pfx1_0 C_src13_r0c0_26189_28652_0 P_src13_r0c0_26189_28652_0 = COk SH_src13_r0c0_26189_28652_0.
Proof. cert_vm (COk SH_src13_r0c0_26189_28652_0). Qed.
End Cert_src13_r0c0_26189_28652_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_2717_3260.   (* [comment removed for export] *)
End Plan_src13_r0c0_2717_3260.

Module Plan_src13_r0c0_2717_3260_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_2717_3260_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?g_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?g_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?g_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_2717_3260_L.

Module Cert_src13_r0c0_2717_3260_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_2717_3260 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_2717_3260_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_2717_3260 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_2717_3260_0 : class := [(QLook,4,4); (QFlen,2723,3266); (QCfgLen,0,0); (QRoom,2717,3260)].
Definition SH_src13_r0c0_2717_3260_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_2717_3260_0 : nat := 3000.
Lemma cert_src13_r0c0_2717_3260_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_2717_3260_0 (hs_of HT_src13_r0c0_2717_3260) HS_src13_pfx1_0 C_src13_r0c0_2717_3260_0 P_src13_r0c0_2717_3260_0 = COk SH_src13_r0c0_2717_3260_0.
Proof. cert_vm (COk SH_src13_r0c0_2717_3260_0). Qed.
End Cert_src13_r0c0_2717_3260_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_285_316.   (* [comment removed for export] *)
End Plan_src13_r0c0_285_316.

Module Plan_src13_r0c0_285_316_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_285_316_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?rcHa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?b?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?b?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_285_316_L.

Module Cert_src13_r0c0_285_316_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_285_316 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_285_316_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX137_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX137.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_285_316 : htab := [(137%nat, (HS_src13_shX137_0, SH_src13_shX137_0))].

Definition C_src13_r0c0_285_316_0 : class := [(QLook,4,4); (QFlen,291,322); (QCfgLen,0,0); (QRoom,285,316)].
Definition SH_src13_r0c0_285_316_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 137).
Definition FUEL_src13_r0c0_285_316_0 : nat := 3000.
Lemma cert_src13_r0c0_285_316_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_285_316_0 (hs_of HT_src13_r0c0_285_316) HS_src13_pfx1_0 C_src13_r0c0_285_316_0 P_src13_r0c0_285_316_0 = COk SH_src13_r0c0_285_316_0.
Proof. cert_vm (COk SH_src13_r0c0_285_316_0). Qed.
End Cert_src13_r0c0_285_316_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_28653_32748.   (* [comment removed for export] *)
End Plan_src13_r0c0_28653_32748.

Module Plan_src13_r0c0_28653_32748_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_28653_32748_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?a__?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?a__?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?a__?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?a?a}N?`]a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_28653_32748_L.

Module Cert_src13_r0c0_28653_32748_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_28653_32748 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_28653_32748_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_28653_32748 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_28653_32748_0 : class := [(QLook,4,4); (QFlen,28659,32754); (QCfgLen,0,0); (QRoom,28653,32748)].
Definition SH_src13_r0c0_28653_32748_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_28653_32748_0 : nat := 3000.
Lemma cert_src13_r0c0_28653_32748_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_28653_32748_0 (hs_of HT_src13_r0c0_28653_32748) HS_src13_pfx1_0 C_src13_r0c0_28653_32748_0 P_src13_r0c0_28653_32748_0 = COk SH_src13_r0c0_28653_32748_0.
Proof. cert_vm (COk SH_src13_r0c0_28653_32748_0). Qed.
End Cert_src13_r0c0_28653_32748_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_29_44.   (* [comment removed for export] *)
End Plan_src13_r0c0_29_44.

Module Plan_src13_r0c0_29_44_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_29_44_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_29_44_L.

Module Cert_src13_r0c0_29_44_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_29_44 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_29_44_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_29_44 : htab := [(40%nat, (HS_src13_shX40_0, SH_src13_shX40_0))].

Definition C_src13_r0c0_29_44_0 : class := [(QLook,4,4); (QFlen,35,50); (QCfgLen,0,0); (QRoom,29,44)].
Definition SH_src13_r0c0_29_44_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_src13_r0c0_29_44_0 : nat := 3000.
Lemma cert_src13_r0c0_29_44_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_29_44_0 (hs_of HT_src13_r0c0_29_44) HS_src13_pfx1_0 C_src13_r0c0_29_44_0 P_src13_r0c0_29_44_0 = COk SH_src13_r0c0_29_44_0.
Proof. cert_vm (COk SH_src13_r0c0_29_44_0). Qed.
End Cert_src13_r0c0_29_44_0.
