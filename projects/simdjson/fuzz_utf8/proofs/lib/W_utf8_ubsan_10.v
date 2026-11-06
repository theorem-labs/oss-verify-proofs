(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require AxSymExec3 AsanPlan PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require AsanNodesIO AsanMainLib ImgParams MainDefs Img_utf8_ubsan Cert_common ITab_utf8_ubsan Segs_utf8_ubsan HS_utf8_ubsan_pfx1 Sh_utf8_ubsan_4 PlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_2029_2332.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_2029_2332.

Module Plan_utf8_ubsan_r0c0_2029_2332_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_2029_2332_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?o_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?o_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?o_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_2029_2332_L.

Module Cert_utf8_ubsan_r0c0_2029_2332_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_2029_2332 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_2029_2332_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_2029_2332 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_2029_2332_0 : class := [(QLook,4,4); (QFlen,2035,2338); (QCfgLen,0,0); (QRoom,2029,2332)].
Definition SH_utf8_ubsan_r0c0_2029_2332_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_2029_2332_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_2029_2332_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_2029_2332_0 (hs_of HT_utf8_ubsan_r0c0_2029_2332) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_2029_2332_0 P_utf8_ubsan_r0c0_2029_2332_0 = COk SH_utf8_ubsan_r0c0_2029_2332_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_2029_2332_0). Qed.
End Cert_utf8_ubsan_r0c0_2029_2332_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_20461_21820.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_20461_21820.

Module Plan_utf8_ubsan_r0c0_20461_21820_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_20461_21820_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`o_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`o_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`o_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_20461_21820_L.

Module Cert_utf8_ubsan_r0c0_20461_21820_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_20461_21820 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_20461_21820_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_20461_21820 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_20461_21820_0 : class := [(QLook,4,4); (QFlen,20467,21826); (QCfgLen,0,0); (QRoom,20461,21820)].
Definition SH_utf8_ubsan_r0c0_20461_21820_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_20461_21820_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_20461_21820_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_20461_21820_0 (hs_of HT_utf8_ubsan_r0c0_20461_21820) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_20461_21820_0 P_utf8_ubsan_r0c0_20461_21820_0 = COk SH_utf8_ubsan_r0c0_20461_21820_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_20461_21820_0). Qed.
End Cert_utf8_ubsan_r0c0_20461_21820_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_21821_24556.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_21821_24556.

Module Plan_utf8_ubsan_r0c0_21821_24556_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_21821_24556_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`o_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`o_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`o_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?`n~?a}N?`rd?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_21821_24556_L.

Module Cert_utf8_ubsan_r0c0_21821_24556_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_21821_24556 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_21821_24556_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_21821_24556 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_21821_24556_0 : class := [(QLook,4,4); (QFlen,21827,24562); (QCfgLen,0,0); (QRoom,21821,24556)].
Definition SH_utf8_ubsan_r0c0_21821_24556_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_21821_24556_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_21821_24556_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_21821_24556_0 (hs_of HT_utf8_ubsan_r0c0_21821_24556) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_21821_24556_0 P_utf8_ubsan_r0c0_21821_24556_0 = COk SH_utf8_ubsan_r0c0_21821_24556_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_21821_24556_0). Qed.
End Cert_utf8_ubsan_r0c0_21821_24556_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_2333_2716.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_2333_2716.

Module Plan_utf8_ubsan_r0c0_2333_2716_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_2333_2716_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?o_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?o_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?o_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_2333_2716_L.

Module Cert_utf8_ubsan_r0c0_2333_2716_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_2333_2716 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_2333_2716_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_2333_2716 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_2333_2716_0 : class := [(QLook,4,4); (QFlen,2339,2722); (QCfgLen,0,0); (QRoom,2333,2716)].
Definition SH_utf8_ubsan_r0c0_2333_2716_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_2333_2716_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_2333_2716_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_2333_2716_0 (hs_of HT_utf8_ubsan_r0c0_2333_2716) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_2333_2716_0 P_utf8_ubsan_r0c0_2333_2716_0 = COk SH_utf8_ubsan_r0c0_2333_2716_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_2333_2716_0). Qed.
End Cert_utf8_ubsan_r0c0_2333_2716_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_237_284.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_237_284.

Module Plan_utf8_ubsan_r0c0_237_284_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_237_284_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?rcHa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?b?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?b?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_237_284_L.

Module Cert_utf8_ubsan_r0c0_237_284_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_237_284 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_237_284_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX137_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX137.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_237_284 : htab := [(137%nat, (HS_utf8_ubsan_shX137_0, SH_utf8_ubsan_shX137_0))].

Definition C_utf8_ubsan_r0c0_237_284_0 : class := [(QLook,4,4); (QFlen,243,290); (QCfgLen,0,0); (QRoom,237,284)].
Definition SH_utf8_ubsan_r0c0_237_284_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 137).
Definition FUEL_utf8_ubsan_r0c0_237_284_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_237_284_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_237_284_0 (hs_of HT_utf8_ubsan_r0c0_237_284) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_237_284_0 P_utf8_ubsan_r0c0_237_284_0 = COk SH_utf8_ubsan_r0c0_237_284_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_237_284_0). Qed.
End Cert_utf8_ubsan_r0c0_237_284_0.
