(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require AxSymExec3 AsanPlan PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require AsanNodesIO AsanMainLib ImgParams MainDefs Img_utf8_ubsan Cert_common ITab_utf8_ubsan Segs_utf8_ubsan HS_utf8_ubsan_pfx1 Sh_utf8_ubsan_2 Sh_utf8_ubsan_4 Sh_utf8_ubsan_1 HS_utf8_ubsan_pfx3 Sh_utf8_ubsan_3 PlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_65517_65529.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_65517_65529.

Module Plan_utf8_ubsan_r0c0_65517_65529_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_65517_65529_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?cg_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?cg_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mweWbmwmW??@`n{dG??N??@`n{dG??N??@`nhu?raYa|WIa|W@Ra|X@`\a|Y?g_?a|Z@Za|[?cg_?a|\@La|]?cg_?a|^@Va}?@Wa}@@X"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_65517_65529_L.

Module Cert_utf8_ubsan_r0c0_65517_65529_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_65517_65529 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_65517_65529_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX90_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX90.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_65517_65529 : htab := [(90%nat, (HS_utf8_ubsan_shX90_0, SH_utf8_ubsan_shX90_0))].

Definition C_utf8_ubsan_r0c0_65517_65529_0 : class := [(QLook,4,4); (QFlen,65523,65535); (QCfgLen,0,0); (QRoom,65517,65529)].
Definition SH_utf8_ubsan_r0c0_65517_65529_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 90).
Definition FUEL_utf8_ubsan_r0c0_65517_65529_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_65517_65529_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_65517_65529_0 (hs_of HT_utf8_ubsan_r0c0_65517_65529) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_65517_65529_0 P_utf8_ubsan_r0c0_65517_65529_0 = COk SH_utf8_ubsan_r0c0_65517_65529_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_65517_65529_0). Qed.
End Cert_utf8_ubsan_r0c0_65517_65529_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_669_796.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_669_796.

Module Plan_utf8_ubsan_r0c0_669_796_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_669_796_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?rcEa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?a?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?a?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_669_796_L.

Module Cert_utf8_ubsan_r0c0_669_796_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_669_796 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_669_796_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX134_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX134.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_669_796 : htab := [(134%nat, (HS_utf8_ubsan_shX134_0, SH_utf8_ubsan_shX134_0))].

Definition C_utf8_ubsan_r0c0_669_796_0 : class := [(QLook,4,4); (QFlen,675,802); (QCfgLen,0,0); (QRoom,669,796)].
Definition SH_utf8_ubsan_r0c0_669_796_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 134).
Definition FUEL_utf8_ubsan_r0c0_669_796_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_669_796_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_669_796_0 (hs_of HT_utf8_ubsan_r0c0_669_796) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_669_796_0 P_utf8_ubsan_r0c0_669_796_0 = COk SH_utf8_ubsan_r0c0_669_796_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_669_796_0). Qed.
End Cert_utf8_ubsan_r0c0_669_796_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_77_92.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_77_92.

Module Plan_utf8_ubsan_r0c0_77_92_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_77_92_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_77_92_L.

Module Cert_utf8_ubsan_r0c0_77_92_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_77_92 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_77_92_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_1.Cert_utf8_ubsan_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_1.HS_utf8_ubsan_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_77_92 : htab := [(40%nat, (HS_utf8_ubsan_shX40_0, SH_utf8_ubsan_shX40_0))].

Definition C_utf8_ubsan_r0c0_77_92_0 : class := [(QLook,4,4); (QFlen,83,98); (QCfgLen,0,0); (QRoom,77,92)].
Definition SH_utf8_ubsan_r0c0_77_92_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_utf8_ubsan_r0c0_77_92_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_77_92_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_77_92_0 (hs_of HT_utf8_ubsan_r0c0_77_92) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_77_92_0 P_utf8_ubsan_r0c0_77_92_0 = COk SH_utf8_ubsan_r0c0_77_92_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_77_92_0). Qed.
End Cert_utf8_ubsan_r0c0_77_92_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_797_1004.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_797_1004.

Module Plan_utf8_ubsan_r0c0_797_1004_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_797_1004_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?rcEa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?a?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?a?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_797_1004_L.

Module Cert_utf8_ubsan_r0c0_797_1004_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_797_1004 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_797_1004_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX134_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX134.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_797_1004 : htab := [(134%nat, (HS_utf8_ubsan_shX134_0, SH_utf8_ubsan_shX134_0))].

Definition C_utf8_ubsan_r0c0_797_1004_0 : class := [(QLook,4,4); (QFlen,803,1010); (QCfgLen,0,0); (QRoom,797,1004)].
Definition SH_utf8_ubsan_r0c0_797_1004_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 134).
Definition FUEL_utf8_ubsan_r0c0_797_1004_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_797_1004_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_797_1004_0 (hs_of HT_utf8_ubsan_r0c0_797_1004) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_797_1004_0 P_utf8_ubsan_r0c0_797_1004_0 = COk SH_utf8_ubsan_r0c0_797_1004_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_797_1004_0). Qed.
End Cert_utf8_ubsan_r0c0_797_1004_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_8173_9340.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_8173_9340.

Module Plan_utf8_ubsan_r0c0_8173_9340_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_8173_9340_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`w_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`w_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`w_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_8173_9340_L.

Module Cert_utf8_ubsan_r0c0_8173_9340_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_8173_9340 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_8173_9340_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_8173_9340 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_8173_9340_0 : class := [(QLook,4,4); (QFlen,8179,9346); (QCfgLen,0,0); (QRoom,8173,9340)].
Definition SH_utf8_ubsan_r0c0_8173_9340_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_8173_9340_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_8173_9340_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_8173_9340_0 (hs_of HT_utf8_ubsan_r0c0_8173_9340) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_8173_9340_0 P_utf8_ubsan_r0c0_8173_9340_0 = COk SH_utf8_ubsan_r0c0_8173_9340_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_8173_9340_0). Qed.
End Cert_utf8_ubsan_r0c0_8173_9340_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_9341_10908.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_9341_10908.

Module Plan_utf8_ubsan_r0c0_9341_10908_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_9341_10908_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?a__?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?a__?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?a__?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_9341_10908_L.

Module Cert_utf8_ubsan_r0c0_9341_10908_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_9341_10908 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_9341_10908_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_9341_10908 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_9341_10908_0 : class := [(QLook,4,4); (QFlen,9347,10914); (QCfgLen,0,0); (QRoom,9341,10908)].
Definition SH_utf8_ubsan_r0c0_9341_10908_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_9341_10908_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_9341_10908_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_9341_10908_0 (hs_of HT_utf8_ubsan_r0c0_9341_10908) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_9341_10908_0 P_utf8_ubsan_r0c0_9341_10908_0 = COk SH_utf8_ubsan_r0c0_9341_10908_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_9341_10908_0). Qed.
End Cert_utf8_ubsan_r0c0_9341_10908_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_93_108.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_93_108.

Module Plan_utf8_ubsan_r0c0_93_108_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_93_108_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_93_108_L.

Module Cert_utf8_ubsan_r0c0_93_108_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_93_108 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_93_108_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_1.Cert_utf8_ubsan_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_1.HS_utf8_ubsan_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_93_108 : htab := [(40%nat, (HS_utf8_ubsan_shX40_0, SH_utf8_ubsan_shX40_0))].

Definition C_utf8_ubsan_r0c0_93_108_0 : class := [(QLook,4,4); (QFlen,99,114); (QCfgLen,0,0); (QRoom,93,108)].
Definition SH_utf8_ubsan_r0c0_93_108_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_utf8_ubsan_r0c0_93_108_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_93_108_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_93_108_0 (hs_of HT_utf8_ubsan_r0c0_93_108) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_93_108_0 P_utf8_ubsan_r0c0_93_108_0 = COk SH_utf8_ubsan_r0c0_93_108_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_93_108_0). Qed.
End Cert_utf8_ubsan_r0c0_93_108_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c1_1005_1148.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c1_1005_1148.

Module Plan_utf8_ubsan_r0c1_1005_1148_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c1_1005_1148_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTbAC??g_?@a@bB?g_?bCC??g_?@^bD?g_?bEC??g_?@LbF?cg_?bGC??g_?@RbH?o_?bI@XbJC??g_?@a@bK?g_?bLC??g_?@^bM?g_?bNC??g_?@LbO?cg_?bP@VbQ@WbR?c__?bS?`~w_?bT?f~~z~o___?bU?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@mxjG@AHF?GC@?E??@`n{dGTT@?C??N??@mxk?ra\a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@fTa}D@fUa}E@fVa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@g?a}R@g@a}S@gAa}T@gB?@nwr??@nwyOmJTgCC??g_?@a@gD?g_?gEC??g_?@^gF?g_?gGC??g_?@LgH?cg_?gIC??g_?@RgJ?o_?gK@XgLC??g_?@a@gM?g_?gNC??g_?@^gO?g_?gPC??g_?@LgQ?cg_?gR@VgS@WgT?c__?gU?`~w_?gV?f~~z~o___?gW?c_o___?@?@mxt?m`?[hE?`UhF?MhG?n?hH@]hIA?A?C??g_?@^C??`?@`??`?hJ??hK@]hLA?A?C??f~^@^C??^@`??`@hM?k?hN?~~~~~~~~~~~z]hO?m?hP?g?hQA?A?C??g_?@^C??`?@`??`?hR??hS?`yzz?hTAHF?GC@?EhU??hV?~~~~~~~~~~~~[hW??hX??hY??hZ??h[?~~~~~~~~|{__?h\?~~~~~~~~}___?h]?~~~~~~~~~~~~Oh^@hDi?@Ti@@X@?@mxjG@AHF?GC@?EA?@`n{dGTT@?C??N??@mxk?ra^a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@nBa}D@nCa}E@nDa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@nMa}R@nNa}S@nOa}T@nP?@nwr??@nwyOmJTnQC??g_?@a@nR?g_?nSC??g_?@^nT?g_?nUC??g_?@LnV?cg_?nWC??g_?@RnX?o_?nY@XnZC??g_?@a@n[?g_?n\C??g_?@^n]?g_?n^C??g_?@Lo??cg_?o@@VoA@WoB?c__?oC?`~w_?oD?f~~z~o___?oE?c_o___?@?@mxt?m`@[oS?`UoT?MoU?n?oV@]oWA?A?C??g_?@^C??`?@`??`?oX??oY@]oZA?A?C??f~^@^C??^@`??`@o[?k?o\?~~~~~~~~~~~z]o]?m?o^?g?p?A?A?C??g_?@^C??`?@`??`?p@??pA?`yzz?pBA?AHF?GC@?E?@pC??pD?~~~~~~~~~~~~[pE??pF??pG??pH??pI?~~~~~~~~|{__?pJ?~~~~~~~~}___?pK?~~~~~~~~~~~~OpL@oRpM@TpN@X@?@mxjG@AHF?GC@?EC?@`n{dGTT@?C??N??@mxk?rb?a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@uPa}D@uQa}E@uRa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@u[a}R@u\a}S@u]a}T@u^?@nwr??@nwyOmJTv?C??g_?@a@v@?g_?vAC??g_?@^vB?g_?vCC??g_?@LvD?cg_?vEC??g_?@RvF?o_?vG@XvHC??g_?@a@vI?g_?vJC??g_?@^vK?g_?vLC??g_?@LvM?cg_?vN@VvO@WvP?c__?vQ?`~w_?vR?f~~z~o___?vS?c_o___?@?@mxt?m`A[wA?`UwB?MwC?n?wD@]wEA?A?C??g_?@^C??`?@`??`?wF??wG@]wHA?A?C??f~^@^C??^@`??`@wI?k?wJ?~~~~~~~~~~~z]wK?m?wL?g?wMA?A?C??g_?@^C??`?@`??`?wN??wO?`yzz?wP?AwQ??wR?~~~~~~~~~~~~[wS??wT??wU??wV??wW?~~~~~~~~|{__?wX?~~~~~~~~}___?wY?~~~~~~~~~~~~OwZ@w@w[@Tw\@X@?@`n{dGTT@?C??N??@mxk?rb@a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@|^a}D@}?a}E@}@a}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@}Ia}R@}Ja}S@}Ka}T@}L"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c1_1005_1148_L.

Module Cert_utf8_ubsan_r0c1_1005_1148_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c1_1005_1148 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx3 Plan_utf8_ubsan_r0c1_1005_1148_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX93_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX95_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX96_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX97_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX93 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX95 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX96 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX97.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c1_1005_1148 : htab := [(93%nat, (HS_utf8_ubsan_shX93_0, SH_utf8_ubsan_shX93_0)); (95%nat, (HS_utf8_ubsan_shX95_0, SH_utf8_ubsan_shX95_0)); (96%nat, (HS_utf8_ubsan_shX96_0, SH_utf8_ubsan_shX96_0)); (97%nat, (HS_utf8_ubsan_shX97_0, SH_utf8_ubsan_shX97_0))].

Definition C_utf8_ubsan_r0c1_1005_1148_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,1005,1148)].
Definition SH_utf8_ubsan_r0c1_1005_1148_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 93) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 95) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 96) (SHole 97)))).
Definition FUEL_utf8_ubsan_r0c1_1005_1148_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c1_1005_1148_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c1_1005_1148_0 (hs_of HT_utf8_ubsan_r0c1_1005_1148) HS_utf8_ubsan_pfx3_0 C_utf8_ubsan_r0c1_1005_1148_0 P_utf8_ubsan_r0c1_1005_1148_0 = COk SH_utf8_ubsan_r0c1_1005_1148_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c1_1005_1148_0). Qed.
End Cert_utf8_ubsan_r0c1_1005_1148_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c1_10909_12268.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c1_10909_12268.

Module Plan_utf8_ubsan_r0c1_10909_12268_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c1_10909_12268_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTbAC??g_?@a@bB?g_?bCC??g_?@^bD?w_?bEC??g_?@LbF?cg_?bGC??g_?@RbH?o_?bI@XbJC??g_?@a@bK?g_?bLC??g_?@^bM?w_?bNC??g_?@LbO?cg_?bP@VbQ@WbR?c__?bS?`~w_?bT?f~~z~o___?bU?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@mxjG@AHF?GC@?E??@`n{dGTT@?C??N??@mxk?ra\a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?w_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fUa}E@fVa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?v~?a}N?xq?a}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@g?a}R@g@a}S@gAa}T@gB?@nwr??@nwyOmJTgCC??g_?@a@gD?g_?gEC??g_?@^gF?w_?gGC??g_?@LgH?cg_?gIC??g_?@RgJ?o_?gK@XgLC??g_?@a@gM?g_?gNC??g_?@^gO?w_?gPC??g_?@LgQ?cg_?gR@VgS@WgT?c__?gU?`~w_?gV?f~~z~o___?gW?c_o___?@?@mxt?m`?[hE?`UhF?MhG?n?hH@]hIA?A?C??g_?@^C??`?@`??`?hJ??hK@]hLA?A?C??f~^@^C??^@`??`@hM?k?hN?~~~~~~~~~~~z]hO?m?hP?g?hQA?A?C??g_?@^C??`?@`??`?hR??hS?`yzz?hTAHF?GC@?EhU??hV?~~~~~~~~~~~~[hW??hX??hY??hZ??h[?~~~~~~~~|{__?h\?~~~~~~~~}___?h]?~~~~~~~~~~~~Oh^@hDi?@Ti@@X@?@mxjG@AHF?GC@?EA?@`n{dGTT@?C??N??@mxk?ra^a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?w_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@nCa}E@nDa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?v~?a}N?xq?a}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@nMa}R@nNa}S@nOa}T@nP?@nwr??@nwyOmJTnQC??g_?@a@nR?g_?nSC??g_?@^nT?w_?nUC??g_?@LnV?cg_?nWC??g_?@RnX?o_?nY@XnZC??g_?@a@n[?g_?n\C??g_?@^n]?w_?n^C??g_?@Lo??cg_?o@@VoA@WoB?c__?oC?`~w_?oD?f~~z~o___?oE?c_o___?@?@mxt?m`@[oS?`UoT?MoU?n?oV@]oWA?A?C??g_?@^C??`?@`??`?oX??oY@]oZA?A?C??f~^@^C??^@`??`@o[?k?o\?~~~~~~~~~~~z]o]?m?o^?g?p?A?A?C??g_?@^C??`?@`??`?p@??pA?`yzz?pBA?AHF?GC@?E?@pC??pD?~~~~~~~~~~~~[pE??pF??pG??pH??pI?~~~~~~~~|{__?pJ?~~~~~~~~}___?pK?~~~~~~~~~~~~OpL@oRpM@TpN@X@?@mxjG@AHF?GC@?EC?@`n{dGTT@?C??N??@mxk?rb?a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?w_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@uQa}E@uRa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?v~?a}N?xq?a}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@u[a}R@u\a}S@u]a}T@u^?@nwr??@nwyOmJTv?C??g_?@a@v@?g_?vAC??g_?@^vB?w_?vCC??g_?@LvD?cg_?vEC??g_?@RvF?o_?vG@XvHC??g_?@a@vI?g_?vJC??g_?@^vK?w_?vLC??g_?@LvM?cg_?vN@VvO@WvP?c__?vQ?`~w_?vR?f~~z~o___?vS?c_o___?@?@mxt?m`A[wA?`UwB?MwC?n?wD@]wEA?A?C??g_?@^C??`?@`??`?wF??wG@]wHA?A?C??f~^@^C??^@`??`@wI?k?wJ?~~~~~~~~~~~z]wK?m?wL?g?wMA?A?C??g_?@^C??`?@`??`?wN??wO?`yzz?wP?AwQ??wR?~~~~~~~~~~~~[wS??wT??wU??wV??wW?~~~~~~~~|{__?wX?~~~~~~~~}___?wY?~~~~~~~~~~~~OwZ@w@w[@Tw\@X@?@`n{dGTT@?C??N??@mxk?rb@a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?w_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@}?a}E@}@a}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?v~?a}N?xq?a}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@}Ia}R@}Ja}S@}Ka}T@}L"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c1_10909_12268_L.

Module Cert_utf8_ubsan_r0c1_10909_12268_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c1_10909_12268 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx3 Plan_utf8_ubsan_r0c1_10909_12268_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX93_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX95_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX96_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX97_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX93 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX95 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX96 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX97.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c1_10909_12268 : htab := [(93%nat, (HS_utf8_ubsan_shX93_0, SH_utf8_ubsan_shX93_0)); (95%nat, (HS_utf8_ubsan_shX95_0, SH_utf8_ubsan_shX95_0)); (96%nat, (HS_utf8_ubsan_shX96_0, SH_utf8_ubsan_shX96_0)); (97%nat, (HS_utf8_ubsan_shX97_0, SH_utf8_ubsan_shX97_0))].

Definition C_utf8_ubsan_r0c1_10909_12268_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,10909,12268)].
Definition SH_utf8_ubsan_r0c1_10909_12268_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 93) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 95) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 96) (SHole 97)))).
Definition FUEL_utf8_ubsan_r0c1_10909_12268_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c1_10909_12268_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c1_10909_12268_0 (hs_of HT_utf8_ubsan_r0c1_10909_12268) HS_utf8_ubsan_pfx3_0 C_utf8_ubsan_r0c1_10909_12268_0 P_utf8_ubsan_r0c1_10909_12268_0 = COk SH_utf8_ubsan_r0c1_10909_12268_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c1_10909_12268_0). Qed.
End Cert_utf8_ubsan_r0c1_10909_12268_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c1_109_124.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c1_109_124.

Module Plan_utf8_ubsan_r0c1_109_124_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c1_109_124_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPb@C??g_?@^bA?g_?bBC??g_?@LbC?cg_?bDC??g_?@RbE?o_?bF@XbGC??g_?@^bH?g_?bIC??g_?@LbJ?cg_?bK@VbL@WbM?c__?bN?`~w_?bO?f~~z~o___?bP?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@mxjG@AHF?GC@?E??@`n{dGTT@?C?@mxk?rbPa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@fOa}B@fPa}C@fQa}D@]a}EA?A?C??g_?@^C??`?@`??b?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??b?a}O@fZa}P@f[a}Q@f\a}R@f]?@nwr??@nwyOmLPf^C??g_?@^g??g_?g@C??g_?@LgA?cg_?gBC??g_?@RgC?o_?gD@XgEC??g_?@^gF?g_?gGC??g_?@LgH?cg_?gI@VgJ@WgK?c__?gL?`~w_?gM?f~~z~o___?gN?c_o___?@?@mxt?m`?[g\?`Ug]?Mg^?n?h?@]h@A?A?C??g_?@^C??`?@`??b?hA??hB@]hCA?A?C??f~^@^C??^@`??b@hD?k?hE?~~~~~~~~~~~z]hF?m?hG?g?hHA?A?C??g_?@^C??`?@`??b?hI??hJ?`yzz?hKAHF?GC@?EhL??hM?~~~~~~~~~~~~[hN??hO??hP??hQ??hR?~~~~~~~~|{__?hS?~~~~~~~~}___?hT?~~~~~~~~~~~~OhU@g[hV@ThW@X@?@mxjG@AHF?GC@?EA?@`n{dGTT@?C?@mxk?rbRa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@mYa}B@mZa}C@m[a}D@]a}EA?A?C??g_?@^C??`?@`??b?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??b?a}O@nDa}P@nEa}Q@nFa}R@nG?@nwr??@nwyOmLPnHC??g_?@^nI?g_?nJC??g_?@LnK?cg_?nLC??g_?@RnM?o_?nN@XnOC??g_?@^nP?g_?nQC??g_?@LnR?cg_?nS@VnT@WnU?c__?nV?`~w_?nW?f~~z~o___?nX?c_o___?@?@mxt?m`@[oF?`UoG?MoH?n?oI@]oJA?A?C??g_?@^C??`?@`??b?oK??oL@]oMA?A?C??f~^@^C??^@`??b@oN?k?oO?~~~~~~~~~~~z]oP?m?oQ?g?oRA?A?C??g_?@^C??`?@`??b?oS??oT?`yzz?oUA?AHF?GC@?E?@oV??oW?~~~~~~~~~~~~[oX??oY??oZ??o[??o\?~~~~~~~~|{__?o]?~~~~~~~~}___?o^?~~~~~~~~~~~~Op?@oEp@@TpA@X@?@mxjG@AHF?GC@?EC?@`n{dGTT@?C?@mxk?rbSa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@uCa}B@uDa}C@uEa}D@]a}EA?A?C??g_?@^C??`?@`??b?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??b?a}O@uNa}P@uOa}Q@uPa}R@uQ?@nwr??@nwyOmLPuRC??g_?@^uS?g_?uTC??g_?@LuU?cg_?uVC??g_?@RuW?o_?uX@XuYC??g_?@^uZ?g_?u[C??g_?@Lu\?cg_?u]@Vu^@Wv??c__?v@?`~w_?vA?f~~z~o___?vB?c_o___?@?@mxt?m`A[vP?`UvQ?MvR?n?vS@]vTA?A?C??g_?@^C??`?@`??b?vU??vV@]vWA?A?C??f~^@^C??^@`??b@vX?k?vY?~~~~~~~~~~~z]vZ?m?v[?g?v\A?A?C??g_?@^C??`?@`??b?v]??v^?`yzz?w??Aw@??wA?~~~~~~~~~~~~[wB??wC??wD??wE??wF?~~~~~~~~|{__?wG?~~~~~~~~}___?wH?~~~~~~~~~~~~OwI@vOwJ@TwK@X@?@`n{dGTT@?C?@mxk?rbTa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@|Ma}B@|Na}C@|Oa}D@]a}EA?A?C??g_?@^C??`?@`??b?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??b?a}O@|Xa}P@|Ya}Q@|Za}R@|["%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c1_109_124_L.

Module Cert_utf8_ubsan_r0c1_109_124_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c1_109_124 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx3 Plan_utf8_ubsan_r0c1_109_124_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.Cert_utf8_ubsan_shX113_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.Cert_utf8_ubsan_shX115_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.Cert_utf8_ubsan_shX116_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.Cert_utf8_ubsan_shX117_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.HS_utf8_ubsan_shX113 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.HS_utf8_ubsan_shX115 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.HS_utf8_ubsan_shX116 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.HS_utf8_ubsan_shX117.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c1_109_124 : htab := [(113%nat, (HS_utf8_ubsan_shX113_0, SH_utf8_ubsan_shX113_0)); (115%nat, (HS_utf8_ubsan_shX115_0, SH_utf8_ubsan_shX115_0)); (116%nat, (HS_utf8_ubsan_shX116_0, SH_utf8_ubsan_shX116_0)); (117%nat, (HS_utf8_ubsan_shX117_0, SH_utf8_ubsan_shX117_0))].

Definition C_utf8_ubsan_r0c1_109_124_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,109,124)].
Definition SH_utf8_ubsan_r0c1_109_124_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 113) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 115) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 116) (SHole 117)))).
Definition FUEL_utf8_ubsan_r0c1_109_124_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c1_109_124_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c1_109_124_0 (hs_of HT_utf8_ubsan_r0c1_109_124) HS_utf8_ubsan_pfx3_0 C_utf8_ubsan_r0c1_109_124_0 P_utf8_ubsan_r0c1_109_124_0 = COk SH_utf8_ubsan_r0c1_109_124_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c1_109_124_0). Qed.
End Cert_utf8_ubsan_r0c1_109_124_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c1_1149_1340.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c1_1149_1340.

Module Plan_utf8_ubsan_r0c1_1149_1340_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c1_1149_1340_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTbAC??g_?@a@bB?g_?bCC??g_?@^bD?g_?bEC??g_?@LbF?cg_?bGC??g_?@RbH?o_?bI@XbJC??g_?@a@bK?g_?bLC??g_?@^bM?g_?bNC??g_?@LbO?cg_?bP@VbQ@WbR?c__?bS?`~w_?bT?f~~z~o___?bU?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@mxjG@AHF?GC@?E??@`n{dGTT@?C??N??@mxk?ra\a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@fTa}D@fUa}E@fVa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@g?a}R@g@a}S@gAa}T@gB?@nwr??@nwyOmJTgCC??g_?@a@gD?g_?gEC??g_?@^gF?g_?gGC??g_?@LgH?cg_?gIC??g_?@RgJ?o_?gK@XgLC??g_?@a@gM?g_?gNC??g_?@^gO?g_?gPC??g_?@LgQ?cg_?gR@VgS@WgT?c__?gU?`~w_?gV?f~~z~o___?gW?c_o___?@?@mxt?m`?[hE?`UhF?MhG?n?hH@]hIA?A?C??g_?@^C??`?@`??`?hJ??hK@]hLA?A?C??f~^@^C??^@`??`@hM?k?hN?~~~~~~~~~~~z]hO?m?hP?g?hQA?A?C??g_?@^C??`?@`??`?hR??hS?`yzz?hTAHF?GC@?EhU??hV?~~~~~~~~~~~~[hW??hX??hY??hZ??h[?~~~~~~~~|{__?h\?~~~~~~~~}___?h]?~~~~~~~~~~~~Oh^@hDi?@Ti@@X@?@mxjG@AHF?GC@?EA?@`n{dGTT@?C??N??@mxk?ra^a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@nBa}D@nCa}E@nDa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@nMa}R@nNa}S@nOa}T@nP?@nwr??@nwyOmJTnQC??g_?@a@nR?g_?nSC??g_?@^nT?g_?nUC??g_?@LnV?cg_?nWC??g_?@RnX?o_?nY@XnZC??g_?@a@n[?g_?n\C??g_?@^n]?g_?n^C??g_?@Lo??cg_?o@@VoA@WoB?c__?oC?`~w_?oD?f~~z~o___?oE?c_o___?@?@mxt?m`@[oS?`UoT?MoU?n?oV@]oWA?A?C??g_?@^C??`?@`??`?oX??oY@]oZA?A?C??f~^@^C??^@`??`@o[?k?o\?~~~~~~~~~~~z]o]?m?o^?g?p?A?A?C??g_?@^C??`?@`??`?p@??pA?`yzz?pBA?AHF?GC@?E?@pC??pD?~~~~~~~~~~~~[pE??pF??pG??pH??pI?~~~~~~~~|{__?pJ?~~~~~~~~}___?pK?~~~~~~~~~~~~OpL@oRpM@TpN@X@?@mxjG@AHF?GC@?EC?@`n{dGTT@?C??N??@mxk?rb?a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@uPa}D@uQa}E@uRa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@u[a}R@u\a}S@u]a}T@u^?@nwr??@nwyOmJTv?C??g_?@a@v@?g_?vAC??g_?@^vB?g_?vCC??g_?@LvD?cg_?vEC??g_?@RvF?o_?vG@XvHC??g_?@a@vI?g_?vJC??g_?@^vK?g_?vLC??g_?@LvM?cg_?vN@VvO@WvP?c__?vQ?`~w_?vR?f~~z~o___?vS?c_o___?@?@mxt?m`A[wA?`UwB?MwC?n?wD@]wEA?A?C??g_?@^C??`?@`??`?wF??wG@]wHA?A?C??f~^@^C??^@`??`@wI?k?wJ?~~~~~~~~~~~z]wK?m?wL?g?wMA?A?C??g_?@^C??`?@`??`?wN??wO?`yzz?wP?AwQ??wR?~~~~~~~~~~~~[wS??wT??wU??wV??wW?~~~~~~~~|{__?wX?~~~~~~~~}___?wY?~~~~~~~~~~~~OwZ@w@w[@Tw\@X@?@`n{dGTT@?C??N??@mxk?rb@a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@|^a}D@}?a}E@}@a}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@}Ia}R@}Ja}S@}Ka}T@}L"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c1_1149_1340_L.

Module Cert_utf8_ubsan_r0c1_1149_1340_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c1_1149_1340 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx3 Plan_utf8_ubsan_r0c1_1149_1340_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX93_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX95_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX96_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX97_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX93 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX95 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX96 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX97.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c1_1149_1340 : htab := [(93%nat, (HS_utf8_ubsan_shX93_0, SH_utf8_ubsan_shX93_0)); (95%nat, (HS_utf8_ubsan_shX95_0, SH_utf8_ubsan_shX95_0)); (96%nat, (HS_utf8_ubsan_shX96_0, SH_utf8_ubsan_shX96_0)); (97%nat, (HS_utf8_ubsan_shX97_0, SH_utf8_ubsan_shX97_0))].

Definition C_utf8_ubsan_r0c1_1149_1340_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,1149,1340)].
Definition SH_utf8_ubsan_r0c1_1149_1340_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 93) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 95) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 96) (SHole 97)))).
Definition FUEL_utf8_ubsan_r0c1_1149_1340_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c1_1149_1340_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c1_1149_1340_0 (hs_of HT_utf8_ubsan_r0c1_1149_1340) HS_utf8_ubsan_pfx3_0 C_utf8_ubsan_r0c1_1149_1340_0 P_utf8_ubsan_r0c1_1149_1340_0 = COk SH_utf8_ubsan_r0c1_1149_1340_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c1_1149_1340_0). Qed.
End Cert_utf8_ubsan_r0c1_1149_1340_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c1_12269_13084.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c1_12269_13084.

Module Plan_utf8_ubsan_r0c1_12269_13084_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c1_12269_13084_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTbAC??g_?@a@bB?g_?bCC??g_?@^bD?`__?bEC??g_?@LbF?cg_?bGC??g_?@RbH?o_?bI@XbJC??g_?@a@bK?g_?bLC??g_?@^bM?`__?bNC??g_?@LbO?cg_?bP@VbQ@WbR?c__?bS?`~w_?bT?f~~z~o___?bU?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@mxjG@AHF?GC@?E??@`n{dGTT@?C??N??@mxk?ra\a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fUa}E@fVa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@g?a}R@g@a}S@gAa}T@gB?@nwr??@nwyOmJTgCC??g_?@a@gD?g_?gEC??g_?@^gF?`__?gGC??g_?@LgH?cg_?gIC??g_?@RgJ?o_?gK@XgLC??g_?@a@gM?g_?gNC??g_?@^gO?`__?gPC??g_?@LgQ?cg_?gR@VgS@WgT?c__?gU?`~w_?gV?f~~z~o___?gW?c_o___?@?@mxt?m`?[hE?`UhF?MhG?n?hH@]hIA?A?C??g_?@^C??`?@`??`?hJ??hK@]hLA?A?C??f~^@^C??^@`??`@hM?k?hN?~~~~~~~~~~~z]hO?m?hP?g?hQA?A?C??g_?@^C??`?@`??`?hR??hS?`yzz?hTAHF?GC@?EhU??hV?~~~~~~~~~~~~[hW??hX??hY??hZ??h[?~~~~~~~~|{__?h\?~~~~~~~~}___?h]?~~~~~~~~~~~~Oh^@hDi?@Ti@@X@?@mxjG@AHF?GC@?EA?@`n{dGTT@?C??N??@mxk?ra^a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@nCa}E@nDa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@nMa}R@nNa}S@nOa}T@nP?@nwr??@nwyOmJTnQC??g_?@a@nR?g_?nSC??g_?@^nT?`__?nUC??g_?@LnV?cg_?nWC??g_?@RnX?o_?nY@XnZC??g_?@a@n[?g_?n\C??g_?@^n]?`__?n^C??g_?@Lo??cg_?o@@VoA@WoB?c__?oC?`~w_?oD?f~~z~o___?oE?c_o___?@?@mxt?m`@[oS?`UoT?MoU?n?oV@]oWA?A?C??g_?@^C??`?@`??`?oX??oY@]oZA?A?C??f~^@^C??^@`??`@o[?k?o\?~~~~~~~~~~~z]o]?m?o^?g?p?A?A?C??g_?@^C??`?@`??`?p@??pA?`yzz?pBA?AHF?GC@?E?@pC??pD?~~~~~~~~~~~~[pE??pF??pG??pH??pI?~~~~~~~~|{__?pJ?~~~~~~~~}___?pK?~~~~~~~~~~~~OpL@oRpM@TpN@X@?@mxjG@AHF?GC@?EC?@`n{dGTT@?C??N??@mxk?rb?a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@uQa}E@uRa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@u[a}R@u\a}S@u]a}T@u^?@nwr??@nwyOmJTv?C??g_?@a@v@?g_?vAC??g_?@^vB?`__?vCC??g_?@LvD?cg_?vEC??g_?@RvF?o_?vG@XvHC??g_?@a@vI?g_?vJC??g_?@^vK?`__?vLC??g_?@LvM?cg_?vN@VvO@WvP?c__?vQ?`~w_?vR?f~~z~o___?vS?c_o___?@?@mxt?m`A[wA?`UwB?MwC?n?wD@]wEA?A?C??g_?@^C??`?@`??`?wF??wG@]wHA?A?C??f~^@^C??^@`??`@wI?k?wJ?~~~~~~~~~~~z]wK?m?wL?g?wMA?A?C??g_?@^C??`?@`??`?wN??wO?`yzz?wP?AwQ??wR?~~~~~~~~~~~~[wS??wT??wU??wV??wW?~~~~~~~~|{__?wX?~~~~~~~~}___?wY?~~~~~~~~~~~~OwZ@w@w[@Tw\@X@?@`n{dGTT@?C??N??@mxk?rb@a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@}?a}E@}@a}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@}Ia}R@}Ja}S@}Ka}T@}L"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c1_12269_13084_L.

Module Cert_utf8_ubsan_r0c1_12269_13084_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c1_12269_13084 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx3 Plan_utf8_ubsan_r0c1_12269_13084_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX93_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX95_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX96_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.Cert_utf8_ubsan_shX97_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX93 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX95 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX96 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_2.HS_utf8_ubsan_shX97.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c1_12269_13084 : htab := [(93%nat, (HS_utf8_ubsan_shX93_0, SH_utf8_ubsan_shX93_0)); (95%nat, (HS_utf8_ubsan_shX95_0, SH_utf8_ubsan_shX95_0)); (96%nat, (HS_utf8_ubsan_shX96_0, SH_utf8_ubsan_shX96_0)); (97%nat, (HS_utf8_ubsan_shX97_0, SH_utf8_ubsan_shX97_0))].

Definition C_utf8_ubsan_r0c1_12269_13084_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,12269,13084)].
Definition SH_utf8_ubsan_r0c1_12269_13084_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 93) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 95) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 96) (SHole 97)))).
Definition FUEL_utf8_ubsan_r0c1_12269_13084_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c1_12269_13084_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c1_12269_13084_0 (hs_of HT_utf8_ubsan_r0c1_12269_13084) HS_utf8_ubsan_pfx3_0 C_utf8_ubsan_r0c1_12269_13084_0 P_utf8_ubsan_r0c1_12269_13084_0 = COk SH_utf8_ubsan_r0c1_12269_13084_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c1_12269_13084_0). Qed.
End Cert_utf8_ubsan_r0c1_12269_13084_0.
