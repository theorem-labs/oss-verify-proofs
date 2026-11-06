(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require AxSymExec3 AsanPlan PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require AsanNodesIO AsanMainLib ImgParams MainDefs Img_utf8_ubsan Cert_common ITab_utf8_ubsan Segs_utf8_ubsan HS_utf8_ubsan_pfx1 Sh_utf8_ubsan_4 Sh_utf8_ubsan_1 PlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_4077_4668.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_4077_4668.

Module Plan_utf8_ubsan_r0c0_4077_4668_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_4077_4668_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`__?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`__?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`__?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_4077_4668_L.

Module Cert_utf8_ubsan_r0c0_4077_4668_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_4077_4668 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_4077_4668_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_4077_4668 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_4077_4668_0 : class := [(QLook,4,4); (QFlen,4083,4674); (QCfgLen,0,0); (QRoom,4077,4668)].
Definition SH_utf8_ubsan_r0c0_4077_4668_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_4077_4668_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_4077_4668_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_4077_4668_0 (hs_of HT_utf8_ubsan_r0c0_4077_4668) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_4077_4668_0 P_utf8_ubsan_r0c0_4077_4668_0 = COk SH_utf8_ubsan_r0c0_4077_4668_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_4077_4668_0). Qed.
End Cert_utf8_ubsan_r0c0_4077_4668_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_40941_43676.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_40941_43676.

Module Plan_utf8_ubsan_r0c0_40941_43676_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_40941_43676_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?aw_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?aw_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?aw_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?aCa}N?`]a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_40941_43676_L.

Module Cert_utf8_ubsan_r0c0_40941_43676_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_40941_43676 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_40941_43676_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_40941_43676 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_40941_43676_0 : class := [(QLook,4,4); (QFlen,40947,43682); (QCfgLen,0,0); (QRoom,40941,43676)].
Definition SH_utf8_ubsan_r0c0_40941_43676_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_40941_43676_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_40941_43676_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_40941_43676_0 (hs_of HT_utf8_ubsan_r0c0_40941_43676) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_40941_43676_0 P_utf8_ubsan_r0c0_40941_43676_0 = COk SH_utf8_ubsan_r0c0_40941_43676_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_40941_43676_0). Qed.
End Cert_utf8_ubsan_r0c0_40941_43676_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_43677_49132.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_43677_49132.

Module Plan_utf8_ubsan_r0c0_43677_49132_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_43677_49132_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@C??g_?AEA?@Y?g`E?WbAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbIC??g_?AEA?@Y?g`E?WbJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[C??g_?AEA?@Y?g`E?Wa|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}MA?C??g_?AEA?@Y?g`E?W?^a}N?bek?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_43677_49132_L.

Module Cert_utf8_ubsan_r0c0_43677_49132_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_43677_49132 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_43677_49132_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_43677_49132 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_43677_49132_0 : class := [(QLook,4,4); (QFlen,43683,49138); (QCfgLen,0,0); (QRoom,43677,49132)].
Definition SH_utf8_ubsan_r0c0_43677_49132_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_43677_49132_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_43677_49132_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_43677_49132_0 (hs_of HT_utf8_ubsan_r0c0_43677_49132) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_43677_49132_0 P_utf8_ubsan_r0c0_43677_49132_0 = COk SH_utf8_ubsan_r0c0_43677_49132_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_43677_49132_0). Qed.
End Cert_utf8_ubsan_r0c0_43677_49132_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_45_60.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_45_60.

Module Plan_utf8_ubsan_r0c0_45_60_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_45_60_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_45_60_L.

Module Cert_utf8_ubsan_r0c0_45_60_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_45_60 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_45_60_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_1.Cert_utf8_ubsan_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_1.HS_utf8_ubsan_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_45_60 : htab := [(40%nat, (HS_utf8_ubsan_shX40_0, SH_utf8_ubsan_shX40_0))].

Definition C_utf8_ubsan_r0c0_45_60_0 : class := [(QLook,4,4); (QFlen,51,66); (QCfgLen,0,0); (QRoom,45,60)].
Definition SH_utf8_ubsan_r0c0_45_60_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_utf8_ubsan_r0c0_45_60_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_45_60_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_45_60_0 (hs_of HT_utf8_ubsan_r0c0_45_60) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_45_60_0 P_utf8_ubsan_r0c0_45_60_0 = COk SH_utf8_ubsan_r0c0_45_60_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_45_60_0). Qed.
End Cert_utf8_ubsan_r0c0_45_60_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_4669_5436.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_4669_5436.

Module Plan_utf8_ubsan_r0c0_4669_5436_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_4669_5436_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`__?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`__?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`__?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_4669_5436_L.

Module Cert_utf8_ubsan_r0c0_4669_5436_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_4669_5436 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_4669_5436_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_4669_5436 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_4669_5436_0 : class := [(QLook,4,4); (QFlen,4675,5442); (QCfgLen,0,0); (QRoom,4669,5436)].
Definition SH_utf8_ubsan_r0c0_4669_5436_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_4669_5436_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_4669_5436_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_4669_5436_0 (hs_of HT_utf8_ubsan_r0c0_4669_5436) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_4669_5436_0 P_utf8_ubsan_r0c0_4669_5436_0 = COk SH_utf8_ubsan_r0c0_4669_5436_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_4669_5436_0). Qed.
End Cert_utf8_ubsan_r0c0_4669_5436_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_49133_52412.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_49133_52412.

Module Plan_utf8_ubsan_r0c0_49133_52412_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_49133_52412_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?bg_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?bg_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?bg_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?aEa}N?`]a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_49133_52412_L.

Module Cert_utf8_ubsan_r0c0_49133_52412_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_49133_52412 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_49133_52412_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_49133_52412 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_49133_52412_0 : class := [(QLook,4,4); (QFlen,49139,52418); (QCfgLen,0,0); (QRoom,49133,52412)].
Definition SH_utf8_ubsan_r0c0_49133_52412_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_49133_52412_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_49133_52412_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_49133_52412_0 (hs_of HT_utf8_ubsan_r0c0_49133_52412) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_49133_52412_0 P_utf8_ubsan_r0c0_49133_52412_0 = COk SH_utf8_ubsan_r0c0_49133_52412_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_49133_52412_0). Qed.
End Cert_utf8_ubsan_r0c0_49133_52412_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_493_572.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_493_572.

Module Plan_utf8_ubsan_r0c0_493_572_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_493_572_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?rcFa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?a?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?a?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_493_572_L.

Module Cert_utf8_ubsan_r0c0_493_572_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_493_572 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_493_572_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX135_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX135.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_493_572 : htab := [(135%nat, (HS_utf8_ubsan_shX135_0, SH_utf8_ubsan_shX135_0))].

Definition C_utf8_ubsan_r0c0_493_572_0 : class := [(QLook,4,4); (QFlen,499,578); (QCfgLen,0,0); (QRoom,493,572)].
Definition SH_utf8_ubsan_r0c0_493_572_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 135).
Definition FUEL_utf8_ubsan_r0c0_493_572_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_493_572_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_493_572_0 (hs_of HT_utf8_ubsan_r0c0_493_572) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_493_572_0 P_utf8_ubsan_r0c0_493_572_0 = COk SH_utf8_ubsan_r0c0_493_572_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_493_572_0). Qed.
End Cert_utf8_ubsan_r0c0_493_572_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_52413_61420.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_52413_61420.

Module Plan_utf8_ubsan_r0c0_52413_61420_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_52413_61420_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@C??g_?AEA?@Y?g`E?WbAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbIC??g_?AEA?@Y?g`E?WbJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[C??g_?AEA?@Y?g`E?Wa|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}MA?C??g_?AEA?@Y?g`E?W?^a}N?b~~?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_52413_61420_L.

Module Cert_utf8_ubsan_r0c0_52413_61420_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_52413_61420 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_52413_61420_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_52413_61420 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_52413_61420_0 : class := [(QLook,4,4); (QFlen,52419,61426); (QCfgLen,0,0); (QRoom,52413,61420)].
Definition SH_utf8_ubsan_r0c0_52413_61420_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_52413_61420_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_52413_61420_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_52413_61420_0 (hs_of HT_utf8_ubsan_r0c0_52413_61420) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_52413_61420_0 P_utf8_ubsan_r0c0_52413_61420_0 = COk SH_utf8_ubsan_r0c0_52413_61420_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_52413_61420_0). Qed.
End Cert_utf8_ubsan_r0c0_52413_61420_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_5437_6540.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_5437_6540.

Module Plan_utf8_ubsan_r0c0_5437_6540_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_5437_6540_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?o_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?o_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?o_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_5437_6540_L.

Module Cert_utf8_ubsan_r0c0_5437_6540_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_5437_6540 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_5437_6540_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_5437_6540 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_5437_6540_0 : class := [(QLook,4,4); (QFlen,5443,6546); (QCfgLen,0,0); (QRoom,5437,6540)].
Definition SH_utf8_ubsan_r0c0_5437_6540_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_5437_6540_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_5437_6540_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_5437_6540_0 (hs_of HT_utf8_ubsan_r0c0_5437_6540) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_5437_6540_0 P_utf8_ubsan_r0c0_5437_6540_0 = COk SH_utf8_ubsan_r0c0_5437_6540_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_5437_6540_0). Qed.
End Cert_utf8_ubsan_r0c0_5437_6540_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_573_668.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_573_668.

Module Plan_utf8_ubsan_r0c0_573_668_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_573_668_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?rcFa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?a?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?a?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_573_668_L.

Module Cert_utf8_ubsan_r0c0_573_668_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_573_668 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_573_668_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX135_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX135.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_573_668 : htab := [(135%nat, (HS_utf8_ubsan_shX135_0, SH_utf8_ubsan_shX135_0))].

Definition C_utf8_ubsan_r0c0_573_668_0 : class := [(QLook,4,4); (QFlen,579,674); (QCfgLen,0,0); (QRoom,573,668)].
Definition SH_utf8_ubsan_r0c0_573_668_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 135).
Definition FUEL_utf8_ubsan_r0c0_573_668_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_573_668_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_573_668_0 (hs_of HT_utf8_ubsan_r0c0_573_668) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_573_668_0 P_utf8_ubsan_r0c0_573_668_0 = COk SH_utf8_ubsan_r0c0_573_668_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_573_668_0). Qed.
End Cert_utf8_ubsan_r0c0_573_668_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_61421_65516.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_61421_65516.

Module Plan_utf8_ubsan_r0c0_61421_65516_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_61421_65516_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?c__?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?c__?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?c__?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?aGa}N?`]a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_61421_65516_L.

Module Cert_utf8_ubsan_r0c0_61421_65516_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_61421_65516 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_61421_65516_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_61421_65516 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_61421_65516_0 : class := [(QLook,4,4); (QFlen,61427,65522); (QCfgLen,0,0); (QRoom,61421,65516)].
Definition SH_utf8_ubsan_r0c0_61421_65516_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_61421_65516_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_61421_65516_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_61421_65516_0 (hs_of HT_utf8_ubsan_r0c0_61421_65516) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_61421_65516_0 P_utf8_ubsan_r0c0_61421_65516_0 = COk SH_utf8_ubsan_r0c0_61421_65516_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_61421_65516_0). Qed.
End Cert_utf8_ubsan_r0c0_61421_65516_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_61_76.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_61_76.

Module Plan_utf8_ubsan_r0c0_61_76_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_61_76_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_61_76_L.

Module Cert_utf8_ubsan_r0c0_61_76_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_61_76 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_61_76_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_1.Cert_utf8_ubsan_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_1.HS_utf8_ubsan_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_61_76 : htab := [(40%nat, (HS_utf8_ubsan_shX40_0, SH_utf8_ubsan_shX40_0))].

Definition C_utf8_ubsan_r0c0_61_76_0 : class := [(QLook,4,4); (QFlen,67,82); (QCfgLen,0,0); (QRoom,61,76)].
Definition SH_utf8_ubsan_r0c0_61_76_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_utf8_ubsan_r0c0_61_76_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_61_76_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_61_76_0 (hs_of HT_utf8_ubsan_r0c0_61_76) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_61_76_0 P_utf8_ubsan_r0c0_61_76_0 = COk SH_utf8_ubsan_r0c0_61_76_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_61_76_0). Qed.
End Cert_utf8_ubsan_r0c0_61_76_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_6541_8172.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_6541_8172.

Module Plan_utf8_ubsan_r0c0_6541_8172_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_6541_8172_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?o_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?o_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?o_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_6541_8172_L.

Module Cert_utf8_ubsan_r0c0_6541_8172_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_6541_8172 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_6541_8172_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_6541_8172 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_6541_8172_0 : class := [(QLook,4,4); (QFlen,6547,8178); (QCfgLen,0,0); (QRoom,6541,8172)].
Definition SH_utf8_ubsan_r0c0_6541_8172_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_6541_8172_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_6541_8172_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_6541_8172_0 (hs_of HT_utf8_ubsan_r0c0_6541_8172) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_6541_8172_0 P_utf8_ubsan_r0c0_6541_8172_0 = COk SH_utf8_ubsan_r0c0_6541_8172_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_6541_8172_0). Qed.
End Cert_utf8_ubsan_r0c0_6541_8172_0.
