(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require AxSymExec3 AsanPlan PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require AsanNodesIO AsanMainLib ImgParams MainDefs Img_utf8_ubsan Cert_common ITab_utf8_ubsan Segs_utf8_ubsan HS_utf8_ubsan_pfx1 Sh_utf8_ubsan_4 Sh_utf8_ubsan_1 PlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_24557_26188.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_24557_26188.

Module Plan_utf8_ubsan_r0c0_24557_26188_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_24557_26188_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`w_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`w_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`w_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_24557_26188_L.

Module Cert_utf8_ubsan_r0c0_24557_26188_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_24557_26188 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_24557_26188_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_24557_26188 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_24557_26188_0 : class := [(QLook,4,4); (QFlen,24563,26194); (QCfgLen,0,0); (QRoom,24557,26188)].
Definition SH_utf8_ubsan_r0c0_24557_26188_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_24557_26188_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_24557_26188_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_24557_26188_0 (hs_of HT_utf8_ubsan_r0c0_24557_26188) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_24557_26188_0 P_utf8_ubsan_r0c0_24557_26188_0 = COk SH_utf8_ubsan_r0c0_24557_26188_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_24557_26188_0). Qed.
End Cert_utf8_ubsan_r0c0_24557_26188_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_26189_28652.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_26189_28652.

Module Plan_utf8_ubsan_r0c0_26189_28652_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_26189_28652_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`w_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`w_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`w_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?`v~?a}N?`~~?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_26189_28652_L.

Module Cert_utf8_ubsan_r0c0_26189_28652_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_26189_28652 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_26189_28652_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_26189_28652 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_26189_28652_0 : class := [(QLook,4,4); (QFlen,26195,28658); (QCfgLen,0,0); (QRoom,26189,28652)].
Definition SH_utf8_ubsan_r0c0_26189_28652_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_26189_28652_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_26189_28652_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_26189_28652_0 (hs_of HT_utf8_ubsan_r0c0_26189_28652) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_26189_28652_0 P_utf8_ubsan_r0c0_26189_28652_0 = COk SH_utf8_ubsan_r0c0_26189_28652_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_26189_28652_0). Qed.
End Cert_utf8_ubsan_r0c0_26189_28652_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_2717_3260.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_2717_3260.

Module Plan_utf8_ubsan_r0c0_2717_3260_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_2717_3260_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?g_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?g_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?g_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_2717_3260_L.

Module Cert_utf8_ubsan_r0c0_2717_3260_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_2717_3260 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_2717_3260_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_2717_3260 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_2717_3260_0 : class := [(QLook,4,4); (QFlen,2723,3266); (QCfgLen,0,0); (QRoom,2717,3260)].
Definition SH_utf8_ubsan_r0c0_2717_3260_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_2717_3260_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_2717_3260_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_2717_3260_0 (hs_of HT_utf8_ubsan_r0c0_2717_3260) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_2717_3260_0 P_utf8_ubsan_r0c0_2717_3260_0 = COk SH_utf8_ubsan_r0c0_2717_3260_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_2717_3260_0). Qed.
End Cert_utf8_ubsan_r0c0_2717_3260_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_285_316.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_285_316.

Module Plan_utf8_ubsan_r0c0_285_316_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_285_316_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?rcHa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?b?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?b?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_285_316_L.

Module Cert_utf8_ubsan_r0c0_285_316_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_285_316 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_285_316_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX137_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX137.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_285_316 : htab := [(137%nat, (HS_utf8_ubsan_shX137_0, SH_utf8_ubsan_shX137_0))].

Definition C_utf8_ubsan_r0c0_285_316_0 : class := [(QLook,4,4); (QFlen,291,322); (QCfgLen,0,0); (QRoom,285,316)].
Definition SH_utf8_ubsan_r0c0_285_316_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 137).
Definition FUEL_utf8_ubsan_r0c0_285_316_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_285_316_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_285_316_0 (hs_of HT_utf8_ubsan_r0c0_285_316) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_285_316_0 P_utf8_ubsan_r0c0_285_316_0 = COk SH_utf8_ubsan_r0c0_285_316_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_285_316_0). Qed.
End Cert_utf8_ubsan_r0c0_285_316_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_28653_32748.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_28653_32748.

Module Plan_utf8_ubsan_r0c0_28653_32748_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_28653_32748_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?a__?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?a__?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?a__?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?a?a}N?`]a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_28653_32748_L.

Module Cert_utf8_ubsan_r0c0_28653_32748_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_28653_32748 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_28653_32748_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_28653_32748 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_28653_32748_0 : class := [(QLook,4,4); (QFlen,28659,32754); (QCfgLen,0,0); (QRoom,28653,32748)].
Definition SH_utf8_ubsan_r0c0_28653_32748_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_28653_32748_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_28653_32748_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_28653_32748_0 (hs_of HT_utf8_ubsan_r0c0_28653_32748) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_28653_32748_0 P_utf8_ubsan_r0c0_28653_32748_0 = COk SH_utf8_ubsan_r0c0_28653_32748_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_28653_32748_0). Qed.
End Cert_utf8_ubsan_r0c0_28653_32748_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_29_44.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_29_44.

Module Plan_utf8_ubsan_r0c0_29_44_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_29_44_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_29_44_L.

Module Cert_utf8_ubsan_r0c0_29_44_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_29_44 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_29_44_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_1.Cert_utf8_ubsan_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_1.HS_utf8_ubsan_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_29_44 : htab := [(40%nat, (HS_utf8_ubsan_shX40_0, SH_utf8_ubsan_shX40_0))].

Definition C_utf8_ubsan_r0c0_29_44_0 : class := [(QLook,4,4); (QFlen,35,50); (QCfgLen,0,0); (QRoom,29,44)].
Definition SH_utf8_ubsan_r0c0_29_44_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_utf8_ubsan_r0c0_29_44_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_29_44_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_29_44_0 (hs_of HT_utf8_ubsan_r0c0_29_44) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_29_44_0 P_utf8_ubsan_r0c0_29_44_0 = COk SH_utf8_ubsan_r0c0_29_44_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_29_44_0). Qed.
End Cert_utf8_ubsan_r0c0_29_44_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_317_396.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_317_396.

Module Plan_utf8_ubsan_r0c0_317_396_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_317_396_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?rcGa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?b?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?b?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_317_396_L.

Module Cert_utf8_ubsan_r0c0_317_396_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_317_396 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_317_396_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX136_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX136.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_317_396 : htab := [(136%nat, (HS_utf8_ubsan_shX136_0, SH_utf8_ubsan_shX136_0))].

Definition C_utf8_ubsan_r0c0_317_396_0 : class := [(QLook,4,4); (QFlen,323,402); (QCfgLen,0,0); (QRoom,317,396)].
Definition SH_utf8_ubsan_r0c0_317_396_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 136).
Definition FUEL_utf8_ubsan_r0c0_317_396_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_317_396_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_317_396_0 (hs_of HT_utf8_ubsan_r0c0_317_396) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_317_396_0 P_utf8_ubsan_r0c0_317_396_0 = COk SH_utf8_ubsan_r0c0_317_396_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_317_396_0). Qed.
End Cert_utf8_ubsan_r0c0_317_396_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_3261_4076.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_3261_4076.

Module Plan_utf8_ubsan_r0c0_3261_4076_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_3261_4076_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?g_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?g_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?g_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_3261_4076_L.

Module Cert_utf8_ubsan_r0c0_3261_4076_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_3261_4076 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_3261_4076_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_3261_4076 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_3261_4076_0 : class := [(QLook,4,4); (QFlen,3267,4082); (QCfgLen,0,0); (QRoom,3261,4076)].
Definition SH_utf8_ubsan_r0c0_3261_4076_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_3261_4076_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_3261_4076_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_3261_4076_0 (hs_of HT_utf8_ubsan_r0c0_3261_4076) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_3261_4076_0 P_utf8_ubsan_r0c0_3261_4076_0 = COk SH_utf8_ubsan_r0c0_3261_4076_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_3261_4076_0). Qed.
End Cert_utf8_ubsan_r0c0_3261_4076_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_32749_36844.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_32749_36844.

Module Plan_utf8_ubsan_r0c0_32749_36844_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_32749_36844_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?ag_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?ag_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?ag_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?af~?a}N?ahc?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_32749_36844_L.

Module Cert_utf8_ubsan_r0c0_32749_36844_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_32749_36844 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_32749_36844_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_32749_36844 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_32749_36844_0 : class := [(QLook,4,4); (QFlen,32755,36850); (QCfgLen,0,0); (QRoom,32749,36844)].
Definition SH_utf8_ubsan_r0c0_32749_36844_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_32749_36844_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_32749_36844_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_32749_36844_0 (hs_of HT_utf8_ubsan_r0c0_32749_36844) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_32749_36844_0 P_utf8_ubsan_r0c0_32749_36844_0 = COk SH_utf8_ubsan_r0c0_32749_36844_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_32749_36844_0). Qed.
End Cert_utf8_ubsan_r0c0_32749_36844_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_36845_37436.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_36845_37436.

Module Plan_utf8_ubsan_r0c0_36845_37436_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_36845_37436_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?ao_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?ao_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?ao_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?aAa}N?`]a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_36845_37436_L.

Module Cert_utf8_ubsan_r0c0_36845_37436_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_36845_37436 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_36845_37436_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_36845_37436 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_36845_37436_0 : class := [(QLook,4,4); (QFlen,36851,37442); (QCfgLen,0,0); (QRoom,36845,37436)].
Definition SH_utf8_ubsan_r0c0_36845_37436_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_36845_37436_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_36845_37436_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_36845_37436_0 (hs_of HT_utf8_ubsan_r0c0_36845_37436) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_36845_37436_0 P_utf8_ubsan_r0c0_36845_37436_0 = COk SH_utf8_ubsan_r0c0_36845_37436_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_36845_37436_0). Qed.
End Cert_utf8_ubsan_r0c0_36845_37436_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_37437_40940.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_37437_40940.

Module Plan_utf8_ubsan_r0c0_37437_40940_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_37437_40940_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~GTS@?C??SB???O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB??@nwr??@nwyOmJTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?ao_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?ao_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`~w_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C??N??@mxk?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?ao_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?an~?a}N?ati?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_37437_40940_L.

Module Cert_utf8_ubsan_r0c0_37437_40940_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_37437_40940 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_37437_40940_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_37437_40940 : htab := [(132%nat, (HS_utf8_ubsan_shX132_0, SH_utf8_ubsan_shX132_0))].

Definition C_utf8_ubsan_r0c0_37437_40940_0 : class := [(QLook,4,4); (QFlen,37443,40946); (QCfgLen,0,0); (QRoom,37437,40940)].
Definition SH_utf8_ubsan_r0c0_37437_40940_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_utf8_ubsan_r0c0_37437_40940_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_37437_40940_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_37437_40940_0 (hs_of HT_utf8_ubsan_r0c0_37437_40940) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_37437_40940_0 P_utf8_ubsan_r0c0_37437_40940_0 = COk SH_utf8_ubsan_r0c0_37437_40940_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_37437_40940_0). Qed.
End Cert_utf8_ubsan_r0c0_37437_40940_0.

(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0c0_397_492.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_397_492.

Module Plan_utf8_ubsan_r0c0_397_492_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0c0_397_492_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~GTS@?C??SB??@`oe~G?@`oe~G??SB??@nwr??@nwyOmLPa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`~w_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`os_WU????SB??@`n{dGTT@?C?@mxk?rcGa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?b?a}F?abng?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?b?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0c0_397_492_L.

Module Cert_utf8_ubsan_r0c0_397_492_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0c0_397_492 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx1 Plan_utf8_ubsan_r0c0_397_492_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.Cert_utf8_ubsan_shX136_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_4.HS_utf8_ubsan_shX136.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0c0_397_492 : htab := [(136%nat, (HS_utf8_ubsan_shX136_0, SH_utf8_ubsan_shX136_0))].

Definition C_utf8_ubsan_r0c0_397_492_0 : class := [(QLook,4,4); (QFlen,403,498); (QCfgLen,0,0); (QRoom,397,492)].
Definition SH_utf8_ubsan_r0c0_397_492_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 136).
Definition FUEL_utf8_ubsan_r0c0_397_492_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0c0_397_492_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0c0_397_492_0 (hs_of HT_utf8_ubsan_r0c0_397_492) HS_utf8_ubsan_pfx1_0 C_utf8_ubsan_r0c0_397_492_0 P_utf8_ubsan_r0c0_397_492_0 = COk SH_utf8_ubsan_r0c0_397_492_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0c0_397_492_0). Qed.
End Cert_utf8_ubsan_r0c0_397_492_0.
