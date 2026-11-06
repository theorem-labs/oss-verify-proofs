(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require AxSymExec3 AsanPlan PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require AsanNodesIO AsanMainLib ImgParams MainDefs Img_src13 Cert_common ITab_src13 Segs_src13 HS_src13_pfx1 Sh_src13_4 PlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
(* [comment removed for export] *)
Module Plan_src13_r0c0_317_396.   (* [comment removed for export] *)
End Plan_src13_r0c0_317_396.

Module Plan_src13_r0c0_317_396_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_317_396_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?rcGa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?b?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?b?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_317_396_L.

Module Cert_src13_r0c0_317_396_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_317_396 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_317_396_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX136_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX136.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_317_396 : htab := [(136%nat, (HS_src13_shX136_0, SH_src13_shX136_0))].

Definition C_src13_r0c0_317_396_0 : class := [(QLook,4,4); (QFlen,323,402); (QCfgLen,0,0); (QRoom,317,396)].
Definition SH_src13_r0c0_317_396_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 136).
Definition FUEL_src13_r0c0_317_396_0 : nat := 3000.
Lemma cert_src13_r0c0_317_396_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_317_396_0 (hs_of HT_src13_r0c0_317_396) HS_src13_pfx1_0 C_src13_r0c0_317_396_0 P_src13_r0c0_317_396_0 = COk SH_src13_r0c0_317_396_0.
Proof. cert_vm (COk SH_src13_r0c0_317_396_0). Qed.
End Cert_src13_r0c0_317_396_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_3261_4076.   (* [comment removed for export] *)
End Plan_src13_r0c0_3261_4076.

Module Plan_src13_r0c0_3261_4076_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_3261_4076_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?g_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?g_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?g_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_3261_4076_L.

Module Cert_src13_r0c0_3261_4076_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_3261_4076 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_3261_4076_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_3261_4076 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_3261_4076_0 : class := [(QLook,4,4); (QFlen,3267,4082); (QCfgLen,0,0); (QRoom,3261,4076)].
Definition SH_src13_r0c0_3261_4076_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_3261_4076_0 : nat := 3000.
Lemma cert_src13_r0c0_3261_4076_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_3261_4076_0 (hs_of HT_src13_r0c0_3261_4076) HS_src13_pfx1_0 C_src13_r0c0_3261_4076_0 P_src13_r0c0_3261_4076_0 = COk SH_src13_r0c0_3261_4076_0.
Proof. cert_vm (COk SH_src13_r0c0_3261_4076_0). Qed.
End Cert_src13_r0c0_3261_4076_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_32749_36844.   (* [comment removed for export] *)
End Plan_src13_r0c0_32749_36844.

Module Plan_src13_r0c0_32749_36844_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_32749_36844_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?ag_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?ag_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?ag_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?af~?a}N?ahc?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_32749_36844_L.

Module Cert_src13_r0c0_32749_36844_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_32749_36844 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_32749_36844_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_32749_36844 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_32749_36844_0 : class := [(QLook,4,4); (QFlen,32755,36850); (QCfgLen,0,0); (QRoom,32749,36844)].
Definition SH_src13_r0c0_32749_36844_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_32749_36844_0 : nat := 3000.
Lemma cert_src13_r0c0_32749_36844_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_32749_36844_0 (hs_of HT_src13_r0c0_32749_36844) HS_src13_pfx1_0 C_src13_r0c0_32749_36844_0 P_src13_r0c0_32749_36844_0 = COk SH_src13_r0c0_32749_36844_0.
Proof. cert_vm (COk SH_src13_r0c0_32749_36844_0). Qed.
End Cert_src13_r0c0_32749_36844_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_36845_37436.   (* [comment removed for export] *)
End Plan_src13_r0c0_36845_37436.

Module Plan_src13_r0c0_36845_37436_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_36845_37436_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?ao_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?ao_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?ao_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?aAa}N?`]a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_36845_37436_L.

Module Cert_src13_r0c0_36845_37436_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_36845_37436 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_36845_37436_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_36845_37436 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_36845_37436_0 : class := [(QLook,4,4); (QFlen,36851,37442); (QCfgLen,0,0); (QRoom,36845,37436)].
Definition SH_src13_r0c0_36845_37436_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_36845_37436_0 : nat := 3000.
Lemma cert_src13_r0c0_36845_37436_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_36845_37436_0 (hs_of HT_src13_r0c0_36845_37436) HS_src13_pfx1_0 C_src13_r0c0_36845_37436_0 P_src13_r0c0_36845_37436_0 = COk SH_src13_r0c0_36845_37436_0.
Proof. cert_vm (COk SH_src13_r0c0_36845_37436_0). Qed.
End Cert_src13_r0c0_36845_37436_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_37437_40940.   (* [comment removed for export] *)
End Plan_src13_r0c0_37437_40940.

Module Plan_src13_r0c0_37437_40940_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_37437_40940_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?ao_?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?ao_?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?ao_?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?an~?a}N?ati?a}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_37437_40940_L.

Module Cert_src13_r0c0_37437_40940_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_37437_40940 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_37437_40940_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_37437_40940 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_37437_40940_0 : class := [(QLook,4,4); (QFlen,37443,40946); (QCfgLen,0,0); (QRoom,37437,40940)].
Definition SH_src13_r0c0_37437_40940_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_37437_40940_0 : nat := 3000.
Lemma cert_src13_r0c0_37437_40940_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_37437_40940_0 (hs_of HT_src13_r0c0_37437_40940) HS_src13_pfx1_0 C_src13_r0c0_37437_40940_0 P_src13_r0c0_37437_40940_0 = COk SH_src13_r0c0_37437_40940_0.
Proof. cert_vm (COk SH_src13_r0c0_37437_40940_0). Qed.
End Cert_src13_r0c0_37437_40940_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_397_492.   (* [comment removed for export] *)
End Plan_src13_r0c0_397_492.

Module Plan_src13_r0c0_397_492_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_397_492_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?rcGa|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?b?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?b?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_397_492_L.

Module Cert_src13_r0c0_397_492_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_397_492 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_397_492_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX136_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX136.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_397_492 : htab := [(136%nat, (HS_src13_shX136_0, SH_src13_shX136_0))].

Definition C_src13_r0c0_397_492_0 : class := [(QLook,4,4); (QFlen,403,498); (QCfgLen,0,0); (QRoom,397,492)].
Definition SH_src13_r0c0_397_492_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 136).
Definition FUEL_src13_r0c0_397_492_0 : nat := 3000.
Lemma cert_src13_r0c0_397_492_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_397_492_0 (hs_of HT_src13_r0c0_397_492) HS_src13_pfx1_0 C_src13_r0c0_397_492_0 P_src13_r0c0_397_492_0 = COk SH_src13_r0c0_397_492_0.
Proof. cert_vm (COk SH_src13_r0c0_397_492_0). Qed.
End Cert_src13_r0c0_397_492_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_4077_4668.   (* [comment removed for export] *)
End Plan_src13_r0c0_4077_4668.

Module Plan_src13_r0c0_4077_4668_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_4077_4668_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?`__?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?`__?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?`__?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_4077_4668_L.

Module Cert_src13_r0c0_4077_4668_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_4077_4668 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_4077_4668_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_4077_4668 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_4077_4668_0 : class := [(QLook,4,4); (QFlen,4083,4674); (QCfgLen,0,0); (QRoom,4077,4668)].
Definition SH_src13_r0c0_4077_4668_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_4077_4668_0 : nat := 3000.
Lemma cert_src13_r0c0_4077_4668_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_4077_4668_0 (hs_of HT_src13_r0c0_4077_4668) HS_src13_pfx1_0 C_src13_r0c0_4077_4668_0 P_src13_r0c0_4077_4668_0 = COk SH_src13_r0c0_4077_4668_0.
Proof. cert_vm (COk SH_src13_r0c0_4077_4668_0). Qed.
End Cert_src13_r0c0_4077_4668_0.
