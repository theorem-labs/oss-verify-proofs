(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require AxSymExec3 AsanPlan PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require AsanNodesIO AsanMainLib ImgParams MainDefs Img_src13 Cert_common ITab_src13 Segs_src13 HS_src13_pfx1 Sh_src13_4 Sh_src13_1 HS_src13_pfx3 Sh_src13_2 Sh_src13_3 PlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
(* [comment removed for export] *)
Module Plan_src13_r0c0_9341_10908.   (* [comment removed for export] *)
End Plan_src13_r0c0_9341_10908.

Module Plan_src13_r0c0_9341_10908_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_9341_10908_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTa]C??g_?@`\a^?g_?b?C??g_?@Zb@?a__?bAC??g_?@LbB?cg_?bCC??g_?@RbD?o_?bE@XbFC??g_?@`\bG?g_?bHC??g_?@ZbI?a__?bJC??g_?@LbK?cg_?bL@VbM@WbN?c__?bO?`|g_?bP?f~~z~o___?bQ?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C??N??@mye?rcCa|W]a|W@`\a|X@La|Y@Ra|Z@Za|[?a__?a|\@Va|]@Wa|^@Xa}?@Ya}@@Ua}A@Ta}B@Sa}C@fPa}D@fQa}E@fRa}F@Ya}GA?A?C??g_?@ZC??`?@[?`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@ZC??`?@[?`?a}Q@f[a}R@f\a}S@f]a}T@f^"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_9341_10908_L.

Module Cert_src13_r0c0_9341_10908_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_9341_10908 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_9341_10908_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.Cert_src13_shX132_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_4.HS_src13_shX132.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_9341_10908 : htab := [(132%nat, (HS_src13_shX132_0, SH_src13_shX132_0))].

Definition C_src13_r0c0_9341_10908_0 : class := [(QLook,4,4); (QFlen,9347,10914); (QCfgLen,0,0); (QRoom,9341,10908)].
Definition SH_src13_r0c0_9341_10908_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 132).
Definition FUEL_src13_r0c0_9341_10908_0 : nat := 3000.
Lemma cert_src13_r0c0_9341_10908_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_9341_10908_0 (hs_of HT_src13_r0c0_9341_10908) HS_src13_pfx1_0 C_src13_r0c0_9341_10908_0 P_src13_r0c0_9341_10908_0 = COk SH_src13_r0c0_9341_10908_0.
Proof. cert_vm (COk SH_src13_r0c0_9341_10908_0). Qed.
End Cert_src13_r0c0_9341_10908_0.

(* [comment removed for export] *)
Module Plan_src13_r0c0_93_108.   (* [comment removed for export] *)
End Plan_src13_r0c0_93_108.

Module Plan_src13_r0c0_93_108_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c0_93_108_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pa\C??g_?@Za]?g_?a^C??g_?@Lb??cg_?b@C??g_?@RbA?o_?bB@XbCC??g_?@ZbD?g_?bEC??g_?@LbF?cg_?bG@VbH@WbI?c__?bJ?`|g_?bK?f~~z~o___?bL?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@`lji?TT@?C?@mye?r`Ga|W[a|W@Za|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@Ya|^@Ua}?@Ta}@@Sa}A@fKa}B@fLa}C@fMa}D@Ya}EA?A?C??g_?@ZC??`?@[?c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@ZC??`?@[?c?a}O@fVa}P@fWa}Q@fXa}R@fY"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c0_93_108_L.

Module Cert_src13_r0c0_93_108_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c0_93_108 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx1 Plan_src13_r0c0_93_108_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX40_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX40.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c0_93_108 : htab := [(40%nat, (HS_src13_shX40_0, SH_src13_shX40_0))].

Definition C_src13_r0c0_93_108_0 : class := [(QLook,4,4); (QFlen,99,114); (QCfgLen,0,0); (QRoom,93,108)].
Definition SH_src13_r0c0_93_108_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SHole 40).
Definition FUEL_src13_r0c0_93_108_0 : nat := 3000.
Lemma cert_src13_r0c0_93_108_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c0_93_108_0 (hs_of HT_src13_r0c0_93_108) HS_src13_pfx1_0 C_src13_r0c0_93_108_0 P_src13_r0c0_93_108_0 = COk SH_src13_r0c0_93_108_0.
Proof. cert_vm (COk SH_src13_r0c0_93_108_0). Qed.
End Cert_src13_r0c0_93_108_0.

(* [comment removed for export] *)
Module Plan_src13_r0c1_1005_1148.   (* [comment removed for export] *)
End Plan_src13_r0c1_1005_1148.

Module Plan_src13_r0c1_1005_1148_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c1_1005_1148_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTbAC??g_?@a@bB?g_?bCC??g_?@^bD?g_?bEC??g_?@LbF?cg_?bGC??g_?@RbH?o_?bI@XbJC??g_?@a@bK?g_?bLC??g_?@^bM?g_?bNC??g_?@LbO?cg_?bP@VbQ@WbR?c__?bS?`|g_?bT?f~~z~o___?bU?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji?TT@?C??N??@mye?ra]a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@fTa}D@fUa}E@fVa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@g?a}R@g@a}S@gAa}T@gB?@nqhW?@nqo?mKTgCC??g_?@a@gD?g_?gEC??g_?@^gF?g_?gGC??g_?@LgH?cg_?gIC??g_?@RgJ?o_?gK@XgLC??g_?@a@gM?g_?gNC??g_?@^gO?g_?gPC??g_?@LgQ?cg_?gR@VgS@WgT?c__?gU?`|g_?gV?f~~z~o___?gW?c_o___?@?@myn?m`?[hE?MhF?n?hG?~~~~~~~~|{__?hH@]hIA?A?C??g_?@^C??`?@`??`?hJ??hK@]hL?k?hM?~~~~~~~~~~~z]hN?m?hO?g?hP?`UhQA?A?C??g_?@^C??`?@`??`?hR??hS?`who?hTAHF?GC@?EhU??hV?~~~~~~~~~~~~[hW??hX??hY??hZ??h[?~~~~~~~~}___?h\@hBh]@hCh^@hDi?@Ti@@X@?@mydG@AHF?GC@?EA?@`lji?TT@?C??N??@mye?ra^a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@nBa}D@nCa}E@nDa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@nMa}R@nNa}S@nOa}T@nP?@nqhW?@nqo?mKTnQC??g_?@a@nR?g_?nSC??g_?@^nT?g_?nUC??g_?@LnV?cg_?nWC??g_?@RnX?o_?nY@XnZC??g_?@a@n[?g_?n\C??g_?@^n]?g_?n^C??g_?@Lo??cg_?o@@VoA@WoB?c__?oC?`|g_?oD?f~~z~o___?oE?c_o___?@?@myn?m`@[oS?MoT?n?oU?~~~~~~~~|{__?oV@]oWA?A?C??g_?@^C??`?@`??`?oX??oY@]oZ?k?o[?~~~~~~~~~~~z]o\?m?o]?g?o^?`Up?A?A?C??g_?@^C??`?@`??`?p@??pA?`who?pBA?AHF?GC@?E?@pC??pD?~~~~~~~~~~~~[pE??pF??pG??pH??pI?~~~~~~~~}___?pJ@oPpK@oQpL@oRpM@TpN@X@?@mydG@AHF?GC@?EC?@`lji?TT@?C??N??@mye?rb?a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@uPa}D@uQa}E@uRa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@u[a}R@u\a}S@u]a}T@u^?@nqhW?@nqo?mKTv?C??g_?@a@v@?g_?vAC??g_?@^vB?g_?vCC??g_?@LvD?cg_?vEC??g_?@RvF?o_?vG@XvHC??g_?@a@vI?g_?vJC??g_?@^vK?g_?vLC??g_?@LvM?cg_?vN@VvO@WvP?c__?vQ?`|g_?vR?f~~z~o___?vS?c_o___?@?@myn?m`A[wA?MwB?n?wC?~~~~~~~~|{__?wD@]wEA?A?C??g_?@^C??`?@`??`?wF??wG@]wH?k?wI?~~~~~~~~~~~z]wJ?m?wK?g?wL?`UwMA?A?C??g_?@^C??`?@`??`?wN??wO?`who?wP?AwQ??wR?~~~~~~~~~~~~[wS??wT??wU??wV??wW?~~~~~~~~}___?wX@v^wY@w?wZ@w@w[@Tw\@X@?@`lji?TT@?C??N??@mye?rb@a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@|^a}D@}?a}E@}@a}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@}Ia}R@}Ja}S@}Ka}T@}L"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c1_1005_1148_L.

Module Cert_src13_r0c1_1005_1148_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c1_1005_1148 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0c1_1005_1148_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX94_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX95_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX96_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX97_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX94 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX95 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX96 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX97.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c1_1005_1148 : htab := [(94%nat, (HS_src13_shX94_0, SH_src13_shX94_0)); (95%nat, (HS_src13_shX95_0, SH_src13_shX95_0)); (96%nat, (HS_src13_shX96_0, SH_src13_shX96_0)); (97%nat, (HS_src13_shX97_0, SH_src13_shX97_0))].

Definition C_src13_r0c1_1005_1148_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,1005,1148)].
Definition SH_src13_r0c1_1005_1148_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 94) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 95) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 96) (SHole 97)))).
Definition FUEL_src13_r0c1_1005_1148_0 : nat := 3000.
Lemma cert_src13_r0c1_1005_1148_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c1_1005_1148_0 (hs_of HT_src13_r0c1_1005_1148) HS_src13_pfx3_0 C_src13_r0c1_1005_1148_0 P_src13_r0c1_1005_1148_0 = COk SH_src13_r0c1_1005_1148_0.
Proof. cert_vm (COk SH_src13_r0c1_1005_1148_0). Qed.
End Cert_src13_r0c1_1005_1148_0.

(* [comment removed for export] *)
Module Plan_src13_r0c1_10909_12268.   (* [comment removed for export] *)
End Plan_src13_r0c1_10909_12268.

Module Plan_src13_r0c1_10909_12268_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c1_10909_12268_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTbAC??g_?@a@bB?g_?bCC??g_?@^bD?w_?bEC??g_?@LbF?cg_?bGC??g_?@RbH?o_?bI@XbJC??g_?@a@bK?g_?bLC??g_?@^bM?w_?bNC??g_?@LbO?cg_?bP@VbQ@WbR?c__?bS?`|g_?bT?f~~z~o___?bU?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji?TT@?C??N??@mye?ra]a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?w_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fUa}E@fVa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?v~?a}N?xq?a}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@g?a}R@g@a}S@gAa}T@gB?@nqhW?@nqo?mKTgCC??g_?@a@gD?g_?gEC??g_?@^gF?w_?gGC??g_?@LgH?cg_?gIC??g_?@RgJ?o_?gK@XgLC??g_?@a@gM?g_?gNC??g_?@^gO?w_?gPC??g_?@LgQ?cg_?gR@VgS@WgT?c__?gU?`|g_?gV?f~~z~o___?gW?c_o___?@?@myn?m`?[hE?MhF?n?hG?~~~~~~~~|{__?hH@]hIA?A?C??g_?@^C??`?@`??`?hJ??hK@]hL?k?hM?~~~~~~~~~~~z]hN?m?hO?g?hP?`UhQA?A?C??g_?@^C??`?@`??`?hR??hS?`who?hTAHF?GC@?EhU??hV?~~~~~~~~~~~~[hW??hX??hY??hZ??h[?~~~~~~~~}___?h\@hBh]@hCh^@hDi?@Ti@@X@?@mydG@AHF?GC@?EA?@`lji?TT@?C??N??@mye?ra^a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?w_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@nCa}E@nDa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?v~?a}N?xq?a}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@nMa}R@nNa}S@nOa}T@nP?@nqhW?@nqo?mKTnQC??g_?@a@nR?g_?nSC??g_?@^nT?w_?nUC??g_?@LnV?cg_?nWC??g_?@RnX?o_?nY@XnZC??g_?@a@n[?g_?n\C??g_?@^n]?w_?n^C??g_?@Lo??cg_?o@@VoA@WoB?c__?oC?`|g_?oD?f~~z~o___?oE?c_o___?@?@myn?m`@[oS?MoT?n?oU?~~~~~~~~|{__?oV@]oWA?A?C??g_?@^C??`?@`??`?oX??oY@]oZ?k?o[?~~~~~~~~~~~z]o\?m?o]?g?o^?`Up?A?A?C??g_?@^C??`?@`??`?p@??pA?`who?pBA?AHF?GC@?E?@pC??pD?~~~~~~~~~~~~[pE??pF??pG??pH??pI?~~~~~~~~}___?pJ@oPpK@oQpL@oRpM@TpN@X@?@mydG@AHF?GC@?EC?@`lji?TT@?C??N??@mye?rb?a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?w_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@uQa}E@uRa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?v~?a}N?xq?a}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@u[a}R@u\a}S@u]a}T@u^?@nqhW?@nqo?mKTv?C??g_?@a@v@?g_?vAC??g_?@^vB?w_?vCC??g_?@LvD?cg_?vEC??g_?@RvF?o_?vG@XvHC??g_?@a@vI?g_?vJC??g_?@^vK?w_?vLC??g_?@LvM?cg_?vN@VvO@WvP?c__?vQ?`|g_?vR?f~~z~o___?vS?c_o___?@?@myn?m`A[wA?MwB?n?wC?~~~~~~~~|{__?wD@]wEA?A?C??g_?@^C??`?@`??`?wF??wG@]wH?k?wI?~~~~~~~~~~~z]wJ?m?wK?g?wL?`UwMA?A?C??g_?@^C??`?@`??`?wN??wO?`who?wP?AwQ??wR?~~~~~~~~~~~~[wS??wT??wU??wV??wW?~~~~~~~~}___?wX@v^wY@w?wZ@w@w[@Tw\@X@?@`lji?TT@?C??N??@mye?rb@a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?w_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@}?a}E@}@a}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M?v~?a}N?xq?a}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@}Ia}R@}Ja}S@}Ka}T@}L"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c1_10909_12268_L.

Module Cert_src13_r0c1_10909_12268_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c1_10909_12268 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0c1_10909_12268_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX94_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX95_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX96_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX97_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX94 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX95 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX96 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX97.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c1_10909_12268 : htab := [(94%nat, (HS_src13_shX94_0, SH_src13_shX94_0)); (95%nat, (HS_src13_shX95_0, SH_src13_shX95_0)); (96%nat, (HS_src13_shX96_0, SH_src13_shX96_0)); (97%nat, (HS_src13_shX97_0, SH_src13_shX97_0))].

Definition C_src13_r0c1_10909_12268_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,10909,12268)].
Definition SH_src13_r0c1_10909_12268_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 94) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 95) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 96) (SHole 97)))).
Definition FUEL_src13_r0c1_10909_12268_0 : nat := 3000.
Lemma cert_src13_r0c1_10909_12268_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c1_10909_12268_0 (hs_of HT_src13_r0c1_10909_12268) HS_src13_pfx3_0 C_src13_r0c1_10909_12268_0 P_src13_r0c1_10909_12268_0 = COk SH_src13_r0c1_10909_12268_0.
Proof. cert_vm (COk SH_src13_r0c1_10909_12268_0). Qed.
End Cert_src13_r0c1_10909_12268_0.

(* [comment removed for export] *)
Module Plan_src13_r0c1_109_124.   (* [comment removed for export] *)
End Plan_src13_r0c1_109_124.

Module Plan_src13_r0c1_109_124_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c1_109_124_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?m@Pb@C??g_?@^bA?g_?bBC??g_?@LbC?cg_?bDC??g_?@RbE?o_?bF@XbGC??g_?@^bH?g_?bIC??g_?@LbJ?cg_?bK@VbL@WbM?c__?bN?`|g_?bO?f~~z~o___?bP?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji?TT@?C?@mye?rbPa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@fOa}B@fPa}C@fQa}D@]a}EA?A?C??g_?@^C??`?@`??b?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??b?a}O@fZa}P@f[a}Q@f\a}R@f]?@nqhW?@nqo?m@Pf^C??g_?@^g??g_?g@C??g_?@LgA?cg_?gBC??g_?@RgC?o_?gD@XgEC??g_?@^gF?g_?gGC??g_?@LgH?cg_?gI@VgJ@WgK?c__?gL?`|g_?gM?f~~z~o___?gN?c_o___?@?@myn?m`?[g\?Mg]?n?g^?~~~~~~~~|{__?h?@]h@A?A?C??g_?@^C??`?@`??b?hA??hB@]hC?k?hD?~~~~~~~~~~~z]hE?m?hF?g?hG?`UhHA?A?C??g_?@^C??`?@`??b?hI??hJ?`who?hKAHF?GC@?EhL??hM?~~~~~~~~~~~~[hN??hO??hP??hQ??hR?~~~~~~~~}___?hS@gYhT@gZhU@g[hV@ThW@X@?@mydG@AHF?GC@?EA?@`lji?TT@?C?@mye?rbRa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@mYa}B@mZa}C@m[a}D@]a}EA?A?C??g_?@^C??`?@`??b?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??b?a}O@nDa}P@nEa}Q@nFa}R@nG?@nqhW?@nqo?m@PnHC??g_?@^nI?g_?nJC??g_?@LnK?cg_?nLC??g_?@RnM?o_?nN@XnOC??g_?@^nP?g_?nQC??g_?@LnR?cg_?nS@VnT@WnU?c__?nV?`|g_?nW?f~~z~o___?nX?c_o___?@?@myn?m`@[oF?MoG?n?oH?~~~~~~~~|{__?oI@]oJA?A?C??g_?@^C??`?@`??b?oK??oL@]oM?k?oN?~~~~~~~~~~~z]oO?m?oP?g?oQ?`UoRA?A?C??g_?@^C??`?@`??b?oS??oT?`who?oUA?AHF?GC@?E?@oV??oW?~~~~~~~~~~~~[oX??oY??oZ??o[??o\?~~~~~~~~}___?o]@oCo^@oDp?@oEp@@TpA@X@?@mydG@AHF?GC@?EC?@`lji?TT@?C?@mye?rbSa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@uCa}B@uDa}C@uEa}D@]a}EA?A?C??g_?@^C??`?@`??b?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??b?a}O@uNa}P@uOa}Q@uPa}R@uQ?@nqhW?@nqo?m@PuRC??g_?@^uS?g_?uTC??g_?@LuU?cg_?uVC??g_?@RuW?o_?uX@XuYC??g_?@^uZ?g_?u[C??g_?@Lu\?cg_?u]@Vu^@Wv??c__?v@?`|g_?vA?f~~z~o___?vB?c_o___?@?@myn?m`A[vP?MvQ?n?vR?~~~~~~~~|{__?vS@]vTA?A?C??g_?@^C??`?@`??b?vU??vV@]vW?k?vX?~~~~~~~~~~~z]vY?m?vZ?g?v[?`Uv\A?A?C??g_?@^C??`?@`??b?v]??v^?`who?w??Aw@??wA?~~~~~~~~~~~~[wB??wC??wD??wE??wF?~~~~~~~~}___?wG@vMwH@vNwI@vOwJ@TwK@X@?@`lji?TT@?C?@mye?rbTa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@|Ma}B@|Na}C@|Oa}D@]a}EA?A?C??g_?@^C??`?@`??b?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??b?a}O@|Xa}P@|Ya}Q@|Za}R@|["%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c1_109_124_L.

Module Cert_src13_r0c1_109_124_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c1_109_124 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0c1_109_124_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX113_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX115_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX116_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX117_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX113 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX115 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX116 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX117.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c1_109_124 : htab := [(113%nat, (HS_src13_shX113_0, SH_src13_shX113_0)); (115%nat, (HS_src13_shX115_0, SH_src13_shX115_0)); (116%nat, (HS_src13_shX116_0, SH_src13_shX116_0)); (117%nat, (HS_src13_shX117_0, SH_src13_shX117_0))].

Definition C_src13_r0c1_109_124_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,109,124)].
Definition SH_src13_r0c1_109_124_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 113) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 115) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 116) (SHole 117)))).
Definition FUEL_src13_r0c1_109_124_0 : nat := 3000.
Lemma cert_src13_r0c1_109_124_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c1_109_124_0 (hs_of HT_src13_r0c1_109_124) HS_src13_pfx3_0 C_src13_r0c1_109_124_0 P_src13_r0c1_109_124_0 = COk SH_src13_r0c1_109_124_0.
Proof. cert_vm (COk SH_src13_r0c1_109_124_0). Qed.
End Cert_src13_r0c1_109_124_0.

(* [comment removed for export] *)
Module Plan_src13_r0c1_1149_1340.   (* [comment removed for export] *)
End Plan_src13_r0c1_1149_1340.

Module Plan_src13_r0c1_1149_1340_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c1_1149_1340_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTbAC??g_?@a@bB?g_?bCC??g_?@^bD?g_?bEC??g_?@LbF?cg_?bGC??g_?@RbH?o_?bI@XbJC??g_?@a@bK?g_?bLC??g_?@^bM?g_?bNC??g_?@LbO?cg_?bP@VbQ@WbR?c__?bS?`|g_?bT?f~~z~o___?bU?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji?TT@?C??N??@mye?ra]a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@fTa}D@fUa}E@fVa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@g?a}R@g@a}S@gAa}T@gB?@nqhW?@nqo?mKTgCC??g_?@a@gD?g_?gEC??g_?@^gF?g_?gGC??g_?@LgH?cg_?gIC??g_?@RgJ?o_?gK@XgLC??g_?@a@gM?g_?gNC??g_?@^gO?g_?gPC??g_?@LgQ?cg_?gR@VgS@WgT?c__?gU?`|g_?gV?f~~z~o___?gW?c_o___?@?@myn?m`?[hE?MhF?n?hG?~~~~~~~~|{__?hH@]hIA?A?C??g_?@^C??`?@`??`?hJ??hK@]hL?k?hM?~~~~~~~~~~~z]hN?m?hO?g?hP?`UhQA?A?C??g_?@^C??`?@`??`?hR??hS?`who?hTAHF?GC@?EhU??hV?~~~~~~~~~~~~[hW??hX??hY??hZ??h[?~~~~~~~~}___?h\@hBh]@hCh^@hDi?@Ti@@X@?@mydG@AHF?GC@?EA?@`lji?TT@?C??N??@mye?ra^a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@nBa}D@nCa}E@nDa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@nMa}R@nNa}S@nOa}T@nP?@nqhW?@nqo?mKTnQC??g_?@a@nR?g_?nSC??g_?@^nT?g_?nUC??g_?@LnV?cg_?nWC??g_?@RnX?o_?nY@XnZC??g_?@a@n[?g_?n\C??g_?@^n]?g_?n^C??g_?@Lo??cg_?o@@VoA@WoB?c__?oC?`|g_?oD?f~~z~o___?oE?c_o___?@?@myn?m`@[oS?MoT?n?oU?~~~~~~~~|{__?oV@]oWA?A?C??g_?@^C??`?@`??`?oX??oY@]oZ?k?o[?~~~~~~~~~~~z]o\?m?o]?g?o^?`Up?A?A?C??g_?@^C??`?@`??`?p@??pA?`who?pBA?AHF?GC@?E?@pC??pD?~~~~~~~~~~~~[pE??pF??pG??pH??pI?~~~~~~~~}___?pJ@oPpK@oQpL@oRpM@TpN@X@?@mydG@AHF?GC@?EC?@`lji?TT@?C??N??@mye?rb?a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@uPa}D@uQa}E@uRa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@u[a}R@u\a}S@u]a}T@u^?@nqhW?@nqo?mKTv?C??g_?@a@v@?g_?vAC??g_?@^vB?g_?vCC??g_?@LvD?cg_?vEC??g_?@RvF?o_?vG@XvHC??g_?@a@vI?g_?vJC??g_?@^vK?g_?vLC??g_?@LvM?cg_?vN@VvO@WvP?c__?vQ?`|g_?vR?f~~z~o___?vS?c_o___?@?@myn?m`A[wA?MwB?n?wC?~~~~~~~~|{__?wD@]wEA?A?C??g_?@^C??`?@`??`?wF??wG@]wH?k?wI?~~~~~~~~~~~z]wJ?m?wK?g?wL?`UwMA?A?C??g_?@^C??`?@`??`?wN??wO?`who?wP?AwQ??wR?~~~~~~~~~~~~[wS??wT??wU??wV??wW?~~~~~~~~}___?wX@v^wY@w?wZ@w@w[@Tw\@X@?@`lji?TT@?C??N??@mye?rb@a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?g_?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C@|^a}D@}?a}E@}@a}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Ea}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@}Ia}R@}Ja}S@}Ka}T@}L"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c1_1149_1340_L.

Module Cert_src13_r0c1_1149_1340_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c1_1149_1340 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0c1_1149_1340_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX94_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX95_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX96_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX97_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX94 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX95 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX96 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX97.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c1_1149_1340 : htab := [(94%nat, (HS_src13_shX94_0, SH_src13_shX94_0)); (95%nat, (HS_src13_shX95_0, SH_src13_shX95_0)); (96%nat, (HS_src13_shX96_0, SH_src13_shX96_0)); (97%nat, (HS_src13_shX97_0, SH_src13_shX97_0))].

Definition C_src13_r0c1_1149_1340_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,1149,1340)].
Definition SH_src13_r0c1_1149_1340_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 94) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 95) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 96) (SHole 97)))).
Definition FUEL_src13_r0c1_1149_1340_0 : nat := 3000.
Lemma cert_src13_r0c1_1149_1340_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c1_1149_1340_0 (hs_of HT_src13_r0c1_1149_1340) HS_src13_pfx3_0 C_src13_r0c1_1149_1340_0 P_src13_r0c1_1149_1340_0 = COk SH_src13_r0c1_1149_1340_0.
Proof. cert_vm (COk SH_src13_r0c1_1149_1340_0). Qed.
End Cert_src13_r0c1_1149_1340_0.

(* [comment removed for export] *)
Module Plan_src13_r0c1_12269_13084.   (* [comment removed for export] *)
End Plan_src13_r0c1_12269_13084.

Module Plan_src13_r0c1_12269_13084_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c1_12269_13084_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTbAC??g_?@a@bB?g_?bCC??g_?@^bD?`__?bEC??g_?@LbF?cg_?bGC??g_?@RbH?o_?bI@XbJC??g_?@a@bK?g_?bLC??g_?@^bM?`__?bNC??g_?@LbO?cg_?bP@VbQ@WbR?c__?bS?`|g_?bT?f~~z~o___?bU?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji?TT@?C??N??@mye?ra]a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fUa}E@fVa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@g?a}R@g@a}S@gAa}T@gB?@nqhW?@nqo?mKTgCC??g_?@a@gD?g_?gEC??g_?@^gF?`__?gGC??g_?@LgH?cg_?gIC??g_?@RgJ?o_?gK@XgLC??g_?@a@gM?g_?gNC??g_?@^gO?`__?gPC??g_?@LgQ?cg_?gR@VgS@WgT?c__?gU?`|g_?gV?f~~z~o___?gW?c_o___?@?@myn?m`?[hE?MhF?n?hG?~~~~~~~~|{__?hH@]hIA?A?C??g_?@^C??`?@`??`?hJ??hK@]hL?k?hM?~~~~~~~~~~~z]hN?m?hO?g?hP?`UhQA?A?C??g_?@^C??`?@`??`?hR??hS?`who?hTAHF?GC@?EhU??hV?~~~~~~~~~~~~[hW??hX??hY??hZ??h[?~~~~~~~~}___?h\@hBh]@hCh^@hDi?@Ti@@X@?@mydG@AHF?GC@?EA?@`lji?TT@?C??N??@mye?ra^a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@nCa}E@nDa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@nMa}R@nNa}S@nOa}T@nP?@nqhW?@nqo?mKTnQC??g_?@a@nR?g_?nSC??g_?@^nT?`__?nUC??g_?@LnV?cg_?nWC??g_?@RnX?o_?nY@XnZC??g_?@a@n[?g_?n\C??g_?@^n]?`__?n^C??g_?@Lo??cg_?o@@VoA@WoB?c__?oC?`|g_?oD?f~~z~o___?oE?c_o___?@?@myn?m`@[oS?MoT?n?oU?~~~~~~~~|{__?oV@]oWA?A?C??g_?@^C??`?@`??`?oX??oY@]oZ?k?o[?~~~~~~~~~~~z]o\?m?o]?g?o^?`Up?A?A?C??g_?@^C??`?@`??`?p@??pA?`who?pBA?AHF?GC@?E?@pC??pD?~~~~~~~~~~~~[pE??pF??pG??pH??pI?~~~~~~~~}___?pJ@oPpK@oQpL@oRpM@TpN@X@?@mydG@AHF?GC@?EC?@`lji?TT@?C??N??@mye?rb?a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@uQa}E@uRa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@u[a}R@u\a}S@u]a}T@u^?@nqhW?@nqo?mKTv?C??g_?@a@v@?g_?vAC??g_?@^vB?`__?vCC??g_?@LvD?cg_?vEC??g_?@RvF?o_?vG@XvHC??g_?@a@vI?g_?vJC??g_?@^vK?`__?vLC??g_?@LvM?cg_?vN@VvO@WvP?c__?vQ?`|g_?vR?f~~z~o___?vS?c_o___?@?@myn?m`A[wA?MwB?n?wC?~~~~~~~~|{__?wD@]wEA?A?C??g_?@^C??`?@`??`?wF??wG@]wH?k?wI?~~~~~~~~~~~z]wJ?m?wK?g?wL?`UwMA?A?C??g_?@^C??`?@`??`?wN??wO?`who?wP?AwQ??wR?~~~~~~~~~~~~[wS??wT??wU??wV??wW?~~~~~~~~}___?wX@v^wY@w?wZ@w@w[@Tw\@X@?@`lji?TT@?C??N??@mye?rb@a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@}?a}E@}@a}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@}Ia}R@}Ja}S@}Ka}T@}L"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c1_12269_13084_L.

Module Cert_src13_r0c1_12269_13084_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c1_12269_13084 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0c1_12269_13084_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX94_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX95_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX96_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX97_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX94 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX95 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX96 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX97.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c1_12269_13084 : htab := [(94%nat, (HS_src13_shX94_0, SH_src13_shX94_0)); (95%nat, (HS_src13_shX95_0, SH_src13_shX95_0)); (96%nat, (HS_src13_shX96_0, SH_src13_shX96_0)); (97%nat, (HS_src13_shX97_0, SH_src13_shX97_0))].

Definition C_src13_r0c1_12269_13084_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,12269,13084)].
Definition SH_src13_r0c1_12269_13084_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 94) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 95) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 96) (SHole 97)))).
Definition FUEL_src13_r0c1_12269_13084_0 : nat := 3000.
Lemma cert_src13_r0c1_12269_13084_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c1_12269_13084_0 (hs_of HT_src13_r0c1_12269_13084) HS_src13_pfx3_0 C_src13_r0c1_12269_13084_0 P_src13_r0c1_12269_13084_0 = COk SH_src13_r0c1_12269_13084_0.
Proof. cert_vm (COk SH_src13_r0c1_12269_13084_0). Qed.
End Cert_src13_r0c1_12269_13084_0.

(* [comment removed for export] *)
Module Plan_src13_r0c1_125_140.   (* [comment removed for export] *)
End Plan_src13_r0c1_125_140.

Module Plan_src13_r0c1_125_140_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c1_125_140_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pb@C??g_?@^bA?g_?bBC??g_?@LbC?cg_?bDC??g_?@RbE?o_?bF@XbGC??g_?@^bH?g_?bIC??g_?@LbJ?cg_?bK@VbL@WbM?c__?bN?`|g_?bO?f~~z~o___?bP?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji?TT@?C?@mye?r`Ia|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@fOa}B@fPa}C@fQa}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@fZa}P@f[a}Q@f\a}R@f]?@nqhW?@nqo?m@Pf^C??g_?@^g??g_?g@C??g_?@LgA?cg_?gBC??g_?@RgC?o_?gD@XgEC??g_?@^gF?g_?gGC??g_?@LgH?cg_?gI@VgJ@WgK?c__?gL?`|g_?gM?f~~z~o___?gN?c_o___?@?@myn?m`?[g\?Mg]?n?g^?~~~~~~~~|{__?h?@]h@A?A?C??g_?@^C??`?@`??c?hA??hB@]hC?k?hD?~~~~~~~~~~~z]hE?m?hF?g?hG?`UhHA?A?C??g_?@^C??`?@`??c?hI??hJ?`who?hKAHF?GC@?EhL??hM?~~~~~~~~~~~~[hN??hO??hP??hQ??hR?~~~~~~~~}___?hS@gYhT@gZhU@g[hV@ThW@X@?@mydG@AHF?GC@?EA?@`lji?TT@?C?@mye?r`Ja|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@mYa}B@mZa}C@m[a}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@nDa}P@nEa}Q@nFa}R@nG?@nqhW?@nqo?m@PnHC??g_?@^nI?g_?nJC??g_?@LnK?cg_?nLC??g_?@RnM?o_?nN@XnOC??g_?@^nP?g_?nQC??g_?@LnR?cg_?nS@VnT@WnU?c__?nV?`|g_?nW?f~~z~o___?nX?c_o___?@?@myn?m`@[oF?MoG?n?oH?~~~~~~~~|{__?oI@]oJA?A?C??g_?@^C??`?@`??c?oK??oL@]oM?k?oN?~~~~~~~~~~~z]oO?m?oP?g?oQ?`UoRA?A?C??g_?@^C??`?@`??c?oS??oT?`who?oUA?AHF?GC@?E?@oV??oW?~~~~~~~~~~~~[oX??oY??oZ??o[??o\?~~~~~~~~}___?o]@oCo^@oDp?@oEp@@TpA@X@?@mydG@AHF?GC@?EC?@`lji?TT@?C?@mye?r`Ka|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@uCa}B@uDa}C@uEa}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@uNa}P@uOa}Q@uPa}R@uQ?@nqhW?@nqo?m@PuRC??g_?@^uS?g_?uTC??g_?@LuU?cg_?uVC??g_?@RuW?o_?uX@XuYC??g_?@^uZ?g_?u[C??g_?@Lu\?cg_?u]@Vu^@Wv??c__?v@?`|g_?vA?f~~z~o___?vB?c_o___?@?@myn?m`A[vP?MvQ?n?vR?~~~~~~~~|{__?vS@]vTA?A?C??g_?@^C??`?@`??c?vU??vV@]vW?k?vX?~~~~~~~~~~~z]vY?m?vZ?g?v[?`Uv\A?A?C??g_?@^C??`?@`??c?v]??v^?`who?w??Aw@??wA?~~~~~~~~~~~~[wB??wC??wD??wE??wF?~~~~~~~~}___?wG@vMwH@vNwI@vOwJ@TwK@X@?@`lji?TT@?C?@mye?r`Na|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@|Ma}B@|Na}C@|Oa}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@|Xa}P@|Ya}Q@|Za}R@|["%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c1_125_140_L.

Module Cert_src13_r0c1_125_140_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c1_125_140 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0c1_125_140_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX42_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX43_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX44_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX47_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX42 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX43 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX44 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX47.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c1_125_140 : htab := [(42%nat, (HS_src13_shX42_0, SH_src13_shX42_0)); (43%nat, (HS_src13_shX43_0, SH_src13_shX43_0)); (44%nat, (HS_src13_shX44_0, SH_src13_shX44_0)); (47%nat, (HS_src13_shX47_0, SH_src13_shX47_0))].

Definition C_src13_r0c1_125_140_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,125,140)].
Definition SH_src13_r0c1_125_140_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 42) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 43) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 44) (SHole 47)))).
Definition FUEL_src13_r0c1_125_140_0 : nat := 3000.
Lemma cert_src13_r0c1_125_140_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c1_125_140_0 (hs_of HT_src13_r0c1_125_140) HS_src13_pfx3_0 C_src13_r0c1_125_140_0 P_src13_r0c1_125_140_0 = COk SH_src13_r0c1_125_140_0.
Proof. cert_vm (COk SH_src13_r0c1_125_140_0). Qed.
End Cert_src13_r0c1_125_140_0.

(* [comment removed for export] *)
Module Plan_src13_r0c1_13085_16364.   (* [comment removed for export] *)
End Plan_src13_r0c1_13085_16364.

Module Plan_src13_r0c1_13085_16364_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c1_13085_16364_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB???O?@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?mKTbAC??g_?@a@bB?g_?bCC??g_?@^bD?`__?bEC??g_?@LbF?cg_?bGC??g_?@RbH?o_?bI@XbJC??g_?@a@bK?g_?bLC??g_?@^bM?`__?bNC??g_?@LbO?cg_?bP@VbQ@WbR?c__?bS?`|g_?bT?f~~z~o___?bU?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji?TT@?C??N??@mye?ra]a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@fUa}E@fVa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@g?a}R@g@a}S@gAa}T@gB?@nqhW?@nqo?mKTgCC??g_?@a@gD?g_?gEC??g_?@^gF?`__?gGC??g_?@LgH?cg_?gIC??g_?@RgJ?o_?gK@XgLC??g_?@a@gM?g_?gNC??g_?@^gO?`__?gPC??g_?@LgQ?cg_?gR@VgS@WgT?c__?gU?`|g_?gV?f~~z~o___?gW?c_o___?@?@myn?m`?[hE?MhF?n?hG?~~~~~~~~|{__?hH@]hIA?A?C??g_?@^C??`?@`??`?hJ??hK@]hL?k?hM?~~~~~~~~~~~z]hN?m?hO?g?hP?`UhQA?A?C??g_?@^C??`?@`??`?hR??hS?`who?hTAHF?GC@?EhU??hV?~~~~~~~~~~~~[hW??hX??hY??hZ??h[?~~~~~~~~}___?h\@hBh]@hCh^@hDi?@Ti@@X@?@mydG@AHF?GC@?EA?@`lji?TT@?C??N??@mye?ra^a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@nCa}E@nDa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@nMa}R@nNa}S@nOa}T@nP?@nqhW?@nqo?mKTnQC??g_?@a@nR?g_?nSC??g_?@^nT?`__?nUC??g_?@LnV?cg_?nWC??g_?@RnX?o_?nY@XnZC??g_?@a@n[?g_?n\C??g_?@^n]?`__?n^C??g_?@Lo??cg_?o@@VoA@WoB?c__?oC?`|g_?oD?f~~z~o___?oE?c_o___?@?@myn?m`@[oS?MoT?n?oU?~~~~~~~~|{__?oV@]oWA?A?C??g_?@^C??`?@`??`?oX??oY@]oZ?k?o[?~~~~~~~~~~~z]o\?m?o]?g?o^?`Up?A?A?C??g_?@^C??`?@`??`?p@??pA?`who?pBA?AHF?GC@?E?@pC??pD?~~~~~~~~~~~~[pE??pF??pG??pH??pI?~~~~~~~~}___?pJ@oPpK@oQpL@oRpM@TpN@X@?@mydG@AHF?GC@?EC?@`lji?TT@?C??N??@mye?rb?a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@uQa}E@uRa}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@u[a}R@u\a}S@u]a}T@u^?@nqhW?@nqo?mKTv?C??g_?@a@v@?g_?vAC??g_?@^vB?`__?vCC??g_?@LvD?cg_?vEC??g_?@RvF?o_?vG@XvHC??g_?@a@vI?g_?vJC??g_?@^vK?`__?vLC??g_?@LvM?cg_?vN@VvO@WvP?c__?vQ?`|g_?vR?f~~z~o___?vS?c_o___?@?@myn?m`A[wA?MwB?n?wC?~~~~~~~~|{__?wD@]wEA?A?C??g_?@^C??`?@`??`?wF??wG@]wH?k?wI?~~~~~~~~~~~z]wJ?m?wK?g?wL?`UwMA?A?C??g_?@^C??`?@`??`?wN??wO?`who?wP?AwQ??wR?~~~~~~~~~~~~[wS??wT??wU??wV??wW?~~~~~~~~}___?wX@v^wY@w?wZ@w@w[@Tw\@X@?@`lji?TT@?C??N??@mye?rb@a|W]a|W@a@a|X@La|Y@Ra|Z@^a|[?`__?a|\@Va|]@Wa|^@Xa}?@]a}@@Ua}A@Ta}B@Sa}C?~~~~~~~~~~w_?a}D@}?a}E@}@a}F@]a}GA?A?C??g_?@^C??`?@`??`?a}H??a}I?~~~~~~~~~~w_Aa}J??a}K@Ta}L?Aa}M??a}N?eGa}O?lMa}PA?A?C??g_?@^C??`?@`??`?a}Q@}Ia}R@}Ja}S@}Ka}T@}L"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c1_13085_16364_L.

Module Cert_src13_r0c1_13085_16364_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c1_13085_16364 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0c1_13085_16364_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX94_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX95_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX96_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX97_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX94 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX95 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX96 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX97.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c1_13085_16364 : htab := [(94%nat, (HS_src13_shX94_0, SH_src13_shX94_0)); (95%nat, (HS_src13_shX95_0, SH_src13_shX95_0)); (96%nat, (HS_src13_shX96_0, SH_src13_shX96_0)); (97%nat, (HS_src13_shX97_0, SH_src13_shX97_0))].

Definition C_src13_r0c1_13085_16364_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,13085,16364)].
Definition SH_src13_r0c1_13085_16364_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 94) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 95) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 96) (SHole 97)))).
Definition FUEL_src13_r0c1_13085_16364_0 : nat := 3000.
Lemma cert_src13_r0c1_13085_16364_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c1_13085_16364_0 (hs_of HT_src13_r0c1_13085_16364) HS_src13_pfx3_0 C_src13_r0c1_13085_16364_0 P_src13_r0c1_13085_16364_0 = COk SH_src13_r0c1_13085_16364_0.
Proof. cert_vm (COk SH_src13_r0c1_13085_16364_0). Qed.
End Cert_src13_r0c1_13085_16364_0.

(* [comment removed for export] *)
Module Plan_src13_r0c1_1341_1628.   (* [comment removed for export] *)
End Plan_src13_r0c1_1341_1628.

Module Plan_src13_r0c1_1341_1628_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c1_1341_1628_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc?TS@?C??SB??@`luc??@`luc??@`luc??@`luc???SB??@nqhW?@nqo?m@Pb@C??g_?@^bA?g_?bBC??g_?@LbC?cg_?bDC??g_?@RbE?o_?bF@XbGC??g_?@^bH?g_?bIC??g_?@LbJ?cg_?bK@VbL@WbM?c__?bN?`|g_?bO?f~~z~o___?bP?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji?TT@?C?@mye?rbAa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@fOa}B@fPa}C@fQa}D@]a}EA?A?C??g_?@^C??`?@`??`?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??`?a}O@fZa}P@f[a}Q@f\a}R@f]?@nqhW?@nqo?m@Pf^C??g_?@^g??g_?g@C??g_?@LgA?cg_?gBC??g_?@RgC?o_?gD@XgEC??g_?@^gF?g_?gGC??g_?@LgH?cg_?gI@VgJ@WgK?c__?gL?`|g_?gM?f~~z~o___?gN?c_o___?@?@myn?m`?[g\?Mg]?n?g^?~~~~~~~~|{__?h?@]h@A?A?C??g_?@^C??`?@`??`?hA??hB@]hC?k?hD?~~~~~~~~~~~z]hE?m?hF?g?hG?`UhHA?A?C??g_?@^C??`?@`??`?hI??hJ?`who?hKAHF?GC@?EhL??hM?~~~~~~~~~~~~[hN??hO??hP??hQ??hR?~~~~~~~~}___?hS@gYhT@gZhU@g[hV@ThW@X@?@mydG@AHF?GC@?EA?@`lji?TT@?C?@mye?rbBa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@mYa}B@mZa}C@m[a}D@]a}EA?A?C??g_?@^C??`?@`??`?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??`?a}O@nDa}P@nEa}Q@nFa}R@nG?@nqhW?@nqo?m@PnHC??g_?@^nI?g_?nJC??g_?@LnK?cg_?nLC??g_?@RnM?o_?nN@XnOC??g_?@^nP?g_?nQC??g_?@LnR?cg_?nS@VnT@WnU?c__?nV?`|g_?nW?f~~z~o___?nX?c_o___?@?@myn?m`@[oF?MoG?n?oH?~~~~~~~~|{__?oI@]oJA?A?C??g_?@^C??`?@`??`?oK??oL@]oM?k?oN?~~~~~~~~~~~z]oO?m?oP?g?oQ?`UoRA?A?C??g_?@^C??`?@`??`?oS??oT?`who?oUA?AHF?GC@?E?@oV??oW?~~~~~~~~~~~~[oX??oY??oZ??o[??o\?~~~~~~~~}___?o]@oCo^@oDp?@oEp@@TpA@X@?@mydG@AHF?GC@?EC?@`lji?TT@?C?@mye?rbCa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@uCa}B@uDa}C@uEa}D@]a}EA?A?C??g_?@^C??`?@`??`?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??`?a}O@uNa}P@uOa}Q@uPa}R@uQ?@nqhW?@nqo?m@PuRC??g_?@^uS?g_?uTC??g_?@LuU?cg_?uVC??g_?@RuW?o_?uX@XuYC??g_?@^uZ?g_?u[C??g_?@Lu\?cg_?u]@Vu^@Wv??c__?v@?`|g_?vA?f~~z~o___?vB?c_o___?@?@myn?m`A[vP?MvQ?n?vR?~~~~~~~~|{__?vS@]vTA?A?C??g_?@^C??`?@`??`?vU??vV@]vW?k?vX?~~~~~~~~~~~z]vY?m?vZ?g?v[?`Uv\A?A?C??g_?@^C??`?@`??`?v]??v^?`who?w??Aw@??wA?~~~~~~~~~~~~[wB??wC??wD??wE??wF?~~~~~~~~}___?wG@vMwH@vNwI@vOwJ@TwK@X@?@`lji?TT@?C?@mye?rbDa|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@|Ma}B@|Na}C@|Oa}D@]a}EA?A?C??g_?@^C??`?@`??`?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?gdWa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??`?a}O@|Xa}P@|Ya}Q@|Za}R@|["%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c1_1341_1628_L.

Module Cert_src13_r0c1_1341_1628_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c1_1341_1628 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0c1_1341_1628_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX100_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX101_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.Cert_src13_shX98_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX99_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX100 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX101 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_2.HS_src13_shX98 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX99.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c1_1341_1628 : htab := [(98%nat, (HS_src13_shX98_0, SH_src13_shX98_0)); (99%nat, (HS_src13_shX99_0, SH_src13_shX99_0)); (100%nat, (HS_src13_shX100_0, SH_src13_shX100_0)); (101%nat, (HS_src13_shX101_0, SH_src13_shX101_0))].

Definition C_src13_r0c1_1341_1628_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,1341,1628)].
Definition SH_src13_r0c1_1341_1628_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 98) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 99) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 100) (SHole 101)))).
Definition FUEL_src13_r0c1_1341_1628_0 : nat := 3000.
Lemma cert_src13_r0c1_1341_1628_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c1_1341_1628_0 (hs_of HT_src13_r0c1_1341_1628) HS_src13_pfx3_0 C_src13_r0c1_1341_1628_0 P_src13_r0c1_1341_1628_0 = COk SH_src13_r0c1_1341_1628_0.
Proof. cert_vm (COk SH_src13_r0c1_1341_1628_0). Qed.
End Cert_src13_r0c1_1341_1628_0.

(* [comment removed for export] *)
Module Plan_src13_r0c1_13_28.   (* [comment removed for export] *)
End Plan_src13_r0c1_13_28.

Module Plan_src13_r0c1_13_28_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c1_13_28_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pb@C??g_?@^bA?g_?bBC??g_?@LbC?cg_?bDC??g_?@RbE?o_?bF@XbGC??g_?@^bH?g_?bIC??g_?@LbJ?cg_?bK@VbL@WbM?c__?bN?`|g_?bO?f~~z~o___?bP?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji?TT@?C?@mye?r`Ia|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@fOa}B@fPa}C@fQa}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@fZa}P@f[a}Q@f\a}R@f]?@nqhW?@nqo?m@Pf^C??g_?@^g??g_?g@C??g_?@LgA?cg_?gBC??g_?@RgC?o_?gD@XgEC??g_?@^gF?g_?gGC??g_?@LgH?cg_?gI@VgJ@WgK?c__?gL?`|g_?gM?f~~z~o___?gN?c_o___?@?@myn?m`?[g\?Mg]?n?g^?~~~~~~~~|{__?h?@]h@A?A?C??g_?@^C??`?@`??c?hA??hB@]hC?k?hD?~~~~~~~~~~~z]hE?m?hF?g?hG?`UhHA?A?C??g_?@^C??`?@`??c?hI??hJ?`who?hKAHF?GC@?EhL??hM?~~~~~~~~~~~~[hN??hO??hP??hQ??hR?~~~~~~~~}___?hS@gYhT@gZhU@g[hV@ThW@X@?@mydG@AHF?GC@?EA?@`lji?TT@?C?@mye?r`Ja|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@mYa}B@mZa}C@m[a}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@nDa}P@nEa}Q@nFa}R@nG?@nqhW?@nqo?m@PnHC??g_?@^nI?g_?nJC??g_?@LnK?cg_?nLC??g_?@RnM?o_?nN@XnOC??g_?@^nP?g_?nQC??g_?@LnR?cg_?nS@VnT@WnU?c__?nV?`|g_?nW?f~~z~o___?nX?c_o___?@?@myn?m`@[oF?MoG?n?oH?~~~~~~~~|{__?oI@]oJA?A?C??g_?@^C??`?@`??c?oK??oL@]oM?k?oN?~~~~~~~~~~~z]oO?m?oP?g?oQ?`UoRA?A?C??g_?@^C??`?@`??c?oS??oT?`who?oUA?AHF?GC@?E?@oV??oW?~~~~~~~~~~~~[oX??oY??oZ??o[??o\?~~~~~~~~}___?o]@oCo^@oDp?@oEp@@TpA@X@?@mydG@AHF?GC@?EC?@`lji?TT@?C?@mye?r`Ka|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@uCa}B@uDa}C@uEa}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@uNa}P@uOa}Q@uPa}R@uQ?@nqhW?@nqo?m@PuRC??g_?@^uS?g_?uTC??g_?@LuU?cg_?uVC??g_?@RuW?o_?uX@XuYC??g_?@^uZ?g_?u[C??g_?@Lu\?cg_?u]@Vu^@Wv??c__?v@?`|g_?vA?f~~z~o___?vB?c_o___?@?@myn?m`A[vP?MvQ?n?vR?~~~~~~~~|{__?vS@]vTA?A?C??g_?@^C??`?@`??c?vU??vV@]vW?k?vX?~~~~~~~~~~~z]vY?m?vZ?g?v[?`Uv\A?A?C??g_?@^C??`?@`??c?v]??v^?`who?w??Aw@??wA?~~~~~~~~~~~~[wB??wC??wD??wE??wF?~~~~~~~~}___?wG@vMwH@vNwI@vOwJ@TwK@X@?@`lji?TT@?C?@mye?r`Na|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@|Ma}B@|Na}C@|Oa}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@|Xa}P@|Ya}Q@|Za}R@|["%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c1_13_28_L.

Module Cert_src13_r0c1_13_28_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c1_13_28 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0c1_13_28_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX42_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX43_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX44_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX47_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX42 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX43 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX44 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX47.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c1_13_28 : htab := [(42%nat, (HS_src13_shX42_0, SH_src13_shX42_0)); (43%nat, (HS_src13_shX43_0, SH_src13_shX43_0)); (44%nat, (HS_src13_shX44_0, SH_src13_shX44_0)); (47%nat, (HS_src13_shX47_0, SH_src13_shX47_0))].

Definition C_src13_r0c1_13_28_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,13,28)].
Definition SH_src13_r0c1_13_28_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 42) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 43) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 44) (SHole 47)))).
Definition FUEL_src13_r0c1_13_28_0 : nat := 3000.
Lemma cert_src13_r0c1_13_28_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c1_13_28_0 (hs_of HT_src13_r0c1_13_28) HS_src13_pfx3_0 C_src13_r0c1_13_28_0 P_src13_r0c1_13_28_0 = COk SH_src13_r0c1_13_28_0.
Proof. cert_vm (COk SH_src13_r0c1_13_28_0). Qed.
End Cert_src13_r0c1_13_28_0.

(* [comment removed for export] *)
Module Plan_src13_r0c1_141_156.   (* [comment removed for export] *)
End Plan_src13_r0c1_141_156.

Module Plan_src13_r0c1_141_156_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0c1_141_156_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc?TS@?C??SB??@`luc??@`luc???SB??@nqhW?@nqo?m@Pb@C??g_?@^bA?g_?bBC??g_?@LbC?cg_?bDC??g_?@RbE?o_?bF@XbGC??g_?@^bH?g_?bIC??g_?@LbJ?cg_?bK@VbL@WbM?c__?bN?`|g_?bO?f~~z~o___?bP?c_o___?@??SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji?TT@?C?@mye?r`Ia|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@fOa}B@fPa}C@fQa}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@fZa}P@f[a}Q@f\a}R@f]?@nqhW?@nqo?m@Pf^C??g_?@^g??g_?g@C??g_?@LgA?cg_?gBC??g_?@RgC?o_?gD@XgEC??g_?@^gF?g_?gGC??g_?@LgH?cg_?gI@VgJ@WgK?c__?gL?`|g_?gM?f~~z~o___?gN?c_o___?@?@myn?m`?[g\?Mg]?n?g^?~~~~~~~~|{__?h?@]h@A?A?C??g_?@^C??`?@`??c?hA??hB@]hC?k?hD?~~~~~~~~~~~z]hE?m?hF?g?hG?`UhHA?A?C??g_?@^C??`?@`??c?hI??hJ?`who?hKAHF?GC@?EhL??hM?~~~~~~~~~~~~[hN??hO??hP??hQ??hR?~~~~~~~~}___?hS@gYhT@gZhU@g[hV@ThW@X@?@mydG@AHF?GC@?EA?@`lji?TT@?C?@mye?r`Ja|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@mYa}B@mZa}C@m[a}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@nDa}P@nEa}Q@nFa}R@nG?@nqhW?@nqo?m@PnHC??g_?@^nI?g_?nJC??g_?@LnK?cg_?nLC??g_?@RnM?o_?nN@XnOC??g_?@^nP?g_?nQC??g_?@LnR?cg_?nS@VnT@WnU?c__?nV?`|g_?nW?f~~z~o___?nX?c_o___?@?@myn?m`@[oF?MoG?n?oH?~~~~~~~~|{__?oI@]oJA?A?C??g_?@^C??`?@`??c?oK??oL@]oM?k?oN?~~~~~~~~~~~z]oO?m?oP?g?oQ?`UoRA?A?C??g_?@^C??`?@`??c?oS??oT?`who?oUA?AHF?GC@?E?@oV??oW?~~~~~~~~~~~~[oX??oY??oZ??o[??o\?~~~~~~~~}___?o]@oCo^@oDp?@oEp@@TpA@X@?@mydG@AHF?GC@?EC?@`lji?TT@?C?@mye?r`Ka|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@uCa}B@uDa}C@uEa}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@uNa}P@uOa}Q@uPa}R@uQ?@nqhW?@nqo?m@PuRC??g_?@^uS?g_?uTC??g_?@LuU?cg_?uVC??g_?@RuW?o_?uX@XuYC??g_?@^uZ?g_?u[C??g_?@Lu\?cg_?u]@Vu^@Wv??c__?v@?`|g_?vA?f~~z~o___?vB?c_o___?@?@myn?m`A[vP?MvQ?n?vR?~~~~~~~~|{__?vS@]vTA?A?C??g_?@^C??`?@`??c?vU??vV@]vW?k?vX?~~~~~~~~~~~z]vY?m?vZ?g?v[?`Uv\A?A?C??g_?@^C??`?@`??c?v]??v^?`who?w??Aw@??wA?~~~~~~~~~~~~[wB??wC??wD??wE??wF?~~~~~~~~}___?wG@vMwH@vNwI@vOwJ@TwK@X@?@`lji?TT@?C?@mye?r`Na|W[a|W@^a|X@La|Y@Ra|Z@Va|[@Wa|\@Xa|]@]a|^@Ua}?@Ta}@@Sa}A@|Ma}B@|Na}C@|Oa}D@]a}EA?A?C??g_?@^C??`?@`??c?a}F?a_{|?a}G??a}H??a}I@Ta}JA?C??g_?@R?ggGa}K??a}L?Ea}M??a}NA?A?C??g_?@^C??`?@`??c?a}O@|Xa}P@|Ya}Q@|Za}R@|["%pstring.
(* [comment removed for export] *)
End Plan_src13_r0c1_141_156_L.

Module Cert_src13_r0c1_141_156_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0c1_141_156 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0c1_141_156_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX42_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX43_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX44_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.Cert_src13_shX47_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX42 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX43 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX44 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_1.HS_src13_shX47.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0c1_141_156 : htab := [(42%nat, (HS_src13_shX42_0, SH_src13_shX42_0)); (43%nat, (HS_src13_shX43_0, SH_src13_shX43_0)); (44%nat, (HS_src13_shX44_0, SH_src13_shX44_0)); (47%nat, (HS_src13_shX47_0, SH_src13_shX47_0))].

Definition C_src13_r0c1_141_156_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,141,156)].
Definition SH_src13_r0c1_141_156_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 42) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 43) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 44) (SHole 47)))).
Definition FUEL_src13_r0c1_141_156_0 : nat := 3000.
Lemma cert_src13_r0c1_141_156_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0c1_141_156_0 (hs_of HT_src13_r0c1_141_156) HS_src13_pfx3_0 C_src13_r0c1_141_156_0 P_src13_r0c1_141_156_0 = COk SH_src13_r0c1_141_156_0.
Proof. cert_vm (COk SH_src13_r0c1_141_156_0). Qed.
End Cert_src13_r0c1_141_156_0.
