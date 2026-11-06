(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require AxSymExec3 AsanPlan PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require AsanNodesIO AsanMainLib ImgParams MainDefs Img_src13 Cert_common ITab_src13 Segs_src13 HS_src13_pfx3 Sh_src13_3 PlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
(* [comment removed for export] *)
Module Plan_src13_r0n0c1.   (* [comment removed for export] *)
End Plan_src13_r0n0c1.

Module Plan_src13_r0n0c1_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_src13_r0n0c1_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mw~GMS????O?@`luc??@`luc??@`luc??@`luc???SB???SB???SB???SA???SB???SB???TO??@`mbdOU????SB??@mydG@AHF?GC@?E??@`lji??@mx_WbmxgW??@`lji???N??@`lji???N??@`kwyWrbXa|WGa|W@Ra|X@^a|Y?g_?a|Z@La|[?cg_?a|\@Va|]@Wa|^@X??SB???SB???SA???SB???SB???SB??@mydG@AHF?GC@?EA?@`lji??@mx_WbmxgW??@`lji???N??@`lji???N??@`kwyWrbWa|WGa|W@Ra|X@^a|Y?g_?a|Z@La|[?cg_?a|\@Va|]@Wa|^@X??SB???SB???SA???SB???SB???SB??@mydG@AHF?GC@?EC?@`lji??@mx_WbmxgW??@`lji???N??@`lji???N??@`kwyWrbVa|WGa|W@Ra|X@^a|Y?g_?a|Z@La|[?cg_?a|\@Va|]@Wa|^@X??SB???SB???SA???SB???SB???SB??@`lji??@mx_WbmxgW??@`lji???N??@`lji???N??@`kwyWrbUa|WGa|W@Ra|X@^a|Y?g_?a|Z@La|[?cg_?a|\@Va|]@Wa|^@X"%pstring.
(* [comment removed for export] *)
End Plan_src13_r0n0c1_L.

Module Cert_src13_r0n0c1_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_src13.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_src13 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_src13 Plan_src13_r0n0c1 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_src13_pfx3 Plan_src13_r0n0c1_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX118_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX119_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX120_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.Cert_src13_shX121_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX118 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX119 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX120 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_src13_3.HS_src13_shX121.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_src13_r0n0c1 : htab := [(118%nat, (HS_src13_shX118_0, SH_src13_shX118_0)); (119%nat, (HS_src13_shX119_0, SH_src13_shX119_0)); (120%nat, (HS_src13_shX120_0, SH_src13_shX120_0)); (121%nat, (HS_src13_shX121_0, SH_src13_shX121_0))].

Definition C_src13_r0n0c1_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,0,0)].
Definition SH_src13_r0n0c1_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 121) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 120) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 119) (SHole 118)))).
Definition FUEL_src13_r0n0c1_0 : nat := 3000.
Lemma cert_src13_r0n0c1_0 : seg_check IP_src13 ITm_src13 SG_src13 FUEL_src13_r0n0c1_0 (hs_of HT_src13_r0n0c1) HS_src13_pfx3_0 C_src13_r0n0c1_0 P_src13_r0n0c1_0 = COk SH_src13_r0n0c1_0.
Proof. cert_vm (COk SH_src13_r0n0c1_0). Qed.
End Cert_src13_r0n0c1_0.
