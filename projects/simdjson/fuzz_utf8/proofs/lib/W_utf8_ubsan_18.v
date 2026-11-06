(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require AxSymExec3 AsanPlan PropExec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require AsanNodesIO AsanMainLib ImgParams MainDefs Img_utf8_ubsan Cert_common ITab_utf8_ubsan Segs_utf8_ubsan HS_utf8_ubsan_pfx3 Sh_utf8_ubsan_3 PlanCodec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
(* [comment removed for export] *)
Module Plan_utf8_ubsan_r0n0c1.   (* [comment removed for export] *)
End Plan_utf8_ubsan_r0n0c1.

Module Plan_utf8_ubsan_r0n0c1_L.   (* [comment removed for export] *)
Import PrimString OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PlanCodec.
Definition P_utf8_ubsan_r0n0c1_0 : AP.plan := PKC.decode_plan "GcK`H`I`J`K`Sa@aDaEaJaLaMaOaPaSaTaVaWa[a]a^b@bAbCbDbGbHbJbNbPbQbSbTbVbWbYbZb]b^c@cDcFcGcIcJcLcMcPcQcScWcYcZc[c^d@dCdFdGdHdIdJdLd\d]eVeWeXeYeZe[e\e]e^f?f@fAfBfCfDfEfFfGfHfIfJfKfLfMfNfOfPfQfRfSfTfUfVfWfXfYfZf[f\f]f^g?g@gAgBgCgDgEgFgGgHgIgJgKgLgMgNgOgPgQgRgSgTgUgVgXgYgZg[g^h@hBhDhEhFhLTQ?d??TN??@mwdGMS????O?@`oe~G?@`oe~G?@`oe~G?@`oe~G??SB???SB???SB???SA???SB???SB???TO??@`os_WU????SB??@mxjG@AHF?GC@?E??@`n{dG?@mweWbmwmW??@`n{dG??N??@`n{dG??N??@`nhu?rbXa|WGa|W@Ra|X@^a|Y?g_?a|Z@La|[?cg_?a|\@Va|]@Wa|^@X??SB???SB???SA???SB???SB???SB??@mxjG@AHF?GC@?EA?@`n{dG?@mweWbmwmW??@`n{dG??N??@`n{dG??N??@`nhu?rbWa|WGa|W@Ra|X@^a|Y?g_?a|Z@La|[?cg_?a|\@Va|]@Wa|^@X??SB???SB???SA???SB???SB???SB??@mxjG@AHF?GC@?EC?@`n{dG?@mweWbmwmW??@`n{dG??N??@`n{dG??N??@`nhu?rbVa|WGa|W@Ra|X@^a|Y?g_?a|Z@La|[?cg_?a|\@Va|]@Wa|^@X??SB???SB???SA???SB???SB???SB??@`n{dG?@mweWbmwmW??@`n{dG??N??@`n{dG??N??@`nhu?rbUa|WGa|W@Ra|X@^a|Y?g_?a|Z@La|[?cg_?a|\@Va|]@Wa|^@X"%pstring.
(* [comment removed for export] *)
End Plan_utf8_ubsan_r0n0c1_L.

Module Cert_utf8_ubsan_r0n0c1_0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.PropExec OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AxSymExec3 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanPlan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanNodesIO OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.AsanMainLib OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.ImgParams OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.MainDefs OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Img_utf8_ubsan.
Import OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Cert_common OSSVerify.Proofs.simdjson.fuzz_utf8.lib.ITab_utf8_ubsan OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Segs_utf8_ubsan Plan_utf8_ubsan_r0n0c1 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.HS_utf8_ubsan_pfx3 Plan_utf8_ubsan_r0n0c1_L OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.Cert_utf8_ubsan_shX118_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.Cert_utf8_ubsan_shX119_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.Cert_utf8_ubsan_shX120_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.Cert_utf8_ubsan_shX121_0 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.HS_utf8_ubsan_shX118 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.HS_utf8_ubsan_shX119 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.HS_utf8_ubsan_shX120 OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Sh_utf8_ubsan_3.HS_utf8_ubsan_shX121.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition HT_utf8_ubsan_r0n0c1 : htab := [(118%nat, (HS_utf8_ubsan_shX118_0, SH_utf8_ubsan_shX118_0)); (119%nat, (HS_utf8_ubsan_shX119_0, SH_utf8_ubsan_shX119_0)); (120%nat, (HS_utf8_ubsan_shX120_0, SH_utf8_ubsan_shX120_0)); (121%nat, (HS_utf8_ubsan_shX121_0, SH_utf8_ubsan_shX121_0))].

Definition C_utf8_ubsan_r0n0c1_0 : class := [(QLook,4,4); (QFlen,7,65535); (QCfgLen,1,32767); (QRoom,0,0)].
Definition SH_utf8_ubsan_r0n0c1_0 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SHole 121) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SHole 120) (SCase (EAlu ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SHole 119) (SHole 118)))).
Definition FUEL_utf8_ubsan_r0n0c1_0 : nat := 3000.
Lemma cert_utf8_ubsan_r0n0c1_0 : seg_check IP_utf8_ubsan ITm_utf8_ubsan SG_utf8_ubsan FUEL_utf8_ubsan_r0n0c1_0 (hs_of HT_utf8_ubsan_r0n0c1) HS_utf8_ubsan_pfx3_0 C_utf8_ubsan_r0n0c1_0 P_utf8_ubsan_r0n0c1_0 = COk SH_utf8_ubsan_r0n0c1_0.
Proof. cert_vm (COk SH_utf8_ubsan_r0n0c1_0). Qed.
End Cert_utf8_ubsan_r0n0c1_0.
