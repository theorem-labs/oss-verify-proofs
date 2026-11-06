(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import RepEcp EcpCurves.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_ecp_defs () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.EcpCurves.c1_P"; "OSSVerify.KrLib.Spec.EcpCurves.c2_P"; "OSSVerify.KrLib.Spec.EcpCurves.c3_P"; "OSSVerify.KrLib.Spec.EcpCurves.c4_P"; "OSSVerify.KrLib.Spec.EcpCurves.c5_P"; "OSSVerify.KrLib.Spec.EcpCurves.c9_P"; "OSSVerify.KrLib.Spec.EcpCurves.c10_P"; "OSSVerify.KrLib.Spec.EcpCurves.c11_P"; "OSSVerify.KrLib.Spec.EcpCurves.c12_P"; "OSSVerify.KrLib.Spec.EcpCurves.c13_P"; "Corelib.Init.Datatypes.nil"].


Definition A_MT : list modp_ent := ltac2:(CDefT.buildp (gd_tbl_A_ecp_defs ()) "(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=1::4.(5.$2.(3.(4.&40.))+270<0.$6.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=1><<.(5.$2.(3.(4.&40.))+27200.$7.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=22;8.(5.$2.(3.(4.&40.))+27340.$8.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=2840.(5.$2.(3.(4.&40.))+27480.$9.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=303<.(5.$2.(3.(4.&40.))+27660.$:.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=3=;<.(5.$2.(3.(4.&40.))+322<0.$;.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=3198.(5.$2.(3.(4.&40.))+278>0.$<.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=35:8.(5.$2.(3.(4.&40.))+27:20.$=.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=39;4.(5.$2.(3.(4.&40.))+27;60.$>.))(0.(1.$2.(1.$2.(3.(4.&40.))))(5.$2.(1.$2.(3.(4.&40.)))+=40:<.(5.$2.(3.(4.&40.))+32340.$?.))(10.(1.$2.(1.$2.(3.(4.&40.)))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_ONE : Z := 0x282a0.   (* [comment removed for export] *)
Definition A_CA (id : Z) : curve_addrs :=
  match id with
  | 1 => mkCA 0x270c0 0x0 0x27100 0x27140 0x27180 0x271c0 0xd1aa4 0xef0c0
  | 2 => mkCA 0x27200 0x0 0x27240 0x27280 0x272c0 0x27300 0xd1ecc 0xef480
  | 3 => mkCA 0x27340 0x0 0x27380 0x273c0 0x27400 0x27440 0xd22b8 0xef840
  | 4 => mkCA 0x27480 0x0 0x274e0 0x27540 0x275a0 0x27600 0xd2840 0xefc00
  | 5 => mkCA 0x27660 0x0 0x276e0 0x27760 0x277e0 0x27860 0xd303c 0xf0380
  | 6 => mkCA 0x27ca0 0x27ce0 0x27d20 0x27d60 0x27da0 0x27de0 0x0 0xf1640
  | 7 => mkCA 0x27e20 0x27e80 0x27ee0 0x27f40 0x27fa0 0x28000 0x0 0xf1a00
  | 8 => mkCA 0x28060 0x280c0 0x28120 0x28180 0x281e0 0x28240 0x0 0xf2180
  | 9 => mkCA 0x322c0 0x0 0x0 0x0 0x0 0x32300 0xd3dbc 0x0
  | 10 => mkCA 0x278e0 0x27920 0x27940 0x27960 0x279a0 0x279e0 0xd3198 0xf0b00
  | 11 => mkCA 0x27a20 0x27a60 0x27a80 0x27aa0 0x27ae0 0x27b20 0xd35a8 0xf0ec0
  | 12 => mkCA 0x27b60 0x27ba0 0x27bc0 0x27be0 0x27c20 0x27c60 0xd39b4 0xf1280
  | 13 => mkCA 0x32340 0x0 0x0 0x0 0x0 0x323a0 0xd40ac 0x0
  | _ => mkCA 0 0 0 0 0 0 0 0 end.
Definition A_GL_JT : Z := 0x2708c.   (* [comment removed for export] *)
Definition A_GL_CASE1 : Z := 0xce0e8.
Definition A_GL_CASE2 : Z := 0xcf93c.
Definition A_GL_CASE3 : Z := 0xcefa0.
Definition A_GL_CASE4 : Z := 0xcf2c0.
Definition A_GL_CASE5 : Z := 0xce784.
Definition A_GL_CASE6 : Z := 0xcfc58.
Definition A_GL_CASE7 : Z := 0xcffcc.
Definition A_GL_CASE8 : Z := 0xcf5e0.
Definition A_GL_CASE9 : Z := 0xd06b0.
Definition A_GL_CASE10 : Z := 0xcec24.
Definition A_GL_CASE11 : Z := 0xd0328.
Definition A_GL_CASE12 : Z := 0xce408.
Definition A_GL_CASE13 : Z := 0xceaa4.
