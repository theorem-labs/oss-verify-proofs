(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition olcc_23720 : cchunk := mkChunk 200%positive 0x23720 35 [
  Some 0xff010113; Some 0x00113423; Some 0x00813023; None; Some 0x02050863; Some 0x00456603; Some 0x01056683; Some 0x03853583;
  Some 0x02c68633; Some 0x00261613; Some 0x00050413; Some 0x00058513; Some 0x00000593; None; Some 0x00040513; Some 0x0400006f;
  None; None; Some 0x00052503; Some 0x00500593; Some 0x02a5c463; None; None; None;
  None; Some 0x00000613; Some 0x00813083; Some 0x00013403; Some 0x01010113; None; Some 0x00000513; Some 0x00813083;
  Some 0x00013403; Some 0x01010113; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_237ac : cchunk := mkChunk 210%positive 0x237ac 79 [
  Some 0xfd010113; Some 0x02113423; Some 0x02813023; Some 0x00913c23; Some 0x01213823; Some 0x00058493; None; Some 0x02050e63;
  Some 0x00050413; Some 0x01052503; None; None; Some 0x00093583; Some 0x02a48533; Some 0x00251513; Some 0x000580e7;
  Some 0x04050c63; Some 0x02a43c23; Some 0x00040513; Some 0x00000593; None; Some 0x0cc0006f; None; None;
  Some 0x00052503; Some 0x00500593; Some 0x0aa5ca63; None; None; None; None; Some 0x00000613;
  Some 0x02813083; Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x03010113; None; Some 0x01440513; Some 0xfff00593;
  Some 0x06b5252f; Some 0x00100593; Some 0x04b51063; Some 0x03843503; Some 0x00050663; Some 0x00893583; Some 0x000580e7; Some 0x02843503;
  Some 0x00050463; None; Some 0x03043503; Some 0x00a13423; Some 0x00050863; Some 0x00810513; None; Some 0x02043823;
  Some 0x00040513; None; None; None; Some 0x00052503; Some 0x00500593; Some 0x02a5c263; None;
  None; None; None; Some 0x00000613; None; Some 0x00050413; Some 0x0080006f; Some 0x00000413;
  Some 0x00040513; Some 0x02813083; Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x03010113; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_238e8 : cchunk := mkChunk 211%positive 0x238e8 191 [
  Some 0xfd010113; Some 0x02113423; Some 0x02813023; Some 0x00913c23; Some 0x01213823; Some 0x01313423; Some 0x01413023; Some 0x02000693;
  Some 0x14c6ea63; Some 0x101016b7; Some 0x00469693; Some 0x11668693; Some 0x00c6d6b3; Some 0x0016f693; Some 0x12068e63; Some 0x06a05a63;
  Some 0x08b05c63; Some 0x02a606b3; Some 0x20000737; Some 0xfe17071b; Some 0x0ae6e863; None; None; Some 0x00042683;
  Some 0x00500493; Some 0x1ed4c663; None; None; None; None; Some 0x00050793; Some 0x00068513;
  Some 0x00058693; Some 0x00070593; Some 0x00060713; Some 0x00078613; None; Some 0x00042503; Some 0x1aa4cc63; None;
  None; None; None; Some 0x0ec0006f; None; None; Some 0x00052503; Some 0x00500593;
  Some 0x18a5c863; None; None; None; None; Some 0x0c40006f; None; None;
  Some 0x00052503; Some 0x00500593; Some 0x16a5c463; None; None; None; None; Some 0x09c0006f;
  Some 0x01f68693; Some 0x0056d413; Some 0x02b406b3; Some 0x00269693; Some 0x01f6d713; Some 0x0a070463; None; None;
  Some 0x00042683; Some 0x00500493; Some 0x12d4c463; None; None; None; None; Some 0x00050793;
  Some 0x00068513; Some 0x00058693; Some 0x00070593; Some 0x00060713; Some 0x00078613; None; Some 0x00042503; Some 0x0ea4ca63;
  None; None; None; None; Some 0x0280006f; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x0ca5c663; None; None; None; None; Some 0x00000613; Some 0x02813083;
  Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x00813983; Some 0x00013a03; Some 0x03010113; None; Some 0x04000737;
  Some 0x0017071b; Some 0x02e6e663; None; None; Some 0x00052503; Some 0x00500593; Some 0x06a5cc63; None;
  None; None; None; Some 0x0600006f; Some 0x000056b7; Some 0xe216869b; Some 0x02d56663; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x04a5c263; None; None; None; None;
  Some 0x02c0006f; Some 0x04d5e863; None; None; Some 0x00052503; Some 0x00500593; Some 0x00a5cc63; None;
  None; None; None; None; Some 0x00000513; Some 0x02813083; Some 0x02013403; Some 0x01813483;
  Some 0x01013903; Some 0x00813983; Some 0x00013a03; Some 0x03010113; Some 0x00008067; Some 0x00050993; Some 0x00058913; Some 0x00060a13;
  Some 0x00100513; Some 0x04000593; Some 0x00100493; None; Some 0x02050463; Some 0xfe8a059b; Some 0xff75f593; Some 0x01352023;
  Some 0x01252223; Some 0x01452423; Some 0x00852823; Some 0x02058a63; Some 0x00100593; Some 0x0300006f; None; None;
  Some 0x00052503; Some 0x00500593; Some 0xf8a5c4e3; None; None; None; None; Some 0xebdff06f;
  Some 0x00300593; Some 0x00b52623; Some 0x0310000f; Some 0x00952a23; Some 0x0330000f; Some 0x02052023; Some 0xf5dff06f].
(* [comment removed for export] *)
Definition olcc_23be4 : cchunk := mkChunk 212%positive 0x23be4 16 [
  Some 0x00050663; Some 0x01052503; Some 0x00008067; None; None; Some 0x00052503; Some 0x00500593; Some 0x00a5ce63;
  None; None; None; None; Some 0x00000613; None; Some 0x00000513; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_23c24 : cchunk := mkChunk 213%positive 0x23c24 51 [
  Some 0xfe010113; Some 0x00113c23; Some 0x00813823; Some 0x00913423; Some 0x06050863; Some 0x00053403; Some 0x0a040063; Some 0x01440593;
  Some 0xfff00613; Some 0x06c5a5af; Some 0x00100613; Some 0x04c59663; Some 0x00050493; Some 0x03843503; Some 0x00050863; None;
  None; Some 0x000580e7; Some 0x02843503; Some 0x00050463; None; Some 0x03043503; Some 0x00a13023; Some 0x00050863;
  Some 0x00010513; None; Some 0x02043823; Some 0x00040513; None; Some 0x00048513; Some 0x00053023; Some 0x03c0006f;
  None; None; Some 0x00052503; Some 0x00400593; Some 0x02a5c463; None; None; None;
  None; Some 0x01813083; Some 0x01013403; Some 0x00813483; Some 0x02010113; None; Some 0x01813083; Some 0x01013403;
  Some 0x00813483; Some 0x02010113; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_23cf0 : cchunk := mkChunk 201%positive 0x23cf0 32 [
  Some 0x00058463; Some 0x0005a023; Some 0x00060463; Some 0x00062023; Some 0x00068463; Some 0x0006a023; Some 0x02050a63; Some 0x00058663;
  Some 0x00052703; Some 0x00e5a023; Some 0x00060663; Some 0x00452583; Some 0x00b62023; Some 0x00000593; Some 0x00068663; Some 0x00852503;
  Some 0x00a6a023; Some 0x00058513; Some 0x00008067; None; None; Some 0x00052503; Some 0x00500593; Some 0x00a5ce63;
  None; None; None; None; Some 0x00100613; None; Some 0x00100513; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_23d70 : cchunk := mkChunk 202%positive 0x23d70 57 [
  Some 0xfd010113; Some 0x02113423; Some 0x02813023; Some 0x00913c23; Some 0x04050863; Some 0x04058263; Some 0x03053603; Some 0x00c13823;
  Some 0x00060e63; Some 0x00050413; Some 0x01010513; Some 0x00058493; None; Some 0x00040513; Some 0x00048593; Some 0x02b53823;
  Some 0x00c10613; Some 0x00058513; Some 0x00000593; None; Some 0x00c12503; Some 0x04050463; Some 0x00000513; Some 0x0740006f;
  None; None; Some 0x00052503; Some 0x00500593; Some 0x04a5ce63; None; None; None;
  None; Some 0x00100613; Some 0x02813083; Some 0x02013403; Some 0x01813483; Some 0x03010113; None; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x02a5c063; None; None; None; None;
  Some 0x00100613; None; Some 0x0080006f; Some 0x00100513; Some 0x02813083; Some 0x02013403; Some 0x01813483; Some 0x03010113;
  Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_23e54 : cchunk := mkChunk 203%positive 0x23e54 16 [
  Some 0x00050663; Some 0x00452503; Some 0x00008067; None; None; Some 0x00052503; Some 0x00500593; Some 0x00a5ce63;
  None; None; None; None; Some 0x00000613; None; Some 0x00000513; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_23e94 : cchunk := mkChunk 204%positive 0x23e94 16 [
  Some 0x00050663; Some 0x00852503; Some 0x00008067; None; None; Some 0x00052503; Some 0x00500593; Some 0x00a5ce63;
  None; None; None; None; Some 0x00000613; None; Some 0x00000513; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_23ed4 : cchunk := mkChunk 214%positive 0x23ed4 16 [
  Some 0x00050663; Some 0x03853503; Some 0x00008067; None; None; Some 0x00052503; Some 0x00500593; Some 0x00a5ce63;
  None; None; None; None; Some 0x00000613; None; Some 0x00000513; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_23f14 : cchunk := mkChunk 205%positive 0x23f14 16 [
  Some 0x00050663; Some 0x00052503; Some 0x00008067; None; None; Some 0x00052503; Some 0x00500593; Some 0x00a5ce63;
  None; None; None; None; Some 0x00000613; None; Some 0x00000513; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_23f9c : cchunk := mkChunk 206%positive 0x23f9c 95 [
  Some 0xfd010113; Some 0x02113423; Some 0x02813023; Some 0x00913c23; Some 0x01213823; Some 0x06050063; Some 0x00050493; Some 0x00058913;
  Some 0x00c10593; Some 0x00810613; Some 0x00410693; None; Some 0x00412503; Some 0x02000593; Some 0x12b50463; Some 0x01800593;
  Some 0x06b51e63; None; None; Some 0x00052583; Some 0x00300613; Some 0x00100513; Some 0x10b64663; None;
  None; None; None; None; Some 0x0440006f; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x02a5c863; None; None; None; None; Some 0x00100613; Some 0x02813083;
  Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x03010113; None; Some 0x00100513; Some 0x0ac0006f; Some 0x00048513;
  None; Some 0x00050413; Some 0x00048513; None; Some 0x00c12583; Some 0x00412603; Some 0x02b605b3; Some 0x43f5d613;
  Some 0x03b65613; Some 0x00c58633; Some 0xfe067693; Some 0x40d586b3; Some 0x06068863; Some 0x00812583; Some 0x06b05463; Some 0x00000593;
  Some 0x02000713; Some 0x40d70733; None; None; Some 0x00271713; Some 0x00e686b3; Some 0x40565713; Some 0x0006a603;
  Some 0x0007071b; Some 0x00271713; Some 0x00e40433; Some 0xfff64693; Some 0x00251513; Some 0x01c0006f; Some 0x00c76733; Some 0x00e42023;
  Some 0x00812703; Some 0x00158593; Some 0x00a40433; Some 0x00e5da63; Some 0x00042703; Some 0xfe0912e3; Some 0x00d77733; Some 0xfe1ff06f;
  Some 0x00000513; Some 0x02813083; Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x03010113; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_24118 : cchunk := mkChunk 207%positive 0x24118 191 [
  Some 0xfd010113; Some 0x02113423; Some 0x02813023; Some 0x00913c23; Some 0x01213823; Some 0x01313423; Some 0x08060e63; Some 0x00062023;
  Some 0x0a050e63; Some 0x00053683; Some 0x0c068e63; Some 0x00852403; Some 0x00800693; Some 0x1886ec63; Some 0x11600693; Some 0x0086d6b3;
  Some 0x0016f693; Some 0x18068463; Some 0x00050913; Some 0x00c52683; Some 0x00100513; Some 0x0085173b; Some 0x10e69863; Some 0x01092703;
  Some 0x12074c63; Some 0x12e6ca63; Some 0x24058c63; Some 0x00060993; Some 0x00058493; Some 0x00058513; None; Some 0x00900593;
  Some 0x00050693; Some 0x18b54063; None; None; Some 0x00052503; Some 0x00500593; Some 0x0aa5c863; None;
  None; None; None; Some 0x00068613; Some 0x1480006f; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x08a5c263; None; None; None; None; Some 0x0500006f; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x04a5ce63; None; None; None; None;
  Some 0x0280006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x02a5ca63; None; None;
  None; None; Some 0x00100613; Some 0x02813083; Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x00813983;
  Some 0x03010113; None; Some 0x00100513; Some 0x02813083; Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x00813983;
  Some 0x03010113; Some 0x00008067; None; None; Some 0x0005a583; Some 0x00500613; Some 0xfcb64ae3; None;
  None; None; None; Some 0x00068613; Some 0x00040693; Some 0x02c0006f; None; None;
  Some 0x0005a583; Some 0x00500613; Some 0xfab642e3; None; None; None; None; Some 0x00070613;
  None; Some 0x00100513; Some 0xf85ff06f; None; None; Some 0x00052583; Some 0x00500613; Some 0x00100513;
  Some 0xf6b646e3; None; None; None; None; Some 0x00040613; None; Some 0x00100513;
  Some 0xf4dff06f; Some 0x00100513; Some 0x02d45663; None; None; Some 0x0005a583; Some 0x00500613; Some 0xf2b648e3;
  None; None; None; None; Some 0xf5dff06f; Some 0x01092603; Some 0x02c05c63; Some 0x00d516bb;
  Some 0x06c6f263; None; None; Some 0x00052583; Some 0x00500713; Some 0x00100513; Some 0xeeb74ae3; None;
  None; None; None; Some 0xf55ff06f; None; None; Some 0x00052583; Some 0x00500613;
  Some 0x00100513; Some 0xecb644e3; None; None; None; None; None; Some 0x00100513;
  Some 0xeadff06f; Some 0x00410593; Some 0x00048513; None; Some 0x00412703; Some 0x01092683; Some 0x00098613; Some 0x00d75a63;
  Some 0x00000513; Some 0x00100593; Some 0x00b62023; Some 0xe81ff06f; None; None; Some 0x00052583; Some 0x00500613;
  Some 0x00100513; Some 0xe6b644e3; None; None; None; None; Some 0xec5ff06f].
(* [comment removed for export] *)
Definition olcc_24414 : cchunk := mkChunk 215%positive 0x24414 33 [
  Some 0xfe010113; Some 0x00113c23; Some 0x00813823; Some 0x00913423; Some 0x02050463; Some 0x00050413; Some 0x00053483; Some 0x04048a63;
  Some 0x0004b503; None; Some 0x00048513; None; Some 0x00043023; Some 0x03c0006f; None; None;
  Some 0x00052503; Some 0x00400593; Some 0x02a5c463; None; None; None; None; Some 0x01813083;
  Some 0x01013403; Some 0x00813483; Some 0x02010113; None; Some 0x01813083; Some 0x01013403; Some 0x00813483; Some 0x02010113;
  Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_24498 : cchunk := mkChunk 208%positive 0x24498 143 [
  Some 0xfb010113; Some 0x04113423; Some 0x04813023; Some 0x02913c23; Some 0x03213823; Some 0x03313423; Some 0x03413023; Some 0x01513c23;
  Some 0x01613823; Some 0x01713423; Some 0x01813023; Some 0x02050a63; Some 0x00058413; Some 0xffb5859b; Some 0xffd00693; Some 0x04b6e263;
  None; None; Some 0x00052503; Some 0x00600593; Some 0x0ab55a63; None; None; Some 0x06c0006f;
  None; None; Some 0x00052503; Some 0x00600593; Some 0x08b55a63; None; None; Some 0x04c0006f;
  Some 0x02c05663; Some 0x10100593; Some 0x0ab66a63; None; None; Some 0x00052503; Some 0x00600593; Some 0x06b55463;
  None; None; Some 0x0200006f; None; None; Some 0x00052503; Some 0x00600593; Some 0x04b55463;
  None; None; None; None; Some 0x00000613; Some 0x04813083; Some 0x04013403; Some 0x03813483;
  Some 0x03013903; Some 0x02813983; Some 0x02013a03; Some 0x01813a83; Some 0x01013b03; Some 0x00813b83; Some 0x00013c03; Some 0x05010113;
  None; Some 0x00000493; Some 0x00048513; Some 0x04813083; Some 0x04013403; Some 0x03813483; Some 0x03013903; Some 0x02813983;
  Some 0x02013a03; Some 0x01813a83; Some 0x01013b03; Some 0x00813b83; Some 0x00013c03; Some 0x05010113; Some 0x00008067; Some 0x00050a93;
  Some 0x01000593; Some 0x00c5f663; Some 0x00800913; Some 0x0180006f; Some 0x00400913; Some 0x00c96863; Some 0x00363513; Some 0x00154913;
  Some 0x00190913; Some 0x00100513; Some 0x01800593; Some 0x00100993; Some 0x00060b13; None; Some 0x00050493; Some 0x0129953b;
  Some 0x0124a423; Some 0x00a4a623; Some 0x00400593; Some 0x00400a13; None; Some 0x00a4b023; Some 0x0004a823; Some 0x020b1513;
  Some 0x003a8a93; None; Some 0x00500b13; Some 0x02055b93; None; None; None; None;
  None; Some 0x0400006f; Some 0x0004b603; Some 0xffdac683; Some 0xffeac703; Some 0xfffac783; Some 0x00259813; Some 0x00158593;
  Some 0x01060633; Some 0x00f60023; Some 0x00e600a3; Some 0x00d60123; Some 0x00a601a3; Some 0x00b4a823; Some 0xfffb8b93; Some 0x008a8ab3;
  Some 0xf00b84e3; Some 0x01441663; Some 0x000ac503; Some 0x0080006f; Some 0x0ff00513; Some 0x00c4a603; Some 0x0104a583; Some 0xfac5c6e3;
  Some 0x000c2503; Some 0xfcab4ae3; Some 0x00100613; Some 0x00090513; Some 0x00098593; None; Some 0xfc1ff06f].
(* [comment removed for export] *)
Definition olcc_246d4 : cchunk := mkChunk 216%positive 0x246d4 178 [
  Some 0xfb010113; Some 0x04113423; Some 0x04813023; Some 0x02913c23; Some 0x03213823; Some 0x03313423; Some 0x03413023; Some 0x01513c23;
  Some 0x08058263; Some 0x00050493; Some 0x0005a023; Some 0x0a050063; Some 0x00058913; Some 0x01410593; Some 0x01010613; Some 0x00c10693;
  Some 0x00048513; None; Some 0x00c12503; Some 0x00800593; Some 0x20a5e663; Some 0x11600593; Some 0x00a5d533; Some 0x00157513;
  Some 0x1e050e63; Some 0x00048513; None; Some 0x00050413; Some 0x00048513; None; Some 0x00c16283; Some 0x00100593;
  Some 0x08b29c63; Some 0x00810593; Some 0x00048513; None; Some 0x00000513; Some 0x00812583; Some 0x0015b593; Some 0x00b92023;
  Some 0x2040006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x1ca5cc63; None; None;
  None; None; Some 0x0280006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x1aa5c863;
  None; None; None; None; Some 0x00100613; Some 0x04813083; Some 0x04013403; Some 0x03813483;
  Some 0x03013903; Some 0x02813983; Some 0x02013a03; Some 0x01813a83; Some 0x05010113; None; Some 0x01012583; Some 0x16b05c63;
  Some 0x00000613; Some 0x00000f93; Some 0x0002869b; Some 0xfff00313; Some 0x01416e03; Some 0x00241713; Some 0x00200793; Some 0xfff00813;
  Some 0x00400893; Some 0x0053133b; Some 0x000e039b; Some 0x01c50e33; Some 0x00800e93; Some 0x00050f13; Some 0x00090293; Some 0x028604b3;
  Some 0x00249493; Some 0x009504b3; Some 0x08f68663; Some 0x03168c63; Some 0x0dd69a63; Some 0x0c705863; Some 0x02c704b3; Some 0x009e04b3;
  Some 0x000f0913; Some 0x00c0006f; Some 0x00190913; Some 0x0a990c63; Some 0x00394993; Some 0x0009c983; Some 0xfff9c8e3; Some 0x00098f93;
  Some 0xfe9ff06f; Some 0x0a705063; Some 0x00000913; Some 0x00000993; Some 0x000f8a13; Some 0x0140006f; Some 0x0019899b; Some 0x00490913;
  Some 0x000f8a13; Some 0x09338063; Some 0x0039df9b; Some 0x002f9f93; Some 0x01f48fb3; Some 0x000faf83; Some 0xfff94a93; Some 0x01cafa93;
  Some 0x015fdfbb; Some 0x00ffff93; Some 0xfdfa48e3; Some 0x000a0f93; Some 0xfc9ff06f; Some 0x04705863; Some 0x00000913; Some 0x00000993;
  Some 0x000f8a13; Some 0x0140006f; Some 0x0019899b; Some 0x00290913; Some 0x000f8a13; Some 0x03338863; Some 0x0049df9b; Some 0x002f9f93;
  Some 0x01f48fb3; Some 0x000faf83; Some 0xfff94a93; Some 0x01eafa93; Some 0x015fdfbb; Some 0x003fff93; Some 0xfdfa48e3; Some 0x000a0f93;
  Some 0xfc9ff06f; Some 0x006fc4b3; Some 0x05048a63; Some 0x00160613; Some 0x00ef0f33; Some 0xf0b614e3; Some 0x0440006f; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x02a5c063; None; None; None; None;
  Some 0x00100613; None; Some 0x01c0006f; Some 0x00100513; Some 0x0140006f; Some 0x00000f93; Some 0x00090293; Some 0x00000513;
  Some 0x01f2a023; Some 0x04813083; Some 0x04013403; Some 0x03813483; Some 0x03013903; Some 0x02813983; Some 0x02013a03; Some 0x01813a83;
  Some 0x05010113; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_2499c : cchunk := mkChunk 217%positive 0x2499c 98 [
  Some 0xfc010113; Some 0x02113c23; Some 0x02813823; Some 0x02913423; Some 0x03213023; Some 0x01313c23; Some 0x01413823; Some 0x01513423;
  Some 0x0c058063; Some 0x00050913; Some 0x00100513; Some 0x00a5a023; Some 0x0c090c63; Some 0x00058a93; Some 0x00090513; None;
  Some 0x00050993; Some 0x00090513; None; Some 0x00050a13; Some 0x00090513; None; Some 0x00050413; Some 0x00090513;
  None; Some 0x00050493; Some 0x00090513; None; Some 0x06805463; Some 0x00000593; Some 0x033a063b; Some 0x02000693;
  Some 0x41f6579b; Some 0x01f67713; Some 0x01b7d79b; Some 0x00f607b3; Some 0x4057d79b; Some 0x40e68833; Some 0x029588b3; Some 0x00289893;
  Some 0x011508b3; Some 0x00d64e63; Some 0x00078293; Some 0x0008a303; Some 0x0a031263; Some 0xfff2829b; Some 0x00488893; Some 0xfe0298e3;
  Some 0x00070863; Some 0x0008a883; Some 0x0108d8bb; Some 0x08089463; Some 0x00158593; Some 0xfc8592e3; Some 0x00000513; Some 0x0880006f;
  None; None; Some 0x00052503; Some 0x00500593; Some 0x06a5c863; None; None; None;
  None; Some 0x0280006f; None; None; Some 0x0005a583; Some 0x00500613; Some 0x04b64663; None;
  None; None; None; Some 0x00100613; Some 0x03813083; Some 0x03013403; Some 0x02813483; Some 0x02013903;
  Some 0x01813983; Some 0x01013a03; Some 0x00813a83; Some 0x04010113; None; Some 0x00000513; Some 0x000aa023; Some 0x0080006f;
  Some 0x00100513; Some 0x03813083; Some 0x03013403; Some 0x02813483; Some 0x02013903; Some 0x01813983; Some 0x01013a03; Some 0x00813a83;
  Some 0x04010113; Some 0x00008067].
(* [comment removed for export] *)
Definition olcc_24b94 : cchunk := mkChunk 209%positive 0x24b94 275 [
  Some 0xf9010113; Some 0x06113423; Some 0x06813023; Some 0x04913c23; Some 0x05213823; Some 0x05313423; Some 0x05413023; Some 0x03513c23;
  Some 0x03613823; Some 0x03713423; Some 0x03813023; Some 0x01913c23; Some 0x04050463; Some 0x80000637; Some 0x00c586b3; Some 0x01b6061b;
  Some 0x06d66063; None; None; Some 0x00052503; Some 0x00500613; Some 0x3ca64063; None; None;
  None; None; Some 0x00058613; Some 0x00068593; None; Some 0x3a00006f; None; None;
  Some 0x00052503; Some 0x00500593; Some 0x38a5c663; None; None; None; None; Some 0x0940006f;
  Some 0x00054603; Some 0x07300693; Some 0x06d61263; Some 0x00154603; Some 0x07000693; Some 0x04d61c63; Some 0x00254603; Some 0x06900693;
  Some 0x04d61663; Some 0x00354603; Some 0x07800693; Some 0x04d61063; Some 0x00452483; Some 0xfff0c637; Some 0xdbf6061b; Some 0x00c486bb;
  Some 0x08d66463; None; None; Some 0x00052503; Some 0x00500593; Some 0x32a5c063; None; None;
  None; None; Some 0x0280006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x2ea5cc63;
  None; None; None; None; Some 0x00000613; Some 0x06813083; Some 0x06013403; Some 0x05813483;
  Some 0x05013903; Some 0x04813983; Some 0x04013a03; Some 0x03813a83; Some 0x03013b03; Some 0x02813b83; Some 0x02013c03; Some 0x01813c83;
  Some 0x07010113; None; Some 0x00852903; Some 0x00c906bb; Some 0x02d66663; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x28a5c863; None; None; None; None; Some 0xf99ff06f; Some 0x02990633;
  Some 0x17d786b7; Some 0x4016869b; Some 0x02d66663; None; None; Some 0x00052503; Some 0x00500593; Some 0x24a5cc63;
  None; None; None; None; Some 0xf61ff06f; Some 0x01456b83; Some 0x10000613; Some 0x0f766063;
  Some 0x007b8613; Some 0x0025d693; Some 0x0cd67a63; Some 0x00058413; Some 0x00050c93; Some 0x00c52a03; Some 0x00048513; Some 0x00090593;
  Some 0x000a0613; None; Some 0x00a13423; Some 0x0c050c63; Some 0x000b899b; None; Some 0x002b9593; Some 0x00299c13;
  Some 0x40b40b3b; Some 0x018c8c33; Some 0x018c2a83; Some 0x02a90533; Some 0x0025141b; Some 0xfe4b0b1b; Some 0x00810513; None;
  Some 0x0d641663; Some 0x0d541463; Some 0x00048513; Some 0x00090593; Some 0x000a0613; None; Some 0x00a13023; Some 0x0e050463;
  Some 0x100b8663; Some 0x018c8513; Some 0x00400593; Some 0x00098613; None; Some 0x10050063; Some 0x00050493; Some 0x00013503;
  Some 0x00048593; None; Some 0x10050e63; Some 0x00010513; None; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x16a5c863; None; None; None; None; Some 0x1500006f; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x14a5c463; None; None; None; None;
  Some 0xe51ff06f; None; None; Some 0x00052503; Some 0x00500593; Some 0x12a5c063; None; None;
  None; None; Some 0xe29ff06f; None; None; Some 0x00052503; Some 0x00500593; Some 0x0ea5cc63;
  None; None; None; None; Some 0x00040613; Some 0x000b0693; Some 0x000a8713; None;
  Some 0x0d40006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x0ca5c063; None; None;
  None; None; Some 0x0a00006f; Some 0x00000493; Some 0x0380006f; Some 0x00010513; None; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x08a5c463; None; None; None; None;
  Some 0x0680006f; Some 0x00013503; None; Some 0x01cc0593; Some 0x00040613; None; Some 0x000b8e63; Some 0x00013583;
  Some 0x01410613; Some 0x00048513; None; Some 0x01412503; Some 0x00050663; Some 0x00013503; Some 0x0400006f; Some 0x00010513;
  None; None; None; Some 0x00052503; Some 0x00500593; Some 0x02a5c063; None; None;
  None; None; Some 0x00000613; None; Some 0x0080006f; Some 0x00000513; Some 0x06813083; Some 0x06013403;
  Some 0x05813483; Some 0x05013903; Some 0x04813983; Some 0x04013a03; Some 0x03813a83; Some 0x03013b03; Some 0x02813b83; Some 0x02013c03;
  Some 0x01813c83; Some 0x07010113; Some 0x00008067].

Definition canon_code_OL : list cchunk := [
  olcc_23720; olcc_237ac; olcc_238e8; olcc_23be4; olcc_23c24; olcc_23cf0; olcc_23d70; olcc_23e54;
  olcc_23e94; olcc_23ed4; olcc_23f14; olcc_23f9c; olcc_24118; olcc_24414; olcc_24498; olcc_246d4;
  olcc_2499c; olcc_24b94].

Class RelocCodeOL (RL : Reloc) := { rl_code_ol_ok : code_check rl_segs rl_delta canon_code_OL = true }.

Lemma rl_fetch_at_OL : forall {RL : Reloc} {RC : RelocCodeOL RL} (i : nat) (ch : cchunk) c (w : bv 32),
  nth_error canon_code_OL i = Some ch -> chunk_has ch c (bv_unsigned w) = true ->
  fetch_word rl_segs (rl (rl_delta (cc_blk ch)) c) = Some w.
Proof. intros RL RC i ch c w Hi H. exact (chunk_sound rl_segs rl_delta canon_code_OL i ch c w rl_code_ol_ok Hi H). Qed.

Ltac rl_F_OL i ch :=
  lazymatch goal with
  | |- fetch_word _ (rl _ ?c) = Some ?w =>
      exact (rl_fetch_at_OL i ch c w (@eq_refl _ (Some ch)) ltac:(vm_cast_no_check (@eq_refl bool true)))
  end.
