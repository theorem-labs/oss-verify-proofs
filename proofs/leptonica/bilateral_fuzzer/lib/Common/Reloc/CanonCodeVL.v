(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition vlcc_237d4 : cchunk := mkChunk 230%positive 0x237d4 41 [
  Some 0xff010113; Some 0x00113423; Some 0x00813023; None; Some 0x04050263; Some 0x00757593; Some 0x08059463; Some 0x01056583;
  Some 0x00456603; Some 0x00259593; Some 0x02c596b3; Some 0x02c58633; Some 0x43f65593; Some 0x06b69663; Some 0x03853583; Some 0x00050413;
  Some 0x00058513; Some 0x00000593; None; Some 0x00040513; Some 0x0400006f; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x02a5c463; None; None; None; None; Some 0x00000613; Some 0x00813083;
  Some 0x00013403; Some 0x01010113; None; Some 0x00000513; Some 0x00813083; Some 0x00013403; Some 0x01010113; Some 0x00008067;
  Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_23878 : cchunk := mkChunk 240%positive 0x23878 82 [
  Some 0xfe010113; Some 0x00113c23; Some 0x00813823; Some 0x00913423; Some 0x00058493; None; Some 0x04050863; Some 0x00050413;
  Some 0x00757513; Some 0x12051063; Some 0x01042503; Some 0x00251513; Some 0x029515b3; Some 0x02950533; Some 0x43f55613; Some 0x10c59463;
  None; None; Some 0x0004b583; Some 0x000580e7; Some 0x04050a63; Some 0x02a43c23; Some 0x00040513; Some 0x00000593;
  None; Some 0x0c80006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x0aa5c863; None;
  None; None; None; Some 0x00000613; Some 0x01813083; Some 0x01013403; Some 0x00813483; Some 0x02010113;
  None; Some 0x01440513; Some 0xfff00593; Some 0x06b5252f; Some 0x00100593; Some 0x04b51063; Some 0x03843503; Some 0x00050663;
  Some 0x0084b583; Some 0x000580e7; Some 0x02843503; Some 0x00050463; None; Some 0x03043503; Some 0x00a13023; Some 0x00050863;
  Some 0x00010513; None; Some 0x02043823; Some 0x00040513; None; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x02a5c263; None; None; None; None; Some 0x00000613; None;
  Some 0x00050413; Some 0x0080006f; Some 0x00000413; Some 0x00040513; Some 0x01813083; Some 0x01013403; Some 0x00813483; Some 0x02010113;
  Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_239c0 : cchunk := mkChunk 241%positive 0x239c0 201 [
  Some 0xfd010113; Some 0x02113423; Some 0x02813023; Some 0x00913c23; Some 0x01213823; Some 0x01313423; Some 0x01413023; Some 0x02000693;
  Some 0x14c6ea63; Some 0x101016b7; Some 0x00469693; Some 0x11668693; Some 0x00c6d6b3; Some 0x0016f693; Some 0x12068e63; Some 0x06a05a63;
  Some 0x08b05c63; Some 0x02a606b3; Some 0x20000737; Some 0xfe17071b; Some 0x0ae6e863; None; None; Some 0x00042683;
  Some 0x00500493; Some 0x1ed4c663; None; None; None; None; Some 0x00050793; Some 0x00068513;
  Some 0x00058693; Some 0x00070593; Some 0x00060713; Some 0x00078613; None; Some 0x00042503; Some 0x1aa4cc63; None;
  None; None; None; Some 0x0ec0006f; None; None; Some 0x00052503; Some 0x00500593;
  Some 0x18a5c863; None; None; None; None; Some 0x0c40006f; None; None;
  Some 0x00052503; Some 0x00500593; Some 0x16a5c463; None; None; None; None; Some 0x09c0006f;
  Some 0x01f68693; Some 0x0056da13; Some 0x02ba06b3; Some 0x00269693; Some 0x01f6d713; Some 0x0a070463; None; None;
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
  Some 0x01013903; Some 0x00813983; Some 0x00013a03; Some 0x03010113; Some 0x00008067; Some 0x00050993; Some 0x00058493; Some 0x00060413;
  Some 0x00100513; Some 0x04000593; None; Some 0x04050863; Some 0x00050913; Some 0x00098593; None; Some 0x00090513;
  Some 0x00048593; None; Some 0x00090513; Some 0x00040593; None; Some 0x00797593; Some 0x06059463; Some 0x00090513;
  Some 0x01492823; Some 0xfe84041b; Some 0xff747413; Some 0x00100593; Some 0x02040a63; Some 0x00100613; Some 0x0300006f; None;
  None; Some 0x00052503; Some 0x00500593; Some 0xf6a5c2e3; None; None; None; None;
  Some 0xe99ff06f; Some 0x00300613; Some 0x00c52623; Some 0x0310000f; Some 0x00b52a23; Some 0x0330000f; Some 0x02052023; Some 0xf39ff06f;
  Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_23ce4 : cchunk := mkChunk 242%positive 0x23ce4 19 [
  Some 0x00050a63; Some 0x00757593; Some 0x04059063; Some 0x01052503; Some 0x00008067; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x00a5ce63; None; None; None; None; Some 0x00000613; None;
  Some 0x00000513; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_23d30 : cchunk := mkChunk 243%positive 0x23d30 56 [
  Some 0xfe010113; Some 0x00113c23; Some 0x00813823; Some 0x00913423; Some 0x08050063; Some 0x00757593; Some 0x0c059263; Some 0x00053403;
  Some 0x0a040463; Some 0x00747593; Some 0x0a059a63; Some 0x01440593; Some 0xfff00613; Some 0x06c5a5af; Some 0x00100613; Some 0x04c59663;
  Some 0x00050493; Some 0x03843503; Some 0x00050863; None; None; Some 0x000580e7; Some 0x02843503; Some 0x00050463;
  None; Some 0x03043503; Some 0x00a13023; Some 0x00050863; Some 0x00010513; None; Some 0x02043823; Some 0x00040513;
  None; Some 0x00048513; Some 0x00053023; Some 0x03c0006f; None; None; Some 0x00052503; Some 0x00400593;
  Some 0x02a5c463; None; None; None; None; Some 0x01813083; Some 0x01013403; Some 0x00813483;
  Some 0x02010113; None; Some 0x01813083; Some 0x01013403; Some 0x00813483; Some 0x02010113; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_23e10 : cchunk := mkChunk 231%positive 0x23e10 47 [
  Some 0x0035f713; Some 0x00058663; Some 0x0a071863; Some 0x0005a023; Some 0x00367793; Some 0x00060663; Some 0x0a079063; Some 0x00062023;
  Some 0x0036f813; Some 0x00068663; Some 0x08081863; Some 0x0006a023; Some 0x04050663; Some 0x00757893; Some 0x00058a63; Some 0x00e8e733;
  Some 0x06071c63; Some 0x00052703; Some 0x00e5a023; Some 0x00060a63; Some 0x00f8e5b3; Some 0x06059263; Some 0x00452583; Some 0x00b62023;
  Some 0x04068463; Some 0x0108e5b3; Some 0x04059863; Some 0x00852503; Some 0x00a6a023; Some 0x00058513; Some 0x00008067; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x02a5c263; None; None; None; None;
  Some 0x00100613; None; Some 0x00000513; Some 0x00008067; Some 0x00100513; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_23ecc : cchunk := mkChunk 232%positive 0x23ecc 60 [
  Some 0xfd010113; Some 0x02113423; Some 0x02813023; Some 0x00913c23; Some 0x04050c63; Some 0x04058663; Some 0x00757613; Some 0x0c061863;
  Some 0x03053603; Some 0x00c13823; Some 0x00060e63; Some 0x00050413; Some 0x01010513; Some 0x00058493; None; Some 0x00040513;
  Some 0x00048593; Some 0x02b53823; Some 0x00c10613; Some 0x00058513; Some 0x00000593; None; Some 0x00c12503; Some 0x04050463;
  Some 0x00000513; Some 0x0740006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x04a5ce63; None;
  None; None; None; Some 0x00100613; Some 0x02813083; Some 0x02013403; Some 0x01813483; Some 0x03010113;
  None; None; None; Some 0x00052503; Some 0x00500593; Some 0x02a5c063; None; None;
  None; None; Some 0x00100613; None; Some 0x0080006f; Some 0x00100513; Some 0x02813083; Some 0x02013403;
  Some 0x01813483; Some 0x03010113; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_23fbc : cchunk := mkChunk 244%positive 0x23fbc 34 [
  Some 0x00050e63; Some 0x00757613; Some 0x0405c063; Some 0x06061c63; Some 0x00b52023; Some 0x00060513; Some 0x00008067; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x04a5c863; None; None; None; None;
  Some 0x00100613; None; Some 0x02061e63; None; None; Some 0x00052023; Some 0x0005a503; Some 0x00500593;
  Some 0x00a5ce63; None; None; None; None; Some 0x00100613; None; Some 0x00100513;
  Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_24044 : cchunk := mkChunk 245%positive 0x24044 34 [
  Some 0x00050e63; Some 0x00757613; Some 0x0405c063; Some 0x06061c63; Some 0x00b52223; Some 0x00060513; Some 0x00008067; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x04a5c863; None; None; None; None;
  Some 0x00100613; None; Some 0x02061e63; None; None; Some 0x0005a583; Some 0x00500613; Some 0x00052223;
  Some 0x00b64e63; None; None; None; None; Some 0x00100613; None; Some 0x00100513;
  Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_240cc : cchunk := mkChunk 246%positive 0x240cc 32 [
  Some 0x00050e63; Some 0x04b05263; Some 0x00757613; Some 0x06061863; Some 0x00b52423; Some 0x00060513; Some 0x00008067; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x04a5c463; None; None; None; None;
  Some 0x00100613; None; None; None; Some 0x00052503; Some 0x00500593; Some 0x00a5ce63; None;
  None; None; None; Some 0x00100613; None; Some 0x00100513; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_2414c : cchunk := mkChunk 233%positive 0x2414c 19 [
  Some 0x00050a63; Some 0x00757593; Some 0x04059063; Some 0x00452503; Some 0x00008067; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x00a5ce63; None; None; None; None; Some 0x00000613; None;
  Some 0x00000513; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_24198 : cchunk := mkChunk 234%positive 0x24198 19 [
  Some 0x00050a63; Some 0x00757593; Some 0x04059063; Some 0x00852503; Some 0x00008067; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x00a5ce63; None; None; None; None; Some 0x00000613; None;
  Some 0x00000513; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_241e4 : cchunk := mkChunk 247%positive 0x241e4 19 [
  Some 0x00050a63; Some 0x00757593; Some 0x04059063; Some 0x03853503; Some 0x00008067; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x00a5ce63; None; None; None; None; Some 0x00000613; None;
  Some 0x00000513; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_24230 : cchunk := mkChunk 235%positive 0x24230 19 [
  Some 0x00050a63; Some 0x00757593; Some 0x04059063; Some 0x00052503; Some 0x00008067; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x00a5ce63; None; None; None; None; Some 0x00000613; None;
  Some 0x00000513; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_242cc : cchunk := mkChunk 236%positive 0x242cc 124 [
  Some 0xfd010113; Some 0x02113423; Some 0x02813023; Some 0x00913c23; Some 0x01213823; Some 0x06050063; Some 0x00058413; Some 0x00050913;
  Some 0x00c10593; Some 0x00810613; Some 0x00410693; None; Some 0x00412503; Some 0x02000593; Some 0x18b50c63; Some 0x01800593;
  Some 0x06b51e63; None; None; Some 0x00052583; Some 0x00300613; Some 0x00100513; Some 0x16b64e63; None;
  None; None; None; None; Some 0x0440006f; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x02a5c863; None; None; None; None; Some 0x00100613; Some 0x02813083;
  Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x03010113; None; Some 0x00100513; Some 0x11c0006f; Some 0x00090513;
  None; Some 0x00050493; Some 0x00090513; None; Some 0x00c12583; Some 0x00412603; Some 0x02b605b3; Some 0x43f5d613;
  Some 0x03b65613; Some 0x00c58633; Some 0xfe067693; Some 0x40d585b3; Some 0x0e058063; Some 0x02000713; Some 0x40b706b3; Some 0x0ed76863;
  Some 0x00269693; None; None; Some 0xfff74593; Some 0x0cd5ee63; Some 0x00812583; Some 0x0ab05c63; Some 0x00000593;
  Some 0x40565793; Some 0x00d706b3; Some 0x0006a603; Some 0x009036b3; Some 0x0007871b; Some 0x00271713; Some 0xfff64793; Some 0x00072813;
  Some 0x0200006f; Some 0x0a028463; Some 0x0008a283; Some 0x00c2e2b3; Some 0x0058a023; Some 0x00812883; Some 0x0015859b; Some 0x0715da63;
  Some 0x02a588b3; Some 0x02a582bb; Some 0x09129263; Some 0x0008889b; Some 0x00289293; Some 0x009282b3; Some 0x0012b313; Some 0x06668863;
  Some 0x0092b333; Some 0x0008a893; Some 0x011348b3; Some 0x0018c893; Some 0x04088e63; Some 0x00e288b3; Some 0x0018b313; Some 0x04668863;
  Some 0x0058b2b3; Some 0x0102c2b3; Some 0x0012c293; Some 0x04028063; Some 0x0038f293; Some 0x0012b293; Some 0x0056f2b3; Some 0xf80414e3;
  Some 0x02028663; Some 0x0008a283; Some 0x00f2f2b3; Some 0xf85ff06f; Some 0x00000513; Some 0x02813083; Some 0x02013403; Some 0x01813483;
  Some 0x01013903; Some 0x03010113; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_244bc : cchunk := mkChunk 237%positive 0x244bc 198 [
  Some 0xfd010113; Some 0x02113423; Some 0x02813023; Some 0x00913c23; Some 0x01213823; Some 0x01313423; Some 0x0a060663; Some 0x00367693;
  Some 0x2e069a63; Some 0x00062023; Some 0x0c050263; Some 0x00757693; Some 0x2e069263; Some 0x00053683; Some 0x0c068e63; Some 0x00852403;
  Some 0x00800693; Some 0x1886ec63; Some 0x11600693; Some 0x0086d6b3; Some 0x0016f693; Some 0x18068463; Some 0x00050913; Some 0x00c52683;
  Some 0x00100513; Some 0x0085173b; Some 0x10e69863; Some 0x01092703; Some 0x12074c63; Some 0x12e6ca63; Some 0x26058063; Some 0x00060993;
  Some 0x00058493; Some 0x00058513; None; Some 0x00900593; Some 0x00050693; Some 0x18b54063; None; None;
  Some 0x00052503; Some 0x00500593; Some 0x0aa5c863; None; None; None; None; Some 0x00068613;
  Some 0x1480006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x08a5c263; None; None;
  None; None; Some 0x0500006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x04a5ce63;
  None; None; None; None; Some 0x0280006f; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x02a5ca63; None; None; None; None; Some 0x00100613; Some 0x02813083;
  Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x00813983; Some 0x03010113; None; Some 0x00100513; Some 0x02813083;
  Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x00813983; Some 0x03010113; Some 0x00008067; None; None;
  Some 0x0005a583; Some 0x00500613; Some 0xfcb64ae3; None; None; None; None; Some 0x00068613;
  Some 0x00040693; Some 0x02c0006f; None; None; Some 0x0005a583; Some 0x00500613; Some 0xfab642e3; None;
  None; None; None; Some 0x00070613; None; Some 0x00100513; Some 0xf85ff06f; None;
  None; Some 0x00052583; Some 0x00500613; Some 0x00100513; Some 0xf6b646e3; None; None; None;
  None; Some 0x00040613; None; Some 0x00100513; Some 0xf4dff06f; Some 0x01f00513; Some 0x0ed56e63; Some 0x00100513;
  Some 0x02d47663; None; None; Some 0x0005a583; Some 0x00500613; Some 0xf2b644e3; None; None;
  None; None; Some 0xf55ff06f; Some 0x01092603; Some 0x02c05c63; Some 0x00d516bb; Some 0x06c6f263; None;
  None; Some 0x00052583; Some 0x00500713; Some 0x00100513; Some 0xeeb746e3; None; None; None;
  None; Some 0xf4dff06f; None; None; Some 0x00052583; Some 0x00500613; Some 0x00100513; Some 0xecb640e3;
  None; None; None; None; None; Some 0x00100513; Some 0xea5ff06f; Some 0x00410593;
  Some 0x00048513; None; Some 0x00412703; Some 0x01092683; Some 0x00098613; Some 0x00d75a63; Some 0x00000513; Some 0x00100593;
  Some 0x00b62023; Some 0xe79ff06f; None; None; Some 0x00052583; Some 0x00500613; Some 0x00100513; Some 0xe6b640e3;
  None; None; None; None; Some 0xebdff06f; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_247d4 : cchunk := mkChunk 248%positive 0x247d4 38 [
  Some 0xfe010113; Some 0x00113c23; Some 0x00813823; Some 0x00913423; Some 0x02050c63; Some 0x00050413; Some 0x00757513; Some 0x06051c63;
  Some 0x00043483; Some 0x04048e63; Some 0x0074f513; Some 0x06051463; Some 0x0004b503; None; Some 0x00048513; None;
  Some 0x00043023; Some 0x03c0006f; None; None; Some 0x00052503; Some 0x00400593; Some 0x02a5c463; None;
  None; None; None; Some 0x01813083; Some 0x01013403; Some 0x00813483; Some 0x02010113; None;
  Some 0x01813083; Some 0x01013403; Some 0x00813483; Some 0x02010113; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_2486c : cchunk := mkChunk 238%positive 0x2486c 193 [
  Some 0xfa010113; Some 0x04113c23; Some 0x04813823; Some 0x04913423; Some 0x05213023; Some 0x03313c23; Some 0x03413823; Some 0x03513423;
  Some 0x03613023; Some 0x01713c23; Some 0x01813823; Some 0x01913423; Some 0x02050c63; Some 0x00058493; Some 0x00050913; Some 0xffb5851b;
  Some 0xffd00593; Some 0x04a5e263; None; None; Some 0x00052503; Some 0x00600593; Some 0x0ab55e63; None;
  None; Some 0x0700006f; None; None; Some 0x00052503; Some 0x00600593; Some 0x08b55e63; None;
  None; Some 0x0500006f; Some 0x00060413; Some 0x02c05663; Some 0x10100513; Some 0x0aa46e63; None; None;
  Some 0x00052503; Some 0x00600593; Some 0x06b55663; None; None; Some 0x0200006f; None; None;
  Some 0x00052503; Some 0x00600593; Some 0x04b55663; None; None; None; None; Some 0x00000613;
  Some 0x05813083; Some 0x05013403; Some 0x04813483; Some 0x04013903; Some 0x03813983; Some 0x03013a03; Some 0x02813a83; Some 0x02013b03;
  Some 0x01813b83; Some 0x01013c03; Some 0x00813c83; Some 0x06010113; None; Some 0x00000993; Some 0x00098513; Some 0x05813083;
  Some 0x05013403; Some 0x04813483; Some 0x04013903; Some 0x03813983; Some 0x03013a03; Some 0x02813a83; Some 0x02013b03; Some 0x01813b83;
  Some 0x01013c03; Some 0x00813c83; Some 0x06010113; Some 0x00008067; Some 0x01000513; Some 0x00857663; Some 0x00800a13; Some 0x0180006f;
  Some 0x00400a13; Some 0x008a6863; Some 0x00343513; Some 0x00154a13; Some 0x001a0a13; Some 0x00100513; Some 0x01800593; None;
  Some 0x18050063; Some 0x00050993; Some 0x00757513; Some 0x16051a63; Some 0x00100513; Some 0x0145153b; Some 0x0149a423; Some 0x00a9a623;
  Some 0x00400593; Some 0x00400b13; None; Some 0x00000b93; Some 0x00a9b023; Some 0x0009a823; None; Some 0x00500c13;
  None; None; None; None; None; Some 0x0200006f; Some 0x00b78023; Some 0x00a780a3;
  Some 0x00c781a3; Some 0x00170713; Some 0x00e9a823; Some 0x001b8b9b; Some 0xf37404e3; Some 0x0374863b; Some 0x03748533; Some 0x10a61263;
  Some 0x01260533; Some 0x0e050e63; Some 0x012535b3; Some 0x00062713; Some 0x00e5c5b3; Some 0x0015c593; Some 0x0e058463; Some 0x0016069b;
  Some 0x0ec6c063; Some 0x012685b3; Some 0x0c058c63; Some 0x0125b7b3; Some 0x0006a693; Some 0x00d7c6b3; Some 0x0016c693; Some 0x0c068263;
  Some 0x0026069b; Some 0x0ac6ce63; Some 0x012687b3; Some 0x0a078a63; Some 0x0127b833; Some 0x0006a693; Some 0x00d846b3; Some 0x0016c693;
  Some 0x0a068063; Some 0x00054683; Some 0x0005c503; Some 0x0007c583; Some 0x03649463; Some 0x00360613; Some 0x01260633; Some 0x08060263;
  Some 0x012637b3; Some 0x00e7c733; Some 0x00174713; Some 0x06070a63; Some 0x00064603; Some 0x0080006f; Some 0x0ff00613; Some 0x00c9a783;
  Some 0x0109a703; Some 0x04f75063; Some 0x0009b803; Some 0x00271793; Some 0x00f807b3; Some 0x010038b3; Some 0x0017b293; Some 0x04588263;
  Some 0x0107b8b3; Some 0x00072293; Some 0x0058c8b3; Some 0x0018c893; Some 0x02088863; Some 0x02080663; Some 0x00d78123; Some 0xee079ee3;
  Some 0x0200006f; Some 0x000ca503; Some 0xf0ac42e3; Some 0x00100613; Some 0x000a0513; Some 0x000a8593; None; Some 0xef1ff06f;
  Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_24b70 : cchunk := mkChunk 249%positive 0x24b70 217 [
  Some 0xfb010113; Some 0x04113423; Some 0x04813023; Some 0x02913c23; Some 0x03213823; Some 0x03313423; Some 0x03413023; Some 0x01513c23;
  Some 0x01613823; Some 0x08058a63; Some 0x00050493; Some 0x0035f513; Some 0x32051863; Some 0x0005a023; Some 0x0a048463; Some 0x00058913;
  Some 0x00c10593; Some 0x00810613; Some 0x00410693; Some 0x00048513; None; Some 0x00412503; Some 0x00800593; Some 0x28a5ea63;
  Some 0x11600593; Some 0x00a5d533; Some 0x00157513; Some 0x28050263; Some 0x00048513; None; Some 0x00050413; Some 0x00048513;
  None; Some 0x00412583; Some 0x01f00613; Some 0x2cc5fa63; Some 0x00100613; Some 0x08c59e63; Some 0x00010593; Some 0x00048513;
  None; Some 0x00000513; Some 0x00012583; Some 0x0015b593; Some 0x00b92023; Some 0x2840006f; None; None;
  Some 0x00052503; Some 0x00500593; Some 0x24a5cc63; None; None; None; None; Some 0x0280006f;
  None; None; Some 0x00052503; Some 0x00500593; Some 0x22a5c863; None; None; None;
  None; Some 0x00100613; Some 0x04813083; Some 0x04013403; Some 0x03813483; Some 0x03013903; Some 0x02813983; Some 0x02013a03;
  Some 0x01813a83; Some 0x01013b03; Some 0x05010113; None; Some 0x00812603; Some 0x1ec05a63; Some 0x00000693; Some 0x00000713;
  Some 0x00000493; Some 0xfff00393; Some 0x00c16783; Some 0x00a03833; Some 0x00200893; Some 0xfff00293; Some 0x00400313; Some 0x00800e13;
  Some 0x00b39ebb; Some 0x00078f1b; Some 0x00300f93; Some 0x00090393; Some 0x028709b3; Some 0x0287093b; Some 0x1f391463; Some 0x0009899b;
  Some 0x00299913; Some 0x01250933; Some 0x00193a13; Some 0x1d480a63; Some 0x00a93a33; Some 0x0009a993; Some 0x013a49b3; Some 0x0019c993;
  Some 0x1c098063; Some 0x0d158463; Some 0x04658c63; Some 0x13c59663; Some 0x00269993; Some 0x013509b3; Some 0x00078a13; Some 0x00098a93;
  Some 0x01e04c63; Some 0x1140006f; Some 0x001a8a93; Some 0xfffa0a13; Some 0x00198993; Some 0x100a0263; Some 0x192ae463; Some 0x001abb13;
  Some 0x01684b33; Some 0x160b0e63; Some 0x17f98c63; Some 0x003acb13; Some 0x000b4b03; Some 0xfc9b4ae3; Some 0x000b0493; Some 0xfcdff06f;
  Some 0x0de05c63; Some 0x00000993; Some 0x00000a13; Some 0x00048a93; Some 0x0140006f; Some 0x001a0a1b; Some 0x00498993; Some 0x00048a93;
  Some 0x0b4f0c63; Some 0x003a549b; Some 0x00249493; Some 0x009904b3; Some 0x1324e863; Some 0x0014bb13; Some 0x01684b33; Some 0x120b0263;
  Some 0x12050063; Some 0x0034fb13; Some 0x100b1c63; Some 0x0004a483; Some 0xfff9cb13; Some 0x01cb7b13; Some 0x0164d4bb; Some 0x00f4f493;
  Some 0xfa9acae3; Some 0x000a8493; Some 0xfadff06f; Some 0x07e05663; Some 0x00000993; Some 0x00000a13; Some 0x00048a93; Some 0x0140006f;
  Some 0x001a0a1b; Some 0x00298993; Some 0x00048a93; Some 0x054f0663; Some 0x004a549b; Some 0x00249493; Some 0x009904b3; Some 0x0d24e263;
  Some 0x0014bb13; Some 0x01684b33; Some 0x0a0b0c63; Some 0x0a050a63; Some 0x0034fb13; Some 0x0a0b1663; Some 0x0004a483; Some 0xfff9cb13;
  Some 0x01eb7b13; Some 0x0164d4bb; Some 0x0034f493; Some 0xfa9acae3; Some 0x000a8493; Some 0xfadff06f; Some 0x01d4c933; Some 0x04590a63;
  Some 0x0017071b; Some 0x008686bb; Some 0xe8c714e3; Some 0x0440006f; None; None; Some 0x00052503; Some 0x00500593;
  Some 0x02a5c063; None; None; None; None; Some 0x00100613; None; Some 0x01c0006f;
  Some 0x00100513; Some 0x0140006f; Some 0x00000493; Some 0x00090393; Some 0x00000513; Some 0x0093a023; Some 0x04813083; Some 0x04013403;
  Some 0x03813483; Some 0x03013903; Some 0x02813983; Some 0x02013a03; Some 0x01813a83; Some 0x01013b03; Some 0x05010113; Some 0x00008067;
  Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_24ed4 : cchunk := mkChunk 250%positive 0x24ed4 124 [
  Some 0xfd010113; Some 0x02113423; Some 0x02813023; Some 0x00913c23; Some 0x01213823; Some 0x01313423; Some 0x01413023; Some 0x12058863;
  Some 0x00058413; Some 0x00050993; Some 0x0035f513; Some 0x1c051063; Some 0x00100513; Some 0x00a42023; Some 0x12098e63; Some 0x00098513;
  None; Some 0x00050493; Some 0x00098513; None; Some 0x02a48a33; Some 0x02a4853b; Some 0x19451a63; Some 0x00098513;
  None; Some 0x00050493; Some 0x00098513; None; Some 0x00050913; Some 0x00098513; None; Some 0x0c905463;
  Some 0x00000593; Some 0x00000613; Some 0x000a069b; Some 0x41fa529b; Some 0x01fa7713; Some 0x02000793; Some 0x00357813; Some 0x00a038b3;
  Some 0x01b2d31b; Some 0x40e782b3; Some 0x006a0333; Some 0x4053531b; Some 0x00500393; Some 0x02c90eb3; Some 0x02c90e3b; Some 0x13de1863;
  Some 0x000e8e9b; Some 0x002e9e13; Some 0x00ae0e33; Some 0x001e3f13; Some 0x11e88e63; Some 0x00ae3f33; Some 0x000eae93; Some 0x01df4eb3;
  Some 0x001ece93; Some 0x100e8463; Some 0x02f6ca63; Some 0x00259e93; Some 0x01d50eb3; Some 0x00030f13; Some 0x004e8e93; Some 0x0e7ee863;
  Some 0x0e0e0663; Some 0x0e081463; Some 0x000e2f83; Some 0x0a0f9863; Some 0xffff0f1b; Some 0x004e0e13; Some 0xfe0f10e3; Some 0x00070e63;
  Some 0x0c0e0663; Some 0x003e7e93; Some 0x0c0e9263; Some 0x000e2e03; Some 0x005e5e3b; Some 0x080e1463; Some 0x0016061b; Some 0x012585bb;
  Some 0xf6961ae3; Some 0x00000513; Some 0x0840006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x06a5c663;
  None; None; None; None; Some 0x0280006f; None; None; Some 0x0005a583;
  Some 0x00500613; Some 0x04b64463; None; None; None; None; Some 0x00100613; Some 0x02813083;
  Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x00813983; Some 0x00013a03; Some 0x03010113; None; Some 0x00000513;
  Some 0x00042023; Some 0x0080006f; Some 0x00100513; Some 0x02813083; Some 0x02013403; Some 0x01813483; Some 0x01013903; Some 0x00813983;
  Some 0x00013a03; Some 0x03010113; Some 0x00008067; Some 0xc0001073].
(* [comment removed for export] *)
Definition vlcc_25134 : cchunk := mkChunk 239%positive 0x25134 315 [
  Some 0xfa010113; Some 0x04113c23; Some 0x04813823; Some 0x04913423; Some 0x05213023; Some 0x03313c23; Some 0x03413823; Some 0x03513423;
  Some 0x03613023; Some 0x01713c23; Some 0x04050463; Some 0x80000637; Some 0x00c586b3; Some 0x01b6061b; Some 0x06d66063; None;
  None; Some 0x00052503; Some 0x00500613; Some 0x46a64663; None; None; None; None;
  Some 0x00058613; Some 0x00068593; None; Some 0x44c0006f; None; None; Some 0x00052503; Some 0x00500593;
  Some 0x42a5cc63; None; None; None; None; Some 0x0fc0006f; Some 0x00054603; Some 0x07300693;
  Some 0x0cd61663; Some 0xfff00613; Some 0x44c50063; Some 0x00154603; Some 0x07000693; Some 0x0ad61c63; Some 0xffd00613; Some 0x42a66663;
  Some 0x00254603; Some 0x06900693; Some 0x0ad61263; Some 0xffc00613; Some 0x40a66c63; Some 0x00354603; Some 0x07800693; Some 0x08d61863;
  Some 0xffb00613; Some 0x40a66263; Some 0x00450613; Some 0x00367613; Some 0x3e061c63; Some 0xff700613; Some 0x3ea66863; Some 0x00850613;
  Some 0x00367613; Some 0x3e061263; Some 0xff300613; Some 0x3ca66e63; Some 0x00c50613; Some 0x00367613; Some 0x3c061863; Some 0xfeb00613;
  Some 0x3ca66463; Some 0x01450613; Some 0x00367693; Some 0x3a069e63; Some 0x00452483; Some 0xfff0c6b7; Some 0xdbf6869b; Some 0x00d4873b;
  Some 0x08e6e063; None; None; Some 0x00052503; Some 0x00500593; Some 0x36a5c263; None; None;
  None; None; Some 0x0280006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x32a5ce63;
  None; None; None; None; Some 0x00000613; Some 0x05813083; Some 0x05013403; Some 0x04813483;
  Some 0x04013903; Some 0x03813983; Some 0x03013a03; Some 0x02813a83; Some 0x02013b03; Some 0x01813b83; Some 0x06010113; None;
  Some 0x00852903; Some 0x00d9073b; Some 0x02e6e663; None; None; Some 0x00052503; Some 0x00500593; Some 0x2ca5ce63;
  None; None; None; None; Some 0xfa1ff06f; Some 0x029906b3; Some 0x17d78737; Some 0x4017071b;
  Some 0x02e6e663; None; None; Some 0x00052503; Some 0x00500593; Some 0x2aa5c263; None; None;
  None; None; Some 0xf69ff06f; Some 0x00066b03; Some 0x10000613; Some 0x11666463; Some 0x007b0613; Some 0x0025d693;
  Some 0x0ed67e63; Some 0x00058a13; Some 0x00050b93; Some 0x00c52983; Some 0x00048513; Some 0x00090593; Some 0x00098613; None;
  Some 0x00a13423; Some 0x10050063; Some 0x00291a9b; None; Some 0x02aa843b; Some 0x02aa8533; Some 0x26a41863; Some 0x002b1593;
  Some 0x01858593; Some 0xfffbc693; Some 0x26b6e063; Some 0x00bb85b3; Some 0x0035f613; Some 0x24061a63; Some 0x000a0513; Some 0x0005aa03;
  Some 0x002b1593; Some 0x40b5053b; Some 0xfe450a9b; Some 0x00810513; None; Some 0x0d541c63; Some 0x0d441a63; Some 0x00048513;
  Some 0x00090593; Some 0x00098613; None; Some 0x00a13023; Some 0x0e050a63; Some 0x000b091b; Some 0x100b0a63; Some 0xfe700593;
  Some 0x2175e463; Some 0x018b8513; Some 0x00400593; Some 0x00090613; None; Some 0x10050063; Some 0x00050493; Some 0x00013503;
  Some 0x00048593; None; Some 0x10050e63; Some 0x00010513; None; None; None; Some 0x00052503;
  Some 0x00500593; Some 0x18a5ca63; None; None; None; None; Some 0x1740006f; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x16a5c663; None; None; None; None;
  Some 0xe31ff06f; None; None; Some 0x00052503; Some 0x00500593; Some 0x14a5c263; None; None;
  None; None; Some 0xe09ff06f; None; None; Some 0x00052503; Some 0x00500593; Some 0x10a5ce63;
  None; None; None; None; Some 0x00040613; Some 0x000a8693; Some 0x000a0713; None;
  Some 0x0f80006f; None; None; Some 0x00052503; Some 0x00500593; Some 0x0ea5c263; None; None;
  None; None; Some 0x0c40006f; Some 0x00000493; Some 0x0380006f; Some 0x00010513; None; None;
  None; Some 0x00052503; Some 0x00500593; Some 0x0aa5c663; None; None; None; None;
  Some 0x08c0006f; Some 0x00013503; None; Some 0xfe300593; Some 0x0b75ec63; Some 0x01cb8593; Some 0x00291913; Some 0xfff5c613;
  Some 0x0b266463; Some 0x012585b3; Some 0x00b56633; Some 0x00367613; Some 0x08061c63; Some 0x00040613; None; Some 0x000b0e63;
  Some 0x00013583; Some 0x01410613; Some 0x00048513; None; Some 0x01412503; Some 0x00050663; Some 0x00013503; Some 0x0400006f;
  Some 0x00010513; None; None; None; Some 0x00052503; Some 0x00500593; Some 0x02a5c063; None;
  None; None; None; Some 0x00000613; None; Some 0x0080006f; Some 0x00000513; Some 0x05813083;
  Some 0x05013403; Some 0x04813483; Some 0x04013903; Some 0x03813983; Some 0x03013a03; Some 0x02813a83; Some 0x02013b03; Some 0x01813b83;
  Some 0x06010113; Some 0x00008067; Some 0xc0001073].

Definition canon_code_VL : list cchunk := [
  vlcc_237d4; vlcc_23878; vlcc_239c0; vlcc_23ce4; vlcc_23d30; vlcc_23e10; vlcc_23ecc; vlcc_23fbc;
  vlcc_24044; vlcc_240cc; vlcc_2414c; vlcc_24198; vlcc_241e4; vlcc_24230; vlcc_242cc; vlcc_244bc;
  vlcc_247d4; vlcc_2486c; vlcc_24b70; vlcc_24ed4; vlcc_25134].

Class RelocCodeVL (RL : Reloc) := { rl_code_vl_ok : code_check rl_segs rl_delta canon_code_VL = true }.

Lemma rl_fetch_at_VL : forall {RL : Reloc} {RC : RelocCodeVL RL} (i : nat) (ch : cchunk) c (w : bv 32),
  nth_error canon_code_VL i = Some ch -> chunk_has ch c (bv_unsigned w) = true ->
  fetch_word rl_segs (rl (rl_delta (cc_blk ch)) c) = Some w.
Proof. intros RL RC i ch c w Hi H. exact (chunk_sound rl_segs rl_delta canon_code_VL i ch c w rl_code_vl_ok Hi H). Qed.

Ltac rl_F_VL i ch :=
  lazymatch goal with
  | |- fetch_word _ (rl _ ?c) = Some ?w =>
      exact (rl_fetch_at_VL i ch c w (@eq_refl _ (Some ch)) ltac:(vm_cast_no_check (@eq_refl bool true)))
  end.
