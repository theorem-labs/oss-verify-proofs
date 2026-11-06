(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cjson/cjson_read_fuzzer/lib/RL/I/IImgP.v for this unit: its address tables keep some of cjson's keys and add this unit's own, each at an address of this unit's plain image (lib/Img0.v); the definitions P_* are renamed N_* and psegs is renamed rsegs; the notations KV and KV3 are no longer Local; the Lia, Nia and Nra cache settings are removed; and the imports name this unit's modules. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/CJ/RL/I/IImgP.v, with its module paths, addresses and numbers changed; 102 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require Export IInst.
Import ListNotations.
Open Scope Z_scope.

Notation KV a b := (a, b) (only parsing).
Notation KV3 a b c := (a, b, c) (only parsing).
(* fuzz_rate's map from the CJ key space to its plain image: the union of libreac/fuzz_disco's printf entries
   (disco lib/CJ/RL/I/IImgP.v at hub 25e3d17bdb50) and reac-pw/fuzz_role's soft-float entries (role
   lib/CJ/RL/I/IImgP.v at b8e5097052e7: the rounding table 0x1145c, __extendsftf2 0x200dc, __floatditf 0x7f000900,
   the intervals of __cmptf2 / __getf2 and __subtf3 / __addtf3 / __fe_getround / __fe_raise_inexact), each value
   moved to fuzz_rate's image by symbol + offset, code reference or bytes. Entries no closure file names are left
   out. *)
Definition N_exact : list (Z * Z) := [
  KV 0x1145c 0x10684;
  KV 0x11988 0x114b0;
  KV 0x15ce0 0x16300;
  KV 0x200dc 0x15050;
  KV 0x35000 0x51000;
  KV 0x7f000100 0x188a8;
  KV 0x7f000200 0x1cc50;
  KV 0x7f000300 0x1cd1c;
  KV 0x7f000400 0x18b70;
  KV 0x7f000700 0x182c4;
  KV 0x7f000800 0x183c0;
  KV 0x7f000900 0x151ac;
  KV 0x10001351c 0x12f48;
  KV 0x100015d84 0x1616c;
  KV 0x100015e4c 0x16234;
  KV 0x100015f14 0x162fc;
  KV 0x100034734 0x2fca4;
  KV 0x100034900 0x4fde8].
Definition N_iv : list (Z * Z * Z) := [
  KV3 0x1029e 0x102a8 (16);
  KV3 0x102ac 0x102bf (73);
  KV3 0x102dd 0x102e0 (90);
  KV3 0x102e5 0x10316 (93);
  KV3 0x1031d 0x10321 (101);
  KV3 0x10326 0x1034b (112);
  KV3 0x10355 0x10381 (195);
  KV3 0x10381 0x10385 (210);
  KV3 0x10385 0x10389 (213);
  KV3 0x103a9 0x103ba (265);
  KV3 0x103c0 0x103c1 (264);
  KV3 0x103d8 0x103d9 (280);
  KV3 0x103e8 0x103f1 (272);
  KV3 0x103f8 0x103f9 (272);
  KV3 0x10420 0x10421 (248);
  KV3 0x10428 0x10431 (248);
  KV3 0x10438 0x10439 (248);
  KV3 0x107e4 0x107e5 (-248);
  KV3 0x10804 0x10883 (-248);
  KV3 0x10884 0x10887 (-228);
  KV3 0x10964 0x10967 (-228);
  KV3 0x10984 0x10987 (-228);
  KV3 0x109cc 0x10b9c (-228);
  KV3 0x10b9c 0x10bac (-1444);
  KV3 0x10bac 0x1145c (-244);
  KV3 0x1145c 0x1145e (-3544);
  KV3 0x1303c 0x130cc (-1452);
  KV3 0x134a8 0x134f0 (-1328);
  KV3 0x15ce4 0x15da4 (1568);
  KV3 0x15da4 0x15dc0 (940);
  KV3 0x15f04 0x15f06 (1540);
  KV3 0x15f44 0x15f50 (1540);
  KV3 0x15f5c 0x15f5e (1528);
  KV3 0x15f60 0x15f62 (1844);
  KV3 0x17cec 0x17cf4 (1844);
  KV3 0x17d50 0x17e88 (1844);
  KV3 0x17f40 0x18138 (1844);
  KV3 0x18138 0x18294 (396);
  KV3 0x18390 0x18554 (1404);
  KV3 0x18554 0x1ae40 (1564);
  KV3 0x1ae48 0x1ae6c (1564);
  KV3 0x1af98 0x1b24c (1564);
  KV3 0x1b24c 0x1b3d0 (-25472);
  KV3 0x1b3d0 0x1bc70 (1176);
  KV3 0x1bc70 0x1c488 (-27040);
  KV3 0x1c488 0x1cfd0 (-896);
  KV3 0x1cfd0 0x1d070 (-17664);
  KV3 0x1d084 0x1d22c (-1076);
  KV3 0x21268 0x21334 (-15924);
  KV3 0x21334 0x21830 (-17672);
  KV3 0x21920 0x21964 (-17712);
  KV3 0x21964 0x21c60 (-17508);
  KV3 0x22db0 0x22df0 (-17400);
  KV3 0x22df0 0x22e30 (-17392);
  KV3 0x23e30 0x23e38 (-17392);
  KV3 0x23f58 0x24050 (-17416);
  KV3 0x24068 0x340a9 (-17424);
  KV3 0x34130 0x34280 (-17496);
  KV3 0x34280 0x34284 (114056);
  KV3 0x34288 0x34290 (114056);
  KV3 0x342a8 0x3431c (114056);
  KV3 0x346c0 0x346cc (114064)].
Definition N_sym (k : Z) : Z := tsym N_exact N_iv k.
Definition N_img : RImg := {| img_segs := rsegs; sym := N_sym |}.
