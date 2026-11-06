(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cjson/cjson_read_fuzzer/lib/RL/I/IImgA.v for this unit: its address tables keep some of cjson's keys and add this unit's own, each at an address of this unit's asan image (lib/A/Img0.v); the definitions A_* are renamed N_* and asegs is renamed rsegs; the notations KV and KV3 are no longer Local; and the imports name this unit's modules. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/CJ/RL/I/IImgA.v at 2d2ff01bb6f2 as lib/CJ/RL/I/IImgAG.v, the map of the GXA (fuzz_reply key space) keys of the snprintf chain for reac-pw/fuzz_rate's ASan image A: module paths changed; every value moved to the image's address (symbol + offset, or the code that forms it, or the image end; ledger provenance/reloc/A-Snp.tsv), every key kept. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require Export IInst.
Import ListNotations.
Open Scope Z_scope.

Notation KV a b := (a, b) (only parsing).
Notation KV3 a b c := (a, b, c) (only parsing).
Definition N_exact : list (Z * Z) := [
  KV 0x1029e 0x10b94;
  KV 0x102ac 0x13850;
  KV 0x102de 0x1426e;
  KV 0x102e5 0x158a4;
  KV 0x1031d 0x16fc9;
  KV 0x10326 0x18ed2;
  KV 0x1032a 0x19779;
  KV 0x10355 0x1d872;
  KV 0x1036a 0x1d887;
  KV 0x10381 0x1dfb0;
  KV 0x10385 0x1ea20;
  KV 0x103b3 0x207af;
  KV 0x103c0 0x102e0;
  KV 0x103d8 0x10350;
  KV 0x103e8 0x10370;
  KV 0x103f0 0x10380;
  KV 0x103f8 0x10388;
  KV 0x10400 0x10390;
  KV 0x10418 0x10390;
  KV 0x10420 0x103a0;
  KV 0x10428 0x103a8;
  KV 0x10430 0x103c8;
  KV 0x107e4 0x22838;
  KV 0x10804 0x22858;
  KV 0x10864 0x228b8;
  KV 0x1087f 0x228d3;
  KV 0x10884 0x228f8;
  KV 0x10964 0x229d8;
  KV 0x10984 0x229f8;
  KV 0x109cc 0x22a40;
  KV 0x10b9c 0x22c10;
  KV 0x1145c 0x21754;
  KV 0x11988 0x250f8;
  KV 0x22e18 0x9caf8;
  KV 0x22e20 0x9cb28;
  KV 0x23f58 0xa0510;
  KV 0x23f60 0xa0518;
  KV 0x24048 0xa0600;
  KV 0x34280 0x5f7e40;
  KV 0x342a8 0x5f7e60;
  KV 0x34320 0x5f7ee0;
  KV 0x346c0 0xa06f0;
  KV 0x35000 0x5fa000;
  KV 0x7f000200 0x948bc;
  KV 0x7f000300 0x94988;
  KV 0x7f000400 0x91790;
  KV 0x7f000700 0x90e40;
  KV 0x7f000800 0x90f3c].
Definition N_iv : list (Z * Z * Z) := [
  KV3 0x12f9c 0x12fc8 (121428);
  KV3 0x12fc8 0x1303c (121428);
  KV3 0x1303c 0x130cc (121428);
  KV3 0x130cc 0x13390 (446888);
  KV3 0x13390 0x13393 (446888);
  KV3 0x13394 0x13399 (446888);
  KV3 0x134a8 0x134f0 (447012);
  KV3 0x15700 0x15701 (483068);
  KV3 0x15704 0x15930 (483068);
  KV3 0x15930 0x1597c (483068);
  KV3 0x1597c 0x159dc (483068);
  KV3 0x159dc 0x15a24 (483068);
  KV3 0x15a24 0x15a2c (483284);
  KV3 0x15ce0 0x15ce4 (484076);
  KV3 0x15ce4 0x15d30 (484076);
  KV3 0x15d30 0x15da4 (484076);
  KV3 0x15da4 0x15dc0 (483400);
  KV3 0x15dc0 0x15ea4 (484560);
  KV3 0x15ea4 0x15f04 (482820);
  KV3 0x15f04 0x15f05 (482820);
  KV3 0x15f0c 0x15f44 (484456);
  KV3 0x15f44 0x15f50 (482764);
  KV3 0x15f5c 0x15f5e (248916);
  KV3 0x15f60 0x15f61 (248916);
  KV3 0x15f64 0x16130 (486640);
  KV3 0x16130 0x16240 (486640);
  KV3 0x16240 0x16618 (486640);
  KV3 0x16618 0x168f0 (486640);
  KV3 0x168f0 0x16c60 (486640);
  KV3 0x16c60 0x17504 (486640);
  KV3 0x17504 0x17654 (486640);
  KV3 0x17a9c 0x17b88 (492544);
  KV3 0x17b88 0x17bd0 (492544);
  KV3 0x17bd0 0x17ca4 (492544);
  KV3 0x17ca4 0x17cec (492544);
  KV3 0x17d50 0x17e88 (497280);
  KV3 0x17e88 0x17f40 (497280);
  KV3 0x17f40 0x17f94 (497280);
  KV3 0x17f94 0x18138 (496280);
  KV3 0x18138 0x18234 (494856);
  KV3 0x18234 0x18294 (494856);
  KV3 0x18294 0x182c4 (496512);
  KV3 0x1838c 0x1838d (493424);
  KV3 0x18390 0x183bc (493424);
  KV3 0x183bc 0x1854c (493712);
  KV3 0x1854c 0x18554 (493304);
  KV3 0x18554 0x18704 (496188);
  KV3 0x18704 0x19534 (496188);
  KV3 0x19534 0x19668 (496188);
  KV3 0x19668 0x1973c (496188);
  KV3 0x1973c 0x1ae04 (496188);
  KV3 0x1ae04 0x1ae40 (462616);
  KV3 0x1ae44 0x1ae45 (465192);
  KV3 0x1ae48 0x1ae6c (480208);
  KV3 0x1ae6c 0x1af98 (479872);
  KV3 0x1af98 0x1b128 (433092);
  KV3 0x1b128 0x1b130 (495384);
  KV3 0x1b130 0x1b174 (473956);
  KV3 0x1b174 0x1b24c (471880);
  KV3 0x1b24c 0x1b314 (432012);
  KV3 0x1b3d0 0x1bad0 (471492);
  KV3 0x1bad0 0x1bbd8 (471560);
  KV3 0x1bbd8 0x1bc70 (473868);
  KV3 0x1bc70 0x1bc80 (430844);
  KV3 0x1bc80 0x1c44c (430844);
  KV3 0x1c44c 0x1c47c (430844);
  KV3 0x1c47c 0x1c488 (430844);
  KV3 0x1c488 0x1c51c (490432);
  KV3 0x1c51c 0x1c608 (490432);
  KV3 0x1c608 0x1c6b0 (471412);
  KV3 0x1c6b0 0x1cfb4 (468784);
  KV3 0x1cfb4 0x1cfd0 (489708);
  KV3 0x1cfd0 0x1d070 (476800);
  KV3 0x1d084 0x1d150 (489528);
  KV3 0x1d150 0x1d22c (489528);
  KV3 0x1deac 0x1df40 (471788);
  KV3 0x1df40 0x1df78 (483976);
  KV3 0x1df78 0x1e040 (483976);
  KV3 0x1e040 0x1e0cc (471244);
  KV3 0x20bd4 0x211ac (472820);
  KV3 0x21268 0x21334 (474096);
  KV3 0x21334 0x21738 (474144);
  KV3 0x21738 0x21830 (474144);
  KV3 0x21830 0x218c0 (474484);
  KV3 0x21920 0x21964 (474816);
  KV3 0x21964 0x21bec (474816);
  KV3 0x21bec 0x21c60 (474816);
  KV3 0x21c60 0x21c84 (474816);
  KV3 0x21c84 0x21c87 (474816);
  KV3 0x21c88 0x21c8a (481524);
  KV3 0x21c94 0x21ce8 (493796);
  KV3 0x21ce8 0x21cf4 (493884);
  KV3 0x21cf4 0x21d28 (493924);
  KV3 0x34130 0x34280 (5913048);
  KV3 0x34288 0x34290 (6044040)].
Definition N_sym (k : Z) : Z := tsym N_exact N_iv k.
Definition N_img : RImg := {| img_segs := rsegs; sym := N_sym |}.
