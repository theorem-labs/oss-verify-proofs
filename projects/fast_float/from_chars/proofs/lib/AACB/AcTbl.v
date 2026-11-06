(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition A_RS : list (Z * nat) := [
  (0x3f570, 69%nat);
  (0x3f7cc, 254%nat);
  (0x3fc4c, 245%nat);
  (0x42820, 65%nat);
  (0x43af8, 44%nat);
  (0x43c70, 17%nat);
  (0x43d4c, 17%nat);
  (0x43dd4, 112%nat);
  (0x44004, 137%nat);
  (0x44294, 214%nat);
  (0x44714, 127%nat);
  (0x449a4, 263%nat);
  (0x44e80, 2%nat);
  (0x44ecc, 32%nat);
  (0x61d28, 25%nat);
  (0x61e10, 87%nat);
  (0x61fcc, 38%nat);
  (0x63038, 44%nat);
  (0x631ac, 5%nat);
  (0x6327c, 35%nat);
  (0x633b4, 14%nat);
  (0x641b4, 6%nat);
  (0x681a8, 6%nat);
  (0x690b8, 13%nat);
  (0x69e40, 46%nat);
  (0x69f68, 14%nat);
  (0x6aa84, 9%nat);
  (0x6b8b8, 8%nat);
  (0x6ba7c, 44%nat);
  (0x6d934, 82%nat);
  (0x6de70, 4%nat);
  (0x6fb18, 11%nat);
  (0x7008c, 12%nat);
  (0x7012c, 26%nat);
  (0x701dc, 9%nat);
  (0x733b8, 9%nat);
  (0x73434, 24%nat);
  (0x73c14, 11%nat);
  (0x75500, 53%nat);
  (0x75940, 67%nat);
  (0x75ac4, 3%nat);
  (0x75fe0, 17%nat);
  (0x76130, 10%nat);
  (0x7db84, 18%nat);
  (0x7dcd0, 4%nat);
  (0x7f980, 103%nat);
  (0x81c94, 18%nat);
  (0x81f7c, 158%nat);
  (0x82710, 36%nat);
  (0x82900, 25%nat);
  (0x829a8, 33%nat);
  (0x82f64, 31%nat);
  (0x83044, 14%nat);
  (0x8f47c, 6%nat);
  (0xd4904, 62%nat);
  (0xd6290, 7%nat);
  (0xd9d20, 18%nat)].
Definition A_WR : list (Z * nat) := [
  (0x102e8, 1%nat);
  (0x10318, 1%nat);
  (0x10378, 1%nat);
  (0x10420, 1%nat);
  (0x10430, 1%nat);
  (0x10440, 1%nat);
  (0x104b8, 1%nat);
  (0x105c0, 1%nat);
  (0x105e8, 1%nat);
  (0xde470, 9%nat);
  (0xdf0e8, 1%nat);
  (0xe03d0, 1%nat);
  (0xe0408, 1%nat)].

From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxImg FxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Fixpoint mk_img_runs (rs : list (Z * nat)) (acc : tree Z) : tree Z :=
  match rs with [] => acc | (lo, n) :: rs' => mk_img_runs rs' (mk_img_acc ASEGS n (Z.shiftr lo 3) acc) end.
Definition ATBLd : tree xi := mk_tbl_ranges ASEGS A_RS.
Definition AIMGd : tree Z := mk_img_runs A_WR TEmpty.
