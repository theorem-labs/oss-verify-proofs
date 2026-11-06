(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition A_RS : list (Z * nat) := [
  (0x3f254, 69%nat);
  (0x3f4b0, 254%nat);
  (0x3f930, 245%nat);
  (0x42504, 65%nat);
  (0x437dc, 44%nat);
  (0x43954, 17%nat);
  (0x43a30, 17%nat);
  (0x43ab8, 112%nat);
  (0x43ce8, 137%nat);
  (0x43f78, 214%nat);
  (0x443f8, 127%nat);
  (0x44688, 263%nat);
  (0x44b64, 2%nat);
  (0x44bb0, 32%nat);
  (0x61d34, 25%nat);
  (0x61e1c, 87%nat);
  (0x61fd8, 38%nat);
  (0x63044, 44%nat);
  (0x631b8, 5%nat);
  (0x63288, 35%nat);
  (0x633c0, 14%nat);
  (0x641c0, 6%nat);
  (0x681b4, 6%nat);
  (0x690c4, 13%nat);
  (0x69e4c, 46%nat);
  (0x69f74, 14%nat);
  (0x6aa90, 9%nat);
  (0x6b8c4, 8%nat);
  (0x6ba88, 44%nat);
  (0x6d940, 82%nat);
  (0x6de7c, 4%nat);
  (0x6fb24, 11%nat);
  (0x70098, 12%nat);
  (0x70138, 26%nat);
  (0x701e8, 9%nat);
  (0x733c4, 9%nat);
  (0x73440, 24%nat);
  (0x73c20, 11%nat);
  (0x7550c, 53%nat);
  (0x7594c, 67%nat);
  (0x75ad0, 3%nat);
  (0x75fec, 17%nat);
  (0x7613c, 10%nat);
  (0x7db90, 18%nat);
  (0x7dcdc, 4%nat);
  (0x7f98c, 103%nat);
  (0x81ca0, 18%nat);
  (0x81f88, 158%nat);
  (0x8271c, 36%nat);
  (0x8290c, 25%nat);
  (0x829b4, 33%nat);
  (0x82f70, 31%nat);
  (0x83050, 14%nat);
  (0x8f488, 6%nat);
  (0xd3088, 62%nat);
  (0xd4a14, 7%nat);
  (0xd84a4, 18%nat)].
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
  (0xdcbf0, 9%nat);
  (0xdd868, 1%nat);
  (0xdeb50, 1%nat);
  (0xdeb88, 1%nat)].

From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxImg FxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS := Asan.M.loaded_segments.
Fixpoint mk_img_runs (rs : list (Z * nat)) (acc : tree Z) : tree Z :=
  match rs with [] => acc | (lo, n) :: rs' => mk_img_runs rs' (mk_img_acc ASEGS n (Z.shiftr lo 3) acc) end.
Definition ATBLd : tree xi := mk_tbl_ranges ASEGS A_RS.
Definition AIMGd : tree Z := mk_img_runs A_WR TEmpty.
