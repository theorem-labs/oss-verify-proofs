(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for fuzz_disco (both images). *)
(* The rounding-mode guard of the program-part contract (lib/A/ACfn.v, lib/Reusable/YCfn.v): frm, bits 5..7 of
   fcsr, is 0 (round to nearest, ties to even). The same body as lib/Lib/FP.v frm0, which the program walks state
   their contract with, so the two are convertible. This file does not Require lib/Lib/FP.v: that file's imports
   redefine Zify.zify_pre_hook globally (Zifyk6b.zon_hook), which would replace the image-bound hook of every core
   file that Requires a driver file after setting its own. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From Stdlib Require Import ZArith.
Definition frm0 (fc : bv 32) : Prop := Z.land (Z.shiftr (bv_unsigned fc) 5) 7 = 0%Z.
