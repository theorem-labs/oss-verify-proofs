(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_pcap's lib/Reusable/YImgTop.v, in the shape
   (fuzz_disco a0d2491b460): the two bounds of reac-pw/fuzz_link's ASan images, measured from their program
   headers. The lowest PT_LOAD of both the asan and the asan-ubsan build starts at 0x10000; the last PT_LOAD ends
   at 0x6534f0 (asan) and 0x652a70 (asan-ubsan), so one page above both is 0x654000.
   Reusable/PcapImgEnd.v's pcap_img_end is IMG_TOP under the name the other files already cite. *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Definition IMG_LO : Z := 0x10000.
Definition IMG_TOP : Z := 0x654000.
