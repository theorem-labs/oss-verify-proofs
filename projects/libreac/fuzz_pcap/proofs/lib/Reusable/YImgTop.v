(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap, in the shape of libreac/fuzz_disco's lib/Reusable/YImgTop.v (a0d2491b460):
   the two bounds of fuzz_pcap's ASan images, measured from their program headers. The lowest PT_LOAD of both the
   asan and the asan-ubsan build starts at 0x10000; the last PT_LOAD ends at 0x5f6170 (asan) and 0x5f6070
   (asan-ubsan), so one page above both is 0x5f7000. lib/A/PcapImgEndCheck.v checks the pair against the image the
   build loads. Reusable/PcapImgEnd.v's pcap_img_end is IMG_TOP under the name the other files already cite. *)
(* Modified by Theorem Labs, 2026-11 (OSSV-267): both bounds are named from lib/ImgPages.v (the asan image's base
   and the page above its .bss), so a relink that grows the image past a page moves them; each body is still the
   numeral (0x10000, 0x5f7000). lib/A/PcapImgEndCheck.v and lib/B/PcapImgEndCheck.v check them against both images,
   so the build fails if the asan and asan-ubsan images ever end in different pages. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require ImgPages.
Local Open Scope Z_scope.

Definition IMG_LO : Z := Eval compute in ImgPages.Asan.ro_lo.
Definition IMG_TOP : Z := Eval compute in ImgPages.Asan.top.
