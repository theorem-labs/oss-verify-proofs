(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_pcap: the first address past its loaded image,
   under the name the ported files cite. The value is YImgTop.IMG_TOP, the one place that states fuzz_pcap's
   image bounds; lib/A/PcapImgEndCheck.v checks them against the image the build loads. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

(* The first address at or above the loaded image that no loaded segment covers, rounded up to a page. *)
Definition pcap_img_end : Z := YImgTop.IMG_TOP.
