(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.libpcap.fuzz_pcap.images Require Export Asan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanAcct__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module IMGM := Asan.M.
Definition SEGS : list Segment := IMGM.loaded_segments.
Definition PC0 : N := IMGM.init_pc.
Definition PH : PhdrInfo := IMGM.phdrs.
Definition IMG : Image := mkImage SEGS PC0 PH.
Definition ROM : word -> option byte := seg_rom SEGS.

(* [comment removed for export] *)
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x603000.

Lemma reserved_top_val : reserved_top (segments_reserved SEGS) = IMG_HI.
Proof. vm_compute. reflexivity. Qed.
Lemma reserved_top_ok : (reserved_top (segments_reserved SEGS)) mod page_size = 0%Z
  /\ (0 <= reserved_top (segments_reserved SEGS) < 2 ^ 64 - brk_aslr_max)%Z.
Proof. split; [vm_compute; reflexivity|]. split; [apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma segs_below : segs_below_b SEGS IMG_HI = true.
Proof. vm_compute. reflexivity. Qed.
Lemma H_off_segments_img : forall H : word -> bool,
  (forall a, H a = true -> (IMG_HI <= bv_unsigned a)%Z) -> H_off_segments SEGS H.
Proof. intros H HI. apply (H_off_segments_above SEGS H IMG_HI segs_below HI). Qed.

(* [comment removed for export] *)
Lemma wx_nowrap : wx_segs_nowrap SEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
From OSSVerify.libpcap.fuzz_pcap.images Require AsanUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Export OSSVerify.libpcap.fuzz_pcap.images.AsanUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanAcct__Common.AsanAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module IMGM := AsanUbsan.M.
Definition SEGS : list Segment := IMGM.loaded_segments.
Definition PC0 : N := IMGM.init_pc.
Definition PH : PhdrInfo := IMGM.phdrs.
Definition IMG : Image := mkImage SEGS PC0 PH.
Definition ROM : word -> option byte := seg_rom SEGS.

(* [comment removed for export] *)
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x604000.

Lemma reserved_top_val : reserved_top (segments_reserved SEGS) = IMG_HI.
Proof. vm_compute. reflexivity. Qed.
Lemma reserved_top_ok : (reserved_top (segments_reserved SEGS)) mod page_size = 0%Z
  /\ (0 <= reserved_top (segments_reserved SEGS) < 2 ^ 64 - brk_aslr_max)%Z.
Proof. split; [vm_compute; reflexivity|]. split; [apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma segs_below : segs_below_b SEGS IMG_HI = true.
Proof. vm_compute. reflexivity. Qed.
Lemma H_off_segments_img : forall H : word -> bool,
  (forall a, H a = true -> (IMG_HI <= bv_unsigned a)%Z) -> H_off_segments SEGS H.
Proof. intros H HI. apply (H_off_segments_above SEGS H IMG_HI segs_below HI). Qed.

(* [comment removed for export] *)
Lemma wx_nowrap : wx_segs_nowrap SEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
End TwB.
