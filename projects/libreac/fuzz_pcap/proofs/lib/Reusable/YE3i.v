From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE3i.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI04 YK04 YB1v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* [IMG_RO_LO, IMG_RO_HI) is the whole read-only PT_LOAD of fuzz_pcap.asan-ubsan (sha256 9e66f771f22a...): p_vaddr
   0x10000, p_memsz 0x1efc0, so it ends at 0x2efc0.  Its sections are .note.gnu.build-id [0x102a8, 0x102cc), .rodata
   [0x102e0, 0x2266c), .eh_frame_hdr [0x2266c, 0x246f8) and .eh_frame [0x246f8, 0x2efc0); IMG_RO_HI is the end of
   .eh_frame.  elf_snapshot maps the segment page-rounded, as tfibsegs' first segment [0x10000, 0x2f000), whose tail
   [0x2efc0, 0x2f000) holds file bytes of .text; img_ro_seg0 below checks that segment against IMG_RO_LO / IMG_RO_HI.
   The relocation wrote 0x2ee90 here, the port of the donor's 0x2f1ac, which sits 0x160 below the read-only PT_LOAD
   end 0x2f30c of cgif's asan-ubsan build.  0x2ee90 is no boundary of fuzz_pcap.asan-ubsan (it is 0x20 bytes into the .eh_frame FDE at
   0x2ee70), so the bound is restated to the segment end (2026-10-29), as lib/A/AE3i.v is.  The last chunk of
   img_ro_chunks ends at IMG_RO_HI and grows with it; no YF0m Tfib_owned_static row lies in [0x2134a, 0x2efc0). *)
Definition IMG_RO_LO : Z := 0x10000.
Definition IMG_RO_HI : Z := (symaddr (Symbols.AsanUbsan.Sec.s_eh_frame + Symbols.AsanUbsan.Sec.Size.s_eh_frame)%Z).
Definition img_ro_chunks : list YP09.chunk :=
(* [IMG_RO_LO, IMG_RO_HI) minus every YF0m.v Tfib_owned_static row inside it, as consecutive chunks
   (the donor's rule, cgif YE3i.v against cgif's Tfib_owned_static). Regenerated for fuzz_pcap
   from this unit's Tfib_owned_static; img_ro_complement_ok below checks it by computation. The last chunk,
   [0x2134a, IMG_RO_HI), is the end of .rodata after the last owned row (0x21348, 2), then .eh_frame_hdr and .eh_frame. *)
[ YP09.mkChunk 0x10000 (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x8)%Z) - 0x10000));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x10)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x28)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x10)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x30)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x48)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x30)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x50)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xb8)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x50)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc8)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd0)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc8)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd8)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x140)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd8)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x180)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x240)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x180)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc978)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc98d)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67488)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc98d)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67492)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68141)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67492)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68160)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68195)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68160)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68224)%Z) (CImg ((symaddr (Symbols.AsanUbsan.Sec.s_rodata + 69636)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68224)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 69640)%Z) (CImg ((symaddr (Symbols.AsanUbsan.s_sysconf_values + 0x3c)%Z) - (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 69640)%Z)));
YP09.mkChunk (symaddr (Symbols.AsanUbsan.s_sysconf_values + 0x3e)%Z) (CImg (IMG_RO_HI - (symaddr (Symbols.AsanUbsan.s_sysconf_values + 0x3e)%Z))) ].
Definition ro_owned_in_range : list (Z * Z) :=
filter (fun r => (IMG_RO_LO <=? fst r) && (fst r + snd r <=? IMG_RO_HI)) YF0m.Tfib_owned_static.
Fixpoint ro_insert (x : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
match l with
| [] => [x]
| y :: l' => if fst x <=? fst y then x :: y :: l' else y :: ro_insert x l'
end.
Fixpoint ro_sort (l : list (Z * Z)) : list (Z * Z) :=
match l with [] => [] | x :: l' => ro_insert x (ro_sort l') end.
Fixpoint ro_complement (lo : Z) (rs : list (Z * Z)) : list (Z * Z) :=
match rs with
| [] => if lo <? IMG_RO_HI then [(lo, IMG_RO_HI - lo)] else []
| (a, n) :: rs' => (if lo <? a then [(lo, a - lo)] else []) ++ ro_complement (Z.max lo (a + n)) rs'
end.
(* The chunk list is the complement, inside [IMG_RO_LO, IMG_RO_HI), of this image's generated Tfib_owned_static,
   as lib/A/AE3i.v checks it for the asan image; checked by computation, not by a measurement outside the tree. *)
Lemma img_ro_complement_ok :
map (fun c => (YP09.c_off c, c_len c)) img_ro_chunks = ro_complement IMG_RO_LO (ro_sort ro_owned_in_range).
Proof. vm_compute. reflexivity. Qed.
Lemma img_ro_seg0 :
nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_base s) + Z.of_N (seg_size s), seg_writable s)) tfibsegs) 0 =
Some (IMG_RO_LO, (IMG_RO_HI + 0xfff) / 0x1000 * 0x1000, false).
Proof. vm_compute. reflexivity. Qed.
Definition img_ro_region : YP09.region := YP09.mkRegion None IMG_RO_LO IMG_RO_HI 0 0 img_ro_chunks.
Definition ro_img (m : word -> option byte) : Prop := forall E, region_ok tfibsegs E m img_ro_region.
Definition ro_clean (m : word -> option byte) : Prop :=
forall x : word, IMG_RO_LO <= bv_unsigned x < IMG_RO_HI -> m x = None.
Lemma img_ro_bytes_ok : forallb (fun c => zallb (img_byte_ok tfibsegs) (YP09.c_off c) (Z.to_nat (c_len c))) img_ro_chunks = true.
Proof. vm_compute. reflexivity. Qed.
Lemma img_ro_chunks_inside : Forall (fun c => IMG_RO_LO <= YP09.c_off c /\ YP09.c_off c + c_len c <= IMG_RO_HI /\ exists n, YP09.c_val c = CImg n) img_ro_chunks.
Proof. unfold img_ro_chunks, IMG_RO_LO, IMG_RO_HI. repeat (apply Forall_cons; [cbn; split; [lia|]; split; [lia | eexists; reflexivity]|]). apply Forall_nil. Qed.
Lemma region_ok_img_of : forall E m,
(forall a, IMG_RO_LO <= a < IMG_RO_HI -> img_byte_ok tfibsegs a = true -> mbyte tfibsegs m a = img_byte tfibsegs a) ->
region_ok tfibsegs E m img_ro_region.
Proof.
intros E m Hm. unfold region_ok, img_ro_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold IMG_RO_LO; lia|]. split; [unfold IMG_RO_HI; lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & n & Hv).
pose proof (proj1 (forallb_forall _ _) img_ro_bytes_ok c Hc) as Hz. cbn beta in Hz.
pose proof (zallb_sound _ _ _ (YP09.c_off c + i) Hz ltac:(lia)) as Hb.
rewrite !Z.add_0_l. destruct c as [co cv]; cbn [YP09.c_off YP09.c_val] in *. subst cv. cbn [cbyte].
rewrite (Hm (co + i)) by (first [lia | exact Hb]).
unfold img_byte_ok in Hb. destruct (img_byte tfibsegs (co + i)) as [b|]; [|discriminate]. exists b. split; reflexivity.
Qed.
Lemma region_ok_img_clean : forall E m, ro_clean m -> region_ok tfibsegs E m img_ro_region.
Proof.
intros E m Hc. apply region_ok_img_of. intros a Ha _. unfold img_byte, mbyte.
rewrite (Hc (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by (unfold IMG_RO_LO, IMG_RO_HI in Ha; lia); exact Ha). reflexivity.
Qed.
Lemma ro_img_of_clean : forall m, ro_clean m -> ro_img m.
Proof. intros m Hc E. apply region_ok_img_clean. exact Hc. Qed.
Lemma ro_clean_mrestrict : forall (Hd : word -> bool) m, ro_clean m -> ro_clean (mrestrict Hd m).
Proof. intros Hd m Hc x Hx. unfold mrestrict. rewrite (Hc x Hx). destruct (Hd x); reflexivity. Qed.
Lemma ro_img_kept : forall (Hd : word -> bool) (m m' : word -> option byte),
(forall x : word, IMG_RO_LO <= bv_unsigned x < IMG_RO_HI -> m' x = m x) -> ro_img (mrestrict Hd m) -> ro_img (mrestrict Hd m').
Proof.
intros Hd m m' Heq Hro E. pose proof (Hro E) as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [intros o Ho; exfalso; clear - Ho; cbn in Ho; lia|].
apply Forall_forall. intros c Hc i Hi. pose proof (proj1 (Forall_forall _ _) H4 c Hc i Hi) as (b & Hcb & Hmb). exists b. split; [exact Hcb|].
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & _).
revert Hmb. cbn [YP09.r_base base_val]. rewrite !Z.add_0_l. unfold mbyte, mrestrict.
rewrite (Heq (Z_to_bv 64 (YP09.c_off c + i))) by (rewrite unsigned_lit_small by (unfold IMG_RO_LO, IMG_RO_HI in *; lia); lia).
intros Hmb. exact Hmb.
Qed.
End d.
