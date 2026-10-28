(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YI09 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0m AB1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AE26 AE27.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0x YI0y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AI12.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbl ACec ACb6 ACb8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ _ PB_tfib) (@pa_relro_lo _ _ PB_tfib) (@pa_relro_hi _ _ PB_tfib)}.
Remark tfib_rawnewX_pc : @pa_val _ _ PB_tfib1 A_TEXT + AF_asan3_cgif_raw_newgif = 0x84178.   Proof. reflexivity. Qed.
Definition tfib_rawnewX := @ACb8.pb_rawnewX fx rc _ PB_tfib1.
Check tfib_rawnewX.
Theorem tfib_rawnewX_spec : forall (B : asyms) (MT : ameter_ops) (CTX : list (list Z)),
AR_laws tfibsegs B -> PALib (PI := PB_tfib1) B -> PALib (PI := PB_tfib) B -> TfibSyms B -> asink_img_laws tfibsegs B tfib_K ->
model_laws (as_universe B) ->
aintrin_realizes tfibsegs B OSet (pa_sigma (PAImg := PB_tfib1) AS_asan_memset) -> aintrin_realizes tfibsegs B OCpy (pa_sigma (PAImg := PB_tfib1) AS_asan_memcpy) ->
astack_malloc_realizes tfibsegs B 2 -> stack_malloc_progressP B -> astack_free_law tfibsegs B -> frame_flag_lawP tfibsegs B ->
PALibF (PI := PB_tfib1) B ->
ameter_laws MT -> ameter_fs_laws MT -> amalloc04_rule tfibsegs B MT ->
(forall (H : word -> bool) mem, arodata_okP tfibsegs (pa_relro_lo (PAImg := PB_tfib1)) (pa_relro_hi (PAImg := PB_tfib1)) B (aview tfibsegs H mem) ->
val_mem tfibsegs (mrestrict H mem) (pa_val (PAImg := PB_tfib1) (A_OBJ 7)) 8 0x84178) ->
(forall c, In c CTX -> (2 <= length c)%nat) ->
(forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) :: flat_map (fun ra => if ra =? pc_malloc_ra0 (as_code B) then [] else [ra]) ((0x84178 + 0x168) :: c))) (as_universe B)) ->
trawnew_specX tfibsegs tfib_K B MT 0x84178 CTX 0x81a18 0 (pa_relro_lo (PAImg := PB_tfib1)) (pa_relro_hi (PAImg := PB_tfib1)).
Proof.
intros B MT CTX LAWS TL1 TL0 TB AIL ML AMS AMC ASM2 SMP ASF FFL TLF MLAW MLAWF AM4 HGOT7 HDEEP HUM.
unfold trawnew_specX. intros.
eapply (ACb8.pb_rawnewX (PI := PB_tfib1) B TL1 LAWS ML AMS AMC ASM2 SMP ASF FFL TLF 0x81a18 0
ltac:(split; [lia | reflexivity]) ltac:(split; [lia | reflexivity]) tfib_K AIL MT MLAW MLAWF AM4 (tfib_wcbF B LAWS TL0 TB AIL) HGOT7 CTX HDEEP HUM); eassumption.
Qed.
End a.
