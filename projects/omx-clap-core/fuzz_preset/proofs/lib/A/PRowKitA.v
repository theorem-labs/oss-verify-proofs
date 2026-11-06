(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A (A/AB1v.v Asan tfibsegs, A/AF0m.v TfibSyms): the image half of c-libc-stdio's runtime-row kit
   (lib/Reusable/PRowKit.v is the image-free half). rule 24: proves no function (kind: segment lemma).
   - prk_rodata_ok_cc = lib/A/AE2y.v rodata_ok (:81) and lib/A/FCxA.v rodata_ok_x (:61), with its premise ARm B ly S (aview ..) (cgif's AR)
     replaced by the one ARm piece the proof reads, the image's const cells
     Forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly): AR_laws_x's field 16 alx_const_cells
     (Reusable/YCbqG.v ARx_const_cells_law) gives it at every ARx state. FCxA.rodata_ok_x takes the frame-area
     interface fs_iface, whose other fields AR_laws_x does not give.
   lib/AU/PRowKitA.v is the image-B twin over Reusable/YE2y.v / YF0m.v.
   Image numerals: none here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma prk_rodata_ok_cc : forall B, TfibSyms B -> forall l ly (H : word -> bool) mem E,
rodata_chk ly l = true -> Forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly) ->
Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region l).
Proof.
intros B TB l ly H mem E Hc HC. unfold rodata_chk in Hc.
rewrite forallb_forall in Hc. apply Forall_map. apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hc _ Hin). cbn [fst snd] in Hc. apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [H0 Hhi].
apply Z.leb_le in H0. apply Z.leb_le in Hhi.
unfold ro_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
rewrite forallb_forall in Hcs. apply Forall_map. apply Forall_forall. intros [[off n] v] Hc'.
specialize (Hcs _ Hc'). cbn [fst snd] in Hcs.
apply andb_prop in Hcs as [Hcs H4]. apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
unfold ro_chunk. cbn [fst snd].
eapply (chunk_ok_val tfibsegs E _ 0 (base + off) n (SLit v) v); [reflexivity | lia | lia |].
rewrite Z.add_0_l. apply (cell_holds_val_mem B ly H mem (ANum (base + off)) (N.to_nat n) (ANum v)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs H mem)) (as_const B ly)) HC).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ (const_chk_sound _ _ _ _ H1)).
Qed.
End a.
