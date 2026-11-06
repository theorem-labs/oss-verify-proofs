(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: image A's lemmas derived from the frame-area interface FCiface.fs_iface, for the walks of
   __asan_stack_malloc_{0,1,3} and __asan_set_shadow_f5. No walk is in this file.
   - img_cover_x       = AF0x.img_cover_of_ledger, with ALedger -> fi_img.
   - const_lookup_sym_x, const_lookup_x = AF0x.tfib_const_lookup_sym / tfib_const_lookup, with ARm -> fi_const.
   - rodata_ok_x       = AE2y.rodata_ok, with ARm -> ARx.
   Image numerals: none here; the image enters through the core's AF0x (TFIB_IMG_LO / TFIB_IMG_END, preset's top 0x600000 at image A'),
   AF0m (Tfib_const, TfibSyms) and the image's own segment list. *)
(* Modified by Theorem Labs, 2026-10: for the snprintf chain restated over ARx (route (a), c-omx-hpreset 10:51Z), only
   lib/A/FCxA.v:44-78 of origin/cold/c-omx-alloc-preset-s1b e47394d004f6 (const_lookup_sym_x, const_lookup_x,
   rodata_ok_x; img_cover_x is not copied), renamed const_lookup_sym_lx / const_lookup_lx / rodata_ok_lx, with
   `Hypothesis I : fs_iface tfibsegs B ARx` and its `fi_const` replaced by the one engine law the proof reads,
   `Hypothesis alx_const_cells : ARx_const_cells_law tfibsegs B ARx` (Reusable/YCbqG.v:139-141, AR_laws_x field
   alx_const_cells), which has the same statement as fi_const. Port-fm's rodata_ok (A/AE2y.v) over `ARU_ARm` plus
   `ARU_mem_low` becomes this one lemma at ARx. No image numeral in this file; no '+ 8' range or presence form. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis alx_const_cells : ARx_const_cells_law tfibsegs B ARx.
Hypothesis TB : TfibSyms B.
Lemma const_lookup_sym_lx : forall ly S Hp W mem md e (w : nat) e',
ARx ly S Hp W mem md ->
cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros ly S Hp W mem md e w e' HAR E.
apply (cell_holds_val_mem B ly (w_H W) mem e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) (alx_const_cells ly S Hp W mem md HAR)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma const_lookup_lx : forall ly S Hp W mem md a (w : nat) v,
ARx ly S Hp W mem md ->
cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
val_mem tfibsegs (mrestrict (w_H W) mem) a w v.
Proof.
intros ly S Hp W mem md a w v HAR E. exact (const_lookup_sym_lx ly S Hp W mem md (ANum a) w (ANum v) HAR E).
Qed.
Lemma rodata_ok_lx : forall l ly S Hp W mem md E,
rodata_chk ly l = true -> ARx ly S Hp W mem md ->
Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) (map ro_region l).
Proof.
intros l ly S Hp W mem md E Hc HAR. unfold rodata_chk in Hc.
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
rewrite Z.add_0_l. exact (const_lookup_lx ly S Hp W mem md (base + off) (N.to_nat n) v HAR (const_chk_sound _ _ _ _ H1)).
Qed.
End b.
End a.
