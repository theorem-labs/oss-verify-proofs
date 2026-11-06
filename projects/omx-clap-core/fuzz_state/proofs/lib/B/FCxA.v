(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: image A's lemmas derived from the frame-area interface FCiface.fs_iface, for the walks of
   __asan_stack_malloc_{0,1,3} and __asan_set_shadow_f5. No walk is in this file.
   - img_cover_x       = AF0x.img_cover_of_ledger, with ALedger -> fi_img.
   - const_lookup_sym_x, const_lookup_x = AF0x.tfib_const_lookup_sym / tfib_const_lookup, with ARm -> fi_const.
   - rodata_ok_x       = AE2y.rodata_ok, with ARm -> ARx.
   Image numerals: none here; the image enters through the core's AF0x (TFIB_IMG_LO / TFIB_IMG_END, preset's top 0x600000),
   AF0m (Tfib_const, TfibSyms) and the image's own segment list. *)
(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_preset (a working branch b120217aa206) to omx-clap-core/fuzz_state's ASan image A as fuzz_state's image-A lemmas over FCiface.fs_iface: module paths and the image numerals of A/FCimg.v (generated from fuzz_state.asan), nothing else. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/FCxA.v at cb01f65c0f3: fuzz_state.asan-ubsan's lemmas over FCiface.fs_iface. Changes: module paths (lib.A -> lib.B: AB1v -> YB1v, AB1w -> YB1w, AE34 -> YE34, AF0l -> YF0l, AF0m -> YF0m, AF0x -> YF0x, AE2y -> YE2y, AE3d -> YE3d, and A's FCimg / FCxA / FCm<k>r / FCm<k>s / FCf5 / FSH_Base -> their lib/B twins; the image-generic lib/A FSupoison, FSupoisonU, FSifaceU, SetShadowDefU and FSuwalk stay), nothing else; image B's segments AsanUbsan.AsanUbsan_segment_000 / _003 in place of Asan.Asan_segment_000 / _003 (bases read from the generated images/AsanUbsan.v, the same 0x10000 and 0x5fd000 as A's); no image numeral is typed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis I : fs_iface tfibsegs B ARx.
Lemma img_cover_x : forall ly S Hp W mem md, ARx ly S Hp W mem md -> img_cover ly.
Proof.
intros ly S Hp W mem md HAR. split.
- destruct (fi_img _ _ _ I ly S Hp W mem md AsanUbsan.AsanUbsan_segment_000 HAR ltac:(left; reflexivity)) as [H _].
cbn in H. unfold TFIB_IMG_LO. lia.
- destruct (fi_img _ _ _ I ly S Hp W mem md AsanUbsan.AsanUbsan_segment_003 HAR ltac:(do 3 right; left; reflexivity)) as [_ H].
cbn in H. unfold TFIB_IMG_END. lia.
Qed.
Hypothesis TB : TfibSyms B.
Lemma const_lookup_sym_x : forall ly S Hp W mem md e (w : nat) e',
ARx ly S Hp W mem md ->
cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e').
Proof.
intros ly S Hp W mem md e w e' HAR E.
apply (cell_holds_val_mem B ly (w_H W) mem e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) (fi_const _ _ _ I ly S Hp W mem md HAR)).
rewrite (ts_const B TB ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma const_lookup_x : forall ly S Hp W mem md a (w : nat) v,
ARx ly S Hp W mem md ->
cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) ->
val_mem tfibsegs (mrestrict (w_H W) mem) a w v.
Proof.
intros ly S Hp W mem md a w v HAR E. exact (const_lookup_sym_x ly S Hp W mem md (ANum a) w (ANum v) HAR E).
Qed.
Lemma rodata_ok_x : forall l ly S Hp W mem md E,
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
rewrite Z.add_0_l. exact (const_lookup_x ly S Hp W mem md (base + off) (N.to_nat n) v HAR (const_chk_sound _ _ _ _ H1)).
Qed.
End b.
End a.
