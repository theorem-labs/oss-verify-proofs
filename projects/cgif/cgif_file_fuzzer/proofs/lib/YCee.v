(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YI09 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef YF0m YB1w YCej YD2l YCeh.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YE2k YE26 YE27 YE2m.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YD1k.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0z YI10 YI12 YC4a YC8i YCbj YC1f YC20 YC8g YC44 YC93 YC97.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YCbp YC7z YCbh YC7y YCbi YC7x YCbl YC9l YC8v YC8n YCb8.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCe6 YCe7 YCe8 YCec YCe9 YCeb YCea YCkf.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCed.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Lemma tfibX_ro_relro : forall a, 0x9dca8 <= a < 0x9ef18 -> in_ro_tfa a.
Proof. intros a Ha. right. exact Ha. Qed.
Lemma tfibX_ro_seg1 : forall a, 0x10000 <= a < 0x30000 -> in_ro_tfa a.
Proof.
intros a Ha. left.
assert (P : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs) 0 = Some (65536, 131072, false)) by (vm_compute; reflexivity).
destruct tfibsegs as [|s1 rest]; [discriminate|]. cbn [map nth_error] in P. injection P as P1 P2 P3.
exists s1. split; [left; reflexivity|]. split; [exact P3|]. lia.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation B := TfibB.
#[local] Abbreviation HB := TfibB_syms.
Lemma tfibX_rom_cell : forall (H : word -> bool) mem lo hi a n v,
arodata_okP tfibsegs 0x9dca8 0x9ef18 B (aview tfibsegs H mem) ->
(forall x, lo <= x < hi -> in_ro_tfa x) ->
forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r)) Tfib_owned_static = true ->
0x10000 <= lo -> hi <= 0x9f000 ->
lo <= a -> a + Z.of_nat n <= hi -> img_cell_chk a n v = true ->
val_mem tfibsegs (mrestrict H mem) a n v.
Proof.
intros H mem lo hi a n v HRO Hro Hst Hlo Hhi Ha1 Ha2 Hc.
apply (val_mem_img (mrestrict H mem) lo hi a n v); [| exact Ha1 | exact Ha2 | exact Hc].
apply img_rd_of_aview. intros x Hx. apply HRO; [exact (Hro x Hx) | exact (tfib_not_owned_static B lo hi x HB Hst Hx) |].
rewrite (ts_errno B HB). unfold TFIB_ERRNO. lia.
Qed.
Definition tfib_wcbF_closed : twcbF_spec tfibsegs tfib_K B 0x8131c := tfib_wcbF B tfibX_LAWS tfibX_PALib0 HB tfibX_AIL.
Definition tfib_cbbX_closed := tfib_cbbX B tfibX_LAWS tfibX_PALib1 tfibX_AMEMCPY.
Definition tfib_cblX_closed := tfib_cblX B tfibX_LAWS tfibX_PALib1.
Lemma tfib_lzwX_closed : YCbh.tlzw_specX tfibsegs B ameter_triv (xn_pb XN0) (@pa_val _ _ PB_tfib1 A_TEXT + YC93.A_LZW) CTX_LZW_GenerateStream 0x9dca8 0x9ef18.
Proof.
refine (@tfib_lzwX fx rc tfib_sink_head tfibX_RO1 B tfibX_PALib1 tfibX_LAWS ameter_triv ameter_triv_laws tfibX_AMALLOC4 tfibX_AFREE4 tfibX_AFREEN4 (xn_pb XN0) tfibX_AMEMSET tfibX_AMEMCPY _ CTX_LZW_GenerateStream _ _ _ _ _).
- unfold lzw_traces. cbn [map app]. tfibX_universe.
- intros c Hc. cbv [CTX_LZW_GenerateStream In] in Hc.
repeat (destruct Hc as [<- | Hc]; [tfibX_universe_in|]). destruct Hc.
- intros H mem HRO. unfold lzw_rodata_ok.
apply (tfibX_rom_cell H mem 0x103b0 0x103b8); [exact HRO | intros x Hx; apply tfibX_ro_seg1; lia | vm_compute; reflexivity | lia | lia | (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]) | (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]) | vm_compute; reflexivity].
- cbn [as_gp TfibB]. unfold TFIB_GP. lia.
- intros nP idl _ _. unfold pro_msum, epi_msum. cbn. lia.
- intros nP idl _ _. unfold pro_msum, epi_msum. cbn. lia.
Qed.
Lemma tfibX_got_rawnew : forall (H : word -> bool) mem, arodata_okP tfibsegs 0x9dca8 0x9ef18 B (aview tfibsegs H mem) ->
val_mem tfibsegs (mrestrict H mem) 0x9ee88 8 0x83dcc.
Proof.
intros H mem HRO.
apply (tfibX_rom_cell H mem 0x9ee88 0x9ee90); [exact HRO | intros x Hx; apply tfibX_ro_relro; lia | vm_compute; reflexivity | lia | lia | lia | cbn; lia | vm_compute; reflexivity].
Qed.
Lemma tfibX_got_rawadd : forall (H : word -> bool) mem, arodata_okP tfibsegs 0x9dca8 0x9ef18 B (aview tfibsegs H mem) ->
val_mem tfibsegs (mrestrict H mem) 0x9ee90 8 0x845d8.
Proof.
intros H mem HRO.
apply (tfibX_rom_cell H mem 0x9ee90 0x9ee98); [exact HRO | intros x Hx; apply tfibX_ro_relro; lia | vm_compute; reflexivity | lia | lia | lia | cbn; lia | vm_compute; reflexivity].
Qed.
Lemma tfibX_deep_rawnew : forall c, In c CTX_cgif_raw_newgif -> (2 <= length c)%nat.
Proof. intros c Hc. cbv [CTX_cgif_raw_newgif In] in Hc. repeat (destruct Hc as [<- | Hc]; [cbn; lia|]). destruct Hc. Qed.
Lemma tfibX_um_rawnew : forall c, In c CTX_cgif_raw_newgif ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) :: flat_map (fun ra => if ra =? pc_malloc_ra0 (as_code B) then [] else [ra]) ((0x83dcc + 0x16c) :: c))) (as_universe B).
Proof. intros c Hc. cbv [CTX_cgif_raw_newgif In] in Hc. repeat (destruct Hc as [<- | Hc]; [tfibX_universe_in|]). destruct Hc. Qed.
Lemma tfib_rawnewX_closed : forall hw, 0 <= hw < 2 ^ 64 -> hw mod 2 = 0 ->
trawnew_specX tfibsegs tfib_K B ameter_triv 0x83dcc CTX_cgif_raw_newgif 0x8131c hw 0x9dca8 0x9ef18.
Proof.
intros hw Rhw Phw. unfold trawnew_specX. intros.
eapply (YCb8.pb_rawnewX (PI := PB_tfib1) B tfibX_PALib1 tfibX_LAWS tfibX_ML tfibX_AMEMSET tfibX_AMEMCPY tfibX_ASM2 tfibX_SMP tfibX_ASF tfibX_FFL tfibX_PALibF1 0x8131c hw
ltac:(split; [lia | reflexivity]) (conj Rhw Phw) tfib_K tfibX_AIL ameter_triv ameter_triv_laws ameter_triv_fs_laws tfibX_AMALLOC4 tfib_wcbF_closed
tfibX_got_rawnew CTX_cgif_raw_newgif tfibX_deep_rawnew tfibX_um_rawnew); eassumption.
Qed.
Lemma tfib_raw_closeX_closed : forall hw, 0 <= hw < 2 ^ 64 ->
trawclose_specX tfibsegs tfib_K B ameter_triv 0x8656c [pc_free_ra0 (as_code B); 0x86614] 0x8131c hw.
Proof.
intros hw Rhw.
exact (YC9l.pb_raw_closeX (PI := PB_tfib1) B tfibX_LAWS tfibX_PALib1 ameter_triv tfibX_AFREE4 0x8131c hw
ltac:(split; [lia | reflexivity]) Rhw tfib_K tfibX_AIL tfib_wcbF_closed eq_refl (tfib_trailer_shadow B HB)).
Qed.
Lemma tfibX_raw_close_trace : In [pc_free_ra0 (as_code B); 0x86614] (as_universe B).
Proof. tfibX_universe_in. Qed.
Lemma tfibX_deep_rawadd : forall c, In c CTX_cgif_raw_addframe -> (2 <= length c)%nat.
Proof. intros c Hc. cbv [CTX_cgif_raw_addframe In] in Hc. repeat (destruct Hc as [<- | Hc]; [cbn; lia|]). destruct Hc. Qed.
Lemma tfibX_ctx_rawadd_lzw1 : forall l, In l CTX_cgif_raw_addframe -> In (0x84a50 :: l) CTX_LZW_GenerateStream.
Proof. intros l Hl. cbv [CTX_cgif_raw_addframe In] in Hl. unfold CTX_LZW_GenerateStream. cbn [In]. repeat (destruct Hl as [<- | Hl]; [tauto|]). destruct Hl. Qed.
Lemma tfibX_ctx_rawadd_lzw2 : forall l, In l CTX_cgif_raw_addframe -> In (0x84dd8 :: l) CTX_LZW_GenerateStream.
Proof. intros l Hl. cbv [CTX_cgif_raw_addframe In] in Hl. unfold CTX_LZW_GenerateStream. cbn [In]. repeat (destruct Hl as [<- | Hl]; [tauto|]). destruct Hl. Qed.
Lemma tfibX_trace_rawadd : forall (pcf ra : Z) (regsT regs : bvmap 5 word) ch,
In (raZ regs :: spine ch) CTX_cgif_raw_addframe -> raZ regsT = ra ->
((pcf = pc_free_ra0 (as_code B) /\ ra = 0x83dcc + 0x1018) \/ (pcf = pc_free_ra0 (as_code B) /\ ra = 0x83dcc + 0x1300) \/
(pcf = pc_malloc_ra0 (as_code B) /\ ra = 0x83dcc + 0xc94)) ->
In (call_trace0 pcf regsT ((spZ regs, raZ regs, s0Z regs) :: ch)) (as_universe B).
Proof.
intros pcf ra regsT regs ch Hctx Hra Hpc.
rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). rewrite Hra.
cbv [CTX_cgif_raw_addframe In] in Hctx.
destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]];
(repeat (destruct Hctx as [H | Hctx]; [rewrite <- H; tfibX_universe_in|]); destruct Hctx).
Qed.
Lemma tfib_rawaddX_closed : trawadd_specX tfibsegs tfib_K B ameter_triv XN0 0x845d8 CTX_cgif_raw_addframe 0x8131c 0x9dca8 0x9ef18.
Proof.
refine (@tfib_cgif_raw_addframeX_w fx rc tfibX_RO0 B tfibX_LAWS tfibX_PALib0 tfibX_PALib1 HB tfibX_AIL tfibX_ML tfibX_AMEMSET tfibX_AMEMCPY tfibX_ASM1 tfibX_SMP tfibX_ASF tfibX_FFL tfibX_PALibF1
tfibX_got_rawadd CTX_cgif_raw_addframe tfibX_deep_rawadd ameter_triv ameter_triv_laws ameter_triv_fs_laws XN0 _ _ _ tfibX_AMALLOC4 tfibX_AFREE4
CTX_LZW_GenerateStream tfib_lzwX_closed tfibX_ctx_rawadd_lzw1 tfibX_ctx_rawadd_lzw2 tfibX_trace_rawadd).
- intros N idl _ _. cbn. lia.
- intros N idl _ _. cbn. lia.
- intros N idl _ _. cbn. lia.
Qed.
Lemma tfibX_ctx_flush_rawadd : forall l, In l CTX_flushFrame -> In (0x837ec :: l) CTX_cgif_raw_addframe.
Proof. intros l Hl. cbv [CTX_flushFrame In] in Hl. unfold CTX_cgif_raw_addframe. cbn [In]. repeat (destruct Hl as [<- | Hl]; [tauto|]). destruct Hl. Qed.
Lemma tfibX_trace_flush : forall (pcf ra : Z) (regsT regs : bvmap 5 word) ch,
In (raZ regs :: spine ch) CTX_flushFrame -> raZ regsT = ra ->
((pcf = pc_free_ra0 (as_code B) /\ ra = 0x80cf0 + 0x2b08) \/ (pcf = pc_malloc_ra0 (as_code B) /\ ra = 0x80cf0 + 0x25d4) \/
(pcf = pc_malloc_ra0 (as_code B) /\ ra = 0x80cf0 + 0x2798)) ->
In (call_trace0 pcf regsT ((spZ regs, raZ regs, s0Z regs) :: ch)) (as_universe B).
Proof.
intros pcf ra regsT regs ch Hctx Hra Hpc.
rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). rewrite Hra.
cbv [CTX_flushFrame In] in Hctx.
destruct Hpc as [[-> ->] | [[-> ->] | [-> ->]]];
(repeat (destruct Hctx as [H | Hctx]; [rewrite <- H; tfibX_universe_in|]); destruct Hctx).
Qed.
Theorem tfib_flushX_closed : tflush_specX tfibsegs tfib_K B ameter_triv XN0 0x826f4 CTX_flushFrame 0x8131c 0x9dca8 0x9ef18.
Proof.
refine (@tfib_flushFrameX fx rc tfib_sink_head tfibX_RO0 B tfibX_PALib0 tfibX_LAWS tfibX_ML tfibX_AMEMCPY tfibX_ASM1 tfibX_SMP tfibX_ASF tfibX_FFL tfibX_AMEMCMP tfibX_ABCMP tfibX_PALibF0
CTX_flushFrame 0x8131c tfib_K tfibX_AIL ameter_triv ameter_triv_laws ameter_triv_fs_laws XN0 tfibX_AMALLOC4 tfibX_AFREE4 tfibX_AFREEN4
tfibX_trace_flush CTX_cgif_raw_addframe tfib_rawaddX_closed _ _ _ tfibX_ctx_flush_rawadd).
- intros N M _ _. cbn. lia.
- intros N M _ _. cbn. lia.
- intros M _. cbn. lia.
Qed.
End b.
