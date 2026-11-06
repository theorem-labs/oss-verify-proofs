(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, with its module paths, module names and numbers changed; 1071 of its 1108 lines of code are new or changed and 293 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/TjModel.v; 52 of its 106 lines of code are new or changed and 1054 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaStep DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoRoList DiscoImg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import TjSpec TjBase DiscoRo TjCuts TjEntry TjLoopCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SetShadowDef ConstsViewDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared PfFacts SnprintfDef SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDec SbDecPb ReacBoxName ReacBoxNamePb TjBoxRom.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import TjSnSh TjExit TjClose TjMac TjRoleSh TjModel TjBox TjPre TjTailSh TjImg TjCompose.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition REAC_DISCO_TABLE_JSON_STK : Z := 640 + SNPRINTF_STK.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PB_disco) (@pa_relro_lo _ disco_listing PB_disco) (@pa_relro_hi _ disco_listing PB_disco)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PB_disco).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PB_disco).
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM2 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASF : astack_free_law SEGS B.
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : SIGMA DS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi GC GV IMGLO IMGHI disco_fmt_lo disco_fmt_hi CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA DS___asan_memset).
Hypothesis AMEMCPY : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OCpy (SIGMA DS___asan_memcpy).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA DS___interceptor_trampoline_strlen).
Hypothesis mc_consts_unowned : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis ASSF5 : forall fq : YK11.FPState,
  aset_shadow_realizes (fx := fq) SEGS B (SIGMA DS___asan_set_shadow_f5) 0xf5.
Hypothesis ASM3 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 3.
Hypothesis ASM0 : forall fq : YK11.FPState, astack_malloc_realizes (fx := fq) SEGS B 0.
Theorem pb_reac_disco_table_json_gen : forall (STK : Z) (IMG : world SEGS -> (word -> option byte) -> Prop),
TJ_FRAME + SNPRINTF_STK <= STK -> tj_specP (PI := PB_disco) B STK 0 IMG.
Proof.
intros STK IMG HSTK.
assert (HSTKE : TJ_FRAME + ESTACK <= STK) by (assert (ESTACK <= SNPRINTF_STK) by (apply Z.leb_le; vm_compute; reflexivity); lia).
assert (HEVB : 0 <= 0) by lia.
assert (HEV : 8 * 0 <= 0) by lia.
pose proof (@tj_strs_disco rc) as TJS.
pose proof (@tj_pad_disco rc) as TJP. unfold tj_pad_stmt in TJP.
pose proof (@tj_rbn_rom_disco rc) as RBR.
pose proof (@tj_ro_kd_sep_disco rc) as KDS.
assert (HSBDEC : tsb_dec_spec (PI := PB_disco) B) by (eapply pb_sb_dec; eassumption).
assert (RBN : treac_box_name_spec (PI := PB_disco) B) by (eapply pb_reac_box_name; eassumption).
apply (pb_reac_disco_table_json (PI := PB_disco) B STK 0 0 IMG).
- intros FB. eapply pb_tj_entry; eassumption.
- intros FX FC FL. eapply pb_tj_pre; first [eassumption | exact (FL 0)].
- eapply pb_tj_exit; eassumption.
- intros FX. eapply pb_tj_close; eassumption.
- eapply pb_tj_mac; eassumption.
- eapply pb_tj_seg_role_sh; eassumption.
- eapply pb_tj_box; eassumption.
- eapply pb_tj_seg_unk; eassumption.
- eapply pb_tj_seg_tok; eassumption.
- eapply pb_tj_tail_sh; eassumption.
Qed.
Theorem pb_reac_disco_table_json_A : tj_specP (PI := PB_disco) B REAC_DISCO_TABLE_JSON_STK 0 (fun _ _ => True).
Proof.
apply pb_reac_disco_table_json_gen. apply Z.leb_le. vm_compute. reflexivity.
Qed.
End h.
End d.
