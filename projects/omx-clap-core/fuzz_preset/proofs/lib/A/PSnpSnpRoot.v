(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image A, THE SNPRINTF ROOT (c-libc-stdio, keep group G3; c-omx-alloc 17:03Z
   ruling (b), parent c-libc-stdio 17:1xZ): the chain composed and stated as the engine's text
   YGcallSnp.asnprintf_realizes_xrom (c-omx-alloc's row, engine s1b bb085d091bbe, YGcallSnp.v 5b6dc61efe87), which
   h-mani-a8's field pa_snprintf_cf (origin/cold/h-mani-a8-preset-alloc fee5c13e19d0 lib/A/CfApiPreset.v) is at
   ARx := ARcf tfibsegs B, FF := FF_preset, K := snp_K_A = 2608 + 5552, gc / gv := cf_got_stack_chk_guard /
   cf_stack_chk_guard = 0xa2758 / 0x5fd910, img := [cf_img_lo, cf_img_top) = [0x10000, 0x600000), cr := snp_cr
   tfibsegs (= PSnpPcom.PCM_CR by its body), pc := cf_pc_snprintf = 0x42cc4.
   The chain and its windows (each the least its callee asks):
     snp_ok (K) <- AVSNI  svsni_ok (KV = 8064 = 0x870 + Kvs) <- APCOMMON pcom_preset_x (Kpc = 2320),
                                                                AVSN svsn_ok (Kvs = 5904 = 304 + Kvi)
     svsn_ok <- AMEMSET RowsSet's prow_memset_icpt_xm_A_lit (origin/cold/c-libc-stdio-rows-set a6f4ebf35892,
                         lib/A/PRowSet.v; YGcallMxmn.aintrin_realizes_xm at W_MEMSET = 0x52348),
                AVFPI PSnpSeamI.svfi_ok_seam (Kvi = 5600 = 0x30 + VFA_DEPTH; L3 musl vfprintf through the GXA seam,
                      L1 printf_common at Kp = 2320)
   so 8160 <= K, which snp_K_A meets with equality. The family FF_preset_x lo got (PSnpPfFam.v) takes its stability
   and monotonicity from PSnpSeamFF.v, its inclusion in the seam's family from PSnpSeamI.FF_preset_x_ro, and
   printf_common's from PSnpPfFam.FF_preset_x_pcom (through pcom_preset_x). The laws are ONE record, the engine's
   AR_laws_x (RowsSet's row takes it whole; every field the chain reads is its projection, stk_bounds_x is the engine
   lemma YCbqG.stk_bounds_x); the Section's only other hypotheses are TfibSyms and alx_band_pres (c-omx-alloc's field
   20, its text written out until the Definition lands); the world's w_H8 field is the world record's own, YA0n.w_H8
   (YA0n.v:25), which PSnpSeamReady.v reads. The read-only premise arodata_okP of the text is not read.
   rule 24: proves function snprintf (kind: composition of the chain's walks and leaves at preset image A). *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpSnpRoot.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FMsnprintfPf PSnpShared PSnpSx PSnpPfFam.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA Require
AsanFacts CopyCall SetCall StrnlenCall G_printf_core_common G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require Import IImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PSnpSeamDef.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PSnpSeamNorm PSnpSeamReady PSnpSeam.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PSnpSeamFm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AE2p PSnpI PSnpSvfi.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0x PSnpPcTbl PSnpPcom PSnpSnp PSnpSvsni PSnpSvsn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PSnpSeamI PSnpSeamFF PRowSet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3 Require FMgxa_bzcj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YGcallSnp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpLeaves.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_qck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_memcpyw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_memsetw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_memchrw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_strnlenw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Spec.StrFun.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3.FMgxa_mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3.RT_gxa_strnlen.
Import ListNotations.
Local Open Scope Z_scope.
(* the zify flag as the old-pin build saw it (PSnpGwrc exported `false` there; it is Local since #102 L1 e1ecbbc792f4) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module GXC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GVA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GSA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_printf_snfsink.
Module GCC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.CopyCall.
Module GSC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.SetCall.
Module GNC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.StrnlenCall.
Module NM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpSeamNorm.
Module SR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpSeamReady.
Module SM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpSeam.

Module BR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.R_m2s.
Module BQ := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_qck.
Module BMW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_memcpyw.
Module BSW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_memsetw.
Module BCW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_memchrw.
Module BNW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.A.I_strnlenw.
Module BSF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpBz.Spec.StrFun.

Module FMM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3.FMgxa_mem.
Module RSN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PSnpL3.RT_gxa_strnlen.

Module CJM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib.Mem.

#[local] Existing Instance N_img_asan.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Context {HLx : Z}.
Hypothesis LAWS : YCbqG.AR_laws_x tfibsegs B ARx HLx.
Hypothesis TB : AF0m.TfibSyms B.
(* AR_laws_x field 20 alx_band_pres (c-omx-alloc 14:56Z / 15:51Z), written out until its Definition lands *)
Hypothesis alx_band_pres : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_band_rw a ->
  w_H W (w64 a) = false -> ~ in_vis0 ly a -> aview tfibsegs (w_H W) mem a <> None.

(* ---- the fields the chain reads ---- *)
Let lframe : ARx_frame_law tfibsegs B ARx := alx_frame tfibsegs B ARx LAWS.
Let lstack : ARx_stack_law tfibsegs B ARx := alx_stack tfibsegs B ARx LAWS.
Let lzsh : ARx_zshadow_law tfibsegs B ARx := alx_zshadow tfibsegs B ARx LAWS.
Let lzshb : ARx_zshadow_byte_law tfibsegs ARx := alx_zshadow_byte tfibsegs B ARx LAWS.
Let lcells : ARx_const_cells_law tfibsegs B ARx := alx_const_cells tfibsegs B ARx LAWS.
Let llay : ARx_layout_ok_law tfibsegs ARx := alx_layout_ok tfibsegs B ARx LAWS.
Lemma lbounds : forall ly S Hp W mem md,
  ARx ly S Hp W mem md -> kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. intros ly S Hp W mem md HA. exact (YCbqG.stk_bounds_x tfibsegs B ARx LAWS ly S Hp W mem md HA). Qed.

(* ---- the read-only ranges: every read-only byte lies in one of PCM_CR's segments ---- *)
Lemma ro_cov_pcm : NM.ro_covered PSnpPcom.PCM_CR.
Proof.
intros a Ha. unfold CJM.ro_addr in Ha.
destruct (find_segment tfibsegs (bv_unsigned a) 1) as [sg|] eqn:E; [|discriminate].
destruct (FMgxa_bzcj.find_segment_rng tfibsegs (bv_unsigned a) 1 sg E) as (Hin & H1 & H2).
apply Exists_exists. exists (Z.of_N (seg_base sg), Z.of_N (seg_size sg)). split.
- unfold PSnpPcom.PCM_CR. apply (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s)))).
  apply filter_In. split; [exact Hin | exact Ha].
- unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma ESTACK_val : ESTACK = 4096.
Proof. reflexivity. Qed.

(* ---- the text's top from the chain's top: the text adds only the read-only premise, unread ---- *)
Lemma xrom_of_top : forall rlo rhi FF K gc gv img_lo img_hi cr pc,
  sh_asnprintf_realizes_x tfibsegs B ARx FF K gc gv img_lo img_hi cr pc ->
  YGcallSnp.asnprintf_realizes_xrom tfibsegs B ARx rlo rhi FF K gc gv img_lo img_hi cr pc.
Proof.
intros rlo rhi FF K gc gv img_lo img_hi cr pc H. unfold YGcallSnp.asnprintf_realizes_xrom.
unfold sh_asnprintf_realizes_x in H. intros ly S Hp W regs mem md d n f xs ws T cval. intros.
apply (H ly S Hp W regs mem md d n f xs ws T cval); assumption.
Qed.

(* ---- THE ROOT ---- *)
Theorem snprintf_xrom_A : forall rlo rhi lo got K img_lo img_hi,
  0x10000 <= lo -> got <= AE2p.A_GOT_canary -> 8160 <= K -> img_lo <= 65536 -> 0x600000 <= img_hi ->
  YGcallSnp.asnprintf_realizes_xrom tfibsegs B ARx rlo rhi (FF_preset_x lo got) K
    AE2p.A_GOT_canary AE2p.A_canary img_lo img_hi PSnpPcom.PCM_CR PSnpI.PC_snprintf.
Proof.
intros rlo rhi lo got K img_lo img_hi Hlo Hgot HK Hil Hih.
pose proof ESTACK_val as HES.
pose proof (PSnpSeamFF.FF_preset_x_stable64 lo got) as STAB.
pose proof (PSnpSeamFF.FF_preset_x_mono lo got) as MONO.
assert (Hgt : got <= AF0x.TFIB_IMG_END).
{ assert (E : AE2p.A_GOT_canary <= AF0x.TFIB_IMG_END) by (apply Z.leb_le; vm_compute; reflexivity). lia. }
(* L1, printf_common at 2320, the image's read-only ranges *)
pose proof (PSnpPcom.pcom_preset_x B ARx lframe lstack llay lcells lbounds TB 2320 lo got ltac:(lia) Hgt) as APC0.
assert (EPC : PSnpI.A_PCOM = PSnpPcTbl.PF_PRINTF_COMMON) by reflexivity.
assert (APC : sh_apcommon_realizes_xz tfibsegs B ARx (FF_preset_x lo got) 2320 PSnpPcom.PCM_CR PSnpI.A_PCOM)
  by (rewrite EPC; exact APC0).
(* L3 + svfi_ok: the vfprintf interceptor at 5600 *)
pose proof (PSnpSeamI.svfi_ok_seam B ARx lframe lstack lzsh lzshb lcells llay lbounds alx_band_pres TB
              (FF_preset_x lo got) img_lo img_hi PSnpPcom.PCM_CR 2320 5600 STAB MONO
              (PSnpSeamI.FF_preset_x_ro lo got Hlo Hgot) Hil ltac:(rewrite PSnpSeam.sa_globals_top; lia)
              ro_cov_pcm ltac:(rewrite PSnpSeam.sa_vfa_depth; lia) ltac:(lia) APC) as AVFPI.
(* L2, the memset interceptor at W_MEMSET (RowsSet) *)
pose proof (PRowSet.prow_memset_icpt_xm_A_lit B ARx HLx LAWS TB) as AMEMSET0.
assert (EMS : PSnpI.W_MEMSET = 0x523dc) by reflexivity.
assert (AMEMSET : YGcallMxmn.aintrin_realizes_xm tfibsegs B ARx OSet PSnpI.W_MEMSET) by (rewrite EMS; exact AMEMSET0).
(* musl vsnprintf at 5904 *)
pose proof (PSnpSvsn.svsn_ok B ARx lframe lstack lzshb lbounds (FF_preset_x lo got) STAB MONO 5904 5600
              AE2p.A_GOT_canary AE2p.A_canary img_lo img_hi PSnpPcom.PCM_CR ltac:(lia) ltac:(lia) eq_refl eq_refl
              AMEMSET AVFPI) as AVSN.
(* the vsnprintf interceptor at 8064 *)
pose proof (PSnpSvsni.svsni_ok B ARx lframe lstack lcells lbounds TB (FF_preset_x lo got) STAB MONO
              AE2p.A_GOT_canary AE2p.A_canary img_lo img_hi PSnpPcom.PCM_CR 8064 5904 2320
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) APC AVSN) as AVSNI.
(* snprintf at K *)
pose proof (PSnpSnp.snp_ok B ARx lframe lstack lcells lbounds TB (FF_preset_x lo got)
              AE2p.A_GOT_canary AE2p.A_canary img_lo img_hi PSnpPcom.PCM_CR 8064 K STAB MONO ltac:(lia) ltac:(lia)
              AVSNI) as TOP.
exact (xrom_of_top rlo rhi _ K _ _ img_lo img_hi _ _ TOP).
Qed.

End R.
