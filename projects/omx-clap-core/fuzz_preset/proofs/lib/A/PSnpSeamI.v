(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 503 of its 563 lines of code are new or changed and 644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSnpSeam.v, with its module paths and module names changed; 36 of its 79 lines of code are new or changed and 520 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSnpSeamFm.v; 81 of its 143 lines of code are new or changed and 17 lines of the source are left out. *)
(* THE GXA SEAM AT fm.asan's MUSL VFPRINTF, INSTANTIATED: FMgxaSeam.fm_vfprintf_seam with fm's three interceptor
   call contracts (FMgxa_mem.memcpy_stack_contract_A, FMgxa_mem.memset_stack_contract_A,
   RT_gxa_strnlen.strnlen_stack_contract_A) and their ready predicates, fm's format family pf_family_ro
   pf_fm_piece over [0x10000, 0x9a638) (the image data below the GOT slot of __stack_chk_guard), and fm's cells:
   the stack-protector GOT slot and guard, sn_write and musl vfprintf, each the symbol GXA names (checked by
   vm_compute). READY, the readiness the seam takes, is discharged in FMgxaSeamFm.v, so this file takes no
   hypothesis for it. No function is proved here: this file instantiates the proved seam. New file. *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's restatement for fuzz_preset image A (L3-V2) of proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfSeamI.v at origin/cold/port-fm-rtprintf-param 3e35620c52e: fm_seam_inst -> leaf_vfprintf_A, L3 of the snprintf chain (PSnpLeaves.leaf_vfprintf, = sh_avfprintf_icpt_realizes_xx over ARx with Hp fixed) at preset A's musl vfprintf A_VFP = sym 0x7f000400 = 0x950a0 with sink A_SNW = sym 0x7f000300 = 0x9a708, the stack-protector GOT cell AE2p.A_GOT_canary = sym 0x22e18 = 0xa2758 and guard AE2p.A_canary = sym 0x34288 = 0x5fd910 (each by vm_compute against CJ.RL.I.IImgA.N_img_asan), for preset's put_string pieces (pf_preset_piece: PLit | Pc | Px04) over [0x10000, A_GOT_canary); then the lift to h-mani-a8's family (PSnpPfFam.FF_preset_x lo got) and svfi_ok (PSnpSvfi.v) with its AVFP discharged (svfi_ok_seam). The Section's hypotheses are PSnpSeamFm.v's: the laws, alx_band_pres, TfibSyms. Runtime-option cells read: none (PSnpSeam.v). The sentences above name fm's files and numbers. *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpSeamI.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
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

#[local] Existing Instance N_img_asan.

(* ---- preset A's cells and code addresses are the symbols GXA names on the rebuilt image record ---- *)
Lemma si_got : AE2p.A_GOT_canary = @sym N_img_asan 0x22e18.
Proof. vm_compute. reflexivity. Qed.
Lemma si_guard : AE2p.A_canary = @sym N_img_asan 0x34288.
Proof. vm_compute. reflexivity. Qed.
Lemma si_snw : PSnpI.A_SNW = @sym N_img_asan GXC.K_SN_WRITE.
Proof. vm_compute. reflexivity. Qed.
Lemma si_vfp : PSnpI.A_VFP = @sym N_img_asan 0x7f000400.
Proof. vm_compute. reflexivity. Qed.
(* the family's range: from the image's first byte to the GOT slot *)
Lemma si_fam_lo : 65536 <= 0x10000.
Proof. lia. Qed.

(* put_string's pieces are covered pieces *)
Lemma pf_preset_cov : forall p, pf_preset_piece p -> match p with PLit _ | Pc | Px04 | Ps | Pps => True | _ => False end.
Proof. intros p Hp. destruct p; cbn in Hp |- *; tauto. Qed.

(* ---- put_string's family (h-mani-a8's FF_preset, PSnpPfFam.FF_preset_x) lies inside the seam's ---- *)
Lemma pf_args_asan_len : forall rd rs ws args, pf_args_asan rd rs ws args -> (length args <= length ws)%nat.
Proof.
intros rd rs ws args. revert ws. induction args as [|a args IH]; intros ws H; [cbn; lia|].
destruct ws as [|w ws]; [destruct H|]. destruct H as [_ H]. cbn. specialize (IH ws H). lia.
Qed.

Lemma pf_args_slack_noptr : forall args ws, (length args <= length ws)%nat -> (forall s, ~ In (APtr s) args) ->
  pf_args_slack ws args.
Proof.
induction args as [|a args IH]; intros ws HL HN; [destruct ws; exact I|].
destruct ws as [|w ws]; [cbn in HL; lia|]. cbn in HL.
assert (HN' : forall s, ~ In (APtr s) args) by (intros s Hs; exact (HN s (or_intror Hs))).
destruct a as [v|u|s].
- exact (IH ws ltac:(lia) HN').
- exact (IH ws ltac:(lia) HN').
- exfalso. exact (HN s (or_introl eq_refl)).
Qed.

Lemma FF_preset_x_ro : forall lo got, 0x10000 <= lo -> got <= AE2p.A_GOT_canary ->
  forall rd rs f ws T, FF_preset_x lo got rd rs f ws T ->
  pf_family_ro pf_preset_piece 0x10000 AE2p.A_GOT_canary rd rs f ws T.
Proof.
intros lo got Hlo Hgot rd rs f ws T (fmt & ps & args & HF & HP & HK & HA & HT & HPP & Hl & Hh & _).
exists fmt, ps, args.
repeat (split; [assumption|]).
split; [lia|]. split; [lia|].
exact (pf_args_slack_noptr args ws (pf_args_asan_len rd rs ws args HA) (pf_text_preset_noptr ps args T HK HT)).
Qed.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
(* the AR_laws_x fields the seam and its readiness use (YCbqG.v), each under its field's name, and the engine lemma
   stk_bounds_x's statement (7792959a2abb YCbqG.v:308) *)
Hypothesis alx_frame : ARx_frame_law tfibsegs B ARx.
Hypothesis alx_stack : ARx_stack_law tfibsegs B ARx.
Hypothesis alx_zshadow : ARx_zshadow_law tfibsegs B ARx.
Hypothesis alx_zshadow_byte : ARx_zshadow_byte_law tfibsegs ARx.
Hypothesis alx_const_cells : ARx_const_cells_law tfibsegs B ARx.
Hypothesis alx_layout_ok : ARx_layout_ok_law tfibsegs ARx.
Hypothesis stk_bounds_x : forall ly S Hp W mem md,
  ARx ly S Hp W mem md -> kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
(* AR_laws_x field 20 alx_band_pres (c-omx-alloc 14:56Z), inline until its Definition lands *)
Hypothesis alx_band_pres : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_band_rw a ->
  w_H W (w64 a) = false -> ~ in_vis0 ly a -> aview tfibsegs (w_H W) mem a <> None.
Hypothesis TB : AF0m.TfibSyms B.

(* L3: musl vfprintf at preset A, for put_string's pieces over [0x10000, the GOT slot) *)
Theorem leaf_vfprintf_A : forall K img_lo img_hi cr,
  GVA.VFA_DEPTH <= K -> img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan <= img_hi -> NM.ro_covered cr ->
  leaf_vfprintf tfibsegs B ARx (pf_family_ro pf_preset_piece 0x10000 AE2p.A_GOT_canary) K
    AE2p.A_GOT_canary AE2p.A_canary img_lo img_hi cr PSnpI.A_SNW PSnpI.A_VFP.
Proof.
intros K img_lo img_hi cr HK Hlo Hhi HCOV.
rewrite leaf_vfprintf_is, si_vfp.
exact (vfprintf_seam_closed_x B ARx alx_frame alx_stack alx_zshadow alx_zshadow_byte alx_const_cells alx_layout_ok
         stk_bounds_x alx_band_pres TB pf_preset_piece pf_preset_cov
         K AE2p.A_GOT_canary AE2p.A_canary img_lo img_hi PSnpI.A_SNW 0x10000 AE2p.A_GOT_canary cr HK si_got si_guard si_snw Hlo Hhi
         si_fam_lo ltac:(rewrite si_got at 1; lia) HCOV).
Qed.

(* the same at put_string's family (h-mani-a8's FF_preset with its two image bounds as parameters) *)
Corollary leaf_vfprintf_preset : forall K lo got img_lo img_hi cr,
  GVA.VFA_DEPTH <= K -> img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan <= img_hi -> NM.ro_covered cr ->
  0x10000 <= lo -> got <= AE2p.A_GOT_canary ->
  leaf_vfprintf tfibsegs B ARx (FF_preset_x lo got) K
    AE2p.A_GOT_canary AE2p.A_canary img_lo img_hi cr PSnpI.A_SNW PSnpI.A_VFP.
Proof.
intros K lo got img_lo img_hi cr HK Hlo Hhi HCOV Hl Hg.
pose proof (leaf_vfprintf_A K img_lo img_hi cr HK Hlo Hhi HCOV) as L.
rewrite leaf_vfprintf_is in L |- *.
exact (sh_avfprintf_icpt_realizes_xx_ff tfibsegs B ARx _ _ K _ _ img_lo img_hi cr _ _ (FF_preset_x_ro lo got Hl Hg) L).
Qed.

(* svfi_ok (PSnpSvfi.v) with its AVFP discharged at musl vfprintf's window Kv = VFA_DEPTH, for any family inside the
   seam's (FF_preset_x lo got is, FF_preset_x_ro) *)
Corollary svfi_ok_seam : forall FF img_lo img_hi cr Kp K,
  ff_stable64 FF -> ff_mono FF ->
  (forall rd rs f ws T, FF rd rs f ws T -> pf_family_ro pf_preset_piece 0x10000 AE2p.A_GOT_canary rd rs f ws T) ->
  img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan <= img_hi -> NM.ro_covered cr ->
  0x30 + GVA.VFA_DEPTH <= K -> 0x30 + Kp <= K ->
  sh_apcommon_realizes_xz tfibsegs B ARx FF Kp cr PSnpI.A_PCOM ->
  sh_avfprintf_icpt_realizes_xx tfibsegs B ARx FF K AE2p.A_GOT_canary AE2p.A_canary img_lo img_hi cr
    PSnpI.A_SNW PSnpI.A_VFPI.
Proof.
intros FF img_lo img_hi cr Kp K STAB MONO Hsub Hlo Hhi HCOV HKK HKP APCOMMON.
assert (HV : ESTACK <= GVA.VFA_DEPTH) by (vm_compute; discriminate).
apply (PSnpSvfi.svfi_ok B ARx alx_frame alx_stack alx_const_cells stk_bounds_x TB FF _ _ img_lo img_hi cr Kp
         GVA.VFA_DEPTH K STAB MONO HV HKK HKP APCOMMON).
pose proof (leaf_vfprintf_A GVA.VFA_DEPTH img_lo img_hi cr (Z.le_refl _) Hlo Hhi HCOV) as L.
rewrite leaf_vfprintf_is in L.
exact (sh_avfprintf_icpt_realizes_xx_ff tfibsegs B ARx _ _ _ _ _ img_lo img_hi cr _ _ Hsub L).
Qed.

End I.
