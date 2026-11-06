(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfFmI.v (cold/port-fm-rtprintf-param 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 5 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMsnprintfFmI.table); names: record RT_IImgA -> A_img RecAsanVfA.N_img_asan_vf; YImgTop zify_pre_hook added after the last Require. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMsnprintfFmI.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv); the zify hook that unfolds YImgTop.IMG_TOP / IMG_LO dropped (rate's YImgTop states both as notations, which lia reads as they are). *)
(* fm.asan's snprintf over the shared contract, closed on the GXA route: FMsnprintfFm.fm_snprintf_shared instantiated at
   fm's format family FF_fm, the read-only image fm_cr (FMsnprintfCr.v), printf_common from RtPrintf.Pcommon
   (RT_pf_shU.pcom_shz), the FILE memset (FMsnprintfMs32.memset_icpt_realizesU) and musl vfprintf from RtPrintf.GxSeam's
   seam (FMsnprintfSeamI.fm_seam_inst). New file. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/FMsnprintfFmI.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/FMsnprintfFmI.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/FMsnprintfFmI.v keeps its donor's comment text) is kept as lib/A/FMsnprintfFmI.v writes it. *)
(* Modified by RtPrintf.GxSeam on cold/port-fm-gxseam: uses fm_vfprintf_seam_closed; READY moved to the per-call store. *)
(* Modified by RtPrintf.Param: fm_snprintf_gxa_r / _r_AR renamed fm_snprintf_gxa / fm_snprintf_gxa_AR (no premise beyond AR_laws, TfibSyms). *)
(* Modified by RtPrintf (R-1 W0-inst): FF_fmP PK and fm_snprintf_gxaP for any covered-piece predicate PK with its four arms;
   FF_fm and fm_snprintf_gxa are their instances at fm's pieces, statements unchanged. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import YB1v YE34 YF0l YF0m YF0x YE20 YE2y.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import FMH_Base FMsnprintfImg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import PfFacts SnShared SnSx.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnFF SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RT_pf_sh RT_pf_shU FMsnprintfMs32.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require FMgxaSeamPf FMgxaSeam FMsnprintfFm FMsnprintfCr FMsnprintfSeamI.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA Require G_vfprintf_snf.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require Import RecAsanVfBR.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- fm's format family ---- *)
(* GxSeam's pf_family_ro at fm's .rodata (formats from 0x10000 up to the GOT slot sym 0x22e18 = 0x9a638) and
   RtPrintf.Pcommon's two further facts: a nonempty format, and every string with its NUL word in application memory;
   FF_fmP PK is the same family for the conversions PK covers (R-1 W0), FF_fm its instance at fm's pieces *)
Definition FF_fmP (PK : pf_piece -> Prop) : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall PK ps /\ pf_args_asan rd rs ws args /\
    pf_text ps args = Some T /\ pf_prec_pos ps args /\
    0x10000 <= f /\ f + Z.of_nat (length fmt) + 1 <= 0x9cdf8 /\ pf_args_slack ws args /\
    fmt <> [] /\ RT_pf_sh.pf_args_amem ws args.
Definition FF_fm : fmt_fam := FF_fmP pf_fm_piece.

Lemma FF_fmP_stable64 : forall PK, ff_stable64 (FF_fmP PK).
Proof.
intros PK rd rd' rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham) Hc.
destruct (fam_reads_stable64 rd rd' rs f fmt ws args Hc Hf Ha) as [Hf' Ha'].
exists fmt, ps, args. repeat (split; [assumption|]). exact Ham.
Qed.
Lemma FF_fm_stable64 : ff_stable64 FF_fm.
Proof. exact (FF_fmP_stable64 pf_fm_piece). Qed.

Lemma FF_fmP_mono : forall PK, ff_mono (FF_fmP PK).
Proof.
intros PK rd rs rs' f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham) Hs.
exists fmt, ps, args.
split; [exact (fmt_at_mono rd rs rs' f fmt Hf Hs)|]. split; [exact Hp|]. split; [exact Hk|].
split; [exact (pf_args_asan_mono rd rs rs' ws args Ha Hs)|]. repeat (split; [assumption|]). exact Ham.
Qed.
Lemma FF_fm_mono : ff_mono FF_fm.
Proof. exact (FF_fmP_mono pf_fm_piece). Qed.

Lemma FF_fmP_ro : forall PK rd rs f ws T, FF_fmP PK rd rs f ws T -> pf_family_ro PK 0x10000 0x9cdf8 rd rs f ws T.
Proof.
intros PK rd rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & _ & _).
exists fmt, ps, args. repeat (split; [assumption|]). exact Hsl.
Qed.
Lemma FF_fm_ro : forall rd rs f ws T, FF_fm rd rs f ws T -> pf_family_ro pf_fm_piece 0x10000 0x9cdf8 rd rs f ws T.
Proof. exact (FF_fmP_ro pf_fm_piece). Qed.

(* R-1 W0-ff: FF_fmP PK is inside printf_common's family at any wider piece predicate PK' (RT_pf_sh.FF_pcomK), since
   fm's formats end at the GOT slot 0x9a638, below the image top TFIB_IMG_END = 0x5f7000 *)
Lemma FF_fmP_pcomK : forall PK PK', (forall p, PK p -> PK' p) ->
  forall rd rs f ws T, FF_fmP PK rd rs f ws T -> RT_pf_sh.FF_pcomK PK' rd rs f ws T.
Proof.
intros PK PK' HPK rd rs f ws T (fmt & ps & args & Hf & Hp & Hk & Ha & Ht & Hq & Hlo & Hhi & Hsl & Hne & Ham).
assert (E : TFIB_IMG_END = 0x5fa000) by (vm_compute; reflexivity).
exists fmt, ps, args.
refine (conj Hf (conj Hne (conj _ (conj Hp (conj (Forall_impl _ HPK Hk) (conj Ha (conj Ham (conj Ht Hq)))))))).
rewrite E. lia.
Qed.
Lemma FF_fm_pcom : forall rd rs f ws T, FF_fm rd rs f ws T -> RT_pf_sh.FF_pcom rd rs f ws T.
Proof. intros rd rs f ws T H. apply RT_pf_sh.FF_pcom_K. exact (FF_fmP_pcomK pf_fm_piece pf_fm_piece (fun p Hp => Hp) rd rs f ws T H). Qed.

(* ---- the instance ---- *)
Module GXC := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GVA := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.GXA.G_vfprintf_snf.
#[local] Existing Instance N_img_asan_vf.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* fm's snprintf on the GXA route, for every window K >= fm_glue_img + VF_DEPTH = 8160 (the seam's readiness is
   discharged in FMgxaSeamFm.v, so this takes no hypothesis for it), for fm's family at any covered-piece predicate
   PK whose pieces have their four arms (R-1 W0): the three seam arms (FMgxaSeamPf.v) and the printf_common arm
   (RT_pf_sh.v pcom_pcx_arm) *)
Theorem fm_snprintf_gxaP : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall (PK : pf_piece -> Prop),
  (forall p, PK p -> FMgxaSeamPf.seam_text_arm p) -> (forall p, PK p -> FMgxaSeamPf.seam_pargs_arm p) ->
  (forall p, PK p -> FMgxaSeamPf.seam_bytes_arm p) -> (forall p, PK p -> RT_pf_sh.pcom_pcx_arm p) ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizesU tfibsegs B (FF_fmP PK) K FM_GOT_canary FM_canary img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB PK AT AP AB APC img_lo img_hi K Hlo Hhi HK.
assert (HV : GVA.VFA_DEPTH = FMsnprintfFm.GXA_VF_DEPTH) by (rewrite FMgxaSeam.sa_vfa_depth; reflexivity).
apply (FMsnprintfFm.fm_snprintf_shared B LAWS TB (FF_fmP PK) img_lo img_hi FMsnprintfCr.fm_cr 2320
  FMsnprintfFm.GXA_VF_DEPTH K (FF_fmP_stable64 PK) (FF_fmP_mono PK)).
- unfold ESTACK, FMsnprintfFm.GXA_VF_DEPTH. lia.
- unfold FMsnprintfFm.GXA_VF_DEPTH. lia.
- exact HK.
- apply (sh_apcommon_realizesUz_weaken tfibsegs B (RT_pf_sh.FF_pcomK PK) (FF_fmP PK) 2320 RT_pf_shU.PCM_CR
    FMsnprintfCr.fm_cr A_PCOM (FF_fmP_pcomK PK PK (fun p Hp => Hp))).
  + intros r1 Hr1. exists r1. split; [exact Hr1 | lia].
  + exact (RT_pf_shU.pcom_shzK B LAWS TB PK APC 2320 ltac:(lia)).
- exact (FMsnprintfMs32.memset_icpt_realizesU B LAWS TB).
- apply (sh_avfprintf_icpt_realizesUx_ff tfibsegs B (pf_family_ro PK 0x10000 0x9cdf8) (FF_fmP PK)
    FMsnprintfFm.GXA_VF_DEPTH FM_GOT_canary FM_canary img_lo img_hi FMsnprintfCr.fm_cr A_SNW A_VFP (FF_fmP_ro PK)).
  exact (FMsnprintfSeamI.fm_seam_instP B LAWS TB PK AT AP AB FMsnprintfFm.GXA_VF_DEPTH img_lo img_hi FMsnprintfCr.fm_cr
    ltac:(rewrite HV; lia) Hlo Hhi FMsnprintfCr.fm_cr_ro_covered).
Qed.

(* fm's pieces: literals, %s, %.*s *)
Theorem fm_snprintf_gxa : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizesU tfibsegs B FF_fm K FM_GOT_canary FM_canary img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB.
exact (fm_snprintf_gxaP B LAWS TB pf_fm_piece FMgxaSeamPf.pf_fm_text_arms FMgxaSeamPf.pf_fm_pargs_arms
  FMgxaSeamPf.pf_fm_bytes_arms RT_pf_sh.pf_fm_pcx_arms).
Qed.
(* the AR form (no user-poisoned range) *)
Corollary fm_snprintf_gxa_AR : forall B, AR_laws tfibsegs B -> TfibSyms B ->
  forall img_lo img_hi K, img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi ->
  FMsnprintfFm.fm_glue_img + FMsnprintfFm.GXA_VF_DEPTH <= K ->
  sh_asnprintf_realizes tfibsegs B FF_fm K FM_GOT_canary FM_canary img_lo img_hi FMsnprintfCr.fm_cr PC_snprintf.
Proof.
intros B LAWS TB img_lo img_hi K Hlo Hhi HK.
apply sh_asnprintf_of_U. exact (fm_snprintf_gxa B LAWS TB img_lo img_hi K Hlo Hhi HK).
Qed.
End f.
