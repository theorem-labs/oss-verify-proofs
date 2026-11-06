(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_d.v (cold/port-fm-rtprintf-param 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/RT_pf_d.table). *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/RT_pf_d.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* R-1 row R-d (port-fm's R1-FREE-PIECES.md): the conversion %d (Pd) in ASan printf_common's scan, as W0-pcom's per-piece
   pcom arm (RT_pf_sh.v pcom_pcx_arm, origin/cold/h-grant-a2-r1-W0-pcom 6c733891261). The consumers take it as
   `forall p, PK p -> pcom_pcx_arm p`: RT_pf_sh.v pcx_K / pcomx_K, RT_pf_shU.v pcom_shzK, FMsnprintfFmI.v fm_snprintf_gxaP.
   %d is printf_common's grammar step pcx_dir (100 :: rest) = Some (false, PP_none, PK_int, rest) (I_pcxgram.v): no flag,
   width, precision or length modifier, an int conversion, so the walk consumes one argument word, pa_of (AInt v) = PA_i v,
   which pcx_fits accepts for PK_int, and gives it the coverage entry None (pc_cin1 Pd = [None]; ck_arg of PA_i is True).
   The seam arms of Pd are port-fm's lib/A/FMpfArmPdSeam.v (seam_text_arm_pd / seam_pargs_arm_pd / seam_bytes_arm_pd,
   with the seam-side control seam_pd_control); the printf_common-side control is lib/A/FMpfArmPdCtl.v.
   New file; nothing else is edited. *)
(* Modified by Theorem Labs, 2026-10: the proof is RT_pf_sh.v pcom_pcx_arm_ps (6c733891261 :141-147) with the step at
   %d in place of %s, the %d step as in origin/cold/c-libc-stdio-presetsnp-pcom a28a0fadbcc3
   proofs/omx-clap-core/fuzz_preset/lib/A/PSnpPcGram.v (its %c case) and origin/cold/h-disco-3-cand3 21bcb7200f7
   proofs/libreac/fuzz_disco/lib/A/Prog/pf_bridge.v pcx_cargs_ok (its Pd case). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Bz.A Require Import I_pcxgram.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import PfFacts.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import FMpfStep RT_pf_sh.
Import ListNotations.
Open Scope Z_scope.

Lemma pcom_pcx_arm_Pd : pcom_pcx_arm Pd.
Proof.
  intros fuel rest args c a' C _ H. destruct args as [|[v|u|s] a'']; cbn [pf_step] in H; try discriminate H.
  injection H as <- <-. split.
  - intros n W. exists (1 + n)%nat. cbn [pf_code app map pcx_walk]. cbn. rewrite W. reflexivity.
  - cbn [pf_code pc_cin1 app map]. cbn. reflexivity.
Qed.
