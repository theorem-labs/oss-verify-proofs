(* copied from cgif_file lib/A/AD1n.v by rules r1,r2,r3,r4,r6,rC, generator ed5c0821ce98f1d99fcd7466c0aa65f7671a8daf838ab8f2b2da9f5038f22ee4 *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1n.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YM02 YP0m YP09 YK04 YA0i YA0n YA0e YG00 YG01 YG05 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0l AF0m AD1t AD20 AD1vcf AD1icf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0dcf YG0ncf YG0ucf YGcfNames YGcfTok.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG01cf YGcfPath.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Context {ci : YGcfNames.CfImg} {cp : YGcfNames.CfParams}.

Section c.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws_cf tfibsegs B.
Hypothesis ML : model_laws_cf (as_universe B).
Hypothesis AMALLOC : amalloc_realizes_cf tfibsegs B.
(* drv_pre's ROOM_cf is the model law's three room premises; the site's room_cf n S keeps a granted path off the
   class-full arm (YGcfPath.malloc_cf_success_of_room), the cf form of the donor's ns-flag argument *)
Theorem tfib_malloc_site : malloc_site_tfa B.
Proof.
intros ly S Hp W regs mem md n KB HPRE Ha0 Hn Hlive Hroom Htr2 Htr1 HAI KBLK.
pose proof (acall_pre_of_drv B _ _ _ _ _ _ _ HPRE) as HAP. pose proof HPRE as (HAR & _ & [_ HROOM] & _).
pose proof (amc_wf _ _ _ _ _ (proj1 HAR)) as HWF. pose proof HWF as W0. unfold Wf_cf in W0.
pose proof (shape_cf_of_WfP_cf _ _ _ _ _ W0) as Hsh.
pose proof cf_malloc_max_ge as CMG.
assert (Hn' : 0 <= n < cf_malloc_max) by (unfold MALLOC_MAX in *; lia).
set (trc := call_trace ly (pc_malloc_ra0 (as_code B)) regs []).
assert (Htr : In trc (as_universe B)).
{ subst trc. destruct (call_trace_drv ly regs (pc_malloc_ra0 (as_code B))) as [-> | ->]; assumption. }
pose proof (AMALLOC ly S Hp W regs mem md n [] HAP Ha0 Hn' Hlive (admits_fix _ _ _ (ts_universe B HB) Htr)) as HREAL. fold trc in HREAL.
destruct HROOM as (R1 & R2 & R3).
pose proof (mlr_malloc_cf _ ML S n trc HWF Hn' Hlive (admits_fix _ _ _ (ts_universe B HB) Htr) R1 R2 R3) as HTOK.
apply (SRr_srealizes tfibsegs W (cfg_at tfibsegs (pc_wrap_malloc (as_code B)) regs mem md) _ _
(amreal_SRr04 tfibsegs _ W _ _ HREAL (atok_cf_asafe _ _ _ HTOK) (atok_cf_agprog _ _ _ HTOK) (atok_cf_nospin _ _ HTOK)) HAI).
intros W' c' Hwle HAI' (r & tr & Hpath & Hgf & Hleaf). cbn [cfg_model] in HAI'.
pose proof (malloc_cf_success_of_room n trc S tr r Hsh Hpath Hgf Hroom) as HNN.
destruct r as [p S']. cbn [fst] in HNN.
destruct Hleaf as (ly' & regs' & mem' & md' & -> & HPOST & Hres & _ & _ & HXP & _). cbn [fst snd] in HPOST, Hres, HXP, HAI'.
apply (KBLK ly' S' W' regs' mem' md' trc tr p HNN Htr Hpath); [| exact HXP | exact Hres | exact Hwle | exact HAI'].
pose proof HPOST as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|]. split; [| exact P7].
intros a Ha Ho Ho' Hs HnE. apply P6; [exact Ha | exact Ho | exact Ho' | exact Hs |].
intros [[_ X] | X]; apply HnE; [left | right]; exact X.
Qed.
End c.
End b.
