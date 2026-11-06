(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Divembc SpinAlg.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require ShapeAlg Divembc SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm AsanInit Bothny9 Starr0h Stargqr Bothr3g Boot52v.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb Bothy0u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothjqf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Starazj Bothjqf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Both6eh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Both6eh Bothg0u Both56i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starr0h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Stargqr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothr3g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Boot52v OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothy0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothjqf.Star1i1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starazj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothjqf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both6eh.Starfcw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both6eh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothg0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both56i.   (* [comment removed for export] *)
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.

Section MainB.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  Variables uid gid nofile sigmask hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.
  Variable urandom : InputStream.   (* [comment removed for export] *)
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Variable MAIN : A.TSet.
  Hypothesis MAIN_nil : MAIN [].

  (* [comment removed for export] *)
  Section Both.
    Hypothesis Hbrk : valid_brk BSEGS brk0.
    Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    Hypothesis CERT0 : check BSEGS IT0b BOTH NX0 (@AsanInit.blim BL) (XNb2 NX0) XE0 XB0 HS_both KC0b BFUELb FUELb None both_init startup_plan_both = COk startup_shape_both.
    Hypothesis CERT2 : check BSEGS IT2b BOTH NX2b (@AsanInit.blim BL) (XNb2 NX2b) XE0 XB0 HS_both2 KC2b BFUEL2b FUEL2b None HS_both_0 startup_plan_both2 = COk startup_shape_both2.
    Hypothesis CERT2B : check BSEGS IT2b BOTH NX2b (@AsanInit.blim BL) (XNb2 NX2b) XE0 XB0 HS_both2b KC2b BFUEL2b FUEL2b None HS_both_1 startup_plan_both2b = COk startup_shape_both2.
    #[local] Notation HOLEB HS :=
      (forall E R FULL model,
          cs_ok BSEGS BOTH (@AsanInit.blim BL) (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) fs E HS R FULL model ->
          A.srealizes BSEGS (cfg_of BSEGS R MAIN_PC_BOTH FULL model) MAIN).
    Hypothesis MAIN1_sound : HOLEB HS_both2_1.
    Hypothesis MAIN2_sound : HOLEB HS_both2_2.
    Hypothesis MAIN3_sound : HOLEB HS_both2b_1.
    Hypothesis MAIN4_sound : HOLEB HS_both2b_2.

    Theorem both_startup_main_A : forall apc : N, Z.of_N apc = a_entry BOTH ->
      A.srealizes BSEGS (init_config BSEGS apc BPH sp brk0 mbase rdraw (@AsanInit.blim BL)
                                     (AsanInit.inp argv envp fs stdin uid gid nofile sigmask hw groups net urandom))
                  MAIN.
    Proof.
      intros apc Hapc. apply srealizes_B2A.
      apply (both_startup_main sp rdraw brk0 mbase argv envp fs stdin uid gid nofile sigmask hw groups net urandom Hsp Hbrk Hva Hve Hfit Huid Hhw CERT0 CERT2 CERT2B MAIN MAIN_nil);
        [ .. | exact Hapc]; intros E R FULL model HC; apply srealizes_A2B.
      - exact (MAIN1_sound E R FULL model HC).
      - exact (MAIN2_sound E R FULL model HC).
      - exact (MAIN3_sound E R FULL model HC).
      - exact (MAIN4_sound E R FULL model HC).
    Qed.

    Corollary both_startup_main_A_entry :
      A.srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw (@AsanInit.blim BL)
                                     (AsanInit.inp argv envp fs stdin uid gid nofile sigmask hw groups net urandom))
                  MAIN.
    Proof. exact (both_startup_main_A _ (both_entry_pc)). Qed.
  End Both.
End MainB.
