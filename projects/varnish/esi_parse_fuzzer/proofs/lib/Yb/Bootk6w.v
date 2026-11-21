(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the ASan+UBSan start-up bridge takes the input's kernel build, exec file name and SIGPIPE disposition and the launch's mmap-base and launch facts, its start-up invariant takes the new AsanInit arguments, and its start-up checks, their plans and their hand-off states are the ones computed at the run's CONFIG_RSEQ flag. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm AsanInit Bothny9 Bothr3g Boot52v.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb Bothy0u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothjqf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require BothRegen Bothjqf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Both6eh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Both6eh BothRegen2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.BothRegen OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.BothRegen2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothr3g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Boot52v OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothy0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothjqf.Star1i1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothjqf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both6eh.Starfcw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both6eh.   (* [comment removed for export] *)
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
  (* LPS 727298f3: [AsanInit.inp]'s three new fields *)
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sigdfl : bool.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  (* LPS 727298f3: valid_entry's mmap-base and launch conjuncts and valid_input's
     [valid_launch] *)
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hlaunch : valid_launch (AsanInit.inp argv envp fs stdin uid gid nofile sigmask hw groups net urandom kb execfn sigdfl).
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
                      (AsanInit.inp argv envp fs stdin uid gid nofile sigmask hw groups net urandom kb execfn sigdfl).
  Variable MAIN : A.TSet.
  Hypothesis MAIN_nil : MAIN [].

  (* [comment removed for export] *)
  Section Both.
    Hypothesis Hbrk : valid_brk BSEGS brk0.
    Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* LPS 727298f3: the three checks at the run's CONFIG_RSEQ flag, over the plans and hand-off
       states [BothRegen]/[BothRegen2] compute at it ([startup_cert_both], [startup_cert_both2],
       [startup_cert_both2b]). *)
    Hypothesis CERT0 : check BSEGS IT0b BOTH NX0 (@AsanInit.blim BL) (rseq_z (kb_rseq kb)) (XNb2 NX0) XE0 XB0 (HS_both_r (rseq_z (kb_rseq kb))) KC0b BFUELb FUELb None (both_init (rseq_z (kb_rseq kb))) (startup_plan_both_r (rseq_z (kb_rseq kb))) = COk startup_shape_both.
    Hypothesis CERT2 : check BSEGS IT2b BOTH NX2b (@AsanInit.blim BL) (rseq_z (kb_rseq kb)) (XNb2 NX2b) XE0 XB0 (HS_both2_r (rseq_z (kb_rseq kb))) KC2b BFUEL2b FUEL2b None (HS_both_0r (rseq_z (kb_rseq kb))) (startup_plan_both2_r (rseq_z (kb_rseq kb))) = COk startup_shape_both2.
    Hypothesis CERT2B : check BSEGS IT2b BOTH NX2b (@AsanInit.blim BL) (rseq_z (kb_rseq kb)) (XNb2 NX2b) XE0 XB0 (HS_both2b_r (rseq_z (kb_rseq kb))) KC2b BFUEL2b FUEL2b None (HS_both_1r (rseq_z (kb_rseq kb))) (startup_plan_both2b_r (rseq_z (kb_rseq kb))) = COk startup_shape_both2.
    #[local] Notation HOLEB HS :=
      (forall E R FULL model,
          cs_ok BSEGS BOTH (@AsanInit.blim BL) (SINV0 BOTH BPH sp rdraw brk0 mbase argv envp uid gid hw kb execfn)
                (argH0 sp rdraw argv envp kb execfn) fs E HS R FULL model ->
          A.srealizes BSEGS (cfg_of BSEGS R MAIN_PC_BOTH FULL model) MAIN).
    Hypothesis MAIN1_sound : HOLEB (HS_both2_1r (rseq_z (kb_rseq kb))).
    Hypothesis MAIN2_sound : HOLEB (HS_both2_2r (rseq_z (kb_rseq kb))).
    Hypothesis MAIN3_sound : HOLEB (HS_both2b_1r (rseq_z (kb_rseq kb))).
    Hypothesis MAIN4_sound : HOLEB (HS_both2b_2r (rseq_z (kb_rseq kb))).

    Theorem both_startup_main_A : forall apc : N, Z.of_N apc = a_entry BOTH ->
      A.srealizes BSEGS (init_config BSEGS apc BPH sp brk0 mbase rdraw (@AsanInit.blim BL)
                                     (AsanInit.inp argv envp fs stdin uid gid nofile sigmask hw groups net urandom kb execfn sigdfl))
                  MAIN.
    Proof.
      intros apc Hapc. apply srealizes_B2A.
      apply (both_startup_main sp rdraw brk0 mbase argv envp fs stdin uid gid nofile sigmask hw groups net urandom kb execfn sigdfl
               Hsp Hbrk Hva Hve Hfit Huid Hhw Hmb Hlaunch Hlau CERT0 CERT2 CERT2B MAIN MAIN_nil);
        [ .. | exact Hapc]; intros E R FULL model HC; apply srealizes_A2B.
      - exact (MAIN1_sound E R FULL model HC).
      - exact (MAIN2_sound E R FULL model HC).
      - exact (MAIN3_sound E R FULL model HC).
      - exact (MAIN4_sound E R FULL model HC).
    Qed.

    Corollary both_startup_main_A_entry :
      A.srealizes BSEGS (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw (@AsanInit.blim BL)
                                     (AsanInit.inp argv envp fs stdin uid gid nofile sigmask hw groups net urandom kb execfn sigdfl))
                  MAIN.
    Proof. exact (both_startup_main_A _ (both_entry_pc)). Qed.
  End Both.
End MainB.
