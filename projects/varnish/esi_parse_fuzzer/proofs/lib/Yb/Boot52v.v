(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm AsanInit Asanjze Starob1 Star2r0 Asann0a.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanlzb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asang3k.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Staruoz Asang3k.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan5d5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan5d5 Asano8r Asanc90.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanjze OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starob1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Star2r0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asann0a OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb.Asankdu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanlzb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang3k.Startjo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Staruoz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asang3k OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan5d5.Starnkk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asan5d5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asano8r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanc90.   (* [comment removed for export] *)
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Asan.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.

Module B.   (* [comment removed for export] *)
  Notation TSet := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg.TSet.
  Notation node_ok := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg.node_ok.
  Notation realizes := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg.realizes.
  Notation to_spin := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Divembc.to_spin.
  Notation srealizes := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg.srealizes.
  Notation t_eq := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.ShapeAlg.t_eq.
End B.
Module A.   (* [comment removed for export] *)
  Notation TSet := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg.TSet.
  Notation node_ok := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg.node_ok.
  Notation realizes := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg.realizes.
  Notation to_spin := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc.to_spin.
  Notation srealizes := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.srealizes.
  Notation t_eq := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg.t_eq.
End A.

Section Bridge.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma to_spin_B2A : forall ms model, B.to_spin segs ms model -> A.to_spin segs ms model.
  Proof.
    intros ms model H. induction H as [ms model Hs Hst | ms model ms' model' Hs Hst H IH].
    - exact (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc.ts_spin segs ms model Hs Hst).
    - exact (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Divembc.ts_step segs ms model ms' model' Hs Hst IH).
  Qed.
  Lemma to_spin_A2B : forall ms model, A.to_spin segs ms model -> B.to_spin segs ms model.
  Proof.
    intros ms model H. induction H as [ms model Hs Hst | ms model ms' model' Hs Hst H IH].
    - exact (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Divembc.ts_spin segs ms model Hs Hst).
    - exact (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Divembc.ts_step segs ms model ms' model' Hs Hst IH).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma srealizes_B2A : forall c T, B.srealizes segs c T -> A.srealizes segs c T.
  Proof.
    intros c T H. induction H as [c I evs nx T i0 Hn Hc IH | c Hh | c Hs Hh | c T T' H IH Heq].
    - exact (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.srz_node segs c I evs nx T i0 Hn IH).
    - exact (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.srz_halt segs c Hh).
    - destruct Hs as [[] _].   (* [comment removed for export] *)
    - exact (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg.srz_conseq segs c T T' IH Heq).
  Qed.
  Lemma srealizes_A2B : forall c T, A.srealizes segs c T -> B.srealizes segs c T.
  Proof.
    intros c T H. induction H as [c I evs nx T i0 Hn Hc IH | c Hh | c Hs Hh | c T T' H IH Heq].
    - exact (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg.srz_node segs c I evs nx T i0 Hn IH).
    - exact (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg.srz_halt segs c Hh).
    - destruct Hs as [[] _].   (* [comment removed for export] *)
    - exact (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.SpinAlg.srz_conseq segs c T T' IH Heq).
  Qed.
End Bridge.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MainA.
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

  Section Asan.
    Hypothesis Hbrk : valid_brk ASEGS brk0.
    Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    Hypothesis CERT0 : check ASEGS IT0 ASAN NX0 (@AsanInit.blim BL) (XNa2 NX0) XE0 XB0 HS_asan KC0 BFUEL FUEL None asan_init startup_plan = COk startup_shape.
    Hypothesis CERT2 : check ASEGS IT2 ASAN NX2 (@AsanInit.blim BL) (XNa2 NX2) XE0 XB0 HS_asan2 KC2 BFUEL2 FUEL2 None HS_asan_0 startup_plan2 = COk startup_shape2.
    Hypothesis CERT2B : check ASEGS IT2 ASAN NX2 (@AsanInit.blim BL) (XNa2 NX2) XE0 XB0 HS_asan2b KC2 BFUEL2 FUEL2 None HS_asan_1 startup_plan2b = COk startup_shape2.
    #[local] Notation HOLE HS :=
      (forall E R FULL model,
          cs_ok ASEGS ASAN (@AsanInit.blim BL) (SINV0 APH sp rdraw brk0 argv envp uid hw) (argH0 APH sp rdraw argv envp uid hw) fs E HS R FULL model ->
          A.srealizes ASEGS (cfg_of ASEGS R MAIN_PC FULL model) MAIN).
    Hypothesis MAIN1_sound : HOLE HS_asan2_1.
    Hypothesis MAIN2_sound : HOLE HS_asan2_2.
    Hypothesis MAIN3_sound : HOLE HS_asan2b_1.
    Hypothesis MAIN4_sound : HOLE HS_asan2b_2.

    Theorem asan_startup_main_A : forall apc : N, Z.of_N apc = a_entry ASAN ->
      A.srealizes ASEGS (init_config ASEGS apc APH sp brk0 mbase rdraw (@AsanInit.blim BL)
                                     (AsanInit.inp argv envp fs stdin uid gid nofile sigmask hw groups net urandom))
                  MAIN.
    Proof.
      intros apc Hapc. apply srealizes_B2A.
      apply (asan_startup_main sp rdraw brk0 mbase argv envp fs stdin uid gid nofile sigmask hw groups net urandom Hsp Hbrk Hva Hve Hfit Huid Hhw CERT0 CERT2 CERT2B MAIN MAIN_nil);
        [ .. | exact Hapc]; intros E R FULL model HC; apply srealizes_A2B.
      - exact (MAIN1_sound E R FULL model HC).
      - exact (MAIN2_sound E R FULL model HC).
      - exact (MAIN3_sound E R FULL model HC).
      - exact (MAIN4_sound E R FULL model HC).
    Qed.

    (* [comment removed for export] *)
    Corollary asan_startup_main_A_entry :
      A.srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw (@AsanInit.blim BL)
                                     (AsanInit.inp argv envp fs stdin uid gid nofile sigmask hw groups net urandom))
                  MAIN.
    Proof. exact (asan_startup_main_A _ (asan_entry_pc)). Qed.
  End Asan.
End MainA.
