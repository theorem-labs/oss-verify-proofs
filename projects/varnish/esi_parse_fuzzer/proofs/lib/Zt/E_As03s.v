(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool Classical_Prop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.varnish.esi_parse_fuzzer.images.Plain.
Require OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require E_As0ui.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Spec LibIface V_Img0 D_TrLoop.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require E_As0ui.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require E_As0ui.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.ShapeEF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Img0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_TrLoop OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.D_Mak2g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState AClient ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv AInioec ALogic ARt_u2d AInit0 AInitL ASma77w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASma77w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ASec0jn ACor4x6 ACoresk ACorg10.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AWra9g1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AWra9g1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ACoreF4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ACoreF5.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInioec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInit0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInitL OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASma77w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASma77w.AFreeSF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ASec0jn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACor4x6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACorg10 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWra9g1.AWrapTop OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWra9g1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoreF4.ACoreF3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoreF5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Bothny9 AsanInit Starr0h Stargqr Bothr3g Bootk6w Bothjqf Bothg0u Both56i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starr0h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Stargqr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothr3g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootk6w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothjqf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothg0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Both56i.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Am90 DA_Mwrv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16 A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Import AX2. Import APC. Import AP. Import APS.
Local Open Scope Z_scope.

Definition BOTHI : Image :=
  mkImage OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.M.loaded_segments
          OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.M.init_pc
          OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.M.phdrs.

Section AssemblyB.
  (* [comment removed for export] *)
  Variable AI0 : forall Clg : Ceiling, @AllocSpec Clg LayoutP0.
  Variable DK0 : forall Clg : Ceiling, @DriverKit Clg LayoutP0 InitP0 (AI0 Clg).
  Hypothesis LIB0 : forall Clg : Ceiling, @lib_call_ok Clg LL0 (AI0 Clg).
  (* [comment removed for export] *)
  Hypothesis POP : forall Clg : Ceiling, @pop_core_stmt Clg.
  (* [comment removed for export] *)
  Let A8 : forall Clg : Ceiling, @a8_core_cps1_stmt Clg := fun Clg => @a8_core_cps1_ok Clg.
  (* [comment removed for export] *)
  Hypothesis RESTF2 : forall Clg : Ceiling, @OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoreF4.ACoreF3.restF2_stmt Clg.
  Hypothesis RESTF0 : forall Clg : Ceiling, @OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoreF4.ACoreF3.restF0_stmt Clg.
  Let DCORE (Clg : Ceiling) : @dealloc_core_cps Clg := @ACoreF5.dealloc_core_of_F2F0 Clg (RESTF2 Clg) (RESTF0 Clg).
  (* [comment removed for export] *)
  Let Hmalloc (Clg : Ceiling) : @pa_malloc_obligation Clg DepotRepL := pa_malloc_top (POP Clg) (A8 Clg).
  Let Hfree (Clg : Ceiling) : @pa_free_obligation Clg DepotRepL := pa_free_top (DCORE Clg).
  Let Hcalloc (Clg : Ceiling) : @pa_calloc_obligation Clg DepotRepL := pa_calloc_top (POP Clg) (A8 Clg).
  Let Hrealloc (Clg : Ceiling) : @pa_realloc_obligation Clg DepotRepL := pa_realloc_top (POP Clg) (A8 Clg) (DCORE Clg).
  Let Hsmalloc (Clg : Ceiling) : @pa_smalloc_obligation Clg DepotRepL := pa_smalloc_full.
  Let Hsfree (Clg : Ceiling) : @pa_sfree_obligation Clg DepotRepL := pa_sfree_full.
  Let DINIT (Clg : Ceiling) : depot_init_ok2 (DR:=DepotRepL) := depot_init_okL.
  Let AINIT (Clg : Ceiling) : ainit_top_stmt (DR:=DepotRepL) := ainit_of_raw_top.
  Let AIp (Clg : Ceiling) : AsanAlloc LPA := pasan_AsanAlloc (Hmalloc Clg) (Hfree Clg) (Hcalloc Clg) (Hrealloc Clg) (Hsmalloc Clg) (Hsfree Clg).
  (* [comment removed for export] *)
  Let AI16 (Clg : Ceiling) : AsanAlloc16 (AI:=AIp Clg) :=
    pasan_AsanAlloc16_top (POP Clg) (A8 Clg) (DCORE Clg) (Hmalloc Clg) (Hfree Clg) (Hcalloc Clg) (Hrealloc Clg) (Hsmalloc Clg) (Hsfree Clg).
  (* [comment removed for export] *)
  Hypothesis LIBG : forall (Clg : Ceiling) (AI : AsanAlloc LPA), AsanAlloc16 (AI:=AI) -> alib_call_ok (AI:=AI).
  Let LIB (Clg : Ceiling) : alib_call_ok (AI:=AIp Clg) := LIBG Clg (AIp Clg) (AI16 Clg).

  Theorem both_base : strong_universal_error_free_T_scfg ACFG SRC0 BOTHI.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    pose proof Hvalid as Hvalid0.
    (* [comment removed for export] *)
    destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & [Huid Hgid] & Hnofile & Hsigmask & Hhwcap & Habort & Hva).
    pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.D_Mak2g.ref_realizes_spec_lib_run (BW:=bw_pinned) AI0 DK0 img_ok0 img_ok0_intro LIB0
                  rsp rbrk rmb rrnd inp Hrsp Hrbrk Hargv Henvp Hrfit Habort) as SRC.
    assert (NIL : spec (in_argv inp) (in_fs inp) []) by (eapply realizes_nonempty; [exact SRC | apply never_excused_pinned]).
    (* [comment removed for export] *)
    set (argv := in_argv inp) in *. set (envp := in_envp inp) in *. set (fs := in_fs inp) in *. set (stdin := in_stdin inp) in *.
    set (uid := in_uid inp) in *. set (gid := in_gid inp) in *. set (groups := in_groups inp) in *. set (net := in_net inp) in *.
    set (nofile := in_nofile inp) in *. set (sigmask := in_sigmask inp) in *. set (hw := in_hwcap inp) in *.
    set (urandom := in_urandom inp) in *.
    unfold strong_equiv_error_free_scfg.
    apply (spin_shape_strong_equiv_ef _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec argv fs)).
    - exact SRC.
    - pose (Clg := ceiling_of_sp (BW:=bw_pinned) asp Hasp).
      assert (HCEIL : @alloc_ceiling Clg = bv_unsigned asp - 0x800000).
      { unfold alloc_ceiling, Clg, ceiling_of_sp. rewrite stack_max_size_val. reflexivity. }
      (* [comment removed for export] *)
      assert (HLIM_T : AInv.TLIM_MIN <= @AsanInit.blim AsanInit.BL_T).
      { cbn [AsanInit.blim AsanInit.BL_T]. rewrite AInv.TLIM_MIN_eq. unfold AsanInit.LIMIT, target_alloc_limit. lia. }
      pose proof (@asan_main_hole_1 Clg DepotRepL asp HCEIL arnd abrk argv envp uid hw fs Hasp Hargv Henvp Hafit AsanInit.BL_T HLIM_T
                    (Hmalloc Clg) (Hfree Clg) (Hcalloc Clg) (Hrealloc Clg) (Hsmalloc Clg) (Hsfree Clg) (DINIT Clg) (AINIT Clg)
                    (AI16 Clg) (LIB Clg)) as H1.
      pose proof (@asan_main_hole_2 Clg DepotRepL asp HCEIL arnd abrk argv envp uid hw fs Hasp Hargv Henvp Hafit AsanInit.BL_T HLIM_T
                    (Hmalloc Clg) (Hfree Clg) (Hcalloc Clg) (Hrealloc Clg) (Hsmalloc Clg) (Hsfree Clg) (DINIT Clg) (AINIT Clg)
                    (AI16 Clg) (LIB Clg)) as H2.
      pose proof (@asan_main_hole_3 Clg DepotRepL asp HCEIL arnd abrk argv envp uid hw fs Hasp Hargv Henvp Hafit AsanInit.BL_T HLIM_T
                    (Hmalloc Clg) (Hfree Clg) (Hcalloc Clg) (Hrealloc Clg) (Hsmalloc Clg) (Hsfree Clg) (DINIT Clg) (AINIT Clg)
                    (AI16 Clg) (LIB Clg)) as H3.
      pose proof (@asan_main_hole_4 Clg DepotRepL asp HCEIL arnd abrk argv envp uid hw fs Hasp Hargv Henvp Hafit AsanInit.BL_T HLIM_T
                    (Hmalloc Clg) (Hfree Clg) (Hcalloc Clg) (Hrealloc Clg) (Hsmalloc Clg) (Hsfree Clg) (DINIT Clg) (AINIT Clg)
                    (AI16 Clg) (LIB Clg)) as H4.
      (* [comment removed for export] *)
      rewrite <- (AsanInit.init_config_inp_of _ _ _ _ _ _ _ _ inp Habort).
      exact (both_startup_main_A_entry (BL:=AsanInit.BL_T) asp arnd abrk amb argv envp fs stdin uid gid nofile sigmask hw groups net urandom
               Hasp Hargv Henvp Hafit Huid Hhwcap (spec argv fs) NIL Habrk startup_cert_both startup_cert_both2 startup_cert_both2b
               (fun E R FULL model HC => H1 E R FULL model NIL HC)
               (fun E R FULL model HC => H2 E R FULL model NIL HC)
               (fun E R FULL model HC => H3 E R FULL model NIL HC)
               (fun E R FULL model HC => H4 E R FULL model NIL HC)).
  Qed.

  (* [comment removed for export] *)
  Theorem both_base_budgets :
    strong_universal_error_free_T_scfg_budgets ACFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target SRC0 BOTHI.
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid Hprem.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
    pose proof Hvalid as Hvalid0.
    (* [comment removed for export] *)
    destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & [Huid Hgid] & Hnofile & Hsigmask & Hhwcap & Habort & Hva).
    pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.E_As0ui.D_Mak2g.ref_realizes_spec_lib_run (BW:=bw_premise SanitizerBudgets.lim_source) AI0 DK0 img_ok0 img_ok0_intro LIB0
                  rsp rbrk rmb rrnd inp Hrsp Hrbrk Hargv Henvp Hrfit Habort) as SRC.
    assert (NIL : spec (in_argv inp) (in_fs inp) []) by (eapply realizes_nonempty; [exact SRC | apply never_excused_of_premise; exact Hprem]).
    (* [comment removed for export] *)
    set (argv := in_argv inp) in *. set (envp := in_envp inp) in *. set (fs := in_fs inp) in *. set (stdin := in_stdin inp) in *.
    set (uid := in_uid inp) in *. set (gid := in_gid inp) in *. set (groups := in_groups inp) in *. set (net := in_net inp) in *.
    set (nofile := in_nofile inp) in *. set (sigmask := in_sigmask inp) in *. set (hw := in_hwcap inp) in *.
    set (urandom := in_urandom inp) in *.
    unfold strong_equiv_error_free_budgets_scfg.
    apply (spin_shape_strong_equiv_ef_budgets _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec argv fs)); [| | exact Hprem].
    - exact SRC.
    - pose (Clg := ceiling_of_sp (BW:=bw_pinned) asp Hasp).
      assert (HCEIL : @alloc_ceiling Clg = bv_unsigned asp - 0x800000).
      { unfold alloc_ceiling, Clg, ceiling_of_sp. rewrite stack_max_size_val. reflexivity. }
      (* [comment removed for export] *)
      assert (HLIM_T : AInv.TLIM_MIN <= @AsanInit.blim AsanInit.BL_T).
      { cbn [AsanInit.blim AsanInit.BL_T]. rewrite AInv.TLIM_MIN_eq. unfold AsanInit.LIMIT, target_alloc_limit. lia. }
      pose proof (@asan_main_hole_1 Clg DepotRepL asp HCEIL arnd abrk argv envp uid hw fs Hasp Hargv Henvp Hafit AsanInit.BL_T HLIM_T
                    (Hmalloc Clg) (Hfree Clg) (Hcalloc Clg) (Hrealloc Clg) (Hsmalloc Clg) (Hsfree Clg) (DINIT Clg) (AINIT Clg)
                    (AI16 Clg) (LIB Clg)) as H1.
      pose proof (@asan_main_hole_2 Clg DepotRepL asp HCEIL arnd abrk argv envp uid hw fs Hasp Hargv Henvp Hafit AsanInit.BL_T HLIM_T
                    (Hmalloc Clg) (Hfree Clg) (Hcalloc Clg) (Hrealloc Clg) (Hsmalloc Clg) (Hsfree Clg) (DINIT Clg) (AINIT Clg)
                    (AI16 Clg) (LIB Clg)) as H2.
      pose proof (@asan_main_hole_3 Clg DepotRepL asp HCEIL arnd abrk argv envp uid hw fs Hasp Hargv Henvp Hafit AsanInit.BL_T HLIM_T
                    (Hmalloc Clg) (Hfree Clg) (Hcalloc Clg) (Hrealloc Clg) (Hsmalloc Clg) (Hsfree Clg) (DINIT Clg) (AINIT Clg)
                    (AI16 Clg) (LIB Clg)) as H3.
      pose proof (@asan_main_hole_4 Clg DepotRepL asp HCEIL arnd abrk argv envp uid hw fs Hasp Hargv Henvp Hafit AsanInit.BL_T HLIM_T
                    (Hmalloc Clg) (Hfree Clg) (Hcalloc Clg) (Hrealloc Clg) (Hsmalloc Clg) (Hsfree Clg) (DINIT Clg) (AINIT Clg)
                    (AI16 Clg) (LIB Clg)) as H4.
      (* [comment removed for export] *)
      rewrite <- (AsanInit.init_config_inp_of _ _ _ _ _ _ _ _ inp Habort).
      exact (both_startup_main_A_entry (BL:=AsanInit.BL_T) asp arnd abrk amb argv envp fs stdin uid gid nofile sigmask hw groups net urandom
               Hasp Hargv Henvp Hafit Huid Hhwcap (spec argv fs) NIL Habrk startup_cert_both startup_cert_both2 startup_cert_both2b
               (fun E R FULL model HC => H1 E R FULL model NIL HC)
               (fun E R FULL model HC => H2 E R FULL model NIL HC)
               (fun E R FULL model HC => H3 E R FULL model NIL HC)
               (fun E R FULL model HC => H4 E R FULL model NIL HC)).
  Qed.
End AssemblyB.
