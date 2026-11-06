(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs
  Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Lept_gmax_defs Gm_iface Gm_border_defs LeptB_guard LeptB_guard2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac std_at_call RT AF PFS NFA LOR FR64 :=
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; let P := fresh "P" in pose proof (PFS _ Hx) as P; let N1 := fresh "N" in let N2 := fresh "N" in
                                destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in N1, N2 |- *; clear - P N1 N2 LOR FR64;
                                repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
Ltac rop_pre RT AF PFS NFA LOR FR64 := std_at_call RT AF PFS NFA LOR FR64.

(* [comment removed for export] *)
Ltac regen_pxc PXC POBJ AGF PIN D8 :=
  try clear PXC;
  lazymatch type of AGF with agree_on _ ?m0 ?mc =>
    lazymatch type of PIN with In (?pixs, _) _ =>
      lazymatch type of POBJ with hid (pix_obj _ _ _ ?vs _) =>
        assert (PXC : rw_cells asegs mc pixs (pix_cells vs))
          by (unfold hid in POBJ; apply (rw_cells_agree_nw asegs m0 mc pixs _ (proj1 POBJ)); eapply agree_sub; [exact AGF|]; cbv beta;
              let xx := fresh "xx" in let Hxx := fresh "Hxx" in
              intros xx Hxx; right; right; left; exists pixs, 64; split; [exact PIN| cbn in Hxx; lia]);
        unfold pix_cells in PXC; rewrite D8 in PXC
      end end end.

(* [comment removed for export] *)
Ltac mk_pobjd N RT S1 xpixd xvd xv3 POBJD1 VDC PDC :=
  lazymatch goal with |- cps _ (ASTA RT ?Sc _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mc))) _ =>
    assert (N : pix_obj (rt_live RT Sc) mc xpixd xv3 (mkCmapv 0 0 0 0))
      by (apply (pix_obj_nocmap_fields (rt_live RT S1) (rt_live RT Sc) _ mc xpixd xvd xv3 _ _ POBJD1 VDC
                   ltac:(let e := fresh "e" in let He := fresh "He" in intros e He;
                         repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H end; exact He));
          try reflexivity; unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; exact PDC)
  end.

(* [comment removed for export] *)
Ltac rop_uni ROPU xlo xpixd xv3 xdx xdy xdw xdh xop POBJDc HOP EDd VDD EWd EHd NW :=
  eapply cps_seq;
  [ eapply ROPU with (lo := xlo) (pixd := xpixd) (vd := xv3) (cvd := mkCmapv 0 0 0 0) (dx := xdx) (dy := xdy) (dw := xdw) (dh := xdh) (op := xop); rt_side idtac;
      lazymatch goal with
      | |- pix_obj _ _ xpixd _ _ => exact POBJDc
      | |- _ \/ _ => exact HOP
      | |- p_d _ = 8 => exact EDd
      | |- p_data _ <> 0 => exact VDD
      | |- rect_in _ _ _ _ _ _ => unfold rect_in; cbn [p_w p_h]; rewrite EWd, EHd; clear - NW; unfold hid in NW; lia
      | |- lenv _ _ _ _ _ _ => lenv_tac
      | |- lres _ _ _ _ _ => lres_tac
      end
  | ].

(* [comment removed for export] *)
Ltac rop_post RT AF GP S0 usp NCD :=
  lazymatch goal with
  | SUB : (forall e, In e (rt_live RT S0) -> In e (rt_live RT ?Sold)), H : rt_live RT ?Snew = rt_live RT ?Sold |- cps _ (ASTA RT ?Snew _ _) _ =>
      let N := fresh "SUBLn" in
      assert (N : forall e, In e (rt_live RT S0) -> In e (rt_live RT Snew))
        by (let e := fresh "e" in let He := fresh "He" in intros e He; rewrite H; exact (SUB e He));
      clear SUB;
      fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [exact N| solve [frames_sub_tac]| lia]
                                     | cbn [outside]; pose proof (NCD _ Hx); split; [lia| exact I]])
  end;
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *; park_disj.

(* [comment removed for export] *)
Ltac epilogue_prep RT :=
  clear_acc;
  repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end;
  repeat match goal with H : _ <= rt_credit RT _ |- _ => hide H end;
  repeat match goal with H : rt_credit RT _ = _ |- _ => hide H end.
(* [comment removed for export] *)
Ltac credit_fin RT :=
  unfold hid in *;
  repeat match goal with H : rt_credit RT _ = _ |- _ => revert H end;
  repeat match goal with H : _ <= rt_credit RT _ |- _ => revert H end;
  clear; intros; lia.
