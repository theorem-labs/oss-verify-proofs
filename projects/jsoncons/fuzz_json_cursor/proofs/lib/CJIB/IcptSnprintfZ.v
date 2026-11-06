(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm9RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import SFModel Arr StoreFast.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim Monad SoftFloat FmtFp Stdio.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import SFW1_lemmas.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F9 Require Import F_memset F_memcpy F_fwritex F_pad F_fmt_fp_lib F_fmt_fp F_pop_arg Exit Printf_model Printf_mlib
  F_printf_iface F_printf_core F_printf_snsink F_sn_write F_vfprintf F_vsnprintf F_fmt_fp_nf.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJMB Require Import ShZero QcF IcptCells IcptCellsA RdnCells ShLoads IcptTryinitC FfpTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJIB Require Import IcptPcomS IcptSnprintfS IcptVsnprintfZ IcptHapp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac lit_branch := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
  let c' := eval vm_compute in c in change c with c'; cbv iota end.

Theorem snprintf_icpt_ok : snprintf_icpt_stmt icpt_cells.
Proof.
  unfold snprintf_icpt_stmt. intros until o. cbv zeta.
  intros -> -> -> DST BY NOS AOK MODEL FPF HR HR64 ROOM Hn Hn1 ST LO GLO QHI SSP MI FRM HA0 HA DD1 GD AE0 ZL0 ZR0 XL1 XL2 FQ SDq SKD HDq HX.
  pose proof vsnprintf_icpt_ok as VSI.
  cbn [zb FMT_G map] in BY.
  destruct SSP as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2. change F_memcpy.rsegs with rsegs in SSP1, SSP2.
  unfold SNI_DEPTH, GLOBALS_TOP, STATIC_SPLIT in *.
  pose proof (bv_unsigned_in_range 64 sp) as Rq. unfold bv_modulus in Rq. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Rq.
  pose proof (munch_refl [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (HWx : happ_all [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)]%Z) by (destruct HDq as [HDq1 HDq2]; happ_tac).
  carve_frame 96%nat ST.
  zstep.
  do 16 zstep.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?j1 :: _ :: _ :: _ :: _ :: _ :: CB 8 ?j2 :: _) =>
    set (ja := j1) in FR; set (jb := j2) in FR; clearbody ja jb end.
  call (tryinit_callZ (bv_unsigned sp + -96 - lo)).
  1:{ assumption. } 1:{ lia. } 1:{ replace (bv_unsigned sp + -96 - (bv_unsigned sp + -96 - lo))%Z with lo by lia. exact ST. } 1:{ lia. } 1:{ reflexivity. }
  1:{ lazymatch goal with Hm : munch _ m _ |- _ => exact (aenv_ai _ (aenv_munch_h _ _ _ HWx Hm AE0)) end. }
  change F_memcpy.rsegs with rsegs in *.
  lazymatch goal with H : stk _ ?mm (bv_unsigned sp + -96 - (bv_unsigned sp + -96 - lo))%Z _ |- _ =>
    replace (bv_unsigned sp + -96 - (bv_unsigned sp + -96 - lo))%Z with lo in H by lia end.
  zstep. lit_branch.
  do 5 zstep.

  assert (BV : forall mm, rw_cells rsegs mm (bv_unsigned sp + -96)
      [CB 8 ja; C8 (Z_to_bv 64 (bv_unsigned sp + -40)); C8 s2; C8 s1; C8 s0; C8 ra; CB 8 jb; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
      va_area mm (bv_unsigned sp + -40) [a3; a4; a5; a6; a7]).
  { intros mm H. apply (proj1 (rw_cells_app rsegs _ _ [_;_;_;_;_;_;_] _)) in H. destruct H as [_ H]. cbn [cells_size csize Nat.add app] in H.
    destruct H as [[_ B] _]. unfold va_area. replace (bv_unsigned sp + -40) with (bv_unsigned sp + -96 + Z.of_nat 56) by lia. exact B. }
  eapply evt_cut.
  { eapply VSI with (D := D) (n := n) (A := A) (VA := bv_unsigned sp + -40) (dn := dn) (junkd := junkd) (fmt := FMT_G)
                    (slots := [a3; a4; a5; a6; a7]) (args := args) (lo := lo) (canary := canary) (r := r) (o := o);
      rewrite ?unsigned_lit by lia; unfold VSNI_DEPTH, GLOBALS_TOP, STATIC_SPLIT.
    all: try reflexivity.
    all: lazymatch goal with
         | |- rw_cells _ _ _ [CB _ _] => exact DST
         | |- bytes_at _ _ _ (zb _) => cbn [zb FMT_G map]; exact BY
         | |- Forall no_s _ => exact NOS
         | |- Forall _ (fp_calls _ _ _) => exact FPF
         | |- Forall _ FMT_G => unfold FMT_G; repeat (constructor; try lia)
         | |- pass1_ok _ = true => vm_compute; reflexivity
         | |- va_area _ _ _ => apply BV; exact FR
         | |- args_ok _ _ _ _ _ _ _ _ _ => eapply args_ok_nos; [exact NOS | exact AOK]
         | |- printf_model _ _ _ _ _ = _ => exact MODEL
         | |- stk _ _ _ _ => exact POST
         | |- ssp_cells _ _ => split; [exact SSP1 | exact SSP2]
         | |- mem_inv _ _ => assumption
         | |- frm0 _ => exact FRM
         | |- IcptCells.aenv ?mm => lazymatch goal with Hm : munch _ _ mm |- _ => exact (aenv_munch_h _ _ _ HWx Hm AE0) end
         | |- ShZero.zsh ?mm FfpTac.RODATA_LO _ => lazymatch goal with Hm : munch _ _ mm |- _ =>
             eapply zsh_transport_h; [exact ZR0 | exact Hm | exact HWx | unfold ShZero.app, RODATA_LO, RODATA_HI; left; lia] end
         | |- ShZero.zsh ?mm _ _ => lazymatch goal with Hm : munch _ _ mm |- _ =>
             eapply zsh_sub; [eapply zsh_transport_h; [exact ZL0 | exact Hm | exact HWx | unfold ShZero.app; right; lia] | lia | lia] end
         | |- fmtq ?mm _ _ => lazymatch goal with Hm : munch _ _ mm |- _ =>
             eapply fmtq_munch_h; [exact FQ | exact Hm | exact HWx | lia | change (zlength FMT_G) with 6; lia] end
         | |- ShZero.shz _ ?mm _ _ => lazymatch goal with Hm : munch _ _ mm |- _ =>
             eapply shz_transport_h; [exact SDq | exact Hm | exact HWx | eapply IcptCellsA.app_sub; [exact (proj2 HDq) | unfold zlength in *; lia]] end
         | |- shk _ ?mm _ _ => lazymatch goal with Hm : munch _ _ mm |- _ =>
             eapply shk_transport_h; [exact SKD | exact Hm | exact HWx | eapply IcptCellsA.app_sub; [exact (proj2 HDq) | unfold zlength in *; lia]] end
         | |- _ /\ ShZero.app _ _ => exact HDq
         | |- icpt_cells ?mm => lazymatch goal with Hm : munch _ _ mm |- _ => exact (icpt_cells_munch_h _ _ _ HWx Hm HX) end
         | _ => idtac
         end.
    all: try (change (zlength FMT_G) with 6; lia).
    all: try (unfold zlength in *; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia). }
  cbv beta. intros ms' P. unfold vsnprintf_post in P. rewrite ?unsigned_lit in P by lia.
  destruct P as (z5 & z6 & z7 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & z28 & z29 & z30 & z31 & Ft & fc' & m4 & -> & MUc & WMc & MI4 & FRM' & FOK & ST4 & SSP4 & DST4).
  lazymatch type of MUc with munch _ ?mm0 _ => transport_after_call rsegs mm0 m4 MUc WMc; clear MUc WMc end.
  replace (ret_pc (Z_to_bv 64 0x6f980)) with (Z_to_bv 64 0x6f980) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  do 6 zstep.
  release_frame FR ST4 (bv_unsigned sp).
  apply evt_done. unfold vsnprintf_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI4|]. split; [exact FRM'|]. split; [exact FOK|].
  split; [exact ST4|]. split; [exact SSP4|]. exact DST4.
Qed.
