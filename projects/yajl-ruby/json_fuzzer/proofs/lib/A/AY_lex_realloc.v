(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
Ltac ay_statics_close :=
  unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz; split; [|split; [|split]]; assumption.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Theorem aylex_realloc_proof : aybuf_clear_stmt -> aylex_realloc_stmt.
Proof. aceil.
  intros CLR. unfold aylex_realloc_stmt. intros P L AF lo lx mbl. intros until m.
  intros STA LR HS BI ND L0 B0 LS BS LSH LHI BSHh BHI SEP MI ST LOC LO SPH EA PSTK PIMG PL PB. subst a0.
  destruct LR as ((LC & L1 & L2 & L3 & L4 & L5 & L6) & BR). unfold lexer_cells in LC.
  destruct BR as ((BC & DZ & RL & RU) & BD & FB). pose proof (proj1 DZ ND) as D0. unfold buf_cells in BC.
  unfold AY_LEX_REALLOC, AY_LEX_REALLOC_STACK, AY_BUF_SMALL_STACK, SIZEOF_LEXER, SIZEOF_BUF, wz in *.
  pose proof STA as STA0. ay_statics_open STA.
  aceil. unfold oshw_hi, A_SB, amem in LSH, BSHh.
  assert (LSH2 : 17594333495296 <= L) by (revert LSH CEILB; clear; intros H CEILB; cbn in H; lia).
  assert (BSH2 : 17594333495296 <= mb_addr mbl) by (revert BSHh CEILB; clear; intros H CEILB; cbn in H; lia).
  unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PSTK, PIMG, PL, PB. unfold AY_IMG_LO, AY_IMG_HI in PIMG. destruct PL as [PL PLS]. destruct PB as [PB PBS].
  pose proof (block_shadow_bound asegs m _ L 48 LS) as LSB. unfold A_SB in LSB.
  pose proof BS as BS0. unfold oshadow, A_SB in LS. open_shadow LS.
  assert (L8 : L mod 8 = 0) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp); (L, L + 48); (mb_addr mbl, mb_addr mbl + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  yhide PB. yhide PBS.
  carve_frame 32%nat ST.
  stepA. stepA. stepA. stepA.                         (* [comment removed for export] *)
  do 3 stepA.                                         (* [comment removed for export] *)
  yhide PIMG.
  stepA.                                              (* [comment removed for export] *)
  shadow_fast LS L 4.                                 (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  zstepA. shadow_fast LS (L + 4) 4. zstepA.           (* [comment removed for export] *)
  zstepA. shadow_fast LS (L + 8) 4. zstepA.           (* [comment removed for export] *)
  zstepA. shadow_fast LS (L + 16) 8.                  (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  yshow PB. yshow PBS. yshow PIMG.
  lazymatch goal with H : stk asegs ?mx lo _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST1 end.
  lazymatch goal with H : mem_inv asegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI1 end.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (STA1 : ay_statics mx) by (unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz; split; [exact G1| split; [exact G2| split; [exact G3| exact G4]]]);
    assert (BS1 : oshadow mx (mb_addr mbl) 32) by (destruct BS0 as (X1 & X2 & X3); split; [exact X1|]; split; [exact X2|]; eapply (u8arr_transport asegs); [exact X3| exact MU| exact WM| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; unfold A_SB; lia])
  end.
  clear G1 G2 G3 G4.
  pose proof (CLR P (mb_addr mbl) (mb_data mbl) AF lo (lx_buf lx)) as CLR'. unfold aybuf_clear_rpost in CLR'. rewrite ND in CLR'. cbn [app] in CLR'.
  call_spA CLR'.
  - exact STA1.
  - split; [unfold buf_cells; exact BC| split; [exact DZ| lia]].
  - unfold buf_data. rewrite ND. exact I.
  - exact HS.
  - exact BI.
  - exact B0.
  - unfold SIZEOF_BUF. exact BS1.
  - revert BSH2; clear; intros H. unfold oshw_hi, A_SB, amem. cbn. lia.
  - unfold SIZEOF_BUF; aceil. lia.
  - intros X. exfalso. apply X. reflexivity.
  - exact MI1.
  - exact ST1.
  - aceil. lia.
  - lia.
  - lia.
  - reflexivity.
  - intros a k Ha Hk. apply PSTK; lia.
  - unfold AY_IMG_LO, AY_IMG_HI. intros a k Ha Hk. apply PIMG; lia.
  - unfold SIZEOF_BUF. split; intros a k Ha Hk; [apply PB| apply PBS]; unfold oshw_lo, oshw_hi, A_SB, amem in *; lia.
  - intros X. exfalso. apply X. reflexivity.
  - (* [comment removed for export] *)
    lazymatch goal with H : stk asegs ?mx lo _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2 end.
    lazymatch goal with H : abuf_struct _ _ _ _ _ |- _ => destruct H as (BC2 & _ & _ & _); unfold buf_cells, buf_cleared in BC2; cbn [yb_state yb_len yb_used yb_data buf_state_code] in BC2 | _ => idtac end.
    lazymatch goal with H : abuf_data _ _ _ |- _ => clear H | _ => idtac end.
    lazymatch goal with H : None <> None -> _ |- _ => clear H | _ => idtac end.
    lazymatch goal with H : oshadow _ (mb_addr mbl) _ |- _ => rename H into BX end. unfold oshadow, A_SB, SIZEOF_BUF in BX. open_shadow BX.
    lazymatch goal with H : ay_statics _ |- _ => destruct H as (G1' & G2' & G3' & G4'); unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1', G2', G3', G4' end.

    yhide PB. yhide PBS. yhide PIMG.
    zstepA. shadow_fast LS (L + 24) 4. zstepA.          (* [comment removed for export] *)
    zstepA. shadow_fast LS (L + 28) 4. zstepA.          (* [comment removed for export] *)
    stepA.                                              (* [comment removed for export] *)
    do 4 stepA. stepA.                                  (* [comment removed for export] *)
    release_frame FR ST2 (bv_unsigned sp).
    unfold aylex_realloc_rpost. finishA.
    + reflexivity.
    + split.
      * split; [| cbn; lia]. unfold lexer_cells, lex_reset. cbn [lx_lineOff lx_charOff lx_error lx_bufOff lx_bufInUse lx_allowComments lx_validateUTF8 lex_error_code].
        unfold wz. lazymatch goal with H : rw_cells asegs _ L _ |- _ => exact H end.
      * split; [| split; [unfold buf_data, lex_reset, buf_cleared; cbn [yb_data lx_buf]; rewrite ND; exact I| unfold lex_reset, buf_cleared; cbn; constructor]].
        split; [| split; [cbn; exact DZ| cbn; lia]].
        unfold buf_cells, lex_reset, buf_cleared. cbn [yb_state yb_len yb_used yb_data buf_state_code lx_buf]. unfold wz. exact BC2.
    + unfold oshadow, block_shadow, A_SB, SIZEOF_LEXER. split; [exact L8|]. split; [lia|]. rewrite <- LSeq. exact LS.
    + unfold oshadow, block_shadow, A_SB, SIZEOF_BUF. split; [exact BXa|]. split; [lia|]. rewrite <- BXeq. exact BX.
    + unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz. split; [exact G1'| split; [exact G2'| split; [exact G3'| exact G4']]].
Qed.
End RC__1.
