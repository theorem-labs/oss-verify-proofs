(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BYajlRep BYajl_iface BY_rz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; lia.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Theorem ayreset_parser_proof : aylex_realloc_stmt -> ayreset_parser_stmt.
Proof. aceil.
  intros LRE. unfold ayreset_parser_stmt. intros P h mh lo. intros until m.
  intros (MHP & MHA8 & LXP & LXA8 & LBP & LBA8) STA HS LR ST BI ND H0 L0 B0 SHH SHL SHB HHI HCE LHI LCE BHI BCE SEPLB SEPHL SEPHB MI STK LOC LO SPH EA PSTK PIMG PH PL PB.
  subst a0.
  destruct HS as ((pew & pad & HC & PW) & R1 & R2 & R3 & R4). unfold hand_cells, hand_head_cells, alloc_cells in HC.
  cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC.
  pose proof (rw_cells_bound _ _ _ _ HC) as HCB. cbn [cells_size csize Nat.add length] in HCB.
  destruct LR as ((LC & LRG) & (BS & BD & FB)). destruct BS as (BC & DZ & RL & RU).
  pose proof (proj1 DZ ND) as D0.
  pose proof (rw_cells_bound _ _ _ _ LC) as LCB. rewrite lexer_cells_size in LCB.
  pose proof (rw_cells_bound _ _ _ _ BC) as BCB. rewrite buf_cells_size in BCB.
  unfold lexer_cells in LC. unfold buf_cells in BC.
  unfold AY_RESET, AY_RESET_STACK, AY_LEX_REALLOC_STACK, AY_BUF_SMALL_STACK, SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF, wz in *.
  pose proof STA as STA0. ay_statics_open STA.
  aceil. unfold oshw_hi, A_SB, amem in HHI, LHI, BHI.
  assert (HSH2 : 17594333495296 <= mh_addr mh) by (revert HHI CEILB; clear; intros H CEILB; cbn in H; lia).
  assert (LSH2 : 17594333495296 <= mh_lexer mh) by (revert LHI CEILB; clear; intros H CEILB; cbn in H; lia).
  assert (BSH2 : 17594333495296 <= mb_addr (mh_lexbuf mh)) by (revert BHI CEILB; clear; intros H CEILB; cbn in H; lia).
  unfold opol, pol, oshw_lo, oshw_hi, A_SB, amem in PSTK, PIMG, PH, PL, PB. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  destruct PH as [PH PHS]. destruct PL as [PL PLS]. destruct PB as [PB PBS].
  pose proof (block_shadow_bound bsegs m _ (mh_addr mh) 104 SHH) as HSB. unfold A_SB in HSB.
  pose proof SHL as SHL0. pose proof SHB as SHB0.
  unfold oshadow, A_SB in SHH. open_shadow SHH.
  assert (H8 : mh_addr mh mod 8 = 0) by lia.
  pose proof (munch_refl [(lo, bv_unsigned sp); (mh_addr mh + 16, mh_addr mh + 24); (mh_lexer mh, mh_lexer mh + 48);
                          (mb_addr (mh_lexbuf mh), mb_addr (mh_lexbuf mh) + 32)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  yhide PL. yhide PLS. yhide PB. yhide PBS.
  carve_frame 32%nat STK.
  stepA. stepA. stepA. stepA.                         (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { kill K0. }     (* [comment removed for export] *)
  zstepA. ugd.                                        (* [comment removed for export] *)
  do 3 stepA.                                         (* [comment removed for export] *)
  yhide PIMG.
  zstepA.                                             (* [comment removed for export] *)
  shadow_fast SHH (mh_addr mh + 16) 8.                (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  yshow PL. yshow PLS. yshow PB. yshow PBS. yshow PIMG.
  lazymatch goal with H : stk bsegs ?mx lo _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST1 end.
  lazymatch goal with H : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI1 end.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (STA1 : ay_statics mx) by (unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz; split; [exact G1| split; [exact G2| split; [exact G3| exact G4]]]);
    assert (SHL1 : oshadow mx (mh_lexer mh) 48) by (destruct SHL0 as (X1 & X2 & X3); split; [exact X1|]; split; [exact X2|]; eapply (u8arr_transport bsegs); [exact X3| exact MU| exact WM| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 48) by lia; unfold A_SB; lia]);
    assert (SHB1 : oshadow mx (mb_addr (mh_lexbuf mh)) 32) by (destruct SHB0 as (X1 & X2 & X3); split; [exact X1|]; split; [exact X2|]; eapply (u8arr_transport bsegs); [exact X3| exact MU| exact WM| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; unfold A_SB; lia])
  end.
  clear G1 G2 G3 G4.
  pose proof (LRE P (mh_lexer mh) (mh_addr mh + 72) lo (h_lexer h) (mh_lexbuf mh)) as LRE'. unfold aylex_realloc_rpost in LRE'.
  call_spA LRE'.
  1: { split; [exact LXP|]. split; [exact LXA8|]. split; [exact LBP| exact LBA8]. }   (* [comment removed for export] *)
  - exact STA1.
  - split; [split; [unfold lexer_cells; exact LC| exact LRG]|]. split; [split; [unfold buf_cells; exact BC| split; [exact DZ|lia]]| split; [unfold buf_data; rewrite ND; exact I| exact FB]].
  - exact ST.
  - exact BI.
  - exact ND.
  - exact L0.
  - exact B0.
  - unfold SIZEOF_LEXER. exact SHL1.
  - unfold SIZEOF_BUF. exact SHB1.
  - revert LSH2; clear; intros H. unfold oshw_hi, A_SB, amem. cbn. lia.
  - unfold SIZEOF_LEXER; aceil. lia.
  - revert BSH2; clear; intros H. unfold oshw_hi, A_SB, amem. cbn. lia.
  - unfold SIZEOF_BUF; aceil. lia.
  - unfold SIZEOF_LEXER, SIZEOF_BUF. lia.
  - exact MI1.
  - exact ST1.
  - aceil. lia.
  - unfold AY_LEX_REALLOC_STACK, AY_BUF_SMALL_STACK. lia.
  - lia.
  - reflexivity.
  - intros a k Ha Hk. apply PSTK; lia.
  - unfold AY_IMG_LO, AY_IMG_HI. intros a k Ha Hk. apply PIMG; lia.
  - unfold SIZEOF_LEXER. split; intros a k Ha Hk; [apply PL| apply PLS]; unfold oshw_lo, oshw_hi, A_SB, amem in *; lia.
  - unfold SIZEOF_BUF. split; intros a k Ha Hk; [apply PB| apply PBS]; unfold oshw_lo, oshw_hi, A_SB, amem in *; lia.
  - (* [comment removed for export] *)
    lazymatch goal with H : stk bsegs ?mx lo _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2 end.
    first [ match goal with H : ?x = wz (mh_lexer mh) |- _ => subst x end | match goal with H : ?x = Z_to_bv 64 (mh_lexer mh) |- _ => subst x end ]. unfold wz in *.
    lazymatch goal with H : alexer_rep _ _ _ _ _ |- _ => destruct H as ((LC2 & LRG2) & ((BC2 & BSR2) & BD2 & FB2)); unfold lexer_cells in LC2; unfold buf_cells in BC2 end.
    lazymatch goal with H : oshadow _ (mh_lexer mh) _ |- _ => rename H into LX end. unfold oshadow, A_SB, SIZEOF_LEXER in LX. open_shadow LX.
    lazymatch goal with H : oshadow _ (mb_addr (mh_lexbuf mh)) _ |- _ => rename H into BX end. unfold oshadow, A_SB, SIZEOF_BUF in BX. open_shadow BX.
    lazymatch goal with H : ay_statics _ |- _ => destruct H as (G1' & G2' & G3' & G4'); unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1', G2', G3', G4' end.
    yhide PL. yhide PLS. yhide PB. yhide PBS. yhide PIMG.
    lazymatch goal with |- evtA ?segs _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (SHR : ov_read_bytes segs mx (Z_to_bv 64 (2147450880 + (mh_addr mh + 16) / 8)) 1 = Some [Z_to_bv 8 0])
        by (apply (block_shadow_read0_u segs mx 2147450880 (mh_addr mh) 104 (mh_addr mh + 16) 8); [lia| lia| rewrite <- SHHeq; exact SHH| lia| lia| lia| lia])
    end.
    zstepA. clear SHR. rewrite ?zxb_small, ?sxb_small by lia.   (* [comment removed for export] *)
    zstepA. if_false.                                             (* [comment removed for export] *)
    zstepA.                                                       (* [comment removed for export] *)
    do 4 stepA. stepA.                                            (* [comment removed for export] *)
    release_frame FR ST2 (bv_unsigned sp).
    unfold ayreset_parser_rpost. finishA.
    + split; [| repeat split; try lia; tauto].
      exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
      cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app]. unfold wz. exact HC.
    + split; [split; [unfold lexer_cells; exact LC2| exact LRG2]|].
      split; [split; [unfold buf_cells; exact BC2| exact BSR2]|]. split; [| exact FB2]. unfold buf_data, lex_reset, buf_cleared. cbn [lx_buf yb_data]. rewrite ND. exact I.
    + unfold oshadow, block_shadow, A_SB, SIZEOF_HANDLE. split; [exact H8|]. split; [lia|]. rewrite <- SHHeq. exact SHH.
    + unfold oshadow, block_shadow, A_SB, SIZEOF_LEXER. split; [exact LXa|]. split; [lia|]. rewrite <- LXeq. exact LX.
    + unfold oshadow, block_shadow, A_SB, SIZEOF_BUF. split; [exact BXa|]. split; [lia|]. rewrite <- BXeq. exact BX.
    + unfold ay_statics, AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz. split; [exact G1'| split; [exact G2'| split; [exact G3'| exact G4']]].
Qed.
End RC__1.
