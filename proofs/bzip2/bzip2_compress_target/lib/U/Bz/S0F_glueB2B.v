(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import EvtBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface AllocCover AllocDcv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import S2B2BStmt U.S0B2BDStmt U.S0TRInv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueTac GlueAlloc. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require GlueCarve BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTables BzTablesB2B. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzContracts BzContracts0 DecCut S0_glueDefs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_glueA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_glueA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_glueE S0_bzd_out S0_bzd_loop1.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueAlloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.GlueCarve OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzModel OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTablesB2B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzContracts0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_glueDefs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_glueA.S0_glueA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_glueA.S0_glueB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_glueE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_bzd_loop1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpArith BzCLemmas1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDOut BzDOK BzDOKp BzDFrame. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKp OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDFrame OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_out.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0F_bzd_vspec S0F_bzd_fr4 S0F_bzd_sr7 S0F_bzd_snr5 S0F_decContract S0F_glue10.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_out OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_vspec.S0F_bzd_fnr2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0F_bzd_vspec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_bzd_loop1 S0_bzd_loop1 S0F_bzd_fr4 S0F_bzd_loop5.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import S0F_glueDefs S0F_glueA S0F_glueE S0F_glueTail S0F_glueX.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzImg0TacF.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require NormFast. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require FLiaA.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma b2b_model : forall junkD src dn small,
  let '(rv, d1, s1) := bzDecompress (dst_init junkD 0 small) (dstrm_init src dn) in
  buffToBuffDecompress junkD src dn small =
    (if rv =? BZ_OK then ((if 0 <? s_avail_out s1 then BZ_UNEXPECTED_EOF else BZ_OUTBUFF_FULL), dn, s_output s1, d1)
     else if rv =? BZ_STREAM_END then (BZ_OK, dn - s_avail_out s1, s_output s1, d1)
     else (rv, dn, s_output s1, d1)).
Proof. intros. unfold buffToBuffDecompress. destruct (bzDecompress _ _) as [[rv d1] s1]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma dest_split : forall m dst (outz : list Z) (rest : list byte) dn,
  u8arr s0segs m dst (map (Z_to_bv 8) (rev outz) ++ rest) -> Z.of_nat (length (map (Z_to_bv 8) (rev outz) ++ rest)) = dn ->
  rw_cells s0segs m dst [CB (length (rev outz)) (map (Z_to_bv 8) (rev outz)); CB (Z.to_nat (dn - Z.of_nat (length (rev outz)))) rest].
Proof.
  intros m dst outz rest dn U L.
  rewrite length_app, length_map in L.
  apply (rw_cells_of_u8arr s0segs) in U.
  replace (Z.to_nat (dn - Z.of_nat (length (rev outz)))) with (length rest) by lia.
  eapply rw_cells_same_bytes; [| | | exact U].
  - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity.
  - cbn [cells_size csize]. rewrite length_app, length_map. lia.
  - cbn. rewrite length_map. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ctx_ok_initF : forall S uspb src len dst dn small,
  0 < S -> S + 64144 <= alloc_ceiling -> (S + 64144 <= 0x10000 \/ 0x66000 <= S) -> S mod 16 = 0 ->
  0 < dst -> dst + dn <= alloc_ceiling -> (dst + dn <= 0x10000 \/ 0x66000 <= dst) -> dst mod 16 = 0 ->
  0 < src -> src + len <= alloc_ceiling -> src mod 16 = 0 -> 0 <= len < 2 ^ 27 -> 0 <= dn < 2 ^ 27 ->
  (S + 64144 <= dst \/ dst + dn <= S) -> (S + 64144 <= src \/ src + len <= S) -> (src + len <= dst \/ dst + dn <= src) ->
  alloc_ceiling <= uspb -> uspb + 176 <= 2 ^ 47 -> uspb mod 16 = 0 -> (small = 0 \/ small = 1) ->
  ctx_ok (cx10 S uspb src len dst dn small).
Proof.
  intros. bz_ceil.
  bz_ceil; unfold ctx_ok, ctx_lin, ctx_al, ctx_sep, cx10, cxN, img_apart, disj, IMG_HI_MAX, DSTATE_SIZE, CEILING, STACK_TOP, IHI. cbn.
  repeat match goal with |- _ /\ _ => split end; try lia; try (intros; lia); reflexivity.
Qed.

Section B2B.
  Context (AI : AllocIface s0segs S0_layout) (AC : AllocCover s0segs S0_layout AI).
  Let L := S0_layout.
  Hypothesis DCV : alloc_dcv_law s0segs S0_layout AI AC.
  Hypothesis FREEV : alloc_freev_law s0segs S0_layout AI AC.
  Let DEC10 : dec10F_spec AI AC := S0F_glue10.S0F_dec10F AI AC DCV.   (* [comment removed for export] *)

  Theorem S0F_b2bD : b2bD_spec AI AC S0DI.
  Proof.
    unfold b2bD_spec.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MD s LB pD dst dn dl src len small lo B payload junk errv g1 sv k K.
    intros A0 A1 A2 A3 A4 A5 TP LEN DN SM INV VM AUX HB DST DL DLLO DLHI DLAL DLB PAY PAYL CR SRC0 SRCHI SRCAL SEP1 SEP2 SEP3 ST LOC LO SPAL SP47 ERR MI TABS GOT HK.
    cbn [bd_entry bd_crc bd_rnums S0DI] in *.
    pose proof (u64_range sp) as Usp. unfold B2BD_STACK in LO.
    pose proof LOC as LOC'. bz_ceil.
    destruct (ai_inv_model AI INV) as [Hh Hl].
    assert (BLKS : forall b, In b LB -> block_ok L (blk_addr b) (blk_size b)) by (intros b Hb; exact (ai_inv_blocks AI INV Hb)).
    destruct TABS as [CRC RN]. cbn [bd_crc bd_rnums S0DI] in CRC, RN.
    (* [comment removed for export] *) destruct (Z.eq_dec dst 0) as [D0|D0].
    { subst dst a0 a1 a2 a3 a4 a5.
    eapply (evt_realizes s0segs); [exact Hh | exact Hl | |].
    { eapply glueA0 with (lo := lo); [reflexivity | exact ST | lia | lia | exact MI]. }
    (intros ms1; cps_intros (x0 & x1 & x2 & xa0 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & x3 & x4 & x5 & x6 & m1 & -> & XA0 & MU1 & WM1 & MI1 & ST1)).
    apply HK. unfold b2bD_post.
    exists x0, x1, x2, xa0, xa1, xa2, xa3, xa4, xa5, xa6, xa7, x3, x4, x5, x6, errv, m1, s, BZD_PARAM_ERROR, dn.
    split; [reflexivity|]. split; [exact XA0|].
    split. { eapply (ai_inv_frame AI); [exact INV | exact MU1 | exact WM1 |]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    split. { eapply ac_vm_le; [exact VM| lia]. }
    split. { apply vm_only_refl. }
    split; [exact MI1|]. split; [exact ST1|].
    split. { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | unfold errno_cell, L, S0_layout; cbn; lia]. }
    split. { eapply (ai_aux_frame AI); [exact AUX | exact MU1 | exact WM1 |]. apply Forall_cons; [cbn [fst snd al_static S0_layout]; split; [lia | unfold S0_static; intros; lia] | apply Forall_nil]. }
    split. { intros a Ha CA NO. apply (pres_of_munch _ _ _ MU1 WM1 a Ha). cbn. split; [| exact I]. destruct CA as [C|[C|(b0 & Hb0 & Hr0)]]; [lia| unfold L, S0_layout in C; cbn [al_rw_lo al_img_hi] in C; lia|]. cps_pose (BLKS _ Hb0) as (_ & _ & _ & X4 & _). bz_ceil. lia. }
    split. { eapply rw_cells_transport; [exact DL | exact MU1 | exact WM1 | cbn; lia]. }
    split; [lia|].
    split. { unfold b2bD_tabs. cbn [bd_crc bd_rnums S0DI]. split; [eapply rw_cells_transport; [exact CRC | exact MU1 | exact WM1 | cbn; lia] | eapply rw_cells_transport; [exact RN | exact MU1 | exact WM1 | cbn; lia]]. }
    split. { destruct GOT as [GO1 GO2]. unfold b2bD_got in *. cbn [bd_got bd_stderrp bd_crc bd_rnums S0DI] in *. split; [eapply rw_cells_transport; [exact GO1 | exact MU1 | exact WM1 | cbn; lia] | eapply rw_cells_transport; [exact GO2 | exact MU1 | exact WM1 | cbn; lia]]. }
    left. split; [reflexivity| split; [reflexivity| reflexivity]]. }
    destruct DST as [D00|[IN DSTc]]. { exfalso. exact (D0 D00). }
    cps_pose (BLKS _ IN) as (D1 & D2 & D3 & D4 & D5). cbn [blk_addr blk_size fst snd] in D1, D2, D3, D4, D5.
    bz_ceil. unfold L, S0_layout in D5; cbn [al_img_lo al_img_hi] in D5.
    specialize (SEP1 D0). specialize (SEP3 D0).
    hide CR. hide SEP1. clear SEP2. hide D5.
    subst a0 a1 a2 a3 a4 a5.
    eapply (evt_realizes s0segs); [exact Hh | exact Hl | |].
    { eapply glueAF with (lo := lo) (dst := dst) (dl := dl) (src := src) (len := len) (small := small); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| lia| lia| lia| lia| lia| exact ST| lia| lia| exact MI| zlia]. }
    (intros ms1; cps_intros (x0 & x1 & x2 & xa3 & xa4 & xa5 & xa6 & xa7 & x3 & x4 & x5 & x6 & m2w & m1 & j56 & -> & MU1 & WM1 & MI1 & FR1 & FR0 & ST1)).
    assert (INV1 : ai_inv AI s LB m1 MD).
    { eapply (ai_inv_frame AI); [exact INV | exact MU1 | exact WM1 |]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : ai_aux AI m1 B).
    { eapply (ai_aux_frame AI); [exact AUX | exact MU1 | exact WM1 |]. apply Forall_cons; [cbn [fst snd al_static S0_layout]; split; [lia | unfold S0_static; intros; lia] | apply Forall_nil]. }
    assert (ERR1 : rw_cells s0segs m1 (errno_cell L) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | unfold errno_cell, L, S0_layout; cbn; lia]. }
    eapply DCV with (s := s) (LB := LB) (k := (2 + k)%nat) (n := 64144) (lo := lo) (B := B) (errv := errv); rewrite ?unsigned_lit by lia; [exact INV1 | exact VM | exact AUX1 | lia | exact ST1 | exact LOC | cbn [al_stack L S0_layout]; lia | exact ERR1 | exact MI1 | exact TP | reflexivity | unfold MAX_REQ_D; lia |].
    intros s2' LB2 m2 MD2 r y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 errv2 INV2 VMO2 VMC2 MI2 ST2 ERR2 AUX2 HP2 RES.
    rewrite ?unsigned_lit in ST2 by (clear; lia). rewrite ?unsigned_lit in HP2 by (clear; lia). rewrite ret_pc_lit by (clear; lia || reflexivity).
    destruct (ai_inv_model AI INV2) as [Hh2 Hl2].
    assert (FR1' : rw_cells s0segs m2 (bv_unsigned sp + -128) [CB 56 j56; C8 (Z_to_bv 64 0x13e24); C8 (Z_to_bv 64 0x13e3c); C8 (Z_to_bv 64 0); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply heap_pres_rw_cells; [exact HP2 | exact FR1 | left; cbn; lia]. }
    assert (FR0' : rw_cells s0segs m2 (bv_unsigned sp + -160) [C8 (Z_to_bv 64 len); C8 m2w; C8 (Z_to_bv 64 dl); C8 (Z_to_bv 64 0x15f94)]).
    { eapply heap_pres_rw_cells; [exact HP2 | exact FR0 | left; cbn; lia]. }
    assert (GEOM : alloc_ceiling <= lo /\ lo <= bv_unsigned sp - 16384 /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp + 48 <= 2 ^ 47 /\ bv_unsigned sp <= B) by lia.
    assert (DSTF : In (pD, dst, dn) LB /\ 0 <= len < 2 ^ 27 /\ 0 <= dn < 2 ^ 27) by auto.
    assert (DLF : bv_unsigned sp <= dl /\ dl + 4 <= 2 ^ 64 /\ dl mod 4 = 0 /\ dl + 4 <= B) by auto.
    assert (PRm2 : pres (Pcl dst dn dl LB sp) m m2).
    { eapply pres_trans. - eapply (pres_munch_Pcl lo B dst dn dl len LB pD sp GEOM DSTF DLF BLKS); [exact MU1 | exact WM1 | repeat constructor; cbn; lia]. - eapply (pres_heap_Pcl dst dn dl LB sp); [exact HP2 | lia | auto]. }
    destruct RES as [[-> ->] | (Hr & BO & (pS & -> & NIP) & [junkS DSB])].
    - eapply (evt_realizes s0segs); [exact Hh2 | exact Hl2 | |].
    { eapply glueB0 with (lo := lo); [exact FR1' | exact FR0' | exact ST2 | lia | lia | exact MI2]. }
    (intros ms3; cps_intros (z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & -> & ST3)).
    apply HK. unfold b2bD_post.
    exists z0, z1, z2, (Z_to_bv 64 (-3)), za1, za2, za3, za4, za5, za6, za7, z3, z4, z5, z6, errv2, m2, s2', BZD_MEM_ERROR, dn.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact INV2|]. split; [eapply ac_vm_le; [exact VMC2| lia]|]. split; [exact VMO2|]. split; [exact MI2|]. split; [exact ST3|].
    split; [exact ERR2|]. split; [exact AUX2|].
    split; [apply b2b_pres_of_Pcl; exact PRm2|].
    split. { eapply heap_pres_rw_cells; [exact HP2 | | left; cbn; lia]. eapply rw_cells_transport; [exact DL | exact MU1 | exact WM1 | cbn; lia]. }
    split; [lia|].
    split. { unfold b2bD_tabs; cbn [bd_crc bd_rnums S0DI]. split; (eapply heap_pres_rw_cells; [exact HP2 | | apply (crange_img 0 sp); cbn; lia]); [eapply rw_cells_transport; [exact CRC | exact MU1 | exact WM1 | cbn; lia] | eapply rw_cells_transport; [exact RN | exact MU1 | exact WM1 | cbn; lia]]. }
    split. { destruct GOT as [GO1 GO2]. unfold b2bD_got in *. cbn [bd_got bd_stderrp bd_crc bd_rnums S0DI] in *. split; (eapply heap_pres_rw_cells; [exact HP2 | | apply (crange_img 0 sp); cbn; lia]); [eapply rw_cells_transport; [exact GO1 | exact MU1 | exact WM1 | cbn; lia] | eapply rw_cells_transport; [exact GO2 | exact MU1 | exact WM1 | cbn; lia]]. }
    right; left. split; [reflexivity|]. split; [exact D0|]. split; [reflexivity|].
    exists junk. eapply heap_pres_rw_cells; [exact HP2 | | right; right; exists (pD, dst, dn); split; [exact IN| cbn; lia]]. eapply rw_cells_transport; [exact DSTc | exact MU1 | exact WM1 | cbn; lia].
    - cps_pose BO as (R1 & R2 & R3 & R4 & R5). cbn [al_img_lo al_img_hi L S0_layout] in R5. bz_ceil. clear BO Hr. hide R5.
    assert (SDISJ : forall b0, In b0 LB -> blk_addr b0 + blk_size b0 <= r \/ r + 64144 <= blk_addr b0).
    { intros b0 Hb0. pose proof (ai_inv_disjoint AI (b1 := b0) (b2 := (pS, r, 64144)) INV2 ltac:(right; exact Hb0) ltac:(left; reflexivity)) as X. cbn [blk_addr blk_size fst snd] in X. apply X. intros E. apply NIP. apply in_map_iff. exists b0. split; [rewrite E; reflexivity| exact Hb0]. }
    assert (SDST : r + 64144 <= dst \/ dst + dn <= r) by (pose proof (SDISJ _ IN) as X; cbn [blk_addr blk_size fst snd] in X; destruct X; [right| left]; lia).
    assert (SSRC : r + 64144 <= src \/ src + len <= r).
    { unfold hidden in CR, R5. destruct CR as [C|[(C1 & C2 & _)|(b0 & Hb0 & C1 & C2)]]; [lia| unfold L, S0_layout in C1, C2; cbn [al_rw_lo al_img_hi] in C1, C2; destruct R5; [left|right]; lia|]. destruct (SDISJ _ Hb0); [right|left]; lia. }
    assert (PclS : forall a, 0 <= a < 2 ^ 64 -> Pcl dst dn dl LB sp a -> ~ (r <= a < r + 64144)).
    { unfold hidden in R5. intros a Ha [[C|[C|(b0 & Hb0 & Hr0)]] _]; [lia| unfold L, S0_layout in C; cbn [al_rw_lo al_img_hi] in C; destruct R5; lia|]. destruct (SDISJ _ Hb0); lia. }
    hide SDST. hide SSRC.
    cps_destruct (split_block s0segs m2 r junkS DSB) as (BH & (BA & WA & LA) & BM & (bsB & BB & WB & LBB)).
    eapply (evt_realizes s0segs); [exact Hh2 | exact Hl2 | |].
    { eapply glueB1F with (lo := lo) (dl := dl) (dn := dn) (small := small); [exact FR1' | exact FR0' | exact ST2 | lia | lia | exact MI2 | reflexivity | lia | exact BH | exact BM | lia | lia | zlia | zlia | | lia | lia | lia | lia | lia | lia]. eapply heap_pres_rw_cells; [exact HP2 | | left; cbn; lia]. eapply rw_cells_transport; [exact DL | exact MU1 | exact WM1 | cbn; lia]. }
    (intros ms3; cps_intros (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & xs1 & m3 & q1 & q2 & p20 & p4 & p3 & p12 & q12 & q4 & -> & MU3 & WM3 & MI3 & FR3 & BH3 & BM3 & ST3)).
    unfold glueB1_W in MU3.
    pose proof (carve_head s0segs m3 r _ _ p20 p4 p3 p12 BH3 ltac:(lia)) as CH. cbv zeta in CH.
    cps_destruct CH as (HD3 & Lp1 & Lp2 & Lp3 & Rsol & RrN & RrT & Rnn & Rop & Rsm).
    set (h0 := h_init (bv_unsigned sp + -128) small p20 p4 p3 p12) in *.
    pose proof (carve_mid s0segs m3 (r + 3152) q12 q4 BM3) as CM. cbv zeta in CM. cps_destruct CM as (MID3 & T0 & L160 & L40 & RnI).
    set (d0 := d_init q12 q4) in *.
    assert (BA3 : bytes_at s0segs m3 (r + 68) (firstn (Z.to_nat 3084) (skipn 68 junkS))).
    { eapply bytes_at_transport; [exact BA | exact MU3 | rewrite LA; cbn; lia]. }
    assert (WA3 : wr_at s0segs m3 (r + 68) 3084) by (eapply wr_at_transport; [exact WA | exact WM3]).
    assert (BB3 : bytes_at s0segs m3 (r + 3196) bsB).
    { eapply bytes_at_transport; [exact BB | exact MU3 | rewrite LBB; cbn; lia]. }
    assert (WB3 : wr_at s0segs m3 (r + 3196) 60948) by (eapply wr_at_transport; [exact WB | exact WM3]).
    cps_destruct (carve_rest s0segs m3 r _ _ BA3 WA3 LA BB3 WB3 LBB) as (nbu0 & cf0 & r0 & js & NBU3 & Rnbu & CF3 & Lcf & DR3 & SAV3 & Ljs).
    assert (INV3 : ai_inv AI s2' ((pS, r, 64144) :: LB) m3 MD2).
    { eapply (ai_inv_frame AI); [exact INV2 | exact MU3 | exact WM3 |]. apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [apply (cwo_block _ (pS, r, 64144)); [left; reflexivity| cbn; lia| cbn; lia]|]. apply Forall_cons; [apply (cwo_block _ (pS, r, 64144)); [left; reflexivity| cbn; lia| cbn; lia]| apply Forall_nil]. }
    assert (AUX3 : ai_aux AI m3 B).
    { unfold hidden in R5. destruct R5 as [R5'|R5']; (eapply (ai_aux_frame AI); [exact AUX2 | exact MU3 | exact WM3 |]); repeat (apply Forall_cons; [cbn [fst snd al_static S0_layout]; split; [lia | unfold S0_static; intros; lia] |]); apply Forall_nil. }
    assert (ERR3 : rw_cells s0segs m3 (errno_cell L) [C4 errv2]).
    { unfold hidden in R5. destruct R5; (eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 | unfold errno_cell, L, S0_layout; cbn; lia]). }
    assert (PR3 : pres (Pcl dst dn dl LB sp) m m3).
    { eapply pres_trans; [exact PRm2|]. eapply pres_mono; [| apply pres_of_munch; [exact MU3| exact WM3]]. intros a Ha HP. pose proof (PclS a Ha HP) as NS. destruct HP as [CA _]. cbn. assert (HF : ~ (bv_unsigned sp + -160 <= a < bv_unsigned sp)). { destruct CA as [C|[C|(b0 & Hb0 & Hr0)]]; [lia| unfold L, S0_layout in C; cbn [al_rw_lo al_img_hi] in C; lia|]. cps_pose (BLKS _ Hb0) as (_ & _ & _ & X4 & _). bz_ceil. lia. } split; [exact HF|]. split; [intros X; apply NS; lia|]. split; [intros X; apply NS; lia| exact I]. }
    assert (DST3 : rw_cells s0segs m3 dst [CB (Z.to_nat dn) junk]).
    { unfold hidden in SDST. destruct SDST; (eapply rw_cells_transport; [| exact MU3 | exact WM3 | cbn; lia]); (eapply heap_pres_rw_cells; [exact HP2 | | right; right; exists (pD, dst, dn); split; [exact IN| cbn; lia]]); (eapply rw_cells_transport; [exact DSTc | exact MU1 | exact WM1 | cbn; lia]). }
    assert (PAY3 : bytes_at s0segs m3 src payload).
    { unfold hidden in SSRC. destruct SSRC; (eapply bytes_at_transport; [| exact MU3 | rewrite PAYL; cbn; lia]); (eapply heap_pres_bytes_at; [exact HP2 | | rewrite PAYL]); [ eapply bytes_at_transport; [exact PAY | exact MU1 | rewrite PAYL; cbn; lia] | unfold hidden in CR; destruct CR as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C] | eapply bytes_at_transport; [exact PAY | exact MU1 | rewrite PAYL; cbn; lia] | unfold hidden in CR; destruct CR as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C] ]. }
    assert (CRC3 : rw_cells s0segs m3 0x33178 [CB CRC_BYTES crc_table_bytes]).
    { unfold hidden in R5. rewrite <- bz_crc_table_bytes_eq. destruct R5; (eapply rw_cells_transport; [| exact MU3 | exact WM3 | unfold CRC_BYTES; cbn; lia]); (eapply heap_pres_rw_cells; [exact HP2 | | apply (crange_img 0 sp); unfold CRC_BYTES; cbn; lia]); (eapply rw_cells_transport; [exact CRC | exact MU1 | exact WM1 | unfold CRC_BYTES; cbn; lia]). }
    assert (RN3 : rw_cells s0segs m3 0x335b0 [CB RNUMS_BYTES rnums_table_bytes]).
    { unfold hidden in R5. rewrite <- bz_rnums_table_bytes_eq. destruct R5; (eapply rw_cells_transport; [| exact MU3 | exact WM3 | unfold RNUMS_BYTES; cbn; lia]); (eapply heap_pres_rw_cells; [exact HP2 | | apply (crange_img 0 sp); unfold RNUMS_BYTES; cbn; lia]); (eapply rw_cells_transport; [exact RN | exact MU1 | exact WM1 | unfold RNUMS_BYTES; cbn; lia]). }
    destruct GOT as [GO1 GO2]. unfold b2bD_got in GO1, GO2 |- *. cbn [bd_got bd_stderrp bd_crc bd_rnums S0DI] in GO1, GO2 |- *.
    assert (GO13 : rw_cells s0segs m3 0x320e8 [C8 (Z_to_bv 64 0x32098); C8 g1; C8 (Z_to_bv 64 0x320a0); C8 (Z_to_bv 64 0x33178); C8 (Z_to_bv 64 0x335b0)]).
    { unfold hidden in R5. destruct R5; (eapply rw_cells_transport; [| exact MU3 | exact WM3 | cbn; lia]); (eapply heap_pres_rw_cells; [exact HP2 | | apply (crange_img 0 sp); cbn; lia]); (eapply rw_cells_transport; [exact GO1 | exact MU1 | exact WM1 | cbn; lia]). }
    assert (GO23 : rw_cells s0segs m3 0x32098 [C8 sv]).
    { unfold hidden in R5. destruct R5; (eapply rw_cells_transport; [| exact MU3 | exact WM3 | cbn; lia]); (eapply heap_pres_rw_cells; [exact HP2 | | apply (crange_img 0 sp); cbn; lia]); (eapply rw_cells_transport; [exact GO2 | exact MU1 | exact WM1 | cbn; lia]). }
    pose proof (proj1 (proj1 FR3)) as WF3. cbn in WF3. cps_destruct WF3 as (_ & _ & _ & _ & Lq1 & _ & _ & _ & _ & Lq2 & _).
    set (b0 := BZS src len len (Z_to_bv 64 0) (Z_to_bv 64 0) q1 dst dn dn (Z_to_bv 64 0) (Z_to_bv 64 0) q2 r (Z_to_bv 64 0x13e24) (Z_to_bv 64 0x13e3c) (Z_to_bv 64 0)).
    change (rw_cells s0segs m3 (bv_unsigned sp + -128) ([C8 (Z_to_bv 64 src); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 q1; C8 (Z_to_bv 64 dst); C4 (Z_to_bv 64 dn); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 q2; C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 0x13e24); C8 (Z_to_bv 64 0x13e3c); C8 (Z_to_bv 64 0)] ++ SAVES s4 s3 s2 s1 s0 ra)) in FR3.
    apply rw_cells_split in FR3. destruct FR3 as [STRM3 SAVES3]. cbn [cells_size csize Nat.add] in SAVES3.
    replace (bv_unsigned sp + -128 + Z.of_nat 80) with (bv_unsigned sp + -48) in SAVES3 by lia.
    assert (STRM3' : rw_cells s0segs m3 (bv_unsigned sp + -128) (STRM_CELLS b0)).
    { subst b0. cbn [bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque]. replace (src + (len - len)) with src by lia. replace (dst + (dn - dn)) with dst by lia. exact STRM3. }
    clear STRM3.
    assert (BWF0 : bzs_wf b0) by (subst b0; unfold bzs_wf; cbn; clear -Lq1 Lq2 LEN DN; repeat split; lia).
    set (cx0 := cx10 r (bv_unsigned sp + -128) src len dst dn small).
    assert (CTX0 : ctx_ok cx0).
    { subst cx0. unfold hidden in R5, D5, SDST, SSRC, SEP1, SM. clear - R1 R2 R3 R4 R5 D1 D2 D3 D4 D5 SDST SSRC SEP1 SRC0 SRCHI SRCAL LEN DN SM Usp LOC' LO SP47 SPAL. apply ctx_ok_initF; try lia. all: Z.div_mod_to_equations; lia. }
    set (z0 := BZC cx0 (Z_to_bv 64 0x15fe4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 dl) xs1 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 F fc g1 sv payload lo m3 (repeat (Z_to_bv 8 0) 8) (Z_to_bv 64 (bv_unsigned sp + -128 + -112))).
    assert (BZ0 : bzdctx_ok z0).
    { unfold bzdctx_ok. split; [exact CTX0|]. subst z0 cx0. cbn [z_cx z_sp z_lo z_fj z_payload z_spi cx10 cxN b_sp b_len]. rewrite !unsigned_lit by lia. bz_ceil; unfold CEILING, D14. repeat split; try assumption; try lia. f_equal. lia. }
    destruct (ai_inv_model AI INV3) as [Hh3 Hl3].
    eapply (evt_realizes s0segs); [exact Hh3 | exact Hl3 | |].
    { eapply (S0F_decContract.S0_bzd_entry.S0_bzd_entry z0 BZ0) with (h := h0) (b := b0); subst z0 cx0; cbn [z_cx z_sp z_lo z_g1 z_sv cx10 cxN b_s b_strm]; unfold IMGC; cbn [z_cx z_sp z_lo z_g1 z_sv z_spi cx10 cxN b_s b_strm]. - exact HD3. - subst h0. reflexivity. - subst h0. reflexivity. - exact STRM3'. - subst b0. reflexivity. - split; [exact GO13|]. split; [exact GO23|]. split; [apply rnums_tab_u32arr; exact RN3| apply crc_tab_u32arr; exact CRC3]. - rewrite unsigned_lit by lia. exact ST3. - exact MI3. }
    intros ms4 POST4. unfold bzd_entry_post in POST4. subst z0. cbn [z_cx z_sp z_gp z_tp z_sv z_F z_fc z_lo cx0 cx10 cxN b_s b_strm] in POST4.
    cps_destruct POST4 as (v0 & v1 & v2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & m4 & fj & -> & MU4 & WM4 & MI4 & FRM4 & Lfj & ST4 & HD4 & STRM4 & IMGC4).
    rewrite !unsigned_lit in MU4, FRM4, ST4 |- * by (pose proof alloc_ceiling_range as ACR9; clear - ACR9 Usp LOC' LO SP47; lia).
    assert (SAVES4 : rw_cells s0segs m4 (bv_unsigned sp + -48) (SAVES s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact SAVES3 | exact MU4 | exact WM4 | unfold SAVES, CRC_BYTES, RNUMS_BYTES; cbn; lia]).
    assert (NBU4 : rw_cells s0segs m4 (r + 1092) [C4 (Z_to_bv 64 nbu0)]) by (eapply rw_cells_transport; [exact NBU3 | exact MU4 | exact WM4 | cbn; lia]).
    assert (CF4 : u32arr s0segs m4 (r + 1096) cf0) by (eapply u32arr_transport; [exact CF3 | exact MU4 | exact WM4 | rewrite Lcf; cbn; lia]).
    assert (MID4 : rw_cells s0segs m4 (r + 3152) (MID_CELLS d0)) by (eapply rw_cells_transport; [exact MID3 | exact MU4 | exact WM4 | cbn; lia]).
    assert (DR4 : drest_at s0segs m4 r r0) by (eapply drest_transport; [exact DR3 | exact MU4 | exact WM4 | cbn; lia | cbn; lia | cbn; lia]).
    assert (SAV4 : rw_cells s0segs m4 (r + 64036) [CB 108 js]) by (eapply rw_cells_transport; [exact SAV3 | exact MU4 | exact WM4 | cbn; lia]).
    assert (DL4 : rw_cells s0segs m4 dl [C4 (Z_to_bv 64 dn)]).
    { eapply rw_cells_transport; [| exact MU4 | exact WM4 | cbn; lia]. eapply rw_cells_transport; [| exact MU3 | exact WM3 | cbn; lia]. eapply heap_pres_rw_cells; [exact HP2 | | left; cbn; lia]. eapply rw_cells_transport; [exact DL | exact MU1 | exact WM1 | cbn; lia]. }
    assert (DST4 : rw_cells s0segs m4 dst [CB (Z.to_nat dn) junk]) by (eapply rw_cells_transport; [exact DST3 | exact MU4 | exact WM4 | cbn; lia]).
    assert (PAY4 : bytes_at s0segs m4 src payload) by (eapply bytes_at_transport; [exact PAY3 | exact MU4 | rewrite PAYL; cbn; lia]).
    assert (CRC4 : rw_cells s0segs m4 0x33178 [CB CRC_BYTES crc_table_bytes]) by (eapply rw_cells_transport; [exact CRC3 | exact MU4 | exact WM4 | unfold CRC_BYTES; cbn; lia]).
    assert (RN4 : rw_cells s0segs m4 0x335b0 [CB RNUMS_BYTES rnums_table_bytes]) by (eapply rw_cells_transport; [exact RN3 | exact MU4 | exact WM4 | unfold RNUMS_BYTES; cbn; lia]).
    assert (ERR4 : rw_cells s0segs m4 (errno_cell L) [C4 errv2]) by (eapply rw_cells_transport; [exact ERR3 | exact MU4 | exact WM4 | unfold errno_cell, L, S0_layout; cbn; lia]).
    cps_destruct IMGC4 as (GO14 & GO24 & RNW4 & CRW4).
    assert (INV4 : ai_inv AI s2' ((pS, r, 64144) :: LB) m4 MD2).
    { eapply (ai_inv_frame AI); [exact INV3 | exact MU4 | exact WM4 |]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX4 : ai_aux AI m4 B).
    { eapply (ai_aux_frame AI); [exact AUX3 | exact MU4 | exact WM4 |]. apply Forall_cons; [cbn [fst snd al_static S0_layout]; split; [lia | unfold S0_static; intros; lia] | apply Forall_nil]. }
    assert (PR4 : pres (Pcl dst dn dl LB sp) m m4).
    { eapply pres_trans; [exact PR3|]. eapply (pres_munch_Pcl lo B dst dn dl len LB pD sp GEOM DSTF DLF BLKS); [exact MU4 | exact WM4 |]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    destruct (ai_inv_model AI INV4) as [Hh4 Hlz4].
    eapply DEC10 with (s := s2') (LB := (pS, r, 64144) :: LB) (pS := pS) (pD := pD) (lo := lo) (B := B) (k := k) (h0 := h0) (nbu0 := nbu0) (cf0 := cf0) (d0 := d0) (r0 := r0) (js := js) (b0 := b0) (payload := payload) (errv := errv2) (g1 := g1); [exact CTX0 | exact TP | exact HD4 | | exact NBU4 | exact Rnbu | exact CF4 | exact Lcf | exact MID4 | exact T0 | exact L160 | exact L40 | exact RnI | subst d0; reflexivity | exact DR4 | exact SAV4 | exact STRM4 | exact BWF0 | subst b0; reflexivity | subst b0; reflexivity | subst b0; reflexivity | subst b0; reflexivity | subst b0; reflexivity | subst b0; reflexivity | subst b0; reflexivity | subst b0; reflexivity | subst b0; reflexivity | subst b0; reflexivity | exact PAY4 | exact PAYL | | exact GO14 | exact GO24 | exact RNW4 | exact ST4 | exact LOC | lia | exact MI4 | exact INV4 | exact VMC2 | left; reflexivity | right; exact IN | exact AUX4 | lia | exact ERR4 |].
    { unfold hwf10. repeat match goal with |- _ /\ _ => split end; first [assumption | subst h0; reflexivity | lia]. }
    { unfold hidden in CR. replace (bv_unsigned sp + -128 + 128) with (bv_unsigned sp) by lia. destruct CR as [C|[C|(bq & Hbq & C)]]; [left; exact C | right; left; exact C | right; right; exists bq; split; [right; exact Hbq| exact C]]. }
    intros m5 MD5 s5' c n rc errv5 u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6. cbv zeta.
    intros INV5 VMO5 VMC5 AUX5 ERR5 MI5 ST5 CTX5 SZ5 SH5 N5 GO15 GO25 RNW5 PRES5 OUT5.
    hide SM.
    destruct (ai_inv_model AI INV5) as [Hh5 Hl5].
    set (cx5 := cxN r (bv_unsigned sp + -128) src len dst dn small n (cfg_tt c) (cfg_l16 c) (cfg_l4 c)) in *.
    assert (P10 : forall A cs, rw_cells s0segs m4 A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ((bv_unsigned sp + -128) - 112 <= a \/ (0x32000 <= a < 0x66000 /\ ~ S0_private a /\ ~ (0x4413c <= a < 0x44140)) \/ in_block ((pS, r, 64144) :: LB) a) /\ ~ (r <= a < r + 64144) /\ ~ ((bv_unsigned sp + -128) <= a < (bv_unsigned sp + -128) + 20)) -> rw_cells s0segs m5 A cs).
    { intros A cs H HA. eapply (pres_rw_cells (fun a => ((bv_unsigned sp + -128) - 112 <= a \/ (0x32000 <= a < 0x66000 /\ ~ S0_private a /\ ~ (0x4413c <= a < 0x44140)) \/ in_block ((pS, r, 64144) :: LB) a) /\ ~ (r <= a < r + 64144) /\ ~ ((bv_unsigned sp + -128) <= a < (bv_unsigned sp + -128) + 20))); [| exact H | exact HA]. (intros a Ha; cps_intros (X1 & X2 & X3)). exact (PRES5 a Ha X1 X2 X3). }
    assert (SAVES5 : rw_cells s0segs m5 (bv_unsigned sp + -48) (SAVES s4 s3 s2 s1 s0 ra)).
    { apply P10; [exact SAVES4|]. unfold SAVES; cbn; intros a Ha. repeat split; lia. }
    assert (FRM5 : rw_cells s0segs m5 ((bv_unsigned sp + -128) - 112) (FRMj (BZC cx5 (Z_to_bv 64 0x15fe4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 dl) xs1 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 F fc g1 sv payload lo m5 fj (Z_to_bv 64 ((bv_unsigned sp + -128) + -112))) fj)).
    { unfold FRMj. cbn [z_s11 z_s10 z_s9 z_s8 z_s7 z_s6 z_s5 z_s4 z_s3 z_s2 z_s1 z_s0 z_ra]. apply P10. - unfold FRMj in FRM4. cbn [z_s11 z_s10 z_s9 z_s8 z_s7 z_s6 z_s5 z_s4 z_s3 z_s2 z_s1 z_s0 z_ra] in FRM4. replace ((bv_unsigned sp + -128) - 112) with ((bv_unsigned sp + -128) + -112) by lia. exact FRM4. - cbn [cells_size csize Nat.add length]. intros a Ha. repeat split; lia. }
    assert (DL5 : rw_cells s0segs m5 dl [C4 (Z_to_bv 64 dn)]).
    { apply P10; [exact DL4|]. cbn; intros a Ha. repeat split; lia. }
    assert (DST5 : rw_cells s0segs m5 dst [CB (Z.to_nat dn) junk]).
    { unfold hidden in SDST. apply P10; [exact DST4|]. cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; intros a Ha. split; [right; right; exists (pD, dst, dn); split; [right; exact IN| cbn; lia]|]. destruct SDST; split; lia. }
    assert (CRC5 : rw_cells s0segs m5 0x33178 [CB CRC_BYTES crc_table_bytes]).
    { unfold hidden in R5. apply P10; [exact CRC4|]. unfold CRC_BYTES; cbn; intros a Ha. split; [right; left; unfold S0_private; lia|]. destruct R5; split; lia. }
    assert (RN5 : rw_cells s0segs m5 0x335b0 [CB RNUMS_BYTES rnums_table_bytes]).
    { unfold hidden in R5. apply P10; [exact RN4|]. unfold RNUMS_BYTES; cbn; intros a Ha. split; [right; left; unfold S0_private; lia|]. destruct R5; split; lia. }
    assert (PR5 : pres (Pcl dst dn dl LB sp) m m5).
    { eapply pres_trans; [exact PR4|]. intros a Ha HP. apply PRES5; [exact Ha | | exact (PclS a Ha HP) |]. - destruct HP as [[C|[C|(b1 & Hb1 & Hr1)]] _]; [left; lia | right; left | right; right; exists b1; split; [right; exact Hb1| exact Hr1]]. unfold L, S0_layout, errno_cell, S0_private in C; cbn [al_rw_lo al_img_hi al_private al_tp] in C. unfold S0_private. lia. - destruct HP as [[C|[C|(b1 & Hb1 & Hr1)]] _]; [lia | unfold L, S0_layout in C; cbn [al_rw_lo al_img_hi] in C; lia |]. cps_pose (BLKS _ Hb1) as (_ & _ & _ & X4 & _). bz_ceil. lia. }
    assert (NEWB : forall bb, In bb (cfg_extra c) -> block_ok L (blk_addr bb) (blk_size bb) /\ (forall b1, In b1 LB -> blk_addr bb + blk_size bb <= blk_addr b1 \/ blk_addr b1 + blk_size b1 <= blk_addr bb)).
    { intros bb Hbb. split; [exact (ai_inv_blocks AI INV5 ltac:(apply in_or_app; left; exact Hbb))|]. intros b1 Hb1. apply (ai_inv_disjoint AI INV5); [apply in_or_app; left; exact Hbb | apply in_or_app; right; right; exact Hb1|]. intros E. subst b1. pose proof (ai_inv_nodup AI INV5) as ND. rewrite map_app in ND. eapply (nodup_app_disj _ _ (blk_id bb) ND); [apply in_map; exact Hbb | cbn; right; apply in_map; exact Hb1]. }
    set (z := BZC cx5 (Z_to_bv 64 0x15fe4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp (Z_to_bv 64 dl) xs1 (Z_to_bv 64 len) (Z_to_bv 64 dst) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 F fc g1 sv payload lo m5 fj (Z_to_bv 64 ((bv_unsigned sp + -128) + -112))) in *.
    assert (BZ : bzdctx_ok z).
    { unfold bzdctx_ok. split; [exact CTX5|]. subst z cx5. cbn [z_cx z_sp z_lo z_fj z_payload z_spi cxN b_sp b_len]. rewrite !unsigned_lit by lia. bz_ceil; unfold CEILING, D14. repeat split; try assumption; try lia. f_equal. lia. }
    assert (NN0 : 1 <= b_n cx5 -> b_small cx5 = 0 -> b_tt cx5 <> 0).
    { subst cx5. cbn [b_n b_small b_tt cxN]. intros Hn Hs. destruct c as [|bt|bq4 bq6|bq6|bq4]; cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 cfg_sizes_ok cfg_shape_ok] in SZ5, SH5, NEWB |- *; try lia. pose proof (proj1 (NEWB bt ltac:(left; reflexivity))) as (Y1 & _). lia. }
    assert (NN1 : 1 <= b_n cx5 -> b_small cx5 = 1 -> b_ll16 cx5 <> 0 /\ b_ll4 cx5 <> 0).
    { subst cx5. cbn [b_n b_small b_ll16 b_ll4 cxN]. intros Hn Hs. destruct c as [|bt|bq4 bq6|bq6|bq4]; cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 cfg_sizes_ok cfg_shape_ok] in SZ5, SH5, NEWB |- *; try lia. pose proof (proj1 (NEWB bq4 ltac:(left; reflexivity))) as (Y1 & _). pose proof (proj1 (NEWB bq6 ltac:(right; left; reflexivity))) as (Y2 & _). lia. }
    destruct OUT5 as [(junkD & J' & FUN) | (RC & h5 & d5 & ai5 & til5 & tih5 & HD5 & Hstrm5 & Rst5 & Nst5 & MID5 & Htt5 & Hl165 & Hl45 & STRM5 & Hai5)].
    + (* [comment removed for export] *) remember (decompress (dst_init junkD 0 small) (dstrm_init (map bv_unsigned payload) dn)) as DEC1 eqn:EDEC1 in FUN.
    destruct DEC1 as [[rv1 dq1] sq1]. cps_destruct FUN as (Erc & DM5 & DP5 & PW5). subst rc.
    pose proof (decompress_frame (dst_init junkD 0 small) (dstrm_init (map bv_unsigned payload) dn) ltac:(cbn; unfold BZ_X_OUTPUT, BZ_X_MAGIC_1; lia) ltac:(cbn; unfold BZ_X_MAGIC_1; lia)) as DF.
    rewrite <- EDEC1 in DF. cps_destruct DF as (Fout & Fav & Ftout & Fcc & Fbn & Fbn2 & Fst). clear Fbn Fbn2. cbn [s_out s_avail_out s_tout dstrm_init] in Fout, Fav, Ftout.
    assert (Ecc : d_cccrc dq1 = 0) by (rewrite Fcc; reflexivity).
    assert (DP5' : dpureF cx5 (bs_of cx5 J' sq1) payload J' dq1 sq1).
    { pose proof DP5 as X. unfold dpureF, jk_static in X |- *. subst b0. dvF_cbn_in X. dvF_cbn. subst cx5. cbn [b_len cxN] in X |- *. decompose [and] X. repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia. }
    pose proof (dpureF_cbn _ _ _ _ _ _ DP5') as [Rbn0 _].
    assert (Ljunk : length junk = Z.to_nat dn) by (pose proof (proj1 (proj1 DST5)) as W; cbn in W; destruct W as [W _]; exact W).
    eapply (evt_realizes s0segs); [exact Hh5 | exact Hl5 | |].
    { eapply (bzd_fLK z BZ S0F_decContract.S0F_dec14F_spec FASTR_ok S0F_bzd_snr5.S0F_smallnr_ok S0F_bzd_sr7.S0F_smallr_ok NN0 NN1 (Datatypes.S (length payload)) (Z_to_bv 64 0x1481c) u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 xs1 (Z_to_bv 64 (-2)) s8 u3 u4 u5 u6 m5 rv1 J' dq1 sq1 junk junk).
    - unfold FCH, FIMG, FDEST. subst z. cbn [z_cx z_g1 z_sv z_payload z_spi z_lo z_fj]. unfold FRM. cbn [z_fj z_spi]. rewrite !unsigned_lit by (pose proof alloc_ceiling_range as ACR9; clear - ACR9 Usp LOC' LO SP47; lia). split; [exact DM5|]. split; [apply crc_tab_u32arr; exact CRC5|]. split. { split; [apply (u8arr_of_rw_cells s0segs) in DST5; exact DST5|]. split; [subst cx5; cbn [b_dlen cxN]; rewrite Ljunk, Z2Nat.id by (clear -DN; lia); reflexivity|]. rewrite Fout. split; [reflexivity|]. rewrite Fav. subst cx5; cbn [b_dlen cxN length]. clear -DN. lia. } split; [replace (bv_unsigned sp + -128 + -112) with (bv_unsigned sp + -128 - 112) by (clear; lia); exact FRM5| exact ST5].
    - subst z. cbn [z_m0]. apply munch_refl.
    - subst z. cbn [z_m0]. apply wmono_refl.
    - exact MI5.
    - unfold FFACTS. split; [exact DP5'|]. split; [exact Fst|]. split; [rewrite Ecc; lia|]. split.
    + rewrite Fav. subst z cx5. cbn [z_cx b_dlen cxN]. clear -DN. lia.
    + exact PW5.
    - intros _. subst z cx5. cbn [z_cx b_len cxN]. rewrite Nat2Z.inj_succ, <- PAYL.
    clear -Rbn0. assert (H6 : Z.of_nat (length payload) / 6 <= Z.of_nat (length payload)) by (apply Z.div_le_upper_bound; lia). lia.
    }
    intros ms6 POST6. unfold bzd_fpost in POST6.
    assert (EBZ : bzDecompress (dst_init junkD 0 small) (dstrm_init (map bv_unsigned payload) dn) = K_L (Datatypes.S (length payload)) (rv1, dq1, sq1)).
    { rewrite bzDecompress_eq. cbn [s_in dstrm_init]. rewrite length_map. rewrite bzd_loop_10 by reflexivity. unfold K_call. rewrite <- EDEC1. reflexivity. }
    destruct (K_L (Datatypes.S (length payload)) (rv1, dq1, sq1)) as [[rv2 d2] sq2] eqn:EKL.
    cps_destruct POST6 as (v0' & v1' & v2' & va1' & va2' & va3' & va4' & va5' & va6' & va7' & v3' & v4' & v5' & v6' & m6 & J6 & db6 & rest6 & E6 & MU6 & WM6 & MI6 & ST6 & DM6 & IMG6 & DE6 & DP6 & Rrv2).
    subst ms6. subst z. cbn [z_ra z_sp z_gp z_tp z_s0 z_s1 z_s2 z_s3 z_s4 z_s5 z_s6 z_s7 z_s8 z_s9 z_s10 z_s11 z_F z_fc z_m0 z_lo z_cx z_g1 z_sv z_payload] in *.
    rewrite ret_pc_lit by (clear; lia || reflexivity). rewrite !unsigned_lit in ST6 by (pose proof alloc_ceiling_range as ACR9; clear - ACR9 Usp LOC' LO SP47; lia).
    pose proof DM5 as X5. unfold dmem in X5. cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0] in X5. cps_destruct X5 as (_ & _ & _ & _ & _ & _ & STRM5 & _).
    pose proof DM6 as X6. unfold dmem in X6. cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0] in X6. cps_destruct X6 as (HD6 & NBU6 & CF6 & MID6 & SAV6 & DR6 & STRM6 & BLK6 & PAY6 & GO16 & GO26 & RNA6).
    cps_destruct DE6 as (DB6 & Ldb6 & Edb6 & Lout6). unfold FIMG in IMG6.
    unfold WBZ in MU6. cbn [z_cx z_lo z_sp cxN b_s b_strm b_dst b_dlen] in MU6. unfold DSTATE_SIZE in MU6. rewrite !unsigned_lit in MU6 by (pose proof alloc_ceiling_range as ACR9; clear - ACR9 Usp LOC' LO SP47; lia).
    set (RW := map (fun bb : ablock => (blk_addr bb, blk_addr bb + blk_size bb)) (cfg_extra c)).
    assert (SUB : sub_fp ([(r, r + 64144); (bv_unsigned sp + -128, bv_unsigned sp + -128 + 44); (dst, dst + dn); (lo, bv_unsigned sp + -128)] ++ blk_ivls cx5) ([(r, r + 64144); (bv_unsigned sp + -128, bv_unsigned sp + -128 + 44); (dst, dst + dn); (lo, bv_unsigned sp + -128)] ++ RW)).
    { intros x Hx; apply outside_app in Hx as [HXA HXB]; apply outside_app; split; [exact HXA|]. subst RW cx5; unfold blk_ivls; cbn [b_small b_tt b_ll16 b_ll4 b_n cxN]. destruct c as [|bt|bq4 bq6|bq6|bq4]; cbn [cfg_extra cfg_tt cfg_l16 cfg_l4 cfg_sizes_ok cfg_shape_ok map] in SZ5, SH5, HXB |- *.
    - rewrite SH5. unfold hidden in SM. destruct SM as [-> | ->]; cbn; lia.
    - rewrite SH5. cbn. cbn in HXB. rewrite SZ5 in HXB. exact HXB.
    - rewrite SH5. cbn. cbn in HXB. destruct SZ5 as [Z4 Z6]. rewrite Z4, Z6 in HXB. cps_destruct HXB as (X4 & X6 & _). split; [exact X6| split; [exact X4| exact I]].
    - destruct SH5 as [-> ->]. cbn. lia.
    - destruct SH5 as [-> ->]. cbn. lia. }
    pose proof (munch_weaken _ _ _ _ SUB MU6) as MU6'. clear SUB MU6.
    assert (RWlo : Forall (fun iv => exists bb, In bb (cfg_extra c) /\ fst iv = blk_addr bb /\ snd iv = blk_addr bb + blk_size bb) RW).
    { subst RW. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (bb & <- & Hbb). exists bb. cbn. auto. }
    assert (INV6 : ai_inv AI s5' (cfg_extra c ++ (pS, r, 64144) :: LB) m6 MD5).
    { eapply (ai_inv_frame AI); [exact INV5 | exact MU6' | exact WM6 |]. apply Forall_app. split.
    - apply Forall_cons; [apply (cwo_block _ (pS, r, 64144)); [apply in_or_app; right; left; reflexivity| cbn; clear; lia| cbn; clear; lia]|]. apply Forall_cons; [left; cbn; clear -GEOM; lia|]. apply Forall_cons; [apply (cwo_block _ (pD, dst, dn)); [apply in_or_app; right; right; exact IN| cbn; clear; lia| cbn; clear; lia]|]. apply Forall_cons; [left; cbn; clear -GEOM; lia| apply Forall_nil].
    - apply Forall_forall. intros [l' h'] Hiv. apply (proj1 (Forall_forall _ _) RWlo) in Hiv as (bb & Hbb & E1 & E2). cbn in E1, E2. subst l' h'. apply (cwo_block _ bb); [apply in_or_app; left; exact Hbb| clear; lia| clear; lia]. }
    assert (AUX6 : ai_aux AI m6 B).
    { unfold hidden in R5, D5.
      assert (CWA : forall iv : Z * Z, (snd iv <= alloc_ceiling \/ snd iv <= bv_unsigned sp) -> (snd iv <= 65536 \/ 0x66000 <= fst iv) -> snd iv <= B /\ (forall a, fst iv <= a < snd iv -> ~ al_static L a)).
      { pose proof alloc_ceiling_range as ACR. clear -GEOM HB ACR. intros [l' h'] X Y. cbn [fst snd] in X, Y |- *. unfold L, S0_layout; cbn [al_static]. unfold S0_static. split; [destruct X; lia|]. intros a Ha. destruct Y; lia. }
      eapply (ai_aux_frame AI); [exact AUX5 | exact MU6' | exact WM6 |]. apply Forall_app. split.
      - repeat (apply Forall_cons; [apply CWA; cbn [fst snd]; [pose proof alloc_ceiling_range as ACR; clear -R4 R5 D4 D5 GEOM ACR LOC' LO HB; lia | pose proof alloc_ceiling_range as ACR; clear -R4 R5 D4 D5 GEOM ACR LOC' LO HB; lia] |]). apply Forall_nil.
      - apply Forall_forall. intros [l' h'] Hiv. apply (proj1 (Forall_forall _ _) RWlo) in Hiv as (bb & Hbb & E1 & E2). cbn in E1, E2. subst l' h'. cps_destruct (proj1 (NEWB bb Hbb)) as (Y1 & Y2 & Y3 & Y4 & Y5). unfold L, S0_layout in Y5; cbn [al_img_lo al_img_hi] in Y5. apply CWA; cbn [fst snd]; [clear -Y4; lia | clear -Y5; lia]. }
    assert (OUTW : forall a, 0 <= a < 2 ^ 64 -> ~ (r <= a < r + 64144) -> ~ (bv_unsigned sp + -128 <= a < bv_unsigned sp + -128 + 44) -> ~ (dst <= a < dst + dn) -> ~ (lo <= a < bv_unsigned sp + -128) -> (forall bb, In bb (cfg_extra c) -> ~ (blk_addr bb <= a < blk_addr bb + blk_size bb)) -> outside ([(r, r + 64144); (bv_unsigned sp + -128, bv_unsigned sp + -128 + 44); (dst, dst + dn); (lo, bv_unsigned sp + -128)] ++ RW) a).
    { intros a Ha N1 N2 N3 N4 NB. apply outside_app. split; [cbn; split; [exact N1| split; [exact N2| split; [exact N3| split; [exact N4| exact I]]]]|]. apply outside_Forall. apply Forall_forall. intros [l' h'] Hiv. apply (proj1 (Forall_forall _ _) RWlo) in Hiv as (bb & Hbb & E1 & E2). cbn in E1, E2 |- *. subst l' h'. exact (NB bb Hbb). }
    assert (ERR6 : rw_cells s0segs m6 (errno_cell L) [C4 errv5]).
    { eapply (pres_rw_cells _ _ _ _ _ (pres_of_munch _ _ _ MU6' WM6)); [exact ERR5|]. unfold errno_cell, L, S0_layout; cbn. intros a Ha. apply OUTW.
    - clear -Ha. lia.
    - unfold hidden in R5. clear -Ha R5. destruct R5; lia.
    - clear -Ha GEOM. bz_ceil. lia.
    - unfold hidden in D5. clear -Ha D5. destruct D5; lia.
    - clear -Ha GEOM. bz_ceil. lia.
    - intros bb Hbb. cps_destruct (proj1 (NEWB bb Hbb)) as (_ & _ & _ & Y4 & Y5). unfold L, S0_layout in Y5; cbn [al_img_lo al_img_hi] in Y5. clear -Ha Y4 Y5. bz_ceil. destruct Y5; lia. }
    assert (PR6 : pres (Pcl dst dn dl LB sp) m m6).
    { eapply pres_trans; [exact PR5|]. eapply pres_mono; [| apply pres_of_munch; [exact MU6'| exact WM6]]. intros a Ha HP. pose proof (PclS a Ha HP) as NS. destruct HP as [CA NO]. unfold b2bD_out in NO.
      unfold client_addr, in_block, L, S0_layout in CA. cbn [al_rw_lo al_img_hi al_private errno_cell] in CA.
      apply OUTW.
      - exact Ha.
      - exact NS.
      - pose proof alloc_ceiling_range as ACR. clear -CA GEOM BLKS ACR. destruct CA as [C|[C|(b1 & Hb1 & Hr1)]]; [lia| lia|]. cps_pose (BLKS _ Hb1) as (_ & _ & _ & X4 & _). lia.
      - clear -NO D0. intros X. apply NO. left. split; [exact D0| exact X].
      - pose proof alloc_ceiling_range as ACR. clear -CA GEOM BLKS ACR. destruct CA as [C|[C|(b1 & Hb1 & Hr1)]]; [lia| lia|]. cps_pose (BLKS _ Hb1) as (_ & _ & _ & X4 & _). lia.
      - intros bb Hbb. destruct (NEWB bb Hbb) as [(Y1 & Y2 & Y3 & Y4 & Y5) YD]. unfold L, S0_layout in Y5; cbn [al_img_lo al_img_hi] in Y5. pose proof alloc_ceiling_range as ACR. clear -CA Y4 Y5 YD GEOM ACR Ha. destruct CA as [C|[C|(b1 & Hb1 & Hr1)]]; [lia| destruct Y5; lia|]. destruct (YD _ Hb1) as [HH|HH]; lia. }
    assert (NEWB4 : forall bb a, In bb (cfg_extra c) -> bv_unsigned sp + -160 <= a -> ~ (blk_addr bb <= a < blk_addr bb + blk_size bb)).
    { intros bb a Hbb Ha. cps_destruct (proj1 (NEWB bb Hbb)) as (_ & _ & _ & Y4 & _). clear -Y4 Ha LOC' LO. bz_ceil. lia. }
    assert (SAVES6 : rw_cells s0segs m6 (bv_unsigned sp + -48) (SAVES s4 s3 s2 s1 s0 ra)).
    { eapply (pres_rw_cells _ _ _ _ _ (pres_of_munch _ _ _ MU6' WM6)); [exact SAVES5|]. unfold SAVES; cbn. intros a Ha. apply OUTW.
    - clear -Ha R1 R2 R3 R4 LOC' LO. bz_ceil. pose proof (u64_range sp). lia.
    - clear -Ha R1 R2 R3 R4 LOC' LO. bz_ceil. lia.
    - clear -Ha. lia.
    - clear -Ha D1 D2 D3 D4 LOC' LO. bz_ceil. lia.
    - clear -Ha. lia.
    - intros bb Hbb. apply (NEWB4 bb a Hbb). clear -Ha; lia.
    }
    assert (DL6 : rw_cells s0segs m6 dl [C4 (Z_to_bv 64 dn)]).
    { eapply (pres_rw_cells _ _ _ _ _ (pres_of_munch _ _ _ MU6' WM6)); [exact DL5|]. cbn. intros a Ha. apply OUTW.
    - clear -Ha DLLO DLHI Usp. lia.
    - clear -Ha R1 R2 R3 R4 LOC' LO DLLO. bz_ceil. lia.
    - clear -Ha DLLO. lia.
    - clear -Ha SEP3. lia.
    - clear -Ha DLLO. lia.
    - intros bb Hbb. apply (NEWB4 bb a Hbb). clear -Ha DLLO; lia. }
    subst cx5. clear STRM5 STRM6.
    pose proof DM5 as X5. unfold dmem in X5. cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0 b_strm b_s b_src cxN] in X5. cps_destruct X5 as (_ & _ & _ & _ & _ & _ & STRM5 & _).
    pose proof DM6 as X6. unfold dmem in X6. cbn [di_segs di_got di_stderrp di_crc di_rnums DI_S0 b_strm b_s b_src cxN] in X6. cps_destruct X6 as (_ & _ & _ & _ & _ & _ & STRM6 & _).
    assert (OUT56 : forall x, bv_unsigned sp + -128 + 56 <= x < bv_unsigned sp + -128 + 80 -> outside ([(r, r + 64144); (bv_unsigned sp + -128, bv_unsigned sp + -128 + 44); (dst, dst + dn); (lo, bv_unsigned sp + -128)] ++ RW) x).
    { intros x Hx. apply OUTW.
    - clear -Hx Usp LOC' LO. lia.
    - clear -Hx R1 R2 R3 R4 LOC' LO. bz_ceil. lia.
    - clear -Hx. lia.
    - clear -Hx D1 D2 D3 D4 LOC' LO. bz_ceil. lia.
    - clear -Hx. lia.
    - intros bb Hbb. apply (NEWB4 bb x Hbb). clear -Hx; lia.
    }
    cps_pose (strm_tail_agree _ _ _ _ _ _ STRM5 MU6' WM6 OUT56 STRM6) as (EBA & EBF & EBO).
    cbn [bs_bzalloc bs_bzfree bs_opaque bs_of] in EBA, EBF, EBO.
    cbn [dv_b dvF bs_of bs_bzalloc bs_bzfree bs_opaque] in EBA, EBF, EBO.
    pose proof (proj1 (proj2 DP5)) as JS. unfold jk_static in JS. subst b0. cbn [bs_q1 bs_q2 bs_tol bs_toh bs_bzalloc bs_bzfree bs_opaque] in JS. cps_destruct JS as (Jq1 & Jq2 & Jtol & Jtoh & Jba & Jbf & Jop).
    pose proof (b2b_model junkD (map bv_unsigned payload) dn small) as BM6. rewrite EBZ in BM6.
    assert (Lout6' : Z.of_nat (length (s_out sq2)) = dn - s_avail_out sq2) by (cbn [b_dlen cxN] in Lout6; exact Lout6).
    assert (Ldb6' : Z.of_nat (length db6) = dn) by (cbn [b_dlen cxN] in Ldb6; exact Ldb6).
    assert (Rav6 : 0 <= s_avail_out sq2 <= dn).
    { pose proof (f_equal (@length byte) Edb6) as X. rewrite length_app, length_map, length_rev in X. clear -X Lout6' Ldb6' DN. lia. }
    assert (BWF6 : bzs_wf (bs_of (cxN r (bv_unsigned sp + -128) src len dst dn small n (cfg_tt c) (cfg_l16 c) (cfg_l4 c)) J6 sq2)). 
    { pose proof (dpureF_jwf _ _ _ _ _ _ DP6) as JW. unfold jk_wf in JW. pose proof (in_rel_length _ _ (dpureF_in _ _ _ _ _ _ DP6)) as IRL.
      unfold bzs_wf. cbn [bs_of bs_q1 bs_q2 bs_ai bs_len bs_av bs_dlen b_src b_len b_dst b_dlen cxN]. clear -JW IRL Rav6 LEN DN PAYL. lia. }

    assert (RES3 : forall m', rw_cells s0segs m' dst [CB (Z.to_nat dn) db6] -> (rv2 mod 2 ^ 64 = 0 -> b2bD_result s0segs (if s_avail_out sq2 =? 0 then BZ_OUTBUFF_FULL else BZ_UNEXPECTED_EOF) dst dn (map bv_unsigned payload) small m' dn) /\ (rv2 mod 2 ^ 64 = 4 -> b2bD_result s0segs BZ_OK dst dn (map bv_unsigned payload) small m' (dn - s_avail_out sq2)) /\ (rv2 mod 2 ^ 64 <> 0 -> rv2 mod 2 ^ 64 <> 4 -> b2bD_result s0segs rv2 dst dn (map bv_unsigned payload) small m' dn)).
    { intros m' DBm. split; [| split].
    - intros R0. assert (E0 : rv2 = 0) by (clear -R0 Rrv2; destruct (Z_lt_dec rv2 0); [rewrite <- (Z.mod_add rv2 1) in R0 by lia; rewrite Z.mod_small in R0 by lia | rewrite Z.mod_small in R0 by lia]; lia).
    right; right. split; [exact D0|]. exists junkD, db6. rewrite BM6, E0. cbn [Z.eqb BZ_OK].
    split. { destruct (Z.eqb_spec (s_avail_out sq2) 0) as [E|E]; destruct (Z.ltb_spec 0 (s_avail_out sq2)); try reflexivity; exfalso; clear -E H Rav6; lia. }
    split. { intros X. exfalso. destruct (0 <? s_avail_out sq2); discriminate X. }
    intros _. exact DBm.
    - intros R4'. assert (E4 : rv2 = 4) by (clear -R4' Rrv2; destruct (Z_lt_dec rv2 0); [rewrite <- (Z.mod_add rv2 1) in R4' by lia; rewrite Z.mod_small in R4' by lia | rewrite Z.mod_small in R4' by lia]; lia).
    right; right. split; [exact D0|]. exists junkD. rewrite BM6, E4. cbn [Z.eqb BZ_OK BZ_STREAM_END Pos.eqb].
    assert (LO6 : Z.of_nat (length (s_output sq2)) = dn - s_avail_out sq2) by (unfold s_output; rewrite length_rev; exact Lout6').
    exists (skipn (length (s_output sq2)) db6).
    split; [reflexivity|]. split; [| intros X; exfalso; apply X; reflexivity]. intros _. split; [reflexivity|]. split; [exact LO6|].
    pose proof (dest_split m' dst (s_out sq2) rest6 dn) as DSP. unfold s_output. rewrite <- Edb6 in DSP.
    replace (dn - (dn - s_avail_out sq2)) with (dn - Z.of_nat (length (rev (s_out sq2)))) by (rewrite length_rev; clear -Lout6'; lia).
    replace (skipn (length (rev (s_out sq2))) db6) with rest6 by (rewrite Edb6, <- (length_map (Z_to_bv 8)), skipn_app_exact; reflexivity).
    apply DSP; [apply (u8arr_of_rw_cells s0segs) in DBm; exact DBm| exact Ldb6'].
    - intros R0 R4'. right; right. split; [exact D0|]. exists junkD, db6. rewrite BM6.
    assert (N0 : rv2 <> 0) by (intros E; apply R0; rewrite E; reflexivity). assert (N4 : rv2 <> 4) by (intros E; apply R4'; rewrite E; reflexivity).
    replace (rv2 =? BZ_OK) with false by (symmetry; apply Z.eqb_neq; exact N0). replace (rv2 =? BZ_STREAM_END) with false by (symmetry; apply Z.eqb_neq; exact N4).
    split; [reflexivity|]. split; [intros X; exfalso; exact (N0 X)|]. intros _. exact DBm. }
    eapply (tail_cps AI AC FREEV lo B dst dn dl src len small (map bv_unsigned payload) db6 k LB pD g1 sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m MD K TP GEOM DSTF DLF BLKS HK c rv2 _ _ _ pS r (bs_of (cxN r (bv_unsigned sp + -128) src len dst dn small n (cfg_tt c) (cfg_l16 c) (cfg_l4 c)) J6 sq2) (hd_of (cxN r (bv_unsigned sp + -128) src len dst dn small n (cfg_tt c) (cfg_l16 c) (cfg_l4 c)) J6 d2) (mid_of (cxN r (bv_unsigned sp + -128) src len dst dn small n (cfg_tt c) (cfg_l16 c) (cfg_l4 c)) d2)).
    * exact INV6.
    * exact VMC5.
    * exact NIP.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * eapply vm_only_trans; [exact VMO2 | exact VMO5].
    * exact AUX6.
    * exact ERR6.
    * exact MI6.
    * exact ST6.
    * exact STRM6.
    * exact SAVES6.
    * exact HD6.
    * exact MID6.
    * exact DL6.
    * rewrite <- Ldb6', Nat2Z.id. apply rw_cells_of_u8arr. exact DB6.
    * apply crc_tab_cells. exact IMG6.
    * apply rnums_tab_cells. exact RNA6.
    * unfold b2bD_got. cbn [bd_got bd_stderrp bd_crc bd_rnums S0DI]. split; [exact GO16 | exact GO26].
    * exact BWF6.
    * reflexivity.
    * cbn [bs_bzfree bs_of]. rewrite EBF, Jbf. reflexivity.
    * cbn [bs_opaque bs_of]. rewrite EBO, Jop. reflexivity.
    * reflexivity.
    * cbn [sh_strm hd_of b_strm cxN]. clear; lia.
    * exact RES3.
    * exact PR6.
    + (* [comment removed for export] *)
    assert (Eav0 : bs_av (DecCut.bupd b0 ai5 til5 tih5) = dn) by (unfold DecCut.bupd; subst b0; reflexivity).
    assert (RCF : (rc = 0 \/ rc = -5 \/ rc = -3) /\
      forall m', rw_cells s0segs m' dst [CB (Z.to_nat dn) junk] ->
        (rc mod 2 ^ 64 = 0 -> b2bD_result s0segs (if bs_av (DecCut.bupd b0 ai5 til5 tih5) =? 0 then BZ_OUTBUFF_FULL else BZ_UNEXPECTED_EOF) dst dn (map bv_unsigned payload) small m' dn) /\
        (rc mod 2 ^ 64 = 4 -> b2bD_result s0segs BZ_OK dst dn (map bv_unsigned payload) small m' (dn - bs_av (DecCut.bupd b0 ai5 til5 tih5))) /\
        (rc mod 2 ^ 64 <> 0 -> rc mod 2 ^ 64 <> 4 -> b2bD_result s0segs rc dst dn (map bv_unsigned payload) small m' dn)).
    { rewrite Eav0. destruct RC as [-> | (junkD & RUN)].
      - split; [right; right; reflexivity|]. intros m' DBm.
        split; [intros X; exfalso; clear -X; cbv in X; discriminate X|]. split; [intros X; exfalso; clear -X; cbv in X; discriminate X|].
        intros _ _. right; left. split; [reflexivity|]. split; [exact D0|]. split; [reflexivity|]. exists junk; exact DBm.
      - remember (decompress (dst_init junkD 0 small) (dstrm_init (map bv_unsigned payload) dn)) as DEC1 eqn:EDEC1 in RUN.
        destruct DEC1 as [[rv1 dq1] sq1]. cps_destruct RUN as (-> & Hrv & Rst1 & Sout1 & Sav1).
        assert (EBZ : bzDecompress (dst_init junkD 0 small) (dstrm_init (map bv_unsigned payload) dn) = (rv1, dq1, sq1)).
        { rewrite bzDecompress_eq. cbn [s_in dstrm_init]. rewrite length_map. rewrite bzd_loop_10 by reflexivity. unfold K_call. rewrite <- EDEC1.
          apply K_L_ret; [clear -Hrv; unfold BZ_OK, BZ_DATA_ERROR_MAGIC, BZ_STREAM_END in *; lia | clear -Rst1; unfold BZ_X_OUTPUT; lia]. }
        pose proof (b2b_model junkD (map bv_unsigned payload) dn small) as BMb. rewrite EBZ in BMb.
        split; [clear -Hrv; unfold BZ_OK, BZ_DATA_ERROR_MAGIC in Hrv; lia|].
        intros m' DBm. split; [|split].
        + intros R0. assert (E0 : rv1 = 0) by (clear -R0 Hrv; unfold BZ_OK, BZ_DATA_ERROR_MAGIC in Hrv; destruct Hrv as [E|E]; rewrite E in R0 |- *; [reflexivity| cbv in R0; discriminate R0]).
          right; right. split; [exact D0|]. exists junkD, junk. rewrite BMb, E0, Sav1. cbn [Z.eqb BZ_OK].
          split. { destruct (Z.eqb_spec dn 0) as [E|E]; destruct (Z.ltb_spec 0 dn); try reflexivity; exfalso; clear -E H DN; lia. }
          split. { intros X. exfalso. destruct (0 <? dn); discriminate X. }
          intros _. exact DBm.
        + intros R4'. exfalso. clear -R4' Hrv. unfold BZ_OK, BZ_DATA_ERROR_MAGIC in Hrv. destruct Hrv as [E|E]; rewrite E in R4'; cbv in R4'; discriminate R4'.
        + intros R0 R4'. assert (E5 : rv1 = -5) by (clear -R0 Hrv; unfold BZ_OK, BZ_DATA_ERROR_MAGIC in Hrv; destruct Hrv as [E|E]; rewrite E in R0 |- *; [exfalso; apply R0; reflexivity| reflexivity]).
          right; right. split; [exact D0|]. exists junkD, junk. rewrite BMb, E5. cbn [Z.eqb BZ_OK BZ_STREAM_END Pos.eqb].
          split; [reflexivity|]. split; [intros X; discriminate X|]. intros _. exact DBm. }
    destruct RCF as [Hrc3 RES3b].
    assert (LOLO : 0x66000 <= lo) by (clear -GEOM; bz_ceil; lia).
    eapply (evt_realizes s0segs); [exact Hh5 | exact Hl5 | | ].
    { subst z. unfold FRMj in FRM5. cbn [z_s11 z_s10 z_s9 z_s8 z_s7 z_s6 z_s5 z_s4 z_s3 z_s2 z_s1 z_s0 z_ra] in FRM5.
    eapply (bzd_memexit rc _ (Z_to_bv 64 (bv_unsigned sp + -128 + -112)) (Z_to_bv 64 (bv_unsigned sp + -128))) with (lo := lo) (h := h5) (fj := fj); rewrite ?unsigned_lit by lia.
    - exact Hrc3.
    - replace (bv_unsigned sp + -128 + -112) with (bv_unsigned sp + -128 - 112) by lia. exact FRM5.
    - exact ST5.
    - exact LOLO.
    - clear -GEOM LO. lia.
    - clear -SP47 GEOM. lia.
    - f_equal. lia.
    - exact MI5.
    - exact HD5.
    - exact Rst5.
    - exact Nst5.
    - clear -R1 R2 R3 R4. bz_ceil. lia.
    - clear -R1 R2 R3 R4. bz_ceil. lia. }
    (intros ms7; cps_intros (wa1' & wa2' & -> & ST7)).
    rewrite ret_pc_lit by (clear; lia || reflexivity). rewrite ?unsigned_lit in ST7 by (pose proof alloc_ceiling_range as ACR9; clear - ACR9 Usp LOC' LO SP47; lia).
    eapply (tail_cps AI AC FREEV lo B dst dn dl src len small (map bv_unsigned payload) junk k LB pD g1 sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m MD K TP GEOM DSTF DLF BLKS HK c rc _ _ _ pS r (DecCut.bupd b0 ai5 til5 tih5) h5 d5).
    * exact INV5.
    * exact VMC5.
    * exact NIP.
    * exact Htt5.
    * exact Hl165.
    * exact Hl45.
    * eapply vm_only_trans; [exact VMO2 | exact VMO5].
    * exact AUX5.
    * exact ERR5.
    * exact MI5.
    * exact ST7.
    * exact STRM5.
    * exact SAVES5.
    * unfold DecCut.bupd; subst b0; cbn [bs_S]. exact HD5.
    * unfold DecCut.bupd; subst b0; cbn [bs_S]. exact MID5.
    * exact DL5.
    * exact DST5.
    * exact CRC5.
    * exact RN5.
    * unfold b2bD_got. cbn [bd_got bd_stderrp bd_crc bd_rnums S0DI]. split; [exact GO15 | exact GO25].
    * clear -BWF0 Hai5. unfold bzs_wf, DecCut.bupd in *. subst b0. cbn [bs_q1 bs_q2 bs_ai bs_len bs_av bs_dlen] in *. lia.
    * subst b0; reflexivity.
    * subst b0; reflexivity.
    * subst b0; reflexivity.
    * subst b0; reflexivity.
    * clear -Hstrm5; lia.
    * exact RES3b.
    * exact PR5.
  Qed.
End B2B.
End ACeilS1.
