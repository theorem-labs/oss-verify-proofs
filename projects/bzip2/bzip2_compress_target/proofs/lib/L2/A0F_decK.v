(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim RT_globals.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2StmtD A0_fs_L2f A0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzTac BzTables CmpMem AsanKit AsanKit2 AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzInv BzContracts.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState BzDBlock BzDK DecCutFA A0F_decV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.A0F_decV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Lemma dk_crc_bytes_eq : L_libA.CRC_BYTES = BzTables.bz_crc_table_bytes. Proof. vm_compute. reflexivity. Qed.
Lemma dk_rnums_bytes_eq : L_libA.RNUMS_BYTES = BzTables.bz_rnums_table_bytes. Proof. vm_compute. reflexivity. Qed.

Section DECK.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.

(* [comment removed for export] *)
Definition DSV : word := Z_to_bv 64 STDERR_FILE.
Definition DG1 : word := Z_to_bv 64 0.

Lemma dec_img : forall Σ (m : mem), ART RT Σ m -> L_libA.LIB_A m ->
  ro_cells a0segs m 0xc06b8 [C8 (Z_to_bv 64 0xbf950); C8 DG1; C8 (Z_to_bv 64 0xbf958); C8 (Z_to_bv 64 0xc4000); C8 (Z_to_bv 64 0xc4500)] /\
  ro_cells a0segs m 0xbf950 [C8 DSV] /\ u32arr a0segs m 0xc4500 rnums_words /\ u32arr a0segs m 0xc4000 crc_words.
Proof.
  intros Σ m ART0 (LC & LR).
  destruct (AF_DRV Σ m ART0) as ((GS1 & GS2) & _ & GI & _). destruct (af_got_lib RT AF Σ m ART0) as (GL1 & GL2). pose proof (af_got_slot2 RT AF Σ m ART0) as GL0.
  pose proof (ro_C8_KN m _ _ GS1) as [_ B1]. pose proof (ro_C8_KN m _ _ GI) as [_ B2].
  pose proof (ro_C8_KN m _ _ GL1) as [_ B3]. pose proof (ro_C8_KN m _ _ GL2) as [_ B4]. pose proof (ro_C8_KN m _ _ GL0) as [_ B5].
  split.
  { split; [cbn; tauto|]. cbn [cells_bytes cbytes app] in B1, B2, B3, B4, B5 |- *. rewrite !app_nil_r in *.
    unfold GOT_STDERR in B1. unfold GOT_LLVMINIT in B2.
    apply (proj2 (bytes_at_app a0segs m _ _ _)). split; [exact B1|]. rewrite length_le8. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (proj2 (bytes_at_app a0segs m _ _ _)). split; [exact B2|]. rewrite length_le8. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (proj2 (bytes_at_app a0segs m _ _ _)). split; [exact B5|]. rewrite length_le8. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (proj2 (bytes_at_app a0segs m _ _ _)). split; [exact B3|]. rewrite length_le8. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. exact B4. }
  split; [exact (ro_C8_KN m _ _ GS2)|].
  split.
  - destruct LR as [[_ LB] LW]. cbn [KCells.cells_bytes KCells.cbytes KCells.cells_size KCells.csize Nat.add app] in LB, LW. rewrite app_nil_r in LB.
    pose proof (n_rw_CB_of_bytes m L_libA.RNUMS_A L_libA.RNUMS_BYTES LB ltac:(rewrite L_libA.RNUMS_BYTES_length; exact LW)) as CR.
    rewrite L_libA.RNUMS_BYTES_length, dk_rnums_bytes_eq in CR.
    eapply cb_u32arr; [apply rnums_words_bytes| reflexivity| exact CR].
  - destruct LC as [[_ LB] LW]. cbn [KCells.cells_bytes KCells.cbytes KCells.cells_size KCells.csize Nat.add app] in LB, LW. rewrite app_nil_r in LB.
    pose proof (n_rw_CB_of_bytes m L_libA.CRC_A L_libA.CRC_BYTES LB ltac:(rewrite L_libA.CRC_BYTES_length; exact LW)) as CR.
    rewrite L_libA.CRC_BYTES_length, dk_crc_bytes_eq in CR.
    eapply cb_u32arr; [apply crc_words_bytes| reflexivity| exact CR].
Qed.

Lemma dmem_of_L : forall Σ (m : mem) cx payload v, ART RT Σ m -> L_libA.LIB_A m -> dmemL cx payload m v -> DecCutA.dmem DI_A0 cx DG1 DSV payload m v.
Proof.
  intros Σ m cx payload v ART0 LIB (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  destruct (dec_img Σ m ART0 LIB) as (I1 & I2 & I3 & _).
  unfold DecCutA.dmem. cbn [di_segs di_got di_stderrp di_crc di_rnums DI_A0].
  repeat (split; [assumption|]). exact I3.
Qed.
Lemma dmemL_of : forall (m : mem) cx g1 sv payload v, DecCutA.dmem DI_A0 cx g1 sv payload m v -> dmemL cx payload m v.
Proof.
  intros m cx g1 sv payload v (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _). cbn [di_segs DI_A0] in *.
  unfold dmemL. repeat (split; [assumption|]). exact H9.
Qed.

(* [comment removed for export] *)
Ltac dk_app X OFF := apply shd_app; [clear - X; lia| clear - OFF; unfold SH_LO, SH_HI; lia].

(* [comment removed for export] *)
Lemma dec_act_sh : forall Σ (m : mem) (A : act14) zp zn,
  let cx := a_cx A in
  ART RT Σ m -> a_m0 A = m -> act_ok AIHI0 A ->
  In (b_s cx, 64144) (rt_live RT Σ) -> In (zp, zn) (rt_live RT Σ) -> zp <= b_src cx -> b_src cx + b_len cx <= zp + zn ->
  (b_small cx = 0 -> In (b_tt cx, 400000 * b_n cx) (rt_live RT Σ)) ->
  (b_small cx = 1 -> In (b_ll16 cx, 200000 * b_n cx) (rt_live RT Σ) /\ In (b_ll4 cx, 50000 * b_n cx) (rt_live RT Σ)) ->
  bytes_at a0segs m (a_sht A) (repeat z8 10) ->
  (b_strm cx + 80 <= 0x7fff7000 \/ 0x10007fff8000 <= b_strm cx) -> (a_fb A + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= a_fb A) -> 0x10007fff8000 <= a_P A - 256 ->
  a_usp A <= 2^47 ->
  act_sh DI_A0 A.
Proof.
  intros Σ m A zp zn cx ART0 EM AOK SLIV ZLIV ZLO ZHI TLIV LLIV ZSH OFFT OFFF OFFP USPT. subst cx.
  destruct AOK as (LINB & AL & SEPB & ANS & ANT & ANF & LO2 & LO1 & USP & GEO & _ & _ & PL & _ & _ & _ & _ & _ & _ & _ & _ & NZF & NZS).
  cbv zeta in LINB.
  destruct LINB as (S0 & _ & T0 & T1c & SRC0 & LEN0 & _ & _ & _ & _ & _ & _ & FB0 & _ & _ & _ & SM01 & NR & _).
  pose proof alloc_ceiling_range as ACR. unfold CEILING in T1c.
  destruct AL as (S16 & T8 & _ & _ & TT16 & L1616 & L416).
  destruct SEPB as (_ & _ & _ & _ & _ & _ & DFS & DFT & DFZ & _ & _ & _ & _ & DTT & DL16 & DL4 & _ & _ & _ & IFB & _).
  unfold disj in DFS, DFT, DFZ, DTT, DL16, DL4. unfold img_apartA in IFB.
  pose proof (af_live_range RT AF Σ m _ _ ART0 SLIV) as (SL0 & SL1 & _). pose proof (af_live_offshadow RT AF Σ m _ _ ART0 SLIV) as SOFF.
  pose proof (af_live_range RT AF Σ m _ _ ART0 ZLIV) as (ZL0 & ZL1 & _). pose proof (af_live_offshadow RT AF Σ m _ _ ART0 ZLIV) as ZOFF.
  pose proof (af_sp0_range RT AF Σ m ART0) as (_ & SP0T). unfold USTACK_TOP, STACK_WIN in *.
  destruct (af_acc_live RT AF Σ m _ _ ART0 SLIV) as [_ ACCS]. destruct (af_acc_live RT AF Σ m _ _ ART0 ZLIV) as [_ ACCZ].
  pose proof (strm_acc m (b_strm (a_cx A)) (a_sht A) ANT ltac:(clear - T0; lia) ZSH) as ACCT.
  pose proof (af_acc_rnums RT AF Σ m ART0) as ACCR.
  (* [comment removed for export] *)
  assert (DJ : forall x, 0 <= x < 2^47 -> (x < a_fb A \/ a_fb A + 64 <= x) ->
               disjoint_from (W14 A) (x / 8 + 2147450880) 1).
  { intros x X XF. unfold W14, blk_ivls.
    assert (C0 : x / 8 + 2147450880 + 1 <= b_s (a_cx A) \/ b_s (a_cx A) + DSTATE_SIZE <= x / 8 + 2147450880) by (unfold DSTATE_SIZE; dk_app X SOFF).
    assert (C1 : x / 8 + 2147450880 + 1 <= b_strm (a_cx A) \/ b_strm (a_cx A) + 20 <= x / 8 + 2147450880) by (dk_app X OFFT).
    assert (C2 : x / 8 + 2147450880 + 1 <= a_P A - 256 \/ a_usp A <= x / 8 + 2147450880) by (apply shd_app; [clear - X; lia| right; unfold SH_HI; clear - OFFP; lia]).
    assert (C3 : x / 8 + 2147450880 + 1 <= a_fb A \/ a_fb A + 56 <= x / 8 + 2147450880) by (dk_app X OFFF).
    assert (C4 : x / 8 + 2147450880 + 1 <= a_shf A \/ a_shf A + 8 <= x / 8 + 2147450880).
    { pose proof (shd_anchor (a_fb A) (a_shf A) 0 8 x ANF ltac:(clear - XF; lia)) as H. rewrite Z.add_0_r in H. exact H. }
    destruct (b_small (a_cx A) =? 0) eqn:ESM; cbn [app disjoint_from].
    - apply Z.eqb_eq in ESM. pose proof (TLIV ESM) as TL. pose proof (af_live_offshadow RT AF Σ m _ _ ART0 TL) as TOFF.
      repeat (split; [assumption|]). split; [dk_app X TOFF| exact I].
    - apply Z.eqb_neq in ESM. assert (E1 : b_small (a_cx A) = 1) by (clear - SM01 ESM; lia). destruct (LLIV E1) as (L16L & L4L).
      pose proof (af_live_offshadow RT AF Σ m _ _ ART0 L16L) as O16. pose proof (af_live_offshadow RT AF Σ m _ _ ART0 L4L) as O4.
      repeat (split; [assumption|]). split; [dk_app X O16|]. split; [dk_app X O4| exact I]. }
  unfold act_sh. cbv zeta. rewrite EM. cbn [di_segs di_rnums DI_A0].
  split; [| split; [| split; [| split; [| split]]]].
  - apply (shzW_of_acc_gen a0segs _ m (b_s (a_cx A)) 64144 _ _ ACCS); [clear - SL0; lia| clear; lia| clear - S16; Z.div_mod_to_equations; lia|].
    intros x Hx. apply DJ; [clear - Hx SL0 SL1 SP0T; lia| clear - Hx DFS; unfold DSTATE_SIZE in DFS; lia].
  - apply (shzW_of_acc_gen a0segs _ m (b_strm (a_cx A)) 80 _ _ ACCT); [clear - T0; lia| clear; lia| clear - T8; Z.div_mod_to_equations; lia|].
    intros x Hx. apply DJ; [clear - Hx T0 T1c ACR; lia| clear - Hx DFT; lia].
  - pose proof (L2Kit.acc_sub asegs m zp zn (b_src (a_cx A)) (b_len (a_cx A)) ACCZ ZLO ZHI) as ACCP.
    apply (shpW_of_acc_gen a0segs _ m _ _ ACCP). intros x Hx. apply DJ; [clear - Hx ZLO ZHI ZL0 ZL1 SP0T; lia| clear - Hx DFZ; lia].
  - apply (shzW_of_acc_gen a0segs _ m 0xc4500 2048 _ _ ACCR); [clear; lia| clear; lia| apply Z.leb_le; vm_compute; reflexivity|].
    intros x Hx. apply DJ; [clear - Hx; lia| clear - Hx IFB FB0; lia].
  - intros ESM. pose proof (TLIV ESM) as TL. pose proof (NZF ESM) as TNZ. destruct (DTT TNZ) as (_ & _ & _ & DFB & _).
    pose proof (af_live_range RT AF Σ m _ _ ART0 TL) as (TL0 & TL1 & _). unfold STACK_WIN in TL1. destruct (af_acc_live RT AF Σ m _ _ ART0 TL) as [_ ACCB].
    apply (shzW_of_acc_gen a0segs _ m (b_tt (a_cx A)) (400000 * b_n (a_cx A)) _ _ ACCB); [clear - TL0; lia| clear; lia| clear - TT16; Z.div_mod_to_equations; lia|].
    intros x Hx. apply DJ; [clear - Hx TL0 TL1 SP0T; lia| clear - Hx DFB; lia].
  - intros ESM. destruct (LLIV ESM) as (L16L & L4L). destruct (NZS ESM) as (N16 & N4).
    destruct (DL16 N16) as (_ & _ & _ & DFB16 & _). destruct (DL4 N4) as (_ & _ & _ & DFB4 & _).
    pose proof (af_live_range RT AF Σ m _ _ ART0 L16L) as (A0 & A1 & _). unfold STACK_WIN in A1. destruct (af_acc_live RT AF Σ m _ _ ART0 L16L) as [_ ACC16].
    pose proof (af_live_range RT AF Σ m _ _ ART0 L4L) as (B0 & B1 & _). unfold STACK_WIN in B1. destruct (af_acc_live RT AF Σ m _ _ ART0 L4L) as [_ ACC4].
    split.
    + apply (shzW_of_acc_gen a0segs _ m (b_ll16 (a_cx A)) (200000 * b_n (a_cx A)) _ _ ACC16); [clear - A0; lia| clear; lia| clear - L1616; Z.div_mod_to_equations; lia|].
      intros x Hx. apply DJ; [clear - Hx A0 A1 SP0T; lia| clear - Hx DFB16; lia].
    + apply (shzW_of_acc_gen a0segs _ m (b_ll4 (a_cx A)) (50000 * b_n (a_cx A)) _ _ ACC4); [clear - B0; lia| clear; lia| clear - L416; Z.div_mod_to_equations; lia|].
      intros x Hx. apply DJ; [clear - Hx B0 B1 SP0T; lia| clear - Hx DFB4; lia].
Qed.

(* [comment removed for export] *)
Lemma dec_act_ok : forall Σ (m : mem) (A : act14) zp zn op on fr fS kS,
  ART RT Σ m -> alloc_ceiling = rt_sp0 RT Σ - STACK_WIN ->
  rt_frames RT Σ = (a_fb A, 0%nat) :: fr -> In (fS, kS) fr -> fS <= b_strm (a_cx A) -> b_strm (a_cx A) + 80 <= fS + fs_size kS - 8 -> b_strm (a_cx A) mod 8 = 0 ->
  In (b_s (a_cx A), 64144) (rt_live RT Σ) ->
  In (zp, zn) (rt_live RT Σ) -> zp <= b_src (a_cx A) -> b_src (a_cx A) + b_len (a_cx A) <= zp + zn ->
  In (op, on) (rt_live RT Σ) -> op <= b_dst (a_cx A) -> b_dst (a_cx A) + b_dlen (a_cx A) <= op + on ->
  (b_tt (a_cx A) <> 0 -> In (b_tt (a_cx A), 400000 * b_n (a_cx A)) (rt_live RT Σ)) ->
  (b_ll16 (a_cx A) <> 0 -> In (b_ll16 (a_cx A), 200000 * b_n (a_cx A)) (rt_live RT Σ)) ->
  (b_ll4 (a_cx A) <> 0 -> In (b_ll4 (a_cx A), 50000 * b_n (a_cx A)) (rt_live RT Σ)) ->
  dpureA (a_cx A) -> 1 <= b_n (a_cx A) ->
  (b_small (a_cx A) = 0 -> b_tt (a_cx A) <> 0) -> (b_small (a_cx A) = 1 -> b_ll16 (a_cx A) <> 0 /\ b_ll4 (a_cx A) <> 0) ->
  sanchor (b_s (a_cx A)) (a_shs A) -> sanchor (b_strm (a_cx A)) (a_sht A) -> sanchor (a_fb A) (a_shf A) ->
  alloc_ceiling <= a_lo A -> a_lo A + 256 <= a_P A -> a_P A + 832 <= a_usp A <= a_P A + 848 -> a_P A mod 32 = 0 ->
  dsh_wf (a_h0 A) -> bzs_wf (a_b0 A) -> Z.of_nat (length (a_payload A)) = b_len (a_cx A) ->
  sh_strm (a_h0 A) = b_strm (a_cx A) -> sh_n (a_h0 A) = b_n (a_cx A) -> bv_unsigned (sh_small (a_h0 A)) = b_small (a_cx A) ->
  bs_S (a_b0 A) = b_s (a_cx A) -> bs_src (a_b0 A) = b_src (a_cx A) -> bs_len (a_b0 A) = b_len (a_cx A) ->
  bs_dst (a_b0 A) = b_dst (a_cx A) -> bs_dlen (a_b0 A) = b_dlen (a_cx A) ->
  act_ok AIHI0 A.
Proof.
  intros Σ m A zp zn op on fr fS kS ART0 CEQ FRS FSIN FSLO FSHI T8 SLIV ZLIV ZLO ZHI OLIV OLO OHI TLIV L16LIV L4LIV PURE N1 NZF NZS ANS ANT ANF
         LO1 LO2 GEO P32 HWF BWF PL HS HN HSM QS QSRC QLEN QDST QDLEN.
  destruct PURE as (LEN0 & DLEN0 & SM01 & NR & S16 & TT16 & L1616 & L416 & SEP).
  destruct SEP as (D1 & D2 & D3 & D4 & D5 & D6 & DTT & DL16 & DL4 & DLL). cbv zeta in D1, D2, D3, D4, D5, D6, DTT, DL16, DL4, DLL.
  assert (FBIN : In (a_fb A, 0%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (FSIN' : In (fS, kS) (rt_frames RT Σ)) by (rewrite FRS; right; exact FSIN).
  pose proof (af_frames_range RT AF Σ m _ _ ART0 FBIN) as (FB0 & FB1 & FBI & FBL). change (fs_size 0) with 64 in FB1, FBI, FBL.
  pose proof (af_frames_range RT AF Σ m _ _ ART0 FSIN') as (FS0 & FS1 & FSI & _).
  pose proof (af_frames_align RT AF Σ m _ _ ART0 FBIN) as (FB64 & _).
  pose proof (af_frames_disj RT AF Σ m (a_fb A) 0%nat fS kS [] fr ART0 FRS FSIN) as FBS. change (fs_size 0) with 64 in FBS.
  pose proof (af_fshadow_apart RT AF Σ m _ _ ART0 FBIN) as (SHL & SHFR). change (fs_size 0) with 64 in SHL, SHFR.
  assert (SHE : shad (a_fb A) = a_shf A /\ shad (a_fb A + 64) = a_shf A + 8).
  { destruct ANF as [F8 ->]. unfold shad, SHB. clear - F8. split; [reflexivity| Z.div_mod_to_equations; lia]. }
  destruct SHE as [SHE0 SHE1]. rewrite SHE0, SHE1 in SHL, SHFR.
  pose proof (af_live_range RT AF Σ m _ _ ART0 SLIV) as (SL0 & SL1 & SLI). pose proof (af_live_range RT AF Σ m _ _ ART0 ZLIV) as (ZL0 & ZL1 & _).
  pose proof (af_live_range RT AF Σ m _ _ ART0 OLIV) as (OL0 & OL1 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as (_ & SP0T). pose proof alloc_ceiling_range as ACR.
  pose proof (bv_unsigned_in_range 64 (a_sp A)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  rewrite <- CEQ in *. unfold SEGTOP_A, USTACK_TOP in *.
  pose proof (FBL _ _ SLIV) as XS. pose proof (FBL _ _ ZLIV) as XZ. pose proof (SHL _ _ SLIV) as YS. pose proof (SHL _ _ ZLIV) as YZ. pose proof (SHFR _ _ FSIN') as YT.
  pose proof (SHFR _ _ FBIN) as YF. change (fs_size 0) with 64 in YF.
  assert (BLK : forall p n, In (p, n) (rt_live RT Σ) -> (0 < p /\ p + n <= alloc_ceiling) /\ (a_fb A + 64 <= p \/ p + n <= a_fb A) /\ (p + n <= a_shf A \/ a_shf A + 8 <= p) /\ (p + n <= 0x10000 \/ 6414336 <= p)).
  { intros p n IN. pose proof (af_live_range RT AF Σ m _ _ ART0 IN) as (A0 & A1 & A2). rewrite <- CEQ in A1. unfold SEGTOP_A in A2.
    split; [split; [exact A0| exact A1]|]. split; [exact (FBL _ _ IN)|]. split; [exact (SHL _ _ IN)| exact A2]. }
  unfold act_ok. cbv zeta.
  split.
  { unfold DSTATE_SIZE, CEILING. repeat split; try assumption; try (clear - SL0 SL1 ZL0 ZL1 ZLO ZHI OL0 OL1 OLO OHI FS0 FS1 FSLO FSHI FB0 FB1 LEN0 DLEN0 NR N1; lia).
    - destruct ANF as [_ ->]. clear - FB0. Z.div_mod_to_equations. lia.
    - destruct ANF as [_ ->]. clear - FB1 ACR. Z.div_mod_to_equations. lia.
    - destruct (Z.eq_dec (b_tt (a_cx A)) 0) as [E|E]; [left; exact E| right; exact (proj1 (BLK _ _ (TLIV E)))].
    - destruct (Z.eq_dec (b_ll16 (a_cx A)) 0) as [E|E]; [left; exact E| right; exact (proj1 (BLK _ _ (L16LIV E)))].
    - destruct (Z.eq_dec (b_ll4 (a_cx A)) 0) as [E|E]; [left; exact E| right; exact (proj1 (BLK _ _ (L4LIV E)))]. }
  split. { unfold ctx_alA. repeat split; assumption. }
  split.
  { unfold act_sepA, disj, img_apartA, DSTATE_SIZE. cbv zeta. unfold disj in D1, D2, D3, D4, D5, D6, DTT, DL16, DL4, DLL.
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split; [exact D5|]. split; [exact D6|].
    split; [clear - XS; lia|]. split; [clear - FBS FSLO FSHI; lia|]. split; [clear - XZ ZLO ZHI; lia|]. split; [clear - YF; lia|].
    split; [clear - YS; lia|]. split; [clear - YT FSLO FSHI; lia|]. split; [clear - YZ ZLO ZHI; lia|].
    split. { intros E. destruct (DTT E) as (B1 & B2 & B3 & _). destruct (BLK _ _ (TLIV E)) as (_ & B4 & B5 & _). repeat split; try assumption; clear - B4 B5; lia. }
    split. { intros E. destruct (DL16 E) as (B1 & B2 & B3 & _). destruct (BLK _ _ (L16LIV E)) as (_ & B4 & B5 & _). repeat split; try assumption; clear - B4 B5; lia. }
    split. { intros E. destruct (DL4 E) as (B1 & B2 & B3 & _). destruct (BLK _ _ (L4LIV E)) as (_ & B4 & B5 & _). repeat split; try assumption; clear - B4 B5; lia. }
    split; [exact DLL|].
    split; [exact SLI|]. split; [clear - FSI FSLO FSHI; lia|]. split; [exact FBI|].
    split; [intros E; exact (proj2 (proj2 (proj2 (BLK _ _ (TLIV E)))))|]. split; [intros E; exact (proj2 (proj2 (proj2 (BLK _ _ (L16LIV E)))))|].
    intros E; exact (proj2 (proj2 (proj2 (BLK _ _ (L4LIV E))))). }
  unfold CEILING. repeat (split; [first [assumption| clear - SPR; lia]|]). assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dk_dj_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l h] W IH]; cbn [disjoint_from]; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H0 HW]. split; [clear - H0 H1 H2; lia| exact (IH a n a' n' HW H1 H2)].
Qed.

Section DecAct.
Variables (lo P usp sp0 FB SHF : Z) (fr : list (Z * nat)) (live0 Wc : list (Z * Z)).
Hypothesis G : act_geom RT lo P usp sp0 true 0 FB SHF 64 8 fr live0 Wc.
Variable A : act14.
Hypothesis AP : a_P A = P.
Hypothesis AFB : a_fb A = FB.
Hypothesis ASHF : a_shf A = SHF.
Hypothesis AUSP : a_usp A = usp.

Lemma dec_rframe_xfer : forall Σ W (m m' : mem) a cs,
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m' -> disjoint_from W P (usp - P) ->
  P <= a -> a + Z.of_nat (cells_size cs) <= usp -> rw_cells a0segs m a cs -> rw_cells a0segs m' a cs.
Proof.
  intros Σ W m m' a cs STEP DJ A0 A1 H.
  apply (x_rw_cells RT P Σ W m m' STEP a cs H).
  - apply (cls_rframe G Σ); [exact A0| exact A1].
  - apply (dk_dj_sub W P (usp - P)); [exact DJ| exact A0| clear - A1; lia].
Qed.

Lemma dec_aframe_xfer : forall Σ W (m m' mi : mem),
  sig_ok RT sp0 true 0 FB fr live0 Σ -> ART RT Σ m' ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) P W m m' ->
  disjoint_from W P (usp - P) -> disjoint_from W FB 64 -> disjoint_from W SHF 8 ->
  aframe A m -> aframe A m'.
Proof.
  intros Σ W m m' mi SOK ART' STEP DP DF DS (zt & ng & jg & j24 & pos & j38 & fl & GEO & NG & FLP & FRM & FRT & FF & FS).
  destruct (release_inline2 AF G (mi := mi) Σ m' eq_refl SOK ART') as (_ & fl' & _ & FLP' & _).
  rewrite AP, AUSP in GEO. rewrite AP in FRM, FRT. rewrite AFB in FF. rewrite ASHF in FS.
  exists zt, ng, jg, j24, pos, j38, fl'. rewrite AP, AUSP, AFB, ASHF.
  split; [exact GEO|]. split; [exact NG|].
  split; [replace (FB + 56) with (FB + 64 - 8) by (clear; lia); exact (ro_C8_KN m' _ _ FLP')|].
  split; [apply (dec_rframe_xfer Σ W m m' _ _ STEP DP); [clear; lia| unfold FM_CELLS; cbn [cells_size csize Nat.add length]; clear - GEO; lia| exact FRM]|].
  split; [apply (dec_rframe_xfer Σ W m m' _ _ STEP DP); [clear; lia| unfold FT_REGS; cbn [cells_size csize Nat.add]; clear - GEO NG; lia| exact FRT]|].
  split.
  - apply (x_rw_cells RT P Σ W m m' STEP _ _ FF); cbn [cells_size csize Nat.add].
    + apply (cls_frame G Σ _ _ SOK); clear; lia.
    + apply (dk_dj_sub W FB 64); [exact DF| clear; lia| clear; lia].
  - apply (x_rw_cells RT P Σ W m m' STEP _ _ FS); cbn [cells_size csize Nat.add].
    + apply (cls_shadow G Σ _ _ SOK); clear; lia.
    + exact DS.
Qed.
End DecAct.

End DECK.
