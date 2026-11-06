(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib RY_yalloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BI_globals2 BI_region_is_poisoned BI_asan_memcpy1 BI_asan_memcpy BI_asan_memset BYajlRep BYajl_iface BY_rz BY_hand BY_set_default BY_client BY_alloc1 BY_alloc2 BY_alloc3 BY_alloc4 BY_alloc5 BY_alloc6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis AFLSEP : AHK_y_aflsep_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis GLOBY : AHK_y_globals_shadow_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis RREFL : ayR_refl_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YNEW : yphi_new_alloc_stmt Y.
Hypothesis ASM1 : astack_malloc_stmt Y 1 AY_STACK_MALLOC_1.
Hypothesis FREL : AHK_y_fake_release_stmt Y.
Hypothesis FND : AHK_y_fnodup_stmt Y.
Hypothesis AFLC : AHK_y_flag_cell_stmt Y.
Hypothesis WMAL : aywrap_malloc_stmt Y.
Hypothesis WREA0 : aywrap_realloc_null_stmt Y.
Hypothesis LALLOC : aylex_alloc_stmt Y.
Hypothesis BALLOC : aybuf_alloc_stmt Y.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis USTEP : forall m SP ra s0 ra' s0', In (bv_unsigned ra) URA -> SP + 16 <= bv_unsigned s0 < 2^47 ->
    rw_cells bsegs m (bv_unsigned s0 - 16) [C8 s0'; C8 ra'] -> y_uanchor Y m (bv_unsigned s0) ra' s0' -> y_uanchor Y m SP ra s0.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.
Hypothesis URA_mal : In 0x824f8 URA.      (* [comment removed for export] *)
Hypothesis URA_lxa : In 0x8259c URA.      (* [comment removed for export] *)
Hypothesis URA_ba : In 0x825d8 URA.       (* [comment removed for export] *)
Hypothesis URA_rea : In 0x8269c URA.      (* [comment removed for export] *)
Hypothesis ICPG : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals bsegs m A_SB.
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window bsegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).
Hypothesis STATY : AHK_y_statics_stmt Y.

Ltac rchain := first [eassumption | eapply RRT; [eassumption| rchain]].

Section Tail.
Variables (LF : list fblock) (REST : list ablock) (CFGP CX lo L RR : Z) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (mo : Model) (s : y_APS Y).
Variables (SQ ff : Z).
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : y_APS Y) (h : yhandle) (mh : mhand),
     ayalloc_rpost Y sp m mo s LF REST CFGP CX lo L RR a0' fc' m' mo' s' h mh ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom bsegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis TP : tp = Z_to_bv 64 (c_tp ACONSTS).
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - (208 + (64 + (32 + 8192))).   (* [comment removed for export] *)
Hypothesis SPLT : bv_unsigned sp < 2^47.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis SQR : bv_unsigned sp - 176 <= SQ <= bv_unsigned sp - 160.
Hypothesis FFsh : amem ff 128.   (* [comment removed for export] *)
Hypothesis FFce : ff + 128 <= alloc_ceiling.
Hypothesis FFal : ff mod 128 = 0.
Hypothesis PFR : amem (y_aflag Y 1 ff) 1 /\ y_aflag Y 1 ff + 1 <= alloc_ceiling.
Variable AL : Z.    (* [comment removed for export] *)
Hypothesis FLin : In (1, AL) LF.
Hypothesis FLcx : AL + 32 = CX.
Hypothesis ECFG : CFGP = CX + 32.
Hypothesis FL_1 : amem AL 128.
Hypothesis FL_2 : AL + 128 <= alloc_ceiling.
Hypothesis FL_ff : AL + 128 <= ff \/ ff + 128 <= AL.
Hypothesis FRESH : forall g, In g LF -> In g ((1, ff) :: LF) /\ snd g <> snd (1, ff).
Hypothesis RR0 : 0 <= RR.
Hypothesis SQ32 : SQ mod 32 = 0.
Hypothesis NBIG : nbig REST <= AY_NBIG_REST.
Hypothesis UA : y_uanchor Y m (bv_unsigned sp) ra s0.

(* [comment removed for export] *)
Lemma nd_mid_ne : forall (l1 : list ablock) x l2 b, List.NoDup (map ab_addr (l1 ++ x :: l2)) -> In b l2 -> ab_addr x <> ab_addr b.
Proof. aceil.
  induction l1 as [|y l1 IH]; intros x l2 b ND Hb; cbn [app] in ND.
  - exact (nd_head_ne _ _ _ ND Hb).
  - apply (IH x l2 b); [exact (nd_tail _ _ ND)| exact Hb].
Qed.

(* [comment removed for export] *)
Lemma j_realloc : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (H Lx B0 NS : Z) (mbl : mbuf) (bb : nat) (lblk : yptr) (RR4 : Z)
    (k0 k32 : list byte) (pew pad w0 : word) (shf : list byte),
  let lx := mkLexer 0 0 LE_ok ybuf_zero bb 0 0 1 1 in
  let LBX := mkABlock B0 32 :: mkABlock Lx 48 :: mkABlock (mb_addr mbl) 32 :: mkABlock H 104 :: REST in
  a0 = Z_to_bv 64 NS -> ablock_range ACONSTS NS 128 -> oshw_hi 0 (2^47) <= NS -> oshadow m1 NS 128 ->
  (exists junk, rw_cells bsegs m1 NS [CB (Z.to_nat 128) junk]) -> AYST Y s1' (mkABlock NS 128 :: LBX) ((1, ff) :: LF) m1 mo1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 56) (bv_unsigned sp + -104) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ [CB 8 k0; C8 (Z_to_bv 64 (ff + 48)); C8 (Z_to_bv 64 AY_CALLBACKS); C8 (Z_to_bv 64 CX); CB 16 k32; C8 (Z_to_bv 64 ff)] ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m1 ff [C8 w0] ->
  rw_cells bsegs m1 (ff + 120) [C8 (Z_to_bv 64 (y_aflag Y 1 ff))] -> rw_cells bsegs m1 (ff / 8 + 2147450880) [CB 16 shf] ->
  rw_cells bsegs m1 (ff + 32) [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  u8arr bsegs m1 (2147450880 + (ff + 32) / 8) (blk_shadow 32) ->
  rw_cells bsegs m1 CFGP [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1)] -> oshadow m1 CFGP 8 -> oshadow m1 CX 8 ->
  rw_cells bsegs m1 H (hcells15 AY_CALLBACKS CX Lx pew (Z_to_bv 64 0) pad (Z_to_bv 64 B0) (Z_to_bv 64 0) (Z_to_bv 64 128) (Z_to_bv 64 0) (Z_to_bv 64 (H + 72))) ->
  u8arr bsegs m1 (2147450880 + H / 8) (blk_shadow 104) ->
  17594333495296 <= H -> H + 104 <= alloc_ceiling -> H mod 16 = 0 -> (H + 104 <= ff \/ ff + 128 <= H) -> (AL + 128 <= H \/ H + 104 <= AL) ->
  rw_cells bsegs m1 Lx (lexer_cells lx (mb_addr mbl) (H + 72)) -> rw_cells bsegs m1 (mb_addr mbl) (buf_cells ybuf_zero 0 (H + 72)) -> mb_data mbl = 0 ->
  rw_cells bsegs m1 B0 (buf_cells ybuf_zero 0 (H + 72)) -> 17594333495296 <= B0 ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s ->
  RR4 <= y_acredit Y s1' ->
  RR <= RR4 ->
  (forall hb lb db sb, y_phi_hand Y (yalloc_hand hb lb db sb bb) L + RR <= RR4) ->
  yleaf (ylex_alloc 1 1) (Some (lblk, lx)) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR (Z_to_bv 64 AAL_RET7) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (H + 48)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 (H + 60)) (Z_to_bv 64 (H + 96)) (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
                          F1 (Z_to_bv 64 AAL_RET7) fc1 None m1 (seg_rom bsegs)) mo1) K.
Proof. aceil.
  intros until shf. intros lx LBX EA0 NSR NSSH OSN NCJ AYX MI1 ST1 GAP1 FRM1 FR1 SV1 FF8 FFP SHC YAF ASH CFC1 OSC1 OSX1 HC HS HR1 HR2 H16 SEPHF SEPHL LXC LBC MBD0 B0C B0SH PRES1 R1 SO1 CRED1 CRA CRB HLX.
  unfold amem in FFsh, PFR, FL_1.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (E8F : ff = 8 * (ff / 8)) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  assert (H8 : H mod 8 = 0) by (clear -CEILB H16; Z.div_mod_to_equations; lia).
  destruct NONNEG as (NA0 & NB0 & NH0 & NN0). pose proof (NB0 ybuf_zero) as NBZ.
  assert (INH : In (mkABlock H 104) LBX) by (right; right; right; left; reflexivity).
  assert (AGREE1 : forall a, bv_unsigned sp <= a < 2^47 -> m1 (wa a) = m (wa a)).
  { intros a Ha. destruct (PRES1 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  (* [comment removed for export] *)
  subst a0. destruct NCJ as (nj & NC). apply AYST_split in AYX. destruct AYX as [AHKX YSX].
  change (Z.to_nat 128) with 128%nat in NC. assert (LNJ : length nj = 128%nat) by (destruct NC as [[WF _] _]; cbn in WF; tauto).
  unfold ablock_range, ACONSTS in NSR; aceil. cbn [c_img_hi] in NSR. rewrite oshw_hi_0 in NSSH.
  pose proof OSN as (_ & _ & NSH). unfold A_SB in NSH.
  destruct (BLKY _ _ _ _ _ AHKX) as (RNGX & SEPX & NDX).
  assert (INH' : In (mkABlock H 104) (mkABlock NS 128 :: LBX)) by (right; exact INH).
  assert (NDH : forall b, In b REST -> In b (mkABlock NS 128 :: LBX) /\ ab_addr b <> ab_addr (mkABlock H 104)).
  { intros b Hb. split; [right; right; right; right; right; exact Hb|]. intros E. exact (nd_mid_ne [mkABlock NS 128; mkABlock B0 32; mkABlock Lx 48; mkABlock (mb_addr mbl) 32] (mkABlock H 104) REST b NDX Hb (eq_sym E)). }
  assert (NDN : forall b, In b REST -> In b (mkABlock NS 128 :: LBX) /\ ab_addr b <> ab_addr (mkABlock NS 128)).
  { intros b Hb. split; [right; right; right; right; right; exact Hb|]. intros E. exact (nd_head_ne _ _ _ NDX ltac:(right; right; right; right; exact Hb) (eq_sym E)). }
  pose proof (RNGX _ (or_intror (or_introl eq_refl))) as RB0. pose proof (RNGX _ (or_intror (or_intror (or_introl eq_refl)))) as RLX. pose proof (RNGX _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as RLB.
  cbn [ab_addr ab_size] in RB0, RLX, RLB. unfold ablock_range, ACONSTS in RB0, RLX, RLB; aceil. cbn [c_img_hi] in RB0, RLX, RLB.
  pose proof (SEPX _ _ (or_introl eq_refl) INH' (nd_head_ne _ _ _ NDX INH)) as SNH. cbn [ab_addr ab_size] in SNH.
  pose proof (SEPX _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) (nd_head_ne _ _ _ NDX (or_introl eq_refl))) as SNB0. cbn [ab_addr ab_size] in SNB0.
  pose proof (SEPX _ _ (or_introl eq_refl) (or_intror (or_intror (or_introl eq_refl))) (nd_head_ne _ _ _ NDX (or_intror (or_introl eq_refl)))) as SNL. cbn [ab_addr ab_size] in SNL.
  pose proof (SEPX _ _ (or_introl eq_refl) (or_intror (or_intror (or_intror (or_introl eq_refl)))) (nd_head_ne _ _ _ NDX (or_intror (or_intror (or_introl eq_refl))))) as SNLB. cbn [ab_addr ab_size] in SNLB.
  destruct (LAYY _ _ _ _ _ AHKX) as (_ & LAYFBX & _).
  pose proof (proj1 (LAYFBX (1, ff) (mkABlock NS 128) (or_introl eq_refl) (or_introl eq_refl))) as SNF. cbn [fst snd ab_addr ab_size] in SNF. rewrite ff_bytes_1 in SNF.
  pose proof (proj1 (LAYFBX (1, AL) (mkABlock NS 128) (or_intror FLin) (or_introl eq_refl))) as SNAL. cbn [fst snd ab_addr ab_size] in SNAL. rewrite ff_bytes_1 in SNAL.
  pose proof (proj1 (LAYFBX (1, ff) (mkABlock B0 32) (or_introl eq_refl) (or_intror (or_introl eq_refl)))) as SFB0.
  pose proof (proj1 (LAYFBX (1, ff) (mkABlock Lx 48) (or_introl eq_refl) (or_intror (or_intror (or_introl eq_refl))))) as SFL.
  pose proof (proj1 (LAYFBX (1, ff) (mkABlock (mb_addr mbl) 32) (or_introl eq_refl) (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as SFLB.
  cbn [fst snd ab_addr ab_size] in SFB0, SFL, SFLB. rewrite ff_bytes_1 in SFB0, SFL, SFLB.
  clear LAYFBX.
  pose proof (SEPX _ _ (or_intror (or_introl eq_refl)) INH' ltac:(cbn; intros E; exact (nd_mid_ne [mkABlock NS 128] _ _ _ NDX (or_intror (or_intror (or_introl eq_refl))) E))) as SB0H. cbn [ab_addr ab_size] in SB0H.
  pose proof (SEPX _ _ (or_intror (or_intror (or_introl eq_refl))) INH' ltac:(cbn; intros E; exact (nd_mid_ne [mkABlock NS 128; mkABlock B0 32] _ _ _ NDX (or_intror (or_introl eq_refl)) E))) as SLH. cbn [ab_addr ab_size] in SLH.
  pose proof (SEPX _ _ (or_intror (or_intror (or_intror (or_introl eq_refl)))) INH' ltac:(cbn; intros E; exact (nd_mid_ne [mkABlock NS 128; mkABlock B0 32; mkABlock Lx 48] _ _ _ NDX (or_introl eq_refl) E))) as SBH. cbn [ab_addr ab_size] in SBH.
  pose proof (BSMALL _ _ _ _ _ (mkABlock Lx 48) AHKX (or_intror (or_intror (or_introl eq_refl))) ltac:(cbn; unfold SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE; lia)) as LXSH.
  pose proof (BSMALL _ _ _ _ _ (mkABlock (mb_addr mbl) 32) AHKX (or_intror (or_intror (or_intror (or_introl eq_refl)))) ltac:(cbn; unfold SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE; lia)) as LBSH.
  cbn [ab_addr] in LXSH, LBSH. rewrite oshw_hi_0 in LXSH, LBSH.
  yhide SNH. yhide SNB0. yhide SNL. yhide SNLB. yhide SNF. yhide SNAL. yhide SFB0. yhide SFL. yhide SFLB. yhide SB0H. yhide SLH. yhide SBH.
  yhide SEPHF. yhide SEPHL. yhide FL_ff.
  (* [comment removed for export] *)
  arz_seg KIPY AHKX.
  pose proof (aypol_opol_block Y _ ((1, ff) :: LF) _ _ LINK (mkABlock H 104) INH' ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PH PHS].
  cbn [ab_addr ab_size] in PH, PHS. unfold oshw_lo, oshw_hi, A_SB, amem in PHS. change ((104 + 7) / 8) with 13 in PHS.
  pose proof (aypol_opol_block Y _ ((1, ff) :: LF) _ _ LINK (mkABlock NS 128) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PN PNS].
  cbn [ab_addr ab_size] in PN, PNS. unfold oshw_lo, oshw_hi, A_SB, amem in PNS. change ((128 + 7) / 8) with 16 in PNS.
  pose proof (aypol_fframe Y _ ((1, ff) :: LF) _ _ LINK (1, ff) ff (ff + 128) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; rewrite ff_bytes_1; lia) ltac:(lia) ltac:(cbn; rewrite ff_bytes_1; lia)) as PFF.
  pose proof (aypol_ffshadow Y _ ((1, ff) :: LF) _ _ LINK (1, ff) (ff / 8 + 2147450880) (ff / 8 + 2147450880 + 16) (or_introl eq_refl)
                ltac:(cbn [snd]; unfold oshw_lo, A_SB; lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia) ltac:(lia) ltac:(cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as PFFS.
  eapply evtA_cut.
  { eapply aal8_seg;
      [ exact MI1 | lia | lia | exact HC | exact HS | reflexivity | lia | lia | exact H16
      | exact NC | exact NSH | reflexivity | lia | lia | lia | clear -CEILB SNH; unfold yhide in *; lia
      | exact PH | exact PHS | exact PN | exact PNS ]. }
  cbv beta. intros ms2 (a0x & a1x & a2x & a3x & m2 & -> & MU2 & WM2 & MI2 & HC2 & NSD2 & HS2 & NSH2).
  eapply (rw_cells_transport bsegs) in FR1; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport bsegs) in SHC; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport bsegs) in FF8; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SEPHF SNF; unfold yhide in *; lia].
  eapply (rw_cells_transport bsegs) in FFP; [| exact MU2| exact WM2| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SEPHF SNF; unfold yhide in *; lia].
  unfold AAL_EPI.
  eapply evtA_cut.
  { eapply aal9a_seg; [ exact MI2 | exact SHC | exact FF8 | exact FFP | exact FFsh | lia | exact FFal | lia | exact PFF | exact PFFS ]. }
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & SH3 & FFM3 & FFP3).
  apply evtA_done. intros mo3 Hag3 HLI3 Hh3. destruct (BACK mo3 Hag3 HLI3) as [AHKb R3].
  pose proof (munch_app _ _ _ _ _ MU2 MU3) as MU23. cbn [app] in MU23. pose proof (wmono_trans _ _ _ _ WM2 WM3) as WM23.
  assert (AHK3 : y_AHK Y s1' (mkABlock NS 128 :: LBX) ((1, ff) :: LF) m3 mo3).
  { eapply FRAMEY; [exact AHKb| exact MU23| exact WM23|].
    constructor; [right; left; exists (mkABlock H 104); split; [exact INH'| cbn; lia]|].
    constructor; [right; left; exists (mkABlock NS 128); split; [left; reflexivity| cbn; lia]|].
    constructor; [right; right; right; left; exists (1, ff); split; [left; reflexivity| cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia]|].
    constructor; [right; right; left; exists (1, ff); split; [left; reflexivity| cbn [fst snd]; rewrite ff_bytes_1; lia]| constructor]. }
  clear AHKb LINK BACK PH PHS PN PNS PFF PFFS.
  pose proof (aystatics_munch _ _ _ YSX MU23 WM23 ltac:(do 4 (constructor; [cbn [fst snd]; lia|]); constructor)) as YS3.
  assert (PRES3w : ay_pres REST LF (bv_unsigned sp) [] m m3).
  { eapply ay_pres_trans; [exact PRES1|]. eapply ay_pres_of_munch; [exact MU23| exact WM23|]. intros a Ha Hc _.
    apply outside_cons; [| apply outside_cons; [| apply outside_cons; [| apply outside_cons; [| exact I]]]].
    - eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock H 104));
        [exact AHKX| exact INH'| exact NDH| cbn; lia| cbn; lia| lia| aceil; lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)].
    - eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock NS 128));
        [exact AHKX| left; reflexivity| exact NDN| cbn; lia| cbn; lia| lia| aceil; lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHKX| left; reflexivity| exact FRESH| intros b0 Hb0; exact (proj1 (NDH _ Hb0))| right; cbn [fst snd]; unfold oshw_lo, A_SB; rewrite shl8_1; lia| lia| aceil; lia| exact Hc].
    - eapply (ay_client_outside_fframe Y BLKY BSHY LAYY _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHKX| left; reflexivity| exact FRESH| intros b0 Hb0; exact (proj1 (NDH _ Hb0))| left; cbn [fst snd]; rewrite ff_bytes_1; lia| lia| aceil; lia| exact Hc]. }
  (* [comment removed for export] *)
  eapply (rw_cells_transport bsegs) in SV1; [| exact MU23| exact WM23| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport bsegs) in FR1; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU23| exact WM23| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint bsegs) in ST1; [| exact MU23| exact WM23| cbv [disjoint_from fst snd]; lia].
  eapply (rw_cells_transport bsegs) in CFC1; [| exact MU23| exact WM23| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SEPHL SNAL FLcx ECFG FL_ff FL_1 FL_2 E8F FFsh FFce; unfold yhide in *; lia].
  eapply (rw_cells_transport bsegs) in HC2; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; unfold hcells15; cbn [cells_size csize Nat.add length]; clear -CEILB SEPHF HR1 HR2 E8F FFsh FFce; unfold yhide in *; lia].
  eapply (u8arr_transport bsegs) in NSD2; [| exact MU3| exact WM3| cbv [disjoint_from fst snd]; rewrite upd_length, LNJ; clear -CEILB SNF NSSH E8F FFsh FFce; unfold yhide in *; lia].
  eapply (rw_cells_transport bsegs) in LXC; [| exact MU23| exact WM23| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length lexer_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB SNL SLH SFL LXSH E8F FFsh FFce; unfold yhide in *; lia].
  eapply (rw_cells_transport bsegs) in LBC; [| exact MU23| exact WM23| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length buf_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB SNLB SBH SFLB LBSH E8F FFsh FFce; unfold yhide in *; lia].
  eapply (rw_cells_transport bsegs) in B0C; [| exact MU23| exact WM23| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length buf_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB SNB0 SB0H SFB0 B0SH E8F FFsh FFce; unfold yhide in *; lia].
  clear SHC FF8 HC HS NSH YAF ASH OSC1 OSX1.
  (* [comment removed for export] *)
  destruct (AFLC _ _ _ _ _ (1, ff) AHK3 (or_introl eq_refl)) as [[fl FLG] _]. cbn [fst snd] in FLG.
  pose proof (AFLSEP _ _ _ _ _ (1, ff) (1, AL) AHK3 (or_introl eq_refl) (or_intror FLin) ltac:(cbn [snd]; intros E; exact (proj2 (FRESH _ FLin) (eq_sym E)))) as PFfl.
  cbn [fst snd] in PFfl. rewrite ff_bytes_1 in PFfl.
  destruct (LAYY _ _ _ _ _ AHK3) as (_ & LAYFB3 & _).
  pose proof (proj2 (LAYFB3 (1, ff) (mkABlock H 104) (or_introl eq_refl) INH')) as PFH.
  pose proof (proj2 (LAYFB3 (1, ff) (mkABlock NS 128) (or_introl eq_refl) (or_introl eq_refl))) as PFN.
  pose proof (proj2 (LAYFB3 (1, ff) (mkABlock B0 32) (or_introl eq_refl) (or_intror (or_introl eq_refl)))) as PFB0.
  pose proof (proj2 (LAYFB3 (1, ff) (mkABlock Lx 48) (or_introl eq_refl) (or_intror (or_intror (or_introl eq_refl))))) as PFL.
  pose proof (proj2 (LAYFB3 (1, ff) (mkABlock (mb_addr mbl) 32) (or_introl eq_refl) (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as PFLB.
  cbn [fst snd ab_addr ab_size] in PFH, PFN, PFB0, PFL, PFLB. clear LAYFB3.
  yhide PFfl. yhide PFH. yhide PFN. yhide PFB0. yhide PFL. yhide PFLB.
  (* [comment removed for export] *)
  arz_seg KIPY AHK3.
  assert (PPF : acc_ok (m_vm_lazy mo3) (y_aS Y s1') (Z_to_bv 64 (y_aflag Y 1 ff), 1%nat)).
  { apply LINK. unfold ay_acc. cbn [fst snd]. rewrite unsigned_lit by lia. do 6 right. left. exists (1, ff). split; [left; reflexivity|]. cbn [fst snd]. split; [reflexivity| reflexivity]. }
  pose proof (aypol_stack Y _ ((1, ff) :: LF) _ _ LINK (bv_unsigned sp - 160) (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  eapply evtA_cut.
  { eapply aal9b_seg; [ exact MI3 | exact FLG | exact SV1 | exact (proj1 PFR) | exact (proj2 PFR) | lia | lia | exact PPF | exact PSTK ]. }
  cbv beta. intros ms4 (m4 & -> & MU4 & WM4 & MI4 & FL4 & SV4).
  apply evtA_done. intros mo4 Hag4 HLI4 Hh4. destruct (BACK mo4 Hag4 HLI4) as [AHKc R4].
  pose proof (FREL _ _ _ _ _ _ 1 ff AHKc (or_introl eq_refl) MU4 WM4 FL4) as AHK4.
  cbn [ff_remove fst snd] in AHK4. rewrite !Z.eqb_refl in AHK4. cbn [andb] in AHK4.
  clear AHKc LINK BACK PPF PSTK.
  pose proof (aystatics_munch _ _ _ YS3 MU4 WM4 ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS4.
  assert (PRES4w : ay_pres REST LF (bv_unsigned sp) [] m m4).
  { eapply ay_pres_trans; [exact PRES3w|]. eapply ay_pres_of_munch; [exact MU4| exact WM4|]. intros a Ha Hc _.
    eapply (ay_client_outside_flag Y LAYY AFLSEP _ _ _ _ _ REST LF (bv_unsigned sp) (1, ff)); [exact AHK3| left; reflexivity| exact FRESH| intros b0 Hb0; exact (proj1 (NDH _ Hb0))| aceil; lia| exact Hc]. }
  eapply (rw_cells_transport bsegs) in FR1; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; lia].
  eapply (stk_transport_disjoint bsegs) in ST1; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; lia].
  eapply (rw_cells_transport bsegs) in CFC1; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB PFfl FLcx ECFG; unfold yhide in *; lia].
  eapply (rw_cells_transport bsegs) in HC2; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; unfold hcells15; cbn [cells_size csize Nat.add length]; clear -CEILB PFH; unfold yhide in *; lia].
  eapply (u8arr_transport bsegs) in NSD2; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; rewrite upd_length, LNJ; clear -CEILB PFN; unfold yhide in *; lia].
  eapply (rw_cells_transport bsegs) in LXC; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length lexer_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB PFL; unfold yhide in *; lia].
  eapply (rw_cells_transport bsegs) in LBC; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length buf_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB PFLB; unfold yhide in *; lia].
  eapply (rw_cells_transport bsegs) in B0C; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length buf_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB PFB0; unfold yhide in *; lia].
  (* [comment removed for export] *)
  pose proof (stk_release bsegs _ _ _ _ ST1 FR1 ltac:(lia)) as ST2. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ST2.
  pose proof (stk_merge bsegs _ _ _ _ ST2 GAP1 ltac:(lia)) as ST3'.
  pose proof (stk_release bsegs _ _ _ _ ST3' SV4 ltac:(lia)) as ST4. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in ST4.
  replace (bv_unsigned sp + -104 + 104) with (bv_unsigned sp) in ST4 by lia.
  (* [comment removed for export] *)
  pose proof (proj1 (BSHY _ _ _ _ _ (mkABlock H 104) AHK4 INH' ltac:(cbn; lia))) as OSH4.
  pose proof (proj1 (BSHY _ _ _ _ _ (mkABlock NS 128) AHK4 (or_introl eq_refl) ltac:(cbn; lia))) as OSN4.
  pose proof (proj1 (BSHY _ _ _ _ _ (mkABlock B0 32) AHK4 (or_intror (or_introl eq_refl)) ltac:(cbn; lia))) as OSB4.
  pose proof (proj1 (BSHY _ _ _ _ _ (mkABlock Lx 48) AHK4 (or_intror (or_intror (or_introl eq_refl))) ltac:(cbn; lia))) as OSL4.
  pose proof (proj1 (BSHY _ _ _ _ _ (mkABlock (mb_addr mbl) 32) AHK4 (or_intror (or_intror (or_intror (or_introl eq_refl)))) ltac:(cbn; lia))) as OSLB4.
  cbn [ab_addr ab_size] in OSH4, OSN4, OSB4, OSL4, OSLB4.
  (* [comment removed for export] *)
  rewrite (upd_firstn_skipn nj 0 (Z_to_bv 8 0)) in NSD2 by lia. cbn [firstn app] in NSD2.
  pose proof (CB2_of_u8arr bsegs m4 NS [Z_to_bv 8 0] (skipn 1 nj) 1 127 NSD2 eq_refl ltac:(rewrite length_skipn; lia)) as BSC.
  eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m4 mo4 s1'
            (yalloc_hand 0%nat lblk 0%nat 0%nat bb) (mkMH (0%N, 0, 0) H (0%N, 0, 0) Lx mbl (mkMB (0%N, 0, 0) B0 (0%N, 0, 0) 0) (0%N, 0, 0) NS CX)).
  unfold ayalloc_rpost. cbn [mh_addr mh_ctx mh_lexer mh_lexbuf mh_decbuf mh_stack mb_addr].
  split; [exact SO1|].
  split; [eapply RRT; [exact R1|]; eapply RRT; [exact R3| exact R4]|].
  split; [pose proof (CRB 0%nat lblk 0%nat 0%nat) as CRBX; clear -CEILB CRBX CRED1; unfold yhide in *; lia|].
  split; [split; [exact MI4|]; split; [exact ST4|]; split; [exact FRM1|]; split; [exact I| exact PRES4w]|].
  split; [unfold wz; exact CFC1|].
  split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
  split; [unfold yalloc_hand; apply (yalloc_leaf_ok 1 1); exact HLX|].
  split.
  { (* [comment removed for export] *)
    split; [| split; [| split]].
    - split.
      + exists pew, pad. split; [| exact I].
        unfold hand_cells, hand_head_cells, alloc_cells, yalloc_hand. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc mh_ctx mh_lexer mh_decbuf mh_stack mh_addr mb_addr h_bytesConsumed h_stack_size h_parseError app].
        replace (h_used _) with 1 by reflexivity. unfold wz. unfold hcells15 in HC2. exact HC2.
      + unfold yalloc_hand. cbn [h_bytesConsumed h_stack_size h_stack_blk mh_stack]. replace (h_used _) with 1 by reflexivity.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [intros X; discriminate| intros X; exfalso; clear -CEILB X NSR; unfold yhide in *; lia].
    - split; [split; [exact LXC| cbn; lia]|]. split; [| split; [cbn; exact I| cbn; apply Forall_nil]].
      split; [rewrite MBD0; unfold buf_cells, ybuf_zero; cbn [buf_state_code yb_state yb_len yb_used]; unfold buf_cells, ybuf_zero in LBC; exact LBC| split; [cbn; rewrite MBD0; tauto| cbn; lia]].
    - split; [split; [cbn [mb_addr mb_data]; exact B0C| split; [cbn; tauto| cbn; lia]]| split; [cbn; exact I| cbn; apply Forall_nil]].
    - unfold bs_rep, yalloc_hand. cbn [h_stack_blk h_stack h_stack_size mh_stack]. split; [lia|].
      replace (h_used _) with 1 by reflexivity. change (Z.to_nat 1) with 1%nat. change (Z.to_nat (128 - 1)) with 127%nat.
      change (zbytes (stack_bytes [ST_start])) with [Z_to_bv 8 0]. exists (skipn 1 nj). exact BSC. }
  split; [exact OSH4|]. split; [exact OSL4|]. split; [exact OSLB4|]. split; [exact OSB4|].
  split; [intros _; unfold yalloc_hand; cbn [h_stack_size]; exact OSN4|].
  split.
  { intros b Hb. unfold yalloc_hand in Hb.
    cbn [yblocks lexer_blocks buf_blocks bs_blocks lx_buf yb_data yb_len ybuf_zero h_lexer h_decbuf h_stack_blk h_stack_size mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack mb_id mb_addr abl map blk_addr blk_size fst snd app] in Hb.
    rewrite oshw_hi_0. destruct Hb as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [ab_addr]; lia. }
  apply AYST_split. split; [| exact YS4].
  eapply PERMY; [exact AHK4| | apply Permutation_refl].
  unfold yalloc_hand. cbn [yblocks lexer_blocks buf_blocks bs_blocks lx_buf yb_data yb_len ybuf_zero h_lexer h_decbuf h_stack_blk h_stack_size mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack mb_id mb_addr abl map blk_addr blk_size fst snd app].
  unfold LBX, SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF. apply perm_yalloc.
Qed.

End Tail.
End W.
End RC__1.
