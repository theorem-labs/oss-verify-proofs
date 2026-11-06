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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BI_globals2 BI_region_is_poisoned BI_asan_memcpy1 BI_asan_memcpy BI_asan_memset BYajlRep BYajl_iface BY_rz BY_hand BY_set_default BY_alloc1 BY_alloc2 BY_alloc3 BY_alloc4 BY_alloc5 BY_alloc6 BY_client BY_allocj4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
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
Lemma j_bufalloc : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9v : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (H Lx B0 : Z) (mbl : mbuf) (bb : nat) (lblk : yptr) (RR1 : Z)
    (k0 k32 : list byte) (pew pad DB SBw SZ U YFw w0 : word) (shf : list byte),
  let lx := mkLexer 0 0 LE_ok ybuf_zero bb 0 0 1 1 in
  let LB8 := mkABlock Lx 48 :: mkABlock (mb_addr mbl) 32 :: mkABlock H 104 :: REST in
  a0 = Z_to_bv 64 B0 -> 0 < B0 -> oshw_hi 0 (2^47) <= B0 -> buf_struct bsegs m1 B0 ybuf_zero 0 (H + 72) -> oshadow m1 B0 SIZEOF_BUF ->
  AYST Y s1' (mkABlock B0 SIZEOF_BUF :: LB8) ((1, ff) :: LF) m1 mo1 ->
  mem_inv bsegs m1 -> stk bsegs m1 lo SQ -> stk bsegs m1 (SQ + 56) (bv_unsigned sp + -104) -> frm0 fc1 ->
  rw_cells bsegs m1 SQ [CB 8 k0; C8 (Z_to_bv 64 (ff + 48)); C8 (Z_to_bv 64 AY_CALLBACKS); C8 (Z_to_bv 64 CX); CB 16 k32; C8 (Z_to_bv 64 ff)] ->
  rw_cells bsegs m1 (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m1 ff [C8 w0] ->
  rw_cells bsegs m1 (ff + 120) [C8 (Z_to_bv 64 (y_aflag Y 1 ff))] -> rw_cells bsegs m1 (ff / 8 + 2147450880) [CB 16 shf] ->
  bytes_at bsegs m1 (ff / 8 + 2147450880) afs_win ->
  rw_cells bsegs m1 (ff + 32) [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  u8arr bsegs m1 (2147450880 + (ff + 32) / 8) (blk_shadow 32) ->
  rw_cells bsegs m1 CFGP [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1)] -> oshadow m1 CFGP 8 -> oshadow m1 CX 8 ->
  rw_cells bsegs m1 H [C8 (Z_to_bv 64 AY_CALLBACKS); C8 (Z_to_bv 64 CX); C8 (Z_to_bv 64 Lx); C8 pew; C4 (Z_to_bv 64 0); C4 pad; C8 DB; C8 SBw; C4 SZ; C4 U; C8 YFw] ->
  rw_cells bsegs m1 (H + 72) [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  u8arr bsegs m1 (2147450880 + H / 8) (blk_shadow 104) ->
  17594333495296 <= H -> H + 104 <= alloc_ceiling -> H mod 16 = 0 -> (H + 104 <= ff \/ ff + 128 <= H) -> (AL + 128 <= H \/ H + 104 <= AL) ->
  rw_cells bsegs m1 Lx (lexer_cells lx (mb_addr mbl) (H + 72)) -> rw_cells bsegs m1 (mb_addr mbl) (buf_cells ybuf_zero 0 (H + 72)) -> mb_data mbl = 0 ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s ->
  y_phi_buf Y ybuf_zero + RR1 <= y_acredit Y s1' ->
  y_acharge Y 128 + RR <= RR1 + y_phi_buf Y ybuf_zero ->
  (forall hb lb db sb, y_acharge Y 128 + y_phi_hand Y (yalloc_hand hb lb db sb bb) L + RR <= RR1 + y_phi_buf Y ybuf_zero) ->
  yleaf (ylex_alloc 1 1) (Some (lblk, lx)) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR (Z_to_bv 64 AAL_RET5) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 CFGP) (Z_to_bv 64 (H + 72)) s9v (Z_to_bv 64 (ff + 56)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
                          F1 (Z_to_bv 64 AAL_RET5) fc1 None m1 (seg_rom bsegs)) mo1) K.
Proof. aceil.
  intros until shf. intros lx LB8 EA0 B0P B0SH BST B0S AYX MI1 ST1 GAP1 FRM1 FR1 SV1 FF8 FFP SHC AW YAF ASH CFC1 OSC1 OSX1 HH HA HS HR1 HR2 H16 SEPHF SEPHL LXC LBC MBD0 PRES1 R1 SO1 CRED1 CRA CRB HLX.
  unfold amem in FFsh, PFR, FL_1.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (E8F : ff = 8 * (ff / 8)) by (clear -CEILB FFal; Z.div_mod_to_equations; lia).
  assert (H8 : H mod 8 = 0) by (clear -CEILB H16; Z.div_mod_to_equations; lia).
  destruct NONNEG as (NA0 & NB0 & NH0 & NN0). pose proof (NB0 ybuf_zero) as NBZ.
  pose proof (NA0 128) as NA128.
  assert (INH : In (mkABlock H 104) LB8) by (right; right; left; reflexivity).
  (* [comment removed for export] *)
  lazymatch type of HH with rw_cells _ _ _ ?cs1 => lazymatch type of HA with rw_cells _ _ _ ?cs2 =>
    assert (HC : rw_cells bsegs m1 H (cs1 ++ cs2)) by (apply (proj2 (ycells_app bsegs _ _ cs1 cs2)); split; [exact HH| cbn [cells_size csize Nat.add]; exact HA]) end end.
  cbn [app] in HC. clear HH.
  (* [comment removed for export] *)
  subst a0. unfold SIZEOF_BUF in B0S, AYX. destruct BST as (RC & _ & _ & _). rewrite oshw_hi_0 in B0SH.
  apply AYST_split in AYX. destruct AYX as [AHKX YSX].
  destruct (BLKY _ _ _ _ _ AHKX) as (RNGX & SEPX & NDX).
  pose proof (RNGX _ (or_introl eq_refl)) as B0R. unfold ablock_range in B0R; aceil. cbn [ab_addr ab_size] in B0R.
  pose proof (SEPX _ _ (or_introl eq_refl) (or_intror INH) (nd_head_ne _ _ _ NDX INH)) as SB0H. cbn [ab_addr ab_size] in SB0H.
  assert (NDH : forall b, In b REST -> In b (mkABlock B0 32 :: LB8) /\ ab_addr b <> ab_addr (mkABlock H 104)).
  { intros b Hb. split; [right; right; right; right; exact Hb|]. cbn [ab_addr]. intros E.
    exact (nd_mid_ne [mkABlock Lx 48; mkABlock (mb_addr mbl) 32] (mkABlock H 104) REST b (nd_tail _ _ NDX) Hb (eq_sym E)). }
  pose proof (RNGX _ (or_intror (or_introl eq_refl))) as RLX. pose proof (RNGX _ (or_intror (or_intror (or_introl eq_refl)))) as RLB. cbn [ab_addr ab_size] in RLX, RLB.
  unfold ablock_range, ACONSTS in RLX, RLB; aceil. cbn [c_img_hi] in RLX, RLB.
  pose proof (SEPX _ _ (or_intror (or_introl eq_refl)) (or_intror INH) ltac:(cbn; intros E; exact (nd_mid_ne [] _ _ _ (nd_tail _ _ NDX) (or_intror (or_introl eq_refl)) E))) as SLH'. cbn [ab_addr ab_size] in SLH'.
  pose proof (SEPX _ _ (or_intror (or_intror (or_introl eq_refl))) (or_intror INH) ltac:(cbn; intros E; exact (nd_mid_ne [mkABlock Lx 48] _ _ _ (nd_tail _ _ NDX) (or_introl eq_refl) E))) as SBH'. cbn [ab_addr ab_size] in SBH'.
  (* [comment removed for export] *)
  destruct (ICPB _ _ _ _ _ (mkABlock H 104) (H + 48) 16 AHKX (or_intror INH) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as (wsS & [SWB SWL] & RCW & _ & _).
  pose proof (ICPR _ _ _ _ _ (mkABlock H 104) (H + 48) 16 AHKX (or_intror INH) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as PGS.
  pose proof (ICPG _ _ _ _ _ AHKX) as IG1. unfold A_SB in SWB, SWL, RCW, PGS, IG1.
  pose proof (shw_geom 2147450880 (H + 48) 16 ltac:(lia) ltac:(lia) ltac:(lia)) as GEOS. cbv zeta in GEOS.
  assert (WSH : shw_hi 2147450880 (H + 48) 16 <= 17594333495296) by (clear -CEILB GEOS HR2; lia).
  arz_seg KIPY AHKX.
  pose proof (aypol_stack Y _ ((1, ff) :: LF) _ _ LINK lo (SQ + 56) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ ((1, ff) :: LF) _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  pose proof (aypol_opol_block Y _ ((1, ff) :: LF) _ _ LINK (mkABlock H 104) (or_intror INH) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PH PHS].
  cbn [ab_addr ab_size] in PH, PHS. unfold oshw_lo, oshw_hi, A_SB, amem in PHS. change ((104 + 7) / 8) with 13 in PHS.
  pose proof (aypol_pages (m_vm_lazy mo1) _ _ _ PGS ltac:(unfold shw_lo, al8 in *; clear -CEILB GEOS HR1; Z.div_mod_to_equations; lia) ltac:(lia)) as PWS.
  eapply evtA_cut.
  { eapply aal7_seg;
      [ exact ST1 | exact MI1 | lia | lia | lia | exact HC | exact HS | reflexivity | lia | lia | exact H16 | lia | lia
      | split; [exact SWB| exact SWL] | exact RCW | exact WSH | exact IG1
      | exact PSTK | eapply pol_sub; [exact PIMG| lia| lia] | exact PH | exact PHS | exact PWS ]. }
  cbv beta. intros ms4 (t0h & t1h & t2h & a4h & a5h & a6h & a7h & t3h & t4h & t5h & t6h & m4 & -> & MU4 & WM4 & MI4 & ST4 & HC4 & HS4 & IG4).
  apply evtA_done. intros mo4 Hag4 HLI4 Hh4. destruct (BACK mo4 Hag4 HLI4) as [AHKb R4].
  assert (AHK4 : y_AHK Y s1' (mkABlock B0 32 :: LB8) ((1, ff) :: LF) m4 mo4).
  { eapply FRAMEY; [exact AHKb| exact MU4| exact WM4|].
    constructor; [left; cbn [fst snd]; aceil; lia|].
    constructor; [right; left; exists (mkABlock H 104); split; [right; exact INH| cbn; lia]| constructor]. }
  clear AHKb LINK BACK.
  pose proof (aystatics_munch _ _ _ YSX MU4 WM4 ltac:(do 2 (constructor; [cbn [fst snd]; lia|]); constructor)) as YS4.
  assert (PRES4w : ay_pres REST LF (bv_unsigned sp) [] m m4).
  { eapply ay_pres_trans; [exact PRES1|]. eapply ay_pres_of_munch; [exact MU4| exact WM4|]. intros a Ha Hc _.
    apply outside_cons; [| apply outside_cons; [| exact I]].
    - eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHKX| intros b0 Hb0; exact (proj1 (NDH _ Hb0))| aceil; lia| lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)].
    - eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock H 104));
        [exact AHKX| exact (or_intror INH)| exact NDH| cbn; lia| cbn; lia| lia| aceil; lia| exact (ay_client_addr_mono _ _ ((1, ff) :: LF) _ _ (fun f Hf => or_intror Hf) Hc)]. }
  (* [comment removed for export] *)
  eapply (rw_cells_transport bsegs) in SV1; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (stk_transport_disjoint bsegs) in GAP1; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; lia].
  eapply (rw_cells_transport bsegs) in FR1; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport bsegs) in FF8; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport bsegs) in FFP; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport bsegs) in SHC; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport bsegs) in YAF; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (u8arr_transport bsegs) in ASH; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; clear -CEILB HR1 E8F FFce FFsh CEIL LO SQR; Z.div_mod_to_equations; lia].
  eapply (rw_cells_transport bsegs) in CFC1; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SEPHL FLcx ECFG FL_1 FL_2 CEIL LO SQR; lia].
  assert (OSC4 : oshadow m4 CFGP 8).
  { eapply oshadow_munch; [exact OSC1| exact MU4| exact WM4|]. unfold oshw_lo, A_SB. replace (CFGP / 8) with (AL / 8 + 8) by (clear -CEILB ECFG FLcx FL_1; Z.div_mod_to_equations; lia). change ((8 + 7) / 8) with 1.
    cbv [disjoint_from fst snd]. clear -CEILB HR1 FL_1 FL_2 CEIL LO SQR. Z.div_mod_to_equations. lia. }
  assert (OSX4 : oshadow m4 CX 8).
  { eapply oshadow_munch; [exact OSX1| exact MU4| exact WM4|]. unfold oshw_lo, A_SB. replace (CX / 8) with (AL / 8 + 4) by (clear -CEILB FLcx FL_1; Z.div_mod_to_equations; lia). change ((8 + 7) / 8) with 1.
    cbv [disjoint_from fst snd]. clear -CEILB HR1 FL_1 FL_2 CEIL LO SQR. Z.div_mod_to_equations. lia. }
  clear OSC1 OSX1.
  eapply (rw_cells_transport bsegs) in LXC; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length lexer_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB SLH' RLX CEIL LO SQR; lia].
  eapply (rw_cells_transport bsegs) in LBC; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length buf_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB SBH' RLB CEIL LO SQR; lia].
  eapply (rw_cells_transport bsegs) in RC; [| exact MU4| exact WM4| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length buf_cells Z.of_nat Pos.of_succ_nat Pos.succ]; clear -CEILB SB0H B0R CEIL LO SQR; lia].
  assert (AGREE4 : forall a, bv_unsigned sp <= a < 2^47 -> m4 (wa a) = m (wa a)).
  { intros a Ha. destruct (PRES4w a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  pose proof (sub_chunk m4 _ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] [] ltac:(rewrite app_nil_r; exact SV1)) as SV16.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV16. replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV16 by lia.
  unfold AAL_RET7.
  (* [comment removed for export] *)
  eapply (WREA0 128 (mkABlock B0 32 :: LB8) ((1, ff) :: LF) lo (RR1 + y_phi_buf Y ybuf_zero - y_acharge Y 128));
    [ exact K0
    | apply AYST_split; split; [exact AHK4| exact YS4]
    | reflexivity | reflexivity
    | lia
    | clear -CEILB CRED1; lia
    | clear -CEILB CRA NBZ RR0 NA128; lia
    | unfold LB8; change (nbig (mkABlock B0 32 :: mkABlock Lx 48 :: mkABlock (mb_addr mbl) 32 :: mkABlock H 104 :: REST)) with (nbig REST); unfold AY_NBIG_REST in NBIG; lia
    | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil; rewrite unsigned_lit by lia;
      split; [exact ST4|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [clear -CEILB SQ32; Z.div_mod_to_equations; lia|];
      split; [exact MI4|]; split; [exact TP| exact FRM1]
    | rewrite unsigned_lit by lia; eapply USTEP; [rewrite unsigned_lit by lia; exact URA_rea| lia| exact SV16| eapply UFRAME; [exact AGREE4| exact UA]]
    | ].
  cbv beta. intros t0i t1i t2i a0i a1i a2i a3i a4i a5i a6i a7i t3i t4i t5i t6i F5 fc5 m5 mo5 sa5 NS (MI5 & ST5 & FRM5 & _ & PRES5) SO5 R5 CRED5 RESS.
  destruct RESS as (EA5 & NSR & AM5 & NSSH & OSN & NCJ & AY5). specialize (NSSH ltac:(lia)).
  rewrite unsigned_lit in ST5, PRES5 by lia.
  replace (ret_pc (Z_to_bv 64 0x8269c)) with (Z_to_bv 64 0x8269c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES5 FR1 ltac:(lia)) as FR5.
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES5 SV1 ltac:(lia)) as SV5.
  assert (GAP5 : stk bsegs m5 (SQ + 56) (bv_unsigned sp + -104)).
  { eapply stk_agree; [eapply ay_pres_agree; exact PRES5| exact GAP1| intros a Ha; split; [left; lia| intros F0; exact F0]]. }
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES5 FF8 (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FF8_5.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES5 FFP (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as FFP5.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES5 SHC (or_introl eq_refl) ltac:(right; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; unfold oshw_lo, A_SB; rewrite shl8_1; lia)) as SHC5.
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, ff) PRES5 YAF (or_introl eq_refl) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as YAF5.
  assert (ASH5 : u8arr bsegs m5 (2147450880 + (ff + 32) / 8) (blk_shadow 32)).
  { eapply u8arr_agree; [eapply ay_pres_agree; exact PRES5| exact ASH|]. intros a Ha. rewrite (blk_shadow_length 32) in Ha by lia. split; [| intros F0; exact F0].
    right; right; left. exists (1, ff). split; [left; reflexivity|]. right. cbn [fst snd]. unfold oshw_lo, A_SB. rewrite shl8_1. clear -CEILB Ha E8F. Z.div_mod_to_equations. lia. }
  pose proof (aypres_fframe _ _ _ _ _ _ _ (1, AL) PRES5 CFC1 (or_intror FLin) ltac:(left; cbn [fst snd cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ff_bytes_1; lia)) as CFC5.
  assert (OSC5 : oshadow m5 CFGP 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES5| exact OSC4|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [right; exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha ECFG FLcx FL_1. Z.div_mod_to_equations. lia. }
  assert (OSX5 : oshadow m5 CX 8).
  { eapply oshadow_agree; [eapply ay_pres_agree; exact PRES5| exact OSX4|]. intros a Ha. split; [| intros F0; exact F0].
    right; right; left. exists (1, AL). split; [right; exact FLin|]. right. cbn [fst snd]. unfold oshw_lo, oshw_hi, A_SB, amem in Ha |- *. rewrite shl8_1. clear -CEILB Ha FLcx FL_1. Z.div_mod_to_equations. lia. }
  pose proof (aypres_block _ _ _ _ _ _ _ PRES5 HC4 ltac:(exists (mkABlock H 104); split; [right; exact INH| unfold hcells15; cbn; lia])) as HC5.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES5 LXC ltac:(exists (mkABlock Lx 48); split; [right; left; reflexivity| cbn [ab_addr ab_size cells_size csize Nat.add length lexer_cells Z.of_nat Pos.of_succ_nat Pos.succ]; lia])) as LXC5.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES5 LBC ltac:(exists (mkABlock (mb_addr mbl) 32); split; [right; right; left; reflexivity| cbn [ab_addr ab_size cells_size csize Nat.add length buf_cells Z.of_nat Pos.of_succ_nat Pos.succ]; lia])) as LBC5.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES5 RC ltac:(exists (mkABlock B0 32); split; [left; reflexivity| cbn [ab_addr ab_size cells_size csize Nat.add length buf_cells Z.of_nat Pos.of_succ_nat Pos.succ]; lia])) as RC5.
  assert (PRES5w : ay_pres REST LF (bv_unsigned sp) [] m m5).
  { eapply ay_pres_trans; [exact PRES4w|]. eapply (ay_pres_weaken Y); [exact PRES5| lia| intros b0 Hb0; right; right; right; right; exact Hb0| intros f Hf; right; exact Hf| auto]. }
  assert (HS5 : u8arr bsegs m5 (2147450880 + H / 8) (blk_shadow 104)).
  { pose proof AY5 as AYx. apply AYST_split in AYx. destruct AYx as [AHKx _].
    pose proof (proj1 (BSHY _ _ _ _ _ _ AHKx (or_intror (or_intror INH)) ltac:(cbn; lia))) as (_ & _ & X). cbn [ab_addr] in X. unfold A_SB in X. exact X. }
  eapply j_realloc with (H := H) (Lx := Lx) (B0 := B0) (NS := NS) (mbl := mbl) (bb := bb) (lblk := lblk) (RR4 := RR1 + y_phi_buf Y ybuf_zero - y_acharge Y 128).
  all: try eassumption.
  all: try (rewrite ?SO5; exact SO1).
  all: try rchain.
  all: try (clear -CEILB CRA NBZ RR0 NA128; lia).
  all: try (clear -CEILB B0SH; lia).
  all: try (intros hb lb db sb; pose proof (CRB hb lb db sb) as CRBX; clear -CEILB CRBX NBZ RR0 NA128; lia).
Qed.

End Tail.
End W.
End RC__1.
