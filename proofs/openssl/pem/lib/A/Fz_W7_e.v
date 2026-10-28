(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr Mem MState.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Fz_W3_j0lem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_libiface_pem D_agree D_clx PLayout I_lkit I_ut Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_writec Fz_W1_pploc Fz_W1_misc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux3  Fz_G_kit Fz_W7_defs Fz_W7_segs Fz_W7_inv Fz_W7_calls Fz_W7_x Fz_W7_f Fz_W7_p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Lemma junk_C8 : forall (m : mem) A pre post bs, rw_cells asegs m A (pre ++ CB 8 bs :: post) -> rw_cells asegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs H. pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [_ [L _]]. cbn in L.
  apply (Fz_kit.rw_cells_recast m A _ _ H).
  - pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]]. apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (Fz_W3_j0lem.le8_of_junk bs L). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w7_j_walk : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem), mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_fuzz_one_body) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 e_fuzz) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI. unfold e_fuzz, e_fuzz_one_body.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fr1 (usp pd f : Z) (j1 j2 j3 j4 j5 j6 : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) (m : mem) : Prop :=
  let '(c1, c2, c3, c4, c5, c6) := w7_mframe1 pd f j1 j2 j3 j4 j5 j6 in rw_cells asegs m (usp + -160) (w7_mframe c1 c2 c3 c4 c5 c6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).
Definition fr2 (usp pd f : Z) (j1 j2 j3 j4 j5 j6 : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) (m : mem) : Prop :=
  let '(c1, c2, c3, c4, c5, c6) := w7_mframe2 pd f j1 j2 j3 j4 j5 j6 in rw_cells asegs m (usp + -160) (w7_mframe c1 c2 c3 c4 c5 c6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).

Lemma fr1_keep : forall usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra (m m' : mem) KEEP fr W,
  (pd = 0 \/ pd = 16) -> usp + 16 <= USTACK_TOP -> fr1 usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra m ->
  rt_pres_fp KEEP fr (usp + -160 - pd) W m m' -> (forall x, usp + -160 - pd <= x < USTACK_TOP -> outside W x) ->
  fr1 usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra m'.
Proof.
  intros until W. intros PD TOP FR PR HO. unfold fr1, w7_mframe1, w7_mframe, w7_mframe7 in *.
  destruct PD as [E|E]; rewrite E in *; cbn [Z.eqb] in *;
    (eapply stack_keep; [exact FR| exact PR| clear; lia| cbn [cells_size csize Nat.add]; clear - TOP; unfold USTACK_TOP in *; lia|];
     intros x Hx; apply HO; cbn [cells_size csize Nat.add] in Hx; clear - Hx TOP; lia).
Qed.
Lemma fr2_keep : forall usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra (m m' : mem) KEEP fr W,
  (pd = 0 \/ pd = 16) -> usp + 16 <= USTACK_TOP -> fr2 usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra m ->
  rt_pres_fp KEEP fr (usp + -160 - pd) W m m' -> (forall x, usp + -160 - pd <= x < USTACK_TOP -> outside W x) ->
  fr2 usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra m'.
Proof.
  intros until W. intros PD TOP FR PR HO. unfold fr2, w7_mframe2, w7_mframe, w7_mframe7 in *.
  destruct PD as [E|E]; rewrite E in *; cbn [Z.eqb] in *;
    (eapply stack_keep; [exact FR| exact PR| clear; lia| cbn [cells_size csize Nat.add]; clear - TOP; unfold USTACK_TOP in *; lia|];
     intros x Hx; apply HO; cbn [cells_size csize Nat.add] in Hx; clear - Hx TOP; lia).
Qed.
(* [comment removed for export] *)
Lemma fr1_parts : forall usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra (m : mem),
  (pd = 0 \/ pd = 16) -> fr1 usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra m ->
  rw_cells asegs m (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ exists lowj, rw_cells asegs m (usp + -160) [CB 56 lowj].
Proof.
  intros until m. intros PD FR. unfold fr1, w7_mframe1, w7_mframe, w7_mframe7 in FR.
  destruct PD as [E|E]; rewrite E in FR; cbn [Z.eqb] in FR;
  lazymatch type of FR with rw_cells _ _ _ (?x0 :: ?x1 :: ?x2 :: ?x3 :: ?x4 :: ?x5 :: ?x6 :: ?tl) =>
      destruct (proj1 (rw_cells_app m _ [x0; x1; x2; x3; x4; x5; x6] tl) FR) as [LOW SAV]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SAV;
      replace (usp + -160 + 56) with (usp + -104) in SAV by lia; split; [exact SAV|];
      destruct (rw_cells_forget asegs m _ _ LOW) as [lowj LOW']; exists lowj; exact LOW' end.
Qed.

Section W7E.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_live_agree : forall m m' E top bot strs, errst_live E top bot strs m -> agree_on (errst_fp E strs) m m' -> errst_live E top bot strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Variable LIB : list (Z * Z) -> mem -> Prop.
Variable REST : mem -> Prop.
Variable REST_fp : Z -> Prop.
Hypothesis REST_agree : forall m m', REST m -> agree_on REST_fp m m' -> REST m'.
Hypothesis REST_fp_where : forall a, REST_fp a -> client_static a /\ outside LIB_W a /\ ~ cl_cell a.
(* [comment removed for export] *)
Hypothesis SM2 : stack_malloc_contract RT 2.
Hypothesis HCG_W7 : cg_sub W7_SITES_OWN W7_CALLS_ALL FZ_SITES FZ_CALLS.
Hypothesis C_BNEW : bio_new_mem_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis C_BW : bio_writeg_stmt RT FZ_SITES FZ_CALLS.
Hypothesis C_PEM : pem_read_bio_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis P7P : P7_stmt RT libenv errst_live FZ_SITES FZ_CALLS LIB REST.
Hypothesis EXITP : EXIT_stmt RT libenv errst_at_rest FZ_SITES FZ_CALLS LIB REST.
Hypothesis W7_OPEN : forall CL m (g : word) (v : word), LIB CL m -> ro_cells asegs m ssp_guard [C8 g] -> rw_cells asegs m (errno_cell (wz TP_A)) [C4 v] ->
    cl_env m (Z_to_bv 8 1) g /\ sec_off m /\ exists (E : Z) (LBL : list (Z * Z)),
    libenv m LBL E /\ errst_at_rest E [] m /\ In (E, 904) CL /\ incl_live LBL CL /\ ~ In (E, 904) LBL /\ REST m.

Local Notation w7a := (w7a RT).
Local Notation w7_com := (w7_com RT libenv FZ_SITES FZ_CALLS REST).
Local Notation P5 x := (x RT libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation P6 x := (x RT AF libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation P7 x := (x RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation PC x := (x RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS REST REST_fp REST_agree REST_fp_where) (only parsing).
Local Notation PCE x := (x RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live FZ_SITES FZ_CALLS REST REST_fp REST_agree REST_fp_where) (only parsing).

Theorem E7_proof : fuzz_one_cps RT LIB FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs CL DRV lo
         FDO MST ERA EA0 EA1 ETP D0 BLT PAY PAYIN PERM CLM FR0 LPOS LIVB CRED FPI CGH LIBM SSP [ev ERR] ART0 MI ST LOW LOS TOP AL16 SPTOP.
  unfold cps. intros T c HA Hk. subst ra a0 a1 tp. change (Z_to_bv 64 0xba3ef0) with (Z_to_bv 64 TP_A) in ERR, HA, Hk.
  destruct SSP as (g & _ & SSPG).
  destruct (W7_OPEN CL m g ev LIBM SSPG ERR) as (CLE & SEC & E & LBL & LE & ER0 & INE & INCL & NLE & RST).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *. set (pd := usp mod 32).
  assert (HP : pd = 0 \/ pd = 16) by (unfold pd; clear - AL16; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pd) by reflexivity. clearbody pd.
  assert (HLOS : 0x10007fff8000 <= lo) by (clear - SP0W LOW; unfold STACK_WIN in *; lia).
  assert (SPH : usp <= 2 ^ 47) by (clear - TOP; unfold USTACK_TOP in *; lia).
  assert (HLO : lo <= usp - 176) by (clear - LOS; unfold FUZZ_STACK in *; lia).
  assert (HLOI : SEGTOP_A <= lo) by (clear - HLOS; unfold SEGTOP_A; lia).
  set (usp1 := usp + -160 - pd).
  set (len := Z.of_nat (length bs)) in *. assert (LEN : 0 <= len < 2 ^ 26) by (subst len; clear - BLT; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1; clear - HP HLO HLOS SPH; lia).
  pose proof (Permutation_sym PERM) as PERM'.
  assert (CLV : forall e, In e CL -> In e (rt_live RT Σ)) by (intros e He; apply (Permutation_in _ PERM'); apply in_or_app; left; exact He).
  assert (DLV : forall e, In e DRV -> In e (rt_live RT Σ)) by (intros e He; apply (Permutation_in _ PERM'); apply in_or_app; right; exact He).
  (* [comment removed for export] *)
  assert (STLO : forall a, client_static a -> a < usp - 160) by (intros a Ha; pose proof (client_static_range a Ha); clear - H HLO HLOI; unfold SEGTOP_A in *; lia).
  assert (LVLO : forall p n a, In (p, n) (rt_live RT Σ) -> p <= a < p + n -> a < usp - 160).
  { intros p n a Hin Hp. pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (_ & X & _). clear - X Hp HLO LOW. lia. }
  (* [comment removed for export] *)
  pose proof (w7_j_walk (Z_to_bv 64 RA_FUZZ) sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m MI) as WJ.
  cl_lift WJ HA c0 Hc0. destruct (ASTA_unpack RT Σ _ _ c0 Hc0) as (ms0 & -> & Hc0'). clear Hc0 HA.
  (* [comment removed for export] *)
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  pose proof (w7_s0_walk (Z_to_bv 64 RA_FUZZ) sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pd
                HP HPM ST ltac:(fold usp; clear - HLO; lia) HLOS ltac:(fold usp; clear - SPH; lia) UT SHC UAR MI) as W0.
  cl_lift W0 Hc0' c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j1 & j2 & j3 & j4 & j5 & j6 & m1 & -> & MU1 & WM1 & MI1 & FR1 & GAP1 & ST1) & Hc1'). clear Hc1 Hc0'.
  fold usp in MU1, FR1, GAP1, ST1, Hc1'. fold usp1 in GAP1, ST1, Hc1'.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 160 [] ART0 ltac:(clear - LOW HLO; lia) ltac:(clear - TOP; lia) MU1 ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  (* [comment removed for export] *)
  apply (SM2 Σ PMc (Z_to_bv 64 SITE_w7_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 160) a1' a2' a3 a4 a5 a6 a7
           s2 (Z_to_bv 64 d) s4 (Z_to_bv 64 len) s6 (Z_to_bv 64 0x7fff8000) s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(right; right; reflexivity) eq_refl
           ltac:(rewrite FR0; unfold FRAMES_MAX; cbn; clear; lia) ltac:(clear - CRED; unfold FUZZ_COST in *; lia) ART1 MI1).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. unfold usp1. split; [clear - LOS HP; unfold RT_STACK, FUZZ_STACK in *; lia|]. split; [clear - TOP HP; unfold USTACK_TOP in *; lia|].
    clear - AL16 HP HPM. Z.div_mod_to_equations. lia. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CRE1 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_w7_smalloc) in Hc2' by (unfold SITE_w7_smalloc; clear; lia).
  rewrite FR0 in FRS1.
  assert (INF : In (f, 2%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 2%nat ART2 INF) as (_ & FLO & _ & PF). rewrite SP1 in FLO.
  pose proof (af_frames_align RT AF Σ1 m2 f 2%nat ART2 INF) as (_ & FIMG). pose proof (af_frames_hi RT AF Σ1 m2 f 2%nat ART2 INF) as FSH.
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 2%nat ART2 INF) as [SFL _].
  change (fs_size 2) with 256 in FLO, FSH, FU, WF2, WS2, PF, SFL. change (256 - 8) with 248 in WF2. change (256 / 8) with 32 in WS2.
  assert (FLO' : f + 256 <= lo) by (clear - FLO LOW; lia).
  assert (SHF : shad (f + 256) = shad f + 32) by (replace (f + 256) with (f + 64 * 4) by lia; rewrite (shad_add64 f 4 F64); lia).
  rewrite SHF in SFL. unfold shad, SHB in WS2, SFL.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 32 <= 0x10007fff8000).
  { pose proof (Z.div_pos f 8 ltac:(clear - F0; lia) ltac:(clear; lia)) as DP. assert (D44 : f / 8 + 32 <= 2^44) by (clear - FU F0; unfold USTACK_TOP in FU; Z.div_mod_to_equations; lia).
    clear - DP D44. lia. }
  assert (AG2 : forall a k, usp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2) by (intros a k H1 H2 x Hx; cbv beta in Hx; apply PRES2; left; lia).
  assert (FR2 : rw_cells asegs m2 (usp + -160) (w7_mframe (CB 8 j1) (CB 8 j2) (CB 8 j3) (CB 8 j4) (CB 8 j5) (CB 8 j6) s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (Z_to_bv 64 RA_FUZZ))).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply AG2; [unfold usp1; clear - HP; lia|]. unfold w7_mframe, w7_mframe7. cbn [cells_size csize Nat.add]. clear - TOP. lia. }
  assert (GAP2 : stk asegs m2 usp1 (usp + -160)) by (apply (stk_agree_nw asegs m1 m2 _ _ GAP1); intros x Hx; cbv beta in Hx; apply PRES2; left; clear - Hx TOP HP; unfold usp1, USTACK_TOP in *; lia).
  destruct (wr_at_rw_CB m2 f 248 WF2 ltac:(clear; lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (f / 8 + 2147450880) 32 WS2 ltac:(clear; lia)) as (sj & SB2).
  change (Z.to_nat 248) with 248%nat in FB2. change (Z.to_nat 32) with 32%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (w7_s1_walk sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2 s4 s6 s8 s9 s10 s11 u3 u4 u5 u6
                (Z_to_bv 64 RA_FUZZ) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m2 d len f lo pd j1 j2 j3 j4 j5 j6 fj sj
                HP F0 F64 ltac:(clear - FIMG; unfold SEGTOP_A in *; lia) FLO' ltac:(clear - FSH; lia) ltac:(fold usp; clear - HLO; lia) HLOS ltac:(fold usp; clear - SPH; lia)
                ltac:(clear - LEN; lia) UT2 FR2 GAP2 ST2 FB2 SB2 MI2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (j24 & j40 & j72 & j104 & jol & j136 & sjr & m3 & X) & Hc3'). clear Hc3 Hc2'.
  assert (X' : ms3 = MS (mkR (Z_to_bv 64 SITE_w7_smalloc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp (Z_to_bv 64 usp1)
                            (Z_to_bv 64 (len + -2147483648)) (Z_to_bv 64 (-2147483646)) (Z_to_bv 64 e_fuzz_one_body) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-15)) b5 b6 b7
                            (Z_to_bv 64 f) (Z_to_bv 64 d) s4 (Z_to_bv 64 len) (Z_to_bv 64 (-8)) (Z_to_bv 64 0x7fff8000) s8 s9
                            (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) u3 u4 u5 u6)
                       F2 (Z_to_bv 64 J_w7_lentest) fc2 None m3 (seg_rom asegs)
            /\ munch [(usp - 128, usp - 104); (f, f + 104); (f / 8 + 2147450880, f / 8 + 2147450880 + 20)] m2 m3 /\ wmono asegs m2 m3 /\ mem_inv asegs m3
            /\ fr1 usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (Z_to_bv 64 RA_FUZZ) m3
            /\ stk asegs m3 usp1 (usp + -160) /\ stk asegs m3 lo usp1
            /\ rw_cells asegs m3 f (w7_fframe j24 j40 j72 j104 j136 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (CB 8 jol))
            /\ rw_cells asegs m3 (f / 8 + 2147450880) (w7_shadow_live ++ [CB 12 sjr])).
  { unfold fr1. unfold usp1 in X |- *. destruct HP as [EP|EP]; rewrite EP in X |- *; cbn [w7_mframe1 Z.eqb] in X |- *; exact X. }
  clear X. destruct X' as (-> & MU3 & WM3 & MI3 & FR3 & GAP3 & ST3 & FF3 & SB3).
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 usp1 ART2 ltac:(rewrite SP1; unfold usp1; clear - LOW HLO HP; lia)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside]. split; [| split; [| split; [| exact I]]]; intros Hin; apply Ha.
    - apply acl_stack. unfold usp1, USTACK_TOP in *. clear - Hin HP TOP. lia.
    - apply (acl_frame _ _ _ f 2%nat); [exact INF| change (fs_size 2) with 256; clear - Hin; lia].
    - apply (acl_fshadow _ _ _ f 2%nat); [exact INF| rewrite SHF; unfold shad, SHB; clear - Hin; lia]. }
  (* [comment removed for export] *)
  assert (G3 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned x) -> bv_unsigned x < usp - 160 \/ usp <= bv_unsigned x -> m3 x = m x).
  { intros x Hx Hlt.
    destruct (newframe_apart RT AF Σ Σ1 m2 f 2%nat usp _ ART2 ltac:(rewrite FRS1, FR0; reflexivity) LV1 SP1 ltac:(clear - LOW HLO; lia) Hx) as (N1 & N2).
    change (fs_size 2) with 256 in N1, N2. rewrite SHF in N2. unfold shad, SHB in N2.
    rewrite (MU3 x ltac:(cbn [outside]; clear - N1 N2 Hlt; lia)).
    rewrite (PRES2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ Hx); [auto| rewrite FR0; intros e0 []| unfold usp1; clear - HP; lia])).
    apply MU1. cbn [outside]. clear - Hlt. lia. }
  assert (GS : forall x : word, client_static (bv_unsigned x) -> m3 x = m x) by (intros x Hx; apply G3; [apply acl_static; exact Hx| left; exact (STLO _ Hx)]).
  assert (GL : forall p n (x : word), In (p, n) (rt_live RT Σ) -> p <= bv_unsigned x < p + n -> m3 x = m x).
  { intros p n x Hin Hp. apply G3; [exact (acl_live _ _ _ p n _ Hin Hp)| left; exact (LVLO p n _ Hin Hp)]. }
  (* [comment removed for export] *)
  set (en := W7A RT Σ PMc (Z_to_bv 64 RA_FUZZ) sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo CL DRV d bs g E LBL pd f).
  destruct (fr1_parts usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (Z_to_bv 64 RA_FUZZ) m3 HP FR3) as (SAVED3 & lowj & LOW56).
  pose proof SB3 as SB3'. apply (proj1 (rw_cells_app m3 _ w7_shadow_live [CB 12 sjr])) in SB3'. destruct SB3' as [SHL3 SHJ3].
  change (w7_shadow_live) with (w7_shadow_live) in SHL3.
  pose proof FF3 as FF3'. unfold w7_fframe in FF3'.
  change ([C8 (Z_to_bv 64 W7_MAGIC); C8 (Z_to_bv 64 W7_DESCR); C8 (Z_to_bv 64 e_fuzz_one_body); CB 8 j24; C8 (Z_to_bv 64 0); CB 24 j40; C8 (Z_to_bv 64 0); CB 24 j72; C8 (Z_to_bv 64 0); CB 24 j104; CB 8 jol; CB 112 j136])
    with (w7_fhdr ++ [CB 8 j24] ++ [C8 (Z_to_bv 64 0)] ++ [CB 24 j40] ++ [C8 (Z_to_bv 64 0)] ++ [CB 24 j72] ++ [C8 (Z_to_bv 64 0)] ++ [CB 24 j104] ++ [CB 8 jol] ++ [CB 112 j136]) in FF3'.
  destruct (proj1 (rw_cells_app m3 _ _ _) FF3') as [FHD3 R1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ w7_fhdr] in R1.
  destruct (proj1 (rw_cells_app m3 _ _ _) R1) as [_ R2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R2. clear R1.
  destruct (proj1 (rw_cells_app m3 _ _ _) R2) as [CN3 R3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R3. clear R2.
  destruct (proj1 (rw_cells_app m3 _ _ _) R3) as [_ R4]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R4. clear R3.
  destruct (proj1 (rw_cells_app m3 _ _ _) R4) as [CH3 R5]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R5. clear R4.
  destruct (proj1 (rw_cells_app m3 _ _ _) R5) as [_ R6]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R6. clear R5.
  destruct (proj1 (rw_cells_app m3 _ _ _) R6) as [CD3 R7]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R7. clear R6.
  destruct (proj1 (rw_cells_app m3 _ _ _) R7) as [_ R8]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R8. clear R7.
  destruct (proj1 (rw_cells_app m3 _ _ _) R8) as [CL3 _]. clear R8.
  replace (f + 24 + 8) with (f + 32) in CN3 by lia. replace (f + 24 + 8 + 8 + 24) with (f + 64) in CH3 by lia.
  replace (f + 24 + 8 + 8 + 24 + 8 + 24) with (f + 96) in CD3 by lia. replace (f + 24 + 8 + 8 + 24 + 8 + 24 + 8 + 24) with (f + 128) in CL3 by lia.
  pose proof (junk_C8 m3 (f + 128) [] [] jol CL3) as CL3w. cbn [app] in CL3w. set (ol := le_bytes_to_word jol) in CL3w.
  (* [comment removed for export] *)
  assert (COM3 : w7_com en Σ1 m3 (FUZZ_COST - 1) []).
  { split; [exact ART3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact GAP3|]. split; [exact HP|]. split; [exact HPM|]. split; [exact TOP|].
    split; [rewrite SP1; exact LOW|]. split; [cbv beta iota delta [a_lo a_sp1 a_SP a_sp a_pd en]; fold usp; clear - LOS HP; unfold RT_STACK, W7_CALLEE_STACK, FUZZ_STACK in *; lia|].
    split; [exact HLOS|].
    split; [apply (cl_env_agree m m3 _ _ CLE); intros a Ha; exact (GS a (cl_cell_static _ Ha))|].
    split; [apply (sec_off_agree m m3 SEC); intros a Ea; apply GS; rewrite Ea; exact sec_init_static|].
    split. { eapply libenv_agree; [exact LE|]. intros a Ha. destruct (libenv_fp_where _ _ Ha) as [(_ & CS & _)|(p & n & Hin & Hp)]; [exact (GS a CS)| exact (GL p n a (CLV _ (INCL _ Hin)) Hp)]. }
    split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|].
    split; [apply (REST_agree m m3 RST); intros a Ha; exact (GS a (proj1 (REST_fp_where _ Ha)))|].
    split; [rewrite LV1; cbn [app]; exact PERM|]. split; [intros e []|]. split; [constructor|]. split; [rewrite LV1; intros [p0 n0] He; exact (LPOS p0 n0 He)|].
    split; [exact FRS1|]. split; [exact SP1|]. split; [exact CG1|].
    split; [cbv beta iota delta [a_CL a_DRV en]; rewrite length_app, Nat2Z.inj_add; clear - LIVB CLM; lia|]. split; [exact CLM|].
    split; [cbv beta iota delta [a_S0 en]; rewrite CRE1; clear; lia|]. split; [clear; unfold FUZZ_COST; lia|]. split; [exact CRED|].
    split; [rewrite CG1; exact CGH|]. split; [exact HCG_W7|]. split; [exact FPI|]. split; [reflexivity|]. split; [cbn; clear; unfold FUZZ_LIVE; lia|].
    split; [exact F0|]. split; [exact F64|]. split; [exact FU|].
    split; [exact SHL3|]. split; [exists sjr; exact SHJ3|]. split; [exact FHD3|]. split; [exact SAVED3|].
    split. { intros a Ha Ho. apply G3; [| destruct Ha as [H|[H|[H|[H|H]]]]].
             - eapply (aclient_mono _ _ _ _ _ _ _ Ha); [exact DLV| intros e0 []| cbv beta iota delta [a_SP a_sp en]; apply Z.le_refl].
             - right. exact (proj1 H).
             - left. exact (STLO _ H).
             - destruct H as (p & n & Hin & Hp). left. exact (LVLO p n _ (DLV _ Hin) Hp).
             - destruct H as (f' & k & [] & _).
             - destruct H as (f' & k & [] & _). }
    split. { eapply bytes_at_agree; [exact PAY|]. destruct PAYIN as [(p & n & Hin & P1 & P2)|[EBS _]]; [| intros x Hx; exfalso; cbv beta iota delta [a_d a_bs en] in Hx; rewrite EBS in Hx; cbn [length Z.of_nat] in Hx; clear - Hx; lia].
             intros x Hx. cbv beta iota delta [a_d a_bs en] in Hx. fold len in Hx, P2. exact (GL p n x (DLV _ Hin) ltac:(clear - Hx P1 P2; lia)). }
    split; [destruct PAYIN as [H|[H _]]; [right; exact H| left; exact H]|]. split; [exact (proj2 LEN)|]. split; [exact FDO| exact MST]. }
  assert (ER3 : errst_at_rest E [] m3).
  { apply (errst_rest_agree m m3 _ _ ER0). intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [R|(p & n & [] & _)]. exact (GL (a_E RT en) 904 a (CLV _ INE) R). }
  assert (HkE : forall c', w7_post RT LIB en c' -> realizes asegs c' T) by (intros c' Hc'; apply Hk; exact Hc').
  clear G3 GS GL SAVED3 SHL3 SHJ3 FHD3 FF3 FF3' SB3 MU3 WM3 MU1 WM1 WM2 PRES2 AG2 FR2 GAP2 FB2 SB2 FR1 GAP1 ST1 ST2 ART1 ART2 MI1 MI2 Hk.
  (* [comment removed for export] *)
  destruct (Z_lt_ge_dec len 2) as [SHORT|LONG].
  - (* [comment removed for export] *)
    pose proof (w7_lx_walk sp gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 e_fuzz_one_body) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-15)) b5 b6 b7 s4 s8 s9 u3 u4 u5 u6 F2 fc2 m3 d f pd len
                  ltac:(clear - SHORT LEN; lia) MI3) as WX.
    unfold w7_regsE in WX. fold usp usp1 in WX.
    cl_lift WX Hc3' c4 Hc4. destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & -> & Hc4'). clear Hc4 Hc3'.
    exact (EXITP en Σ1 m3 (FUZZ_COST - 1) F2 fc2 (Z_to_bv 64 SITE_w7_smalloc) u0 u1 u2 (Z_to_bv 64 (len + -2147483648)) (Z_to_bv 64 (-2147483646)) (Z_to_bv 64 e_fuzz_one_body)
             (Z_to_bv 64 (-14)) (Z_to_bv 64 (-15)) b5 b6 b7 (Z_to_bv 64 d) s4 (Z_to_bv 64 len) (Z_to_bv 64 0x7fff8000) s8 s9 u3 u4 u5 u6 lowj COM3 ER3 LOW56 T c4 Hc4' HkE).
  - (* [comment removed for export] *)
    pose proof (w7_lc_walk sp gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 e_fuzz_one_body) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-15)) b5 b6 b7 s4 s8 s9 u3 u4 u5 u6 F2 fc2 m3 d f pd len
                  ltac:(clear - LONG LEN; lia) MI3) as WC.
    unfold w7_regsE in WC. fold usp usp1 in WC.
    cl_lift WC Hc3' c4 Hc4. destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & -> & Hc4'). clear Hc4 Hc3'.
    pose proof (bio_s_mem_walk (Z_to_bv 64 SITE_w7_smem) (Z_to_bv 64 usp1) gp u0 u1 u2 sp (Z_to_bv 64 usp1) (Z_to_bv 64 (len + -2147483648)) (Z_to_bv 64 (-2147483646))
                  (Z_to_bv 64 e_fuzz_one_body) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-15)) b5 b6 b7 (Z_to_bv 64 f) (Z_to_bv 64 d) s4 (Z_to_bv 64 len) (Z_to_bv 64 (-8)) (Z_to_bv 64 0x7fff8000) s8 s9
                  (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) u3 u4 u5 u6 F2 fc2 m3 lo
                  ltac:(rewrite EU1; unfold usp1; clear - LOS HP; unfold FUZZ_STACK in *; lia) HLOS ltac:(rewrite EU1; unfold usp1; clear - SPH HP; lia) ltac:(rewrite EU1; exact ST3) MI3) as WS.
    cl_lift WS Hc4' c5 Hc5. destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m4 & -> & MU4 & WM4 & MI4 & ST4) & Hc5'). clear Hc5 Hc4'.
    rewrite EU1 in MU4, ST4. rewrite (ret_pc_even SITE_w7_smem) in Hc5' by (unfold SITE_w7_smem; clear; lia).
    assert (COM4 : w7_com en Σ1 m4 (FUZZ_COST - 1) []).
    { eapply (PC w7_seg en Σ1 m3 m4 _ [] _ COM3 MU4 WM4 MI4 ST4). constructor; [| constructor]. left. cbn [fst snd]. cbv beta iota delta [a_lo a_sp1 a_SP a_sp a_pd en]. fold usp. unfold usp1. clear - LOS HP; unfold FUZZ_STACK in *. lia. }
    assert (PR4 : rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) usp1 [(usp1 - 16, usp1)] m3 m4) by (intros a _ Ho; exact (MU4 a Ho)).
    assert (OUT4 : forall x, x < lo \/ usp1 <= x -> outside [(usp1 - 16, usp1)] x) by (intros x Hx; cbn; split; [clear - Hx LOS HP; unfold usp1, FUZZ_STACK in *; lia| exact I]).
    assert (ER4 : errst_at_rest E [] m4).
    { eapply (rest_keep errst_at_rest errst_fp errst_rest_agree errst_fp_where m3 m4); [exact ER3| exact PR4| rewrite LV1; exact (CLV _ INE)|].
      intros x Hx. apply OUT4. left. pose proof (af_live_range RT AF Σ m E 904 ART0 (CLV _ INE)) as (_ & X & _). cbv beta iota delta [a_E en] in Hx. clear - X Hx LOW. lia. }
    assert (FFK4 : forall A cs, rw_cells asegs m3 (f + A) cs -> 24 <= A -> A + Z.of_nat (cells_size cs) <= 248 -> rw_cells asegs m4 (f + A) cs).
    { intros A cs C H1 H2. eapply ff2_keep; [exact C| exact PR4| exact INF| clear - H1; lia| clear - H2; lia|]. intros x Hx. apply OUT4. left. clear - Hx H2 FLO'. lia. }
    pose proof (FFK4 32 _ CN3 ltac:(clear; lia) ltac:(cbn; clear; lia)) as CN4. pose proof (FFK4 64 _ CH3 ltac:(clear; lia) ltac:(cbn; clear; lia)) as CH4.
    pose proof (FFK4 96 _ CD3 ltac:(clear; lia) ltac:(cbn; clear; lia)) as CD4. pose proof (FFK4 128 _ CL3w ltac:(clear; lia) ltac:(cbn; clear; lia)) as CL4.
    pose proof (fr1_keep usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (Z_to_bv 64 RA_FUZZ) m3 m4 _ _ _ HP TOP FR3 PR4 ltac:(intros x Hx; apply OUT4; right; unfold usp1; clear - Hx; lia)) as FR4.
    clear PR4 OUT4 FFK4 CN3 CH3 CD3 CL3 CL3w FR3 ER3 COM3 MU4 WM4 MI3 ST3 ST4 GAP3 LOW56 lowj.
    (* [comment removed for export] *)
    pose proof (w7_n0_walk sp gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 MEM_METHOD) (Z_to_bv 64 (-2147483646)) (Z_to_bv 64 e_fuzz_one_body) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-15)) b5 b6 b7
                  s4 s8 s9 u3 u4 u5 u6 F2 fc2 m4 d f pd len MI4) as WN.
    unfold w7_regsE in WN. fold usp usp1 in WN.
    cl_lift WN Hc5' c6 Hc6. destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & -> & Hc6'). clear Hc6 Hc5'.
    eapply (PC w7c_bnew C_BNEW T en Σ1 m4 (FUZZ_COST - 1) F2 fc2 u0 u1 u2 (Z_to_bv 64 (-2147483646)) (Z_to_bv 64 e_fuzz_one_body) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-15)) b5 b6 b7
              _ _ _ _ _ _ _ _ _ _ _ u3 u4 u5 u6 c6 COM4 ltac:(clear; unfold FUZZ_COST; lia) Hc6').
    clear Hc6'. intros Σ2 m5 F5 fc5 y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 c7 K BI BB BM RP HK COM5 LV5 FRS5 PR5 MB5 Hc7. cbv beta delta [Fz_W7_calls.w7_cs] in Hc7.
    cbv beta iota delta [a_PMc a_sp a_gp a_sp1 a_SP a_pd en] in Hc7. fold usp in Hc7. fold usp1 in Hc7.
    destruct (P5 w7_lists en Σ2 m5 _ _ COM5) as (CLV5 & CLL5 & DLV5).
    assert (ER5 : errst_at_rest E [] m5).
    { eapply (rest_keep errst_at_rest errst_fp errst_rest_agree errst_fp_where m4 m5); [exact ER4| exact PR5| rewrite LV1; exact (CLV _ INE)|].
      intros x Hx. apply (P7 w7_out_libW en Σ1 m4 _ _ x COM4). do 3 right. exact Hx. }
    assert (FFK5 : forall A v, rw_cells asegs m4 (f + A) [C8 v] -> 24 <= A -> A + 8 <= 248 -> rw_cells asegs m5 (f + A) [C8 v]).
    { intros A v C H1 H2. eapply ff2_keep; [exact C| exact PR5| exact INF| clear - H1; lia| cbn [cells_size csize Nat.add]; clear - H2; lia|].
      intros x Hx. apply (P7 w7_out_libW en Σ1 m4 _ _ x COM4). right; left. cbn [cells_size csize Nat.add] in Hx. cbv beta iota delta [a_f en]. clear - Hx H1 H2. lia. }
    pose proof (FFK5 32 _ CN4 ltac:(clear; lia) ltac:(clear; lia)) as CN5. pose proof (FFK5 64 _ CH4 ltac:(clear; lia) ltac:(clear; lia)) as CH5.
    pose proof (FFK5 96 _ CD4 ltac:(clear; lia) ltac:(clear; lia)) as CD5. pose proof (FFK5 128 _ CL4 ltac:(clear; lia) ltac:(clear; lia)) as CL5.
    pose proof (fr1_keep usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (Z_to_bv 64 RA_FUZZ) m4 m5 _ _ _ HP TOP FR4 PR5
                  ltac:(intros x Hx; apply (P7 w7_out_libW en Σ1 m4 _ _ x COM4); do 2 right; left; cbv beta iota delta [a_sp1 a_SP a_sp a_pd en]; fold usp; clear - Hx; lia)) as FR5.
    clear FFK5 CN4 CH4 CD4 CL4 FR4 ER4 COM4 PR5 MI4.
    (* [comment removed for export] *)
    assert (INBI : In (BI, 128) (mbio_ent K 0)) by (rewrite HK; cbn; left; reflexivity).
    pose proof (P7 w7_cur_facts en Σ2 m5 _ _ (BI, 128) COM5 INBI ltac:(cbn; clear; lia)) as (_ & BI0 & BILO & _). cbn [fst snd] in BI0, BILO.
    pose proof COM5 as (ART5 & MI5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CFR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PAY5 & _).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct PAYIN as [(p & n & HinD & P1 & P2)|[EBS _]]; [| exfalso; subst len; rewrite EBS in LONG; cbn in LONG; clear - LONG; lia].
    fold len in P2.
    assert (DHI : d + 1 < 2 ^ 64) by (pose proof (LVLO p n d (DLV _ HinD) ltac:(clear - P1 P2 LONG; lia)) as X; clear - X SPH; lia).
    pose proof (w7_n1_walk sp gp (Z_to_bv 64 TP_A) y0 y1 y2 e1 e2 e3 e4 e5 e6 e7 s4 s8 s9 y3 y4 y5 y6 F5 fc5 m5 d f lo pd len BI
                  BI0 ltac:(clear - BILO; cbv beta iota delta [a_lo en] in BILO; lia) ltac:(fold usp; clear - HLO; lia) HLOS ltac:(fold usp; clear - SPH; lia) ltac:(clear - LONG LEN; lia)
                  D0 DHI MI5) as WN1.
    unfold w7_regsE in WN1. fold usp usp1 in WN1.
    cl_lift WN1 Hc7 c8 Hc8. destruct (ASTA_unpack RT Σ2 _ _ c8 Hc8) as (ms8 & -> & Hc8'). clear Hc8 Hc7.
    (* [comment removed for export] *)
    assert (HBS : exists b0 bsr, bs = b0 :: bsr) by (clear - LONG; subst len; destruct bs as [|b0 bsr]; [cbn in LONG; lia| exists b0, bsr; reflexivity]).
    destruct HBS as (b0 & bsr & EBS).
    assert (LBSR : Z.of_nat (length bsr) = len - 1) by (subst len; rewrite EBS; cbn [length]; clear; lia).
    assert (SRC : bytes_at asegs m5 (d + 1) bsr).
    { cbv beta iota delta [a_d a_bs en] in PAY5. rewrite EBS in PAY5. pose proof (proj1 (bytes_at_app _ m5 d [b0] bsr) PAY5) as [_ X]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in X. exact X. }
    assert (SB : src_blk (rt_live RT Σ2) (d + 1) (len - 1) (mbio_blocks K)).
    { right. exists p, n. split; [exact (DLV5 _ HinD)|]. split; [clear - P1; lia|]. split; [clear - P2; lia|].
      intros X. rewrite <- (mbio_ent_fst K 0) in X. apply in_map_iff in X. destruct X as (e & Ee & He).
      apply (CFR5 e He). rewrite map_app. apply in_or_app; right. rewrite Ee. cbv beta iota delta [a_DRV en]. exact (in_map fst _ _ HinD). }
    assert (GRN : gr_n (0 - 0 + (len - 1)) <= 2 ^ 27) by (unfold gr_n; clear - LEN; Z.div_mod_to_equations; lia).
    pose proof (w7p_cost (0 - 0) (len - 1) 0 GRN) as PCB.
    rewrite <- (app_nil_r (mbio_ent K 0)) in COM5.
    eapply (PC w7c_write C_BW T en Σ2 m5 (FUZZ_COST - 1 - 1) [] K BI 0 0 0 (d + 1) (len - 1) bsr SITE_w7_write1 F5 fc5 y0 y1 y2 e3 e4 e5 e6 e7
              _ _ _ _ _ _ _ _ _ _ _ y3 y4 y5 y6 c8 COM5 MB5 GRN ltac:(clear - LONG LEN; lia) SRC ltac:(rewrite <- LBSR, Nat2Z.id; reflexivity) SB
              ltac:(clear - PCB; unfold W7P_WCOST, FUZZ_COST in *; lia) ltac:(cbn; clear; lia)
              ltac:(unfold W7_SITES_OWN; cbn [map]; do 3 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 3 right; left; reflexivity)
              ltac:(unfold SITE_w7_write1; clear; lia) eq_refl Hc8').
    clear Hc8'. intros Σ3 m6 F6 fc6 z0 z1 z2 h1 h2 h3 h4 h5 h6 h7 z3 z4 z5 z6 c9 pd' max' COM6 FRS6 PR6 KP6 MB6 HMAX HFIT Hc9. cbv beta delta [Fz_W7_calls.w7_cs] in Hc9.
    cbv beta iota delta [a_PMc a_sp a_gp a_sp1 a_SP a_pd en] in Hc9. fold usp in Hc9. fold usp1 in Hc9.
    rewrite app_nil_r in COM6. replace (0 - 0 + (len - 1)) with (len - 1) in MB6, HMAX, HFIT by (clear; lia). rewrite HK in PR6. cbn [k_d] in PR6. rewrite <- HK in PR6.
    pose proof COM5 as COM5'. rewrite app_nil_r in COM5'.
    destruct (P5 w7_lists en Σ3 m6 _ _ COM6) as (CLV6 & CLL6 & DLV6).
    assert (HO6 : forall x, ((exists p0 n0, In (p0, n0) [] /\ p0 <= x < p0 + n0) \/ (a_f RT en + 24 <= x < a_f RT en + 248) \/ (a_sp1 RT en <= x < USTACK_TOP) \/ (a_E RT en <= x < a_E RT en + 904)) ->
                  outside ((G_ALLOW_CUST, G_ALLOW_CUST + 1) :: mbio_W K 0) x) by (intros x Hx; exact (w7_out_bioW RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS REST en Σ2 m5 _ K 0 [] x COM5 Hx)).
    assert (ER6 : errst_at_rest E [] m6).
    { eapply (rest_keep errst_at_rest errst_fp errst_rest_agree errst_fp_where m5 m6); [exact ER5| exact PR6| exact (CLL5 _ INE)|]. intros x Hx. apply HO6. do 3 right. exact Hx. }
    assert (FFK6 : forall A v, rw_cells asegs m5 (f + A) [C8 v] -> 24 <= A -> A + 8 <= 248 -> rw_cells asegs m6 (f + A) [C8 v]).
    { intros A v C H1 H2. eapply ff2_keep; [exact C| exact PR6| rewrite FRS5; exact INF| clear - H1; lia| cbn [cells_size csize Nat.add]; clear - H2; lia|].
      intros x Hx. apply HO6. right; left. cbn [cells_size csize Nat.add] in Hx. cbv beta iota delta [a_f en]. clear - Hx H1 H2. lia. }
    pose proof (FFK6 32 _ CN5 ltac:(clear; lia) ltac:(clear; lia)) as CN6. pose proof (FFK6 64 _ CH5 ltac:(clear; lia) ltac:(clear; lia)) as CH6.
    pose proof (FFK6 96 _ CD5 ltac:(clear; lia) ltac:(clear; lia)) as CD6. pose proof (FFK6 128 _ CL5 ltac:(clear; lia) ltac:(clear; lia)) as CL6.
    rewrite FRS5 in PR6.
    pose proof (fr1_keep usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (Z_to_bv 64 RA_FUZZ) m5 m6 _ _ _ HP TOP FR5 PR6
                  ltac:(intros x Hx; apply HO6; do 2 right; left; cbv beta iota delta [a_sp1 a_SP a_sp a_pd en]; fold usp; clear - Hx; lia)) as FR6.
    clear FFK6 HO6 CN5 CH5 CD5 CL5 FR5 ER5 PR6 KP6 MB5 SRC SB PAY5 CFR5 COM5 COM5' CLV5 CLL5 DLV5 ART5 MI5.
    (* [comment removed for export] *)
    pose proof COM6 as (ART6 & MI6 & ST6 & GAP6 & _ & _ & _ & LOW6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PAY6 & _).
    cbv beta iota delta [a_d a_bs a_lo a_sp1 a_SP a_sp a_pd a_S0 en] in PAY6, GAP6, ST6, LOW6. fold usp in GAP6, ST6. fold usp1 in GAP6, ST6. rewrite EBS in PAY6.
    pose proof (af_live_range RT AF Σ3 m6 p n ART6 (DLV6 _ HinD)) as (Q0 & Q1 & _). destruct (af_acc_live RT AF Σ3 m6 p n ART6 (DLV6 _ HinD)) as [_ ACC6].
    pose proof (w7_s2_walk sp gp (Z_to_bv 64 TP_A) z0 z1 z2 h1 h2 h3 h4 h5 h6 h7 s8 s9 z3 z4 z5 z6 (Z_to_bv 64 RA_FUZZ) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 b0 bsr F6 fc6 m6 d len BI f lo pd p n
                  j1 j2 j3 j4 j5 j6 HP F0 ltac:(clear - FIMG; unfold SEGTOP_A in *; lia) FLO' ltac:(fold usp; clear - HLO; lia) HLOS ltac:(fold usp; clear - SPH; lia)
                  ltac:(clear - LONG LEN; lia) Q0 P1 ltac:(clear - P2 LONG; lia) ltac:(clear - Q1 LOW6; lia) ACC6 PAY6 FR6 GAP6 MI6) as W2.
    unfold w7_s2_post in W2. fold usp usp1 in W2.
    cl_lift W2 Hc9 c10 Hc10. destruct (ASTA_unpack RT Σ3 _ _ c10 Hc10) as (ms10 & (m7 & X2) & Hc10'). clear Hc10 Hc9.
    assert (X2' : ms10 = MS (mkR (Z_to_bv 64 SITE_w7_pem) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) z0 z1 z2 sp (Z_to_bv 64 usp1)
                              (Z_to_bv 64 BI) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 64)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (f + 128)) (Z_to_bv 64 (bv_unsigned b0)) h6 h7
                              (Z_to_bv 64 f) (Z_to_bv 64 d) (Z_to_bv 64 BI) (Z_to_bv 64 (d / 8 + 2147450880)) (Z_to_bv 64 (-8)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 128)) (Z_to_bv 64 (f + 96))
                              (Z_to_bv 64 (f / 8 + 2147450880)) (Z_to_bv 64 f) z3 z4 z5 z6)
                         F6 (Z_to_bv 64 A_PEM_read_bio_ex) fc6 None m7 (seg_rom asegs)
              /\ munch [(usp - 152, usp - 128)] m6 m7 /\ wmono asegs m6 m7 /\ mem_inv asegs m7
              /\ fr2 usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (Z_to_bv 64 RA_FUZZ) m7 /\ stk asegs m7 usp1 (usp + -160)).
    { unfold fr2. unfold usp1 in X2 |- *. destruct HP as [EP|EP]; rewrite EP in X2 |- *; cbn [w7_mframe2 Z.eqb] in X2 |- *; exact X2. }
    clear X2. destruct X2' as (-> & MU7 & WM7 & MI7 & FR7 & GAP7).
    assert (ST7 : stk asegs m7 lo usp1) by (eapply stk_munch; [exact ST6| exact MU7| exact WM7| intros x Hx; cbn; split; [unfold usp1 in Hx; clear - Hx HP; lia| exact I]]).
    assert (COM7 : w7_com en Σ3 m7 (FUZZ_COST - 1 - 1 - puts_cost (0 - 0) (len - 1) 0) (mbio_ent (mbk_data K pd') max')).
    { eapply (PC w7_seg en Σ3 m6 m7 _ _ _ COM6 MU7 WM7 MI7 ST7). constructor; [| constructor]. right; left. cbn [fst snd]. cbv beta iota delta [a_SP a_sp en]. fold usp. clear. lia. }
    assert (PR7 : rt_pres_fp (rt_live RT Σ3) (rt_frames RT Σ3) usp1 [(usp - 152, usp - 128)] m6 m7) by (intros a _ Ho; exact (MU7 a Ho)).
    assert (HO7 : forall x, ((exists p0 n0, In (p0, n0) (mbio_ent (mbk_data K pd') max') /\ p0 <= x < p0 + n0) \/ (a_f RT en <= x < a_f RT en + 248) \/ (a_SP RT en + -104 <= x < USTACK_TOP) \/ (a_E RT en <= x < a_E RT en + 904)) ->
                  outside [(usp - 152, usp - 128)] x).
    { intros x Hx. exact (w7_out_seg RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS REST en Σ3 m6 _ _ x (usp - 152) (usp - 128) COM6 ltac:(cbv beta iota delta [a_SP a_sp en]; fold usp; clear; lia) ltac:(cbv beta iota delta [a_SP a_sp en]; fold usp; clear; lia) Hx). }
    assert (ER7 : errst_at_rest E [] m7).
    { eapply (rest_keep errst_at_rest errst_fp errst_rest_agree errst_fp_where m6 m7); [exact ER6| exact PR7| exact (CLL6 _ INE)|]. intros x Hx. apply HO7. do 3 right. exact Hx. }
    assert (FFK7 : forall A v, rw_cells asegs m6 (f + A) [C8 v] -> 24 <= A -> A + 8 <= 248 -> rw_cells asegs m7 (f + A) [C8 v]).
    { intros A v C H1 H2. eapply ff2_keep; [exact C| exact PR7| rewrite FRS6, FRS5; exact INF| clear - H1; lia| cbn [cells_size csize Nat.add]; clear - H2; lia|].
      intros x Hx. apply HO7. right; left. cbn [cells_size csize Nat.add] in Hx. cbv beta iota delta [a_f en]. clear - Hx H1 H2. lia. }
    pose proof (FFK7 32 _ CN6 ltac:(clear; lia) ltac:(clear; lia)) as CN7. pose proof (FFK7 64 _ CH6 ltac:(clear; lia) ltac:(clear; lia)) as CH7.
    pose proof (FFK7 96 _ CD6 ltac:(clear; lia) ltac:(clear; lia)) as CD7. pose proof (FFK7 128 _ CL6 ltac:(clear; lia) ltac:(clear; lia)) as CL7.
    assert (MB7 : mbio_rep (rt_live RT Σ3) m7 (mbk_data K pd') BI M_MEM (len - 1) max' 0).
    { eapply (mbio_rep_keep (rt_live RT Σ3)); [exact MB6| exact PR7| intros e He; split; exact (CLV6 _ He)|].
      intros e x He Hx. apply HO7. left. exists (fst e), (snd e). split; [destruct e; exact He| exact Hx]. }
    clear FFK7 HO7 PR7 CN6 CH6 CD6 CL6 FR6 ER6 MB6 MU7 WM7 COM6 ART6 MI6 ST6 GAP6 PAY6 ACC6.
    set (crem1 := FUZZ_COST - 1 - 1 - puts_cost (0 - 0) (len - 1) 0) in *.
    assert (CR1 : 2 ^ 33 - 2 - W7P_WCOST <= crem1) by (subst crem1; clear - PCB; unfold FUZZ_COST; lia).
    pose proof (bv_unsigned_in_range 8 b0) as B0R. unfold bv_modulus in B0R. change (2 ^ Z.of_N 8) with 256 in B0R.
    (* [comment removed for export] *)
    eapply (PCE w7c_pem C_PEM T en Σ3 m7 crem1 (mbk_data K pd') BI (len - 1) max' (bv_unsigned b0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) ol F6 fc6 z0 z1 z2 h6 h7
              _ _ _ _ _ _ _ _ _ _ _ z3 z4 z5 z6 c10 COM7 MB7 ltac:(clear - LEN; lia) ER7 CN7 CH7 CD7 CL7
              ltac:(unfold pem_credit; clear - CR1 LEN; unfold W7P_WCOST in *; lia) ltac:(clear - B0R; lia) Hc10').
    clear Hc10'. intros Σ4 m8 F8 fc8 w0 w1 w2 k1 k2 k3 k4 k5 k6 k7 w3 w4 w5 w6 c11 ret boff' top bot strs news COM8 FRS8 PR8 KP8 BOFF MB8 EL8 LS2 S64 NDSN POUT NSZ Hc11.
    cbv beta delta [Fz_W7_calls.w7_cs] in Hc11.
    destruct (P5 w7_lists en Σ3 m7 _ _ COM7) as (CLV7 & CLL7 & DLV7). pose proof COM7 as (ART7 & _).
    (* [comment removed for export] *)
    assert (HO8 : forall x, usp1 <= x < USTACK_TOP ->
      outside ([(a_f RT en + 32, a_f RT en + 32 + 8); (a_f RT en + 64, a_f RT en + 64 + 8); (a_f RT en + 96, a_f RT en + 96 + 8); (a_f RT en + 128, a_f RT en + 128 + 8); (a_E RT en, a_E RT en + 904)]
               ++ mbio_W (mbk_data K pd') max' ++ lib_W (a_LBL RT en)) x).
    { intros x Hx. pose proof (af_live_range RT AF Σ3 m7 E 904 ART7 (CLL7 _ INE)) as (_ & XE & _).
      pose proof COM7 as (_ & _ & _ & _ & _ & _ & _ & LOW7 & _). cbv beta iota delta [a_lo a_S0 en] in LOW7.
      apply outside_app_intro.
      - cbv beta iota delta [a_f a_E en]. cbn [outside]. unfold usp1 in Hx. clear - Hx FLO' HLO HP XE LOW7. repeat split; try exact I; lia.
      - apply outside_app_intro.
        + apply outside_intro. intros [u v] Hiv R. cbn [fst snd] in R. apply in_mbio_W in Hiv. destruct Hiv as (e & He & -> & ->). destruct e as [q k]. cbn [fst snd] in R.
          pose proof (af_live_range RT AF Σ3 m7 q k ART7 (CLV7 _ He)) as (_ & Y & _). unfold usp1 in Hx. clear - Y R Hx LOW7 HLO HP. lia.
        + apply (P7 w7_out_libW en Σ3 m7 _ _ x COM7). do 2 right; left. cbv beta iota delta [a_sp1 a_SP a_sp a_pd en]. fold usp. unfold usp1 in Hx. clear - Hx. lia. }
    pose proof (fr2_keep usp pd f j1 j2 j3 j4 j5 j6 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (Z_to_bv 64 RA_FUZZ) m7 m8 _ _ _ HP TOP FR7 PR8 HO8) as FR8.
    exact (P7P en Σ4 m8 (crem1 - pem_credit (len - 1 - 0)) (mbk_data K pd') BI (len - 1) max' boff' strs top bot news ret j1 j2 j3 j4 j5 j6 F8 fc8 w0 w1 w2 k1 k2 k3 k4 k5 k6 k7 w3 w4 w5 w6
             COM8 BOFF ltac:(clear - LEN; lia) MB8 EL8 LS2 S64 POUT ltac:(clear - NSZ; lia) FR8
             ltac:(subst crem1; unfold pem_credit, W7P_CREDIT, W7P_WCOST, FUZZ_COST in *; clear - PCB LEN; lia) ltac:(cbv beta iota delta [a_len a_bs en]; fold len; clear - LONG; lia) T c11 Hc11 HkE).
Qed.
End W7E.
