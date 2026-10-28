(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA Image.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx D_rlkit D_libiface_pem D_loopdefs D_hdr X_ax D_trpro D_trwalk D_trdefs D_tr1 D_tr3 D_file3.
From Stdlib Require Import Permutation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma ft_short : forall (data : list byte), Z.of_nat (length data) < 6 -> file_trace (map bv_unsigned data) = mkCT 2 msg_short_hdr 2.
Proof.
  intros data H. unfold file_trace, zlength. rewrite length_map.
  rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Definition cfgL (d0 d1 : byte) : Z := Z.land (bv_unsigned d0 + bv_unsigned d1 * 256) 32767.

Lemma cfg_len_cons : forall (d0 d1 : byte) (rest : list byte), cfg_len (map bv_unsigned (d0 :: d1 :: rest)) = cfgL d0 d1.
Proof. intros d0 d1 rest. reflexivity. Qed.

Lemma ft_over : forall (d0 d1 : byte) (rest : list byte), 6 <= Z.of_nat (length (d0 :: d1 :: rest)) < 67108864 ->
  Z.of_nat (length (d0 :: d1 :: rest)) < 6 + cfgL d0 d1 ->
  file_trace (map bv_unsigned (d0 :: d1 :: rest)) = mkCT 2 msg_cfg_overrun 2.
Proof.
  intros d0 d1 rest H1 H2. unfold file_trace, zlength. rewrite length_map, cfg_len_cons.
  rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma ft_good : forall (d0 d1 d2 : byte) (rest : list byte), Z.of_nat (length (d0 :: d1 :: d2 :: rest)) < 67108864 ->
  6 + cfgL d0 d1 <= Z.of_nat (length (d0 :: d1 :: d2 :: rest)) ->
  file_trace (map bv_unsigned (d0 :: d1 :: d2 :: rest)) = mkCT 1 (zeros_out (Z.to_nat (tr_calls (cfgL d0 d1) d2))) 0.
Proof.
  intros d0 d1 d2 rest H1 H2. unfold file_trace, zlength. rewrite length_map, cfg_len_cons.
  rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by (unfold cfgL in *; pose proof (Z.land_nonneg (bv_unsigned d0 + bv_unsigned d1 * 256) 32767); lia).
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  unfold cfg_calls, tr_calls. rewrite cfg_len_cons. destruct (Z.eqb_spec (cfgL d0 d1) 0) as [E|E].
  - rewrite E. cbn. reflexivity.
  - pose proof (Z.land_nonneg (bv_unsigned d0 + bv_unsigned d1 * 256) 32767). unfold cfgL in E, H.
    rewrite (proj2 (Z.ltb_lt 0 (cfgL d0 d1))) by (unfold cfgL; lia). reflexivity.
Qed.

Lemma zeros_out_split : forall k, (0 < k)%nat -> evw 1 (zeros_out k) = evw 1 [48; 10] ++ evw 1 (zeros_out (k - 1)).
Proof. intros [|k] H; [lia|]. unfold evw. cbn [zeros_out repeat concat]. rewrite <- map_app. replace (S k - 1)%nat with k by lia. reflexivity. Qed.

Lemma fd_remove_FD : forall argvb n, fd_remove (FD argvb n) (Z_to_bv 64 3) = fds0.
Proof. intros argvb n. reflexivity. Qed.

Lemma list3' : forall (l : list byte), (3 <= length l)%nat -> exists d0 d1 d2 r, l = d0 :: d1 :: d2 :: r.
Proof. intros l H. destruct l as [|d0 [|d1 [|d2 r]]]; cbn in H; try lia. do 4 eexists. reflexivity. Qed.

Section File4.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable CG : cgraph.                (* [comment removed for export] *)
(* [comment removed for export] *)
Variable LIB0P : mem -> Prop.
Variable LIBP : list (Z * Z) -> mem -> Prop.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Variable argvb : list (list byte).
Variable fs : Fs.
Variable data : list byte.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis CLS : close_contract RT.
Hypothesis MAL : malloc_contract RT.
Hypothesis FRE : free_contract RT.
Hypothesis FRN : free_null_contract RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis FWR : fwrite_stderr_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis INITC : fuzz_init_cps RT LIB0P LIBP FZ_SITES FZ_CALLS.
Hypothesis FUZZC : fuzz_one_cps RT LIBP FZ_SITES FZ_CALLS.
Hypothesis VPR : vprintf_emit0_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis EXC : exit_contract RT XENV OUT_rep ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
(* [comment removed for export] *)
Variable XENV' : mem -> Prop.
Hypothesis XENV'_loc : fp_local XENV_FP XENV'.
Hypothesis XENV_ax : forall m, XENV m -> exists fin p1 p2, ax_chunks false fin p1 p2 m.
Hypothesis XENV_libc : forall m, XENV m -> libc_cells m.
Hypothesis XENV_incb : forall m, XENV m -> rw_cells asegs m TR_INCB [C1 (Z_to_bv 8 0)].
Hypothesis XENV_step : forall m m', XENV m ->
  agree_on (fun x => in_ranges XENV_FP x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> TR_INCB) m m' ->
  (exists fin p1 p2, ax_chunks true fin p1 p2 m') -> rw_cells asegs m' TR_INCB [C1 (Z_to_bv 8 0)] -> XENV' m'.
Hypothesis XENV_fp_ax : forall x, (0xbc3f40 <= x < 0xbc3f70 \/ 0xbc4060 <= x < 0xbc4070 \/ x = TR_INCB) -> in_ranges XENV_FP x.
Hypothesis XENV'_ax : forall m, XENV' m -> exists fin p1 p2, ax_chunks true fin p1 p2 m.
Hypothesis XENV'_incb : forall m, XENV' m -> rw_cells asegs m TR_INCB [C1 (Z_to_bv 8 0)].
Hypothesis XENV'_upd : forall m m', XENV' m ->
  agree_on (fun x => in_ranges XENV_FP x /\ ~ (0xbc3f40 <= x < 0xbc3f70) /\ ~ (0xbc4060 <= x < 0xbc4070) /\ x <> TR_INCB) m m' ->
  (exists fin p1 p2, ax_chunks true fin p1 p2 m') -> rw_cells asegs m' TR_INCB [C1 (Z_to_bv 8 0)] -> XENV' m'.
Hypothesis EXC' : exit_contract RT XENV' OUT_rep ERR_rep.
Hypothesis LIB_pre : forall m, LIB m -> LIB0P m /\ rw_cells asegs m TR_INIT [C1 (Z_to_bv 8 0)].
Hypothesis LOC0 : lib0_local_d LIB0P.
Hypothesis LOCP : lib_local_d LIBP.
Hypothesis CGH : cg_has CG FZ_SITES FZ_CALLS.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, CREDIT_DRV, g_read_stage, S_SHORT, S_OVER in *; lia.

Theorem done_cpsE : Z.of_nat (length data) < 67108864 ->
  cpsE asegs (RDONE RT OUT_rep ERR_rep XENV LIB CG argvb fs data)
    (evw (ct_fd (file_trace (map bv_unsigned data))) (ct_bytes (file_trace (map bv_unsigned data))))
    (EXIT fs (ct_code (file_trace (map bv_unsigned data)))).
Proof using AF AF_DRV CLS MAL FRE FRN MCP FWR INITC FUZZC VPR EXC OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img LIB_pre LOC0 LOCP CGH XENV'_loc XENV_ax XENV_libc XENV_incb XENV_step XENV_fp_ax XENV'_ax XENV'_incb XENV'_upd EXC'.
  intros Hbig T c HR Hk.
  destruct HR as (Σ & usp & ap & path & buf & cap & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11
                  & t3 & t4 & t5 & t6 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & HA & HD & HLS & HBUF & Hdc & HCAP).
  pose proof HD as ((ART0 & MI0 & CLX0 & ARGV0 & FR0 & ST0 & B16 & UA & ULO & USP0) & HB & Hap & Hhi & SPW).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof HLS as (LV & FRS & CR & USP0').
  pose proof (cap_ok_range cap HCAP) as CAPR.
  assert (INB : In (buf, cap) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m buf cap ART0 INB) as (PR1 & PR2 & PR3).
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  set (n := Z.of_nat (length data)) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  assert (UTOP : usp + 16 <= USTACK_TOP) by lia.
  (* [comment removed for export] *)
  apply (CLS Σ (FD argvb n) fs (Z_to_bv 64 0x1f2c90) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 2)
           (Z_to_bv 64 buf) (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 path) (Z_to_bv 64 n) (Z_to_bv 64 3) (Z_to_bv 64 cap)
           (Z_to_bv 64 g_read_stage) (Z_to_bv 64 0) s8 s9 s10 s11 t3 t4 t5 t6 F fc m 3 lo); try reflexivity; try assumption.
  - lia.
  - unfold FD. rewrite fd_lookup_insert_same. discriminate.
  - rewrite EU. exact ST0.
  - rewrite EU. ul.
  - intros cf1 (m1 & Hc1). rewrite fd_remove_FD in Hc1.
    destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (RS1 & (ART1 & MI1 & WM1 & ST1 & MU1)) & Hc1').
    destruct RS1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F' & fc' & ->).
    rewrite EU in ST1, MU1.
    rewrite (ret_pc_even 0x1f2c90) in Hc1' by lia.
    assert (CLX1 : CLX OUT_rep ERR_rep XENV LIB stdout_init m1).
    { apply (CLX_munch OUT_rep ERR_rep IO_FP XENV XENV_FP LIB OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img _ m m1 _ CLX0 MU1 WM1).
      intros x Hx. cbn. split; [ul| exact I]. }
    assert (FR1 : main_frame m1 usp c0 c1 c2 c3 c4 c5 c6 c7).
    { apply (main_frame_agree m m1 usp _ _ _ _ _ _ _ _ FR0); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1).
      intros x Hx. cbn. split; [lia| exact I]. }
    assert (HBUF1 : bytes_at asegs m1 buf data).
    { apply (bytes_at_agree asegs m m1 _ _ HBUF). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [ul| exact I]. }
    assert (FC1 : FCTX RT OUT_rep ERR_rep XENV LIB Σ stdout_init usp buf cap c0 c1 c2 c3 c4 c5 c6 c7 m1).
    { split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|]. split; [exact FR1|]. split; [exact ST1|].
      split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|]. split; [exact INB|].
      split; [exact FRS| exact UTOP]. }
    pose proof (AF_DRV Σ m1 ART1) as (SC1 & _ & _ & ACS & ACO).
    destruct (Z.ltb_spec n 6) as [SHORT|LONG].
    + (* [comment removed for export] *)
      rewrite (ft_short data SHORT) in Hk |- *. cbn [ct_fd ct_bytes ct_code] in Hk |- *.
      pose proof (hdr_short_walk usp n gp t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 buf) (Z_to_bv 64 path)
                    (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 0) s8 s9 s10 s11 t3' t4' t5' t6' F' fc' m1
                    ltac:(lia) SC1 MI1) as W1.
      lazymatch type of W1 with evt asegs _ ?X =>
        assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
      clear W1.
      rewrite <- s_short_msg.
      apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ fds0 fs _ _ W1') Hc1').
      intros cf2 Hc2.
      destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & <- & Hc2').
      rewrite <- s_short_len in Hc2'.
      exact (diag_tail_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB fs AF AF_DRV FRE FWR EXC OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
               Σ usp buf cap S_SHORT s_short gp t0' t1' t2' a4' a5' a6' a7' (Z_to_bv 64 path) (Z_to_bv 64 n) (Z_to_bv 64 3) (Z_to_bv 64 cap)
               (Z_to_bv 64 g_read_stage) (Z_to_bv 64 0) s8 s9 s10 s11 t3' t4' t5' t6' c0 c1 c2 c3 c4 c5 c6 c7 F' fc' m1
               FC1 (s_short_at m1 MI1) ltac:(rewrite s_short_len; exact ACS) ltac:(ul) ltac:(rewrite s_short_len; ul) ltac:(rewrite s_short_len; lia)
               (or_introl eq_refl) T cf2 Hc2' Hk).
    + (* [comment removed for export] *)
      destruct (list3' data ltac:(lia)) as (d0 & d1 & d2 & rest & ED). subst data.
      set (L := cfgL d0 d1) in *.
      assert (LR : 0 <= L < 32768).
      { unfold L, cfgL. change 32767 with (Z.ones 15). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
      destruct (Z.ltb_spec n (6 + L)) as [OVER|GOOD].
      * (* [comment removed for export] *)
        rewrite (ft_over d0 d1 (d2 :: rest) ltac:(lia) OVER) in Hk |- *. cbn [ct_fd ct_bytes ct_code] in Hk |- *.
        pose proof (hdr_over_walk usp buf n d0 d1 (d2 :: rest) gp t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 path) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 0) s8 s9 s10 s11
                      t3' t4' t5' t6' F' fc' m1 ltac:(lia) ltac:(lia) ltac:(ul) HBUF1 OVER SC1 MI1) as W1.
        lazymatch type of W1 with evt asegs _ ?X =>
          assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
        clear W1.
        rewrite <- s_over_msg.
        apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ fds0 fs _ _ W1') Hc1').
        intros cf2 Hc2.
        destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & (b0 & b1 & ->) & Hc2').
        rewrite <- s_over_len in Hc2'.
        exact (diag_tail_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB fs AF AF_DRV FRE FWR EXC OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
                 Σ usp buf cap S_OVER s_over gp t0' t1' t2' a4' a5' a6' a7' b0 (Z_to_bv 64 n) (Z_to_bv 64 3) b1
                 (Z_to_bv 64 g_read_stage) (Z_to_bv 64 0) s8 s9 s10 s11 t3' t4' t5' t6' c0 c1 c2 c3 c4 c5 c6 c7 F' fc' m1
                 FC1 (s_over_at m1 MI1) ltac:(rewrite s_over_len; exact ACO) ltac:(ul) ltac:(rewrite s_over_len; ul) ltac:(rewrite s_over_len; lia)
                 (or_intror eq_refl) T cf2 Hc2' Hk).
      * (* [comment removed for export] *)
        rewrite (ft_good d0 d1 d2 rest ltac:(lia) GOOD) in Hk |- *. cbn [ct_fd ct_bytes ct_code] in Hk |- *.
        fold L in Hk |- *.
        set (calls := tr_calls L d2) in *.
        pose proof (tr_calls_range L d2) as TCR. fold calls in TCR.
        rewrite (zeros_out_split (Z.to_nat calls) ltac:(lia)).
        eapply rz_conseq; [| apply t_eq_sym, t_emit_app].
        pose proof (hdr_good_walk usp buf n d0 d1 (d2 :: rest) gp t0' t1' t2' (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 path) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 0) s8 s9 s10 s11
                      t3' t4' t5' t6' F' fc' m1 ltac:(lia) ltac:(lia) ltac:(ul) HBUF1 eq_refl GOOD MI1) as W1.
        lazymatch type of W1 with evt asegs _ ?X =>
          assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
        clear W1.
        apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ fds0 fs _ _ W1') Hc1').
        intros cf2 Hc2.
        destruct (ASTA_unpack RT Σ _ _ cf2 Hc2) as (ms2 & (b0 & ->) & Hc2').
        fold L in Hc2'.
        (* [comment removed for export] *)
        set (payload := skipn (Z.to_nat (6 + L)) (d0 :: d1 :: d2 :: rest)) in *.
        assert (LPL : Z.of_nat (length payload) = n - 6 - L) by (unfold payload; rewrite length_skipn; lia).
        assert (BPL : bytes_at asegs m1 (buf + 6 + L) payload).
        { pose proof HBUF1 as X. rewrite <- (firstn_skipn (Z.to_nat (6 + L)) (d0 :: d1 :: d2 :: rest)) in X.
          apply bytes_at_app in X. destruct X as [_ X]. rewrite length_firstn in X.
          replace (buf + Z.of_nat (Nat.min (Z.to_nat (6 + L)) (length (d0 :: d1 :: d2 :: rest)))) with (buf + 6 + L) in X by lia. exact X. }
        assert (BC : bytes_at asegs m1 (buf + 2) [d2]).
        { pose proof (bytes_at_nth1 asegs m1 buf (d0 :: d1 :: d2 :: rest) 2 d2 HBUF1 eq_refl) as X. exact X. }
        eapply (target_run_cpsE RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB CG LIB0P LIBP FZ_SITES FZ_CALLS fs AF AF_DRV MAL FRE FRN MCP INITC FUZZC
                  VPR OUT_loc ERR_loc XENV_loc IO_img XENV_img XENV' XENV'_loc XENV_ax XENV_libc XENV_incb XENV_step XENV_fp_ax XENV'_ax XENV'_incb XENV'_upd
                  LIB_pre LOC0 LOCP CGH Σ usp buf cap (buf + 2) L (buf + 6 + L) (n - 6 - L) d2 payload gp t0' t1' t2' b0 a5' a6' a7'
                  (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 L) (Z_to_bv 64 (buf + 6 + L)) (Z_to_bv 64 (n - 6 - L)) (sxb d1)
                  (Z_to_bv 64 g_read_stage) (Z_to_bv 64 0) s8 s9 s10 s11 t3' t4' t5' t6' c0 c1 c2 c3 c4 c5 c6 c7 F' fc' m1); [| exact Hc2'|].
        { split; [exact ART1|]. split; [exact MI1|]. split; [exact CLX1|]. split; [exact FR1|]. split; [exact ST1|].
          split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|]. split; [exact LV|].
          split; [exact FRS|]. split; [exact CR|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [intros _; exact BC|].
          split; [exact LR|]. split; [lia|]. split; [lia|]. split; [exact BPL|]. split; [lia|]. split; [lia|]. split; [exact UTOP| exact (proj2 USP0')]. }
        intros cf3 (Σ3 & CL3 & gp3 & u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v6 & v7 & v8 & v9 & v10 & v11 & u3 & u4 & u5 & u6
                    & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & F3 & fc3 & m3 & Hc3 & ART3 & MI3 & CLX3 & FR3 & ST3 & B16' & ULO3 & USP3
                    & SPW3 & LV3 & FRS3 & UT3).
        (* [comment removed for export] *)
        assert (INB3 : In (buf, cap) (rt_live RT Σ3)).
        { destruct LV3 as (P3 & _). apply (Permutation_in _ (Permutation_sym P3)). left. reflexivity. }
        assert (FC3 : FCTX RT OUT_rep ERR_rep XENV' LIBT Σ3 (so_lines (Z.to_nat calls - 1)) usp buf cap e0 e1 e2 e3 e4 e5 e6 e7 m3).
        { split; [exact ART3|]. split; [exact MI3|]. split; [exact CLX3|]. split; [exact FR3|]. split; [exact ST3|].
          split; [exact B16'|]. split; [exact ULO3|]. split; [exact USP3|]. split; [exact SPW3|]. split; [exact INB3|].
          split; [exact FRS3| exact UT3]. }
        destruct (Z.ltb_spec (bv_unsigned d1) 128) as [NC|CNT].
        -- pose proof (tr_ret_walk usp d1 gp3 u0 u1 u2 (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 0) w1 w2 w3 w4 w5 w6 w7
                         (Z_to_bv 64 L) (Z_to_bv 64 (buf + 6 + L)) (Z_to_bv 64 (n - 6 - L)) v6 v7 v8 v9 v10 v11 u3 u4 u5 u6 F3 fc3 m3
                         NC MI3) as W3.
           lazymatch type of W3 with evt asegs _ ?X =>
             assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
           clear W3.
           apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ3 fds0 fs _ _ W3') Hc3).
           intros cf4 Hc4.
           destruct (ASTA_unpack RT Σ3 _ _ cf4 Hc4) as (ms4 & <- & Hc4').
           exact (ret_tail_cpsE RT OUT_rep ERR_rep IO_FP XENV' XENV_FP LIBT fs AF AF_DRV FRE EXC' OUT_loc ERR_loc XENV'_loc LIBT_loc IO_img XENV_img
                    Σ3 (so_lines (Z.to_nat calls - 1)) 0 usp buf cap gp3 u0 u1 u2 w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 L)
                    (Z_to_bv 64 (buf + 6 + L)) (Z_to_bv 64 (n - 6 - L)) (sxb d1) v6 v7 v8 v9 v10 v11 u3 u4 u5 u6 e0 e1 e2 e3 e4 e5 e6 e7
                    F3 fc3 m3 FC3 ltac:(lia) ltac:(right; eexists; split; [| reflexivity]; lia)
                    T cf4 Hc4' Hk).
        -- pose proof (tr_ret_walk_count usp d1 gp3 u0 u1 u2 (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 0) w1 w2 w3 w4 w5 w6 w7
                         (Z_to_bv 64 L) (Z_to_bv 64 (buf + 6 + L)) (Z_to_bv 64 (n - 6 - L)) v6 v7 v8 v9 v10 v11 u3 u4 u5 u6 F3 fc3 m3
                         CNT MI3) as W3.
           lazymatch type of W3 with evt asegs _ ?X =>
             assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
           clear W3.
           apply (cps_realizes asegs _ _ _ _ (asta_evt RT AF Σ3 fds0 fs _ _ W3') Hc3).
           intros cf4 Hc4.
           destruct (ASTA_unpack RT Σ3 _ _ cf4 Hc4) as (ms4 & <- & Hc4').
           exact (ret_tail_cpsE RT OUT_rep ERR_rep IO_FP XENV' XENV_FP LIBT fs AF AF_DRV FRE EXC' OUT_loc ERR_loc XENV'_loc LIBT_loc IO_img XENV_img
                    Σ3 (so_lines (Z.to_nat calls - 1)) 0 usp buf cap gp3 u0 u1 u2 (Z_to_bv 64 251) w2 w3 w4 w5 w6 w7 (Z_to_bv 64 L)
                    (Z_to_bv 64 (buf + 6 + L)) (Z_to_bv 64 (n - 6 - L)) (sxb d1) v6 v7 v8 v9 v10 v11 u3 u4 u5 u6 e0 e1 e2 e3 e4 e5 e6 e7
                    F3 fc3 m3 FC3 ltac:(lia) ltac:(right; eexists; split; [| reflexivity]; lia)
                    T cf4 Hc4' Hk).
Qed.

End File4.
