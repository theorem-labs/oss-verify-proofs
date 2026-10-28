(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_libiface_pem D_agree D_clx PLayout I_lkit I_ut Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_env Fz_M_malloc Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_grow Fz_W1_writec Fz_W1_pploc Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux3 Fz_G_kit Fz_W7_defs Fz_W7_segs Fz_W7_inv Fz_W7_calls Fz_W7_x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation wz := (Z_to_bv 64) (only parsing).

(* [comment removed for export] *)
Lemma w7_f1g_walk : forall (sec : bool) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (buf BI f lo pd HD : Z),
  (pd = 0 \/ pd = 16) -> 0 < f -> f + 256 <= lo -> lo <= bv_unsigned sp - 176 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m (bv_unsigned sp + -160 - pd + 24) [C8 (Z_to_bv 64 (f + 64))] ->
  rw_cells asegs m (f + 64) [C8 (Z_to_bv 64 HD)] -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (w7_regsF (Z_to_bv 64 (if sec then SITE_w7_sfree2 else SITE_w7_free2)) sp gp tp t0 t1 t2 (Z_to_bv 64 HD) (Z_to_bv 64 W7_FILE)
                                         (Z_to_bv 64 (if sec then 51 else 55)) a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
                              F (Z_to_bv 64 (w7_free_entry sec)) fc None m (seg_rom asegs))
    (MS (w7_regsF (Z_to_bv 64 (if sec then SITE_w7_sfree1 else SITE_w7_free1)) sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (f + 96)) t3 t4 t5 t6 buf BI f pd)
        F (Z_to_bv 64 (if sec then SITE_w7_sfree1 else SITE_w7_free1)) fc None m (seg_rom asegs)).
Proof.
  intros until HD. intros HP F0 FLO HLO HLOS SPH SL HDC MI. unfold w7_regsF, w7_free_entry, SITE_w7_sfree1, SITE_w7_free1, SITE_w7_sfree2, SITE_w7_free2, A_CRYPTO_secure_free, A_CRYPTO_free, W7_FILE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EU1 : bv_unsigned (Z_to_bv 64 (SP + -160 - pd)) = SP + -160 - pd) by (apply unsigned_lit; lia).
  destruct sec.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep; zstep.
  all: subst SP; apply evt_done; reflexivity.
Qed.

Section W7F.
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
Hypothesis C_FR : crypto_free_env_stmt RT.
Hypothesis C_FN : crypto_free_null_env_stmt RT.
Hypothesis C_SF : crypto_secure_free_env_stmt RT.
Hypothesis C_BF : bio_free_mem_stmt RT libenv FZ_SITES FZ_CALLS.
Hypothesis C_EC : err_clear_steady_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis EXITP : EXIT_stmt RT libenv errst_at_rest FZ_SITES FZ_CALLS LIB REST.

Local Notation w7a := (w7a RT).
Local Notation w7_com := (w7_com RT libenv FZ_SITES FZ_CALLS REST).
Local Notation w7_at := (w7_at RT LIB).
Local Notation w7_cs := (w7_cs RT).
Local Notation P5 x := (x RT libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation P6 x := (x RT AF libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation P7 x := (x RT AF GOBJ AFP libenv FZ_SITES FZ_CALLS REST) (only parsing).
Local Notation PC x := (x RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS REST REST_fp REST_agree REST_fp_where) (only parsing).
Local Notation PCE x := (x RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where errst_at_rest errst_live FZ_SITES FZ_CALLS REST REST_fp REST_agree REST_fp_where) (only parsing).

(* [comment removed for export] *)
Definition F7_stmt : Prop :=
  forall (en : w7a) Σ m crem K BI len max off strs top bot news (NM HD DT : Z) (lowc : list cell) (F : bvmap 5 word) (fc : bv 32)
         (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  w7_com en Σ m crem (mbio_ent K max ++ strs ++ news) -> mbio_rep (rt_live RT Σ) m K BI M_MEM len max off ->
  errst_live (a_E RT en) top bot strs m -> (length strs <= 2)%nat -> Forall (fun e => 0 < snd e <= 64) strs ->
  ((news = [] /\ NM = 0 /\ HD = 0 /\ DT = 0) \/ (exists nn nh dlen, news = [(DT, dlen); (HD, nh); (NM, nn)] /\ 1 <= nn /\ 1 <= nh /\ 1 <= dlen)) ->
  rw_cells asegs m (a_f RT en + 32) [C8 (wz NM)] -> rw_cells asegs m (a_f RT en + 64) [C8 (wz HD)] -> rw_cells asegs m (a_f RT en + 96) [C8 (wz DT)] ->
  rw_cells asegs m (a_SP RT en + -160) lowc -> Z.of_nat (cells_size lowc) = 56 -> rw_cells asegs m (a_sp1 RT en + 24) [C8 (wz (a_f RT en + 64))] ->
  2 <= crem -> 2 <= a_len RT en ->
  w7_at en Σ (MS (w7_regs ra (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (a_f RT en + 96)) t3 t4 t5 t6 (a_d RT en) BI (a_f RT en) (a_pd RT en))
              F (wz J_w7_fpart) fc None m (seg_rom asegs)).

Theorem F7_proof : F7_stmt.
Proof.
  intros en Σ m crem K BI len max off strs top bot news NM HD DT lowc F fc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
         COM MBK EL LS2 S64 NEWS CN CH CD LOWC LSZ H24 CRM LEN2. unfold w7_at, cps. intros T c HA Hk.
  pose proof COM as (ART0 & MI & ST & GAP & PD & PDM & TOP & LOW & LOR & HLOS & CLE & SEC & LE & INCL & INE & NLE & RST & PERM & CFR & ND & LPOS & FRS & SP0 & CG & LIV & CLM & CR & CR0 & CRE
    & CGH & CGS & FPI & RAF & CURL & F0 & F64 & FTOP & FSH & FSJ & FHD & SAVED & PRES & PAY & PAYIN & LEN & FDO & MST).
  destruct (P5 w7_lists en Σ m crem _ COM) as (CLV & CLL & DLV).
  destruct (P7 w7_fframe_facts en Σ m crem _ COM) as (INF & FLO & FSEG & FSHR & FLV & SH1 & SH2 & SH8).
  assert (HLO : a_lo RT en <= a_SP RT en - 176) by (clear - LOR PD; unfold RT_STACK, W7_CALLEE_STACK, a_sp1 in *; lia).
  assert (SPH : a_SP RT en <= 2 ^ 47) by (clear - TOP; unfold USTACK_TOP in *; lia).
  (* [comment removed for export] *)
  destruct PAYIN as [EBS0|(p & n & HinD & P1 & P2)]; [exfalso; unfold a_len in LEN2; rewrite EBS0 in LEN2; cbn in LEN2; clear - LEN2; lia|].
  destruct (a_bs RT en) as [|b0 bsr] eqn:EBS; [unfold a_len in LEN2; rewrite EBS in LEN2; cbn in LEN2; clear - LEN2; lia|].
  unfold a_len in P2. rewrite EBS in P2. cbn [length] in P2.
  pose proof (af_live_range RT AF Σ m p n ART0 (DLV _ HinD)) as (Q0 & Q1 & _). destruct (af_acc_live RT AF Σ m p n ART0 (DLV _ HinD)) as [_ ACC].
  pose proof (w7_f0_walk ra (a_sp RT en) (a_gp RT en) (wz TP_A) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 b0 bsr F fc m (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) p n NM
                F0 FLO HLO HLOS SPH Q0 P1 ltac:(clear - P2; lia) ltac:(clear - Q1 LOW; lia) ACC PAY CN MI) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & -> & Hc1'). clear Hc1 HA.
  remember (Z.odd (bv_unsigned b0)) as sec eqn:ESEC in Hc1'. clear ESEC. cbv beta in Hc1'.
  (* [comment removed for export] *)
  assert (KEEP0 : forall Σa Σb (ma mb : mem) cra cura Ka BMa blwa lena maxa offa NMa HDa DTa,
    w7_com en Σa ma cra cura -> rt_pres_fp (rt_live RT Σb) (rt_frames RT Σ) (a_sp1 RT en) [] ma mb ->
    (forall e, In e (mbio_ent Ka maxa ++ strs ++ a_CL RT en) -> In e (rt_live RT Σb)) ->
    mbio_repx (rt_live RT Σa) ma Ka BI BMa blwa M_MEM lena maxa offa -> errst_live (a_E RT en) top bot strs ma ->
    rw_cells asegs ma (a_f RT en + 32) [C8 (wz NMa)] -> rw_cells asegs ma (a_f RT en + 64) [C8 (wz HDa)] -> rw_cells asegs ma (a_f RT en + 96) [C8 (wz DTa)] ->
    rw_cells asegs ma (a_SP RT en + -160) lowc -> rw_cells asegs ma (a_sp1 RT en + 24) [C8 (wz (a_f RT en + 64))] ->
       mbio_repx (rt_live RT Σb) mb Ka BI BMa blwa M_MEM lena maxa offa /\ errst_live (a_E RT en) top bot strs mb
    /\ rw_cells asegs mb (a_f RT en + 32) [C8 (wz NMa)] /\ rw_cells asegs mb (a_f RT en + 64) [C8 (wz HDa)] /\ rw_cells asegs mb (a_f RT en + 96) [C8 (wz DTa)]
    /\ rw_cells asegs mb (a_SP RT en + -160) lowc /\ rw_cells asegs mb (a_sp1 RT en + 24) [C8 (wz (a_f RT en + 64))]).
  { intros Σa Σb ma mb cra cura Ka BMa blwa lena maxa offa NMa HDa DTa COMa PR KIN MBXa ELa CNa CHa CDa LOWa H24a.
    split; [eapply (mbio_repx_keep (rt_live RT Σa)); [exact MBXa| exact PR| intros e He; split; apply KIN; apply in_or_app; left; exact He| intros e x _ _; exact I]|].
    split; [eapply (elive_keep errst_live errst_fp errst_live_agree errst_fp_where); [exact ELa| exact PR| apply KIN; apply in_or_app; right; apply in_or_app; right; exact INE
            | intros e He; apply KIN; apply in_or_app; right; apply in_or_app; left; exact He| intros x _; exact I| intros e x _ _; exact I]|].
    split; [eapply ff2_keep; [exact CNa| exact PR| exact INF| clear; lia| cbn [cells_size csize Nat.add]; clear; lia| intros x _; exact I]|].
    split; [eapply ff2_keep; [exact CHa| exact PR| exact INF| clear; lia| cbn [cells_size csize Nat.add]; clear; lia| intros x _; exact I]|].
    split; [eapply ff2_keep; [exact CDa| exact PR| exact INF| clear; lia| cbn [cells_size csize Nat.add]; clear; lia| intros x _; exact I]|].
    split; [eapply stack_keep; [exact LOWa| exact PR| unfold a_sp1; clear - PD; lia| rewrite LSZ; clear - TOP; unfold USTACK_TOP in *; lia| intros x _; exact I]|].
    eapply stack_keep; [exact H24a| exact PR| clear; lia| cbn [cells_size csize Nat.add]; unfold a_sp1; clear - TOP PD; unfold USTACK_TOP in *; lia| intros x _; exact I]. }
  destruct MBK as [BM0 MBX].
  destruct sec.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (TAILK : forall Σ5 (m5 : mem) cr5 (F5 : bvmap 5 word) (fc5 : bv 32) (z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 : word) c5,
      w7_com en Σ5 m5 cr5 (mbio_ent K max ++ strs) -> 2 <= cr5 ->
      mbio_repx (rt_live RT Σ5) m5 K BI BM0 (wz len) M_MEM len max off -> errst_live (a_E RT en) top bot strs m5 -> rw_cells asegs m5 (a_SP RT en + -160) lowc ->
      ASTA RT Σ5 (a_PMc RT en) (eq (MS (w7_regsF (wz SITE_w7_sfree3) (a_sp RT en) (a_gp RT en) (wz TP_A) z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 (wz (a_f RT en + 96)) z3 z4 z5 z6
                                                  (a_d RT en) BI (a_f RT en) (a_pd RT en)) F5 (wz SITE_w7_sfree3) fc5 None m5 (seg_rom asegs))) c5 ->
      realizes asegs c5 T).
    { intros Σ5 m5 cr5 F5 fc5 z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 c5 COM5 CR5 MBX5 EL5 LOW5 Hc5. cbv beta delta [Fz_W7_calls.w7_cs] in Hc5.
      pose proof COM5 as (_ & MI5 & _).
      pose proof (w7_f3_walk true (a_sp RT en) (a_gp RT en) (wz TP_A) z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 F5 fc5 m5 (a_d RT en) BI (a_f RT en) (a_pd RT en) MI5) as W.
      cl_lift W Hc5 c6 Hc6. destruct (ASTA_unpack RT Σ5 _ _ c6 Hc6) as (ms6 & -> & Hc6'). clear Hc6 Hc5.
      eapply (PC w7c_bfree C_BF T en Σ5 m5 cr5 strs K BI BM0 (wz len) len max off F5 fc5 z0 z1 z2 g1 g2 g3 g4 g5 g6 g7 _ _ _ _ _ _ _ _ _ _ _ z3 z4 z5 z6 c6 COM5 MBX5 ltac:(clear - CR5; lia) Hc6').
      clear Hc6'. intros Σ6 m6 F6 fc6 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c7 COM6 LV6 FRS6 PR6 KP6 Hc7.
      assert (EL6 : errst_live (a_E RT en) top bot strs m6).
      { eapply (elive_keep errst_live errst_fp errst_live_agree errst_fp_where); [exact EL5| exact PR6| apply KP6; apply in_or_app; right; apply in_or_app; left; exact INE
          | intros e He; apply KP6; apply in_or_app; left; exact He| |].
        - intros x Hx. apply (P7 w7_out_libW en Σ5 m5 cr5 _ x COM5). do 3 right. exact Hx.
        - intros e x He Hx. apply (P7 w7_out_libW en Σ5 m5 cr5 _ x COM5). left. exists (fst e), (snd e). split; [apply in_or_app; right; destruct e; exact He| exact Hx]. }
      assert (LOW6 : rw_cells asegs m6 (a_SP RT en + -160) lowc).
      { eapply stack_keep; [exact LOW5| exact PR6| unfold a_sp1; clear - PD; lia| rewrite LSZ; clear - TOP; unfold USTACK_TOP in *; lia|].
        intros x Hx. apply (P7 w7_out_libW en Σ5 m5 cr5 _ x COM5). do 2 right; left. rewrite LSZ in Hx. unfold a_sp1. clear - Hx PD TOP. unfold USTACK_TOP in *. lia. }
      pose proof COM6 as (_ & MI6 & _).
      pose proof (w7_b_walk (a_sp RT en) (a_gp RT en) (wz TP_A) y0 y1 y2 (wz 1) b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F6 fc6 m6 (a_d RT en) BI (a_f RT en) (a_pd RT en) MI6) as W.
      cl_lift W Hc7 c8 Hc8. destruct (ASTA_unpack RT Σ6 _ _ c8 Hc8) as (ms8 & -> & Hc8'). clear Hc8 Hc7.
      rewrite <- (app_nil_r strs) in COM6.
      eapply (PCE w7c_eclear C_EC T en Σ6 m6 (cr5 - 1) strs [] top bot F6 fc6 y0 y1 y2 (wz 1) b1 b2 b3 b4 b5 b6 b7 _ _ _ _ _ _ _ _ _ _ _ y3 y4 y5 y6 c8 COM6 EL6 ltac:(clear - CR5; lia) Hc8').
      clear Hc8'. intros Σ7 m7 F7 fc7 v z0' z1' z2' d1 d2 d3 d4 d5 d6 d7 z3' z4' z5' z6' c9 COM7 REST7 LV7 FRS7 PR7 KP7 Hc9.
      assert (LOW7 : rw_cells asegs m7 (a_SP RT en + -160) lowc).
      { eapply stack_keep; [exact LOW6| exact PR7| unfold a_sp1; clear - PD; lia| rewrite LSZ; clear - TOP; unfold USTACK_TOP in *; lia|].
        intros x Hx. rewrite LSZ in Hx. cbn [outside]. split; [apply (P7 w7_out_E en Σ6 m6 (cr5 - 1) _ x COM6)| apply (P7 w7_out_libW en Σ6 m6 (cr5 - 1) _ x COM6)]; do 2 right; [| left];
          unfold a_sp1; clear - Hx PD TOP; unfold USTACK_TOP in *; lia. }
      destruct (rw_cells_forget asegs m7 _ _ LOW7) as (lowj & LOW7'). replace (cells_size lowc) with 56%nat in LOW7' by (clear - LSZ; lia).
      exact (EXITP en Σ7 m7 (cr5 - 1 - 1) F7 fc7 (wz J_w7_exit) z0' z1' z2' v d1 d2 d3 d4 d5 d6 d7 (wz W7_FILE) (wz BI) (wz (a_d RT en / 8 + 2147450880)) (wz (a_f RT en + 32)) (wz (a_f RT en + 128)) (wz (a_f RT en + 96))
               z3' z4' z5' z6' lowj COM7 REST7 LOW7' T c9 Hc9 Hk). }
    assert (KIN0 : forall e, In e (mbio_ent K max ++ strs ++ a_CL RT en) -> In e (rt_live RT Σ)).
    { intros e He. apply in_app_iff in He. destruct He as [He|He]; [apply CLV; apply in_or_app; left; exact He|].
      apply in_app_iff in He. destruct He as [He|He]; [apply CLV; apply in_or_app; right; apply in_or_app; left; exact He| exact (CLL _ He)]. }
    destruct NEWS as [(EN & EN1 & EN2 & EN3)|(nn & nh & dlen & EN & NN & NH & DL)]; subst news.
    + (* [comment removed for export] *)
      subst NM HD DT. rewrite app_nil_r in COM.
      eapply (PC w7c_sfreen T en Σ m crem _ SITE_w7_sfree1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ COM ltac:(unfold SITE_w7_sfree1; clear; lia) eq_refl Hc1').
      clear Hc1'. intros m2 c2 COM2 PR2 Hc2. cbv beta delta [Fz_W7_calls.w7_cs] in Hc2. 
      destruct (KEEP0 Σ Σ m m2 crem _ K BM0 (wz len) len max off 0 0 0 COM PR2 KIN0 MBX EL CN CH CD LOWC H24) as (MBX2 & EL2 & CN2 & CH2 & CD2 & LOW2 & H242).
      pose proof COM2 as (_ & MI2 & _).
      lazymatch type of Hc2 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        pose proof (w7_f1g_walk true (a_sp RT en) (a_gp RT en) (wz TP_A) x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 FF ffc m2 (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) 0
                      PD F0 FLO HLO HLOS SPH H242 CH2 MI2) as W end.
      cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3 Hc2. cbv beta in Hc3'.
      eapply (PC w7c_sfreen T en Σ m2 crem _ SITE_w7_sfree2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ COM2 ltac:(unfold SITE_w7_sfree2; clear; lia) eq_refl Hc3').
      clear Hc3'. intros m4 c4 COM4 PR4 Hc4. cbv beta delta [Fz_W7_calls.w7_cs] in Hc4. 
      destruct (KEEP0 Σ Σ m2 m4 crem _ K BM0 (wz len) len max off 0 0 0 COM2 PR4 KIN0 MBX2 EL2 CN2 CH2 CD2 LOW2 H242) as (MBX4 & EL4 & CN4 & CH4 & CD4 & LOW4 & H244).
      pose proof COM4 as (_ & MI4 & _).
      lazymatch type of Hc4 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        pose proof (w7_f2_walk true (a_sp RT en) (a_gp RT en) (wz TP_A) x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 FF ffc m4 (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) 0
                      F0 FLO HLO HLOS SPH CD4 MI4) as W end.
      cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5 Hc4. cbv beta in Hc5'.
      eapply (PC w7c_sfreen T en Σ m4 crem _ SITE_w7_sfree3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ COM4 ltac:(unfold SITE_w7_sfree3; clear; lia) eq_refl Hc5').
      clear Hc5'. intros m6 c6 COM6 PR6 Hc6. cbv beta delta [Fz_W7_calls.w7_cs] in Hc6. 
      destruct (KEEP0 Σ Σ m4 m6 crem _ K BM0 (wz len) len max off 0 0 0 COM4 PR6 KIN0 MBX4 EL4 CN4 CH4 CD4 LOW4 H244) as (MBX6 & EL6 & _ & _ & _ & LOW6 & _).
      lazymatch type of Hc6 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        exact (TAILK Σ m6 crem FF ffc x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 c6 COM6 CRM MBX6 EL6 LOW6 Hc6) end.
    + (* [comment removed for export] *)
      assert (HPM1 : Permutation (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh); (NM, nn)]) ((NM, nn) :: (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh)]))).
      { apply Permutation_sym. rewrite (app_assoc (mbio_ent K max) strs [(DT, dlen); (HD, nh)]), (app_assoc (mbio_ent K max) strs [(DT, dlen); (HD, nh); (NM, nn)]).
        change ((mbio_ent K max ++ strs) ++ [(DT, dlen); (HD, nh); (NM, nn)]) with ((mbio_ent K max ++ strs) ++ ([(DT, dlen); (HD, nh)] ++ [(NM, nn)])).
        rewrite (app_assoc (mbio_ent K max ++ strs) [(DT, dlen); (HD, nh)] [(NM, nn)]). apply Permutation_cons_append. }
      eapply (PC w7c_sfree C_SF T en Σ m crem (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh)]) NM nn SITE_w7_sfree1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P5 w7_perm en Σ m crem _ _ COM HPM1) NN ltac:(unfold W7_SITES_OWN; cbn [map]; do 13 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 13 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 4 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 7 right; left; reflexivity) ltac:(unfold SITE_w7_sfree1; clear; lia) eq_refl Hc1').
      clear Hc1'. intros Σ2 m2 F2 fc2 v2 u20 u21 u22 b21 b22 b23 b24 b25 b26 b27 u23 u24 u25 u26 c2 COM2 LV2 FRS2 PR2 KP2 Hc2. cbv beta delta [Fz_W7_calls.w7_cs] in Hc2.
      assert (KIN2 : forall e, In e (mbio_ent K max ++ strs ++ a_CL RT en) -> In e (rt_live RT Σ2)).
      { intros e He. apply KP2. apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; left; exact He|].
        apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact He| apply in_or_app; right; apply in_or_app; left; exact He]. }
      destruct (KEEP0 Σ Σ2 m m2 crem _ K BM0 (wz len) len max off NM HD DT COM PR2 KIN2 MBX EL CN CH CD LOWC H24) as (MBX2 & EL2 & CN2 & CH2 & CD2 & LOW2 & H242).
      pose proof COM2 as (_ & MI2 & _).
      lazymatch type of Hc2 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        pose proof (w7_f1g_walk true (a_sp RT en) (a_gp RT en) (wz TP_A) x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 FF ffc m2 (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) HD
                      PD F0 FLO HLO HLOS SPH H242 CH2 MI2) as W end.
      cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3 Hc2. cbv beta in Hc3'.
      assert (HPM2 : Permutation (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh)]) ((HD, nh) :: (mbio_ent K max ++ strs ++ [(DT, dlen)]))).
      { apply Permutation_sym. rewrite (app_assoc (mbio_ent K max) strs [(DT, dlen)]), (app_assoc (mbio_ent K max) strs [(DT, dlen); (HD, nh)]).
        change ((mbio_ent K max ++ strs) ++ [(DT, dlen); (HD, nh)]) with ((mbio_ent K max ++ strs) ++ ([(DT, dlen)] ++ [(HD, nh)])).
        rewrite (app_assoc (mbio_ent K max ++ strs) [(DT, dlen)] [(HD, nh)]). apply Permutation_cons_append. }
      eapply (PC w7c_sfree C_SF T en Σ2 m2 crem (mbio_ent K max ++ strs ++ [(DT, dlen)]) HD nh SITE_w7_sfree2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P5 w7_perm en Σ2 m2 crem _ _ COM2 HPM2) NH ltac:(unfold W7_SITES_OWN; cbn [map]; do 14 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 14 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 5 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 8 right; left; reflexivity) ltac:(unfold SITE_w7_sfree2; clear; lia) eq_refl Hc3').
      clear Hc3'. intros Σ4 m4 F4 fc4 v4 u40 u41 u42 b41 b42 b43 b44 b45 b46 b47 u43 u44 u45 u46 c4 COM4 LV4 FRS4 PR4 KP4 Hc4. cbv beta delta [Fz_W7_calls.w7_cs] in Hc4.
      rewrite FRS2 in PR4, FRS4.
      assert (KIN4 : forall e, In e (mbio_ent K max ++ strs ++ a_CL RT en) -> In e (rt_live RT Σ4)).
      { intros e He. apply KP4. apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; left; exact He|].
        apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact He| apply in_or_app; right; apply in_or_app; left; exact He]. }
      destruct (KEEP0 Σ2 Σ4 m2 m4 crem _ K BM0 (wz len) len max off NM HD DT COM2 PR4 KIN4 MBX2 EL2 CN2 CH2 CD2 LOW2 H242) as (MBX4 & EL4 & CN4 & CH4 & CD4 & LOW4 & H244).
      pose proof COM4 as (_ & MI4 & _).
      lazymatch type of Hc4 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        pose proof (w7_f2_walk true (a_sp RT en) (a_gp RT en) (wz TP_A) x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 FF ffc m4 (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) DT
                      F0 FLO HLO HLOS SPH CD4 MI4) as W end.
      cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ4 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5 Hc4. cbv beta in Hc5'.
      assert (HPM3 : Permutation (mbio_ent K max ++ strs ++ [(DT, dlen)]) ((DT, dlen) :: (mbio_ent K max ++ strs))).
      { apply Permutation_sym. rewrite (app_assoc (mbio_ent K max) strs [(DT, dlen)]). apply Permutation_cons_append. }
      eapply (PC w7c_sfree C_SF T en Σ4 m4 crem (mbio_ent K max ++ strs) DT dlen SITE_w7_sfree3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P5 w7_perm en Σ4 m4 crem _ _ COM4 HPM3) DL ltac:(unfold W7_SITES_OWN; cbn [map]; do 15 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 15 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 6 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 9 right; left; reflexivity) ltac:(unfold SITE_w7_sfree3; clear; lia) eq_refl Hc5').
      clear Hc5'. intros Σ6 m6 F6 fc6 v6 u60 u61 u62 b61 b62 b63 b64 b65 b66 b67 u63 u64 u65 u66 c6 COM6 LV6 FRS6 PR6 KP6 Hc6. cbv beta delta [Fz_W7_calls.w7_cs] in Hc6.
      rewrite FRS4 in PR6, FRS6.
      assert (KIN6 : forall e, In e (mbio_ent K max ++ strs ++ a_CL RT en) -> In e (rt_live RT Σ6)).
      { intros e He. apply KP6. apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; left; exact He|].
        apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; right; exact He| apply in_or_app; right; apply in_or_app; left; exact He]. }
      destruct (KEEP0 Σ4 Σ6 m4 m6 crem _ K BM0 (wz len) len max off NM HD DT COM4 PR6 KIN6 MBX4 EL4 CN4 CH4 CD4 LOW4 H244) as (MBX6 & EL6 & _ & _ & _ & LOW6 & _).
      lazymatch type of Hc6 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        exact (TAILK Σ6 m6 crem FF ffc x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 c6 COM6 CRM MBX6 EL6 LOW6 Hc6) end.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (TAILK : forall Σ5 (m5 : mem) cr5 (F5 : bvmap 5 word) (fc5 : bv 32) (z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 : word) c5,
      w7_com en Σ5 m5 cr5 (mbio_ent K max ++ strs) -> 2 <= cr5 ->
      mbio_repx (rt_live RT Σ5) m5 K BI BM0 (wz len) M_MEM len max off -> errst_live (a_E RT en) top bot strs m5 -> rw_cells asegs m5 (a_SP RT en + -160) lowc ->
      ASTA RT Σ5 (a_PMc RT en) (eq (MS (w7_regsF (wz SITE_w7_free3) (a_sp RT en) (a_gp RT en) (wz TP_A) z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 (wz (a_f RT en + 96)) z3 z4 z5 z6
                                                  (a_d RT en) BI (a_f RT en) (a_pd RT en)) F5 (wz SITE_w7_free3) fc5 None m5 (seg_rom asegs))) c5 ->
      realizes asegs c5 T).
    { intros Σ5 m5 cr5 F5 fc5 z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 c5 COM5 CR5 MBX5 EL5 LOW5 Hc5. cbv beta delta [Fz_W7_calls.w7_cs] in Hc5.
      pose proof COM5 as (_ & MI5 & _).
      pose proof (w7_f3_walk false (a_sp RT en) (a_gp RT en) (wz TP_A) z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 F5 fc5 m5 (a_d RT en) BI (a_f RT en) (a_pd RT en) MI5) as W.
      cl_lift W Hc5 c6 Hc6. destruct (ASTA_unpack RT Σ5 _ _ c6 Hc6) as (ms6 & -> & Hc6'). clear Hc6 Hc5.
      eapply (PC w7c_bfree C_BF T en Σ5 m5 cr5 strs K BI BM0 (wz len) len max off F5 fc5 z0 z1 z2 g1 g2 g3 g4 g5 g6 g7 _ _ _ _ _ _ _ _ _ _ _ z3 z4 z5 z6 c6 COM5 MBX5 ltac:(clear - CR5; lia) Hc6').
      clear Hc6'. intros Σ6 m6 F6 fc6 y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 c7 COM6 LV6 FRS6 PR6 KP6 Hc7.
      assert (EL6 : errst_live (a_E RT en) top bot strs m6).
      { eapply (elive_keep errst_live errst_fp errst_live_agree errst_fp_where); [exact EL5| exact PR6| apply KP6; apply in_or_app; right; apply in_or_app; left; exact INE
          | intros e He; apply KP6; apply in_or_app; left; exact He| |].
        - intros x Hx. apply (P7 w7_out_libW en Σ5 m5 cr5 _ x COM5). do 3 right. exact Hx.
        - intros e x He Hx. apply (P7 w7_out_libW en Σ5 m5 cr5 _ x COM5). left. exists (fst e), (snd e). split; [apply in_or_app; right; destruct e; exact He| exact Hx]. }
      assert (LOW6 : rw_cells asegs m6 (a_SP RT en + -160) lowc).
      { eapply stack_keep; [exact LOW5| exact PR6| unfold a_sp1; clear - PD; lia| rewrite LSZ; clear - TOP; unfold USTACK_TOP in *; lia|].
        intros x Hx. apply (P7 w7_out_libW en Σ5 m5 cr5 _ x COM5). do 2 right; left. rewrite LSZ in Hx. unfold a_sp1. clear - Hx PD TOP. unfold USTACK_TOP in *. lia. }
      pose proof COM6 as (_ & MI6 & _).
      pose proof (w7_b_walk (a_sp RT en) (a_gp RT en) (wz TP_A) y0 y1 y2 (wz 1) b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F6 fc6 m6 (a_d RT en) BI (a_f RT en) (a_pd RT en) MI6) as W.
      cl_lift W Hc7 c8 Hc8. destruct (ASTA_unpack RT Σ6 _ _ c8 Hc8) as (ms8 & -> & Hc8'). clear Hc8 Hc7.
      rewrite <- (app_nil_r strs) in COM6.
      eapply (PCE w7c_eclear C_EC T en Σ6 m6 (cr5 - 1) strs [] top bot F6 fc6 y0 y1 y2 (wz 1) b1 b2 b3 b4 b5 b6 b7 _ _ _ _ _ _ _ _ _ _ _ y3 y4 y5 y6 c8 COM6 EL6 ltac:(clear - CR5; lia) Hc8').
      clear Hc8'. intros Σ7 m7 F7 fc7 v z0' z1' z2' d1 d2 d3 d4 d5 d6 d7 z3' z4' z5' z6' c9 COM7 REST7 LV7 FRS7 PR7 KP7 Hc9.
      assert (LOW7 : rw_cells asegs m7 (a_SP RT en + -160) lowc).
      { eapply stack_keep; [exact LOW6| exact PR7| unfold a_sp1; clear - PD; lia| rewrite LSZ; clear - TOP; unfold USTACK_TOP in *; lia|].
        intros x Hx. rewrite LSZ in Hx. cbn [outside]. split; [apply (P7 w7_out_E en Σ6 m6 (cr5 - 1) _ x COM6)| apply (P7 w7_out_libW en Σ6 m6 (cr5 - 1) _ x COM6)]; do 2 right; [| left];
          unfold a_sp1; clear - Hx PD TOP; unfold USTACK_TOP in *; lia. }
      destruct (rw_cells_forget asegs m7 _ _ LOW7) as (lowj & LOW7'). replace (cells_size lowc) with 56%nat in LOW7' by (clear - LSZ; lia).
      exact (EXITP en Σ7 m7 (cr5 - 1 - 1) F7 fc7 (wz J_w7_exit) z0' z1' z2' v d1 d2 d3 d4 d5 d6 d7 (wz W7_FILE) (wz BI) (wz (a_d RT en / 8 + 2147450880)) (wz (a_f RT en + 32)) (wz (a_f RT en + 128)) (wz (a_f RT en + 96))
               z3' z4' z5' z6' lowj COM7 REST7 LOW7' T c9 Hc9 Hk). }
    assert (KIN0 : forall e, In e (mbio_ent K max ++ strs ++ a_CL RT en) -> In e (rt_live RT Σ)).
    { intros e He. apply in_app_iff in He. destruct He as [He|He]; [apply CLV; apply in_or_app; left; exact He|].
      apply in_app_iff in He. destruct He as [He|He]; [apply CLV; apply in_or_app; right; apply in_or_app; left; exact He| exact (CLL _ He)]. }
    destruct NEWS as [(EN & EN1 & EN2 & EN3)|(nn & nh & dlen & EN & NN & NH & DL)]; subst news.
    + (* [comment removed for export] *)
      subst NM HD DT. rewrite app_nil_r in COM.
      eapply (PC w7c_freen C_FN T en Σ m crem _ SITE_w7_free1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ COM ltac:(unfold W7_SITES_OWN; cbn [map]; do 10 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 10 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 1 right; left; reflexivity) ltac:(unfold SITE_w7_free1; clear; lia) eq_refl Hc1').
      clear Hc1'. intros m2 F2 fc2 v2 u20 u21 u22 b21 b22 b23 b24 b25 b26 b27 u23 u24 u25 u26 c2 COM2 PR2 Hc2. cbv beta delta [Fz_W7_calls.w7_cs] in Hc2.
      destruct (KEEP0 Σ Σ m m2 crem _ K BM0 (wz len) len max off 0 0 0 COM PR2 KIN0 MBX EL CN CH CD LOWC H24) as (MBX2 & EL2 & CN2 & CH2 & CD2 & LOW2 & H242).
      pose proof COM2 as (_ & MI2 & _).
      lazymatch type of Hc2 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        pose proof (w7_f1g_walk false (a_sp RT en) (a_gp RT en) (wz TP_A) x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 FF ffc m2 (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) 0
                      PD F0 FLO HLO HLOS SPH H242 CH2 MI2) as W end.
      cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3 Hc2. cbv beta in Hc3'.
      eapply (PC w7c_freen C_FN T en Σ m2 crem _ SITE_w7_free2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ COM2 ltac:(unfold W7_SITES_OWN; cbn [map]; do 11 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 11 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 2 right; left; reflexivity) ltac:(unfold SITE_w7_free2; clear; lia) eq_refl Hc3').
      clear Hc3'. intros m4 F4 fc4 v4 u40 u41 u42 b41 b42 b43 b44 b45 b46 b47 u43 u44 u45 u46 c4 COM4 PR4 Hc4. cbv beta delta [Fz_W7_calls.w7_cs] in Hc4.
      destruct (KEEP0 Σ Σ m2 m4 crem _ K BM0 (wz len) len max off 0 0 0 COM2 PR4 KIN0 MBX2 EL2 CN2 CH2 CD2 LOW2 H242) as (MBX4 & EL4 & CN4 & CH4 & CD4 & LOW4 & H244).
      pose proof COM4 as (_ & MI4 & _).
      lazymatch type of Hc4 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        pose proof (w7_f2_walk false (a_sp RT en) (a_gp RT en) (wz TP_A) x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 FF ffc m4 (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) 0
                      F0 FLO HLO HLOS SPH CD4 MI4) as W end.
      cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5 Hc4. cbv beta in Hc5'.
      eapply (PC w7c_freen C_FN T en Σ m4 crem _ SITE_w7_free3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ COM4 ltac:(unfold W7_SITES_OWN; cbn [map]; do 12 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 12 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 3 right; left; reflexivity) ltac:(unfold SITE_w7_free3; clear; lia) eq_refl Hc5').
      clear Hc5'. intros m6 F6 fc6 v6 u60 u61 u62 b61 b62 b63 b64 b65 b66 b67 u63 u64 u65 u66 c6 COM6 PR6 Hc6. cbv beta delta [Fz_W7_calls.w7_cs] in Hc6.
      destruct (KEEP0 Σ Σ m4 m6 crem _ K BM0 (wz len) len max off 0 0 0 COM4 PR6 KIN0 MBX4 EL4 CN4 CH4 CD4 LOW4 H244) as (MBX6 & EL6 & _ & _ & _ & LOW6 & _).
      lazymatch type of Hc6 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        exact (TAILK Σ m6 crem FF ffc x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 c6 COM6 CRM MBX6 EL6 LOW6 Hc6) end.
    + (* [comment removed for export] *)
      assert (HPM1 : Permutation (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh); (NM, nn)]) ((NM, nn) :: (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh)]))).
      { apply Permutation_sym. rewrite (app_assoc (mbio_ent K max) strs [(DT, dlen); (HD, nh)]), (app_assoc (mbio_ent K max) strs [(DT, dlen); (HD, nh); (NM, nn)]).
        change ((mbio_ent K max ++ strs) ++ [(DT, dlen); (HD, nh); (NM, nn)]) with ((mbio_ent K max ++ strs) ++ ([(DT, dlen); (HD, nh)] ++ [(NM, nn)])).
        rewrite (app_assoc (mbio_ent K max ++ strs) [(DT, dlen); (HD, nh)] [(NM, nn)]). apply Permutation_cons_append. }
      eapply (PC w7c_free C_FR T en Σ m crem (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh)]) NM nn SITE_w7_free1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P5 w7_perm en Σ m crem _ _ COM HPM1) ltac:(unfold W7_SITES_OWN; cbn [map]; do 10 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 10 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 1 right; left; reflexivity) ltac:(unfold SITE_w7_free1; clear; lia) eq_refl Hc1').
      clear Hc1'. intros Σ2 m2 F2 fc2 v2 u20 u21 u22 b21 b22 b23 b24 b25 b26 b27 u23 u24 u25 u26 c2 COM2 LV2 FRS2 PR2 KP2 Hc2. cbv beta delta [Fz_W7_calls.w7_cs] in Hc2.
      assert (KIN2 : forall e, In e (mbio_ent K max ++ strs ++ a_CL RT en) -> In e (rt_live RT Σ2)).
      { intros e He. apply KP2. apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; left; exact He|].
        apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact He| apply in_or_app; right; apply in_or_app; left; exact He]. }
      destruct (KEEP0 Σ Σ2 m m2 crem _ K BM0 (wz len) len max off NM HD DT COM PR2 KIN2 MBX EL CN CH CD LOWC H24) as (MBX2 & EL2 & CN2 & CH2 & CD2 & LOW2 & H242).
      pose proof COM2 as (_ & MI2 & _).
      lazymatch type of Hc2 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        pose proof (w7_f1g_walk false (a_sp RT en) (a_gp RT en) (wz TP_A) x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 FF ffc m2 (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) HD
                      PD F0 FLO HLO HLOS SPH H242 CH2 MI2) as W end.
      cl_lift W Hc2 c3 Hc3. destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & -> & Hc3'). clear Hc3 Hc2. cbv beta in Hc3'.
      assert (HPM2 : Permutation (mbio_ent K max ++ strs ++ [(DT, dlen); (HD, nh)]) ((HD, nh) :: (mbio_ent K max ++ strs ++ [(DT, dlen)]))).
      { apply Permutation_sym. rewrite (app_assoc (mbio_ent K max) strs [(DT, dlen)]), (app_assoc (mbio_ent K max) strs [(DT, dlen); (HD, nh)]).
        change ((mbio_ent K max ++ strs) ++ [(DT, dlen); (HD, nh)]) with ((mbio_ent K max ++ strs) ++ ([(DT, dlen)] ++ [(HD, nh)])).
        rewrite (app_assoc (mbio_ent K max ++ strs) [(DT, dlen)] [(HD, nh)]). apply Permutation_cons_append. }
      eapply (PC w7c_free C_FR T en Σ2 m2 crem (mbio_ent K max ++ strs ++ [(DT, dlen)]) HD nh SITE_w7_free2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P5 w7_perm en Σ2 m2 crem _ _ COM2 HPM2) ltac:(unfold W7_SITES_OWN; cbn [map]; do 11 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 11 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 2 right; left; reflexivity) ltac:(unfold SITE_w7_free2; clear; lia) eq_refl Hc3').
      clear Hc3'. intros Σ4 m4 F4 fc4 v4 u40 u41 u42 b41 b42 b43 b44 b45 b46 b47 u43 u44 u45 u46 c4 COM4 LV4 FRS4 PR4 KP4 Hc4. cbv beta delta [Fz_W7_calls.w7_cs] in Hc4.
      rewrite FRS2 in PR4, FRS4.
      assert (KIN4 : forall e, In e (mbio_ent K max ++ strs ++ a_CL RT en) -> In e (rt_live RT Σ4)).
      { intros e He. apply KP4. apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; left; exact He|].
        apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact He| apply in_or_app; right; apply in_or_app; left; exact He]. }
      destruct (KEEP0 Σ2 Σ4 m2 m4 crem _ K BM0 (wz len) len max off NM HD DT COM2 PR4 KIN4 MBX2 EL2 CN2 CH2 CD2 LOW2 H242) as (MBX4 & EL4 & CN4 & CH4 & CD4 & LOW4 & H244).
      pose proof COM4 as (_ & MI4 & _).
      lazymatch type of Hc4 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        pose proof (w7_f2_walk false (a_sp RT en) (a_gp RT en) (wz TP_A) x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 FF ffc m4 (a_d RT en) BI (a_f RT en) (a_lo RT en) (a_pd RT en) DT
                      F0 FLO HLO HLOS SPH CD4 MI4) as W end.
      cl_lift W Hc4 c5 Hc5. destruct (ASTA_unpack RT Σ4 _ _ c5 Hc5) as (ms5 & -> & Hc5'). clear Hc5 Hc4. cbv beta in Hc5'.
      assert (HPM3 : Permutation (mbio_ent K max ++ strs ++ [(DT, dlen)]) ((DT, dlen) :: (mbio_ent K max ++ strs))).
      { apply Permutation_sym. rewrite (app_assoc (mbio_ent K max) strs [(DT, dlen)]). apply Permutation_cons_append. }
      eapply (PC w7c_free C_FR T en Σ4 m4 crem (mbio_ent K max ++ strs) DT dlen SITE_w7_free3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (P5 w7_perm en Σ4 m4 crem _ _ COM4 HPM3) ltac:(unfold W7_SITES_OWN; cbn [map]; do 12 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_OWN; apply in_or_app; left; do 12 right; left; reflexivity) ltac:(unfold W7_CALLS_ALL, W7_CALLS_X; apply in_or_app; right; do 3 right; left; reflexivity) ltac:(unfold SITE_w7_free3; clear; lia) eq_refl Hc5').
      clear Hc5'. intros Σ6 m6 F6 fc6 v6 u60 u61 u62 b61 b62 b63 b64 b65 b66 b67 u63 u64 u65 u66 c6 COM6 LV6 FRS6 PR6 KP6 Hc6. cbv beta delta [Fz_W7_calls.w7_cs] in Hc6.
      rewrite FRS4 in PR6, FRS6.
      assert (KIN6 : forall e, In e (mbio_ent K max ++ strs ++ a_CL RT en) -> In e (rt_live RT Σ6)).
      { intros e He. apply KP6. apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; left; exact He|].
        apply in_app_iff in He. destruct He as [He|He]; [apply in_or_app; left; apply in_or_app; right; exact He| apply in_or_app; right; apply in_or_app; left; exact He]. }
      destruct (KEEP0 Σ4 Σ6 m4 m6 crem _ K BM0 (wz len) len max off NM HD DT COM4 PR6 KIN6 MBX4 EL4 CN4 CH4 CD4 LOW4 H244) as (MBX6 & EL6 & _ & _ & _ & LOW6 & _).
      lazymatch type of Hc6 with ASTA _ _ _ (eq (MS (mkR _ _ _ _ ?x0 ?x1 ?x2 _ _ ?y0 ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 _ _ _ _ _ _ _ _ _ _ ?x3 ?x4 ?x5 ?x6) ?FF _ ?ffc _ _ _)) _ =>
        exact (TAILK Σ6 m6 crem FF ffc x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 c6 COM6 CRM MBX6 EL6 LOW6 Hc6) end.
Qed.
End W7F.
