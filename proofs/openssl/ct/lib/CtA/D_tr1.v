(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Nodes RzCPS NodesA. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_clx D_libkit D_rlkit D_trpro D_trwalk D_atiface D_trdefs RT_client_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma tr_calls_range : forall L c0, 1 <= tr_calls L c0 <= 4.
Proof.
  intros L c0. unfold tr_calls. destruct (L =? 0); [lia|].
  change 3 with (Z.ones 2). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (bv_unsigned c0) (2^2) ltac:(lia)). lia.
Qed.

Section Tr1.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable XENV1 : mem -> Prop.
Variable XENV1_FP : list (Z * Z).
Variable LIBA : rts RT -> list (Z * Z) -> mem -> Prop.
Variable fs : Fs.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract_ok RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis ATX : atexit_contract RT XENV XENV1.
Hypothesis INIT : init_cps RT LIBA.
Hypothesis LFR : liba_frame RT LIBA.
Hypothesis LEX : liba_exit RT LIBA.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis XENV1_loc : fp_local XENV1_FP XENV1.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
Hypothesis XENV1_img : forall x, in_ranges XENV1_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.
(* [comment removed for export] *)
Hypothesis XENV_incb : forall m, XENV m -> incb 0 m.
Hypothesis INCB_off : forall x, TR_INIT + 1 <= x < TR_INIT + 5 -> outside IO_FP x /\ outside XENV1_FP x.
Hypothesis ATXW_off : forall x, in_ranges ATX_W x -> outside IO_FP x.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, FUZZ_STACK, FUZZ_COST, FUZZ_LIVE, INIT_STACK, INIT_COST, INIT_LIVE, LIVE_MAX, CREDIT_DRV, g_read_stage in *; lia.

(* [comment removed for export] *)
Definition TPRE (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (c0 c1 c2 c3 c4 c5 c6 c7 : word) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv ctasegs m /\ CLX OUT_rep ERR_rep XENV lib_startA stdout_init m /\ main_frame m usp c0 c1 c2 c3 c4 c5 c6 c7
  /\ stk ctasegs m (rt_sp0 RT Σ - STACK_WIN) (usp - 80)
  /\ usp mod 16 = 0 /\ rt_sp0 RT Σ - STACK_WIN + 0x100000 <= usp /\ usp <= rt_sp0 RT Σ /\ 0x7fff80000000 <= rt_sp0 RT Σ
  /\ rt_live RT Σ = [(buf, cap)] /\ rt_frames RT Σ = [] /\ CREDIT_DRV - 5 * cap <= rt_credit RT Σ /\ cap <= 67108864
  /\ buf <= cp /\ cp + 1 <= buf + cap /\ (0 < L -> bytes_at ctasegs m cp [c0b]) /\ 0 <= L < 32768
  /\ buf <= pp /\ pp + plen <= buf + cap /\ bytes_at ctasegs m pp payload /\ plen = Z.of_nat (length payload) /\ plen < 2^26
  /\ usp + 16 <= USTACK_TOP.

Lemma LIB_FP_range : forall x, in_ranges LIB_FP x -> 0x10000 <= x < SEGTOP_A.
Proof. intros x H. exact (client_static_range x (proj1 (LIB_img x H))). Qed.

Lemma LIB_FPE_outside_hi : forall x, SEGTOP_A <= x -> outside LIB_FPE x.
Proof. intros x Hx. unfold LIB_FPE, LIB_FP. cbn [outside]. unfold SEGTOP_A in Hx. repeat split; try exact I; lia. Qed.

(* [comment removed for export] *)
Lemma incb_static : forall x, TR_INIT + 1 <= x < TR_INIT + 5 -> client_static x.
Proof. intros x Hx. apply client_static_intro. unfold TR_INIT in Hx. lia. Qed.
Lemma incb_off_lib : forall x, TR_INIT + 1 <= x < TR_INIT + 5 -> outside LIB_FPE x.
Proof. intros x Hx. unfold LIB_FPE, LIB_FP. cbn [outside]. unfold TR_INIT in Hx. repeat split; try exact I; lia. Qed.

Theorem tr_start : forall (Σ : rts RT) (usp buf cap cp L pp plen : Z) (c0b : byte) (payload : list byte)
    (gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (c0 c1 c2 c3 c4 c5 c6 c7 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  TPRE Σ usp buf cap cp L pp plen c0b payload c0 c1 c2 c3 c4 c5 c6 c7 m ->
  cps ctasegs (ASTA RT Σ (PMfd fds0 fs)
               (eq (entry_st (Z_to_bv 64 0x1f3db8) (Z_to_bv 64 (usp - 80)) gp (Z_to_bv 64 TP_A) t0 t1 t2 x0 x1
                     (Z_to_bv 64 cp) (Z_to_bv 64 L) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11
                     t3 t4 t5 t6 F fc e_target_run m)))
    (TLOOP RT OUT_rep ERR_rep XENV1 LIBA fs (tr_calls L c0b) stdout_init usp buf cap x0 x1 x2 x3 x4 x5 x6 x7).
Proof using AF AF_DRV MAL MCP ATX INIT LFR LEX OUT_loc ERR_loc XENV_loc XENV1_loc IO_img XENV_img XENV1_img XENV_incb INCB_off ATXW_off.
  intros Σ usp buf cap cp L pp plen c0b payload gp t0 t1 t2 a4 a5 a6 a7 x0 x1 x2 x3 x4 x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6
    c0 c1 c2 c3 c4 c5 c6 c7 F fc m HP T c HA Hk.
  destruct HP as (ART0 & MI0 & CLX0 & FR0 & ST0 & B16 & ULO & USP0 & SPW & LV & FRS & CR & CAPB & Hcp1 & Hcp2 & HC0 & HL
                  & Hpp1 & Hpp2 & BP & PL & PB & UT0).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  assert (INB : In (buf, cap) (rt_live RT Σ)) by (rewrite LV; left; reflexivity).
  pose proof (af_live_range RT AF Σ m buf cap ART0 INB) as (PR1 & PR2 & PR3).
  pose proof (AF_DRV Σ m ART0) as (_ & _ & GI & _).
  pose proof CLX0 as (_ & _ & XE0 & (LP0 & LT0) & _).
  pose proof (tr_calls_range L c0b) as TCR.
  set (lo := rt_sp0 RT Σ - STACK_WIN) in *.
  assert (EU : bv_unsigned (Z_to_bv 64 (usp - 80)) = usp - 80) by (apply unsigned_lit; ul).
  assert (B16' : (usp - 80) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 5); lia).
  assert (B16'' : (usp - 160) mod 16 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in B16; [| lia]; destruct B16 as (q & ->); exists (q - 10); lia).
  assert (PLR : 0 <= plen) by lia.
  (* [comment removed for export] *)
  pose proof (tr_pro_atexit (usp - 80) cp L pp plen (Z_to_bv 64 0x1f3db8) gp t0 t1 t2 x0 x1 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7
                s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ST0 ltac:(ul) ltac:(ul) B16' ltac:(ul) ltac:(ul) HL ltac:(ul) ltac:(lia) LT0 MI0) as W1.
  lazymatch type of W1 with evt ctasegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes ctasegs _ _ _ c (asta_evt RT AF Σ _ fs _ _ W1') HA).
  intros cf1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ cf1 Hc1) as (ms1 & (m1 & junk1 & -> & MU1 & WM1 & MI1 & FR1 & ST1 & LT1) & Hc1').
  replace (usp - 80 - 80) with (usp - 160) in Hc1', ST1, MU1, FR1 by lia.
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 (usp - 160) ART0); [ul| |exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [intros Hin; apply Ha; left; ul|]. split; [| exact I].
    intros Hin. apply Ha. right; left. apply client_static_intro. unfold TR_INIT in *. lia. }
  assert (LP1 : lib_pristineA m1).
  { apply (lib_pristineA_munch m m1 _ LP0 MU1). intros x Hx Hne. pose proof (LIB_FP_range x Hx) as R.
    cbn [outside]. split; [ul|]. split; [unfold TR_INIT in *; lia| exact I]. }
  assert (CLX1 : CLX OUT_rep ERR_rep XENV lib_pristineA stdout_init m1).
  { apply (CLX_munch_lib OUT_rep ERR_rep IO_FP XENV XENV_FP lib_startA lib_pristineA OUT_loc ERR_loc XENV_loc IO_img XENV_img _ m m1 _ CLX0 MU1);
      [| exact LP1]. intros x Hx Ho. cbn [outside]. split; [ul|]. split; [| exact I].
    unfold LIB_FP in Ho. cbn [outside] in Ho. unfold TR_INIT. lia. }
  pose proof CLX1 as (_ & _ & XE1 & _).
  pose proof (XENV_incb m1 XE1) as IC1.
  assert (AGM1 : agree_on (fun x => usp - 80 <= x < USTACK_TOP) m m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [lia|]. split; [unfold TR_INIT in *; ul| exact I]. }
  assert (AGB1 : agree_on (fun x => buf <= x < buf + cap) m m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn. split; [ul|]. split; [unfold TR_INIT in *; destruct PR3; ul| exact I]. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp - 160)) = usp - 160) by (apply unsigned_lit; ul).
  (* [comment removed for export] *)
  apply (ATX Σ fds0 fs (Z_to_bv 64 0x1f3fb0) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 plen)
           (Z_to_bv 64 pp) (Z_to_bv 64 AEF_GUARD) (Z_to_bv 64 0) (Z_to_bv 64 pp) (Z_to_bv 64 plen) a4 a5 a6 a7
           (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) x5 x6 x7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo);
    [reflexivity| rewrite EU2; exact ST1| rewrite EU2; ul| unfold lo; lia| exact XE1| exact ART1| exact MI1| exact Hc1'|].
  intros cfA (mA & HcA).
  destruct (ASTA_unpack RT Σ _ _ cfA HcA) as (msA & (RSA & (ARTA & MIA & WMA & STA & MUA) & X1A) & HcA').
  destruct RSA as (r0 & r1 & r2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & r3 & r4 & r5 & r6 & FA & fcA & ->).
  rewrite EU2 in STA, MUA.
  rewrite (ret_pc_even 0x1f3fb0) in HcA' by lia.
  assert (OFFA : forall x, ~ (usp - 288 <= x < usp - 160) -> ~ in_ranges ATX_W x -> outside ((usp - 160 - 128, usp - 160) :: ATX_W) x).
  { intros x Hx NI. unfold ATX_W. cbn [outside]. split; [lia|].
    repeat (split; [intros Hr; apply NI; eexists; eexists; split; [| exact Hr]; unfold ATX_W; cbn [In]; tauto|]). exact I. }
  assert (NATX : forall x, x < 0x10000 \/ 0xbc9570 <= x \/ in_ranges LIB_FP x \/ TR_INIT <= x < TR_INIT + 5 -> ~ in_ranges ATX_W x).
  { intros x Hx (lo0 & hi0 & Hin & Hr). unfold ATX_W in Hin.
    assert (Hx' : x < 0x10000 \/ 0xbc9570 <= x \/ (0x5aebe0 <= x < 0x5af400 \/ 0xba4690 <= x < 0xba8ae0 \/ 0xba935a <= x < 0xba9398 \/ 0xbca358 <= x < 0xbcab98)).
    { destruct Hx as [H|[H|[(l1 & h1 & Hin1 & Hr1)|H]]]; [left; exact H| right; left; exact H| |unfold TR_INIT in H; lia].
      unfold LIB_FP in Hin1. repeat (destruct Hin1 as [E1|Hin1]; [injection E1 as <- <-; lia|]). destruct Hin1. }
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
  assert (LPA : lib_pristineA mA).
  { apply (lib_pristineA_munch m1 mA _ LP1 MUA). intros x Hx Hne. pose proof (LIB_FP_range x Hx) as R.
    apply OFFA; [ul| apply NATX; right; right; left; exact Hx]. }
  assert (CLXA : CLX OUT_rep ERR_rep XENV1 lib_pristineA stdout_init mA).
  { apply (CLX_switch OUT_rep ERR_rep IO_FP XENV XENV1 OUT_loc ERR_loc IO_img ATXW_off _ lib_pristineA m1 mA _ CLX1 MUA);
      [| exact X1A| exact LPA]. intros x Hx Hn. apply OFFA; [ul| exact Hn]. }
  assert (AGSA : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m1 mA).
  { apply (agree_of_munch _ _ _ _ MUA). intros x Hx. apply OFFA; [lia| apply NATX; right; left; ul]. }
  assert (AGIA : agree_on (fun x => TR_INIT <= x < TR_INIT + 5) m1 mA).
  { apply (agree_of_munch _ _ _ _ MUA). intros x Hx. apply OFFA; [unfold TR_INIT in *; ul| apply NATX; right; right; right; exact Hx]. }
  assert (AGBA : agree_on (fun x => buf <= x < buf + cap) m1 mA).
  { apply (agree_of_munch _ _ _ _ MUA). intros x Hx. apply OFFA; [ul|]. apply NATX.
    destruct PR3 as [R3|R3]; [left; lia| right; left; unfold SEGTOP_A in *; lia]. }
  assert (ICA : incb 0 mA).
  { apply (incb_agree 0 m1 mA IC1). eapply agree_sub; [exact AGIA|]. intros x Hx. cbv beta. lia. }
  assert (FRA : rw_cells ctasegs mA (usp - 160) [CB 8 junk1; C8 x7; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 (Z_to_bv 64 0x1f3db8)]).
  { apply (rw_cells_agree ctasegs m1 mA _ _ FR1); [| exact WMA]. eapply agree_sub; [exact AGSA|]. intros x Hx.
    cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
  (* [comment removed for export] *)
  pose proof (AF_DRV Σ mA ARTA) as (_ & _ & GIA & _).
  pose proof (tr_pro_init (usp - 80) cp L pp plen gp r0 r1 r2 q1 q2 q3 q4 q5 q6 q7 x5 x6 x7 s8 s9 s10 s11 r3 r4 r5 r6 junk1
                x0 x1 x2 x3 x4 x5 x6 x7 (Z_to_bv 64 0x1f3db8) FA fcA mA B16' ltac:(ul) ltac:(ul)
                ltac:(replace (usp - 80 - 80) with (usp - 160) by lia; exact FRA) GIA MIA) as W2.
  replace (usp - 80 - 80) with (usp - 160) in W2 by lia.
  lazymatch type of W2 with evt ctasegs _ ?X =>
    assert (W2' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W2) end.
  clear W2.
  apply (cps_realizes ctasegs _ _ _ cfA (asta_evt RT AF Σ _ fs _ _ W2') HcA').
  intros cfB HcB.
  destruct (ASTA_unpack RT Σ _ _ cfB HcB) as (msB & (mB & -> & MUB & WMB & MIB & TFB) & HcB').
  assert (STB : stk ctasegs mB lo (usp - 160)).
  { apply (stk_agree ctasegs mA mB _ _ STA); [| exact WMB]. apply (agree_of_munch _ _ _ _ MUB). intros x Hx. cbn. split; [lia| exact I]. }
  assert (ARTB : ART RT Σ mB).
  { apply (af_frame RT AF Σ mA mB (usp - 160) ARTA); [ul| |exact WMB].
    intros a Ha. apply MUB. cbn [outside]. split; [intros Hin; apply Ha; left; ul| exact I]. }
  assert (LPB : lib_pristineA mB).
  { apply (lib_pristineA_munch mA mB _ LPA MUB). intros x Hx Hne. pose proof (LIB_FP_range x Hx) as R. cbn [outside]. split; [ul| exact I]. }
  assert (CLXB : CLX OUT_rep ERR_rep XENV1 lib_pristineA stdout_init mB).
  { apply (CLX_munch OUT_rep ERR_rep IO_FP XENV1 XENV1_FP lib_pristineA OUT_loc ERR_loc XENV1_loc lib_pristineA_loc IO_img XENV1_img
             _ mA mB _ CLXA MUB WMB). intros x Hx. cbn. split; [ul| exact I]. }
  assert (AGSB : agree_on (fun x => usp - 80 <= x < USTACK_TOP) m mB).
  { apply (agree_trans _ m m1 mB); [exact AGM1|]. apply (agree_trans _ m1 mA mB).
    - eapply agree_sub; [exact AGSA|]. intros x Hx. cbv beta in *. lia.
    - apply (agree_of_munch _ _ _ _ MUB). intros x Hx. cbn. split; [lia| exact I]. }
  assert (AGBB : agree_on (fun x => buf <= x < buf + cap) m mB).
  { apply (agree_trans _ m m1 mB); [exact AGB1|]. apply (agree_trans _ m1 mA mB); [exact AGBA|].
    apply (agree_of_munch _ _ _ _ MUB). intros x Hx. cbn. split; [destruct PR3; ul| exact I]. }
  assert (ICB : incb 0 mB).
  { apply (incb_agree 0 mA mB ICA). apply (agree_of_munch _ _ _ _ MUB). intros x Hx. cbn. split; [unfold TR_INIT in *; ul| exact I]. }
  (* [comment removed for export] *)
  apply (INIT Σ (PMfd fds0 fs) (Z_to_bv 64 0x1f4070) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) r0 r1 r2 (Z_to_bv 64 plen)
           (Z_to_bv 64 pp) (Z_to_bv 64 AEF_ARGC) (Z_to_bv 64 (usp - 160)) q2 q3 q4 q5 q6 q7
           (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) x5 x6 x7 s8 s9 s10 s11 r3 r4 r5 r6 FA fcA mB lo);
    try reflexivity; try assumption.
  - apply PMfd_fdfs_only.
  - apply PMfd_mat_stable.
  - rewrite LV. apply lroom3_of_len; cbn [length]; unfold INIT_PB, INIT_NB, INIT_LIVE, LIVE_MAX, PBYTES_MAX, NSEC_LIVE, LW_MAX; lia.      (* [comment removed for export] *)
  - ul.
  - left. rewrite unsigned_lit by lia. ul.
  - rewrite EU2. exact STB.
  - rewrite EU2. ul.
  - rewrite EU2. ul.
  - rewrite EU2. exact B16''.
  - intros cf2 (Σ2 & LW & v2 & Hc2 & LV2 & (LWN & LWP & LWB) & FRS2 & SP2 & CR2).      (* [comment removed for export] *)
    destruct (ASTA_unpack RT Σ2 _ _ cf2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & LB2) & Hc2').
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    rewrite EU2 in ST2, PRES2.
    rewrite (ret_pc_even 0x1f4070) in Hc2' by lia.
    rewrite LV in LV2, PRES2.
    assert (PRESE : rt_pres_fp [(buf, cap)] [] (usp - 160) LIB_FPE mB m2) by exact (rt_pres_fp_weaken _ _ _ _ _ _ _ LIBW_HXA_sub PRES2).
    assert (CLX2 : CLX OUT_rep ERR_rep XENV1 lib_exit_cells stdout_init m2)
      by exact (CLX_libE OUT_rep ERR_rep IO_FP XENV1 XENV1_FP lib_pristineA lib_exit_cells OUT_loc ERR_loc XENV1_loc IO_img XENV1_img
                  _ mB m2 _ _ _ CLXB PRESE (LEX Σ2 LW m2 LB2)).
    pose proof (agree_stack_pres_fp _ _ _ _ _ _ PRESE ltac:(intros x Hx; apply LIB_FPE_outside_hi; ul)) as AG2.
    assert (AGB2 : agree_on (fun x => buf <= x < buf + cap) mB m2).
    { apply (agree_of_pres_fp _ _ _ _ _ _ _ PRESE). intros x Hx.
      split; [right; right; left; exists buf, cap; split; [left; reflexivity| lia]|].
      destruct PR3 as [R3|R3]; [| apply LIB_FPE_outside_hi; lia].
      unfold LIB_FPE, LIB_FP. cbn [outside]. repeat split; try exact I; lia. }
    assert (IC2 : incb 0 m2).
    { apply (incb_agree 0 mB m2 ICB). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRESE). intros x Hx.
      split; [right; left; exact (incb_static x Hx)| exact (incb_off_lib x Hx)]. }
    assert (FR2 : main_frame m2 usp c0 c1 c2 c3 c4 c5 c6 c7).
    { apply (main_frame_agree_nw m m2 usp _ _ _ _ _ _ _ _ FR0). apply (agree_trans _ m mB m2);
        [eapply agree_sub; [exact AGSB|]; intros x Hx; cbv beta in *; ul| eapply agree_sub; [exact AG2|]; intros x Hx; cbv beta in *; ul]. }
    assert (TF2 : tr_frame m2 (usp - 80) (Z_to_bv 64 0x1f3db8) x0 x1 x2 x3 x4 x5 x6 x7).
    { apply (tr_frame_agree_nw mB m2 _ _ _ _ _ _ _ _ _ _ TFB). eapply agree_sub; [exact AG2|]. intros x Hx; cbv beta in *; lia. }
    assert (INB2 : In (buf, cap) (rt_live RT Σ2)) by (rewrite LV2; apply in_or_app; right; left; reflexivity).
    assert (HC2 : 0 < L -> bytes_at ctasegs m2 cp [c0b]).
    { intros HL0. apply (bytes_at_agree ctasegs m m2 _ _ (HC0 HL0)). apply (agree_trans _ m mB m2);
        [eapply agree_sub; [exact AGBB|]| eapply agree_sub; [exact AGB2|]]; intros x Hx; cbn [length] in Hx; cbv beta; lia. }
    assert (BP2 : bytes_at ctasegs m2 pp payload).
    { apply (bytes_at_agree ctasegs m m2 _ _ BP). apply (agree_trans _ m mB m2);
        [eapply agree_sub; [exact AGBB|]| eapply agree_sub; [exact AGB2|]]; intros x Hx; rewrite <- PL in Hx; cbv beta; lia. }
    (* [comment removed for export] *)
    assert (LR2 : lroom3 (rt_live RT Σ2) (FUZZ_LIVE + 4 * KEEP_LIVE + 2) (FUZZ_PB + 4 * KEEP_PB + 2 * LW_MAX) (FUZZ_NB + 4 * KEEP_NB + 2)).
    { rewrite LV2. apply lroom3_app_intro. apply lroom3_of_len; cbn [length];
        unfold FUZZ_LIVE, KEEP_LIVE, FUZZ_PB, KEEP_PB, FUZZ_NB, KEEP_NB, INIT_PB, INIT_NB, INIT_LIVE, LIVE_MAX, PBYTES_MAX, NSEC_LIVE, LW_MAX in *; lia. }
    destruct (Z.eq_dec plen 0) as [Z0|NZ].
    + (* [comment removed for export] *)
      destruct payload as [|b payload]; [| cbn in PL; lia]. cbn in PL. clear PL. subst plen.
      destruct (incb_cells 0 m2 IC2) as (l2 & p2 & TC2).
      pose proof (tr_pro2_empty (usp - 160) cp L pp c0b l2 (Z_to_bv 8 0) p2 gp u0 u1 u2 v2 b1 b2 b3 b4 b5 b6 b7 x5 x6 x7 s8 s9 s10 s11 u3 u4 u5 u6
                    F2 fc2 m2 ltac:(ul) HL HC2 TC2 MI2) as W3.
      lazymatch type of W3 with evt ctasegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes ctasegs _ _ _ _ (asta_evt RT AF Σ2 _ fs _ _ W3') Hc2').
      intros cf3 Hc3. apply Hk.
      destruct (ASTA_unpack RT Σ2 _ _ cf3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & TC3) & Hc3').
      assert (OFF3 : forall x, ~ (TR_INIT + 1 <= x < TR_INIT + 5) -> outside [(AEF_INCB, AEF_INCB + 1)] x)
        by (intros x Hx; unfold AEF_INCB, TR_INIT in *; cbn [outside]; split; [lia| exact I]).
      assert (ART3 : ART RT Σ2 m3).
      { apply (af_frame RT AF Σ2 m2 m3 (usp - 160) ART2); [rewrite SP2; ul| |exact WM3].
        intros a Ha. apply MU3. apply OFF3. intros Hr. apply Ha. right; left. exact (incb_static _ Hr). }
      assert (CLX3 : CLX OUT_rep ERR_rep XENV1 lib_exit_cells stdout_init m3)
        by exact (CLX_incb_munch OUT_rep ERR_rep IO_FP XENV1 XENV1_FP OUT_loc ERR_loc XENV1_loc IO_img XENV1_img INCB_off
                    _ lib_exit_cells m2 m3 _ lib_exit_loc CLX2 MU3 WM3 ltac:(intros x _ Hx; exact (OFF3 x Hx))).
      assert (AG3 : agree_on (fun x => ~ (TR_INIT + 1 <= x < TR_INIT + 5)) m2 m3).
      { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. exact (OFF3 x Hx). }
      assert (LB3 : LIBA Σ2 LW m3).
      { apply (LFR Σ2 Σ2 LW m2 m3 LB2). intros a [Ha|(p & n & Hin & Hx)]; apply AG3; intros Hr.
        - exact (not_in_ranges_of_outside LIB_FP _ (proj2 (incb_off_lib _ Hr)) Ha).
        - assert (Hin2 : In (p, n) (rt_live RT Σ2)) by (rewrite LV2; apply in_or_app; left; exact Hin).
          pose proof (af_live_range RT AF Σ2 m2 p n ART2 Hin2) as (R1 & R2 & R3). unfold TR_INIT in Hr. unfold SEGTOP_A in *. lia. }
      exists Σ2, LW, 0, TR_EMPTY, 0, [], gp, u0, u1, u2, b2, b3, b4, b5, b6, b7, (Z_to_bv 64 cp), s8, s9, s10, s11.
      exists u3, u4, u5, u6, c0, c1, c2, c3, c4, c5, c6, c7, F2, fc2, m3.
      split; [exact Hc3'|].
      split; [| split; [exact TCR| split; [ul| eapply lroom3_mono; [exact LR2| | |]; unfold KEEP_LIVE, KEEP_PB, KEEP_NB, LW_MAX; lia]]].      (* [comment removed for export] *)
      split; [exact ART3|]. split; [exact MI3|]. split; [exact CLX3|].
      split; [apply (main_frame_agree_nw m2 m3 usp _ _ _ _ _ _ _ _ FR2); eapply agree_sub; [exact AG3|]; intros x Hx; cbv beta in *; unfold TR_INIT; ul|].
      split; [apply (tr_frame_agree_nw m2 m3 _ _ _ _ _ _ _ _ _ _ TF2); eapply agree_sub; [exact AG3|]; intros x Hx; cbv beta in *; unfold TR_INIT; ul|].
      rewrite SP2. split; [apply (stk_agree ctasegs m2 m3 _ _ ST2); [eapply agree_sub; [exact AG3|]; intros x Hx; cbv beta in *; unfold TR_INIT; ul| exact WM3]|].
      split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
      split; [rewrite LV2; unfold tr_live; cbn; apply Permutation_refl|]. split; [exact FRS2|]. split; [reflexivity|]. split; [lia|].
      split; [apply bytes_at_nil; unfold TR_EMPTY; lia|]. split; [intros _; split; reflexivity|]. split; [intros Hp; lia|]. split; [ul|].
      split; [exact UT0|]. split; [exact LB3|]. exists p2. exact (tr_cells_split m3 l2 p2 _ TC3).
    + (* [comment removed for export] *)
      pose proof (tr_pro2_copy (usp - 160) cp L pp plen c0b gp u0 u1 u2 v2 b1 b2 b3 b4 b5 b6 b7 x5 x6 x7 s8 s9 s10 s11 u3 u4 u5 u6
                    F2 fc2 m2 ltac:(ul) HL ltac:(lia) HC2 MI2) as W3.
      lazymatch type of W3 with evt ctasegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes ctasegs _ _ _ _ (asta_evt RT AF Σ2 _ fs _ _ W3') Hc2').
      intros cf3 Hc3.
      destruct (ASTA_unpack RT Σ2 _ _ cf3 Hc3) as (ms3 & <- & Hc3').
      apply (MAL Σ2 (PMfd fds0 fs) (Z_to_bv 64 0x1f3f7c) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 plen)
               (Z_to_bv 64 pp) (Z_to_bv 64 plen) b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT)
               (Z_to_bv 64 (tr_calls L c0b)) x6 x7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 plen lo); try reflexivity; try assumption.
      * apply PMfd_fdfs_only.
      * apply PMfd_mat_stable.
      * lia.
      * exact (lroom3_live_room _ _ _ _ plen LR2 ltac:(unfold FUZZ_LIVE, KEEP_LIVE; lia) ltac:(unfold FUZZ_PB, KEEP_PB, LW_MAX; lia) ltac:(unfold FUZZ_NB, KEEP_NB; lia)).      (* [comment removed for export] *)
      * unfold mcost, CREDIT_DRV, INIT_COST in *. destruct (Z.leb_spec plen 64512); lia.
      * unfold call_ok. rewrite EU2, SP2. split; [exact ST2|]. ul.
      * unfold unwind_ok. rewrite EU2, !unsigned_lit by ul. split; [cbn; tauto|]. left. ul.
      * intros cf4 (Σ3 & owned & Hc4 & LV3 & FRS3 & SP3 & CR3 & Pow & Pal & Ptop).
        destruct (ASTA_unpack RT Σ3 _ _ cf4 Hc4) as (ms4 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & WR3 & ACC3) & Hc4').
        destruct RS3 as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
        rewrite EU2 in ST3, PRES3.
        rewrite (ret_pc_even 0x1f3f7c) in Hc4' by lia.
        assert (INO : In (owned, plen) (rt_live RT Σ3)) by (rewrite LV3; left; reflexivity).
        assert (INB3 : In (buf, cap) (rt_live RT Σ3)) by (rewrite LV3; right; exact INB2).
        assert (DISJ : forall p n, In (p, n) (rt_live RT Σ2) -> owned + plen <= p \/ p + n <= owned).
        { intros p n Hin. exact (af_live_disj RT AF Σ3 m3 owned plen p n [] (rt_live RT Σ2) ART3 LV3 Hin). }
        pose proof (DISJ buf cap INB2) as DISJB.
        pose proof (af_live_range RT AF Σ3 m3 owned plen ART3 INO) as (OR1 & OR2 & OR3).
        assert (CLX3 : CLX OUT_rep ERR_rep XENV1 lib_exit_cells stdout_init m3)
          by exact (CLX_pres OUT_rep ERR_rep IO_FP XENV1 XENV1_FP lib_exit_cells OUT_loc ERR_loc XENV1_loc lib_exit_loc IO_img XENV1_img
                      _ m2 m3 _ _ _ CLX2 PRES3 WM3).
        pose proof (agree_stack_pres _ _ _ _ _ PRES3) as AG3.
        assert (IC3 : incb 0 m3).
        { apply (incb_agree 0 m2 m3 IC2). apply (agree_of_pres _ _ _ _ _ _ PRES3). intros x Hx. right; left. exact (incb_static x Hx). }
        assert (BP3 : bytes_at ctasegs m3 pp payload).
        { apply (bytes_at_agree ctasegs m2 m3 _ _ BP2). apply (agree_of_pres _ _ _ _ _ _ PRES3). intros x Hx.
          rewrite <- PL in Hx. right; right; left. exists buf, cap. split; [exact INB2| lia]. }
        assert (LB3 : LIBA Σ3 LW m3).
        { apply (LFR Σ2 Σ3 LW m2 m3 LB2). intros a [Ha|(p & n & Hin & Hx)]; apply PRES3.
          - right; left. exact (proj1 (LIB_img _ Ha)).
          - right; right; left. exists p, n. split; [rewrite LV2; apply in_or_app; left; exact Hin| exact Hx]. }
        (* [comment removed for export] *)
        pose proof (tr_copy_walk (usp - 160) owned gp w0 w1 w2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) d1 d2 d3 d4 d5 d6 d7
                      (Z_to_bv 64 L) (Z_to_bv 64 cp) (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) x6 x7 s8 s9 s10 s11
                      w3 w4 w5 w6 F3 fc3 m3 ltac:(ul) MI3) as W4.
        lazymatch type of W4 with evt ctasegs _ ?X =>
          assert (W4' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W4) end.
        clear W4.
        apply (cps_realizes ctasegs _ _ _ _ (asta_evt RT AF Σ3 _ fs _ _ W4') Hc4').
        intros cf5 Hc5.
        destruct (ASTA_unpack RT Σ3 _ _ cf5 Hc5) as (ms5 & <- & Hc5').
        apply (MCP Σ3 (PMfd fds0 fs) (Z_to_bv 64 0x1f3f90) (Z_to_bv 64 (usp - 160)) gp (Z_to_bv 64 TP_A) w0 w1 w2 (Z_to_bv 64 plen)
                 (Z_to_bv 64 pp) (Z_to_bv 64 owned) (Z_to_bv 64 pp) (Z_to_bv 64 plen) d3 d4 d5 d6 d7 (Z_to_bv 64 owned) (Z_to_bv 64 cp)
                 (Z_to_bv 64 TR_INIT) (Z_to_bv 64 (tr_calls L c0b)) x6 x7 s8 s9 s10 s11 w3 w4 w5 w6 F3 fc3 m3 owned pp payload lo);
          try reflexivity; try assumption.
        -- apply PMfd_fdfs_only.
        -- apply PMfd_mat_stable.
        -- rewrite <- PL. reflexivity.
        -- ul.
        -- ul.
        -- lia.
        -- rewrite <- PL. exact (checked_src_live RT AF Σ3 m3 _ lo buf cap pp plen ART3 INB3 ltac:(lia) ltac:(lia) ltac:(rewrite SP3, SP2; lia)).
        -- rewrite <- PL. exact (checked_dst_live RT AF Σ3 m3 _ owned plen owned plen ART3 INO ltac:(lia) ltac:(lia) ltac:(lia)).
        -- rewrite <- PL. lia.
        -- unfold call_ok. rewrite EU2, SP3, SP2. split; [exact ST3|]. ul.
        -- intros cf6 Hc6.
           destruct (ASTA_unpack RT Σ3 _ _ cf6 Hc6) as (ms6 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BS4) & Hc6').
           destruct RS4 as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & F4 & fc4 & ->).
           rewrite EU2 in ST4, PRES4. rewrite <- PL in PRES4.
           rewrite (ret_pc_even 0x1f3f90) in Hc6' by lia.
           assert (CLX4 : CLX OUT_rep ERR_rep XENV1 lib_exit_cells stdout_init m4)
             by exact (CLX_pres_ex OUT_rep ERR_rep IO_FP XENV1 XENV1_FP lib_exit_cells OUT_loc ERR_loc XENV1_loc lib_exit_loc IO_img XENV1_img
                         _ m3 m4 _ _ _ _ _ CLX3 PRES4 WM4 ltac:(intros x Hx; unfold SEGTOP_A in *; lia)).
           pose proof (agree_stack_pres_ex _ _ _ _ _ _ _ PRES4 ltac:(ul)) as AG4.
           assert (IC4 : incb 0 m4).
           { apply (incb_agree 0 m3 m4 IC3). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4). intros x Hx.
             split; [right; left; exact (incb_static x Hx)| unfold TR_INIT in Hx; unfold SEGTOP_A in *; lia]. }
           assert (LB4 : LIBA Σ3 LW m4).
           { apply (LFR Σ3 Σ3 LW m3 m4 LB3). intros a [Ha|(p & n & Hin & Hx)]; apply PRES4.
             - right; left. exact (proj1 (LIB_img _ Ha)).
             - pose proof (LIB_FP_range _ Ha) as R. unfold SEGTOP_A in *. lia.
             - right; right; left. exists p, n. split; [rewrite LV3; right; rewrite LV2; apply in_or_app; left; exact Hin| exact Hx].
             - assert (Hin2 : In (p, n) (rt_live RT Σ2)) by (rewrite LV2; apply in_or_app; left; exact Hin).
               pose proof (DISJ p n Hin2). lia. }
           (* [comment removed for export] *)
           destruct (incb_cells 0 m4 IC4) as (l4 & p4 & TC4).
           pose proof (tr_copy_ret_walk (usp - 160) owned l4 (Z_to_bv 8 0) p4 gp y0 y1 y2 (Z_to_bv 64 plen) (Z_to_bv 64 pp) (Z_to_bv 64 owned)
                         e1 e2 e3 e4 e5 e6 e7 (Z_to_bv 64 cp) (Z_to_bv 64 (tr_calls L c0b)) x6 x7 s8 s9 s10 s11 y3 y4 y5 y6
                         F4 fc4 m4 TC4 MI4) as W6.
           lazymatch type of W6 with evt ctasegs _ ?X =>
             assert (W6' : forall ms, eq X ms -> evt ctasegs _ ms) by (intros ms <-; exact W6) end.
           clear W6.
           apply (cps_realizes ctasegs _ _ _ _ (asta_evt RT AF Σ3 _ fs _ _ W6') Hc6').
           intros cf7 Hc7. apply Hk.
           destruct (ASTA_unpack RT Σ3 _ _ cf7 Hc7) as (ms7 & (m5 & -> & MU5 & WM5 & MI5 & TC5) & Hc7').
           assert (OFF5 : forall x, ~ (TR_INIT + 1 <= x < TR_INIT + 5) -> outside [(AEF_INCB, AEF_INCB + 1)] x)
             by (intros x Hx; unfold AEF_INCB, TR_INIT in *; cbn [outside]; split; [lia| exact I]).
           assert (ART5 : ART RT Σ3 m5).
           { apply (af_frame RT AF Σ3 m4 m5 (usp - 160) ART4); [rewrite SP3, SP2; ul| |exact WM5].
             intros a Ha. apply MU5. apply OFF5. intros Hr. apply Ha. right; left. exact (incb_static _ Hr). }
           assert (CLX5 : CLX OUT_rep ERR_rep XENV1 lib_exit_cells stdout_init m5)
             by exact (CLX_incb_munch OUT_rep ERR_rep IO_FP XENV1 XENV1_FP OUT_loc ERR_loc XENV1_loc IO_img XENV1_img INCB_off
                         _ lib_exit_cells m4 m5 _ lib_exit_loc CLX4 MU5 WM5 ltac:(intros x _ Hx; exact (OFF5 x Hx))).
           assert (AG5 : agree_on (fun x => ~ (TR_INIT + 1 <= x < TR_INIT + 5)) m4 m5).
           { apply (agree_of_munch _ _ _ _ MU5). intros x Hx. exact (OFF5 x Hx). }
           assert (LB5 : LIBA Σ3 LW m5).
           { apply (LFR Σ3 Σ3 LW m4 m5 LB4). intros a [Ha|(p & n & Hin & Hx)]; apply AG5; intros Hr.
             - exact (not_in_ranges_of_outside LIB_FP _ (proj2 (incb_off_lib _ Hr)) Ha).
             - assert (Hin3 : In (p, n) (rt_live RT Σ3)) by (rewrite LV3; right; rewrite LV2; apply in_or_app; left; exact Hin).
               pose proof (af_live_range RT AF Σ3 m4 p n ART4 Hin3) as (R1 & R2 & R3). unfold TR_INIT in Hr. unfold SEGTOP_A in *. lia. }
           exists Σ3, LW, plen, owned, owned, payload, gp, y0, y1, y2, e2, e3, e4, e5, e6, e7, (Z_to_bv 64 cp), s8, s9, s10, s11.
           exists y3, y4, y5, y6, c0, c1, c2, c3, c4, c5, c6, c7, F4, fc4, m5.
           split; [exact Hc7'|].
           assert (LR3 : lroom3 (rt_live RT Σ3) (FUZZ_LIVE + 4 * KEEP_LIVE + 1) (FUZZ_PB + 4 * KEEP_PB + LW_MAX) (FUZZ_NB + 4 * KEEP_NB + 1))
             by (rewrite LV3; eapply lroom3_mono; [exact (lroom3_cons _ _ _ _ owned plen LR2)| | |]; unfold LW_MAX; lia).      (* [comment removed for export] *)
           split; [| split; [exact TCR| split; [rewrite CR3; unfold mcost, FUZZ_COST, CREDIT_DRV, INIT_COST in *;
                                                 destruct (Z.leb_spec plen 64512); lia
                                               | eapply lroom3_mono; [exact LR3| | |]; unfold KEEP_LIVE, KEEP_PB, KEEP_NB, LW_MAX; lia]]].
           assert (AG25 : agree_on (fun x => usp - 160 <= x < USTACK_TOP) m2 m5).
           { apply (agree_trans _ m2 m3 m5); [eapply agree_sub; [exact AG3|]; intros x Hx; cbv beta in *; lia|].
             apply (agree_trans _ m3 m4 m5); [eapply agree_sub; [exact AG4|]; intros x Hx; cbv beta in *; lia|].
             eapply agree_sub; [exact AG5|]. intros x Hx; cbv beta in *. unfold TR_INIT. ul. }
           split; [exact ART5|]. split; [exact MI5|]. split; [exact CLX5|].
           split; [apply (main_frame_agree_nw m2 m5 usp _ _ _ _ _ _ _ _ FR2); eapply agree_sub; [exact AG25|]; intros x Hx; cbv beta in *; ul|].
           split; [apply (tr_frame_agree_nw m2 m5 _ _ _ _ _ _ _ _ _ _ TF2); eapply agree_sub; [exact AG25|]; intros x Hx; cbv beta in *; lia|].
           rewrite SP3, SP2. split; [apply (stk_agree ctasegs m4 m5 _ _ ST4); [eapply agree_sub; [exact AG5|]; intros x Hx; cbv beta in *; unfold TR_INIT; ul| exact WM5]|].
           split; [exact B16|]. split; [exact ULO|]. split; [exact USP0|]. split; [exact SPW|].
           split; [rewrite LV3, LV2; unfold tr_live; rewrite (proj2 (Z.eqb_neq plen 0) NZ); cbn [app]; apply Permutation_middle|].
           split; [rewrite FRS3; exact FRS2|]. split; [exact PL|]. split; [lia|].
           split; [apply (bytes_at_agree ctasegs m4 m5 _ _ BS4); eapply agree_sub; [exact AG5|]; intros x Hx; cbv beta in *; unfold TR_INIT; unfold SEGTOP_A in *; lia|].
           split; [intros Hp; lia|]. split; [intros _; reflexivity|]. split; [ul|]. split; [exact UT0|]. split; [exact LB5|].
           exists p4. exact (tr_cells_split m5 l4 p4 _ TC5).
Qed.

End Tr1.
