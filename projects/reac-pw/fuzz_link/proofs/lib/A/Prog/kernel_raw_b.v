(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 609 of its 643 lines of code are new or changed and 1890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_exit.v, with its module paths and module names changed; 408 of its 447 lines of code are new or changed and 604 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), two straight runs of the raw
   path. Listing (internal path) (internal record, sha256 7bc02d6772b3):
     kr_e  kr_c4 +0x2078: w1.n := w1.n + t (= t); n_chunks = j (j <= 2: `blt 63, a0` not taken); s11 := w1.n = t
           (`beqz s11` not taken: t >= 1); a0 := (j << 12) + g_nl, s6 := g_nl, a1 := w1, a2 := t      -> kr_c5 +0x20b8
     kr_g  kr_c6 +0x20bc: n_chunks := j + 1; the instrumented check of chunk_len[j] (+0x20e4); chunk_len[j] := s11 = t;
           a1 := 0x202, a0 := slot KS_W1SH                                                        -> kr_c7 +0x20f8
   THE PROOF of each: the cut rebuilt as a symbolic state (j split into 0, 1, 2 first, so the state is closed): for
   kr_e the slots KS_GNL, KS_W1, KS_W1N, KS_GQ read-only, w1.n (atom 32 = &w1.n) writable, n_chunks read-only, s11 the
   atom 27 = t in [1, 4096]; for kr_g kernel_qmsg_b.v's qc_ss with the slot KS_W1SH for KS_W2SH. The engine runs to
   the cut; the cut after it is kernel_kit.v kat_frame_w1 (kr_e: only w1.n written) or kernel_qmsg_kit.v kq_kat_g +
   kq_gnl_next (kr_g: n_chunks and chunk_len[j] written).
   Section hypotheses: LAWS, LV, TB, KI, AMEMCPY, AMEMSET.
   Proves no function (kind: segment lemma of kernel's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_msg0_kit kernel_next kernel_qmsg_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_qmsg_a kernel_qmsg_b kernel_raw_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- kr_e's state at +0x2078: atom 32 = &w1.n, atom 27 = s11 = t ---- *)
Definition re_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x38 0x78 0 0
    [YP09.mkChunk 0x38 (CVal 8 (SOff 243 0)); YP09.mkChunk 0x40 (CVal 8 (SOff 32 (-4096)));
     YP09.mkChunk 0x48 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 243 0x40000))].
Definition re_wn : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))].
Definition re_g (j : Z) : YP09.region :=
  YP09.mkRegion (Some 243%nat) 0x40200 0x40204 0 0 [YP09.mkChunk 0x40200 (CVal 4 (SLit j))].
Definition re_atoms : list (nat * afact) :=
  [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (243%nat, mkAF LA_G_NL LA_G_NL 0); (32%nat, mkAF 8192 (2 ^ 47 - 32) 5);
   (27%nat, mkAF 1 4096 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)].
Definition re_ss (j : Z) : sstate := mkSS (kpc 0x2078) sr_atoms [re_sl; re_wn; re_g j] None (mkFacts re_atoms [] []).

(* ---- kr_g's state at +0x20bc: kernel_qmsg_b.v's qc_ss with the slot KS_W1SH (atom 32 = shadow(w1)) ---- *)
Definition rg_sp : YP09.region := YP09.mkRegion (Some 9%nat) 0x50 0x78 0 0
  [YP09.mkChunk 0x50 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 243 0x40000))].
Definition rg_ss (j : Z) : sstate :=
  mkSS (kpc 0x20bc) (sr_set sr_atoms (Z_to_bv 5 22) (SOff 243 0)) [rg_sp; qc_gl j; qc_gn j] None
    (mkFacts kq_atoms [] []).

(* a register's symbolic value at the end of a run, computed, then its value *)
Ltac kr_reg HS Ex ssx msn :=
  rewrite (st_ok_pi_restrict_reg _ Ex ssx msn _ HS);
  lazymatch goal with |- sv_denot _ (sr_get ?rs ?r) = _ =>
    let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end;
  cbn [sv_denot];
  repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu end;
  rewrite ?Z.add_0_r; first [reflexivity | unfold w64; f_equal; unfold NW_N; lia].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.                                (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis KI : KernImg pa_segs B.                              (* kernel_img_syms at the image *)
Hypothesis AMEMCPY : aintrin_realizes pa_segs B OCpy 0x52d78.   (* checked_memcpy: AE2q.v asan_memcpy_realizes *)
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.   (* checked_memset: AE2r.v asan_memset_realizes *)

Lemma kr_U_reg : forall (ms3 : machine_state) rl extra (q : nat) v,
  kregs_eq ms3 rl -> In (q, v) rl -> (q < 32)%nat -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (Eimg (Ereg (ms_regs ms3) extra)) q) = v.
Proof.
  intros ms3 rl extra q v HRL Hin Hq Hv.
  rewrite (ew_Eimg_Ereg_nat _ _ q (Z_to_bv 5 (Z.of_nat q))).
  - rewrite (kn_reg_of ms3 rl q v HRL Hin). unfold w64. apply unsigned_lit_small. exact Hv.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* ---- kr_e: kr_c4 +0x2078 -> kr_c5 +0x20b8 ---- *)
Lemma re_seat : forall cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv t (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kw_at W3 ms3 (kW1 cx fpos) 0 0 ->
  kat B cx fpos 0x2078 (kr_rl4 cx fpos ci t) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  0 <= j <= 2 -> 1 <= t <= 4096 ->
  E = Eimg (Ereg (ms_regs ms3) [w64 (kW1 cx fpos + NW_N)]) ->
  st_ok_pi SEGS pa_val E (re_ss j) (restrict (w_H W3) ms3) /\
  sh_ok SEGS kq_Bx [mkSHE 32 0 8] E (mrestrict (w_H W3) (ms_mem ms3)) /\
  awr_ok_x E (ss_mem (re_ss j)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j adv t E HB HJ HW HK Hj Ht HEdef.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & _ & _ & HGN & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  destruct HW as (Ww0 & Wwl & Wpres & Wnv & Wfv & Wnr & Wfr).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hs1f & Hs1g & Hs1h).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8 & S9 & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & F3 & F4 & F5 & _).
  rewrite kn_fsb8 in F2, F3, F5. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F5.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in F3.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity.
  assert (U9 : bv_unsigned (ew E 9%nat) = ksp1 cx)
    by (rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 9 9%bv eq_refl), A9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20%nat) = SHADOW_OFF)
    by (rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 20 20%bv eq_refl), A20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U27 : bv_unsigned (ew E 27%nat) = t)
    by (rewrite HEdef; apply (kr_U_reg ms3 (kr_rl4 cx fpos ci t)); [exact HRL | kr_in | lia | lia]).
  assert (U32 : bv_unsigned (ew E 32%nat) = kW1 cx fpos + NW_N).
  { rewrite HEdef, (kq_E_32 SK B LAWS TB KI AMEMCPY LV). apply unsigned_lit_small. unfold kW1, KN_W1, NW_N. lia. }
  assert (U243 : bv_unsigned (ew E 243%nat) = LA_G_NL) by (rewrite HEdef; apply (kq_U243 SK B LAWS TB KI AMEMCPY LV)).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact U9.
  assert (BV32 : base_val E (Some 32%nat) = kW1 cx fpos + NW_N) by exact U32.
  assert (BV243 : base_val E (Some 243%nat) = LA_G_NL) by exact U243.
  pose proof (kn_slot_of cx W3 ms3 _ KS_GNL LA_G_NL HSL
                ltac:(unfold kr_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_GNL.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W1 (kW1 cx fpos) HSL
                ltac:(unfold kr_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_W1.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W1N (kW1 cx fpos + NW_N) HSL
                ltac:(unfold kr_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_W1N.
  pose proof (kn_slot_of cx W3 ms3 _ KS_GQ (LA_G_NL + NK_CHUNK_LEN) HSL
                ltac:(unfold kr_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_GQ.
  pose proof (kq_nchunks cx W3 ms3 j HGN) as HNC.
  assert (HFA : frame_addr ly3 KN_CID fpos = kF cx fpos) by exact (km_fa SK B cx fpos k2 ly3 S3 W3 _ md3 HB HJ KN_CID fpos).
  split; [|split].
  - rewrite (km_ms_shape ms3 (BASE + kpc 0x2078) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
    unfold re_ss. apply pa_entry_st_ok_full.
    + rewrite HEdef. apply regs_ok_Eimg_Ereg.
    + assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia.
      destruct Hj3 as [-> | [-> | ->]]; vm_compute; reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil.
      * unfold re_sl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x38 (SOff 243 0) LA_G_NL); [|exact SL_GNL].
           cbn [sv_denot]. rewrite U243, Z.add_0_r. reflexivity.
        -- apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x40 (SOff 32 (-4096)) (kW1 cx fpos)); [|exact SL_W1].
           cbn [sv_denot]. rewrite U32. f_equal. unfold NW_N. lia.
        -- apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x48 (SOff 32 0) (kW1 cx fpos + NW_N)); [|exact SL_W1N].
           cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
        -- apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x70 (SOff 243 0x40000) (LA_G_NL + NK_CHUNK_LEN));
             [|exact SL_GQ].
           cbn [sv_denot]. rewrite U243. reflexivity.
      * unfold re_wn, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV32. split; [unfold kW1, KN_W1, NW_N; lia|]. split; [unfold kW1, KN_W1, NW_N; lia|]. split.
        { intros o Ho. replace (kW1 cx fpos + NW_N + o) with (kW1 cx fpos + (NW_N + o)) by lia.
          exact (proj2 (Wpres (NW_N + o) ltac:(unfold NW_N, NW_SIZE; lia))). }
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (kW1 cx fpos + NW_N) 0 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact Wnv.
      * unfold re_g, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV243. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ LA_G_NL 0x40200 4 (SLit j) j); [reflexivity | cbn; lia | cbn; lia | exact HNC].
    + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, re_sl, re_wn, re_g.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV9, BV32, BV243.
      unfold LA_G_NL, kW1, KN_W1, NW_N, alloc_ceiling in *. rewrite HK8 in S1. repeat split; lia.
    + unfold facts_ok, re_atoms. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U243, U32, U27, U9.
      change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
      unfold SHADOW_OFF, LA_G_NL, kW1, KN_W1, NW_N, alloc_ceiling in *. rewrite HK8 in S1. repeat split; lia.
  - assert (HUB : U E kq_Bx = SHADOW_OFF)
      by (unfold kq_Bx; rewrite U_SOff, U20, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
    pose proof (kn_w1_ra B LAWS cx fpos k2 ly3 S3 md3 W3 ms3 0xf8 0xf3 HJB HSH) as HRA.
    unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E kq_Bx 32 (kW1 cx fpos) NW_SIZE (kW1 cx fpos + NW_N) 0 8
             HRA HUB);
      [rewrite U_SOff, U32, Z.add_0_r; apply zcanon_id; unfold M64, kW1, KN_W1, NW_N; lia
      | unfold NW_N; lia | unfold NW_N, NW_SIZE; lia |].
    intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia.
    unfold kW1, KN_W1, NW_N, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  - unfold re_ss. cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; unfold re_sl in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    + intros x Hx. unfold re_wn in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV32 in Hx.
      left.
      apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KN_CID fpos x HJ).
      * left. reflexivity.
      * left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFA, kn_fsb8. unfold kW1, KN_W1, NW_N in Hx. lia.
    + intros x Hx. unfold re_g in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia.
Qed.

Theorem kr_e : forall POST Rc, kfrom SK B POST (kr_c5 B Rc) -> kfrom SK B POST (kr_c4 B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & t & HRcv & Hcr & Hci & Hj & Ht & HW & HK).
  pose proof HK as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _).
  rewrite kn_fsb8 in F2.
  pose proof asan_consts as ((C1a & C1b) & _).
  remember (Eimg (Ereg (ms_regs ms3) [w64 (kW1 cx fpos + NW_N)])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) [w64 (kW1 cx fpos + NW_N)]) E)
    by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & _).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hs1f & Hs1g & Hs1h).
  assert (UR : forall (q : nat) v, In (q, v) (kr_rl4 cx fpos ci t) -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E q) = v).
  { intros q v Hin Hv. rewrite HEdef. apply (kr_U_reg ms3 (kr_rl4 cx fpos ci t)); [exact HRL | exact Hin | | exact Hv].
    unfold kr_rl4, kregs_chunk in Hin. cbn [In app] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]). destruct Hin. }
  assert (U19 : bv_unsigned (ew E 19%nat) = ka0 cx + 8) by (apply UR; [kr_in | lia]).
  assert (U21 : bv_unsigned (ew E 21%nat) = kW2 cx fpos) by (apply UR; [kr_in | unfold kW2, KN_W2 in *; lia]).
  assert (U24 : bv_unsigned (ew E 24%nat) = kS8 cx)
    by (apply UR; [kr_in | unfold kS8, shadow_of_addr, SHADOW_OFF; lia]).
  assert (U25 : bv_unsigned (ew E 25%nat) = kW2 cx fpos + NW_N)
    by (apply UR; [kr_in | unfold kW2, KN_W2, NW_N in *; lia]).
  assert (U23 : bv_unsigned (ew E 23%nat) = ci) by (apply UR; [kr_in | lia]).
  assert (U27 : bv_unsigned (ew E 27%nat) = t) by (apply UR; [kr_in | lia]).
  assert (U32 : bv_unsigned (ew E 32%nat) = kW1 cx fpos + NW_N).
  { rewrite HEdef, (kq_E_32 SK B LAWS TB KI AMEMCPY LV). apply unsigned_lit_small. unfold kW1, KN_W1, NW_N. lia. }
  assert (U243 : bv_unsigned (ew E 243%nat) = LA_G_NL) by (rewrite HEdef; apply (kq_U243 SK B LAWS TB KI AMEMCPY LV)).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  assert (Hj2 : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct Hj2 as [-> | [-> | ->]];
    (lazymatch type of HK with kat _ _ _ _ _ _ _ _ _ (Some ?jv) _ _ _ _ _ _ =>
     destruct (re_seat cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv adv t E HB HJ HW HK ltac:(lia) Ht HEdef)
       as (HS & SHOK & HAWR);
     paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x20b8); [exact HAWR|];
     lazymatch goal with
     | HS' : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msn), HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
       HG' : mem_grows _ (mrestrict _ (ms_mem ?msn))
       |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
       apply (HNEXT cx fpos k2 ly3 S3 W3 msn mdn HB HJ Hfrm);
       exists c, ci, jv, adv, t; split; [exact HRcv|]; split; [exact Hcr|]; split; [exact Hci|]; split; [lia|];
       split; [exact Ht|];
       apply (kat_frame_w1 SK B LAWS NW_N (NW_N + 8) cx fpos 0x2078 _ _ _ true adv (Some jv) k2 ly3 S3 W3 ms3 md3 0x20b8
                (kr_rl5 cx fpos ci t jv) (kr_sl cx fpos c) W3 msn mdn HB HK);
       [ apply (kn_kms_of _ Ex ssx msn 0x20b8 HS'); vm_compute; reflexivity
       | exact (kregs0_keep cx ms3 msn (regs_kept_of_st_ok_pi Ex ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
                  HR0)
       | unfold kregs_eq; cbn [kr_rl5 kr_rl0 app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
         kr_reg HS' Ex ssx msn
       | apply incl_refl | apply kr_sl_ok | apply kfsh_fits
       | exact (proj1 (wvb_fds_fs _ _ _))
       | exact (proj2 (wvb_fds_fs _ _ _))
       | unfold NW_N; lia | unfold NW_N, NW_SIZE; lia
       | kq_un HFr' (fun x => kW1 cx fpos + NW_N <= x < kW1 cx fpos + (NW_N + 8))
       | intros a Ha; exact (kq_apres_grows _ _ _ a HG' Ha) ]
     end end).
Qed.

(* ---- kr_g: kr_c6 +0x20bc -> kr_c7 +0x20f8 ---- *)
Lemma rg_seat : forall cx fpos k2 ly3 S3 W3 ms3 md3 c ci j t adv (E : env),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kat B cx fpos 0x20bc (kr_rl6 cx fpos ci t) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  0 <= j <= 2 ->
  E = Eimg (Ereg (ms_regs ms3) [w64 (kFSH cx fpos + 4)]) ->
  st_ok_pi SEGS pa_val E (rg_ss j) (restrict (w_H W3) ms3) /\
  sh_ok SEGS kq_Bx qc_SH E (mrestrict (w_H W3) (ms_mem ms3)) /\
  awr_ok_x E (ss_mem (rg_ss j)) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx)
    (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3 ((KN_CID, fpos) :: k_own cx).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 c ci j t adv E HB HJ HK Hj HEdef.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & HKK & _ & HGN & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  pose proof HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
  pose proof (kn_sp1 SK B cx HB) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e & Hs1f & Hs1g & Hs1h).
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (U9 : bv_unsigned (ew E 9%nat) = ksp1 cx)
    by (rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 9 9%bv eq_refl), A9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20%nat) = SHADOW_OFF)
    by (rewrite HEdef, (ew_Eimg_Ereg_nat _ _ 20 20%bv eq_refl), A20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew E 32%nat) = kFSH cx fpos + 4).
  { rewrite HEdef, (kq_E_32 SK B LAWS TB KI AMEMCPY LV). apply unsigned_lit_small. unfold kHighMemBeg, SHADOW_OFF in *. lia. }
  assert (U243 : bv_unsigned (ew E 243%nat) = LA_G_NL) by (rewrite HEdef; apply (kq_U243 SK B LAWS TB KI AMEMCPY LV)).
  assert (E243 : ew E 243%nat = Z_to_bv 64 LA_G_NL) by (rewrite HEdef; apply (kq_E_243 SK B LAWS TB KI AMEMCPY LV)).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by exact U9.
  assert (BV243 : base_val E (Some 243%nat) = LA_G_NL) by exact U243.
  pose proof (kn_slot_of cx W3 ms3 _ KS_GQ (LA_G_NL + NK_CHUNK_LEN) HSL
                ltac:(unfold kr_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_GQ.
  pose proof (kn_slot_of cx W3 ms3 _ KS_W1SH (kFSH cx fpos + 4) HSL
                ltac:(unfold kr_sl; apply in_or_app; left; unfold kslots_setup; kn_in)) as SL_W1SH.
  pose proof (kq_nchunks cx W3 ms3 j HGN) as HNC.
  assert (GW : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS (mrestrict (w_H W3) (ms_mem ms3)) a)
    by exact (writable_at_of_wseg SEGS _ LA_G_NL NK_SIZE ltac:(unfold LA_G_NL; lia)
                ltac:(unfold LA_G_NL, NK_SIZE; lia) (ki_gnl_wseg _ _ KI)).
  destruct (kq_gnl_ra SK B LAWS TB KI AMEMCPY LV cx fpos k2 ly3 S3 W3 ms3 md3 LA_G_NL NK_SIZE HB HJ HJB HKK
              ltac:(lia) ltac:(lia) ltac:(unfold NK_SIZE; lia)) as (HRAg & _).
  split; [|split].
  - rewrite (km_ms_shape ms3 (BASE + kpc 0x20bc) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
    unfold rg_ss. apply pa_entry_st_ok_full.
    + apply kn_regs_ok_set; [rewrite HEdef; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |].
      rewrite (sv_off0 E 243 LA_G_NL E243). symmetry. apply (kn_reg_of ms3 _ 22 _ HRL). kr_in.
    + assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia.
      destruct Hj3 as [-> | [-> | ->]]; vm_compute; reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil.
      * unfold rg_sp, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x50 (SOff 32 0) (kFSH cx fpos + 4)); [|exact SL_W1SH].
           cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
        -- apply (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x70 (SOff 243 0x40000) (LA_G_NL + NK_CHUNK_LEN));
             [|exact SL_GQ].
           cbn [sv_denot]. rewrite U243. reflexivity.
      * unfold qc_gl, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV243. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split; [|apply Forall_nil].
        intros o Ho. apply GW. unfold NK_SIZE. lia.
      * unfold qc_gn, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite BV243. split; [unfold LA_G_NL; lia|]. split; [unfold LA_G_NL; lia|]. split.
        { intros o Ho. apply GW. unfold NK_SIZE. lia. }
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ LA_G_NL 0x40200 4 (SLit j) j); [reflexivity | cbn; lia | cbn; lia | exact HNC].
    + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, rg_sp, qc_gl, qc_gn.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite BV9, BV243. unfold LA_G_NL. repeat split; lia.
    + unfold facts_ok, kq_atoms. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U243. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      unfold SHADOW_OFF, LA_G_NL. repeat split; lia.
  - assert (HUB : U E kq_Bx = SHADOW_OFF)
      by (unfold kq_Bx; rewrite U_SOff, U20, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
    unfold sh_ok, qc_SH. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E kq_Bx 243 LA_G_NL NK_SIZE LA_G_NL 0x40000 0x40018 HRAg HUB);
      [rewrite U_SOff, U243, Z.add_0_r; apply zcanon_id; unfold M64, LA_G_NL; lia | lia | unfold NK_SIZE; lia |].
    intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold LA_G_NL, SHADOW_OFF in *. lia.
  - unfold rg_ss. cbn [ss_mem].
    apply awr_ok_x_cons; [intros x Hx; unfold rg_sp in Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
    + intros x Hx. unfold qc_gl in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV243 in Hx.
      exact (kq_ajw SK B cx fpos k2 ly3 S3 W3 _ md3 x HB HJ HJB
               (kq_kE_gnl SK B LAWS TB KI AMEMCPY LV cx x ltac:(unfold NK_OPEN; lia))).
    + intros x Hx. unfold qc_gn in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV243 in Hx.
      exact (kq_ajw SK B cx fpos k2 ly3 S3 W3 _ md3 x HB HJ HJB
               (kq_kE_gnl SK B LAWS TB KI AMEMCPY LV cx x ltac:(unfold NK_OPEN; lia))).
Qed.

(* the cut after kr_g's run: n_chunks = j + 1, chunk_len[j] = t *)
Lemma rg_land : forall POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j t adv (E : env) (ms : machine_state) md
    cs1 cs2,
  kfrom SK B POST (kr_c7 B Rc) ->
  kbase SK B cx -> frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  Rc cx (c - ci) -> 1 <= c <= 3 -> 0 <= ci < c -> 0 <= j <= ci -> 1 <= t <= 4096 ->
  kat B cx fpos 0x20bc (kr_rl6 cx fpos ci t) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3 ->
  bv_unsigned (ew E 27%nat) = t -> bv_unsigned (ew E 243%nat) = LA_G_NL ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms))
    (YP09.mkRegion (Some 243%nat) (0x40000 + 8 * j) (0x40008 + 8 * j) (0x40000 + 8 * j) (0x40008 + 8 * j) cs1) ->
  In (YP09.mkChunk (0x40000 + 8 * j) (CVal 8 (SOff 27 0))) cs1 ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (YP09.mkRegion (Some 243%nat) 0x40200 0x40204 0x40200 0x40204 cs2) ->
  In (YP09.mkChunk 0x40200 (CVal 4 (SLit (j + 1)))) cs2 ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ ((LA_G_NL + (0x40000 + 8 * j) <= a < LA_G_NL + (0x40008 + 8 * j)) \/ (LA_G_NL + 0x40200 <= a < LA_G_NL + 0x40204)) ->
     aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  mem_grows (mrestrict (w_H W3) (ms_mem ms3)) (mrestrict (w_H W3) (ms_mem ms)) ->
  kms 0x20f8 ms -> kregs0 cx ms -> kregs_eq ms (kr_rl7 cx fpos ci) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci j t adv E ms md cs1 cs2 HN HB HFRM HJ HRc Hc Hci Hj Ht HK
    U27 U243 HR1 Hin1 HR2 Hin2 UN HG HMS HR0 HRL Hfds Hfs.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & _ & _ & HGN & _).
  apply (HN cx fpos k2 ly3 S3 W3 ms md HB HJ HFRM).
  exists c, ci, (j + 1), adv. split; [exact HRc|]. split; [exact Hc|]. split; [exact Hci|]. split; [lia|].
  assert (HCL : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (LA_G_NL + (NK_CHUNK_LEN + 8 * j)) 8 t).
  { exact (field_of_region E _ 243 LA_G_NL _ _ _ _ _ (0x40000 + 8 * j) 8 (SOff 27 0) t HR1 U243 Hin1
             ltac:(cbn [sv_denot]; rewrite U27, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (HNC : val_mem SEGS (mrestrict (w_H W3) (ms_mem ms)) (LA_G_NL + NK_N_CHUNKS) 4 (j + 1)).
  { exact (field_of_region E _ 243 LA_G_NL _ _ _ _ _ 0x40200 4 (SLit (j + 1)) (j + 1) HR2 U243 Hin2
             eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
  apply (kq_kat_g SK B LAWS TB KI AMEMCPY LV (fun _ => False)
           (fun a => (LA_G_NL + (0x40000 + 8 * j) <= a < LA_G_NL + (0x40008 + 8 * j)) \/
                     (LA_G_NL + 0x40200 <= a < LA_G_NL + 0x40204))
           cx fpos 0x20bc (kr_rl6 cx fpos ci t) (kr_sl cx fpos c) (kfsh 0 0xf8 0xf3) true adv (Some j)
           k2 ly3 S3 W3 ms3 md3 0x20f8 (kr_rl7 cx fpos ci) (kr_sl cx fpos c) (Some (j + 1)) W3 ms md HB HK HMS HR0 HRL
           (incl_refl _) (kfsh_fits _ _ _) Hfds Hfs).
  - intros a Ha _ Hg. exact (UN a Ha Hg).
  - intros a Ha. exact (kq_apres_grows _ _ _ a HG Ha).
  - intros a [].
  - exact (kq_miss0 SK B LAWS TB KI AMEMCPY LV cx fpos (kr_sl cx fpos c) _ (kr_sl_ok cx fpos c)).
  - intros a [Ha | Ha]; unfold NK_OPEN; lia.
  - assert (HnM : 0 <= t <= NL_CHUNK_MAX) by (unfold NL_CHUNK_MAX; lia).
    apply (kq_gnl_next SK B LAWS TB KI AMEMCPY LV cx W3 ms3 ms j (j + 1) t HGN ltac:(lia)
             (or_intror (conj eq_refl HnM))).
    + intros i Hi. apply (kq_aview_grows SK B LAWS TB KI AMEMCPY LV _ _ _ _ HG).
      exact (kq_gnl_vis SK B LAWS TB KI AMEMCPY LV cx W3 ms3 (Some j) HGN i Hi).
    + intros i Hi Hc1 Hc2. apply UN; [unfold LA_G_NL, NK_SIZE, NK_CHUNK_LEN in *; lia|].
      unfold NK_CHUNK_LEN, NK_N_CHUNKS in *. lia.
    + exact HNC.
    + exact HCL.
Qed.

Theorem kr_g : forall POST Rc, kfrom SK B POST (kr_c7 B Rc) -> kfrom SK B POST (kr_c6 B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & t & HRcv & Hcr & Hci & Hj & Ht & HK).
  pose proof HK as (_ & HR0 & HRL & _ & _ & _ & _ & HJB & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  destruct (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2).
  pose proof asan_consts as ((C1a & C1b) & _).
  remember (Eimg (Ereg (ms_regs ms3) [w64 (kFSH cx fpos + 4)])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAG : YP06.env_agree 32 (Ereg (ms_regs ms3) [w64 (kFSH cx fpos + 4)]) E)
    by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & _).
  assert (UR : forall (q : nat) v, In (q, v) (kr_rl6 cx fpos ci t) -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E q) = v).
  { intros q v Hin Hv. rewrite HEdef. apply (kr_U_reg ms3 (kr_rl6 cx fpos ci t)); [exact HRL | exact Hin | | exact Hv].
    unfold kr_rl6, kr_rl0 in Hin. cbn [In app] in Hin.
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]). destruct Hin. }
  assert (U19 : bv_unsigned (ew E 19%nat) = ka0 cx + 8) by (apply UR; [kr_in | lia]).
  assert (U21 : bv_unsigned (ew E 21%nat) = kW2 cx fpos)
    by (apply UR; [kr_in | destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _);
                         rewrite kn_fsb8 in F2; unfold kW2, KN_W2 in *; lia]).
  assert (U24 : bv_unsigned (ew E 24%nat) = kS8 cx)
    by (apply UR; [kr_in | unfold kS8, shadow_of_addr, SHADOW_OFF; lia]).
  assert (U25 : bv_unsigned (ew E 25%nat) = kW2 cx fpos + NW_N)
    by (apply UR; [kr_in | destruct (kn_F_facts B LAWS cx fpos k2 ly3 S3 md3 HJB) as (F1 & F2 & _);
                         rewrite kn_fsb8 in F2; unfold kW2, KN_W2, NW_N in *; lia]).
  assert (U23 : bv_unsigned (ew E 23%nat) = ci) by (apply UR; [kr_in | lia]).
  assert (U27 : bv_unsigned (ew E 27%nat) = t) by (apply UR; [kr_in | lia]).
  assert (U32 : bv_unsigned (ew E 32%nat) = kFSH cx fpos + 4).
  { rewrite HEdef, (kq_E_32 SK B LAWS TB KI AMEMCPY LV). apply unsigned_lit_small. unfold kHighMemBeg, SHADOW_OFF in *. lia. }
  assert (U243 : bv_unsigned (ew E 243%nat) = LA_G_NL) by (rewrite HEdef; apply (kq_U243 SK B LAWS TB KI AMEMCPY LV)).
  pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  assert (Hj2 : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct Hj2 as [-> | [-> | ->]];
    (lazymatch type of HK with kat _ _ _ _ _ _ _ _ _ (Some ?jv) _ _ _ _ _ _ =>
     destruct (rg_seat cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv t adv E HB HJ HK ltac:(lia) HEdef) as (HS & SHOK & HAWR);
     paj_run_to_tok RUNTO HS HJ SHOK kq_span (kpc 0x20f8); [exact HAWR|];
     lazymatch goal with
     | HS' : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msn), HFr' : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)),
       HG' : mem_grows _ (mrestrict _ (ms_mem ?msn))
       |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
       let HR1 := fresh "HR1" in let HR2 := fresh "HR2" in
       spregion HS' 1%nat HR1; spregion HS' 2%nat HR2;
       lazymatch type of HR1 with region_ok _ _ _ ?r1 =>
       lazymatch type of HR2 with region_ok _ _ _ ?r2 =>
       let cs1 := eval vm_compute in (YP09.r_chunks r1) in
       let cs2 := eval vm_compute in (YP09.r_chunks r2) in
       apply (rg_land POST Rc cx fpos k2 ly3 S3 W3 ms3 md3 c ci jv t adv Ex msn mdn cs1 cs2 HNEXT HB Hfrm HJ HRcv Hcr
                Hci ltac:(lia) Ht HK U27 U243 HR1 ltac:(kn_in) HR2 ltac:(kn_in));
       [ kq_un HFr' (fun x => (LA_G_NL + (0x40000 + 8 * jv) <= x < LA_G_NL + (0x40008 + 8 * jv)) \/
                              (LA_G_NL + 0x40200 <= x < LA_G_NL + 0x40204))
       | exact HG'
       | apply (kn_kms_of _ Ex ssx msn 0x20f8 HS'); vm_compute; reflexivity
       | exact (kregs0_keep cx ms3 msn (regs_kept_of_st_ok_pi Ex ssx _ _ _ nx_keep0 HS' HAG ltac:(vm_compute; reflexivity))
                  HR0)
       | unfold kregs_eq; cbn [kr_rl7 kr_rl0 app]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
         kr_reg HS' Ex ssx msn
       | exact (proj1 (wvb_fds_fs _ _ _))
       | exact (proj2 (wvb_fds_fs _ _ _)) ]
       end end
     end end).
Qed.

End b.
End a.
