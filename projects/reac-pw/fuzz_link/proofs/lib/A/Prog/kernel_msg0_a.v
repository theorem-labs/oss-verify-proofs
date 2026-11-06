(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 289 of its 324 lines of code are new or changed and 1270 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the message path's first steps up to
   meta_fill_00 of w2's shadow. Listing (internal path) (internal record, sha256 7bc02d6772b3):
     +0x594  lbu a0, 0(s8); beqz -> +0x5a0       the instrumented check of the cursor's n word (s8 = shadow(a0 + 8))
     +0x5a0  sd s6, 0x78(s1)                      slot KS_CI := ci
     +0x5a4  ld s3, 0(s3)                         s3 := the cursor's n (s3 = a0 + 8)
     +0x5a8  li a1, 0x202; ld a0, 0x80(s1)        a0 = shadow(w2) (slot KS_W2SH)
     +0x5b0  jal meta_fill_00                     (0x55e74), returns at +0x5b4
   and the empty cursor's path at the mode byte:
     +0x1e7c sd s6, 0x78(s1); li a1, 0x202; ld a0, 0x80(s1); jal meta_fill_00 (+0x1e88), returns at +0x1e8c.
   So the +0x1e7c path DOES unpoison w2 (kin_qmsg's F shadow kfsh 0xf8 0 0xf3 holds there): no invariant change.
   THE PROOF: the state is rebuilt from the cut (the cursor's two words as a read-only region with the shadow entry
   mkSHE 18 0 16 for the check; the slots 0x58, 0x80 and the written slot 0x78), the engine runs to the call, the call
   is kernel_msg0_kit.v km_call_mf (LinkWalkSide.v aj_gx_set_shadow_at over AS00) and the cut after it is km_land_mf
   (kernel_kit.v kat_frame with the change set {slot 0x78, w2's shadow}; F's shadow restated with w2's bytes 0).
   kn_m5a: kin_msg0 -> kin_m5b4; kn_mza: kin_mz -> kin_z1e8c.
   Section hypotheses: LAWS, TB (the cursor's shadow at the current memory, through LinkWalkShadow.v), LV (the
   call's pc), AS00.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro kernel_defs kernel_kit kernel_msg0_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : AF0m.PcapSyms B.     (* AF0m.v; discharged at the frame's B by AD2l.PcapB_syms *)
Hypothesis LV : LinkVals.
Hypothesis AS00 : SetShadowDef.aset_shadow_realizes pa_segs B 0x55e74 0x00.   (* meta_fill_00: SetShadow.v link_set_shadow_00 *)

(* the slots of kin_msg0 / kin_mz lie in [s1 + 0x18, s1 + 0xf8) away from the slot KS_CI *)
Lemma ma_sl0 : forall cx fpos c ov, In ov (kslots_setup cx fpos c) ->
  0x18 <= fst ov <= 0xf0 /\ (fst ov + 8 <= KS_CI \/ KS_CI + 8 <= fst ov).
Proof.
  intros cx fpos c ov Hov. unfold kslots_setup in Hov. cbn [In] in Hov.
  repeat (destruct Hov as [<- | Hov];
    [cbv [fst KS_FSH KS_FRES KS_W1F KS_F KS_GNL KS_W1 KS_W1N KS_W1SH KS_NW KS_C KS_GQ KS_W2SH KS_MASK KS_CN
          KS_M6 KS_CSH KS_W2F KS_M4098 KS_M4093 KS_F2 KS_CI]; lia |]).
  destruct Hov.
Qed.

Lemma ma_sl1 : forall cx fpos c ov, In ov (kslots_setup cx fpos c ++ [(KS_ROOM, 4097)]) ->
  0x18 <= fst ov <= 0xf0 /\ (fst ov + 8 <= KS_CI \/ KS_CI + 8 <= fst ov).
Proof.
  intros cx fpos c ov Hov. apply in_app_or in Hov. destruct Hov as [Hov | Hov]; [exact (ma_sl0 cx fpos c ov Hov)|].
  cbn [In] in Hov. destruct Hov as [<- | []]. cbv [fst KS_ROOM KS_CI]. lia.
Qed.

(* the state at +0x594 *)
Lemma ma_seatA : forall cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv g,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kat B cx fpos KP_MSG0 rl sl (kfsh 0xf8 0xf8 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 ->
  In (19%nat, ka0 cx + 8) rl -> In (24%nat, kS8 cx) rl ->
  In (KS_NW, NW_SIZE) sl -> In (KS_W2SH, kFSH cx fpos + 0x226) sl ->
  st_ok_pi SEGS pa_val (km_E ms3 (k_wp cx + adv) (k_wn cx - adv) (kFSH cx fpos + 0x226)) km_ssA
    (restrict (w_H W3) ms3).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv g HB HJ HK H19 H24 Hnw Hws.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & _ & HSL & HJB & _ & HCUR & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  destruct HCUR as (Hadv0 & HCP & HCN & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & S6 & S7 & S8 & S9 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1, S6.
  destruct (km_cur_loc SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (CU0 & CU16 & CL).
  pose proof (proj2 (CL (ka0 cx) ltac:(lia))) as CLa. pose proof (proj2 (CL (ka0 cx + 15) ltac:(lia))) as CLb.
  rewrite HK8 in CLa, CLb.
  assert (Hp64 : 0 <= k_wp cx + adv /\ k_wp cx + adv < 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAMR; lia).
  destruct (km_E0 cx ms3 (k_wp cx + adv) (k_wn cx - adv) (kFSH cx fpos + 0x226) HR0) as (E18 & E9 & E20 & _).
  destruct (km_E_ext ms3 (k_wp cx + adv) (k_wn cx - adv) (kFSH cx fpos + 0x226)) as (E32 & E33 & E34).
  remember (km_E ms3 (k_wp cx + adv) (k_wn cx - adv) (kFSH cx fpos + 0x226)) as E eqn:HEdef.
  assert (BV18 : bv_unsigned (ew E 18%nat) = ka0 cx) by (apply km_bv; [exact E18 | lia]).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  rewrite (km_ms_shape ms3 (BASE + kpc KP_MSG0) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
  assert (HS0 : st_ok_pi SEGS pa_val E (mkSS (kpc KP_MSG0) sr_atoms [km_curA; km_slA] None (mkFacts km_atoms [] []))
                 (mkst (ms_regs ms3) (w64 (BASE + kpc KP_MSG0)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - subst E. unfold km_E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + unfold km_curA, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite BV18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS E _ (ka0 cx) 0 8 (SOff 32 0) (k_wp cx + adv));
            [apply sv_off0; exact E32 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HCP].
        * apply (chunk_ok_val SEGS E _ (ka0 cx) 8 8 (SOff 33 0) (k_wn cx - adv));
            [apply sv_off0; exact E33 | cbn; lia | cbn; lia | exact HCN].
      + unfold km_slA, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite BV9. split; [lia|]. split; [lia|].
        split; [intros o Ho; apply kn_apresent_writable;
                apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * exact (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x58 (SLit 4112) 4112 eq_refl
            (kn_slot_of cx W3 ms3 sl KS_NW NW_SIZE HSL Hnw)).
        * exact (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x80 (SOff 34 0) (kFSH cx fpos + 0x226)
            (sv_off0 E 34 _ E34) (kn_slot_of cx W3 ms3 sl KS_W2SH _ HSL Hws)).
    - apply pairwise_disjoint_of_extents.
      unfold extent_of_region, km_curA, km_slA. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite BV18, BV9.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; lia.
    - exact (km_facts SK B LAWS cx fpos k2 ly3 S3 md3 E HB HJB E18 E9 E20). }
  assert (HD19 : sv_denot E (SOff 18 8) = getr (ms_regs ms3) (Z_to_bv 5 19)).
  { transitivity (w64 (ka0 cx + 8)).
    - cbn [sv_denot]. rewrite E18. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    - symmetry. exact (kn_reg_of ms3 rl 19 _ HRL H19). }
  assert (HD24 : sv_denot E (km_sh 18 8) = getr (ms_regs ms3) (Z_to_bv 5 24)).
  { rewrite (km_denot_sh E 18 (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
    symmetry. exact (kn_reg_of ms3 rl 24 _ HRL H24). }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 19) (SOff 18 8) HS0 eq_refl HD19) as HS1.
  pose proof (ast_ok_pi_set_reg_fp E _ _ (Z_to_bv 5 24) (km_sh 18 8) HS1 eq_refl HD24) as HS2.
  exact HS2.
Qed.

(* the state at +0x1e7c *)
Lemma ma_seatZ : forall cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv g,
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kat B cx fpos KP_MZ rl sl (kfsh 0xf8 0xf8 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 ->
  In (KS_W2SH, kFSH cx fpos + 0x226) sl ->
  st_ok_pi SEGS pa_val (km_E ms3 0 0 (kFSH cx fpos + 0x226)) km_ssZ (restrict (w_H W3) ms3).
Proof.
  intros cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv g HB HJ HK Hws.
  pose proof HK as (HMS & HR0 & _ & _ & _ & _ & HSL & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & S6 & S7 & S8 & S9 & _).
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1, S6.
  destruct (km_E0 cx ms3 0 0 (kFSH cx fpos + 0x226) HR0) as (E18 & E9 & E20 & _).
  destruct (km_E_ext ms3 0 0 (kFSH cx fpos + 0x226)) as (_ & _ & E34).
  remember (km_E ms3 0 0 (kFSH cx fpos + 0x226)) as E eqn:HEdef.
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  rewrite (km_ms_shape ms3 (BASE + kpc KP_MZ) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
  apply pa_entry_st_ok_full.
  - subst E. unfold km_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold km_slZ, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite BV9. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply kn_apresent_writable;
            apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia|].
    apply Forall_cons; [|apply Forall_nil].
    exact (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x80 (SOff 34 0) (kFSH cx fpos + 0x226)
      (sv_off0 E 34 _ E34) (kn_slot_of cx W3 ms3 sl KS_W2SH _ HSL Hws)).
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - exact (km_facts SK B LAWS cx fpos k2 ly3 S3 md3 E HB HJB E18 E9 E20).
Qed.

(* +0x594 -> +0x5b4 *)
Theorem kn_m5a : forall POST Rc, kfrom SK B POST (kin_m5b4 B Rc) -> kfrom SK B POST (kin_msg0 B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HK).
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & S6 & S7 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1, S6.
  pose proof (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2). unfold kHighMemBeg in FS2.
  pose proof (ma_seatA cx fpos k2 ly3 S3 W3 ms3 md3 _ _ adv (Some j) HB HJ HK
    ltac:(unfold kregs_chunk; km_inl) ltac:(unfold kregs_chunk; km_inl)
    ltac:(apply in_or_app; left; unfold kslots_setup; km_inl)
    ltac:(apply in_or_app; left; unfold kslots_setup; km_inl)) as HS.
  destruct (km_E0 cx ms3 (k_wp cx + adv) (k_wn cx - adv) (kFSH cx fpos + 0x226) HR0) as (E18 & E9 & E20 & _).
  destruct (km_E_ext ms3 (k_wp cx + adv) (k_wn cx - adv) (kFSH cx fpos + 0x226)) as (E32 & E33 & E34).
  assert (E22 : ew (km_E ms3 (k_wp cx + adv) (k_wn cx - adv) (kFSH cx fpos + 0x226)) 22%nat = w64 ci).
  { rewrite (km_E_reg _ _ _ _ 22 (Z_to_bv 5 22) eq_refl).
    exact (kn_reg_of ms3 _ 22 ci HRL ltac:(unfold kregs_chunk; km_inl)). }
  pose proof (km_E_agree ms3 (k_wp cx + adv) (k_wn cx - adv) (kFSH cx fpos + 0x226)) as HAG.
  remember (km_E ms3 (k_wp cx + adv) (k_wn cx - adv) (kFSH cx fpos + 0x226)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  assert (SHOK : sh_ok SEGS km_Bx km_SHA E (mrestrict (w_H W3) (ms_mem ms3)))
    by exact (km_shok SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 E HB HJ HJB HKK E18 E20).
  pose proof HS as HS0.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK km_span.
  { intros a (r & Hin & Hr). cbn [km_ssA ss_mem In] in Hin. destruct Hin as [<- | [<- | []]];
      cbn [km_curA km_slA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
    rewrite BV9 in Hr. left. split; [left; lia | lia]. }
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ms1)) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) E (ss_mem km_ssA) (w_H W3) (ms_mem ms3) (ms_mem ms1)
      (fun a => ksp1 cx + KS_CI <= a < ksp1 cx + KS_CI + 8) Hx) as UN1 end.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (ksp1 cx + KS_CI <= a < ksp1 cx + KS_CI + 8) ->
            aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { apply UN1. intros bb wlo whi x Hin Hx. cbv beta. vm_compute in Hin.
    destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hx; [lia|].
    rewrite BV9 in Hx. unfold KS_CI. lia. }
  clear UN1.
  sregion HS 1%nat HR1.
  pose proof (km_rd_of_region E (w_H W3) (ms_mem ms1) 9 (ksp1 cx) _ _ _ _ _ 0x78 (SOff 22 0) ci HR1 BV9
    ltac:(km_inl) (sv_off0 E 22 ci E22) ltac:(lia)) as RCI.
  pose proof (km_reg_same E km_ssA _ (w_H W3) ms3 ms1 [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25] HS0 HS
    ltac:(vm_compute; reflexivity)) as KEEP.
  prreg HS (Z_to_bv 5 (Z.of_nat 19)) R19. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
  prreg HS (1%bv : bv 5) R1.
  pmkst HS.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_set_shadow_00) with 0x55e74.
  eapply (km_call_mf SK B LAWS AS00 cx fpos k2 ly3 S3 W3 (ms_mem ms1) _ (ms_regs ms1) _ (POST cx) HB HJ);
    [ rewrite R10; exact E34
    | exact R11
    | rewrite (KEEP 2%bv) by reflexivity; exact (proj1 HR0)
    | rewrite (KEEP 3%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 HR0))))
    | rewrite (KEEP 4%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 (proj2 HR0)))))
    | exact R1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | ].
  intros regs2 mem2 md2 HJ2 HP2 H00 Hkeep Hpres Hsbm.
  apply (HNEXT cx fpos k2 ly3 S3 W3 _ md2 HB); [exact HJ2 | exact Hfrm |].
  unfold kin_m5b4. exists c, ci, j, adv.
  split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  apply (km_land_mf SK B LAWS cx fpos KP_MSG0 _ _ adv (Some j) k2 ly3 S3 W3 ms3 md3 _ md2 _ _ ci HB HK
    (ma_sl1 cx fpos c)).
  - intros a Ha H1 H2. cbn [ms_mem mkst]. rewrite (Hkeep a Ha ltac:(lia)). exact (UN a Ha H1).
  - intros i Hi. cbn [ms_mem mkst]. exact (H00 i Hi).
  - cbn [ms_mem mkst]. rewrite <- RCI. apply kk_rdword_agree. intros i Hi.
    apply Hkeep; [lia | unfold KS_CI in *; lia].
  - intros a Hp. cbn [ms_mem mkst]. apply Hpres. exact (apresent_grows _ _ _ a HG Hp).
  - rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]. repeat split; reflexivity.
  - unfold kregs0. cbn [ms_regs mkst].
    destruct HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite (km_pres _ _ _ HP2) by reflexivity; rewrite KEEP by reflexivity; assumption.
  - unfold kregs_eq, kregs_m5. cbn [ms_regs mkst].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      rewrite (km_pres _ _ _ HP2) by reflexivity;
      first [ rewrite R19, E33; reflexivity
            | rewrite KEEP by reflexivity; apply (kn_reg_of ms3 _ _ _ HRL); unfold kregs_chunk; km_inl ].
Qed.

(* +0x1e7c -> +0x1e8c *)
Theorem kn_mza : forall POST Rc, kfrom SK B POST (kin_z1e8c B Rc) -> kfrom SK B POST (kin_mz B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & HRcv & Hcr & Hci & Hj & HK).
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & HSL & HJB & HKK & HCUR & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & S5 & S6 & S7 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1, S6.
  pose proof (km_FSH_bound B LAWS cx fpos k2 ly3 S3 md3 HJB) as (FS1 & FS2). unfold kHighMemBeg in FS2.
  pose proof (ma_seatZ cx fpos k2 ly3 S3 W3 ms3 md3 _ _ _ (Some j) HB HJ HK
    ltac:(unfold kslots_setup; km_inl)) as HS.
  destruct (km_E0 cx ms3 0 0 (kFSH cx fpos + 0x226) HR0) as (E18 & E9 & E20 & _).
  destruct (km_E_ext ms3 0 0 (kFSH cx fpos + 0x226)) as (_ & _ & E34).
  assert (E22 : ew (km_E ms3 0 0 (kFSH cx fpos + 0x226)) 22%nat = w64 ci).
  { rewrite (km_E_reg _ _ _ _ 22 (Z_to_bv 5 22) eq_refl).
    exact (kn_reg_of ms3 _ 22 ci HRL ltac:(unfold kregs_chunk; km_inl)). }
  pose proof (km_E_agree ms3 0 0 (kFSH cx fpos + 0x226)) as HAG.
  remember (km_E ms3 0 0 (kFSH cx fpos + 0x226)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  assert (SHOK : sh_ok SEGS km_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose proof HS as HS0.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  paj_run_tok RUN HS HJ SHOK km_span.
  { intros a (r & Hin & Hr). cbn [km_ssZ ss_mem In] in Hin. destruct Hin as [<- | []].
    cbn [km_slZ YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    rewrite BV9 in Hr. left. split; [left; lia | lia]. }
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  lazymatch goal with Hx : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ms1)) |- _ =>
    pose proof (kept_of_frame (segs := SEGS) E (ss_mem km_ssZ) (w_H W3) (ms_mem ms3) (ms_mem ms1)
      (fun a => ksp1 cx + KS_CI <= a < ksp1 cx + KS_CI + 8) Hx) as UN1 end.
  assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (ksp1 cx + KS_CI <= a < ksp1 cx + KS_CI + 8) ->
            aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { apply UN1. intros bb wlo whi x Hin Hx. cbv beta. vm_compute in Hin.
    destruct Hin as [Hq | []]; injection Hq as <- <- <-; cbn [base_val] in Hx.
    rewrite BV9 in Hx. unfold KS_CI. lia. }
  clear UN1.
  sregion HS 0%nat HR1.
  pose proof (km_rd_of_region E (w_H W3) (ms_mem ms1) 9 (ksp1 cx) _ _ _ _ _ 0x78 (SOff 22 0) ci HR1 BV9
    ltac:(km_inl) (sv_off0 E 22 ci E22) ltac:(lia)) as RCI.
  pose proof (km_reg_same E km_ssZ _ (w_H W3) ms3 ms1 [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25] HS0 HS
    ltac:(vm_compute; reflexivity)) as KEEP.
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (1%bv : bv 5) R1.
  pmkst HS.
  rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_set_shadow_00) with 0x55e74.
  eapply (km_call_mf SK B LAWS AS00 cx fpos k2 ly3 S3 W3 (ms_mem ms1) _ (ms_regs ms1) _ (POST cx) HB HJ);
    [ rewrite R10; exact E34
    | exact R11
    | rewrite (KEEP 2%bv) by reflexivity; exact (proj1 HR0)
    | rewrite (KEEP 3%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 HR0))))
    | rewrite (KEEP 4%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 (proj2 HR0)))))
    | exact R1
    | apply ret_ok_codeptr_v; [lia | reflexivity]
    | ].
  intros regs2 mem2 md2 HJ2 HP2 H00 Hkeep Hpres Hsbm.
  apply (HNEXT cx fpos k2 ly3 S3 W3 _ md2 HB); [exact HJ2 | exact Hfrm |].
  unfold kin_z1e8c. exists c, ci, j.
  split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
  apply (km_land_mf SK B LAWS cx fpos KP_MZ _ _ _ (Some j) k2 ly3 S3 W3 ms3 md3 _ md2 _ _ ci HB HK
    (ma_sl0 cx fpos c)).
  - intros a Ha H1 H2. cbn [ms_mem mkst]. rewrite (Hkeep a Ha ltac:(lia)). exact (UN a Ha H1).
  - intros i Hi. cbn [ms_mem mkst]. exact (H00 i Hi).
  - cbn [ms_mem mkst]. rewrite <- RCI. apply kk_rdword_agree. intros i Hi.
    apply Hkeep; [lia | unfold KS_CI in *; lia].
  - intros a Hp. cbn [ms_mem mkst]. apply Hpres. exact (apresent_grows _ _ _ a HG Hp).
  - rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst]. repeat split; reflexivity.
  - unfold kregs0. cbn [ms_regs mkst].
    destruct HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite (km_pres _ _ _ HP2) by reflexivity; rewrite KEEP by reflexivity; assumption.
  - unfold kregs_eq, kregs_chunk. cbn [ms_regs mkst].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      rewrite (km_pres _ _ _ HP2) by reflexivity;
      rewrite KEEP by reflexivity; apply (kn_reg_of ms3 _ _ _ HRL); unfold kregs_chunk; km_inl.
Qed.

End b.
End a.
