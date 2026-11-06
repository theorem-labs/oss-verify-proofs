(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 199 of its 233 lines of code are new or changed and 1271 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30), the checked_memset of w2.
   Listing (internal path) (internal record, sha256 7bc02d6772b3), the same four instructions twice:
     +0x5b4 / +0x1e8c  mv a0, s5            a0 = w2
     +0x5b8 / +0x1e90  mv a1, zero
     +0x5bc / +0x1e94  ld a2, 0x58(s1)      a2 = NW_SIZE (slot KS_NW)
     +0x5c0 / +0x1e98  jal checked_memset   (0x53214)
   and the return at +0x5c4 / +0x1e9c, with w2's 4112 bytes 0: n = 0, full = 0.
   THE PROOF (km_phaseB, one lemma for both pcs): the state is rebuilt from the cut (one read-only region: the slot
   KS_NW), the engine runs to the call (no store), the call is kernel_msg0_kit.v km_call_ms (link_ajkit.v
   aj_gx_intrin_at over AMEMSET), and the cut after it is km_land_ms (kernel_kit.v kat_frame with the change set w2
   and the callee's window). kn_m5b: kin_m5b4 -> kin_m5c4; kn_mzb: kin_z1e8c -> kin_qmsg.
   Section hypotheses: LAWS, LV (the call's pc), AMEMSET.
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
Hypothesis LV : LinkVals.
Hypothesis AMEMSET : aintrin_realizes pa_segs B OSet 0x53214.

(* the state at +0x5b4 / +0x1e8c: the slot KS_NW *)
Lemma mb_seat : forall pc cx fpos rl sl sh live adv g k2 ly3 S3 W3 ms3 md3,
  kbase SK B cx ->
  kat B cx fpos pc rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 -> In (KS_NW, NW_SIZE) sl ->
  st_ok_pi SEGS pa_val (km_E ms3 0 0 0) (km_ssB pc) (restrict (w_H W3) ms3).
Proof.
  intros pc cx fpos rl sl sh live adv g k2 ly3 S3 W3 ms3 md3 HB HK Hnw.
  pose proof HK as (HMS & HR0 & _ & _ & _ & _ & HSL & HJB & _).
  destruct HMS as (Hpc & Hrv & Hsvc & Hrom & Hfr & Hfc).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof asan_consts as ((C1a & C1b) & _). assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1.
  destruct (km_E0 cx ms3 0 0 0 HR0) as (E18 & E9 & E20 & _).
  remember (km_E ms3 0 0 0) as E eqn:HEdef.
  assert (BV9 : bv_unsigned (ew E 9%nat) = ksp1 cx) by (apply km_bv; [exact E9 | lia]).
  rewrite (km_ms_shape ms3 (BASE + kpc pc) Hpc Hrv Hsvc Hrom Hfr Hfc), restrict_mkst_fx.
  apply pa_entry_st_ok_full.
  - subst E. unfold km_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold km_slB, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite BV9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    exact (km_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x58 (SLit 4112) 4112 eq_refl
      (kn_slot_of cx W3 ms3 sl KS_NW NW_SIZE HSL Hnw)).
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - exact (km_facts SK B LAWS cx fpos k2 ly3 S3 md3 E HB HJB E18 E9 E20).
Qed.

(* THE PHASE at either pc *)
Lemma km_phaseB : forall pc0 cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv g (Q : world SEGS -> config -> Prop),
  pc0 = 0x5b4 \/ pc0 = 0x1e8c ->
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kat B cx fpos pc0 rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms3 md3 ->
  In (21%nat, kW2 cx fpos) rl -> In (KS_NW, NW_SIZE) sl -> (forall ov, In ov sl -> 0x18 <= fst ov <= 0xf0) ->
  (forall rv, In rv rl -> existsb (Z.eqb (Z.of_nat (fst rv))) km_csz = true) ->
  (forall ms' md',
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
       (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
     kw_at W3 ms' (kW2 cx fpos) 0 0 ->
     kat B cx fpos (pc0 + 0x10) rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros pc0 cx fpos k2 ly3 S3 W3 ms3 md3 rl sl adv g Q Hpc HB HJ HK H21 Hnw Hsl Hcs CONT.
  pose proof HK as (HMS & HR0 & HRL & _ & _ & HSH & _ & HJB & _).
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  pose proof (kn_sp SK B cx HB) as (S1 & S2 & _ & S4 & _).
  pose proof asan_consts as ((C1a & C1b) & _). assert (HK8 : KERNEL_AK = 4640) by reflexivity. rewrite HK8 in S1.
  pose proof (mb_seat pc0 cx fpos rl sl _ true adv g k2 ly3 S3 W3 ms3 md3 HB HK Hnw) as HS.
  assert (E21 : ew (km_E ms3 0 0 0) 21%nat = w64 (kW2 cx fpos)).
  { rewrite (km_E_reg ms3 0 0 0 21 (Z_to_bv 5 21) eq_refl). exact (kn_reg_of ms3 rl 21 _ HRL H21). }
  pose proof (km_E_agree ms3 0 0 0) as HAG.
  remember (km_E ms3 0 0 0) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (SHOK : sh_ok SEGS km_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
  pose proof HS as HS0.
  pose (RUN := paj_run_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
  destruct Hpc as [-> | ->].
  - paj_run_tok RUN HS HJ SHOK km_span.
    { intros a (r & Hin & Hr). cbn [km_ssB ss_mem In] in Hin. destruct Hin as [<- | []].
      cbn [km_slB YP09.r_wlo YP09.r_whi] in Hr. lia. }
    (* the call of checked_memset and the cut after it *)
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
    lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
      assert (HM1 : ms_mem ms1 = ms_mem ms3)
        by (apply functional_extensionality; intros x; apply Hx; intros (r & Hin & Hr);
            cbn [km_ssB ss_mem In] in Hin; destruct Hin as [<- | []];
            cbn [km_slB YP09.r_wlo YP09.r_whi] in Hr; lia) end.
    pose proof (km_reg_same E (km_ssB 0x5b4) _ (w_H W3) ms3 ms1 km_csz HS0 HS ltac:(vm_compute; reflexivity)) as KEEP.
    prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
    prreg HS (1%bv : bv 5) R1.
    pmkst HS.
    rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memset) with 0x53214.
    rewrite HM1. rewrite HM1 in HJ.
    eapply (km_call_ms SK B LAWS AMEMSET cx fpos k2 ly3 S3 W3 ms3 _ (ms_regs ms1) _ Q HB HJ HJB HSH);
      [ rewrite R10; exact E21
      | exact R11
      | exact R12
      | rewrite (KEEP 2%bv) by reflexivity; exact (proj1 HR0)
      | rewrite (KEEP 3%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 HR0))))
      | rewrite (KEEP 4%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 (proj2 HR0)))))
      | exact R1
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | ].
    intros regs2 mem2 md2 HJ2 HP2 H0s Hkeep Hpres Hsbm.
    lazymatch goal with |- SRr _ _ (mkCfg ?msn _) _ =>
      assert (L : kw_at W3 msn (kW2 cx fpos) 0 0 /\
                  kat B cx fpos (0x5b4 + 0x10) rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 msn md2) end.
    { apply (km_land_ms SK B LAWS cx fpos _ rl sl adv g k2 ly3 S3 W3 ms3 md3 _ md2 _ rl HB HK Hsl).
      - intros i Hi. exact (H0s i Hi).
      - intros a Ha Hd Hw. exact (Hkeep a Ha Hd Hw).
      - intros a Ha. exact (Hpres a Ha).
      - rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
        repeat split; reflexivity.
      - unfold kregs0. cbn [ms_regs mkst].
        destruct HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
          rewrite (km_pres _ _ _ HP2) by reflexivity; rewrite KEEP by reflexivity; assumption.
      - unfold kregs_eq. cbn [ms_regs mkst]. rewrite Forall_forall. intros [r v] Hin. cbn [fst snd].
        pose proof (km_cs_bv r (Hcs (r, v) Hin)) as Hc.
        rewrite (km_pres _ _ _ HP2 Hc), (KEEP _ Hc). exact (kn_reg_of ms3 rl r v HRL Hin). }
    apply (CONT _ md2); [exact HJ2 | exact (proj1 L) | exact (proj2 L)].
  - paj_run_tok RUN HS HJ SHOK km_span.
    { intros a (r & Hin & Hr). cbn [km_ssB ss_mem In] in Hin. destruct Hin as [<- | []].
      cbn [km_slB YP09.r_wlo YP09.r_whi] in Hr. lia. }
    (* the call of checked_memset and the cut after it *)
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
    lazymatch goal with Hx : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ =>
      assert (HM1 : ms_mem ms1 = ms_mem ms3)
        by (apply functional_extensionality; intros x; apply Hx; intros (r & Hin & Hr);
            cbn [km_ssB ss_mem In] in Hin; destruct Hin as [<- | []];
            cbn [km_slB YP09.r_wlo YP09.r_whi] in Hr; lia) end.
    pose proof (km_reg_same E (km_ssB 0x1e8c) _ (w_H W3) ms3 ms1 km_csz HS0 HS ltac:(vm_compute; reflexivity)) as KEEP.
    prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12.
    prreg HS (1%bv : bv 5) R1.
    pmkst HS.
    rewrite (lv_sigma LV). change (LinkAddr.link_sigma LS___asan_memset) with 0x53214.
    rewrite HM1. rewrite HM1 in HJ.
    eapply (km_call_ms SK B LAWS AMEMSET cx fpos k2 ly3 S3 W3 ms3 _ (ms_regs ms1) _ Q HB HJ HJB HSH);
      [ rewrite R10; exact E21
      | exact R11
      | exact R12
      | rewrite (KEEP 2%bv) by reflexivity; exact (proj1 HR0)
      | rewrite (KEEP 3%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 HR0))))
      | rewrite (KEEP 4%bv) by reflexivity; exact (proj1 (proj2 (proj2 (proj2 (proj2 HR0)))))
      | exact R1
      | apply ret_ok_codeptr_v; [lia | reflexivity]
      | ].
    intros regs2 mem2 md2 HJ2 HP2 H0s Hkeep Hpres Hsbm.
    lazymatch goal with |- SRr _ _ (mkCfg ?msn _) _ =>
      assert (L : kw_at W3 msn (kW2 cx fpos) 0 0 /\
                  kat B cx fpos (0x1e8c + 0x10) rl sl (kfsh 0xf8 0 0xf3) true adv g k2 ly3 S3 W3 msn md2) end.
    { apply (km_land_ms SK B LAWS cx fpos _ rl sl adv g k2 ly3 S3 W3 ms3 md3 _ md2 _ rl HB HK Hsl).
      - intros i Hi. exact (H0s i Hi).
      - intros a Ha Hd Hw. exact (Hkeep a Ha Hd Hw).
      - intros a Ha. exact (Hpres a Ha).
      - rewrite (proj1 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
      - rewrite (proj2 (kn_sbm_fds_fs _ _ Hsbm)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
      - unfold kms. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
        repeat split; reflexivity.
      - unfold kregs0. cbn [ms_regs mkst].
        destruct HR0 as (A2 & A9 & A8 & A3 & A4 & A18 & A20).
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
          rewrite (km_pres _ _ _ HP2) by reflexivity; rewrite KEEP by reflexivity; assumption.
      - unfold kregs_eq. cbn [ms_regs mkst]. rewrite Forall_forall. intros [r v] Hin. cbn [fst snd].
        pose proof (km_cs_bv r (Hcs (r, v) Hin)) as Hc.
        rewrite (km_pres _ _ _ HP2 Hc), (KEEP _ Hc). exact (kn_reg_of ms3 rl r v HRL Hin). }
    apply (CONT _ md2); [exact HJ2 | exact (proj1 L) | exact (proj2 L)].
Qed.

(* the slots of the two cuts lie in [s1 + 0x18, s1 + 0xf8) *)
Lemma mb_sl_ok : forall cx fpos c extra, (forall ov, In ov extra -> 0x18 <= fst ov <= 0xf0) ->
  forall ov, In ov (kslots_setup cx fpos c ++ extra) -> 0x18 <= fst ov <= 0xf0.
Proof.
  intros cx fpos c extra Hx ov Hov. apply in_app_or in Hov. destruct Hov as [Hov | Hov]; [|exact (Hx ov Hov)].
  unfold kslots_setup in Hov. cbn [In] in Hov.
  repeat (destruct Hov as [<- | Hov];
    [cbv [fst KS_FSH KS_FRES KS_W1F KS_F KS_GNL KS_W1 KS_W1N KS_W1SH KS_NW KS_C KS_GQ KS_W2SH KS_MASK KS_CN
          KS_M6 KS_CSH KS_W2F KS_M4098 KS_M4093 KS_F2]; lia |]).
  destruct Hov.
Qed.

(* +0x5b4 -> +0x5c4 *)
Theorem kn_m5b : forall POST Rc, kfrom SK B POST (kin_m5c4 B Rc) -> kfrom SK B POST (kin_m5b4 B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & adv & HRcv & Hcr & Hci & Hj & HK).
  apply (km_phaseB 0x5b4 cx fpos k2 ly3 S3 W3 ms3 md3 _ _ adv (Some j) (POST cx) (or_introl eq_refl) HB HJ HK).
  - unfold kregs_m5. km_inl.
  - apply in_or_app. left. unfold kslots_setup. km_inl.
  - apply mb_sl_ok. intros ov Hov. cbn [In] in Hov.
    destruct Hov as [<- | [<- | []]]; cbv [fst KS_ROOM KS_CI]; lia.
  - intros rv Hin. unfold kregs_m5 in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [reflexivity |]). destruct Hin.
  - intros ms' md' HJ' HW HK'. apply (HNEXT cx fpos k2 ly3 S3 W3 ms' md' HB HJ' Hfrm).
    exists c, ci, j, adv. split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|]. split; [exact Hj|].
    split; [exact HW | exact HK'].
Qed.

(* +0x1e8c -> +0x1e9c *)
Theorem kn_mzb : forall POST Rc, kfrom SK B POST (kin_qmsg B Rc) -> kfrom SK B POST (kin_z1e8c B Rc).
Proof.
  intros POST Rc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & HRcv & Hcr & Hci & Hj & HK).
  apply (km_phaseB 0x1e8c cx fpos k2 ly3 S3 W3 ms3 md3 _ _ (k_wn cx) (Some j) (POST cx) (or_intror eq_refl) HB HJ HK).
  - unfold kregs_chunk. km_inl.
  - apply in_or_app. left. unfold kslots_setup. km_inl.
  - apply mb_sl_ok. intros ov Hov. cbn [In] in Hov.
    destruct Hov as [<- | []]; cbv [fst KS_CI]; lia.
  - intros rv Hin. unfold kregs_chunk in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [<- | Hin]; [reflexivity |]). destruct Hin.
  - intros ms' md' HJ' HW HK'. apply (HNEXT cx fpos k2 ly3 S3 W3 ms' md' HB HJ' Hfrm).
    exists c, ci, j, 0, 0, (k_wn cx). split; [exact HRcv|]. split; [exact Hcr|]. split; [exact Hci|].
    split; [exact Hj|]. split; [exact HW|].
    apply (km_kat_rl B cx fpos _ (kregs_chunk cx fpos ci) _ _ _ _ _ _ k2 ly3 S3 W3 ms' md' HK').
    intros x Hx. unfold kregs_chunk. cbn [In] in Hx |- *. tauto.
Qed.

End b.
End a.
