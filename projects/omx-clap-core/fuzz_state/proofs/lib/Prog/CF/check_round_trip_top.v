(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names, addresses and numbers changed; 556 of its 631 lines of code are new or changed and 671 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/past_nul.v, with its module names changed; 711 of its 786 lines of code are new or changed and 556 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_as_written.v, with its module names, addresses and numbers changed; 1716 of its 1784 lines of code are new or changed and 718 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_no_overread.v, with its module paths, module names and numbers changed; 1316 of its 1472 lines of code are new or changed and 1628 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_calls.v; 223 of its 404 lines of code are new or changed and 1291 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_sd5.v; 137 of its 201 lines of code are new or changed and 340 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL01 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger LedgerFacts HState ReaderRes WriterSpec PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import KindBGlue HStateRoom fuzz_free_c fuzz_malloc_c preset_base64_encode_c preset_base64_decode_c pj_string_c pj_set_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterApp WriterAppFacts WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import put_c put_string_c indent_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import check_round_trip_runs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import check_round_trip_c check_round_trip_glue check_round_trip_calls check_round_trip_stages_a check_round_trip_stages_b check_round_trip_st8 check_round_trip_stdefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB WriterSpecFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require fuzz_free check_no_overread.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.

(* check_round_trip (check_4, plain, 0x138ac): the top. From the function's entry (check_round_trip_contract), the
   prologue crt_r0 to the call of preset_base64_encode (c0), then stage 0 (St0, check_round_trip_stdefs.v), whose
   conclusion crt_post is the contract's post. *)

#[local] Set Default Proof Using "All".

(* The frame registers right after the prologue: sp - 336 and the untouched gp, tp, s10, s11. *)
Lemma top_RF : forall regs (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  sp = Z_to_bv 64 (spZ regs - 336) -> gp = getr regs 3 -> tp = getr regs 4 -> s10 = getr regs 26 ->
  s11 = getr regs 27 ->
  RF regs (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
Proof.
  intros regs ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    E2 E3 E4 E26 E27. subst sp gp tp s10 s11.
  split; [reflexivity|]. intros k Hk. destruct Hk as [->|[->|[->| ->]]]; reflexivity.
Qed.

(* Cells written on the normalized memory, in the memory it stands for. *)
Lemma top_rw_rel : forall m m0 a cs, mem_rel rsegs m m0 -> Step.rw_cells rsegs m0 a cs -> Step.rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m m0 a _ HR) Hb)] | exact (wr_at_rel rsegs m m0 a _ HR Hw)].
Qed.

Section TOP.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis MAL : ms_malloc B = 0x16594.
Hypothesis FRE : ms_free B = 0x16454.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GF : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)].
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis CO : ctx_owned B API.
Hypothesis BSP : block_slack_present B API.
Hypothesis RTP : ms_tp B = strtod_c.STRTOD_TP.
Hypothesis RER : errno_addr B = strtod_c.STRTOD_ERRNO.
Hypothesis RGG : ms_got_guard B = strtod_c.STRTOD_GOT_GUARD.
Hypothesis RGD : ms_guard B = strtod_c.STRTOD_GUARD.
Hypothesis STRLEN : strlen_contract.
Hypothesis STRCMP : strcmp_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis PJO : pj_object_contract.
Hypothesis PJG : pj_get_contract.
Hypothesis PJGS : pj_get_str_contract.
Hypothesis MALLOC : forall fx' : YK11.FPState, malloc_contract (fx := fx') B API.
Hypothesis FREE : forall fx' : YK11.FPState, free_contract (fx := fx') B API.
Hypothesis FFREE : forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form.
Hypothesis ENC : forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form.
Hypothesis DEC : forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form.
Hypothesis PJS : forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form.
Hypothesis PJSET : forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form.
Hypothesis PJF : forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form.
Hypothesis PJW : forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API.
Hypothesis PJP : forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form.
Hypothesis H0 : St0.

(* A lemma of check_round_trip_stages_a.v or check_round_trip_stages_b.v at this section's variables; the entry
   state's variables follow. *)
Local Notation PF f := (f B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC
  FREE FFREE ENC DEC PJS PJSET PJF PJW PJP) (only parsing).

Lemma crt_top_sec : forall fx : YK11.FPState, check_round_trip_contract (fx := fx) B API.
Proof.
  intros fx. unfold check_round_trip_contract.
  intros L A regs mem md t tb slack bd bs bnd Lam peak cnt PRE R10 R11 R12 TB NZ SL Htl NW EX HD Hbd0 BB EK LG HCNT
    RD RSP RGT FRM ROK HS.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  pose proof alloc_ceiling_val as Hacv. pose proof alloc_ceiling_lt as Hacl.
  assert (HK : CRT_STK = 14336) by reflexivity.
  assert (RA0 : ro_agree rsegs mem) by (rewrite <- SEG; exact (proj1 RD)).
  assert (TB' : Mem.bytes_at rsegs mem t (tb ++ Z_to_bv 8 0 :: slack)) by (rewrite <- SEG; exact TB).
  assert (BB' : Mem.bytes_at rsegs mem bd (bz bs)) by (rewrite <- SEG; exact BB).
  destruct EK as (k & Hin & Hk).
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ bd k HM LG Hin) as (Hb1 & Hb2 & _).
  (* the input t lies in a block of the caller, so the allocator is initialized *)
  pose proof EX as (pt & kt & Hpt & Hpt1 & Hpt2).
  destruct (HsKindB.in_blocks L A pt kt Hpt) as (q & Hq & _).
  pose proof (fuzz_free.ff_init_of_block A (q, kt) HWF Hq) as INIT.
  (* the body bs: its bytes are bytes and its length is bounded by its encoding's *)
  pose proof (WriterSpecFacts.b64_dec_ok (zs tb) bs HD) as Hbo.
  assert (Hbl : Z.of_nat (length bs) <= 9 * 2 ^ 18).
  { pose proof (check_no_overread.dec_len (zs tb) bs HD) as DL. unfold zs in DL. rewrite length_map in DL. lia. }
  (* the frame, on the normalized memory *)
  assert (IL : img_low B).
  { apply (img_low_of_check B 0x55000); [unfold img_check; rewrite SEG; vm_compute; reflexivity | lia]. }
  assert (STK : Frame.stk rsegs mem (spZ regs - CRT_STK) (spZ regs)).
  { pose proof (kb_stk B API IL CRT_STK L A regs mem md PRE ltac:(lia)) as K. rewrite SEG in K. exact K. }
  pose proof ((PF stk_normalize) L A regs mem md PRE Lam peak cnt bnd LG HCNT RSP RGT fx mem (spZ regs - CRT_STK)
    (spZ regs) RA0 STK ltac:(lia)) as STKN.
  pose proof ((PF crt_evn) L A regs mem md PRE Lam peak cnt bnd LG HCNT RSP RGT fx) as EVN.
  eapply (SR_mono (ms_segs B) _ (crt_post B API L A regs mem md Lam peak cnt bnd fx)); [| intros c' Hc; exact Hc].
  (* the prologue crt_r0: a0 = body, a1 = len, s3 = len, s4 = body, s5 = input *)
  eapply (kb_run B regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem md
    (fun R pc' m' => exists m0, (RF regs R /\ getr R 1 = Z_to_bv 64 0x138f4 /\ getr R 10 = Z_to_bv 64 bd /\
       getr R 11 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\
       getr R 20 = Z_to_bv 64 bd /\ getr R 21 = Z_to_bv 64 t /\ pc' = Z_to_bv 64 0x14d10 /\
       Step.rw_cells rsegs m0 (spZ regs - 88) (crt_cells regs) /\
       munch [(spZ regs - 336, spZ regs)] (normalize rsegs mem) m0 /\ wmono rsegs (normalize rsegs mem) m0) /\
       mem_rel rsegs m' m0 /\ ro_same rsegs mem m'));
    [exact (proj1 (kb_md B API _ _ _ _ HM)) | exact (proj2 (kb_md B API _ _ _ _ HM)) | |].
  { rewrite SEG. unfold CHECK_ROUND_TRIP, rmk. rewrite R10, R11, R12.
    apply EVN; [exact RA0|].
    eapply Exec.evt_mono.
    - eapply crt_r0; [exact STKN | unfold spZ in *; lia | apply mem_inv_normalize].
    - intros ms' (m1 & -> & FR & MU & WM & _).
      do 3 eexists. split; [reflexivity|].
      split; [apply top_RF; [f_equal; unfold spZ; lia | reflexivity ..]|].
      do 7 (split; [reflexivity|]).
      split.
      { unfold spZ, crt_cells.
        replace (bv_unsigned (getr regs 2) - 88) with (bv_unsigned (getr regs 2) + -88) by lia. exact FR. }
      split; [|exact WM].
      unfold spZ. replace (bv_unsigned (getr regs 2) - 336) with (bv_unsigned (getr regs 2) + -336) by lia.
      exact MU. }
  intros RR pc1 mem1 regs1 (m0 & (RF1 & Q1 & Q10 & Q11 & Q19 & Q20 & Q21 & -> & FR0 & MU0 & WM0) & HR & ROS) HG.
  assert (RF2 : RF regs regs1).
  { destruct RF1 as (P2 & PG). split; [rewrite HG; exact P2|]. intros kk Hkk. rewrite HG. exact (PG kk Hkk). }
  rewrite <- HG in Q1, Q10, Q11, Q19, Q20, Q21.
  (* the prologue in the real memory: it wrote only the frame *)
  pose proof (mem_rel_normalize rsegs mem RA0) as HR0.
  pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem1 m0 HR0 HR ROS MU0) as MU1.
  pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem1 m0 HR0 HR ROS WM0) as WM1.
  pose proof (ro_agree_same rsegs mem mem1 RA0 ROS) as RA1.
  pose proof (top_rw_rel mem1 m0 _ _ HR FR0) as FR1.
  assert (OUT1 : forall x, 0 <= x < alloc_ceiling -> Frame.outside [(spZ regs - 336, spZ regs)] x)
    by (intros x Hx; apply outside_one; lia).
  (* the frame invariant with nothing held, at the call of preset_base64_encode *)
  assert (CR0 : CR B API L A regs mem md Lam peak cnt bnd [] [] L A mem1 md Lam peak cnt 160%nat).
  { split.
    { split.
      { apply (kb_mid_A B API IL CRT_STK (spZ regs) L A mem md mem1 [(spZ regs - 336, spZ regs)] alloc_statics
          HM HWF HBD).
        - intros a [Ha|Ha]; [apply HWS; exact Ha | apply HER; exact Ha].
        - exact MU1.
        - rewrite SEG. exact WM1.
        - intros x Hx Hs _. apply outside_one. lia.
        - intros x Hx _. apply outside_one. lia. }
      split; [lia|]. split; [intros q' k' Hq' _; exact Hq'|]. split; [exact INIT|]. split; [exact RA1|].
      split; [|exact FR1].
      intros i Hi.
      assert (Ho : owned B L A (ms_got_guard B + i))
        by (right; unfold static_owned; right; right; right; right; left; lia).
      pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho) as Hlo.
      apply (mbyte_munch (ms_segs B) _ mem mem1 _ MU1); [lia | apply outside_one; lia]. }
    split.
    { unfold NBok. cbn [app map]. split; [intros y [] | split; [constructor | intros y []]]. }
    split; [exact (HsKindB.ledger_munch B API L A mem md mem1 _ Lam peak cnt _ HM LG MU1 OUT1)|].
    split; [lia|]. split; [lia|]. split; [exact (Permutation_refl Lam)|].
    split; rewrite bat_nil; [exact ROK | exact HS]. }
  (* the caller's bytes across the prologue: the body in a ledger block, the input and its slack outside the
     function's stack window *)
  assert (BB1 : Mem.bytes_at rsegs mem1 bd (bz bs)).
  { apply (crt_bytes_keep mem mem1 bd (bz bs) BB'). intros i Hi. unfold bz in Hi. rewrite length_map in Hi.
    apply (mbyte_munch rsegs _ mem mem1 i MU1); [lia | apply outside_one; lia]. }
  assert (TB1 : Mem.bytes_at rsegs mem1 t (tb ++ Z_to_bv 8 0 :: slack)).
  { apply (crt_bytes_keep mem mem1 t _ TB'). intros i Hi.
    pose proof TB' as (Tb0 & Tb1 & _).
    rewrite length_app in Hi, Tb1. cbn [length] in Hi, Tb1.
    pose proof (NW i ltac:(lia)) as Hw. unfold in_window in Hw.
    apply (mbyte_munch rsegs _ mem mem1 i MU1); [lia | apply outside_one; lia]. }
  exact (H0 rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG HCNT RSP RGT fx fx (fk_refl fx) FRM
    L A regs1 mem1 md Lam peak cnt 160%nat bs bd k t tb slack CR0 ltac:(unfold CRT_ALLOCS; lia) ltac:(lia)
    Hbo Hbl BB1 Hin Hk TB1 NZ SL Htl EX HD RF2 Q1 Q10 Q11 Q19 Q20 Q21).
Qed.

End TOP.

(* check_round_trip's contract from the frame facts, the contracts of its callees (in the order of St8's premises)
   and stage 0. *)
Theorem check_round_trip_top : forall (rc : YM05.RunCeil) (B : malloc_syms) (API : AllocAPI B),
  ms_segs B = rsegs -> ms_malloc B = 0x16594 -> ms_free B = 0x16454 -> errno_addr B + 4 <= alloc_ceiling ->
  globals_free B API [(G_FAIL, 8); (G_LIVE, 24)] -> YL01.AllocExtra B (aa_MR API) -> ctx_owned B API ->
  block_slack_present B API ->
  ms_tp B = strtod_c.STRTOD_TP -> errno_addr B = strtod_c.STRTOD_ERRNO ->
  ms_got_guard B = strtod_c.STRTOD_GOT_GUARD -> ms_guard B = strtod_c.STRTOD_GUARD ->
  strlen_contract /\ strcmp_contract /\ bcmp_contract /\ pj_object_contract /\ pj_get_contract /\
  pj_get_str_contract /\
  (forall fx' : YK11.FPState, malloc_contract (fx := fx') B API) /\
  (forall fx' : YK11.FPState, free_contract (fx := fx') B API) /\
  (forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form) /\
  (forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API) /\
  (forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form) ->
  St0 -> forall fx : YK11.FPState, check_round_trip_contract (fx := fx) B API.
Proof.
  intros rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD
    (STRLEN & STRCMP & BCMP & PJO & PJG & PJGS & MALLOC & FREE & FFREE & ENC & DEC & PJS & PJSET & PJF & PJW & PJP)
    H0 fx.
  exact (crt_top_sec B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE
    FFREE ENC DEC PJS PJSET PJF PJW PJP H0 fx).
Qed.
