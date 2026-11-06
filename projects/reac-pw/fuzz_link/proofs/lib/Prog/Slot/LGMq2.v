(* LGlue's ARM 2 (op_mark) at the SR level. Three pieces:
     LC2A.c2_segA   the loop head -> c2_15d88, the call of mark_quietly at 0x13dac (cut_evt);
     lfr_mark       the call -> its return 0x13db0, where lgmq2_post turns the call cut and mark_quietly's
                    Post (lmq_post) into LC2Defs' return cut c2_13db0, up to ms_eqv;
     LC2B.c2_segB   0x13db0 -> the next loop head or the exit (cut_evt_or).
   The step makes the FILE f the kept block; it joins hb when this driver call opened it (lmq_hb). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import kernel_c model_read_c model_decide_c
  bcmp_c model_write_c printf_facts_c strcmp_c snprintf_c check_socket_c check_write_c check_marks_c
  check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memfile_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require StdioModel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs LFr LFrEn LFrLo
  LFrRun LFrMqDefs LFrMq LGlue LC2Defs LC2DecCall LC2A LC2B LGMqLib LGMqKeep LGMqArm.
Import ListNotations.
Local Open Scope Z_scope.

(* the return cut the step reaches: c2_13db0 up to ms_eqv *)
Definition lgmq2_ret (E : lenv) (i : Z) (gp : word) : machine_state -> Prop :=
  eqv_cl (fun c => exists s, c2_13db0 E i gp s c).

Section G2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Hypothesis KERNEL_OK : kernel_contract.
Hypothesis MODEL_READ_OK : model_read_contract.
Hypothesis MODEL_DECIDE_OK : model_decide_contract.
Hypothesis BCMP_OK : bcmp_contract.
Hypothesis MODEL_WRITE_OK : model_write_contract.
Hypothesis STRCMP_OK : strcmp_contract.
Hypothesis SNPRINTF_OK : snprintf_contract.
Hypothesis CHECK_SOCKET_OK : check_socket_contract.
Hypothesis CHECK_MARK_OK : check_mark_contract.
Hypothesis CHECK_MARKS_OK : check_marks_contract.
Hypothesis CHECK_REQUESTS_OK : check_requests_contract.

Hypothesis MQ : forall fx' : YK11.FPState, @mark_quietly_contract fx' rc B API.

(* mark_quietly's premises at 0x13dac *)
Lemma lgmq2_pre : forall g md mk hb T i s ms sink,
  lenv_ok (lg_E g md mk) -> hb_inv g (lg_E g md mk) hb T ->
  c2_15d88 (lg_E g md mk) i (lg_gp g) s ms -> lmq_sink B g hb T sink ->
  exists tab kbs nm, lmq_arm g hb (ms_regs ms) (ms_mem ms) sink tab kbs nm.
Proof.
  intros g md mk hb T i s ms sink OK HI H Hs.
  destruct H as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0 & P & N
                 & j0 & j1 & j2 & kbs0 & mbs & gbs & EQ & FC & Hi & Hs8 & FR & FX & CU & NO & KN & MKS & MA & MW
                 & MR & MM).
  subst ms. cbn [ms_regs ms_mem MS].
  destruct KN as (KA0 & KW0 & IT0 & KO0 & KMI0 & KOC0 & KOB0 & KNX0 & KNS0).
  destruct FX as (SV & GN0 & OD & PR & LA & TX & IP & ER & GD & MI & TM & ST).
  exists link_tab, kbs0, (sel_name s).
  assert (Hop : nk_opened kbs0 <= 64 * 47) by lia.
  refine (lgmq_arm B API FF g md mk hb T _ m0 sink kbs0 mk (sel_ptr s) (sel_name s) OK HI Hs _ _ _
            (or_intror eq_refl) _ NO KA0 KW0 KO0 IT0 Hop KOC0 PR IP ER GD MI
            (fun _ => ex_intro _ gbs MKS)); reflexivity.
Qed.

(* the return cut at 0x13db0, from the call cut and mark_quietly's Post *)
Lemma lgmq2_post : forall g md mk hb T i s ms sink tab kbs nm regs' F' fc' m' sink',
  LGV B API g -> lenv_ok (lg_E g md mk) -> hb_inv g (lg_E g md mk) hb T ->
  c2_15d88 (lg_E g md mk) i (lg_gp g) s ms -> lmq_sink B g hb T sink ->
  lmq_arm g hb (ms_regs ms) (ms_mem ms) sink tab kbs nm ->
  lmq_post B g hb T (ms_regs ms) (ms_mem ms) sink tab kbs nm regs' fc' m' sink' ->
  lgmq2_ret (lg_E g md mk) i (lg_gp g) (MS regs' F' (Z_to_bv 64 0x13db0) fc' None m' (seg_rom rsegs)).
Proof.
  intros g md mk hb T i s ms sink tab kbs nm regs' F' fc' m' sink' HV OK HI H Hs Ha Hp.
  pose proof (lgmq_pl B API FF g md mk HV OK) as (HPL & HPT).
  pose proof OK as (HS1 & HS2 & HS3 & (Bd1 & Bd2 & Bd3) & (Bk1 & Bk2 & Bk3) & _ & _ & _ & _ & _ & _ & _ & Hsv).
  assert (Emk : e_mk (lg_E g md mk) = mk) by reflexivity.
  destruct H as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0 & P & N
                 & j0 & j1 & j2 & kbs0 & mbs & gbs & EQ & FC & Hi & Hs8 & FR & FX & CU & NO & KN & MKS & MA & MW
                 & MR & MM).
  subst ms. cbn [ms_regs ms_mem MS] in Ha, Hp.
  destruct Ha as (KA & _ & _ & IT & _ & _ & _ & SA & _).
  rewrite lgmq_g11, (lgmq_uw (sel_ptr s)) in SA by (apply lgmq_sel_ptr_rng; lia).
  destruct KN as (KA0 & KW0 & IT0 & KO0 & KMI0 & KOC0 & KOB0 & KNX0 & KNS0).
  pose proof (lgmq_nlk_inj _ _ _ KA KA0) as Ek. subst kbs.
  pose proof (lgmq_iftab_inj _ _ _ _ IT IT0) as Et. subst tab.
  pose proof (lgmq_str_arg_inj _ _ _ _ SA (proj1 NO)) as En. subst nm.
  destruct Hp as (RP & FC' & LC & LPM & _ & _ & _ & _ & (k' & _ & MFK) & Hkeep & Hfresh & _ & H1).
  assert (Hmkr : 0 <= e_mk (lg_E g md mk) < 2 ^ 64)
    by (unfold blk_out, SLOT_STACK_Z, MK_SIZE in *; lia).
  rewrite lgmq_g10, (lgmq_uw _ Hmkr) in LC, H1.
  destruct MFK as (_ & _ & _ & _ & MPO).
  assert (LC2 : lcarry (lgmq_reg (lg_E g md mk) mk) m0 m').
  { apply (lcarry_mono _ _ m0 m' (fun x Hx => lgmq_keep B API FF g md mk hb T sink sink' mk x OK HI HPL HPT Hs
             (or_intror eq_refl) Hkeep Hfresh MPO Hx) LC). }
  specialize (H1 ltac:(lia) gbs (proj1 MKS)). cbv zeta in H1.
  destruct H1 as (R10 & GB & KB).
  destruct FX as (SV & GN0 & OD & PR & LA & TX & IP & ER & GD & MI & TM & ST).
  destruct (lgmq_views _ _ _ _ LC2 GN0 OD PR LA TX IP) as (GN1 & OD1 & PR1 & LA1 & TX1 & IP1).
  destruct (lgmq_mach g md mk m' LPM) as (MI1 & TM1 & ST1 & ER1 & GD1).
  assert (FR1 : c2_frame (lg_E g md mk) P N j0 j1 j2 m').
  { unfold c2_frame in *. refine (lgmq_frame_cells _ mk m0 m' _ _ _ _ LC2 FR);
      [lia | rewrite lo_lh_cells_size; unfold SLOT_FRAME; lia]. }
  assert (SV1 : bytes_at rsegs m' (e_S (lg_E g md mk) - 104) (e_saved (lg_E g md mk))).
  { refine (lgmq_frame_bytes _ mk m0 m' _ _ _ _ LC2 SV);
      [unfold SLOT_FRAME; lia | rewrite Hsv; change (Z.of_nat 104) with 104; lia]. }
  pose proof (lgmq_cursor _ mk m0 m' P N LC2 CU) as CU1.
  pose proof (lgmq_model _ mk m0 m' mbs LC2 MA) as MA1.
  exists (MS (Regs6ss.mkR_of regs') F' (Z_to_bv 64 0x13db0) fc' None m' (seg_rom rsegs)). split.
  2: { split; [intros r Hr; symmetry; exact (Regs6ss.mkR_of_eqv regs' r Hr)|]. repeat split. }
  exists s.
  rewrite (c2d_canon_of_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' RP).
  rewrite <- lgmq_reg10, R10.
  exists (reg_get regs' 1), (reg_get regs' 5), (reg_get regs' 6),
    (reg_get regs' 7), (reg_get regs' 11), (reg_get regs' 12),
    (reg_get regs' 13), (reg_get regs' 14), (reg_get regs' 15),
    (reg_get regs' 16), (reg_get regs' 17), s4, (reg_get regs' 28),
    (reg_get regs' 29), (reg_get regs' 30), (reg_get regs' 31),
    F', fc', m', P, N, j0, j1, j2, kbs0, mbs, gbs.
  split; [reflexivity|].
  split; [exact FC'|]. split; [exact Hi|]. split; [exact Hs8|].
  split; [exact FR1|].
  split; [exact (conj SV1 (conj GN1 (conj OD1 (conj PR1 (conj LA1 (conj TX1 (conj IP1 (conj ER1 (conj GD1
           (conj MI1 (conj TM1 ST1)))))))))))|].
  split; [exact CU1|]. split; [exact MA1|]. split; [exact MW|]. split; [exact MR|]. split; [exact MM|].
  split; [exact KW0|]. split; [exact KO0|]. split; [exact KMI0|]. split; [exact KOC0|].
  split; [exact KOB0|]. split; [exact KNX0|]. split; [exact KNS0|]. split; [exact (proj2 MKS)|].
  split; [exact GB | exact KB].
Qed.

(* segment B from the return cut up to ms_eqv *)
Lemma lgmq2_segB : forall E i gp ms, lenv_ok E -> lgmq2_ret E i gp ms ->
  evt rsegs (eqv_cl (fun ms' => ((i < 47 /\ lh_ms E (i + 1) gp ms') \/ ex_ms E gp ms') /\
                                seg_fp (e_S E) (c2_hp E) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp ms OK (c & (s & H) & EQ).
  pose proof (evt_register_transport rsegs _ c ms EQ
    (c2_segB CHECK_SOCKET_OK CHECK_MARK_OK CHECK_MARKS_OK CHECK_REQUESTS_OK E i gp s c OK H)) as TR.
  eapply evt_mono; [exact TR|]. intros a (c' & (c'' & (HR & F2) & E1) & E2).
  exists c''. split; [split; [exact HR|] | exact (c2_ms_eqv_trans _ _ _ E1 E2)].
  destruct EQ as (_ & _ & _ & _ & _ & _ & EM & _). rewrite <- EM. exact F2.
Qed.

Theorem glue_arm2 : ARM B API 2.
Proof.
  intros g md mk hb T i c OK HI Hi HC.
  pose proof (cut_T B API g L_LH hb T _ c HC) as HT.
  pose proof (lgmq_kept B API g L_LH hb T _ c HC) as HK.
  pose proof (cut_lgv B API g L_LH hb T _ c HC) as HV.
  apply (SR_bind (ms_segs B) c
           (CUT B API g MARK_QUIETLY hb T (fun ms => exists s, c2_15d88 (lg_E g md mk) i (lg_gp g) s ms))).
  { apply (cut_evt B API FF g L_LH hb T [(e_md (lg_E g md mk), MD_SIZE); (e_mk (lg_E g md mk), MK_SIZE)] _
             MARK_QUIETLY _ c HC (hp_md_mk g (lg_E g md mk) hb T HI HT)).
    - intros ms (HL & HO).
      exact (c2_segA KERNEL_OK MODEL_READ_OK MODEL_DECIDE_OK BCMP_OK MODEL_WRITE_OK STRCMP_OK SNPRINTF_OK
               (lg_E g md mk) i (lg_gp g) ms OK HL HO).
    - intros ms' (s & H).
      destruct H as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0
                     & P0 & N0 & y0 & y1 & y2 & y3 & y4 & y5 & -> & FC & _).
      eexists _, _, _, _. split; [reflexivity | exact FC]. }
  intros c1 HC1.
  apply (SR_bind (ms_segs B) c1
           (fun c' => exists f, CUT B API g 0x13db0 (lmq_hb T f hb) [(f, MF_BLOCK)]
                                  ((fun _ => lgmq2_ret (lg_E g md mk) i (lg_gp g)) f) c')).
  { apply (lfr_mark_ok B API FF MQ g hb T 0x13db0 _ (fun _ => lgmq2_ret (lg_E g md mk) i (lg_gp g)) c1
             (lgmq_room g _ hb T HI HT) ltac:(lia) eq_refl HC1).
    - intros ms (s & H).
      destruct H as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0
                     & P0 & N0 & y0 & y1 & y2 & y3 & y4 & y5 & -> & _).
      split; [reflexivity|]. split; reflexivity.
    - intros ms sink (s & H) Hs. exact (lgmq2_pre g md mk hb T i s ms sink OK HI H Hs).
    - intros R F fc m sink tab kbs nm regs' F' fc' m' sink' (s & H) Hs Ha Hp.
      exact (lgmq2_post g md mk hb T i s _ sink tab kbs nm regs' F' fc' m' sink' HV OK HI H Hs Ha Hp). }
  intros c2 (f & HC2).
  pose proof (lgmq_kept B API g _ _ _ _ c2 HC2) as HK2.
  pose proof (lgmq_hb_next g _ hb T f HI HK HK2) as HI2.
  pose proof (cut_T B API g _ _ _ _ c2 HC2) as HT2.
  eapply SR_mono.
  - apply (cut_evt_or B API FF g 0x13db0 (lmq_hb T f hb) [(f, MF_BLOCK)]
             [(e_md (lg_E g md mk), MD_SIZE); (e_mk (lg_E g md mk), MK_SIZE)] _
             L_LH (fun ms => i < 47 /\ lh_ms (lg_E g md mk) (i + 1) (lg_gp g) ms)
             L_EXIT (ex_ms (lg_E g md mk) (lg_gp g)) c2 HC2 (hp_md_mk g (lg_E g md mk) _ _ HI2 HT2)).
    + intros ms HR. exact (lgmq2_segB (lg_E g md mk) i (lg_gp g) ms OK HR).
    + intros ms' (_ & H). exact (lgmq_lh_pc _ _ _ _ H).
    + intros ms' H. exact (lgmq_ex_pc _ _ _ H).
  - intros c' [H1 | H2]; unfold arm_post; exists (lmq_hb T f hb), [(f, MF_BLOCK)]; split; try exact HI2.
    + left. split.
      * destruct H1 as (fx' & L & A & regs & mem & md' & _ & _ & _ & (c0 & (Hlt & _) & _)). exact Hlt.
      * exact (cut_mono B API g L_LH _ _ _ _ c' (fun ms H => proj2 H) H1).
    + right. exact H2.
Qed.

End G2.

Print Assumptions glue_arm2.
About glue_arm2.
