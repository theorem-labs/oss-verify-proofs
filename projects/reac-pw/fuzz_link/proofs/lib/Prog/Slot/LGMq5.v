(* LGlue's ARM 5 (op_refused) at the SR level. Three pieces:
     LC45Arms.c45_refused_head  the loop head -> c45_13c70, the call of mark_quietly at 0x13c70 (cut_evt);
     lfr_mark                   the call -> its return 0x13c74, where lgmq5_post turns the call cut and
                                mark_quietly's Post (lmq_post) into LC45Defs' return cut c45_13c74, up to
                                ms_eqv (a0 = NULL when the op word w is odd, else the marks block);
     LC45Arms.c45_refused_end   0x13c74 -> the next loop head or the exit (cut_evt_or). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import check_write_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memfile_c reac_served_mark_c mark_quietly_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require StdioModel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs LFr LFrEn LFrLo
  LFrRun LFrMqDefs LFrMq LGlue LC45Defs LC45Call LC45Arms LC3LoopLib LGMqLib LGMqKeep LGMqArm.
Import ListNotations.
Local Open Scope Z_scope.

(* the return cut the step reaches: c45_13c74 up to ms_eqv *)
Definition lgmq5_ret (E : lenv) (i : Z) (gp : word) : machine_state -> Prop :=
  eqv_cl (fun c => exists w, c45_13c74 E i gp w c).

(* op_refused's name argument: "" (bit 1 of w) or NULL *)
Lemma lgmq5_name : forall m w, policy_ro m -> mem_inv rsegs m -> lgmq_name m (c45_mq_a1 w) (c45_mq_nm w).
Proof.
  intros m w PR MI. unfold lgmq_name, c45_mq_a1, c45_mq_nm.
  destruct (Z.testbit w 1).
  - split; [split; [unfold A_EMPTY; lia | exact (proj2 (proj2 (proj2 PR)))]|].
    intros t Ht. injection Ht as <-.
    split; [cbn; lia|]. split; [left; unfold A_RO_LO, A_RO_END, A_EMPTY; lia|].
    eexists. split; [exact (c3l_empty_slack m MI)|]. reflexivity.
  - split; [reflexivity|]. intros t Ht. discriminate Ht.
Qed.

Section G5.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.

Hypothesis CMK : check_mark_contract.
Hypothesis CRQ : check_requests_contract.

Hypothesis MQ : forall fx' : YK11.FPState, @mark_quietly_contract fx' rc B API.

(* mark_quietly's premises at 0x13c70 *)
Lemma lgmq5_pre : forall g md mk hb T i w ms sink,
  lenv_ok (lg_E g md mk) -> hb_inv g (lg_E g md mk) hb T ->
  c45_13c70 (lg_E g md mk) i (lg_gp g) w ms -> lmq_sink B g hb T sink ->
  exists tab kbs nm, lmq_arm g hb (ms_regs ms) (ms_mem ms) sink tab kbs nm.
Proof.
  intros g md mk hb T i w ms sink OK HI H Hs.
  destruct H as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0
                 & P & N & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & Hi & Hw & FRm & CUR & B40 & B256 & KMG
                 & KNS & MNR & KEEP & MACH).
  subst ms. cbn [ms_regs ms_mem MS].
  destruct KMG as (KA & KW & IT & KO & KMI & KOC & KOB & MA & MW & GA & GW & GAR).
  destruct KEEP as (GN & OD & PR & LA & TX & IP & ER & GD & PL).
  destruct MACH as (MI & TM & ST).
  exists link_tab, kbs, (c45_mq_nm w).
  assert (Hop : nk_opened kbs <= 64 * 47) by lia.
  assert (Ha0 : c45_mq_a0 (lg_E g md mk) w = 0 \/ c45_mq_a0 (lg_E g md mk) w = mk)
    by (unfold c45_mq_a0; destruct (Z.odd w); [left | right]; reflexivity).
  refine (lgmq_arm B API FF g md mk hb T _ m0 sink kbs (c45_mq_a0 (lg_E g md mk) w) (c45_mq_a1 w)
            (c45_mq_nm w) OK HI Hs _ _ _ Ha0 _ (lgmq5_name m0 w PR MI)
            KA KW KO IT Hop KOC PR IP ER GD MI (fun _ => ex_intro _ gbs (conj GA GW))); reflexivity.
Qed.

(* the return cut at 0x13c74, from the call cut and mark_quietly's Post *)
Lemma lgmq5_post : forall g md mk hb T i w ms sink tab kbs nm regs' F' fc' m' sink',
  LGV B API g -> lenv_ok (lg_E g md mk) -> hb_inv g (lg_E g md mk) hb T ->
  c45_13c70 (lg_E g md mk) i (lg_gp g) w ms -> lmq_sink B g hb T sink ->
  lmq_arm g hb (ms_regs ms) (ms_mem ms) sink tab kbs nm ->
  lmq_post B g hb T (ms_regs ms) (ms_mem ms) sink tab kbs nm regs' fc' m' sink' ->
  lgmq5_ret (lg_E g md mk) i (lg_gp g) (MS regs' F' (Z_to_bv 64 C45_MQ_RA) fc' None m' (seg_rom rsegs)).
Proof.
  intros g md mk hb T i w ms sink tab kbs nm regs' F' fc' m' sink' HV OK HI H Hs Ha Hp.
  pose proof (lgmq_pl B API FF g md mk HV OK) as (HPL & HPT).
  pose proof OK as (HS1 & HS2 & HS3 & (Bd1 & Bd2 & Bd3) & (Bk1 & Bk2 & Bk3) & _ & _ & _ & _ & _ & _ & _ & Hsv).
  assert (Emk : e_mk (lg_E g md mk) = mk) by reflexivity.
  destruct H as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0
                 & P & N & kbs0 & mbs & gbs & j0 & j1 & j2 & EQ & FC & Hi & Hw & FRm & CUR & B40 & B256 & KMG
                 & KNS & MNR & KEEP & MACH).
  subst ms. cbn [ms_regs ms_mem MS] in Ha, Hp. unfold c45_R in Ha, Hp.
  set (a0 := c45_mq_a0 (lg_E g md mk) w) in *.
  assert (Ha0 : a0 = 0 \/ a0 = mk) by (unfold a0, c45_mq_a0; destruct (Z.odd w); [left | right]; reflexivity).
  assert (Ha1 : 0 <= c45_mq_a1 w < 2 ^ 64) by (unfold c45_mq_a1, A_EMPTY; destruct (Z.testbit w 1); lia).
  destruct KMG as (KA0 & KW & IT0 & KO & KMI & KOC & KOB & MA & MW & GA & GW & GAR).
  destruct KEEP as (GN & OD & PR & LA & TX & IP & ER & GD & PL).
  destruct MACH as (MI & TM & ST).
  destruct Ha as (KA & _ & _ & IT & _ & _ & _ & SA & _).
  rewrite lgmq_g11, (lgmq_uw (c45_mq_a1 w) Ha1) in SA.
  pose proof (lgmq_nlk_inj _ _ _ KA KA0) as Ek. subst kbs.
  pose proof (lgmq_iftab_inj _ _ _ _ IT IT0) as Et. subst tab.
  pose proof (lgmq_str_arg_inj _ _ _ _ SA (proj1 (lgmq5_name m0 w PR MI))) as En. subst nm.
  destruct Hp as (RP & FC' & LC & LPM & _ & _ & _ & _ & (k' & _ & MFK) & Hkeep & Hfresh & H0 & H1).
  assert (Ha0r : 0 <= a0 < 2 ^ 64)
    by (destruct Ha0 as [E0 | E0]; rewrite E0; [lia | rewrite <- Emk; unfold SLOT_STACK_Z, MK_SIZE in *; lia]).
  rewrite lgmq_g10, (lgmq_uw _ Ha0r) in LC, H0, H1.
  destruct MFK as (_ & _ & _ & _ & MPO).
  assert (LC2 : lcarry (lgmq_reg (lg_E g md mk) a0) m0 m').
  { apply (lcarry_mono _ _ m0 m' (fun x Hx => lgmq_keep B API FF g md mk hb T sink sink' a0 x OK HI HPL HPT Hs
             Ha0 Hkeep Hfresh MPO Hx) LC). }
  destruct (lgmq_views _ _ _ _ LC2 GN OD PR LA TX IP) as (GN1 & OD1 & PR1 & LA1 & TX1 & IP1).
  destruct (lgmq_mach g md mk m' LPM) as (MI1 & TM1 & ST1 & ER1 & GD1).
  destruct FRm as (FP & FC8 & SV).
  assert (Hsp : c45_sp (lg_E g md mk) = e_S (lg_E g md mk) - SLOT_FRAME) by reflexivity.
  assert (FR1 : c45_frame (lg_E g md mk) j0 P N m').
  { split; [|split].
    - refine (lgmq_frame_cells _ a0 m0 m' _ _ _ _ LC2 FP); [rewrite Hsp; lia|].
      change (Z.of_nat (cells_size (c45_ptrs (lg_E g md mk) j0))) with 64. rewrite Hsp. unfold SLOT_FRAME. lia.
    - refine (lgmq_frame_cells _ a0 m0 m' _ _ _ _ LC2 FC8); [rewrite Hsp; unfold FO_P; lia|].
      change (Z.of_nat (cells_size [C8 (wz P); C8 (wz N)])) with 16. rewrite Hsp. unfold FO_P, SLOT_FRAME. lia.
    - refine (lgmq_frame_bytes _ a0 m0 m' _ _ _ _ LC2 SV); [unfold SLOT_FRAME; lia|].
      rewrite Hsv. change (Z.of_nat 104) with 104. lia. }
  assert (B401 : rw_cells rsegs m' (c45_sp (lg_E g md mk) + FO_B40) [CB 40 j1]).
  { refine (lgmq_frame_cells _ a0 m0 m' _ _ _ _ LC2 B40); [rewrite Hsp; unfold FO_B40; lia|].
    change (Z.of_nat (cells_size [CB 40 j1])) with 40. rewrite Hsp. unfold FO_B40, SLOT_FRAME. lia. }
  assert (B2561 : rw_cells rsegs m' (c45_sp (lg_E g md mk) + FO_B256) [CB 256 j2]).
  { refine (lgmq_frame_cells _ a0 m0 m' _ _ _ _ LC2 B256); [rewrite Hsp; unfold FO_B256; lia|].
    change (Z.of_nat (cells_size [CB 256 j2])) with 256. rewrite Hsp. unfold FO_B256, SLOT_FRAME. lia. }
  pose proof (lgmq_model _ a0 m0 m' mbs LC2 MA) as MA1.
  pose proof (lgmq_payload _ a0 m0 m' LC2 PL) as PL1.
  exists (MS (Regs6ss.mkR_of regs') F' (Z_to_bv 64 C45_MQ_RA) fc' None m' (seg_rom rsegs)). split.
  2: { split; [intros r Hr; symmetry; exact (Regs6ss.mkR_of_eqv regs' r Hr)|]. repeat split. }
  exists w.
  rewrite (c45_canon_of_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' RP).
  exists (reg_get regs' 1), (reg_get regs' 5), (reg_get regs' 6), (reg_get regs' 7), (reg_get regs' 10),
    (reg_get regs' 11), (reg_get regs' 12), (reg_get regs' 13), (reg_get regs' 14), (reg_get regs' 15),
    (reg_get regs' 16), (reg_get regs' 17), s2, s3, s4, (reg_get regs' 28), (reg_get regs' 29),
    (reg_get regs' 30), (reg_get regs' 31), F', fc', m', P, N, kbs0, mbs, gbs, j0, j1, j2.
  split; [reflexivity|].
  split; [exact FC'|]. split; [exact Hi|]. split; [exact Hw|].
  split; [exact FR1|]. split; [exact CUR|]. split; [exact B401|]. split; [exact B2561|].
  split; [exact KW|]. split; [exact KO|]. split; [exact KMI|]. split; [exact KOC|]. split; [exact KOB|].
  split; [exact KNS|]. split; [exact MA1|]. split; [exact MW|]. split; [exact MNR|].
  split; [exact GW|]. split; [exact GAR|].
  split; [|split].
  - intros Hodd. assert (A0 : a0 = 0) by (unfold a0, c45_mq_a0; rewrite Hodd; reflexivity).
    destruct (H0 A0) as (R10 & KA1).
    rewrite A0 in LC2.
    split; [exact R10|]. split; [exact KA1|].
    split; [exact (lgmq_iftab _ _ m0 m' kbs0 LC2 IT0 IP) | exact (lgmq_marks0 _ m0 m' gbs LC2 GA)].
  - intros Hev. assert (A0 : a0 = e_mk (lg_E g md mk)) by (unfold a0, c45_mq_a0; rewrite Hev; reflexivity).
    rewrite A0 in H1. specialize (H1 ltac:(lia) gbs GA). cbv zeta in H1 |- *.
    destruct H1 as (R10 & GB & KB). split; [exact R10|]. split; [exact GB | exact KB].
  - split; [exact (conj GN1 (conj OD1 (conj PR1 (conj LA1 (conj TX1 (conj IP1 (conj ER1 (conj GD1 PL1))))))))|].
    exact (conj MI1 (conj TM1 ST1)).
Qed.

(* the last segment from the return cut up to ms_eqv *)
Lemma lgmq5_segB : forall E i gp ms, lenv_ok E -> lgmq5_ret E i gp ms ->
  evt rsegs (eqv_cl (fun ms' => c45_fin E i gp ms' /\ seg_fp (e_S E) (c45_hp E) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp ms OK (c & (w & H) & EQ).
  pose proof (evt_register_transport rsegs _ c ms EQ (c45_refused_end CMK CRQ E i gp w c OK H)) as TR.
  eapply evt_mono; [exact TR|]. intros a (c' & (c'' & (HR & F2) & E1) & E2).
  exists c''. split; [split; [exact HR|] | exact (c45_ms_eqv_trans _ _ _ E1 E2)].
  destruct EQ as (_ & _ & _ & _ & _ & _ & EM & _). rewrite <- EM. exact F2.
Qed.

Theorem glue_arm5 : ARM B API 5.
Proof.
  intros g md mk hb T i c OK HI Hi HC.
  pose proof (cut_T B API g L_LH hb T _ c HC) as HT.
  pose proof (lgmq_kept B API g L_LH hb T _ c HC) as HK.
  pose proof (cut_lgv B API g L_LH hb T _ c HC) as HV.
  apply (SR_bind (ms_segs B) c
           (CUT B API g MARK_QUIETLY hb T (fun ms => exists w, c45_13c70 (lg_E g md mk) i (lg_gp g) w ms))).
  { apply (cut_evt B API FF g L_LH hb T [(e_md (lg_E g md mk), MD_SIZE); (e_mk (lg_E g md mk), MK_SIZE)] _
             MARK_QUIETLY _ c HC (hp_md_mk g (lg_E g md mk) hb T HI HT)).
    - intros ms (HL & HO). exact (c45_refused_head (lg_E g md mk) i (lg_gp g) ms OK HL HO).
    - intros ms' (w & H).
      destruct H as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F0 & fc0
                     & m0 & P0 & N0 & y0 & y1 & y2 & y3 & y4 & y5 & -> & FC & _).
      eexists _, _, _, _. split; [reflexivity | exact FC]. }
  intros c1 HC1.
  apply (SR_bind (ms_segs B) c1
           (fun c' => exists f, CUT B API g C45_MQ_RA (lmq_hb T f hb) [(f, MF_BLOCK)]
                                  ((fun _ => lgmq5_ret (lg_E g md mk) i (lg_gp g)) f) c')).
  { apply (lfr_mark_ok B API FF MQ g hb T C45_MQ_RA _ (fun _ => lgmq5_ret (lg_E g md mk) i (lg_gp g)) c1
             (lgmq_room g _ hb T HI HT) ltac:(unfold C45_MQ_RA; lia) eq_refl HC1).
    - intros ms (w & H).
      destruct H as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F0 & fc0
                     & m0 & P0 & N0 & y0 & y1 & y2 & y3 & y4 & y5 & -> & _).
      split; [reflexivity|]. split; reflexivity.
    - intros ms sink (w & H) Hs. exact (lgmq5_pre g md mk hb T i w ms sink OK HI H Hs).
    - intros R F fc m sink tab kbs nm regs' F' fc' m' sink' (w & H) Hs Ha Hp.
      exact (lgmq5_post g md mk hb T i w _ sink tab kbs nm regs' F' fc' m' sink' HV OK HI H Hs Ha Hp). }
  intros c2 (f & HC2).
  pose proof (lgmq_kept B API g _ _ _ _ c2 HC2) as HK2.
  pose proof (lgmq_hb_next g _ hb T f HI HK HK2) as HI2.
  pose proof (cut_T B API g _ _ _ _ c2 HC2) as HT2.
  eapply SR_mono.
  - apply (cut_evt_or B API FF g C45_MQ_RA (lmq_hb T f hb) [(f, MF_BLOCK)]
             [(e_md (lg_E g md mk), MD_SIZE); (e_mk (lg_E g md mk), MK_SIZE)] _
             L_LH (fun ms => i < 47 /\ lh_ms (lg_E g md mk) (i + 1) (lg_gp g) ms)
             L_EXIT (ex_ms (lg_E g md mk) (lg_gp g)) c2 HC2 (hp_md_mk g (lg_E g md mk) _ _ HI2 HT2)).
    + intros ms HR. exact (lgmq5_segB (lg_E g md mk) i (lg_gp g) ms OK HR).
    + intros ms' (_ & H). exact (lgmq_lh_pc _ _ _ _ H).
    + intros ms' H. exact (lgmq_ex_pc _ _ _ H).
  - intros c' [H1 | H2]; unfold arm_post; exists (lmq_hb T f hb), [(f, MF_BLOCK)]; split; try exact HI2.
    + left. split.
      * destruct H1 as (fx' & L & A & regs & mem & md' & _ & _ & _ & (c0 & (Hlt & _) & _)). exact Hlt.
      * exact (cut_mono B API g L_LH _ _ _ _ c' (fun ms H => proj2 H) H1).
    + right. exact H2.
Qed.

End G5.

Print Assumptions glue_arm5.
About glue_arm5.
