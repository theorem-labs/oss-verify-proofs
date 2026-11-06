(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_box_model_block (0x85b44) on fuzz_ctrl's ASan build, image A: THE THEOREM pb_reac_box_model_block, the
   cgif caller-journal contract whose statement is lib/A/Prog/C_reac_box_model_block.v (pb_reac_box_model_block_stmt,
   blob 4631d95bcf7, unchanged).  rule 24: no function is proved here.  This is the final assembly of the glue of an
   already-proved run (lib/A/Prog/reac_box_model_block_glue.v, Module BmbGlue: S1 / event 1 / S2 / event 2 / S3 of
   a Theorem Labs lane's proved v1.9 run re-run as the footprint files) with standalone lemmas proved by other hands:
     ro_agree / asan_cells at a cut       reac_box_model_block_glue_rt.v   (a Theorem Labs lane, BmbGlueRT)
     the route (C) shadow premise         reac_box_model_block_glue_sr.v   (a Theorem Labs lane, BmbGlueSR)
     the range rows 5-8, 27-29            reac_box_model_block_glue_rng.v  (a Theorem Labs lane, BmbGlueRng)
     the range rows 9-16                  reac_box_model_block_glue_rng2.v (a Theorem Labs lane, BmbGlueRng2)
     the o-window rows 3, 4, 25, 26, 31   reac_box_model_block_glue_o.v    (a Theorem Labs lane, BmbGlueO)
     the write-set row 24                 reac_box_model_block_hawr.v      (a Theorem Labs lane, BmbHawr)
   and the rows the glue owns (1, 2, 18-23, 30, 32) proved below.  The rows are numbered as in
   tmb-goals.md (a working note, not in this delivery).  The theorem takes no hypothesis beyond the
   spec's parameters except TSY (the bundle's const table is ctrl's), which the composer discharges with
   A.AD2l.CtrlB_syms.  This file is downstream of the glue and of the
   hand files (they Require the glue), so the glue cannot hold it. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
(* The six core modules that ctrl's lib/A/Reusable duplicates (YI04, YI16, YK11, YK1b, YM05, YO09) are Required, never
   Imported, and written lib.Reusable.X.n (porter 04:24Z / 04:33Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YI04 YI16 YM05 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK0h YK0i YK14 YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal CtrlSyms CtrlList CtrlAddr CtrlPa CtrlPaLib CtrlBase CtrlFrame
CtrlRo YC85.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require CtrlImg.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcBox RcSynth.
(* the statement, qualified *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require C_reac_box_model_block.
#[local] Existing Instance CtrlImg.PI_ctrl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

From Ltac2 Require Ltac2.
(* The lib.Lib family is doubled under lib/A/Bz/Lib: Required from its own directory and named lib.Lib.X (a Theorem Labs lane 05:20Z). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec MState Mem Frame Cells Step ExecF StepF Regs6ss
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Reusable.YK04R Reusable.YA0nR Reusable.YG0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Img0 A.AsanRT A.ProgBridge A.MemNorm A.MemNormF
  A.MemNormTr A.ProgWorld A.ProgWorld_Fs A.ProgWorldShadow A.ProgWorldAstack A.ProgWorldCtlRt
  A.ProgWorldVisFrame A.ProgWorldVisWin A.ProgWorldVisHeap A.Prog.CtrlRo.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.RcAsanFPLib
  A.Prog.reac_box_model_block_c A.Prog.reac_box_model_block_cF A.Prog.rng_asan A.Prog.reac_box_model_block_base
  A.Prog.asan_memsetF A.Prog.ImgBounds A.Prog.reac_box_model_block_baseF A.Prog.reac_box_model_block_epi A.Prog.reac_box_model_block_epiF.


From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_box_model_block_glue reac_box_model_block_glue_sr
  reac_box_model_block_glue_rt reac_box_model_block_glue_rng reac_box_model_block_glue_rng2 reac_box_model_block_glue_o
  reac_box_model_block_hawr.
Module BmbThm.
Import reac_box_model_block_glue.BmbGlue.
Import lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame lib.Lib.Cells lib.Lib.Step.
Import A.Img0 A.AsanRT A.Prog.asan_stack_malloc_c A.Prog.RcAsanFP A.Prog.reac_box_model_block_c.
Import Reusable.YK04R Reusable.YA0nR A.ProgBridge A.MemNorm A.MemNormTr.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals), as in the _F files. *)
Import lib.Lib.ExecF lib.Lib.StepF.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------
   The rows the glue owns, as standalone lemmas: goals 18-22 (the class-0 frame's facts of bmb_frame_facts, at the
   raw memory, moved to the normalized memory) and goal 23 (the callee-saved cells at the allocator's return). *)
Section Rows.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Lemma bmb_frame_norm : forall (mem2 : word -> option byte) FS pos,
  ro_agree rsegs mem2 -> ASAN_GT <= fs_frame FS 0%nat pos ->
  bytes_at rsegs mem2 (fs_flag FS 0 pos) [Z_to_bv 8 1] ->
  bytes_at rsegs mem2 (fs_frame FS 0%nat pos + 56) (le8 (Z_to_bv 64 (fs_flag FS 0 pos))) ->
  bytes_at rsegs mem2 (shadow_addr (fs_frame FS 0%nat pos)) (repeat (Z_to_bv 8 0) 8) ->
  addressable mem2 (fs_frame FS 0%nat pos) 64 ->
  stk rsegs mem2 (fs_frame FS 0%nat pos) (fs_frame FS 0%nat pos + 64) ->
  bytes_at rsegs (normalize rsegs mem2) (fs_flag FS 0 pos) [Z_to_bv 8 1] /\
  bytes_at rsegs (normalize rsegs mem2) (fs_frame FS 0%nat pos + 56) (le8 (Z_to_bv 64 (fs_flag FS 0 pos))) /\
  bytes_at rsegs (normalize rsegs mem2) (shadow_addr (fs_frame FS 0%nat pos)) (repeat (Z_to_bv 8 0) 8) /\
  addressable (normalize rsegs mem2) (fs_frame FS 0%nat pos) 64 /\
  stk rsegs (normalize rsegs mem2) (fs_frame FS 0%nat pos) (fs_frame FS 0%nat pos + 64).
Proof.
  intros mem2 FS pos Hro Hgt Hfl H56 Hsh Had Hst.
  split; [exact (A.MemNorm.bytes_at_normalize rsegs mem2 _ _ Hro Hfl)|].
  split; [exact (A.MemNorm.bytes_at_normalize rsegs mem2 _ _ Hro H56)|].
  split; [exact (A.MemNorm.bytes_at_normalize rsegs mem2 _ _ Hro Hsh)|].
  split; [exact (A.MemNormTr.addressable_normalize mem2 _ 64 Hro Had)|].
  apply (A.MemNormTr.stk_normalize_ro mem2 _ _ Hro); [|exact Hst].
  unfold ASAN_GT in Hgt. unfold ImgBounds.IMG_HI. lia.
Qed.

Lemma bmb_hsv : forall (mem2 : word -> option byte) (sp : Z) cs,
  ro_agree rsegs mem2 -> HIGHMEM_BEG <= sp - 4272 -> sp <= APPMEM_END ->
  Z.of_nat (lib.Lib.Cells.cells_size cs) <= 104 ->
  lib.Lib.Step.rw_cells rsegs mem2 (sp + -104) cs -> lib.Lib.Step.rw_cells rsegs (normalize rsegs mem2) (sp + -104) cs.
Proof.
  intros mem2 sp cs Hro Hlo Hhi Hsz H.
  apply (A.MemNormTr.rw_cells_normalize mem2 (sp + -104) cs Hro); [|exact H].
  intros i Hi. apply A.MemNormTr.ro_addr_above_img.
  unfold HIGHMEM_BEG, APPMEM_END in *. unfold ImgBounds.IMG_HI. lia.
Qed.

Lemma saves_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  Z.of_nat (lib.Lib.Cells.cells_size (A.Prog.reac_box_model_block_base.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) <= 104.
Proof. intros. unfold A.Prog.reac_box_model_block_base.SAVES. cbn. lia. Qed.
End Rows.

Section Thm.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variables (B : asyms) (GLOBS : list (Z * Z)) (RLO RHI : Z).
Hypothesis TSY : A.AF0m.CtrlTSyms B.

Theorem pb_reac_box_model_block : C_reac_box_model_block.pb_reac_box_model_block_stmt B GLOBS RLO RHI.
Proof.
  unfold C_reac_box_model_block.pb_reac_box_model_block_stmt, C_reac_box_model_block.treac_box_model_block_spec.
  intros RELRO ROFL TL LAWS ML AMEMSET AMEMCPY ASM0 SMP ASF FFL TLF JE HJT_rng HJT_pos HJT_eq HJT_e HJ13_rng HJ14_rng
    HJ13 HJ14 HGM HIMGSH HZS_J13 HZS_J14.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b o row nb.
  intros HJ HROS Hra Hra4096 Hgp Htp Ha0 Ha1 Ha2 Rp Rb Ro Hal Hlo Hhi Hroom HPs HNs HOs.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk
    & G5 & HQT).
  pose proof Hstk as (Hal0 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof (A.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HROS ltac:(lia) ltac:(lia)) as HROP.
  destruct (reac_box_model_block_glue_rt.BmbGlueRT.bmb_rt_facts_on B LAWS TSY RLO RHI lyc Sc W memc mdc HAR HROP) as (Hro & AC0).
  assert (Ea : C_reac_box_model_block.A_reac_box_model_blockP = 0x85b44) by (vm_compute; reflexivity).
  rewrite Ea.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (ESTK : C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK = 4320) by reflexivity.
  rewrite ESTK in Hlo.
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  assert (HCL : lib.Reusable.YM05.alloc_ceiling <= spZ regs - 4320) by (rewrite <- Eslo in Hceil; lia).
  assert (HAPP : spZ regs <= APPMEM_END) by (unfold APPMEM_END; rewrite <- Eshi in H47; lia).
  assert (Hpw : forall a, spZ regs - 4272 <= a < spZ regs -> apresent (YA0n.w_H W) memc a)
    by (intros a Ha; apply Hpres; lia).
  destruct (win_facts B LAWS lyc Sc W memc mdc (spZ regs - 4272) (spZ regs) HAR Hro
              ltac:(rewrite <- Eslo in Hceil; lia) ltac:(lia) ltac:(rewrite <- Eshi in H47; lia) Hpw)
    as (ST0 & AW0 & HHM & HAE & _).
  assert (Etp : bv_unsigned (lib.Reusable.YK11.getr regs 4) = RT_TP).
  { rewrite Htp, (A.ProgWorld.as_tp_RT_TP B TSY). unfold w64, RT_TP.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  assert (FP0 : fp [0%nat] (normalize rsegs memc) (bv_unsigned (lib.Reusable.YK11.getr regs 4)) (ly_F lyc)
                  (spZ regs - 4272) (spZ regs)
                  (reac_box_model_block_W o (spZ regs)) (reac_box_model_block_D p o)).
  { rewrite Etp.
    apply (fp0_facts B LAWS TSY lyc Sc W memc mdc (spZ regs) p o HAR Hro HCL HAPP).
    - intros Hp. destruct (HPs Hp) as (_ & _ & _ & _ & P5 & P6 & _).
      unfold ASAN_GT. unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI,
        A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI in P5, P6. lia.
    - intros Ho. destruct (HOs Ho) as (Hhome & Hnimg & Htwr & Htsrc & Hsepw).
      destruct Hhome as [(cid & pos & Hin & Hcid & Hx) | [Hs1 Hs2]].
      + split; [| left; exists cid, pos; split; [exact Hin | split; [exact Hcid | exact Hx]]].
        destruct (frames_bounds AB1v.tfibsegs B LAWS _ _ _ _ _ cid pos HAR Hin) as (F1 & F2 & F3).
        pose proof (Hx o ltac:(lia)) as X0. unfold in_zr, frame_rng in X0. cbn [fst snd] in X0. lia.
      + split; [lia | right]. rewrite <- Eslo in Hceil. rewrite <- Eshi in H47.
        unfold APPMEM_END. lia. }
  (* the JOIN constants, and the premises of the route (C) shadow lemma (BmbGlueSR.reac_box_model_block_sr_on_img) *)
  lazymatch type of HJ13_rng with _ /\ ?v + 32 + 64 <= _ =>
    assert (EJ13 : v = JOIN_0013) by (vm_compute; reflexivity) end.
  lazymatch type of HJ14_rng with _ /\ ?v + 32 + 64 <= _ =>
    assert (EJ14 : v = JOIN_0014) by (vm_compute; reflexivity) end.
  rewrite EJ13 in HJ13_rng, HZS_J13. rewrite EJ14 in HJ14_rng, HZS_J14.
  assert (SRG : p <> 0 -> exists q sz, In (q, sz) GLOBS /\ q <= p /\ p + 296 <= q + sz)
    by (intros Hp; destruct (HPs Hp) as (_ & _ & _ & HG & _); exact HG).
  assert (SRN : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
            exists q sz, In (q, sz) GLOBS /\ q <= RcSynth.rname row /\
              RcSynth.rname row + Z.of_nat (length nb) <= q + sz)
    by (intros Hp Hb Hh Hr; destruct (HNs Hp Hb Hh Hr) as (_ & _ & HG & _); exact HG).
  assert (SRB : p <> 0 -> A.Prog.CtrlRo.IMG_LO + 64 <= p /\ p + 296 + 64 <= A.Prog.CtrlRo.IMG_HI)
    by (intros Hp; destruct (HPs Hp) as (_ & _ & _ & _ & P5 & P6 & _); split; [exact P5 | exact P6]).
  assert (SRR : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
            forall x, RcSynth.rname row <= x < RcSynth.rname row + Z.of_nat (length nb) ->
              in_roP AB1v.tfibsegs RLO RHI x)
    by (intros Hp Hb Hh Hr x Hx; destruct (HNs Hp Hb Hh Hr) as (_ & _ & _ & Hx' & _); exact (proj1 (Hx' x Hx))).
  assert (SRO : o <> 0 -> C_reac_box_model_block.tbmb_o_home lyc Sc o /\
                  (forall x, o <= x < o + 32 -> ~ in_img AB1v.tfibsegs x))
    by (intros Ho; destruct (HOs Ho) as (Hh & Hn & _); split; [exact Hh | exact Hn]).
  (* S1's data premises at the entry memory (the narrowed baseF.entry_pre_F reads them): what the call keeps from
     the entry memory to itself, then the row (as HP2 below), o's cells and its addressability (BmbGlueO's rows at
     the entry: S2 := Sc, mem2 := memc). *)
  assert (KREFL : acall_kept AB1v.tfibsegs B lyc Sc W memc W memc
                    (spZ regs - C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK) (spZ regs) (fun _ => False)).
  { split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    split; [intros; reflexivity|]. split; [intros a _ _ Hp; exact Hp|].
    intros a Ha. apply Hpres. lia. }
  assert (OFACTS0 : o <> 0 -> (forall a, o <= a < o + 32 -> aview AB1v.tfibsegs (YA0n.w_H W) memc a <> None) /\
                      shadow_hull_vis (aview AB1v.tfibsegs (YA0n.w_H W) memc) o 32 /\
                      ly_F lyc + 8 <= o /\ o + 32 <= APPMEM_END).
  { intros Ho. destruct (HOs Ho) as (Hhome & Hnimg & Htwr & Htsrc & Hsep).
    pose proof Htsrc as (TV & TRA & THU & TAM & TQ0 & TQ1).
    exact (bmb_o_facts B lyc Sc Sc W memc mdc memc mdc _ _ (spZ regs) o HAR HAR KREFL ltac:(lia) ltac:(lia) Hhome
             (fun a Ha => proj1 (TV a Ha)) THU). }
  assert (HP0 : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs (normalize rsegs memc) p row /\
                  (spZ regs <= p \/ p + 296 <= spZ regs - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o)).
  { intros Hp. destruct (HPs Hp) as (Hm8 & Hlen & HG & _ & P5 & P6 & Hx & Ho).
    unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in P5, P6.
    destruct (bmb_hp B lyc Sc W memc memc _ _ _ p (spZ regs) row KREFL Hro Hp Hm8 Hlen HG ltac:(lia) ltac:(lia)
                (fun x Hx' => proj2 (Hx x Hx')) ltac:(lia)) as (A1 & A2 & A3 & A4).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4 | exact Ho]. }
  assert (HOX0 : exists ob : list byte, o <> 0 ->
            rw_cells rsegs (normalize rsegs memc) o [CB 32 ob] /\
            (bv_unsigned (lib.Reusable.YK11.getr regs 2) <= o \/
             o + 32 <= bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4272) /\
            (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o))
    by (eapply reac_box_model_block_glue_o.BmbGlueO.bmb_o_HO; eassumption).
  destruct HOX0 as (ob0 & HO0).
  assert (AO0 : o <> 0 -> addressable (normalize rsegs memc) o 32 /\ app_mem (o + 32) /\
                  (o + 32 <= RT_LO \/ RT_HI <= o))
    by (eapply reac_box_model_block_glue_o.BmbGlueO.bmb_o_AO; eassumption).
  pose proof (eq_rect _ (fun n => addressable (normalize rsegs memc) (spZ regs - 4272) n) AW0 4272 ltac:(ring))
    as AW0'.
  assert (Hwx : wx_segs_nowrap AB1v.tfibsegs) by (apply wx_segs_nowrap_of_b; vm_compute; reflexivity).
  apply (bmb_to_ret B LAWS TL TLF ML SMP ASM0 Hwx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
           regs p b o row nb ob0 _ HJ Hra Hgp Htp Ha0 Ha1 Ha2 Rp Rb Ro Hal ltac:(rewrite ESTK; exact Hlo) Hhi Hroom
           Hro ST0 AC0 HHM HAE AW0' FP0 HP0 HO0 AO0).
  intros S2 regs2 mem2 md2 pos HJ2 Hfrs2 Hnin2 Eab2 Ha02 Hregs2 Hzs2 Hflag2 HK2 HJin2 Hsaves2.
  pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstk2 & _).
  destruct HJin2 as (mem1 & model1 & HMU1 & HJin2).
  (* the RO premise at the return memory: memc -> mem1 (only the window changed) -> mem2 (the callee's journal) *)
  assert (HROP1 : APostBase.arodata_okP AB1v.tfibsegs RLO RHI B (aview AB1v.tfibsegs (YA0n.w_H W) mem1)).
  { intros a Hroa Ho He. rewrite <- (HROP a Hroa Ho He).
    assert (Hi : in_img AB1v.tfibsegs a).
    { destruct Hroa as [(sg & Hsg & _ & Hr) | Hgot]; [exists sg; split; [exact Hsg | exact Hr] | exact (RELRO a Hgot)]. }
    pose proof (img_bounds_of_in_img a Hi) as Hb.
    apply (aview_munch_out W [(spZ regs - 4272, spZ regs)] memc mem1 a HMU1 ltac:(lia)).
    cbn [outside]. split; [rewrite <- Eslo in Hceil; lia | exact I]. }
  pose proof (APostBase.arodata_ok_journalP AB1v.tfibsegs RLO RHI RELRO B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJin2 HROP1)
    as HROP2.
  destruct (reac_box_model_block_glue_rt.BmbGlueRT.bmb_rt_facts_on B LAWS TSY RLO RHI lyc S2 W mem2 md2 HAR2 HROP2) as (Hro2 & AC2).
  (* S2 / S3's Section facts at m := normalize rsegs mem2 *)
  rewrite <- ?Eslo in Hceil, Hbot. rewrite <- ?Eshi in H47, Htop2, Htop.
  assert (Hpw2 : forall a, spZ regs - 4272 <= a < spZ regs -> apresent (YA0n.w_H W) mem2 a)
    by (intros a Ha; apply Hpres2; lia).
  destruct (win_facts B LAWS lyc S2 W mem2 md2 (spZ regs - 4272) (spZ regs) HAR2 Hro2
              ltac:(lia) ltac:(lia) ltac:(lia) Hpw2) as (ST2 & AW2 & HHM2 & HAE2 & _).
  destruct (bmb_frame_facts B LAWS lyc S2 W mem2 md2 pos (frames Sc) HAR2 Hfrs2 Hzs2 Hflag2)
    as (Hpos & Efa & Efl & Hfl & H56 & Hshf & Hadf & Hstf & Hfpres & Hfa64 & HFle & HFhi & HFgt).
  assert (OHOME2 : o <> 0 -> 0 <= o /\
     ((exists cid pos', In (cid, pos') (frames S2) /\ cid <> 0 /\
         forall x, o <= x < o + 32 -> in_zr x (frame_rng lyc (cid, pos'))) \/
      (lib.Reusable.YM05.alloc_ceiling <= o /\ o + 32 <= APPMEM_END))).
  { intros Ho. destruct (HOs Ho) as (Hhome & _ & _ & _ & _).
    destruct Hhome as [(cid & pos' & Hin & Hcid & Hx) | [Hs1 Hs2]].
    - destruct (frames_bounds AB1v.tfibsegs B LAWS _ _ _ _ _ cid pos' HAR Hin) as (F1 & F2 & F3).
      pose proof (Hx o ltac:(lia)) as X0. unfold in_zr, frame_rng in X0. cbn [fst snd] in X0.
      split; [lia | left; exists cid, pos'; split; [rewrite Hfrs2; right; exact Hin | split; [exact Hcid | exact Hx]]].
    - split; [lia | right]. unfold APPMEM_END. lia. }
  assert (FP2 : fp [0%nat] (normalize rsegs mem2) (bv_unsigned (lib.Reusable.YK11.getr regs 4)) (ly_F lyc)
                  (spZ regs - 4272) (spZ regs) (reac_box_model_block_W o (spZ regs)) (reac_box_model_block_D p o)).
  { rewrite Etp. apply (fp0_facts B LAWS TSY lyc S2 W mem2 md2 (spZ regs) p o HAR2 Hro2 HCL HAPP).
    - intros Hp. destruct (HPs Hp) as (_ & _ & _ & _ & P5 & P6 & _).
      unfold ASAN_GT. unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI,
        A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI in P5, P6. lia.
    - exact OHOME2. }
  assert (TLS2 : reac_box_model_block_tls (normalize rsegs mem2) (bv_unsigned (lib.Reusable.YK11.getr regs 4))
                   (ly_F lyc) (spZ regs - REAC_BOX_MODEL_BLOCK_K) (spZ regs)).
  { rewrite Etp. exact (tls0_facts B TSY lyc S2 W mem2 md2 (spZ regs - 4272) (spZ regs) HAR2 Hro2
                          ltac:(lia) ltac:(lia) HAPP). }
  (* the data facts at m *)
  assert (ROIMG : forall x, in_roP AB1v.tfibsegs RLO RHI x -> 0x10000 <= x < 0x5fe000).
  { intros x [(sg & Hsg & _ & Hr) | Hg]; apply img_bounds_of_in_img;
      [exists sg; split; [exact Hsg | exact Hr] | exact (RELRO x Hg)]. }
  unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in HJ13_rng, HJ14_rng.
  assert (HP2 : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs (normalize rsegs mem2) p row /\
                  (spZ regs <= p \/ p + 296 <= spZ regs - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o)).
  { intros Hp. destruct (HPs Hp) as (Hm8 & Hlen & HG & _ & P5 & P6 & Hx & Ho).
    unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in P5, P6.
    destruct (bmb_hp B lyc Sc W memc mem2 _ _ _ p (spZ regs) row HK2 Hro2 Hp Hm8 Hlen HG ltac:(lia) ltac:(lia)
                (fun x Hx' => proj2 (Hx x Hx')) ltac:(lia)) as (A1 & A2 & A3 & A4).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4 | exact Ho]. }
  assert (HN2 : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
                  RcBox.name_ok nb /\ bytes_at rsegs (normalize rsegs mem2) (RcSynth.rname row) nb /\
                  (spZ regs <= RcSynth.rname row \/ RcSynth.rname row + Z.of_nat (length nb) <= spZ regs - 4272) /\
                  (o = 0 \/ o + 32 <= RcSynth.rname row \/ RcSynth.rname row + Z.of_nat (length nb) <= o)).
  { intros Hp Hb Hh Hr. destruct (HNs Hp Hb Hh Hr) as (Hok & HG & _ & Hx & Ho).
    pose proof Hok as ((L1 & L2) & _ & _).
    pose proof (ROIMG _ (proj1 (Hx (RcSynth.rname row) ltac:(lia)))) as B0.
    pose proof (ROIMG _ (proj1 (Hx (RcSynth.rname row + Z.of_nat (length nb) - 1) ltac:(lia)))) as B1.
    split; [exact Hok|]. split.
    - apply (bmb_bytes_norm B lyc Sc W memc mem2 _ _ _ _ nb HK2 Hro2 HG); [lia | lia |].
      intros x Hx'. exact (proj2 (Hx x Hx')).
    - split; [right; lia | exact Ho]. }
  assert (AP2 : p <> 0 -> addressable (normalize rsegs mem2) p 296).
  { intros Hp. destruct (HPs Hp) as (_ & _ & _ & (q & sz & Hin & Hq & Hsz) & P5 & P6 & _).
    unfold A.Prog.CtrlRo.IMG_LO, A.Prog.CtrlRo.IMG_HI in P5, P6.
    exact (bmb_glob_addressable B GLOBS lyc S2 W mem2 md2 q sz p 296 HGM Hin HAR2 Hq ltac:(lia) Hsz
             ltac:(lia) ltac:(lia)). }
  assert (ANB2 : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
                   addressable (normalize rsegs mem2) (RcSynth.rname row) (Z.of_nat (length nb))).
  { intros Hp Hb Hh Hr. destruct (HNs Hp Hb Hh Hr) as (Hok & _ & (q & sz & Hin & Hq & Hsz) & Hx & _).
    pose proof Hok as ((L1 & L2) & _ & _).
    pose proof (ROIMG _ (proj1 (Hx (RcSynth.rname row) ltac:(lia)))) as B0.
    pose proof (ROIMG _ (proj1 (Hx (RcSynth.rname row + Z.of_nat (length nb) - 1) ltac:(lia)))) as B1.
    exact (bmb_glob_addressable B GLOBS lyc S2 W mem2 md2 q sz (RcSynth.rname row) (Z.of_nat (length nb)) HGM Hin HAR2 Hq ltac:(lia) Hsz
             ltac:(lia) ltac:(lia)). }
  assert (AJ1x : b = 1 -> addressable (normalize rsegs mem2) JOIN_0014 32).
  { intros _. destruct HZS_J14 as (q & mm & Hin & Hq & Hm).
    pose proof HAR2 as (M2 & _). pose proof (am_syms _ _ _ _ M2) as SOK.
    pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ SOK) _ Hin) as (Z1 & Z2 & Z3 & Z4 & Z5).
    cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
    exact (bmb_zs_addressable B LAWS lyc S2 W mem2 md2 q mm JOIN_0014 32 HAR2 Hro2 Hin Hq ltac:(lia)
             ltac:(clear - Hm Z4; Z.div_mod_to_equations; lia)). }
  assert (AJ2x : b = 2 -> addressable (normalize rsegs mem2) JOIN_0013 32).
  { intros _. destruct HZS_J13 as (q & mm & Hin & Hq & Hm).
    pose proof HAR2 as (M2 & _). pose proof (am_syms _ _ _ _ M2) as SOK.
    pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ SOK) _ Hin) as (Z1 & Z2 & Z3 & Z4 & Z5).
    cbn [fst snd] in Z1, Z2, Z3, Z4, Z5.
    exact (bmb_zs_addressable B LAWS lyc S2 W mem2 md2 q mm JOIN_0013 32 HAR2 Hro2 Hin Hq ltac:(lia)
             ltac:(clear - Hm Z4; Z.div_mod_to_equations; lia)). }
  assert (NDJ2 : p <> 0 -> (b = 5 \/ b = 6) -> RcSynth.has row <> 0 -> RcSynth.rname row <> 0 ->
                   fp_dj [(RcSynth.rname row, RcSynth.rname row + Z.of_nat (length nb))] (fp_w [0%nat] (ly_F lyc))).
  { intros Hp Hb Hh Hr. destruct (HNs Hp Hb Hh Hr) as (Hok & _ & _ & Hx & _).
    pose proof Hok as ((L1 & L2) & _ & _).
    pose proof (ROIMG _ (proj1 (Hx (RcSynth.rname row) ltac:(lia)))) as B0.
    pose proof (ROIMG _ (proj1 (Hx (RcSynth.rname row + Z.of_nat (length nb) - 1) ltac:(lia)))) as B1.
    exact (bmb_ndj B lyc S2 W mem2 md2 (RcSynth.rname row) (Z.of_nat (length nb)) HAR2 ltac:(lia) ltac:(lia)). }
  (* the footprint facts at RNG := RNG_W (hidden_plus (w_H W) (ly_F lyc)) *)
  destruct (bmb_FS_app B lyc S2 W mem2 md2 HAR2) as (FA0 & FAapp & FAgt).
  unfold kFakeStackSize, kLowShadowBeg, kHighMemBeg in FAapp.
  assert (HFSsp : ly_F lyc + FS_SIZE <= spZ regs - 4272) by (unfold FS_SIZE; clear - FAapp HCL C1; lia).
  destruct (bmb_win_rng B LAWS lyc S2 W mem2 md2 (spZ regs) HAR2 HFSsp ltac:(clear - Hslo Hlo Eslo; lia)
              ltac:(clear - Hhi Hshi Eshi; lia) HAPP Hpw2)
    as (Rwin2 & Rwsh2 & Rwsw2).
  destruct (bmb_fs_rng B lyc S2 W mem2 md2 HAR2) as (RFSw2 & RFSsh2).
  assert (OFACTS : o <> 0 -> (forall a, o <= a < o + 32 -> aview AB1v.tfibsegs (YA0n.w_H W) mem2 a <> None) /\
                     shadow_hull_vis (aview AB1v.tfibsegs (YA0n.w_H W) mem2) o 32 /\
                     ly_F lyc + 8 <= o /\ o + 32 <= APPMEM_END).
  { intros Ho. destruct (HOs Ho) as (Hhome & Hnimg & Htwr & Htsrc & Hsep).
    pose proof Htsrc as (TV & TRA & THU & TAM & TQ0 & TQ1).
    exact (bmb_o_facts B lyc Sc S2 W memc mdc mem2 md2 _ _ (spZ regs) o HAR HAR2 HK2 ltac:(clear - HCL ESTK; lia) Hsep Hhome
             (fun a Ha => proj1 (TV a Ha)) THU). }
  (* the route (C) shadow premise at the allocator's return memory *)
  assert (SRO2 : o <> 0 -> C_reac_box_model_block.tbmb_o_home lyc S2 o /\
                   (forall x, o <= x < o + 32 -> ~ in_img AB1v.tfibsegs x)).
  { intros Ho. destruct (HOs Ho) as (Hh & Hn & _). split; [|exact Hn].
    destruct Hh as [(cid & pos' & Hin & Hcid & Hx) | Hs]; [left | right; exact Hs].
    exists cid, pos'. split; [rewrite Hfrs2; right; exact Hin | split; [exact Hcid | exact Hx]]. }
  pose proof (reac_box_model_block_glue_sr.BmbGlueSR.reac_box_model_block_sr_on_img B GLOBS TSY LAWS HGM HIMGSH
                HZS_J13 HZS_J14 lyc S2 W mem2 md2 (spZ regs) p b o row nb HAR2 Hro2
                ltac:(unfold REAC_BOX_MODEL_BLOCK_K; clear - Hslo Hlo Eslo; lia) ltac:(clear - Hhi Hshi Eshi; lia)
                SRG SRN SRO2 RLO RHI SRB SRR RELRO) as SR2.
  (* row 3 (HO): o's cells at the return memory, with the witness ob (BmbGlueO.bmb_o_HO, its witness before the
     o <> 0 guard) *)
  assert (HOX : exists ob : list byte, o <> 0 ->
            rw_cells rsegs (normalize rsegs mem2) o [CB 32 ob] /\
            (bv_unsigned (lib.Reusable.YK11.getr regs 2) <= o \/
             o + 32 <= bv_unsigned (lib.Reusable.YK11.getr regs 2) - 4272) /\
            (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o))
    by (eapply reac_box_model_block_glue_o.BmbGlueO.bmb_o_HO; eassumption).
  destruct HOX as (ob & HO2).
  (* the return state, in the tail's register shape *)
  change (lib.Reusable.YK11.mkst regs2 (w64 0x85bbc) mem2 (lib.Reusable.YK11.seg_rom AB1v.tfibsegs))
    with (lib.Lib.MState.MS regs2 fp_regs (w64 0x85bbc) fp_csr None mem2 (lib.Reusable.YK11.seg_rom AB1v.tfibsegs)).
  apply (SRr_xregs_eqv AB1v.tfibsegs W (lib.Lib.Regs6ss.mkR_of regs2) regs2);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs2))].
  destruct Hregs2 as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
  change (lib.Reusable.YK11.getr regs2 2) with (reg_get regs2 2) in R2. change (lib.Reusable.YK11.getr regs2 3) with (reg_get regs2 3) in R3.
  change (lib.Reusable.YK11.getr regs2 4) with (reg_get regs2 4) in R4. change (lib.Reusable.YK11.getr regs2 8) with (reg_get regs2 8) in R8.
  change (lib.Reusable.YK11.getr regs2 9) with (reg_get regs2 9) in R9. change (lib.Reusable.YK11.getr regs2 10) with (reg_get regs2 10) in Ha02.
  change (lib.Reusable.YK11.getr regs2 18) with (reg_get regs2 18) in R18. change (lib.Reusable.YK11.getr regs2 19) with (reg_get regs2 19) in R19.
  change (lib.Reusable.YK11.getr regs2 20) with (reg_get regs2 20) in R20. change (lib.Reusable.YK11.getr regs2 21) with (reg_get regs2 21) in R21.
  change (lib.Reusable.YK11.getr regs2 22) with (reg_get regs2 22) in R22. change (lib.Reusable.YK11.getr regs2 23) with (reg_get regs2 23) in R23.
  change (lib.Reusable.YK11.getr regs2 24) with (reg_get regs2 24) in R24. change (lib.Reusable.YK11.getr regs2 25) with (reg_get regs2 25) in R25.
  change (lib.Reusable.YK11.getr regs2 26) with (reg_get regs2 26) in R26. change (lib.Reusable.YK11.getr regs2 27) with (reg_get regs2 27) in R27.
  unfold lib.Lib.Regs6ss.mkR_of.
  rewrite R2, R3, R4, R8, R9, Ha02, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27.
  rewrite ?Efa.
  eapply (reac_box_model_block_glue.BmbGlue.bmb_body (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2) (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4)
            (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22)
            (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27) _ _
            (normalize rsegs mem2) p b o (ly_F lyc) ASAN_K ((spZ regs - 160) / 32 * 32) row nb ob).
  all: try first [eassumption | reflexivity].
  (* the glue's rows *)
  all: try exact (mem_inv_normalize rsegs mem2).
  all: try exact (eq_rect _ (fun n => addressable (normalize rsegs mem2) (spZ regs - 4272) n) AW2 4272 ltac:(ring)).
  all: try (pose proof (bmb_frame_norm mem2 (ly_F lyc) pos Hro2 HFgt Hfl H56 Hshf Hadf Hstf)
              as (FN1 & FN2 & FN3 & FN4 & FN5);
            first [exact FN1 | exact FN2 | exact FN3 | exact FN4 | exact FN5]).
  all: try exact (bmb_hsv mem2 (spZ regs) _ Hro2 HHM2 HAE2 (saves_size _ _ _ _ _ _ _ _ _ _ _ _ _) Hsaves2).
  all: try (intros Ho; destruct (HOs Ho) as (_ & _ & _ & _ & Hs); exact Hs).
  all: try exact (Z.lt_le_incl _ _ (proj2 Hspr)).
  (* row 24 (Hawr), a Theorem Labs lane *)
  all: try exact (A.Prog.reac_box_model_block_hawr.BmbHawr.bmb_hawr_hos B STK sp0 FP ly S own lyc Sc W memc regs
                    p o S2 pos Hlo Hhi Eab2 HOs).
  (* rows 5-8, 27-29, a Theorem Labs lane (row 17, Rrt, is no premise of the narrowed bmb_body) *)
  all: try exact (reac_box_model_block_glue_rng.BmbGlueRng.bmb_rng_Rimg lyc W FAgt).
  all: try exact (reac_box_model_block_glue_rng.BmbGlueRng.bmb_rng_Rtp88 lyc W regs Etp FAgt).
  all: try exact (reac_box_model_block_glue_rng.BmbGlueRng.bmb_rng_Rtp8 lyc W regs Etp FAgt).
  all: try exact (reac_box_model_block_glue_rng.BmbGlueRng.bmb_rng_Rtls B TSY lyc S2 W mem2 md2 regs Etp HAR2 Hro2).
  all: try exact (reac_box_model_block_glue_rng.BmbGlueRng.bmb_rng_Ho0 o Ro).
  all: try exact (reac_box_model_block_glue_rng.BmbGlueRng.bmb_rng_Ho1 lyc W mem2 o Ro OFACTS).
  all: try exact (reac_box_model_block_glue_rng.BmbGlueRng.bmb_rng_Hlen B GLOBS RLO RHI W memc p o row HPs).
  (* rows 9-16, a Theorem Labs lane *)
  all: try solve [eapply reac_box_model_block_glue_rng2.BmbGlueRng2.bmb_rng2_RP; eassumption].
  all: try solve [eapply reac_box_model_block_glue_rng2.BmbGlueRng2.bmb_rng2_RPs; eassumption].
  all: try solve [eapply reac_box_model_block_glue_rng2.BmbGlueRng2.bmb_rng2_RO; eassumption].
  all: try solve [eapply reac_box_model_block_glue_rng2.BmbGlueRng2.bmb_rng2_ROs; eassumption].
  all: try solve [eapply reac_box_model_block_glue_rng2.BmbGlueRng2.bmb_rng2_RN; eassumption].
  all: try solve [eapply reac_box_model_block_glue_rng2.BmbGlueRng2.bmb_rng2_RNs; eassumption].
  all: try solve [eapply reac_box_model_block_glue_rng2.BmbGlueRng2.bmb_rng2_RJ13s; eassumption].
  all: try solve [eapply reac_box_model_block_glue_rng2.BmbGlueRng2.bmb_rng2_RJ14s; eassumption].
  (* rows 4, 25, 26, 31, a Theorem Labs lane *)
  all: try solve [eapply reac_box_model_block_glue_o.BmbGlueO.bmb_o_AO; eassumption].
  all: try solve [eapply reac_box_model_block_glue_o.BmbGlueO.bmb_o_Hvis; eassumption].
  all: try solve [eapply reac_box_model_block_glue_o.BmbGlueO.bmb_o_Hni; eassumption].
  all: try solve [eapply reac_box_model_block_glue_o.BmbGlueO.bmb_o_HOm; eassumption].
Qed.
End Thm.
End BmbThm.
