(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_model_block_glue.v, with its module paths, module names and numbers changed; 167 of its 228 lines of code are new or changed and 2351 lines of the source are left out. *)
(* ctrl_lay_block (0x86104) on fuzz_ctrl's ASan+UBSan build, image B (libreac v1.9.0): region R1 of the cgif glue
   pb_ctrl_lay_block (a Theorem Labs lane, hand a Theorem Labs lane).  rule 24: no function proved here.

   PLAN OF RECORD: R1 (ctrl_lay_block-B-glue-plan.md section 3 (a working note, not in this delivery)).
   lay_to_ret is the image-B twin of a Theorem Labs lane's image-A lay_to_ret (
   lib/A/Prog/C_ctrl_lay_block_glue.v (at head lib/A/Prog/C_ctrl_lay_block_glue.v:759-926; from a working branch 9861af6cbb5)), same proof shape:
   - the entry 0x86104 -> the jal into __asan_stack_malloc_1 is CUTS.ly_pre_sm1 (ctrl_lay_block_cutsF.v) run on the
     normalized entry memory (B.MemNorm.normalize memc) and lifted by ctrl_lay_block_gbase.lay_SRr_norm at
     RNG := B.ProgBridge.RNG_W (w_H W).  Its post is the call state at pc 0x3d868 (252008), ra 0x8617c (549244),
     sp = SP2, with the window munch and the 12 saves at S - 96 (lay_R1_call below);
   - ly_pre_sm1 is closed over Section CUTS's row / model facts (FL K9 TM MDP) only through ctrl_lay_blockF.SP2_facts,
     and its conclusion does not mention fr / tb / mb / nb: they are instantiated with a 24-byte zero row (kind 0),
     which makes TM and MDP vacuous;
   - the journal step: B.ProgWorld.ajournal_of_fsteps (PROVED) with WR = [(S - 4512, S)], every byte a window byte;
   - the class-1 request: ctrl_lay_block_gbase.lay_stack_malloc_atS at cid 1, o = SP2 - sp0, ra = 0x8617c;
   - the class-1 frame's bytes: B.ProgWorld.ctl_fs_of_astack_stmt 1 with lo = S - 4512;
   - the continuation receives ctrl_lay_block_gbase.lay_D1.

   CLOSURE: as ctrl_lay_block_gbase.v (the _F files Required QUALIFIED; lib.Reusable twins named in full; B.<module>
   names in full). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YI04 YI16 YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK0h YK0i YK14 YK1a YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI09 YI08 YI00 YI0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YK04R YA0nR YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.ProgBridge B.ProgWorld B.MemNorm B.MemNormF
  B.MemNormTr.
(* the proved B ProgWorld statement this file reads, by its lemma (a Theorem Labs lane) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldAstack.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec ExecF MState Mem Frame Step Cells Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds CtrlBase asan_stack_malloc_c ctrl_lay_block_c
  ctrl_lay_blockF_on ctrl_lay_block_cutsF C_ctrl_lay_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import ctrl_lay_block_gbase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLay.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation rget := lib.Reusable.YK11.getr.
Local Notation rmkst := lib.Reusable.YK11.mkst.
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.

(* The call state CUTS.ly_pre_sm1 hands to its continuation (ctrl_lay_block_cutsF.v :1216-1224): pc 0x3d868 (252008),
   ra 0x8617c (549244), sp = s1 = SP2, s0 = the entry sp, a0 = 96, with the window munch from the base memory m and the
   12 saves at S - 96.  The post of the R1 lift. *)
Definition lay_R1_call (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f md g : Z) : machine_state -> Prop :=
  fun ms => exists m1 : word -> option byte,
    lib.Lib.Frame.munch [(bv_unsigned sp - ctrl_lay_block_c.CTRL_LAY_BLOCK_K, bv_unsigned sp)] m m1 /\
    lib.Lib.Step.rw_cells B.Img0.rsegs m1 (bv_unsigned sp + -96)
      (ctrl_lay_blockF_on.SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10) /\
    ms = lib.Lib.MState.MS
           (lib.Lib.Frame.mkR (Z_to_bv 64 549244) (Z_to_bv 64 ((bv_unsigned sp - 128) / 32 * 32)) gp tp t0 t1 t2 sp
              (Z_to_bv 64 ((bv_unsigned sp - 128) / 32 * 32)) (Z_to_bv 64 96) (lib.Lib.Mem.wa 693944)
              (lib.Lib.Mem.sx32 (lib.Lib.Mem.wa 1)) (Z_to_bv 64 g) a4 a5 a6 a7 s2
              (Z_to_bv 64 g) (Z_to_bv 64 f) s5 (Z_to_bv 64 p) (Z_to_bv 64 md) s8 s9 (lib.Lib.Mem.wa B.AsanRT.ASAN_K) s11
              t3 t4 t5 t6)
           F (Z_to_bv 64 252008) fc None m1 (lib.Lib.PropExec.seg_rom B.Img0.rsegs).

(* The 24-byte zero row: kind 0, so the k = 2 and k = 3..9 premises of ly_pre_sm1 are vacuous. *)
Definition lay_R1_row0 : list byte := repeat (Z_to_bv 8 0) 24.

Lemma lay_R1_row0_k : RcLay.ly_k lay_R1_row0 = 0.
Proof. reflexivity. Qed.

Section R1.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI : Z.
(* ---- core (YCbq Section d0 premises; B's TfibLib record Reusable.YCeg does not compile on any B base yet) ---- *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis errno_low : api_env SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis HWX : lib.Reusable.YK04.wx_segs_nowrap SEGS.
(* ---- the class-1 fake-stack rule and B's code-table entry for it (0x3d868, asan_stack_malloc_c.v:9) ---- *)
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis PC1 : pc_stack_malloc (as_code B) 1 = B.Prog.asan_stack_malloc_c.ASAN_STACK_MALLOC_1.
(* ---- the bundle's symbols; the B ProgWorld statement ctl_fs_of_astack_stmt 1 is PROVED (a Theorem Labs lane), cited ---- *)
Hypothesis CTS : lib.Reusable.YF0m.CtrlTSyms B.
Let ctl_fs_of_astack1 : B.ProgWorld.ctl_fs_of_astack_stmt B 1 := B.ProgWorldAstack.ctl_fs_of_astack B 1.

(* R1: from the entry (cfg_at 0x86104, the caller's journal) to the return of __asan_stack_malloc_1 at 0x8617c, whose
   state the continuation receives with the descriptor lay_D1. *)
Lemma lay_to_ret : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
    (regs : bvmap 5 word) (p f md g : Z) (Q : world SEGS -> config -> Prop),
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->
  rget regs 3 = w64 (as_gp B) -> rget regs 4 = w64 (as_tp B) ->
  rget regs 10 = w64 p -> rget regs 11 = w64 f -> rget regs 12 = w64 md -> rget regs 13 = w64 g ->
  0 <= p < 2 ^ 64 -> 0 <= f < 2 ^ 64 -> 0 <= md < 2 ^ 64 -> 0 <= g < 2 ^ 64 ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK -> spZ regs <= sp0 ->
  count_cid 1 (frames Sc) < fs_frames 1 ->
  p <> 0 ->
  (forall S2 regs2 mem2 md2 pos,
     lay_D1 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p f md g S2 regs2 mem2 md2 pos ->
     SRr SEGS W (mkCfg (rmkst regs2 (Z_to_bv 64 549244) mem2 (lib.Reusable.YK11.seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (cfg_at SEGS C_ctrl_lay_block.CTRL_LAY_BLOCK regs memc mdc) Q.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p f md g Q HJ HRO Hgp Htp Ha0 Ha1 Ha2 Ha3
    Rp Rf Rmd Rg Hal Hlo Hhi Hroom P0 K.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5
    & HQT).
  pose proof Hstk as (Hal0 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EK : C_ctrl_lay_block.CTRL_LAY_BLOCK_STK = 4512) by reflexivity.
  assert (EKc : ctrl_lay_block_c.CTRL_LAY_BLOCK_K = 4512) by reflexivity.
  rewrite EK in Hlo.
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ (proj1 HAR)) as LO.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as [[Hc0 _] _].
  assert (Hspr : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply bv_unsigned_in_range).
  set (A := (spZ regs - 128) / 32 * 32) in *.
  assert (HA1 : spZ regs - 144 <= A <= spZ regs - 128 /\ A mod 32 = 0) by (subst A; Z.div_mod_to_equations; lia).
  (* the runtime facts at the entry: ro_agree memc and asan_cells (normalize memc) (ctl_rt_C_of_AR) *)
  destruct (lay_rt_facts B LAWS CTS RLO RHI lyc Sc W memc mdc HAR
              (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ HRO (Z.le_refl _) (Z.le_refl _)))
    as (Hro & AC0 & _).
  (* the window [S - K, S): visible and present (the caller's journal); stk on the normalized memory *)
  assert (RWIN : lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (w_H W)) (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K)
                   ctrl_lay_block_c.CTRL_LAY_BLOCK_K).
  { rewrite EKc. apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  assert (ST0 : lib.Lib.Frame.stk B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs memc)
                  (spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K) (spZ regs)).
  { rewrite EKc. apply B.MemNormTr.stk_normalize_ro; [exact Hro | unfold B.Prog.ImgBounds.IMG_HI; lia |].
    apply (LayLib.stk_of_present (w_H W)); [lia | lia |]. intros a Ha. apply Hpres. lia. }
  assert (HHM : B.AsanRT.HIGHMEM_BEG <= spZ regs - ctrl_lay_block_c.CTRL_LAY_BLOCK_K)
    by (unfold B.AsanRT.HIGHMEM_BEG; rewrite EKc; lia).
  assert (HAE : spZ regs <= B.AsanRT.APPMEM_END) by (unfold B.AsanRT.APPMEM_END; lia).
  (* the image: visible in every world *)
  assert (RIMG : lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (w_H W)) 65536 6217728).
  { pose proof (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W)) as R.
    unfold B.Prog.ImgBounds.IMG_LO, B.Prog.ImgBounds.IMG_HI in R. exact R. }
  (* the entry state in mkR form, the arguments substituted *)
  change (rget regs 10) with (reg_get regs 10) in Ha0.
  change (rget regs 11) with (reg_get regs 11) in Ha1.
  change (rget regs 12) with (reg_get regs 12) in Ha2.
  change (rget regs 13) with (reg_get regs 13) in Ha3.
  change C_ctrl_lay_block.CTRL_LAY_BLOCK with ctrl_lay_block_c.CTRL_LAY_BLOCK.
  rewrite (B.ProgBridge.cfg_at_MS SEGS).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv SEGS W (lib.Lib.Regs6ss.mkR_of regs) regs);
    [| exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv regs))].
  unfold lib.Lib.Regs6ss.mkR_of. rewrite Ha0, Ha1, Ha2, Ha3.
  (* the lift of CUTS.ly_pre_sm1 on the normalized entry memory *)
  refine (lay_SRr_norm HWX W (B.ProgBridge.RNG_W (w_H W)) mdc _ lib.Reusable.YK11.fp_regs _ lib.Reusable.YK11.fp_csr
            memc
            (lay_R1_call (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
               (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 14)
               (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19)
               (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
               (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29)
               (reg_get regs 30) (reg_get regs 31) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr
               (B.MemNorm.normalize B.Img0.rsegs memc) p f md g)
            Q (B.ProgBridge.fp_avoids_RNG_W _) Hro _ _).
  { eapply (ctrl_lay_block_cutsF.ly_pre_sm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (B.MemNorm.normalize B.Img0.rsegs memc) p f md g lay_R1_row0 nil nil nil nil);
      [ exact Rp | exact Rf | exact Rmd | exact Rg | exact Hal | exact ST0 | reflexivity
      | rewrite lay_R1_row0_k; lia | rewrite lay_R1_row0_k; discriminate | exact P0
      | rewrite lay_R1_row0_k; lia | exact (B.MemNorm.mem_inv_normalize B.Img0.rsegs memc) | exact AC0
      | exact HHM | exact HAE | exact RIMG | exact RWIN | reflexivity | ].
    intros m1 MU _ _ _ FR. eexists. split; [apply lib.Lib.ExecF.mstepsF_refl|].
    exists m1. split; [exact MU|]. split; [exact FR | reflexivity]. }
  intros ms1 model1 Hrun1 (s1' & HP1 & HREL1 & HROS1) Hhid1 Hsame1.
  destruct HP1 as (mg & MU & FR & Es1). subst s1'.
  destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL1) as [Ems1 HMR1].
  assert (HMU1 : lib.Lib.Frame.munch [(spZ regs - 4512, spZ regs)] memc (ms_mem ms1)).
  { pose proof (B.MemNorm.munch_rel B.Img0.rsegs _ memc (B.MemNorm.normalize B.Img0.rsegs memc) (ms_mem ms1) mg
                  (B.MemNorm.mem_rel_normalize B.Img0.rsegs memc Hro) HMR1 HROS1 MU) as H.
    rewrite EKc in H. exact H. }
  (* the journal across the lifted stretch: its writes are window bytes *)
  assert (HJ1 : ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) model1 k).
  { lazymatch type of Hrun1 with lib.Reusable.YK04R.fsteps _ _ ?ms0 _ =>
      refine (B.ProgWorld.ajournal_of_fsteps B LAWS HWX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W ms0 ms1 mdc model1 k
                _ _ HJ Hrun1 (B.ProgBridge.fp_avoids_RNG_W _) HMU1 Hsame1 _) end.
    intros a Ha Hout. left. cbn [lib.Lib.Frame.outside] in Hout. lia. }
  rewrite Ems1. clear Ems1.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  (* the allocator event, class 1 *)
  lazymatch goal with |- SRr _ _ {| cfg_ms := lib.Lib.MState.MS ?R _ _ _ _ ?mm _; cfg_model := _ |} _ =>
    set (regsT := R) in *; set (mem1 := mm) in * end.
  replace (Z_to_bv 64 252008) with (Z_to_bv 64 (pc_stack_malloc (as_code B) 1)) by (rewrite PC1; reflexivity).
  change (SRr SEGS W (mkCfg (rmkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) 1)) mem1
            (lib.Reusable.YK11.seg_rom SEGS)) model1) Q).
  change (rget regs 3) with (reg_get regs 3) in Hgp. change (rget regs 4) with (reg_get regs 4) in Htp.
  assert (EspT : spZ regsT = A).
  { unfold spZ. change (rget regsT 2) with (Z_to_bv 64 A). rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  eapply SRr_bind.
  { refine (lay_stack_malloc_atS B LAWS errno_low ML SMP 1 ASM1 ltac:(lia) W regsT mem1
              STK sp0 FP ly S W0 mem0 md0 own lyc Sc model1 k (A - sp0) (Z_to_bv 64 549244) HJ1 _ _ _ _ _ _
              eq_refl _ Hroom).
    - rewrite EspT. lia.
    - Z.div_mod_to_equations. lia.
    - lia.
    - unfold ESTACK. lia.
    - exact Hgp.
    - exact Htp.
    - apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha02 & Eab & Hfrs2 & Hnin & Hnev2 &
    Hbb2 & Hz & Hflag & HK & HfS & HPRE & HAR2 & Hpres2 & Hfr).
  replace (sp0 + (A - sp0) - ESTACK) with (A - 4096) in HK by (unfold ESTACK; lia).
  replace (sp0 + (A - sp0)) with A in HK by lia.
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ2 & _).
  rewrite EspT in Hpres2, Hfr.
  (* the class-1 frame's bytes: ctl_fs_of_astack at cid = 1, lo := S - 4512 *)
  assert (HFS : lay_fs1 (ly_F lyc) pos (spZ regs - 4512) A (rget regs2 10) mem2).
  { pose proof (ctl_fs_of_astack1 B.ProgWorld.ctl_fs_geom LAWS ltac:(lia) lyc Sc S2 W regsT regs2
                  mem1 mem2 model1 md2 pos (spZ regs - 4512) (fs_frame_bytes 1) HPRE) as H.
    rewrite EspT in H.
    unfold lay_fs1. apply H; clear H.
    - rewrite Eslo. lia.
    - unfold ESTACK. lia.
    - intros a Ha. apply Hpres1. unfold ESTACK in Ha. lia.
    - exact Hfrs2.
    - exact Hnin.
    - exact HAR2.
    - exact Ha02.
    - exact Hz.
    - exact Hflag.
    - exact Hpres2.
    - exact Hfr.
    - split; [vm_compute; discriminate | lia]. }
  apply (K S2 regs2 mem2 md2 pos). unfold lay_D1. rewrite EK.
  split; [exact HJ2|]. split; [exact Hfrs2|]. split; [exact Hnin|]. split; [exact Eab|]. split; [exact HfS|].
  split; [exact HAR2|]. split; [exact Ha02|].
  split.
  { unfold lay_ret_regs.
    assert (P : forall r, acallee_saved r -> rget regs2 (Z_to_bv 5 r) = rget regsT (Z_to_bv 5 r)) by exact HP2.
    repeat split.
    all: lazymatch goal with
         | |- rget _ ?n = _ =>
             let z := eval vm_compute in (bv_unsigned n) in
             transitivity (rget regsT (Z_to_bv 5 z)); [exact (P z ltac:(unfold acallee_saved; lia)) | reflexivity]
         end. }
  split; [exact HFS|].
  split.
  { apply (lay_acall_kept_after_munch B LAWS lyc Sc W memc mem1 mem2 mdc (spZ regs - 4512) (spZ regs) (A - 4096) A
             (spZ regs - 4512) (spZ regs) (fun _ => False) HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             HMU1 HK).
    intros a Ha. apply HpresJ2. lia. }
  split.
  { (* the realizes frame condition, carried from the call memory mem1 to the entry memory memc off the window *)
    intros a Ha Ho1 Ho2 Hw. rewrite (Hfr a Ha Ho1 Ho2 ltac:(unfold ESTACK; lia)).
    apply aview_eq_of. unfold mrestrict. rewrite (HMU1 (Z_to_bv 64 a)); [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
  (* the 12 saves: written by the prologue (on the normalized run), carried back by ms_rel, kept by the allocator
     ([S - 96, S) is above SP2, outside its ESTACK window) *)
  assert (E96 : spZ regs - 96 = bv_unsigned (reg_get regs 2) + -96) by reflexivity.
  rewrite E96.
  apply (LayLib.rw_cells_agree mem1).
  - exact (B.MemNormTr.rw_cells_of_rel _ _ _ _ HMR1 FR).
  - intros i Hi. cbn [lib.Lib.Cells.cells_size lib.Lib.Cells.csize Nat.add ctrl_lay_blockF_on.SAVES] in Hi.
    rewrite <- E96.
    pose proof (proj1 (HpresJ2 (spZ regs - 96 + i) ltac:(lia))) as Hv.
    apply (LayLib.raw_of_aview W mem1 mem2); [lia | exact Hv | apply LayLib.above_ceil_not_img; lia |].
    pose proof HK as (K1 & _). apply K1; lia.
Qed.
End R1.
