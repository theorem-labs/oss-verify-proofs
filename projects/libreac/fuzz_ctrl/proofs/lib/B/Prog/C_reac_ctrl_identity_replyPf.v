(* lib/B/Prog/C_reac_ctrl_identity_replyPf.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the pieces of
   pb_reac_ctrl_identity_reply (the cgif-form glue of reac_ctrl_identity_reply, 0x848fc), written stretch by stretch
   on the plan of record analyses/libreac/fuzz_ctrl/glue-B/identity_reply/pb_reac_ctrl_identity_reply.plan.md.  Every lemma here
   is Qed; the image-B facts that do not exist yet are premises of the lemma that needs them, each named after the
   image-A statement that will supply it.

   rrB_lift is the one lift pattern every stretch uses: a footprint run of the stretch on `normalize rsegs m` at
   RNG := RNG_W (w_H W) becomes a silent prefix of the world walk from the REAL memory m (MemNormF.evtF_normalize_ro,
   ProgBridge.fevt_of_evtF, YA0nR.SRr_fevt, ProgBridge.fp_avoids_RNG_W).  It takes `wx_segs_nowrap rsegs`, exactly as
   a Theorem Labs lane's image-B lifts do (lib/B/ProgLift/*.v, not in this delivery): that fact is not proved for image B on this base
   (OWNER PENDING: a Theorem Labs lane, B ProgBridge / Img0).
   rrB_SA is the first stretch, the entry 0x848fc to the first slot of __asan_stack_malloc_1, at the caller's memory:
   rp_stretchA_F (lib/B/Prog/reac_ctrl_identity_replyF.v (not in this delivery)) run on normalize memc, its memory premises moved there by
   B MemNormTr (stk_normalize_ro under IMG_HI <= S - 9072, asan_cells_normalize) and MemNorm.mem_inv_normalize, its
   footprint premises by ProgBridge.rng_of_visible (img_vis_W for the image, the window's visibility for the window). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
(* reac_ctrl_identity_replyRB: the generated copy of the route-(C) run reac_ctrl_identity_replyF_on.v's Sections + the
   glue's cut lemmas (unit decision 125; analyses/libreac/fuzz_ctrl/glue-B/identity_reply/gen_reac_ctrl_identity_replyRB.py). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c reac_ctrl_identity_reply_c
  reac_ctrl_identity_reply_c_on reac_ctrl_identity_replyRB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK04R YA0n YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YM05 YI16 YG0f YG0d YCbq.
(* the class-generic stack-malloc event: YCbq.aj_stack_malloc_at's continuation does not carry ecall_pre,
   astack_malloc_realizes' frame condition or the presence clauses, which ctl_fs_of_astack needs. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YCbqMalloc.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0n YG0v YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr MemNormF ProgBridge ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
(* fp / fp_w / fp_dj (the side-stack bundle) and the re-based S-B run (rrB_QSB, rrB_SB_run, rrB_rBI_at). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanFP C_reac_ctrl_identity_replyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import GlueLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
Import ListNotations.
Open Scope Z_scope.

Section Pf.
Context {fx : lib.Reusable.YK11.FPState}.

(* The covers of a range of application bytes move to a footprint that avoids an application range [lo, hi). *)
Lemma rrB_shcov_avoid : forall R p n lo hi, 0 <= p -> p + n <= APPMEM_END -> lo < hi -> app_mem lo -> app_mem (hi - 1) ->
  hi - lo <= HIGHMEM_BEG - LOWMEM_END -> shcov R p n -> shcov (rrB_avoid R lo hi) p n.
Proof.
  intros R p n lo hi Hp Hn Hl A1 A2 Hs H x Hx. apply rrB_rng_avoid; [exact (H x Hx)|].
  destruct (rrB_shadow_byte_in x ltac:(lia)) as [B1 B2].
  exact (rrB_shadow_vs_app (x / 8 + ASAN_K) 1 lo hi B1 B2 Hl A1 A2 Hs).
Qed.

Lemma rrB_shkov_avoid : forall R p n lo hi, 0 <= p -> p + n <= APPMEM_END -> lo < hi -> app_mem lo -> app_mem (hi - 1) ->
  hi - lo <= HIGHMEM_BEG - LOWMEM_END -> shkov R p n -> shkov (rrB_avoid R lo hi) p n.
Proof.
  intros R p n lo hi Hp Hn Hl A1 A2 Hs H a b H1 H2 H3. apply rrB_rng_avoid; [exact (H a b H1 H2 H3)|].
  apply rrB_shadow_vs_app; [| | exact Hl | exact A1 | exact A2 | exact Hs];
    unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END, ASAN_K in *; Z.div_mod_to_equations; lia.
Qed.

(* The first stretch's footprint run on the normalized caller memory, from single-memory facts at the REAL memory
   memc (the spec's P1 gives them through AR: stk and asan_cells by ctlrt_of_AR; the window's visibility by win_vis;
   OWNER PENDING: a Theorem Labs lane's lib/B/ProgWorld.v, a Theorem Labs lane's B V-lemmas). *)
Lemma rrB_SA_run : forall (W : lib.Reusable.YA0n.world rsegs)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (memc : word -> option byte) (fr len pa pp pn S : Z) (g : list byte)
    (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
    0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    S < 2^64 -> S mod 16 = 0 -> 9072 <= S ->
    B.MemNorm.ro_agree rsegs memc ->
    lib.Lib.Frame.stk rsegs memc (S - 9072) S ->
    length g = 50%nat ->
    asan_cells memc ->
    HIGHMEM_BEG <= S - 9072 -> S <= APPMEM_END ->
    B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (S - 9072) 9072 ->
    ExecF.evtF rsegs (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
      (fun ms' => exists mc : word -> option byte,
         rMCALL ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (B.MemNorm.normalize rsegs memc) S mc /\
         ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8497c) (Z_to_bv 64 (rA S)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
                       (Z_to_bv 64 128) (lib.Lib.Mem.wa CELL_K) (lib.Lib.Mem.sx32 (lib.Lib.Mem.wa 1)) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7
                       s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len)
                       s8 s9 s10 (lib.Lib.Mem.wa ASAN_K) t3 t4 t5 t6)
                  F (Z_to_bv 64 ASAN_STACK_MALLOC_1) fc None mc (lib.Lib.PropExec.seg_rom rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
               (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None (B.MemNorm.normalize rsegs memc) (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros W ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc memc fr len pa pp pn S g t0 t1 t2 a5 a6 a7 t3 t4 t5 t6
    Rfr Rlen Rpa Rpp Rpn HS S16 HSK RO ST Hg AC HHM HAE VW.
  assert (STn : lib.Lib.Frame.stk rsegs (B.MemNorm.normalize rsegs memc) (S - 9072) S).
  { apply B.MemNormTr.stk_normalize_ro; [exact RO | | exact ST].
    unfold ImgBounds.IMG_HI. unfold HIGHMEM_BEG in HHM. lia. }
  pose proof (B.MemNorm.mem_inv_normalize rsegs memc) as MIn.
  pose proof (B.MemNormTr.asan_cells_normalize memc RO AC) as ACn.
  assert (RIMG : ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) 0x10000 0x5ee000).
  { pose proof (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W)) as R.
    unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI in R. exact R. }
  pose proof (B.ProgBridge.rng_of_visible _ _ _ VW) as RWIN.
  exact (rp_stretchA_F ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (B.MemNorm.normalize rsegs memc)
           fr len pa pp pn S g Rfr Rlen Rpa Rpp Rpn HS S16 HSK STn MIn Hg ACn HHM HAE
           (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) RIMG RWIN t0 t1 t2 a5 a6 a7 t3 t4 t5 t6
           (B.MemNorm.normalize rsegs memc) eq_refl).
Qed.
(* The first stretch LIFTED: from the cgif cut at the entry (real caller memory memc) to the world walk at the first
   slot of __asan_stack_malloc_1.  The continuation receives the real state there, related by ms_rel to the
   normalized run's end state (rMCALL over normalize memc, the registers of the call) and keeping memc's read-only
   bytes.  General shape: every stretch lift in this file is rrB_lift applied to the stretch's own run. *)
Lemma rrB_SA : lib.Reusable.YK04.wx_segs_nowrap rsegs ->
  forall (W : lib.Reusable.YA0n.world rsegs) (md : Model)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (memc : word -> option byte) (fr len pa pp pn S : Z) (g : list byte)
    (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    S < 2^64 -> S mod 16 = 0 -> 9072 <= S ->
    B.MemNorm.ro_agree rsegs memc ->
    lib.Lib.Frame.stk rsegs memc (S - 9072) S ->
    length g = 50%nat ->
    asan_cells memc ->
    HIGHMEM_BEG <= S - 9072 -> S <= APPMEM_END ->
    B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (S - 9072) 9072 ->
    (forall ms' md',
       (exists s', (exists mc : word -> option byte,
          rMCALL ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (B.MemNorm.normalize rsegs memc) S mc /\
          s' = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8497c) (Z_to_bv 64 (rA S)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
                       (Z_to_bv 64 128) (lib.Lib.Mem.wa CELL_K) (lib.Lib.Mem.sx32 (lib.Lib.Mem.wa 1)) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7
                       s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len)
                       s8 s9 s10 (lib.Lib.Mem.wa ASAN_K) t3 t4 t5 t6)
                  F (Z_to_bv 64 ASAN_STACK_MALLOC_1) fc None mc (lib.Lib.PropExec.seg_rom rsegs)) /\
          B.MemNorm.ms_rel rsegs ms' s' /\ B.MemNorm.ro_same rsegs memc (ms_mem ms')) ->
       (forall x : word, lib.Reusable.YA0n.w_H W x = true -> ms_mem ms' x = memc x) ->
       lib.Reusable.YK04.same_but_materialized md md' -> lib.Reusable.YA0n.SRr rsegs W (mkCfg ms' md') Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
                      (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None memc (lib.Lib.PropExec.seg_rom rsegs)) md) Q.
Proof.
  intros Hwx W md ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc memc fr len pa pp pn S g
    t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 Q Rfr Rlen Rpa Rpp Rpn HS S16 HSK RO ST Hg AC HHM HAE VW K.
  eapply (rrB_lift Hwx W md); [exact RO | | exact K].
  exact (rrB_SA_run W ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc memc fr len pa pp pn S g
           t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 Rfr Rlen Rpa Rpp Rpn HS S16 HSK RO ST Hg AC HHM HAE VW).
Qed.
End Pf.

Section Journal.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* The two Section premises of YCbq's Section a0 (YCbq.v:204-208), for B's bundle.  segs_low: core, PENDING THE
   RECORD CORE (a refused name in an earlier version of YCeg.v, not in this delivery).  Its statement is Reusable.YCeg.tfib_segs_low (YCeg.v:66, stated and
   proved), but the file lib/Reusable/YCeg.v compiled on NO B base then: that version named port_core_refused_103b0
   (a Theorem Labs lane's probe-free build, 2026-10-29 05:06:50Z).  So YCeg is
   NOT Required; when it compiles, segs_low := Reusable.YCeg.tfib_segs_low (tfibsegs = rsegs by
   ProgBridge.tfibsegs_rsegs). *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.

(* ---- S-A then the journal J1, ending AT the first slot of __asan_stack_malloc_1 with the real memory m1 there.
   rrB_SA, MemNormTr.ms_rel_MS to read the real state back, and rrB_journal_win over the window [S - 9072, S): the
   run's munch is rMCALL's first conjunct, and the window is readable in the normalized end memory (stk below the
   frame, the frame slot and the 13 saved registers by stk_of_rw_cells, merged). ---- *)
Lemma rrB_to_E1 : lib.Reusable.YK04.wx_segs_nowrap rsegs ->
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs)
    memc mdc k (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fr len pa pp pn S : Z) (g : list byte) (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word)
    (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
    sp0 - STK <= S - 9072 -> S <= sp0 ->
    0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    S < 2^64 -> S mod 16 = 0 -> 9072 <= S ->
    B.MemNorm.ro_agree rsegs memc -> lib.Lib.Frame.stk rsegs memc (S - 9072) S -> length g = 50%nat -> asan_cells memc ->
    HIGHMEM_BEG <= S - 9072 -> S <= APPMEM_END ->
    B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (S - 9072) 9072 ->
    (forall (m1 mc : word -> option byte) mdc1,
       rMCALL ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (B.MemNorm.normalize rsegs memc) S mc ->
       B.MemNorm.mem_rel rsegs m1 mc -> B.MemNorm.ro_same rsegs memc m1 ->
       lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k ->
       lib.Reusable.YA0n.SRr rsegs W
         (mkCfg (lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8497c) (Z_to_bv 64 (rA S)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
                         (Z_to_bv 64 128) (lib.Lib.Mem.wa CELL_K) (lib.Lib.Mem.sx32 (lib.Lib.Mem.wa 1)) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7
                         s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len)
                         s8 s9 s10 (lib.Lib.Mem.wa ASAN_K) t3 t4 t5 t6)
                    F (Z_to_bv 64 ASAN_STACK_MALLOC_1) fc None m1 (lib.Lib.PropExec.seg_rom rsegs)) mdc1) Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
                      (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None memc (lib.Lib.PropExec.seg_rom rsegs)) mdc) Q.
Proof using LAWS segs_low.
  intros Hwx STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    fr len pa pp pn S g t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 Q HJ Hlo Hhi Rfr Rlen Rpa Rpp Rpn HS S16 HSK RO ST Hg AC HHM HAE
    VW K.
  apply (rrB_SA Hwx W mdc ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc memc fr len pa pp pn S g
           t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 Q Rfr Rlen Rpa Rpp Rpn HS S16 HSK RO ST Hg AC HHM HAE VW).
  intros ms' md' (s' & (mc & HR & Es') & HREL & HROS) Hhid Hsame.
  rewrite Es' in HREL. destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
  rewrite Ems.
  apply (K (ms_mem ms') mc md' HR HMR HROS).
  pose proof HR as (MU & _ & _ & _ & _ & _ & _ & _ & STw & SV & (junk & SJ)).
  pose proof (lib.Lib.Frame.stk_of_rw_cells rsegs _ _ _ SV) as S1. pose proof (lib.Lib.Frame.stk_of_rw_cells rsegs _ _ _ SJ) as S2.
  assert (E104 : Z.of_nat (lib.Lib.Cells.cells_size (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) = 104) by reflexivity.
  assert (E24 : Z.of_nat (lib.Lib.Cells.cells_size [lib.Lib.Cells.C8 (Z_to_bv 64 0); lib.Lib.Cells.CB 16 junk]) = 24) by reflexivity.
  rewrite E104 in S1. rewrite E24 in S2.
  replace (S - 104 + 104) with S in S1 by lia. replace (S - 128 + 24) with (S - 104) in S2 by lia.
  pose proof (lib.Lib.Frame.stk_merge rsegs _ _ _ _ (lib.Lib.Frame.stk_merge rsegs _ _ _ _ STw S2 ltac:(lia)) S1 ltac:(lia)) as SW.
  apply (rrB_journal_win B LAWS segs_low STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k (ms_mem ms') mc md' (S - 9072) S HJ);
    [lia | lia | unfold ImgBounds.IMG_HI; unfold HIGHMEM_BEG in HHM; lia | lia | exact MU | | exact HMR | exact HROS
    | exact Hhid | exact Hsame].
  intros a Ha. destruct SW as (_ & _ & Hsw). destruct (Hsw a Ha) as [_ Hb]. exact Hb.
Qed.

(* ---- E1: the class-1 fake-stack request, by the core's YCbq.aj_stack_malloc_at at cid := 1.  Its Section premises
   for B's bundle, besides LAWS and segs_low above (each a NAMED hypothesis with its owner):
     errno_low : api_env        core, PENDING THE RECORD CORE (Reusable.YCeg.tl_env, YCeg.v:38; YCeg.v:25 refused name)
     ML        : model_laws     core B bundle fact (the core's TfibLib, same pending file)
     SMP       : stack_malloc_progressP, ASM1 : astack_malloc_realizes 1
                                a Theorem Labs lane's class-1 fake-stack rules, a working branch ff613211c11 (cgif lib/A/ACed.v:125-133)
     PC1       : the class-1 entry of B's code table is __asan_stack_malloc_1 (0x3d868); core, the TfibLib code table,
                 same pending file.
   The state is the end state of rrB_to_E1 with fp_regs / fp_csr (the cfg_at form of the spec's entry). ---- *)
Hypothesis errno_low : lib.Reusable.YCbq.api_env rsegs B.
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
Hypothesis SMP : lib.Reusable.YCbq.stack_malloc_progressP B.
Hypothesis ASM1 : lib.Reusable.YG0d.astack_malloc_realizes rsegs B 1.
Hypothesis PC1 : lib.Reusable.YG0f.pc_stack_malloc (lib.Reusable.YG0f.as_code B) 1 = ASAN_STACK_MALLOC_1.

(* The call configuration's register bundle, written once and used by the statement below three times. *)
Definition rrB_regsT (gp tp t0 t1 t2 a5 a6 a7 s2 s8 s9 s10 t3 t4 t5 t6 : word) (fr len pa pp pn S : Z) :=
  lib.Lib.Frame.mkR (Z_to_bv 64 0x8497c) (Z_to_bv 64 (rA S)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
    (Z_to_bv 64 128) (lib.Lib.Mem.wa CELL_K) (lib.Lib.Mem.sx32 (lib.Lib.Mem.wa 1)) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7
    s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len)
    s8 s9 s10 (lib.Lib.Mem.wa ASAN_K) t3 t4 t5 t6.

Lemma rrB_E1 :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs)
    (m1 : word -> option byte) mdc1 k (gp tp t0 t1 t2 a5 a6 a7 s2 s8 s9 s10 t3 t4 t5 t6 : word)
    (fr len pa pp pn S : Z) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k ->
    sp0 - STK <= S - 9072 -> S <= sp0 -> S < 2^64 -> S mod 16 = 0 -> 9072 <= S ->
    gp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) -> tp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
    lib.Reusable.YG01.count_cid 1 (lib.Reusable.YG01.frames Sc) < lib.Reusable.YG00.fs_frames 1 ->
    (forall S2 regs2 mem2 md2 pos,
       lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k ->
       lib.Reusable.YG0d.aregs_preserved
         (rrB_regsT gp tp t0 t1 t2 a5 a6 a7 s2 s8 s9 s10 t3 t4 t5 t6 fr len pa pp pn S) regs2 ->
       lib.Reusable.YK11.getr regs2 10 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.frame_addr lyc 1 pos) ->
       lib.Reusable.YG0d.ablocks B lyc S2 = lib.Reusable.YG0d.ablocks B lyc Sc ->
       lib.Reusable.YG01.frames S2 = (1, pos) :: lib.Reusable.YG01.frames Sc ->
       ~ In (1, pos) (lib.Reusable.YG01.frames Sc) ->
       lib.Reusable.YG00.st_nev S2 = lib.Reusable.YG00.st_nev Sc ->
       lib.Reusable.YG01.blocks_bytes S2 = lib.Reusable.YG01.blocks_bytes Sc ->
       lib.Reusable.YG0v.zero_shadow (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
         lib.Reusable.YG0f.SHADOW_OFF (lib.Reusable.YG0f.frame_addr lyc 1 pos) (lib.Reusable.YG00.fs_frame_bytes 1) ->
       lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
         (lib.Reusable.YG0f.frame_addr lyc 1 pos + lib.Reusable.YG00.fs_frame_bytes 1 - 8) =
         Some (lib.Reusable.YG0f.flag_addr lyc 1 pos) ->
       lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W m1 W mem2
         (sp0 + (rA S - sp0) - lib.Reusable.YG0d.ESTACK) (sp0 + (rA S - sp0)) (fun _ => False) ->
       (* the four facts YCbq.aj_stack_malloc_at does NOT pass on and B.ProgWorldAstack.ctl_fs_of_astack needs
          (ProgWorld.v:466, :479-483); they come from the core lemma lib.Reusable.YCbqMalloc.aj_stack_malloc_at_fc *)
       lib.Reusable.YG0d.ecall_pre rsegs B lyc Sc W
         (rrB_regsT gp tp t0 t1 t2 a5 a6 a7 s2 s8 s9 s10 t3 t4 t5 t6 fr len pa pp pn S) m1 mdc1 ->
       (forall a, lib.Reusable.YG0f.frame_addr lyc 1 pos <= a <
                    lib.Reusable.YG0f.frame_addr lyc 1 pos + lib.Reusable.YG00.fs_frame_bytes 1 ->
          lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a) ->
       (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Reusable.YG0n.aowned B lyc Sc a -> ~ lib.Reusable.YG0n.aowned B lyc S2 a ->
          ~ (sp0 + (rA S - sp0) - lib.Reusable.YG0d.ESTACK <= a < sp0 + (rA S - sp0)) ->
          lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2 a =
            lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m1 a) ->
       (forall a, sp0 + (rA S - sp0) - lib.Reusable.YG0d.ESTACK <= a < sp0 + (rA S - sp0) ->
          lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a) ->
       lib.Reusable.YA0n.SRr rsegs W
         (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x8497c) mem2 (lib.Reusable.YK11.seg_rom rsegs)) md2) Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (lib.Lib.MState.MS (rrB_regsT gp tp t0 t1 t2 a5 a6 a7 s2 s8 s9 s10 t3 t4 t5 t6 fr len pa pp pn S)
                 lib.Reusable.YK11.fp_regs (Z_to_bv 64 ASAN_STACK_MALLOC_1) lib.Reusable.YK11.fp_csr None m1
                 (lib.Lib.PropExec.seg_rom rsegs)) mdc1) Q.
Proof using LAWS segs_low errno_low ML SMP ASM1 PC1.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k gp tp t0 t1 t2 a5 a6 a7 s2 s8 s9 s10 t3 t4 t5 t6
    fr len pa pp pn S Q HJ Hlo Hhi HS S16 HSK Egp Etp Hcnt K.
  set (regsT := rrB_regsT gp tp t0 t1 t2 a5 a6 a7 s2 s8 s9 s10 t3 t4 t5 t6 fr len pa pp pn S).
  assert (HA : rA S mod 32 = 0 /\ S - 144 <= rA S <= S - 128)
    by (unfold rA; Z.div_mod_to_equations; lia).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _).
  assert (Hsp : lib.Reusable.YG0d.spZ regsT = sp0 + (rA S - sp0)).
  { unfold lib.Reusable.YG0d.spZ.
    change (lib.Reusable.YK11.getr regsT 2) with (Z_to_bv 64 (rA S)).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_small by lia. lia. }
  assert (Hal : (rA S - sp0) mod 16 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hraw : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 0x8497c)) by (unfold lib.Reusable.YK0s.ret_ok; vm_compute; reflexivity).
  rewrite <- PC1.
  eapply lib.Reusable.YA0n.SRr_bind.
  - exact (lib.Reusable.YCbqMalloc.aj_stack_malloc_at_fc rsegs B LAWS segs_low errno_low ML SMP 1 ASM1 ltac:(lia) W regsT m1
             STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc mdc1 k (rA S - sp0) (Z_to_bv 64 0x8497c) HJ Hsp Hal ltac:(lia)
             ltac:(unfold lib.Reusable.YG0d.ESTACK; lia) ltac:(subst gp; reflexivity) ltac:(subst tp; reflexivity)
             eq_refl Hraw Hcnt).
  - intros W2 c2 Hle (EW & S2 & regs2 & mem2 & md2 & pos & Ec & HJ2 & HP & H10 & HAB & HFR & HNI & HNEV & HBB & HZ &
      HFL & HKEPT & HPRE & HFPRES & HFRC & HWPRES).
    subst W2 c2.
    rewrite Hsp in HFRC, HWPRES.
    cbn beta in HFRC, HWPRES.
    exact (K S2 regs2 mem2 md2 pos HJ2 HP H10 HAB HFR HNI HNEV HBB HZ HFL HKEPT HPRE HFPRES HFRC HWPRES).
Qed.
End Journal.
(* ---- S-B LIFTED: the stretch after the class-1 request (rrB_SB_run, at the normalized base memory) as a silent prefix
   of the world walk from the REAL base memory mb.  The run is taken under the footprint RNG_W (w_H W) WITHOUT the
   class-1 hint word [FS + 8, FS + 16) and WITHOUT the class-1 flag byte [fs_flag FS 1 jj, fs_flag FS 1 jj + 1): none
   of the chain's lemmas takes an rng premise for either (measured: no RFSS, RFLG or RW1), so rrB_evtF_keep proves both
   unchanged - the bytes the _F munch lists name but the stretch never writes (unit decision 125's finding,
   script-free).  The continuation gets the real end state, related to an end state of rrB_QSB jj over normalize mb,
   the hint and the flag kept, and the lift's own facts. ---- *)
Section SB.
Context {fx : lib.Reusable.YK11.FPState}.

Definition rrB_SBpost (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (fr len pa pp pn S FS : Z) (g : list byte) (jj : Z)
    (W : lib.Reusable.YA0n.world rsegs) (md : Model) (ms' : machine_state) (md' : Model) : Prop :=
  (exists s0', rrB_QSB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (B.MemNorm.normalize rsegs mb)
                 fr len pa pp pn S FS g jj s0' /\
     B.MemNorm.ms_rel rsegs ms' s0' /\ B.MemNorm.ro_same rsegs mb (ms_mem ms') /\
     (forall x, rrB_inH (FS + 8) (FS + 16) x = true -> ms_mem s0' x = B.MemNorm.normalize rsegs mb x) /\
     (forall x, rrB_inH (fs_flag FS 1 jj) (fs_flag FS 1 jj + 1) x = true ->
        ms_mem s0' x = B.MemNorm.normalize rsegs mb x)) /\
  (forall x : word, lib.Reusable.YA0n.w_H W x = true -> ms_mem ms' x = mb x) /\
  lib.Reusable.YK04.same_but_materialized md md'.

Lemma rrB_SB_lifted : lib.Reusable.YK04.wx_segs_nowrap rsegs ->
  forall (W : lib.Reusable.YA0n.world rsegs) (md : Model)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (fr len pa pp pn S FS : Z) (g ja jp jn : list byte) (jj : Z)
    (rr0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    S < 2^64 -> S mod 16 = 0 -> 9072 <= S ->
    B.MemNorm.ro_agree rsegs mb ->
    lib.Lib.Frame.stk rsegs mb (S - 9072) S -> length g = 50%nat ->
    (reply_args fr pa pp pn = true -> 50 <= len ->
       fr + 50 <= 2^64 /\ lib.Lib.Mem.bytes_at rsegs mb fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
       (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)) ->
    (reply_args fr pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       lib.Lib.Step.rw_cells rsegs mb pa [lib.Lib.Cells.CB 2 ja] /\ lib.Lib.Step.rw_cells rsegs mb pp [lib.Lib.Cells.CB 8 jp] /\ lib.Lib.Step.rw_cells rsegs mb pn [lib.Lib.Cells.CB 8 jn] /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)) ->
    (* the caller's three cells lie above the image (in caller frames), so they are not read-only *)
    (reply_args fr pa pp pn = true -> ImgBounds.IMG_HI <= pa /\ ImgBounds.IMG_HI <= pp /\ ImgBounds.IMG_HI <= pn) ->
    shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mb ->
    HIGHMEM_BEG <= S - 9072 -> S <= APPMEM_END ->
    addressable mb (S - 9072) 9072 ->
    (reply_args fr pa pp pn = true -> 50 <= len -> addressable mb fr 50) ->
    (reply_args fr pa pp pn = true ->
       addressable mb pa 2 /\ addressable mb pp 8 /\ addressable mb pn 8 /\
       (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) ->
    fp [1%nat] mb (bv_unsigned tp) FS (S - 9072) S
      (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) ->
    reac_ctrl_identity_reply_tls mb (bv_unsigned tp) FS (S - 9072) S ->
    lib.Lib.Step.rw_cells rsegs mb (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    lib.Lib.Mem.bytes_at rsegs mb (fs_frame FS 1 jj + 120) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 1 jj))) ->
    lib.Lib.Mem.bytes_at rsegs mb (fs_flag FS 1 jj) [Z_to_bv 8 1] ->
    0 <= jj < fs_M 1 ->
    (* the run's footprint at RNG_W (w_H W) (the statement's forms, from the world's visibility) *)
    ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (S - 9072) 9072 ->
    shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (S - 9072) 9072 ->
    (reply_args fr pa pp pn = true -> 50 <= len -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) ->
    (reply_args fr pa pp pn = true -> 50 <= len -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) ->
    (reply_args fr pa pp pn = true -> 50 <= len -> shkov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) ->
    (reply_args fr pa pp pn = true -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pa 2) ->
    (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pa 2) ->
    (reply_args fr pa pp pn = true -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pp 8) ->
    (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pp 8) ->
    (reply_args fr pa pp pn = true -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pn 8) ->
    (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pn 8) ->
    ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (fs_frame FS 1 0)
      (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0) ->
    shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0) ->
    (forall ms' md', rrB_SBpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g jj
                       W md ms' md' -> lib.Reusable.YA0n.SRr rsegs W (mkCfg ms' md') Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (lib.Lib.MState.MS (lib.Lib.Frame.mkR rr0 (Z_to_bv 64 (rA S)) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
                      (Z_to_bv 64 (fs_frame FS 1 jj)) x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp)
                      (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8 s9 s10 (lib.Lib.Mem.wa ASAN_K) u3 u4 u5 u6)
                 F (Z_to_bv 64 0x8497c) fc None mb (lib.Lib.PropExec.seg_rom rsegs)) md) Q.
Proof.
  intros Hwx W md ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g ja jp jn jj
    rr0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Q
    Rfr Rlen Rpa Rpp Rpn HS S16 HSK RO ST Hg HF HO HOimg SW HHM HAE AW AFfr AOUT FP0 TLS0 SV FL1 FL2 Hjj
    RWIN SCW RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN RFRM SCFM K.
  (* (normalize mb is reached through the lemmas below) *)
  (* the side stack, from fp at the real base memory *)
  pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (FS0 & FS4 & FSGT & FSapp & _) & _ & _ & _ & HFSlo & _ & _ & HDd).
  unfold ASAN_GT, FS_SIZE in *.
  assert (HHM' : 17594333495296 <= S - 9072) by (unfold HIGHMEM_BEG in HHM; exact HHM).
  assert (Himg : ImgBounds.IMG_HI <= FS + 8) by (unfold ImgBounds.IMG_HI; lia).
  assert (HA1 : app_mem (FS + 8)) by (apply FSapp; lia).
  assert (HA2 : app_mem (FS + 16 - 1)) by (apply FSapp; lia).
  assert (Hsz : FS + 16 - (FS + 8) <= HIGHMEM_BEG - LOWMEM_END) by (unfold HIGHMEM_BEG, LOWMEM_END; lia).
  (* the class-1 flag byte: inside fp_w1 FS 1's flag range [fs_flag FS 1 0, fs_flag FS 1 0 + fs_M 1) =
     [FS + 20480, FS + 28672), below the class-1 frames, inside the side stack *)
  assert (EFLg : forall j, fs_flag FS 1 j = FS + 20480 + j)
    by (intros j; unfold fs_flag; change (Z.of_nat 1) with 1; change (2 ^ 15) with 32768;
        change (2 ^ (15 - 1)) with 16384; lia).
  pose proof (EFLg jj) as EFL.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (Hjj' : 0 <= jj < 8192) by (rewrite <- EM; exact Hjj).
  assert (HimgF : ImgBounds.IMG_HI <= fs_flag FS 1 jj) by (unfold ImgBounds.IMG_HI; lia).
  assert (HF1 : app_mem (fs_flag FS 1 jj)) by (apply FSapp; lia).
  assert (HF2 : app_mem (fs_flag FS 1 jj + 1 - 1)) by (apply FSapp; lia).
  assert (HszF : fs_flag FS 1 jj + 1 - fs_flag FS 1 jj <= HIGHMEM_BEG - LOWMEM_END)
    by (unfold HIGHMEM_BEG, LOWMEM_END; lia).
  set (RG := B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) in *.
  set (RH1 := rrB_avoid RG (FS + 8) (FS + 16)).
  set (RH := rrB_avoid RH1 (fs_flag FS 1 jj) (fs_flag FS 1 jj + 1)).
  (* the data ranges are apart from the hint word and from the class-1 flag bytes (fp_dj D (fp_w [1] FS)) *)
  assert (DJ : forall a b, In (a, b) (reac_ctrl_identity_reply_D fr len pa pp pn) ->
                 (b <= FS + 8 \/ FS + 16 <= a) /\ (b <= fs_flag FS 1 jj \/ fs_flag FS 1 jj + 1 <= a)).
  { intros a b Hin. unfold fp_dj in HDd. rewrite Forall_forall in HDd. pose proof (HDd (a, b) Hin) as H1. cbv beta in H1.
    rewrite Forall_forall in H1.
    assert (Hh : In (FS + 8, FS + 16) (fp_w [1%nat] FS)).
    { unfold fp_w, fp_w1. cbn [flat_map app]. left.
      assert (E1 : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
      rewrite E1. f_equal. lia. }
    assert (Hf : In (fs_flag FS 1 0, fs_flag FS 1 0 + fs_M 1) (fp_w [1%nat] FS))
      by (unfold fp_w, fp_w1; cbn [flat_map app]; right; left; reflexivity).
    pose proof (H1 _ Hh) as H2. pose proof (H1 _ Hf) as H3. pose proof (EFLg 0) as EF00.
    unfold lib.Prog.RcLay.ly_dj in H2, H3. cbn [fst snd] in H2, H3. split; lia. }
  assert (Dfr : reply_args fr pa pp pn = true -> 50 <= len ->
                (fr + 50 <= FS + 8 \/ FS + 16 <= fr) /\ (fr + 50 <= fs_flag FS 1 jj \/ fs_flag FS 1 jj + 1 <= fr)).
  { intros RA HL. apply DJ. unfold reac_ctrl_identity_reply_D. rewrite RA.
    replace (len <? 50) with false by (symmetry; apply Z.ltb_ge; lia). left. reflexivity. }
  assert (Dpa : reply_args fr pa pp pn = true ->
                (pa + 2 <= FS + 8 \/ FS + 16 <= pa) /\ (pa + 2 <= fs_flag FS 1 jj \/ fs_flag FS 1 jj + 1 <= pa)).
  { intros RA. apply DJ. unfold reac_ctrl_identity_reply_D. rewrite RA. apply in_or_app. right. left. reflexivity. }
  assert (Dpp : reply_args fr pa pp pn = true ->
                (pp + 8 <= FS + 8 \/ FS + 16 <= pp) /\ (pp + 8 <= fs_flag FS 1 jj \/ fs_flag FS 1 jj + 1 <= pp)).
  { intros RA. apply DJ. unfold reac_ctrl_identity_reply_D. rewrite RA. apply in_or_app. right. right. left.
    reflexivity. }
  assert (Dpn : reply_args fr pa pp pn = true ->
                (pn + 8 <= FS + 8 \/ FS + 16 <= pn) /\ (pn + 8 <= fs_flag FS 1 jj \/ fs_flag FS 1 jj + 1 <= pn)).
  { intros RA. apply DJ. unfold reac_ctrl_identity_reply_D. rewrite RA. apply in_or_app. right. right. right.
    left. reflexivity. }
  (* the footprint without the hint and without the flag byte: each range is apart from the hint (inner avoid) and
     from the flag byte (outer avoid); the window and the frames lie above the side stack's flag area *)
  assert (RWINh : ExecF.rng RH (S - 9072) 9072)
    by (apply rrB_rng_avoid; [apply rrB_rng_avoid; [exact RWIN | right; lia] | right; lia]).
  assert (SCWh : shcov RH (S - 9072) 9072).
  { apply rrB_shcov_avoid; [lia | unfold APPMEM_END in *; lia | lia | exact HF1 | exact HF2 | exact HszF |].
    apply rrB_shcov_avoid; [lia | unfold APPMEM_END in *; lia | lia | exact HA1 | exact HA2 | exact Hsz | exact SCW]. }
  pose proof (rrF_fs_frame1 FS 0) as EF0. pose proof (rrF_fs_frame1 FS (fs_M 1)) as EFM.
  assert (RFRMh : ExecF.rng RH (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0))
    by (apply rrB_rng_avoid; [apply rrB_rng_avoid; [exact RFRM | right; rewrite EF0; lia] | right; rewrite EF0; lia]).
  assert (SCFMh : shcov RH (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0)).
  { assert (L1 : fs_frame FS 1 0 = FS + 1085440) by (rewrite EF0; lia).
    assert (L2 : fs_frame FS 1 (fs_M 1) = FS + 2134016) by (rewrite EFM, EM; lia).
    apply rrB_shcov_avoid;
      [rewrite L1; lia | rewrite L1, L2; unfold APPMEM_END in *; lia | lia | exact HF1 | exact HF2 | exact HszF |].
    apply rrB_shcov_avoid;
      [rewrite L1; lia | rewrite L1, L2; unfold APPMEM_END in *; lia | lia | exact HA1 | exact HA2 | exact Hsz
      | exact SCFM]. }
  assert (RFRh : reply_args fr pa pp pn = true -> 50 <= len -> ExecF.rng RH fr 50).
  { intros RA HL. destruct (Dfr RA HL) as [D1 D2].
    apply rrB_rng_avoid; [apply rrB_rng_avoid; [exact (RFR RA HL) | destruct D1; [left|right]; lia] |
      destruct D2; [left|right]; lia]. }
  assert (SCFh : reply_args fr pa pp pn = true -> 50 <= len -> shcov RH fr 50).
  { intros RA HL. destruct (AFfr RA HL) as (A0 & _ & A2 & _).
    apply rrB_shcov_avoid; [lia | lia | lia | exact HF1 | exact HF2 | exact HszF |].
    apply rrB_shcov_avoid; [lia | lia | lia | exact HA1 | exact HA2 | exact Hsz | exact (SCF RA HL)]. }
  assert (SKFh : reply_args fr pa pp pn = true -> 50 <= len -> shkov RH fr 50).
  { intros RA HL. destruct (AFfr RA HL) as (A0 & _ & A2 & _).
    apply rrB_shkov_avoid; [lia | lia | lia | exact HF1 | exact HF2 | exact HszF |].
    apply rrB_shkov_avoid; [lia | lia | lia | exact HA1 | exact HA2 | exact Hsz | exact (SKF RA HL)]. }
  assert (RPAh : reply_args fr pa pp pn = true -> ExecF.rng RH pa 2).
  { intros RA. destruct (Dpa RA) as [D1 D2].
    apply rrB_rng_avoid; [apply rrB_rng_avoid; [exact (RPA RA) | destruct D1; [left|right]; lia] |
      destruct D2; [left|right]; lia]. }
  assert (SCPAh : reply_args fr pa pp pn = true -> shcov RH pa 2).
  { intros RA. destruct (AOUT RA) as ((A0 & _ & A2 & _) & _).
    apply rrB_shcov_avoid; [lia | lia | lia | exact HF1 | exact HF2 | exact HszF |].
    apply rrB_shcov_avoid; [lia | lia | lia | exact HA1 | exact HA2 | exact Hsz | exact (SCPA RA)]. }
  assert (RPPh : reply_args fr pa pp pn = true -> ExecF.rng RH pp 8).
  { intros RA. destruct (Dpp RA) as [D1 D2].
    apply rrB_rng_avoid; [apply rrB_rng_avoid; [exact (RPP RA) | destruct D1; [left|right]; lia] |
      destruct D2; [left|right]; lia]. }
  assert (SCPPh : reply_args fr pa pp pn = true -> shcov RH pp 8).
  { intros RA. destruct (AOUT RA) as (_ & (A0 & _ & A2 & _) & _).
    apply rrB_shcov_avoid; [lia | lia | lia | exact HF1 | exact HF2 | exact HszF |].
    apply rrB_shcov_avoid; [lia | lia | lia | exact HA1 | exact HA2 | exact Hsz | exact (SCPP RA)]. }
  assert (RPNh : reply_args fr pa pp pn = true -> ExecF.rng RH pn 8).
  { intros RA. destruct (Dpn RA) as [D1 D2].
    apply rrB_rng_avoid; [apply rrB_rng_avoid; [exact (RPN RA) | destruct D1; [left|right]; lia] |
      destruct D2; [left|right]; lia]. }
  assert (SCPNh : reply_args fr pa pp pn = true -> shcov RH pn 8).
  { intros RA. destruct (AOUT RA) as (_ & _ & (A0 & _ & A2 & _) & _).
    apply rrB_shcov_avoid; [lia | lia | lia | exact HF1 | exact HF2 | exact HszF |].
    apply rrB_shcov_avoid; [lia | lia | lia | exact HA1 | exact HA2 | exact Hsz | exact (SCPN RA)]. }
  (* the single-memory facts at normalize mb *)
  assert (STn : lib.Lib.Frame.stk rsegs (B.MemNorm.normalize rsegs mb) (S - 9072) S)
    by (apply B.MemNormTr.stk_normalize_ro; [exact RO | unfold ImgBounds.IMG_HI; lia | exact ST]).
  pose proof (B.MemNorm.mem_inv_normalize rsegs mb) as MIn.
  assert (HFn : reply_args fr pa pp pn = true -> 50 <= len ->
     fr + 50 <= 2^64 /\ lib.Lib.Mem.bytes_at rsegs (B.MemNorm.normalize rsegs mb) fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
     (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)).
  { intros RA HL. destruct (HF RA HL) as (A1 & A2 & A3). split; [exact A1|]. split; [|exact A3].
    exact (B.MemNorm.bytes_at_normalize rsegs mb _ _ RO A2). }
  assert (NR : forall p n, ImgBounds.IMG_HI <= p -> p + n <= 2 ^ 64 -> forall i, 0 <= i < n -> lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa (p + i)) = false)
    by (intros p n Hp Hn i Hi; apply (B.MemNormTr.ro_addr_above_img_range p n Hp Hn i Hi)).
  assert (HOn : reply_args fr pa pp pn = true ->
     pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
     lib.Lib.Step.rw_cells rsegs (B.MemNorm.normalize rsegs mb) pa [lib.Lib.Cells.CB 2 ja] /\ lib.Lib.Step.rw_cells rsegs (B.MemNorm.normalize rsegs mb) pp [lib.Lib.Cells.CB 8 jp] /\
     lib.Lib.Step.rw_cells rsegs (B.MemNorm.normalize rsegs mb) pn [lib.Lib.Cells.CB 8 jn] /\
     (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
     (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)).
  { intros RA. destruct (HO RA) as (A1 & A2 & A3 & C1 & C2 & C3 & REST).
    destruct (HOimg RA) as (I1 & I2 & I3). destruct (AOUT RA) as ((B0 & _ & B2 & _) & (B3 & _ & B5 & _) & (B6 & _ & B8 & _) & _).
    unfold APPMEM_END in *.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    split; [apply (B.MemNormTr.rw_cells_normalize mb pa _ RO); [intros i Hi; apply (NR pa 2); [exact I1 | lia | cbn in Hi; lia] | exact C1]|].
    split; [apply (B.MemNormTr.rw_cells_normalize mb pp _ RO); [intros i Hi; apply (NR pp 8); [exact I2 | lia | cbn in Hi; lia] | exact C2]|].
    split; [apply (B.MemNormTr.rw_cells_normalize mb pn _ RO); [intros i Hi; apply (NR pn 8); [exact I3 | lia | cbn in Hi; lia] | exact C3]|].
    exact REST. }
  pose proof (B.ShadowRwOnT.shadow_rw_on_normalize _ mb RO SW) as SWn.
  pose proof (B.MemNormTr.addressable_normalize mb _ _ RO AW) as AWn.
  assert (AFfrn : reply_args fr pa pp pn = true -> 50 <= len -> addressable (B.MemNorm.normalize rsegs mb) fr 50)
    by (intros RA HL; exact (B.MemNormTr.addressable_normalize mb _ _ RO (AFfr RA HL))).
  assert (AOUTn : reply_args fr pa pp pn = true ->
     addressable (B.MemNorm.normalize rsegs mb) pa 2 /\ addressable (B.MemNorm.normalize rsegs mb) pp 8 /\
     addressable (B.MemNorm.normalize rsegs mb) pn 8 /\
     (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)).
  { intros RA. destruct (AOUT RA) as (B1 & B2 & B3 & REST).
    split; [exact (B.MemNormTr.addressable_normalize mb _ _ RO B1)|].
    split; [exact (B.MemNormTr.addressable_normalize mb _ _ RO B2)|].
    split; [exact (B.MemNormTr.addressable_normalize mb _ _ RO B3) | exact REST]. }
  pose proof (B.MemNormTr.fp_normalize _ mb _ _ _ _ _ _ RO FP0) as FP0n.
  assert (TLS0n : reac_ctrl_identity_reply_tls (B.MemNorm.normalize rsegs mb) (bv_unsigned tp) FS (S - 9072) S)
    by exact (B.MemNormTr.tls_dj_normalize mb (bv_unsigned tp)
                (fp_w [1%nat] FS ++ [(shadow_addr (S - 9072), shadow_addr S)]) RO TLS0).
  assert (SVn : lib.Lib.Step.rw_cells rsegs (B.MemNorm.normalize rsegs mb) (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (B.MemNormTr.rw_cells_normalize mb _ _ RO); [|exact SV].
    intros i Hi. apply (NR (S - 104) 104); [unfold ImgBounds.IMG_HI; lia | lia | cbn in Hi; lia]. }
  pose proof (B.MemNorm.bytes_at_normalize rsegs mb _ _ RO FL1) as FL1n.
  pose proof (B.MemNorm.bytes_at_normalize rsegs mb _ _ RO FL2) as FL2n.
  pose proof (rrB_rBI_at ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (B.MemNorm.normalize rsegs mb) S FS MIn
                (fs_frame FS 1 jj) jj 1 SVn (fun _ => conj FL1n FL2n)) as HB.
  (* the run, the flag byte and the hint kept, the larger footprint, the lift *)
  pose proof (rrB_SB_run ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (B.MemNorm.normalize rsegs mb)
                fr len pa pp pn S FS g ja jp jn Rfr Rlen Rpa Rpp Rpn HS S16 HSK STn Hg HFn HOn SWn HHM HAE AWn
                AFfrn AOUTn FP0n TLS0n RH RWINh SCWh RFRh SCFh SKFh RPAh SCPAh RPPh SCPPh RPNh SCPNh RFRMh SCFMh
                jj rr0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hjj HB) as RUN.
  pose proof (rrB_evtF_keep Hwx RH (rrB_inH (fs_flag FS 1 jj) (fs_flag FS 1 jj + 1)) _ _ (rrB_inH_off _ _ HimgF)
                (rrB_avoid_fp _ _ _) RUN) as KEEPF.
  assert (AVH : lib.Reusable.YK04R.fp_avoids (rrB_inH (FS + 8) (FS + 16)) RH).
  { intros a n Ha.
    exact (rrB_avoid_fp RG (FS + 8) (FS + 16) a n
             (rrB_avoid_sub RH1 (fs_flag FS 1 jj) (fs_flag FS 1 jj + 1) (bv_unsigned a) n Ha)). }
  pose proof (rrB_evtF_keep Hwx RH (rrB_inH (FS + 8) (FS + 16)) _ _ (rrB_inH_off _ _ Himg) AVH KEEPF) as KEEP.
  pose proof (rrB_evtF_mono RH RG _ _
                (fun b n Hb => rrB_avoid_sub RG (FS + 8) (FS + 16) b n
                                 (rrB_avoid_sub RH1 (fs_flag FS 1 jj) (fs_flag FS 1 jj + 1) b n Hb)) KEEP) as RUNW.
  apply (rrB_lift Hwx W md _ F _ fc None mb (lib.Lib.PropExec.seg_rom rsegs) _ Q RO RUNW).
  intros ms' md' (s0' & ((HQ & HKFL) & HK) & HREL & HROS) Hhid Hs. apply K. unfold rrB_SBpost.
  split; [exists s0'; split; [exact HQ|]; split; [exact HREL|]; split; [exact HROS|]; split; [exact HK | exact HKFL]|].
  split; [exact Hhid | exact Hs].
Qed.
End SB.
