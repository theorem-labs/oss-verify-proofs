(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_model_block_glue.v, with its module paths and module names changed; 268 of its 348 lines of code are new or changed and 2332 lines of the source are left out. *)
(* ctrl_lay_block (0x86104) on fuzz_ctrl's ASan+UBSan build, image B (libreac v1.9.0): the SHARED base of the cgif
   glue pb_ctrl_lay_block (a Theorem Labs lane; hands a Theorem Labs lane).  rule 24: no function proved here.

   PLAN OF RECORD: ctrl_lay_block-B-glue-plan.md sections 1, 2 (a working note, not in this delivery).
   This file is the image-B twin of the shared part of a Theorem Labs lane's image-A glue
   (lib/A/Prog/C_ctrl_lay_block_glue.v (from a working branch 9861af6cbb5), at head: lay_SRr_norm :103, LayLib :137,
   LayBase :205-385, lay_stack_malloc_atS :608, lay_acall_kept_after_munch :698, lay_ret_regs :735, lay_fs1 :744),
   same proofs with B's names, and the descriptor lay_D1 (plan section 2): the boundary facts after
   __asan_stack_malloc_1 returns at pc 0x861bc, which lay_to_ret (ctrl_lay_block_gR1.v) produces and lay_R23
   (ctrl_lay_block_gR23.v) consumes.  B's spec is general in g (A's has g = 0), so lay_ret_regs takes g.

   CLOSURE (glue closure rule): the _F files are Required QUALIFIED, never Imported; no lib/AZ, no AsanW / W6 /
   SegCF / *_cfw / Cf* file.  The six core modules that exist twice (lib/Reusable/<X> and lib/B/Reusable/<X>: YI04 YI16
   YK11 YK1b YM05 YO09) are Required, never Imported, and named lib.Reusable.<X>.<name>.  Every MemNorm / MemNormF /
   MemNormTr / ProgBridge / ProgWorld / AsanRT / Img0 name is written B.<module>.<name> (the root lib/MemNorm.v is a
   convertible twin of lib/B/MemNorm.v). *)
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
(* the B world bridges and ProgWorld (lemmas and statements only) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.Img0 B.AsanRT B.ProgBridge B.ProgWorld B.MemNorm B.MemNormF
  B.MemNormTr B.ACtlK B.ACtlCut.
(* route (C): the cut's runtime facts without AR_states_vis0_shadow (a Theorem Labs lane: ctl_rt_C_of_AR, PROVED from
   AR; its shadow parts are the cut's own regions cut_shadow / img_shadow, B.ACtlRtC) and their transport to the
   normalized memory (B.ShadowRwOnT.shadow_rw_on_normalize) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn B.ShadowRwOnT B.ACtlRtC B.ProgWorldCtlRtC.
(* the B ProgWorld statements this file reads, by their PROVING lemmas (a Theorem Labs lane; no statement is a hypothesis) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldShadow.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require PropExec ExecF MState Mem Frame Step Cells Regs6ss.
(* the _F closure and the contract, QUALIFIED only *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds CtrlBase asan_stack_malloc_c ctrl_lay_block_c
  ctrl_lay_blockF_on C_ctrl_lay_block.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation rget := lib.Reusable.YK11.getr.
Local Notation rmkst := lib.Reusable.YK11.mkst.
(* The walk's segments (C_ctrl_lay_block.v:79); = B.Img0.rsegs by conversion (B.ProgBridge.tfibsegs_rsegs). *)
#[local] Notation SEGS := lib.Reusable.YB1v.tfibsegs.

(* ================================================================================================================
   1. The lift of one stretch: a footprint run on the normalized memory is a silent prefix of a world walk from the
   real memory, for a footprint that avoids the world's hidden bytes; the continuation gets the run, the post carried
   back through ms_rel, and the hidden bytes kept.  A glue :82-111, same proof.
   ================================================================================================================ *)
Section Lift.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma lay_SRr_norm : lib.Reusable.YK04.wx_segs_nowrap B.Img0.rsegs ->
  forall (W : world B.Img0.rsegs) (RNG : lib.Lib.ExecF.footprint) (model : Model) (R F : bvmap 5 word) (pc : word)
         (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
         (K : world B.Img0.rsegs -> config -> Prop),
  lib.Reusable.YK04R.fp_avoids (w_H W) RNG ->
  B.MemNorm.ro_agree B.Img0.rsegs m ->
  lib.Lib.ExecF.evtF B.Img0.rsegs RNG Q
    (lib.Lib.MState.MS R F pc fc None (B.MemNorm.normalize B.Img0.rsegs m) (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) ->
  (forall ms' model',
     lib.Reusable.YK04R.fsteps B.Img0.rsegs RNG
       (lib.Lib.MState.MS R F pc fc None m (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) ms' ->
     (exists s0, Q s0 /\ B.MemNorm.ms_rel B.Img0.rsegs ms' s0 /\ B.MemNorm.ro_same B.Img0.rsegs m (ms_mem ms')) ->
     (forall x : word, w_H W x = true -> ms_mem ms' x = m x) ->
     same_but_materialized model model' -> SRr B.Img0.rsegs W (mkCfg ms' model') K) ->
  SRr B.Img0.rsegs W
    (mkCfg (lib.Lib.MState.MS R F pc fc None m (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) model) K.
Proof.
  intros Hwx W RNG model R F pc fc m Q K Hfp Hro HN Hk.
  destruct (B.MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ m _ Hro HN) as (ms' & Hrun & HP).
  pose proof (B.ProgBridge.fsteps_of_mstepsF _ _ _ Hrun) as Hf.
  apply (lib.Reusable.YA0nR.SRr_fevt_hid B.Img0.rsegs Hwx W
           (lib.Lib.MState.MS R F pc fc None m (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) model RNG
           (fun s => lib.Reusable.YK04R.fsteps B.Img0.rsegs RNG
                       (lib.Lib.MState.MS R F pc fc None m (lib.Lib.PropExec.seg_rom B.Img0.rsegs)) s /\
                     exists s0, Q s0 /\ B.MemNorm.ms_rel B.Img0.rsegs s s0 /\
                                B.MemNorm.ro_same B.Img0.rsegs m (ms_mem s))).
  - exists ms'. split; [exact Hf | split; [exact Hf | exact HP]].
  - exact Hfp.
  - intros ms1 model1 [Hf1 HP1] Hhid Hs. exact (Hk ms1 model1 Hf1 HP1 Hhid Hs).
Qed.
End Lift.

(* ================================================================================================================
   2. Byte-level glue between the core's view and ctrl's raw-memory facts (A glue :137-191, same proofs), and the
   view -> raw-memory readings of A's ProgWorld_Fs.v (pw_view_mrd :48, pw_bytes_of_view :67, pw_stk_of_present :116)
   which image B also proves, in lib/B/ProgWorld_Fs.v (:77, :96, :145).  The lib.Lib layer is Imported inside this
   module only.
   ================================================================================================================ *)
Module LayLib.
Import lib.Lib.PropExec lib.Lib.MState lib.Lib.Mem lib.Lib.Frame lib.Lib.Cells lib.Lib.Step.
Local Open Scope Z_scope.

Lemma bytes_at_agree : forall (m m' : word -> option byte) a bs, bytes_at B.Img0.rsegs m a bs ->
  (forall i, (i < length bs)%nat -> m' (wa (a + Z.of_nat i)) = m (wa (a + Z.of_nat i))) ->
  bytes_at B.Img0.rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  specialize (H i Hi). unfold mrd in *. rewrite (E i Hi). exact H.
Qed.

Lemma wr_at_agree : forall (m m' : word -> option byte) a n, wr_at B.Img0.rsegs m a n ->
  (forall i, 0 <= i < n -> m' (wa (a + i)) = m (wa (a + i))) -> wr_at B.Img0.rsegs m' a n.
Proof.
  intros m m' a n (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  specialize (H i Hi). unfold wview in *. rewrite (E i Hi). exact H.
Qed.

Lemma rw_cells_agree : forall (m m' : word -> option byte) a cs, rw_cells B.Img0.rsegs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wa (a + i)) = m (wa (a + i))) ->
  rw_cells B.Img0.rsegs m' a cs.
Proof.
  intros m m' a cs [[Hwf Hb] Hw] E. split; [split; [exact Hwf|]|].
  - apply (bytes_at_agree m); [exact Hb|]. intros i Hi. apply E.
    rewrite (cells_bytes_length cs Hwf) in Hi. lia.
  - exact (wr_at_agree m m' a _ Hw E).
Qed.

(* At a visible address outside the segments the view determines the raw byte. *)
Lemma raw_of_aview : forall {fx : lib.Reusable.YK11.FPState} (W : world SEGS)
    (mem mem' : word -> option byte) (a : Z),
  0 <= a < 2 ^ 64 -> w_H W (Z_to_bv 64 a) = false -> ~ in_img SEGS a ->
  aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a ->
  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
  intros fx W mem mem' a Ha Hh Hni E.
  rewrite !(B.ProgWorld.aview_vis_mrd W _ a Hh) in E.
  assert (Hs : seg_rom B.Img0.rsegs (Z_to_bv 64 a) = None).
  { apply (B.MemNorm.seg_rom_unmapped B.Img0.rsegs). rewrite Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    exact (find_segment_none SEGS a Hni). }
  unfold mrd in E. rewrite Hs in E.
  destruct (mem' (Z_to_bv 64 a)) as [b'|], (mem (Z_to_bv 64 a)) as [b0|]; cbn [option_map] in E;
    try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* Addresses at or above the allocation ceiling are outside the segments. *)
Lemma above_ceil_not_img : forall {rc : lib.Reusable.YM05.RunCeil} a, lib.Reusable.YM05.alloc_ceiling <= a ->
  ~ in_img SEGS a.
Proof.
  intros rc a Ha Hi. pose proof (B.ProgWorld.pws_segs_low a Hi) as H.
  pose proof asan_consts as (C1 & _). unfold kLowMemEnd in H. lia.
Qed.

(* A byte the view reads is visible, and mrd reads it (A ProgWorld_Fs.v pw_view_mrd :47). *)
Lemma view_mrd : forall {fx : lib.Reusable.YK11.FPState} (W : world SEGS) (m : word -> option byte) (a v : Z),
  aview SEGS (w_H W) m a = Some v ->
  w_H W (Z_to_bv 64 a) = false /\ mrd B.Img0.rsegs m (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros fx W m a v Hv.
  assert (Hh : w_H W (Z_to_bv 64 a) = false).
  { destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [|reflexivity]. exfalso.
    unfold aview, mbyte, mrestrict in Hv. rewrite Hh in Hv.
    unfold lib.Reusable.YK11.seg_rom in Hv.
    rewrite (memory_read1_hidden SEGS (w_H W) (w_Hoff W) _ Hh) in Hv.
    cbn [option_map] in Hv. discriminate Hv. }
  split; [exact Hh|].
  rewrite (B.ProgWorld.aview_vis_mrd W m a Hh) in Hv.
  destruct (mrd B.Img0.rsegs m (Z_to_bv 64 a)) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as <-. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* Bytes the view reads, as ctrl's bytes_at (A ProgWorld_Fs.v pw_bytes_of_view :66). *)
Lemma bytes_of_view : forall {fx : lib.Reusable.YK11.FPState} (W : world SEGS) (m : word -> option byte) (a : Z)
    (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat -> exists b, nth_error bs i = Some b /\
     aview SEGS (w_H W) m (a + Z.of_nat i) = Some (bv_unsigned b)) ->
  bytes_at B.Img0.rsegs m a bs.
Proof.
  intros fx W m a bs Ha Hb H. split; [exact Ha|]. split; [exact Hb|].
  intros i Hi. destruct (H i Hi) as (b & Hn & Hv). rewrite Hn.
  destruct (view_mrd W m _ _ Hv) as [_ Hm]. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hm. exact Hm.
Qed.

(* Present bytes are stack bytes (A ProgWorld_Fs.v pw_stk_of_present :115). *)
Lemma stk_of_present : forall (H : word -> bool) (m : word -> option byte) (lo hi : Z),
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) ->
  stk B.Img0.rsegs m lo hi.
Proof.
  intros H m lo hi Hlo Hhi Hp. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. destruct (Hp a Ha) as [_ (b & Hb)]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.
End LayLib.

(* ================================================================================================================
   3. The world-side lemmas over B's bundle.  Section hypotheses: core rules (LAWS, errno_low, ML, SMP) and the
   bundle's symbols (CTS); the B ProgWorld statements are PROVED (a Theorem Labs lane) and cited by their lemmas (Let), so none
   is a premise.  Only the hypotheses a lemma uses become its premises after End.
   ================================================================================================================ *)
Section GB.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}.
Variable B : asyms.
(* ---- core (YCbq Section d0 premises; B's TfibLib record Reusable.YCeg does not compile on any B base yet) ---- *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis errno_low : api_env SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
(* ---- B ProgWorld: the bundle's symbols, and the proved statements cited by their lemmas ---- *)
Hypothesis CTS : lib.Reusable.YF0m.CtrlTSyms B.
Let ctl_stack_shadow_of_AR : B.ProgWorld.ctl_stack_shadow_of_AR_stmt B := B.ProgWorldShadow.ctl_stack_shadow_of_AR B.

(* ---- 3a. The runtime facts at the normalized memory of a cut (A glue LayBase.rt_facts :192), route (C): from
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR (PROVED from AR; no AR_states_vis0_shadow, no AR_states_owned_ro), the shadow as
   the cut's own regions, B.ACtlRtC.cut_shadow B ly S (frames F, live blocks L, zero-shadow ranges Z, the side
   stack's frames area) and B.ACtlRtC.img_shadow (the image hull I) ---- *)
Lemma lay_rt_facts : forall RLO RHI ly S (W : world SEGS) m md,
  AR SEGS B ly S W m md ->
  B.Prog.CtrlBase.arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) m) ->
  B.MemNorm.ro_agree B.Img0.rsegs m /\ B.AsanRT.asan_cells (B.MemNorm.normalize B.Img0.rsegs m) /\
  B.ShadowRwOn.shadow_rw_on (B.ACtlRtC.cut_shadow B ly S) (B.MemNorm.normalize B.Img0.rsegs m) /\
  B.ShadowRwOn.shadow_rw_on B.ACtlRtC.img_shadow (B.MemNorm.normalize B.Img0.rsegs m).
Proof.
  intros RLO RHI ly S W m md HAR HRO.
  destruct (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B CTS LAWS RLO RHI ly S W m md HAR HRO) as (AC & SC & SI & RO).
  assert (Hro : B.MemNorm.ro_agree B.Img0.rsegs m) by exact RO.
  split; [exact Hro|].
  split; [exact (B.MemNormTr.asan_cells_normalize m Hro AC)|].
  split; [exact (B.ShadowRwOnT.shadow_rw_on_normalize _ m Hro SC) |
          exact (B.ShadowRwOnT.shadow_rw_on_normalize _ m Hro SI)].
Qed.

(* ---- 3b. A present stack window at the normalized memory (A glue LayBase.win_facts :203) ---- *)
Lemma lay_win_facts : forall ly S (W : world SEGS) m md lo hi,
  AR SEGS B ly S W m md -> B.MemNorm.ro_agree B.Img0.rsegs m ->
  ly_stk_lo ly <= lo -> lo <= hi -> hi <= ly_stk_hi ly ->
  (forall a, lo <= a < hi -> apresent (w_H W) m a) ->
  lib.Lib.Frame.stk B.Img0.rsegs (B.MemNorm.normalize B.Img0.rsegs m) lo hi /\
  B.AsanRT.addressable (B.MemNorm.normalize B.Img0.rsegs m) lo (hi - lo) /\
  B.AsanRT.HIGHMEM_BEG <= lo /\ hi <= B.AsanRT.APPMEM_END /\ lib.Reusable.YM05.alloc_ceiling <= lo.
Proof.
  intros ly S W m md lo hi HAR Hro Hlo Hle Hhi Hp.
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_stk_ceil _ LO) as SC. pose proof (lo_top _ LO) as (_ & _ & _ & T4 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold ASAN_CEIL in SC.
  split; [|split; [|split; [|split]]].
  - apply B.MemNormTr.stk_normalize_ro; [exact Hro | unfold B.Prog.ImgBounds.IMG_HI; lia |].
    apply (LayLib.stk_of_present (w_H W)); [lia | unfold kHighMemEnd in T4; lia | exact Hp].
  - apply B.MemNormTr.addressable_normalize; [exact Hro|].
    exact (ctl_stack_shadow_of_AR LAWS ly S W m md lo (hi - lo) HAR Hlo ltac:(lia) ltac:(lia)).
  - unfold B.AsanRT.HIGHMEM_BEG. lia.
  - unfold B.AsanRT.APPMEM_END. unfold kHighMemEnd in T4. lia.
  - lia.
Qed.

(* ---- 3c. The allocator event (class cid), A glue :592-669 (= YCbq.aj_stack_malloc_at, YCbq.v:1749-1809, same
   proof), whose post also hands on what B.ProgWorld.ctl_fs_of_astack_stmt takes from astack_malloc_realizes:
   ecall_pre at the call, AR at the new state, the realizes post's frame condition (YG0d.v:298-299) and the window
   presence (YG0d.v:300). ---- *)
Lemma lay_stack_malloc_atS : forall cid, astack_malloc_realizes SEGS B cid -> 0 <= cid <= 10 ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  rget regsT 3 = w64 (as_gp B) -> rget regsT 4 = w64 (as_tp B) ->
  rget regsT 1 = raw -> lib.Reusable.YK0s.ret_ok raw ->
  count_cid cid (frames Sc) < fs_frames cid ->
  SRr SEGS W (mkCfg (rmkst regsT (Z_to_bv 64 (pc_stack_malloc (as_code B) cid)) memT (lib.Reusable.YK11.seg_rom SEGS))
                    mdc)
    (fun W2 c2 => W2 = W /\ exists S2 regs2 mem2 md2 pos,
      c2 = mkCfg (rmkst regs2 raw mem2 (lib.Reusable.YK11.seg_rom SEGS)) md2 /\
      ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem md ((cid, pos) :: own) lyc S2 W mem2 md2 k /\
      aregs_preserved regsT regs2 /\ rget regs2 10 = w64 (frame_addr lyc cid pos) /\
      ablocks B lyc S2 = ablocks B lyc Sc /\ frames S2 = (cid, pos) :: frames Sc /\ ~ In (cid, pos) (frames Sc) /\
      st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
      zero_shadow (aview SEGS (w_H W) mem2) SHADOW_OFF (frame_addr lyc cid pos) (fs_frame_bytes cid) /\
      rdword (aview SEGS (w_H W) mem2) (frame_addr lyc cid pos + fs_frame_bytes cid - 8) =
        Some (flag_addr lyc cid pos) /\
      acall_kept SEGS B lyc Sc W memT W mem2 (sp0 + o - ESTACK) (sp0 + o) (fun _ => False) /\
      (exists f, S2 = set_fs f Sc) /\
      (* what ctl_fs_of_astack takes *)
      ecall_pre SEGS B lyc Sc W regsT memT mdc /\ AR SEGS B lyc S2 W mem2 md2 /\
      (forall a, spZ regsT - ESTACK <= a < spZ regsT -> apresent (w_H W) mem2 a) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a ->
         ~ (spZ regsT - ESTACK <= a < spZ regsT) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
  intros cid ASM Hcid W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
    HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hcnt.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5
    & HQT).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
  assert (ASTACK = 16384) as Has by reflexivity. assert (ESTACK = 4096) as Hes by reflexivity.
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (HstkC : astk_ok ESTACK lyc (spZ regsT)).
  { unfold astk_ok, ly_bot in *. rewrite Hsp', Eslo, Eshi, Etop. repeat split; try zlia.
    all: rewrite Z.add_mod, Hal16, Hal by zlia; reflexivity. }
  assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
  { split; [exact HAR|]. split; [rewrite Hra; exact Hraw|]. split; [destruct HstkC as (Q1 & _); exact Q1|].
    split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
    split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
  pose proof (am_wf _ _ _ _ (proj1 HAR)) as HWF.
  destruct (SMP Sc cid HWF Hcid Hcnt) as (pos & S2 & Hpath).
  pose proof (ml_stack_malloc _ ML Sc cid HWF Hcid) as HTOK.
  destruct (atok_apath _ _ _ [] (PFake cid pos, S2) HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post in HQ.
  destruct HQ as (HWF2 & (f & ES2) & _ & Hpos & Hfrs2 & Hfresh).
  eapply SRr_mono; [exact (ASM lyc Sc W regsT memT mdc pos S2 HPRE Hcnt Hpath)|].
  cbv beta. intros W2 c2 HwleW (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hz & Hflag & Hfpres & Hfr
    & Hpres2).
  assert (Hblk : blocks S2 = blocks Sc) by (rewrite ES2; reflexivity).
  assert (Eab2 : ablocks B lyc S2 = ablocks B lyc Sc) by (unfold ablocks; rewrite Hblk; reflexivity).
  assert (Hnev2 : st_nev S2 = st_nev Sc) by (rewrite ES2; reflexivity).
  assert (Hbb : blocks_bytes S2 = blocks_bytes Sc) by (rewrite ES2; reflexivity).
  assert (Hsecs2 : st_secs S2 = st_secs Sc) by (rewrite ES2; reflexivity).
  assert (HJ1 : ajournal (SK := SK) SEGS B ESTACK (spZ regsT) [] lyc Sc W memT mdc [(cid, pos)] lyc S2 W mem2 md2 0).
  { eapply (call_effect_journal SEGS B LAWS B.ProgWorld.pws_segs_low errno_low ESTACK lyc Sc W regsT memT mdc lyc S2 W
              mem2 md2 (fun _ => False) [] [(cid, pos)] 0);
      [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hpres2
      | exact HAR | exact HstkC | cbn; exact Hfrs2 | zlia | zlia | rewrite Hsecs2; zlia | intros a [] | | ].
    - intros a H0 H1 H2 H3 _. apply (Hfr a H0 H1 H2). intros H. apply H3. left. exact H.
    - intros p n i Hp Hnp. exfalso. apply Hnp. rewrite Eab2. exact Hp.
    - rewrite ES2. apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT]. }
  split; [reflexivity|]. exists S2, regs2, mem2, md2, pos.
  split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned;
          reflexivity|].
  split.
  { rewrite Hsp' in HJ1. replace k with (k + 0) by zlia. change ((cid, pos) :: own) with ([(cid, pos)] ++ own).
    eapply (ajournal_sub SEGS B LAWS B.ProgWorld.pws_segs_low); [exact HJ | exact HJ1 | zlia | zlia | intros a (rg & [] & _)]. }
  split; [exact HP|]. split; [exact Hres|]. split; [exact Eab2|]. split; [exact Hfrs2|]. split; [exact Hfresh|].
  split; [exact Hnev2|]. split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hflag|].
  split.
  { rewrite Hsp' in HJ1. eapply (acall_kept_of_journal SEGS B B.ProgWorld.pws_segs_low);
      [exact HJ1 | exact HAR | intros a (rg & [] & _) | | exact sink_closed_nil].
    intros b m i Hb Hi _. rewrite Eab2. exact Hb. }
  split; [exists f; exact ES2|].
  split; [exact HPRE|]. split; [exact HAR2|]. split; [exact Hpres2 | exact Hfr].
Qed.

(* ---- 3d. What a call keeps (acall_kept), after a stretch that wrote only a window of the machine stack
   (A glue :682-716, same proof). ---- *)
Lemma lay_acall_kept_after_munch : forall lyc Sc (W : world SEGS) (memc mem1 mem2 : word -> option byte)
    md (lo hi lo1 hi1 lo2 hi2 : Z) (E : Z -> Prop),
  AR SEGS B lyc Sc W memc md ->
  lib.Reusable.YM05.alloc_ceiling <= lo -> lo2 <= lo -> hi <= hi2 -> lo2 <= lo1 -> hi1 <= hi2 ->
  lib.Lib.Frame.munch [(lo, hi)] memc mem1 ->
  acall_kept SEGS B lyc Sc W mem1 W mem2 lo1 hi1 E ->
  (forall a, lo2 <= a < hi2 -> apresent (w_H W) mem2 a) ->
  acall_kept SEGS B lyc Sc W memc W mem2 lo2 hi2 E.
Proof.
  intros lyc Sc W memc mem1 mem2 md lo hi lo1 hi1 lo2 hi2 E HAR Hc H1 H2 H3 H4 HM (K1 & K2 & K3 & K4 & K5 & K6) Hp.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
            aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a).
  { intros a Ha Hn. apply aview_eq_of. unfold mrestrict. rewrite (HM (Z_to_bv 64 a)); [reflexivity|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    cbn [lib.Lib.Frame.outside]. split; [lia | exact I]. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn. rewrite (K1 a Ha ltac:(lia)). apply EQ; lia.
  - intros b0 m0 i Hin Hi HE. rewrite (K2 b0 m0 i Hin Hi HE).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b0 m0 HAR Hin) as (_ & Hb0 & Hb1 & _). apply EQ; lia.
  - intros a Hi Hs He. rewrite (K3 a Hi Hs He). pose proof (B.ProgWorld.pws_segs_low a Hi) as HL.
    unfold kLowMemEnd in HL. apply EQ; lia.
  - intros cid pos a Hin Hr HE. rewrite (K4 cid pos a Hin Hr HE).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (F1 & F2 & F3).
    pose proof (fs_frame_bytes_nonneg cid) as Fn.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
    + apply EQ; lia.
    + unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Hr. pose proof asan_consts as (D1 & _).
      apply EQ; Z.div_mod_to_equations; lia.
  - intros a Ha Hn Hpr. apply (K5 a Ha ltac:(lia)).
    destruct Hpr as [Hh (bb & Hb)]. split; [exact Hh|]. exists bb. rewrite (HM (Z_to_bv 64 a)); [exact Hb|].
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    cbn [lib.Lib.Frame.outside]. split; [lia | exact I].
  - exact Hp.
Qed.

(* ================================================================================================================
   4. The descriptor D1 (plan section 2): the state after __asan_stack_malloc_1 returns (pc 0x861bc), real memory mem2.
   SP2 := (spZ regs - 128) / 32 * 32.
   ================================================================================================================ *)
(* The callee-saved registers after the allocator returns: CUTS.ly_pre_sm1's call state (x2 = x9 = SP2, x8 = the entry
   sp, x19 = g, x20 = f, x22 = p, x23 = md, x26 = ASAN_K; x3 x4 x18 x21 x24 x25 x27 the entry's). *)
Definition lay_ret_regs (regs regs2 : bvmap 5 word) (A p f md g : Z) : Prop :=
  rget regs2 2 = w64 A /\ rget regs2 3 = rget regs 3 /\ rget regs2 4 = rget regs 4 /\
  rget regs2 8 = rget regs 2 /\ rget regs2 9 = w64 A /\ rget regs2 18 = rget regs 18 /\
  rget regs2 19 = w64 g /\ rget regs2 20 = w64 f /\ rget regs2 21 = rget regs 21 /\
  rget regs2 22 = w64 p /\ rget regs2 23 = w64 md /\ rget regs2 24 = rget regs 24 /\
  rget regs2 25 = rget regs 25 /\ rget regs2 26 = w64 B.AsanRT.ASAN_K /\ rget regs2 27 = rget regs 27.

(* ctl_fs_of_astack_stmt's conclusion for the class-1 frame (B ProgWorld.v:485-500 at cid = 1), on the memory after
   the allocator; lo := S - 4512, the bottom of the call window; S2sp := SP2. *)
Definition lay_fs1 (FS pos lo S2sp : Z) (a0 : word) (mem' : word -> option byte) : Prop :=
  let fr := B.Prog.asan_stack_malloc_c.fs_frame FS 1 pos in
  let n := B.Prog.asan_stack_malloc_c.fs_B 1 in
  0 <= pos < B.Prog.asan_stack_malloc_c.fs_M 1 /\
  a0 = Z_to_bv 64 fr /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem' (B.Prog.asan_stack_malloc_c.fs_flag FS 1 pos) (Z_to_bv 8 1 :: nil) /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem' (fr + n - 8)
    (lib.Lib.Mem.le8 (Z_to_bv 64 (B.Prog.asan_stack_malloc_c.fs_flag FS 1 pos))) /\
  lib.Lib.Mem.bytes_at B.Img0.rsegs mem' (B.AsanRT.shadow_addr fr) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8))) /\
  B.AsanRT.addressable mem' fr (fs_frame_bytes 1) /\
  lib.Lib.Frame.stk B.Img0.rsegs mem' fr (fr + n) /\
  (forall a, fr <= a < fr + n -> B.AsanRT.app_mem a) /\
  fr mod 64 = 0 /\ FS <= fr /\ fr + n <= FS + B.Prog.asan_stack_malloc_c.FS_SIZE /\
  B.Prog.asan_stack_malloc_c.ASAN_GT <= fr /\
  lib.Lib.Frame.stk B.Img0.rsegs mem' lo S2sp.

(* D1.  The caller's journal grown by the class-1 frame (1, pos); AR at the new state; a0 = the frame; the registers;
   the class-1 frame's bytes (lay_fs1); what the call keeps of the entry memory memc outside the call window
   [S - 4512, S) (acall_kept, and the non-owned frame condition of astack_malloc_realizes carried to memc); the 12
   saves the prologue wrote at [S - 96, S). *)
Definition lay_D1 (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS)
    (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (p f md g : Z)
    (S2 : astate) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) (pos : Z) : Prop :=
  ajournal (SK := SK) SEGS B STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k /\
  frames S2 = (1, pos) :: frames Sc /\ ~ In (1, pos) (frames Sc) /\
  ablocks B lyc S2 = ablocks B lyc Sc /\ (exists fS, S2 = set_fs fS Sc) /\
  AR SEGS B lyc S2 W mem2 md2 /\
  rget regs2 10 = w64 (frame_addr lyc 1 pos) /\
  lay_ret_regs regs regs2 ((spZ regs - 128) / 32 * 32) p f md g /\
  lay_fs1 (ly_F lyc) pos (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) ((spZ regs - 128) / 32 * 32)
    (rget regs2 10) mem2 /\
  acall_kept SEGS B lyc Sc W memc W mem2 (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK) (spZ regs) (fun _ => False) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B lyc S2 a ->
     ~ (spZ regs - C_ctrl_lay_block.CTRL_LAY_BLOCK_STK <= a < spZ regs) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
  lib.Lib.Step.rw_cells B.Img0.rsegs mem2 (spZ regs - 96)
    (ctrl_lay_blockF_on.SAVES (rget regs 1) (rget regs 8) (rget regs 9) (rget regs 18) (rget regs 19) (rget regs 20)
       (rget regs 21) (rget regs 22) (rget regs 23) (rget regs 24) (rget regs 25) (rget regs 26)).
End GB.
