(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane). *)
(* fuzz_ctrl image A: reac_ctrl_build_as (0x84870) as a step of the cgif-form world walk, up to its tail jump to
   ctrl_emit_as. From the proved stretch reac_ctrl_build_as_stretch_F_holds (A/Prog/reac_ctrl_build_asF.v: the
   run from entry to the tail jump, or to the return of 0 when the argument checks fail) through the kit bridge
   (Reusable/YA0nR.v SRr_fevt) at RNG := RNG_W (w_H Wd) (A/ProgBridge.v), in the form of
   ProgLift/reac_ctrl_kind_name.v. The stretch stops at the jump because ctrl_emit_as reaches the fake-stack
   allocator (__asan_stack_malloc_1, via ctrl_lay_block) and the bridge lifts only silent runs; the caller applies
   ctrl_emit_as's cgif spec from the jump state. reac_box_model_upstream_width (a leaf, no fake-stack event) runs
   inside the stretch on its footprint contract.
   Premises: the stretch's own non-footprint premises, verbatim, except its `mem_inv rsegs m`: the caller gives
   `ro_agree rsegs m` (MemNorm; no world source exists for mem_inv, two Theorem Labs lanes), the stretch runs on
   `normalize rsegs m` and MemNormF.evtF_normalize_ro moves it to m (a Theorem Labs lane's pattern, declaration_of.v (not in this delivery)). One
   range_visible fact per caller-owed rng range (image shadow, window, md); the image, GOT_CELL_K and CELL_K are
   paid by ProgBridge.img_vis_W. The continuation takes reac_ctrl_build_as_stretch_post_ro. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK0i YK11 YK04 YK04R YA0n YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 ProgBridge.
(* AsanRT (frame-route list, a Theorem Labs lane 23:52Z): qualified; this lift is proof-internal (a Theorem Labs lane 23:54Z, decision (A)). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcPorts RcPortsLib RcBox RcSynth RcLay
  RcLayLib RcFin RcEmit RcEmitLib RcAsan RcAsanLib RcLeafLib reac_ctrl_build_as_c reac_ctrl_build_as.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c RcAsanFP
  ctrl_emit_as_c reac_box_model_upstream_width_c reac_box_model_block_c reac_ctrl_build_as_c reac_ctrl_build_as.
(* The _F file, qualified (glue closure rule, a Theorem Labs lane 23:38Z): only its stretch theorem is used. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_build_asF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNorm MemNormTr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ImgBounds.
Import ListNotations.
Open Scope Z_scope.

Lemma vis2 : forall H a1 n1 a2 n2, range_visible H a1 n1 /\ range_visible H a2 n2 ->
  ExecF.rng (RNG_W H) a1 n1 /\ ExecF.rng (RNG_W H) a2 n2.
Proof. intros H a1 n1 a2 n2 [V1 V2]. split; apply rng_of_visible; assumption. Qed.

Section L.
Context {fx : lib.Reusable.YK11.FPState}.

(* INTERFACE (a Theorem Labs lane's _post_ro form, 03:07Z): the stretch's post with `ro_agree rsegs _` in place of
   `mem_inv rsegs _` in both arms, over the REAL memory; nothing else changed. *)
Definition reac_ctrl_build_as_stretch_post_ro
    (ra sp gp tp s0 s1 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (o md b d s ns : Z) (mb : list byte) (ms' : machine_state) : Prop :=
    let S := bv_unsigned sp in
    let Lo := S - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let go := ba_go o md b in

         (go = true /\ (exists (t0' t1' t2' a0' a1' a2' a3' a4' a6' a7' t3' t4' t5' t6' : word) (mu : word -> option byte),
            ms' = lib.Lib.MState.MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5 a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 CTRL_EMIT_AS) fc None mu (lib.Reusable.YK11.seg_rom rsegs)
            /\ a0' = Z_to_bv 64 o /\ a1' = Z_to_bv 64 (lib.A.Prog.reac_ctrl_build_as_c.BA_FR + 24 * ba_row b) /\ a2' = Z_to_bv 64 md
            /\ a3' = Z_to_bv 64 d /\ a4' = Z_to_bv 64 s /\ a6' = Z_to_bv 64 n /\ a7' = Z_to_bv 64 0
            /\ t4' = Z_to_bv 64 ns
            /\ munch [(Lo, S)] m mu /\ wmono rsegs m mu /\ ro_agree rsegs mu /\ stk rsegs mu Lo S))
         \/
         (go = false /\ (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                                (m' : word -> option byte),
            ms' = lib.Lib.MState.MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0)
                          a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (lib.Lib.MState.ret_pc ra) fc None m' (lib.Reusable.YK11.seg_rom rsegs)
            /\ munch [(S - 80, S)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' Lo S)).

(* route (C) (a Theorem Labs lane 09:20Z; a Theorem Labs lane form rule 09:37Z): the _on twin; the universal shadow_rw premise is DROPPED
   (the stretch's _on twin reads none). *)
Lemma reac_ctrl_build_as_SRr_at_on :
  wx_segs_nowrap rsegs -> reac_box_model_upstream_width_contract_F ->
  forall (Wd : world rsegs) (model : Model)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns : Z) (mb db sb : list byte)
         (Q : world rsegs -> config -> Prop),
    let S := bv_unsigned sp in
    let Lo := S - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let go := ba_go o md b in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns ->
    stk rsegs m Lo S ->
    length db = 6%nat -> length sb = 6%nat ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ lib.Lib.Mem.bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    ro_agree rsegs m ->
    (* asan *)
    AsanRT.asan_cells m ->
    AsanRT.HIGHMEM_BEG <= Lo -> AsanRT.addressable m BA_SW 56 -> (md <> 0 -> AsanRT.addressable m md 296) ->
    (* the footprint the caller owes: image shadow, own window, model at md (image, GOT_CELL_K and CELL_K are
       paid here by ProgBridge.img_vis_W) *)
    range_visible (w_H Wd) 0x7fffa000 0xbdc00 ->
    range_visible (w_H Wd) Lo lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K ->
    (md <> 0 -> range_visible (w_H Wd) md 296 /\
       range_visible (w_H Wd) (AsanRT.shadow_addr md / 8 * 8) (AsanRT.shadow_addr (md + 295) / 8 * 8 + 8 - AsanRT.shadow_addr md / 8 * 8)) ->
    (forall ms' model',
       reac_ctrl_build_as_stretch_post_ro ra sp gp tp s0 s1 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m o md b d s ns mb ms' ->
       same_but_materialized model model' -> SRr rsegs Wd (mkCfg ms' model') Q) ->
    SRr rsegs Wd
      (mkCfg (lib.Lib.MState.MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS) fc None m (lib.Reusable.YK11.seg_rom rsegs)) model) Q.
Proof.
  intros Hwx HUW Wd model ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns mb db sb Q.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 HST Hdb Hsb HM Pro HAC HHM ASW AM VISH VWIN VMD K.
  (* the stretch's memory premises on normalize m (MemNormTr; the stretch writes only its own stack frame, so no
     not-read-only premise is owed) *)
  assert (Nstk : stk rsegs (normalize rsegs m) (bv_unsigned sp - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp)).
  { apply stk_normalize_ro; [exact Pro | unfold ImgBounds.IMG_HI, AsanRT.HIGHMEM_BEG in *; lia | exact HST]. }
  assert (NM : md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\
                lib.Lib.Mem.bytes_at rsegs (normalize rsegs m) md mb /\
                ly_dj (bv_unsigned sp - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) md (md + 296)).
  { intros H0. destruct (HM H0) as (M1 & M2 & M3 & M4 & M5).
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
    split; [exact (bytes_at_normalize rsegs m _ _ Pro M4) | exact M5]. }
  pose proof (mem_inv_normalize rsegs m) as Nmi.
  pose proof (asan_cells_normalize m Pro HAC) as Nac.
  pose proof (addressable_normalize m _ _ Pro ASW) as Nsw56.
  assert (Nam : md <> 0 -> AsanRT.addressable (normalize rsegs m) md 296)
    by (intros H0; exact (addressable_normalize m _ _ Pro (AM H0))).
  pose proof (mem_rel_normalize rsegs m Pro) as REL.
  (* the image and the two runtime cells inside it: visible in every world (ProgBridge) *)
  assert (VIMG : range_visible (w_H Wd) 0x10000 0x5ee000) by exact (img_vis_W Wd).
  assert (VGK : range_visible (w_H Wd) AsanRT.GOT_CELL_K 8).
  { apply (range_visible_sub _ ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO));
      [exact (img_vis_W Wd) | | | ]; unfold AsanRT.GOT_CELL_K, ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia. }
  assert (VCK : range_visible (w_H Wd) AsanRT.CELL_K 8).
  { apply (range_visible_sub _ ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO));
      [exact (img_vis_W Wd) | | | ]; unfold AsanRT.CELL_K, ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia. }
  apply (SRr_fevt rsegs Hwx Wd _ model (RNG_W (w_H Wd))
           (reac_ctrl_build_as_stretch_post_ro ra sp gp tp s0 s1 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m o md b d s ns mb)).
  - apply fevt_of_evtF.
    (* the stretch's run on normalize m *)
    pose proof (reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_on_holds (RNG_W (w_H Wd)) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  F fc (normalize rsegs m) o md b d s ns mb db sb
                  Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Nstk Hdb Hsb NM Nmi Nac HHM Nsw56 Nam
                  (rng_of_visible _ _ _ VIMG) (rng_of_visible _ _ _ VISH) (rng_of_visible _ _ _ VWIN)
                  (rng_of_visible _ _ _ VGK) (rng_of_visible _ _ _ VCK)
                  (fun H0 => vis2 _ _ _ _ _ (VMD H0))) as HN.
    cbv zeta in HN.
    (* moved to m; the post comes back through ms_rel *)
    destruct (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ m _ Pro HN) as (ms' & Hrun & s0' & PO & HREL & HROS).
    exists ms'. split; [exact Hrun|].
    unfold reac_ctrl_build_as_stretch_post_ro. cbv zeta. cbv beta in PO.
    destruct PO as [[HG (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a6' & a7' & t3' & t4' & t5' & t6' & mu &
                        E & E0 & E1 & E2 & E3 & E4 & E6 & E7 & E9 & MU & WM & _ & ST)] |
                    [HG (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                        E & MU & WM & _ & ST)]].
    + rewrite E in HREL. destruct (ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
      left. split; [exact HG|].
      exists t0', t1', t2', a0', a1', a2', a3', a4', a6', a7', t3', t4', t5', t6', (ms_mem ms').
      split; [exact Ems|].
      split; [exact E0|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
      split; [exact E4|]. split; [exact E6|]. split; [exact E7|]. split; [exact E9|].
      split; [exact (munch_rel rsegs _ m _ _ _ REL HMR HROS MU)|].
      split; [exact (wmono_rel rsegs m _ _ _ REL HMR HROS WM)|].
      split; [exact (ro_agree_of_mem_rel rsegs _ _ HMR)|].
      exact (stk_of_rel _ _ _ _ HMR ST).
    + rewrite E in HREL. destruct (ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
      right. split; [exact HG|].
      exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem ms').
      split; [exact Ems|].
      split; [exact (munch_rel rsegs _ m _ _ _ REL HMR HROS MU)|].
      split; [exact (wmono_rel rsegs m _ _ _ REL HMR HROS WM)|].
      split; [exact (ro_agree_of_mem_rel rsegs _ _ HMR)|].
      exact (stk_of_rel _ _ _ _ HMR ST).
  - exact (fp_avoids_RNG_W (w_H Wd)).
  - exact K.
Qed.

(* The old name, from the _on twin. *)
Lemma reac_ctrl_build_as_SRr_at :
  wx_segs_nowrap rsegs -> reac_box_model_upstream_width_contract_F ->
  forall (Wd : world rsegs) (model : Model)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns : Z) (mb db sb : list byte)
         (Q : world rsegs -> config -> Prop),
    let S := bv_unsigned sp in
    let Lo := S - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let go := ba_go o md b in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns ->
    stk rsegs m Lo S ->
    length db = 6%nat -> length sb = 6%nat ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ lib.Lib.Mem.bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    ro_agree rsegs m ->
    (* asan *)
    AsanRT.asan_cells m -> AsanRT.shadow_rw m ->
    AsanRT.HIGHMEM_BEG <= Lo -> AsanRT.addressable m BA_SW 56 -> (md <> 0 -> AsanRT.addressable m md 296) ->
    (* the footprint the caller owes: image shadow, own window, model at md (image, GOT_CELL_K and CELL_K are
       paid here by ProgBridge.img_vis_W) *)
    range_visible (w_H Wd) 0x7fffa000 0xbdc00 ->
    range_visible (w_H Wd) Lo lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K ->
    (md <> 0 -> range_visible (w_H Wd) md 296 /\
       range_visible (w_H Wd) (AsanRT.shadow_addr md / 8 * 8) (AsanRT.shadow_addr (md + 295) / 8 * 8 + 8 - AsanRT.shadow_addr md / 8 * 8)) ->
    (forall ms' model',
       reac_ctrl_build_as_stretch_post_ro ra sp gp tp s0 s1 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m o md b d s ns mb ms' ->
       same_but_materialized model model' -> SRr rsegs Wd (mkCfg ms' model') Q) ->
    SRr rsegs Wd
      (mkCfg (lib.Lib.MState.MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS) fc None m (lib.Reusable.YK11.seg_rom rsegs)) model) Q.
Proof.
  intros Hwx HUW Wd model ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns mb db sb Q.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 HST Hdb Hsb HM Pro HAC _ HHM ASW AM VISH VWIN VMD K.
  exact (reac_ctrl_build_as_SRr_at_on Hwx HUW Wd model ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o md b d s ns mb db sb Q
           Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 HST Hdb Hsb HM Pro HAC HHM ASW AM VISH VWIN VMD K).
Qed.

(* reac_ctrl_build_as_SRr_at whose continuation also gets that the run keeps every hidden byte of the start
   memory m (Reusable/YA0nR.v SRr_fevt_hid): the premise of Reusable/YCbq.v ajournal_exec after a callee that
   writes memory (a Theorem Labs lane 03:41Z; same binders and premises; the fact is over the real m). *)
(* route (C) (a Theorem Labs lane 09:20Z; a Theorem Labs lane form rule 09:37Z): the _on twin; the universal shadow_rw premise is DROPPED
   (the stretch's _on twin reads none). *)
Lemma reac_ctrl_build_as_SRr_at_hid_on :
  wx_segs_nowrap rsegs -> reac_box_model_upstream_width_contract_F ->
  forall (Wd : world rsegs) (model : Model)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns : Z) (mb db sb : list byte)
         (Q : world rsegs -> config -> Prop),
    let S := bv_unsigned sp in
    let Lo := S - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let go := ba_go o md b in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns ->
    stk rsegs m Lo S ->
    length db = 6%nat -> length sb = 6%nat ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ lib.Lib.Mem.bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    ro_agree rsegs m ->
    (* asan *)
    AsanRT.asan_cells m ->
    AsanRT.HIGHMEM_BEG <= Lo -> AsanRT.addressable m BA_SW 56 -> (md <> 0 -> AsanRT.addressable m md 296) ->
    (* the footprint the caller owes: image shadow, own window, model at md (image, GOT_CELL_K and CELL_K are
       paid here by ProgBridge.img_vis_W) *)
    range_visible (w_H Wd) 0x7fffa000 0xbdc00 ->
    range_visible (w_H Wd) Lo lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K ->
    (md <> 0 -> range_visible (w_H Wd) md 296 /\
       range_visible (w_H Wd) (AsanRT.shadow_addr md / 8 * 8) (AsanRT.shadow_addr (md + 295) / 8 * 8 + 8 - AsanRT.shadow_addr md / 8 * 8)) ->
    (forall ms' model',
       reac_ctrl_build_as_stretch_post_ro ra sp gp tp s0 s1 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m o md b d s ns mb ms' ->
       (forall x : word, w_H Wd x = true -> ms_mem ms' x = m x) ->
       same_but_materialized model model' -> SRr rsegs Wd (mkCfg ms' model') Q) ->
    SRr rsegs Wd
      (mkCfg (lib.Lib.MState.MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS) fc None m (lib.Reusable.YK11.seg_rom rsegs)) model) Q.
Proof.
  intros Hwx HUW Wd model ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns mb db sb Q.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 HST Hdb Hsb HM Pro HAC HHM ASW AM VISH VWIN VMD K.
  (* the stretch's memory premises on normalize m (MemNormTr; the stretch writes only its own stack frame, so no
     not-read-only premise is owed) *)
  assert (Nstk : stk rsegs (normalize rsegs m) (bv_unsigned sp - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp)).
  { apply stk_normalize_ro; [exact Pro | unfold ImgBounds.IMG_HI, AsanRT.HIGHMEM_BEG in *; lia | exact HST]. }
  assert (NM : md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\
                lib.Lib.Mem.bytes_at rsegs (normalize rsegs m) md mb /\
                ly_dj (bv_unsigned sp - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K) (bv_unsigned sp) md (md + 296)).
  { intros H0. destruct (HM H0) as (M1 & M2 & M3 & M4 & M5).
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
    split; [exact (bytes_at_normalize rsegs m _ _ Pro M4) | exact M5]. }
  pose proof (mem_inv_normalize rsegs m) as Nmi.
  pose proof (asan_cells_normalize m Pro HAC) as Nac.
  pose proof (addressable_normalize m _ _ Pro ASW) as Nsw56.
  assert (Nam : md <> 0 -> AsanRT.addressable (normalize rsegs m) md 296)
    by (intros H0; exact (addressable_normalize m _ _ Pro (AM H0))).
  pose proof (mem_rel_normalize rsegs m Pro) as REL.
  (* the image and the two runtime cells inside it: visible in every world (ProgBridge) *)
  assert (VIMG : range_visible (w_H Wd) 0x10000 0x5ee000) by exact (img_vis_W Wd).
  assert (VGK : range_visible (w_H Wd) AsanRT.GOT_CELL_K 8).
  { apply (range_visible_sub _ ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO));
      [exact (img_vis_W Wd) | | | ]; unfold AsanRT.GOT_CELL_K, ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia. }
  assert (VCK : range_visible (w_H Wd) AsanRT.CELL_K 8).
  { apply (range_visible_sub _ ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO));
      [exact (img_vis_W Wd) | | | ]; unfold AsanRT.CELL_K, ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia. }
  apply (SRr_fevt_hid rsegs Hwx Wd _ model (RNG_W (w_H Wd))
           (reac_ctrl_build_as_stretch_post_ro ra sp gp tp s0 s1 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m o md b d s ns mb)).
  - apply fevt_of_evtF.
    (* the stretch's run on normalize m *)
    pose proof (reac_ctrl_build_asF.reac_ctrl_build_as_stretch_F_on_holds (RNG_W (w_H Wd)) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  F fc (normalize rsegs m) o md b d s ns mb db sb
                  Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Nstk Hdb Hsb NM Nmi Nac HHM Nsw56 Nam
                  (rng_of_visible _ _ _ VIMG) (rng_of_visible _ _ _ VISH) (rng_of_visible _ _ _ VWIN)
                  (rng_of_visible _ _ _ VGK) (rng_of_visible _ _ _ VCK)
                  (fun H0 => vis2 _ _ _ _ _ (VMD H0))) as HN.
    cbv zeta in HN.
    (* moved to m; the post comes back through ms_rel *)
    destruct (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ m _ Pro HN) as (ms' & Hrun & s0' & PO & HREL & HROS).
    exists ms'. split; [exact Hrun|].
    unfold reac_ctrl_build_as_stretch_post_ro. cbv zeta. cbv beta in PO.
    destruct PO as [[HG (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a6' & a7' & t3' & t4' & t5' & t6' & mu &
                        E & E0 & E1 & E2 & E3 & E4 & E6 & E7 & E9 & MU & WM & _ & ST)] |
                    [HG (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                        E & MU & WM & _ & ST)]].
    + rewrite E in HREL. destruct (ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
      left. split; [exact HG|].
      exists t0', t1', t2', a0', a1', a2', a3', a4', a6', a7', t3', t4', t5', t6', (ms_mem ms').
      split; [exact Ems|].
      split; [exact E0|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|].
      split; [exact E4|]. split; [exact E6|]. split; [exact E7|]. split; [exact E9|].
      split; [exact (munch_rel rsegs _ m _ _ _ REL HMR HROS MU)|].
      split; [exact (wmono_rel rsegs m _ _ _ REL HMR HROS WM)|].
      split; [exact (ro_agree_of_mem_rel rsegs _ _ HMR)|].
      exact (stk_of_rel _ _ _ _ HMR ST).
    + rewrite E in HREL. destruct (ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
      right. split; [exact HG|].
      exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem ms').
      split; [exact Ems|].
      split; [exact (munch_rel rsegs _ m _ _ _ REL HMR HROS MU)|].
      split; [exact (wmono_rel rsegs m _ _ _ REL HMR HROS WM)|].
      split; [exact (ro_agree_of_mem_rel rsegs _ _ HMR)|].
      exact (stk_of_rel _ _ _ _ HMR ST).
  - exact (fp_avoids_RNG_W (w_H Wd)).
  - exact K.
Qed.

(* The old name, from the _on twin. *)
Lemma reac_ctrl_build_as_SRr_at_hid :
  wx_segs_nowrap rsegs -> reac_box_model_upstream_width_contract_F ->
  forall (Wd : world rsegs) (model : Model)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns : Z) (mb db sb : list byte)
         (Q : world rsegs -> config -> Prop),
    let S := bv_unsigned sp in
    let Lo := S - lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let go := ba_go o md b in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns ->
    stk rsegs m Lo S ->
    length db = 6%nat -> length sb = 6%nat ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ lib.Lib.Mem.bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    ro_agree rsegs m ->
    (* asan *)
    AsanRT.asan_cells m -> AsanRT.shadow_rw m ->
    AsanRT.HIGHMEM_BEG <= Lo -> AsanRT.addressable m BA_SW 56 -> (md <> 0 -> AsanRT.addressable m md 296) ->
    (* the footprint the caller owes: image shadow, own window, model at md (image, GOT_CELL_K and CELL_K are
       paid here by ProgBridge.img_vis_W) *)
    range_visible (w_H Wd) 0x7fffa000 0xbdc00 ->
    range_visible (w_H Wd) Lo lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS_K ->
    (md <> 0 -> range_visible (w_H Wd) md 296 /\
       range_visible (w_H Wd) (AsanRT.shadow_addr md / 8 * 8) (AsanRT.shadow_addr (md + 295) / 8 * 8 + 8 - AsanRT.shadow_addr md / 8 * 8)) ->
    (forall ms' model',
       reac_ctrl_build_as_stretch_post_ro ra sp gp tp s0 s1 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m o md b d s ns mb ms' ->
       (forall x : word, w_H Wd x = true -> ms_mem ms' x = m x) ->
       same_but_materialized model model' -> SRr rsegs Wd (mkCfg ms' model') Q) ->
    SRr rsegs Wd
      (mkCfg (lib.Lib.MState.MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 lib.A.Prog.reac_ctrl_build_as_c.REAC_CTRL_BUILD_AS) fc None m (lib.Reusable.YK11.seg_rom rsegs)) model) Q.
Proof.
  intros Hwx HUW Wd model ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns mb db sb Q.
  cbv zeta.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 HST Hdb Hsb HM Pro HAC _ HHM ASW AM VISH VWIN VMD K.
  exact (reac_ctrl_build_as_SRr_at_hid_on Hwx HUW Wd model ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o md b d s ns mb db sb Q
           Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 HST Hdb Hsb HM Pro HAC HHM ASW AM VISH VWIN VMD K).
Qed.
End L.
