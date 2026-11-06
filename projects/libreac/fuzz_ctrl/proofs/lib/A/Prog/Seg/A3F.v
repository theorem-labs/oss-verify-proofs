(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 785 of its 828 lines of code are new or changed and 353 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/A3.v; 154 of its 243 lines of code are new or changed and 739 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/A3.v 0d4714ea12bd (the blob this tree had at release c5e779efe8c) at 6a74d5929d2.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: a3_evt_of_F re-derives A3.a3_evt at ExecF.RNG_all; a3_evt_of_F_verbatim checks by constr_eq that its
   type is the type of A3.a3_evt after the callee premise. Mechanical re-run, route (a) (lead 22:15Z); input to the
   ported walk only. *)

(* The footprint (ExecF.evtF) twin of A3.v's one run lemma a3_evt (segment-runs-A.tsv row S_A3, a3_evt:217):
   0x80f88-0x810e0, the 87 instructions of the ASan prologue of LLVMFuzzerTestOneInput, and the shadow fill call
   of meta_fill_f8 (__asan_set_shadow_f8, 0x55008) at 0x810e0 by its contract.

   WHAT CHANGES AGAINST A3.v, and nothing else:
   - The run steps over lib/Lib/StepF.v instead of the lib/A/Tk/UL engine, so every hypothesis the store tactic
     reads must be a lib.Lib one. A3.a3_evt states its four write regions as lib.A.Tk.UL cells
     (US.rw_cells ... [UCl.CB n junk]); a3_evt_F states them UNCHANGED and converts them in the first four lines
     of the proof by lib/A/Tk/UL/CellBridge.v's rw_cells_ul_lib (that file is a Theorem Labs lane's image-B bridge, blob
     7761521b3b52 at a working branch 7cfcf43257e, with the module paths changed to lib.A.Tk.UL).
     The two cell inductives have the same five constructors, so the conversion is total.
   - The callee is taken through asan_set_shadow_cF.v's asan_set_shadow_f8_contract_F (PROVED by
     asan_set_shadowF.v asan_set_shadow_f8_holds_F, both taken by path from a Theorem Labs lane 71a8e88cc7e), in the place
     where A3.a3_evt takes the plain asan_set_shadow_f8_contract: the first premise, the R2F / R19F shape.
   - f8_callF is the evtF twin of A3.f8_call, used only inside a3_evt_F. A3.f8_call is the contract application
     itself: its start state IS the callee entry 0x55008 and its continuation is a universal hypothesis, so it is
     not a run that needs a stretch and it gets no deliverable _F / _of_F / pin of its own (A3F.rng.tsv records
     this). A3.lib_evt_cut is an engine bridge, not a run, and is re-used here as it stands.
   - A3.v is unchanged apart from comments.

   APPENDED PREMISES (all after every premise of A3.a3_evt; RNG is the FIRST binder):
     - RngBytes.rng_bytes RNG: a premise of asan_set_shadow_f8_contract_F itself (its route-1 proof needs the
       footprint byte-wise, since an access may straddle two adjacent rng ranges). PASSED THROUGH unchanged, as
       the spec directs for a callee premise that is itself a forall-memory form.
     - ExecF.rng RNG (A + 304) 8   : the spill cell, premise US.rw_cells rsegs mem (A + 304) [CB 8 j1].
     - ExecF.rng RNG fr 24         : the frame header, premise US.rw_cells rsegs mem fr [CB 24 j2].
     - ExecF.rng RNG S3 68         : the first 68 shadow bytes, premise US.rw_cells rsegs mem S3 [CB 68 j3].
     - ExecF.rng RNG (S3 + 68) 187 : the 187 shadow bytes the call fills, premise
                                     US.rw_cells rsegs mem (S3 + 68) [CB 187 j4]; it is also the callee's own
                                     written-range premise ExecF.rng RNG A N.
     - ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) : the callee's image range (its code, the GOT cell GOT_REAL_MEMSET
                                     and the runtime cell REAL_MEMSET lie inside it), by its contract_F.
     - ExecF.rng RNG (bv_unsigned (reg_get regs 2) - ASAN_SET_SHADOW_K) ASAN_SET_SHADOW_K : the callee's own stack
                                     window, with ASAN_SET_SHADOW_K = 0 (EXACT: the helper and musl memset have no
                                     frame), by its contract_F. The run itself never touches sp.
   The run reads no image constant of its own (the frame-description word 0x11b66 and the function word 0x80edc
   are auipc/addi immediates, and S3 = fr / 8 + ASAN_K is srli/add), so no further region is named. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge Exec Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require CellBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI BzBridge MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require YN01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib asan_set_shadow_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_malloc_c asan_set_shadow_cF ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs A3.
(* Last but YK11: StepF's step / if_false / finish (evtF goals) shadow the UL engine's (evt goals), and StepF
   re-exports lib.Lib's PropExec / MState / Mem / Cells / Exec / Step / Frame / Tac, so every bare engine name
   below (MS, mkR, rw_cells, CB, munch, bytes_at) is lib.Lib's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
(* Restore YK11.getr / YK11.FPState (A3.a3_evt's fp_regs and fp_csr are YK11's) as the default. By the FULL path,
   as A3.v:33 does: lib/Reusable/YK11.v and lib/B/Reusable/YK11.v carry the same short name, and the require
   closure of MemNormF / RngBytes brings lib/Reusable into scope. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module CBr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.CellBridge.
Module SSC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_set_shadow_c.
Module SSHF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_set_shadow_cF.
Module IMGB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ImgBounds.
Module RBY := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.RngBytes.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.

(* ---- The shadow fill call at 0x810e0 under a footprint: A3.f8_call with the footprint contract in the place of
   the plain one, ExecF.evtF in the place of the UL engine's evt, and the lib.Lib cells the StepF store tactic
   reads. The memory is normalized first (MemNormF.evtF_normalize_ro, the evtF form of MemNorm.evt_normalize that
   A3.f8_call uses: the contract asks mem_inv, the run gives ro_agree). *)
Lemma f8_callF : SSHF.asan_set_shadow_f8_contract_F ->
  forall (RNG : ExecF.footprint)
    (Q : machine_state -> Prop) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 (F : bvmap 5 word) fc (m : word -> option byte) (a n : Z) junk,
  0x5fe000 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  (forall i, 0 <= i < n -> in_shadow (a + i)) ->
  rw_cells rsegs m a [CB (Z.to_nat n) junk] -> asan_cells m -> ro_agree rsegs m ->
  (forall t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
     munch [(a, a + n)] m m' -> wmono rsegs m m' -> ro_agree rsegs m' ->
     bytes_at rsegs m' a (repeat (Z_to_bv 8 0xf8) (Z.to_nat n)) ->
     ExecF.evtF rsegs RNG Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
               s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  RBY.rng_bytes RNG ->
  ExecF.rng RNG IMGB.IMG_LO (IMGB.IMG_HI - IMGB.IMG_LO) ->
  ExecF.rng RNG (bv_unsigned sp - SSHF.ASAN_SET_SHADOW_K) SSHF.ASAN_SET_SHADOW_K ->
  ExecF.rng RNG a n ->
  ExecF.evtF rsegs RNG Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
            s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x55008) fc None m (seg_rom rsegs)).
Proof.
  intros HC RNG Q ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a n
    junk Ha Hn Han HIS HRW HAC HRO K RBYT RIMG RSP RDST.
  pose proof (mem_rel_normalize rsegs m HRO) as HREL.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib.MState.unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by
    (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib.MState.unsigned_lit; lia).
  unfold SSHF.asan_set_shadow_f8_contract_F, SSHF.asan_set_shadow_contract_F, SSC.ASAN_SET_SHADOW_F8 in HC.
  eapply ExecF.evtF_cut.
  - eapply (MNF.evtF_normalize_ro RNG _ _ F _ fc None m (seg_rom rsegs) HRO).
    pose proof (HC RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
      s9 s10 s11 t3 t4 t5 t6 F fc (normalize rsegs m) junk) as H.
    cbv zeta in H. rewrite Ua, Un in H.
    apply H.
    + exact HIS.
    + apply (A3.rw_norm m a (Z.to_nat n) junk HRO Ha); [rewrite Z2Nat.id by lia; lia|].
      pose proof (CBr.rw_cells_lib_ul rsegs m a _ HRW) as HRWu.
      cbn [map CBr.lib_cell_ul] in HRWu. exact HRWu.
    + exact (A3.asan_cells_norm m HRO HAC).
    + apply mem_inv_normalize.
    + exact RBYT.
    + exact RIMG.
    + exact RSP.
    + exact RDST.
  - intros ms' (s0' & HP & HMS & HROS).
    unfold SSC.asan_set_shadow_post in HP.
    destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' & -> &
      MU & WM & MI & RW).
    rewrite Ua, Un in MU, RW.
    destruct ms' as [r' f' pc' svc' rv' fc' mm ro'].
    unfold ms_rel in HMS. cbn in HMS, HROS.
    destruct HMS as (Er & Ef & Epc & Esvc & Erv & Efc & Ero & HMR). subst r' f' pc' svc' rv' fc' ro'.
    refine (K t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mm _ _ _ _).
    + intros x Hx. destruct (ro_addr rsegs x) eqn:E.
      * exact (HROS x E).
      * rewrite <- (mem_rel_rw rsegs mm m'' x HMR E). rewrite (MU x Hx). unfold normalize. rewrite E. reflexivity.
    + intros x Hx. destruct (ro_addr rsegs x) eqn:E.
      * unfold wview in *. rewrite (HROS x E). exact Hx.
      * rewrite <- (wview_rel_rw rsegs mm m'' x HMR E). apply WM.
        rewrite (wview_rel_rw rsegs m (normalize rsegs m) x HREL E). exact Hx.
    + exact (ro_agree_of_mem_rel rsegs mm m'' HMR).
    + destruct RW as ((_ & RB) & _). cbn [cells_bytes cbytes] in RB. rewrite app_nil_r in RB.
      destruct RB as (B0 & B1 & B2). split; [exact B0|]. split; [exact B1|]. intros i Hi.
      rewrite (mrd_rel rsegs mm m'' _ HMR). exact (B2 i Hi).
Qed.

(* A lib.Lib run is a UL-engine run: A3.lib_evt_cut (A3.v:83, an engine bridge, not a run) with the trivial
   continuation. The two msteps are separate inductives over the same mstep, so this needs the bridge. *)
Lemma evt_lib_ul : forall (P : machine_state -> Prop) ms, LEx.evt rsegs P ms -> UE.evt rsegs P ms.
Proof. intros P ms H. apply (A3.lib_evt_cut P P ms H). intros ms' HP. apply UE.evt_done. exact HP. Qed.

Section RunF.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

(* A3.a3_evt with (RNG : ExecF.footprint) bound FIRST, the same binders and premises in the same order, the
   footprint premises appended, and ExecF.evtF in the place of the UL engine's evt. The post is A3.KA, unchanged. *)
Lemma a3_evt_F : SSHF.asan_set_shadow_f8_contract_F ->
  forall (RNG : ExecF.footprint) (regs : bvmap 5 word) (mem : word -> option byte) (A fr S3 : Z) j1 j2 j3 j4,
  getr regs 9 = Z_to_bv 64 A -> getr regs 22 = Z_to_bv 64 fr -> getr regs 26 = Z_to_bv 64 ASAN_K ->
  US.rw_cells rsegs mem (A + 304) [UCl.CB 8 j1] -> US.rw_cells rsegs mem fr [UCl.CB 24 j2] ->
  US.rw_cells rsegs mem S3 [UCl.CB 68 j3] -> US.rw_cells rsegs mem (S3 + 68) [UCl.CB 187 j4] ->
  fr + 24 <= A + 304 -> S3 + 255 <= A + 304 -> (fr + 24 <= S3 \/ S3 + 255 <= fr) ->
  0x5fe000 <= fr -> 0x5fe000 <= S3 -> S3 + 255 < 2 ^ 64 -> fr < 2 ^ 64 -> S3 = fr / 8 + ASAN_K ->
  (forall i, 0 <= i < 187 -> in_shadow (S3 + 68 + i)) ->
  asan_cells mem -> ro_agree rsegs mem ->
  RBY.rng_bytes RNG ->
  ExecF.rng RNG (A + 304) 8 ->
  ExecF.rng RNG fr 24 ->
  ExecF.rng RNG S3 68 ->
  ExecF.rng RNG (S3 + 68) 187 ->
  ExecF.rng RNG IMGB.IMG_LO (IMGB.IMG_HI - IMGB.IMG_LO) ->
  ExecF.rng RNG (bv_unsigned (reg_get regs 2) - SSHF.ASAN_SET_SHADOW_K) SSHF.ASAN_SET_SHADOW_K ->
  ExecF.evtF rsegs RNG
    (fun ms => exists R pc' mem',
       ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS R fp_regs pc' fp_csr None mem'
         (seg_rom rsegs) /\
                 A3.KA regs mem A fr S3 R pc' mem')
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS (Regs6ss.mkR_of regs) fp_regs
       (Z_to_bv 64 0x80f88) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros HC RNG regs mem A fr S3 j1 j2 j3 j4 H9 H22 H26 C1u C2u C3u C4u D1 D2 D3 G1 G2 G3 Hfr HS3 HIS HAC HRO
    RBYT RA304 RFR RS3 RSH RIMG RSP.
  (* the four write regions, carried from the UL engine's cells into lib.Lib's (CellBridge) *)
  pose proof (CBr.rw_cells_ul_lib rsegs mem (A + 304) _ C1u) as C1. cbn [map CBr.ul_cell_lib] in C1.
  pose proof (CBr.rw_cells_ul_lib rsegs mem fr _ C2u) as C2. cbn [map CBr.ul_cell_lib] in C2.
  pose proof (CBr.rw_cells_ul_lib rsegs mem S3 _ C3u) as C3. cbn [map CBr.ul_cell_lib] in C3.
  pose proof (CBr.rw_cells_ul_lib rsegs mem (S3 + 68) _ C4u) as C4. cbn [map CBr.ul_cell_lib] in C4.
  clear C1u C2u C3u C4u.
  assert (H9' : reg_get regs 9 = Z_to_bv 64 A) by exact H9.
  assert (H22' : reg_get regs 22 = Z_to_bv 64 fr) by exact H22.
  assert (H26' : reg_get regs 26 = Z_to_bv 64 ASAN_K) by exact H26.
  rewrite A3.ms_ul_lib.
  unfold Regs6ss.mkR_of. rewrite H9', H22', H26'.
  clear H9 H22 H26 H9' H22' H26'.
  pose proof (munch_refl [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] mem) as MU.
  pose proof (wmono_refl rsegs mem) as WM.
  do 15 step.
  replace (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 fr)) 3 + ASAN_K)) with (Z_to_bv 64 S3)
    by (f_equal; rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib.MState.unsigned_lit by lia;
      rewrite Z.shiftr_div_pow2 by lia; exact HS3).
  do 68 step.
  do 4 step.
  match goal with |- ExecF.evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HW : forall x : word, 0x5fe000 > bv_unsigned x ->
             outside [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] (bv_unsigned x)).
  { intros x Hx. cbn [outside]. repeat split; intros [? ?]; lia. }
  assert (HRO1 : ro_agree rsegs m1).
  { intros x Hx. rewrite <- (HRO x Hx). unfold mrd.
    rewrite (MU x (HW x ltac:(pose proof (A3.ro_addr_lo x Hx); lia))). reflexivity. }
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept [(A + 304, A + 312); (fr, fr + 24); (S3, S3 + 68); (S3 + 68, S3 + 255)] mem m1 HAC MU).
    cbn [disjoint_from]. unfold RT_LO, RT_HI. repeat split; lia. }
  eapply (f8_callF HC RNG);
    [lia | lia | lia | exact HIS | exact C4 | exact HAC1 | exact HRO1 | | exact RBYT | exact RIMG | exact RSP
     | exact RSH].
  intros t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2 MU2 WM2 HRO2 HB2.
  apply ExecF.evtF_done. cbv beta. eexists _, _, m2. split; [reflexivity|].
  unfold A3.KA.
  assert (DJ : forall a k, (a + k <= S3 + 68 \/ S3 + 68 + 187 <= a) -> disjoint_from [(S3 + 68, S3 + 68 + 187)] a k).
  { intros a k Hd. cbn [disjoint_from]. split; [exact Hd | exact I]. }
  pose proof (bytes_at_transport rsegs [(S3 + 68, S3 + 68 + 187)] m1 m2) as TR.
  destruct C1 as ((_ & B1) & _). cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1.
  destruct C2 as ((_ & B2) & _). cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2.
  apply (bytes_at_app rsegs) in B2 as [B2a B2r]. rewrite length_le8 in B2r.
  apply (bytes_at_app rsegs) in B2r as [B2b B2c]. rewrite length_le8 in B2c.
  replace (fr + Z.of_nat 8 + Z.of_nat 8) with (fr + 16) in B2c by lia.
  replace (fr + Z.of_nat 8) with (fr + 8) in B2b by lia.
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split.
  { apply (munch_trans _ mem m1 m2); [exact MU|].
    apply (munch_weaken [(S3 + 68, S3 + 68 + 187)] _ m1 m2); [|exact MU2].
    intros x Hx. cbn [outside] in *. destruct Hx as (_ & _ & _ & H4 & _). split; [|exact I].
    intros ?; apply H4; lia. }
  split; [exact (wmono_trans rsegs mem m1 m2 WM WM2)|].
  split; [exact HRO2|].
  split.
  { unfold q64. apply TR; [exact B1 | exact MU2 |].
    apply DJ. rewrite ?length_le8. lia. }
  split.
  { unfold q64. apply TR; [exact B2a | exact MU2 |].
    apply DJ. rewrite ?length_le8. lia. }
  split.
  { unfold q64. apply TR; [exact B2b | exact MU2 |].
    apply DJ. rewrite ?length_le8. lia. }
  split.
  { unfold q64. apply TR; [exact B2c | exact MU2 |].
    apply DJ. rewrite ?length_le8. lia. }
  split.
  { lazymatch type of C3 with rw_cells _ _ _ ?cs =>
      destruct C3 as ((Wf3 & B3) & _);
      assert (L3 : length (cells_bytes cs) = 68%nat)
        by (rewrite (cells_bytes_length cs Wf3); vm_compute; reflexivity);
      exists (cells_bytes cs); split; [|exact L3]
    end.
    apply TR; [exact B3 | exact MU2 | apply DJ; rewrite L3; lia]. }
  split; [exact HB2|].
  repeat (split; [reflexivity|]). reflexivity.
Qed.

(* RECIPE step 1: A3.a3_evt's statement, with the callee's FOOTPRINT contract in the place of the plain one (the
   first premise); every appended rng premise is discharged by ExecF.rng_all, rng_bytes holds of RNG_all, and the
   lib.Lib run is carried back into the UL engine by A3.lib_evt_cut (A3.v:83, an engine bridge, not a run). *)
Lemma a3_evt_of_F : SSHF.asan_set_shadow_f8_contract_F ->
  forall (regs : bvmap 5 word) (mem : word -> option byte) (A fr S3 : Z) j1 j2 j3 j4,
  getr regs 9 = Z_to_bv 64 A -> getr regs 22 = Z_to_bv 64 fr -> getr regs 26 = Z_to_bv 64 ASAN_K ->
  US.rw_cells rsegs mem (A + 304) [UCl.CB 8 j1] -> US.rw_cells rsegs mem fr [UCl.CB 24 j2] ->
  US.rw_cells rsegs mem S3 [UCl.CB 68 j3] -> US.rw_cells rsegs mem (S3 + 68) [UCl.CB 187 j4] ->
  fr + 24 <= A + 304 -> S3 + 255 <= A + 304 -> (fr + 24 <= S3 \/ S3 + 255 <= fr) ->
  0x5fe000 <= fr -> 0x5fe000 <= S3 -> S3 + 255 < 2 ^ 64 -> fr < 2 ^ 64 -> S3 = fr / 8 + ASAN_K ->
  (forall i, 0 <= i < 187 -> in_shadow (S3 + 68 + i)) ->
  asan_cells mem -> ro_agree rsegs mem ->
  UE.evt rsegs (fun ms => exists R pc' mem',
       ms = OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS R fp_regs pc' fp_csr None mem'
         (seg_rom rsegs) /\
                   A3.KA regs mem A fr S3 R pc' mem')
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.MS (Regs6ss.mkR_of regs) fp_regs
       (Z_to_bv 64 0x80f88) fp_csr None mem (seg_rom rsegs)).
Proof.
  intros HC regs mem A fr S3 j1 j2 j3 j4 H9 H22 H26 C1 C2 C3 C4 D1 D2 D3 G1 G2 G3 Hfr HS3 HIS HAC HRO.
  pose proof (bv_unsigned_in_range 64 (reg_get regs 2)) as Rsp.
  unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  (* Every region is bounded by the source's OWN cell premises (rw_cells carries 0 <= A and A + size <= 2^64),
     so no _of_F_bounded form is needed and no premise is added. *)
  pose proof (rw_cells_bound rsegs mem (A + 304) _ (CBr.rw_cells_ul_lib rsegs mem (A + 304) _ C1)) as HB1.
  pose proof (rw_cells_bound rsegs mem fr _ (CBr.rw_cells_ul_lib rsegs mem fr _ C2)) as HB2.
  pose proof (rw_cells_bound rsegs mem S3 _ (CBr.rw_cells_ul_lib rsegs mem S3 _ C3)) as HB3.
  pose proof (rw_cells_bound rsegs mem (S3 + 68) _ (CBr.rw_cells_ul_lib rsegs mem (S3 + 68) _ C4)) as HB4.
  cbn [map CBr.ul_cell_lib cells_size csize Nat.add] in HB1, HB2, HB3, HB4.
  apply evt_lib_ul. eapply ExecF.evtF_evt. eapply (a3_evt_F HC ExecF.RNG_all); try eassumption.
  - (* rng_bytes: RNG_all admits every access *) intros ? ? _ _ _. exact I.
  - (* [A + 304, A + 312) *) apply ExecF.rng_all; lia.
  - (* [fr, fr + 24) *) apply ExecF.rng_all; lia.
  - (* [S3, S3 + 68) *) apply ExecF.rng_all; lia.
  - (* [S3 + 68, S3 + 255) *) apply ExecF.rng_all; lia.
  - (* the image *) apply ExecF.rng_all; cbv [IMGB.IMG_LO IMGB.IMG_HI]; lia.
  - (* the callee's empty stack window *) apply ExecF.rng_all; unfold SSHF.ASAN_SET_SHADOW_K; lia.
Qed.

(* The pin: a3_evt_of_F differs from A3.a3_evt only in the first premise, which names the _F contract in place of
   the plain one; both are checked by name, the rest term for term, with fx opaque. *)
Example a3_evt_of_F_verbatim : True.
Proof.
  lazymatch type of (@A3.a3_evt fx) with ?P -> ?A =>
  lazymatch type of a3_evt_of_F with ?Q -> ?B =>
    constr_eq P SSC.asan_set_shadow_f8_contract;
    constr_eq Q SSHF.asan_set_shadow_f8_contract_F;
    constr_eq A B
  end end.
  exact I.
Qed.

End RunF.
