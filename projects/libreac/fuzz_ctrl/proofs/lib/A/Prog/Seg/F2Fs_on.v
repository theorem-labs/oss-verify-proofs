(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2065 of its 2181 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3.v, with its module paths and module names changed; 1051 of its 1229 lines of code are new or changed and 2003 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F2.v; 74 of its 187 lines of code are new or changed and 1116 lines of the source are left out. *)
(* lib/A/Prog/Seg/F2Fs_on.v -- route (C) twin of F2Fs.f2_evt_Fs (the len > 0 stretch of segment F2 of fuzz_ctrl
   image A's LLVMFuzzerTestOneInput, libreac v1.9.0, 0x81da4 -> the checked memcpy at 0x81dcc -> 0x81dd0).  Written by
   a Theorem Labs lane (GO from a Theorem Labs lane 12:5xZ, F2Fs.v (not in this delivery) being a Theorem Labs lane's own file), in a NEW file: Seg/F2Fs.v
   and a Theorem Labs lane's Seg/F2F.v stay byte-identical in their proof text (this delivery's comment passes aside).  rule 24: no function proved (a re-proof of an already-proved run
   with the route (C) shadow premise and post).

   WHY.  Route (C) (a Theorem Labs lane DECISION 09:20Z): the walk's cut carries A.ACtlRtC.ctl_rt_C, the shadow of the cut's own
   state and of the image only, not the universal AsanRT.shadow_rw.  f2_evt_Fs takes `shadow_rw m`, which the glue
   (lib/A/ACtlG/F2.v) can no longer give.  Its callee has a route (C) form: a Theorem Labs lane's asan_memcpy_contract_F_on
   (asan_memcpy_cF_on.v, 83ab88c3325, signed a Theorem Labs lane 11:16Z), proved by asan_memcpyF_on.asan_memcpy_holds_F_on.

   WHAT CHANGED against F2Fs.f2_evt_Fs (statement and proof otherwise verbatim):
   - the callee premise asan_memcpy_contract_F -> asan_memcpy_contract_F_on;
   - the premise `shadow_rw m` -> `shadow_rw_on (f2_evt_Fs_shadow_R phi S N) m`, R = the callee's own region
     asan_memcpy_shadow_R at the call's a0 = phi, a1 = S, a2 = N: the contiguous aligned shadow-word spans of the
     source [S, S + N) and of the destination [phi, phi + N) (sh_word_on.v).  The stretch's own steps (mv, bnez,
     sltiu, two sd into the spill words [A + 216, A + 224) / [A + 232, A + 240), beqz, three mv, jal) read and write
     no shadow byte, so R is exactly the callee's;
   - the post's `shadow_rw m'` -> `forall P, shadow_rw_on P m -> shadow_rw_on P m'` (the wave's post form): across
     the two spill stores by ShadowRwOnK.fl_shadow_rw_on (the stores miss the shadow, F2.f2_sh_out), across the call
     by the callee post's own forall-P conjunct.
   Proof steps changed: the two fl_shadow_rw uses become fl_shadow_rw_on; the callee's shadow premise is closed by
   shadow_rw_on_mono (R is the callee's R at the literal register words); the post's shadow conjunct as above.
   Names: F2Fs.v's two family-ambiguous proof uses (MState.unsigned_lit, Cells.cbytes) are written in full path to
   the copy they bind (A.Tk.UL.MState / A.Tk.UL.Cells, by Locate in this file's context, the same binding as in
   F2Fs.v's context; F2Fs.v is not in this delivery), as a Theorem Labs lane's fold 4bae33fdf54 does in F2F.v (a Theorem Labs lane 08:56Z copy-per-occurrence rule). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_c reac_ctrl_parse_c reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_cF asan_memcpyF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_identity_fragment_c asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 F1.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F2.
(* a Theorem Labs lane's footprint twins, Required (not Imported): the spill-access hint names them qualified. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F2F.
(* route (C): the region form, its munch transport, the callee's _on contract (all Required, used qualified) *)
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnK.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c_on.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_cF_on.
(* as in F2F.v (and F2.v), so that munch / wmono / outside / bytes_at are lib/Lib's, the ones the callee contract
   speaks about *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
(* Last: StepF's step / if_true_by (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
(* fully qualified, as F2F.v:50: StepF's require-closure loads lib/Reusable/YK11.v too, and a bare `Import YK11`
   would take that one, whose seg_rom is a second constant (F2F.v's statements name lib/A/Reusable/YK11's). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

(* F2F.v:57-58's aliases, the two the proof uses, and the route (C) modules *)
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SRK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnK.
Module SWO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.sh_word_on.
Module MCO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_c_on.
Module MCFO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_memcpy_cF_on.

(* F2F.v:74's hint (a Local redefinition there, so not exported by its Require): the two spill stores' accesses
   from their rng premises, by F2F.v's own f2_accF. *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= F2F.f2_accF.

(* The stretch's shadow region: the callee's asan_memcpy_shadow_R at a0 = phi, a1 = S, a2 = N (source span, then
   destination span). *)
Definition f2_evt_Fs_shadow_R (phi S N : Z) (a : Z) : Prop :=
  SWO.sh_word_on S N a \/ SWO.sh_word_on phi N a.

(* ---- the len > 0 run 0x81da4 -> 0x81dcc (the call) -> 0x81dd0 under a footprint RNG, route (C) ---- *)
Lemma f2_evt_Fs_on : forall (RNG : ExecF.footprint),
  MCFO.asan_memcpy_contract_F_on ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A phi S N lo : Z) (src junk j1 j2 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N -> s4 = Z_to_bv 64 S ->
    0 < phi -> 0 < N -> 0 <= S -> N <= 2 ^ 40 -> (phi + N <= RT_LO \/ RT_HI <= phi) ->
    phi + N <= lo -> S + N <= lo -> (S + N <= phi \/ phi + N <= S) ->
    HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= spv -> spv <= A -> A + 416 <= APPMEM_END ->
    spv <= APPMEM_END -> spv mod 16 = 0 ->
    bytes_at rsegs m S src -> length src = Z.to_nat N ->
    rw_cells rsegs m phi [CB (Z.to_nat N) junk] ->
    rw_cells rsegs m (A + 216) [CB 8 j1] -> rw_cells rsegs m (A + 232) [CB 8 j2] ->
    addressable m S N -> addressable m phi N -> end_in_app S N -> end_in_app phi N ->
    app_mem (S + 7) -> app_mem (phi + 7) ->
    stk rsegs m lo spv -> asan_cells m -> SRO.shadow_rw_on (f2_evt_Fs_shadow_R phi S N) m -> mem_inv rsegs m ->
    (* the segment's own accesses: the two spill stores *)
    ExecF.rng RNG (A + 216) 8 ->
    ExecF.rng RNG (A + 232) 8 ->
    (* the callee's regions (asan_memcpy_contract_F_on's footprint premises), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO (IMG_HI - IMG_LO) ->
    ExecF.rng RNG (spv - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    ExecF.rng RNG phi N -> ExecF.rng RNG S N ->
    sh_word_rng RNG phi N -> sh_word_rng RNG S N ->
    sh_word_rng RNG (spv - ASAN_MEMCPY_K) ASAN_MEMCPY_K ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dd0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 phi)
                       a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 N) s3 (Z_to_bv 64 S) s5
                       (Z_to_bv 64 (b2z (N <? 50))) (Z_to_bv 64 phi) s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x81dd0) fc None m' (seg_rom rsegs) /\
         munch [(A + 216, A + 224); (A + 232, A + 240); (phi, phi + N); (spv - ASAN_MEMCPY_K, spv)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo spv /\
         rw_cells rsegs m' phi [CB (Z.to_nat N) src] /\ bytes_at rsegs m' S src /\
         asan_cells m' /\ (forall P : Z -> Prop, SRO.shadow_rw_on P m -> SRO.shadow_rw_on P m') /\
         bytes_at rsegs m' (A + 216) (le8 (Z_to_bv 64 S)) /\
         bytes_at rsegs m' (A + 232) (le8 (Z_to_bv 64 (b2z (N <? 50)))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da4) fc None m (seg_rom rsegs)).
Proof.
  (* F2Fs.v:117-218, verbatim except the route (C) steps (marked) *)
  intros RNG MCPY ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A phi S N lo src junk j1 j2 -> -> -> -> -> Hph0 HN0 HS0 HN40 HRT Hphlo HSlo Hdj
    Hlo Hlosp HspA HA64 HspE Hal HbS HLs HRWd HR216 HR232 HAS HAD HES HED HAPS HAPD HST HAC HSW HMI
    R216 R232 Rby Rimg Rstk RngD RngS RngDs RngSs RngKs.
  assert (HK : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HRTH : RT_HI = 0xa9578) by reflexivity.
  assert (HAWW : all_app [(A + 216, A + 224); (A + 232, A + 240); (phi, phi + N);
                          (spv - ASAN_MEMCPY_K, spv)]).
  { cbn [all_app app_ivl]. split; [|split; [|split; [|split; [|exact I]]]].
    - intros x Hx. unfold app_mem. right. lia.
    - intros x Hx. unfold app_mem. right. lia.
    - intros x Hx. destruct HAD as (_ & _ & _ & HAb). destruct (HAb (x - phi) ltac:(lia)) as (Hap & _).
      replace (phi + (x - phi)) with x in Hap by lia. exact Hap.
    - intros x Hx. unfold app_mem. right. lia. }
  pose proof (munch_refl [(A + 216, A + 224); (A + 232, A + 240); (phi, phi + N); (spv - ASAN_MEMCPY_K, spv)] m)
    as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.                                              (* 81da4 mv s7,a0 *)
  step. if_true_by (F2.f2_neqb0 phi ltac:(lia)).      (* 81da8 bnez a0,81db0 *)
  step.                                              (* 81db0 sltiu s6,s2,50 *)
  lazymatch goal with
  | |- context [LP.v_sltiu (Z_to_bv 64 N) ?i] =>
      rewrite (F2.f2_sltiu N i ltac:(lia) ltac:(vm_compute; reflexivity))
  end.
  step.                                              (* 81db4 sd s4,216(s1) *)
  step.                                              (* 81db8 sd s6,232(s1) *)
  (* the runtime cells, the shadow region and the two addressable ranges move across the two spill stores *)
  pose proof (fl_asan_cells _ m _ HAC MU
                ltac:(intros x Hx; cbn [outside]; repeat split; try exact I; lia)) as HAC1.
  (* ROUTE (C): fl_shadow_rw -> ShadowRwOnK.fl_shadow_rw_on on the region *)
  pose proof (SRK.fl_shadow_rw_on _ _ m _ HSW MU WM
                ltac:(intros x Hx; exact (F2.f2_sh_out _ x HAWW Hx))) as HSW1.
  pose proof (fl_addressable _ m _ S N HAS MU
                ltac:(intros x Hx; exact (F2.f2_sh_out _ x HAWW Hx))) as HAS1.
  pose proof (fl_addressable _ m _ phi N HAD MU
                ltac:(intros x Hx; exact (F2.f2_sh_out _ x HAWW Hx))) as HAD1.
  step. if_false_by (F2.f2_eqb0 N ltac:(lia)).        (* 81dbc beqz s2,81e54 *)
  step. step. step.                                  (* mv a0,s7; mv a1,s4; mv a2,s2 *)
  step.                                              (* 81dcc jal checked_memcpy *)
  unfold MCFO.asan_memcpy_contract_F_on in MCPY.
  eapply ExecF.evtF_cut.
  { eapply MCPY with (RNG := RNG) (src := src) (junk := junk) (lo := lo);
      rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia.
    - exact HbS.
    - exact HLs.
    - exact HRWd.
    - destruct Hdj as [Hd|Hd]; [right; left; lia | right; right; lia].
    - lia.
    - exact HAS1.
    - exact HAD1.
    - exact HES.
    - exact HED.
    - right. split; [exact HAPS | exact HAPD].
    - (* F2Fs.v's one changed step: the contract's (D + N <= RT_LO \/ RT_HI <= D) by a case split *)
      destruct HRT as [HRT | HRT]; [left | right]; lia.
    - left. lia.
    - left. lia.
    - exact HST.
    - lia.
    - lia.
    - lia.
    - exact HAC1.
    - (* ROUTE (C): the callee's region is this stretch's R at the literal register words *)
      apply (SRO.shadow_rw_on_mono (f2_evt_Fs_shadow_R phi S N)); [|exact HSW1].
      intros x Hx. unfold MCO.asan_memcpy_shadow_R in Hx.
      rewrite ?OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit in Hx by lia.
      exact Hx.
    - assumption.
    - exact Rby.
    - exact Rimg.
    - exact Rstk.
    - exact RngD.
    - exact RngS.
    - exact RngDs.
    - exact RngSs.
    - exact RngKs. }
  intros ms' PO. unfold MCO.asan_memcpy_post_on in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MUc & WMc & MI' & STc & RWc & HBc & AC' & SW').
  subst ms'.
  assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply LM.unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply LM.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply LM.unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply LM.unsigned_lit; lia).
  rewrite Ephi in MUc, RWc. rewrite EN in MUc, RWc. rewrite Esp in MUc, STc. rewrite ES in HBc.
  rewrite (LM.ret_pc_even 0x81dd0) by (first [reflexivity | lia]).
  apply ExecF.evtF_done. do 15 eexists. split; [reflexivity|].
  split.
  { apply (munch_trans _ m _ m' MU). eapply munch_weaken; [|exact MUc].
    intros x (O1 & O2 & O3 & O4 & _). cbn [outside].
    split; [exact O3|]. split; [exact O4 | exact I]. }
  split; [exact (wmono_trans rsegs _ _ m' WM WMc)|].
  split; [exact STc|].
  split; [exact RWc|].
  split; [exact HBc|].
  split; [exact AC'|].
  split.
  { (* ROUTE (C): any region the caller holds at m, across the two stores (they miss the shadow), then the call *)
    intros P HP. apply SW'.
    exact (SRK.fl_shadow_rw_on P _ m _ HP MU WM (fun x Hx => F2.f2_sh_out _ x HAWW Hx)). }
  split.
  { apply (bytes_at_transport rsegs _ _ m' _ _ (F2.f2_c_bytes _ _ _ HR216) MUc).
    cbn [disjoint_from OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Cells.cbytes]. rewrite ?length_le8.
      cbn [length].
    repeat split; try exact I; lia. }
  { apply (bytes_at_transport rsegs _ _ m' _ _ (F2.f2_c_bytes _ _ _ HR232) MUc).
    cbn [disjoint_from OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Cells.cbytes]. rewrite ?length_le8.
      cbn [length].
    repeat split; try exact I; lia. }
Qed.
