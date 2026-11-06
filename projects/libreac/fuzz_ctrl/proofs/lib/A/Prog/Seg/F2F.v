(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2065 of its 2181 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3.v, with its module paths and module names changed; 1051 of its 1229 lines of code are new or changed and 2003 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F2.v; 339 of its 505 lines of code are new or changed and 1063 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F2.v 26e353ed3a9f (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F2.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F2.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twins of Seg/F2.v's two evt run lemmas (segment F2 = 0x81da4-0x81dcc, the call of
   checked_memcpy at 0x81dcc):
   - f2_evt_F: F2.f2_evt (:290), the len > 0 run, as an ExecF.evtF under a footprint RNG. The segment's own
     data accesses are the two spill stores `sd s4,216(s1)` and `sd s6,232(s1)`, which the lemma's own
     premises `rw_cells rsegs m (A + 216) [CB 8 j1]` / `rw_cells rsegs m (A + 232) [CB 8 j2]` name as
     [A + 216, A + 224) and [A + 232, A + 240): two rng premises. The callee enters through its footprint
     contract asan_memcpy_contract_F (lib/A/Prog/asan_memcpy_cF.v, proved by asan_memcpyF.v
     asan_memcpy_holds_F) in the place of F2.f2_evt's plain asan_memcpy_contract premise; the callee's own
     footprint premises are that contract's, passed through unchanged (rng_bytes, the image range
     [IMG_LO, IMG_HI), the callee window [sp - ASAN_MEMCPY_K, sp), the destination Phi and the source S, and
     the 8-aligned shadow word spans of those two buffers and of the callee window).
   - f2z_evt_F: F2.f2z_evt (:415), the len = 0 run, which makes no call: its only accesses are the same two
     spill stores, so it carries those two rng premises and no callee premise.
   F2.f2_run (:458) is NOT re-run: it concludes SR, not evt, so it is out of the spec's scope (a Theorem Labs lane,
   2026-10-28); it stays plain and the ported walk reaches it through the twins above.
   F2.v itself is unchanged apart from comment text.
   rule 24: no function proved (a mechanical re-run of two already-proved segment runs). *)
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
(* route (C) (f2_evt_F_on / f2_evt_of_F_on): the copy's region-restricted contracts and proof (a Theorem Labs lane 83ab88c3325,
   taken by path) and the form (lib/A/ShadowRwOn.v, ShadowRwOnK.v; a Theorem Labs lane 9ec78006def) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_c_on asan_memcpy_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_memcpyF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_identity_fragment_c asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 F1.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F2.
(* as in F2.v, so that munch / wmono / outside / bytes_at are lib/Lib's, the ones the callee contract speaks about *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
(* Last: StepF's step / if_true_by (evtF goals) shadow Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
(* fully qualified: StepF's require-closure loads lib/Reusable/YK11.v too, and a bare `Import YK11` would take
   that one, whose seg_rom is a second constant (F2.v's statements name lib/A/Reusable/YK11's). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* the step tactics leave the compare of 0x81db0 in lib/Lib's PropExec, which a later import shadows *)
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.

(* The spill addresses reach solve_accs as bv_unsigned (Z_to_bv 64 A) + 216 / + 232, which its syntactic
   matching does not relate to the premises [ExecF.rng RNG (A + 216) 8] / [ExecF.rng RNG (A + 232) 8]; close
   such a goal from any rng hypothesis after normalizing bv_unsigned (Z_to_bv 64 _). (The v1.8 Seg/R8F.v's
   r8_accF, unchanged.) *)
Ltac f2_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?x, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      match goal with
      | H : rng RNG ?lo ?len |- _ =>
          apply (rng_acc_varZ RNG lo len x n nz H (@eq_refl Z nz));
          cbv [wa]; rewrite ?LM.unsigned_lit_wrap; Z.div_mod_to_equations; lia
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= f2_accF.

(* ---- the len > 0 run 0x81da4 -> 0x81dcc (the call) -> 0x81dd0 under a footprint RNG ---- *)
Lemma f2_evt_F : forall (RNG : ExecF.footprint),
  asan_memcpy_contract_F ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A phi S N lo : Z) (src junk j1 j2 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N -> s4 = Z_to_bv 64 S ->
    0 < phi -> 0 < N -> 0 <= S -> N <= 2 ^ 40 -> RT_HI <= phi ->
    phi + N <= lo -> S + N <= lo -> (S + N <= phi \/ phi + N <= S) ->
    HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= spv -> spv <= A -> A + 416 <= APPMEM_END ->
    spv <= APPMEM_END -> spv mod 16 = 0 ->
    bytes_at rsegs m S src -> length src = Z.to_nat N ->
    rw_cells rsegs m phi [CB (Z.to_nat N) junk] ->
    rw_cells rsegs m (A + 216) [CB 8 j1] -> rw_cells rsegs m (A + 232) [CB 8 j2] ->
    addressable m S N -> addressable m phi N -> end_in_app S N -> end_in_app phi N ->
    app_mem (S + 7) -> app_mem (phi + 7) ->
    stk rsegs m lo spv -> asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    (* the segment's own accesses: the two spill stores *)
    ExecF.rng RNG (A + 216) 8 ->
    ExecF.rng RNG (A + 232) 8 ->
    (* the callee's regions (asan_memcpy_contract_F's footprint premises), unchanged *)
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
         asan_cells m' /\ shadow_rw m' /\
         bytes_at rsegs m' (A + 216) (le8 (Z_to_bv 64 S)) /\
         bytes_at rsegs m' (A + 232) (le8 (Z_to_bv 64 (b2z (N <? 50)))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da4) fc None m (seg_rom rsegs)).
Proof.
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
  (* the runtime cells, the shadow map and the two addressable ranges move across the two spill stores *)
  pose proof (fl_asan_cells _ m _ HAC MU
                ltac:(intros x Hx; cbn [outside]; repeat split; try exact I; lia)) as HAC1.
  pose proof (fl_shadow_rw _ m _ HSW MU WM
                ltac:(intros x Hx; exact (F2.f2_sh_out _ x HAWW Hx))) as HSW1.
  pose proof (fl_addressable _ m _ S N HAS MU
                ltac:(intros x Hx; exact (F2.f2_sh_out _ x HAWW Hx))) as HAS1.
  pose proof (fl_addressable _ m _ phi N HAD MU
                ltac:(intros x Hx; exact (F2.f2_sh_out _ x HAWW Hx))) as HAD1.
  step. if_false_by (F2.f2_eqb0 N ltac:(lia)).        (* 81dbc beqz s2,81e54 *)
  step. step. step.                                  (* mv a0,s7; mv a1,s4; mv a2,s2 *)
  step.                                              (* 81dcc jal checked_memcpy *)
  unfold asan_memcpy_contract_F in MCPY.
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
    - right. lia.
    - left. lia.
    - left. lia.
    - exact HST.
    - lia.
    - lia.
    - lia.
    - exact HAC1.
    - exact HSW1.
    - assumption.
    - exact Rby.
    - exact Rimg.
    - exact Rstk.
    - exact RngD.
    - exact RngS.
    - exact RngDs.
    - exact RngSs.
    - exact RngKs. }
  intros ms' PO. unfold asan_memcpy_post in PO.
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
  split; [exact SW'|].
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

(* ---- the len = 0 run 0x81da4 -> 0x81e54 under a footprint RNG (no call) ---- *)
Lemma f2z_evt_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A phi S : Z) (j1 j2 : list byte),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 0 -> s4 = Z_to_bv 64 S ->
    0 < phi < 2 ^ 64 -> 0 <= A -> A + 416 <= 2 ^ 64 ->
    rw_cells rsegs m (A + 216) [CB 8 j1] -> rw_cells rsegs m (A + 232) [CB 8 j2] ->
    (* the run's own accesses: the two spill stores *)
    ExecF.rng RNG (A + 216) 8 ->
    ExecF.rng RNG (A + 232) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0) s3 (Z_to_bv 64 S) s5 (Z_to_bv 64 1) (Z_to_bv 64 phi)
                       s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81e54) fc None m' (seg_rom rsegs) /\
         munch [(A + 216, A + 224); (A + 232, A + 240)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 216) (le8 (Z_to_bv 64 S)) /\
         bytes_at rsegs m' (A + 232) (le8 (Z_to_bv 64 1)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da4) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A phi S j1 j2 -> -> -> -> Hph HA0 HA64 HR216 HR232 R216 R232.
  pose proof (munch_refl [(A + 216, A + 224); (A + 232, A + 240)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  step. if_true_by (F2.f2_neqb0 phi ltac:(lia)).
  step.
  lazymatch goal with
  | |- context [LP.v_sltiu (Z_to_bv 64 0) ?i] =>
      rewrite (F2.f2_sltiu 0 i ltac:(lia) ltac:(vm_compute; reflexivity))
  end.
  cbn [Z.ltb Z.compare b2z].
  step.
  step.
  step. if_true.
  apply ExecF.evtF_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact (F2.f2_c_bytes _ _ _ HR216) | exact (F2.f2_c_bytes _ _ _ HR232)].
Qed.

(* ---- the two corollaries at ExecF.RNG_all, each stating its source lemma's text ---- *)

(* F2.f2_evt's statement, term for term: f2_evt_F at ExecF.RNG_all, with the footprint contract discharged by
   a Theorem Labs lane's proof asan_memcpy_holds_F (lib/A/Prog/asan_memcpyF.v), so that the plain asan_memcpy_contract
   premise of F2.f2_evt is kept in its place and used by nothing. *)
Lemma f2_evt_of_F : asan_memcpy_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A phi S N lo : Z) (src junk j1 j2 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N -> s4 = Z_to_bv 64 S ->
    0 < phi -> 0 < N -> 0 <= S -> N <= 2 ^ 40 -> RT_HI <= phi ->
    phi + N <= lo -> S + N <= lo -> (S + N <= phi \/ phi + N <= S) ->
    HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= spv -> spv <= A -> A + 416 <= APPMEM_END ->
    spv <= APPMEM_END -> spv mod 16 = 0 ->
    bytes_at rsegs m S src -> length src = Z.to_nat N ->
    rw_cells rsegs m phi [CB (Z.to_nat N) junk] ->
    rw_cells rsegs m (A + 216) [CB 8 j1] -> rw_cells rsegs m (A + 232) [CB 8 j2] ->
    addressable m S N -> addressable m phi N -> end_in_app S N -> end_in_app phi N ->
    app_mem (S + 7) -> app_mem (phi + 7) ->
    stk rsegs m lo spv -> asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dd0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 phi)
                       a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 N) s3 (Z_to_bv 64 S) s5
                       (Z_to_bv 64 (b2z (N <? 50))) (Z_to_bv 64 phi) s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x81dd0) fc None m' (seg_rom rsegs) /\
         munch [(A + 216, A + 224); (A + 232, A + 240); (phi, phi + N); (spv - ASAN_MEMCPY_K, spv)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo spv /\
         rw_cells rsegs m' phi [CB (Z.to_nat N) src] /\ bytes_at rsegs m' S src /\
         asan_cells m' /\ shadow_rw m' /\
         bytes_at rsegs m' (A + 216) (le8 (Z_to_bv 64 S)) /\
         bytes_at rsegs m' (A + 232) (le8 (Z_to_bv 64 (b2z (N <? 50)))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da4) fc None m (seg_rom rsegs)).
Proof.
  intros _ ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A phi S N lo src junk j1 j2 Esp Es1 Ea0 Es2 Es4 Hph0 HN0 HS0 HN40 HRT Hphlo HSlo Hdj
    Hlo Hlosp HspA HA64 HspE Hal HbS HLs HRWd HR216 HR232 HAS HAD HES HED HAPS HAPD HST HAC HSW HMI.
  pose proof two64 as H64.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f2_evt_F ExecF.RNG_all asan_memcpy_holds_F
           ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m spv A phi S N lo src junk j1 j2 Esp Es1 Ea0 Es2 Es4 Hph0 HN0 HS0 HN40 HRT Hphlo HSlo Hdj
           Hlo Hlosp HspA HA64 HspE Hal HbS HLs HRWd HR216 HR232 HAS HAD HES HED HAPS HAPD HST HAC HSW HMI).
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; cbv [IMG_LO IMG_HI]; lia.
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply sh_word_rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply sh_word_rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply sh_word_rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
Qed.

(* F2.f2z_evt's statement, term for term: f2z_evt_F at ExecF.RNG_all (both rng premises by ExecF.rng_all, from
   the lemma's own 0 <= A and A + 416 <= 2 ^ 64). *)
Lemma f2z_evt_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A phi S : Z) (j1 j2 : list byte),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 0 -> s4 = Z_to_bv 64 S ->
    0 < phi < 2 ^ 64 -> 0 <= A -> A + 416 <= 2 ^ 64 ->
    rw_cells rsegs m (A + 216) [CB 8 j1] -> rw_cells rsegs m (A + 232) [CB 8 j2] ->
    LE.evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0) s3 (Z_to_bv 64 S) s5 (Z_to_bv 64 1) (Z_to_bv 64 phi)
                       s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81e54) fc None m' (seg_rom rsegs) /\
         munch [(A + 216, A + 224); (A + 232, A + 240)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 216) (le8 (Z_to_bv 64 S)) /\
         bytes_at rsegs m' (A + 232) (le8 (Z_to_bv 64 1)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A phi S j1 j2 Es1 Ea0 Es2 Es4 Hph HA0 HA64 HR216 HR232.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f2z_evt_F ExecF.RNG_all
           ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m A phi S j1 j2 Es1 Ea0 Es2 Es4 Hph HA0 HA64 HR216 HR232).
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
Qed.

(* The pins: each *_of_F states F2's v1.9 text, term for term (constr_eq: syntactic, not up to conversion);
   f2_evt_of_F's plain asan_memcpy_contract premise is included. *)
Lemma f2_evt_of_F_verbatim : True.
Proof.
  let A := type of F2.f2_evt in let B := type of f2_evt_of_F in constr_eq A B; exact I.
Qed.

Lemma f2z_evt_of_F_verbatim : True.
Proof.
  let A := type of F2.f2z_evt in let B := type of f2z_evt_of_F in constr_eq A B; exact I.
Qed.

(* ---- Route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery), 10:34Z amendment): ADDITIVE twins
   of f2_evt_F and f2_evt_of_F.  Both old lemmas stay byte-identical with their own proofs (a Theorem Labs lane 09:58Z: a run that
   takes a callee contract keeps X); the twins take the copy's region-restricted contracts. ----
   R (the shadow bytes the run reads or stores through its shadow_rw premise): f2_evt_F reads no shadow byte and
   stores none (its two stores are the spills at A + 216 / A + 232, app memory, `all_app` above); its premise HSW
   has one use, the copy's shadow premise (F2F.v `exact HSW1` in the `eapply MCPY` block), carried across the two
   spills by fl_shadow_rw (here A.ShadowRwOnK.fl_shadow_rw_on). So R is the copy's own region at the call's
   arguments a0 = phi, a1 = S, a2 = N (0x81dc0 mv a0,s7; mv a1,s4; mv a2,s2; s7 = a0, s4, s2 the premises'
   words): asan_memcpy_shadow_R. The post's shadow_rw m' (the copy's post) becomes the forall-P post. *)
Definition f2_evt_F_shadow_R (phi S N : Z) : Z -> Prop :=
  fun a => asan_memcpy_shadow_R (Z_to_bv 64 phi) (Z_to_bv 64 S) (Z_to_bv 64 N) a.

Lemma f2_evt_F_on : forall (RNG : ExecF.footprint),
  asan_memcpy_contract_F_on ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A phi S N lo : Z) (src junk j1 j2 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N -> s4 = Z_to_bv 64 S ->
    0 < phi -> 0 < N -> 0 <= S -> N <= 2 ^ 40 -> RT_HI <= phi ->
    phi + N <= lo -> S + N <= lo -> (S + N <= phi \/ phi + N <= S) ->
    HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= spv -> spv <= A -> A + 416 <= APPMEM_END ->
    spv <= APPMEM_END -> spv mod 16 = 0 ->
    bytes_at rsegs m S src -> length src = Z.to_nat N ->
    rw_cells rsegs m phi [CB (Z.to_nat N) junk] ->
    rw_cells rsegs m (A + 216) [CB 8 j1] -> rw_cells rsegs m (A + 232) [CB 8 j2] ->
    addressable m S N -> addressable m phi N -> end_in_app S N -> end_in_app phi N ->
    app_mem (S + 7) -> app_mem (phi + 7) ->
    stk rsegs m lo spv -> asan_cells m -> A.ShadowRwOn.shadow_rw_on (f2_evt_F_shadow_R phi S N) m -> mem_inv rsegs m ->
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
         asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         bytes_at rsegs m' (A + 216) (le8 (Z_to_bv 64 S)) /\
         bytes_at rsegs m' (A + 232) (le8 (Z_to_bv 64 (b2z (N <? 50)))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da4) fc None m (seg_rom rsegs)).
Proof.
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
  (* the runtime cells, every shadow region and the two addressable ranges move across the two spill stores *)
  pose proof (fl_asan_cells _ m _ HAC MU
                ltac:(intros x Hx; cbn [outside]; repeat split; try exact I; lia)) as HAC1.
  pose proof (fun (P : Z -> Prop) (HP : A.ShadowRwOn.shadow_rw_on P m) =>
                A.ShadowRwOnK.fl_shadow_rw_on P _ m _ HP MU WM (fun x Hx => F2.f2_sh_out _ x HAWW Hx)) as HSWk.
  pose proof (HSWk _ HSW) as HSW1.
  pose proof (fl_addressable _ m _ S N HAS MU
                ltac:(intros x Hx; exact (F2.f2_sh_out _ x HAWW Hx))) as HAS1.
  pose proof (fl_addressable _ m _ phi N HAD MU
                ltac:(intros x Hx; exact (F2.f2_sh_out _ x HAWW Hx))) as HAD1.
  step. if_false_by (F2.f2_eqb0 N ltac:(lia)).        (* 81dbc beqz s2,81e54 *)
  step. step. step.                                  (* mv a0,s7; mv a1,s4; mv a2,s2 *)
  step.                                              (* 81dcc jal checked_memcpy *)
  unfold asan_memcpy_contract_F_on in MCPY.
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
    - right. lia.
    - left. lia.
    - left. lia.
    - exact HST.
    - lia.
    - lia.
    - lia.
    - exact HAC1.
    - (* the copy's region at the call's arguments is f2_evt_F_shadow_R phi S N *)
      exact HSW1.
    - assumption.
    - exact Rby.
    - exact Rimg.
    - exact Rstk.
    - exact RngD.
    - exact RngS.
    - exact RngDs.
    - exact RngSs.
    - exact RngKs. }
  intros ms' PO. unfold asan_memcpy_post_on in PO.
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
  (* every region: across the spills (HSWk), then the copy's post *)
  split; [intros P HP; exact (SW' P (HSWk P HP))|].
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

(* The plain twin of f2_evt_of_F: f2_evt_F_on at ExecF.RNG_all, the footprint contract discharged by a Theorem Labs lane's
   asan_memcpy_holds_F_on (lib/A/Prog/asan_memcpyF_on.v). As f2_evt_of_F keeps the plain asan_memcpy_contract in
   its place, this keeps the plain region contract asan_memcpy_contract_on in its place, used by nothing. R: the
   same region as f2_evt_F_on's. No pin (no new constr_eq pin against a plain X_on). *)
Lemma f2_evt_of_F_on : asan_memcpy_contract_on ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A phi S N lo : Z) (src junk j1 j2 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N -> s4 = Z_to_bv 64 S ->
    0 < phi -> 0 < N -> 0 <= S -> N <= 2 ^ 40 -> RT_HI <= phi ->
    phi + N <= lo -> S + N <= lo -> (S + N <= phi \/ phi + N <= S) ->
    HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= spv -> spv <= A -> A + 416 <= APPMEM_END ->
    spv <= APPMEM_END -> spv mod 16 = 0 ->
    bytes_at rsegs m S src -> length src = Z.to_nat N ->
    rw_cells rsegs m phi [CB (Z.to_nat N) junk] ->
    rw_cells rsegs m (A + 216) [CB 8 j1] -> rw_cells rsegs m (A + 232) [CB 8 j2] ->
    addressable m S N -> addressable m phi N -> end_in_app S N -> end_in_app phi N ->
    app_mem (S + 7) -> app_mem (phi + 7) ->
    stk rsegs m lo spv -> asan_cells m -> A.ShadowRwOn.shadow_rw_on (f2_evt_F_shadow_R phi S N) m -> mem_inv rsegs m ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dd0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 phi)
                       a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 N) s3 (Z_to_bv 64 S) s5
                       (Z_to_bv 64 (b2z (N <? 50))) (Z_to_bv 64 phi) s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x81dd0) fc None m' (seg_rom rsegs) /\
         munch [(A + 216, A + 224); (A + 232, A + 240); (phi, phi + N); (spv - ASAN_MEMCPY_K, spv)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo spv /\
         rw_cells rsegs m' phi [CB (Z.to_nat N) src] /\ bytes_at rsegs m' S src /\
         asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\
         bytes_at rsegs m' (A + 216) (le8 (Z_to_bv 64 S)) /\
         bytes_at rsegs m' (A + 232) (le8 (Z_to_bv 64 (b2z (N <? 50)))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da4) fc None m (seg_rom rsegs)).
Proof.
  intros _ ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A phi S N lo src junk j1 j2 Esp Es1 Ea0 Es2 Es4 Hph0 HN0 HS0 HN40 HRT Hphlo HSlo Hdj
    Hlo Hlosp HspA HA64 HspE Hal HbS HLs HRWd HR216 HR232 HAS HAD HES HED HAPS HAPD HST HAC HSW HMI.
  pose proof two64 as H64.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f2_evt_F_on ExecF.RNG_all asan_memcpyF_on.asan_memcpy_holds_F_on
           ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m spv A phi S N lo src junk j1 j2 Esp Es1 Ea0 Es2 Es4 Hph0 HN0 HS0 HN40 HRT Hphlo HSlo Hdj
           Hlo Hlosp HspA HA64 HspE Hal HbS HLs HRWd HR216 HR232 HAS HAD HES HED HAPS HAPD HST HAC HSW HMI).
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - intros b j _ _ _. exact I.
  - apply ExecF.rng_all; cbv [IMG_LO IMG_HI]; lia.
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply ExecF.rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply sh_word_rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply sh_word_rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
  - apply sh_word_rng_all; unfold HIGHMEM_BEG, APPMEM_END, ASAN_MEMCPY_K in *; lia.
Qed.
