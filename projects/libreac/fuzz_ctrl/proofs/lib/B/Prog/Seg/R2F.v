(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 741 of its 860 lines of code are new or changed and 892 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R2.v; 114 of its 170 lines of code are new or changed and 804 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/R2.v r2_evt :199.  R2.v is not in a working branch 3803efccea0: it
     is a Theorem Labs lane's WIP d574f6c66de (blob c8e8264e8e3a1815df751c41d25dd3dff05bb6e7), taken by path onto
     3803efccea0 on a working branch f9a9f80d79e (unchanged, same blob) and built there (-s ours
     type-check rc=0);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
     lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: r2_evt calls meta_fill_00 (__asan_set_shadow_00) at 0x8163c, so it is split there: r2_evt_pre_F
     re-runs R2.v lines 224-249 (0x815fc .. the jal, stopping AT the callee entry SSH.ASAN_SET_SHADOW_00 with
     ra = 0x81640), r2_evt_post_F lines 256-275 (from the return pc 0x81640; the run ends there, so it has no
     instruction); r2_evt_of_F re-derives the source statement from the pair and the __asan_set_shadow_00
     contract taken at the call (checked by conversion against R2.r2_evt, r2_evt_src_check).
   R2.v's other lemma named in the inventory, r2_run :415, is not a run: it has no instruction and no Exec.evt
     conclusion (it lifts an evt on MemNorm.normalize to SR through evt_normalize and evt_SR_canon_lazy), so it has
     no footprint twin here; the evtF form of evt_normalize is not in 3803efccea0's kit.
   No _F steps through a callee.  This file states no callee contract. *)
(* rule 24: no function proved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem Instr.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require YK14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_set_shadow_c SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require R2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

Module SSH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_set_shadow_c.
Module Y14 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK14.

(* R2.v's r2_s2 without its first step (the register read off the final mkR): normalize the remu / srli values
   of the row register s2 after 0x8162c `add s2,a0,a1`. *)
Ltac r2F_s2 :=
  rewrite ?Y14.m_remu by (rewrite MState.unsigned_lit by lia; lia);
  rewrite ?Y14.v_remu_small by (rewrite MState.unsigned_lit by lia; lia);
  rewrite ?(MState.unsigned_lit 11) by lia;
  rewrite ?R2.r2_srl1;
  f_equal; lia.

(* ---- r2_evt (R2.v:199-276), split at the call 0x8163c jal meta_fill_00.
   _pre_F: 0x815fc bnez a0 (taken), 0x81604 ld a1,0(s4) (= 11), 0x81608 bnez a1 (taken), the row offset arithmetic
   0x81610 .. 0x81620, the UBSan wrap test 0x81624 (T04, taken), 0x8162c add s2, 0x81630 li a1,186,
   0x81634 sd s11,8(s1), 0x81638 mv a0,s11, 0x8163c jal, stopping AT the callee entry SSH.ASAN_SET_SHADOW_00 with
   ra = 0x81640, a0 = s11 = Q, a1 = 186.  Accesses: the catalogue count [c, c + 8) and the spill [Ab + 8, Ab + 16).
   Its post is the state at the jal target with the facts the source run has there (R2.v:244-249: the write set and
   wmono from m, the 186 shadow bytes still one cell, the spill window's stk, [Ab + 8] = s11, asan_cells, and
   mem_inv carried by the stores) and uses at the call or after it. ---- *)
Lemma r2_evt_pre_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab c Q : Z) (junk jsp : list byte),
    a0 = Z_to_bv 64 SlotModel.CAT -> s1 = Z_to_bv 64 Ab -> s4 = Z_to_bv 64 c -> s11 = Z_to_bv 64 Q ->
    RT_HI <= Q -> Q + 186 <= Ab + 8 -> Ab + 16 <= 2 ^ 64 ->
    ro_cells rsegs m c [C8 (Z_to_bv 64 11)] ->
    (forall i, 0 <= i < 186 -> in_shadow (Q + i)) ->
    rw_cells rsegs m Q [CB 186 junk] ->
    rw_cells rsegs m (Ab + 8) [CB 8 jsp] -> stk rsegs m (Ab + 8) (Ab + 16) ->
    asan_cells m -> mem_inv rsegs m ->
    rng RNG c 8 -> rng RNG (Ab + 8) 8 ->
    evtF rsegs RNG
      (fun ms' => exists (a2' s2' : word) (m1 : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81640) sp gp tp t0 t1 t2 s0 s1 s11 (Z_to_bv 64 186) a2' a3 a4 a5 a6 a7
                       s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 SSH.ASAN_SET_SHADOW_00) fc None m1 (seg_rom rsegs) /\
         s2' = Z_to_bv 64 (SlotModel.CAT + 296 * ((bv_unsigned s6 / 2) mod 11)) /\
         munch [(Q, Q + 186); (Ab + 8, Ab + 16)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 Q [CB 186 junk] /\ stk rsegs m1 (Ab + 8) (Ab + 16) /\
         bytes_at rsegs m1 (Ab + 8) (le8 s11) /\ asan_cells m1 /\ mem_inv rsegs m1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815fc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab c Q junk jsp -> -> -> -> HQrt HQA HA64 RC HQsh CHQ CHS STS HAC HMI Rc R8.
  (* the run computes with the catalogue address's value (a0 = CAT, the reac_box_catalogue result) *)
  unfold SlotModel.CAT.
  pose proof (rw_cells_bound rsegs m Q _ CHQ) as HQb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HQb.
  unfold RT_HI in HQrt.
  pose proof (munch_refl [(Q, Q + 186); (Ab + 8, Ab + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 0x815fc bnez a0 (a0 = BOX_CATALOGUE <> 0) *)
  step. if_true.
  (* 0x81604 ld a1,0(s4) = 11; 0x81608 bnez a1 (taken: 0x81610) *)
  step. step. if_true.
  (* 0x81610 srli; 0x81614 remu; 0x81618 li a2,296; 0x8161c mul; 0x81620 not a2,a0; 0x81624 bgeu a2,a1 (T04) *)
  step. step. step. step. step. step.
  lazymatch goal with
  | |- context [Sem.mul_div Instr.M_REMU ?x (Z_to_bv 64 11)] =>
      rewrite (R2.r2_wrap _ x) by (unfold SlotModel.CAT; reflexivity)
  end.
  cbv iota.
  (* 0x8162c add s2,a0,a1; 0x81630 li a1,186; 0x81634 sd s11,8(s1); 0x81638 mv a0,s11; 0x8163c jal meta_fill_00:
     stop at its entry *)
  step. step. step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  (* the spill word [A + 8] = s11 the store left in the spill cell *)
  pose proof (proj2 (proj1 CHS)) as B11. cbn [cells_bytes cbytes] in B11. rewrite ?app_nil_r in B11.
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  apply evtF_done. do 3 eexists.
  split; [reflexivity|].
  split; [r2F_s2|].
  split; [exact MU|]. split; [exact WM|]. split; [exact CHQ|]. split; [exact STS|].
  split; [exact B11|]. split; [exact HAC1 | exact HMI].
Qed.

(* _post_F: from the return pc 0x81640, with the __asan_set_shadow_00 post facts as R2.v:256-260 uses them (a0 kept
   = s11, the write set [(Q, Q + 186)], wmono, the 186 bytes now 00) over the post-call state m2, and the pre-call
   facts on m1 the source run carries across the call (the write set and wmono from m, the spill window's stk,
   [Ab + 8] = s11).  s2 is callee-saved, so it still holds the row address.  The run ends at 0x81640: no
   instruction, no access. *)
Lemma r2_evt_post_F :
  forall (RNG : footprint)
         (sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6' : word)
         (F : bvmap 5 word) (fc : bv 32) (m m1 m2 : word -> option byte) (Ab Q : Z),
    s11 = Z_to_bv 64 Q ->
    RT_HI <= Q -> Q + 186 <= Ab + 8 -> Ab + 16 <= 2 ^ 64 ->
    munch [(Q, Q + 186); (Ab + 8, Ab + 16)] m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 (Ab + 8) (Ab + 16) -> bytes_at rsegs m1 (Ab + 8) (le8 s11) ->
    munch [(Q, Q + 186)] m1 m2 -> wmono rsegs m1 m2 ->
    rw_cells rsegs m2 Q [CB 186 (repeat (Z_to_bv 8 0) 186)] ->
    evtF rsegs RNG
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81640) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 18 = Z_to_bv 64 (SlotModel.CAT + 296 * ((bv_unsigned s6 / 2) mod 11)) /\
         munch [(Q, Q + 186); (Ab + 8, Ab + 16)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' Q [CB 186 (repeat (Z_to_bv 8 0) 186)] /\ stk rsegs m' (Ab + 8) (Ab + 16) /\
         bytes_at rsegs m' (Ab + 8) (le8 s11))
      (MS (mkR (Z_to_bv 64 0x81640) sp gp tp t0' t1' t2' s0 s1 s11 a1' a2' a3' a4' a5' a6' a7'
               (Z_to_bv 64 (SlotModel.CAT + 296 * ((bv_unsigned s6 / 2) mod 11))) s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3' t4' t5' t6')
          F (Z_to_bv 64 0x81640) fc None m2 (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp t0' t1' t2' s0 s1 a1' a2' a3' a4' a5' a6' a7' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
    F fc m m1 m2 Ab Q -> HQrt HQA HA64 MU WM STS B11 MU2 WM2 RW2.
  unfold RT_HI in HQrt.
  assert (Hsub : sub_fp [(Q, Q + 186)] [(Q, Q + 186); (Ab + 8, Ab + 16)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m2 MU (munch_weaken _ _ m1 m2 Hsub MU2)) as MUf.
  pose proof (stk_transport_disjoint rsegs [(Q, Q + 186)] m1 m2 (Ab + 8) (Ab + 16) STS MU2 WM2
    ltac:(cbn [disjoint_from]; repeat split; first [exact I | lia])) as STf.
  pose proof (bytes_at_transport rsegs [(Q, Q + 186)] m1 m2 _ _ B11 MU2
    ltac:(rewrite length_le8; change (Z.of_nat 8) with 8; cbn [disjoint_from]; repeat split; first [exact I | lia]))
    as B11'.
  apply evtF_done. do 2 eexists. split; [reflexivity|].
  do 9 (split; [reflexivity|]).
  split; [reflexivity|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m2 WM WM2)|].
  split; [exact RW2|]. split; [exact STf | exact B11'].
Qed.

(* r2_evt from its two stretches and the __asan_set_shadow_00 contract taken at the call, as R2.v:250-255 takes
   it. *)
Lemma r2_evt_of_F : SSH.asan_set_shadow_00_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Ab c Q : Z) (junk jsp : list byte),
    a0 = Z_to_bv 64 SlotModel.CAT -> s1 = Z_to_bv 64 Ab -> s4 = Z_to_bv 64 c -> s11 = Z_to_bv 64 Q ->
    RT_HI <= Q -> Q + 186 <= Ab + 8 -> Ab + 16 <= 2 ^ 64 ->
    ro_cells rsegs m c [C8 (Z_to_bv 64 11)] ->
    (forall i, 0 <= i < 186 -> in_shadow (Q + i)) ->
    rw_cells rsegs m Q [CB 186 junk] ->
    rw_cells rsegs m (Ab + 8) [CB 8 jsp] -> stk rsegs m (Ab + 8) (Ab + 16) ->
    asan_cells m -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81640) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 23 = s7 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 18 = Z_to_bv 64 (SlotModel.CAT + 296 * ((bv_unsigned s6 / 2) mod 11)) /\
         munch [(Q, Q + 186); (Ab + 8, Ab + 16)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' Q [CB 186 (repeat (Z_to_bv 8 0) 186)] /\ stk rsegs m' (Ab + 8) (Ab + 16) /\
         bytes_at rsegs m' (Ab + 8) (le8 s11))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815fc) fc None m (seg_rom rsegs)).
Proof.
  intros SH0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Ab c Q junk jsp Ea0 Es1 Es4 Es11 HQrt HQA HA64 RC HQsh CHQ CHS STS HAC HMI.
  pose proof (rw_cells_bound rsegs m Q _ CHQ) as HQb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HQb.
  assert (HcB : 0 <= c /\ c + 8 <= 2 ^ 64).
  { destruct RC as (_ & HB). cbn [cells_bytes cbytes] in HB. rewrite ?app_nil_r in HB.
    apply bytes_at_bound in HB. rewrite length_le8 in HB. change (Z.of_nat 8) with 8 in HB. lia. }
  assert (HQ0 : 0 <= Q) by (unfold RT_HI in HQrt; lia).
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply (r2_evt_pre_F RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m Ab c Q junk jsp Ea0 Es1 Es4 Es11 HQrt HQA HA64 RC HQsh CHQ CHS STS HAC HMI);
      apply rng_all; lia. }
  intros ms1 (a2' & s2' & m1 & E1 & Es2 & MU & WM & CHQ1 & STS1 & B11 & HAC1 & HMI1).
  subst ms1 s11.
  unfold SSH.asan_set_shadow_00_contract, SSH.asan_set_shadow_contract in SH0.
  eapply evt_cut.
  { eapply SH0 with (junk := junk); cbv zeta.
    - rewrite !MState.unsigned_lit by lia. intros i Hi. apply HQsh. lia.
    - rewrite !MState.unsigned_lit by lia. exact CHQ1.
    - exact HAC1.
    - exact HMI1. }
  intros ms' PO. unfold SSH.asan_set_shadow_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2'' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  E & MU2 & WM2 & MI2 & RW2).
  subst ms'.
  rewrite !MState.unsigned_lit in MU2, RW2 by lia.
  replace (ret_pc (Z_to_bv 64 0x81640)) with (Z_to_bv 64 0x81640)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  subst s2'.
  apply (evtF_evt rsegs RNG_all).
  exact (r2_evt_post_F RNG_all sp gp tp t0' t1' t2' s0 s1 a1' a2'' a3' a4' a5' a6' a7' s3 s4 s5 s6 s7 s8 s9 s10
           (Z_to_bv 64 Q) t3' t4' t5' t6' F fc m m1 m2 Ab Q eq_refl HQrt HQA HA64 MU WM STS1 B11 MU2 WM2 RW2).
Qed.
Definition r2_evt_src_check : ltac:(let t := type of r2_evt_of_F in exact t) := R2.r2_evt.
