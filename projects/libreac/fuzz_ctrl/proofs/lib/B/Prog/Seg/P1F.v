(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 741 of its 860 lines of code are new or changed and 892 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R2.v, with its module paths, module names, addresses and numbers changed; 241 of its 367 lines of code are new or changed and 734 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/P1.v; 293 of its 404 lines of code are new or changed and 256 lines of the source are left out. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/P1.v p1_evt_bfc, p1_evt, p1_evt_pc at a working branch
     3803efccea0 (blob 0de0b82c0a61f46fe6498af06e04e6bf6381bbd1);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: p1_evt_bfc_of_F / p1_evt_of_F / p1_evt_pc_of_F compose the pre stretch, the caller's
     asan_set_shadow_f8_contract premise and p1_post_F and re-derive the three source statements verbatim;
     p1_evt_bfc_same / p1_evt_same / p1_evt_pc_same check those types against P1's lemmas.
     p1_bfc_pre_F re-runs P1.v lines 69-96 (0x81c60 .. 0x81ca4, up to the callee entry), p1_pre_F line 159
     and that stretch (0x81c58 .. 0x81ca4), p1_pc_pre_F both entries, p1_post_F lines 104-132 (the return pc
     0x81ca8, no instruction left in the stretch). *)
(* rule 24: no function proved. *)
(* The footprint twins of P1's runs, split at the call (parent ruling: every call splits):
     li s2,-8; the 14 frame-shadow stores; li a1,187; ld a0,8(s1); jal meta_fill_f8
       -> p1_bfc_pre_F, stops AT the callee entry 0x55144 with ra = 0x81ca8.
   Regions of the stretch: the 19 frame-shadow bytes [Sh + 272, Sh + 291) (written) and the frame-shadow
   pointer [Ab + 8, Ab + 16) (read).  No instrumented check in the stretch; the 187 shadow bytes
   [Q, Q + 187) are the callee's own footprint and appear only in the post facts. *)
(* Route (C) (a Theorem Labs lane 09:38Z, amendment 10:34Z; writer of record a Theorem Labs lane): p1_pc_pre_F_on is p1_pc_pre_F with the
   universal premise `shadow_rw m` narrowed to B.ShadowRwOn.shadow_rw_on (p1_pc_pre_F_shadow_R Q) m, and with the
   post p1_at_call_on, whose conjunct `shadow_rw m1` is the transport `forall P, shadow_rw_on P m -> shadow_rw_on P m1`
   (every region: the stretch writes only the 19 frame-shadow bytes, and those are present in m1).
   Measured from the stretch's proof: the 19 frame-shadow stores go through the rw_cells premise (rng (Sh + 272) 19)
   and the pointer load through the ro_cells premise (rng (Ab + 8) 8), so neither uses the shadow premise; the shadow
   premise is used for exactly one region, the 187 shadow bytes [Q, Q + 187) that the post's callee window
   rw_cells m1 Q [CB 187 junkQ] needs present (bp_stk_rw).  So p1_pc_pre_F_shadow_R Q covers the bytes of the post's
   rw_cells m1 Q [CB 187 junkQ], not bytes the run accesses: the stretch neither reads nor stores [Q, Q + 187) (the
   callee at 0x55144, ASS.asan_set_shadow_f8_contract, stores them).  p1_bfc_pre_F_on carries the stretch's proof;
   p1_bfc_pre_F and p1_pc_pre_F keep their statements, as corollaries (shadow_rw_on_of_shadow_rw; the post through
   p1_at_call_of_on, P := fun _ => True). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_set_shadow_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_bp.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require P1.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn.
Import ListNotations.
Open Scope Z_scope.

Module ASS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_set_shadow_c.

(* Tac_bp.bp_fix matches [evt] (3 arguments); the [evtF] goal has 4.  Same hook over evtF. *)
Ltac bp_fixF :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      first [rewrite (bp_le1_lit z) by lia | rewrite (bp_le1 (Z_to_bv 64 z))]; mem_after_store
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (bp_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac bp_sbF := step; bp_fixF.

(* The state at the callee entry, shared by the three pre lemmas. *)
Definition p1_at_call (sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z)
    : machine_state -> Prop :=
  fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) (m1 : word -> option byte) (junkQ : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x81ca8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab)
                  (Z_to_bv 64 Q) (Z_to_bv 64 187) a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (-8)) (Z_to_bv 64 Sh) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x55144) fc None m1 (seg_rom rsegs) /\
    munch [(Sh + 272, Sh + 291)] m m1 /\ wmono rsegs m m1 /\
    mem_inv rsegs m1 /\ asan_cells m1 /\ shadow_rw m1 /\
    rw_cells rsegs m1 Q [CB 187 junkQ] /\
    (forall x, Sh + 272 <= x < Sh + 291 -> exists b, mrd rsegs m1 (wa x) = Some b).

(* Route (C): the shadow bytes p1_pc_pre_F needs present through its shadow premise (header). *)
Definition p1_pc_pre_F_shadow_R (Q : Z) : Z -> Prop := fun a => Q <= a < Q + 187.

(* p1_at_call with route (C)'s post: `shadow_rw m1` becomes the transport of every region from m to m1. *)
Definition p1_at_call_on (sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z)
    : machine_state -> Prop :=
  fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) (m1 : word -> option byte) (junkQ : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x81ca8) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 Ab)
                  (Z_to_bv 64 Q) (Z_to_bv 64 187) a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (-8)) (Z_to_bv 64 Sh) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x55144) fc None m1 (seg_rom rsegs) /\
    munch [(Sh + 272, Sh + 291)] m m1 /\ wmono rsegs m m1 /\
    mem_inv rsegs m1 /\ asan_cells m1 /\
    (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1) /\
    rw_cells rsegs m1 Q [CB 187 junkQ] /\
    (forall x, Sh + 272 <= x < Sh + 291 -> exists b, mrd rsegs m1 (wa x) = Some b).

(* The old post from the new one and the universal form at m (P := fun _ => True). *)
Lemma p1_at_call_of_on :
  forall (sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z),
    shadow_rw m -> forall ms',
    p1_at_call_on sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q ms' ->
    p1_at_call sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q ms'.
Proof.
  intros sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q HSW ms' PO.
  unfold p1_at_call_on in PO. unfold p1_at_call.
  destruct PO as (a2' & a3' & a4' & a5' & a6' & a7' & m1 & junkQ & E & MU & WM & MI & AC & SW & RW & RD).
  exists a2', a3', a4', a5', a6', a7', m1, junkQ.
  exact (conj E (conj MU (conj WM (conj MI (conj AC
           (conj (B.ShadowRwOn.shadow_rw_of_on_all m1 (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)))
                 (conj RW RD))))))).
Qed.

(* Tac_bp.bp_shadow_rw under a region guard P: a munch whose written shadow bytes are present after it keeps every
   shadow_rw_on region. *)
Lemma p1_srw_on_munch : forall (P : Z -> Prop) W m m', B.ShadowRwOn.shadow_rw_on P m -> munch W m m' ->
  wmono rsegs m m' -> (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) ->
  B.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P W m m' HS MU WM H a Hp Ha. destruct (HS a Hp Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* ---- 0x81c60 .. 0x81ca4: li s2,-8; the 14 shadow stores; li a1,187; ld a0,8(s1); jal meta_fill_f8 ---- *)
(* Route (C): the stretch's proof, under the narrowed premise and with the post p1_at_call_on. *)
Lemma p1_bfc_pre_F_on :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> B.ShadowRwOn.shadow_rw_on (p1_pc_pre_F_shadow_R Q) m ->
    rng RNG (Sh + 272) 19 -> rng RNG (Ab + 8) 8 ->
    evtF rsegs RNG
      (p1_at_call_on sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs -> -> HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW GS GA.
  do 19 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  pose proof (rw_cells_bound rsegs m (Sh + 272) _ CH) as HSb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HSb.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  unfold RT_HI in HSrt.
  pose proof (munch_refl [(Sh + 272, Sh + 291)] m) as MU1.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  bp_sbF. bp_sbF. bp_sbF. bp_sbF. bp_sbF.
  bp_sbF. bp_sbF. bp_sbF. bp_sbF. bp_sbF.
  bp_sbF. bp_sbF. bp_sbF. bp_sbF.
  step. step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  assert (HRD1 : forall x, Sh + 272 <= x < Sh + 291 -> exists b, mrd rsegs m1 (wa x) = Some b).
  { intros x Hx. apply (bp_ba_rd m1 (Sh + 272) _ x HbC).
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU1). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (HSW1 : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1).
  { intros P HP. apply (p1_srw_on_munch P _ m m1 HP MU1 WM). intros a Ha.
    destruct (Z_le_gt_dec (Sh + 272) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 291)) as [H2|H2]|].
    - right. exact (HRD1 a ltac:(lia)).
    - left. cbn [outside]. split; [lia | exact I].
    - left. cbn [outside]. split; [lia | exact I]. }
  assert (HstkQ : stk rsegs m1 Q (Q + 187)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (Hin : in_shadow a) by (replace a with (Q + (a - Q)) by lia; apply Hshq; lia).
    exact (HSW1 _ HSW a ltac:(unfold p1_pc_pre_F_shadow_R; cbv beta; lia) Hin). }
  destruct (bp_stk_rw _ _ _ HstkQ ltac:(lia)) as (junkQ & RWQ).
  replace (Z.to_nat (Q + 187 - Q)) with 187%nat in RWQ by lia.
  apply evtF_done. unfold p1_at_call_on.
  do 6 eexists. exists m1. exists junkQ.
  split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM|]. split; [exact HMI|]. split; [exact HAC1|].
  split; [exact HSW1|]. split; [exact RWQ | exact HRD1].
Qed.

Lemma p1_bfc_pre_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    rng RNG (Sh + 272) 19 -> rng RNG (Ab + 8) 8 ->
    evtF rsegs RNG
      (p1_at_call sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs Hs3 Hs1 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW GS GA.
  exact (evtF_mono rsegs RNG _ _ _
           (p1_bfc_pre_F_on RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6 F fc m Sh Ab Q xs Hs3 Hs1 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC
              (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) GS GA)
           (p1_at_call_of_on sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q HSW)).
Qed.

(* ---- 0x81c58: beqz a0,0x81c60 taken (a0 = 0), then the same stretch ---- *)
Lemma p1_pre_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 0 ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    rng RNG (Sh + 272) 19 -> rng RNG (Ab + 8) 8 ->
    evtF rsegs RNG
      (p1_at_call sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81c58) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs Hs3 Hs1 -> HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW GS GA.
  step. if_true.
  exact (p1_bfc_pre_F RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
           s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q xs Hs3 Hs1 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16
           HMI HAC HSW GS GA).
Qed.

(* ---- both entries of the poison block, route (C): the narrowed premise and the post p1_at_call_on ---- *)
Lemma p1_pc_pre_F_on :
  forall (RNG : footprint) (pc : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    pc = 0x81c58 \/ pc = 0x81c60 ->
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 0 ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> B.ShadowRwOn.shadow_rw_on (p1_pc_pre_F_shadow_R Q) m ->
    rng RNG (Sh + 272) 19 -> rng RNG (Ab + 8) 8 ->
    evtF rsegs RNG
      (p1_at_call_on sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG pc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs [Hpc | Hpc] Hs3 Hs1 Ha0 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW GS GA;
    subst pc.
  - (* 0x81c58: beqz a0,0x81c60 taken (a0 = 0), then the stretch *)
    subst a0. step. if_true.
    exact (p1_bfc_pre_F_on RNG ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
             s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q xs Hs3 Hs1 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16
             HMI HAC HSW GS GA).
  - exact (p1_bfc_pre_F_on RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             s11 t3 t4 t5 t6 F fc m Sh Ab Q xs Hs3 Hs1 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW
             GS GA).
Qed.

(* ---- both entries of the poison block ---- *)
Lemma p1_pc_pre_F :
  forall (RNG : footprint) (pc : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    pc = 0x81c58 \/ pc = 0x81c60 ->
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 0 ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    rng RNG (Sh + 272) 19 -> rng RNG (Ab + 8) 8 ->
    evtF rsegs RNG
      (p1_at_call sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros RNG pc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs Hpc Hs3 Hs1 Ha0 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW GS GA.
  exact (evtF_mono rsegs RNG _ _ _
           (p1_pc_pre_F_on RNG pc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
              s11 t3 t4 t5 t6 F fc m Sh Ab Q xs Hpc Hs3 Hs1 Ha0 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC
              (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) GS GA)
           (p1_at_call_of_on sp gp tp t0 t1 t2 s0 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q HSW)).
Qed.

(* ---- the return pc 0x81ca8: the premises are the callee post facts and the pre-call facts ---- *)
Lemma p1_post_F :
  forall (RNG : footprint) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32)
         (m m1 m' : word -> option byte) (sp gp tp s0 s1 s3 s7 s9 s10 s11 : word) (Sh Ab Q : Z),
    getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
    getr R 19 = s3 -> getr R 26 = s10 -> getr R 27 = s11 -> getr R 23 = s7 -> getr R 25 = s9 ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 -> Sh <= Q -> Q + 187 <= Sh + 392 ->
    munch [(Sh + 272, Sh + 291)] m m1 -> wmono rsegs m m1 ->
    (forall x, Sh + 272 <= x < Sh + 291 -> exists b, mrd rsegs m1 (wa x) = Some b) ->
    munch [(Q, Q + 187)] m1 m' -> wmono rsegs m1 m' ->
    bytes_at rsegs m' Q (repeat (Z_to_bv 8 0xf8) 187) ->
    evtF rsegs RNG
      (fun ms' => exists (R' : bvmap 5 word) (m'' : word -> option byte),
         ms' = MS R' F (Z_to_bv 64 0x81ca8) fc None m'' (seg_rom rsegs) /\
         getr R' 2 = sp /\ getr R' 3 = gp /\ getr R' 4 = tp /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\
         getr R' 19 = s3 /\ getr R' 26 = s10 /\ getr R' 27 = s11 /\ getr R' 23 = s7 /\ getr R' 25 = s9 /\
         munch [(Sh + 272, Sh + 291); (Q, Q + 187)] m m'' /\ wmono rsegs m m'' /\
         (forall x, Sh + 272 <= x < Sh + 291 \/ Q <= x < Q + 187 ->
            exists b, mrd rsegs m'' (wa x) = Some b))
      (MS R F (Z_to_bv 64 0x81ca8) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG R F fc m m1 m' sp gp tp s0 s1 s3 s7 s9 s10 s11 Sh Ab Q
    K2 K3 K4 K8 K9 K19 K26 K27 K23 K25 HSrt HSA HA64 HQ1 HQ2 MU1 WM HRD1 MU2 WM2 HQb.
  unfold RT_HI in HSrt.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Hsub1 : sub_fp [(Sh + 272, Sh + 291)] [(Sh + 272, Sh + 291); (Q, Q + 187)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  assert (Hsub : sub_fp [(Q, Q + 187)] [(Sh + 272, Sh + 291); (Q, Q + 187)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m'
                (munch_weaken _ _ m m1 Hsub1 MU1) (munch_weaken _ _ m1 m' Hsub MU2)) as MUf.
  assert (RDfin : forall x, Sh + 272 <= x < Sh + 291 \/ Q <= x < Q + 187 ->
            exists b, mrd rsegs m' (wa x) = Some b).
  { intros x Hx.
    destruct (Z_le_gt_dec Q x) as [H1|H1]; [destruct (Z_lt_ge_dec x (Q + 187)) as [H2|H2]|].
    - apply (bp_ba_rd m' Q _ x HQb). rewrite repeat_length. lia.
    - destruct (HRD1 x ltac:(lia)) as (bq & Hbq). exists bq.
      unfold mrd in *. rewrite (MU2 (wa x)); [exact Hbq|].
      rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I].
    - destruct (HRD1 x ltac:(lia)) as (bq & Hbq). exists bq.
      unfold mrd in *. rewrite (MU2 (wa x)); [exact Hbq|].
      rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I]. }
  apply evtF_done. exists R, m'. split; [reflexivity|].
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
  split; [exact K19|]. split; [exact K26|]. split; [exact K27|]. split; [exact K23|]. split; [exact K25|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2) | exact RDfin].
Qed.

(* ---- the compare lemmas: the three source statements of P1 ---- *)
Lemma p1_evt_bfc_of_F : ASS.asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81ca8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 272, Sh + 291); (Q, Q + 187)] m m' /\ wmono rsegs m m' /\
         (forall x, Sh + 272 <= x < Sh + 291 \/ Q <= x < Q + 187 ->
            exists b, mrd rsegs m' (wa x) = Some b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs -> -> HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW.
  unfold ASS.asan_set_shadow_f8_contract, ASS.asan_set_shadow_contract, ASS.ASAN_SET_SHADOW_F8 in SET.
  cbv zeta in SET.
  unfold RT_HI in HSrt.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (EQ1 : bv_unsigned (Z_to_bv 64 Q) = Q) by (apply MState.unsigned_lit; lia).
  assert (EQ2 : bv_unsigned (Z_to_bv 64 187) = 187) by reflexivity.
  eapply evt_cut.
  { apply (evtF_evt rsegs RNG_all).
    apply p1_bfc_pre_F with (Sh := Sh) (Ab := Ab) (Q := Q) (xs := xs); try reflexivity; try assumption;
      apply rng_all; unfold RT_HI in *; lia. }
  intros ms' PO. unfold p1_at_call in PO.
  destruct PO as (a2' & a3' & a4' & a5' & a6' & a7' & m1 & junkQ &
                  E & MU1 & WM & MI1 & AC1 & SW1 & RWQ & HRD1).
  subst ms'.
  eapply evt_cut.
  { eapply SET with (junk := junkQ).
    all: rewrite ?EQ1, ?EQ2.
    - intros i Hi. apply Hshq. lia.
    - exact RWQ.
    - exact AC1.
    - exact MI1. }
  intros ms' PO. unfold ASS.asan_set_shadow_post in PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m' &
                  E & MU2 & WM2 & MI2 & RW2).
  subst ms'.
  rewrite EQ1, EQ2 in MU2, RW2.
  change (Z.to_nat 187) with 187%nat in RW2.
  assert (HQb : bytes_at rsegs m' Q (repeat (Z_to_bv 8 0xf8) 187)).
  { destruct RW2 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  replace (ret_pc (Z_to_bv 64 0x81ca8)) with (Z_to_bv 64 0x81ca8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply (evtF_evt rsegs RNG_all).
  apply p1_post_F with (m := m) (m1 := m1) (Sh := Sh) (Ab := Ab) (Q := Q);
    try reflexivity; try assumption; try (unfold RT_HI); lia.
Qed.

Lemma p1_evt_of_F : ASS.asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 0 ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81ca8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 272, Sh + 291); (Q, Q + 187)] m m' /\ wmono rsegs m m' /\
         (forall x, Sh + 272 <= x < Sh + 291 \/ Q <= x < Q + 187 ->
            exists b, mrd rsegs m' (wa x) = Some b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81c58) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs Hs3 Hs1 -> HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW.
  apply (evt_cut rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5
                                             a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                       F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs))).
  - apply (evtF_evt rsegs RNG_all). step. if_true. apply evtF_done. reflexivity.
  - intros ms' ->.
    exact (p1_evt_bfc_of_F SET ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
             s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Sh Ab Q xs Hs3 Hs1 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16
             HMI HAC HSW).
Qed.

Lemma p1_evt_pc_of_F : ASS.asan_set_shadow_f8_contract ->
  forall (pc : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Sh Ab Q : Z) (xs : list byte),
    pc = 0x81c58 \/ pc = 0x81c60 ->
    s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> a0 = Z_to_bv 64 0 ->
    RT_HI <= Sh -> Sh + 392 <= Ab -> Ab + 24 <= 2 ^ 64 ->
    Sh <= Q -> Q + 187 <= Sh + 392 ->
    (forall i, 0 <= i < 187 -> in_shadow (Q + i)) ->
    length xs = 19%nat -> rw_cells rsegs m (Sh + 272) (map C1 xs) ->
    ro_cells rsegs m (Ab + 8) [C8 (Z_to_bv 64 Q)] ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81ca8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = s11 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 272, Sh + 291); (Q, Q + 187)] m m' /\ wmono rsegs m m' /\
         (forall x, Sh + 272 <= x < Sh + 291 \/ Q <= x < Q + 187 ->
            exists b, mrd rsegs m' (wa x) = Some b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros SET pc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Sh Ab Q xs [Hpc | Hpc] Hs3 Hs1 Ha0 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW; subst pc.
  - exact (p1_evt_of_F SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m Sh Ab Q xs Hs3 Hs1 Ha0 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW).
  - exact (p1_evt_bfc_of_F SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             s11 t3 t4 t5 t6 F fc m Sh Ab Q xs Hs3 Hs1 HSrt HSA HA64 HQ1 HQ2 Hshq Hxs CH RO16 HMI HAC HSW).
Qed.

(* The three compare lemmas have exactly the statements of the source lemmas. *)
Definition p1_evt_bfc_same : ltac:(let T := type of P1.p1_evt_bfc in exact T) := p1_evt_bfc_of_F.
Definition p1_evt_same : ltac:(let T := type of P1.p1_evt in exact T) := p1_evt_of_F.
Definition p1_evt_pc_same : ltac:(let T := type of P1.p1_evt_pc in exact T) := p1_evt_pc_of_F.
