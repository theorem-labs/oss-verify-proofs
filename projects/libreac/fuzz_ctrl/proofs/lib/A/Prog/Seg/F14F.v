(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 748 of its 797 lines of code are new or changed and 962 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F14.v, with its module paths, addresses and numbers changed; 281 of its 423 lines of code are new or changed and 655 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/F14.v blob c01112d1eb85 (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: each <r>_of_F re-derives F14.<r> at ExecF.RNG_all; <r>_of_F_verbatim checks by constr_eq that its type is
   the type of F14.<r>. Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint twins of Seg/F14.v's run lemmas (segment F14 = 0x82154 -> 0x82174 / 0x82178, the bcmp wrapper
   call at 0x82170):
   - f14_evt_e0_F: F14.f14_evt_e0 (:76), the [A+280] <> 0 arm. Its one access is the 8-byte load [A+280], which
     its own premise `bytes_at rsegs m (A + 280) (le8 ...)` names: one rng premise.
   - f14_evt_dc_F: F14.f14_evt_dc (:106), the [A+280] = 0 arm with the wrapper call. Its own accesses are the
     three 8-byte loads [A+280], [A+184], [A+192], each named by its own bytes_at premise. The wrapper enters
     through bcmp_wrap_contract_F (lib/A/Prog/bcmp_wrap_c.v) in the place of F14.f14_evt_dc's plain
     bcmp_wrap_contract premise; the wrapper's own rng premises (rng_bytes, the image range, its window
     [sp - BCMP_WRAP_K, sp), the 72 bytes at L and at R and the aligned 8-byte shadow words covering their
     shadow bytes) are that contract's, passed through unchanged at N = 72.
   - f14_evt_dc_ro_F: F14.f14_evt_dc_ro (:206), the same run on the memory the cut carries (ro_agree in place
     of mem_inv): f14_evt_dc_F on the normalized memory, moved back by MemNormF.evtF_normalize_ro, as
     F14.f14_evt_dc_ro does with MemNorm.evt_normalize.
   F14.sl_run_lib (:303) is NOT re-run: it concludes SR, not evt, so it is out of the spec's scope (a Theorem Labs lane,
   2026-10-28); it stays plain and the ported walk reaches it through the twins above.
   F14.v itself is unchanged. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv memcmp_c bcmp_wrap_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import F13.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals); RngBytes for rng_bytes. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes ExecF_all.
Import ListNotations.
(* As in F14.v: YK11 last among the term-level names (its seg_rom / getr). *)
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.

(* ---- The [A+280] <> 0 arm: four instructions, one 8-byte load, landing at 0x82178. ---- *)
Lemma f14_evt_e0_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A r v280 : Z),
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= v280 < 2 ^ 64 -> v280 <> 0 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 v280)) ->
    ExecF.rng RNG (A + 280) 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 v280)
                                a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 r) s10 s11 t3 t4 t5 t6)
                             Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82154) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r v280 -> -> Hr Hv280b Hv280nz H280 G280.
  pose proof (F14.rd8 m (A + 280) (le8 (Z_to_bv 64 v280)) H280 ltac:(apply length_le8)) as RD280.
  assert (Hbltz : bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false).
  { unfold bv_lts. rewrite (signed_lit r) by lia. rewrite (signed_lit 0) by lia. apply Z.ltb_ge. lia. }
  step.
  replace (bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
  step. step. step.
  assert (EV : bv_unsigned (Z_to_bv 64 v280) = v280) by (apply unsigned_lit; lia).
  replace (negb (bv_eqb (Z_to_bv 64 v280) (Z_to_bv 64 0))) with true
    by (symmetry; apply Bool.negb_true_iff; unfold bv_eqb; rewrite EV;
        change (bv_unsigned (Z_to_bv 64 0)) with 0; apply Z.eqb_neq; exact Hv280nz).
  cbv iota.
  apply ExecF.evtF_done. reflexivity.
Qed.

Lemma f14_evt_e0_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A r v280 : Z),
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= v280 < 2 ^ 64 -> v280 <> 0 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 v280)) ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 v280)
                                a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 r) s10 s11 t3 t4 t5 t6)
                             Fr (Z_to_bv 64 0x82178) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82154) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r v280 E1 E10 Hr Hv280b Hv280nz H280.
  pose proof H280 as (B280a & B280b & _). rewrite length_le8 in B280b.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f14_evt_e0_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6 Fr fc m A r v280 E1 E10 Hr Hv280b Hv280nz H280).
  apply ExecF.rng_all; lia.
Qed.

(* ---- The [A+280] = 0 arm: the three 8-byte loads and the wrapper call, landing at 0x82174. ---- *)
Lemma f14_evt_dc_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r L R vcmp lo : Z) (ls rs : list byte),
    bcmp_wrap_contract_F ->
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 0)) ->
    bytes_at rsegs m (A + 184) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m L ls -> length ls = 72%nat ->
    bytes_at rsegs m R rs -> length rs = 72%nat ->
    memcmp_model ls rs 72 = Some vcmp ->
    mem_inv rsegs m -> addressable m L 72 -> addressable m R 72 ->
    app_mem (L + 72) -> app_mem (L + 7) -> app_mem (R + 72) -> app_mem (R + 7) ->
    (L + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    (* the segment's own accesses: the three spill loads *)
    ExecF.rng RNG (A + 280) 8 -> ExecF.rng RNG (A + 184) 8 -> ExecF.rng RNG (A + 192) 8 ->
    (* the wrapper's regions (bcmp_wrap_contract_F's rng premises at N = 72), unchanged *)
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
    ExecF.rng RNG L 72 ->
    ExecF.rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + 72 - 1) / 8) + 8 - 8 * (shadow_addr L / 8)) ->
    ExecF.rng RNG R 72 ->
    ExecF.rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + 72 - 1) / 8) + 8 - 8 * (shadow_addr R / 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) (Z_to_bv 64 vcmp)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 r) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82174) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ bytes_at rsegs m' L ls /\ bytes_at rsegs m' R rs)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82154) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r L R vcmp lo ls rs HB -> -> Hr HLb HRb H280 H184 H208 HbL Lls HbR Lrs Hmm
    HMI HADL HADR HaL72 HaL7 HaR72 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC0 HSW0 HRB HRM HGC HC254 HC255
    G280 G184 G192 Gby Gimg Gstk GL GsL GR GsR.
  pose proof (F14.rd8 m (A + 280) (le8 (Z_to_bv 64 0)) H280 ltac:(apply length_le8)) as RD280.
  pose proof (F14.rd8 m (A + 184) (le8 (Z_to_bv 64 L)) H184 ltac:(apply length_le8)) as RD184.
  pose proof (F14.rd8 m (A + 192) (le8 (Z_to_bv 64 R)) H208 ltac:(apply length_le8)) as RD208.
  assert (Hbltz : bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false).
  { unfold bv_lts. rewrite (signed_lit r) by lia. rewrite (signed_lit 0) by lia. apply Z.ltb_ge. lia. }
  step.
  replace (bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
  step. step. step.
  replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
  step. step. step. step.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ER : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
  assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by reflexivity.
  pose proof HB as HBc. unfold bcmp_wrap_contract_F, BCMP_WRAP_K in HBc. cbv zeta in HBc.
  eapply ExecF.evtF_cut.
  { eapply HBc with (RNG := RNG) (ls := ls) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER, ?E72.
    - exact HbL.
    - exact HbR.
    - change (Z.to_nat 72) with 72%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL72.
    - right; exact HaR72.
    - right; exact HaL7.
    - right; exact HaR7.
    - exact HdjL.
    - exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC0.
    - exact HSW0.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255.
    - exact Gby.
    - exact Gimg.
    - exact Gstk.
    - exact GL.
    - right; exact GsL.
    - exact GR.
    - right; exact GsR. }
  intros ms' Hp.
  unfold bcmp_wrap_post in Hp.
  destruct Hp as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI' & ST' & AC' & SW' & HbL' & HbR').
  subst ms'.
  replace (ret_pc (Z_to_bv 64 532852)) with (Z_to_bv 64 532852)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply ExecF.evtF_done.
  exists (Z_to_bv 64 532852), a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC'|]. split; [exact SW'|].
  rewrite EL, E72 in HbL'. rewrite ER, E72 in HbR'. change (Z.to_nat 72) with 72%nat in HbL', HbR'.
  rewrite firstn_all2 in HbL' by lia. rewrite firstn_all2 in HbR' by lia.
  split; [exact HbL' | exact HbR'].
Qed.

Lemma f14_evt_dc_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r L R vcmp lo : Z) (ls rs : list byte),
    bcmp_wrap_contract_F ->
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 0)) ->
    bytes_at rsegs m (A + 184) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m L ls -> length ls = 72%nat ->
    bytes_at rsegs m R rs -> length rs = 72%nat ->
    memcmp_model ls rs 72 = Some vcmp ->
    mem_inv rsegs m -> addressable m L 72 -> addressable m R 72 ->
    app_mem (L + 72) -> app_mem (L + 7) -> app_mem (R + 72) -> app_mem (R + 7) ->
    (L + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) (Z_to_bv 64 vcmp)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 r) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82174) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ bytes_at rsegs m' L ls /\ bytes_at rsegs m' R rs)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82154) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r L R vcmp lo ls rs HB E1 E10 Hr HLb HRb H280 H184 H208 HbL Lls HbR Lrs Hmm
    HMI HADL HADR HaL72 HaL7 HaR72 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC0 HSW0 HRB HRM HGC HC254 HC255.
  pose proof H280 as (B280a & B280b & _). rewrite length_le8 in B280b.
  pose proof H184 as (B184a & B184b & _). rewrite length_le8 in B184b.
  pose proof H208 as (B192a & B192b & _). rewrite length_le8 in B192b.
  pose proof HADL as (_ & _ & BL & _). pose proof HADR as (_ & _ & BR & _).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f14_evt_dc_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6 Fr fc m A r L R vcmp lo ls rs HB E1 E10 Hr HLb HRb H280 H184 H208 HbL Lls
           HbR Lrs Hmm HMI HADL HADR HaL72 HaL7 HaR72 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC0 HSW0 HRB HRM HGC
           HC254 HC255).
  all: first [ intros ? ? ? ? ?; exact I
             | apply ExecF.rng_all;
               unfold shadow_addr, ASAN_K, BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END in *;
               first [ lia | Z.div_mod_to_equations; lia ] ].
Qed.

(* ---- The same run on the memory the cut carries (ro_agree, not mem_inv). ---- *)
Lemma f14_evt_dc_ro_F :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r L R vcmp lo : Z) (ls rs : list byte),
    bcmp_wrap_contract_F ->
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 0)) ->
    bytes_at rsegs m (A + 184) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m L ls -> length ls = 72%nat ->
    bytes_at rsegs m R rs -> length rs = 72%nat ->
    memcmp_model ls rs 72 = Some vcmp ->
    ro_agree rsegs m -> addressable m L 72 -> addressable m R 72 ->
    app_mem (L + 72) -> app_mem (L + 7) -> app_mem (R + 72) -> app_mem (R + 7) ->
    (L + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    ExecF.rng RNG (A + 280) 8 -> ExecF.rng RNG (A + 184) 8 -> ExecF.rng RNG (A + 192) 8 ->
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
    ExecF.rng RNG L 72 ->
    ExecF.rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + 72 - 1) / 8) + 8 - 8 * (shadow_addr L / 8)) ->
    ExecF.rng RNG R 72 ->
    ExecF.rng RNG (8 * (shadow_addr R / 8)) (8 * (shadow_addr (R + 72 - 1) / 8) + 8 - 8 * (shadow_addr R / 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) (Z_to_bv 64 vcmp)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 r) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82174) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ bytes_at rsegs m' L ls /\ bytes_at rsegs m' R rs)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82154) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r L R vcmp lo ls rs HB E1 E10 Hr HLb HRb H280 H184 H208 HbL Lls HbR Lrs Hmm
    HRO HADL HADR HaL72 HaL7 HaR72 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC0 HSW0 HRB HRM HGC HC254 HC255
    G280 G184 G192 Gby Gimg Gstk GL GsL GR GsR.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hrostk : forall x, lo <= x < bv_unsigned sp -> ro_addr rsegs (wa x) = false).
  { intros x Hx. apply RoAdapt.ro_addr_false_hi. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (f14_evt_dc_F RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
    s11 t3 t4 t5 t6 Fr fc (normalize rsegs m) A r L R vcmp lo ls rs HB E1 E10 Hr HLb HRb
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) H280) (proj1 (bytes_at_rel rsegs m _ _ _ REL) H184)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) H208)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HbL) Lls (proj1 (bytes_at_rel rsegs m _ _ _ REL) HbR) Lrs Hmm
    (mem_inv_normalize rsegs m) (RoAdapt.rel_addr_norm m _ _ _ REL HADL) (RoAdapt.rel_addr_norm m _ _ _ REL HADR)
    HaL72 HaL7 HaR72 HaR7 HdjL HdjR (RoAdapt.rel_stk_norm m _ _ _ REL Hrostk HST) Hlo1 Hlo2 Hspa
    (RoAdapt.rel_ac_norm m _ REL HAC0) (RoAdapt.rel_sw_norm m _ REL HSW0)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRB) (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRM)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HGC) (proj1 (bytes_at_rel rsegs m _ _ _ REL) HC254)
    (proj1 (bytes_at_rel rsegs m _ _ _ REL) HC255)
    G280 G184 G192 Gby Gimg Gstk GL GsL GR GsR) as HC.
  pose proof (MNF.evtF_normalize_ro RNG _ _ _ _ _ _ m (seg_rom rsegs) HRO HC) as HN.
  eapply ExecF.evtF_mono; [exact HN|].
  intros ms (s0' & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
              & E & MU & WM & MI' & ST' & AC' & SW' & HbL' & HbR') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exact (RoAdapt.rel_stk_back memX m0' _ _ Hmr ST')|].
  split; [exact (RoAdapt.rel_ac_back memX m0' Hmr AC')|].
  split; [exact (RoAdapt.rel_sw_back memX m0' Hmr SW')|].
  split; [exact (proj2 (bytes_at_rel rsegs memX m0' _ _ Hmr) HbL')
        | exact (proj2 (bytes_at_rel rsegs memX m0' _ _ Hmr) HbR')].
Qed.

Lemma f14_evt_dc_ro_of_F :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r L R vcmp lo : Z) (ls rs : list byte),
    bcmp_wrap_contract_F ->
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 r -> 0 <= r <= 1 ->
    0 <= L < 2 ^ 64 -> 0 <= R < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 0)) ->
    bytes_at rsegs m (A + 184) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m (A + 192) (le8 (Z_to_bv 64 R)) ->
    bytes_at rsegs m L ls -> length ls = 72%nat ->
    bytes_at rsegs m R rs -> length rs = 72%nat ->
    memcmp_model ls rs 72 = Some vcmp ->
    ro_agree rsegs m -> addressable m L 72 -> addressable m R 72 ->
    app_mem (L + 72) -> app_mem (L + 7) -> app_mem (R + 72) -> app_mem (R + 7) ->
    (L + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 72 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) (Z_to_bv 64 vcmp)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 r) s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82174) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ bytes_at rsegs m' L ls /\ bytes_at rsegs m' R rs)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82154) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r L R vcmp lo ls rs HB E1 E10 Hr HLb HRb H280 H184 H208 HbL Lls HbR Lrs Hmm
    HRO HADL HADR HaL72 HaL7 HaR72 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC0 HSW0 HRB HRM HGC HC254 HC255.
  pose proof H280 as (B280a & B280b & _). rewrite length_le8 in B280b.
  pose proof H184 as (B184a & B184b & _). rewrite length_le8 in B184b.
  pose proof H208 as (B192a & B192b & _). rewrite length_le8 in B192b.
  pose proof HADL as (_ & _ & BL & _). pose proof HADR as (_ & _ & BR & _).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (f14_evt_dc_ro_F ExecF.RNG_all ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
           s9 s10 s11 t3 t4 t5 t6 Fr fc m A r L R vcmp lo ls rs HB E1 E10 Hr HLb HRb H280 H184 H208 HbL Lls
           HbR Lrs Hmm HRO HADL HADR HaL72 HaL7 HaR72 HaR7 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC0 HSW0 HRB HRM HGC
           HC254 HC255).
  all: first [ intros ? ? ? ? ?; exact I
             | apply ExecF.rng_all;
               unfold shadow_addr, ASAN_K, BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END in *;
               first [ lia | Z.div_mod_to_equations; lia ] ].
Qed.

(* ---- The pins. ---- *)
Example f14_evt_e0_of_F_verbatim : True.
Proof.
  let a := type of F14.f14_evt_e0 in let b := type of f14_evt_e0_of_F in constr_eq a b.
  exact I.
Qed.

Example f14_evt_dc_of_F_verbatim : True.
Proof.
  assert (pin : forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                        t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
                       (A r L R vcmp lo : Z) (ls rs : list byte), True).
  { intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      Fr fc m A r L R vcmp lo ls rs.
    lazymatch type of (F14.f14_evt_dc ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
                         s9 s10 s11 t3 t4 t5 t6 Fr fc m A r L R vcmp lo ls rs) with
    | ?P -> ?X =>
      lazymatch type of (f14_evt_dc_of_F ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                           s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m A r L R vcmp lo ls rs) with
      | ?Q -> ?Y => constr_eq P bcmp_wrap_contract; constr_eq Q bcmp_wrap_contract_F; constr_eq X Y
      end
    end.
    exact I. }
  exact I.
Qed.

Example f14_evt_dc_ro_of_F_verbatim : True.
Proof.
  assert (pin : forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                        t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
                       (A r L R vcmp lo : Z) (ls rs : list byte), True).
  { intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      Fr fc m A r L R vcmp lo ls rs.
    lazymatch type of (F14.f14_evt_dc_ro ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                         s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m A r L R vcmp lo ls rs) with
    | ?P -> ?X =>
      lazymatch type of (f14_evt_dc_ro_of_F ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                           s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m A r L R vcmp lo ls rs) with
      | ?Q -> ?Y => constr_eq P bcmp_wrap_contract; constr_eq Q bcmp_wrap_contract_F; constr_eq X Y
      end
    end.
    exact I. }
  exact I.
Qed.

