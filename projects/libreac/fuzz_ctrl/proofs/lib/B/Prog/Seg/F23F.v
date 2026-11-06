(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F12.v, with its module names, addresses and numbers changed; 628 of its 880 lines of code are new or changed and 1457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F23.v, with its module names changed; 174 of its 307 lines of code are new or changed and 747 lines of the source are left out. *)
(* rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source run: lib/B/Prog/Seg/F23.v f23_evt (:297) (from a working branch 3803efccea0)
     (blob 239425eb4a73e99e2011d0236d92c3f1d9ed2fc1);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c);
   compare: f23_evt calls __asan_memcpy (jal at 0x82870, return pc 0x82874), so it is split: f23_pre_F re-runs
     F23.v:350-440 (0x82844 -> the callee entry 0x52164, ra = 0x82874), carrying to the callee entry exactly the
     facts about the post-store memory that f23_evt feeds to the contract, and f23_post_F re-runs F23.v:468-509
     (the return pc 0x82874 -> the run's end 0x82878: the single step `li s7,1`), with the callee post facts as
     premises; f23_li_F re-runs that same single step (F23.v:468) on its own, with no memory premise. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcFrag RcFragLib RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv asan_memcpy_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_f23.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F23.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn B.Prog.MemMono.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.

(* The `bne` of 0x82844 compares two copies of the same value, so it is not taken (F23.v:70-80 over evtF). *)
Ltac f23f_bne :=
  match goal with
  | |- context [negb (bv_eqb ?x ?x)] =>
      replace (negb (bv_eqb x x)) with false by (rewrite bv_eqb_refl; reflexivity); cbv iota
  end.

(* Route (C) (a Theorem Labs lane 09:20Z; form a Theorem Labs lane 09:38Z, amendment 10:34Z): f23_pre_F with its shadow facts narrowed.
   Measured from f23_pre_F's proof: its premise `shadow_rw m` (HSWm) has ONE use, in RT3, where it gives every shadow
   byte other than K3 + 16 / K3 + 17 readable in the post-store memory, for HRTnew's third premise; that builds the
   post's shadow_rw, it is not an access.  The run's memory accesses are the `rng` ranges: 0x82848 sd s8,272(s1) to
   [A + 272, A + 280) (writable by wr_at m (A + 272) 8), 0x82850 sb zero,16(s3) and 0x82858 sb a0,17(s3) to the
   shadow bytes K3 + 16, K3 + 17 (writable by wr_at m (K3 + 16) 2), 0x82868 ld s5,104(s1) from [A + 104, A + 112)
   (bytes_at m (A + 104)).  No read or store goes through `shadow_rw m`, so the premise is DROPPED.
   HRTnew is narrowed in the same form: its third premise (every shadow byte readable in mm, which needs the whole
   shadow of m) becomes B.Prog.MemMono.rd_mono m mm (every byte readable in m is readable in mm), and its
   `shadow_rw mm` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P mm`.  The post's `shadow_rw m'` becomes
   `forall P, shadow_rw_on P m -> shadow_rw_on P m'`; the two shadow bytes the run writes are readable after it (b8). *)
Lemma f23_pre_F_on :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3v s4 s5v s6v s7v s8v s9 s10 s11
          t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A K3 D v kk lo : Z) (junk : list byte),
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 v -> s7v = Z_to_bv 64 v -> s3v = Z_to_bv 64 K3 ->
    s8v = Z_to_bv 64 kk ->
    0 <= A -> A + 448 <= 2 ^ 64 ->
    0 <= K3 -> K3 + FRAME_SHADOW <= 2 ^ 64 -> ASAN_K + 0x4240 <= K3 ->
    0 <= D -> D + 12 <= APPMEM_END -> D mod 8 = 0 -> D / 8 + ASAN_K = K3 + 16 ->
    (forall t, 0 <= t <= 12 -> app_mem (D + t)) ->
    AC.GT <= D -> D + 12 <= A -> K3 + 18 <= A -> K3 + 18 <= lo ->
    (K3 + 18 <= D \/ D + 12 <= K3 + 16) ->
    0 <= kk < 2 ^ 64 ->
    wr_at rsegs m (K3 + 16) 2 ->
    wr_at rsegs m (A + 272) 8 ->
    (forall mm, munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m mm -> wmono rsegs m mm ->
       B.Prog.MemMono.rd_mono m mm ->
       asan_cells mm /\ (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P mm)) ->
    bytes_at rsegs m (A + 104) (le8 (Z_to_bv 64 D)) ->
    rw_cells rsegs m D [CB 12 junk] ->
    addressable m 0x21180 12 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMCPY_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    RT_HI <= D ->
    (D + 12 <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= D) ->
    bv_unsigned sp <= A ->
    rng RNG (A + 272) 8 -> rng RNG (K3 + 16) 2 -> rng RNG (A + 104) 8 ->
    evtF rsegs RNG
      (fun ms' => exists m',
         ms' = MS (mkR (Z_to_bv 64 0x82874) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 D) (Z_to_bv 64 0x21180)
                       (Z_to_bv 64 12) a3 a4 a5 a6 a7 s2 s3v s4 (Z_to_bv 64 D) s6v s7v s9 s9 s10 s11
                       t3 t4 t5 t6)
                  Fr (Z_to_bv 64 ASAN_MEMCPY) fc None m' (seg_rom rsegs)
         /\ munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m')
         /\ b8 m' (K3 + 16) 0 /\ b8 m' (K3 + 17) 4 /\ q64 m' (A + 272) kk
         /\ rw_cells rsegs m' D [CB 12 junk] /\ addressable m' 0x21180 12 /\ addressable m' D 12)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3v s4 s5v s6v s7v s8v s9 s10 s11
              t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82844) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3v s4 s5v s6v s7v s8v s9 s10 s11
    t3 t4 t5 t6 Fr fc m A K3 D v kk lo junk -> -> -> -> ->
    HA0 HA1 HK0 HK1 HKlow HD0 HDE HD8 HDK HappD HGTD HDA HKA HKlo HdjKD Hkk
    HWRsh HWRsp HRTnew H104 HRWD HADS HMI HST Hlo1 Hlo2 Hspa HRTD HdjDW HspA R272 R16 R104.
  pose proof FRAME_SHADOW_val as HFSv.
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold ASAN_MEMCPY_K in Hlo1; lia).
  (* the FAIL branch at 0x82844 is not taken: a0 and s7 both hold the record-verify result *)
  step. f23f_bne.
  (* 0x82848 sd s8,272(s1) *)
  assert (HS272 : store_ok rsegs m (wa (A + 272)) 8 = true).
  { replace (A + 272) with (A + 272 + 0) by lia.
    apply (wr_at_store_ok rsegs m (A + 272) 8 0 8%nat HWRsp); [lia | cbn; lia]. }
  step.
  (* 0x8284c mv s8,s9 *)
  step.
  (* 0x82850 sb zero,16(s3) *)
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS16 : store_ok rsegs mm (wa (K3 + 16)) 1 = true) by
      (replace (K3 + 16) with (K3 + 16 + 0) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 16) 2 0 1%nat);
       [repeat apply wr_at_write; exact HWRsh | lia | cbn; lia])
  end.
  step.
  (* 0x82854 li a0,4 *)
  step.
  (* 0x82858 sb a0,17(s3) *)
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS17 : store_ok rsegs mm (wa (K3 + 17)) 1 = true) by
      (replace (K3 + 17) with (K3 + 16 + 1) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 16) 2 1 1%nat);
       [repeat apply wr_at_write; exact HWRsh | lia | cbn; lia])
  end.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MU3 : munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m mm) by
      (repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; slia ]);
       apply munch_refl);
    assert (WM3 : wmono rsegs m mm) by (repeat apply wmono_write; apply wmono_refl);
    assert (ST3 : stk rsegs mm lo (bv_unsigned sp)) by
      (repeat (apply stk_write; [ | lia | simpl_sizes; lia ]); exact HST);
    assert (MI3 : mem_inv rsegs mm) by
      (apply mem_inv_store; [|simpl_sizes; exact HS17];
       apply mem_inv_store; [|simpl_sizes; exact HS16];
       apply mem_inv_store; [|simpl_sizes; exact HS272]; exact HMI);
    assert (B16 : b8 mm (K3 + 16) 0) by
      (apply tf_wother; [F23.f23_zb | | lia | lia | lia];
       apply tf_wsame; [F23.f23_zb | lia | lia]);
    assert (B17 : b8 mm (K3 + 17) 4) by
      (apply tf_wsame; [F23.f23_zb | lia | lia]);
    assert (Q272 : q64 mm (A + 272) kk) by
      (unfold q64;
       repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]);
       apply bytes_at_write_same; [lia | rewrite length_le8; lia]);
    assert (RD104 : ov_read_bytes rsegs mm (wa (A + 104)) 8 = Some (le8 (Z_to_bv 64 D))) by
      (apply tf_rd8;
       [ repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]); exact H104
       | apply length_le8 ]);
    assert (RW3 : rw_cells rsegs mm D [CB 12 junk]) by
      (repeat (apply rw_cells_frame; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]); exact HRWD);
    assert (AS3 : addressable mm 0x21180 12) by
      (apply (tf_addr_munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m mm 0x21180 12 HADS MU3);
       intros i Hi;
       assert (Hsh : ASAN_K + 0x4230 <= shadow_addr (0x21180 + i) <= ASAN_K + 0x4231)
         by (unfold shadow_addr; Z.div_mod_to_equations; lia);
       cbn [Frame.outside];
       split; [lia|]; split; [unfold HIGHMEM_BEG, ASAN_K in *; lia | exact I]);
    assert (AD3 : addressable mm D 12) by
      (apply (tf_addr_sh mm D 12); [lia | lia | lia | exact HD8 | intros t Ht; apply HappD; lia |];
       intros t Ht;
       assert (Esh : shadow_addr D = K3 + 16) by (unfold shadow_addr; lia);
       rewrite Esh;
       destruct (Z_lt_le_dec t 8) as [Hlt|Hge];
       [ exists 0; replace (K3 + 16 + t / 8) with (K3 + 16) by (Z.div_mod_to_equations; lia);
         split; [exact B16|]; split; [lia | left; reflexivity]
       | exists 4; replace (K3 + 16 + t / 8) with (K3 + 17) by (Z.div_mod_to_equations; lia);
         split; [exact B17|]; split; [lia | right; Z.div_mod_to_equations; lia] ]);
    (* the three stores only add or replace bytes, so every byte readable in m is readable in mm *)
    assert (RT3 : asan_cells mm /\ (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P mm)) by
      (apply (HRTnew mm MU3 WM3);
       repeat apply B.Prog.MemMono.rd_mono_write; apply B.Prog.MemMono.rd_mono_refl)
  end.
  destruct RT3 as (AC3 & SW3).
  (* 0x8285c auipc a0,0xfff9f ; 0x82860 addi a1,a0,-1756 (a1 = 0x21180) ; 0x82864 li a2,12 ;
     0x82868 ld s5,104(s1) ; 0x8286c mv a0,s5 ; 0x82870 jal checked_memcpy *)
  do 6 step.
  apply evtF_done. eexists.
  split; [reflexivity|].
  split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3|].
  split; [exact AC3|]. split; [exact SW3|].
  split; [exact B16|]. split; [exact B17|]. split; [exact Q272|].
  split; [exact RW3|]. split; [exact AS3 | exact AD3].
Qed.

(* The pre half of f23_evt: the FAIL branch that is not taken, the spill store, the register move s8 = s9, the
   two shadow stores that mark [D, D + 12) usable, the source address, the count, the spill load and the jal,
   stopping at the copy's entry 0x52164 with ra = 0x82874.  The post carries exactly the facts about the written
   memory that f23_evt gives the copy contract.  Route (C): proved from f23_pre_F_on, statement unchanged. *)
Lemma f23_pre_F :
  forall (RNG : footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3v s4 s5v s6v s7v s8v s9 s10 s11
          t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A K3 D v kk lo : Z) (junk : list byte),
    s1v = Z_to_bv 64 A -> a0v = Z_to_bv 64 v -> s7v = Z_to_bv 64 v -> s3v = Z_to_bv 64 K3 ->
    s8v = Z_to_bv 64 kk ->
    0 <= A -> A + 448 <= 2 ^ 64 ->
    0 <= K3 -> K3 + FRAME_SHADOW <= 2 ^ 64 -> ASAN_K + 0x4240 <= K3 ->
    0 <= D -> D + 12 <= APPMEM_END -> D mod 8 = 0 -> D / 8 + ASAN_K = K3 + 16 ->
    (forall t, 0 <= t <= 12 -> app_mem (D + t)) ->
    AC.GT <= D -> D + 12 <= A -> K3 + 18 <= A -> K3 + 18 <= lo ->
    (K3 + 18 <= D \/ D + 12 <= K3 + 16) ->
    0 <= kk < 2 ^ 64 ->
    wr_at rsegs m (K3 + 16) 2 ->
    wr_at rsegs m (A + 272) 8 ->
    shadow_rw m ->
    (forall mm, munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m mm -> wmono rsegs m mm ->
       (forall a, in_shadow a -> exists b, mrd rsegs mm (wa a) = Some b) ->
       asan_cells mm /\ shadow_rw mm) ->
    bytes_at rsegs m (A + 104) (le8 (Z_to_bv 64 D)) ->
    rw_cells rsegs m D [CB 12 junk] ->
    addressable m 0x21180 12 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMCPY_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    RT_HI <= D ->
    (D + 12 <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= D) ->
    bv_unsigned sp <= A ->
    rng RNG (A + 272) 8 -> rng RNG (K3 + 16) 2 -> rng RNG (A + 104) 8 ->
    evtF rsegs RNG
      (fun ms' => exists m',
         ms' = MS (mkR (Z_to_bv 64 0x82874) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 D) (Z_to_bv 64 0x21180)
                       (Z_to_bv 64 12) a3 a4 a5 a6 a7 s2 s3v s4 (Z_to_bv 64 D) s6v s7v s9 s9 s10 s11
                       t3 t4 t5 t6)
                  Fr (Z_to_bv 64 ASAN_MEMCPY) fc None m' (seg_rom rsegs)
         /\ munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ b8 m' (K3 + 16) 0 /\ b8 m' (K3 + 17) 4 /\ q64 m' (A + 272) kk
         /\ rw_cells rsegs m' D [CB 12 junk] /\ addressable m' 0x21180 12 /\ addressable m' D 12)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3v s4 s5v s6v s7v s8v s9 s10 s11
              t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82844) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3v s4 s5v s6v s7v s8v s9 s10 s11
    t3 t4 t5 t6 Fr fc m A K3 D v kk lo junk E1 E2 E3 E4 E5
    HA0 HA1 HK0 HK1 HKlow HD0 HDE HD8 HDK HappD HGTD HDA HKA HKlo HdjKD Hkk
    HWRsh HWRsp HSWm HRTnew H104 HRWD HADS HMI HST Hlo1 Hlo2 Hspa HRTD HdjDW HspA R272 R16 R104.
  assert (HRTon : forall mm, munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m mm -> wmono rsegs m mm ->
            B.Prog.MemMono.rd_mono m mm ->
            asan_cells mm /\ (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P mm)).
  { intros mm MU WM RD.
    destruct (HRTnew mm MU WM (fun a Ha => RD _ (proj2 (HSWm a Ha)))) as (AC & SW).
    split; [exact AC | intros P _; exact (B.ShadowRwOn.shadow_rw_on_of_shadow_rw P mm SW)]. }
  eapply evtF_mono;
    [exact (f23_pre_F_on RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1v a2v a3 a4 a5 a6 a7 s2 s3v s4 s5v s6v s7v s8v s9
              s10 s11 t3 t4 t5 t6 Fr fc m A K3 D v kk lo junk E1 E2 E3 E4 E5
              HA0 HA1 HK0 HK1 HKlow HD0 HDE HD8 HDK HappD HGTD HDA HKA HKlo HdjKD Hkk
              HWRsh HWRsp HRTon H104 HRWD HADS HMI HST Hlo1 Hlo2 Hspa HRTD HdjDW HspA R272 R16 R104)|].
  intros ms' (m' & E & MU & WM & MI & ST & AC & SW & Rest).
  exists m'. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact AC|].
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all m' (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSWm)))|].
  exact Rest.
Qed.

(* The post half of f23_evt (F23.v:468-509): the return pc 0x82874 `li s7,1`, then the run's exit cut 0x82878.
   The premises are the copy post clauses f23_evt reads at that point plus the facts about the pre-call memory
   it carries through.  The single step makes no memory access. *)
Lemma f23_post_F :
  forall (RNG : footprint)
         (sp gp tp t0' t1' t2' s0 s1v a1' a2' a3' a4' a5' a6' a7' s2 s3v s4 s6v s7v s9 s10 s11
          t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m mm m' : word -> option byte)
         (A K3 D kk lo : Z),
    munch [(K3 + 16, K3 + 18); (A + 272, A + 280)] m mm -> wmono rsegs m mm ->
    b8 mm (K3 + 16) 0 -> b8 mm (K3 + 17) 4 -> q64 mm (A + 272) kk ->
    0 <= D -> D + 12 <= APPMEM_END -> 0 <= K3 -> K3 + 18 <= A -> K3 + 18 <= lo ->
    AC.GT <= D -> D + 12 <= A -> HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= bv_unsigned sp ->
    (K3 + 18 <= D \/ D + 12 <= K3 + 16) -> (D + 12 <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= D) ->
    bv_unsigned sp <= A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
    munch [(D, D + 12); (bv_unsigned sp - ASAN_MEMCPY_K, bv_unsigned sp)] mm m' ->
    wmono rsegs mm m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
    bytes_at rsegs m' D F23.f23_src -> asan_cells m' -> shadow_rw m' ->
    evtF rsegs RNG
      (fun ms' => exists (ra'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word)
                         (m'' : word -> option byte),
         ms' = MS (mkR ra'' sp gp tp t0'' t1'' t2'' s0 s1v a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                       s2 s3v s4 (Z_to_bv 64 D) s6v (Z_to_bv 64 1) s9 s9 s10 s11
                       t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x82878) fc None m'' (seg_rom rsegs)
         /\ munch (F23.f23_W K3 A D (bv_unsigned sp)) m m''
         /\ wmono rsegs m m'' /\ mem_inv rsegs m''
         /\ stk rsegs m'' lo (bv_unsigned sp)
         /\ asan_cells m'' /\ shadow_rw m''
         /\ bytes_at rsegs m'' D F23.f23_src
         /\ q64 m'' (A + 272) kk
         /\ b8 m'' (K3 + 16) 0 /\ b8 m'' (K3 + 17) 4)
      (MS (mkR (Z_to_bv 64 0x82874) sp gp tp t0' t1' t2' s0 s1v (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7'
               s2 s3v s4 (Z_to_bv 64 D) s6v s7v s9 s9 s10 s11 t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x82874) fc None m' (seg_rom rsegs)).
Proof.
  intros RNG sp gp tp t0' t1' t2' s0 s1v a1' a2' a3' a4' a5' a6' a7' s2 s3v s4 s6v s7v s9 s10 s11
    t3' t4' t5' t6' Fr fc m mm m' A K3 D kk lo
    MU3 WM3 B16 B17 Q272 HD0 HDE HK0 HKA HKlo HGTD HDA Hlohi Hlo1 HdjKD HdjDW HspA HA0 HA1
    MUc WMc MIc STc BSc ACc SWc.
  (* 0x82874 li s7,1 *)
  step.
  apply evtF_done.
  do 17 eexists.
  split; [reflexivity|].
  split.
  { eapply munch_trans.
    - apply (munch_weaken [(K3 + 16, K3 + 18); (A + 272, A + 280)]); [|exact MU3].
      unfold sub_fp, F23.f23_W, ASAN_MEMCPY_K. cbn [Frame.outside].
      intros x (Hx1 & Hx2 & _). split; [lia|]. split; [lia | exact I].
    - apply (munch_weaken [(D, D + 12); (bv_unsigned sp - ASAN_MEMCPY_K, bv_unsigned sp)]); [|exact MUc].
      unfold sub_fp, F23.f23_W. cbn [Frame.outside].
      intros x (_ & _ & Hx3 & Hx4 & _). split; [lia|]. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m _ m' WM3 WMc)|].
  split; [exact MIc|].
  split; [exact STc|].
  split; [exact ACc|].
  split; [exact SWc|].
  split; [exact BSc|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Q272 | exact MUc |].
    rewrite length_le8. intros x Hx. cbn [Frame.outside].
    split; [lia|]. split; [unfold ASAN_MEMCPY_K; lia | exact I]. }
  split.
  { unfold b8 in *. eapply fl_bytes; [exact B16 | exact MUc |].
    cbn [length]. intros x Hx. cbn [Frame.outside].
    split; [lia|]. split; [unfold ASAN_MEMCPY_K, HIGHMEM_BEG in *; lia | exact I]. }
  { unfold b8 in *. eapply fl_bytes; [exact B17 | exact MUc |].
    cbn [length]. intros x Hx. cbn [Frame.outside].
    split; [lia|]. split; [unfold ASAN_MEMCPY_K, HIGHMEM_BEG in *; lia | exact I]. }
Qed.

(* The bare one-step footprint run of the instruction that f23_post_F steps: the return pc of the
   __asan_memcpy call, 0x82874 `li s7,1`, to the run's exit cut 0x82878.  It reads and writes no memory
   (the fetch is not a data access), so it carries NO memory premise and no `rng` premise at all; the
   memory, the fregs, the fcsr, the reservation and every register other than s7 and the pc are untouched. *)
Lemma f23_li_F :
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
          t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
                       (Z_to_bv 64 1) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x82878) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82874) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 Fr fc m.
  (* 0x82874 li s7,1 *)
  step.
  apply evtF_done. reflexivity.
Qed.
