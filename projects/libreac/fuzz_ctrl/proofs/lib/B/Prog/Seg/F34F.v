(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1126 of its 1261 lines of code are new or changed and 876 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F34.v; 294 of its 560 lines of code are new or changed and 995 lines of the source are left out. *)
(* Footprint (ExecF.evtF) twins of the segment-F34 machine runs of lib/B/Prog/Seg/F34.v (fuzz_ctrl
   LLVMFuzzerTestOneInput, asan-ubsan image B). Bridge input for the cgif-form walk only.
   rule 24: no function proved. *)
(* Provenance (route (a) bridge input, lead 22:18Z; auditor a Theorem Labs lane):
   image fuzz_ctrl.asan-ubsan v1.9.0, pau-libreac-v190,
     sha256 12136677c5cf9891b3aed0c4821499bba9dde76b0e6baadb7ac66e07e6a62c17;
   source runs: lib/B/Prog/Seg/F34.v f34_evt (:288), f34_evt_ro (:583) at
     a working branch 3803efccea0 (blob 3ea1805a512e7c61ff389eef317e9438cb9536c9);
   tool: lib/Lib/StepF.v c97545265d26d5d39c131602ff95accd1bc78f07 (the blob this tree had at release c5e779efe8c),
         lib/Lib/ExecF.v 38b86b5d83a511566e396810e9b0b51804f48e22 (the blob this tree had at release c5e779efe8c),
         lib/B/MemNormF.v blob 99f8b314301ceb0f253f1a6c8165b488b23ce218 (taken by path from dba073859bd);
   compare: both runs call declaration_of (jal at 0x82c20), so each is split: f34_evt_pre_F re-runs F34.v:335-476
     (0x82bf4 up to the callee entry 0x83114, ra = 0x82c24) and f34_evt_post_F re-runs F34.v:499-556 (from the
     return pc 0x82c24 to the exit cut 0x82c24, no step); f34_evt_ro_pre_F is the ro twin of the pre stretch
     (F34.v:619-643) and f34_evt_ro_post_F the ro twin of the post (F34.v:645-668). No callee contract is stated
     here, so there is no _of_F. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI BzBridge MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require declaration_of_c declaration_of.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import F34.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn B.ShadowRwOnT B.Prog.MemMono.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

(* rw_cells comes back from the normalized memory (the same move as F30.v:459-464; copied here so that this file
   does not depend on F30). *)
Lemma f34F_rwc_back : forall m m0 a cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 a _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 a _ HR Hw).
Qed.

(* Route (C) (a Theorem Labs lane 09:20Z; form a Theorem Labs lane 09:38Z, amendment 10:34Z): f34_evt_pre_F with its shadow facts narrowed
   (the run f34_evt_ro_pre_F_on takes on the normalized memory).  Measured from f34_evt_pre_F's proof: its premise
   `shadow_rw m` (HSW) is used only in Hsh1 / HSW1, the post's shadow_rw m1 (every shadow byte outside [S + 8, S + 12)
   still readable after the stores); it is not an access.  The run's memory accesses are the `rng` ranges: the four
   stores sb zero to the shadow bytes S + 8 .. S + 11 (writable by the wview premise on [S + 8, S + 12)) and
   ld s6,152(s1) from [A + 152, A + 160) (bytes_at).  No read or store goes through `shadow_rw m`, so the premise is
   DROPPED.  The post's `shadow_rw m1` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P m1`: the four stores
   only add or replace bytes (ShadowRwOnT.shadow_rw_on_mem_mono, MemMono.rd_mono_write). *)
Lemma f34_evt_pre_F_on :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (S A T o ost spv lo : Z) (row ob : list byte) (RNG : footprint),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 A -> x19 = Z_to_bv 64 S ->
    x10 = Z_to_bv 64 o -> x11 = Z_to_bv 64 0 -> x12 = Z_to_bv 64 0 ->
    x21 = Z_to_bv 64 T -> x23 = Z_to_bv 64 (T + o) ->
    2148236288 <= S -> S + 12 <= HIGHMEM_BEG ->
    (forall k, 0 <= k < 4 -> wview rsegs m (wa (S + 8 + k)) <> None) ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= ost -> ost + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (ost + k)) -> app_mem (ost + 32) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (ost + k) < S + 12) ->
    rw_cells rsegs m ost [CB 32 ob] -> length ob = 32%nat ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 ost)) -> HIGHMEM_BEG <= A -> A + 160 <= 2 ^ 64 ->
    0 <= o -> 0 <= T -> T + o + 296 <= 656088 -> (T + o) mod 8 = 0 ->
    length row = 296%nat -> decl_ok row = true ->
    bytes_at rsegs m (T + o) row -> addressable m (T + o) 296 ->
    stk rsegs m lo spv -> HIGHMEM_BEG <= lo -> lo + 2256 <= spv -> spv <= APPMEM_END ->
    (ost + 32 <= spv - 2256 \/ spv <= ost) -> RT_HI <= ost ->
    mem_inv rsegs m -> asan_cells m ->
    rng RNG (S + 8) 4 -> rng RNG (A + 152) 8 ->
    evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR (Z_to_bv 64 0x82c24) (Z_to_bv 64 spv) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 A)
                       (Z_to_bv 64 (T + o)) (Z_to_bv 64 ost) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                       x18 (Z_to_bv 64 S) x20 (Z_to_bv 64 T) (Z_to_bv 64 ost) (Z_to_bv 64 (T + o))
                       (Z_to_bv 64 (o + T)) x25 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 DECLc.DECLARATION_OF) fcs None m1 (seg_rom rsegs) /\
         munch [(S + 8, S + 12)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         asan_cells m1 /\ (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1) /\
         stk rsegs m1 lo spv /\
         bytes_at rsegs m1 (T + o) row /\ rw_cells rsegs m1 ost [CB 32 ob] /\
         addressable m1 (T + o) 296 /\ addressable m1 ost 32)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82bf4) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m S A T o ost spv lo row ob RNG
    E2 E9 E19 E10 E11 E12 E21 E23 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
    H152 HAhi HAb Hoz HTz Hrhi Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoRT HMI HAC
    RS8 R152.
  subst x2 x9 x19 x10 x11 x12 x21 x23.
  assert (EAPP : APPMEM_END = 140737488355328) by reflexivity.
  assert (EHMB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (ERTH : RT_HI = 697272) by reflexivity.
  assert (ERTL : RT_LO = 657648) by reflexivity.
  assert (EDK : DECLc.DECLARATION_OF_K = 2256) by reflexivity.
  assert (EK : ASAN_K = 2147450880) by reflexivity.
  assert (HSok : forall (m' : word -> option byte) k, wmono rsegs m m' -> 0 <= k < 4 ->
            store_ok rsegs m' (wa (S + 8 + k)) 1 = true).
  { intros m' k Hw Hk.
    assert (WR : wr_at rsegs m' (S + 8 + k) 1).
    { split; [lia|]. split; [lia|]. intros kk Hkk. assert (Ei : kk = 0) by lia. subst kk.
      rewrite Z.add_0_r. apply Hw. apply HWv. lia. }
    pose proof (wr_at_store_ok rsegs m' (S + 8 + k) 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HSS.
    rewrite Z.add_0_r in HSS. exact HSS. }
  assert (H8 : store_ok rsegs m (wa (S + 8)) 1 = true).
  { replace (S + 8) with (S + 8 + 0) by lia. apply (HSok m 0); [apply wmono_refl | lia]. }
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H9 : store_ok rsegs mm (wa (S + 9)) 1 = true)
        by (replace (S + 9) with (S + 8 + 1) by lia; apply (HSok mm 1);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H10 : store_ok rsegs mm (wa (S + 10)) 1 = true)
        by (replace (S + 10) with (S + 8 + 2) by lia; apply (HSok mm 2);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H11 : store_ok rsegs mm (wa (S + 11)) 1 = true)
        by (replace (S + 11) with (S + 8 + 3) by lia; apply (HSok mm 3);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Em1 : mm = write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (S + 8)) [Z_to_bv 8 0])
                       (wa (S + 9)) [Z_to_bv 8 0]) (wa (S + 10)) [Z_to_bv 8 0]) (wa (S + 11)) [Z_to_bv 8 0])
        by (repeat f_equal; try reflexivity; vm_compute; reflexivity);
      rewrite Em1; clear Em1
  end.
  set (m1 := write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (S + 8)) [Z_to_bv 8 0])
                 (wa (S + 9)) [Z_to_bv 8 0]) (wa (S + 10)) [Z_to_bv 8 0]) (wa (S + 11)) [Z_to_bv 8 0]) in *.
  assert (MU1 : munch [(S + 8, S + 12)] m m1).
  { unfold m1. apply munch_write; [apply munch_write; [apply munch_write; [apply munch_write;
      [apply munch_refl | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]. }
  assert (WM1 : wmono rsegs m m1)
    by (unfold m1; apply wmono_write, wmono_write, wmono_write, wmono_write, wmono_refl).
  assert (MI1 : mem_inv rsegs m1).
  { unfold m1. apply mem_inv_store; [apply mem_inv_store; [apply mem_inv_store;
      [apply mem_inv_store; [exact HMI|] |] |] |]; cbn [length].
    - replace (S + 8) with (S + 8 + 0) by lia. apply (HSok m 0); [apply wmono_refl | lia].
    - replace (S + 9) with (S + 8 + 1) by lia. apply (HSok _ 1); [apply wmono_write, wmono_refl | lia].
    - replace (S + 10) with (S + 8 + 2) by lia.
      apply (HSok _ 2); [apply wmono_write, wmono_write, wmono_refl | lia].
    - replace (S + 11) with (S + 8 + 3) by lia.
      apply (HSok _ 3); [apply wmono_write, wmono_write, wmono_write, wmono_refl | lia]. }
  assert (Hb8 : forall k, 0 <= k < 4 -> bytes_at rsegs m1 (S + 8 + k) [Z_to_bv 8 0]).
  { intros k Hk. unfold m1.
    assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct Hk' as [ -> | [ -> | [ -> | -> ]]].
    - rewrite Z.add_0_r.
      apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_other;
        [apply bytes_at_write_same | | |] | | |] | | |]; cbn [length]; lia.
    - replace (S + 8 + 1) with (S + 9) by lia.
      apply bytes_at_write_other; [apply bytes_at_write_other;
        [apply bytes_at_write_same | | |] | | |]; cbn [length]; lia.
    - replace (S + 8 + 2) with (S + 10) by lia.
      apply bytes_at_write_other; [apply bytes_at_write_same | | |]; cbn [length]; lia.
    - replace (S + 8 + 3) with (S + 11) by lia. apply bytes_at_write_same; cbn [length]; lia. }
  assert (Hkeep : forall a bs, bytes_at rsegs m a bs -> (a + Z.of_nat (length bs) <= S + 8 \/ S + 12 <= a) ->
                    bytes_at rsegs m1 a bs).
  { intros a bs Hb Hd. eapply fl_bytes; [exact Hb | exact MU1 |].
    intros x Hx. cbn [outside]. split; [lia | exact I]. }
  (* every region of m: the four stores only add or replace bytes *)
  assert (HSW1 : forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1).
  { intros P HP. apply (B.ShadowRwOnT.shadow_rw_on_mem_mono P m m1 HP WM1).
    unfold m1. apply B.Prog.MemMono.rd_mono_write, B.Prog.MemMono.rd_mono_write, B.Prog.MemMono.rd_mono_write,
      B.Prog.MemMono.rd_mono_write, B.Prog.MemMono.rd_mono_refl. }
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept [(S + 8, S + 12)] m m1 HAC MU1).
    unfold RT_LO, RT_HI. cbn [disjoint_from]. split; [left; lia | exact I]. }
  assert (Hrow1 : bytes_at rsegs m1 (T + o) row) by (apply Hkeep; [exact Hrow | rewrite Hrlen; lia]).
  assert (H152' : bytes_at rsegs m1 (A + 152) (le8 (Z_to_bv 64 ost)))
    by (apply Hkeep; [exact H152 | rewrite length_le8; lia]).
  assert (HL152 : ov_read_bytes rsegs m1 (wa (A + 152)) 8 = Some (le8 (Z_to_bv 64 ost))).
  { pose proof (bytes_at_ov_read rsegs m1 (A + 152) (le8 (Z_to_bv 64 ost)) 0 8 H152'
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (Hob1 : rw_cells rsegs m1 ost [CB 32 ob]).
  { destruct Hob as ((Hwf & Hbb) & Hw). split.
    - split; [exact Hwf|]. eapply fl_bytes; [exact Hbb | exact MU1 |].
      intros x Hx. cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hoblen in Hx.
      cbn [outside]. split; [|exact I]. intros Hc.
      apply (app_not_shadow x).
      + replace x with (ost + (x - ost)) by lia. apply Hoapp. cbn [Z.of_nat] in Hx. lia.
      + replace x with (S + 8 + (x - S - 8)) by lia. apply HSin. lia.
    - unfold m1. apply wr_at_write, wr_at_write, wr_at_write, wr_at_write. exact Hw. }
  assert (Hstk1 : stk rsegs m1 lo spv).
  { unfold m1. apply stk_write; [apply stk_write; [apply stk_write; [apply stk_write;
      [exact HST | lia | cbn [length]; lia] | lia | cbn [length]; lia] | lia | cbn [length]; lia]
      | lia | cbn [length]; lia]. }
  assert (Haddr1 : addressable m1 ost 32).
  { split; [lia|]. split; [lia|]. split; [lia|].
    intros k Hk. split; [apply Hoapp; lia|].
    exists (Z_to_bv 8 0). split; [|unfold shadow_ok; left; reflexivity].
    destruct (Hb8 (shadow_addr (ost + k) - S - 8) ltac:(pose proof (Hosh k Hk); lia)) as (_ & _ & Hb).
    replace (S + 8 + (shadow_addr (ost + k) - S - 8)) with (shadow_addr (ost + k)) in Hb
      by (pose proof (Hosh k Hk); lia).
    pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0. cbn [Z.of_nat] in Hb0.
    rewrite Z.add_0_r in Hb0. exact Hb0. }
  assert (Haddrrow1 : addressable m1 (T + o) 296).
  { apply (f34_addr_keep m m1 (T + o) 296 Hraddr). intros a Ha. unfold mrd.
    rewrite (MU1 (wa (shadow_addr a))); [reflexivity|].
    assert (Happa : app_mem a) by (pose proof (f34_addr_app m (T + o) 296 (a - (T + o)) Hraddr ltac:(lia)) as Hp;
      replace (T + o + (a - (T + o))) with a in Hp by lia; exact Hp).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ (shadow_of_app a Happa)); lia).
    cbn [outside]. split; [|exact I]. intros Hc.
    unfold shadow_addr, ASAN_K in *. revert Ha Hc Hrhi HTz Hoz HSlo. Z.div_mod_to_equations. lia. }
  (* --- 0x82c04 bne a1,a2 (0 = 0): not taken --- *)
  step. if_false.
  (* --- 0x82c08 add s8,a0,s5 ; 0x82c0c sltu a0,s8,a0 --- *)
  step. step.
  rewrite (f34_sltu_zero (o + T) o) by (first [lia | rewrite Z.mod_small by lia; lia]).
  (* --- 0x82c10 bnez a0 (a0 = 0): not taken --- *)
  step. if_false.
  (* --- 0x82c14 mv a0,s7 ; 0x82c18 ld s6,152(s1) ; 0x82c1c mv a1,s6 ; 0x82c20 jal declaration_of --- *)
  step. step. step. step.
  apply evtF_done. exists m1.
  split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
  split; [exact HAC1|]. split; [exact HSW1|]. split; [exact Hstk1|].
  split; [exact Hrow1|]. split; [exact Hob1|].
  split; [exact Haddrrow1 | exact Haddr1].
Qed.

(* ---- 0x82bf4 up to the declaration_of entry 0x83114 (F34.v:335-476).  Route (C): proved from f34_evt_pre_F_on,
   statement unchanged. *)
Lemma f34_evt_pre_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (S A T o ost spv lo : Z) (row ob : list byte) (RNG : footprint),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 A -> x19 = Z_to_bv 64 S ->
    x10 = Z_to_bv 64 o -> x11 = Z_to_bv 64 0 -> x12 = Z_to_bv 64 0 ->
    x21 = Z_to_bv 64 T -> x23 = Z_to_bv 64 (T + o) ->
    2148236288 <= S -> S + 12 <= HIGHMEM_BEG ->
    (forall k, 0 <= k < 4 -> wview rsegs m (wa (S + 8 + k)) <> None) ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= ost -> ost + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (ost + k)) -> app_mem (ost + 32) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (ost + k) < S + 12) ->
    rw_cells rsegs m ost [CB 32 ob] -> length ob = 32%nat ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 ost)) -> HIGHMEM_BEG <= A -> A + 160 <= 2 ^ 64 ->
    0 <= o -> 0 <= T -> T + o + 296 <= 656088 -> (T + o) mod 8 = 0 ->
    length row = 296%nat -> decl_ok row = true ->
    bytes_at rsegs m (T + o) row -> addressable m (T + o) 296 ->
    stk rsegs m lo spv -> HIGHMEM_BEG <= lo -> lo + 2256 <= spv -> spv <= APPMEM_END ->
    (ost + 32 <= spv - 2256 \/ spv <= ost) -> RT_HI <= ost ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    rng RNG (S + 8) 4 -> rng RNG (A + 152) 8 ->
    evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR (Z_to_bv 64 0x82c24) (Z_to_bv 64 spv) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 A)
                       (Z_to_bv 64 (T + o)) (Z_to_bv 64 ost) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                       x18 (Z_to_bv 64 S) x20 (Z_to_bv 64 T) (Z_to_bv 64 ost) (Z_to_bv 64 (T + o))
                       (Z_to_bv 64 (o + T)) x25 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 DECLc.DECLARATION_OF) fcs None m1 (seg_rom rsegs) /\
         munch [(S + 8, S + 12)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         asan_cells m1 /\ shadow_rw m1 /\ stk rsegs m1 lo spv /\
         bytes_at rsegs m1 (T + o) row /\ rw_cells rsegs m1 ost [CB 32 ob] /\
         addressable m1 (T + o) 296 /\ addressable m1 ost 32)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82bf4) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m S A T o ost spv lo row ob RNG
    E2 E9 E19 E10 E11 E12 E21 E23 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
    H152 HAhi HAb Hoz HTz Hrhi Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoRT HMI HAC HSW
    RS8 R152.
  eapply evtF_mono;
    [exact (f34_evt_pre_F_on x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
              x24 x25 x26 x27 x28 x29 x30 x31 Fr fcs m S A T o ost spv lo row ob RNG
              E2 E9 E19 E10 E11 E12 E21 E23 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
              H152 HAhi HAb Hoz HTz Hrhi Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoRT HMI HAC
              RS8 R152)|].
  intros ms' (m1 & E & MU & WM & MI & AC & SW & Rest).
  exists m1. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact AC|].
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all m1 (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)))|].
  exact Rest.
Qed.

(* ---- From the return pc 0x82c24 to the exit cut 0x82c24 (F34.v:499-556): no step. *)
Lemma f34_evt_post_F :
  forall (x3 x4 x8 x18 x20 x25 x26 x27 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fcs : bv 32) (m m1 m2 : word -> option byte)
         (S A T o ost spv lo : Z) (row : list byte) (RNG : footprint),
    2148236288 <= S -> S + 12 <= HIGHMEM_BEG ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= ost -> ost + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (ost + k)) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (ost + k) < S + 12) ->
    HIGHMEM_BEG <= lo -> lo + 2256 <= spv -> spv <= APPMEM_END ->
    length row = 296%nat ->
    munch [(S + 8, S + 12)] m m1 -> wmono rsegs m m1 -> addressable m1 ost 32 ->
    munch [(spv - 2256, spv); (ost, ost + 32)] m1 m2 -> wmono rsegs m1 m2 ->
    mem_inv rsegs m2 -> stk rsegs m2 lo spv -> shadow_rw m2 ->
    rw_cells rsegs m2 ost [CB 32 (decl row)] ->
    evtF rsegs RNG
      (fun ms' => exists (t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82c24) (Z_to_bv 64 spv) x3 x4 t0'' t1'' t2'' x8 (Z_to_bv 64 A)
                       (Z_to_bv 64 1) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                       x18 (Z_to_bv 64 S) x20 (Z_to_bv 64 T) (Z_to_bv 64 ost) (Z_to_bv 64 (T + o))
                       (Z_to_bv 64 (o + T)) x25 x26 x27 t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x82c24) fcs None m' (seg_rom rsegs) /\
         munch [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ shadow_rw m' /\ stk rsegs m' lo spv /\
         bytes_at rsegs m' ost (decl row) /\ addressable m' ost 32 /\
         (forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] q ->
            exists b, mrd rsegs m' (wa q) = Some b))
      (MS (mkR (Z_to_bv 64 0x82c24) (Z_to_bv 64 spv) x3 x4 t0' t1' t2' x8 (Z_to_bv 64 A)
               (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
               x18 (Z_to_bv 64 S) x20 (Z_to_bv 64 T) (Z_to_bv 64 ost) (Z_to_bv 64 (T + o))
               (Z_to_bv 64 (o + T)) x25 x26 x27 t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x82c24) fcs None m2 (seg_rom rsegs)).
Proof.
  intros x3 x4 x8 x18 x20 x25 x26 x27 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    Fr fcs m m1 m2 S A T o ost spv lo row RNG
    HSlo HShi HSin Ho0 Ho1 Hoapp Hosh Hlo1 Hlo2 Hsp1 Hrlen MU1 WM1 Haddr1 MU2 WM2 MI2 ST2 SW2 RW2.
  assert (EAPP : APPMEM_END = 140737488355328) by reflexivity.
  assert (EHMB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (MUa : munch [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] m m2).
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU1]. intros x (Hx & _). cbn [outside]. split; [exact Hx | exact I].
    - eapply munch_weaken; [|exact MU2]. intros x (_ & Hx1 & Hx2 & _). cbn [outside].
      split; [exact Hx1|]. split; [exact Hx2 | exact I]. }
  assert (WMa : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  destruct RW2 as (((Hdlen & _) & Hdbb) & _).
  cbn [cells_bytes cbytes] in Hdbb. rewrite app_nil_r in Hdbb.
  assert (HINa : forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] q ->
            exists b, mrd rsegs m2 (wa q) = Some b).
  { intros q Hq Hno.
    assert (Hslot : ost <= q < ost + 32 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. destruct Hdbb as (_ & _ & Hb).
      pose proof (Hb (Z.to_nat (q - ost)) ltac:(rewrite Hdlen; lia)) as Hb0.
      replace (ost + Z.of_nat (Z.to_nat (q - ost))) with q in Hb0 by lia.
      destruct (nth_error (decl row) (Z.to_nat (q - ost))) as [b|] eqn:En;
        [exists b; exact Hb0 | apply nth_error_None in En; rewrite Hdlen in En; lia]. }
    assert (Hshq : S + 8 <= q < S + 12 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (SW2 q ltac:(replace q with (S + 8 + (q - S - 8)) by lia; apply HSin; lia))). }
    assert (Hwinq : spv - 2256 <= q < spv -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (proj2 (proj2 ST2) q ltac:(lia))). }
    destruct (Z_le_dec (S + 8) q) as [L1|L1]; destruct (Z_lt_dec q (S + 12)) as [L2|L2];
    destruct (Z_le_dec (spv - 2256) q) as [L3|L3]; destruct (Z_lt_dec q spv) as [L4|L4];
    destruct (Z_le_dec ost q) as [L5|L5]; destruct (Z_lt_dec q (ost + 32)) as [L6|L6];
    first [ apply Hshq; lia | apply Hwinq; lia | apply Hslot; lia
          | exfalso; apply Hno; cbn [outside]; repeat split; try exact I; lia ]. }
  assert (Haddr2 : addressable m2 ost 32).
  { apply (f34_addr_keep m1 m2 ost 32 Haddr1). intros a Ha. unfold mrd.
    rewrite (MU2 (wa (shadow_addr a))); [reflexivity|].
    assert (Hin : S + 8 <= shadow_addr a < S + 12) by (pose proof (Hosh (a - ost) ltac:(lia)) as Hp;
      replace (ost + (a - ost)) with a in Hp by lia; exact Hp).
    assert (Happa : app_mem a) by (replace a with (ost + (a - ost)) by lia; apply Hoapp; lia).
    assert (Hinsh : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Happa).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ Hinsh); lia).
    cbn [outside]. split; [|split; [|exact I]].
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      replace (shadow_addr a) with (ost + (shadow_addr a - ost)) by lia. apply Hoapp. lia. }
  apply evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
  split; [reflexivity|].
  split; [exact MUa|]. split; [exact WMa|]. split; [exact MI2|]. split; [exact SW2|].
  split; [exact ST2|]. split; [exact Hdbb|]. split; [exact Haddr2 | exact HINa].
Qed.

(* Route (C) (a Theorem Labs lane 09:20Z; form a Theorem Labs lane 09:38Z, amendment 10:34Z): f34_evt_ro_pre_F with its shadow facts
   narrowed.  Measured from f34_evt_ro_pre_F's proof: its premise `shadow_rw m` (HSW) has ONE use, moved to the
   normalized memory (Tac_ro.shadow_rw_rel) as f34_evt_pre_F's premise, whose only use is the post (see
   f34_evt_pre_F_on); its accesses are f34_evt_pre_F's: the four stores to the shadow bytes S + 8 .. S + 11
   (writable by the wview premise) and the load from [A + 152, A + 160).  No read or store goes through
   `shadow_rw m`, so the premise is DROPPED.  The post's `shadow_rw m1` becomes
   `forall P, shadow_rw_on P m -> shadow_rw_on P m1`: f34_evt_pre_F_on's post on the normalized memory, moved by
   ShadowRwOnT.shadow_rw_on_rel (m to normalize m) and ShadowRwOnT.shadow_rw_on_of_rel (back to m1). *)
Lemma f34_evt_ro_pre_F_on :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (S A T o ost spv lo : Z) (row ob : list byte) (RNG : footprint),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 A -> x19 = Z_to_bv 64 S ->
    x10 = Z_to_bv 64 o -> x11 = Z_to_bv 64 0 -> x12 = Z_to_bv 64 0 ->
    x21 = Z_to_bv 64 T -> x23 = Z_to_bv 64 (T + o) ->
    2148236288 <= S -> S + 12 <= HIGHMEM_BEG ->
    (forall k, 0 <= k < 4 -> wview rsegs m (wa (S + 8 + k)) <> None) ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= ost -> ost + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (ost + k)) -> app_mem (ost + 32) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (ost + k) < S + 12) ->
    rw_cells rsegs m ost [CB 32 ob] -> length ob = 32%nat ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 ost)) -> HIGHMEM_BEG <= A -> A + 160 <= 2 ^ 64 ->
    0 <= o -> 0 <= T -> T + o + 296 <= 656088 -> (T + o) mod 8 = 0 ->
    length row = 296%nat -> decl_ok row = true ->
    bytes_at rsegs m (T + o) row -> addressable m (T + o) 296 ->
    stk rsegs m lo spv -> HIGHMEM_BEG <= lo -> lo + 2256 <= spv -> spv <= APPMEM_END ->
    (ost + 32 <= spv - 2256 \/ spv <= ost) -> AC.GT <= ost ->
    ro_agree rsegs m -> asan_cells m ->
    rng RNG (S + 8) 4 -> rng RNG (A + 152) 8 ->
    evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR (Z_to_bv 64 0x82c24) (Z_to_bv 64 spv) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 A)
                       (Z_to_bv 64 (T + o)) (Z_to_bv 64 ost) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                       x18 (Z_to_bv 64 S) x20 (Z_to_bv 64 T) (Z_to_bv 64 ost) (Z_to_bv 64 (T + o))
                       (Z_to_bv 64 (o + T)) x25 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 DECLc.DECLARATION_OF) fcs None m1 (seg_rom rsegs) /\
         munch [(S + 8, S + 12)] m m1 /\ wmono rsegs m m1 /\ ro_agree rsegs m1 /\
         (forall P, B.ShadowRwOn.shadow_rw_on P m -> B.ShadowRwOn.shadow_rw_on P m1) /\ stk rsegs m1 lo spv /\
         bytes_at rsegs m1 (T + o) row /\ rw_cells rsegs m1 ost [CB 32 ob] /\
         addressable m1 (T + o) 296 /\ addressable m1 ost 32)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82bf4) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m S A T o ost spv lo row ob RNG
    E2 E9 E19 E10 E11 E12 E21 E23 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
    H152 HAhi HAb Hoz HTz Hrhi Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoGT HRO HAC
    RS8 R152.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hlo0 : LOWMEM_END <= lo) by (unfold HIGHMEM_BEG, LOWMEM_END in *; lia).
  assert (Hsp64 : spv <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HWv0 : forall k, 0 <= k < 4 -> wview rsegs (normalize rsegs m) (wa (S + 8 + k)) <> None).
  { intros k Hk.
    apply (proj2 (Tac_ro.wview_hi m _ (S + 8 + k) REL ltac:(unfold HIGHMEM_BEG, LOWMEM_END in *; lia))).
    exact (HWv k Hk). }
  assert (Hob0 : rw_cells rsegs (normalize rsegs m) ost [CB 32 ob]).
  { destruct Hob as ((Hwf & Hbb) & Hw). split.
    - split; [exact Hwf | exact (Tac_ro.ba_rel m _ _ _ REL Hbb)].
    - pose proof Hw as (Hw0 & Hw1 & _).
      eapply (wr_at_norm rsegs); [exact REL | exact Hw |].
      intros i Hi. apply f34_ro_gt. lia. }
  pose proof (f34_evt_pre_F_on x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x24 x25 x26 x27 x28 x29 x30 x31 Fr fcs (normalize rsegs m) S A T o ost spv lo row ob RNG
    E2 E9 E19 E10 E11 E12 E21 E23 HSlo HShi HWv0 HSin Ho0 Ho1 Hoapp Hoend Hosh Hob0 Hoblen
    (Tac_ro.ba_rel m _ _ _ REL H152) HAhi HAb Hoz HTz Hrhi Hr8 Hrlen Hok (Tac_ro.ba_rel m _ _ _ REL Hrow)
    (Tac_ro.addressable_rel m _ _ _ REL Hraddr) (Tac_ro.stk_rel m _ lo _ REL Hlo0 Hsp64 HST) Hlo1 Hlo2 Hsp1
    Hodj ltac:(unfold RT_HI, AC.GT in *; lia) (mem_inv_normalize rsegs m)
    (Tac_ro.asan_cells_rel m _ REL HAC) RS8 R152) as HC.
  pose proof (MemNormF.evtF_normalize_ro RNG _ _ _ _ _ _ m (seg_rom rsegs) HRO HC) as HN.
  eapply evtF_mono; [exact HN|].
  intros ms (s0' & (m0' & E & MU & WM & MI' & AC' & SW' & ST' & BR' & OB' & AR' & AO') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists memX. split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  (* every region of m: to the normalized memory, the run's post, back to memX *)
  split.
  { intros P HP. apply (B.ShadowRwOnT.shadow_rw_on_of_rel P memX m0' Hmr). apply SW'.
    exact (B.ShadowRwOnT.shadow_rw_on_rel P m _ REL HP). }
  split; [exact (Tac_ro.stk_rel_back memX m0' lo _ Hmr Hlo0 Hsp64 ST')|].
  split; [exact (proj2 (bytes_at_rel rsegs memX m0' _ _ Hmr) BR')|].
  split; [exact (f34F_rwc_back memX m0' _ _ Hmr OB')|].
  split; [exact (f34_addr_back memX m0' _ _ Hmr AR') | exact (f34_addr_back memX m0' ost 32 Hmr AO')].
Qed.

(* ---- The ro twin of the pre stretch (F34.v:619-643): the run is taken on the normalized memory and
   MemNormF.evtF_normalize_ro carries it back to the cut's own memory.  Route (C): proved from f34_evt_ro_pre_F_on,
   statement unchanged. *)
Lemma f34_evt_ro_pre_F :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (S A T o ost spv lo : Z) (row ob : list byte) (RNG : footprint),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 A -> x19 = Z_to_bv 64 S ->
    x10 = Z_to_bv 64 o -> x11 = Z_to_bv 64 0 -> x12 = Z_to_bv 64 0 ->
    x21 = Z_to_bv 64 T -> x23 = Z_to_bv 64 (T + o) ->
    2148236288 <= S -> S + 12 <= HIGHMEM_BEG ->
    (forall k, 0 <= k < 4 -> wview rsegs m (wa (S + 8 + k)) <> None) ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= ost -> ost + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (ost + k)) -> app_mem (ost + 32) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (ost + k) < S + 12) ->
    rw_cells rsegs m ost [CB 32 ob] -> length ob = 32%nat ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 ost)) -> HIGHMEM_BEG <= A -> A + 160 <= 2 ^ 64 ->
    0 <= o -> 0 <= T -> T + o + 296 <= 656088 -> (T + o) mod 8 = 0 ->
    length row = 296%nat -> decl_ok row = true ->
    bytes_at rsegs m (T + o) row -> addressable m (T + o) 296 ->
    stk rsegs m lo spv -> HIGHMEM_BEG <= lo -> lo + 2256 <= spv -> spv <= APPMEM_END ->
    (ost + 32 <= spv - 2256 \/ spv <= ost) -> AC.GT <= ost ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    rng RNG (S + 8) 4 -> rng RNG (A + 152) 8 ->
    evtF rsegs RNG
      (fun ms' => exists m1,
         ms' = MS (mkR (Z_to_bv 64 0x82c24) (Z_to_bv 64 spv) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 A)
                       (Z_to_bv 64 (T + o)) (Z_to_bv 64 ost) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                       x18 (Z_to_bv 64 S) x20 (Z_to_bv 64 T) (Z_to_bv 64 ost) (Z_to_bv 64 (T + o))
                       (Z_to_bv 64 (o + T)) x25 x26 x27 x28 x29 x30 x31)
                  Fr (Z_to_bv 64 DECLc.DECLARATION_OF) fcs None m1 (seg_rom rsegs) /\
         munch [(S + 8, S + 12)] m m1 /\ wmono rsegs m m1 /\ ro_agree rsegs m1 /\
         shadow_rw m1 /\ stk rsegs m1 lo spv /\
         bytes_at rsegs m1 (T + o) row /\ rw_cells rsegs m1 ost [CB 32 ob] /\
         addressable m1 (T + o) 296 /\ addressable m1 ost 32)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82bf4) fcs None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m S A T o ost spv lo row ob RNG
    E2 E9 E19 E10 E11 E12 E21 E23 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
    H152 HAhi HAb Hoz HTz Hrhi Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoGT HRO HAC HSW
    RS8 R152.
  eapply evtF_mono;
    [exact (f34_evt_ro_pre_F_on x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
              x23 x24 x25 x26 x27 x28 x29 x30 x31 Fr fcs m S A T o ost spv lo row ob RNG
              E2 E9 E19 E10 E11 E12 E21 E23 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
              H152 HAhi HAb Hoz HTz Hrhi Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoGT HRO HAC
              RS8 R152)|].
  intros ms' (m1 & E & MU & WM & RO & SW & Rest).
  exists m1. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact RO|].
  split; [exact (B.ShadowRwOn.shadow_rw_of_on_all m1 (SW _ (B.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)))|].
  exact Rest.
Qed.

(* ---- The ro twin of the post (F34.v:645-668): ro_agree in place of mem_inv. *)
Lemma f34_evt_ro_post_F :
  forall (x3 x4 x8 x18 x20 x25 x26 x27 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
         (Fr : bvmap 5 word) (fcs : bv 32) (m m1 m2 : word -> option byte)
         (S A T o ost spv lo : Z) (row : list byte) (RNG : footprint),
    2148236288 <= S -> S + 12 <= HIGHMEM_BEG ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= ost -> ost + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (ost + k)) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (ost + k) < S + 12) ->
    HIGHMEM_BEG <= lo -> lo + 2256 <= spv -> spv <= APPMEM_END ->
    length row = 296%nat ->
    munch [(S + 8, S + 12)] m m1 -> wmono rsegs m m1 -> addressable m1 ost 32 ->
    munch [(spv - 2256, spv); (ost, ost + 32)] m1 m2 -> wmono rsegs m1 m2 ->
    ro_agree rsegs m2 -> stk rsegs m2 lo spv -> shadow_rw m2 ->
    rw_cells rsegs m2 ost [CB 32 (decl row)] ->
    evtF rsegs RNG
      (fun ms' => exists (t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82c24) (Z_to_bv 64 spv) x3 x4 t0'' t1'' t2'' x8 (Z_to_bv 64 A)
                       (Z_to_bv 64 1) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                       x18 (Z_to_bv 64 S) x20 (Z_to_bv 64 T) (Z_to_bv 64 ost) (Z_to_bv 64 (T + o))
                       (Z_to_bv 64 (o + T)) x25 x26 x27 t3'' t4'' t5'' t6'')
                  Fr (Z_to_bv 64 0x82c24) fcs None m' (seg_rom rsegs) /\
         munch [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\ stk rsegs m' lo spv /\
         bytes_at rsegs m' ost (decl row) /\ addressable m' ost 32 /\
         (forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] q ->
            exists b, mrd rsegs m' (wa q) = Some b))
      (MS (mkR (Z_to_bv 64 0x82c24) (Z_to_bv 64 spv) x3 x4 t0' t1' t2' x8 (Z_to_bv 64 A)
               (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
               x18 (Z_to_bv 64 S) x20 (Z_to_bv 64 T) (Z_to_bv 64 ost) (Z_to_bv 64 (T + o))
               (Z_to_bv 64 (o + T)) x25 x26 x27 t3' t4' t5' t6')
          Fr (Z_to_bv 64 0x82c24) fcs None m2 (seg_rom rsegs)).
Proof.
  intros x3 x4 x8 x18 x20 x25 x26 x27 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
    Fr fcs m m1 m2 S A T o ost spv lo row RNG
    HSlo HShi HSin Ho0 Ho1 Hoapp Hosh Hlo1 Hlo2 Hsp1 Hrlen MU1 WM1 Haddr1 MU2 WM2 RO2 ST2 SW2 RW2.
  assert (EAPP : APPMEM_END = 140737488355328) by reflexivity.
  assert (EHMB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (MUa : munch [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] m m2).
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU1]. intros x (Hx & _). cbn [outside]. split; [exact Hx | exact I].
    - eapply munch_weaken; [|exact MU2]. intros x (_ & Hx1 & Hx2 & _). cbn [outside].
      split; [exact Hx1|]. split; [exact Hx2 | exact I]. }
  assert (WMa : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  destruct RW2 as (((Hdlen & _) & Hdbb) & _).
  cbn [cells_bytes cbytes] in Hdbb. rewrite app_nil_r in Hdbb.
  assert (HINa : forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] q ->
            exists b, mrd rsegs m2 (wa q) = Some b).
  { intros q Hq Hno.
    assert (Hslot : ost <= q < ost + 32 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. destruct Hdbb as (_ & _ & Hb).
      pose proof (Hb (Z.to_nat (q - ost)) ltac:(rewrite Hdlen; lia)) as Hb0.
      replace (ost + Z.of_nat (Z.to_nat (q - ost))) with q in Hb0 by lia.
      destruct (nth_error (decl row) (Z.to_nat (q - ost))) as [b|] eqn:En;
        [exists b; exact Hb0 | apply nth_error_None in En; rewrite Hdlen in En; lia]. }
    assert (Hshq : S + 8 <= q < S + 12 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (SW2 q ltac:(replace q with (S + 8 + (q - S - 8)) by lia; apply HSin; lia))). }
    assert (Hwinq : spv - 2256 <= q < spv -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (proj2 (proj2 ST2) q ltac:(lia))). }
    destruct (Z_le_dec (S + 8) q) as [L1|L1]; destruct (Z_lt_dec q (S + 12)) as [L2|L2];
    destruct (Z_le_dec (spv - 2256) q) as [L3|L3]; destruct (Z_lt_dec q spv) as [L4|L4];
    destruct (Z_le_dec ost q) as [L5|L5]; destruct (Z_lt_dec q (ost + 32)) as [L6|L6];
    first [ apply Hshq; lia | apply Hwinq; lia | apply Hslot; lia
          | exfalso; apply Hno; cbn [outside]; repeat split; try exact I; lia ]. }
  assert (Haddr2 : addressable m2 ost 32).
  { apply (f34_addr_keep m1 m2 ost 32 Haddr1). intros a Ha. unfold mrd.
    rewrite (MU2 (wa (shadow_addr a))); [reflexivity|].
    assert (Hin : S + 8 <= shadow_addr a < S + 12) by (pose proof (Hosh (a - ost) ltac:(lia)) as Hp;
      replace (ost + (a - ost)) with a in Hp by lia; exact Hp).
    assert (Happa : app_mem a) by (replace a with (ost + (a - ost)) by lia; apply Hoapp; lia).
    assert (Hinsh : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Happa).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ Hinsh); lia).
    cbn [outside]. split; [|split; [|exact I]].
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      replace (shadow_addr a) with (ost + (shadow_addr a - ost)) by lia. apply Hoapp. lia. }
  apply evtF_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m2.
  split; [reflexivity|].
  split; [exact MUa|]. split; [exact WMa|]. split; [exact RO2|]. split; [exact SW2|].
  split; [exact ST2|]. split; [exact Hdbb|]. split; [exact Haddr2 | exact HINa].
Qed.
