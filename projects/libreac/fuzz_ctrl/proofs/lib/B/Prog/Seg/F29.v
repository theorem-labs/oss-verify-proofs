(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2004 of its 2120 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F30.v, with its module paths, addresses and numbers changed; 450 of its 544 lines of code are new or changed and 2026 lines of the source are left out. *)
(* Segment F29 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, libreac v1.9.0 image B): the join 0x82aa4-0x82ab8
   (slot-plan-asan-ubsan section 2 row F29, no call, no branch, no instrumented check). With s3 = S(fr) (the shadow
   byte of the frame base, FRA reg 19), the six instructions
     0x82aa4  sb s11,16(s3)      store the low byte of s11 (0xf8 "variable out of scope") to S(fr)+16
     0x82aa8  sb s11,17(s3)      .. S(fr)+17
     0x82aac  sb s11,20(s3)      .. S(fr)+20   (the shadow of fr+128..fr+167)
     0x82ab0  addi s6,zero,1     s6 := 1 (the frame-loop constant)
     0x82ab4  mv s9,s8           s9 := old s8  (the sum flag b2z(t_sum_ok), moved back into s9)
     0x82ab8  ld s8,272(s1)      s8 := [A+272] = k = t_k (reloaded into s8)
   fall through to 0x82abc (F30's entry). No FRA register (sp 2, gp 3, tp 4, s0 8, s1 9, s3 19, s10 26) changes; the
   three shadow stores stay inside the frame's FRAME_SHADOW = 392 shadow bytes [S(fr), S(fr)+392). The v1.9.0 move
   of the patched-image seg_F29 (a working branch 4131ff88f40): v1.9.0 inserts `addi s6,zero,1` and moves the
   sum flag through s8 -> s9 where the patched image moved the fill flag s8 -> s5 and fr + 176 s5 -> s6.

   Entry cut: the official Inv_B82aa4_at of lib/B/Prog/SlotInv.v (v1.9 pc 0x82aa4; FCUTP: s2 = phi, s4 = len,
   FTURN, LK, FTL, IFS (S j)), which F27 (r <> 0) and F28 (r = 0) reach. Exit cut: the official Inv_B82abc_at
   (v1.9 pc 0x82abc, F30's entry; FCUTP: LK, FTK, IFS (S j), the block spill [A+312]): the run gives FTK's s6 = 1,
   s9 = the sum flag (old s8) and s8 = k ([A+272]); FTL gives the fill-flag and k spills.
   The stores take mem_inv, which the cuts do not carry: the run is taken on the normalized memory and
   MemNorm.evt_normalize carries it back to the cut's memory, which has ro_agree (f29_evt_ro). FRA moves across the
   three stores by Tac_slot.sl_fr_meta with the heap invariant from SlotInv.lw_store (real-stack arm) or
   SlotInv.lw_fs_store (side-stack arm), ENT by Tac_slot.ent_store (f29_fra1). The frame's bytes, the spills, the
   turn's block at Phi (apart from the frame: F27.f27_blk) and the kind-name table are not frame-shadow bytes, so
   they and their shadow bytes keep their values. The single lazy-model run is in Tac_slot.sl_run_lib. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro Tac_fsfree F27.
Import ListNotations.
(* lib.B.Prog's chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy; this file's
   registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

(* ---- Pure helpers (bytes, shadow arithmetic), from a Theorem Labs lane's image-B F29 (18fad27a160) and the image-A twin
   lib/A/Prog/Seg/F29.v. *)

Lemma le1_byte : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma ba_present : forall m n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat i)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  intros m n. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [exact Ha|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b0 & Hb0).
    assert (Hrest : forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + 1 + Z.of_nat i)) = Some b).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as (b & Hb). exists b.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact Hb. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrest) as (bs & (Ha' & Hl' & Hb') & Hlen).
    exists (b0 :: bs). split; [|cbn [length]; lia].
    split; [exact Ha|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. exact Hb0.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hb'. cbn [length] in Hi. lia.
Qed.

Lemma ba_some : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa (a + i)) = Some b.
Proof.
  intros m a bs i (_ & _ & H) Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma sh_frame_of : forall fr k, 0 <= fr -> fr mod 8 = 0 -> 0 <= k ->
  shadow_addr (fr + 8 * k) = shadow_addr fr + k.
Proof. unfold shadow_addr. intros fr k H0 H8 Hk. Z.div_mod_to_equations. lia. Qed.

Lemma sh_frame : forall fr y k, 0 <= fr -> fr mod 8 = 0 -> 0 <= y -> shadow_addr y = shadow_addr fr + k ->
  fr + 8 * k <= y < fr + 8 * k + 8.
Proof. unfold shadow_addr. intros fr y k H0 H8 Hy E. Z.div_mod_to_equations. lia. Qed.

Lemma in_shadow_bnd : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

Lemma addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

Lemma fs_meta_ge : forall FS q, Tac_fs.fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold Tac_fs.fs_meta in H.
  destruct H as [H | [H | [[c [Hc Hr]] | [c [jj [Hc [Hj Heq]]]]]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. pose proof (Tac_fs.a_fs_flag_range FS c jj Hc Hj). lia.
Qed.

Lemma ag_bound : forall a, in_globals AF.frame_AG a -> 0x21140 <= a < 0xa0708.
Proof.
  intros a (lo & len & Hil & Hr). unfold AF.frame_AG in Hil. cbn [In] in Hil.
  repeat (destruct Hil as [E | Hil]; [injection E as <- <-; lia |]). destruct Hil.
Qed.

(* A spilled word at s1 + off read at the FRA spill base A (the existential base of spill is A, mod 2^64). *)
Lemma f29_spill : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold rg in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal (@bv_unsigned 64)) in HA'. rewrite !MState.unsigned_lit_wrap in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* ---- The run: three one-byte stores to S3+16/+17/+20, then addi s6,zero,1; mv s9,s8; ld s8,272(s1). *)
Lemma f29_evt :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 A kv : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x9 = Z_to_bv 64 A ->
    rw_cells rsegs m (S3 + 16) [CB 5 bs] -> bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 kv)) ->
    mem_inv rsegs m ->
    0 <= S3 -> S3 + 21 <= 2 ^ 64 -> S3 + 21 <= A -> 0 <= A -> A + 280 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) m',
         ms' = MS R Fr (Z_to_bv 64 0x82abc) fc None m' (seg_rom rsegs) /\
         getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
         getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
         getr R 25 = x24 /\ getr R 22 = Z_to_bv 64 1 /\ getr R 24 = Z_to_bv 64 kv /\
         munch [(S3 + 16, S3 + 21)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         exists cs, rw_cells rsegs m' (S3 + 16) cs /\ cells_size cs = 5%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82aa4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 A kv bs -> -> HRW Hspill HMI H0 H1 HSA H0A H1A.
  pose proof (munch_refl [(S3 + 16, S3 + 21)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. rewrite le1_byte. mem_after_store.
  step. rewrite le1_byte. mem_after_store.
  step. rewrite le1_byte. mem_after_store.
  step. step.
  match goal with H : bytes_at rsegs ?m3 (A + 272) _ |- _ =>
    assert (Hrd : ov_read_bytes rsegs m3 (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 kv)));
    [ pose proof (bytes_at_ov_read rsegs m3 (A + 272) _ 0 8 H ltac:(rewrite length_le8; lia)) as HH;
      cbn [Z.of_nat] in HH; rewrite Z.add_0_r, skipn_O in HH;
      rewrite firstn_all2 in HH by (rewrite length_le8; lia); exact HH
    | ] end.
  step.
  apply evt_done.
  match goal with |- context [MS ?R _ _ _ _ ?m3 _] => exists R, m3 end.
  split; [reflexivity|].
  simp_regs.
  do 13 (split; [reflexivity|]).
  split; [assumption|]. split; [assumption|]. split; [assumption|].
  match goal with H : rw_cells rsegs ?m3 (S3 + 16) ?cs |- _ => exists cs; split; [exact H | reflexivity] end.
Qed.

(* ---- Normalized-memory transfer (as a Theorem Labs lane's F30 f30s_evt_ro). The cuts carry ro_agree, not mem_inv; the run
   lemma f29_evt takes mem_inv, so it runs on `normalize rsegs m` (mem_inv_normalize) and MemNorm.evt_normalize
   carries it back to m. Every byte the run touches (the frame's shadow, the spill word) is at or above LOWMEM_END,
   where no byte is read-only (Tac_ro.ro_hi). *)
Lemma f29_rwc_norm : forall m a cs, ro_agree rsegs m -> rw_cells rsegs m a cs ->
  LOWMEM_END <= a -> a + Z.of_nat (cells_size cs) <= 2 ^ 64 -> rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs HR ((Hwf & Hb) & Hw) H1 H2. split; [split; [exact Hwf|]|].
  - apply bytes_at_normalize; assumption.
  - eapply wr_at_norm; [apply mem_rel_normalize; exact HR | exact Hw |].
    intros i Hi. apply Tac_ro.ro_hi. lia.
Qed.

Lemma f29_rwc_back : forall m m0 a cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 a _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 a _ HR Hw).
Qed.

(* f29_evt on the cut's own memory: ro_agree in place of mem_inv. *)
Lemma f29_evt_ro :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
          x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S3 A kv : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x9 = Z_to_bv 64 A ->
    rw_cells rsegs m (S3 + 16) [CB 5 bs] -> bytes_at rsegs m (A + 272) (le8 (Z_to_bv 64 kv)) ->
    ro_agree rsegs m ->
    LOWMEM_END <= S3 -> S3 + 21 <= 2 ^ 64 -> S3 + 21 <= A -> 0 <= A -> A + 280 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) m',
         ms' = MS R Fr (Z_to_bv 64 0x82abc) fc None m' (seg_rom rsegs) /\
         getr R 2 = x2 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
         getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
         getr R 25 = x24 /\ getr R 22 = Z_to_bv 64 1 /\ getr R 24 = Z_to_bv 64 kv /\
         munch [(S3 + 16, S3 + 21)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m' /\
         exists cs, rw_cells rsegs m' (S3 + 16) cs /\ cells_size cs = 5%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
               x29 x30 x31) Fr (Z_to_bv 64 0x82aa4) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 Fr fc m S3 A kv bs E19 E9 HRW Hspill HRO HS3 H1 HSA H0A H1A.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (HL : LOWMEM_END = 2147450880) by reflexivity.
  pose proof (f29_evt x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc (normalize rsegs m) S3 A kv bs E19 E9
    (f29_rwc_norm m _ _ HRO HRW ltac:(lia) ltac:(cbn; lia)) (bytes_at_normalize rsegs m _ _ HRO Hspill)
    (mem_inv_normalize rsegs m) ltac:(lia) H1 HSA H0A H1A) as HC.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply LE.evt_mono; [exact HN|].
  intros ms (s0' & (R & m0' & E & F2 & F3 & F4 & F8 & F9 & F18 & F19 & F20 & F26 & F27 & F25 & F22 & F24 &
                    MU & WM & MI' & cs & Hcs & Hcsl) & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists R, memX. split; [reflexivity|].
  do 13 (split; [assumption|]).
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  exists cs. split; [exact (f29_rwc_back memX m0' _ _ Hmr Hcs) | exact Hcsl].
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Local Abbreviation STKLO mem md := (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).

(* The FRA facts this file reads, projected by name (tauto), not by position. *)
Lemma f29_fra_parts : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists A sp,
    AsanRTInv.RT sp mem md /\ AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md /\
    m_halted md = None /\ AC.aspZ regs = sp /\ STKLO mem md <= g_S g - AF.SLOT_STACK /\
    rg regs 9 A /\ rg regs 19 (Sfr fr) /\ fr mod 32 = 0 /\ A <= g_S g /\ sp <= A /\ A + 448 <= g_S g /\
    g_S g - 4096 < sp /\ g_S g < APPMEM_END /\
    (exists sh, bytes_at rsegs mem (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) /\
    stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g) /\
    (forall a, in_globals AF.frame_AG a -> addressable mem a 1) /\ ro_agree rsegs mem /\
    ((forall a, fr <= a < fr + FRAME_BYTES -> STKLO mem md <= a < APPMEM_END) \/
     (forall a, fr <= a < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a)).
Proof.
  intros g fr hb regs mem md HFRA. destruct HFRA as (A & sp & s5 & HF). exists A, sp. tauto.
Qed.

(* The frame's place (as a Theorem Labs lane's f30_fra_loc): the side stack FS is the word at tp (FSFREE), below stklo; the
   frame is on the real stack (at or above stklo) or inside FS (FRA's side arm), and is application memory at or
   above the image top GT. *)
Lemma f29_fra_loc : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
    FS + AC.FS_SIZE <= STKLO mem md /\ (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    AC.GT <= fr /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\
    ((forall a, fr <= a < fr + FRAME_BYTES -> STKLO mem md <= a < APPMEM_END) \/
     (forall a, fr <= a < fr + FRAME_BYTES -> FS <= a < FS + AC.FS_SIZE)).
Proof.
  intros g fr hb regs mem md HFRA.
  destruct (f29_fra_parts g fr hb regs mem md HFRA)
    as (A & sp & _ & HAH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hloc).
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Happ).
  destruct (Tac_fsfree.fra_fsfree B APIf ra g fr hb regs mem md HFRA) as (FS & Hwm & HFSr & _).
  destruct (lw_fs_place (APIf rc) _ mem md FS HAH Hwm HFSr) as [_ HFSlo _ HFSapp].
  exists FS. split; [exact Hwm|]. split; [exact HFSr|]. split; [exact HFSlo|]. split; [exact HFSapp|].
  split; [exact HGTfr|]. split; [exact Happ|].
  destruct Hloc as [Hreal | Hfs]; [left; exact Hreal | right].
  intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hwb & Hab).
  assert (Eb : b = FS).
  { apply (Tac_fsfree.fsf_wm_uniq mem (AC.as_tp AC.ASYMS) b FS Hwb Hwm Hbr HFSr);
      unfold AC.as_tp, AC.ASYMS; cbn; lia. }
  subst b. exact Hab.
Qed.

(* FRA and ENT across the three shadow stores (the frame's shadow bytes [S(fr)+16, S(fr)+21)): Tac_slot.sl_fr_meta,
   with the heap invariant from SlotInv.lw_store (real-stack arm: each written byte is the shadow byte of a
   frame granule, a_store_ok) or SlotInv.lw_fs_store with Tac_fs.a_fs_ok_pres (side-stack arm: the shadow of
   FS bytes, apart from the FakeStack's metadata). ENT moves by Tac_slot.ent_store (every written byte is a byte of
   the frame's shadow), with its stack bounds and ownership half from the same law. *)
Lemma f29_fra1 : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  munch [(Sfr fr + 16, Sfr fr + 21)] mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall a, 0 <= a < 2 ^ 64 -> (exists b, mbyte rsegs mem a = Some b) -> (exists b, mbyte rsegs mem' a = Some b)) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  FRA B APIf ra g fr hb regs mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md HFRA HENT MU WM HroM PM Hshnew.
  destruct (f29_fra_loc g fr hb regs mem md HFRA)
    as (FS & Hwm & HFSr & HFSlo & HFSapp & HGTfr & Happ & Hloc2).
  destruct (f29_fra_parts g fr hb regs mem md HFRA)
    as (A & sp & _ & HAH & _ & Haspz & Hstklo & Hr9 & _ & Hfrm & HAS & Hspa & _ & HS4 & HAPP & _ & Hwin & HAG &
        _ & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHBv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (Hfr0 : 0 <= fr) by (unfold AC.GT in HGTfr; lia).
  assert (Hfr8 : fr mod 8 = 0) by (clear -Hfrm; Z.div_mod_to_equations; lia).
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HAhi : HIGHMEM_BEG <= A) by lia.
  (* the shadow bytes the stores touch are the shadow bytes of the frame granules [fr+128, fr+168) *)
  assert (HWsh : forall k, 16 <= k <= 20 -> Sfr fr + k = shadow_addr (fr + 8 * k) /\ in_shadow (Sfr fr + k)).
  { intros k Hk.
    assert (E : shadow_addr (fr + 8 * k) = Sfr fr + k) by (unfold Sfr; apply sh_frame_of; lia).
    split; [symmetry; exact E | rewrite <- E; apply shadow_of_app; apply Happ; lia]. }
  pose proof (in_shadow_bnd _ (proj2 (HWsh 16 ltac:(lia)))) as HSb.
  pose proof (in_shadow_bnd _ (proj2 (HWsh 20 ltac:(lia)))) as HSc.
  (* an application byte, and every byte at or above HIGHMEM_BEG, is outside the write set *)
  assert (HWapp : forall a, app_mem a -> outside [(Sfr fr + 16, Sfr fr + 21)] a).
  { intros a Ha. cbn [outside]. split; [|exact I].
    intros [H1 H2]. destruct (HWsh (a - Sfr fr) ltac:(lia)) as (_ & Hin).
    replace (Sfr fr + (a - Sfr fr)) with a in Hin by lia. exact (app_not_shadow a Ha Hin). }
  assert (HWhi : forall a, HIGHMEM_BEG <= a -> outside [(Sfr fr + 16, Sfr fr + 21)] a).
  { intros a Ha. cbn [outside]. split; [lia | exact I]. }
  (* the shadow byte of an address outside [fr+128, fr+168) is outside the write set *)
  assert (HnotW : forall y, 0 <= y -> ~ (fr + 128 <= y < fr + 168) ->
                    outside [(Sfr fr + 16, Sfr fr + 21)] (shadow_addr y)).
  { intros y Hy0 Hy. cbn [outside]. split; [|exact I]. intros Hin.
    pose proof (sh_frame fr y (shadow_addr y - Sfr fr) Hfr0 Hfr8 Hy0 ltac:(unfold Sfr; lia)) as Hz.
    apply Hy. lia. }
  assert (HWM : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (HD : rt_disjoint [(Sfr fr + 16, Sfr fr + 21)]).
  { unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN.
    unfold LOWMEM_END in HSb. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
  (* AH, stklo / stkhi and the runtime's ownership across the write *)
  assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                 STKLO mem' md = STKLO mem md /\
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                 (forall a, AC.a_in_img a ->
                    AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
                    AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a)).
  { destruct Hloc2 as [Hreal | Hfs].
    - assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
        ~ AC.a_store_ok (hb ++ g_H g) (STKLO mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
        cbn [outside]. split; [|exact I].
        intros Hc. apply Hns. destruct (HWsh (a - Sfr fr) ltac:(lia)) as (E & _).
        unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (a - Sfr fr)).
        split; [replace (Sfr fr + (a - Sfr fr)) with a in E by lia; exact E|].
        right; left. apply Hreal. lia. }
      destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HWM)
        as [HAH' Hown HSTK HSTKHI].
      split; [exact HAH'|]. split; [exact HSTK|]. split; [exact HSTKHI|].
      intros a _ Ho. exact (proj2 (Hown a) Ho).
    - assert (Hmeta : forall q, Tac_fs.fs_meta FS q -> outside [(Sfr fr + 16, Sfr fr + 21)] q).
      { intros q Hq. pose proof (Tac_fs.fs_meta_below FS q Hq) as Hb.
        apply HWapp, HFSapp. split; [exact (fs_meta_ge FS q Hq) | lia]. }
      assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
        ~ AC.a_store_ok (hb ++ g_H g) (STKLO mem md) a -> ~ (FS <= a < FS + AC.FS_SIZE) ->
        ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
        mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { intros a Ha Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by lia.
        cbn [outside]. split; [|exact I].
        intros Hc. apply Hnsh. destruct (HWsh (a - Sfr fr) ltac:(lia)) as (E & _).
        exists (fr + 8 * (a - Sfr fr)). split; [apply Hfs; lia|].
        replace (Sfr fr + (a - Sfr fr)) with a in E by lia. exact E. }
      assert (Hfsok : AC.a_fs_ok mem' FS).
      { refine (Tac_fs.a_fs_ok_pres _ mem mem' FS _ MU HWM PM Hmeta ltac:(lia) ltac:(lia)).
        exact (lw_fs_ok (APIf rc) (hb ++ g_H g) mem md FS HAH Hwm HFSr). }
      destruct (lw_fs_store (APIf rc) (hb ++ g_H g) mem mem' md FS HAH Hwm HFSr HstoreC HWM Hfsok)
        as [HAH' Hown HSTK HSTKHI].
      split; [exact HAH'|]. split; [exact HSTK|]. split; [exact HSTKHI|].
      intros a _ Ho. exact (proj2 (Hown a) Ho). }
  destruct HAHS as (HAH' & HSTK & HSTKHI & Hown).
  (* A in register 9 is the spill base *)
  assert (HregA : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r. unfold rg in Hr9. rewrite Hr9 in HA'. apply (f_equal (@bv_unsigned 64)) in HA'.
    rewrite !MState.unsigned_lit in HA' by lia. lia. }
  split.
  2: { eapply ent_store with (W := [(Sfr fr + 16, Sfr fr + 21)]) (fr := fr) (regs := regs);
         [exact HENT | exact HFRA | exact MU | | exact HSTK | exact HSTKHI | exact Hown].
       intros x Hx.
       destruct (Z_le_gt_dec (Sfr fr + 16) x) as [L1|L1]; [destruct (Z_lt_ge_dec x (Sfr fr + 21)) as [L2|L2]|].
       - right; right; right. lia.
       - left. cbn [outside]. split; [lia | exact I].
       - left. cbn [outside]. split; [lia | exact I]. }
  apply (sl_fr_meta B APIf ra empty FF g fr hb regs regs mem mem' md
           [(Sfr fr + 16, Sfr fr + 21)] HFRA MU WM HroM HD HAH' HSTK Happ HGTfr Hshnew);
    try reflexivity.
  - intros x _ _ Hx2. cbn [outside]. split; [lia | exact I].
  - intros A' HA' HA'r x Hx. rewrite (HregA A' HA' HA'r) in Hx. apply HWhi. lia.
  - intros x Hx. apply HWhi. lia.
  - intros A' HA' HA'r x Hx. rewrite (HregA A' HA' HA'r) in Hx. apply HWhi. lia.
  - intros x Hx. left. apply HWhi. lia.
  - intros a Hin. pose proof (ag_bound a Hin) as Hab.
    apply (addr_keep [(Sfr fr + 16, Sfr fr + 21)] mem mem' a 1 (HAG a Hin) MU).
    intros i Hi. apply HnotW; [lia|]. unfold AC.GT in HGTfr. lia.
Qed.

Lemma seg_F29 : forall j, Hat B APIf ra (Inv_B82abc_at B APIf ra) j -> Hat B APIf ra (Inv_B82aa4_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j Hexit g c HInv.
  unfold Inv_B82aa4_at, FCUTP, CUTST in HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & Hr18 & Hr20 & HFT & HLK &
    HFTL & HIFS).
  subst c. pose proof (proj1 FF) as SEGS.
  destruct HFTL as (Hr21 & Hs184 & Hsp272 & Hr24e & Hs312).
  destruct (Tac_ro.fli_mem _ _ _ _ (proj2 (proj2 (proj2 HLK))))
    as (Had2624 & Hstkfr & HRid & HRfg & HKNT & Hfst).
  destruct (f29_fra_parts g fr _ regs mem md HFRA)
    as (A & sp & HRT & HAH & Hhalt & Haspz & Hstklo & Hr9 & Hr19 & Hfrm & HAS & Hspa & HA448 & HS4 & HAPP &
        (sh & Hsh & Hshl) & Hwin & HAG & Hro & _).
  rewrite FRAME_SHADOW_val in Hshl. change (Z.to_nat 392) with 392%nat in Hshl.
  destruct (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Hfrapp).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHBv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HAhi : HIGHMEM_BEG <= A) by lia.
  assert (HAbd : 0 <= A /\ A + 448 <= 2 ^ 64) by lia.
  assert (Hfr0 : 0 <= fr) by (unfold AC.GT in HGTfr; lia).
  assert (Hfr8 : fr mod 8 = 0) by (clear -Hfrm; Z.div_mod_to_equations; lia).
  (* the frame's FRAME_SHADOW = 392 shadow bytes: shadow bytes of frame granules *)
  assert (HSh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW ->
    in_shadow x /\ shadow_addr (fr + 8 * (x - Sfr fr)) = x /\ fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = x) by (rewrite sh_frame_of by lia; unfold Sfr; lia).
    split; [rewrite <- E; apply shadow_of_app, Hfrapp; lia | split; [exact E | lia]]. }
  pose proof (in_shadow_bnd _ (proj1 (HSh (Sfr fr) ltac:(lia)))) as HS3a.
  pose proof (in_shadow_bnd _ (proj1 (HSh (Sfr fr + 391) ltac:(lia)))) as HS3b.
  (* the three store targets as one 5-byte cell of the shadow list *)
  pose proof (ba_sub mem (Sfr fr) sh 16 5 Hsh ltac:(lia)) as Hsh5. change (Z.of_nat 16) with 16 in Hsh5.
  assert (Hwr5 : wr_at rsegs mem (Sfr fr + 16) 5).
  { split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj1 (RT_shadow_rw _ _ _ HRT (Sfr fr + 16 + i) (proj1 (HSh (Sfr fr + 16 + i) ltac:(lia))))). }
  assert (HRW : rw_cells rsegs mem (Sfr fr + 16) [CB 5 (firstn 5 (skipn 16 sh))]).
  { split; [split|].
    - cbn [cells_wf cell_wf]. split; [rewrite length_firstn, length_skipn; lia | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hsh5.
    - cbn [cells_size csize Nat.add]. exact Hwr5. }
  pose proof (f29_spill regs mem 272 (t_k (g_in g) j) A Hsp272 Hr9 (proj1 HAbd) (proj2 HAbd) ltac:(lia)) as Hq272.
  unfold q64 in Hq272.
  rewrite SEGS.
  (* The one lazy-model run of this segment: Tac_slot.sl_run_lib (AsanLift.evt_SR_canon_lazy) over f29_evt_ro. It
     writes the three frame-shadow bytes S(fr)+16, +17, +20 (inside [S(fr)+16, S(fr)+21), S(fr) = (fr >> 3) +
     0x7fff8000) and reads the spill word [s1+272, s1+280) for ld s8,272(s1); nothing else is read or written. *)
  apply (sl_run_lib regs (Z_to_bv 64 0x82aa4) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82abc /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 26 = getr regs 26 /\
       getr R0 27 = getr regs 27 /\
       getr R0 25 = getr regs 24 /\ getr R0 22 = Z_to_bv 64 1 /\ getr R0 24 = Z_to_bv 64 (t_k (g_in g) j) /\
       munch [(Sfr fr + 16, Sfr fr + 21)] mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       exists cs, rw_cells rsegs mem' (Sfr fr + 16) cs /\ cells_size cs = 5%nat)
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f29_evt_ro with (m := mem) (S3 := Sfr fr) (A := A) (kv := t_k (g_in g) j);
        [ unfold rg in Hr19; exact Hr19 | unfold rg in Hr9; exact Hr9 | exact HRW | exact Hq272 | exact Hro
        | lia | lia | lia | lia | lia ]. }
    { intros ms' (R & m' & E & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E26 & E27 & E25 & E22 & E24 &
                  MU & WM & MI' & cs & Hcs & Hcsl).
      exists R, (Z_to_bv 64 0x82abc), m'. split; [exact E|].
      split; [reflexivity|].
      do 13 (split; [assumption|]).
      split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. exists cs. split; [exact Hcs | exact Hcsl]. }
  - intros R0 pc' mem' regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er26 & Er27 & Er25 & Er22 & Er24 & MU & WM & HroM &
       cs & Hcs & Hcsl) Hreg Hmat.
    subst pc'.
    assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (F20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fe27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (F25 : getr regs' 25 = getr regs 24) by (rewrite Hreg; exact Er25).
    assert (F22 : getr regs' 22 = Z_to_bv 64 1) by (rewrite Hreg; exact Er22).
    assert (F24 : getr regs' 24 = Z_to_bv 64 (t_k (g_in g) j)) by (rewrite Hreg; exact Er24).
    set (W := [(Sfr fr + 16, Sfr fr + 21)]) in *.
    assert (HWapp : forall x, app_mem x -> outside W x).
    { intros x Hx. subst W. cbn [outside]. split; [|exact I]. intros Hin.
      exact (app_not_shadow x Hx (proj1 (HSh x ltac:(lia)))). }
    assert (HWhi : forall x, HIGHMEM_BEG <= x -> outside W x).
    { intros x Hx. subst W. cbn [outside]. split; [lia | exact I]. }
    assert (HWsh2 : forall x, ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) -> outside W x).
    { intros x Hx. subst W. cbn [outside]. split; [|exact I]. lia. }
    assert (HnotW : forall y, 0 <= y -> ~ (fr + 128 <= y < fr + 168) -> outside W (shadow_addr y)).
    { intros y Hy0 Hy. subst W. cbn [outside]. split; [|exact I]. intros Hin.
      pose proof (sh_frame fr y (shadow_addr y - Sfr fr) Hfr0 Hfr8 Hy0 ltac:(unfold Sfr; lia)) as Hz.
      apply Hy. lia. }
    (* the new shadow list and the presence of every byte *)
    assert (HnewP : forall x, Sfr fr + 16 <= x < Sfr fr + 21 -> exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. destruct Hcs as ((Hwf & Hba) & _).
      pose proof (cells_bytes_length cs Hwf) as Hlen.
      replace x with (Sfr fr + 16 + (x - (Sfr fr + 16))) by lia.
      apply (ba_some mem' (Sfr fr + 16) (cells_bytes cs)); [exact Hba | rewrite Hlen, Hcsl; cbn; lia]. }
    assert (HpresM : forall x, 0 <= x < 2 ^ 64 -> (exists b, mrd rsegs mem (wa x) = Some b) ->
      exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx Hp. destruct (Z_le_gt_dec (Sfr fr + 16) x); [destruct (Z_lt_ge_dec x (Sfr fr + 21))|].
      - apply HnewP. lia.
      - unfold mrd in *. rewrite MU; [exact Hp|]. rewrite wa_unsigned by lia. subst W. cbn [outside].
        split; [lia | exact I].
      - unfold mrd in *. rewrite MU; [exact Hp|]. rewrite wa_unsigned by lia. subst W. cbn [outside].
        split; [lia | exact I]. }
    assert (Hsh' : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { rewrite FRAME_SHADOW_val. change (Z.to_nat 392) with 392%nat.
      apply ba_present; [lia | lia |].
      intros i Hi. apply HpresM; [lia|].
      apply (ba_some mem (Sfr fr) sh); [exact Hsh | rewrite Hshl; lia]. }
    assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
      exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq Hb. destruct (Z_le_gt_dec (Sfr fr + 16) q); [destruct (Z_lt_ge_dec q (Sfr fr + 21))|].
      - destruct (HnewP q ltac:(lia)) as (b & Hb2). unfold mrd, mbyte, wa in *.
        destruct (mem' (Z_to_bv 64 q)) as [b'|] eqn:Em; [exists b'; reflexivity|]. exists b. exact Hb2.
      - unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
        rewrite MState.unsigned_lit by lia. subst W. cbn [outside]. split; [lia | exact I].
      - unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
        rewrite MState.unsigned_lit by lia. subst W. cbn [outside]. split; [lia | exact I]. }
    (* FRA and ENT across the stores (f29_fra1), then to regs' and md' *)
    destruct (f29_fra1 g fr _ regs mem mem' md HFRA HENT MU WM HroM Hpres Hsh')
      as (HFRA1 & HENT1).
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md')
      by (apply (sl_fra_move B APIf ra g fr _ regs regs' mem' md md' HFRA1); assumption).
    (* every spill below s1 + 448 is above HIGHMEM_BEG, so outside W *)
    assert (Hspk : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hsp.
      pose proof (f29_spill regs mem off v A Hsp Hr9 (proj1 HAbd) (proj2 HAbd) Hoff) as Hq.
      exists A. split; [unfold rg; rewrite F9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8. intros x Hx.
      apply HWhi. lia. }
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem', md', fr. split; [reflexivity|]. split; [exact HFRA''|].
    split; [eapply ent_mat; [exact HENT1 | exact Hmat]|].
    split; [exact Hgn|]. split; [exact Hj|].
    (* HB: the block bytes (phi, a_size len) are app memory apart from the frame (F27.f27_blk), so their shadow
       bytes are not the frame's *)
    destruct HHB as (Hphine & Hphad).
    assert (Hphapp : forall i, 0 <= i < AC.a_size (flen g j) -> app_mem (phi + i)).
    { intros i Hi. destruct Hphad as (_ & _ & _ & HA2). destruct (HA2 i Hi) as (Hap & _). exact Hap. }
    assert (HInb : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
      by (apply in_or_app; left; left; reflexivity).
    assert (Hphifr : forall i, 0 <= i < AC.a_size (flen g j) -> ~ (fr <= phi + i < fr + FRAME_BYTES)).
    { intros i Hi.
      exact (proj1 (F27.f27_blk B APIf ra g fr _ regs mem md phi _ (phi + i) HFRA HInb ltac:(lia))). }
    split.
    { split; [exact Hphine|]. apply (addr_keep W mem mem' phi _ Hphad MU).
      intros i Hi. apply HnotW.
      - pose proof (Hphapp i Hi) as Ha. unfold app_mem in Ha. lia.
      - intros Hc. apply (Hphifr i Hi). lia. }
    split; [unfold rg in *; rewrite F18; exact Hr18|].
    split; [unfold rg in *; rewrite F20; exact Hr20|].
    (* FTURN: the spills and the frame bytes at Phi (app memory) are outside the shadow stores *)
    split.
    { apply (Tac_ro.turn_munch g j phi regs regs' W mem mem' HFT);
        [intros off v Hoff Hsp; exact (Hspk off v ltac:(lia) Hsp) | exact MU |].
      intros x Hx. apply HWapp.
      assert (Hi : 0 <= x - phi < AC.a_size (flen g j)) by (unfold AC.a_size, flen; lia).
      pose proof (Hphapp (x - phi) Hi) as Hap. replace (phi + (x - phi)) with x in Hap by lia. exact Hap. }
    (* LK: the frame's facts, the spills and the kind-name table (image data below the shadow map, and its shadow
       bytes are not the frame's) *)
    split.
    { apply (Tac_ro.lk_keep g fr j regs regs' mem mem' HLK).
      - pose proof (proj1 (proj2 (proj2 (proj2 HLK)))) as H27. unfold rg in *. rewrite Fe27. exact H27.
      - apply (addr_keep W mem mem' (fr + 2624) 6 Had2624 MU). intros i Hi. apply HnotW; lia.
      - eapply (LFr.stk_transport rsegs W mem mem' fr (fr + FRAME_BYTES)); [exact Hstkfr | exact MU | exact WM |].
        intros x Hx. left. apply HWapp, Hfrapp. exact Hx.
      - apply (addr_keep W mem mem' (fr + 2688) 38 HRid MU). intros i Hi. apply HnotW; lia.
      - apply (addr_keep W mem mem' (fragb fr) 72 HRfg MU). intros i Hi. apply HnotW; unfold fragb in *; lia.
      - assert (HKL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
        split.
        + eapply fl_bytes; [exact (proj1 HKNT) | exact MU |]. rewrite HKL.
          intros x Hx. apply HWsh2. unfold KNC.KIND_NAME in Hx. lia.
        + apply (addr_keep W mem mem' KNC.KIND_NAME 112 (proj2 HKNT) MU).
          intros i Hi. apply HnotW; unfold KNC.KIND_NAME, AC.GT in *; lia.
      - apply (addr_keep W mem mem' (fr + 2880) 40 Hfst MU). intros i Hi. apply HnotW; lia.
      - pose proof (proj1 (proj2 (proj2 HLK))) as HOUR. unfold OURb in *.
        eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
        intros x Hx. apply HWapp, Hfrapp. change (Z.of_nat 6) with 6 in Hx. lia.
      - intros off v Hoff Hsp. exact (Hspk off v ltac:(lia) Hsp). }
    (* FTK: the fill-flag spill, s6 = 1 (the inserted addi), s8 = k, the k spill, s9 = the sum flag (old s8) *)
    split.
    { split; [exact (Hspk 184 _ ltac:(lia) Hs184)|].
      split; [unfold rg; rewrite F22; reflexivity|].
      split; [unfold rg; rewrite F24; reflexivity|].
      split; [exact (Hspk 272 _ ltac:(lia) Hsp272)|].
      unfold rg in *; rewrite F25; exact Hr24e. }
    split.
    { apply (Tac_ro.ifs_munch g fr (S j) regs regs' W mem mem' HIFS MU).
      - intros x Hx. apply HWapp, Hfrapp. exact Hx.
      - apply (addr_keep W mem mem' (fr + 2880) 40 Hfst MU). intros i Hi. apply HnotW; lia. }
    exact (Hspk 312 _ ltac:(lia) Hs312).
Qed.

End S.
