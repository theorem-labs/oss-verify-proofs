(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 1011 of its 1078 lines of code are new or changed and 944 lines of the source are left out. *)
(* Segment A1 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the prologue and the
   side-stack frame request, 0x81018 .. 0x8108c, from the slot pre Inv_ENTRY to the cut Inv_B81090 (the `mv s8,a0`
   right after `jal frame_alloc_6`). The run (a1_pro, then the
   request): the 448-byte save area, the 13 caller registers spilled at [S - 104, S), s0 = S (the entry sp),
   sp = s1 = A = (S - 448) & -32, s2 = n and s6 = p, the switch word D = 1 and the shadow offset s10 = ASAN_K loaded
   from the runtime's cells (the D = 0 branch `beqz a2,0x81098` is not taken), and the class-6 frame request
   `jal frame_alloc_6` (0x3db94) with a0 = 3136 (0x81084 / 0x81088 lui a0,1; addiw a0,a0,-960), taken on its contract
   asan_stack_malloc_6_contract (a Section Hypothesis). That contract is stated on the lib/Lib engine and needs
   mem_inv, so the segment is stepped with the lib/Lib engine on the normalized memory and carried back to the real
   memory by MemNorm.evt_normalize + AsanLift.evt_SR_canon_lazy (a1_run). The request writes only the slot window
   below S, the side stack FS and its shadow (A1W), so the runtime cells (RT_meta_write), the heap invariant
   (a_laws_fs_store with the side stack's state a_fs_ok, a1_fs_ok_call), the image bytes, errno and the registered
   globals' shadow are kept, and the exit cut's pre-frame subset PREF holds at sp = A with the request result r in
   a0 (0, or a 32-aligned class-6 frame in the side stack FS at or above FS + 6328320, with its FakeStack frame
   record FSREC: the flag byte 1 and the flag's address in the slot's last word, a1_rec). Inv_ENTRY pins the ghost's
   entry sp (AC.aspZ (g_regs g) = g_S g), so the exit cut is the one of the ghost itself. The exit also carries
   ENT (push 5c): it holds of the entry state by ent_entry and moves across the run with ent_munch (no byte of an
   entry block, of the image, of the stack at or above S, or of the shadow of those is in A1W) and ent_mat. PREF's
   input facts (the input bytes at p and, for n > 0, the block (p, n) live and addressable) come from the entry
   pre's blk_data and input-block clause and move across the run with fra_in_keep_sh. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_fsfree.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ClassConsDef.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.AZ.Spec Require AsanCtrl.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.Spec.StrFun.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module BzSF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.Spec.StrFun.
(* This file steps on the lib/Lib engine, whose Frame.munch / Frame.outside are the lib.Lib copies; the ENT
   transports of Seg/Tac_slot speak the lib/B/Tk/UL copies (same bodies). Name them to convert across. *)
Module ULFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Frame.

(* ---------------- the image's top, and the addresses above it ---------------- *)

Lemma a1_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* Every loaded segment of the image ends at or below GT = 0x5fe000 (the runtime's heap floor). *)
Lemma a1_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma a1_find_seg : forall (l : list Segment) x n seg, find_segment l x n = Some seg ->
  In seg l /\ Z.of_N (seg_base seg) <= x /\ x + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros x n seg H; cbn in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1, E2.
    split; [left; reflexivity | lia].
  - destruct (IH x n seg H) as (H1 & H2). split; [right; exact H1 | exact H2].
Qed.

Lemma a1_ro_false : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. unfold ro_addr. rewrite (unsigned_lit a) by lia.
  destruct (find_segment rsegs a 1) as [s|] eqn:E; [|reflexivity]. exfalso.
  destruct (a1_find_seg rsegs a 1 s E) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ rsegs) a1_img_top s Hin) as HB. apply Z.leb_le in HB. lia.
Qed.

Lemma a1_shadow_hi : forall a, in_shadow a -> 0x5fe000 <= a < 2 ^ 64.
Proof.
  intros a Ha. pose proof (in_shadow_range a Ha).
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia.
Qed.

Lemma a1_rt_disjoint_gt : forall A Bb, 0x5fe000 <= A -> AsanRTInv.rt_disjoint [(A, Bb)].
Proof.
  intros A Bb HA. unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
    RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
    RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
  cbn [disjoint_from]. repeat split; try exact I; left; lia.
Qed.

Lemma a1_all_app_high : forall A Bb, HIGHMEM_BEG <= A -> Bb <= APPMEM_END -> all_app [(A, Bb)].
Proof.
  intros A Bb HA HB. cbn [all_app]. split; [|exact I]. intros x Hx. unfold app_mem. right.
  unfold HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* ---------------- mem_rel transport (the real memory vs the normalized one) ---------------- *)

Lemma a1_bytes_rel1 : forall m m0 a bs, mem_rel rsegs m m0 -> bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs.
Proof. intros m m0 a bs H Hb. exact (proj1 (bytes_at_rel rsegs m m0 a bs H) Hb). Qed.
Lemma a1_bytes_rel2 : forall m m0 a bs, mem_rel rsegs m m0 -> bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs.
Proof. intros m m0 a bs H Hb. exact (proj2 (bytes_at_rel rsegs m m0 a bs H) Hb). Qed.

Lemma a1_mbyte_rel : forall m m0 a, mem_rel rsegs m m0 -> mbyte rsegs m0 a = mbyte rsegs m a.
Proof. intros m m0 a H. symmetry. exact (mbyte_rel rsegs m m0 a H). Qed.

Lemma a1_word_rel1 : forall m m0 a v, mem_rel rsegs m m0 -> word_mem rsegs m a v -> word_mem rsegs m0 a v.
Proof. intros m m0 a v H Hw k Hk. rewrite (a1_mbyte_rel m m0 _ H). exact (Hw k Hk). Qed.
Lemma a1_word_rel2 : forall m m0 a v, mem_rel rsegs m m0 -> word_mem rsegs m0 a v -> word_mem rsegs m a v.
Proof. intros m m0 a v H Hw k Hk. rewrite <- (a1_mbyte_rel m m0 _ H). exact (Hw k Hk). Qed.

Lemma a1_wr_rel : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (writable_at rsegs m a <-> writable_at rsegs m0 a).
Proof.
  intros m m0 a H Ha. unfold writable_at.
  rewrite (wview_rel_rw rsegs m m0 (Z_to_bv 64 a) H (a1_ro_false a Ha)). tauto.
Qed.

Ltac a1_tb TB :=
  repeat (lazymatch goal with |- bytes_at _ _ _ _ /\ _ => split; [apply TB; assumption|] end);
  apply TB; assumption.

Lemma a1_RT_rel : forall m m0 sp md, mem_rel rsegs m m0 -> AsanRTInv.RT sp m md -> AsanRTInv.RT sp m0 md.
Proof.
  intros m m0 sp md HR H.
  assert (TB : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs Hb; exact (a1_bytes_rel1 m m0 a bs HR Hb)).
  destruct H as (HC & HSR & HO & HF & HU & HL & HI & HX & HFS).
  apply AsanRTInv.RT_intro.
  - unfold asan_cells in *.
    destruct HC as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?). a1_tb TB.
  - intros a Ha. destruct (HSR a Ha) as [Hw Hb].
    pose proof (a1_shadow_hi a Ha) as Hr. split.
    + rewrite (wview_rel_rw rsegs m m0 (wa a) HR (a1_ro_false a Hr)). exact Hw.
    + destruct Hb as [b Hb]. exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
  - unfold asan_opt_cells in *. destruct HO as (?&?&?&?). a1_tb TB.
  - unfold asan_cf_cells in *. destruct HF as (?&?&?&?&?&?&?&?). a1_tb TB.
  - unfold asan_uw_cells in *. destruct HU as (?&?&?&?&(c&Hc)).
    split; [apply TB; assumption|]. split; [apply TB; assumption|]. split; [apply TB; assumption|].
    split; [apply TB; assumption|]. exists c. apply TB. exact Hc.
  - unfold asan_real_cells in *. rewrite Forall_forall in *. intros p Hp. apply TB. exact (HL p Hp).
  - unfold asan_im_cells in *. destruct HI as (H1 & (t & Ht)). split; [apply TB; exact H1|].
    exists t. apply TB. exact Ht.
  - unfold asan_exit_cells in *. destruct HX as (?&?&?&?). a1_tb TB.
  - unfold asan_fs_cells in *.
    destruct HFS as (?&?&?&?&(fs & Hfs & Hfsok)&(db & Hdb & Hdb0 & Hdba)).
    split; [apply TB; assumption|]. split; [apply TB; assumption|]. split; [apply TB; assumption|].
    split; [apply TB; assumption|].
    split; [exists fs; split; [apply TB; exact Hfs | exact Hfsok]|].
    exists db. split; [apply TB; exact Hdb | split; [exact Hdb0 | exact Hdba]].
Qed.

(* The side stack's state a_fs_ok (Contract.v), taken apart in this one lemma only (a Theorem Labs lane via a Theorem Labs lane 15:32Z: one
   local lemma per Contract.v law per file, so that a new conjunct breaks this line and no use site). *)
Lemma a1_fs_ok_iff : forall m FS, AC.a_fs_ok m FS <->
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs m a /\ exists b, mbyte rsegs m a = Some b) /\
  word_mem rsegs m (FS + 88) 20 /\ mbyte rsegs m (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs m (AC.a_fs_hint FS c) h) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs m (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/ mbyte rsegs m (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)).
Proof.
  intros m FS. unfold AC.a_fs_ok. split.
  - intros (P1 & P2 & P3 & P4 & P5). exact (conj P1 (conj P2 (conj P3 (conj P4 P5)))).
  - intros (P1 & P2 & P3 & P4 & P5). exact (conj P1 (conj P2 (conj P3 (conj P4 P5)))).
Qed.

Lemma a1_fs_rel : forall m m0 FS, mem_rel rsegs m m0 -> 0x5fe000 <= FS -> FS + AC.FS_SIZE <= 2 ^ 64 ->
  AC.a_fs_ok m FS -> AC.a_fs_ok m0 FS.
Proof.
  intros m m0 FS HR HFS HFS2 Hok. apply a1_fs_ok_iff in Hok. destruct Hok as (P1 & P2 & P3 & P4 & P5).
  apply a1_fs_ok_iff.
  assert (SZ : AC.FS_SIZE = 11571200) by reflexivity. rewrite SZ in *.
  split; [|split; [|split; [|split]]].
  - intros a Ha. destruct (P1 a Ha) as (Hw & b & Hb). split.
    + exact (proj1 (a1_wr_rel m m0 a HR ltac:(lia)) Hw).
    + exists b. rewrite (a1_mbyte_rel m m0 a HR). exact Hb.
  - exact (a1_word_rel1 m m0 _ _ HR P2).
  - rewrite (a1_mbyte_rel m m0 _ HR). exact P3.
  - intros c Hc. destruct (P4 c Hc) as (h & Hh). exists h. exact (a1_word_rel1 m m0 _ _ HR Hh).
  - intros c j Hc Hj. rewrite (a1_mbyte_rel m m0 _ HR). exact (P5 c j Hc Hj).
Qed.

Lemma a1_fs_rel' : forall m m0 FS, mem_rel rsegs m m0 -> 0x5fe000 <= FS -> FS + AC.FS_SIZE <= 2 ^ 64 ->
  AC.a_fs_ok m0 FS -> AC.a_fs_ok m FS.
Proof.
  intros m m0 FS HR HFS HFS2 Hok. apply a1_fs_ok_iff in Hok. destruct Hok as (P1 & P2 & P3 & P4 & P5).
  apply a1_fs_ok_iff.
  assert (SZ : AC.FS_SIZE = 11571200) by reflexivity. rewrite SZ in *.
  split; [|split; [|split; [|split]]].
  - intros a Ha. destruct (P1 a Ha) as (Hw & b & Hb). split.
    + exact (proj2 (a1_wr_rel m m0 a HR ltac:(lia)) Hw).
    + exists b. rewrite <- (a1_mbyte_rel m m0 a HR). exact Hb.
  - exact (a1_word_rel2 m m0 _ _ HR P2).
  - rewrite <- (a1_mbyte_rel m m0 _ HR). exact P3.
  - intros c Hc. destruct (P4 c Hc) as (h & Hh). exists h. exact (a1_word_rel2 m m0 _ _ HR Hh).
  - intros c j Hc Hj. rewrite <- (a1_mbyte_rel m m0 _ HR). exact (P5 c j Hc Hj).
Qed.

Lemma a1_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (a1_ro_false a ltac:(lia))) in Hw. exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma a1_stk_norm : forall m lo hi, mem_rel rsegs m (normalize rsegs m) -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a /\ exists b, mbyte rsegs m a = Some b) ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi HR Hlo Hhi H. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m (normalize rsegs m) (wa a) HR (a1_ro_false a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m (normalize rsegs m) (wa a) HR). exact Hb.
Qed.

(* ---------------- bytes present -> a byte list / a word ---------------- *)

Lemma a1_seq_nth : forall N i start, (i < N)%nat -> nth_error (seq start N) i = Some (start + i)%nat.
Proof.
  induction N; intros i start Hi; [lia|].
  cbn [seq]. destruct i; cbn [nth_error].
  - f_equal; lia.
  - rewrite IHN by lia. f_equal; lia.
Qed.

Lemma a1_bytes_build : forall (m : word -> option byte) A (N : nat) (f : nat -> byte),
  0 <= A -> A + Z.of_nat N <= 2 ^ 64 ->
  (forall k, (k < N)%nat -> mbyte rsegs m (A + Z.of_nat k) = Some (f k)) ->
  bytes_at rsegs m A (map f (seq 0 N)).
Proof.
  intros m A N f HA HAN Hf. unfold bytes_at. rewrite length_map, length_seq.
  split; [exact HA|]. split; [exact HAN|]. intros i Hi.
  rewrite (map_nth_error f i (seq 0 N) (a1_seq_nth N i 0 Hi)). cbn [Nat.add].
  exact (Hf i Hi).
Qed.

Lemma a1_bytes_exist : forall (m : word -> option byte) A (N : nat),
  0 <= A -> A + Z.of_nat N <= 2 ^ 64 ->
  (forall k, (k < N)%nat -> exists b, mbyte rsegs m (A + Z.of_nat k) = Some b) ->
  exists bs, length bs = N /\ bytes_at rsegs m A bs.
Proof.
  intros m A N HA HAN H.
  pose (f := fun k : nat => match mbyte rsegs m (A + Z.of_nat k) with Some b => b | None => Z_to_bv 8 0 end).
  exists (map f (seq 0 N)). split; [rewrite length_map, length_seq; reflexivity|].
  apply a1_bytes_build; [exact HA | exact HAN |].
  intros k Hk. destruct (H k Hk) as (b & Hb). unfold f. rewrite Hb. reflexivity.
Qed.

Lemma a1_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by lia.
  rewrite <- L at 1. apply BzSF.Z_to_le_bytes_to_Z.
Qed.

Lemma a1_two_words : forall (m : word -> option byte) A,
  0 <= A -> A + 16 <= 2 ^ 64 ->
  (forall k, (k < 16)%nat -> exists b, mbyte rsegs m (A + Z.of_nat k) = Some b) ->
  exists tb te : word, bytes_at rsegs m A (le8 tb ++ le8 te).
Proof.
  intros m A HA HA16 H.
  destruct (a1_bytes_exist m A 16%nat HA ltac:(cbn; lia) H) as (bs & L & HB).
  exists (Z_to_bv 64 (bytes_le_to_Z (firstn 8 bs))), (Z_to_bv 64 (bytes_le_to_Z (skipn 8 bs))).
  rewrite (a1_le8_of_bytes (firstn 8 bs) ltac:(rewrite firstn_length; lia)).
  rewrite (a1_le8_of_bytes (skipn 8 bs) ltac:(rewrite skipn_length; lia)).
  rewrite firstn_skipn. exact HB.
Qed.

Lemma a1_flags : forall m FS, AC.a_fs_ok m FS -> 0 <= AC.a_fs_flag FS 6 0 -> AC.a_fs_flag FS 6 0 + AC.a_fs_M 6 <= 2 ^ 64 ->
  exists flags, bytes_at rsegs m (AC.a_fs_flag FS 6 0) flags /\ Z.of_nat (length flags) = AC.a_fs_M 6 /\
    Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags.
Proof.
  intros m FS Hafs HA HAN. apply a1_fs_ok_iff in Hafs. destruct Hafs as (_ & _ & _ & _ & Hflag).
  pose (f := fun j : nat => match mbyte rsegs m (AC.a_fs_flag FS 6 (Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end).
  assert (Hj : forall j, (j < Z.to_nat (AC.a_fs_M 6))%nat ->
    mbyte rsegs m (AC.a_fs_flag FS 6 0 + Z.of_nat j) = Some (f j) /\ (f j = Z_to_bv 8 0 \/ f j = Z_to_bv 8 1)).
  { intros j Hjlt.
    assert (Hjb : 0 <= Z.of_nat j < AC.a_fs_M 6) by (unfold AC.a_fs_M in *; cbn in *; lia).
    destruct (Hflag 6%nat (Z.of_nat j) ltac:(lia) Hjb) as [E | E];
      unfold f; replace (AC.a_fs_flag FS 6 0 + Z.of_nat j) with (AC.a_fs_flag FS 6 (Z.of_nat j))
        by (unfold AC.a_fs_flag; lia);
      rewrite E; (split; [reflexivity | auto]). }
  exists (map f (seq 0 (Z.to_nat (AC.a_fs_M 6)))).
  split; [|split].
  - apply a1_bytes_build; [exact HA | rewrite Z2Nat.id by (unfold AC.a_fs_M; cbn; lia); exact HAN |].
    intros k Hk. apply (Hj k Hk).
  - rewrite length_map, length_seq. rewrite Z2Nat.id by (unfold AC.a_fs_M; cbn; lia). reflexivity.
  - apply Forall_forall. intros b Hb. apply in_map_iff in Hb. destruct Hb as (j & <- & Hin).
    apply in_seq in Hin. apply (Hj j). lia.
Qed.

Lemma a1_wm_le8 : forall m a v, word_mem rsegs m a v -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  bytes_at rsegs m a (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v Hw Ha Hb.
  replace (Z_to_bv 64 v) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 v)))
    by (rewrite MState.Z_to_bv_bv_unsigned; reflexivity).
  apply word_mem_le8; [ | | exact Ha | exact Hb].
  - intros k Hk. specialize (Hw k Hk). rewrite Hw. do 2 f_equal.
    unfold YO0f.le_byte. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with (2 ^ (8 * Z.of_nat 8)).
    rewrite Z.mod_mod by (assert (0 < 2 ^ (8 * Z.of_nat 8)) by (apply Z.pow_pos_nonneg; lia); lia).
    reflexivity.
  - pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 v)) as Hr. unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr. lia.
Qed.

Lemma a1_fs_place : forall m FS, 0 < FS -> FS mod 4096 = 0 -> ASAN_GT <= FS ->
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) -> AC.a_fs_ok m FS -> fs_place m FS.
Proof.
  intros m FS H0 Hm HGT Happ Hok. apply a1_fs_ok_iff in Hok. destruct Hok as (Hreg & _ & _ & _ & _).
  assert (SZ : AC.FS_SIZE = 11571200) by reflexivity. rewrite SZ in *.
  assert (HB : FS + FS_SIZE <= 2 ^ 64).
  { pose proof (Happ (FS + 11571200 - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha. unfold FS_SIZE. lia. }
  unfold fs_place, FS_SIZE in *. split; [exact H0|]. split; [exact Hm|]. split; [exact HGT|].
  split; [intros a Ha; apply Happ; lia|].
  split; [lia|]. split; [lia|]. intros a Ha. destruct (Hreg a ltac:(lia)) as (Hw & b & Hb).
  split; [exact Hw | exists b; exact Hb].
Qed.

(* The TLS cells the frame request reads, from the runtime invariant and the thread record of AH. *)
Lemma a1_tls_of : forall m C T DB,
  asan_fs_cells m -> asan_uw_cells m -> asan_cf_cells m -> asan_opt_cells m -> asan_real_cells m ->
  word_mem rsegs m RT_TSDMAIN C -> 0 < C < 2 ^ 64 ->
  word_mem rsegs m (C + 152) T -> 0 < T < 2 ^ 64 -> C + 160 <= 2 ^ 64 ->
  (exists tb te : word, bytes_at rsegs m (T + 48) (le8 tb ++ le8 te)) ->
  word_mem rsegs m (RT_TP + 8) DB -> 0 < DB < 2 ^ 64 -> word_mem rsegs m (DB + 24) RT_TP -> DB + 32 <= 2 ^ 64 ->
  asan_tls_cells m RT_TP (Z_to_bv 64 (RT_TP + 32)) (Z_to_bv 64 RT_TSDMAIN)
    (Z_to_bv 64 C) (Z_to_bv 64 T) (Z_to_bv 64 DB) 0.
Proof.
  intros m C T DB FS UW CFc OPT RL HC HCr HCT HTr HCb (tb & te & Hpair) HDB HDBr HDBtp HDBb.
  destruct FS as (Ftls & Fdtpoff & Ftp8 & Ftp40 & _ & _).
  destruct UW as (Utsdi & Utsdk & _ & Utp88 & _).
  destruct CFc as (Cgot & _ & _ & _ & _ & Ccf137 & _ & _).
  destruct OPT as (_ & _ & Ogotv & Overb).
  pose proof (Forall_inv RL) as Rreal. cbn [fst snd] in Rreal.
  assert (RTv : bv_unsigned (Z_to_bv 64 (RT_TP + 32)) = RT_TP + 32)
    by (rewrite unsigned_lit; [reflexivity | unfold RT_TP; lia]).
  assert (RCv : bv_unsigned (Z_to_bv 64 C) = C) by (rewrite unsigned_lit; lia).
  assert (RTSv : bv_unsigned (Z_to_bv 64 RT_TSDMAIN) = RT_TSDMAIN)
    by (rewrite unsigned_lit; [reflexivity | unfold RT_TSDMAIN; lia]).
  assert (RTTv : bv_unsigned (Z_to_bv 64 T) = T) by (rewrite unsigned_lit; lia).
  assert (RDBv : bv_unsigned (Z_to_bv 64 DB) = DB) by (rewrite unsigned_lit; lia).
  unfold asan_tls_cells, TLS_INDEX, REAL_TLS_GET_ADDR, MUSL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY,
    GOT_CF, CF, GOT_VERBOSITY, VERBOSITY, DTLS_TPOFF.
  split; [exact Ftls|].
  split; [exact Rreal|].
  split; [exact Ftp8|].
  split; [rewrite RTv; replace (RT_TP + 32 + 8) with (RT_TP + 40) by lia; exact Ftp40|].
  split; [exact Utsdi|].
  split; [lia|].
  split; [exact Utsdk|].
  split; [exact Utp88|].
  split; [rewrite RTSv; replace (RT_TSDMAIN + 8 * 0) with RT_TSDMAIN by lia;
          apply word_mem_le8; [exact HC | lia | unfold RT_TSDMAIN; lia | unfold RT_TSDMAIN; lia]|].
  split; [rewrite RCv; apply word_mem_le8; [exact HCT | lia | lia | lia]|].
  split; [rewrite RTTv; exists tb, te; exact Hpair|].
  split; [exact Cgot|].
  split; [exact Ccf137|].
  split; [exact Ogotv|].
  split; [exact Overb|].
  split; [exact Fdtpoff|].
  split; [apply word_mem_le8; [exact HDB | lia | unfold RT_TP; lia | unfold RT_TP; lia]|].
  split; [rewrite RDBv; lia|].
  rewrite RDBv. apply word_mem_le8; [exact HDBtp | unfold RT_TP; lia | lia | lia].
Qed.

(* ---------------- the prologue run, 0x81018 -> the frame request entry ---------------- *)

Lemma ro8l : forall (m : word -> option byte) a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.
Lemma ro4l : forall (m : word -> option byte) a v, bytes_at rsegs m a (le4 v) -> ro_cells rsegs m a [C4 v].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma a1_tail2 : forall (m : word -> option byte) A v n j cs,
  rw_cells rsegs m A (C8 v :: CB n j :: cs) -> bytes_at rsegs m (A + 8 + Z.of_nat n) (cells_bytes cs).
Proof.
  intros m A v n j cs [[Hwf Hb] _]. cbn [cells_bytes cbytes] in Hb.
  apply (proj1 (bytes_at_app rsegs m A (le8 v) (j ++ cells_bytes cs))) in Hb as [_ Hb].
  apply (proj1 (bytes_at_app rsegs m _ j (cells_bytes cs))) in Hb as [_ Hb].
  cbn [cells_wf] in Hwf. destruct Hwf as [_ [Hl _]]. rewrite length_le8, Hl in Hb.
  replace (A + Z.of_nat 8 + Z.of_nat n) with (A + 8 + Z.of_nat n) in Hb by lia. exact Hb.
Qed.

Lemma a1_land32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof.
  intros x Hx.
  replace 18446744073709551584 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 5))) by reflexivity.
  rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.

Lemma a1_pro :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> 0x10007fff8000 <= lo -> lo + 1048576 <= bv_unsigned sp -> mem_inv rsegs m ->
  bv_unsigned sp < 2 ^ 47 -> asan_cells m ->
  evt rsegs
    (fun ms' => exists (ra' sp' a0' a1' a2' s10' : word) (m' : word -> option byte),
       ms' = MS (mkR ra' sp' gp tp t0 t1 t2 sp sp' a0' a1' a2' a3 a4 a5 a6 a7 a1 s3 s4 s5 a0 s7 s8 s9 s10' s11
                     t3 t4 t5 t6) F (Z_to_bv 64 0x3db94) fc None m' (seg_rom rsegs) /\
       ra' = Z_to_bv 64 0x81090 /\
       bv_unsigned sp' = (bv_unsigned sp - 448) - (bv_unsigned sp - 448) mod 32 /\
       bv_unsigned a0' = 3136 /\ s10' = Z_to_bv 64 ASAN_K /\
       munch [(bv_unsigned sp - 448, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       stk rsegs m' lo (bv_unsigned sp) /\
       bytes_at rsegs m' (bv_unsigned sp - 104)
         (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++
          le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81018) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST HLO LO MI HSP HAC.
  destruct HAC as (HCK & HGCK & _ & _ & _ & HUAR & HGUAR & _).
  unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR, ASAN_K in *.
  apply ro8l in HCK, HGCK, HGUAR. apply ro4l in HUAR.
  pose proof (munch_refl [(bv_unsigned sp - 448, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  carve_frame 448%nat ST.
  do 27 step.
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with false by (vm_compute; reflexivity) end.
  cbv iota.
  do 3 step.
  pose proof (a1_tail2 _ _ _ _ _ _ FR) as SB.
  cbn [cells_bytes cbytes] in SB. rewrite app_nil_r in SB.
  replace (bv_unsigned sp + -448 + 8 + Z.of_nat 336) with (bv_unsigned sp - 104) in SB by lia.
  release_frame FR ST (bv_unsigned sp).
  finish.
  all: try reflexivity.
  all: try assumption.
  rewrite (unsigned_lit (bv_unsigned sp + -448)) by lia.
  rewrite a1_land32 by lia.
  rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned sp + -448) 32 ltac:(lia)); lia).
  reflexivity.
Qed.

(* ---------------- byte-level helpers for the end state ---------------- *)

(* Above the image (0x5fe000) no address is in a loaded segment, so a writable byte there is a byte of the overlay. *)
Lemma a1_wview_some : forall (m : word -> option byte) x, 0x5fe000 <= bv_unsigned x ->
  wview rsegs m x <> None -> exists b, m x = Some b.
Proof.
  intros m x Hx H. unfold wview in H. destruct (m x) as [b|] eqn:E; [exists b; reflexivity|].
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:F; [|exfalso; apply H; reflexivity].
  exfalso. destruct (a1_find_seg rsegs _ _ _ F) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ rsegs) a1_img_top s Hin) as HB. apply Z.leb_le in HB. lia.
Qed.

Lemma a1_bytes1 : forall (m : word -> option byte) a b, 0 <= a -> a + 1 <= 2 ^ 64 ->
  mbyte rsegs m a = Some b -> bytes_at rsegs m a [b].
Proof.
  intros m a b H0 H1 H. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
  destruct i as [|i]; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. exact H.
Qed.

(* Two in-range values held by the same 8 bytes are equal. *)
Lemma a1_word_eq : forall (m : word -> option byte) a v v', word_mem rsegs m a v -> word_mem rsegs m a v' ->
  0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
  intros m a v v' H H' Hv Hv'.
  assert (E : forall k, (k < 8)%nat -> le_byte v 8 k = le_byte v' 8 k).
  { intros k Hk. pose proof (H k Hk) as A1. pose proof (H' k Hk) as A2. rewrite A1 in A2.
    assert (A3 : Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (le_byte v' 8 k)) by congruence.
    apply (f_equal bv_unsigned) in A3. rewrite !kb_byte_unsigned in A3. exact A3. }
  rewrite (kb_le8_digits v Hv), (kb_le8_digits v' Hv').
  rewrite !E by lia. reflexivity.
Qed.

(* The registered globals lie in the image, below 0x5fe000. *)
Lemma a1_AG_low : forall a, in_globals AF.frame_AG a -> 0 <= a < 0x5fe000.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (HB : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 0x5fe000)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) HB (lo, len) Hin) as Hp. cbn [fst snd] in Hp.
  apply andb_prop in Hp as [P1 P2]. apply Z.leb_le in P1, P2. lia.
Qed.

(* A one-byte addressability fact survives a run whose writes miss the byte's shadow. *)
Lemma a1_addr_keep : forall (mem m' : word -> option byte) W a, addressable mem a 1 -> munch W mem m' ->
  outside W (shadow_addr a) -> 0 <= shadow_addr a < 2 ^ 64 -> addressable m' a 1.
Proof.
  intros mem m' W a (H1 & H2 & H3 & H) MU Ho Hr. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r in *.
  unfold mrd in *. rewrite (MU (wa (shadow_addr a))); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* The side stack's runtime state after the frame request: the request writes the class-6 hint word, at most one
   class-6 flag byte (to 1), frame words above FS + 36864, the frame's shadow and the allocator's own stack window;
   the other metadata cells are kept. *)
Lemma a1_fs_ok_call : forall (Wc : list ivl) (m1 m2 : word -> option byte) FS,
  AC.a_fs_ok m1 FS -> munch Wc m1 m2 -> wmono rsegs m1 m2 ->
  0x5fe000 <= FS -> FS + AC.FS_SIZE <= 2 ^ 64 ->
  (forall q, FS <= q < FS + 48 -> outside Wc q) ->
  (forall q, FS + 56 <= q < FS + 36864 -> outside Wc q \/
     (exists j, 0 <= j < AC.a_fs_M 6 /\ q = AC.a_fs_flag FS 6 j /\ mbyte rsegs m2 q = Some (Z_to_bv 8 1))) ->
  (exists h, word_mem rsegs m2 (AC.a_fs_hint FS 6) h) ->
  AC.a_fs_ok m2 FS.
Proof.
  intros Wc m1 m2 FS Hok MU WM HFS HFS2 H48 H56 Hh6.
  apply a1_fs_ok_iff in Hok. destruct Hok as (P1 & P2 & P3 & P4 & P5). apply a1_fs_ok_iff.
  assert (SZ : AC.FS_SIZE = 11571200) by reflexivity. rewrite SZ in *.
  assert (KB : forall q, 0 <= q < 2 ^ 64 -> outside Wc q -> mbyte rsegs m2 q = mbyte rsegs m1 q)
    by (intros q Hq Ho; exact (KindBGlue.mbyte_munch rsegs Wc m1 m2 q MU Hq Ho)).
  assert (Hfl6 : forall j, AC.a_fs_flag FS 6 j = FS + 36352 + j).
  { intros j. unfold AC.a_fs_flag. change (Z.of_nat 6) with 6. change (2 ^ 15) with 32768.
    change (2 ^ (15 - 6)) with 512. lia. }
  split; [|split; [|split; [|split]]].
  - intros a Ha. destruct (P1 a Ha) as (Hw & _).
    assert (Hw2 : writable_at rsegs m2 a) by exact (WM (Z_to_bv 64 a) Hw).
    split; [exact Hw2|].
    destruct (a1_wview_some m2 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit by lia; lia) Hw2) as (b & Hb).
    exists b. unfold mbyte. rewrite Hb. reflexivity.
  - intros k Hk. assert (Hk8 : Z.of_nat k < 8) by lia.
    destruct (H56 (FS + 88 + Z.of_nat k) ltac:(lia)) as [Ho | (j & Hj & Eq & _)].
    + rewrite KB; [exact (P2 k Hk) | lia | exact Ho].
    + exfalso. rewrite Hfl6 in Eq. lia.
  - destruct (H56 (FS + 96) ltac:(lia)) as [Ho | (j & Hj & Eq & _)].
    + rewrite KB; [exact P3 | lia | exact Ho].
    + exfalso. rewrite Hfl6 in Eq. lia.
  - intros c Hc. destruct (Nat.eq_dec c 6) as [->|Hc6]; [exact Hh6|].
    destruct (P4 c Hc) as (h & Hh). exists h. intros k Hk. assert (Hk8 : Z.of_nat k < 8) by lia.
    assert (Hc' : Z.of_nat c <= 10 /\ Z.of_nat c <> 6) by lia.
    assert (Ho : outside Wc (AC.a_fs_hint FS c + Z.of_nat k)).
    { unfold AC.a_fs_hint. destruct (Z_lt_le_dec (Z.of_nat c) 6).
      - apply H48. lia.
      - destruct (H56 (FS + 8 * Z.of_nat c + Z.of_nat k) ltac:(lia)) as [Ho | (j & Hj & Eq & _)]; [exact Ho|].
        exfalso. rewrite Hfl6 in Eq. lia. }
    rewrite KB; [exact (Hh k Hk) | unfold AC.a_fs_hint; lia | exact Ho].
  - intros c j Hc Hj.
    pose proof (a_fs_flag_range FS c j Hc Hj) as Hr.
    assert (Hlo : FS + 4096 <= AC.a_fs_flag FS c j).
    { unfold AC.a_fs_flag. assert (2 ^ (15 - Z.of_nat c) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
      assert (0 <= j) by lia. lia. }
    destruct (H56 (AC.a_fs_flag FS c j) ltac:(lia)) as [Ho | (j' & Hj' & Eq & Hv)].
    + rewrite KB; [exact (P5 c j Hc Hj) | lia | exact Ho].
    + right. exact Hv.
Qed.

(* ---------------- the run lemma: an evt on the normalized memory -> SR ---------------- *)

Lemma a1_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Section Run.
Context {fx : YK11.FPState}.

(* The asan run lemma on the normalized memory: the frame request's contract needs mem_inv, so the segment is
   stepped on normalize mem; MemNorm.evt_normalize carries the run back to the real memory (the end memory m' is
   related to the run's end memory by mem_rel and keeps the read-only bytes), and AsanLift.evt_SR_canon_lazy lifts
   it to SR (the end model is some md' with mat_le md md'). *)
Lemma a1_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m0, ms = MS R fp_regs pc' fp_csr None m0 (seg_rom rsegs) /\ K R pc' m0)
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m0 regs' m' md', K R pc' m0 -> (forall r, getr regs' r = getr R r) -> mem_rel rsegs m' m0 ->
     ro_same rsegs mem m' -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hro HE HK.
  apply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs))
          (fun s => exists s0, (exists R pc' m0, s0 = MS R fp_regs pc' fp_csr None m0 (seg_rom rsegs) /\
                                  K R pc' m0) /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s)) md P).
  - change (RegisterBridge.canonical_register_state (mkst regs pc mem (seg_rom rsegs)))
      with (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)).
    apply evt_normalize; [exact a1_wx | exact Hro | exact HE].
  - exact Hh.
  - intros ms' md' (can & (s0 & (R & pc' & m0 & Es0 & HKR) & Hrel & Hsame) & Heq) Hmat.
    subst s0.
    destruct can as [cr cf cp cs cv cc cm co].
    destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn in E1, E2, E3, E4, E5, E6, E7, E8, Hsame.
    subst cr cf cp cs cv cc co.
    destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
    destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
    cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst fr' pcv' svc' rv' fc' m' ro'.
    apply (HK R pc' m0 regs' cm md' HKR); [apply kb_getr_eqv; exact HR | exact E8 | exact Hsame | exact Hmat].
Qed.

End Run.

(* ---------------- the segment ---------------- *)

(* The spill base the prologue computes: A = (S - 448) & -32. *)
Definition a1A (S : Z) : Z := S - 448 - (S - 448) mod 32.

(* The segment's write set: the slot window below the entry sp, the side stack FS and its shadow. *)
Definition A1W (S FS : Z) : list ivl :=
  [(S - AF.SLOT_STACK, S); (FS, FS + AC.FS_SIZE); (shadow_addr FS, shadow_addr FS + 1446400)].

(* The side arm's write set: the class-6 hint word, the frame's flag byte, two frame words, the frame's 512 shadow
   bytes and the request's own 208-byte stack window. *)
Definition A1Wc (FS A j fr : Z) : list ivl :=
  [(FS + 48, FS + 48 + 8); (FS + 36352 + j, FS + 36352 + j + 1); (fr + 24, fr + 32); (fr + 4096 - 8, fr + 4096);
   (shadow_addr fr, shadow_addr fr + 512); (A - 208, A)].

(* It misses the bytes the segment keeps: it lies inside the segment's write set A1W, below the spill base A, apart
   from the side stack's header and hint words, and apart from every metadata byte but the frame's own flag. *)
Lemma a1_side_out : forall S A FS j fr,
  FS mod 8 = 0 -> 0 <= j < 256 -> fr = FS + 6328320 + j * 4096 -> 6283264 <= FS ->
  FS + 11571200 <= 2147450880 \/ 17594333495296 <= FS ->
  FS + 11571200 <= S - 1048576 -> 17594333495296 <= S - 1048576 -> S < 140737488355328 ->
  S - 464 <= A <= S - 448 ->
  (forall x, outside (A1W S FS) x -> outside (A1Wc FS A j fr) x) /\
  (forall x, A <= x < S -> outside (A1Wc FS A j fr) x) /\
  (forall q, FS <= q < FS + 48 -> outside (A1Wc FS A j fr) q) /\
  (forall q, FS + 56 <= q < FS + 36864 -> q <> FS + 36352 + j -> outside (A1Wc FS A j fr) q).
Proof.
  intros S A FS j fr HF8 Hj Efr HF0 HFlh HFS HSlo HSapp HA.
  assert (E1 : shadow_addr fr = FS / 8 + 791040 + j * 512 + 2147450880).
  { subst fr. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
  assert (E2 : shadow_addr FS = FS / 8 + 2147450880) by (unfold shadow_addr, ASAN_K; reflexivity).
  assert (E3 : FS = 8 * (FS / 8)) by (Z.div_mod_to_equations; lia).
  unfold A1Wc, A1W, AF.SLOT_STACK, AC.FS_SIZE. rewrite E1, E2.
  set (F8 := FS / 8) in *. subst fr.
  split; [|split; [|split]].
  - intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & Hx3 & _). repeat split; try exact I; lia.
  - intros x Hx. cbn [outside]. repeat split; try exact I; lia.
  - intros q Hq. cbn [outside]. repeat split; try exact I; lia.
  - intros q Hq Hne. cbn [outside]. repeat split; try exact I; lia.
Qed.

(* The side frame's record as the class-6 request leaves it (asan_stack_malloc_frame, c = 6): slot j, the flag byte
   at fs_flag FS 6 j = FS + 36352 + j is 1 and the slot's last word r + fs_B 6 - 8 = r + 4088 holds the flag's
   address. FSREC of SlotInv.v is this record read through the tp word. *)
Definition a1_rec (FS r : Z) (m : word -> option byte) : Prop :=
  exists j, 0 <= j < 256 /\ r = FS + 6328320 + j * 4096 /\
    bytes_at rsegs m (FS + 36352 + j) [Z_to_bv 8 1] /\
    bytes_at rsegs m (r + 4088) (le8 (Z_to_bv 64 (FS + 36352 + j))).

Section Seg.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The class-6 side-stack frame request frame_alloc_6 (v1.9 0x3db94), on its lib/B contract (asan_stack_malloc_c.v;
   proved as Tk/AW/Sm6.v stack_malloc_6). *)
Hypothesis SM6 : asan_stack_malloc_6_contract.
(* The slot's named entry premise ENTRY_CLASS (Seg/Tac_slot.v Section EntryClass, verbatim): the entry heap's
   per-class bound, owed by the driver until alib_pre carries it. ent_entry takes it for ENT's 14th conjunct. *)
Hypothesis ENTRY_CLASS : forall g c, Inv_ENTRY B APIf ra empty g c ->
  exists BE : Z -> Z,
    (forall cl, 0 <= cl < AsanCtrl.K_NUM_CLASSES -> ClassConsDef.a_class_bytes (g_H g) cl <= BE cl) /\
    (forall cl, 0 <= cl < AsanCtrl.K_NUM_CLASSES -> BE cl + BC_ctrl cl <= 2 ^ 22).

(* ---- The generated allocator laws are read by statement, one lemma per law (a Theorem Labs lane via a Theorem Labs lane 15:18Z / 15:32Z):
   SlotInv.v's lw_* (blocks, not_owned, fs_place, mat_le), Tac_fsfree.v's fsf_thread_fields / fsf_fs_state_fields,
   and a1_law_fs_store below (a_laws_fs_store, which no shared lemma reads). *)
Lemma a1_law_fs_store : forall H mem mem' md FS, AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.a_fs_ok mem' FS ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md FS HAH Htp HFS Hst Hwr Hok.
  decompose [and] (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md FS HAH
                     Htp HFS Hst Hwr Hok).
  refine (conj _ (conj _ (conj _ _))); assumption.
Qed.

(* Stated as S_A1 (forms-asan-ubsan-v190.md). The Inv_B810c4 premise is unused: the only path to that cut is the
   D = 0 branch `beqz a2,0x81098`, which the run does not take (D = 1). *)
Lemma seg_A1 :
  Hcut B APIf ra (Inv_B81090 B APIf ra) -> Hcut B APIf ra (Inv_B810c4 B APIf ra) -> Hcut B APIf ra (Inv_ENTRY B APIf ra empty).
Proof.
  intros Hbc _ g c HInv.
  destruct g as [gin gp gS gregs gmem gmd gH gT].
  pose proof HInv as HI0.
  destruct HInv as (Ec & Hpre & HTH & HTn & Hgimg & Hasp & Hfrm). subst c.
  cbn [g_regs g_mem g_md g_H g_T g_in g_p g_S] in *.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct Hpre as (Hcp & Hra & Hp & Hn & Hpn & Hlen & HnMax & Hblk & HAG & Hlive & Herrno & Hsn & Hfd & Hfss & Himg).
  destruct Hcp as (HRT & HAH & Hret & Hsp16 & Hstklo & HspApp & Hspstkhi & Hstkhi & Hstkpres & Hwin & Htp & Hro &
    Hhalt & Hwinp).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS gH gmem gmd HAH) as Hhigh.
  change (AC.aspZ gregs) with (bv_unsigned (getr gregs 2)) in *.
  set (S := bv_unsigned (getr gregs 2)) in *.
  (* push 5c: Inv_ENTRY pins the ghost's entry sp (AC.aspZ (g_regs g) = g_S g), so g_S is the entry sp S and the
     exit cut is the one of the ghost itself (the old free-g_S workaround is gone). *)
  assert (EgS : gS = S) by (symmetry; exact Hasp).
  subst gS.
  (* ENT (push 5c) at the entry state: every conjunct is a fact of that state about itself. *)
  assert (HENT0 : ENT APIf (Ghost gin gp S gregs gmem gmd gH gT) [] gmem gmd)
    by (eapply ent_entry; first [exact HI0 | exact ENTRY_CLASS]).
  assert (HS64 : 0 <= S < 2 ^ 64).
  { pose proof (bv_unsigned_in_range 64 (getr gregs 2)) as Hr. unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr. exact Hr. }
  assert (ESreg : getr gregs 2 = Z_to_bv 64 S) by (unfold S; symmetry; apply Z_to_bv_bv_unsigned).
  unfold HIGHMEM_BEG, APPMEM_END in Hhigh, HspApp.
  (* the spill base A *)
  set (A := a1A S).
  assert (HAm : A mod 32 = 0 /\ S - 464 <= A <= S - 448).
  { unfold A, a1A. Z.div_mod_to_equations. lia. }
  (* the side stack FS: the word at tp (RT's TLS cells), its state and placement (AH) *)
  destruct (AsanRTInv.RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FSw & HFSb & HFSok) & _).
  set (FS := bv_unsigned FSw).
  assert (EFSw : Z_to_bv 64 FS = FSw) by (unfold FS; apply Z_to_bv_bv_unsigned).
  assert (ETP : AC.as_tp AC.ASYMS = RT_TP) by reflexivity.
  assert (HwtpFS : word_mem rsegs gmem (AC.as_tp AC.ASYMS) FS)
    by (rewrite ETP; exact (bytes_at_le8_word rsegs gmem RT_TP FSw HFSb)).
  assert (HFSr : 0 <= FS < 2 ^ 64).
  { pose proof (bv_unsigned_in_range 64 FSw) as Hr. unfold bv_modulus in Hr.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in Hr. exact Hr. }
  destruct (Tac_fsfree.fsf_fs_state_fields (APIf rc) gH gmem gmd FS HAH HwtpFS HFSr)
    as (DB & [Hok HwDB HDBr HDBnz HwDB24 HDBcell HT48app]).
  assert (HDB32 : DB + 32 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) gmem gmd)
    by (destruct (HDBcell (DB + 31) ltac:(lia)) as (_ & Hl & _); lia).
  destruct (lw_fs_place (APIf rc) gH gmem gmd FS HAH HwtpFS HFSr) as [HGT HFSend HFS4096 HFSapp].
  unfold AC.GT in HGT.
  (* the thread record C, T (AH) *)
  destruct (Tac_fsfree.fsf_thread_fields (APIf rc) gH gmem gmd HAH)
    as (Cv & Tv & [_ HwC HwT HCr HTr HC152 HT48]).
  (* the allocator's bytes are below the real stack *)
  assert (Hown_lo : forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) gH gmem gmd a -> app_mem a ->
            a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) gmem gmd).
  { intros a Ho Ha. destruct (Z_lt_le_dec a (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) gmem gmd)) as [Hl|Hl];
      [exact Hl|].
    exfalso. assert (Ha' : a < APPMEM_END) by (unfold app_mem in Ha; unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha |- *; lia).
    exact (lwn_byte (lw_not_owned (APIf rc) gH gmem gmd a HAH (or_intror (or_intror (or_intror (conj Hl Ha'))))) Ho). }
  assert (HC160 : Cv + 160 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) gmem gmd).
  { destruct (HC152 7 ltac:(lia)) as (Ho & Ha). pose proof (Hown_lo _ Ho Ha). lia. }
  assert (HCapp : Cv + 159 < APPMEM_END).
  { destruct (HC152 7 ltac:(lia)) as (_ & Ha). unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HT64 : Tv + 64 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) gmem gmd).
  { destruct (HT48 15 ltac:(lia)) as (Ho & _). pose proof (HT48app Cv Tv HwC ltac:(lia) HwT ltac:(lia) 15 ltac:(lia)).
    pose proof (Hown_lo _ Ho ltac:(assumption)). lia. }
  assert (HTapp : Tv + 63 < APPMEM_END).
  { pose proof (HT48app Cv Tv HwC ltac:(lia) HwT ltac:(lia) 15 ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  (* the side stack lies wholly in low or wholly in high app memory *)
  assert (HFSlh : FS + 11571200 <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { destruct (Z_lt_le_dec FS LOWMEM_END) as [Hl|Hl].
    - left. destruct (Z_lt_le_dec (FS + 11571200) (LOWMEM_END + 1)) as [H1|H1]; [lia|].
      exfalso. assert (Ha : app_mem LOWMEM_END) by (apply HFSapp; rewrite HFSZ; lia).
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
    - right. assert (Ha : app_mem FS) by (apply HFSapp; rewrite HFSZ; lia).
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HFS8 : FS mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (HshFS : ASAN_K <= shadow_addr FS) by (unfold shadow_addr; pose proof (Z.div_pos FS 8 ltac:(lia) ltac:(lia)); lia).
  unfold LOWMEM_END, HIGHMEM_BEG, ASAN_K in HFSlh, HshFS.
  (* the normalized entry memory m0 *)
  pose proof (mem_rel_normalize rsegs gmem Hro) as HR0.
  set (m0 := normalize rsegs gmem) in *.
  pose proof (a1_RT_rel gmem m0 S gmd HR0 HRT) as RT0.
  assert (ST0 : stk rsegs m0 (S - AF.SLOT_STACK) S).
  { apply (a1_stk_norm gmem (S - AF.SLOT_STACK) S HR0); [lia | lia |].
    intros a Ha. split; [apply Hwin | apply Hwinp]; unfold AC.a_window; exact Ha. }
  pose proof (a1_fs_rel gmem m0 FS HR0 ltac:(lia) ltac:(rewrite HFSZ; lia) Hok) as OK0.
  rewrite SEGS.
  apply (a1_run gregs (Z_to_bv 64 AF.ENTRY) gmem gmd
    (fun R pc' m2 => pc' = Z_to_bv 64 0x81090 /\
       getr R 2 = Z_to_bv 64 A /\ getr R 3 = getr gregs 3 /\ getr R 4 = getr gregs 4 /\
       getr R 8 = getr gregs 2 /\ getr R 9 = Z_to_bv 64 A /\ getr R 18 = getr gregs 11 /\
       getr R 22 = getr gregs 10 /\ getr R 26 = Z_to_bv 64 ASAN_K /\
       munch (A1W S FS) m0 m2 /\ wmono rsegs m0 m2 /\ AC.a_fs_ok m2 FS /\
       stk rsegs m2 (S - AF.SLOT_STACK) S /\
       bytes_at rsegs m2 (S - 104)
         (le8 (getr gregs 27) ++ le8 (getr gregs 26) ++ le8 (getr gregs 25) ++ le8 (getr gregs 24) ++
          le8 (getr gregs 23) ++ le8 (getr gregs 22) ++ le8 (getr gregs 21) ++ le8 (getr gregs 20) ++
          le8 (getr gregs 19) ++ le8 (getr gregs 18) ++ le8 (getr gregs 9) ++ le8 (getr gregs 8) ++
          le8 (getr gregs 1)) /\
       exists r, getr R 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
         (r = 0 \/ (r mod 32 = 0 /\ FS + 6328320 <= r /\ r + 3136 <= FS + AC.FS_SIZE /\ a1_rec FS r m2)))
    (Post B APIf ra (Ghost gin gp S gregs gmem gmd gH gT))); [exact Hhalt | exact Hro | |].
  - (* the run: the prologue (a1_pro), then the frame request on its contract *)
    rewrite a1_mkR_of. unfold AF.ENTRY.
    eapply evt_cut.
    { apply (a1_pro (getr gregs 1) (getr gregs 2) (getr gregs 3) (getr gregs 4) (getr gregs 5) (getr gregs 6)
               (getr gregs 7) (getr gregs 8) (getr gregs 9) (getr gregs 10) (getr gregs 11) (getr gregs 12)
               (getr gregs 13) (getr gregs 14) (getr gregs 15) (getr gregs 16) (getr gregs 17) (getr gregs 18)
               (getr gregs 19) (getr gregs 20) (getr gregs 21) (getr gregs 22) (getr gregs 23) (getr gregs 24)
               (getr gregs 25) (getr gregs 26) (getr gregs 27) (getr gregs 28) (getr gregs 29) (getr gregs 30)
               (getr gregs 31) fp_regs fp_csr m0 (S - AF.SLOT_STACK)).
      - exact ST0.
      - lia.
      - lia.
      - apply mem_inv_normalize.
      - lia.
      - exact (AsanRTInv.RT_cells _ _ _ RT0). }
    intros ms1 (ra' & sp' & a0' & a1' & a2' & s10' & m1 & -> & Hra' & Hsp' & Ha0' & Hs10' & MU1 & WM1 & MI1 &
      ST1 & SB1).
    change (bv_unsigned (getr gregs 2)) with S in Hsp', MU1, ST1, SB1.
    assert (HA : bv_unsigned sp' = A) by (rewrite Hsp'; reflexivity).
    assert (Esp' : sp' = Z_to_bv 64 A) by (rewrite <- HA; symmetry; apply Z_to_bv_bv_unsigned).
    (* the facts at the request's entry (memory m1) *)
    assert (KB1 : forall x, 0 <= x < S - 448 -> mbyte rsegs m1 x = mbyte rsegs gmem x).
    { intros x Hx. rewrite (KindBGlue.mbyte_munch rsegs [(S - 448, S)] m0 m1 x MU1 ltac:(lia)
                              ltac:(cbn; split; [lia | exact I])).
      apply a1_mbyte_rel. exact HR0. }
    assert (W1m : forall a v, word_mem rsegs gmem a v -> 0 <= a -> a + 8 <= S - 448 -> word_mem rsegs m1 a v).
    { intros a v Hw H0 H1. apply (KindBGlue.word_mem_frame rsegs gmem m1 a v Hw). intros k Hk. apply KB1. lia. }
    pose proof (AsanRTInv.RT_store S A m0 m1 gmd gmd [(S - 448, S)] RT0 MU1 WM1
                  (a1_all_app_high (S - 448) S ltac:(unfold HIGHMEM_BEG; lia) ltac:(unfold APPMEM_END; lia))
                  (a1_rt_disjoint_gt (S - 448) S ltac:(lia))) as RT1.
    assert (OK1 : AC.a_fs_ok m1 FS).
    { apply (a_fs_ok_pres [(S - 448, S)] m0 m1 FS OK0 MU1).
      - intros q _ Hw. exact (WM1 (Z_to_bv 64 q) Hw).
      - intros q Hq Hb. destruct (Z_lt_le_dec q (S - 448)) as [Hl|Hl].
        + rewrite (KindBGlue.mbyte_munch rsegs [(S - 448, S)] m0 m1 q MU1 Hq ltac:(cbn; split; [lia | exact I])).
          exact Hb.
        + destruct (Z_lt_le_dec q S) as [Hl2|Hl2].
          * destruct ST1 as (_ & _ & Hst). destruct (Hst q ltac:(lia)) as (_ & b & Hb').
            exists b. exact Hb'.
          * rewrite (KindBGlue.mbyte_munch rsegs [(S - 448, S)] m0 m1 q MU1 Hq ltac:(cbn; split; [lia | exact I])).
            exact Hb.
      - intros q Hq. pose proof (fs_meta_below FS q Hq). cbn. split; [lia | exact I].
      - lia.
      - rewrite HFSZ. lia. }
    pose proof (proj1 (a1_fs_ok_iff m1 FS) OK1) as (_ & OK1w88 & OK1b96 & OK1hint & _).
    destruct (OK1hint 6%nat ltac:(lia)) as (hv & Hhv).
    destruct (a1_flags m1 FS OK1 ltac:(unfold AC.a_fs_flag; cbn; lia) ltac:(unfold AC.a_fs_flag, AC.a_fs_M; cbn; lia))
      as (flags & Hflags & Hflen & Hf01).
    assert (ETPu : bv_unsigned (getr gregs 4) = RT_TP) by (rewrite Htp; reflexivity).
    pose proof SM6 as SMc.
    unfold asan_stack_malloc_6_contract, asan_stack_malloc_contract, ASAN_STACK_MALLOC_6, ASAN_STACK_MALLOC_K in SMc.
    cbv zeta in SMc.
    eapply evt_mono.
    { eapply (SMc ra' sp' (getr gregs 3) (getr gregs 4) (getr gregs 5) (getr gregs 6) (getr gregs 7)
                (getr gregs 2) sp' a0' a1' a2' (getr gregs 13) (getr gregs 14) (getr gregs 15) (getr gregs 16)
                (getr gregs 17) (getr gregs 11) (getr gregs 19) (getr gregs 20) (getr gregs 21) (getr gregs 10)
                (getr gregs 23) (getr gregs 24) (getr gregs 25) s10' (getr gregs 27) (getr gregs 28)
                (getr gregs 29) (getr gregs 30) (getr gregs 31) fp_regs fp_csr m1 (S - AF.SLOT_STACK) FS
                (Z_to_bv 64 hv) (Z_to_bv 64 (RT_TP + 32)) (Z_to_bv 64 RT_TSDMAIN) (Z_to_bv 64 Cv) (Z_to_bv 64 Tv)
                (Z_to_bv 64 DB) 0 flags).
      - rewrite Ha0'. unfold fs_B. cbn. lia.
      - rewrite Ha0'. reflexivity.
      - exact (AsanRTInv.RT_cells _ _ _ RT1).
      - exact (AsanRTInv.RT_shadow_rw _ _ _ RT1).
      - exact MI1.
      - rewrite ETPu.
        apply (a1_tls_of m1 Cv Tv DB (AsanRTInv.RT_fs_cells _ _ _ RT1) (AsanRTInv.RT_uw_cells _ _ _ RT1)
                 (AsanRTInv.RT_cf_cells _ _ _ RT1) (AsanRTInv.RT_opt_cells _ _ _ RT1)
                 (AsanRTInv.RT_real_cells _ _ _ RT1)).
        + apply W1m; [exact HwC | unfold RT_TSDMAIN; lia | unfold RT_TSDMAIN; lia].
        + lia.
        + apply W1m; [exact HwT | lia | lia].
        + lia.
        + lia.
        + apply a1_two_words; [lia | lia |].
          intros k Hk. destruct (HT48 (Z.of_nat k) ltac:(lia)) as (_ & b & Hb).
          exists b. rewrite KB1 by lia. exact Hb.
        + apply W1m; [rewrite <- ETP; exact HwDB | unfold RT_TP; lia | unfold RT_TP; lia].
        + lia.
        + apply W1m; [rewrite <- ETP; exact HwDB24 | lia | lia].
        + lia.
      - intros H7. lia.
      - rewrite ETPu, EFSw.
        apply (fl_bytes [(S - 448, S)] m0 m1 RT_TP (le8 FSw)); [exact (a1_bytes_rel1 gmem m0 _ _ HR0 HFSb) | exact MU1 |].
        rewrite length_le8. intros x Hx. cbn. split; [unfold RT_TP in Hx; lia | exact I].
      - destruct HFSok as (H1 & H2 & H3 & _).
        apply a1_fs_place; [exact H1 | exact H2 | unfold ASAN_GT; unfold RT_GT in H3; exact H3 | | exact OK1].
        intros a Ha. apply HFSapp. exact Ha.
      - apply a1_wm_le8; [exact OK1w88 | lia | rewrite HFSZ in *; lia].
      - apply a1_bytes1; [lia | rewrite HFSZ in *; lia | exact OK1b96].
      - apply a1_wm_le8; [exact Hhv | unfold fs_hint; change (Z.of_nat 6) with 6; lia |
          unfold fs_hint; change (Z.of_nat 6) with 6; rewrite HFSZ in *; lia].
      - exact Hflags.
      - exact Hflen.
      - exact Hf01.
      - rewrite HA. exact (proj1 (stk_split rsegs m1 (S - AF.SLOT_STACK) A S ST1 ltac:(lia))).
      - rewrite HA. lia.
      - rewrite HA. change FS_SIZE with 11571200. rewrite HFSZ in HFSend. lia.
      - rewrite HA. intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END. lia.
      - rewrite HA, ETPu.
        rewrite !unsigned_lit by (unfold RT_TP, RT_TSDMAIN; lia).
        unfold RT_TP, RT_TSDMAIN. cbn [disjoint_from]. repeat split; try exact I; right; lia. }
    intros ms2 POST. unfold asan_stack_malloc_post in POST.
    destruct POST as (t0' & t1' & t2' & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m2 &
      -> & WM2 & MI2 & ST2 & FSP2 & (h' & Hh') & Harm).
    (* the request's write set Wc, its result r, and what they keep *)
    assert (ARM : exists (Wc : list ivl) (r : Z),
      munch Wc m1 m2 /\ b0 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
      (r = 0 \/ (r mod 32 = 0 /\ FS + 6328320 <= r /\ r + 3136 <= FS + AC.FS_SIZE /\ a1_rec FS r m2)) /\
      (forall x, outside (A1W S FS) x -> outside Wc x) /\
      (forall x, A <= x < S -> outside Wc x) /\
      (forall q, FS <= q < FS + 48 -> outside Wc q) /\
      (forall q, FS + 56 <= q < FS + 36864 -> outside Wc q \/
         (exists j, 0 <= j < AC.a_fs_M 6 /\ q = AC.a_fs_flag FS 6 j /\ mbyte rsegs m2 q = Some (Z_to_bv 8 1)))).
    { assert (Ehint : fs_hint FS 6 = FS + 48) by (unfold fs_hint; change (Z.of_nat 6) with 6; lia).
      destruct Harm as [(_ & Eb0 & MUc) | (i & Hi & _ & _ & Hfr)].
      - (* no side frame: the request writes the hint word and its own stack window *)
        exists [(fs_hint FS 6, fs_hint FS 6 + 8); (bv_unsigned sp' - 208, bv_unsigned sp')], 0.
        rewrite Ehint, HA in *.
        split; [exact MUc|]. split; [exact Eb0|]. split; [lia|]. split; [left; reflexivity|].
        split.
        { intros x Hx. unfold A1W in Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & Hx2 & Hx3 & _).
          rewrite HSS, HFSZ in *. split; [lia|]. split; [lia | exact I]. }
        split.
        { intros x Hx. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
        split.
        { intros q Hq. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
        intros q Hq. left. cbn [outside]. split; [lia|]. split; [lia | exact I].
      - (* a side frame fr = fs_frame FS 6 j: the request writes the hint word, the frame's flag byte, two frame
           words, the frame's shadow and its own stack window *)
        unfold asan_stack_malloc_frame in Hfr. cbv zeta in Hfr.
        set (j := (bv_unsigned (Z_to_bv 64 hv) + i) mod fs_M 6) in Hfr.
        destruct Hfr as (Eb0 & Hfr64 & Hfr4096 & Hflag & Hw24 & HwB & Hshz & Haddr & Hstkfr & Happfr & HFSfr & HfrB &
          HGTfr & Hfrsp & Hothers & MUc).
        assert (Hj : 0 <= j < 256) by (unfold j; change (fs_M 6) with 256; apply Z.mod_pos_bound; lia).
        assert (EB : fs_B 6 = 4096) by reflexivity.
        assert (En : fs_shadow_n 6 (bv_unsigned a0') = 512) by (rewrite Ha0'; reflexivity).
        assert (Eflag : fs_flag FS 6 j = FS + 36352 + j).
        { unfold fs_flag. change (Z.of_nat 6) with 6. change (2 ^ 15) with 32768. change (2 ^ (15 - 6)) with 512.
          lia. }
        assert (Efr : fs_frame FS 6 j = FS + 6328320 + j * 4096).
        { unfold fs_frame, fs_B. change (Z.of_nat 6) with 6. change (2 ^ 20) with 1048576. change (2 ^ 6) with 64.
          lia. }
        set (fr := fs_frame FS 6 j) in *. clearbody fr.
        rewrite EB, En, Ehint, Eflag, HA in *.
        assert (Hfr32 : fr mod 32 = 0) by (clear - Hfr64; Z.div_mod_to_equations; lia).
        destruct (a1_side_out S A FS j fr HFS8 Hj Efr ltac:(lia) HFSlh ltac:(rewrite HSS, HFSZ in *; lia)
                    ltac:(rewrite HSS in *; lia) HspApp (proj2 HAm)) as (O1 & O2 & O3 & O4).
        exists (A1Wc FS A j fr), fr.
        split; [exact MUc|]. split; [exact Eb0|]. split; [lia|].
        split; [right; split; [exact Hfr32|]; split; [lia|]; split; [rewrite HFSZ; lia|];
                exists j; split; [exact Hj|]; split; [exact Efr|]; split; [exact Hflag|];
                replace (fr + 4088) with (fr + 4096 - 8) by lia; exact HwB|].
        split; [exact O1|]. split; [exact O2|]. split; [exact O3|].
        intros q Hq. destruct (Z.eq_dec q (FS + 36352 + j)) as [Eq|Nq].
        + right. exists j. split; [change (AC.a_fs_M 6) with 256; lia|].
          split; [unfold AC.a_fs_flag; change (Z.of_nat 6) with 6; change (2 ^ 15) with 32768;
                  change (2 ^ (15 - 6)) with 512; lia|].
          destruct Hflag as (_ & _ & Hf). pose proof (Hf 0%nat ltac:(cbn; lia)) as Hf0. cbn [nth_error] in Hf0.
          rewrite Z.add_0_r in Hf0. subst q. exact Hf0.
        + left. exact (O4 q Hq Nq). }
    destruct ARM as (Wc & r & MUc & Eb0 & Hr & Hrdisj & HsubW & HoutAS & Hout48 & Hout56).
    do 3 eexists. split; [reflexivity|].
    split; [rewrite Hra'; apply bv_eq; vm_compute; reflexivity|].
    split; [exact Esp'|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact Esp'|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [exact Hs10'|].
    split.
    { apply (munch_trans (A1W S FS) m0 m1 m2).
      - apply (munch_weaken [(S - 448, S)] (A1W S FS) m0 m1); [|exact MU1].
        intros x Hx. unfold A1W in Hx. cbn [outside] in Hx |- *. destruct Hx as (Hx1 & _).
        rewrite HSS in Hx1. split; [lia | exact I].
      - exact (munch_weaken Wc (A1W S FS) m1 m2 HsubW MUc). }
    split; [exact (wmono_trans rsegs m0 m1 m2 WM1 WM2)|].
    split.
    { apply (a1_fs_ok_call Wc m1 m2 FS OK1 MUc WM2 ltac:(lia) ltac:(rewrite HFSZ; lia) Hout48 Hout56).
      exists (bv_unsigned h'). exact (bytes_at_le8_word rsegs m2 _ h' Hh'). }
    split.
    { apply (stk_merge rsegs m2 (S - AF.SLOT_STACK) A S); [rewrite <- HA; exact ST2 | | lia].
      apply (stk_transport rsegs Wc m1 m2 A S (proj2 (stk_split rsegs m1 (S - AF.SLOT_STACK) A S ST1 ltac:(lia)))
               MUc WM2).
      intros x Hx. left. apply HoutAS. exact Hx. }
    split.
    { apply (fl_bytes Wc m1 m2 (S - 104)); [exact SB1 | exact MUc |].
      intros x Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. apply HoutAS. lia. }
    exists r. split; [exact Eb0|]. split; [exact Hr | exact Hrdisj].
  - (* the end configuration at 0x81090: Inv_B81090 for the ghost whose entry sp is S *)
    intros R pc' m2 regs' m' md' HK Hreg Hrel Hsame Hmat.
    destruct HK as (Epc & ER2 & ER3 & ER4 & ER8 & ER9 & ER18 & ER22 & ER26 & MU & WM & OK2 & ST2 & SB2 & r & ER10 &
      Hr & Hrdisj).
    subst pc'.
    assert (MUr : munch (A1W S FS) gmem m') by exact (munch_rel rsegs (A1W S FS) gmem m0 m' m2 HR0 Hrel Hsame MU).
    assert (WMr : wmono rsegs gmem m') by exact (wmono_rel rsegs gmem m0 m' m2 HR0 Hrel Hsame WM).
    assert (KBimg : forall x, 0 <= x < 6283264 -> m' (Z_to_bv 64 x) = gmem (Z_to_bv 64 x)).
    { intros x Hx. apply MUr. rewrite unsigned_lit by lia. unfold A1W. cbn [outside].
      rewrite HSS, HFSZ. repeat split; try exact I; lia. }
    assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg m' x = mbyte sg gmem x).
    { intros sg x H0 H1. unfold mbyte. rewrite KBimg; [reflexivity | lia]. }
    assert (OKr : AC.a_fs_ok m' FS) by exact (a1_fs_rel' m' m2 FS Hrel ltac:(lia) ltac:(rewrite HFSZ; lia) OK2).
    assert (Hstore : forall a, 0 <= a < 2 ^ 64 ->
              ~ AC.a_store_ok gH (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) gmem gmd) a ->
              ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
              m' (Z_to_bv 64 a) = gmem (Z_to_bv 64 a)).
    { intros a Ha Hns Hnf Hnsh. apply MUr. rewrite unsigned_lit by lia. unfold A1W. cbn [outside].
      split; [intro Hin; apply Hns; unfold AC.a_store_ok; right; left; rewrite HSS in Hin; lia|].
      split; [exact Hnf|]. split; [|exact I].
      intro Hin. apply Hnsh. exists (FS + 8 * (a - shadow_addr FS)). rewrite HFSZ.
      split; [lia|]. unfold shadow_addr in *. Z.div_mod_to_equations. lia. }
    destruct (a1_law_fs_store gH gmem m' gmd FS HAH HwtpFS HFSr Hstore
                (fun a _ Hw => WMr (Z_to_bv 64 a) Hw) OKr) as (HAH1 & Hown1 & Hlo1 & Hhi1).
    destruct (lw_mat_le (APIf rc) gH m' gmd md' Hmat) as [HAHm _ Hlo2 _].
    assert (HwFSm : word_mem rsegs m' (AC.as_tp AC.ASYMS) FS).
    { apply (KindBGlue.word_mem_frame rsegs gmem m' _ FS HwtpFS). intros k Hk. apply KBlo; rewrite ETP; unfold RT_TP; lia. }
    (* numeric forms of the two placement bounds, for the window / side-stack / shadow case splits *)
    assert (Hstklo' : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) gmem gmd <= S - 1048576)
      by (rewrite <- HSS; exact Hstklo).
    assert (HFSend' : FS + 11571200 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) gmem gmd)
      by (rewrite <- HFSZ; exact HFSend).
    (* every byte of the side stack's shadow is the shadow byte of a side-stack byte, hence never app memory *)
    assert (HshIS : forall x, shadow_addr FS <= x < shadow_addr FS + 1446400 -> in_shadow x).
    { intros x Hx.
      pose proof (shadow_of_app (FS + 8 * (x - shadow_addr FS))
                    (HFSapp (FS + 8 * (x - shadow_addr FS))
                       ltac:(rewrite HFSZ; clear - Hx; unfold shadow_addr in *; lia))) as His.
      replace (shadow_addr (FS + 8 * (x - shadow_addr FS))) with x in His; [exact His|].
      clear - HFS8. unfold shadow_addr. Z.div_mod_to_equations. lia. }
    (* an app-memory byte below the slot window (or at or above the entry sp) and off the side stack is outside
       the segment's write set A1W *)
    assert (Houtapp : forall x, app_mem x -> (x < S - 1048576 \/ S <= x) -> (x < FS \/ FS + 11571200 <= x) ->
              outside (A1W S FS) x).
    { intros x Happ H1 H2. unfold A1W. cbn [outside]. rewrite HSS, HFSZ.
      split; [destruct H1 as [H|H]; lia|].
      split; [destruct H2 as [H|H]; lia|].
      split; [|exact I].
      intros Hin. exact (app_not_shadow x Happ (HshIS x Hin)). }
    (* and so is the shadow byte of such a byte (a shadow address is below HIGHMEM_BEG <= stklo) *)
    assert (HshOut : forall b, app_mem b -> (b < FS \/ FS + 11571200 <= b) ->
              outside (A1W S FS) (shadow_addr b)).
    { intros b Happ Hb.
      assert (Hb0 : 0 <= b) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happ; lia).
      pose proof (shadow_of_app b Happ) as Hsb0.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb0.
      assert (Hsb : 2147450880 <= shadow_addr b < 17594333495296)
        by (destruct Hsb0 as [[? ?]|[? ?]]; lia).
      assert (Hne : ~ (shadow_addr FS <= shadow_addr b < shadow_addr FS + 1446400)).
      { clear - Hb Hb0 HFS8. unfold shadow_addr, ASAN_K. intros Hin.
        destruct Hb as [Hb|Hb]; Z.div_mod_to_equations; lia. }
      unfold A1W. cbn [outside]. rewrite HSS, HFSZ.
      split; [lia|].
      split; [destruct HFSlh as [Hl|Hl]; lia|].
      split; [exact Hne | exact I]. }
    (* ENT across the segment's run: it writes no byte of an entry block (they end below stklo and are never
       side-stack bytes), of the image (below GT <= FS), of the stack at or above S, or of the shadow of those *)
    assert (Hkept : forall x, ent_kept (Ghost gin gp S gregs gmem gmd gH gT) x ->
              ULFr.outside (A1W S FS) x).
    { intros x Hk.
      assert (Hout : outside (A1W S FS) x); [|exact Hout].
      unfold ent_kept in Hk. cbn [g_H g_T g_S] in Hk.
      destruct Hk as [(q & k & i & Hin & Hni & Hi & ->) | [Hik | [Habk | [(b & Hor & ->) |
                      (q & k & i & Hin & Hni & Hi & ->)]]]].
      - destruct (lw_blocks (APIf rc) gH gmem gmd q k HAH Hin) as [_ _ Hend _ Hall].
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        apply Houtapp; [exact Happq | left; lia |].
        destruct (Z_lt_le_dec (q + i) FS) as [Hl|Hl]; [left; exact Hl|].
        destruct (Z_lt_le_dec (q + i) (FS + 11571200)) as [Hl2|Hl2]; [|right; exact Hl2].
        exfalso. apply Hnfs.
        exact (a_fs_in AC.ASYMS gmem FS (q + i) HwtpFS HFSr ltac:(rewrite HFSZ; lia)).
      - pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
        apply Houtapp; [unfold app_mem, LOWMEM_END; left; lia | left; lia | left; lia].
      - unfold APPMEM_END in Habk.
        apply Houtapp; [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; lia |
                        right; lia | right; lia].
      - assert (Happb : app_mem b).
        { destruct Hor as [Hib|Hrb].
          - pose proof (img_below_GT b Hib) as X. unfold AC.GT in X.
            unfold app_mem, LOWMEM_END. left; lia.
          - unfold APPMEM_END in Hrb. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right; lia. }
        apply HshOut; [exact Happb|].
        destruct Hor as [Hib|Hrb].
        + pose proof (img_below_GT b Hib) as X. unfold AC.GT in X. left; lia.
        + right; lia.
      - (* the shadow byte of an entry-block byte, which is app memory off the side stack *)
        destruct (lw_blocks (APIf rc) gH gmem gmd q k HAH Hin) as [_ _ Hend _ Hall].
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        apply HshOut; [exact Happq|].
        destruct (Z_lt_le_dec (q + i) FS) as [Hl|Hl]; [left; exact Hl|].
        destruct (Z_lt_le_dec (q + i) (FS + 11571200)) as [Hl2|Hl2]; [|right; exact Hl2].
        exfalso. apply Hnfs. exact (a_fs_in AC.ASYMS gmem FS (q + i) HwtpFS HFSr ltac:(rewrite HFSZ; lia)). }
    assert (MUru : ULFr.munch (A1W S FS) gmem m') by exact MUr.
    assert (HENTm : ENT APIf (Ghost gin gp S gregs gmem gmd gH gT) [] m' gmd).
    { eapply ent_munch; [exact HENT0 | exact HAH | exact MUru | exact Hkept | exact Hlo1 | exact Hhi1 |
                         intros a Hia Ho; exact (proj2 (Hown1 a) Ho)]. }
    assert (HENT' : ENT APIf (Ghost gin gp S gregs gmem gmd gH gT) [] m' md')
      by (eapply ent_mat; [exact HENTm | exact Hmat]).
    (* FRA's input facts (de2516edf5), from the entry pre: the input bytes from blk_data (0 <= p and
       p + n <= 2^64 by the block's addressability, or by p = empty when n = 0) and, for n > 0, the live block and
       its addressability. The run keeps them (fra_in_keep_sh below): each input byte is app memory below
       stklo <= S - SLOT_STACK and off the side stack (a_laws_blocks), so neither it nor its shadow byte is in A1W. *)
    pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & Hempty & _).
    assert (Hinb0 : bytes_at rsegs gmem gp gin).
    { assert (Hpr : 0 <= gp /\ gp + Z.of_nat (length gin) <= 2 ^ 64).
      { destruct Hpn as [(Hn0 & Hpe) | (_ & _ & Had)].
        - rewrite Hpe. lia.
        - destruct Had as (H0 & _ & Hend & _). unfold APPMEM_END in Hend. lia. }
      split; [lia|]. split; [lia|]. intros i Hi.
      pose proof (Hblk (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id, SEGS in E. exact E. }
    assert (Hinblk0 : 0 < g_n (Ghost gin gp S gregs gmem gmd gH gT) ->
              In (gp, g_n (Ghost gin gp S gregs gmem gmd gH gT)) gH /\
              addressable gmem gp (g_n (Ghost gin gp S gregs gmem gmd gH gT))).
    { intros Hn0. destruct Hpn as [(Hn1 & _) | (_ & Hin & Had)]; [lia | split; [exact Hin | exact Had]]. }
    rewrite <- SEGS.
    enough (HI : Inv_B81090 B APIf ra (Ghost gin gp S gregs gmem gmd gH gT)
                   (mkCfg (mkst regs' (Z_to_bv 64 0x81090) m' (seg_rom (ms_segs B))) md')).
    { exact (Hbc _ _ HI). }
    unfold Inv_B81090. cbn [g_regs g_mem g_md g_H g_T g_in g_p g_S].
    exists regs', m', md', A, r.
    split; [reflexivity|].
    split.
    { unfold PREF. cbn [g_regs g_mem g_md g_H g_T g_in g_p g_S].
      split.
      { apply (AsanRTInv.RT_meta_write S A gmem m' gmd md' (A1W S FS) HRT MUr WMr).
        - unfold AsanRTInv.rt_disjoint, A1W. cbn [disjoint_from].
          unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
            RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
          rewrite HSS, HFSZ. repeat split; try exact I; left; lia.
        - intros a Ha. destruct (AsanRTInv.RT_shadow_rw _ _ _ HRT a Ha) as [Hw _].
          pose proof (a1_shadow_hi a Ha) as Hr'.
          destruct (a1_wview_some m' (wa a) ltac:(rewrite wa_unsigned by lia; lia) (WMr (wa a) Hw)) as (b & Hb).
          exists b. unfold mrd. rewrite Hb. reflexivity. }
      split; [exact (HAHm HAH1)|].
      split; [exact (ro_agree_same rsegs gmem m' Hro Hsame)|].
      split.
      { destruct Hsn as (Hcse & Hohd & Hfd'). split; [|split; [|rewrite (sl_mat_fds gmd md' Hmat); exact Hfd']].
        - destruct Hcse as (Hthrm & Hlockm). split.
          + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
            * lia.
            * rewrite Hthr in Hx. cbn in Hx. lia.
          + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
            * lia.
            * rewrite Hlock in Hx. cbn in Hx. lia.
        - intros k Hk. rewrite KBlo.
          + exact (Hohd k Hk).
          + rewrite Hhead. lia.
          + rewrite Hhead. lia. }
      split; [rewrite (AsanLift.mat_le_halted gmd md' Hmat); exact Hhalt|].
      split.
      { intros a Hin. rewrite KBlo.
        - exact (Hgimg a Hin).
        - destruct Hin as (lo & len & Hil & Hr'). unfold AF.frame_RELRO in Hil. cbn in Hil.
          destruct Hil as [E|[]]; injection E as <- <-; lia.
        - destruct Hin as (lo & len & Hil & Hr'). unfold AF.frame_RELRO in Hil. cbn in Hil.
          destruct Hil as [E|[]]; injection E as <- <-; lia. }
      split; [rewrite Hreg; exact ER2|].
      split; [destruct HAm as (HA32 & _); Z.div_mod_to_equations; lia|].
      split; [unfold AC.aspZ; rewrite Hreg, ER2; apply unsigned_lit; lia|].
      split; [rewrite Hlo2, Hlo1; exact Hstklo|].
      split; [rewrite Hreg, ER4; exact Htp|].
      split; [unfold rg; rewrite Hreg, ER8; exact ESreg|].
      split; [unfold rg; rewrite Hreg; exact ER9|].
      split; [rewrite Hreg, ER3; reflexivity|].
      split; [unfold rg; rewrite Hreg; exact ER26|].
      split; [exact (proj1 HAm)|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
      split; [exact (a1_stk_rel m' m2 (S - AF.SLOT_STACK) S Hrel ltac:(lia) ltac:(lia) ST2)|].
      split; [unfold saved_bytes; cbn [g_regs]; rewrite <- Hra; exact (a1_bytes_rel2 m' m2 _ _ Hrel SB2)|].
      split; [intros a Ha; pose proof (Herrno a Ha) as Hw; rewrite SEGS in Hw; exact (WMr (Z_to_bv 64 a) Hw)|].
      split.
      { intros a Ha. pose proof (a1_AG_low a Ha) as HaL.
        apply (a1_addr_keep gmem m' (A1W S FS) a (HAG a Ha) MUr).
        - unfold A1W. cbn [outside]. rewrite HSS, HFSZ.
          assert (Hsa : 2147450880 <= shadow_addr a < 2147450880 + 785408 /\ 2147450880 + 785408 <= shadow_addr FS)
            by (clear - HaL HGT; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
          repeat split; try exact I; lia.
        - clear - HaL. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
      (* push 5c: the whole slot window is addressable (the run writes the window's bytes, not their shadow,
         and no frame shadow is poisoned before A3) *)
      split.
      { intros a Ha. rewrite HSS in Ha.
        assert (Happa : app_mem a)
          by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; lia).
        apply (a1_addr_keep gmem m' (A1W S FS) a
                 (proj1 (proj2 (Hwin a ltac:(unfold AC.a_window; exact Ha)))) MUr).
        - apply HshOut; [exact Happa | right; lia].
        - pose proof (in_shadow_range (shadow_addr a) (shadow_of_app a Happa)). lia. }
      (* push 5c: the three ENTRY stack-top facts, read off the entry pre *)
      split; [exact Hspstkhi|]. split; [exact Hstkhi|]. split; [exact Hstkpres|].
      split; [exact HnMax|].
      split; [exact Hlive|].
      apply (fra_in_keep_sh (Ghost gin gp S gregs gmem gmd gH gT) gmem m' (A1W S FS) Hinb0 Hinblk0 MUru).
      intros x Hx. cbn [g_p] in Hx.
      destruct (Hinblk0 ltac:(lia)) as (Hin & _).
      destruct (lw_blocks (APIf rc) gH gmem gmd gp _ HAH Hin) as [_ _ Hend _ Hall].
      destruct (Hall x Hx) as (Happx & _ & _ & _ & Hnfs).
      assert (HxFS : x < FS \/ FS + 11571200 <= x).
      { destruct (Z_lt_le_dec x FS) as [Hl|Hl]; [left; exact Hl|].
        destruct (Z_lt_le_dec x (FS + 11571200)) as [Hl2|Hl2]; [|right; exact Hl2].
        exfalso. apply Hnfs. exact (a_fs_in AC.ASYMS gmem FS x HwtpFS HFSr ltac:(rewrite HFSZ; lia)). }
      split; apply (proj2 (fr_outside_lib _ _)).
      + apply Houtapp; [exact Happx | left; lia | exact HxFS].
      + apply HshOut; [exact Happx | exact HxFS]. }
    split; [exact HENT'|].
    split; [unfold rg; rewrite Hreg; exact ER10|].
    split; [exact Hr|].
    split; [unfold rg; rewrite Hreg, ER22; exact Hp|].
    split; [unfold rg; rewrite Hreg, ER18; exact Hn|].
    destruct Hrdisj as [Hr0 | (Hr32 & HrFS & HrEnd & Hrec)]; [left; exact Hr0|]. right.
    split; [exact Hr32|].
    split.
    { intros FS' HwFS' HFS'r. rewrite (a1_word_eq m' _ FS' FS HwFS' HwFSm HFS'r HFSr). lia. }
    split.
    { intros a Ha. rewrite FRAME_BYTES_val in Ha.
      exact (a_fs_in AC.ASYMS m' FS a HwFSm HFSr ltac:(rewrite HFSZ in *; lia)). }
    (* push 5b: the frame record, from the request's flag byte and back pointer, read through mem_rel *)
    destruct Hrec as (j & Hj & Erj & Hfl & Hbk).
    assert (Eflj : fs_flag FS 6 j = FS + 36352 + j).
    { unfold fs_flag. change (Z.of_nat 6) with 6. change (2 ^ 15) with 32768. change (2 ^ (15 - 6)) with 512.
      lia. }
    exists FS, j.
    split; [exact HwFSm|].
    split; [exact HFSr|].
    split; [change (fs_M 6) with 256; lia|].
    split.
    { unfold fs_frame, fs_B. change (Z.of_nat 6) with 6. change (2 ^ 20) with 1048576. change (2 ^ 6) with 64.
      lia. }
    split.
    { rewrite Eflj. exact (a1_bytes_rel2 m' m2 _ _ Hrel Hfl). }
    rewrite Eflj. replace (r + fs_B 6 - 8) with (r + 4088) by (change (fs_B 6) with 4096; lia).
    exact (a1_bytes_rel2 m' m2 _ _ Hrel Hbk).
Qed.

End Seg.
