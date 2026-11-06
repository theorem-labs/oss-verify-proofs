(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1539 of its 1674 lines of code are new or changed and 876 lines of the source are left out. *)
(* Segment R14 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the b = 0 CONFIG block-sum
   loop (head 0x818a8, latch 0x818d8 `bnez a4,818a8`) and its tail, from the cut Inv_B818a8_at b (v1.9 pc 0x818a8)
   to the cut Inv_B819a8_at b (v1.9 pc 0x819a8) (S_R14 (forms-asan-ubsan-v190.md (a working note, not in this delivery)); a Theorem Labs lane's
   S_R14 (v190-segment-table.md (a working note, not in this delivery)): CHANGED, register renamings s2 -> s11 and s9 -> s2).  rule 24: no function
   proved (a slot segment).

   The instructions the segment runs, read off the neutral listing of the v1.9.0 asan-ubsan fuzz_ctrl:

     0x818a8 add a5,a3,a4            the loop head; a3 = room = -(Phi_r + 18) mod 2^64, a4 = 32 - i
     0x818ac bne a5,s11,818b4        the UBSan trap test: the fall-through 0x818b0 `j 0x82fa0` is taken only
                                     when a5 = s11 = 32, i.e. when Phi_r + 18 + i wraps to 0; shown not taken
     0x818b4 srli a5,a0,0x3 / 0x818b8 add a5,a5,s10 / 0x818bc lb a5,0(a5)
                                     the instrumented check (error path 0x818e8 `j 0x8305c`), on the block byte
                                     Phi_r + 18 + i
     0x818c0 bnez a5,818e0           the fast arm (shadow byte 0); the slow arm 0x818e0 andi a6,a0,7 /
                                     0x818e4 blt a6,a5,818c4 rejoins, and 0x818e8 (the error path) is not
                                     reached, because the byte is addressable (CHK)
     0x818c4 lbu a5,0(a2) / 0x818c8 addi a4,a4,-1 / 0x818cc addi a0,a0,1 / 0x818d0 add a1,a1,a5 /
     0x818d4 addi a2,a2,1 / 0x818d8 bnez a4,818a8      the body and the latch
     0x818dc j 81990                 the loop exit, 32 turns done
     0x81990 zext.b a0,a1 / 0x81994 beqz a0,8199c      the sum closes: a1 mod 256 = 0, so the abort edge
                                     0x81998 `j 0x82fa4` is not taken (blocksum of the stamped control block)
     0x8199c mv a0,s4 / 0x819a0 mv a1,s2 / 0x819a4 jal 84e40 <reac_box_catalogue_match>

   The ending call is CATM = reac_box_catalogue_match, taken on its lib/B contract reac_box_catalogue_match_c.v as
   a Section Hypothesis, never on its code; its return 0x819a8 is the exit cut.  The b = 5 fragment arm is reached
   from R10's dispatch, not from this loop, and the loop's own exit 0x818dc `j 81990` runs the sum test and the
   catalogue-match call; this is what Inv_B819a8_at -- a cut at pc 0x819a8 whose a0 is the matched row -- and
   forms-asan-ubsan.md's S_R14 state.

   The loop writes no memory, so every memory fact of the entry cut reaches the call unchanged; the call writes
   only its own stack window [sp - 9136, sp), the side stack's class-0/1/2 areas and the shadow of its window.

   OFFICIAL CUTS.  The official Inv_B818a8_at carries the two registers the loop head reads and never writes --
   a3 = -(Phi_r + 18) (the room value the b = 0 prologue computes at 0x81888-0x8189c) and s11 = 32 (rg 27, read by
   the trap test 0x818ac) -- and the model fact the exit cut asks of the catalogue-match call (a0 = mrow: the match
   finds the mode row) is SlotInv.v's lemma rnb_want0.  So seg_R14 is forms-asan-ubsan.md's S_R14, with no local
   cut.  The exit's RBE carries PRA (11 spills), [A+152] = fr + 64, [A+112] = fr + 2256, [A+160] = fr + 32 and
   `addressable (fr + 2256) 72` across the call (spills at or above A, the record's shadow bytes off the call's
   writes), and s11 = 32 (the call keeps s11).  n_b is in s2 (rg 18, RF), which 0x819a0 passes as a1 and the call
   keeps.  The call's side-stack package is rebuilt from FRA at the call (Tac_fsfree fra_fp), not carried.

   The generic transport lemmas r14_* below are prover a Theorem Labs lane's seg_R6 helpers (lib/B/Prog/Seg/R6.v on this branch),
   renamed; r14_fs_ok / r14_ah / r14_fpw_* / r14_out_all are their class-0/1/2 forms (reac_box_catalogue_match
   runs __asan_stack_malloc_0, _1 and _2, where reac_ctrl_build_as runs only _0 and _1). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcLay RcEmit RcPorts RcFin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFinLib RcSynthLib RcLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcMatch RcRecLib RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_box_catalogue_match_c reac_ctrl_parse_c bcmp_wrap_c memcmp_c
  reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
(* The plain models the build_as contract speaks (ba_E, ba_X, ba_tbl), its image-B constants (BA_FR, read by RBE's
   row table), and the ending callee's image-B contract. *)
Module BAP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module BAC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_build_as_c.
Module CMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_box_catalogue_match_c.
Module RS6 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcSynth.

(* ---- byte, stack and cell helpers (seg_R6) ---- *)

(* The start register map of the run, written with mkR so the engine reads it. *)
Lemma r14_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* ---- shadow arithmetic and interval lists (F3) ---- *)

Lemma r14_sh_frame_of : forall fr k, 0 <= fr -> fr mod 8 = 0 -> 0 <= k ->
  shadow_addr (fr + 8 * k) = shadow_addr fr + k.
Proof. unfold shadow_addr. intros fr k H0 H8 Hk. Z.div_mod_to_equations. lia. Qed.

Lemma r14_in_shadow_bnd : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

Lemma r14_sh_ge : forall x L, L <= x -> shadow_addr L <= shadow_addr x.
Proof. unfold shadow_addr. intros x L H. pose proof (Z.div_le_mono L x 8 ltac:(lia) H). lia. Qed.

Lemma r14_sh_lt : forall x L, L mod 8 = 0 -> x < L -> shadow_addr x < shadow_addr L.
Proof. unfold shadow_addr. intros x L HL Hx. Z.div_mod_to_equations. lia. Qed.

Lemma r14_sh_hi : forall x, 0 <= x <= APPMEM_END -> shadow_addr x <= HIGHMEM_BEG.
Proof.
  intros x Hx. unfold shadow_addr, ASAN_K, HIGHMEM_BEG, APPMEM_END in *.
  assert (Hb : 140737488355328 / 8 = 17592186044416) by (vm_compute; reflexivity).
  pose proof (Z.div_le_mono x 140737488355328 8 ltac:(lia) ltac:(lia)) as H. lia.
Qed.

(* The byte of a shadow address inside [shadow_addr lo, shadow_addr hi) with lo a multiple of 8. *)
Lemma r14_sh_inv : forall q lo hi, lo mod 8 = 0 -> 0 <= lo -> shadow_addr lo <= q < shadow_addr hi ->
  lo <= lo + 8 * (q - shadow_addr lo) < hi /\ shadow_addr (lo + 8 * (q - shadow_addr lo)) = q.
Proof.
  intros q lo hi Hm Hlo Hq.
  assert (Hk : 0 <= q - shadow_addr lo) by lia.
  pose proof (r14_sh_frame_of lo (q - shadow_addr lo) Hlo Hm Hk) as E.
  split; [split; [lia|] | rewrite E; lia].
  destruct (Z_lt_le_dec (lo + 8 * (q - shadow_addr lo)) hi) as [H|H]; [exact H|].
  exfalso. pose proof (r14_sh_ge (lo + 8 * (q - shadow_addr lo)) hi H) as Hge. rewrite E in Hge. lia.
Qed.

Lemma r14_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

Lemma r14_addr_sub : forall m p n p' n', addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma r14_addr_of1 : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> addressable m (p + i) 1) -> addressable m p n.
Proof.
  intros m p n Hp Hn He H. split; [exact Hp|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (H i Hi) as (_ & _ & _ & HA). pose proof (HA 0 ltac:(lia)) as Hb.
  rewrite Z.add_0_r in Hb. exact Hb.
Qed.

Lemma r14_out_app : forall A C x, outside A x -> outside C x -> outside (A ++ C) x.
Proof.
  induction A as [|[lo hi] A IH]; intros C x HA HB; cbn [app outside] in *; [exact HB|].
  destruct HA as [H1 H2]. split; [exact H1 | exact (IH C x H2 HB)].
Qed.

Lemma r14_mbyte_mrd : forall m a, mbyte rsegs m a = mrd rsegs m (wa a).
Proof.
  intros m a. unfold mbyte, mrd, wa. destruct (m (Z_to_bv 64 a)); [reflexivity|].
  unfold YK11.seg_rom, PropExec.seg_rom. reflexivity.
Qed.

Lemma r14_dj_lo : forall W a n, Forall (fun r => a + n <= fst r) W -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
  apply Forall_cons_iff in H as [H1 H2]. cbn [fst] in H1.
  split; [left; exact H1 | exact (IH a n H2)].
Qed.

Lemma r14_rt_disjoint : forall W, Forall (fun r => AC.GT <= fst r) W -> rt_disjoint W.
Proof.
  intros W H. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
    RT_AGLOB_LEN.
  repeat split; apply r14_dj_lo; (eapply Forall_impl; [|exact H]);
    intros [lo hi] Hl; cbn [fst] in *; unfold AC.GT in Hl; lia.
Qed.

Lemma r14_stk : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) Hm Hw HX. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  destruct (HX a Ha) as [Ho | Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* A point of application memory is apart from the shadow of any application range. *)
Lemma r14_app_not_sh : forall x lo hi, app_mem x -> 0 <= lo -> hi <= APPMEM_END ->
  ~ (shadow_addr lo <= x < shadow_addr hi).
Proof.
  intros x lo hi Hx Hlo Hhi.
  assert (H1 : ASAN_K <= shadow_addr lo)
    by (unfold shadow_addr; pose proof (Z.div_pos lo 8 Hlo ltac:(lia)); lia).
  destruct (Z_lt_le_dec hi 0) as [Hneg|Hpos].
  - pose proof (r14_sh_ge lo hi ltac:(lia)) as Hle. lia.
  - pose proof (r14_sh_hi hi ltac:(lia)) as H2.
    unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.


(* ---- the side stack of a call that runs __asan_stack_malloc_0, _1 and _2 ---- *)

(* The side stack's runtime state after a run that writes, inside the metadata region [FS, FS + 36864), only the
   class-0, class-1 and class-2 hint words [FS, FS + 24) and their flag bytes [FS + 4096, FS + 32768): the other
   classes' cells are unchanged and the class-0/1/2 cells are the ones the run's own post states (fp_cls). *)
Lemma r14_fs_ok : forall mem mem' FS W,
  AC.a_fs_ok mem FS -> munch W mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q) ->
  (forall q, FS <= q < FS + AC.FS_SIZE -> exists b, mbyte rsegs mem' q = Some b) ->
  (forall q, FS <= q < FS + 36864 -> ~ (FS <= q < FS + 24) -> ~ (FS + 4096 <= q < FS + 32768) -> outside W q) ->
  fp_cls mem' FS 0%nat -> fp_cls mem' FS 1%nat -> fp_cls mem' FS 2%nat ->
  0 <= FS -> FS + AC.FS_SIZE <= 2 ^ 64 -> AC.a_fs_ok mem' FS.
Proof.
  intros mem mem' FS W (P1 & P2 & P3 & P4 & P5) MU Hwm Hpr Hkeep HC0 HC1 HC2 HFS0 Hsz.
  assert (HSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (KEEP : forall q, FS <= q < FS + 36864 -> ~ (FS <= q < FS + 24) ->
                   ~ (FS + 4096 <= q < FS + 32768) -> mbyte rsegs mem' q = mbyte rsegs mem q).
  { intros q Hq H1 H2. apply (KindBGlue.mbyte_munch rsegs W mem mem' q MU ltac:(lia) (Hkeep q Hq H1 H2)). }
  split.
  { intros q Hq. destruct (P1 q Hq) as (Hw & Hpa). split.
    - apply (Hwm q); [lia | exact Hw].
    - exact (Hpr q Hq). }
  split.
  { unfold word_mem. intros k Hk. rewrite KEEP by lia. exact (P2 k Hk). }
  split.
  { rewrite KEEP by lia. exact P3. }
  split.
  { intros c Hc.
    destruct (Nat.eq_dec c 0) as [->|Hn0].
    - destruct HC0 as (_ & h & flags & HH & _). exists (bv_unsigned h).
      change (AC.a_fs_hint FS 0) with (fs_hint FS 0).
      exact (KindBGlue.bytes_at_le8_word rsegs mem' (fs_hint FS 0) h HH).
    - destruct (Nat.eq_dec c 1) as [->|Hn1].
      + destruct HC1 as (_ & h & flags & HH & _). exists (bv_unsigned h).
        change (AC.a_fs_hint FS 1) with (fs_hint FS 1).
        exact (KindBGlue.bytes_at_le8_word rsegs mem' (fs_hint FS 1) h HH).
      + destruct (Nat.eq_dec c 2) as [->|Hn2].
        * destruct HC2 as (_ & h & flags & HH & _). exists (bv_unsigned h).
          change (AC.a_fs_hint FS 2) with (fs_hint FS 2).
          exact (KindBGlue.bytes_at_le8_word rsegs mem' (fs_hint FS 2) h HH).
        * destruct (P4 c Hc) as (h' & Hh'). exists h'. unfold word_mem. intros k Hk.
          assert (Hz : 3 <= Z.of_nat c <= 10) by lia.
          rewrite (KEEP (AC.a_fs_hint FS c + Z.of_nat k) ltac:(unfold AC.a_fs_hint; lia)
                     ltac:(unfold AC.a_fs_hint; lia) ltac:(unfold AC.a_fs_hint; lia)).
          exact (Hh' k Hk). }
  { intros c j Hc Hj.
    assert (FLG : forall (cc : nat) (flags : list byte),
              bytes_at rsegs mem' (fs_flag FS cc 0) flags -> Z.of_nat (length flags) = fs_M cc ->
              Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
              0 <= j < AC.a_fs_M cc ->
              mbyte rsegs mem' (AC.a_fs_flag FS cc j) = Some (Z_to_bv 8 0) \/
              mbyte rsegs mem' (AC.a_fs_flag FS cc j) = Some (Z_to_bv 8 1)).
    { intros cc flags HFl HFlen HFb Hjr.
      change (AC.a_fs_M cc) with (fs_M cc) in Hjr.
      destruct HFl as (Hb0 & Hb1 & Hb2).
      assert (Hji : (Z.to_nat j < length flags)%nat) by lia.
      pose proof (Hb2 (Z.to_nat j) Hji) as Hnb. rewrite Z2Nat.id in Hnb by lia.
      destruct (nth_error flags (Z.to_nat j)) as [bb|] eqn:Eb; [|apply nth_error_None in Eb; lia].
      rewrite Forall_forall in HFb. pose proof (HFb bb (nth_error_In flags (Z.to_nat j) Eb)) as Hv.
      change (AC.a_fs_flag FS cc j) with (fs_flag FS cc j).
      assert (Em : mbyte rsegs mem' (fs_flag FS cc j) = Some bb).
      { rewrite r14_mbyte_mrd.
        replace (wa (fs_flag FS cc j)) with (wa (fs_flag FS cc 0 + j))
          by (unfold wa, fs_flag; f_equal; lia).
        rewrite Hnb. reflexivity. }
      rewrite Em. destruct Hv as [-> | ->]; [left; reflexivity | right; reflexivity]. }
    destruct (Nat.eq_dec c 0) as [->|Hn0].
    - destruct HC0 as (_ & h & flags & _ & HFl & HFlen & HFb). exact (FLG 0%nat flags HFl HFlen HFb Hj).
    - destruct (Nat.eq_dec c 1) as [->|Hn1].
      + destruct HC1 as (_ & h & flags & _ & HFl & HFlen & HFb). exact (FLG 1%nat flags HFl HFlen HFb Hj).
      + destruct (Nat.eq_dec c 2) as [->|Hn2].
        * destruct HC2 as (_ & h & flags & _ & HFl & HFlen & HFb). exact (FLG 2%nat flags HFl HFlen HFb Hj).
        * pose proof (a_fs_flag_range FS c j Hc Hj) as Hr.
          assert (Hz : 3 <= Z.of_nat c <= 10) by lia.
          assert (Hple : 2 ^ (15 - Z.of_nat c) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
          assert (Hpge : 0 < 2 ^ (15 - Z.of_nat c)) by (apply Z.pow_pos_nonneg; lia).
          assert (Hout : ~ (FS + 4096 <= AC.a_fs_flag FS c j < FS + 32768)).
          { unfold AC.a_fs_flag in *. change (2 ^ 15) with 32768 in *. change (2 ^ 12) with 4096 in *. lia. }
          assert (Hout0 : ~ (FS <= AC.a_fs_flag FS c j < FS + 24)).
          { unfold AC.a_fs_flag in *. change (2 ^ 15) with 32768 in *. change (2 ^ 12) with 4096 in *. lia. }
          rewrite (KEEP (AC.a_fs_flag FS c j) ltac:(lia) Hout0 Hout).
          exact (P5 c j Hc Hj). }
Qed.

(* The class-0, class-1 and class-2 side-stack ranges all lie in [FS, FS + 3182592) or in its shadow. *)
Lemma r14_fpw_out : forall FS x,
  0 <= FS -> ~ (FS <= x < FS + 3182592) -> ~ (shadow_addr FS <= x < shadow_addr (FS + 3182592)) ->
  outside (fp_w [0%nat; 1%nat; 2%nat] FS) x.
Proof.
  intros FS x HFS H1 H2.
  pose proof (r14_sh_ge (FS + 36864) FS ltac:(lia)) as S1.
  pose proof (r14_sh_ge (FS + 3182592) (FS + 2134016) ltac:(lia)) as S2.
  pose proof (r14_sh_ge (FS + 1085440) FS ltac:(lia)) as S3.
  pose proof (r14_sh_ge (FS + 2134016) (FS + 36864) ltac:(lia)) as S4.
  pose proof (r14_sh_ge (FS + 2134016) (FS + 1085440) ltac:(lia)) as S5.
  pose proof (r14_sh_ge (FS + 3182592) (FS + 36864) ltac:(lia)) as S6.
  assert (E1 : fs_hint FS 0%nat = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (E2 : fs_hint FS 1%nat = FS + 8) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (E2b : fs_hint FS 2%nat = FS + 16) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (E3 : fs_flag FS 0%nat 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (E4 : fs_flag FS 1%nat 0 = FS + 20480) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (E4b : fs_flag FS 2%nat 0 = FS + 28672) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (E5 : fs_M 0%nat = 16384) by reflexivity.
  assert (E6 : fs_M 1%nat = 8192) by reflexivity.
  assert (E6b : fs_M 2%nat = 4096) by reflexivity.
  assert (E7 : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (E8 : fs_frame FS 0%nat (fs_M 0%nat) = FS + 1085440) by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  assert (E9 : fs_frame FS 1%nat 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (E10 : fs_frame FS 1%nat (fs_M 1%nat) = FS + 2134016)
    by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  assert (E11 : fs_frame FS 2%nat 0 = FS + 2134016) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (E12 : fs_frame FS 2%nat (fs_M 2%nat) = FS + 3182592)
    by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  cbn [fp_w fp_w1 flat_map app].
  rewrite E1, E2, E2b, E3, E4, E4b, E7, E8, E9, E10, E11, E12, E5, E6, E6b.
  cbn [outside]. repeat split; try lia; exact I.
Qed.

(* A byte of the side stack's metadata region that is neither a class-0/1/2 hint word nor one of their flag
   bytes is outside the call's class-0/1/2 write set: the frames begin at FS + 36864, above it. *)
Lemma r14_fpw_meta : forall FS q,
  0 <= FS -> FS <= q < FS + 36864 -> ~ (FS <= q < FS + 24) -> ~ (FS + 4096 <= q < FS + 32768) ->
  ~ (shadow_addr FS <= q < shadow_addr (FS + 3182592)) ->
  outside (fp_w [0%nat; 1%nat; 2%nat] FS) q.
Proof.
  intros FS q HFS Hq H1 H2 H3.
  pose proof (r14_sh_ge (FS + 36864) FS ltac:(lia)) as S1.
  pose proof (r14_sh_ge (FS + 3182592) (FS + 2134016) ltac:(lia)) as S2.
  pose proof (r14_sh_ge (FS + 1085440) FS ltac:(lia)) as S3.
  pose proof (r14_sh_ge (FS + 2134016) (FS + 36864) ltac:(lia)) as S4.
  pose proof (r14_sh_ge (FS + 2134016) (FS + 1085440) ltac:(lia)) as S5.
  pose proof (r14_sh_ge (FS + 3182592) (FS + 36864) ltac:(lia)) as S6.
  assert (E1 : fs_hint FS 0%nat = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (E2 : fs_hint FS 1%nat = FS + 8) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (E2b : fs_hint FS 2%nat = FS + 16) by (unfold fs_hint; cbn [Z.of_nat]; lia).
  assert (E3 : fs_flag FS 0%nat 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (E4 : fs_flag FS 1%nat 0 = FS + 20480) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (E4b : fs_flag FS 2%nat 0 = FS + 28672) by (unfold fs_flag; cbn [Z.of_nat]; lia).
  assert (E5 : fs_M 0%nat = 16384) by reflexivity.
  assert (E6 : fs_M 1%nat = 8192) by reflexivity.
  assert (E6b : fs_M 2%nat = 4096) by reflexivity.
  assert (E7 : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (E8 : fs_frame FS 0%nat (fs_M 0%nat) = FS + 1085440) by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  assert (E9 : fs_frame FS 1%nat 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (E10 : fs_frame FS 1%nat (fs_M 1%nat) = FS + 2134016)
    by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  assert (E11 : fs_frame FS 2%nat 0 = FS + 2134016) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  assert (E12 : fs_frame FS 2%nat (fs_M 2%nat) = FS + 3182592)
    by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia).
  cbn [fp_w fp_w1 flat_map app].
  rewrite E1, E2, E2b, E3, E4, E4b, E7, E8, E9, E10, E11, E12, E5, E6, E6b.
  cbn [outside]. repeat split; try lia; exact I.
Qed.

(* Every range of the class-0/1/2 write set starts at or above the image top GT. *)
Lemma r14_fpw_gt : forall FS r, AC.GT <= FS -> In r (fp_w [0%nat; 1%nat; 2%nat] FS) -> AC.GT <= fst r.
Proof.
  intros FS r HFS Hr.
  assert (HK : forall y, 0 <= y -> AC.GT <= shadow_addr y).
  { intros y Hy. unfold shadow_addr, AC.GT, ASAN_K. pose proof (Z.div_pos y 8 Hy ltac:(lia)). lia. }
  assert (HG : 0 <= FS) by (unfold AC.GT in HFS; lia).
  cbn [fp_w fp_w1 flat_map app] in Hr.
  repeat (destruct Hr as [<-|Hr]);
    try (cbn [fst]; unfold fs_hint, fs_flag, fs_frame, fs_B, fs_M; cbn [Z.of_nat]; lia);
    try (cbn [fst]; apply HK; unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
  destruct Hr.
Qed.

(* The write set of the catalogue-match call: its own window, the class-0/1/2 areas, and the window's shadow. *)
Lemma r14_out_all : forall Lo Sp FS x,
  ~ (Lo <= x < Sp) -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  ~ (shadow_addr Lo <= x < shadow_addr Sp) ->
  outside ([(Lo, Sp)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr Lo, shadow_addr Sp)]) x.
Proof.
  intros Lo Sp FS x H1 H2 H3.
  apply r14_out_app; [cbn [outside]; split; [lia | exact I]|].
  apply r14_out_app; [exact H2 | cbn [outside]; split; [lia | exact I]].
Qed.


(* One byte of a byte block, read as a one-byte block at its own address. *)
Lemma r14_ba_nth1 : forall m a bs k b, bytes_at rsegs m a bs -> nth_error bs k = Some b ->
  bytes_at rsegs m (a + Z.of_nat k) [b].
Proof.
  intros m a bs k b (H0 & H1 & H) Hk.
  assert (Hlt : (k < length bs)%nat) by (apply nth_error_Some; rewrite Hk; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros j Hj. cbn [length] in Hj. destruct j as [|j]; [|lia].
  cbn [nth_error]. rewrite Nat2Z.inj_0, Z.add_0_r. rewrite (H k Hlt). exact Hk.
Qed.

Lemma r14_ba_at : forall m a a' bs, bytes_at rsegs m a bs -> a = a' -> bytes_at rsegs m a' bs.
Proof. intros m a a' bs H <-. exact H. Qed.

(* ---- the model facts of the turn: the row address, the request size, and `go` ---- *)

(* The catalogue row the round trip passes: one of the 11 rows of BOX_CATALOGUE, 8-byte aligned. *)
Lemma r14_mrow_rng : forall inp, CAT <= mrow inp <= CAT + 296 * 10 /\ mrow inp mod 8 = 0.
Proof.
  intros inp. unfold mrow, istar, CAT_ROW, CAT_N, CAT.
  pose proof (Z.mod_pos_bound (mode inp / 2) 11 ltac:(lia)) as Hb.
  set (k := (mode inp / 2) mod 11) in *.
  split; [lia|].
  replace (0x9f620 + 296 * k) with ((81604 + 37 * k) * 8) by lia.
  apply Z_mod_mult.
Qed.

(* The request the round trip makes is 0 or a valid frame length 52 + 36 n with 2 <= n <= 40. *)
Lemma r14_rtn_bnd : forall inp x, 0 <= rt_n inp x <= 1492.
Proof.
  intros inp x. unfold rt_n. destruct (rt_E inp x) eqn:E; [|lia].
  unfold rt_E, BAP.ba_E in E. apply andb_prop in E as [E _].
  unfold em_wok in E. apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(* The width the model reads from a catalogue row is non-negative. *)
Lemma r14_bmuw_nonneg : forall mp bs, 0 <= bm_uw mp bs.
Proof.
  intros mp bs. unfold bm_uw.
  repeat match goal with |- context[if ?c then _ else _] => destruct c end;
    try lia; pose proof (Z.le_max_r (bm_in_ch bs) 2); lia.
Qed.

(* The emitted frame is len bytes long: the 18-byte header, the 32-byte control block, the zero fill and the
   two-byte trailer (RcSynthLib's rs_synth_len, RcFinLib's rcf_stamp32_len). *)
Lemma r14_lyZ_len : forall md mb nb bx, length mb = 296%nat -> length (ly_Z md mb nb bx) = 32%nat.
Proof.
  intros md mb nb bx L. unfold ly_Z. destruct (md =? 0); [reflexivity|].
  destruct (RS6.rc mb bx =? 1); [apply rs_synth_len; exact L | reflexivity].
Qed.

Lemma r14_baX_len : forall md mb nb bx, length mb = 296%nat -> length (BAP.ba_X md mb nb bx) = 32%nat.
Proof.
  intros md mb nb bx L. unfold BAP.ba_X. destruct (bx <=? 1).
  - apply rcf_stamp32_len. apply r14_lyZ_len. exact L.
  - apply r14_lyZ_len. exact L.
Qed.

Lemma r14_emfr_len : forall d6 s6 c16 t0 t1 blk len,
  length d6 = 6%nat -> length s6 = 6%nat -> length blk = 32%nat -> 52 <= len ->
  Z.of_nat (length (em_fr d6 s6 c16 t0 t1 blk len)) = len.
Proof.
  intros d6 s6 c16 t0 t1 blk len L1 L2 L3 Hl.
  unfold em_fr, em_hdr. rewrite !length_app, repeat_length. cbn [length]. lia.
Qed.

Lemma r14_rid_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fst];
    first [exact IH | apply RcIdentModel.ING_length; exact IH].
Qed.

Lemma r14_rtg_len : forall inp x, length (rt_g inp x) = 50%nat.
Proof. intros inp x. unfold rt_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma r14_fgst_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, RcFrag.fg_class. cbn [Z.eqb orb].
  destruct (RcFrag.fg_fr len g) eqn:Efr; cbn [negb fg_next]; [|exact Hs].
  assert (Hn : 1 <= RcFrag.fg_n g <= 22).
  { unfold RcFrag.fg_fr in Efr.
    apply andb_prop in Efr as [Efr _]. apply andb_prop in Efr as [Efr H22]. apply andb_prop in Efr as [_ H1].
    apply Z.leb_le in H22. apply Z.leb_le in H1. lia. }
  destruct (RcFrag.bat g 19 =? 1).
  - cbn [fg_next]. unfold RcFrag.fg_first, RcFrag.fg_body, RcFrag.bsl.
    rewrite !length_app, !length_firstn, !length_skipn, Hs, Hg. cbn [length]. lia.
  - destruct (RcFrag.fg_keep st g) eqn:Ek; cbn [negb].
    + assert (HT : RcFrag.fg_T st g <= 64).
      { unfold RcFrag.fg_keep in Ek. apply andb_prop in Ek as [_ HT]. apply Z.leb_le in HT. exact HT. }
      destruct (RcFrag.fg_close st g); cbn [negb fg_next];
        apply RcFragLib.rf_clear_length; apply RcFragLib.rf_fg_join_length; assumption.
    + cbn [fg_next]. apply RcFragLib.rf_clear_length. exact Hs.
Qed.

Lemma r14_rfg_len : forall inp b, length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RFG. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st]. unfold rp_id, fg_id.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [snd];
    first [exact IH | apply r14_fgst_len; [exact IH | apply r14_rtg_len]].
Qed.

(* ---- the model facts of the b = 0 block sum ---- *)

Lemma r14_firstn_all : forall (l1 l2 : list byte) n, (length l1 = n)%nat -> firstn n (l1 ++ l2) = l1.
Proof.
  intros l1 l2 n <-. induction l1 as [|a l1 IH]; [reflexivity|].
  cbn [length firstn app]. rewrite IH. reflexivity.
Qed.

Lemma r14_firstn_cat : forall (l1 l2 : list byte) n k, (length l1 = n)%nat ->
  firstn (n + k) (l1 ++ l2) = l1 ++ firstn k l2.
Proof.
  intros l1 l2 n k <-. induction l1 as [|a l1 IH]; [reflexivity|].
  cbn [length firstn app Nat.add]. rewrite IH. reflexivity.
Qed.

Lemma r14_skipn_app : forall (l1 l2 : list byte) n, (length l1 = n)%nat -> skipn n (l1 ++ l2) = l2.
Proof.
  intros l1 l2 n <-. induction l1 as [|a l1 IH]; [reflexivity|].
  cbn [length skipn app]. exact IH.
Qed.

(* The catalogue row the turn passes is a 296-byte image row. *)
Lemma r14_mb_len : forall inp, length (rt_mb inp) = 296%nat.
Proof.
  intros inp. unfold rt_mb, rowb, img.
  destruct (Lib.Image.image_bytes rsegs (CAT + CAT_ROW * istar inp) 296) eqn:Ei;
    [exact (Lib.Image.image_bytes_length rsegs 296 _ _ Ei) | apply repeat_length].
Qed.

(* The turn's record, when the turn makes a request at all, is at least the 52-byte minimum frame. *)
Lemma r14_rtn_lo : forall inp x, rt_n inp x <> 0 -> 52 <= rt_n inp x.
Proof.
  intros inp x H. unfold rt_n in *. destruct (rt_E inp x); [|lia].
  pose proof (r14_bmuw_nonneg (mrow inp) (firstn 8 (skipn 16 (rt_mb inp)))) as Hnn.
  unfold rt_uw in *. lia.
Qed.

(* The emitted frame's header is the 18 bytes before the control block. *)
Lemma r14_hdr_len : forall inp, length (em_hdr (OUR inp) box6 CNT16 (RcIdentModel.zb 205) (RcIdentModel.zb 234)) = 18%nat.
Proof. intros inp. unfold em_hdr. rewrite !length_app, OUR_length. reflexivity. Qed.

Lemma r14_rtF_split : forall inp b,
  rt_F inp b = em_hdr (OUR inp) box6 CNT16 (RcIdentModel.zb 205) (RcIdentModel.zb 234) ++
               (rt_X inp b ++ (repeat (Z_to_bv 8 0) (Z.to_nat (rt_n inp b - 52)) ++ [Z_to_bv 8 194; Z_to_bv 8 234])).
Proof. intros inp b. reflexivity. Qed.

(* The 50 bytes the catalogue match reads are the header and the control block. *)
Lemma r14_rtg_eq : forall inp b,
  rt_g inp b = em_hdr (OUR inp) box6 CNT16 (RcIdentModel.zb 205) (RcIdentModel.zb 234) ++ rt_X inp b.
Proof.
  intros inp b.
  assert (LH : length (em_hdr (OUR inp) box6 CNT16 (RcIdentModel.zb 205) (RcIdentModel.zb 234)) = 18%nat) by apply r14_hdr_len.
  assert (LX : length (rt_X inp b) = 32%nat) by (unfold rt_X; apply r14_baX_len; apply r14_mb_len).
  unfold rt_g, fr50, rt_F, em_fr.
  rewrite <- !app_assoc.
  change 50%nat with (18 + 32)%nat.
  rewrite (r14_firstn_cat _ _ 18 32 LH).
  rewrite (r14_firstn_all _ _ 32 LX).
  reflexivity.
Qed.

Lemma r14_skip18 : forall inp b, skipn 18 (rt_g inp b) = rt_X inp b.
Proof.
  intros inp b. rewrite r14_rtg_eq. apply r14_skipn_app. apply r14_hdr_len.
Qed.

(* The control block of turn 0 is stamped, so its 32 bytes sum to 0 mod 256 (block_sum_closes). Stated with psum
   and reached by rewriting, not by a cast: the kernel's check of `blocksum (rt_X ..) = 0` against its unfolding
   at a model input runs the model term. *)
Lemma r14_bsum_eq : forall bs, blocksum bs = psum bs 32 mod 256.
Proof. intros bs. reflexivity. Qed.

Lemma r14_blocksum : forall inp b, b <= 1 -> psum (rt_X inp b) 32 mod 256 = 0.
Proof.
  intros inp b Hb. rewrite <- r14_bsum_eq. unfold rt_X, BAP.ba_X.
  replace (b <=? 1) with true by (symmetry; apply Z.leb_le; exact Hb). cbv iota.
  apply rcf_stamp32_sum. apply r14_lyZ_len. apply r14_mb_len.
Qed.

Lemma r14_blocksum0 : forall inp, psum (rt_X inp (Z.of_nat 0%nat)) 32 mod 256 = 0.
Proof. intros inp. apply r14_blocksum. cbn. lia. Qed.

(* The block bytes in memory: the record's bytes from its 18th on. *)
Lemma r14_blk_bytes : forall inp b m phi,
  bytes_at rsegs m phi (rt_F inp b) -> bytes_at rsegs m (phi + 18) (rt_X inp b).
Proof.
  intros inp b m phi Hb. rewrite r14_rtF_split in Hb.
  apply bytes_at_app in Hb. destruct Hb as (_ & Hb).
  rewrite r14_hdr_len in Hb. change (Z.of_nat 18) with 18 in Hb.
  apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Lemma r14_g_bytes : forall inp b m phi,
  bytes_at rsegs m phi (rt_F inp b) -> bytes_at rsegs m phi (rt_g inp b).
Proof.
  intros inp b m phi Hb. pose proof Hb as Hb2.
  rewrite r14_rtF_split in Hb. apply bytes_at_app in Hb. destruct Hb as (H1 & _).
  pose proof (r14_blk_bytes inp b m phi Hb2) as H2.
  rewrite r14_rtg_eq. apply (proj2 (bytes_at_app rsegs m phi _ _)). split; [exact H1|].
  rewrite r14_hdr_len. change (Z.of_nat 18) with 18. exact H2.
Qed.

Lemma r14_rtF_len : forall inp b, 52 <= rt_n inp b -> Z.of_nat (length (rt_F inp b)) = rt_n inp b.
Proof.
  intros inp b Hl. unfold rt_F. apply r14_emfr_len;
    [apply OUR_length | reflexivity | unfold rt_X; apply r14_baX_len; apply r14_mb_len | exact Hl].
Qed.

(* The room word -(phi + 18) the prologue leaves in a3 is 2^64 - 18 - phi. *)
Lemma r14_room : forall phi, 0 <= phi <= 140737488355328 ->
  Z_to_bv 64 (- (phi + 18)) = Z_to_bv 64 (18446744073709551598 - phi).
Proof.
  intros phi H. rewrite <- (ZBridge.Z_to_bv_mod64 (- (phi + 18))). f_equal.
  change (2 ^ 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

(* ---- the 32-turn block-sum loop 0x818a8 .. 0x818dc (no memory write) ---- *)

Section Loop.
  Variables (ra0 sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p off : Z) (bs : list byte)
    (W : list ivl) (Q : machine_state -> Prop).
  Hypothesis Hp : 4096 <= p.
  Hypothesis Hp50 : p + 50 <= APPMEM_END.
  Hypothesis Hlen : length bs = 32%nat.
  Hypothesis HB : bytes_at rsegs m (p + 18) bs.
  Hypothesis HSR : asan_shadow_rd rsegs m off (p + 18) 32 W.
  Hypothesis HAD : asan_addressable rsegs m off (p + 18) 32.

  Abbreviation ST pc x10 x11 x12 x14 x15 x16 :=
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 (Z_to_bv 64 (18446744073709551598 - p)) x14 x15 x16 a7
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 off) (Z_to_bv 64 32) t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  Hypothesis EXIT : forall x10 x12 x14 x15 x16,
    evt rsegs Q (ST 0x818dc x10 (Z_to_bv 64 (psum bs 32)) x12 x14 x15 x16).

  Lemma r14_loop : forall n i x15 x16,
    (i + n = 32)%nat -> (0 < n)%nat ->
    evt rsegs Q (ST 0x818a8 (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
                    (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) x15 x16).
  Proof.
    assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
    induction n as [|n IH]; intros i x15 x16 Hin Hn; [lia|].
    assert (BODY : forall y15 y16,
      evt rsegs Q (ST 0x818c4 (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i))
                      (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (32 - Z.of_nat i)) y15 y16)).
    { intros y15 y16.
      pose proof (rd_byte rsegs m (p + 18) bs i HB ltac:(lia)) as RD.
      pose proof (psum_range bs i) as PR.
      step. step. step. step.
      rewrite psum_S_zxb.
      step. step.
      rewrite (rc_eqb0 (32 - Z.of_nat i + -1)) by lia.
      destruct n as [|n].
      - replace (32 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb].
        replace i with 31%nat in * by lia.
        apply EXIT.
      - replace (32 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb].
        replace (32 - Z.of_nat i + -1) with (32 - Z.of_nat (S i)) by lia.
        replace (p + 18 + Z.of_nat i + 1) with (p + 18 + Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    (* 0x818a8 add a5,a3,a4 ; 0x818ac bne a5,s11 -- the UBSan trap test, not taken *)
    step. step.
    lazymatch goal with
    | |- context [bv_eqb (Z_to_bv 64 ?E) (Z_to_bv 64 32)] =>
        rewrite (eqb_le64 E 32) by lia;
        replace (E =? 32) with false by (symmetry; apply Z.eqb_neq; lia)
    end.
    cbn [negb].
    (* 0x818b4 srli / 0x818b8 add / 0x818bc lb -- the instrumented check, error path not reached *)
    destruct (asan_shadow_read rsegs m off (p + 18) 32 W (Z.of_nat i) HSR ltac:(lia)) as (k & RK & BK).
    pose proof (HAD (Z.of_nat i) k ltac:(lia) BK) as OK.
    pose proof (rc_byte_signed k) as KR.
    clear BK.
    step.
    rewrite (unsigned_lit (p + 18 + Z.of_nat i)) by lia. rewrite rc_shr3.
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k)) by lia.
    destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite (unsigned_lit (p + 18 + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((p + 18 + Z.of_nat i) mod 8) (bv_signed k))
        by (pose proof (Z.mod_pos_bound (p + 18 + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((p + 18 + Z.of_nat i) mod 8 <? bv_signed k) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.
End Loop.


(* ---- the run of the segment: the 32-turn loop, the sum test and the catalogue-match call ---- *)

(* The state the run reaches at 0x819a8: a0 is the matched row, the callee-saved registers are kept, and the
   memory facts the exit cut and the caller's FRA rebuild need. *)
Definition r14_post (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (sp0 gp tp s0 s1 s3 s5 s6 s7 s8 s9 : word) (p Sp FS len : Z) (fb : list byte) : machine_state -> Prop :=
  fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
    ms' = MS R F (Z_to_bv 64 0x819a8) fc None m' (seg_rom rsegs) /\
    getr R 1 = Z_to_bv 64 0x819a8 /\ getr R 2 = sp0 /\ getr R 3 = gp /\ getr R 4 = tp /\
    getr R 8 = s0 /\ getr R 9 = s1 /\ getr R 10 = Z_to_bv 64 (want CMC.CM_T len fb) /\
    getr R 18 = Z_to_bv 64 len /\ getr R 19 = s3 /\ getr R 20 = Z_to_bv 64 p /\ getr R 21 = s5 /\
    getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
    getr R 26 = Z_to_bv 64 ASAN_K /\ getr R 27 = Z_to_bv 64 32 /\
    munch ([(Sp - CMC.CM_K, Sp)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++
           [(shadow_addr (Sp - CMC.CM_K), shadow_addr Sp)]) m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (Sp - CMC.CM_K) Sp /\
    asan_cells m' /\ shadow_rw m' /\ addressable m' (Sp - CMC.CM_K) CMC.CM_K /\
    fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (Sp - CMC.CM_K) Sp
      (CMC.reac_box_catalogue_match_W Sp) (CMC.reac_box_catalogue_match_D p len) /\
    CMC.reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (Sp - CMC.CM_K) Sp.

Lemma r14_evt : CMC.reac_box_catalogue_match_contract ->
  forall (ra0 gp tp t0 t1 t2 s0 s1 a5 a6 a7 s3 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (p Sp FS len : Z) (i : nat) (bs fb : list byte),
    4096 <= p -> p + 50 <= APPMEM_END -> 50 <= len -> 0 <= len < 2 ^ 64 -> (i < 32)%nat ->
    length bs = 32%nat -> bytes_at rsegs m (p + 18) bs -> psum bs 32 mod 256 = 0 ->
    length fb = 50%nat -> bytes_at rsegs m p fb ->
    addressable m p 50 -> app_mem (p + 50) ->
    Sp < 2 ^ 64 -> Sp mod 16 = 0 -> CMC.CM_K <= Sp -> p + 50 <= Sp - CMC.CM_K ->
    stk rsegs m (Sp - CMC.CM_K) Sp ->
    (forall a, Sp - CMC.CM_K <= a < Sp -> seg_rom rsegs (wa a) = None) ->
    (forall a, CMC.CM_T <= a < CMC.CM_T + 3256 -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= Sp - CMC.CM_K -> Sp <= APPMEM_END -> addressable m (Sp - CMC.CM_K) CMC.CM_K ->
    addressable m CMC.CM_T 3256 -> addressable m reac_ctrl_parse_c.REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m bcmp_wrap_c.REAL_BCMP (le8 (wa bcmp_wrap_c.BCMP)) ->
    bytes_at rsegs m bcmp_wrap_c.REAL_MEMCMP (le8 (wa memcmp_c.MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - CMC.CM_K) Sp
      (CMC.reac_box_catalogue_match_W Sp) (CMC.reac_box_catalogue_match_D p len) ->
    CMC.reac_box_catalogue_match_tls m (bv_unsigned tp) FS (Sp - CMC.CM_K) Sp ->
    evt rsegs (r14_post F fc m (Z_to_bv 64 Sp) gp tp s0 s1 s3 s5 s6 s7 s8 s9 p Sp FS len fb)
      (MS (mkR ra0 (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1
               (Z_to_bv 64 (p + 18 + Z.of_nat i)) (Z_to_bv 64 (psum bs i)) (Z_to_bv 64 (p + 18 + Z.of_nat i))
               (Z_to_bv 64 (18446744073709551598 - p)) (Z_to_bv 64 (32 - Z.of_nat i)) a5 a6 a7
               (Z_to_bv 64 len) s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 32)
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x818a8) fc None m (seg_rom rsegs)).
Proof.
  intros CATM ra0 gp tp t0 t1 t2 s0 s1 a5 a6 a7 s3 s5 s6 s7 s8 s9 t3 t4 t5 t6 F fc m p Sp FS len i bs fb
    Hp Hp50 Hlen50 Hlen64 Hi Hbsl Hbsat Hsum Hfbl Hfbat HADp HAPPp
    HSp64 HSp16 HSpK HpSp HSTK HROM HCAT HMI HAC HSW HHM HSPapp HAWwin HACAT HBC
    HBCMP HMEMCMP HGOTCF HCF1 HCF2 HFP HTLS.
  unfold CMC.reac_box_catalogue_match_contract, CMC.REAC_BOX_CATALOGUE_MATCH in CATM.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  pose proof (addressable_sub m p 50 18 32 HADp ltac:(lia) ltac:(lia) ltac:(lia)) as HAD18.
  pose proof (rt_shadow_rd m (p + 18) 32 [] HAD18 (fun x _ => I)) as HSRd.
  pose proof (rt_addressable m (p + 18) 32 HAD18) as HADr.
  assert (HEXIT : forall x10 x12 x14 x15 x16,
    evt rsegs (r14_post F fc m (Z_to_bv 64 Sp) gp tp s0 s1 s3 s5 s6 s7 s8 s9 p Sp FS len fb)
      (MS (mkR ra0 (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 (psum bs 32)) x12
               (Z_to_bv 64 (18446744073709551598 - p)) x14 x15 x16 a7
               (Z_to_bv 64 len) s3 (Z_to_bv 64 p) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) (Z_to_bv 64 32)
               t3 t4 t5 t6)
          F (Z_to_bv 64 0x818dc) fc None m (seg_rom rsegs))).
  { intros x10 x12 x14 x15 x16.
    pose proof (psum_range bs 32) as PR32. change (Z.of_nat 32) with 32 in PR32.
    (* 0x818dc j 81990 ; 0x81990 zext.b a0,a1 ; 0x81994 beqz a0,8199c -- the sum closes *)
    step. step. step.
    rewrite rf_land255 by lia.
    rewrite Hsum. change (0 =? 0) with true. cbn [negb]. cbv iota.
    (* 0x8199c mv a0,s4 ; 0x819a0 mv a1,s2 ; 0x819a4 jal reac_box_catalogue_match *)
    step. step.
    rewrite ?(Z.add_0_r p), ?(Z.add_0_r len), ?(Z.add_0_l p), ?(Z.add_0_l len).
    step.
    eapply evt_cut.
    { eapply CATM with (fb := fb) (FS := FS);
        try reflexivity; try assumption; try lia.
      - intros _. split; [lia|]. split; [lia|]. split; [exact Hfbat | left; lia].
      - intros _. split; [exact HADp | exact HAPPp]. }
    intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                    Ems & MU & WM & MI & ST & AC' & SW' & AW & FP' & TLS').
    subst ms'.
    replace (ret_pc (Z_to_bv 64 0x819a8)) with (Z_to_bv 64 0x819a8)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    apply evt_done. unfold r14_post. do 2 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact AC'|]. split; [exact SW'|]. split; [exact AW|]. split; [exact FP' | exact TLS']. }
  apply (r14_loop ra0 (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a7 (Z_to_bv 64 len) s3 (Z_to_bv 64 p) s5 s6 s7 s8
           s9 t3 t4 t5 t6 F fc m p ASAN_K bs []
           (r14_post F fc m (Z_to_bv 64 Sp) gp tp s0 s1 s3 s5 s6 s7 s8 s9 p Sp FS len fb)
           Hp Hp50 Hbsl Hbsat HSRd HADr HEXIT (32 - i)%nat i a5 a6 ltac:(lia) ltac:(lia)).
Qed.

(* ---- the normalized memory: every address at or above GT is read-write in the image (R4) ---- *)

Lemma r14_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r14_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r14_ro_false : forall x : word, 0x5fe000 <= bv_unsigned x -> Lib.Mem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (KindBGlue.kb_find_segment _ _ _ _ E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) r14_img_top s Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs.
  pose proof (N2Z.is_nonneg (seg_size s)). exfalso. lia.
Qed.

Lemma r14_ro_wa : forall a, 0x5fe000 <= a < 2 ^ 64 -> Lib.Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Ha. apply r14_ro_false. rewrite wa_unsigned by lia. lia. Qed.

Lemma r14_shadow_gt : forall a, in_shadow a -> 0x5fe000 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. Qed.

Lemma r14_srw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r14_shadow_gt a Ha) as Hr. split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r14_ro_wa a Hr)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r14_srw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (r14_shadow_gt a Ha) as Hr. split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r14_ro_wa a Hr)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r14_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r14_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r14_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (r14_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

(* The runtime cells, the thread cells and the side stack's state are byte facts, so they move with the bytes. *)
Lemma r14_cells_tr : forall m m0, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  asan_cells m -> asan_cells m0.
Proof.
  intros m m0 TB H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply TB; assumption.
Qed.

(* addressable reads only shadow bytes through mrd, which mem_rel keeps. *)
Lemma r14_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite <- (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma r14_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma r14_tls_tr : forall m m0 TP DT TS C T DB k,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells m0 TP DT TS C T DB k.
Proof.
  intros m m0 TP DT TS C T DB k TB
    (T1 & T2 & T3 & T4 & T5 & Hk & T6 & T7 & T8 & T9 & (tb & te & T10) & T11 & T12 & T13 & T14 & T15 & T16 &
     HDB & T17).
  unfold asan_tls_cells.
  repeat match goal with |- _ /\ _ => split end.
  all: try (apply TB; assumption).
  all: try lia.
  all: try assumption.
  exists tb, te. apply TB. exact T10.
Qed.

Lemma r14_cls_tr : forall m m0 FS c, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  fp_cls m FS c -> fp_cls m0 FS c.
Proof.
  intros m m0 FS c TB (Hc & h & flags & HH & HF & HFl & HFb).
  split; [exact Hc|]. exists h, flags. split; [apply TB; exact HH|]. split; [apply TB; exact HF|].
  split; [exact HFl | exact HFb].
Qed.

Lemma r14_fp_tr : forall m m0 cs TP FS lo hi W D,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  (forall l h, 0x5fe000 <= l -> stk rsegs m l h -> stk rsegs m0 l h) ->
  fp cs m TP FS lo hi W D -> fp cs m0 TP FS lo hi W D.
Proof.
  intros m m0 cs TP FS lo hi W D TB TSk
    (DT & TSv & C & T & DB & k & Htls & Htp & (P1 & P2 & P3 & P4 & P5) & H88 & H96 & Hcls & Hlo & Happ &
     Hd1 & Hd2).
  exists DT, TSv, C, T, DB, k.
  split; [exact (r14_tls_tr m m0 TP DT TSv C T DB k TB Htls)|].
  split; [apply TB; exact Htp|].
  split.
  { split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    apply TSk; [unfold ASAN_GT in P3; lia | exact P5]. }
  split; [apply TB; exact H88|]. split; [apply TB; exact H96|].
  split; [eapply Forall_impl; [|exact Hcls]; intros c Hc; exact (r14_cls_tr m m0 FS c TB Hc)|].
  split; [exact Hlo|]. split; [exact Happ|]. split; [exact Hd1 | exact Hd2].
Qed.

(* ---- the segment on the cuts ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.

(* The run lemma: an evt on the normalized memory, lifted to SR on the real configuration (R4's r4_run). *)
Section Run.
Context {fx : FPState}.

Lemma r14_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m0', ms = MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs) /\ K R pc' m0')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m0' regs' m' md', K R pc' m0' -> (forall r, getr regs' r = getr R r) ->
     mem_rel rsegs m' m0' -> ro_same rsegs mem m' -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hro HE HK.
  pose proof (evt_normalize rsegs _ (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs) r14_wx Hro HE)
    as HE'.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE' | exact Hh |].
  intros ms' md' (can & (s0 & (R & pc' & m0' & Es0 & HKR) & Hrel & Hsame) & Heq) Hmat.
  subst s0.
  destruct can as [cr cf cp cs cv cc cm co].
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  destruct Hrel as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS] in *.
  subst.
  apply (HK _ _ _ regs' _ md' HKR); [apply KindBGlue.kb_getr_eqv; exact HR | exact E8 | exact Hsame | exact Hmat].
Qed.

End Run.


(* ---- The Contract.v laws whose conclusion lists this file takes apart: each one ONCE, here (a Theorem Labs lane via a Theorem Labs lane
   15:32Z: the next generation then breaks one line per law, not every site). ---- *)

(* a_laws_fs_place: the side stack FS is above GT, ends at or below stklo, and is application memory. *)
Lemma r14_fs_place : forall (API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT) H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros API H mem md FS HAH Hw HFS.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H mem md FS HAH Hw HFS)
    as (HGT & Hend & _ & Happ).
  split; [exact HGT|]. split; [exact Hend | exact Happ].
Qed.

(* a_laws_blocks: a live block (p, n) is at or above 4096, ends at or below stklo, and each of its bytes is
   application memory off the side stack. *)
Lemma r14_blocks : forall (API : AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT) H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT API H mem md -> In (p, n) H ->
  4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros API H mem md p n HAH Hin.
  destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT API) H mem md p n HAH Hin)
    as (_ & H4096 & Hstk & _ & Hb).
  split; [exact H4096|]. split; [exact Hstk|].
  intros a Ha. destruct (Hb a Ha) as (Happ & _ & _ & _ & Hfs). exact (conj Happ Hfs).
Qed.

Section R14.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The ending callee reac_box_catalogue_match (CATM@0x819a4), taken on its lib/B contract, never on its code. *)
Hypothesis CATMH : CMC.reac_box_catalogue_match_contract.

(* ---- facts read off FRA (F3's f3_fr_* / f3_A_app / f3_sh_in) ---- *)

Lemma r14_sh_in : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x.
Proof.
  intros g fr hb regs mem md HFRA x Hx.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ). unfold AC.GT in Hgt.
  assert (Hfrm : fr mod 32 = 0).
  { destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
      Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & _). exact Hfrm. }
  assert (H8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = x).
  { rewrite r14_sh_frame_of by lia. unfold Sfr. lia. }
  rewrite <- E. apply shadow_of_app. apply Happ. lia.
Qed.

(* The registered globals of the image lie below the image top GT, and a range inside one of them is addressable. *)
Lemma r14_ag_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (HB : forallb (fun r => (0 <=? fst r) && (fst r + snd r <=? AC.GT)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB. pose proof (HB _ Hin) as Hb.
  apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
  cbn [fst snd] in *. lia.
Qed.

Lemma r14_ag : forall m p n lo len,
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  In (lo, len) AF.frame_AG -> 0 <= lo -> lo <= p -> 0 <= n -> p + n <= lo + len -> lo + len <= AC.GT ->
  addressable m p n.
Proof.
  intros m p n lo len HAG Hin Hlo0 Hlo Hn Hhi HGT.
  apply r14_addr_of1; [lia | exact Hn | unfold AC.GT, APPMEM_END in *; lia |].
  intros i Hi. apply HAG. exists lo, len. split; [exact Hin | lia].
Qed.

Ltac r14_in := unfold AF.frame_AG; repeat first [ left; reflexivity | right ].

(* The spill base named by a spill conjunct is the A of register 9 (R4's r4_spill_A). *)
Lemma r14_spill_A : forall (regs : bvmap 5 word) m off v A A1,
  rg regs 9 A1 -> q64 m (A1 + off) v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off -> A1 = A.
Proof.
  intros regs m off v A A1 H1 Hq H2 HA0 HAe Hoff.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. change (Z.of_nat 8) with 8 in Hq.
  pose proof (rg_eq64 regs 9 A1 A H1 H2) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* FSREC (SlotInv.v's side-arm FakeStack frame record) across a run that writes none of its bytes: the tp word
   (in the image, below GT), the class-6 flag byte FS + 36352 + j (below FS + 36864) and the slot's last word
   fr + 4088 (fr = FS + 6328320 + 4096 j).  Tac_slot's fsrec_munch / fsrec_munch_lo do not apply to the build_as
   call: its write set holds app bytes outside the frame body (its window) and bytes below stklo (the class-0 /
   class-1 side-stack areas), so the premise here names the three byte groups themselves. *)
Lemma r14_fsrec : forall mem mem' W fr,
  FSREC fr mem -> munch W mem mem' ->
  (forall x, 0 <= x < AC.GT -> outside W x) ->
  (forall FS j x, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> 0 <= j < 256 ->
     fr = FS + 6328320 + j * 4096 ->
     (FS + 36352 <= x < FS + 36864 \/ fr + 3136 <= x < fr + 4096) -> outside W x) ->
  FSREC fr mem'.
Proof.
  intros mem mem' W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) MU HWlo HW.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HB6 : fs_B 6 = 4096) by reflexivity.
  assert (HM6 : fs_M 6 = 256) by reflexivity.
  assert (Hfl : fs_flag FS 6 j = FS + 36352 + j) by (unfold fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold fs_frame, fs_B; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < AC.GT)
      by (rewrite HGTv; unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by (rewrite HGTv in Hx; lia). apply HWlo. exact Hx. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply (HW FS j x Htp HFSr Hj Hfrv). left. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply (HW FS j x Htp HFSr Hj Hfrv). right. rewrite HB6 in Hx. lia. }
Qed.

(* FRA moves across a run whose write set W keeps: the image and the runtime cells below GT, the frame header,
   everything at or above the spill base A, the frame's 392 shadow bytes; whose written entry-window bytes are
   readable afterwards; which keeps every shadow byte readable (so RT_meta_write); and after which the registered
   globals and the slot window outside the frame are still addressable (F3's f3_fra_run, R4's r4_fra). *)
Lemma r14_fra_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W -> shadow_rw mem' ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, 0 <= x < AC.GT -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall x, bv_unsigned (getr regs 9) <= x -> outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + 392 -> outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HSW' HAH' HSTK HWlo HWhdr HWA HWsh HWwin HAG' HWA'
    HREC HWin E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA0 &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWA.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x Hx0 Hx1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. apply HWlo. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD (fun a Ha => proj2 (HSW' a Ha)))|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA448|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS0 Hw HFSr. apply (Hfsb FS0); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * exact (HREC Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen, FRAME_SHADOW_val.
    change (Z.of_nat (Z.to_nat 392)) with 392. intros x Hx. apply HWsh. lia. }
  split.
  { exact (r14_stk W mem mem' _ _ Hwin MU WM HWwin). }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWA. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  exact (fra_in_keep_sh g mem mem' W Hinb Hinblk MU HWin).
Qed.


(* Above GT the image has no bytes, so the call's stack window holds no image byte (A3's a3_seg_rom_none). *)
Definition r14_tops (sgs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sgs.

Lemma r14_find_below : forall sgs top x n s,
  r14_tops sgs top = true -> find_segment sgs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction sgs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold r14_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma r14_tops_GT : r14_tops rsegs AC.GT = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r14_rom_none : forall x, AC.GT <= x -> x < 2 ^ 64 -> seg_rom rsegs (wa x) = None.
Proof.
  intros x H1 H2. assert (H1' : 6283264 <= x) by (unfold AC.GT in H1; lia).
  apply seg_rom_unmapped.
  destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. destruct (r14_find_below rsegs AC.GT (bv_unsigned (wa x)) 1 s r14_tops_GT E ltac:(lia)) as [L|L];
    [rewrite wa_unsigned in L by lia; unfold AC.GT in L; lia | discriminate L].
Qed.

(* The heap invariant, ownership and the stack bounds across the catalogue-match call: the write set touches the
   call's stack window, the class-0/1/2 side-stack areas and the shadow of the window, so AH moves by
   a_laws_fs_store with the side stack's state rebuilt by r14_fs_ok. *)
Lemma r14_ah : forall g fr hb regs mem mem' md W FS,
  FRA B APIf ra g fr hb regs mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS + AC.FS_SIZE <= 2 ^ 64 ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall q, FS <= q < FS + AC.FS_SIZE -> exists b, mbyte rsegs mem' q = Some b) ->
  (forall q, FS <= q < FS + 36864 -> ~ (FS <= q < FS + 24) -> ~ (FS + 4096 <= q < FS + 32768) -> outside W q) ->
  fp_cls mem' FS 0%nat -> fp_cls mem' FS 1%nat -> fp_cls mem' FS 2%nat ->
  (forall q, 0 <= q < 2 ^ 64 ->
     ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
     ~ (FS <= q < FS + AC.FS_SIZE) ->
     ~ (exists bb, FS <= bb < FS + AC.FS_SIZE /\ q = shadow_addr bb) ->
     mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros g fr hb regs mem mem' md W FS HFRA Hwtp HFSr HFSsz MU WM Hpres Hkeep HC0 HC1 HC2 Hagree.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (HAH : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md).
  { destruct HFRA as (A & sp & s5 & _ & HAH & _). exact HAH. }
  assert (Hwrit : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)).
  assert (Hok : AC.a_fs_ok mem FS)
    by exact (proj1 (AC.a_laws_fs_state _ _ _ _ _ LAWS (hb ++ g_H g) mem md FS HAH Hwtp HFSr)).
  pose proof (r14_fs_ok mem mem' FS W Hok MU Hwrit Hpres Hkeep HC0 HC1 HC2 ltac:(lia) HFSsz) as Hok'.
  exact (AC.a_laws_fs_store _ _ _ _ _ LAWS (hb ++ g_H g) mem mem' md FS HAH Hwtp HFSr Hagree Hwrit Hok').
Qed.


(* ---- the segment lemma ---- *)

Lemma seg_R14 : forall b : nat, Hat B APIf ra (Inv_B819a8_at B APIf ra) b -> Hat B APIf ra (Inv_B818a8_at B APIf ra) b.
Proof.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct HInv as (phi & i & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hble & HHB & Hr22 & HOUR & HCUR &
    HRBE & Hs5r & Hile & Hr10 & Hr12 & Hr14 & Hb0 & Hilt & Hr11 & HRF & Hsl24 & Hsl16 & Hsl96 & Hsp120 &
    HA2528 & Hr13 & Hr27).
  subst b c. rewrite SEGS.
  pose proof (rnb_want0 g 0%nat eq_refl) as HWANT.
  destruct HRBE as (B128 & B312 & B272 & B264 & B256 & B248 & B56 & B184 & B144 & B8 & B32 & B24 & B16 &
                    B96 & B120 & B240 & B232 & B224 & B176 & B208 & B64 & BOUT & BID38 & BNAME & BOUR & BTBL &
                    BBOX & BMROW & BPRA & B152 & B112 & BA2256 & B160).
  destruct HRF as (HRFb & Hr18). destruct HRFb as (HRB & Hrnb0 & Hr20 & Hphib).
  destruct HRB as (_ & _ & _ & _ & HIDB & HFGB).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & spv & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspillf & Hself & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  destruct (fra_win B APIf ra g fr (hb1 phi (rnb g 0%nat)) regs mem md HFRA) as (Hlostk & Hstkw).
  destruct (fra_frame B APIf ra g fr (hb1 phi (rnb g 0%nat)) regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (fra_app B APIf ra g fr (hb1 phi (rnb g 0%nat)) regs mem md HFRA) as (HGTfr & Happ).
  pose proof (r14_sh_in g fr (hb1 phi (rnb g 0%nat)) regs mem md HFRA) as HshIn.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (rnb g 0%nat) ++ g_H g) mem md HAH) as Hhigh.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HACm.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSWm.
  (* the turn's record block (phi, n_0): a live harness block of 52 .. 1492 bytes below stklo (HBR) *)
  assert (Hrnblo : 52 <= rnb g 0%nat) by exact (r14_rtn_lo (g_in g) (Z.of_nat 0%nat) Hrnb0).
  assert (Hrnbhi : rnb g 0%nat <= 1492) by exact (proj2 (r14_rtn_bnd (g_in g) (Z.of_nat 0%nat))).
  assert (Hinhb : In (phi, rnb g 0%nat) (hb1 phi (rnb g 0%nat) ++ g_H g))
    by (cbn [hb1 app In]; left; reflexivity).
  (* the catalogue-match call's side-stack package (classes 0, 1, 2; window CM_K; the contract's W and D),
     rebuilt from FRA (Tac_fsfree fra_fp) *)
  assert (Hcs3 : forall c, In c [0%nat; 1%nat; 2%nat] -> (c <= 5)%nat) by (intros c Hc; cbn [In] in Hc; lia).
  assert (HKcm : 8 <= CMC.CM_K <= FN_STACK) by (change CMC.CM_K with 9136; change FN_STACK with 1044480; lia).
  assert (HWcm : forall w, In w (CMC.reac_box_catalogue_match_W (AC.aspZ regs)) ->
            (g_S g - AF.SLOT_STACK <= fst w /\ snd w <= g_S g) \/ (fr <= fst w /\ snd w <= fr + FRAME_BYTES) \/
            (Sfr fr <= fst w /\ snd w <= Sfr fr + FRAME_SHADOW)).
  { intros w Hw. unfold CMC.reac_box_catalogue_match_W in Hw. cbn [In] in Hw. destruct Hw as [<- | []].
    left. cbn [fst snd]. rewrite Haspz. change CMC.CM_K with 9136. change AF.SLOT_STACK with 1048576. lia. }
  assert (HDcm : forall d, In d (CMC.reac_box_catalogue_match_D phi (rnb g 0%nat)) -> snd d <= AC.GT \/
            (fr <= fst d /\ snd d <= fr + FRAME_BYTES) \/
            (fst d < snd d /\ exists p n, In (p, n) (hb1 phi (rnb g 0%nat) ++ g_H g) /\ p <= fst d /\
                                           snd d <= p + n)).
  { intros d Hd. unfold CMC.reac_box_catalogue_match_D in Hd.
    replace (rnb g 0%nat <? 50) with false in Hd by (symmetry; apply Z.ltb_ge; lia).
    cbn [In] in Hd. destruct Hd as [<- | []]. right; right. cbn [fst snd].
    split; [lia|]. exists phi, (rnb g 0%nat). split; [exact Hinhb | lia]. }
  destruct (fra_fp B APIf ra g fr (hb1 phi (rnb g 0%nat)) regs mem md [0%nat; 1%nat; 2%nat] CMC.CM_K
              (CMC.reac_box_catalogue_match_W (AC.aspZ regs)) (CMC.reac_box_catalogue_match_D phi (rnb g 0%nat))
              HFRA Hcs3 HKcm HWcm HDcm) as (FS & HFP & HTLS & HDJfr & _).
  unfold AC.aspZ in *.
  (* numbers *)
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HCMK : CMC.CM_K = 9136) by reflexivity.
  assert (HCMT : CMC.CM_T = 652832) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HKv : ASAN_K = 2147450880) by reflexivity.
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HFSZ' : FS_SIZE = 11571200) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  assert (Hfr0 : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H1, H2. lia. }
  pose proof (Hplace CMC.CM_K ltac:(lia)) as Hsep.
  assert (HbvA2 : fr + 3136 <= A) by (rewrite HbvA in HfrA; exact HfrA).
  (* the record block's placement *)
  destruct (r14_blocks (APIf rc) (hb1 phi (rnb g 0%nat) ++ g_H g) mem md phi (rnb g 0%nat) HAH Hinhb)
    as (Hphi4 & Hphistk & Hphiall).
  destruct HHB as (Hphi0 & HAphi).
  assert (Hasz : AC.a_size (rnb g 0%nat) = rnb g 0%nat) by (unfold AC.a_size; lia).
  rewrite Hasz in HAphi.
  assert (HAphi50 : addressable mem phi 50) by (apply (addressable_prefix mem phi (rnb g 0%nat) 50 HAphi); lia).
  assert (Hphiapp : forall x, phi <= x < phi + rnb g 0%nat -> app_mem x)
    by (intros x Hx; exact (proj1 (Hphiall x Hx))).
  assert (Hphifs : forall x, phi <= x < phi + rnb g 0%nat -> ~ AC.a_in_fs AC.ASYMS mem x)
    by (intros x Hx; exact (proj2 (Hphiall x Hx))).
  assert (Hphi50 : phi + 50 <= APPMEM_END) by (destruct HAphi50 as (_ & _ & H & _); exact H).
  assert (Hphisp : phi + rnb g 0%nat <= bv_unsigned (getr regs 2) - CMC.CM_K) by lia.
  (* the block and its 32 control bytes *)
  pose proof (r14_blk_bytes (g_in g) (Z.of_nat 0%nat) mem phi Hphib) as Hblk.
  pose proof (r14_g_bytes (g_in g) (Z.of_nat 0%nat) mem phi Hphib) as Hgb.
  assert (Hblkl : length (rt_X (g_in g) (Z.of_nat 0%nat)) = 32%nat)
    by (unfold rt_X; apply r14_baX_len; apply r14_mb_len).
  pose proof (r14_blocksum0 (g_in g)) as Hsum.
  assert (Hrs : rsum g 0%nat i = psum (rt_X (g_in g) (Z.of_nat 0%nat)) i)
    by (unfold rsum; rewrite r14_skip18; reflexivity).
  (* the spill base of each spill is A *)
  assert (Hspl0 : forall off v, 0 <= off <= 336 -> spill regs mem off v -> q64 mem (A + off) v).
  { intros off v Hoff (A' & HA' & Hq).
    assert (A' = A) by (apply (r14_spill_A regs mem off v A A' HA' Hq Hr9); lia). subst A'. exact Hq. }
  (* the normalized memory the run is stepped on, and the transports onto it *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  assert (TB0 : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs (normalize rsegs mem) a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
  assert (TS0 : forall l h, 0x5fe000 <= l -> stk rsegs mem l h -> stk rsegs (normalize rsegs mem) l h)
    by (intros l h Hl Hs; exact (r14_stk_rel mem (normalize rsegs mem) l h HR0 Hl Hs)).
  assert (TA0 : forall p n, addressable mem p n -> addressable (normalize rsegs mem) p n)
    by (intros p n Ha; exact (r14_addr_rel mem (normalize rsegs mem) p n HR0 Ha)).
  pose proof (r14_srw_rel mem (normalize rsegs mem) HR0 HSWm) as HSW0.
  pose proof (r14_cells_tr mem (normalize rsegs mem) TB0 HACm) as HAC0.
  (* the window of the call *)
  assert (HHMlo : HIGHMEM_BEG <= bv_unsigned (getr regs 2) - CMC.CM_K) by lia.
  assert (Hsp0K : 0 <= bv_unsigned (getr regs 2) - CMC.CM_K) by lia.
  assert (Hwinle : bv_unsigned (getr regs 2) - FN_STACK <=
                   bv_unsigned (getr regs 2) - CMC.CM_K <= bv_unsigned (getr regs 2)) by lia.
  assert (HSTKw : stk rsegs mem (bv_unsigned (getr regs 2) - CMC.CM_K) (bv_unsigned (getr regs 2))).
  { destruct (stk_split rsegs mem (bv_unsigned (getr regs 2) - FN_STACK)
                (bv_unsigned (getr regs 2) - CMC.CM_K) (bv_unsigned (getr regs 2))
                Hstkw Hwinle) as (_ & Hw). exact Hw. }
  assert (Hlo5 : 0x5fe000 <= bv_unsigned (getr regs 2) - CMC.CM_K) by lia.
  pose proof (TS0 _ _ Hlo5 HSTKw) as HSTKw0.
  assert (HAWwin : addressable mem (bv_unsigned (getr regs 2) - CMC.CM_K) CMC.CM_K).
  { apply r14_addr_of1; [lia | lia | lia |]. intros j Hj.
    apply HWA; [lia|]. destruct Hsep as [Hs|Hs]; lia. }
  pose proof (TA0 _ _ HAWwin) as HAWwin0.
  assert (HROMw : forall a, bv_unsigned (getr regs 2) - CMC.CM_K <= a < bv_unsigned (getr regs 2) ->
                    seg_rom rsegs (wa a) = None)
    by (intros a Ha; apply r14_rom_none; lia).
  (* the image ranges the callee reads *)
  assert (HACAT : addressable mem CMC.CM_T 3256).
  { eapply (r14_ag mem CMC.CM_T 3256 0x9f620 3256 HAG); [r14_in | lia | lia | lia | lia | lia]. }
  assert (HABC : addressable mem reac_ctrl_parse_c.REAC_CTRL_PARSE_BC 6).
  { eapply (r14_ag mem reac_ctrl_parse_c.REAC_CTRL_PARSE_BC 6 0x21200 7 HAG);
      [r14_in | lia | unfold reac_ctrl_parse_c.REAC_CTRL_PARSE_BC; lia | lia
      | unfold reac_ctrl_parse_c.REAC_CTRL_PARSE_BC; lia | lia]. }
  assert (HCATrom : forall a, CMC.CM_T <= a < CMC.CM_T + 3256 ->
                      mrd rsegs (normalize rsegs mem) (wa a) = seg_rom rsegs (wa a)).
  { intros a Ha. rewrite <- (mrd_rel rsegs mem (normalize rsegs mem) _ HR0). rewrite <- r14_mbyte_mrd.
    assert (Hin : in_globals AF.frame_RELRO a).
    { exists 0x9f168, 9344. split; [unfold AF.frame_RELRO; cbn [In]; left; reflexivity|].
      rewrite HCMT in Ha. lia. }
    pose proof (Hgimg a Hin) as E. try rewrite SEGS in E. exact E. }
  (* the runtime cells the callee's bcmp wrapper reads *)
  assert (HBCMP : bytes_at rsegs mem bcmp_wrap_c.REAL_BCMP (le8 (wa bcmp_wrap_c.BCMP)))
    by (apply real_cell_of; [exact (AsanRTInv.RT_real_cells _ _ _ HRT) | vm_compute; reflexivity]).
  assert (HMEMCMP : bytes_at rsegs mem bcmp_wrap_c.REAL_MEMCMP (le8 (wa memcmp_c.MEMCMP)))
    by (apply real_cell_of; [exact (AsanRTInv.RT_real_cells _ _ _ HRT) | vm_compute; reflexivity]).
  destruct (AsanRTInv.RT_cf_cells _ _ _ HRT) as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  pose proof (r14_ba_nth1 _ _ _ 14 (Z_to_bv 8 1) HCF240 eq_refl) as HCFa.
  pose proof (r14_ba_nth1 _ _ _ 15 (Z_to_bv 8 1) HCF240 eq_refl) as HCFb.
  assert (HCF254 : bytes_at rsegs mem (CF + 254) [Z_to_bv 8 1])
    by (eapply r14_ba_at; [exact HCFa | vm_compute; reflexivity]).
  assert (HCF255 : bytes_at rsegs mem (CF + 255) [Z_to_bv 8 1])
    by (eapply r14_ba_at; [exact HCFb | vm_compute; reflexivity]).
  (* the side stack of the call *)
  pose proof HFP as HFP0.
  destruct HFP0 as (DT & TS & C & T & DB & k & HTLSc & HFStp & HFSpl & H88 & H96 & HCLS & HFSlo & HFSapp &
                    HWdj & HDdj).
  assert (HFSw : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { change (AC.as_tp AC.ASYMS) with RT_TP.
    pose proof (KindBGlue.bytes_at_le8_word rsegs mem RT_TP (Z_to_bv 64 FS) HFStp) as Hw.
    rewrite MState.unsigned_lit in Hw; [exact Hw|].
    destruct HFSpl as (HF1 & HF2 & HF3 & HF4 & HF5). unfold stk, FS_SIZE in HF5. lia. }
  assert (HFSrange : 0 < FS /\ FS mod 4096 = 0 /\ AC.GT <= FS /\ FS + AC.FS_SIZE <= APPMEM_END).
  { destruct HFSpl as (HF1 & HF2 & HF3 & HF4 & HF5).
    pose proof (HF4 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as Hap.
    unfold app_mem, ASAN_GT, FS_SIZE, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, AC.GT, AC.FS_SIZE in *. lia. }
  assert (HFSapp' : forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
  { destruct HFSpl as (_ & _ & _ & HF4 & _). intros a Ha. apply HF4. lia. }
  assert (HFSuniq : forall FS', word_mem rsegs mem (AC.as_tp AC.ASYMS) FS' -> 0 <= FS' < 2 ^ 64 -> FS' = FS).
  { intros FS' Hwb HFS'r.
    change (AC.as_tp AC.ASYMS) with RT_TP in Hwb.
    pose proof (KindBGlue.word_mem_le8 rsegs mem RT_TP FS' Hwb ltac:(lia)
                  ltac:(unfold RT_TP; lia) ltac:(unfold RT_TP; lia)) as Hb1.
    pose proof HFSw as HFSw2. change (AC.as_tp AC.ASYMS) with RT_TP in HFSw2.
    pose proof (KindBGlue.word_mem_le8 rsegs mem RT_TP FS HFSw2 ltac:(lia)
                  ltac:(unfold RT_TP; lia) ltac:(unfold RT_TP; lia)) as Hb2.
    pose proof (fl_le8_eq [] mem mem RT_TP (Z_to_bv 64 FS') (Z_to_bv 64 FS) Hb1 Hb2
                  (munch_refl [] mem) (fun _ _ => I)) as Heq.
    apply (f_equal (bv_unsigned (n:=64))) in Heq.
    rewrite !MState.unsigned_lit in Heq by lia. exact Heq. }
  assert (HFS8 : FS mod 8 = 0) by (destruct HFSrange as (_ & Hm & _); Z.div_mod_to_equations; lia).
  assert (HFSstklo : FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct (r14_fs_place (APIf rc) (hb1 phi (rnb g 0%nat) ++ g_H g) mem md FS HAH HFSw ltac:(lia))
      as (_ & He & _). exact He. }
  (* the frame is above the class-0/1/2 areas: on the real arm it is at or above stklo, on the side arm it is a
     class-6 frame, FS + 6328320 <= fr *)
  assert (HFSfr : FS + 3182592 <= fr).
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs Hrec]]]].
    - pose proof (Hreal fr ltac:(lia)) as Hr. lia.
    - pose proof (Hfsb FS HFSw ltac:(lia)) as Hb. lia. }
  (* the remaining contract premises, on the normalized memory *)
  assert (Hsp16 : bv_unsigned (getr regs 2) mod 16 = 0) by (rewrite Haspz; exact Hspm).
  assert (Htp : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS).
  { rewrite Hr4. apply MState.unsigned_lit. unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  assert (HFP' : fp [0%nat; 1%nat; 2%nat] (normalize rsegs mem) (bv_unsigned (getr regs 4)) FS
                   (bv_unsigned (getr regs 2) - CMC.CM_K) (bv_unsigned (getr regs 2))
                   (CMC.reac_box_catalogue_match_W (bv_unsigned (getr regs 2)))
                   (CMC.reac_box_catalogue_match_D phi (rnb g 0%nat))).
  { rewrite Htp. exact (r14_fp_tr mem (normalize rsegs mem) _ _ _ _ _ _ _ TB0 TS0 HFP). }
  assert (HTLS' : CMC.reac_box_catalogue_match_tls (normalize rsegs mem) (bv_unsigned (getr regs 4)) FS
                    (bv_unsigned (getr regs 2) - CMC.CM_K) (bv_unsigned (getr regs 2))).
  { rewrite Htp. intros DT' TS' C' T' DB' k' Hc. apply HTLS.
    apply (r14_tls_tr (normalize rsegs mem) mem _ _ _ _ _ _ _
             (fun a bs Hb => proj2 (bytes_at_rel rsegs mem (normalize rsegs mem) a bs HR0) Hb)).
    exact Hc. }
  assert (Hr2v : getr regs 2 = Z_to_bv 64 (bv_unsigned (getr regs 2))) by (rewrite Haspz; exact Hr2).
  assert (HSpA : bv_unsigned (getr regs 2) <= A) by lia.
  (* the arithmetic and transported premises of the run lemma, named so that it applies by assumption *)
  assert (Hrnb50 : 50 <= rnb g 0%nat) by lia.
  assert (Hrnb64 : 0 <= rnb g 0%nat < 2 ^ 64) by lia.
  assert (HSp64 : bv_unsigned (getr regs 2) < 2 ^ 64) by lia.
  assert (HSpK : CMC.CM_K <= bv_unsigned (getr regs 2)) by lia.
  assert (HpSp : phi + 50 <= bv_unsigned (getr regs 2) - CMC.CM_K) by lia.
  assert (HSPapp : bv_unsigned (getr regs 2) <= APPMEM_END) by lia.
  assert (Hphi50app : app_mem (phi + 50)) by (apply Hphiapp; lia).
  pose proof (TB0 _ _ Hgb) as Hgb0. pose proof (TB0 _ _ Hblk) as Hblk0.
  pose proof (TA0 _ _ HAphi50) as HAphi0. pose proof (TA0 _ _ HACAT) as HACAT0.
  pose proof (TA0 _ _ HABC) as HABC0.
  pose proof (TB0 _ _ HBCMP) as HBCMP0. pose proof (TB0 _ _ HMEMCMP) as HMEMCMP0.
  assert (HGOTCF0 : bytes_at rsegs (normalize rsegs mem) GOT_CF (le8 (wa CF))) by exact (TB0 _ _ HGOTCF).
  pose proof (TB0 _ _ HCF254) as HCF2540. pose proof (TB0 _ _ HCF255) as HCF2550.
  pose proof (r14_rtg_len (g_in g) (Z.of_nat 0%nat)) as Hgl.
  unfold rg in Hr10, Hr11, Hr12, Hr13, Hr14, Hr18, Hr20, Hr27, Hr26.
  (* the run, on the normalized memory *)
  apply (r14_run regs (Z_to_bv 64 0x818a8) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x819a8 /\
       getr R 1 = Z_to_bv 64 0x819a8 /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
       getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
       getr R 10 = Z_to_bv 64 (want CMC.CM_T (rnb g 0%nat) (rt_g (g_in g) (Z.of_nat 0%nat))) /\
       getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\ getr R 27 = Z_to_bv 64 32 /\
       munch ([(bv_unsigned (getr regs 2) - CMC.CM_K, bv_unsigned (getr regs 2))] ++
              fp_w [0%nat; 1%nat; 2%nat] FS ++
              [(shadow_addr (bv_unsigned (getr regs 2) - CMC.CM_K), shadow_addr (bv_unsigned (getr regs 2)))])
             (normalize rsegs mem) m0' /\
       wmono rsegs (normalize rsegs mem) m0' /\
       stk rsegs m0' (bv_unsigned (getr regs 2) - CMC.CM_K) (bv_unsigned (getr regs 2)) /\
       asan_cells m0' /\ shadow_rw m0' /\
       addressable m0' (bv_unsigned (getr regs 2) - CMC.CM_K) CMC.CM_K /\
       fp [0%nat; 1%nat; 2%nat] m0' (bv_unsigned (getr regs 4)) FS
          (bv_unsigned (getr regs 2) - CMC.CM_K) (bv_unsigned (getr regs 2))
          (CMC.reac_box_catalogue_match_W (bv_unsigned (getr regs 2)))
          (CMC.reac_box_catalogue_match_D phi (rnb g 0%nat)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite r14_mkR_of.
    eapply evt_mono.
    + rewrite Hr10, Hr11, Hr12, Hr13, Hr14, Hr18, Hr20, Hr27, Hr26, Hrs, Hr2v.
      rewrite (r14_room phi ltac:(lia)).
      apply (r14_evt CATMH (getr regs 1) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
               (getr regs 8) (getr regs 9) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 19)
               (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
               (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
               fp_regs fp_csr (normalize rsegs mem) phi (bv_unsigned (getr regs 2)) FS (rnb g 0%nat) i
               (rt_X (g_in g) (Z.of_nat 0%nat)) (rt_g (g_in g) (Z.of_nat 0%nat)));
        assumption.
    + intros ms' HP. unfold r14_post in HP.
      destruct HP as (R & m' & Hms & K1 & K2 & K3 & K4 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & K22 & K23 &
                      K24 & K25 & K26 & K27 & MU & WM & MI & ST & ACm & SWm & AW & FP' & TLS').
      exists R, (Z_to_bv 64 0x819a8), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact K1|]. split; [rewrite K2; exact (eq_sym Hr2v)|].
      split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
      split; [exact K10|]. split; [rewrite K18; exact (eq_sym Hr18)|]. split; [exact K19|].
      split; [rewrite K20; exact (eq_sym Hr20)|].
      split; [exact K21|]. split; [exact K22|]. split; [exact K23|]. split; [exact K24|].
      split; [exact K25|]. split; [rewrite K26; exact (eq_sym Hr26)|]. split; [exact K27|].
      split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
      split; [exact ACm|]. split; [exact SWm|]. split; [exact AW|]. exact FP'.
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K1 & K2 & K3 & K4 & K8 & K9 & K10 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 &
       MU0 & WM0 & ST0 & AC0' & SW0' & AW0 & FP0') Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E10 : getr regs'' 10 = Z_to_bv 64 (want CMC.CM_T (rnb g 0%nat) (rt_g (g_in g) (Z.of_nat 0%nat))))
      by (rewrite Hreg; exact K10).
    assert (E18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E20 : getr regs'' 20 = getr regs 20) by (rewrite Hreg; exact K20).
    assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E27 : getr regs'' 27 = Z_to_bv 64 32) by (rewrite Hreg; exact K27).
    (* back from the normalized memory to the real one *)
    assert (TB' : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs mem' a bs)
      by (intros a bs Hb; exact (proj2 (bytes_at_rel rsegs mem' m0' a bs HRel) Hb)).
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HroM.
    pose proof (r14_stk_back mem' m0' _ _ HRel Hlo5 ST0) as ST.
    pose proof (r14_srw_back mem' m0' HRel SW0') as SWm.
    pose proof (r14_addr_back mem' m0' _ _ HRel AW0) as AW.
    pose proof (r14_fp_tr m0' mem' _ _ _ _ _ _ _ TB'
                  (fun l h Hl Hs => r14_stk_back mem' m0' l h HRel Hl Hs) FP0') as FP'.
    (* the side-stack state after the call, and the presence of its bytes *)
    pose proof FP' as FP1.
    destruct FP1 as (DT' & TS' & C' & T' & DB' & k2 & HTLSc' & HFStp' & HFSpl' & H88' & H96' & HCLS' & _).
    assert (HC0 : fp_cls mem' FS 0%nat) by (inversion HCLS' as [|c0 l0 Hc0 Hl0]; exact Hc0).
    assert (HC1 : fp_cls mem' FS 1%nat)
      by (inversion HCLS' as [|c0 l0 Hc0 Hl0]; inversion Hl0 as [|c1 l1 Hc1 Hl1]; exact Hc1).
    assert (HC2 : fp_cls mem' FS 2%nat)
      by (inversion HCLS' as [|c0 l0 Hc0 Hl0]; inversion Hl0 as [|c1 l1 Hc1 Hl1];
          inversion Hl1 as [|c2 l2 Hc2 Hl2]; exact Hc2).
    assert (HFSstk : stk rsegs mem' FS (FS + FS_SIZE)) by (destruct HFSpl' as (_ & _ & _ & _ & H); exact H).
    assert (HFSpres : forall q, FS <= q < FS + AC.FS_SIZE -> exists bb, mbyte rsegs mem' q = Some bb).
    { intros q Hq. destruct HFSstk as (_ & _ & Hs).
      destruct (proj2 (Hs q ltac:(lia))) as (bb & Hb).
      exists bb. rewrite r14_mbyte_mrd. exact Hb. }
    (* the write set and its complement *)
    set (Wall := [(bv_unsigned (getr regs 2) - CMC.CM_K, bv_unsigned (getr regs 2))] ++
                 fp_w [0%nat; 1%nat; 2%nat] FS ++
                 [(shadow_addr (bv_unsigned (getr regs 2) - CMC.CM_K), shadow_addr (bv_unsigned (getr regs 2)))])
      in *.
    assert (Hm8 : (bv_unsigned (getr regs 2) - CMC.CM_K) mod 8 = 0) by (Z.div_mod_to_equations; lia).
    (* the shadow byte of an application byte off the call's window and off the class-0/1/2 areas *)
    assert (HoutSHb : forall b0, app_mem b0 -> 0 <= b0 ->
              (b0 < bv_unsigned (getr regs 2) - CMC.CM_K \/ bv_unsigned (getr regs 2) <= b0) ->
              (b0 < FS \/ FS + 3182592 <= b0) -> outside Wall (shadow_addr b0)).
    { intros b0 Happb Hb0 Hwb Hfb.
      pose proof (shadow_of_app b0 Happb) as Hsb.
      pose proof (r14_in_shadow_bnd _ Hsb) as Hbd.
      unfold Wall. apply r14_out_all.
      - lia.
      - apply r14_fpw_out; [lia | |].
        + intros Hc. exact (app_not_shadow (shadow_addr b0) (HFSapp' (shadow_addr b0) ltac:(lia)) Hsb).
        + destruct Hfb as [Hl|Hh].
          * pose proof (r14_sh_lt b0 FS HFS8 Hl). lia.
          * pose proof (r14_sh_ge b0 (FS + 3182592) Hh). lia.
      - destruct Hwb as [Hl|Hh].
        + pose proof (r14_sh_lt b0 _ Hm8 Hl). lia.
        + pose proof (r14_sh_ge b0 _ Hh). lia. }
    assert (HoutLO : forall x, 0 <= x < AC.GT -> outside Wall x).
    { intros x Hx. unfold Wall. apply r14_out_all; [lia | |].
      - apply r14_fpw_out; [lia | lia |].
        assert (Hs0 : ASAN_K <= shadow_addr FS)
          by (unfold shadow_addr; pose proof (Z.div_pos FS 8 ltac:(lia) ltac:(lia)); lia).
        lia.
      - assert (H0 : ASAN_K <= shadow_addr (bv_unsigned (getr regs 2) - CMC.CM_K)).
        { unfold shadow_addr.
          pose proof (Z.div_pos (bv_unsigned (getr regs 2) - CMC.CM_K) 8 Hsp0K ltac:(lia)). lia. }
        lia. }
    assert (HoutHI : forall x, A <= x -> outside Wall x).
    { intros x Hx. unfold Wall. apply r14_out_all; [lia | |].
      - apply r14_fpw_out; [lia | lia |].
        pose proof (r14_sh_hi (FS + 3182592) ltac:(lia)) as Hs. lia.
      - assert (Hs : shadow_addr (bv_unsigned (getr regs 2)) <= HIGHMEM_BEG) by (apply r14_sh_hi; lia). lia. }
    assert (HoutFR : forall x, fr <= x < fr + 3136 -> outside Wall x).
    { intros x Hx. unfold Wall. apply r14_out_all.
      - destruct Hsep as [Hs|Hs]; lia.
      - apply r14_fpw_out; [lia | lia |]. apply (r14_app_not_sh x _ _ (Happ x Hx)); lia.
      - apply (r14_app_not_sh x _ _ (Happ x Hx)); lia. }
    assert (HoutSH : forall x, Sfr fr <= x < Sfr fr + 392 -> outside Wall x).
    { intros x Hx. pose proof (HshIn x Hx) as Hin. pose proof (r14_in_shadow_bnd x Hin) as Hbd.
      assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
      unfold Wall. apply r14_out_all.
      - lia.
      - apply r14_fpw_out; [lia | |].
        + intros Hc. exact (app_not_shadow x (HFSapp' x ltac:(lia)) Hin).
        + assert (Hge : shadow_addr (FS + 3182592) <= Sfr fr) by (unfold Sfr; apply r14_sh_ge; lia). lia.
      - destruct Hsep as [Hs|Hs].
        + assert (Hle : Sfr fr + 392 <= shadow_addr (bv_unsigned (getr regs 2) - CMC.CM_K)).
          { unfold Sfr. rewrite <- (r14_sh_frame_of fr 392 ltac:(lia) Hfr8 ltac:(lia)).
            apply r14_sh_ge. lia. }
          lia.
        + assert (Hge : shadow_addr (bv_unsigned (getr regs 2)) <= Sfr fr)
            by (unfold Sfr; apply r14_sh_ge; lia).
          lia. }
    assert (HoutAG : forall a, in_globals AF.frame_AG a -> outside Wall (shadow_addr a)).
    { intros a Hin. destruct (r14_ag_lo a Hin) as (Ha0 & Hagt).
      apply HoutSHb; [unfold app_mem; left; lia | lia | left; lia | left; lia]. }
    (* the record block's bytes and their shadow bytes *)
    assert (HoutPHI : forall x, phi <= x < phi + rnb g 0%nat -> outside Wall x /\ outside Wall (shadow_addr x)).
    { intros x Hx.
      assert (Hxa : app_mem x) by exact (Hphiapp x Hx).
      assert (Hxfs : x < FS \/ FS + 3182592 <= x).
      { destruct (Z_lt_le_dec x FS) as [Hl|Hl]; [left; exact Hl|].
        destruct (Z_lt_le_dec x (FS + 3182592)) as [Hh|Hh]; [|right; exact Hh].
        exfalso. apply (Hphifs x Hx). apply (a_fs_in AC.ASYMS mem FS x HFSw); lia. }
      split.
      - unfold Wall. apply r14_out_all.
        + lia.
        + apply r14_fpw_out; [lia | lia |]. apply (r14_app_not_sh x _ _ Hxa); lia.
        + apply (r14_app_not_sh x _ _ Hxa); lia.
      - apply HoutSHb; [exact Hxa | lia | left; lia | exact Hxfs]. }
    (* the slot window below the call's window holds no frame byte (seg_R6's HfrLo) *)
    assert (HfrLo : forall x, g_S g - AF.SLOT_STACK <= x < bv_unsigned (getr regs 2) - CMC.CM_K ->
              ~ (fr <= x < fr + 3136)).
    { intros x Hx Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs Hrec]]]].
      - lia.
      - destruct (Hfs x Hf) as (FSb & HFSbr & Hwb & Hlob & Hhib).
        pose proof (HFSuniq FSb Hwb HFSbr) as EFS. subst FSb. lia. }
    assert (HoutWIN : forall x, g_S g - AF.SLOT_STACK <= x < g_S g ->
              outside Wall x \/ exists bb, mrd rsegs mem' (wa x) = Some bb).
    { intros x Hx.
      destruct (Z_le_gt_dec (bv_unsigned (getr regs 2) - CMC.CM_K) x) as [HL|HL];
        [destruct (Z_lt_ge_dec x (bv_unsigned (getr regs 2))) as [HU|HU]|].
      - right. destruct ST as (_ & _ & Hs).
        exact (proj2 (Hs x ltac:(lia))).
      - destruct (Z_le_gt_dec fr x) as [HF|HF]; [destruct (Z_lt_ge_dec x (fr + 3136)) as [HF2|HF2]|].
        + left. apply HoutFR; lia.
        + left. unfold Wall. apply r14_out_all; [lia | |].
          * apply r14_fpw_out; [lia | lia |].
            pose proof (r14_sh_hi (FS + 3182592) ltac:(lia)) as Hs. lia.
          * apply (r14_app_not_sh x _ _); [unfold app_mem; right; lia | lia | lia].
        + left. unfold Wall. apply r14_out_all; [lia | |].
          * apply r14_fpw_out; [lia | lia |].
            pose proof (r14_sh_hi (FS + 3182592) ltac:(lia)) as Hs. lia.
          * apply (r14_app_not_sh x _ _); [unfold app_mem; right; lia | lia | lia].
      - left. unfold Wall. apply r14_out_all; [lia | |].
        + apply r14_fpw_out; [lia | lia |].
          pose proof (r14_sh_hi (FS + 3182592) ltac:(lia)) as Hs. lia.
        + apply (r14_app_not_sh x _ _); [unfold app_mem; right; lia | lia | lia]. }
    (* the runtime cells and the heap invariant after the call *)
    assert (HFPWgt : forall r, In r (fp_w [0%nat; 1%nat; 2%nat] FS) -> AC.GT <= fst r)
      by (intros r Hr; apply (r14_fpw_gt FS r); [lia | exact Hr]).
    assert (HRTD : rt_disjoint Wall).
    { apply r14_rt_disjoint. unfold Wall. apply Forall_app. split.
      - repeat constructor; cbn [fst]; lia.
      - apply Forall_app. split.
        + apply Forall_forall. exact HFPWgt.
        + repeat constructor; cbn [fst]. unfold shadow_addr.
          pose proof (Z.div_pos (bv_unsigned (getr regs 2) - CMC.CM_K) 8 Hsp0K ltac:(lia)). lia. }
    assert (Hkeepfs : forall q, FS <= q < FS + 36864 -> ~ (FS <= q < FS + 24) ->
              ~ (FS + 4096 <= q < FS + 32768) -> outside Wall q).
    { intros q Hq H1 H2.
      assert (Hqapp : app_mem q) by (apply HFSapp'; lia).
      assert (Hsh3 : ~ (shadow_addr (bv_unsigned (getr regs 2) - CMC.CM_K) <= q <
                        shadow_addr (bv_unsigned (getr regs 2))))
        by (apply (r14_app_not_sh q); [exact Hqapp | lia | lia]).
      assert (Hshfs : ~ (shadow_addr FS <= q < shadow_addr (FS + 3182592)))
        by (apply (r14_app_not_sh q); [exact Hqapp | lia | lia]).
      unfold Wall. apply r14_out_all; [lia | | exact Hsh3].
      apply r14_fpw_meta; [lia | lia | exact H1 | exact H2 | exact Hshfs]. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok (hb1 phi (rnb g 0%nat) ++ g_H g)
                  (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (FS <= q < FS + AC.FS_SIZE) ->
              ~ (exists bb, FS <= bb < FS + AC.FS_SIZE /\ q = shadow_addr bb) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
      unfold Wall. apply r14_out_app.
      - cbn [outside]. split; [|exact I].
        destruct (Z_le_gt_dec (bv_unsigned (getr regs 2) - CMC.CM_K) q) as [HL|HL];
          [destruct (Z_lt_ge_dec q (bv_unsigned (getr regs 2))) as [HU|HU]; [|lia] | lia].
        exfalso. apply Hns. right; left. lia.
      - apply r14_out_app.
        + apply r14_fpw_out; [lia| |].
          * intros Hc. apply Hnf. unfold AC.FS_SIZE. lia.
          * intros Hc. apply Hnsh.
            destruct (r14_sh_inv q FS (FS + 3182592) HFS8 ltac:(lia) Hc) as (Hsv1 & Hsv2).
            exists (FS + 8 * (q - shadow_addr FS)).
            split; [unfold AC.FS_SIZE; lia | symmetry; exact Hsv2].
        + cbn [outside]. split; [|exact I].
          destruct (Z_le_gt_dec (shadow_addr (bv_unsigned (getr regs 2) - CMC.CM_K)) q)
            as [HL|HL]; [destruct (Z_lt_ge_dec q (shadow_addr (bv_unsigned (getr regs 2)))) as [HU|HU];
                         [|lia] | lia].
          exfalso. apply Hns.
          assert (Hqi : shadow_addr (bv_unsigned (getr regs 2) - CMC.CM_K) <= q <
                        shadow_addr (bv_unsigned (getr regs 2))) by lia.
          destruct (r14_sh_inv q _ _ Hm8 Hsp0K Hqi) as (Hsv1 & Hsv2).
          right; right; right.
          exists (bv_unsigned (getr regs 2) - CMC.CM_K +
                  8 * (q - shadow_addr (bv_unsigned (getr regs 2) - CMC.CM_K))).
          split; [symmetry; exact Hsv2|]. right; left. lia. }
    destruct (r14_ah g fr (hb1 phi (rnb g 0%nat)) regs mem mem' md Wall FS HFRA HFSw ltac:(lia) ltac:(lia)
                MU WM HFSpres Hkeepfs HC0 HC1 HC2 Hagree) as (HAH' & HOWN' & HSTKeq & HSTKhi).
    (* the registered globals and the slot window outside the frame stay addressable *)
    assert (HAGm : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Hin. apply (r14_addr_keep Wall mem mem' a 1 (HAG a Hin) MU).
      intros j Hj. replace (a + j) with a by lia. exact (HoutAG a Hin). }
    assert (HWAm : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) ->
              addressable mem' a 1).
    { intros a Ha1 Ha2.
      destruct (Z_le_gt_dec (bv_unsigned (getr regs 2) - CMC.CM_K) a) as [HL|HL];
        [destruct (Z_lt_ge_dec a (bv_unsigned (getr regs 2))) as [HU|HU]|].
      - apply (r14_addr_sub mem' (bv_unsigned (getr regs 2) - CMC.CM_K) CMC.CM_K); [exact AW | lia | lia | lia].
      - apply (r14_addr_keep Wall mem mem' a 1 (HWA a Ha1 Ha2) MU).
        intros j Hj. replace (a + j) with a by lia.
        apply HoutSHb; [unfold app_mem; right; lia | lia | right; lia | right; lia].
      - apply (r14_addr_keep Wall mem mem' a 1 (HWA a Ha1 Ha2) MU).
        intros j Hj. replace (a + j) with a by lia.
        apply HoutSHb; [unfold app_mem; right; lia | lia | left; lia | right; lia]. }
    (* ENT across the call: no written byte is one ENT speaks of (the entry blocks' shadow bytes included: every
       entry block is application memory below stklo and off the side stack) *)
    assert (HENT1 : ENT APIf g (hb1 phi (rnb g 0%nat)) mem' md).
    { eapply ent_munch with (W := Wall) (mem := mem);
        [exact HENT | exact HAH | exact MU | | exact HSTKeq | exact HSTKhi |].
      - intros x Hk. destruct Hk as [Hkb | [Himg | [Habv | [(b0 & Hor & ->) | Hks]]]].
        + destruct Hkb as (q & kk & j & Hin & Hni & Hj & ->).
          destruct (r14_blocks (APIf rc) (hb1 phi (rnb g 0%nat) ++ g_H g) mem md q kk HAH
                      (in_or_app _ _ _ (or_intror Hin))) as (Hq4 & Hend & Hall).
          destruct (Hall (q + j) ltac:(lia)) as (Happq & Hnfs).
          unfold Wall. apply r14_out_all.
          * lia.
          * apply r14_fpw_out; [lia | |].
            -- intros Hc. apply Hnfs. apply (a_fs_in AC.ASYMS mem FS (q + j) HFSw); lia.
            -- apply (r14_app_not_sh (q + j) _ _ Happq); lia.
          * apply (r14_app_not_sh (q + j) _ _ Happq); lia.
        + apply HoutLO. exact (img_below_GT x Himg).
        + apply HoutHI. lia.
        + assert (Hb0 : (0 <= b0 < AC.GT) \/ (g_S g <= b0 < APPMEM_END)).
          { destruct Hor as [Hi|Hr]; [left; exact (img_below_GT b0 Hi) | right; exact Hr]. }
          apply HoutSHb.
          * unfold app_mem. destruct Hb0; lia.
          * destruct Hb0; lia.
          * destruct Hb0 as [Hl|Hh]; [left; lia | right; lia].
          * destruct Hb0 as [Hl|Hh]; [left; lia | right; lia].
        + destruct Hks as (q & kk & j & Hin & Hni & Hj & ->).
          destruct (r14_blocks (APIf rc) (hb1 phi (rnb g 0%nat) ++ g_H g) mem md q kk HAH
                      (in_or_app _ _ _ (or_intror Hin))) as (Hq4 & Hend & Hall).
          destruct (Hall (q + j) ltac:(lia)) as (Happq & Hnfs).
          assert (Hxfs : q + j < FS \/ FS + 3182592 <= q + j).
          { destruct (Z_lt_le_dec (q + j) FS) as [Hl|Hl]; [left; exact Hl|].
            destruct (Z_lt_le_dec (q + j) (FS + 3182592)) as [Hh|Hh]; [|right; exact Hh].
            exfalso. apply Hnfs. apply (a_fs_in AC.ASYMS mem FS (q + j) HFSw); lia. }
          assert (Hq0 : 0 <= q + j) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
          apply HoutSHb; [exact Happq | exact Hq0 | left; lia | exact Hxfs].
      - intros a _ Ho. exact (proj2 (HOWN' a) Ho). }
    assert (HENT'' : ENT APIf g (hb1 phi (rnb g 0%nat)) mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
    (* the side-arm frame record after the call *)
    assert (HFSREC' : FSREC fr mem -> FSREC fr mem').
    { intros Hrec. apply (r14_fsrec mem mem' Wall fr Hrec MU HoutLO).
      intros FS' j x Hw' HFS'r Hj Hfrj Hx.
      pose proof (HFSuniq FS' Hw' HFS'r) as EFS. subst FS'.
      destruct Hx as [Hx|Hx].
      - apply Hkeepfs; lia.
      - assert (Hxa : app_mem x) by (apply HFSapp'; unfold AC.FS_SIZE; lia).
        unfold Wall. apply r14_out_all.
        + lia.
        + apply r14_fpw_out; [lia | lia |]. apply (r14_app_not_sh x _ _ Hxa); lia.
        + apply (r14_app_not_sh x _ _ Hxa); lia. }
    (* the input block (FRA's input facts) is a live entry block: below stklo and outside FS, so neither it nor
       its shadow bytes are written *)
    assert (HoutIN : forall x, g_p g <= x < g_p g + g_n g -> outside Wall x /\ outside Wall (shadow_addr x)).
    { intros x Hx.
      destruct (Hinblk ltac:(lia)) as (HinI & _).
      destruct (r14_blocks (APIf rc) (hb1 phi (rnb g 0%nat) ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror HinI))) as (HpI4 & HendI & HallI).
      destruct (HallI x Hx) as (Hxa & Hxnfs).
      assert (Hxfs : x < FS \/ FS + 3182592 <= x).
      { destruct (Z_lt_le_dec x FS) as [Hl|Hl]; [left; exact Hl|].
        destruct (Z_lt_le_dec x (FS + 3182592)) as [Hh|Hh]; [|right; exact Hh].
        exfalso. apply Hxnfs. apply (a_fs_in AC.ASYMS mem FS x HFSw); lia. }
      split.
      - unfold Wall. apply r14_out_all.
        + lia.
        + apply r14_fpw_out; [lia | lia |]. apply (r14_app_not_sh x _ _ Hxa); lia.
        + apply (r14_app_not_sh x _ _ Hxa); lia.
      - apply HoutSHb; [exact Hxa | lia | left; lia | exact Hxfs]. }
    assert (HFRAm : FRA B APIf ra g fr (hb1 phi (rnb g 0%nat)) regs'' mem' md).
    { apply (r14_fra_run g fr (hb1 phi (rnb g 0%nat)) regs regs'' mem mem' md Wall HFRA MU WM HroM HRTD SWm
               HAH' HSTKeq HoutLO);
        try assumption.
      - intros x Hx. apply HoutFR; lia.
      - intros x Hx. apply HoutHI. lia. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g 0%nat)) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g 0%nat)) regs'' regs'' mem' md md' HFRAm); try reflexivity.
      exact Hmat. }
    (* the spills of the exit cut lie at or above A, outside the write set *)
    assert (Hspl : forall off v, 0 <= off -> q64 mem (A + off) v -> spill regs'' mem' off v).
    { intros off v Hoff Hq. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
      rewrite length_le8. intros x Hx. apply HoutHI. lia. }
    assert (Hspl2 : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs'' mem' off v)
      by (intros off v Hoff Hs; apply Hspl; [lia | exact (Hspl0 off v Hoff Hs)]).
    (* out[] stays addressable: its shadow bytes are off the call's writes *)
    assert (HOUTAm : OUTA fr mem').
    { unfold OUTA. apply (r14_addr_keep Wall mem mem' (fr + 544) 1492 BOUT MU).
      intros j Hj. apply HoutSHb; [apply Happ; lia | lia | destruct Hsep as [Hs|Hs]; [left | right]; lia
        | right; lia]. }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists phi, regs'', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|].
    split; [exact HENT''|].
    split; [exact Hgn|].
    split; [lia|].
    split.
    { split; [exact Hphi0|]. rewrite Hasz.
      apply (r14_addr_keep Wall mem mem' phi (rnb g 0%nat) HAphi MU).
      intros j Hj. exact (proj2 (HoutPHI (phi + j) ltac:(lia))). }
    split; [unfold rg; rewrite E22; exact Hr22|].
    split.
    { unfold OURb. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. apply HoutFR; lia. }
    split.
    { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR.
      split; [exact Hc0|].
      split; [unfold rg; rewrite E23; exact Hc23 | unfold rg; rewrite E25; exact Hc25]. }
    split; [exact (Hspl2 120 _ ltac:(lia) Hsp120)|].
    split.
    { unfold RBE.
      do 21 (split; [apply Hspl2; [lia | assumption]|]).
      split; [exact HOUTAm|].
      split.
      { apply (r14_addr_keep Wall mem mem' (fr + 2176) 38 BID38 MU).
        intros j Hj. apply HoutSHb; [apply Happ; lia | lia | destruct Hsep as [Hs|Hs]; [left | right]; lia
          | right; lia]. }
      split.
      { intros Hnm. destruct (BNAME Hnm) as (Hok & Hbs & Had & Hpos & Hhi).
        split; [exact Hok|]. split.
        - eapply fl_bytes; [exact Hbs | exact MU |]. intros x Hx. apply HoutLO. lia.
        - split; [|split; [exact Hpos | exact Hhi]].
          apply (r14_addr_keep Wall mem mem' _ _ Had MU). intros j Hj.
          apply HoutSHb; [unfold app_mem; left; lia | lia | left; lia | left; lia]. }
      split.
      { apply (r14_addr_keep Wall mem mem' (fr + 2624) 6 BOUR MU).
        intros j Hj. apply HoutSHb; [apply Happ; lia | lia | destruct Hsep as [Hs|Hs]; [left | right]; lia
          | right; lia]. }
      split.
      { eapply fl_bytes; [exact BTBL | exact MU |]. change (length BAP.ba_tbl) with 168%nat.
        intros x Hx. apply HoutLO. unfold BAC.BA_FR in Hx. lia. }
      split.
      { eapply fl_bytes; [exact BBOX | exact MU |]. change (length box6) with 6%nat.
        intros x Hx. apply HoutLO. unfold BOXA in Hx. lia. }
      split.
      { eapply fl_bytes; [exact BMROW | exact MU |]. rewrite r14_mb_len.
        pose proof (r14_mrow_rng (g_in g)) as (Hm1 & _).
        intros x Hx. apply HoutLO. unfold CAT in Hm1. lia. }
      split; [unfold PRA in BPRA |- *; destruct BPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 &
                                                         P296 & P304 & P168b);
              do 10 (split; [apply Hspl2; [lia | assumption]|]); apply Hspl2; [lia | assumption]|].
      split; [exact (Hspl2 152 _ ltac:(lia) B152)|].
      split; [exact (Hspl2 112 _ ltac:(lia) B112)|].
      split.
      { apply (r14_addr_keep Wall mem mem' (fr + 2256) 72 BA2256 MU).
        intros j Hj. apply HoutSHb; [apply Happ; lia | lia | destruct Hsep as [Hs|Hs]; [left | right]; lia
          | right; lia]. }
      exact (Hspl2 160 _ ltac:(lia) B160). }
    split; [unfold rg; rewrite E21; exact Hs5r|].
    split; [reflexivity|].
    split.
    { unfold RFb, RB.
      split.
      { split; [lia|].
        split.
        { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR.
          split; [exact Hc0|].
          split; [unfold rg; rewrite E23; exact Hc23 | unfold rg; rewrite E25; exact Hc25]. }
        split.
        { unfold OURb. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
          intros x Hx. apply HoutFR; lia. }
        split; [unfold rg; rewrite E22; exact Hr22|].
        split.
        { unfold IDBr. eapply fl_bytes; [exact HIDB | exact MU |]. rewrite r14_rid_len.
          intros x Hx. apply HoutFR; lia. }
        { unfold FGBr. eapply fl_bytes; [exact HFGB | exact MU |]. rewrite r14_rfg_len.
          intros x Hx. apply HoutFR; lia. } }
      split; [exact Hrnb0|].
      split; [unfold rg; rewrite E20; exact Hr20|].
      eapply fl_bytes; [exact Hphib | exact MU |].
      rewrite (r14_rtF_len (g_in g) (Z.of_nat 0%nat) Hrnblo).
      intros x Hx. exact (proj1 (HoutPHI x Hx)). }
    split.
    { unfold a0v, rg. rewrite E10. change CMC.CM_T with CAT. rewrite HWANT. reflexivity. }
    split; [exact (Hspl2 24 _ ltac:(lia) Hsl24)|].
    split; [exact (Hspl2 16 _ ltac:(lia) Hsl16)|].
    split; [exact (Hspl2 96 _ ltac:(lia) Hsl96)|].
    split.
    { apply (r14_addr_keep Wall mem mem' (fr + 2528) 12 HA2528 MU).
      intros j Hj. apply HoutSHb; [apply Happ; lia | lia | destruct Hsep as [Hs|Hs]; [left | right]; lia
        | right; lia]. }
    unfold rg. exact E27.
Qed.

End R14.

