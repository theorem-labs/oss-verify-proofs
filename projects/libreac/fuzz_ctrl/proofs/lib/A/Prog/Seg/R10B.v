(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names and addresses changed; 1437 of its 1585 lines of code are new or changed and 1354 lines of the source are left out. *)
(* Segment R10 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A), the two fragment arms (b = 6 and b = 5) of the
   round-trip kind dispatch: entry 0x81680 (Inv_A81680_at, after reac_ctrl_parse), exits 0x81708 (Inv_A81708_at,
   b = 6) and 0x817c8 (Inv_A817c8_at, b = 5).  rule 24: no function proved (a slot segment; the callee
   reac_ctrl_identity_fragment is a Section hypothesis on its contract, lib/A/Prog/reac_ctrl_identity_fragment_c.v).

   Both arms run 0x81680 `li a3,2`, the three metadata stores 0x81684 `sb a3,306(s3)`, 0x81688 `sb zero,308(s3)`,
   0x8168c `sb zero,312(s3)` (s3 = S(fr): the 2 bytes at fr + 2448 and the 8 bytes at fr + 2464 / fr + 2496 become
   addressable), 0x81690 `li a2,4` and 0x81694 `blt s11,s7` (s11 = 4 < b, taken).
     b = 6: 0x816d0 `li a1,5`, 0x816d4 `beq s7,a1` not taken, 0x816d8 `li a1,6`, 0x816dc `bne s7,a1` not taken,
            0x816e0 `li a1,11`, 0x816e4 `beq a0,a1` taken (a0 = rt_k 6 = 11, B3Rtm.a_rtm_k11, so the abort edge
            0x816e8 is not reached), 0x816ec .. 0x81700 the six arguments, FRAG@0x81704 -> 0x81708.
     b = 5: 0x816d4 `beq s7,a1` taken, 0x817a0 `li a1,11`, 0x817a4 `beq a0,a1` taken (abort edge 0x817a8 not
            reached), 0x817ac .. 0x817c0 the same six arguments, FRAG@0x817c4 -> 0x817c8.
   The call is reac_ctrl_identity_fragment(f = [A + 48] = fr + 2256, Phi = s8, n_b = s2, pa = [A + 88] = fr + 2448,
   pp = [A + 80] = fr + 2464, pn = [A + 72] = fr + 2496).

   Write sets: W1 = [S(fr) + 306, S(fr) + 313) (three frame metadata bytes) and W2 = r10b_W fr sp (the fragment
   record [fr + 2256, fr + 2328), the three reply cells [fr + 2448, fr + 2450), [fr + 2464, fr + 2472),
   [fr + 2496, fr + 2504) and the callee window [sp - 4656, sp)).  Every fact the arms carry (the spills [A + off],
   PRO's spills, our[] fr + 2624 and the harness input block at g_p, the frame cells at fr + 2688 / 2768 / 2960 /
   2976, the identity record fr + 2176, out[]'s addressability fr + 544, the record bytes at Phi, the 392 frame
   metadata bytes) is shown apart from W1 (it is application memory, or the metadata of bytes apart from
   [fr + 2448, fr + 2504)) and from W2.

   r10b_evt is the Lib-level run of both arms with the contract (push 5b: FRA carries ro_agree, not mem_inv, so the
   call runs on MemNorm.normalize, whose mem_inv the contract asks for); r10b_run is the shared segment part (FRA,
   ENT and the carried facts at the exit pc); r10b_b6 / r10b_b5 are the two arm lemmas. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv AsanRTFacts PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcEmit RcEmitLib RcSynth RcSynthLib RcLay RcFinLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 B3Rtm.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module ACx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module FGC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_fragment_c.
Module BAS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.

(* ---- byte, cell and stack helpers ---- *)

Lemma r10b_le1_lit : forall z, 0 <= z < 2 ^ 64 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite MState.unsigned_lit by lia. reflexivity. Qed.

(* A whole byte run read in one access. *)
Lemma r10b_rdn : forall m a bs (n : nat), bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H Hn.
  pose proof (bytes_at_ov_read rsegs m a bs 0 n H ltac:(lia)) as HR.
  replace (a + Z.of_nat 0) with a in HR by lia.
  assert (E : firstn n (skipn 0 bs) = bs).
  { change (skipn 0 bs) with bs. apply firstn_all2. lia. }
  rewrite E in HR. exact HR.
Qed.

(* A one-byte run is the byte at its address. *)
Lemma r10b_b1_rd : forall m a (bb : byte), bytes_at rsegs m a [bb] -> mrd rsegs m (wa a) = Some bb.
Proof.
  intros m a bb (_ & _ & H). pose proof (H 0%nat ltac:(cbn [length]; lia)) as H0.
  replace (a + Z.of_nat 0) with a in H0 by lia. cbn [nth_error] in H0. exact H0.
Qed.

(* A byte of a byte run is readable. *)
Lemma r10b_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

(* A slice of a byte run. *)
Lemma r10b_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(* One byte of a byte run, by its index. *)
Lemma r10b_byte : forall m a bs k x, bytes_at rsegs m a bs -> nth_error bs k = Some x ->
  bytes_at rsegs m (a + Z.of_nat k) [x].
Proof.
  intros m a bs k x (Ha & Hl & H) E.
  assert (Hk : (k < length bs)%nat) by (apply nth_error_Some; congruence).
  split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite (H k Hk). rewrite E. reflexivity.
Qed.

(* A present, writable byte run gives store_ok for each of its bytes. *)
Lemma r10b_stk_store_ok : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 1 <= hi ->
  store_ok rsegs m (wa a) 1%nat = true.
Proof.
  intros m lo hi a (H1 & H2 & H) Hlo Hhi.
  assert (WR : wr_at rsegs m a 1).
  { split; [lia|]. split; [lia|]. intros i Hi. assert (Ei : i = 0) by lia. subst i.
    rewrite Z.add_0_r. exact (proj1 (H a ltac:(lia))). }
  pose proof (wr_at_store_ok rsegs m a 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* n present bytes form a byte run. *)
Lemma r10b_bytes_of_present : forall (n : nat) (m : word -> option byte) a,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, (k < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat k)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros m a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b & Hb). replace (a + Z.of_nat 0) with a in Hb by lia.
    destruct (IH m (a + 1) ltac:(lia) ltac:(lia)) as (bs & HBs & HL).
    { intros k Hk. replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (S k)) by lia. apply H. lia. }
    exists (b :: bs). split; [|cbn [length]; lia].
    change (b :: bs) with ([b] ++ bs).
    apply (proj2 (bytes_at_app rsegs m a [b] bs)). split.
    + split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
      intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
      replace (a + Z.of_nat 0) with a by lia. cbn [nth_error]. exact Hb.
    + cbn [length]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact HBs.
Qed.

Lemma r10b_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

(* ADDR-KEEP for a run whose write set misses the metadata bytes of the range. *)
Lemma r10b_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

(* One CB cell's rw_cells across a run whose write set W misses the cell's bytes. *)
Lemma r10b_rwcb_keep : forall W (m m' : word -> option byte) a n bs,
  munch W m m' -> wmono rsegs m m' ->
  (forall x, a <= x < a + Z.of_nat n -> outside W x) ->
  rw_cells rsegs m a [CB n bs] -> rw_cells rsegs m' a [CB n bs].
Proof.
  intros W m m' a n bs MU WM HO ((Hwf & Hb) & Hw).
  assert (Hlen : length bs = n) by (destruct Hwf as (Hl & _); exact Hl).
  split; [split; [exact Hwf|]|].
  - apply (fl_bytes W m m' a _ Hb MU). intros x Hx.
    cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hlen in Hx. exact (HO x Hx).
  - destruct Hw as (Hw0 & Hw1 & Hw). split; [exact Hw0|]. split; [exact Hw1|].
    intros i Hi. exact (WM _ (Hw i Hi)).
Qed.

Lemma r10b_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r10b_shadow_rw : forall W m m', shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) -> shadow_rw m'.
Proof.
  intros W m m' HS MU WM H a Ha. destruct (HS a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* A sub-range of a present, writable run is writable. *)
Lemma r10b_wr_sub : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi ->
  wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Ha Hn Hb. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma r10b_nth_repeat : forall (x : byte) n k, (k < n)%nat -> nth_error (repeat x n) k = Some x.
Proof. intros x n. induction n as [|n IH]; intros k Hk; [lia|]. destruct k; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma r10b_sh8 : forall fr k, shadow_addr (fr + 8 * k) = shadow_addr fr + k.
Proof.
  intros fr k. unfold shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* The shadow of 8 z bytes at p (p mod 8 = 0) is z zero bytes. *)
Lemma r10b_addr_z : forall m p (z : nat) n, n = 8 * Z.of_nat z -> 0 <= p -> p mod 8 = 0 -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) (repeat (Z_to_bv 8 0) z) -> addressable m p n.
Proof.
  intros m p z n -> Hp Hp8 Hpe Happ (_ & _ & Hb).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|].
  exists (Z_to_bv 8 0). split; [|left; reflexivity].
  assert (Hsh : shadow_addr (p + i) = shadow_addr p + i / 8)
    by (unfold shadow_addr; Z.div_mod_to_equations; lia).
  rewrite Hsh.
  assert (Hq : 0 <= i / 8 < Z.of_nat z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hk : (Z.to_nat (i / 8) < z)%nat) by lia.
  pose proof (Hb (Z.to_nat (i / 8))) as E. rewrite repeat_length in E. specialize (E Hk).
  rewrite Z2Nat.id in E by lia. rewrite E. apply r10b_nth_repeat. exact Hk.
Qed.

(* The shadow of r < 8 bytes at p (p mod 8 = 0) is the byte r. *)
Lemma r10b_addr_r : forall m p r (b : byte), 0 <= p -> p mod 8 = 0 -> 0 < r < 8 -> bv_signed b = r ->
  p + r <= APPMEM_END -> (forall i, 0 <= i < r -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) [b] -> addressable m p r.
Proof.
  intros m p r b Hp Hp8 Hr Hb Hpe Happ (_ & _ & H).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|]. exists b. split.
  - assert (Hsh : shadow_addr (p + i) = shadow_addr p) by (unfold shadow_addr; Z.div_mod_to_equations; lia).
    rewrite Hsh. pose proof (H 0%nat ltac:(cbn; lia)) as E. cbn [Z.of_nat nth_error] in E.
    rewrite Z.add_0_r in E. exact E.
  - right. rewrite Hb. assert (Hm : (p + i) mod 8 = i) by (Z.div_mod_to_equations; lia). lia.
Qed.

(* A shadow byte is never application memory. *)
Lemma r10b_sh_app_dj : forall x a, in_shadow x -> app_mem a -> x + 1 <= a \/ a + 1 <= x.
Proof.
  intros x a Hx Ha.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hx.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha.
  destruct Hx as [Hx|Hx]; destruct Ha as [Ha|Ha]; lia.
Qed.

(* A frame metadata byte is in the shadow map. *)
Lemma r10b_fsh : forall fr k, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> 0 <= k < FRAME_SHADOW ->
  in_shadow (Sfr fr + k).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros fr k Happ Hk. replace (Sfr fr + k) with (shadow_addr (fr + 8 * k)).
  - apply shadow_of_app. apply Happ. lia.
  - rewrite r10b_sh8. unfold Sfr. reflexivity.
Qed.

(* An application byte is outside any window of frame metadata bytes. *)
Lemma r10b_appbyte_out : forall fr lo hi a,
  (forall x, fr <= x < fr + FRAME_BYTES -> app_mem x) -> 0 <= lo -> hi <= FRAME_SHADOW -> app_mem a ->
  outside [(Sfr fr + lo, Sfr fr + hi)] a.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros fr lo hi a Hfapp Hlo Hhi Happ. cbn [outside]. split; [|exact I].
  intros [H1 H2]. apply (AsanRTFacts.app_not_shadow a Happ).
  replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10b_fsh; [exact Hfapp | lia].
Qed.

(* The metadata of an object [p, p + n) apart from the window's frame bytes [fr + 8 lo, fr + 8 hi) is outside
   the window (whole 8-byte granules; fr mod 8 = 0). *)
Lemma r10b_shobj_out : forall fr lo hi p n i,
  fr mod 8 = 0 -> 0 <= fr -> 0 <= p -> (p + n <= fr + 8 * lo \/ fr + 8 * hi <= p) -> 0 <= i < n ->
  outside [(Sfr fr + lo, Sfr fr + hi)] (shadow_addr (p + i)).
Proof.
  intros fr lo hi p n i Hfr8 Hfr0 Hp0 Hdj Hi. cbn [outside]. split; [|exact I].
  unfold Sfr, shadow_addr. destruct Hdj as [Hd|Hd]; Z.div_mod_to_equations; lia.
Qed.

(* ---- the low image and ro_agree ---- *)

Lemma r10b_hull : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 6283264.
Proof.
  assert (H : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 6283264) rsegs = true)
    by (vm_compute; reflexivity).
  intros s Hin. apply Z.leb_le. rewrite forallb_forall in H. exact (H s Hin).
Qed.

Lemma r10b_ro_lt : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 6283264.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  pose proof (YK1j.find_segment_in rsegs (bv_unsigned a) 1 s E) as Hin.
  pose proof (YK1j.find_segment_range rsegs (bv_unsigned a) 1 s E) as (_ & Hhi).
  pose proof (r10b_hull s Hin) as Hb. lia.
Qed.

Lemma r10b_ro_keep : forall (mem mem' : word -> option byte) (W : list ivl),
  ro_agree rsegs mem -> munch W mem mem' ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  ro_agree rsegs mem'.
Proof.
  intros mem mem' W HRO MU Hout a Hro. unfold mrd. rewrite (MU a); [exact (HRO a Hro)|].
  apply Hout. pose proof (r10b_ro_lt a Hro). pose proof (bv_unsigned_in_range 64 a). lia.
Qed.

(* A byte run of the low image across a run that writes nothing below GT. *)
Lemma r10b_keep_low : forall W m m' a bs, munch W m m' -> bytes_at rsegs m a bs ->
  (forall x, 0 <= x < 6283264 -> outside W x) -> a + Z.of_nat (length bs) <= 6283264 ->
  bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs MU HB Hout Hle.
  apply (fl_bytes W m m' a bs HB MU). intros x Hx. apply Hout.
  pose proof (proj1 HB) as Ha0. lia.
Qed.

(* Every registered global lies in the image, below GT. *)
Definition r10b_AGb : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 6283264)) AFx.frame_AG.

Lemma r10b_AGb_true : r10b_AGb = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r10b_AG_lt : forall a lo len, In (lo, len) AFx.frame_AG -> lo <= a < lo + len -> 0 <= a < 6283264.
Proof.
  intros a lo len Hin Hr.
  pose proof r10b_AGb_true as HB. unfold r10b_AGb in HB. rewrite forallb_forall in HB.
  pose proof (HB (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_true_iff in H as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* ---- spills ---- *)

Lemma r10b_bv_mod : forall a a' d, Z_to_bv 64 a = Z_to_bv 64 a' -> Z_to_bv 64 (a + d) = Z_to_bv 64 (a' + d).
Proof.
  intros a a' d H. apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap in *.
  rewrite (Zplus_mod a d), (Zplus_mod a' d), H. reflexivity.
Qed.

Lemma r10b_bytes_cong : forall m a a' bs,
  Z_to_bv 64 a = Z_to_bv 64 a' -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs m a' bs -> bytes_at rsegs m a bs.
Proof.
  intros m a a' bs Hcong Ha0 Hal (Ha'0 & Ha'l & Hr). split; [exact Ha0|]. split; [exact Hal|].
  intros i Hi.
  assert (Heq : wa (a + Z.of_nat i) = wa (a' + Z.of_nat i)).
  { unfold wa. apply r10b_bv_mod. exact Hcong. }
  rewrite Heq. exact (Hr i Hi).
Qed.

(* A q64 spill as an 8-byte read at the FRA spill base A + off. *)
Lemma r10b_spill_rd : forall (regs : bvmap 5 word) m off v A,
  spill regs m off v -> getr regs 9 = Z_to_bv 64 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  ov_read_bytes rsegs m (wa (A + off)) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros regs m off v A (A1 & Hr9' & Hq) Hr9 HA0 HAb Hoff.
  unfold rg in Hr9'. assert (Hcong : Z_to_bv 64 A = Z_to_bv 64 A1) by (rewrite <- Hr9; exact Hr9').
  unfold q64 in Hq.
  assert (HB : bytes_at rsegs m (A + off) (le8 (Z_to_bv 64 v)))
    by (eapply r10b_bytes_cong; [ apply r10b_bv_mod; exact Hcong | lia | rewrite length_le8; lia | exact Hq ]).
  exact (r10b_rdn m _ _ 8%nat HB (length_le8 _)).
Qed.

(* A q64 spill transported across a run whose write set W avoids the spill's 8-byte footprint at A + off. *)
Lemma r10b_spill_keep : forall (regs regs'' : bvmap 5 word) m m' off v A W,
  spill regs m off v -> getr regs 9 = Z_to_bv 64 A -> getr regs'' 9 = getr regs 9 ->
  0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) ->
  spill regs'' m' off v.
Proof.
  intros regs regs'' m m' off v A W (A1 & Hr9' & Hq) Hr9 K9 HA0 HAb Hoff MU Hout.
  unfold rg in Hr9'. assert (Hcong : Z_to_bv 64 A = Z_to_bv 64 A1) by (rewrite <- Hr9; exact Hr9').
  assert (Hq2 : q64 m (A + off) v).
  { unfold q64 in *.
    eapply r10b_bytes_cong; [ apply r10b_bv_mod; exact Hcong | lia | rewrite length_le8; lia | exact Hq ]. }
  exists A. split; [unfold rg; transitivity (getr regs 9); [exact K9 | exact Hr9]|].
  unfold q64 in *. eapply fl_bytes; [exact Hq2 | exact MU |]. rewrite length_le8. exact Hout.
Qed.

(* ---- the mem_rel transports of the normalized call (B3Norm's, restated) ---- *)

Lemma r10b_segs_below : BzBridge.seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r10b_ro_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (BzBridge.find_segment_below sg 0x5fe000 x n s r10b_segs_below E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma r10b_wv : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof. intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r10b_ro_hi a Ha)). tauto. Qed.

Lemma r10b_rel_stk : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi HR Hlo Hhi.
  split; intros (H0 & H1 & H); (split; [lia|]); (split; [lia|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb); (split; [apply (r10b_wv m m0 a HR ltac:(lia)); exact Hw|]);
    exists b; [rewrite <- (mrd_rel rsegs m m0 (wa a) HR) | rewrite (mrd_rel rsegs m m0 (wa a) HR)]; exact Hb.
Qed.

Lemma r10b_rel_sw : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 HR. split; intros H a Ha; pose proof (in_shadow_range a Ha) as Hr;
    assert (Hhi : 0x5fe000 <= a < 2 ^ 64)
      by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha; lia);
    destruct (H a Ha) as (Hw & b & Hb); (split; [apply (r10b_wv m m0 a HR Hhi); exact Hw|]);
    exists b; [rewrite <- (mrd_rel rsegs m m0 (wa a) HR) | rewrite (mrd_rel rsegs m m0 (wa a) HR)]; exact Hb.
Qed.

Lemma r10b_rel_ad : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n HR.
  split; intros (H0 & H1 & H2 & H); (split; [exact H0|]); (split; [exact H1|]); (split; [exact H2|]);
    intros i Hi; destruct (H i Hi) as (Hap & b & Hb & Hok); (split; [exact Hap|]); exists b;
    [rewrite <- (mrd_rel rsegs m m0 _ HR) | rewrite (mrd_rel rsegs m m0 _ HR)]; split; assumption.
Qed.

Lemma r10b_cells_gen : forall m m1, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m1 a bs) ->
  asan_cells m -> asan_cells m1.
Proof.
  intros m m1 Fb H. unfold asan_cells in *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => apply Fb; assumption end.
Qed.

Lemma r10b_rel_cells : forall m m0, mem_rel rsegs m m0 -> (asan_cells m <-> asan_cells m0).
Proof.
  intros m m0 HR. split; apply r10b_cells_gen; intros a bs Hb;
    [exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb) | exact (proj2 (bytes_at_rel rsegs m m0 a bs HR) Hb)].
Qed.

Lemma r10b_rel_wr : forall m m0 a n, mem_rel rsegs m m0 -> 0x5fe000 <= a ->
  (wr_at rsegs m a n <-> wr_at rsegs m0 a n).
Proof.
  intros m m0 a n HR Ha.
  split; intros (H0 & H1 & H); (split; [exact H0|]); (split; [exact H1|]); intros i Hi;
    apply (r10b_wv m m0 (a + i) HR ltac:(lia)); exact (H i Hi).
Qed.

Lemma r10b_rel_rw : forall m m0 a cs, mem_rel rsegs m m0 -> 0x5fe000 <= a ->
  (rw_cells rsegs m a cs <-> rw_cells rsegs m0 a cs).
Proof.
  intros m m0 a cs HR Ha. unfold rw_cells, cells_at.
  pose proof (bytes_at_rel rsegs m m0 a (cells_bytes cs) HR) as E1.
  pose proof (r10b_rel_wr m m0 a (Z.of_nat (cells_size cs)) HR Ha) as E2.
  tauto.
Qed.

Lemma r10b_ms_eta : forall s, ms_svc_pending s = None ->
  s = MS (ms_regs s) (ms_fregs s) (ms_pc_val s) (ms_fcsr s) (ms_resv s) (ms_mem s) (ms_rom s).
Proof. intros [] H; cbn in H; subst; reflexivity. Qed.

Lemma r10b_fgmem_rel : forall m m0 f pa pp pn st g c, mem_rel rsegs m m0 ->
  FGC.fg_mem f pa pp pn st g c m0 -> FGC.fg_mem f pa pp pn st g c m.
Proof.
  intros m m0 f pa pp pn st g c HR H.
  pose proof (fun a bs (Hb : bytes_at rsegs m0 a bs) => proj2 (bytes_at_rel rsegs m m0 a bs HR) Hb) as T.
  destruct c; cbn [FGC.fg_mem] in H |- *;
    [ exact I | exact I | exact (T _ _ H) | exact (T _ _ H) | exact (T _ _ H) |].
  destruct H as (H1 & H2 & H3 & H4).
  exact (conj (T _ _ H1) (conj (T _ _ H2) (conj (T _ _ H3) (T _ _ H4)))).
Qed.

(* ---- the five image cells the fragment's bcmp wrapper reads (Seg/R19.v r19_cells) ---- *)

Lemma r10b_cells : forall m, asan_cf_cells m -> asan_real_cells m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Proof.
  intros m HCF HR.
  destruct HCF as (HCF1 & _ & _ & _ & _ & _ & HCF7 & _).
  split; [exact (AsanRTInv.real_cell_of m REAL_BCMP BCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact (AsanRTInv.real_cell_of m REAL_MEMCMP MEMCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact HCF1|].
  split.
  - replace (CF + 254) with (RT_CF + 240 + Z.of_nat 14) by (unfold CF, RT_CF; lia).
    exact (r10b_byte m (RT_CF + 240) _ 14%nat (Z_to_bv 8 1) HCF7 eq_refl).
  - replace (CF + 255) with (RT_CF + 240 + Z.of_nat 15) by (unfold CF, RT_CF; lia).
    exact (r10b_byte m (RT_CF + 240) _ 15%nat (Z_to_bv 8 1) HCF7 eq_refl).
Qed.

(* ---- the model ---- *)

Lemma r10b_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img.
  match goal with |- context [match ?t with Some _ => _ | None => _ end] => destruct t as [l|] eqn:E end.
  - exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

Lemma r10b_rtX_len : forall inp b, length (rt_X inp b) = 32%nat.
Proof.
  intros inp b. unfold rt_X, BAS.ba_X, RcLay.ly_Z.
  assert (HZ : length (if mrow inp =? 0 then RcLay.ly_zero
                       else if RcSynth.rc (rt_mb inp) b =? 1 then RcSynth.synth (rt_mb inp) b (rt_nb inp)
                       else RcLay.ly_zero) = 32%nat).
  { destruct (mrow inp =? 0); [reflexivity|].
    destruct (RcSynth.rc (rt_mb inp) b =? 1); [|reflexivity].
    apply RcSynthLib.rs_synth_len. apply r10b_row_len. }
  destruct (b <=? 1); [apply RcFinLib.rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* n_b != 0: 124 <= n_b <= 1492 and F_b has n_b bytes (Tac_rt2_b2.a_rtn). *)
Lemma r10b_rtn : forall inp b, rt_n inp b <> 0 ->
  rt_E inp b = true /\ 124 <= rt_n inp b <= 1492 /\ length (rt_F inp b) = Z.to_nat (rt_n inp b).
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence].
  pose proof E as E'. unfold rt_E, BAS.ba_E in E'. apply andb_true_iff in E' as [Ew _].
  destruct (RcEmitLib.em_wok_range _ Ew) as [R _].
  split; [reflexivity|]. split; [lia|].
  unfold rt_F, RcEmit.em_fr, RcEmit.em_hdr, box6. unfold rt_n. rewrite E.
  rewrite !length_app, OUR_length, length_map, r10b_rtX_len, repeat_length. cbn [length]. lia.
Qed.

(* The record lengths of turns 5, 6 and 7 (computed over the 11 catalogue rows). *)
Lemma r10b_lens : forall inp,
  length (RFG inp 5) = 72%nat /\ length (RFG inp 6) = 72%nat /\ length (RFG inp 7) = 72%nat /\
  length (RID inp 5) = 38%nat /\ length (RID inp 6) = 38%nat.
Proof. intros inp. a_rows inp; a_fin. Qed.

(* The 50 record bytes the fragment reads are the first 50 of the frame. *)
Lemma r10b_g50 : forall m phi bs, bytes_at rsegs m phi bs -> (50 <= length bs)%nat ->
  bytes_at rsegs m phi (fr50 bs).
Proof.
  intros m phi bs H Hl. unfold fr50. rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r.
  pose proof (r10b_sub m phi bs 0 50 H ltac:(lia)) as Hs. cbn [skipn] in Hs. rewrite Z.add_0_r in Hs. exact Hs.
Qed.

(* With all five pointers nonzero the contract's case is the model's fcls. *)
Lemma r10b_cls : forall f fr pa pp pn len st g, f <> 0 -> fr <> 0 -> pa <> 0 -> pp <> 0 -> pn <> 0 ->
  fg_class f fr pa pp pn len st g = fcls len st g.
Proof.
  intros f fr pa pp pn len st g Hf Hfr Hpa Hpp Hpn. unfold fcls, fg_class.
  rewrite (proj2 (Z.eqb_neq f 0) Hf), (proj2 (Z.eqb_neq fr 0) Hfr), (proj2 (Z.eqb_neq pa 0) Hpa),
    (proj2 (Z.eqb_neq pp 0) Hpp), (proj2 (Z.eqb_neq pn 0) Hpn).
  reflexivity.
Qed.

(* ---- the branch conditions of the two arms (closed: the engine tests these booleans) ---- *)

(* 0x81694 blt s11,s7 with s11 = 4 and s7 = 6 / 5: taken. *)
Lemma r10b_c46 : bv_lts (Z_to_bv 64 4) (Z_to_bv 64 6) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r10b_c45 : bv_lts (Z_to_bv 64 4) (Z_to_bv 64 5) = true.
Proof. vm_compute. reflexivity. Qed.
(* 0x816d4 beq s7,a1 with a1 = 5: not taken for s7 = 6, taken for s7 = 5. *)
Lemma r10b_c65 : bv_eqb (Z_to_bv 64 6) (Z_to_bv 64 5) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma r10b_c55 : bv_eqb (Z_to_bv 64 5) (Z_to_bv 64 5) = true.
Proof. vm_compute. reflexivity. Qed.
(* 0x816dc bne s7,a1 with s7 = a1 = 6: not taken. *)
Lemma r10b_c66 : negb (bv_eqb (Z_to_bv 64 6) (Z_to_bv 64 6)) = false.
Proof. vm_compute. reflexivity. Qed.
(* 0x816e4 / 0x817a4 beq a0,a1 with a0 = a1 = 11: taken (the abort edges 0x816e8 / 0x817a8 are not reached). *)
Lemma r10b_c1111 : bv_eqb (Z_to_bv 64 11) (Z_to_bv 64 11) = true.
Proof. vm_compute. reflexivity. Qed.

(* A fact kept out of lia's sight (an opaque head symbol): the engine's failed address matches call lia. *)
Definition r10b_box (P : Prop) : Prop := P.

(* ---- the two write sets ---- *)

Definition r10b_W (fr spv : Z) : list ivl :=
  [(fr + 2256, fr + 2256 + 72); (fr + 2448, fr + 2448 + 2); (fr + 2464, fr + 2464 + 8);
   (fr + 2496, fr + 2496 + 8); (spv - REAC_CTRL_IDENTITY_FRAGMENT_K, spv)].

Lemma r10b_W_in : forall fr spv x, ~ outside (r10b_W fr spv) x ->
  (fr + 2256 <= x < fr + 2504) \/ (spv - REAC_CTRL_IDENTITY_FRAGMENT_K <= x < spv).
Proof.
  intros fr spv x H.
  destruct (Z_lt_le_dec x (fr + 2256)) as [H1|H1];
  [|destruct (Z_lt_le_dec x (fr + 2504)) as [H2|H2]; [left; lia|]];
  (destruct (Z_lt_le_dec x (spv - REAC_CTRL_IDENTITY_FRAGMENT_K)) as [H3|H3];
   [|destruct (Z_lt_le_dec x spv) as [H4|H4]; [right; lia|]]);
  exfalso; apply H; unfold r10b_W; cbn [outside]; repeat split; lia.
Qed.

Lemma r10b_W_out : forall fr spv x, (x < fr + 2256 \/ fr + 2504 <= x) ->
  (x < spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= x) -> outside (r10b_W fr spv) x.
Proof. intros fr spv x H1 H2. unfold r10b_W. cbn [outside]. repeat split; lia. Qed.

Lemma r10b_notout : forall lo hi W x, ~ outside ((lo, hi) :: W) x -> (lo <= x < hi) \/ ~ outside W x.
Proof.
  intros lo hi W x H. destruct (r10b_out_dec W x) as [Ho|Ho]; [|right; exact Ho].
  left. destruct (Z_lt_le_dec x lo) as [H1|H1]; [exfalso; apply H; cbn [outside]; split; [lia | exact Ho]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [lia | exfalso; apply H; cbn [outside]; split; [lia | exact Ho]].
Qed.

(* The callee's write set fg_fp, for every case, lies in r10b_W; every written byte reads back (the window from
   the callee's stk, the record and the reply cells from fg_mem, the bytes it did not write from m1). *)
Lemma r10b_wfc : forall (m1 m' : word -> option byte) fr spv nb st g,
  0 <= fr -> fr + FRAME_BYTES <= 2 ^ 64 -> 0 <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K ->
  (fr + FRAME_BYTES <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= fr) ->
  length (fg_st nb st g) = 72%nat ->
  munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) spv
           (fcls nb st g)) m1 m' ->
  stk rsegs m' (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) spv ->
  stk rsegs m1 (fr + 2256) (fr + 2504) ->
  FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st g (fcls nb st g) m' ->
  munch (r10b_W fr spv) m1 m' /\
  (forall x, ~ outside (r10b_W fr spv) x -> exists b, mrd rsegs m' (wa x) = Some b).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros m1 m' fr spv nb st g Hfr0 Hfrb Hsp0 Hsep Hlen MU STw STf FM.
  unfold fg_st in Hlen.
  remember (fcls nb st g) as cl eqn:Ecl. clear Ecl.
  assert (Hwin : forall x, spv - REAC_CTRL_IDENTITY_FRAGMENT_K <= x < spv -> exists b, mrd rsegs m' (wa x) = Some b)
    by (intros x Hx; destruct STw as (_ & _ & H); exact (proj2 (H x Hx))).
  assert (Hout : forall x,
            outside (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) spv cl) x ->
            fr + 2256 <= x < fr + 2504 -> exists b, mrd rsegs m' (wa x) = Some b).
  { intros x Hx Hr. destruct STf as (_ & _ & H). destruct (proj2 (H x Hr)) as (b & Hb).
    exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite wa_unsigned by lia. exact Hx. }
  split.
  - apply (munch_weaken (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) spv cl)
             (r10b_W fr spv) m1 m'); [|exact MU].
    unfold r10b_W. destruct cl; intros x Hx; cbn [fg_fp outside] in Hx |- *; tauto.
  - intros x Hx.
    destruct (r10b_W_in fr spv x Hx) as [Hf|Hw]; [|exact (Hwin x Hw)].
    destruct (r10b_out_dec (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496)
                              spv cl) x) as [Ho|Hno]; [exact (Hout x Ho Hf)|].
    destruct cl; cbn [fg_fp] in Hno; cbn [FGC.fg_mem] in FM; cbn [fg_next] in Hlen.
    + destruct (r10b_notout _ _ _ _ Hno) as [C|C]; [exfalso; lia | exfalso; apply C; exact I].
    + destruct (r10b_notout _ _ _ _ Hno) as [C|C]; [exfalso; lia | exfalso; apply C; exact I].
    + destruct (r10b_notout _ _ _ _ Hno) as [C|C]; [apply (r10b_ba_rd m' _ _ x FM); lia|].
      destruct (r10b_notout _ _ _ _ C) as [C2|C2]; [exfalso; lia | exfalso; apply C2; exact I].
    + destruct (r10b_notout _ _ _ _ Hno) as [C|C]; [apply (r10b_ba_rd m' _ _ x FM); lia|].
      destruct (r10b_notout _ _ _ _ C) as [C2|C2]; [exfalso; lia | exfalso; apply C2; exact I].
    + destruct (r10b_notout _ _ _ _ Hno) as [C|C]; [apply (r10b_ba_rd m' _ _ x FM); lia|].
      destruct (r10b_notout _ _ _ _ C) as [C2|C2]; [exfalso; lia | exfalso; apply C2; exact I].
    + destruct FM as (F1 & F2 & F3 & F4).
      destruct (r10b_notout _ _ _ _ Hno) as [C|C]; [apply (r10b_ba_rd m' _ _ x F1); lia|].
      destruct (r10b_notout _ _ _ _ C) as [C2|C2];
        [apply (r10b_ba_rd m' _ _ x F2); rewrite length_le2; lia|].
      destruct (r10b_notout _ _ _ _ C2) as [C3|C3];
        [apply (r10b_ba_rd m' _ _ x F3); rewrite length_le8; lia|].
      destruct (r10b_notout _ _ _ _ C3) as [C4|C4];
        [apply (r10b_ba_rd m' _ _ x F4); rewrite length_le8; lia|].
      destruct (r10b_notout _ _ _ _ C4) as [C5|C5]; [exfalso; lia | exfalso; apply C5; exact I].
Qed.

(* ---- the Lib-level run of both arms ---- *)

(* What the six argument loads and the call read in the memory after the three metadata stores. *)
Definition r10b_pre (m1 : word -> option byte) (A spv fr phi : Z) (g st : list byte) : Prop :=
  ov_read_bytes rsegs m1 (wa (A + 48)) 8 = Some (le8 (Z_to_bv 64 (fr + 2256))) /\
  ov_read_bytes rsegs m1 (wa (A + 88)) 8 = Some (le8 (Z_to_bv 64 (fr + 2448))) /\
  ov_read_bytes rsegs m1 (wa (A + 80)) 8 = Some (le8 (Z_to_bv 64 (fr + 2464))) /\
  ov_read_bytes rsegs m1 (wa (A + 72)) 8 = Some (le8 (Z_to_bv 64 (fr + 2496))) /\
  stk rsegs m1 (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) spv /\
  bytes_at rsegs m1 phi g /\ addressable m1 phi 50 /\
  rw_cells rsegs m1 (fr + 2256) [CB 72 st] /\ addressable m1 (fr + 2256) 72 /\
  stk rsegs m1 (fr + 2256) (fr + 2504) /\
  addressable m1 (fr + 2448) 2 /\ addressable m1 (fr + 2464) 8 /\ addressable m1 (fr + 2496) 8 /\
  asan_cells m1 /\ shadow_rw m1 /\
  bytes_at rsegs m1 REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m1 REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m1 GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m1 (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m1 (CF + 255) [Z_to_bv 8 1].

(* The state at the exit pc pce: the callee-saved registers kept, a0 = the fragment's result, the two write sets
   (the metadata stores m -> m1, the callee m1 -> m') and the callee's outputs. *)
Definition r10b_K (sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : word -> option byte)
    (SHv spv fr nb pce : Z) (g st : list byte) (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) : Prop :=
  pc' = Z_to_bv 64 pce /\
  exists m1 : word -> option byte,
    getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
    getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 20 = s4 /\ getr R 21 = s5 /\ getr R 22 = s6 /\
    getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
    getr R 10 = Z_to_bv 64 (fg_ret (fcls nb st g)) /\
    munch [(SHv + 306, SHv + 313)] m m1 /\ wmono rsegs m m1 /\ stk rsegs m1 (SHv + 306) (SHv + 313) /\
    munch (fg_fp REAC_CTRL_IDENTITY_FRAGMENT_K (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) spv
             (fcls nb st g)) m1 m' /\
    wmono rsegs m1 m' /\ ro_agree rsegs m' /\
    stk rsegs m' (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) spv /\ stk rsegs m1 (fr + 2256) (fr + 2504) /\
    FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) st g (fcls nb st g) m'.

(* One metadata store `sb r,off(s3)`, with the munch / stk / wmono bookkeeping (Seg/R18.v r18_sb). *)
Ltac r10b_sb SHv off STh MUh WMh :=
  let HS := fresh "HSok" in
  (lazymatch goal with
   | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
       assert (HS : store_ok rsegs mm (wa (SHv + off)) 1%nat = true)
         by (apply (r10b_stk_store_ok mm (SHv + 306) (SHv + 313) (SHv + off) STh); lia)
   end);
  step;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bs) _) =>
       apply (munch_write [(SHv + 306, SHv + 313)] _ mm (SHv + off) bs) in MUh;
         [ | lia
           | rewrite ?length_le1; cbn [length Z.of_nat]; lia
           | rewrite ?length_le1; cbn [length inside Z.of_nat]; left; lia ];
       apply (stk_write rsegs mm (SHv + 306) (SHv + 313) (SHv + off) bs) in STh;
         [ | lia | rewrite ?length_le1; cbn [length Z.of_nat]; lia ];
       apply (wmono_write rsegs _ mm aa bs) in WMh
   end);
  clear HS.

(* The byte just stored, as a one-byte run. *)
Ltac r10b_newb SHv off v Bn :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      assert (Bn : bytes_at rsegs (write_to_mem mm (wa (SHv + off)) bs) (SHv + off) [Z_to_bv 8 v]) by
        (replace [Z_to_bv 8 v] with bs by (apply a_bytes_eq; vm_compute; reflexivity);
         apply (bytes_at_write_same rsegs mm (SHv + off) bs);
         [ lia | rewrite ?length_le1; cbn [length Z.of_nat]; lia ])
  end.

(* An earlier metadata byte across a later one-byte store. *)
Ltac r10b_keepb SHv off Bn :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      apply (bytes_at_write_other rsegs mm (SHv + off) bs) in Bn;
        [ | lia
          | rewrite ?length_le1; cbn [length Z.of_nat]; lia
          | rewrite ?length_le1; cbn [length Z.of_nat]; lia ]
  end.

Lemma r10b_evt : FGC.reac_ctrl_identity_fragment_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (bb pce spv A SHv fr phi nb : Z) (g st : list byte),
    (bb = 6 /\ pce = 0x81708) \/ (bb = 5 /\ pce = 0x817c8) ->
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 SHv -> s7 = Z_to_bv 64 bb ->
    s11 = Z_to_bv 64 4 -> a0 = Z_to_bv 64 11 -> s8 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 nb ->
    HIGHMEM_BEG <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K -> spv <= APPMEM_END -> spv mod 16 = 0 ->
    0 <= A -> A + 96 <= 2 ^ 64 -> 6283264 <= SHv -> SHv + 313 <= 2 ^ 64 ->
    6283264 <= fr -> fr + FRAME_BYTES <= 2 ^ 64 -> fr mod 8 = 0 ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 50 <= nb < 2 ^ 64 ->
    (phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) ->
    (phi + 50 <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= phi) ->
    (fr + FRAME_BYTES <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= fr) ->
    app_mem (fr + 2256 + 78) -> length g = 50%nat -> length st = 72%nat ->
    stk rsegs m (SHv + 306) (SHv + 313) -> ro_agree rsegs m ->
    (forall m1, munch [(SHv + 306, SHv + 313)] m m1 -> wmono rsegs m m1 ->
       stk rsegs m1 (SHv + 306) (SHv + 313) -> ro_agree rsegs m1 ->
       bytes_at rsegs m1 (SHv + 306) [Z_to_bv 8 2] -> bytes_at rsegs m1 (SHv + 308) [Z_to_bv 8 0] ->
       bytes_at rsegs m1 (SHv + 312) [Z_to_bv 8 0] -> r10b_pre m1 A spv fr phi g st) ->
    evt rsegs
      (fun ms => exists R pc' m', ms = MS R F pc' fc None m' (seg_rom rsegs) /\
         r10b_K sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SHv spv fr nb pce g st R pc' m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81680) fc None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros FRAG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bb pce spv A SHv fr phi nb g st Harm -> -> -> -> -> -> -> -> HspK HspE Hsp16 HA0 HA96 HSH0 HSHb
    Hfr0 Hfrb Hfr8 Hphi0 Hphib Hnb Hphifr Hphiw Hfrw Happf Hgl Hstl ST HRO HPRE.
  unfold FGC.reac_ctrl_identity_fragment_contract in FRAG.
  assert (EK : REAC_CTRL_IDENTITY_FRAGMENT_K = 4656) by reflexivity.
  assert (EHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (EAE : APPMEM_END = 0x800000000000) by reflexivity.
  pose proof (munch_refl [(SHv + 306, SHv + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Ecls : fg_class (fr + 2256) phi (fr + 2448) (fr + 2464) (fr + 2496) nb st g = fcls nb st g)
    by (apply r10b_cls; lia).
  (* the separations are kept out of lia's sight during the run (the engine's failed address matches call lia) *)
  assert (DJ : r10b_box ((phi + 50 <= fr \/ fr + FRAME_BYTES <= phi) /\
                         (phi + 50 <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= phi) /\
                         (fr + FRAME_BYTES <= spv - REAC_CTRL_IDENTITY_FRAGMENT_K \/ spv <= fr)))
    by exact (conj Hphifr (conj Hphiw Hfrw)).
  clear Hphifr Hphiw Hfrw.
  (* 0x81680 li a3,2 ; 0x81684 .. 0x8168c the three metadata stores *)
  step.
  r10b_sb SHv 306 ST MU WM. r10b_newb SHv 306 2 B0.
  r10b_sb SHv 308 ST MU WM. r10b_keepb SHv 308 B0. r10b_newb SHv 308 0 B1.
  r10b_sb SHv 312 ST MU WM. r10b_keepb SHv 312 B0. r10b_keepb SHv 312 B1. r10b_newb SHv 312 0 B2.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MI : ro_agree rsegs mm)
        by (apply (r10b_ro_keep m mm [(SHv + 306, SHv + 313)] HRO MU); intros x Hx;
            cbn [outside]; split; [lia | exact I])
  end.
  destruct (HPRE _ MU WM ST MI B0 B1 B2)
    as (R48 & R88 & R80 & R72 & STw & Hgb & ADphi & RWf & ADf & STf & ADpa & ADpp & ADpn & HAC & HSW &
        HB1 & HB2 & HB3 & HB4 & HB5).
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      change (ov_read_bytes rsegs mm (wa (A + 48)) 8 = Some (le8 (Z_to_bv 64 (fr + 2256)))) in R48;
      change (ov_read_bytes rsegs mm (wa (A + 88)) 8 = Some (le8 (Z_to_bv 64 (fr + 2448)))) in R88;
      change (ov_read_bytes rsegs mm (wa (A + 80)) 8 = Some (le8 (Z_to_bv 64 (fr + 2464)))) in R80;
      change (ov_read_bytes rsegs mm (wa (A + 72)) 8 = Some (le8 (Z_to_bv 64 (fr + 2496)))) in R72
  end.
  (* 0x81690 li a2,4 ; 0x81694 blt s11,s7 (taken: 4 < bb); then the arm's own kind checks *)
  destruct Harm as [[-> ->]|[-> ->]];
    [ (* b = 6: 0x81690 li a2,4 ; 0x81694 blt (taken) ; 0x816d0 li a1,5 ; 0x816d4 beq s7,a1 (not taken) ;
         0x816d8 li a1,6 ; 0x816dc bne s7,a1 (not taken) ; 0x816e0 li a1,11 ; 0x816e4 beq a0,a1 (taken) ;
         0x816ec .. 0x81700 the six arguments ; 0x81704 jal reac_ctrl_identity_fragment *)
      step; step; first [ if_true_by r10b_c46 | if_true ];
      step; step; first [ if_false_by r10b_c65 | if_false ];
      step; step; first [ if_false_by r10b_c66 | if_false ];
      step; step; first [ if_true_by r10b_c1111 | if_true ];
      step; step; step; step; step; step; step
    | (* b = 5: 0x81690 li a2,4 ; 0x81694 blt (taken) ; 0x816d0 li a1,5 ; 0x816d4 beq s7,a1 (taken) ;
         0x817a0 li a1,11 ; 0x817a4 beq a0,a1 (taken) ; 0x817ac .. 0x817c0 the six arguments ;
         0x817c4 jal reac_ctrl_identity_fragment *)
      step; step; first [ if_true_by r10b_c45 | if_true ];
      step; step; first [ if_true_by r10b_c55 | if_true ];
      step; step; first [ if_true_by r10b_c1111 | if_true ];
      step; step; step; step; step; step; step ].
  (* the call's premises on the normalized memory *)
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in *
       end.
  all: unfold r10b_box in DJ.
  all: destruct DJ as (Hphifr & Hphiw & Hfrw).
  all: assert (MI1 : ro_agree rsegs m1) by exact MI.
  all: pose proof (mem_rel_normalize rsegs m1 MI1) as REL.
  (* (the normalized transports follow) *)
  all: assert (STw0 : stk rsegs (normalize rsegs m1) (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) spv)
    by exact (proj1 (r10b_rel_stk m1 _ (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) spv REL ltac:(lia) ltac:(lia)) STw).
  all: assert (STf0 : stk rsegs (normalize rsegs m1) (fr + 2256) (fr + 2504))
    by exact (proj1 (r10b_rel_stk m1 _ (fr + 2256) (fr + 2504) REL ltac:(lia) ltac:(lia)) STf).
  all: assert (Hgb0 : bytes_at rsegs (normalize rsegs m1) phi g)
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) Hgb).
  all: assert (RWf0 : rw_cells rsegs (normalize rsegs m1) (fr + 2256) [CB 72 st])
    by exact (proj1 (r10b_rel_rw m1 _ (fr + 2256) _ REL ltac:(lia)) RWf).
  all: assert (ADphi0 : addressable (normalize rsegs m1) phi 50) by exact (proj1 (r10b_rel_ad m1 _ _ _ REL) ADphi).
  all: assert (ADf0 : addressable (normalize rsegs m1) (fr + 2256) 72)
    by exact (proj1 (r10b_rel_ad m1 _ _ _ REL) ADf).
  all: assert (ADpa0 : addressable (normalize rsegs m1) (fr + 2448) 2)
    by exact (proj1 (r10b_rel_ad m1 _ _ _ REL) ADpa).
  all: assert (ADpp0 : addressable (normalize rsegs m1) (fr + 2464) 8)
    by exact (proj1 (r10b_rel_ad m1 _ _ _ REL) ADpp).
  all: assert (ADpn0 : addressable (normalize rsegs m1) (fr + 2496) 8)
    by exact (proj1 (r10b_rel_ad m1 _ _ _ REL) ADpn).
  all: assert (HAC0 : asan_cells (normalize rsegs m1)) by exact (proj1 (r10b_rel_cells m1 _ REL) HAC).
  all: assert (HSW0 : shadow_rw (normalize rsegs m1)) by exact (proj1 (r10b_rel_sw m1 _ REL) HSW).
  all: assert (HB10 : bytes_at rsegs (normalize rsegs m1) REAL_BCMP (le8 (wa BCMP)))
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HB1).
  all: assert (HB20 : bytes_at rsegs (normalize rsegs m1) REAL_MEMCMP (le8 (wa MEMCMP)))
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HB2).
  all: assert (HB30 : bytes_at rsegs (normalize rsegs m1) GOT_CF (le8 (wa CF)))
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HB3).
  all: assert (HB40 : bytes_at rsegs (normalize rsegs m1) (CF + 254) [Z_to_bv 8 1])
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HB4).
  all: assert (HB50 : bytes_at rsegs (normalize rsegs m1) (CF + 255) [Z_to_bv 8 1])
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HB5).
  all: assert (P17 : fr + 2256 <> 0 -> phi <> 0 -> fr + 2448 <> 0 -> fr + 2464 <> 0 -> fr + 2496 <> 0 -> 50 <= nb ->
                bytes_at rsegs (normalize rsegs m1) phi g) by (intros; exact Hgb0).
  all: assert (P18 : fr + 2256 <> 0 -> phi <> 0 -> fr + 2448 <> 0 -> fr + 2464 <> 0 -> fr + 2496 <> 0 ->
                rw_cells rsegs (normalize rsegs m1) (fr + 2256) [CB 72 st] /\ (fr + 2448) mod 2 = 0 /\
                (fr + 2464) mod 8 = 0 /\ (fr + 2496) mod 8 = 0 /\
                wr_at rsegs (normalize rsegs m1) (fr + 2448) 2 /\ wr_at rsegs (normalize rsegs m1) (fr + 2464) 8 /\
                wr_at rsegs (normalize rsegs m1) (fr + 2496) 8 /\
                all_dj [(fr + 2256, fr + 2256 + 72); (fr + 2448, fr + 2448 + 2); (fr + 2464, fr + 2464 + 8);
                        (fr + 2496, fr + 2496 + 8); (phi, phi + 50);
                        (spv - REAC_CTRL_IDENTITY_FRAGMENT_K, spv)])
    by (intros _ _ _ _ _; split; [exact RWf0|];
        split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia|];
        split; [Z.div_mod_to_equations; lia|];
        split; [apply (r10b_wr_sub _ _ _ _ _ STf0); lia|];
        split; [apply (r10b_wr_sub _ _ _ _ _ STf0); lia|];
        split; [apply (r10b_wr_sub _ _ _ _ _ STf0); lia|];
        destruct Hphifr as [Hd1|Hd1]; destruct Hphiw as [Hd2|Hd2]; destruct Hfrw as [Hd3|Hd3];
        cbn [all_dj dj_from]; repeat split; lia).
  all: assert (P24 : fr + 2256 <> 0 -> phi <> 0 -> fr + 2448 <> 0 -> fr + 2464 <> 0 -> fr + 2496 <> 0 -> 50 <= nb ->
                addressable (normalize rsegs m1) phi 50) by (intros; exact ADphi0).
  all: assert (P25 : fr + 2256 <> 0 -> phi <> 0 -> fr + 2448 <> 0 -> fr + 2464 <> 0 -> fr + 2496 <> 0 ->
                addressable (normalize rsegs m1) (fr + 2256) 72 /\ addressable (normalize rsegs m1) (fr + 2448) 2 /\
                addressable (normalize rsegs m1) (fr + 2464) 8 /\ addressable (normalize rsegs m1) (fr + 2496) 8 /\
                app_mem (fr + 2256 + 78) /\
                dj_from RT_LO RT_HI [(fr + 2256, fr + 2256 + 72); (fr + 2448, fr + 2448 + 2);
                                     (fr + 2464, fr + 2464 + 8); (fr + 2496, fr + 2496 + 8)])
    by (intros _ _ _ _ _; split; [exact ADf0|]; split; [exact ADpa0|]; split; [exact ADpp0|];
        split; [exact ADpn0|]; split; [exact Happf|]; cbn [dj_from]; unfold RT_LO, RT_HI; repeat split; lia).
  (* the call, on the normalized memory *)
  all: (eapply evt_mono;
        [ eapply (evt_normalize rsegs _ _ _ _ _ _ _ _ wx_apart_asan MI1);
          eapply FRAG with (m := normalize rsegs m1) (f := fr + 2256) (fr := phi) (len := nb) (pa := fr + 2448)
            (pp := fr + 2464) (pn := fr + 2496) (st := st) (g := g);
          rewrite ?(MState.unsigned_lit spv) by lia;
          first
            [ reflexivity
            | exact Hgl | exact Hstl | exact STw0 | exact Hsp16 | exact (mem_inv_normalize rsegs m1)
            | exact HAC0 | exact HSW0 | exact P17 | exact P18 | exact P24 | exact P25
            | exact HB10 | exact HB20 | exact HB30 | exact HB40 | exact HB50
            | lia ]
        | idtac ]).
  all: intros ms' (s0' & PO & HREL & HROS).
  all: destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                       E & MU0 & WM0 & MI0 & ST0 & FM0 & AC0 & SW0).
  all: subst s0'.
  all: destruct HREL as (ERg & EF & EP & ES & EV & EC & ERo & HMR).
  all: cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in
         ERg, EF, EP, ES, EV, EC, ERo, HMR.
  all: pose proof (r10b_ms_eta ms' ES) as Ems.
  all: rewrite ERg, EF, EP, EC, EV, ERo in Ems.
  all: lazymatch type of Ems with
       | context [ret_pc (Z_to_bv 64 ?k)] =>
           replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) in Ems
             by (symmetry; apply ret_pc_even; [lia | reflexivity])
       end.
  all: remember (ms_mem ms') as m' eqn:Em'.
  all: clear Em'.
  all: rewrite ?(MState.unsigned_lit spv) in MU0, ST0 by lia.
  all: rewrite Ecls in Ems, MU0, FM0.
  all: do 3 eexists; split; [exact Ems|].
  all: split; [reflexivity|].
  all: exists m1.
  all: do 16 (split; [reflexivity|]).
  all: split; [exact MU|]. all: split; [exact WM|]. all: split; [exact ST|].
  all: split; [exact (munch_rel rsegs _ m1 _ m' m0' REL HMR HROS MU0)|].
  all: split; [exact (wmono_rel rsegs m1 _ m' m0' REL HMR HROS WM0)|].
  all: split; [exact (ro_agree_same rsegs m1 m' MI1 HROS)|].
  all: split; [exact (proj2 (r10b_rel_stk m' m0' (spv - REAC_CTRL_IDENTITY_FRAGMENT_K) spv HMR ltac:(lia)
                                ltac:(lia)) ST0)|].
  all: split; [exact STf|].
  all: exact (r10b_fgmem_rel m' m0' _ _ _ _ _ _ _ HMR FM0).
Qed.

(* ---- the segment ---- *)

(* The parenthesized official body that Inv_A81680_at, Inv_A81708_at and (in part) Inv_A817c8_at share. *)
Definition r10b_body (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  g_n g < 2 ^ 26 /\ (b <= 6)%nat /\ HB m phi (rnb g b) /\ rg regs 23 (Z.of_nat b) /\ OURb g fr m /\ OUTA fr m /\
    CUR g 7 regs /\
    spill regs m 112 (mrow (g_in g)) /\ spill regs m 128 (fr + 544) /\ PRO g fr regs m /\
    spill regs m 104 0x21140 /\ spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\
    spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
    (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
    spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
    (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
    spill regs m 152 (Sfr fr + 68) /\ rg regs 21 (fr + 2176) /\
    addressable m (fr + 2176) 38.

(* What both arms give at their exit pc: the official body, RXS, the turn-b round-trip facts that the fragment
   does not touch (s8 = Phi, Phi's bytes, the identity record), a0 = the fragment's result and its fg_mem. *)
Definition r10b_out (g : ghost) (b : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  r10b_body g b phi fr regs m /\ RXS g fr regs m /\ rnb g b <> 0 /\ rg regs 24 phi /\
  bytes_at rsegs m phi (rt_F (g_in g) (Z.of_nat b)) /\ IDBr g fr (RID (g_in g) b) m /\
  a0v regs (fg_ret (fcls (rnb g b) (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b)))) /\
  FGC.fg_mem (fr + 2256) (fr + 2448) (fr + 2464) (fr + 2496) (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b))
    (fcls (rnb g b) (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b))) m.

(* The side-stack metadata is the first 36864 bytes of the FakeStack. *)
Lemma r10b_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold ACx.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

Section R10B.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACx.AsanAllocAPI ACx.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FRAG :
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_fragment_c.reac_ctrl_identity_fragment_contract.

(* Every frame byte is present in the state's memory (real arm: inside the entry-anchored slot window; side arm:
   inside the FakeStack, whose bytes a_fs_ok keeps mapped). *)
Lemma r10b_frame_rd : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  forall a, fr <= a < fr + FRAME_BYTES -> exists b, mbyte rsegs mem a = Some b.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md HFRA a Ha.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AFx.SLOT_STACK = 1048576) by reflexivity.
  destruct Hloc as [(H0 & Hspfr & Hreal)|(Hfr0 & HfsbS & Hfs & _)].
  - pose proof Hwin as Hw. unfold stk in Hw. destruct Hw as (_ & _ & Hwv).
    exact (proj2 (Hwv a ltac:(lia))).
  - destruct (Hfs a Ha) as (bb & Hb0 & Hwtp & Hbr).
    destruct (ACx.a_laws_fs_state ACx.ASYMS _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md bb HAH Hwtp Hb0) as (Hfsok & _).
    exact (proj2 (proj1 Hfsok a Hbr)).
Qed.

(* The heap invariant, the ownership relation and the real stack's bounds across a run that writes only the frame,
   the frame's metadata and real-stack bytes at or above stklo (Seg/R1.v r1_ah, any live list hb). *)
Lemma r10b_ah : forall g fr hb regs mem mem' md (W : list ivl),
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  (forall x, ~ outside W x -> (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
     (ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END)) ->
  (forall x, ~ outside W x -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  ACx.aa_AH ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall a, ACx.aa_owned ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
             ACx.aa_owned ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
  ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem' md =
    ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  ACx.aa_stkhi ACx.ASYMS AsanRTInv.RT (APIf rc) mem' md =
    ACx.aa_stkhi ACx.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem mem' md W HFRA MU WM HWcl HRD.
  pose proof (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ').
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
    by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
  assert (Hsh8 : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> shadow_addr (fr + 8 * (x - Sfr fr)) = x).
  { intros x Hx. rewrite r10b_sh8. unfold Sfr. lia. }
  destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5fr [Hfsb [Hfs _]]]].
  - assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
              ~ ACx.a_store_ok (hb ++ g_H g) (ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Hnok.
      destruct (r10b_out_dec W x) as [Ho|Hno].
      - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
      - exfalso. apply Hnok. destruct (HWcl x Hno) as [H|[H|H]].
        + right; left. pose proof (Hreal x ltac:(lia)). lia.
        + right; right; right. exists (fr + 8 * (x - Sfr fr)).
          split; [symmetry; exact (Hsh8 x H)|].
          right; left. apply Hreal. lia.
        + right; left. exact H. }
    destruct (ACx.a_laws_store _ _ _ _ _ ALAWS (hb ++ g_H g) mem mem' md HAH Hmc Hwrit)
      as (HAH' & Hown & Hstk' & Hhi').
    split; [exact HAH'|]. split; [exact Hown|]. split; [exact Hstk' | exact Hhi'].
  - destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
    pose proof (Hfsb FS HwFS HFSr) as HFSfr.
    destruct (ACx.a_laws_fs_place _ _ _ _ _ ALAWS (hb ++ g_H g) mem md FS HAH HwFS HFSr)
      as (HGTFS & HFSend & _ & HFSapp).
    assert (HFS64 : FS + ACx.FS_SIZE <= 2 ^ 64).
    { pose proof (HFSapp (FS + ACx.FS_SIZE - 1) ltac:(unfold ACx.FS_SIZE in *; lia)) as H.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
    assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
              exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq (b & Hb).
      destruct (r10b_out_dec W q) as [Ho|Hno].
      - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
        rewrite MState.unsigned_lit by exact Hq. exact Ho.
      - destruct (HRD q Hno) as (b' & Hb'). exists b'. exact Hb'. }
    assert (Hmeta : forall q, fs_meta FS q -> outside W q).
    { intros q Hq. pose proof (r10b_fs_meta_range FS q Hq) as Hqr.
      assert (Hqa : app_mem q) by (apply HFSapp; unfold ACx.FS_SIZE in *; lia).
      destruct (r10b_out_dec W q) as [Ho|Hno]; [exact Ho|].
      exfalso. destruct (HWcl q Hno) as [H|[H|H]].
      - lia.
      - pose proof (r10b_sh_app_dj q q ltac:(rewrite <- (Hsh8 q H);
          apply shadow_of_app; apply Happ'; lia) Hqa). lia.
      - unfold ACx.FS_SIZE in HFSend. lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ ACx.a_store_ok (hb ++ g_H g) (ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (FS <= q < FS + ACx.FS_SIZE) ->
              ~ (exists b, FS <= b < FS + ACx.FS_SIZE /\ q = shadow_addr b) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hnok Hnfs Hnsh.
      destruct (r10b_out_dec W q) as [Ho|Hno].
      - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
      - exfalso. destruct (HWcl q Hno) as [H|[H|H]].
        + apply Hnfs. unfold ACx.FS_SIZE in *. lia.
        + apply Hnsh. exists (fr + 8 * (q - Sfr fr)).
          split; [unfold ACx.FS_SIZE in *; lia | symmetry; exact (Hsh8 q H)].
        + apply Hnok. right; left. exact H. }
    destruct (a_fs_ok_store_AH _ _ _ _ _ W (hb ++ g_H g) mem mem' md FS ALAWS HAH HwFS HFSr HFS64 MU
                Hwrit Hpres Hmeta Hagree)
      as (HAH' & Hown & Hstk' & Hhi').
    split; [exact HAH'|]. split; [exact Hown|]. split; [exact Hstk' | exact Hhi'].
Qed.

(* FRA across a run whose write set is application memory inside the frame body or the callee window
   [sp - K, sp): the canonical sl_fr_cl (Seg/R1.v r1_fra_app, any live list hb and any window K). *)
Lemma r10b_fra_app : forall g fr hb regs regs' mem mem' md (W : list ivl) K,
  FRA B APIf ra g fr hb regs mem md -> 0 <= K <= FN_STACK ->
  munch W mem mem' -> wmono rsegs mem mem' -> AsanRTInv.rt_disjoint W -> all_app W ->
  (forall x, ~ outside W x -> (fr + 24 <= x < fr + FRAME_BYTES) \/ (ACx.aspZ regs - K <= x < ACx.aspZ regs)) ->
  (forall x, ~ outside W x -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs regs' mem mem' md W K HFRA HK MU WM HDJ HAW HWcl HRD E2 E3 E4 E8 E9 E19 E26.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlowin & _).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hplace & _ & _ & _).
  pose proof (Hplace K HK) as Hsep.
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AFx.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (EGT : ACx.GT = 6283264) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  rewrite Haspz in HWcl, Hlowin, Hsep.
  pose proof (ACx.a_laws_stack_high _ _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH) as Hhigh.
  assert (EHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (EAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HWout : forall x, (x < fr + 24 \/ fr + FRAME_BYTES <= x) -> (x < sp - K \/ sp <= x) -> outside W x).
  { intros x H1 H2. destruct (r10b_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. destruct (HWcl x Hno); lia. }
  destruct (r10b_ah g fr hb regs mem mem' md W HFRA MU WM
              ltac:(intros x Hx; destruct (HWcl x Hx) as [H|H]; [left; lia | right; right; split; lia]) HRD)
    as (HAH' & Hown & HSTK' & HSTKhi').
  apply (sl_fr_cl B APIf ra empty FF g fr hb regs regs' mem mem' md W HFRA MU WM
           (r10b_ro_keep mem mem' W Hro MU ltac:(intros x Hx; apply HWout; lia)) HAW HDJ HAH' HSTK').
  - intros x Hx. apply HWout; lia.
  - intros x Hx. apply HWout; [lia | destruct Hsep; lia].
  - intros A0 HA0 HA0r x Hx.
    assert (A0 = A) by (rewrite <- HbvA, HA0, MState.unsigned_lit by lia; reflexivity).
    subst A0. apply HWout; lia.
  - intros x Hx. apply HWout; lia.
  - intros x Hx. destruct (r10b_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso.
    assert (Hin : in_shadow x) by (replace x with (Sfr fr + (x - Sfr fr)) by lia;
      apply r10b_fsh; [exact Happ | lia]).
    destruct (HWcl x Hno) as [H|H].
    + pose proof (r10b_sh_app_dj x x Hin (Happ x ltac:(lia))). lia.
    + pose proof (r10b_sh_app_dj x x Hin ltac:(unfold app_mem; right; lia)). lia.
  - intros A0 HA0 HA0r x Hx.
    assert (A0 = A) by (rewrite <- HbvA, HA0, MState.unsigned_lit by lia; reflexivity).
    subst A0. apply HWout; lia.
  - apply (r10b_stk_tr W mem mem' _ _ Hwin MU WM). intros x Hx.
    destruct (r10b_out_dec W x) as [Ho|Hno]; [left; exact Ho | right; exact (HRD x Hno)].
  - apply (fra_fsrec_stklo B APIf ra g fr hb regs mem mem' md W HFRA MU).
    intros x Hx Hnb. destruct (r10b_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. destruct (HWcl x Hno) as [H|H]; lia.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.

(* FRA and ENT across the three stores into the frame's metadata bytes S(fr) + 306 .. + 312 (Seg/R18.v
   r18_sh_move for the range [S(fr) + 306, S(fr) + 313)). *)
Lemma r10b_sh_move : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md -> ENT (fx := fx) APIf g hb mem md ->
  munch [(Sfr fr + 306, Sfr fr + 313)] mem mem' -> wmono rsegs mem mem' ->
  (forall qq, Sfr fr + 306 <= qq < Sfr fr + 313 -> exists b, mrd rsegs mem' (wa qq) = Some b) ->
  FRA B APIf ra g fr hb regs mem' md /\ ENT (fx := fx) APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem mem' md HFRA HENT MU WM HPres.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (ACx.a_laws_stack_high ACx.ASYMS _ _ _ _ ALAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  unfold ACx.GT in HGT.
  assert (EHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (EAK : ASAN_K = 0x7fff8000) by reflexivity.
  assert (EAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)); lia).
  assert (Hinsh : forall x, Sfr fr + 306 <= x < Sfr fr + 313 -> in_shadow x).
  { intros x Hx. replace x with (Sfr fr + (x - Sfr fr)) by lia. apply r10b_fsh; [exact Happ | lia]. }
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (r10b_fsh fr (FRAME_SHADOW - 1) Happ ltac:(lia)) as IS.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  assert (HA64 : 0 <= A < 2 ^ 64) by (pose proof Hwin as Hw; unfold stk in Hw; lia).
  assert (HAhi : A + 312 <= 2 ^ 64).
  { unfold q64 in Hspill. apply bytes_at_bound in Hspill. rewrite length_le8 in Hspill. lia. }
  assert (HAlo : HIGHMEM_BEG <= A) by (unfold AFx.SLOT_STACK in Hstklo; lia).
  assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x).
  { intros x Hx Hwx. exact (WM (Z_to_bv 64 x) Hwx). }
  assert (Hout : forall x, 0 <= x < 2 ^ 64 -> ~ (Sfr fr + 306 <= x < Sfr fr + 313) ->
                   mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hx Hn. apply MU. rewrite MState.unsigned_lit by exact Hx.
    cbn [outside]. split; [exact Hn | exact I]. }
  assert (Hpres : forall q0, 0 <= q0 < 2 ^ 64 -> (exists b, mbyte rsegs mem q0 = Some b) ->
            exists b, mbyte rsegs mem' q0 = Some b).
  { intros q0 Hq0 Hb.
    destruct (Z_lt_le_dec q0 (Sfr fr + 306)) as [H1|H1].
    - unfold mbyte. rewrite (Hout q0 Hq0 ltac:(lia)). exact Hb.
    - destruct (Z_lt_le_dec q0 (Sfr fr + 313)) as [H2|H2].
      + exact (HPres q0 ltac:(lia)).
      + unfold mbyte. rewrite (Hout q0 Hq0 ltac:(lia)). exact Hb. }
  assert (LAWS : ACx.aa_AH ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                 (forall a, ACx.aa_owned ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
                            ACx.aa_owned ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
                 ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem' md
                   = ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                 ACx.aa_stkhi ACx.ASYMS AsanRTInv.RT (APIf rc) mem' md
                   = ACx.aa_stkhi ACx.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { apply (r10b_ah g fr hb regs mem mem' md [(Sfr fr + 306, Sfr fr + 313)] HFRA MU WM).
    - intros x Hx. right; left.
      destruct (Z_lt_le_dec x (Sfr fr + 306)) as [H1|H1];
        [exfalso; apply Hx; cbn [outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec x (Sfr fr + 313)) as [H2|H2];
        [lia | exfalso; apply Hx; cbn [outside]; split; [lia | exact I]].
    - intros x Hx.
      destruct (Z_lt_le_dec x (Sfr fr + 306)) as [H1|H1];
        [exfalso; apply Hx; cbn [outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec x (Sfr fr + 313)) as [H2|H2];
        [exact (HPres x ltac:(lia)) | exfalso; apply Hx; cbn [outside]; split; [lia | exact I]]. }
  destruct LAWS as (HAH' & HOWN' & HSTK' & HSHI').
  (* the new 392 metadata bytes of the frame *)
  assert (Hsh' : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
  { destruct Hsh as (sh0 & Hb0 & HL0).
    apply (r10b_bytes_of_present (Z.to_nat FRAME_SHADOW) mem' (Sfr fr)); [lia | lia |].
    intros k Hk.
    pose proof (proj2 (proj2 Hb0) k ltac:(lia)) as Hb0k.
    destruct (nth_error sh0 k) as [b|] eqn:Ek; [|exfalso; apply nth_error_None in Ek; lia].
    destruct (Z_lt_le_dec (Sfr fr + Z.of_nat k) (Sfr fr + 306)) as [H1|H1].
    - exists b. unfold mrd, wa in Hb0k |- *. rewrite (Hout (Sfr fr + Z.of_nat k) ltac:(lia) ltac:(lia)).
      exact Hb0k.
    - destruct (Z_lt_le_dec (Sfr fr + Z.of_nat k) (Sfr fr + 313)) as [H2|H2].
      + exact (HPres (Sfr fr + Z.of_nat k) ltac:(lia)).
      + exists b. unfold mrd, wa in Hb0k |- *. rewrite (Hout (Sfr fr + Z.of_nat k) ltac:(lia) ltac:(lia)).
        exact Hb0k. }
  assert (HA9 : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 -> A0 = A).
  { intros A0 HA0r HA0b. unfold rg in Hr9.
    pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HA0r)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A (2 ^ 64)) in E0 by lia. rewrite (Z.mod_small A0 (2 ^ 64)) in E0 by lia.
    symmetry; exact E0. }
  assert (Hrokeep : ro_agree rsegs mem').
  { apply (r10b_ro_keep mem mem' _ Hro MU). intros x Hx.
    cbn [outside]. split; [|exact I]. unfold ASAN_K in HSfrlo. lia. }
  assert (HDJ : AsanRTInv.rt_disjoint [(Sfr fr + 306, Sfr fr + 313)]).
  { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
      RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
      RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [disjoint_from].
    unfold ASAN_K in HSfrlo. repeat split; (lia || exact I). }
  assert (HWkept : forall x, 0 <= x < 2 ^ 64 -> ~ (fr + 24 <= x < fr + FRAME_BYTES) ->
            ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) -> outside [(Sfr fr + 306, Sfr fr + 313)] x).
  { intros x Hx Hnb Hnsh. cbn [outside]. split; [|exact I]. lia. }
  assert (HWspill : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
            forall x, A0 + 304 <= x < A0 + 312 -> outside [(Sfr fr + 306, Sfr fr + 313)] x).
  { intros A0 HA0r HA0b x Hx. pose proof (HA9 A0 HA0r HA0b) as <-.
    cbn [outside]. split; [|exact I]. lia. }
  assert (HWsaved : forall x, g_S g - 104 <= x < g_S g -> outside [(Sfr fr + 306, Sfr fr + 313)] x).
  { intros x Hx. cbn [outside]. split; [|exact I]. lia. }
  assert (HWsel : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
            forall x, A0 + 16 <= x < A0 + 32 -> outside [(Sfr fr + 306, Sfr fr + 313)] x).
  { intros A0 HA0r HA0b x Hx. pose proof (HA9 A0 HA0r HA0b) as <-.
    cbn [outside]. split; [|exact I]. lia. }
  assert (HWwin : forall x, g_S g - AFx.SLOT_STACK <= x < g_S g ->
            outside [(Sfr fr + 306, Sfr fr + 313)] x \/ exists b, mem' (wa x) = Some b).
  { intros x Hx. left. cbn [outside]. split; [|exact I].
    unfold AFx.SLOT_STACK in *. lia. }
  assert (HAG' : forall a, in_globals AFx.frame_AG a -> addressable mem' a 1).
  { intros a Hin.
    apply (addr1_munch [(Sfr fr + 306, Sfr fr + 313)] mem mem' a MU); [|exact (HAG a Hin)].
    cbn [outside]. split; [|exact I].
    destruct Hin as (lo & len & Hinl & Hr).
    pose proof (r10b_AG_lt a lo len Hinl Hr) as Halt.
    unfold Sfr, shadow_addr, ASAN_K in *.
    revert Halt HGT. Z.div_mod_to_equations. lia. }
  split.
  - exact (sl_fr_meta B APIf ra empty FF g fr hb regs regs mem mem'
             md [(Sfr fr + 306, Sfr fr + 313)] HFRA MU WM
             Hrokeep HDJ HAH' HSTK' Happ ltac:(unfold ACx.GT; lia) Hsh' HWkept HWspill HWsaved HWsel HWwin HAG'
             eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl).
  - apply (ent_store B APIf ra g fr hb regs mem mem' md [(Sfr fr + 306, Sfr fr + 313)] HENT HFRA MU);
      [| exact HSTK' | exact HSHI' |].
    + intros x Hx.
      destruct (Z_lt_le_dec x (Sfr fr + 306)) as [H1|H1];
        [left; cbn [outside]; split; [lia|exact I]|].
      destruct (Z_lt_le_dec x (Sfr fr + 313)) as [H2|H2];
        [|left; cbn [outside]; split; [lia|exact I]].
      right. right. right. lia.
    + intros a Himg Ho. exact (proj2 (HOWN' a) Ho).
Qed.

(* The shared part of both arms: from the entry cut, a run to the exit pc pce whose state carries FRA, ENT and
   r10b_out. *)
Lemma r10b_run : forall (b : nat) (pce : Z) (P : config -> Prop) (g : ghost) (c : config),
  (b = 6%nat /\ pce = 0x81708) \/ (b = 5%nat /\ pce = 0x817c8) ->
  Inv_A81680_at (fx := fx) B APIf ra g b c ->
  (forall regs mem md fr phi,
     FRA B APIf ra g fr (hb1 phi (rnb g b)) regs mem md ->
     ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem md ->
     r10b_out g b phi fr regs mem ->
     SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 pce) mem (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) c P.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros b pce P g c Harm HInv HK.
  pose proof (proj1 FF) as SEGS.
  assert (Hbn : (b = 5 \/ b = 6)%nat) by (destruct Harm as [[-> _]|[-> _]]; [right | left]; reflexivity).
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hbody & HX).
  pose proof Hbody as (Hgn & Hb6 & HHB & H23 & HOUR & HOUTA & HCUR & Hsp112 & Hsp128 & HPRO & Hsp104 &
    Hsp96 & Hsp64 & Hsp144 & Hsp208 & HRWid & HRWjk & Hsp280 & Hsp240 & HRWjy & HRWj32 & Hsp152 & H21 & HAid).
  pose proof HPRO as (Hsp40 & Hsp120 & Hsp136 & Hsp160 & Hsp168 & Hsp176 & Hsp200 & Hsp248 & HAour & HIN & HINL &
    Hsp184 & Hsp256 & Hsp264 & Hsp272 & Hsp32).
  destruct HX as (HRF & HRXS & Ha0 & H27).
  destruct HRF as ((HRB & Hnz & H24 & HF) & H18).
  destruct HRB as (_ & _ & _ & _ & HIDB & HFGB).
  pose proof HRXS as (Hsp48 & Hsp56 & Hsp88 & Hsp80 & Hsp72 & Hsp16 & Hsp8 & Hsp192 & Hsp216 & HAfg).
  subst c.
  (* ---- the model ---- *)
  assert (Hk11 : rt_k (g_in g) (Z.of_nat b) = 11).
  { apply a_rtm_k11; [destruct Hbn as [-> | ->]; [left | right]; reflexivity | exact Hnz]. }
  unfold a0v in Ha0. rewrite Hk11 in Ha0.
  destruct (r10b_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HLF).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in Hnb, HLF.
  pose proof (r10b_lens (g_in g)) as (HL5 & HL6 & HL7 & HI5 & HI6).
  assert (HLst : length (RFG (g_in g) b) = 72%nat) by (destruct Hbn as [-> | ->]; assumption).
  assert (HLid : length (RID (g_in g) b) = 38%nat) by (destruct Hbn as [-> | ->]; assumption).
  assert (HLfs : length (fg_st (rnb g b) (RFG (g_in g) b) (rt_g (g_in g) (Z.of_nat b))) = 72%nat).
  { pose proof (proj2 (a_RS_56 (g_in g) b Hbn Hnz)) as E. unfold rnb. rewrite <- E.
    destruct Hbn as [-> | ->]; assumption. }
  set (g50 := rt_g (g_in g) (Z.of_nat b)).
  set (st := RFG (g_in g) b).
  assert (Hg50l : length g50 = 50%nat) by (unfold g50, rt_g; apply fr50_length).
  (* ---- the frame, the window and the block ---- *)
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hlowin & Hstkwin).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (Hfrpl & Hfr9 & Hfspl & Hfrwr).
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (HGTfr & Hframeapp).
  rewrite Haspz in Hlowin, Hstkwin, Hfrpl.
  pose proof (ACx.a_laws_stack_high ACx.ASYMS _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))
                (hb1 phi (rnb g b) ++ g_H g) mem md HAH) as Hhigh.
  pose proof (ACx.a_laws_blocks ACx.ASYMS _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))
                (hb1 phi (rnb g b) ++ g_H g) mem md phi (rnb g b) HAH
                ltac:(unfold hb1; apply in_or_app; left; apply in_eq)) as (Hal & Hphilo & Hphihi & Hein & Hphib).
  pose proof HRT as (HAC & HSW & HasO & HCF & HasR & HREAL & HasRest).
  assert (EK : REAC_CTRL_IDENTITY_FRAGMENT_K = 4656) by reflexivity.
  assert (EHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (EAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (ELE : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (EAK : ASAN_K = 0x7fff8000) by reflexivity.
  assert (ESS : AFx.SLOT_STACK = 1048576) by reflexivity.
  assert (EFN : FN_STACK = 1044480) by reflexivity.
  assert (EGT : ACx.GT = 6283264) by reflexivity.
  assert (HA0 : 0 <= A) by (pose proof Hwin as Hw; unfold stk in Hw; lia).
  assert (HSle : g_S g <= 2 ^ 64) by (pose proof Hwin as Hw; unfold stk in Hw; lia).
  assert (HA312 : A + 312 <= 2 ^ 64) by lia.
  assert (Hframe8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  assert (Hfr0 : 6283264 <= fr) by lia.
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Hframeapp (fr + FRAME_BYTES - 1) ltac:(lia)) as H. unfold app_mem in H. lia. }
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia).
  assert (HSfr380 : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (r10b_fsh fr (FRAME_SHADOW - 1) Hframeapp ltac:(lia)) as IS.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS. lia. }
  assert (HspK : HIGHMEM_BEG <= sp - REAC_CTRL_IDENTITY_FRAGMENT_K) by lia.
  assert (Hsep : fr + FRAME_BYTES <= sp - REAC_CTRL_IDENTITY_FRAGMENT_K \/ sp <= fr)
    by (rewrite EK; apply (Hfrpl 4656); lia).
  assert (Hblkfr : fr + FRAME_BYTES <= phi \/ phi + rnb g b <= fr).
  { destruct Hloc as [(H0' & Hspfr & Hreal)|(Hfr0' & HfsbS & Hfs & _)].
    - right. pose proof (Hreal fr ltac:(lia)). lia.
    - destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [Hle|Hgt]; [left; exact Hle|].
      destruct (Z_le_gt_dec (phi + rnb g b) fr) as [Hle2|Hgt2]; [right; exact Hle2|].
      exfalso.
      destruct (Hphib (Z.max phi fr) ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
      exact (Hnfs (Hfs (Z.max phi fr) ltac:(lia))). }
  assert (Hphiw : phi + rnb g b <= sp - REAC_CTRL_IDENTITY_FRAGMENT_K) by lia.
  (* the harness's input block (PRO): live, below the real stack and apart from the frame on both arms *)
  assert (HINblk : 0 < g_n g -> (forall x, g_p g <= x < g_p g + g_n g -> app_mem x) /\
            g_p g + g_n g <= ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md /\
            (fr + FRAME_BYTES <= g_p g \/ g_p g + g_n g <= fr)).
  { intros Hn0. destruct (HINL Hn0) as (Hin & _).
    pose proof (ACx.a_laws_blocks ACx.ASYMS _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))
                  (hb1 phi (rnb g b) ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hqhi & _ & Hqb).
    split; [intros x Hx; exact (proj1 (Hqb x Hx))|]. split; [exact Hqhi|].
    destruct Hloc as [(H0' & Hspfr & Hreal)|(Hfr0' & HfsbS & Hfs & _)].
    - right. pose proof (Hreal fr ltac:(lia)). lia.
    - destruct (Z_le_gt_dec (fr + FRAME_BYTES) (g_p g)) as [Hle|Hgt]; [left; exact Hle|].
      destruct (Z_le_gt_dec (g_p g + g_n g) fr) as [Hle2|Hgt2]; [right; exact Hle2|].
      exfalso.
      destruct (Hqb (Z.max (g_p g) fr) ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
      exact (Hnfs (Hfs (Z.max (g_p g) fr) ltac:(lia))). }
  (* ---- the memory facts before the stores ---- *)
  set (W1 := [(Sfr fr + 306, Sfr fr + 313)]).
  assert (HoW1 : forall x, app_mem x -> outside W1 x)
    by (intros x Hx; exact (r10b_appbyte_out fr 306 313 x Hframeapp ltac:(lia) ltac:(lia) Hx)).
  assert (Happhi : forall x, HIGHMEM_BEG <= x < APPMEM_END -> app_mem x) by (intros x Hx; right; exact Hx).
  assert (STwin : stk rsegs mem (sp - REAC_CTRL_IDENTITY_FRAGMENT_K) sp).
  { destruct (stk_split rsegs mem (g_S g - AFx.SLOT_STACK) (sp - REAC_CTRL_IDENTITY_FRAGMENT_K) (g_S g)
                Hwin ltac:(lia)) as (_ & H1).
    destruct (stk_split rsegs mem (sp - REAC_CTRL_IDENTITY_FRAGMENT_K) sp (g_S g) H1 ltac:(lia)) as (H2 & _).
    exact H2. }
  assert (STfr : stk rsegs mem (fr + 2256) (fr + 2504)).
  { split; [lia|]. split; [lia|]. intros a Ha. split.
    - exact (Hfrwr a ltac:(lia)).
    - destruct (r10b_frame_rd g fr (hb1 phi (rnb g b)) regs mem md HFRA a ltac:(lia)) as (bb & Hbb).
      exists bb. exact Hbb. }
  assert (ST306 : stk rsegs mem (Sfr fr + 306) (Sfr fr + 313)).
  { split; [lia|]. split; [lia|]. intros a Ha. apply HSW.
    replace a with (Sfr fr + (a - Sfr fr)) by lia. apply r10b_fsh; [exact Hframeapp | lia]. }
  pose proof (r10b_cells mem HCF HREAL) as (HBc1 & HBc2 & HBc3 & HBc4 & HBc5).
  assert (HFg : bytes_at rsegs mem phi g50).
  { unfold g50, rt_g. apply r10b_g50; [exact HF | rewrite HLF; lia]. }
  assert (HRWst : rw_cells rsegs mem (fr + 2256) [CB 72 st]).
  { split; [split|].
    - cbn [cells_wf cell_wf]. split; [exact HLst | exact I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HFGB.
    - cbn [cells_size csize]. rewrite ?Nat.add_0_r.
      apply (r10b_wr_sub _ _ _ _ _ STfr); lia. }
  assert (Hsz : ACx.a_size (rnb g b) = rnb g b) by (unfold ACx.a_size; lia).
  destruct HHB as (Hphinz & HAphi). rewrite Hsz in HAphi.
  assert (HAphi50 : addressable mem phi 50).
  { pose proof HAphi as (H1 & H2 & H3 & H). split; [lia|]. split; [lia|]. split; [lia|].
    intros i Hi. apply H. lia. }
  assert (HshPhi : forall i, 0 <= i < rnb g b -> outside W1 (shadow_addr (phi + i))).
  { intros i Hi. apply (r10b_shobj_out fr 306 313 phi (rnb g b) i Hframe8 ltac:(lia) ltac:(lia));
      [destruct Hblkfr; [right | left]; lia | exact Hi]. }
  (* ---- the run ---- *)
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x81680) mem md
    (r10b_K (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 8) (getr regs 9) (getr regs 18)
       (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
       (getr regs 25) (getr regs 26) (getr regs 27) mem (Sfr fr) sp fr (rnb g b) pce g50 st) P).
  - exact Hhalt.
  - cbn [Regs6ss.mkR_of].
    unfold rg in H23, H24, H18, H27, Ha0, Hr9, Hr19.
    apply (r10b_evt FRAG) with (bb := Z.of_nat b) (spv := sp) (A := A) (SHv := Sfr fr) (fr := fr) (phi := phi).
    + destruct Harm as [[-> ->]|[-> ->]]; [left | right]; split; reflexivity.
    + exact Hr2.
    + exact Hr9.
    + exact Hr19.
    + exact H23.
    + exact H27.
    + exact Ha0.
    + exact H24.
    + exact H18.
    + exact HspK.
    + lia.
    + exact Hspm.
    + exact HA0.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact Hframe8.
    + lia.
    + lia.
    + lia.
    + destruct Hblkfr; [right | left]; lia.
    + left; lia.
    + exact Hsep.
    + apply Hframeapp. lia.
    + exact Hg50l.
    + exact HLst.
    + exact ST306.
    + exact Hro.
    + (* the facts the loads and the call read, after the three metadata stores *)
      intros m1 MU1 WM1 ST1 RO1 B306 B308 B312.
      unfold r10b_pre.
      assert (Hsk : forall off v, 0 <= off -> off + 8 <= 312 -> spill regs mem off v -> spill regs m1 off v).
      { intros off v Ho1 Ho2 HS.
        apply (r10b_spill_keep regs regs mem m1 off v A W1 HS Hr9 eq_refl HA0 ltac:(lia) ltac:(lia) MU1).
        intros x Hx. apply HoW1. apply Happhi. lia. }
      split; [exact (r10b_spill_rd regs m1 48 _ A (Hsk 48 _ ltac:(lia) ltac:(lia) Hsp48) Hr9 HA0 ltac:(lia) ltac:(lia))|].
      split; [exact (r10b_spill_rd regs m1 88 _ A (Hsk 88 _ ltac:(lia) ltac:(lia) Hsp88) Hr9 HA0 ltac:(lia) ltac:(lia))|].
      split; [exact (r10b_spill_rd regs m1 80 _ A (Hsk 80 _ ltac:(lia) ltac:(lia) Hsp80) Hr9 HA0 ltac:(lia) ltac:(lia))|].
      split; [exact (r10b_spill_rd regs m1 72 _ A (Hsk 72 _ ltac:(lia) ltac:(lia) Hsp72) Hr9 HA0 ltac:(lia) ltac:(lia))|].
      split.
      { apply (r10b_stk_tr W1 mem m1 _ _ STwin MU1 WM1). intros x Hx. left. apply HoW1, Happhi. lia. }
      split.
      { apply (fl_bytes W1 mem m1 phi g50 HFg MU1). intros x Hx. rewrite Hg50l in Hx.
        apply HoW1. exact (proj1 (Hphib x ltac:(lia))). }
      split.
      { apply (r10b_addr_keep W1 mem m1 phi 50 HAphi50 MU1). intros i Hi. apply HshPhi. lia. }
      split.
      { apply (r10b_rwcb_keep W1 mem m1 (fr + 2256) 72 st MU1 WM1); [|exact HRWst].
        intros x Hx. apply HoW1, Hframeapp. lia. }
      split.
      { apply (r10b_addr_keep W1 mem m1 (fr + 2256) 72 HAfg MU1). intros i Hi.
        apply (r10b_shobj_out fr 306 313 (fr + 2256) 72 i Hframe8 ltac:(lia) ltac:(lia)); [left; lia | exact Hi]. }
      split.
      { apply (r10b_stk_tr W1 mem m1 _ _ STfr MU1 WM1). intros x Hx. left. apply HoW1, Hframeapp. lia. }
      split.
      { apply (r10b_addr_r m1 (fr + 2448) 2 (Z_to_bv 8 2)); [lia | Z.div_mod_to_equations; lia | lia |
          vm_compute; reflexivity | lia | intros i Hi; apply Hframeapp; lia |].
        replace (shadow_addr (fr + 2448)) with (Sfr fr + 306)
          by (replace (fr + 2448) with (fr + 8 * 306) by lia; rewrite r10b_sh8; reflexivity).
        exact B306. }
      split.
      { apply (r10b_addr_z m1 (fr + 2464) 1 8); [reflexivity | lia | Z.div_mod_to_equations; lia | lia |
          intros i Hi; apply Hframeapp; lia |].
        replace (shadow_addr (fr + 2464)) with (Sfr fr + 308)
          by (replace (fr + 2464) with (fr + 8 * 308) by lia; rewrite r10b_sh8; reflexivity).
        exact B308. }
      split.
      { apply (r10b_addr_z m1 (fr + 2496) 1 8); [reflexivity | lia | Z.div_mod_to_equations; lia | lia |
          intros i Hi; apply Hframeapp; lia |].
        replace (shadow_addr (fr + 2496)) with (Sfr fr + 312)
          by (replace (fr + 2496) with (fr + 8 * 312) by lia; rewrite r10b_sh8; reflexivity).
        exact B312. }
      assert (HWlo1 : forall x, 0 <= x < 6283264 -> outside W1 x).
      { intros x Hx. unfold W1. cbn [outside]. split; [|exact I]. lia. }
      split.
      { pose proof HAC as HAC'. unfold asan_cells in HAC' |- *.
        decompose [and] HAC'.
        repeat split;
          (eapply r10b_keep_low; [exact MU1 | eassumption | exact HWlo1 |
             rewrite ?length_le8, ?length_le4; cbn [length Z.of_nat];
             unfold CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND,
               GOT_HIEND, MIDBEG, GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, REAL_MEMSET,
               GOT_REAL_MEMSET; lia]). }
      split.
      { apply (r10b_shadow_rw W1 mem m1 HSW MU1 WM1). intros a Ha.
        destruct (Z_lt_le_dec a (Sfr fr + 306)) as [H1|H1];
          [left; unfold W1; cbn [outside]; split; [lia | exact I]|].
        destruct (Z_lt_le_dec a (Sfr fr + 313)) as [H2|H2];
          [|left; unfold W1; cbn [outside]; split; [lia | exact I]].
        right. destruct ST1 as (_ & _ & ST1v). exact (proj2 (ST1v a ltac:(lia))). }
      split; [apply (r10b_keep_low W1 mem m1 _ _ MU1 HBc1 HWlo1); rewrite length_le8; unfold REAL_BCMP; lia|].
      split; [apply (r10b_keep_low W1 mem m1 _ _ MU1 HBc2 HWlo1); rewrite length_le8; unfold REAL_MEMCMP; lia|].
      split; [apply (r10b_keep_low W1 mem m1 _ _ MU1 HBc3 HWlo1); rewrite length_le8; unfold GOT_CF; lia|].
      split; [apply (r10b_keep_low W1 mem m1 _ _ MU1 HBc4 HWlo1); cbn [length]; unfold CF; lia|].
      apply (r10b_keep_low W1 mem m1 _ _ MU1 HBc5 HWlo1); cbn [length]; unfold CF; lia.
  - (* the continuation at pce: FRA, ENT and the carried facts *)
    intros R pc' mem' regs'' md'
      (Hpc & m1 & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K10 &
       MU1 & WM1 & ST1 & MU2 & WM2 & RO2 & STw2 & STf1 & FM2) Hreg Hmat.
    subst pc'.
    (* phase 1: the three metadata stores *)
    assert (HPres1 : forall qq, Sfr fr + 306 <= qq < Sfr fr + 313 -> exists bb, mrd rsegs m1 (wa qq) = Some bb).
    { intros qq Hq. destruct ST1 as (_ & _ & ST1v). exact (proj2 (ST1v qq Hq)). }
    destruct (r10b_sh_move g fr (hb1 phi (rnb g b)) regs mem m1 md HFRA HENT MU1 WM1 HPres1)
      as (HFRA1 & HENT1).
    (* phase 2: the callee *)
    set (W2 := r10b_W fr sp).
    destruct (r10b_wfc m1 mem' fr sp (rnb g b) st g50 ltac:(lia) ltac:(lia) ltac:(lia) Hsep HLfs MU2 STw2 STf1 FM2)
      as (MUW2 & HRD2).
    fold W2 in MUW2, HRD2.
    assert (HW2in : forall x, ~ outside W2 x ->
              (fr + 2256 <= x < fr + 2504) \/ (sp - REAC_CTRL_IDENTITY_FRAGMENT_K <= x < sp))
      by (intros x Hx; exact (r10b_W_in fr sp x Hx)).
    assert (HoW2 : forall x, (x < fr + 2256 \/ fr + 2504 <= x) ->
              (x < sp - REAC_CTRL_IDENTITY_FRAGMENT_K \/ sp <= x) -> outside W2 x)
      by (intros x H1 H2; exact (r10b_W_out fr sp x H1 H2)).
    assert (HAW2 : all_app W2).
    { unfold W2, r10b_W. cbn [all_app]. unfold app_ivl.
      repeat split; first [ exact I | intros a Ha; first [ apply Hframeapp; lia | apply Happhi; lia ] ]. }
    assert (HDJ2 : AsanRTInv.rt_disjoint W2).
    { unfold W2, r10b_W, AsanRTInv.rt_disjoint; cbn [disjoint_from].
      unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
        RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
      repeat split; first [ lia | exact I ]. }
    assert (HW2cl : forall x, ~ outside W2 x -> (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
              (ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) m1 md <= x < APPMEM_END)).
    { pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g b)) regs m1 md HFRA1) as (Hlo1 & _).
      rewrite Haspz in Hlo1.
      intros x Hx. destruct (HW2in x Hx) as [H|H]; [left; lia | right; right; lia]. }
    destruct (r10b_ah g fr (hb1 phi (rnb g b)) regs m1 mem' md W2 HFRA1 MUW2 WM2 HW2cl HRD2)
      as (HAH2 & HOWN2 & HSTK2 & HSHI2').
    assert (E2 : getr regs'' 2 = getr regs 2) by exact (eq_trans (Hreg _) K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by exact (eq_trans (Hreg _) K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by exact (eq_trans (Hreg _) K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by exact (eq_trans (Hreg _) K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by exact (eq_trans (Hreg _) K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by exact (eq_trans (Hreg _) K19).
    assert (E26 : getr regs'' 26 = getr regs 26) by exact (eq_trans (Hreg _) K26).
    assert (HFRAmd : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md).
    { apply (r10b_fra_app g fr (hb1 phi (rnb g b)) regs regs'' m1 mem' md W2 REAC_CTRL_IDENTITY_FRAGMENT_K
               HFRA1 ltac:(lia) MUW2 WM2 HDJ2 HAW2); [| exact HRD2 | exact E2 | exact E3 | exact E4 |
               exact E8 | exact E9 | exact E19 | exact E26].
      intros x Hx. rewrite Haspz. destruct (HW2in x Hx) as [H|H]; [left; lia | right; exact H]. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRAmd);
        try reflexivity. exact Hmat. }
    assert (HENT2 : ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem' md).
    { apply (ent_store B APIf ra g fr (hb1 phi (rnb g b)) regs m1 mem' md W2 HENT1 HFRA1 MUW2);
        [| exact HSTK2 | exact HSHI2' |].
      - intros x Hx. destruct (r10b_out_dec W2 x) as [Ho|Hno]; [left; exact Ho|].
        destruct (HW2in x Hno) as [H|H].
        + right. right. left. lia.
        + right. left. lia.
      - intros a Himg Ho. exact (proj2 (HOWN2 a) Ho). }
    pose proof (ent_mat APIf g (hb1 phi (rnb g b)) mem' md md' HENT2 Hmat) as HENT'.
    (* ---- the carried facts ---- *)
    assert (Hkeep : forall a bs, bytes_at rsegs mem a bs ->
              (forall x, a <= x < a + Z.of_nat (length bs) -> app_mem x /\ outside W2 x) ->
              bytes_at rsegs mem' a bs).
    { intros a bs Hb Hr.
      apply (fl_bytes W2 m1 mem' a bs); [|exact MUW2|intros x Hx; exact (proj2 (Hr x Hx))].
      apply (fl_bytes W1 mem m1 a bs Hb MU1). intros x Hx. apply HoW1. exact (proj1 (Hr x Hx)). }
    assert (Hspk : forall off v, 0 <= off -> off + 8 <= 312 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Ho1 Ho2 HS.
      assert (HS1 : spill regs m1 off v).
      { apply (r10b_spill_keep regs regs mem m1 off v A W1 HS Hr9 eq_refl HA0 ltac:(lia) ltac:(lia) MU1).
        intros x Hx. apply HoW1, Happhi. lia. }
      apply (r10b_spill_keep regs regs'' m1 mem' off v A W2 HS1 Hr9 E9 HA0 ltac:(lia) ltac:(lia) MUW2).
      intros x Hx. apply HoW2; lia. }
    assert (Hrwk : forall a n bs, fr + 2504 <= a -> a + Z.of_nat n <= fr + FRAME_BYTES ->
              rw_cells rsegs mem a [CB n bs] -> rw_cells rsegs mem' a [CB n bs]).
    { intros a n bs Ha1 Ha2 HRWa.
      apply (r10b_rwcb_keep W2 m1 mem' a n bs MUW2 WM2); [intros x Hx; apply HoW2; lia|].
      apply (r10b_rwcb_keep W1 mem m1 a n bs MU1 WM1); [intros x Hx; apply HoW1, Hframeapp; lia | exact HRWa]. }
    assert (Hadk : forall p n, addressable mem p n ->
              (forall i, 0 <= i < n -> outside W1 (shadow_addr (p + i))) -> addressable mem' p n).
    { intros p n Hp Hsh1.
      apply (sl_addr_keep m1 mem' W2 p n); [| exact MUW2 | exact HAW2].
      exact (r10b_addr_keep W1 mem m1 p n Hp MU1 Hsh1). }
    assert (HOUR' : OURb g fr mem').
    { unfold OURb in *. apply Hkeep; [exact HOUR|].
      rewrite OUR_length. intros x Hx. split; [apply Hframeapp; lia | apply HoW2; lia]. }
    assert (HIDB' : IDBr g fr (RID (g_in g) b) mem').
    { unfold IDBr in *. apply Hkeep; [exact HIDB|].
      rewrite HLid. intros x Hx. split; [apply Hframeapp; lia | apply HoW2; lia]. }
    assert (HF' : bytes_at rsegs mem' phi (rt_F (g_in g) (Z.of_nat b))).
    { apply Hkeep; [exact HF|]. rewrite HLF. intros x Hx. rewrite Z2Nat.id in Hx by lia.
      split; [exact (proj1 (Hphib x Hx)) | apply HoW2; destruct Hblkfr; lia]. }
    assert (HAphi' : addressable mem' phi (rnb g b)) by (apply (Hadk phi (rnb g b) HAphi); exact HshPhi).
    assert (HOUTA' : OUTA fr mem').
    { unfold OUTA in *. apply (Hadk (fr + 544) 1492 HOUTA). intros i Hi.
      apply (r10b_shobj_out fr 306 313 (fr + 544) 1492 i Hframe8 ltac:(lia) ltac:(lia)); [left; lia | exact Hi]. }
    assert (HAid' : addressable mem' (fr + 2176) 38).
    { apply (Hadk (fr + 2176) 38 HAid). intros i Hi.
      apply (r10b_shobj_out fr 306 313 (fr + 2176) 38 i Hframe8 ltac:(lia) ltac:(lia)); [left; lia | exact Hi]. }
    assert (HAour' : addressable mem' (fr + 2624) 6).
    { apply (Hadk (fr + 2624) 6 HAour). intros i Hi.
      apply (r10b_shobj_out fr 306 313 (fr + 2624) 6 i Hframe8 ltac:(lia) ltac:(lia)); [right; lia | exact Hi]. }
    assert (HAfg' : addressable mem' (fr + 2256) 72).
    { apply (Hadk (fr + 2256) 72 HAfg). intros i Hi.
      apply (r10b_shobj_out fr 306 313 (fr + 2256) 72 i Hframe8 ltac:(lia) ltac:(lia)); [left; lia | exact Hi]. }
    assert (HIN' : bytes_at rsegs mem' (g_p g) (g_in g)).
    { apply Hkeep; [exact HIN|]. intros x Hx. rewrite <- g_n_len in Hx.
      destruct (HINblk ltac:(lia)) as (Happq & Hqlo & Hqfr).
      split; [exact (Happq x Hx) | apply HoW2; destruct Hqfr; lia]. }
    assert (HINL' : 0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem' (g_p g) (g_n g)).
    { intros Hn0. destruct (HINL Hn0) as (Hin & HAq). split; [exact Hin|].
      pose proof HAq as (Hq0 & _).
      destruct (HINblk Hn0) as (_ & _ & Hqfr).
      apply (Hadk (g_p g) (g_n g) HAq). intros i Hi.
      apply (r10b_shobj_out fr 306 313 (g_p g) (g_n g) i Hframe8 ltac:(lia) Hq0);
        [destruct Hqfr; [right | left]; lia | exact Hi]. }
    assert (ER : forall r v, getr R r = getr regs r -> rg regs r v -> rg regs'' r v).
    { intros r v Kr Hv. unfold rg in Hv |- *. rewrite (Hreg r), Kr. exact Hv. }
    rewrite <- SEGS.
    apply (HK regs'' mem' md' fr phi HFRA' HENT').
    unfold r10b_out.
    split.
    { unfold r10b_body.
      split; [exact Hgn|]. split; [exact Hb6|].
      split; [split; [exact Hphinz | rewrite Hsz; exact HAphi']|].
      split; [exact (ER _ _ K23 H23)|]. split; [exact HOUR'|]. split; [exact HOUTA'|].
      split; [destruct HCUR as (Hc0 & Hc22 & Hc25); split; [exact Hc0|];
              split; [exact (ER _ _ K22 Hc22) | exact (ER _ _ K25 Hc25)]|].
      split; [exact (Hspk 112 _ ltac:(lia) ltac:(lia) Hsp112)|].
      split; [exact (Hspk 128 _ ltac:(lia) ltac:(lia) Hsp128)|].
      split; [split; [exact (Hspk 40 _ ltac:(lia) ltac:(lia) Hsp40)|];
              split; [exact (Hspk 120 _ ltac:(lia) ltac:(lia) Hsp120)|];
              split; [exact (Hspk 136 _ ltac:(lia) ltac:(lia) Hsp136)|];
              split; [exact (Hspk 160 _ ltac:(lia) ltac:(lia) Hsp160)|];
              split; [exact (Hspk 168 _ ltac:(lia) ltac:(lia) Hsp168)|];
              split; [exact (Hspk 176 _ ltac:(lia) ltac:(lia) Hsp176)|];
              split; [exact (Hspk 208 _ ltac:(lia) ltac:(lia) Hsp200)|];
              split; [exact (Hspk 248 _ ltac:(lia) ltac:(lia) Hsp248)|];
              split; [exact HAour'|]; split; [exact HIN'|]; split; [exact HINL'|];
              split; [exact (Hspk 184 _ ltac:(lia) ltac:(lia) Hsp184)|];
              split; [exact (Hspk 256 _ ltac:(lia) ltac:(lia) Hsp256)|];
              split; [exact (Hspk 264 _ ltac:(lia) ltac:(lia) Hsp264)|];
              split; [exact (Hspk 272 _ ltac:(lia) ltac:(lia) Hsp272)|];
              exact (Hspk 32 _ ltac:(lia) ltac:(lia) Hsp32)|].
      split; [exact (Hspk 104 _ ltac:(lia) ltac:(lia) Hsp104)|].
      split; [exact (Hspk 96 _ ltac:(lia) ltac:(lia) Hsp96)|].
      split; [exact (Hspk 64 _ ltac:(lia) ltac:(lia) Hsp64)|].
      split; [exact (Hspk 144 _ ltac:(lia) ltac:(lia) Hsp144)|].
      split; [exact (Hspk 192 _ ltac:(lia) ltac:(lia) Hsp208)|].
      split; [destruct HRWid as (idb & HRWi); exists idb; exact (Hrwk (fr + 2688) 38%nat idb ltac:(lia) ltac:(lia) HRWi)|].
      split; [destruct HRWjk as (junk & HRWj); exists junk; exact (Hrwk (fr + 2768) 72%nat junk ltac:(lia) ltac:(lia) HRWj)|].
      split; [exact (Hspk 280 _ ltac:(lia) ltac:(lia) Hsp280)|].
      split; [exact (Hspk 240 _ ltac:(lia) ltac:(lia) Hsp240)|].
      split; [destruct HRWjy as (jy & HRWy); exists jy; exact (Hrwk (fr + 3040) 1%nat jy ltac:(lia) ltac:(lia) HRWy)|].
      split; [destruct HRWj32 as (junk & HRWz); exists junk; exact (Hrwk (fr + 3056) 32%nat junk ltac:(lia) ltac:(lia) HRWz)|].
      split; [exact (Hspk 152 _ ltac:(lia) ltac:(lia) Hsp152)|].
      split; [exact (ER _ _ K21 H21)|].
      exact HAid'. }
    split.
    { split; [exact (Hspk 48 _ ltac:(lia) ltac:(lia) Hsp48)|].
      split; [exact (Hspk 56 _ ltac:(lia) ltac:(lia) Hsp56)|].
      split; [exact (Hspk 88 _ ltac:(lia) ltac:(lia) Hsp88)|].
      split; [exact (Hspk 80 _ ltac:(lia) ltac:(lia) Hsp80)|].
      split; [exact (Hspk 72 _ ltac:(lia) ltac:(lia) Hsp72)|].
      split; [exact (Hspk 8 _ ltac:(lia) ltac:(lia) Hsp16)|].
      split; [exact (Hspk 0 _ ltac:(lia) ltac:(lia) Hsp8)|].
      split; [exact (Hspk 200 _ ltac:(lia) ltac:(lia) Hsp192)|].
      split; [exact (Hspk 216 _ ltac:(lia) ltac:(lia) Hsp216) | exact HAfg']. }
    split; [exact Hnz|].
    split; [exact (ER _ _ K24 H24)|].
    split; [exact HF'|].
    split; [exact HIDB'|].
    split; [unfold a0v, rg; exact (eq_trans (Hreg _) K10) | exact FM2].
Qed.

(* ---- the two arm lemmas ---- *)

Lemma r10b_b6 : Hat B APIf ra (Inv_A81708_at (fx := fx) B APIf ra) 6%nat ->
  Hat B APIf ra (Inv_A81680_at (fx := fx) B APIf ra) 6%nat.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros Hexit g c Hc.
  eapply (r10b_run 6%nat 0x81708); [left; split; reflexivity | exact Hc |].
  intros regs mem md fr phi HFRA HENT Hout.
  destruct Hout as (Hbody & HRXS & Hnz & H24 & HF & HIDB & Ha0 & FM).
  assert (Hc6 : fcls (rnb g 6) (RFG (g_in g) 6) (rt_g (g_in g) (Z.of_nat 6)) = FgClose)
    by exact (a_rtm_close (g_in g) Hnz).
  assert (Hc6' : fcls (rt_n (g_in g) (Z.of_nat 6)) (RFG (g_in g) 6) (rt_g (g_in g) (Z.of_nat 6)) = FgClose)
    by exact (a_rtm_close (g_in g) Hnz).
  rewrite Hc6 in Ha0, FM. cbn [fg_ret] in Ha0. cbn [FGC.fg_mem] in FM.
  destruct FM as (FG7 & Cpa & Cpp & Cpn).
  assert (E7 : RFG (g_in g) 7 = fg_clear (fg_join (RFG (g_in g) 6) (rt_g (g_in g) (Z.of_nat 6)))).
  { rewrite (proj2 (a_RS_56 (g_in g) 6 (or_intror eq_refl) Hnz)). unfold fg_st, fg_next. rewrite Hc6'.
    reflexivity. }
  pose proof Hbody as (Hgn & Hb6 & HHB & H23 & HOUR & HOUTA & HCUR & _).
  apply Hexit. exists phi, regs, mem, md, fr.
  split; [reflexivity|]. split; [exact HFRA|]. split; [exact HENT|].
  split; [exact Hbody|].
  split; [reflexivity|].
  split; [exact Ha0|].
  split.
  { split; [split; [exact Hb6|]; split; [exact HCUR|]; split; [exact HOUR|]; split; [exact H23|];
            split; [exact HIDB | unfold FGBr; rewrite E7; exact FG7]|].
    split; [exact Hnz|]. split; [exact H24 | exact HF]. }
  split; [exact HRXS|].
  split; [exact Cpa|]. split; [exact Cpp | exact Cpn].
Qed.

Lemma r10b_b5 : Hat B APIf ra (Inv_A817c8_at (fx := fx) B APIf ra) 5%nat ->
  Hat B APIf ra (Inv_A81680_at (fx := fx) B APIf ra) 5%nat.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros Hexit g c Hc.
  eapply (r10b_run 5%nat 0x817c8); [right; split; reflexivity | exact Hc |].
  intros regs mem md fr phi HFRA HENT Hout.
  destruct Hout as (Hbody & HRXS & Hnz & H24 & HF & HIDB & Ha0 & FM).
  assert (Hc5 : fcls (rnb g 5) (RFG (g_in g) 5) (rt_g (g_in g) (Z.of_nat 5)) = FgFirst)
    by exact (a_rtm_first (g_in g) Hnz).
  assert (Hc5' : fcls (rt_n (g_in g) (Z.of_nat 5)) (RFG (g_in g) 5) (rt_g (g_in g) (Z.of_nat 5)) = FgFirst)
    by exact (a_rtm_first (g_in g) Hnz).
  rewrite Hc5 in Ha0, FM. cbn [fg_ret] in Ha0. cbn [FGC.fg_mem] in FM.
  assert (E6 : RFG (g_in g) 6 = fg_first (RFG (g_in g) 5) (rt_g (g_in g) (Z.of_nat 5))).
  { rewrite (proj2 (a_RS_56 (g_in g) 5 (or_introl eq_refl) Hnz)). unfold fg_st, fg_next. rewrite Hc5'.
    reflexivity. }
  assert (I6 : RID (g_in g) 6 = RID (g_in g) 5).
  { rewrite (proj1 (a_RS_56 (g_in g) 5 (or_introl eq_refl) Hnz)). unfold fg_id, fg_rf. rewrite Hc5'.
    reflexivity. }
  destruct Hbody as (Hgn & Hb6 & HHB & H23 & HOUR & HOUTA & HCUR & Hsp112 & Hsp128 & HPRO & Hsp104 &
    Hsp96 & Hsp64 & Hsp144 & Hsp208 & HRWid & HRWjk & Hsp280 & Hsp240 & HRWjy & HRWj32 & Hsp152 & H21 & HAid).
  apply Hexit. exists phi, regs, mem, md, fr.
  split; [reflexivity|]. split; [exact HFRA|]. split; [exact HENT|].
  split; [split; [exact Hgn|]; split; [exact Hb6|]; split; [exact HHB|]; split; [exact H23|];
          split; [exact HOUR|]; split; [exact HOUTA | exact HCUR]|].
  split.
  { split; [exact Hb6|]. split; [exact HCUR|]. split; [exact HOUR|]. split; [exact H23|].
    split; [unfold IDBr; rewrite I6; exact HIDB | unfold FGBr; rewrite E6; exact FM]. }
  split; [exact H24|]. split; [exact Ha0|].
  split; [exact Hsp128|]. split; [exact HPRO|]. split; [exact Hsp104|]. split; [exact Hsp96|].
  split; [exact Hsp64|]. split; [exact H21|]. split; [exact Hsp112|]. split; [exact Hsp144|].
  split; [exact Hsp208|]. split; [exact HRWid|]. split; [exact HRWjk|]. split; [exact Hsp280|].
  split; [exact Hsp240|]. split; [exact HRWjy|]. split; [exact HRWj32|]. split; [exact Hsp152|].
  split; [exact HAid | exact HRXS].
Qed.

End R10B.
