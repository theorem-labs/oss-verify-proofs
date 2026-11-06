(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 1068 of its 1186 lines of code are new or changed and 1084 lines of the source are left out. *)
(* Segment F23 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, patched image A), 0x825a0-0x825c8: the head of the
   inlined check_ports, from the return point of reac_ctrl_headamp_record_verify to the return point of the
   memory-checking runtime's copy.
     0x825a0  bne  a0,s4,82bf4   -- the branch to the error path is not taken: the call's result a0 and s4 are
                                    both t_want_v.
     0x825a4  sb   zero,16(s3)   -- s3 = S(fr): the shadow byte at S(fr) + 16 becomes 0x00.
     0x825a8  li   a0,4
     0x825ac  sb   a0,17(s3)     -- the shadow byte at S(fr) + 17 becomes 0x04; the 12 bytes at fr + 128 are now
                                    marked usable (addressable m (fr + 128) 12).
     0x825b0  auipc a0,0xfff9f
     0x825b4  addi a1,a0,-1072    -- a1 = 0x21180, the image constant of three 32-bit words -7.
     0x825b8  li   a2,12
     0x825bc  ld   s4,136(s1)    -- s4 = [A+136] = fr + 128 (the ports words of the frame).
     0x825c0  mv   a0,s4
     0x825c4  jal  52028         -- checked_memcpy(fr + 128, 0x21180, 12), composed on its contract
                                    (lib/A/Prog/asan_memcpy_c.v, a Section Hypothesis).
   The exit cut is SlotInv.Inv_A825c8_at (s4 = fr + 128, the three words -7 at fr + 128 and the 12 bytes
   addressable), the entry cut SlotInv.Inv_A825a0_at. The frame's bytes being present (B7X', the copy's destination
   cells) is FLSI's stk fr (fr + FRAME_BYTES); the frame's place and writability come from SlotInv.fra_frame, the copy's
   stack window from SlotInv.fra_win, and the mem_inv the copy's contract asks for from MemNorm.normalize (the frame
   carries ro_agree only). FLSI and B7K move by B7Cuts.b7_flsi_keep / b7_B7K_keep.

   The write set of the segment is W = [(sp - 2224, sp); (fr + 128, fr + 140); (S(fr) + 16, S(fr) + 18)]: the copy's
   stack bytes, the ports words and the two shadow bytes. FRA moves across it by f23_fra (sl_fr_meta with the copy's
   own 2224 stack bytes below sp allowed in W; the entry-anchored window [S - SLOT_STACK, S) is re-established
   pointwise after the run).

   The plain twin is a Theorem Labs lane's lib/Prog/Seg/Q01.v (q01_m7, branch #74). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib asan_memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs B7Cuts.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---- The image constant at 0x21180 (__const.check_ports.ports): three 32-bit words -7. ---- *)

Definition PORTSC : Z := 0x21180.
Definition m7w : list byte := le4 (Z_to_bv 64 (-7)).
Definition ports_c_bytes : list byte := m7w ++ m7w ++ m7w.

Lemma f23_ports_len : length ports_c_bytes = 12%nat.
Proof. reflexivity. Qed.

(* The 12 bytes are read-only bytes of the image, so every memory whose overlay holds no read-only byte has them. *)
Lemma f23_src_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m PORTSC ports_c_bytes.
Proof.
  intros m HI.
  assert (HR : ro_bytes_b rsegs PORTSC ports_c_bytes = true) by (vm_compute; reflexivity).
  assert (H1 : 0 <= PORTSC) by (unfold PORTSC; lia).
  assert (H2 : PORTSC + Z.of_nat (length ports_c_bytes) <= 2 ^ 64)
    by (rewrite f23_ports_len; unfold PORTSC; lia).
  destruct (ro_cells_image rsegs m PORTSC ports_c_bytes HI HR H1 H2) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.

(* ---- Small arithmetic and memory helpers. ---- *)

Lemma f23_In_of_existsb : forall (l : list (Z * Z)) (p : Z * Z),
  existsb (fun q => (fst q =? fst p) && (snd q =? snd p)) l = true -> In p l.
Proof.
  intros l p H. apply existsb_exists in H. destruct H as (q & Hin & Hq).
  apply andb_true_iff in Hq. destruct Hq as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  destruct p as [p1 p2]; destruct q as [q1 q2]; cbn in H1, H2; subst. exact Hin.
Qed.

Lemma f23_In_AG : In (PORTSC, 12) AF.frame_AG.
Proof. apply f23_In_of_existsb. vm_compute. reflexivity. Qed.

(* The registered globals' addressability (the slot pre's frame_AG fact) covers the 12 constant bytes. *)
Lemma f23_img_addr : forall m, (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  addressable m PORTSC 12.
Proof.
  intros m H. split; [unfold PORTSC; lia|]. split; [lia|].
  split; [unfold PORTSC, APPMEM_END; lia|].
  intros i Hi.
  assert (Hin : in_globals AF.frame_AG (PORTSC + i)).
  { exists PORTSC, 12. split; [exact f23_In_AG | lia]. }
  destruct (H _ Hin) as (_ & _ & _ & HH).
  destruct (HH 0 ltac:(lia)) as (Happ & b & Hb & Hok).
  rewrite Z.add_0_r in Happ, Hb, Hok. split; [exact Happ|]. exists b. split; [exact Hb | exact Hok].
Qed.

(* Every registered global lies in the image, below 0x5fe000 = AC.GT (so below every frame base). *)
Lemma f23_AG_low : forall lo len, In (lo, len) AF.frame_AG -> lo + len <= 6283264.
Proof.
  intros lo len Hin.
  assert (H : forallb (fun p => fst p + snd p <=? 6283264) AF.frame_AG = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H _ Hin). cbn [fst snd] in H. apply Z.leb_le in H. exact H.
Qed.

Lemma f23_bv_eq_Z : forall x y, Z_to_bv 64 x = Z_to_bv 64 y -> x mod 2 ^ 64 = y mod 2 ^ 64.
Proof.
  intros x y E. apply (f_equal (@bv_unsigned 64)) in E. rewrite !MState.unsigned_lit_wrap in E. exact E.
Qed.

(* Two word values at one address agree mod 2^64 (as A/Prog/Seg P2's p2_wm_congr). *)
Lemma f23_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !KindBGlue.kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.ltb_spec j 64) as [Hlt|Hge].
  - set (k := Z.to_nat (j / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (j - 8 * Z.of_nat k) = j) by lia.
    assert (Hjk : j - 8 * Z.of_nat k = j mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod j 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= j - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (j - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (j - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt j 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge j 64)) by lia. reflexivity.
Qed.

(* A byte-backed, writable range is a `stk` range. *)
Lemma f23_stk_of : forall (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at rsegs m a /\ exists b, mbyte rsegs m a = Some b) ->
  stk rsegs m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (HW & b & HB). split; [exact HW|]. exists b. exact HB.
Qed.

(* A shadow range is a `stk` range (shadow_rw gives both halves). *)
Lemma f23_stk_shadow : forall (m : word -> option byte) a n,
  shadow_rw m -> 0 <= a -> a + n <= 2 ^ 64 -> (forall x, a <= x < a + n -> in_shadow x) ->
  stk rsegs m a (a + n).
Proof.
  intros m a n HSW H0 H1 HI. split; [lia|]. split; [lia|]. intros x Hx. exact (HSW x (HI x Hx)).
Qed.

(* One writable byte gives store_ok for a 1-byte store, in any later memory. *)
Lemma f23_store_ok1 : forall (m m' : word -> option byte) a,
  wview rsegs m (wa a) <> None -> wmono rsegs m m' -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  store_ok rsegs m' (wa a) 1 = true.
Proof.
  intros m m' a HW WM H0 H1.
  assert (WR : wr_at rsegs m' a 1).
  { split; [lia|]. split; [lia|]. intros i Hi.
    assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r. exact (WM (wa a) HW). }
  pose proof (wr_at_store_ok rsegs m' a 1 0 1%nat WR ltac:(lia) ltac:(cbn; lia)) as H.
  rewrite Z.add_0_r in H. exact H.
Qed.

(* A write keeps the shadow map readable and writable. *)
Lemma f23_shadow_rw_write : forall (m : word -> option byte) a bs,
  shadow_rw m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  shadow_rw (write_to_mem m (wa a) bs).
Proof.
  intros m a bs HSW Ha Hl x Hx. destruct (HSW x Hx) as (HV & b & Hb).
  pose proof (in_shadow_range x Hx) as Hr.
  split; [apply wview_write_mono; exact HV|].
  unfold mrd in *. rewrite (write_to_mem_spec bs m a (wa x)) by lia.
  rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a x) as [Hle|Hle]; destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))) as [Hlt|Hlt];
    cbn [andb]; try (exists b; exact Hb).
  destruct (nth_error bs (Z.to_nat (x - a))) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* ---- The copy runs on the normalized memory (MemNorm.evt_normalize, as a Theorem Labs lane's a1_req_evt in Seg/A1.v):
   its contract asks for mem_inv, which the frame does not carry; normalize gives it, and every other premise and
   conclusion crosses mem_rel. The helpers below are A1.v's, for the addresses above the image. ---- *)

Lemma f23_rsegs_below_gt : seg_tops_below rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

(* Above the image there is no read-only byte, so normalizing changes nothing there. *)
Lemma f23_ro_addr_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (find_segment_below sg 0x5fe000 x n s f23_rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma f23_wview_rel_hi : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (f23_ro_addr_hi a Ha)). split; auto.
Qed.

Lemma f23_stk_rel_hi : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (f23_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f23_stk_rel_hi_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (f23_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f23_shadow_rw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj2 (f23_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f23_shadow_rw_rel_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - apply (proj1 (f23_wview_rel_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f23_addressable_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma f23_ba_rel1 : forall m m0 a bs, mem_rel rsegs m m0 -> bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs.
Proof. intros m m0 a bs R H. exact (proj1 (bytes_at_rel rsegs m m0 a bs R) H). Qed.

Lemma f23_asan_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs => exact (f23_ba_rel1 m m0 a bs R ltac:(assumption)) end.
Qed.

(* The copy's destination cells above the image cross mem_rel (their bytes, and their writability, since no
   read-only byte is there). *)
Lemma f23_rw_cells_rel : forall m m0 a cs, mem_rel rsegs m m0 -> 0x5fe000 <= a ->
  rw_cells rsegs m a cs -> rw_cells rsegs m0 a cs.
Proof.
  intros m m0 a cs HR Ha ((Hwf & HB) & HW). split; [split; [exact Hwf|]|].
  - exact (proj1 (bytes_at_rel rsegs m m0 a _ HR) HB).
  - apply (wr_at_norm rsegs m m0 a _ HR HW). intros i Hi.
    destruct HW as (H0 & H1 & _). apply f23_ro_addr_hi. lia.
Qed.

(* A 1-byte store above the image keeps ro_agree. *)
Lemma f23_ro_agree_write1 : forall m a b, ro_agree rsegs m -> 0x5fe000 <= a < 2 ^ 64 ->
  ro_agree rsegs (write_to_mem m (wa a) [b]).
Proof.
  intros m a b H Ha. apply (ro_agree_same rsegs m _ H).
  intros x Hx. apply (write_ro_same rsegs [b] m (wa a) x); [|exact Hx].
  cbn [length all_rw]. split; [exact (f23_ro_addr_hi a Ha) | exact I].
Qed.

(* addressable survives a run whose write set misses the shadow bytes of the buffer. *)
Lemma f23_addr_keep : forall m m' W p n,
  addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' W p n (H0 & H1 & H2 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok).
  pose proof (in_shadow_range _ (shadow_of_app _ Happ)) as Hr.
  assert (E : m' (wa (shadow_addr (p + i))) = m (wa (shadow_addr (p + i)))).
  { apply MU. rewrite wa_unsigned by lia. exact (HO i Hi). }
  split; [exact Happ|]. exists b. split; [|exact Hok]. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* The two shadow bytes 0x00 and 0x04 at S(fr) + 16 mark the 12 bytes at fr + 128 usable. *)
Lemma f23_addr12 : forall (m : word -> option byte) fr,
  fr mod 8 = 0 -> 0 <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  mrd rsegs m (wa (Sfr fr + 16)) = Some (Z_to_bv 8 0) ->
  mrd rsegs m (wa (Sfr fr + 17)) = Some (Z_to_bv 8 4) ->
  addressable m (fr + 128) 12.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros m fr H8 H0 Hend Happ H16 H17.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|].
  destruct (Z_lt_ge_dec i 8) as [Hlt|Hge].
  - assert (E : (fr + 128 + i) / 8 = fr / 8 + 16) by (Z.div_mod_to_equations; lia).
    exists (Z_to_bv 8 0). split.
    + replace (shadow_addr (fr + 128 + i)) with (Sfr fr + 16);
        [exact H16 | unfold Sfr, shadow_addr; rewrite E; lia].
    + left. vm_compute. reflexivity.
  - assert (E : (fr + 128 + i) / 8 = fr / 8 + 17) by (Z.div_mod_to_equations; lia).
    assert (Em : (fr + 128 + i) mod 8 = i - 8) by (Z.div_mod_to_equations; lia).
    exists (Z_to_bv 8 4). split.
    + replace (shadow_addr (fr + 128 + i)) with (Sfr fr + 17);
        [exact H17 | unfold Sfr, shadow_addr; rewrite E; lia].
    + right. unfold shadow_ok. rewrite Em.
      assert (Es : bv_signed (Z_to_bv 8 4) = 4) by (vm_compute; reflexivity).
      rewrite Es. lia.
Qed.

(* The FRAME_SHADOW (392) shadow bytes of the frame are shadow bytes. *)
Lemma f23_fr_shadow : forall fr i, 0 <= i < FRAME_SHADOW ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> in_shadow (Sfr fr + i).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr i Hi Happ.
  assert (E : shadow_addr (fr + i * 8) = Sfr fr + i).
  { unfold Sfr, shadow_addr. rewrite Z.div_add by lia. lia. }
  rewrite <- E. apply shadow_of_app. apply Happ. lia.
Qed.

(* mkR_of made concrete, so that `step` reads a register slot. *)
Lemma f23_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma f23_bne_same : forall (x : word), negb (bv_eqb x x) = false.
Proof. intros x. rewrite bv_eqb_refl. reflexivity. Qed.

Section R.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

(* The asan run lemma on the Lib engine (Tac_slot.sl_run without the UL bridge; a Theorem Labs lane's sl_run_lib). *)
Lemma f23_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply KindBGlue.kb_getr_eqv; exact HR | exact Hmat].
Qed.

End R.

(* ---- The entry cut. ---- *)

(* B7X': the frame's bytes are present (the copy's destination cells). It is NOT a cut conjunct: B7Cuts.b7_frame_stk
   derives it from the FRA the cut already carries (real arm: the frame is the top of the slot window; side arm:
   a_in_fs plus the allocator laws give AC.a_fs_ok). The entry cut of F23 is therefore B7Cuts.Inv_A825a0_loc
   itself, which is what seg_F22 proves at its exit. *)
Definition B7X' (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  forall a, fr <= a < fr + FRAME_BYTES -> exists b, mbyte rsegs m a = Some b.

Section S.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The memory-checking runtime's copy (checked_memcpy at 0x52028), a Section Hypothesis. *)
Hypothesis MCPY : asan_memcpy_contract.

(* The facts of the allocator laws and of the runtime's side-stack record the segment reads, each taken apart once
   here (a Theorem Labs lane 15:32Z: an inner list of a law is destructed in one lemma per law per file). *)
Lemma f23_blk : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md p n HAH Hin)
    as (H16 & H4096 & Hst & _ & Hby).
  split; [exact H16|]. split; [exact H4096|]. split; [exact Hst|].
  intros a Ha. destruct (Hby a Ha) as (Happ & _ & _ & _ & Hnfs). split; [exact Happ | exact Hnfs].
Qed.

Lemma f23_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hs Hw.
  destruct (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hs Hw)
    as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Lemma f23_fs_place : forall H mem md b,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Hw Hb.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md b HAH Hw Hb)
    as (H1 & H2 & _ & H4).
  split; [exact H1|]. split; [exact H2 | exact H4].
Qed.

Lemma f23_fs_state : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> AC.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw HFS.
  destruct (AC.a_laws_fs_state _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw HFS)
    as (Hok & _).
  exact Hok.
Qed.

Lemma f23_fs_store : forall H mem mem' md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) FS ->
  0 <= FS < 2 ^ 64 ->
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
  intros H mem mem' md FS HAH Hw HFS Hs Hwm Hok.
  destruct (AC.a_laws_fs_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md FS HAH Hw HFS
              Hs Hwm Hok) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

(* The runtime's side-stack word at the thread pointer and its value facts (AsanRT.asan_fs_cells, fs_value_ok). *)
Lemma f23_rt_fs : forall sp m md, AsanRTInv.RT sp m md ->
  exists FS : word, bytes_at rsegs m AsanRT.RT_TP (le8 FS) /\ 0 < bv_unsigned FS /\ bv_unsigned FS mod 4096 = 0 /\
    AsanRT.RT_GT <= bv_unsigned FS /\
    (forall a, bv_unsigned FS <= a < bv_unsigned FS + AsanRT.RT_FS_SIZE -> app_mem a).
Proof.
  intros sp m md HRT.
  pose proof (AsanRTInv.RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FS & HB & (H0 & H1 & H2 & H3)) & _).
  exists FS. split; [exact HB|]. split; [exact H0|]. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* FRA across the segment's run: Tac_slot.sl_fr_meta with the copy's own stack bytes [sp - 2224, sp) allowed in the
   write set (the copy writes them and hands them back; the entry-anchored window [S - SLOT_STACK, S), its
   addressability outside the frame, the registered globals' addressability and the side arm's frame record FSREC
   after the run are the caller's premises). *)
Lemma f23_fra : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (forall x, 0 <= x < 6283264 -> outside W x) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> forall x, A + 304 <= x < A + 312 -> outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> forall x, A + 16 <= x < A + 32 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (FSREC fr mem -> FSREC fr mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew Hwin' HAG' HWA'
    HWlo HWhdr HWspill HWsel HWsaved Hrec' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x Hx0 Hx1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
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
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
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
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill A Hr9 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split; [|exact (Hrec' Hrec)].
        intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr; lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr; lia. }
  split; [exact Hshnew|].
  split; [exact Hwin'|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* The ten instructions 0x825a0-0x825c4 on explicit registers, the copy composed on its contract. *)
Lemma f23_evt : forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte) (spv A fr Sf : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 Sf -> a0 = s4 -> Sf = Sfr fr ->
    0 <= fr -> fr mod 8 = 0 -> AC.GT <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spv - 2224 \/ spv <= fr) ->
    fr + FRAME_BYTES <= A -> spv <= A -> A + 312 <= 2 ^ 64 ->
    HIGHMEM_BEG + FN_STACK <= spv -> spv <= APPMEM_END ->
    0 <= Sf -> Sf + FRAME_SHADOW <= HIGHMEM_BEG -> (fr + FRAME_BYTES <= Sf \/ Sf + FRAME_SHADOW <= fr) ->
    q64 m (A + 136) (fr + 128) ->
    rw_cells rsegs m (fr + 128) [CB 12 junk] ->
    addressable m PORTSC 12 ->
    asan_cells m -> shadow_rw m -> ro_agree rsegs m -> stk rsegs m (spv - FN_STACK) spv ->
    LE.evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R Fr (Z_to_bv 64 0x825c8) fcs None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\
         getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         getr R 20 = Z_to_bv 64 (fr + 128) /\
         munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\
         stk rsegs m' (spv - FN_STACK) spv /\
         bytes_at rsegs m' (fr + 128) ports_c_bytes /\ addressable m' (fr + 128) 12)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825a0) fcs None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fcs m spv A fr Sf junk Esp Es1 Es3 Ea0 ESf Hfr0 Hfr8 HGT Hfrend Happ Hfrw HfrA HspA HAhi Hsplo Hspend
    HSf0 HSfhi HSfap Hq136 RWq HADimg HAC HSW HRO HST.
  subst sp s1 s3 a0.
  unfold AC.GT in HGT.
  assert (KAPP : APPMEM_END = 0x800000000000) by reflexivity.
  assert (KHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KLM : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (KSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (KFN : FN_STACK = 1044480) by reflexivity.
  assert (KMC : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (Hspb : 0 <= spv < 2 ^ 64) by (unfold HIGHMEM_BEG, AF.SLOT_STACK, APPMEM_END in *; lia).
  assert (HAb : 0 <= A < 2 ^ 64) by (unfold HIGHMEM_BEG, AF.SLOT_STACK in *; lia).
  assert (HSfb : 0 <= Sf /\ Sf + 18 <= 2 ^ 64) by (unfold HIGHMEM_BEG in *; lia).
  assert (HSfK : 2147450880 <= Sf).
  { rewrite ESf. unfold Sfr, shadow_addr, ASAN_K.
    assert (0 <= fr / 8) by (apply Z.div_pos; lia). lia. }
  assert (HSH16 : in_shadow (Sf + 16)) by (rewrite ESf; exact (f23_fr_shadow fr 16 ltac:(lia) Happ)).
  assert (HSH17 : in_shadow (Sf + 17)) by (rewrite ESf; exact (f23_fr_shadow fr 17 ltac:(lia) Happ)).
  assert (HS16 : store_ok rsegs m (wa (Sf + 16)) 1 = true)
    by (eapply f23_store_ok1; [exact (proj1 (HSW _ HSH16)) | apply wmono_refl | lia | lia]).
  (* 0x825a0 bne a0,s4: the call's result and s4 are the same word, the branch is not taken *)
  step.
  rewrite f23_bne_same. cbv iota.
  (* 0x825a4 sb zero,16(s3) *)
  step.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HS17 : store_ok rsegs mm (wa (Sf + 17)) 1 = true)
        by (eapply (f23_store_ok1 m); [exact (proj1 (HSW _ HSH17)) | apply wmono_write; apply wmono_refl
                                      | lia | lia])
  end.
  (* 0x825a8 li a0,4 ; 0x825ac sb a0,17(s3) *)
  step. step.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ (write_to_mem (write_to_mem _ _ ?bA) _ ?bB) _) =>
      assert (EA : bA = [Z_to_bv 8 0]) by (vm_compute; reflexivity);
      assert (EB : bB = [Z_to_bv 8 4]) by (vm_compute; reflexivity);
      rewrite EA, EB
  end.
  set (m2 := write_to_mem (write_to_mem m (Z_to_bv 64 (Sf + 16)) [Z_to_bv 8 0])
               (Z_to_bv 64 (Sf + 17)) [Z_to_bv 8 4]).
  (* the two shadow bytes of m2 *)
  assert (HB16 : bytes_at rsegs m2 (Sf + 16) [Z_to_bv 8 0]).
  { unfold m2. apply bytes_at_write_other; [apply bytes_at_write_same; cbn; lia | lia | cbn; lia | cbn; lia]. }
  assert (HB17 : bytes_at rsegs m2 (Sf + 17) [Z_to_bv 8 4]).
  { unfold m2. apply bytes_at_write_same; cbn; lia. }
  assert (HM16 : mrd rsegs m2 (wa (Sf + 16)) = Some (Z_to_bv 8 0)).
  { destruct HB16 as (_ & _ & HH). pose proof (HH 0%nat ltac:(cbn; lia)) as HE.
    cbn [Z.of_nat nth_error] in HE. rewrite Z.add_0_r in HE. exact HE. }
  assert (HM17 : mrd rsegs m2 (wa (Sf + 17)) = Some (Z_to_bv 8 4)).
  { destruct HB17 as (_ & _ & HH). pose proof (HH 0%nat ltac:(cbn; lia)) as HE.
    cbn [Z.of_nat nth_error] in HE. rewrite Z.add_0_r in HE. exact HE. }
  (* the memory facts of m2 *)
  assert (MU2 : munch [(Sf + 16, Sf + 18)] m m2).
  { unfold m2. apply munch_write; [|lia|cbn; lia|cbn; lia].
    apply munch_write; [apply munch_refl | lia | cbn; lia | cbn; lia]. }
  assert (WM2 : wmono rsegs m m2)
    by (unfold m2; apply wmono_write; apply wmono_write; apply wmono_refl).
  assert (RO2 : ro_agree rsegs m2).
  { unfold m2. apply f23_ro_agree_write1; [apply f23_ro_agree_write1; [exact HRO | lia] | lia]. }
  assert (SW2 : shadow_rw m2).
  { unfold m2. apply f23_shadow_rw_write; [apply f23_shadow_rw_write; [exact HSW | lia | cbn; lia] | lia | cbn; lia]. }
  assert (AC2 : asan_cells m2).
  { apply (asan_cells_kept [(Sf + 16, Sf + 18)] m m2 HAC MU2).
    cbn [disjoint_from]. split; [|exact I]. unfold RT_LO, RT_HI. lia. }
  assert (ST2 : stk rsegs m2 (spv - FN_STACK) spv).
  { apply (stk_transport_disjoint rsegs [(Sf + 16, Sf + 18)] m m2 _ _ HST MU2 WM2).
    cbn [disjoint_from]. split; [|exact I]. unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
  assert (AD2 : addressable m2 (fr + 128) 12).
  { apply (f23_addr12 m2 fr Hfr8 Hfr0 Hfrend Happ); rewrite <- ESf; assumption. }
  assert (ADS2 : addressable m2 PORTSC 12).
  { apply (f23_addr_keep m m2 [(Sf + 16, Sf + 18)] PORTSC 12 HADimg MU2).
    intros i Hi. cbn [outside]. split; [|exact I].
    assert (Hd : (PORTSC + i) / 8 <= 16946)
      by (apply Z.div_le_upper_bound; unfold PORTSC; lia).
    assert (Hfd : 785408 <= fr / 8)
      by (replace 785408 with (6283264 / 8) by reflexivity; apply Z.div_le_mono; lia).
    rewrite ESf. unfold Sfr, shadow_addr. lia. }
  assert (RW2 : rw_cells rsegs m2 (fr + 128) [CB 12 junk]).
  { unfold m2.
    apply rw_cells_frame;
      [ apply rw_cells_frame;
          [ exact RWq | lia | cbn; lia | cbn; lia ]
      | lia | cbn; lia | cbn; lia ]. }
  assert (RO136 : ro_cells rsegs m2 (A + 136) [C8 (Z_to_bv 64 (fr + 128))]).
  { apply ro_c8. unfold q64 in Hq136. unfold m2.
    apply bytes_at_write_other;
      [ apply bytes_at_write_other;
          [ exact Hq136 | lia | cbn; lia | rewrite length_le8; cbn; unfold HIGHMEM_BEG in *; lia ]
      | lia | cbn; lia | rewrite length_le8; cbn; unfold HIGHMEM_BEG in *; lia ]. }
  (* 0x825b0 auipc ; 0x825b4 addi a1 ; 0x825b8 li a2,12 ; 0x825bc ld s4,136(s1) ; 0x825c0 mv a0,s4 ; 0x825c4 jal *)
  step. step. step. step.
  step. step.
  (* the copy, on its contract, run on the normalized memory: the contract asks for mem_inv, which the frame does
     not carry; every premise and every conclusion crosses mem_rel (MemNorm) *)
  pose proof (mem_rel_normalize rsegs m2 RO2) as REL2.
  eapply LE.evt_cut.
  { eapply (evt_normalize rsegs _ _ Fr _ fcs None m2 (seg_rom rsegs) wx_apart_asan RO2).
    eapply MCPY with (src := ports_c_bytes) (junk := junk) (lo := spv - FN_STACK).
    - rewrite !MState.unsigned_lit by (unfold PORTSC; lia).
      exact (f23_src_bytes _ (mem_inv_normalize rsegs m2)).
    - rewrite !MState.unsigned_lit by lia. rewrite f23_ports_len. reflexivity.
    - rewrite !MState.unsigned_lit by lia.
      exact (f23_rw_cells_rel m2 _ (fr + 128) _ REL2 ltac:(lia) RW2).
    - rewrite !MState.unsigned_lit by (unfold PORTSC; lia). unfold PORTSC. lia.
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by (unfold PORTSC; lia).
      exact (f23_addressable_rel m2 _ PORTSC 12 REL2 ADS2).
    - rewrite !MState.unsigned_lit by lia. exact (f23_addressable_rel m2 _ (fr + 128) 12 REL2 AD2).
    - rewrite !MState.unsigned_lit by (unfold PORTSC; lia).
      unfold end_in_app, app_mem, PORTSC, LOWMEM_END. right. left. lia.
    - rewrite !MState.unsigned_lit by lia. unfold end_in_app. right. apply Happ. lia.
    - rewrite !MState.unsigned_lit by (unfold PORTSC; lia). right. split.
      + unfold app_mem, PORTSC, LOWMEM_END. left. lia.
      + apply Happ. lia.
    - rewrite !MState.unsigned_lit by lia. unfold RT_LO, RT_HI. lia.
    - rewrite !MState.unsigned_lit by lia. lia.
    - rewrite !MState.unsigned_lit by (unfold PORTSC; lia). unfold PORTSC, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - rewrite !MState.unsigned_lit by lia.
      exact (f23_stk_rel_hi m2 _ (spv - FN_STACK) spv REL2 ltac:(lia) ltac:(lia) ST2).
    - rewrite !MState.unsigned_lit by lia. lia.
    - unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - rewrite !MState.unsigned_lit by lia. lia.
    - exact (f23_asan_cells_rel m2 _ REL2 AC2).
    - exact (f23_shadow_rw_rel m2 _ REL2 SW2).
    - exact (mem_inv_normalize rsegs m2). }
  intros ms' PO. destruct PO as (st0 & PO & REL & SAME).
  unfold asan_memcpy_post in PO.
  destruct PO as (u0 & u1 & u2 & b1' & b2' & b3 & b4 & b5 & b6 & b7 & v3 & v4 & v5 & v6 & m3n &
                  E3 & MU3 & WM3 & MI3 & ST3 & RW3 & HBS3 & AC3 & SW3).
  subst st0.
  destruct REL as (ER & EF & EPC & ESV & ERV & EFC & EROM & R8).
  destruct ms' as [R' F' pc' svc' rv' fc' m3 ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in ER, EF, EPC, ESV, ERV, EFC, EROM, R8, SAME |- *.
  subst R' F' pc' svc' rv' fc' ro'.
  rewrite !MState.unsigned_lit in ST3, RW3, HBS3 by lia.
  assert (MU3nn : munch [(fr + 128, fr + 140); (spv - 2224, spv)] (normalize rsegs m2) m3n).
  { intros x Hx. apply MU3. cbn [outside] in Hx |- *. destruct Hx as (HO1 & HO2 & _).
    rewrite !MState.unsigned_lit by lia.
    split; [intros [Q1 Q2]; apply HO1; lia|]. split; [intros [Q1 Q2]; apply HO2; lia | exact I]. }
  assert (MU3n : munch [(fr + 128, fr + 140); (spv - 2224, spv)] m2 m3)
    by (eapply munch_rel; [exact REL2 | exact R8 | exact SAME | exact MU3nn]).
  assert (WM3r : wmono rsegs m2 m3)
    by (eapply wmono_rel; [exact REL2 | exact R8 | exact SAME | exact WM3]).
  replace (ret_pc (Z_to_bv 64 0x825c8)) with (Z_to_bv 64 0x825c8)
    by (symmetry; apply MState.ret_pc_even; [lia | reflexivity]).
  apply LE.evt_done.
  do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  (* munch, wmono *)
  assert (MUa : munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m m2).
  { eapply munch_weaken; [|exact MU2]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _).
    split; [exact H3 | exact I]. }
  assert (MUb : munch [(spv - 2224, spv); (fr + 128, fr + 140); (Sf + 16, Sf + 18)] m2 m3).
  { eapply munch_weaken; [|exact MU3n]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & H3 & _).
    split; [intros [Q1 Q2]; apply H2; lia|]. split; [intros [Q1 Q2]; apply H1; lia | exact I]. }
  split; [exact (munch_trans _ _ _ _ MUa MUb)|].
  split; [exact (wmono_trans rsegs _ _ _ WM2 WM3r)|].
  split; [exact (ro_agree_same rsegs m2 m3 RO2 SAME)|].
  split; [exact (f23_shadow_rw_rel_back m3 m3n R8 SW3)|].
  split; [exact (f23_stk_rel_hi_back m3 m3n (spv - FN_STACK) spv R8 ltac:(lia) ltac:(lia) ST3)|].
  split.
  { destruct RW3 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    exact (proj2 (bytes_at_rel rsegs m3 m3n (fr + 128) ports_c_bytes R8) HB). }
  { apply (f23_addr_keep m2 m3 _ (fr + 128) 12 AD2 MU3n).
    intros i Hi. cbn [outside].
    assert (Hap : app_mem (fr + 128 + i)) by (apply Happ; lia).
    pose proof (shadow_of_app _ Hap) as Hsh.
    pose proof (Happ (fr + 128) ltac:(lia)) as Hap0.
    pose proof (Happ (fr + 139) ltac:(lia)) as Hap1.
    unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END,
      AF.SLOT_STACK in *.
    split; [lia|]. split; [lia | exact I]. }
Qed.

Lemma seg_F23 : forall j : nat,
  Hat B APIf ra (Inv_A825c8_at B APIf ra) j -> Hat B APIf ra (Inv_A825a0_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  unfold Inv_A825a0_at, B7CUT in HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HK & Ha0 & Hs4).
  subst c. rewrite SEGS.
  pose proof (b7_asize_flen g j phi fr regs mem HK) as Hasz.
  rewrite Hasz in HFRA, HENT.
  (* the frame's bytes are present: FLSI's window fact stk fr (fr + FRAME_BYTES) *)
  pose proof HFLSI as ((_ & _ & Fstk & _ & _) & _ & _ & _ &
                       (Fin1 & (_ & _ & _ & Hadin) & _) & _).
  assert (HXpres : B7X' fr regs mem).
  { intros a Ha. exact (proj2 (proj2 (proj2 Fstk) a Ha)). }
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWAD & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  (* the frame's place against the stack below sp and its writability (fra_frame), the copy's window (fra_win) *)
  destruct (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HXsep & _ & HFRfs & HFRwr).
  destruct (fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (_ & Hwstk).
  rewrite Haspz in HXsep, Hwstk.
  pose proof HK as (HLK & H23 & H22 & Hphi0 & Hphi50 & Hflen & Hblk & Hs280 & H24 & H18 & H152 & Hgph & Hph &
    Hlen & HLT & HSPL).
  destruct HLK as (Hj255 & H21 & HOUR).
  unfold rg in Hr8, Hr9, Hr19, Hr26.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS (hb1 phi (flen g j) ++ g_H g) mem md HAH) as Hstkhigh.
  assert (KAPP : APPMEM_END = 0x800000000000) by reflexivity.
  assert (KHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KLM : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (KSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (KFN : FN_STACK = 1044480) by reflexivity.
  assert (KGT : AC.GT = 0x5fe000) by reflexivity.
  assert (KFS : AC.FS_SIZE = 11571200) by reflexivity.
  pose proof (HXsep 2224 ltac:(lia)) as HXw.
  assert (HXsp : sp <= APPMEM_END) by lia.
  assert (Hsplo : HIGHMEM_BEG + FN_STACK <= sp) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hspb : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; unfold AC.aspZ; apply u64_range).
  pose proof Hhdr1 as Hh1'. unfold q64 in Hh1'. apply bytes_at_bound in Hh1'. rewrite length_le8 in Hh1'.
  pose proof Hspill as Hsp'. unfold q64 in Hsp'. apply bytes_at_bound in Hsp'. rewrite length_le8 in Hsp'.
  assert (HAb : 0 <= A < 2 ^ 64) by lia.
  (* a spill base read off reg 9 is the frame's spill base A (the two agree mod 2^64 and both are in range) *)
  assert (HWA : forall A0 off, getr regs 9 = Z_to_bv 64 A0 -> 0 <= off <= 300 ->
                  0 <= A0 + off -> A0 + off + 8 <= 2 ^ 64 -> A0 = A).
  { intros A0 off HA0 Hoff Hlo Hhi. rewrite Hr9 in HA0. pose proof (f23_bv_eq_Z _ _ HA0) as Hc.
    revert Hc Hoff Hlo Hhi. pose proof HAb as HAb0. pose proof Hsp' as Hsp0.
    Z.div_mod_to_equations. lia. }
  (* the side stack's base, and the frame's place in AppMem *)
  destruct (f23_rt_fs _ _ _ HRT) as (FSw & HFSb0 & HF0 & HFmod & HFGT & HFapp).
  apply KindBGlue.bytes_at_le8_word in HFSb0.
  pose proof (u64_range FSw) as HFSr.
  assert (HFStp : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw)) by exact HFSb0.
  pose proof (HFRfs _ HFStp HFSr) as HFSfr.
  destruct (f23_fs_place (hb1 phi (flen g j) ++ g_H g) mem md (bv_unsigned FSw) HAH HFStp HFSr)
    as (HFSgt & HFSstk & HFSapp2).
  assert (HGT : AC.GT <= fr) by (unfold AC.GT; unfold AsanRT.RT_GT in HFGT; lia).
  assert (HfsRange : forall a, AC.a_in_fs AC.ASYMS mem a -> 0 <= a < 2 ^ 64 + FRAME_BYTES ->
            bv_unsigned FSw <= a < bv_unsigned FSw + AC.FS_SIZE).
  { intros a (b & Hbr & Hwm & Hb1 & Hb2) Hab.
    pose proof (f23_wm_congr mem _ _ _ Hwm HFStp) as Hc.
    pose proof (HFapp (bv_unsigned FSw + RT_FS_SIZE - 1) ltac:(unfold RT_FS_SIZE; lia)) as Htop.
    unfold AC.FS_SIZE in *. unfold RT_FS_SIZE in Htop.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Htop. unfold AsanRT.RT_GT in HFGT.
    assert (Eb : b = bv_unsigned FSw) by (revert Hc Hb1 Hb2 Htop HFGT HFSr Hab; Z.div_mod_to_equations; lia).
    subst b. lia. }
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a).
  { intros a Ha. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - specialize (Hreal a Ha). unfold app_mem, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. right. lia.
    - pose proof (HfsRange a (Hfs a Ha) ltac:(lia)) as Hr. unfold AC.FS_SIZE in Hr.
      apply HFapp. unfold RT_FS_SIZE. lia. }
  pose proof (Happ fr ltac:(lia)) as Happ0.
  pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Happ1.
  assert (Hfrend : fr + FRAME_BYTES <= APPMEM_END)
    by (unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Happ1; lia).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
  assert (HshIS : forall i, 0 <= i < FRAME_SHADOW -> in_shadow (Sfr fr + i))
    by (intros i Hi; exact (f23_fr_shadow fr i Hi Happ)).
  pose proof (HshIS 0 ltac:(lia)) as Hsh0. rewrite Z.add_0_r in Hsh0.
  pose proof (HshIS (FRAME_SHADOW - 1) ltac:(lia)) as Hsh379.
  assert (HSf0 : 0 <= Sfr fr)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh0; lia).
  assert (HSfhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh0, Hsh379; lia).
  assert (HSfap : fr + FRAME_BYTES <= Sfr fr \/ Sfr fr + FRAME_SHADOW <= fr).
  { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh0, Hsh379.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happ0, Happ1. lia. }
  assert (HSh16 : Sfr fr + 16 = shadow_addr (fr + 128)).
  { unfold Sfr, shadow_addr. replace (fr + 128) with (fr + 16 * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (HSh17 : Sfr fr + 17 = shadow_addr (fr + 136)).
  { unfold Sfr, shadow_addr. replace (fr + 136) with (fr + 17 * 8) by lia. rewrite Z.div_add by lia. lia. }
  (* the block's bytes and its place *)
  destruct (f23_blk (hb1 phi (flen g j) ++ g_H g) mem md phi (flen g j) HAH ltac:(cbn; left; reflexivity))
    as (Hm16 & Hp4096 & Hpstk & Hpbytes).
  assert (Hasize : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  assert (Hblkfr : phi + AC.a_size (flen g j) <= fr \/ fr + FRAME_BYTES <= phi).
  { destruct (Z_le_gt_dec (phi + AC.a_size (flen g j)) fr) as [HL|HL]; [left; lia|].
    destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [HR|HR]; [right; lia|].
    exfalso. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - specialize (Hreal fr ltac:(lia)). lia.
    - destruct (Hpbytes (Z.max phi fr) ltac:(lia)) as (_ & Hnfs).
      apply Hnfs. apply Hfs. lia. }
  (* the frame-pointer spill the segment loads *)
  destruct HSPL as (HS136 & HS120 & HS176).
  destruct HS136 as (A' & Hr9' & Hq136). unfold rg in Hr9'.
  pose proof Hq136 as Hq'. unfold q64 in Hq'. apply bytes_at_bound in Hq'. rewrite length_le8 in Hq'.
  assert (EA : A' = A) by (apply (HWA A' 136 Hr9'); lia).
  subst A'.
  (* the copy's destination cells, from the frame's writable and present bytes *)
  assert (HstkF : stk rsegs mem (fr + 128) (fr + 140)).
  { apply f23_stk_of; [lia | unfold APPMEM_END in *; lia |].
    intros a Ha. split; [apply HFRwr; lia | apply HXpres; lia]. }
  destruct (stk_carve rsegs mem (fr + 128) (fr + 140) 12 HstkF ltac:(cbn; lia)) as (_ & junk & RWq).
  replace (fr + 140 - Z.of_nat 12) with (fr + 128) in RWq by (cbn; lia).
  (* the run *)
  apply (f23_run_lib regs (Z_to_bv 64 0x825a0) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x825c8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 20 = Z_to_bv 64 (fr + 128) /\
       munch [(sp - 2224, sp); (fr + 128, fr + 140); (Sfr fr + 16, Sfr fr + 18)] mem mem' /\
       wmono rsegs mem mem' /\ ro_agree rsegs mem' /\ shadow_rw mem' /\
       stk rsegs mem' (sp - FN_STACK) sp /\
       bytes_at rsegs mem' (fr + 128) ports_c_bytes /\ addressable mem' (fr + 128) 12)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f23_mkR_of_expand.
    eapply LE.evt_mono.
    + eapply f23_evt with (spv := sp) (A := A) (fr := fr) (Sf := Sfr fr) (junk := junk).
      * exact Hr2.
      * exact Hr9.
      * exact Hr19.
      * unfold rg in Ha0, Hs4. rewrite Ha0, Hs4. reflexivity.
      * reflexivity.
      * lia.
      * exact Hfr8.
      * exact HGT.
      * exact Hfrend.
      * exact Happ.
      * exact HXw.
      * exact Hfa.
      * exact Hspa.
      * lia.
      * exact Hsplo.
      * exact HXsp.
      * exact HSf0.
      * exact HSfhi.
      * exact HSfap.
      * exact Hq136.
      * exact RWq.
      * exact (f23_img_addr mem HAG).
      * exact HAC.
      * exact HSW.
      * exact Hro.
      * exact Hwstk.
    + intros ms' (R & m' & Hms & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K20 &
        MU & WM & RO' & SW' & ST' & HBS & HAD').
      exists R, (Z_to_bv 64 0x825c8), m'. split; [exact Hms|].
      split; [reflexivity|].
      split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K8|]. split; [exact K9|].
      split; [exact K18|]. split; [exact K19|]. split; [exact K21|]. split; [exact K22|].
      split; [exact K23|]. split; [exact K24|]. split; [exact K25|]. split; [exact K26|].
      split; [exact K20|].
      split; [exact MU|]. split; [exact WM|]. split; [exact RO'|]. split; [exact SW'|].
      split; [exact ST'|]. split; [exact HBS | exact HAD'].
  - intros R pc' mem' regs' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K18 & K19 & K21 & K22 & K23 & K24 & K25 & K26 &
      K20 & MU & WM & RO' & SW' & ST' & HBS & HAD') Hreg Hmat.
    subst pc'.
    set (W := [(sp - 2224, sp); (fr + 128, fr + 140); (Sfr fr + 16, Sfr fr + 18)]) in *.
    assert (E2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact K18).
    assert (E19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact K21).
    assert (E22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact K22).
    assert (E23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (E26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E20 : getr regs' 20 = Z_to_bv 64 (fr + 128)) by (rewrite Hreg; exact K20).
    assert (Easp : AC.aspZ regs' = sp) by (unfold AC.aspZ; rewrite E2; exact Haspz).
    (* the write set: below the runtime's cells, and the bytes it writes are bytes the program may store into *)
    assert (HW1 : 6283264 <= sp - 2224) by (unfold HIGHMEM_BEG, AF.SLOT_STACK in *; lia).
    assert (HW2 : 6283264 <= fr + 128) by (unfold AC.GT in HGT; lia).
    assert (HW3 : 6283264 <= Sfr fr + 16)
      by (unfold Sfr, shadow_addr, ASAN_K; assert (0 <= fr / 8) by (apply Z.div_pos; lia); lia).
    assert (HRTD : rt_disjoint W).
    { unfold rt_disjoint, W. cbn [disjoint_from].
      unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK,
        RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
      repeat split; try exact I; left; lia. }
    assert (HWlo : forall x, 0 <= x < 6283264 -> outside W x).
    { intros x Hx. unfold W. cbn [outside].
      split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (HWhdr : forall x, fr <= x < fr + 24 -> outside W x).
    { intros x Hx. unfold W. cbn [outside].
      split; [destruct HXw as [Hw|Hw]; lia|]. split; [lia|]. split; [destruct HSfap; lia | exact I]. }
    assert (HWcong : forall A0 x, getr regs 9 = Z_to_bv 64 A0 -> A0 + 16 <= x < A0 + 312 -> outside W x).
    { intros A0 x HA0 Hx. rewrite Hr9 in HA0. pose proof (f23_bv_eq_Z _ _ HA0) as Hc.
      unfold W. cbn [outside].
      split; [|split; [|split; [|exact I]]];
        intros [Q1 Q2]; revert Hc Hx Q1 Q2; Z.div_mod_to_equations; lia. }
    assert (HWspill : forall A0, getr regs 9 = Z_to_bv 64 A0 ->
              forall x, A0 + 304 <= x < A0 + 312 -> outside W x)
      by (intros A0 HA0 x Hx; apply (HWcong A0 x HA0); lia).
    assert (HWsel : forall A0, getr regs 9 = Z_to_bv 64 A0 ->
              forall x, A0 + 16 <= x < A0 + 32 -> outside W x)
      by (intros A0 HA0 x Hx; apply (HWcong A0 x HA0); lia).
    assert (HWsaved : forall x, g_S g - 104 <= x < g_S g -> outside W x).
    { intros x Hx. unfold W. cbn [outside].
      split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (HWmono : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
      by (intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)).
    assert (HPres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                      exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq Hb.
      destruct (Z_le_gt_dec (sp - 2224) q) as [Q1|Q1]; destruct (Z_lt_ge_dec q sp) as [Q2|Q2].
      1:{ destruct ST' as (_ & _ & HH). destruct (HH q ltac:(lia)) as (_ & b' & Hb').
          exists b'. exact Hb'. }
      all: destruct (Z_le_gt_dec (fr + 128) q) as [Q3|Q3]; destruct (Z_lt_ge_dec q (fr + 140)) as [Q4|Q4].
      all: try (destruct HBS as (_ & _ & HH);
                pose proof (HH (Z.to_nat (q - (fr + 128))) ltac:(rewrite f23_ports_len; lia)) as HE;
                rewrite Z2Nat.id in HE by lia;
                replace (fr + 128 + (q - (fr + 128))) with q in HE by lia;
                destruct (nth_error ports_c_bytes (Z.to_nat (q - (fr + 128)))) as [b'|] eqn:EN;
                [exists b'; exact HE
                | exfalso; apply nth_error_None in EN; rewrite f23_ports_len in EN; lia]).
      all: destruct (Z_le_gt_dec (Sfr fr + 16) q) as [Q5|Q5]; destruct (Z_lt_ge_dec q (Sfr fr + 18)) as [Q6|Q6].
      all: try (destruct (SW' q ltac:(replace q with (Sfr fr + (q - Sfr fr)) by lia; apply HshIS; lia))
                  as (_ & b' & Hb'); exists b'; exact Hb').
      all: destruct Hb as (b & Hb); exists b; unfold mbyte in *;
           rewrite (MU (Z_to_bv 64 q)); [exact Hb|];
           rewrite MState.unsigned_lit by lia; unfold W; cbn [outside];
           split; [lia|]; split; [lia|]; split; [lia | exact I]. }
    (* the heap invariant and the stack low bound after the run *)
    assert (HAHst : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem' md /\
                    (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem' md a <->
                               AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem md a) /\
                    AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                    AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5f [Hfsb [Hfs _]]]].
      - assert (Hprem : forall a, 0 <= a < 2 ^ 64 ->
                  ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g)
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
                  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
        { intros a Ha Hns.
        rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. rewrite MState.unsigned_lit by lia.
        unfold W. cbn [outside].
        split; [intros [Q1 Q2]; apply Hns; right; left; lia|].
        split; [intros [Q1 Q2]; apply Hns; right; left; specialize (Hreal a ltac:(lia)); lia|].
        split; [|exact I].
        intros [Q1 Q2]. apply Hns.
        destruct (Z.eq_dec a (Sfr fr + 16)) as [Ea|Hne].
        + subst a. right. right. right. exists (fr + 128). split; [exact HSh16|].
          right. left. specialize (Hreal (fr + 128) ltac:(lia)). lia.
        + assert (Ea : a = Sfr fr + 17) by lia. subst a.
          right. right. right. exists (fr + 136). split; [exact HSh17|].
          right. left. specialize (Hreal (fr + 136) ltac:(lia)). lia. }
        destruct (f23_store (hb1 phi (flen g j) ++ g_H g) mem mem' md HAH Hprem HWmono)
          as (H1 & H2 & H3 & H4).
        split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
      - assert (HfsFS : forall a, fr <= a < fr + FRAME_BYTES ->
                  bv_unsigned FSw <= a < bv_unsigned FSw + AC.FS_SIZE)
          by (intros a Ha; apply (HfsRange a (Hfs a Ha)); lia).
        pose proof (f23_fs_state (hb1 phi (flen g j) ++ g_H g) mem md (bv_unsigned FSw) HAH HFStp HFSr)
          as Hfsok'.
        assert (Hfsok2 : AC.a_fs_ok mem' (bv_unsigned FSw)).
        { apply (a_fs_ok_pres W mem mem' (bv_unsigned FSw) Hfsok' MU HWmono HPres);
            [| lia | unfold AC.FS_SIZE in *; lia].
          intros q Hq. pose proof (fs_meta_below (bv_unsigned FSw) q Hq) as Hqb.
          assert (Hqlo : bv_unsigned FSw <= q).
          { unfold fs_meta in Hq. unfold AC.a_fs_hint, AC.a_fs_flag in Hq.
            destruct Hq as [Hq | [Hq | [ [c [Hc Hr]] | [c [k [Hc [Hk Heq]]]] ]]].
            - lia.
            - lia.
            - assert (0 <= Z.of_nat c) by lia. lia.
            - subst q. unfold AC.a_fs_M in Hk.
              assert (Hp1 : 2 ^ (15 - Z.of_nat c) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
              assert (Hp2 : 0 <= k) by lia. lia. }
          pose proof (HFapp q ltac:(unfold RT_FS_SIZE; lia)) as Hqapp.
          unfold W. cbn [outside].
          split; [lia|].
          split; [lia|].
          split; [|exact I].
          unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END
            in Hqapp, Hsh0, Hsh379. lia. }
        assert (Hprem : forall a, 0 <= a < 2 ^ 64 ->
                  ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g)
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
                  ~ (bv_unsigned FSw <= a < bv_unsigned FSw + AC.FS_SIZE) ->
                  ~ (exists b, bv_unsigned FSw <= b < bv_unsigned FSw + AC.FS_SIZE /\ a = shadow_addr b) ->
                  mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
        { intros a Ha Hns Hnf Hnsh.
        rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. rewrite MState.unsigned_lit by lia.
        unfold W. cbn [outside].
        split; [intros [Q1 Q2]; apply Hns; right; left; unfold APPMEM_END in *; lia|].
        split; [intros [Q1 Q2]; apply Hnf; exact (HfsFS a ltac:(lia))|].
        split; [|exact I].
        intros [Q1 Q2]. apply Hnsh.
        destruct (Z.eq_dec a (Sfr fr + 16)) as [Ea|Hne].
        + subst a. exists (fr + 128). split; [exact (HfsFS (fr + 128) ltac:(lia)) | exact HSh16].
        + assert (Ea : a = Sfr fr + 17) by lia. subst a.
          exists (fr + 136). split; [exact (HfsFS (fr + 136) ltac:(lia)) | exact HSh17]. }
        destruct (f23_fs_store (hb1 phi (flen g j) ++ g_H g) mem mem' md (bv_unsigned FSw) HAH HFStp HFSr Hprem
                    HWmono Hfsok2) as (H1 & H2 & H3 & H4).
        split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4]. }
    destruct HAHst as (HAH' & Hown' & Hlo' & Hhi').
    (* every byte W writes is a byte of the slot window, of the frame or of the frame's 392 shadow bytes *)
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 -> outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/
                        (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx.
      destruct (Z_le_gt_dec fr x) as [F1|F1]; [destruct (Z_lt_ge_dec x (fr + FRAME_BYTES)) as [F2|F2]|].
      1:{ right; right; left; lia. }
      all: destruct (Z_le_gt_dec (Sfr fr) x) as [S1|S1]; [destruct (Z_lt_ge_dec x (Sfr fr + FRAME_SHADOW)) as [S2|S2]|].
      all: try (right; right; right; lia).
      all: destruct (Z_le_gt_dec (sp - 2224) x) as [P1|P1]; [destruct (Z_lt_ge_dec x sp) as [P2|P2]|].
      all: try (right; left; lia).
      all: left; unfold W; cbn [outside]; split; [lia|]; split; [lia|]; split; [lia | exact I]. }
    (* FRA moves to (regs', mem', md') *)
    assert (HstkSh : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
    { apply f23_stk_shadow; [exact SW' | lia | unfold HIGHMEM_BEG in *; lia |].
      intros x Hx. replace x with (Sfr fr + (x - Sfr fr)) by lia. apply HshIS. lia. }
    destruct (stk_bytes rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW) HstkSh ltac:(lia)) as (shb & Hshlen & Hshb).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md).
    { apply (f23_fra g fr (hb1 phi (flen g j)) regs regs' mem mem' md W HFRA MU WM RO' HRTD HAH' Hlo').
      - intros a Ha. exact (proj2 (SW' a Ha)).
      - exists shb. split; [exact Hshb|].
        rewrite Hshlen. replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity.
      - (* the entry-anchored window: writability by wmono, the bytes by HPres *)
        pose proof Hwin as (Hw0 & Hw1 & Hwv). split; [exact Hw0|]. split; [exact Hw1|].
        intros a Ha. destruct (Hwv a Ha) as (HWa & HBa). split.
        + exact (WM (Z_to_bv 64 a) HWa).
        + exact (HPres a ltac:(lia) HBa).
      - (* the registered globals: image bytes below GT <= fr, so their shadow bytes miss W *)
        intros a Hin. pose proof (HAG a Hin) as Had.
        destruct Hin as (lo & len & Hil & Hr). pose proof (f23_AG_low lo len Hil) as Hlow.
        apply (addr1_munch W mem mem' a MU); [|exact Had].
        pose proof (addr1_app mem a Had) as Happa. pose proof (shadow_of_app a Happa) as Hsha.
        assert (Hd : a / 8 <= fr / 8) by (apply Z.div_le_mono; lia).
        unfold W. cbn [outside].
        split; [unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsha; lia|].
        split; [unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END
                  in Hsha, Happ0, Happ1; lia|].
        split; [unfold Sfr, shadow_addr in *; lia | exact I].
      - (* the window outside the frame: its shadow bytes miss W *)
        intros a H1 H2. pose proof (HWAD a H1 H2) as Had.
        apply (addr1_munch W mem mem' a MU); [|exact Had].
        pose proof (addr1_app mem a Had) as Happa. pose proof (shadow_of_app a Happa) as Hsha.
        assert (Hage : 0 <= a) by (destruct Had as (Hz & _); exact Hz).
        unfold W. cbn [outside].
        split; [unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsha; lia|].
        split; [unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END
                  in Hsha, Happ0, Happ1; lia|].
        split; [|exact I].
        assert (Hfr0 : 0 <= fr) by lia.
        intros Hb. apply H2. unfold Sfr, shadow_addr in Hb.
        revert Hb Hfrm Hage Hfr0 HFBv HFSv. clear. intros. Z.div_mod_to_equations. lia.
      - exact HWlo.
      - exact HWhdr.
      - exact HWspill.
      - exact HWsel.
      - exact HWsaved.
      - (* the side arm's frame record: W misses the low image, and its app bytes below stklo are frame bytes *)
        intros HR. eapply fsrec_munch_lo with (W := W); [exact HR | exact HAH | exact MU | exact HWlo |].
        intros x Hxa Hxf Hxs. unfold W. cbn [outside].
        split; [intros [Q1 Q2]; lia|].
        split; [intros [Q1 Q2]; apply Hxf; lia|].
        split; [|exact I]. intros [Q1 Q2]. apply (app_not_shadow x Hxa).
        replace x with (Sfr fr + (x - Sfr fr)) by lia. apply HshIS. lia.
      - exact E2.
      - exact E3.
      - exact E4.
      - exact E8.
      - exact E9.
      - exact E19.
      - exact E26. }
    (* ENT moves across the run (ent_store: W is the slot window, the frame and the frame's shadow) and across
       the model's materialization (ent_mat) *)
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md).
    { apply (ent_store B APIf ra g fr (hb1 phi (flen g j)) regs mem mem' md W HENT HFRA MU HWcases Hlo' Hhi').
      intros a _ Ho. exact (proj2 (Hown' a) Ho). }
    assert (HENT'' : ENT APIf g (hb1 phi (flen g j)) mem' md')
      by (eapply ent_mat; [exact HENT' | exact Hmat]).
    rewrite <- SEGS. apply Hexit.
    unfold Inv_A825c8_at, B7CUT.
    exists phi, regs', mem', md', fr.
    rewrite ?Hasz.
    cbv beta.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs' regs' mem' md md' HFRA');
        try reflexivity. exact Hmat. }
    split; [exact HENT''|].
    split; [exact Hgn|].
    split; [exact Hj|].
    (* the harness buffer is still addressable *)
    assert (HWsh : forall i, 0 <= i < AC.a_size (flen g j) -> outside W (shadow_addr (phi + i))).
    { intros i Hi.
      destruct (Hpbytes (phi + i) ltac:(lia)) as (Hpapp & _).
      pose proof (shadow_of_app _ Hpapp) as Hpsh.
      unfold W. cbn [outside].
      split.
      { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
      split.
      { unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END
          in Hpsh, Happ0, Happ1. lia. }
      split; [|exact I].
      assert (Hdiv : (phi + i) / 8 <= fr / 8 \/ fr / 8 + FRAME_SHADOW <= (phi + i) / 8).
      { destruct Hblkfr as [HL|HR].
        - left. apply Z.div_le_mono; lia.
        - right. assert (HD : (fr + FRAME_SHADOW * 8) / 8 <= (phi + i) / 8) by (apply Z.div_le_mono; lia).
          rewrite Z.div_add in HD by lia. lia. }
      unfold Sfr, shadow_addr. lia. }
    split.
    { destruct HHB as (Hp0 & Hpad). split; [exact Hp0|].
      exact (f23_addr_keep mem mem' W phi (AC.a_size (flen g j)) Hpad MU HWsh). }
    (* FLSI and B7K: the run writes the copy's window [sp - 2224, sp), the ports words fr + 128 .. fr + 139 and
       their two shadow bytes; none of FLSI's or B7K's bytes *)
    assert (Hfr0 : 0 <= fr) by (unfold AC.GT in HGT; lia).
    assert (HAb' : A + 416 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
    assert (HWAr : forall x, A <= x < A + 416 -> outside W x).
    { intros x Hx. unfold W. cbn [outside].
      split; [lia|]. split; [lia|]. split; [unfold HIGHMEM_BEG in *; lia | exact I]. }
    assert (HinB : forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)).
    { intros x Hx.
      destruct (f23_blk (hb1 phi (flen g j) ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror (Fin1 ltac:(lia))))) as (_ & _ & Hqstk & Hqbytes).
      destruct (Hadin (x - g_p g) ltac:(lia)) as (Hxa & _).
      replace (g_p g + (x - g_p g)) with x in Hxa by lia.
      assert (Hxfr : ~ (fr <= x < fr + FRAME_BYTES)).
      { intros Hxf. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
        - specialize (Hreal x Hxf). lia.
        - destruct (Hqbytes x Hx) as (_ & Hnfs). exact (Hnfs (Hfs x Hxf)). }
      pose proof (shadow_of_app x Hxa) as Hxs.
      assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
      split.
      - unfold W. cbn [outside].
        split; [intros [Q1 Q2]; unfold AF.SLOT_STACK in *; lia|].
        split; [intros [Q1 Q2]; apply Hxfr; lia|].
        split; [|exact I]. intros [Q1 Q2]. apply (app_not_shadow x Hxa).
        replace x with (Sfr fr + (x - Sfr fr)) by lia. apply HshIS. lia.
      - unfold W. cbn [outside].
        split; [unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, AF.SLOT_STACK in *; lia|].
        split; [unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END
                  in Hxs, Happ0, Happ1; lia|].
        split; [|exact I]. intros [Q1 Q2]. apply Hxfr.
        unfold Sfr, shadow_addr in Q1, Q2. clear - Q1 Q2 Hx0 Hfr8 Hfr0 HFBv. Z.div_mod_to_equations. lia. }
    assert (Hstk' : stk rsegs mem' fr (fr + FRAME_BYTES)).
    { pose proof Fstk as (Hf0 & Hf1 & Hfv). split; [exact Hf0|]. split; [exact Hf1|].
      intros a Ha. destruct (Hfv a Ha) as (HWa & HBa). split.
      + exact (WM (Z_to_bv 64 a) HWa).
      + exact (HPres a ltac:(lia) HBa). }
    split.
    { apply (b7_flsi_keep g j fr regs regs' mem mem' W A HFLSI Hr9 ltac:(lia) HAb' E9 MU HWAr).
      - intros i Hi. unfold W. cbn [outside].
        assert (Hs : Sfr fr + 328 <= shadow_addr (fr + 2624 + i) < Sfr fr + 330).
        { unfold Sfr, shadow_addr. clear - Hi Hfr8 Hfr0. Z.div_mod_to_equations. lia. }
        split; [unfold HIGHMEM_BEG in *; lia|]. split; [destruct HSfap; lia|]. split; [lia | exact I].
      - intros i Hi. unfold W. cbn [outside].
        assert (Hs : Sfr fr + 336 <= shadow_addr (fr + 2688 + i) < Sfr fr + 341).
        { unfold Sfr, shadow_addr. clear - Hi Hfr8 Hfr0. Z.div_mod_to_equations. lia. }
        split; [unfold HIGHMEM_BEG in *; lia|]. split; [destruct HSfap; lia|]. split; [lia | exact I].
      - intros i Hi. unfold W. cbn [outside].
        assert (Hs : Sfr fr + 346 <= shadow_addr (fragb fr + i) < Sfr fr + 355).
        { unfold fragb, Sfr, shadow_addr. clear - Hi Hfr8 Hfr0. Z.div_mod_to_equations. lia. }
        split; [unfold HIGHMEM_BEG in *; lia|]. split; [destruct HSfap; lia|]. split; [lia | exact I].
      - intros x Hx. exact (proj1 (HinB x Hx)).
      - intros i Hi. exact (proj2 (HinB (g_p g + i) ltac:(lia))).
      - exact Hstk'. }
    split.
    { apply (b7_B7K_keep g j phi fr regs regs' mem mem' W A HK MU Hr9 ltac:(lia) HAb' E9 E18 E21 E22 E23 E24 HWAr).
      - intros x Hx. destruct (Hpbytes x ltac:(lia)) as (Hxa & _). unfold W. cbn [outside].
        split; [intros [Q1 Q2]; unfold AF.SLOT_STACK in *; lia|].
        split; [intros [Q1 Q2]; destruct Hblkfr; lia|].
        split; [|exact I]. intros [Q1 Q2]. apply (app_not_shadow x Hxa).
        replace x with (Sfr fr + (x - Sfr fr)) by lia. apply HshIS. lia.
      - intros x Hx. unfold W. cbn [outside].
        split; [destruct HXw; lia|]. split; [lia|]. split; [destruct HSfap; lia | exact I].
      - (* v1.9: the FIRST body first.sroa.7 [fr + 2880, fr + 2915) and its shadow bytes S(fr) + 360 .. 364 *)
        intros x Hx. unfold W. cbn [outside].
        split; [destruct HXw; lia|]. split; [lia|]. split; [destruct HSfap; lia | exact I].
      - intros i Hi. unfold W. cbn [outside].
        assert (Hs : Sfr fr + 360 <= shadow_addr (fr + 2880 + i) < Sfr fr + 365).
        { unfold Sfr, shadow_addr. clear - Hi Hfr8 Hfr0. Z.div_mod_to_equations. lia. }
        split; [unfold HIGHMEM_BEG in *; lia|]. split; [destruct HSfap; lia|]. split; [lia | exact I]. }
    (* the segment's own exit facts *)
    split; [unfold rg; exact E20|].
    unfold ports_c_bytes in HBS.
    apply (proj1 (bytes_at_app rsegs mem' (fr + 128) m7w (m7w ++ m7w))) in HBS.
    destruct HBS as (HBS0 & HBS1).
    unfold m7w in HBS1 at 1. rewrite length_le4 in HBS1. cbn [Z.of_nat] in HBS1.
    apply (proj1 (bytes_at_app rsegs mem' (fr + 128 + 4) m7w m7w)) in HBS1.
    destruct HBS1 as (HBS1 & HBS2).
    unfold m7w in HBS2 at 1. rewrite length_le4 in HBS2. cbn [Z.of_nat] in HBS2.
    split; [unfold u32, m7w in *; exact HBS0|].
    split; [unfold u32, m7w in *; replace (fr + 132) with (fr + 128 + 4) by lia; exact HBS1|].
    split; [unfold u32, m7w in *; replace (fr + 136) with (fr + 128 + 4 + 4) by lia; exact HBS2|].
    exact HAD'.
Qed.

End S.
