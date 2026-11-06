(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, addresses and numbers changed; 555 of its 598 lines of code are new or changed and 353 lines of the source are left out. *)
(* Segment F20 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B), libreac v1.9.0: the cut-to-cut range
   0x82668 .. 0x82728 (v1.8: 0x825e8 .. 0x826a4), the twin of lib/A/Prog/Seg/F20.v.  Both cuts are the official
   ones of lib/B/Prog/SlotInv.v (Inv_B82668_at, Inv_B82728_at).
   From the entry cut at 0x82668 (a0 = 0 on the bcmp fall-through) the block runs:
   - four one-byte instrumented checks on the record bytes Phi+14 .. Phi+17 (each loads the shadow byte at
     (a >> 3) + 0x7fff8000 and the `bnez shadow,<errpath>` is shown NOT taken from the zero shadow byte the cut
     carries);
   - the arithmetic-check compares `beqz s2,82fa0` and `bltu a0,s2,82fa0` with a0 = -15 / -16 / -17 / -18: each
     branch to the trap routine at 0x82fa0 is not taken because the cut carries 0 < Phi and Phi + 50 <= 2 ^ 64,
     so Phi is non-zero and Phi + 14 .. Phi + 17 stay below 2 ^ 64;
   - the two record comparisons at 0x826c0 (the u16 at fr + 196 = [[A+280] + 20], [A+280] = fr + 176 from FLI; v1.8
     read it through s6 = fr + 176 with `lhu a2,20(s6)`, v1.9.0 adds the load 0x82690 `ld a2,280(s1)`) against
     (v15 << 8) | v14, and 0x8271c, both shown NOT taken from the field equalities the cut carries;
   - `mv a0,s2` at 0x82720 and the call `jal reac_ctrl_checksum_verify` at 0x82724 (Section Hypothesis HCKV):
     a0 = Phi, the 32 record bytes [Phi + 18, Phi + 50) are addressable, and the only memory the callee writes is
     its own 16 bytes [sp - 16, sp) inside the slot's stack window.  It returns 0 when the block sum of those 32
     bytes is 0 and -1 otherwise, which the exit cut at 0x82728 carries in a0.
   The run is one B.Tk.UL run (Tac_slot.sl_run, AsanLift.evt_SR_canon_lazy); the callee contract speaks the Lib
   engine, carried over by lu_evt.  FRA moves across the callee's 16-byte window by Tac_slot.sl_win_run (its
   ro_agree premise comes from FRA's ro_agree and the window lying above HIGHMEM_BEG, its AH / stklo premises from
   the allocator law a_laws_store, its frame premises from SlotInv.fra_app / fra_frame, its below-stklo premise from
   FRA's stklo <= S - SLOT_STACK < sp - 16), and ENT by Tac_slot.ent_store; the model step is Tac_slot.sl_fra_move /
   ent_mat.  The frame-loop bundles LK (with FLI) and FM move by lk_move / fm_move: their spills lie at or above
   the spill base A >= sp, our[] and the frame body [fr, fr + 3136) miss the window (fra_frame).  No cut carries
   mem_inv. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_checksum_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFragLib RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Mem.
Module UEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.
Module LEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module CKV := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_checksum_verify_c.

(* A Lib.Exec run is a UL run: the two step relations have the same body. *)
Lemma lu_msteps : forall s s', LEx.msteps rsegs s s' -> UEx.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UEx.msteps_refl|].
  eapply UEx.msteps_cons; [exact Hs | exact IH].
Qed.
Lemma lu_evt : forall Q ms, LEx.evt rsegs Q ms -> UEx.evt rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (lu_msteps _ _ H) | exact HQ]. Qed.

(* Z_to_bv 64 is injective on [-440, 2^64) x [0, 2^64 - 448]: a spill base read twice is the same base (the save
   area of this function is 448 bytes, so a spill offset is at most 440). *)
Lemma bv64_inj_near : forall x y, -440 <= x < 2 ^ 64 -> 0 <= y <= 2 ^ 64 - 448 ->
  Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal (bv_unsigned (n:=64))) in E.
  rewrite !MState.unsigned_lit_wrap in E. rewrite (Z.mod_small y) in E by lia.
  destruct (Z_lt_le_dec x 0) as [Hn|Hp].
  - assert (Em : x mod 2 ^ 64 = x + 2 ^ 64).
    { rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    lia.
  - rewrite Z.mod_small in E by lia. exact E.
Qed.

(* The record bytes: t_g is 50 bytes, so its slices below 50 have their full length. *)
Lemma bsl_tg_len : forall inp j k n, 0 <= k -> 0 <= n -> k + n <= 50 ->
  length (bsl (t_g inp j) k n) = Z.to_nat n.
Proof.
  intros inp j k n Hk Hn Hkn. unfold bsl, t_g. rewrite length_firstn, length_skipn, fr50_length. lia.
Qed.
Lemma t_blk_len : forall inp j, length (t_blk inp j) = 32%nat.
Proof. intros inp j. unfold t_blk. rewrite bsl_tg_len by lia. reflexivity. Qed.

(* Every read-only image address lies below HIGHMEM_BEG (every image segment ends below it). *)
Lemma rsegs_low : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? HIGHMEM_BEG) rsegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ro_below : forall a, ro_addr rsegs a = true -> bv_unsigned a < HIGHMEM_BEG.
Proof.
  intros a Ha. unfold ro_addr in Ha.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:Ef; [|discriminate].
  destruct (kb_find_segment rsegs (bv_unsigned a) 1 s Ef) as (Hs & _ & Hs2).
  pose proof (proj1 (forallb_forall _ rsegs) rsegs_low s Hs) as Hb. cbn beta in Hb. apply Z.leb_le in Hb. lia.
Qed.

(* ---- Read facts in the `ov_read_bytes _ _ (wa a) n = Some bs` form the UL `step` consumes. ---- *)
Lemma rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (ULMem.wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma rd2 : forall m a bs, bytes_at rsegs m a bs -> length bs = 2%nat ->
  ov_read_bytes rsegs m (ULMem.wa a) 2 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (ULMem.bytes_at_ov_read rsegs m a bs 0 2 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

(* ---- Byte / word arithmetic of the two record comparisons. ---- *)
Lemma ubv8 : forall v, 0 <= v < 256 -> bv_unsigned (zxb (Z_to_bv 8 v)) = v.
Proof.
  intros v Hv. unfold zxb. rewrite (MState.unsigned_lit (bv_unsigned (Z_to_bv 8 v))).
  - rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
  - rewrite Z_to_bv_unsigned, (bv_wrap_small 8 v) by (unfold bv_modulus; cbn; lia). lia.
Qed.
Lemma rd8 : forall m a v, q64 m a v -> ov_read_bytes rsegs m (ULMem.wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold q64 in H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite ULMem.length_le8; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH.
  rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite ULMem.length_le8; lia).
  exact HH.
Qed.
(* A spill cell read at the cut's own spill base A (the base is pinned by register 9). *)
Lemma spill_q64 : forall regs m off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA HA0 HA1 Hoff.
  pose proof (LMem.bytes_at_bound rsegs m _ _ Hq) as Hb. rewrite LMem.length_le8 in Hb.
  assert (EA : A' = A).
  { apply bv64_inj_near; [lia | lia |].
    unfold rg in *. transitivity (getr regs 9); [symmetry; exact HA' | exact HA]. }
  subst A'. exact Hq.
Qed.
Lemma zxb8 : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; cbn; lia.
Qed.
Lemma eqb0_false : forall v, 0 < v < 2 ^ 64 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = false.
Proof.
  intros v Hv. apply Bool.not_true_iff_false. intro HC. apply bv_eqb_eq in HC.
  apply (f_equal bv_unsigned) in HC. rewrite !MState.unsigned_lit in HC by lia. lia.
Qed.
(* seqz (= sltiu _ 1) reduces to the 0/1 indicator, matching the carried booleans. *)
Lemma seqz_v17 : forall v17, 0 <= v17 < 256 ->
  PropExec.v_sltiu (zxb (Z_to_bv 8 v17)) 1 = Z_to_bv 64 (if v17 =? 0 then 1 else 0).
Proof.
  intros v17 Hv. unfold PropExec.v_sltiu. rewrite ubv8 by lia. change (bv_wrap 64 1) with 1%Z.
  replace (v17 <? 1) with (v17 =? 0) by
    (destruct (Z.eqb_spec v17 0); destruct (Z.ltb_spec v17 1); lia).
  destruct (v17 =? 0); reflexivity.
Qed.
Lemma seqz_vs8 : forall vs8, 0 <= vs8 < 2 ^ 64 ->
  PropExec.v_sltiu (Z_to_bv 64 (vs8 + -1)) 1 = Z_to_bv 64 (if vs8 =? 1 then 1 else 0).
Proof.
  intros vs8 Hv. unfold PropExec.v_sltiu. rewrite MState.unsigned_lit_wrap. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.eq_dec vs8 0) as [->|H0].
  - change ((0 + -1) mod 2 ^ 64 <? 1) with false. reflexivity.
  - rewrite (Z.mod_small (vs8 + -1) (2 ^ 64)) by lia.
    replace (vs8 + -1 <? 1) with (vs8 =? 1) by
      (destruct (Z.eqb_spec vs8 1); destruct (Z.ltb_spec (vs8 + -1) 1); lia).
    destruct (vs8 =? 1); reflexivity.
Qed.
Lemma cmp16_eq : forall v14 v15 field16, 0 <= v14 < 256 -> 0 <= v15 < 256 -> field16 = v14 + 256 * v15 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb (Z_to_bv 8 v15))) 8)))
                    (bv_unsigned (zxb (Z_to_bv 8 v14))))
  = zx16 (Z_to_bv 64 field16).
Proof.
  intros v14 v15 field16 H14 H15 Hf.
  rewrite (ubv8 v15), (ubv8 v14) by lia.
  rewrite (MState.unsigned_lit (Z.shiftl v15 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia.
  unfold zx16. rewrite (MState.unsigned_lit field16) by lia.
  rewrite Z.mod_small by lia. subst field16. reflexivity.
Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map; exposing it lets `step` read a slot we have
   rewritten to a concrete value. *)
Lemma mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried concrete value, from H : rg regs r v. *)
Ltac subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* A spill at A + off survives a write [lo, hi) that lies below it (the run keeps s1). *)
Lemma spill_keep : forall regs regs' m m' off v A lo hi,
  spill regs m off v -> rg regs 9 A -> getr regs' 9 = getr regs 9 ->
  0 <= off <= 440 -> 0 <= A -> A + 448 <= 2 ^ 64 -> hi <= A + off ->
  LFr.munch [(lo, hi)] m m' -> spill regs' m' off v.
Proof.
  intros regs regs' m m' off v A lo hi (A' & HA' & Hq) HA E9 Hoff HA0 HA1 Hhi MU.
  pose proof (LMem.bytes_at_bound rsegs m _ _ Hq) as Hb. rewrite LMem.length_le8 in Hb.
  assert (EA : A' = A).
  { apply bv64_inj_near; [lia | lia |]. unfold rg in *. transitivity (getr regs 9); [symmetry; exact HA' | exact HA]. }
  subst A'. exists A. split; [unfold rg in *; rewrite E9; exact HA'|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite LMem.length_le8.
  intros x Hx. simpl. split; [lia | exact I].
Qed.

(* LK (with its FLI bundle) survives a write [lo, hi) below the spill base A that misses the frame body
   [fr, fr + 3136) and keeps s1 and s11: the spills by spill_keep, our[] (inside the frame body) by fl_bytes,
   its six addressable bytes and RAD's records by sl_addr_keep, the frame body's stk by stk_transport. *)
Lemma lk_move : forall g fr j regs regs' m m' A lo hi,
  LK g fr j regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> hi <= A ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 ->
  LFr.munch [(lo, hi)] m m' -> LFr.wmono rsegs m m' -> all_app [(lo, hi)] -> HIGHMEM_BEG <= lo ->
  (forall x, fr <= x < fr + 3136 -> x < lo \/ hi <= x) ->
  LK g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' A lo hi (Hj & H240 & HOUR & HFLI) HA HA0 HA1 Hhi E9 E27 MU WM HAW Hlo Hfr.
  assert (SK : forall off v, 0 <= off <= 440 -> spill regs m off v -> spill regs' m' off v)
    by (intros off v Hoff Hs; exact (spill_keep regs regs' m m' off v A lo hi Hs HA E9 Hoff HA0 HA1
                                       ltac:(lia) MU)).
  split; [exact Hj|]. split; [apply SK; [lia | exact H240]|].
  split.
  { unfold OURb in *. apply (fl_bytes _ m m' (fr + 2624) (OUR (g_in g)) HOUR MU).
    rewrite OUR_length. intros x Hx. simpl. split; [|exact I]. specialize (Hfr x ltac:(lia)). lia. }
  unfold FLI in *. destruct HFLI as (H27 & H).
  split; [unfold rg in *; rewrite E27; exact H27|].
  repeat (let X := fresh "X" in destruct H as (X & H); split; [apply SK; [lia | exact X]|]).
  destruct H as (Had & Hstk & (Hrad1 & Hrad2 & Hrad3) & (Hknt1 & Hknt2) & S168 & S88).
  split; [exact (sl_addr_keep m m' [(lo, hi)] (fr + 2624) 6 Had MU HAW)|].
  split.
  { apply (LFr.stk_transport rsegs [(lo, hi)] m m' fr (fr + FRAME_BYTES) Hstk MU WM).
    intros x Hx. left. simpl. split; [|exact I]. unfold FRAME_BYTES in Hx. specialize (Hfr x Hx). lia. }
  (* RAD: the three frame records stay marked usable (the write set is app memory) *)
  split; [split; [exact (sl_addr_keep m m' [(lo, hi)] (fr + 2688) 38 Hrad1 MU HAW)|
                  split; [exact (sl_addr_keep m m' [(lo, hi)] (fragb fr) 72 Hrad2 MU HAW)
                         | exact (sl_addr_keep m m' [(lo, hi)] (fr + 2880) 40 Hrad3 MU HAW)]]|].
  (* KNT: the kind-name table is image memory, far below the high-memory write set *)
  split.
  { split.
    - assert (HKL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
      apply (fl_bytes _ m m' KNC.KIND_NAME KNC.kind_name_bytes Hknt1 MU).
      rewrite HKL. intros x Hx. simpl. split; [|exact I]. unfold KNC.KIND_NAME, HIGHMEM_BEG in *. lia.
    - exact (sl_addr_keep m m' [(lo, hi)] KNC.KIND_NAME 112 Hknt2 MU HAW). }
  split; [apply SK; [lia | exact S168] | apply SK; [lia | exact S88]].
Qed.

(* FM (v1.9.0: the fill flag [A+184], k = s8, s6 = 1, the sum flag s9, the block [A+312]) survives the same write
   when s1, s6, s8 and s9 are kept. *)
Lemma fm_move : forall g j phi fr regs regs' m m' A lo hi,
  FM g j phi fr regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> hi <= A ->
  getr regs' 9 = getr regs 9 -> getr regs' 22 = getr regs 22 -> getr regs' 24 = getr regs 24 ->
  getr regs' 25 = getr regs 25 -> LFr.munch [(lo, hi)] m m' ->
  FM g j phi fr regs' m'.
Proof.
  intros g j phi fr regs regs' m m' A lo hi (H184 & H24 & H22 & H25 & H312) HA HA0 HA1 Hhi E9 E22 E24 E25 MU.
  split; [exact (spill_keep regs regs' m m' 184 _ A lo hi H184 HA E9 ltac:(lia) HA0 HA1 ltac:(lia) MU)|].
  split; [unfold rg in *; rewrite E24; exact H24|].
  split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E25; exact H25|].
  exact (spill_keep regs regs' m m' 312 _ A lo hi H312 HA E9 ltac:(lia) HA0 HA1 ltac:(lia) MU).
Qed.

(* ---- The turn's two frame records by length (model): t_FG j has 72 bytes (every fragment step keeps 72) and
   t_ID j 38 (every ingest keeps 38); the IFS transport below needs both to keep them inside the frame. ---- *)
Lemma rl_fg_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.
Lemma rl_keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.
Lemma rl_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. pose proof (rl_fg_n len g FR) as Hn. unfold fg_first, fg_body.
    rewrite !length_app, length_skipn, (RcFragLib.rf_bsl_length g 6 6),
      (RcFragLib.rf_bsl_length g 27 (fg_n g)) by lia.
    cbn [length]. lia.
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply RcFragLib.rf_clear_length; exact HL].
    destruct (fg_close st g); cbn [negb fg_next]; apply RcFragLib.rf_clear_length, RcFragLib.rf_fg_join_length;
      solve [exact HL | exact HG | apply (rl_fg_n len); exact FR | apply rl_keep_T; exact KEEP].
Qed.
Lemma rl_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (rl_next_length 1 1 1 1 1); solve [exact IH | unfold t_g; apply fr50_length].
Qed.
Lemma rl_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_ID in *. rewrite fst_at_S. unfold turn. cbv zeta.
    assert (Hr : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
    { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact IH | exact IH]. }
    assert (Hf : length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) (t_len inp j)
                           (fs_fg (fst_at inp j)) (t_g inp j)) = 38%nat).
    { unfold fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [apply RcIdentModel.ING_length; exact Hr | exact Hr]. }
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; exact Hf.
Qed.

(* FTURN survives a write [lo, hi) below the spill base A that misses Phi's len bytes (the run keeps s1). *)
Lemma turn_move : forall g j phi regs regs' m m' A lo hi,
  FTURN g j phi regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> hi <= A ->
  getr regs' 9 = getr regs 9 -> LFr.munch [(lo, hi)] m m' ->
  (forall x, phi <= x < phi + t_len (g_in g) j -> x < lo \/ hi <= x) ->
  FTURN g j phi regs' m'.
Proof.
  intros g j phi regs regs' m m' A lo hi (H224 & H232 & Hphi & Hlen) HA HA0 HA1 Hhi E9 MU Hout.
  split; [exact (spill_keep regs regs' m m' 224 _ A lo hi H224 HA E9 ltac:(lia) HA0 HA1 ltac:(lia) MU)|].
  split; [exact (spill_keep regs regs' m m' 232 _ A lo hi H232 HA E9 ltac:(lia) HA0 HA1 ltac:(lia) MU)|].
  split; [|exact Hlen].
  apply (fl_bytes _ m m' phi _ Hphi MU). intros x Hx. simpl. split; [|exact I].
  specialize (Hout x ltac:(lia)). lia.
Qed.

(* The body of the first-fragment state is at most 23 bytes (frame bytes 27 .. 50). *)
Lemma fst_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* IFS (both frame records and the local `first` at fr + 2880) survives a write [lo, hi) of app memory below the
   spill base A that misses the frame body [fr, fr + 3136), which holds all three. *)
Lemma ifs_move : forall g fr j regs regs' m m' A lo hi,
  IFS g fr j regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> hi <= A ->
  getr regs' 9 = getr regs 9 -> LFr.munch [(lo, hi)] m m' -> all_app [(lo, hi)] ->
  (forall x, fr <= x < fr + 3136 -> x < lo \/ hi <= x) ->
  IFS g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' A lo hi ((Hid & Hidok) & (Hfg & Hfgok) & (Hhave & Hn & Hbody & Had & HFI))
    HA HA0 HA1 Hhi E9 MU HAW Hfr.
  pose proof (fst_body_len (g_in g) j) as HBL.
  split; [split; [|exact Hidok]|split; [split; [|exact Hfgok]|]].
  - unfold IDBe in *. apply (fl_bytes _ m m' (fr + 2688) _ Hid MU).
    rewrite rl_ID_length. intros x Hx. simpl. split; [|exact I]. specialize (Hfr x ltac:(lia)). lia.
  - unfold FGBe in *. apply (fl_bytes _ m m' (fr + 2768) _ Hfg MU).
    rewrite rl_FG_length. intros x Hx. simpl. split; [|exact I]. specialize (Hfr x ltac:(lia)). lia.
  - split.
    { unfold u32 in *. apply (fl_bytes _ m m' (fr + 2880) _ Hhave MU). rewrite LMem.length_le4.
      intros x Hx. simpl. split; [|exact I]. specialize (Hfr x ltac:(lia)). lia. }
    split.
    { unfold b8 in *. apply (fl_bytes _ m m' (fr + 2884) _ Hn MU). cbn [length].
      intros x Hx. simpl. split; [|exact I]. specialize (Hfr x ltac:(lia)). lia. }
    split.
    { apply (fl_bytes _ m m' (fr + 2885) _ Hbody MU).
      intros x Hx. simpl. split; [|exact I]. specialize (Hfr x ltac:(lia)). lia. }
    split; [exact (sl_addr_keep m m' [(lo, hi)] (fr + 2880) 40 Had MU HAW) | exact HFI].
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract of reac_ctrl_checksum_verify (lib/B/Prog/reac_ctrl_checksum_verify_c.v). *)
Hypothesis HCKV : CKV.reac_ctrl_checksum_verify_contract.

(* The FRA facts this segment reads, by name (tauto), not by position. *)
Lemma f20_fra : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists A sp,
    AsanRTInv.RT sp mem md /\ AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md /\
    ro_agree rsegs mem /\ m_halted md = None /\
    getr regs 2 = Z_to_bv 64 sp /\ AC.aspZ regs = sp /\
    AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= g_S g - AF.SLOT_STACK /\
    rg regs 9 A /\ rg regs 26 ASAN_K /\
    A <= g_S g /\ sp <= A /\ fr + FRAME_BYTES <= A /\ A + 448 <= g_S g /\ g_S g - 4096 < sp /\ g_S g < APPMEM_END /\
    LFr.stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g).
Proof. intros g fr hb regs mem md H. destruct H as (A & sp & s5 & H). exists A, sp. tauto. Qed.

(* FRA and ENT across a callee that writes only its own 16 bytes [sp - 16, sp) inside the slot's stack window and
   keeps the FRA registers (sp 2, gp 3, tp 4, s0 8, s1 9, s3 19, s10 26). *)
Lemma call16_move : forall g fr hb regs regs' mem mem' md md' sp,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  AC.aspZ regs = sp ->
  LFr.munch [(sp - 16, sp)] mem mem' -> LFr.wmono rsegs mem mem' ->
  LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) sp ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  intros g fr hb regs regs' mem mem' md md' sp HFRA HENT Haspz MU WM ST
    E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hfrw & _ & _ & _).
  pose proof (Hfrw 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as Hdisjfr.
  rewrite Haspz in Hdisjfr.
  destruct (f20_fra g fr hb regs mem md HFRA)
    as (A & sp0 & HRT & HAH & Hro & Hhalt & Hr2 & Haspz0 & Hstklo & Hr9 & Hr26 &
        HAS & HspA & HfrA & HA448 & HS4 & HAPP & Hwin).
  assert (Esp : sp0 = sp) by (rewrite <- Haspz0; exact Haspz). subst sp0.
  unfold FRAME_BYTES in HfrA.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (Hlo16 : HIGHMEM_BEG <= sp - 16) by lia.
  assert (HOW : forall x, (x < sp - 16 \/ sp <= x) -> LFr.outside [(sp - 16, sp)] x)
    by (intros x Hx; simpl; split; [lia | exact I]).
  assert (Hallapp : all_app [(sp - 16, sp)]).
  { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    unfold APPMEM_END in *. lia. }
  assert (Hrtdj : rt_disjoint [(sp - 16, sp)]) by (apply rt_disjoint_hi; lia).
  assert (HroM : ro_agree rsegs mem').
  { apply (ro_agree_same rsegs mem mem' Hro). intros a Ha. apply MU. apply HOW. left.
    pose proof (ro_below a Ha). lia. }
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. apply HOW.
    destruct (Z_lt_le_dec a (sp - 16)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec a sp) as [H2|H2]; [|right; exact H2].
    exfalso. apply Hns. unfold AC.a_store_ok. right; left. unfold APPMEM_END in *. split; lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (AC.a_laws_store _ _ _ _ _ LAWS (hb ++ g_H g) mem mem' md HAH HstoreC HwmL)
    as (HAH' & Hownst & HSTKeq & HSTKHeq).
  assert (HFRAm : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_win_run B APIf ra empty FF g fr hb regs regs' mem mem' md [(sp - 16, sp)]
             HFRA MU WM HroM Hallapp Hrtdj HAH' HSTKeq).
    - intros x Hx. apply HOW. rewrite Haspz in Hx. destruct Hx as [Hx|Hx]; [left; lia | right; lia].
    - intros x Hx. apply HOW. unfold FRAME_BYTES in *. destruct Hdisjfr as [Hd|Hd]; [left; lia | right; lia].
    - (* below stklo <= S - SLOT_STACK < sp - 16: under the window *)
      apply (fsrec_stklo APIf (hb ++ g_H g) mem mem' md [(sp - 16, sp)] fr HAH MU). intros x Hx _. apply HOW. left. lia.
    - (* the input block is below stklo (fra_in_apart): under the window *)
      intros x Hx. destruct (fra_in_apart B APIf ra g fr hb regs mem md HFRA x Hx) as (_ & Hxlo & _ & _).
      apply HOW. left. lia.
    - exact Hfrapp.
    - rewrite Haspz. exact ST.
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split.
  { exact (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRAm
             eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat). }
  assert (HENTm : ENT APIf g hb mem' md).
  { apply (ent_store B APIf ra g fr hb regs mem mem' md [(sp - 16, sp)] HENT HFRA MU).
    - intros x Hx.
      destruct (Z_lt_le_dec x (sp - 16)) as [Hd|Hd]; [left; apply HOW; left; exact Hd|].
      destruct (Z_lt_le_dec x sp) as [Hd2|Hd2]; [right; left; lia | left; apply HOW; right; exact Hd2].
    - exact HSTKeq.
    - exact HSTKHeq.
    - intros a Hia Ho. exact (proj2 (Hownst a) Ho). }
  exact (ent_mat APIf g hb mem' md md' HENTm Hmat).
Qed.

Lemma seg_F20 : forall j,
  Hat B APIf ra (Inv_B82728_at B APIf ra) j -> Hat B APIf ra (Inv_B82668_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & Hr20 & HFM &
    Hs2 & Hs8 & Ha0 & Hphi0 & Hphi50 & Hbig & Rtk & Hblk & Hrec & Hs9 & Hdjphi & Hturn & Hifs &
    v14 & v15 & v16 & v17 & field16 &
    Hfield & Hb14 & Hb15 & Hb16 & Hb17 & Rv14 & Rv15 & Rv16 & Rv17 &
    Hsh14 & Hsh15 & Hsh16 & Hsh17 & Heq1 & Heq2).
  subst c. rewrite SEGS.
  (* [A+280] = fr + 176 (FLI), so the halfword `ld a2,280(s1) ; lhu a2,20(a2)` reads is the cut's u16 at
     fr + 196 (v1.8 read it through s6 = fr + 176) *)
  pose proof HLK as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & S280 & _)).
  replace (fr + 196) with (fr + 176 + 20) in Hfield by lia.
  destruct (f20_fra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
    as (A & sp & HRT & HAH & Hro & Hhalt & Hr2 & Haspz & Hstklo & Hr9 & Hr26 &
        HAS & HspA & HfrA & HA448 & HS4 & HAPP & Hwin).
  unfold FRAME_BYTES in HfrA.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (Esp : bv_unsigned (getr regs 2) = sp)
    by (rewrite Hr2; apply MState.unsigned_lit; unfold APPMEM_END in *; lia).
  pose proof Hdjphi as Hdjphi'. rewrite Haspz in Hdjphi'.
  (* The premises of the checksum contract at its entry 0x83a84 (p = Phi, lo = S - SLOT_STACK, bs = the 32 record
     bytes at Phi + 18). *)
  assert (CK4 : length (t_blk (g_in g) j) = 32%nat) by apply t_blk_len.
  assert (CK6 : LFr.stk rsegs mem (g_S g - AF.SLOT_STACK) (bv_unsigned (getr regs 2))).
  { rewrite Esp. exact (proj1 (LFr.stk_split rsegs mem _ sp _ Hwin ltac:(lia))). }
  assert (CK7 : g_S g - AF.SLOT_STACK + 16 <= bv_unsigned (getr regs 2)) by (rewrite Esp; lia).
  assert (CK8 : phi + 50 <= bv_unsigned (getr regs 2) - 16 \/ bv_unsigned (getr regs 2) <= phi + 18)
    by (rewrite Esp; exact Hdjphi').
  assert (CK9 : asan_cells mem) by exact (RT_cells sp mem md HRT).
  assert (CK10 : shadow_rw mem) by exact (RT_shadow_rw sp mem md HRT).
  assert (CK11 : addressable mem (phi + 18) 32).
  { destruct HHB as (_ & Hphiad). apply (addressable_sub mem phi (AC.a_size (flen g j)) 18 32 Hphiad);
      unfold AC.a_size; lia. }
  assert (CK12 : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            LFr.outside [(bv_unsigned (getr regs 2) - 16, bv_unsigned (getr regs 2))] x).
  { intros x Hx. rewrite Esp. simpl. split; [|exact I].
    unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  pose proof HCKV as HC.
  unfold CKV.reac_ctrl_checksum_verify_contract, CKV.REAC_CTRL_CHECKSUM_VERIFY_FRAME in HC.
  (* The one lazy-model run of this segment (Tac_slot.sl_run).  It reads the record bytes [Phi + 14, Phi + 18),
     their shadow bytes ((Phi + 14 .. 17) >> 3) + 0x7fff8000 and the u16 at fr + 196; in the callee it reads the 32
     bytes [Phi + 18, Phi + 50) with their shadow bytes.  It writes only the callee's 16 bytes [sp - 16, sp). *)
  apply (sl_run regs (Z_to_bv 64 0x82668) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x82728 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = Z_to_bv 64 ASAN_K /\ getr R 18 = Z_to_bv 64 phi /\
       getr R 24 = Z_to_bv 64 (t_k (g_in g) j) /\
       getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 27 = getr regs 27 /\ getr R 25 = getr regs 25 /\
       getr R 10 = Z_to_bv 64 (if RcModel.blocksum (t_blk (g_in g) j) =? 0 then 0 else -1) /\
       LFr.munch [(sp - 16, sp)] mem mem' /\ LFr.wmono rsegs mem mem' /\
       LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) sp)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* expose the register slots and pin the ones this segment reads to their carried values *)
    rewrite mkR_of_expand.
    subst_slot Ha0. subst_slot Hs2. subst_slot Hr9. subst_slot Hs8. subst_slot Hr26.
    pose proof (rd1 mem _ _ Hsh14) as RD14. pose proof (rd1 mem _ _ Hsh15) as RD15.
    pose proof (rd1 mem _ _ Hsh16) as RD16. pose proof (rd1 mem _ _ Hsh17) as RD17.
    pose proof (rd1 mem _ _ Hb14) as RDb14. pose proof (rd1 mem _ _ Hb15) as RDb15.
    pose proof (rd1 mem _ _ Hb16) as RDb16. pose proof (rd1 mem _ _ Hb17) as RDb17.
    pose proof (rd2 mem _ _ Hfield ltac:(apply LMem.length_le2)) as RDfield.
    pose proof (rd8 mem _ _ (spill_q64 regs mem 280 _ A S280 Hr9 ltac:(unfold APPMEM_END in *; lia)
                              ltac:(unfold APPMEM_END in *; lia) ltac:(lia))) as RD280.
    assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply MState.unsigned_lit; lia).
    (* 0x82668 bnez a0 : a0 = 0, not taken *)
    step. if_false.
    (* 0x8266c beqz s2 : the branch to 0x82fa0 is not taken because the cut carries 0 < Phi *)
    step. if_false.
    (* 0x82670 li a0,-15 ; 0x82674 bltu a0,s2 : not taken because Phi + 50 <= 2 ^ 64, so Phi + 14 < 2 ^ 64 *)
    step. step. if_false.
    (* 0x82678 li a0,-16 ; 0x8267c bltu a0,s2 : not taken (Phi + 15 < 2 ^ 64) *)
    step. step. if_false.
    (* 0x82680 addi ; srli ; add ; lb a1 = the shadow byte of Phi + 14, which the cut carries as 0 *)
    step. step. step. rewrite (MState.unsigned_lit (phi + 14)) by lia.
    step.
    (* 0x82690 ld a2,280(s1) = fr + 176 ; 0x82694 lhu a2,20(a2) = field16 ; 0x82698 bnez a1 (= 0) not taken *)
    step. step. step. if_false.
    (* 0x8269c addi ; srli ; add ; lb a3 = the shadow byte of Phi + 15 (0) *)
    step. step. step. rewrite (MState.unsigned_lit (phi + 15)) by lia.
    step.
    (* 0x826ac lbu a0 = v14 ; 0x826b0 bnez a3 (= 0) not taken ; 0x826b4 lbu a1 = v15 ; slli ; or *)
    step. step. if_false. step. step. step.
    (* 0x826c0 bne a0,a2 : (v15 << 8) | v14 = field16, not taken *)
    step. rewrite (cmp16_eq v14 v15 field16 Rv14 Rv15 Heq1), bv_eqb_refl; cbn [negb]; cbv_concl_iota.
    (* 0x826c4 li a0,-17 ; 0x826c8 bltu a0,s2 : not taken (Phi + 16 < 2 ^ 64) *)
    step. step. if_false.
    (* 0x826cc addi ; srli ; add ; lb a1 = the shadow byte of Phi + 16 (0) *)
    step. step. step. rewrite (MState.unsigned_lit (phi + 16)) by lia.
    step.
    (* 0x826dc bnez a1 (= 0) not taken ; 0x826e0 lbu a0 = v16 ; 0x826e4 beqz a0 *)
    step. if_false. step. step. rewrite (zxb8 v16) by lia.
    destruct (Z.eq_dec v16 0) as [Hv16|Hv16].
    + (* v16 = 0 : beqz taken to 0x826f0 *)
      subst v16. rewrite bv_eqb_refl. cbv_concl_iota.
      (* 0x826f0 li a0,-18 ; 0x826f4 bltu a0,s2 : not taken (Phi + 17 < 2 ^ 64) *)
      step. step. if_false.
      (* 0x826f8 addi ; srli ; add ; lb a1 = the shadow byte of Phi + 17 (0) *)
      step. step. step. rewrite (MState.unsigned_lit (phi + 17)) by lia.
      step.
      (* bnez a1 (= 0) ; lbu a0 = v17 ; seqz a0 ; addi a1,s8,-1 ; seqz a1 ; bne (the carried equality) *)
      step. if_false. step. step. step. step. step.
      rewrite (seqz_v17 v17 Rv17), (seqz_vs8 (t_k (g_in g) j) Rtk).
      replace (0 =? 0) with true in Heq2 by reflexivity. cbv iota in Heq2.
      rewrite Heq2, bv_eqb_refl; cbn [negb]; cbv_concl_iota.
      (* 0x82720 mv a0,s2 ; 0x82724 jal reac_ctrl_checksum_verify ; back at 0x82728 *)
      step. step.
      eapply UEx.evt_cut.
      { apply lu_evt. eapply HC with (p := phi) (lo := g_S g - AF.SLOT_STACK) (bs := t_blk (g_in g) j).
        all: first [ reflexivity | assumption ]. }
      intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & Ems & MU & WM & MIi & ST).
      subst ms'. apply UEx.evt_done. cbv beta. do 3 eexists. split; [reflexivity|].
      split; [apply bv_eq; vm_compute; reflexivity|].
      do 15 (split; [reflexivity|]).
      rewrite Esp in MU, ST.
      split; [exact MU|]. split; [exact WM | exact ST].
    + (* v16 <> 0 : beqz not taken, fall to 0x826e8 *)
      rewrite (eqb0_false v16) by lia. cbv_concl_iota.
      (* 0x826e8 li a0,0 ; 0x826ec j 82714 ; 0x82714 addi a1,s8,-1 ; 0x82718 seqz a1 ; 0x8271c bne *)
      step. step. step. step. step.
      rewrite (seqz_vs8 (t_k (g_in g) j) Rtk).
      replace (v16 =? 0) with false in Heq2 by (symmetry; apply Z.eqb_neq; exact Hv16). cbv iota in Heq2.
      rewrite <- Heq2, bv_eqb_refl; cbn [negb]; cbv_concl_iota.
      step. step.
      eapply UEx.evt_cut.
      { apply lu_evt. eapply HC with (p := phi) (lo := g_S g - AF.SLOT_STACK) (bs := t_blk (g_in g) j).
        all: first [ reflexivity | assumption ]. }
      intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & Ems & MU & WM & MIi & ST).
      subst ms'. apply UEx.evt_done. cbv beta. do 3 eexists. split; [reflexivity|].
      split; [apply bv_eq; vm_compute; reflexivity|].
      do 15 (split; [reflexivity|]).
      rewrite Esp in MU, ST.
      split; [exact MU|]. split; [exact WM | exact ST].
  - (* continuation: rebuild the exit cut Inv_B82728_at and apply it *)
    intros R pc' mem' regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er26 & Er18 & Er24 & Er20 & Er21 & Er22 & Er27 & Er25 & Er10 &
       MU & WM & ST')
      Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr26 : getr regs' 26 = getr regs 26)
      by (rewrite Hreg, Er26; unfold rg in Hr26; symmetry; exact Hr26).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr24 : getr regs' 24 = getr regs 24)
      by (rewrite Hreg, Er24; unfold rg in Hs8; symmetry; exact Hs8).
    assert (Easp : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    assert (HOW : forall x, (x < sp - 16 \/ sp <= x) -> LFr.outside [(sp - 16, sp)] x)
      by (intros x Hx; simpl; split; [lia | exact I]).
    assert (Hallapp : all_app [(sp - 16, sp)]).
    { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold APPMEM_END in *. lia. }
    destruct (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
      as (Hfrw & _ & _ & _).
    pose proof (Hfrw 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as Hdisjfr.
    rewrite Haspz in Hdisjfr. unfold FRAME_BYTES in Hdisjfr.
    assert (Hfrout : forall x, fr <= x < fr + 3136 -> x < sp - 16 \/ sp <= x)
      by (intros x Hx; destruct Hdisjfr as [Hd|Hd]; lia).
    assert (HA0 : 0 <= A) by (unfold APPMEM_END in *; lia).
    assert (HA64 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
    destruct (call16_move g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md md' sp
                HFRA HENT Haspz MU WM ST' Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat) as (HFRA' & HENT').
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|].
    split; [exact HENT'|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
      exact (sl_addr_keep mem mem' [(sp - 16, sp)] phi (AC.a_size (flen g j)) Hphiad MU Hallapp). }
    split; [exact (lk_move g fr j regs regs' mem mem' A (sp - 16) sp HLK Hr9 HA0 HA64 HspA Fr9 Fr27
                     MU WM Hallapp ltac:(unfold AF.SLOT_STACK in *; lia) Hfrout)|].
    split; [unfold rg in *; rewrite Fr20; exact Hr20|].
    split; [exact (fm_move g j phi fr regs regs' mem mem' A (sp - 16) sp HFM Hr9 HA0 HA64 HspA Fr9 Fr22 Fr24
                     Fr25 MU)|].
    split; [unfold rg; rewrite Hreg; exact Er10|].
    split; [unfold rg; rewrite Hreg; exact Er18|].
    split; [unfold rg; rewrite Hreg; exact Er24|].
    split; [exact Hphi0|].
    split; [exact Hphi50|].
    split; [exact Hbig|].
    split; [exact Rtk|].
    split.
    { apply (fl_bytes _ mem mem' (phi + 18) (t_blk (g_in g) j) Hblk MU).
      rewrite t_blk_len. intros x Hx. apply HOW. lia. }
    split.
    { apply (fl_bytes _ mem mem' (phi + 34) (bsl (t_g (g_in g) j) 34 6) Hrec MU).
      rewrite bsl_tg_len by lia. intros x Hx. apply HOW.
      change (Z.of_nat (Z.to_nat 6)) with 6 in Hx. lia. }
    split; [unfold rg in *; rewrite Fr25; exact Hs9|].
    split; [rewrite Easp; exact Hdjphi|].
    (* FTURN: Phi's len bytes are a live heap block below stklo <= S - SLOT_STACK < sp - 16 *)
    assert (Hin : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
      by (unfold hb1; cbn; left; reflexivity).
    destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md phi (AC.a_size (flen g j)) HAH Hin)
      as (_ & _ & Hbelow & _).
    assert (Easz : AC.a_size (flen g j) = flen g j)
      by (unfold AC.a_size; rewrite Z.max_l by lia; reflexivity).
    rewrite Easz in Hbelow.
    assert (Hphiout : forall x, phi <= x < phi + t_len (g_in g) j -> x < sp - 16 \/ sp <= x)
      by (intros x Hx; left; unfold flen in *; lia).
    split; [exact (turn_move g j phi regs regs' mem mem' A (sp - 16) sp Hturn Hr9 HA0 HA64 HspA Fr9 MU Hphiout)|].
    exact (ifs_move g fr (S j) regs regs' mem mem' A (sp - 16) sp Hifs Hr9 HA0 HA64 HspA Fr9 MU Hallapp Hfrout).
Qed.

End S.
