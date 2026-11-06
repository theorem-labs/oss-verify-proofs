(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, addresses and numbers changed; 711 of its 753 lines of code are new or changed and 354 lines of the source are left out. *)
(* Segment F21 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B), libreac v1.9.0: the cut-to-cut range
   0x82728 .. 0x827f8 (the 6-turn record sum loop head) / 0x82844 (the return point of the head-amp record call)
   (v1.8: 0x826a4 .. 0x82778 / 0x827c4), the twin of lib/A/Prog/Seg/F21.v.  All three cuts are the official ones of
   lib/B/Prog/SlotInv.v (Inv_B82728_at, Inv_B827f8_at, Inv_B82844_at), used unchanged.
   From the entry cut at 0x82728 (a0 = the checksum call's result):
   - 0x82728-0x8272c the result is compared with s9 - 1 (s9 = the sum flag b2z (t_sum_ok j), FM; v1.8 loaded it
     from the spill [s1 + 288]) and the branch to 0x82fa4 is shown NOT taken (the flag is "the block sum of the 32
     record bytes is 0", which is what the callee returns);
   - 0x82730-0x82784 when s8 = k = 6 the record bytes Phi[18] / Phi[19] are 4 / 3, so those two compares do not
     branch either;
   - 0x82788-0x827f4 the bytes are read once more, s7 := -1, and either the block falls through to the sum loop
     head 0x827f8 (exit 1, with a0 = 0 the turn index, a1 = 0 the sum, a2 = Phi + 34, a3 = ~(Phi + 34), a7 = 6) or,
     when a byte differs, branches to 0x8283c `mv a0,s2` / 0x82840 `jal reac_ctrl_headamp_record_verify`
     (Section Hypothesis HHRV) and lands at 0x82844 (exit 2) with a0 = s7 = -1 = t_want_v.
   Every one-byte load is preceded by the instrumented check (a load of the shadow byte at (a >> 3) + 0x7fff8000
   and a compare); the shadow byte is 0 because Phi is 16-aligned and the granule of the byte lies inside the
   addressable block (shadow_ok at the granule's last byte forces 0), so the error path is not reached.
   The arithmetic-check compares `bltu a0,s2,82fa0` with a0 = -19 / -20 / -19 / -20 / -35: each branch to the trap
   routine at 0x82fa0 is not taken because the cut carries Phi + 50 <= 2 ^ 64, so Phi + 18, Phi + 19 and Phi + 34
   stay below 2 ^ 64.
   The run is one B.Tk.UL run (Tac_slot.sl_run); the callee contract speaks the Lib engine, carried over by
   lu_evt.  On exit 1 no memory changes (Tac_slot.sl_fra_move / ent_mat); on exit 2 FRA and ENT move across the
   callee's 16-byte window [sp - 16, sp) by Tac_slot.sl_win_run / ent_store, whose ro_agree premise comes from
   FRA's ro_agree, whose AH / stklo premises come from AC.a_laws_store and whose below-stklo premise comes from
   FRA's stklo <= S - SLOT_STACK < sp - 16.  The frame-loop bundles LK (with FLI) and FM move by lk_move /
   fm_move on both exits (exit 1 with the empty change): their spills lie at or above the spill base A >= sp,
   our[] and the frame body [fr, fr + 3136) miss the window (fra_frame).  No cut carries mem_inv. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require reac_ctrl_headamp_record_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel RcLeaf.
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
Module HRV := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_headamp_record_verify_c.

(* A Lib.Exec run is a UL run: the two step relations have the same body. *)
Lemma lu_msteps : forall s s', LEx.msteps rsegs s s' -> UEx.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UEx.msteps_refl|].
  eapply UEx.msteps_cons; [exact Hs | exact IH].
Qed.
Lemma lu_evt : forall Q ms, LEx.evt rsegs Q ms -> UEx.evt rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (lu_msteps _ _ H) | exact HQ]. Qed.

(* ---- Read facts in the `ov_read_bytes _ _ (wa a) n = Some bs` form the UL `step` consumes. ---- *)
Lemma rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (ULMem.wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma rd8 : forall m a v, q64 m a v -> ov_read_bytes rsegs m (ULMem.wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold q64 in H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite ULMem.length_le8; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH.
  rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite ULMem.length_le8; lia).
  exact HH.
Qed.
Lemma zxb8 : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; cbn; lia.
Qed.
Lemma ubyte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H. exact H. Qed.

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

(* ---- The model facts the segment reads. ---- *)
Lemma f21_nth_firstn : forall (l : list byte) N i d, (i < N)%nat -> nth i (firstn N l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros N i d Hi.
  - rewrite firstn_nil. reflexivity.
  - destruct N as [|N]; [lia|]. destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.
Lemma f21_nth_skipn : forall (l : list byte) K i d, nth i (skipn K l) d = nth (K + i) l d.
Proof.
  induction l as [|x l IH]; intros K i d.
  - rewrite skipn_nil, !nth_overflow by (cbn; lia). reflexivity.
  - destruct K as [|K]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma bsl_nth : forall g k n i, (i < Z.to_nat n)%nat ->
  nth i (bsl g k n) cp_z = nth (Z.to_nat k + i) g cp_z.
Proof. intros g k n i Hi. unfold bsl. rewrite f21_nth_firstn by exact Hi. apply f21_nth_skipn. Qed.
Lemma t_g_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.
Lemma bsl_tg_len : forall inp j k n, 0 <= k -> 0 <= n -> k + n <= 50 ->
  length (bsl (t_g inp j) k n) = Z.to_nat n.
Proof.
  intros inp j k n Hk Hn Hkn. unfold bsl. rewrite length_firstn, length_skipn, t_g_len. lia.
Qed.
Lemma t_blk_len : forall inp j, length (t_blk inp j) = 32%nat.
Proof. intros inp j. unfold t_blk. rewrite bsl_tg_len by lia. reflexivity. Qed.
Lemma t_blk_skip : forall inp j, t_blk inp j = skipn 18 (t_g inp j).
Proof.
  intros inp j. unfold t_blk, bsl. change (Z.to_nat 18) with 18%nat. change (Z.to_nat 32) with 32%nat.
  apply firstn_all2. rewrite length_skipn, t_g_len. lia.
Qed.
(* The checksum result (0 when the block sum of the 32 block bytes is 0, else -1) is the sum flag minus 1. *)
Lemma ckv_eq : forall inp j, 50 <= t_len inp j ->
  (if RcModel.blocksum (t_blk inp j) =? 0 then 0 else -1) = b2z (t_sum_ok inp j) + -1.
Proof.
  intros inp j H. unfold b2z, t_sum_ok, t_big. rewrite (proj2 (Z.leb_le 50 _) H), t_blk_skip. cbn [andb].
  destruct (RcModel.blocksum (skipn 18 (t_g inp j)) =? 0); reflexivity.
Qed.
Lemma sumok_range : forall inp j, 0 <= b2z (t_sum_ok inp j) <= 1.
Proof. intros inp j. unfold b2z. destruct (t_sum_ok inp j); lia. Qed.
(* k = 6 (headamp) carries the record type bytes 4 / 3 at g[18], g[19]. *)
Lemma k6_rec : forall inp j, t_k inp j = 6 -> cp_v (t_g inp j) 18 = 4 /\ cp_v (t_g inp j) 19 = 3.
Proof.
  intros inp j H. unfold t_k in H. apply ctrlparse_headamp in H. destruct H as (_ & Hr & _).
  unfold cp_rec in Hr. apply andb_prop in Hr as [Hr H19]. apply andb_prop in Hr as [_ H18].
  apply Z.eqb_eq in H18, H19. split; assumption.
Qed.
(* When the record bytes are not 4 / 3 the head-amp want value is -1. *)
Lemma want_m1 : forall inp j, cp_v (t_g inp j) 18 <> 4 \/ cp_v (t_g inp j) 19 <> 3 -> t_want_v inp j = -1.
Proof.
  intros inp j H. unfold t_want_v, RcLeaf.hv. unfold cp_v in H.
  destruct H as [H|H].
  - rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. reflexivity.
Qed.
(* The i-th byte of the 32 block bytes at Phi + 18 is g[18 + i]. *)
Lemma blk_b8 : forall m phi inp j i x n, (i < 32)%nat -> x = phi + 18 + Z.of_nat i -> n = (18 + i)%nat ->
  LMem.bytes_at rsegs m (phi + 18) (t_blk inp j) -> b8 m x (cp_v (t_g inp j) n).
Proof.
  intros m phi inp j i x n Hi -> -> (H0 & H1 & H2).
  unfold b8, LMem.bytes_at. cbn [length].
  rewrite t_blk_len in H1.
  split; [lia|]. split; [lia|]. intros i' Hi'. destruct i' as [|i']; [|cbn in Hi'; lia]. cbn [nth_error].
  change (Z.of_nat 0) with 0%Z. rewrite Z.add_0_r.
  unfold cp_v, cp_b, cp_z. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned.
  rewrite (H2 i) by (rewrite t_blk_len; exact Hi).
  replace (nth (18 + i) (t_g inp j) (Z_to_bv 8 0)) with (nth i (bsl (t_g inp j) 18 32) (Z_to_bv 8 0))
    by (rewrite bsl_nth by (cbn; lia); reflexivity).
  unfold t_blk. apply nth_error_nth'. unfold bsl.
  rewrite length_firstn, length_skipn, t_g_len. cbn. lia.
Qed.
(* The first two of the 32 block bytes, as the head-amp contract reads them. *)
Lemma blk_pre2 : forall m phi inp j, LMem.bytes_at rsegs m (phi + 18) (t_blk inp j) ->
  LMem.bytes_at rsegs m (phi + 18) [cp_b (t_g inp j) 18; cp_b (t_g inp j) 19].
Proof.
  intros m phi inp j (H0 & H1 & H2). rewrite t_blk_len in H1.
  split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  assert (Enth : forall i', (i' < 32)%nat -> nth_error (t_blk inp j) i' = Some (cp_b (t_g inp j) (18 + i'))).
  { intros i' Hi'. unfold cp_b, t_blk.
    replace (nth (18 + i') (t_g inp j) cp_z) with (nth i' (bsl (t_g inp j) 18 32) cp_z)
      by (rewrite bsl_nth by (cbn; lia); reflexivity).
    apply nth_error_nth'. unfold bsl. rewrite length_firstn, length_skipn, t_g_len. cbn. lia. }
  destruct i as [|[|i]]; try (cbn in Hi; lia).
  - rewrite (H2 0%nat) by (rewrite t_blk_len; lia). rewrite (Enth 0%nat) by lia. reflexivity.
  - rewrite (H2 1%nat) by (rewrite t_blk_len; lia). rewrite (Enth 1%nat) by lia. reflexivity.
Qed.

(* A zero shadow byte for the granule of p + t: p is 8-aligned and the granule's last byte p + 8(t/8) + 7 is in
   the addressable range, where shadow_ok with offset 7 forces the shadow byte to be 0. *)
Lemma sh0 : forall m p L t, addressable m p L -> p mod 8 = 0 -> 0 <= t -> 8 * (t / 8) + 8 <= L ->
  b8 m (Z.shiftr (p + t) 3 + ASAN_K) 0.
Proof.
  intros m p L t (Hp0 & HL0 & HLe & HA) Hpm Ht HtL.
  pose proof (Z.div_pos t 8 Ht ltac:(lia)) as Ht8.
  pose proof (Z.mul_div_le t 8 ltac:(lia)) as Htd.
  destruct (HA (8 * (t / 8) + 7) ltac:(lia)) as (Happ & b & Hb & Hok).
  assert (Ep : p = 8 * (p / 8)) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
  assert (Hm7 : (p + (8 * (t / 8) + 7)) mod 8 = 7).
  { replace (p + (8 * (t / 8) + 7)) with (7 + (p / 8 + t / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  unfold shadow_ok in Hok. rewrite Hm7 in Hok.
  assert (Hs : bv_signed b = 0) by lia.
  assert (Eb : b = Z_to_bv 8 0).
  { apply bv_eq_signed. rewrite Hs. reflexivity. }
  assert (EX : Z.shiftr (p + t) 3 + ASAN_K = shadow_addr (p + (8 * (t / 8) + 7))).
  { unfold shadow_addr. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. f_equal.
    replace (p + (8 * (t / 8) + 7)) with (7 + (p / 8 + t / 8) * 8) by lia.
    replace (p + t) with (t + (p / 8) * 8) by lia.
    rewrite !Z.div_add by lia. change (7 / 8) with 0. lia. }
  unfold b8, LMem.bytes_at. cbn [length].
  assert (Hlo : 0 <= Z.shiftr (p + t) 3) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
  assert (Hhi : Z.shiftr (p + t) 3 < 2 ^ 61).
  { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [lia|]. unfold APPMEM_END in HLe. lia. }
  split; [unfold ASAN_K; lia|]. split; [unfold ASAN_K; lia|].
  intros i Hi. destruct i as [|i]; [|cbn in Hi; lia]. cbn [nth_error]. change (Z.of_nat 0) with 0.
  rewrite Z.add_0_r, EX. rewrite Eb in Hb. exact Hb.
Qed.

(* `not a3,a2` (xori a3,a2,-1) on a2 = Phi + 34: the bitwise complement within 64 bits, 2^64 - (Phi + 35). *)
Lemma lxor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (Z.ones 64) = Z.lnot x mod 2 ^ 64.
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec.
  destruct (Z.lt_ge_cases i 64) as [Hl|Hg].
  - rewrite Z.ones_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
    destruct (Z.testbit x i); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite Z.mod_pow2_bits_high by lia.
    rewrite <- (Z.mod_small x (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma f21_not : forall x, 0 <= x < 2 ^ 64 ->
  Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615) = Z_to_bv 64 (2 ^ 64 - (x + 1)).
Proof.
  intros x Hx. rewrite (MState.unsigned_lit x) by lia.
  change 18446744073709551615 with (Z.ones 64). rewrite lxor_ones64 by lia.
  f_equal. unfold Z.lnot. rewrite <- Z.sub_1_r. symmetry. apply (Z.mod_unique _ _ (-1)); [left; lia | lia].
Qed.

(* A spill read through s1 survives a register change that keeps s1. *)
Lemma spill_reg : forall regs regs' m off v, getr regs' 9 = getr regs 9 -> spill regs m off v -> spill regs' m off v.
Proof. intros regs regs' m off v E (A & HA & Hq). exists A. split; [unfold rg in *; rewrite E; exact HA | exact Hq]. Qed.
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
  intros g fr j regs regs' m m' A lo hi (Hj & H232 & HOUR & HFLI) HA HA0 HA1 Hhi E9 E27 MU WM HAW Hlo Hfr.
  assert (SK : forall off v, 0 <= off <= 440 -> spill regs m off v -> spill regs' m' off v)
    by (intros off v Hoff Hs; exact (spill_keep regs regs' m m' off v A lo hi Hs HA E9 Hoff HA0 HA1
                                       ltac:(lia) MU)).
  split; [exact Hj|]. split; [apply SK; [lia | exact H232]|].
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
      apply (rl_next_length 1 1 1 1 1); solve [exact IH | apply t_g_len].
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
  rewrite length_firstn, length_skipn, t_g_len. lia.
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
(* After `srli x,a,3` on a = Phi + c: expose the unsigned value of the literal word. *)
Ltac ush := match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3] => rewrite (MState.unsigned_lit X) by lia
  end.
(* After `lbu`: the zero-extended byte as a word literal. *)
Ltac zx := match goal with
  | |- context [zxb (Z_to_bv 8 ?v)] => rewrite (zxb8 v) by lia
  end.
Ltac bvlit := first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
(* The a3 slot after `not a3,a2` with a2 = Phi + 34. *)
Ltac a3_not phi :=
  transitivity (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (phi + 34))) 18446744073709551615));
  [reflexivity | rewrite f21_not by lia; f_equal; lia].

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract of reac_ctrl_headamp_record_verify (lib/B/Prog/reac_ctrl_headamp_record_verify_c.v). *)
Hypothesis HHRV : HRV.reac_ctrl_headamp_record_verify_contract.

(* The FRA facts this segment reads, by name (tauto), not by position. *)
Lemma f21_fra : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
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
  destruct (f21_fra g fr hb regs mem md HFRA)
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

Lemma seg_F21 : forall j,
  Hat B APIf ra (Inv_B827f8_at B APIf ra) j -> Hat B APIf ra (Inv_B82844_at B APIf ra) j ->
  Hat B APIf ra (Inv_B82728_at B APIf ra) j.
Proof.
  intros j Hloop Hver g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & Hr20 & HFM &
    Ha0 & Hs2 & Hs8 & Hphi0 & Hphi50 & Hbig & Rtk & Hblk & Hrec & Hs9 & Hdjphi & Hturn & Hifs).
  subst c. rewrite SEGS.
  destruct (f21_fra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
    as (A & sp & HRT & HAH & Hro & Hhalt & Hr2 & Haspz & Hstklo & Hr9 & Hr26 &
        HAS & HspA & HfrA & HA448 & HS4 & HAPP & Hwin).
  unfold FRAME_BYTES in HfrA.
  pose proof (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGTfr & Hfrapp).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (Esp : bv_unsigned (getr regs 2) = sp)
    by (rewrite Hr2; apply MState.unsigned_lit; unfold APPMEM_END in *; lia).
  pose proof Hdjphi as Hdjphi'. rewrite Haspz in Hdjphi'.
  (* Phi is 16-aligned (a block of the live heap), so 8-aligned *)
  assert (Hin : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (unfold hb1; cbn; left; reflexivity).
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md phi (AC.a_size (flen g j)) HAH Hin)
    as (Hal16 & _ & Hbelow & _).
  (* Phi's len bytes are a live heap block below stklo <= S - SLOT_STACK < sp - 16 (FTURN's transport) *)
  assert (Hphiout : forall x, phi <= x < phi + t_len (g_in g) j -> x < sp - 16 \/ sp <= x).
  { intros x Hx. left. unfold AC.a_size in Hbelow. rewrite Z.max_l in Hbelow by lia. unfold flen in *. lia. }
  assert (Hal8 : phi mod 8 = 0).
  { assert (Ep : phi = 16 * (phi / 16)) by (pose proof (Z.div_mod phi 16 ltac:(lia)); lia).
    rewrite Ep. replace (16 * (phi / 16)) with (0 + (2 * (phi / 16)) * 8) by lia. rewrite Z.mod_add by lia.
    reflexivity. }
  pose proof HHB as (Hphinz & Hadr). unfold AC.a_size in Hadr. rewrite Z.max_l in Hadr by lia.
  (* the shadow bytes of the record granules are 0 *)
  pose proof (sh0 mem phi (flen g j) 18 Hadr Hal8 ltac:(lia) ltac:(change (8 * (18 / 8) + 8) with 24; lia)) as Sh18.
  pose proof (sh0 mem phi (flen g j) 19 Hadr Hal8 ltac:(lia) ltac:(change (8 * (19 / 8) + 8) with 24; lia)) as Sh19.
  assert (Sh34 : forall i, 0 <= i < 6 -> b8 mem (Z.shiftr (phi + 34 + i) 3 + ASAN_K) 0).
  { intros i Hi. rewrite <- Z.add_assoc. apply (sh0 mem phi (flen g j) (34 + i) Hadr Hal8); [lia|].
    pose proof (Z.mul_div_le (34 + i) 8 ltac:(lia)). lia. }
  (* the record bytes Phi[18], Phi[19] *)
  pose proof (blk_b8 mem phi (g_in g) j 0 (phi + 18) 18 ltac:(lia) ltac:(lia) eq_refl Hblk) as Hy0.
  pose proof (blk_b8 mem phi (g_in g) j 1 (phi + 19) 19 ltac:(lia) ltac:(cbn; lia) eq_refl Hblk) as Hy1.
  pose proof (ubyte (cp_b (t_g (g_in g) j) 18)) as Ry0. pose proof (ubyte (cp_b (t_g (g_in g) j) 19)) as Ry1.
  fold (cp_v (t_g (g_in g) j) 18) in Ry0. fold (cp_v (t_g (g_in g) j) 19) in Ry1.
  (* the premises of the head-amp record contract at its entry 0x857d4 *)
  assert (HV2 : LMem.bytes_at rsegs mem (phi + 18) [cp_b (t_g (g_in g) j) 18; cp_b (t_g (g_in g) j) 19])
    by exact (blk_pre2 mem phi (g_in g) j Hblk).
  assert (HV3 : length (bsl (t_g (g_in g) j) 34 6) = 6%nat) by (rewrite bsl_tg_len by lia; reflexivity).
  assert (HV6 : LFr.stk rsegs mem (g_S g - AF.SLOT_STACK) (bv_unsigned (getr regs 2))).
  { rewrite Esp. exact (proj1 (LFr.stk_split rsegs mem _ sp _ Hwin ltac:(lia))). }
  assert (HV7 : g_S g - AF.SLOT_STACK + 16 <= bv_unsigned (getr regs 2)) by (rewrite Esp; lia).
  assert (HV8 : phi + 20 <= bv_unsigned (getr regs 2) - 16 \/ bv_unsigned (getr regs 2) <= phi + 18)
    by (rewrite Esp; destruct Hdjphi' as [Hd|Hd]; [left; lia | right; lia]).
  assert (HV9 : phi + 40 <= bv_unsigned (getr regs 2) - 16 \/ bv_unsigned (getr regs 2) <= phi + 34)
    by (rewrite Esp; destruct Hdjphi' as [Hd|Hd]; [left; lia | right; lia]).
  assert (HV10 : asan_cells mem) by exact (RT_cells sp mem md HRT).
  assert (HV11 : shadow_rw mem) by exact (RT_shadow_rw sp mem md HRT).
  assert (HV12 : addressable mem (phi + 18) 2)
    by (apply (addressable_sub mem phi (flen g j) 18 2 Hadr); lia).
  assert (HV13 : addressable mem (phi + 34) 6)
    by (apply (addressable_sub mem phi (flen g j) 34 6 Hadr); lia).
  assert (HV14 : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            LFr.outside [(bv_unsigned (getr regs 2) - 16, bv_unsigned (getr regs 2))] x).
  { intros x Hx. rewrite Esp. simpl. split; [|exact I].
    unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  assert (HV15 : phi + 40 <= 2 ^ 64) by lia.
  pose proof HHRV as HV.
  unfold HRV.reac_ctrl_headamp_record_verify_contract, HRV.REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME in HV.
  remember (cp_v (t_g (g_in g) j) 18) as y0 eqn:Ey0.
  remember (cp_v (t_g (g_in g) j) 19) as y1 eqn:Ey1.
  (* the sum flag s9 (v1.8: the spill [s1 + 288]) and the checksum result it is compared with *)
  pose proof (sumok_range (g_in g) j) as Rsv.
  rewrite (ckv_eq (g_in g) j Hbig) in Ha0.
  remember (b2z (t_sum_ok (g_in g) j)) as sv eqn:Esv.
  remember (t_k (g_in g) j) as k eqn:Ek.
  pose proof (rd1 mem _ _ Sh18) as RS18. pose proof (rd1 mem _ _ Sh19) as RS19.
  pose proof (rd1 mem _ _ Hy0) as RY0. pose proof (rd1 mem _ _ Hy1) as RY1.
  assert (Uphi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply MState.unsigned_lit; lia).
  assert (Uk : bv_unsigned (Z_to_bv 64 k) = k) by (apply MState.unsigned_lit; lia).
  assert (Uy0 : bv_unsigned (Z_to_bv 64 y0) = y0) by (apply MState.unsigned_lit; lia).
  assert (Uy1 : bv_unsigned (Z_to_bv 64 y1) = y1) by (apply MState.unsigned_lit; lia).
  (* The one lazy-model run of this segment (Tac_slot.sl_run).  It reads the record bytes Phi + 18 and Phi + 19
     and their shadow bytes; on the second arm the callee reads the two record bytes and the six bytes at Phi + 34
     and writes only its own 16 bytes [sp - 16, sp). *)
  apply (sl_run regs (Z_to_bv 64 0x82728) mem md
    (fun R pc' mem' =>
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 27 = getr regs 27 /\ getr R 25 = getr regs 25 /\
       ((pc' = Z_to_bv 64 0x827f8 /\ mem' = mem /\ y0 = 4 /\ y1 = 3 /\
         getr R 10 = Z_to_bv 64 0 /\ getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 (phi + 34) /\
         getr R 13 = Z_to_bv 64 (2 ^ 64 - (phi + 35)) /\ getr R 17 = Z_to_bv 64 6) \/
        (pc' = Z_to_bv 64 0x82844 /\ (y0 <> 4 \/ y1 <> 3) /\
         getr R 23 = Z_to_bv 64 (-1) /\
         getr R 10 = Z_to_bv 64 (t_want_v (g_in g) j) /\
         LFr.munch [(sp - 16, sp)] mem mem' /\ LFr.wmono rsegs mem mem' /\
         LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) sp)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite mkR_of_expand.
    subst_slot Ha0. subst_slot Hs2. subst_slot Hs8. subst_slot Hr9. subst_slot Hr26. subst_slot Hs9.
    (* 0x82728 addi a1,s9,-1 ; bne a0,a1,82fa4 (equal: not taken) *)
    step. step. if_false.
    (* 0x82730 li a0,6 ; bne s8,a0,82788 *)
    step. step.
    destruct (Z.eq_dec k 6) as [Ek6|Nk6].
    + (* k = 6: the record bytes are 4 / 3 *)
      assert (E43 : y0 = 4 /\ y1 = 3) by (subst y0 y1 k; apply k6_rec; exact Ek6).
      destruct E43 as [E4 E3]. rewrite E4 in RY0. rewrite E3 in RY1. rewrite Ek6. if_false.
      (* 0x82738 li a0,-19 ; bltu a0,s2 : not taken (Phi + 18 < 2 ^ 64) *)
      step. step. if_false.
      (* addi a0,s2,18 ; srli ; add ; lb = the shadow byte of Phi + 18 (0) ; bnez (not taken) *)
      step. step. ush. step. step. step. if_false.
      (* lbu a0 = 4 ; li a1,4 ; bne a0,a1,82fa4 (not taken) *)
      step. zx. step. step. if_false.
      (* 0x82760 li a0,-20 ; bltu a0,s2 : not taken (Phi + 19 < 2 ^ 64) *)
      step. step. if_false.
      step. step. ush. step. step. step. if_false.
      (* lbu a0 = 3 ; li a1,3 ; bne a0,a1,82fa4 (not taken) *)
      step. zx. step. step. if_false.
      (* 0x82788 li a0,-19 ; bltu a0,s2 : not taken *)
      step. step. if_false.
      step. step. ush. step. step. step. if_false.
      (* lbu a0 = 4 ; li s7,-1 ; li a1,4 ; bne a0,a1,8283c (not taken) *)
      step. zx. step. step. step. if_false.
      (* 0x827b4 li a0,-20 ; bltu a0,s2 : not taken *)
      step. step. if_false.
      step. step. ush. step. step. step. if_false.
      (* lbu a0 = 3 ; li a1,3 ; bne a0,a1,8283c (not taken) *)
      step. zx. step. step. if_false.
      (* 0x827dc li a0,-35 ; bltu a0,s2 : not taken (Phi + 34 < 2 ^ 64) *)
      step. step. if_false.
      (* li a0,0 ; li a1,0 ; addi a2,s2,34 ; not a3,a2 ; li a7,6 : the loop head 0x827f8 *)
      step. step. step. step. step.
      apply UEx.evt_done. cbv beta. do 3 eexists. split; [reflexivity|].
      do 14 (split; [reflexivity|]).
      left.
      split; [bvlit|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
      split; [bvlit|]. split; [bvlit|]. split; [bvlit|].
      split; [a3_not phi|]. bvlit.
    + (* k <> 6 *)
      if_true.
      (* 0x82788 li a0,-19 ; bltu a0,s2 : not taken (Phi + 18 < 2 ^ 64) *)
      step. step. if_false.
      (* addi a0,s2,18 ; srli ; add ; lb = the shadow byte of Phi + 18 (0) ; bnez (not taken) *)
      step. step. ush. step. step. step. if_false.
      (* lbu a0 = y0 ; li s7,-1 ; li a1,4 ; bne a0,a1,8283c *)
      step. zx. step. step. step.
      destruct (Z.eq_dec y0 4) as [E4|N4].
      2: { if_true.
           (* 0x8283c mv a0,s2 ; 0x82840 jal reac_ctrl_headamp_record_verify ; back at 0x82844 *)
           step. step.
           eapply UEx.evt_cut.
           { apply lu_evt.
             eapply HV with (p := phi) (lo := g_S g - AF.SLOT_STACK)
               (b0 := cp_b (t_g (g_in g) j) 18) (b1 := cp_b (t_g (g_in g) j) 19)
               (rec := bsl (t_g (g_in g) j) 34 6).
             all: first [ reflexivity | assumption ]. }
           intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & Ems & MU & WM & MIi & ST).
           subst ms'. apply UEx.evt_done. cbv beta. do 3 eexists.
           do 15 (split; [reflexivity|]).
           right.
           split; [apply bv_eq; vm_compute; reflexivity|].
           split; [left; exact N4|].
           split; [bvlit|].
           split; [unfold t_want_v; reflexivity|].
           rewrite Esp in MU, ST.
           split; [exact MU|]. split; [exact WM | exact ST]. }
      rewrite E4. if_false.
      (* 0x827b4 li a0,-20 ; bltu a0,s2 : not taken (Phi + 19 < 2 ^ 64) *)
      step. step. if_false.
      step. step. ush. step. step. step. if_false.
      (* lbu a0 = y1 ; li a1,3 ; bne a0,a1,8283c *)
      step. zx. step. step.
      destruct (Z.eq_dec y1 3) as [E3|N3].
      2: { if_true.
           step. step.
           eapply UEx.evt_cut.
           { apply lu_evt.
             eapply HV with (p := phi) (lo := g_S g - AF.SLOT_STACK)
               (b0 := cp_b (t_g (g_in g) j) 18) (b1 := cp_b (t_g (g_in g) j) 19)
               (rec := bsl (t_g (g_in g) j) 34 6).
             all: first [ reflexivity | assumption ]. }
           intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & Ems & MU & WM & MIi & ST).
           subst ms'. apply UEx.evt_done. cbv beta. do 3 eexists.
           do 15 (split; [reflexivity|]).
           right.
           split; [apply bv_eq; vm_compute; reflexivity|].
           split; [right; exact N3|].
           split; [bvlit|].
           split; [unfold t_want_v; reflexivity|].
           rewrite Esp in MU, ST.
           split; [exact MU|]. split; [exact WM | exact ST]. }
      rewrite E3. if_false.
      (* 0x827dc li a0,-35 ; bltu a0,s2 : not taken (Phi + 34 < 2 ^ 64) *)
      step. step. if_false.
      (* li a0,0 ; li a1,0 ; addi a2,s2,34 ; not a3,a2 ; li a7,6 : the loop head 0x827f8 *)
      step. step. step. step. step.
      apply UEx.evt_done. cbv beta. do 3 eexists. split; [reflexivity|].
      do 14 (split; [reflexivity|]).
      left.
      split; [bvlit|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
      split; [bvlit|]. split; [bvlit|]. split; [bvlit|].
      split; [a3_not phi|]. bvlit.
  - (* continuation: rebuild the exit cut the arm reached and apply it *)
    intros R pc' mem' regs' md'
      (E2 & E3 & E4 & E8 & E9 & E19 & E26 & E18 & E24 & E20 & E21 & E22 & E27 & E25 & Hex) Hreg Hmat.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact E27).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (Easp : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    assert (Hs2' : rg regs' 18 phi) by (unfold rg in *; rewrite Fr18; exact Hs2).
    assert (Hs8' : rg regs' 24 k) by (unfold rg in *; rewrite Fr24; exact Hs8).
    assert (HOW : forall x, (x < sp - 16 \/ sp <= x) -> LFr.outside [(sp - 16, sp)] x)
      by (intros x Hx; simpl; split; [lia | exact I]).
    assert (Hr20' : rg regs' 20 (flen g j)) by (unfold rg in *; rewrite Fr20; exact Hr20).
    assert (Hallapp : all_app [(sp - 16, sp)]).
    { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold APPMEM_END in *. lia. }
    destruct (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
      as (Hfrw & _ & _ & _).
    pose proof (Hfrw 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as Hdisjfr. rewrite Haspz in Hdisjfr.
    unfold FRAME_BYTES in Hdisjfr.
    assert (Hfrout : forall x, fr <= x < fr + 3136 -> x < sp - 16 \/ sp <= x)
      by (intros x Hx; destruct Hdisjfr as [Hd|Hd]; lia).
    assert (HA0 : 0 <= A) by (unfold APPMEM_END in *; lia).
    assert (HA64 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
    rewrite <- SEGS.
    destruct Hex as [(Hpc & Hm & Hy0e & Hy1e & E10 & E11 & E12 & E13 & E17)
                    |(Hpc & Hy01 & E23 & E10 & MU & WM & ST')]; subst pc'.
    + (* exit 1: the sum loop head 0x827f8, no memory change *) subst mem'.
      assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem md')
        by exact (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat).
      assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md')
        by exact (ent_mat APIf g _ mem md md' HENT Hmat).
      assert (HLK' : LK g fr j regs' mem)
        by exact (lk_move g fr j regs regs' mem mem A (sp - 16) sp HLK Hr9 HA0 HA64 HspA Fr9 Fr27
                    (LFr.munch_refl _ _) (LFr.wmono_refl rsegs mem) Hallapp
                    ltac:(unfold AF.SLOT_STACK in *; lia) Hfrout).
      assert (HFM' : FM g j phi fr regs' mem)
        by exact (fm_move g j phi fr regs regs' mem mem A (sp - 16) sp HFM Hr9 HA0 HA64 HspA Fr9 Fr22 Fr24
                    Fr25 (LFr.munch_refl _ _)).
      apply Hloop. exists phi, regs', mem, md', fr.
      split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HLK'|].
      split; [exact Hr20'|]. split; [exact HFM'|].
      split; [unfold rg; rewrite Hreg; exact E10|].
      split; [unfold rg; rewrite Hreg; exact E11|].
      split; [unfold rg; rewrite Hreg; exact E12|].
      split; [unfold rg; rewrite Hreg; exact E13|].
      split; [unfold rg; rewrite Hreg; exact E17|].
      split; [exact Hs2'|]. split; [subst k; exact Hs8'|].
      split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hbig|]. split; [subst k; exact Rtk|].
      split; [subst y0; exact Hy0e|]. split; [subst y1; exact Hy1e|].
      split; [exact Hblk|]. split; [exact Hrec|]. split; [exact Sh34|].
      split; [subst sv; unfold rg in *; rewrite Fr25; exact Hs9|].
      split; [exact Hfrapp|].
      split; [rewrite Easp; exact Hdjphi|].
      split; [exact (turn_move g j phi regs regs' mem mem A (sp - 16) sp Hturn Hr9 HA0 HA64 HspA Fr9
                       (LFr.munch_refl _ _) Hphiout)|].
      exact (ifs_move g fr (S j) regs regs' mem mem A (sp - 16) sp Hifs Hr9 HA0 HA64 HspA Fr9
               (LFr.munch_refl _ _) Hallapp Hfrout).
    + (* exit 2: the record call returned at 0x82844, the callee wrote only [sp - 16, sp) *)
      destruct (call16_move g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md md' sp
                  HFRA HENT Haspz MU WM ST' Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat) as (HFRA' & HENT').
      assert (Ewant : t_want_v (g_in g) j = -1) by (apply want_m1; subst y0 y1; exact Hy01).
      apply Hver. exists phi, regs', mem', md', fr.
      split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|]. split; [exact Hj|].
      split.
      { split; [exact Hphinz|].
        exact (sl_addr_keep mem mem' [(sp - 16, sp)] phi (AC.a_size (flen g j)) (proj2 HHB) MU Hallapp). }
      split; [exact (lk_move g fr j regs regs' mem mem' A (sp - 16) sp HLK Hr9 HA0 HA64 HspA Fr9 Fr27
                       MU WM Hallapp ltac:(unfold AF.SLOT_STACK in *; lia) Hfrout)|].
      split; [exact Hr20'|].
      split; [exact (fm_move g j phi fr regs regs' mem mem' A (sp - 16) sp HFM Hr9 HA0 HA64 HspA Fr9 Fr22 Fr24
                       Fr25 MU)|].
      split; [unfold rg; rewrite Hreg, E10; rewrite Ewant; reflexivity|].
      split; [exact Hs2'|].
      split; [unfold rg; rewrite Hreg, E23, Ewant; reflexivity|].
      split; [subst k; exact Hs8'|].
      split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hbig|]. split; [subst k; exact Rtk|].
      split.
      { apply (fl_bytes _ mem mem' (phi + 18) (t_blk (g_in g) j) Hblk MU).
        rewrite t_blk_len. intros x Hx. apply HOW. lia. }
      split.
      { apply (fl_bytes _ mem mem' (phi + 34) (bsl (t_g (g_in g) j) 34 6) Hrec MU).
        rewrite bsl_tg_len by lia. intros x Hx. apply HOW.
        change (Z.of_nat (Z.to_nat 6)) with 6 in Hx. lia. }
      split; [subst sv; unfold rg in *; rewrite Fr25; exact Hs9|].
      split; [exact Hfrapp|].
      split; [rewrite Easp; exact Hdjphi|].
      split; [exact (turn_move g j phi regs regs' mem mem' A (sp - 16) sp Hturn Hr9 HA0 HA64 HspA Fr9 MU
                       Hphiout)|].
      exact (ifs_move g fr (S j) regs regs' mem mem' A (sp - 16) sp Hifs Hr9 HA0 HA64 HspA Fr9 MU Hallapp Hfrout).
Qed.

End S.
