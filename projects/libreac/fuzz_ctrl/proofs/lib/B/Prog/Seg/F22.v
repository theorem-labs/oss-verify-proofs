(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1441 of its 1505 lines of code are new or changed and 947 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/YTail.v, with its module paths and module names changed; 587 of its 677 lines of code are new or changed and 1415 lines of the source are left out. *)
(* Segment F22 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the range 0x827f8-0x8283c
   (v1.8 0x82778-0x827bc; segment table rows S_F22 / S_F22t: IDENTICAL; the 6-turn record sum loop and its result
   test) and the call `jal reac_ctrl_headamp_record_verify` at 0x82840, up to the return point 0x82844 (the F23
   entry). Two lemmas:
   - seg_F22 (0x827f8 -> 0x8283c): from the F21 exit at the loop head (a0 = 0 the turn index, a1 = 0 the sum,
     a2 = Phi + 34, a3 = ~(Phi + 34) = 2^64 - (Phi + 35), a7 = 6, the shadow offset 0x7fff8000 in s10). Each turn i
     runs the UBSan check T54 (`bltu a3,a0` to the trap: not taken, Phi + 34 + i does not wrap), the
     instrumented check before the 1-byte load of Phi[34 + i] (the shadow byte ((Phi + 34 + i) >> 3) + 0x7fff8000
     is 0, so the `bnez` to the slow path 0x82824 is not taken and the error path is not reached), the load
     and the sum a1 += Phi[34 + i]. The loop invariant f22_loop (by the turn count) carries a0 = i and
     a1 = psum rec i. After turn 6, 0x82830-0x82838 sets s7 = (a1 & 127 = 0 ? 0 : -1), which is t_want_v since
     the record bytes Phi[18] / Phi[19] are 4 / 3. No memory changes; the registers the run writes (a0, a1, a4,
     a5, s7) are not FRA registers, so FRA moves by Tac_slot.sl_fra_move.
   - seg_F22t (0x8283c -> 0x82844): `mv a0,s2` and the head-amp record call. The callee contract
     (lib/B/Prog/reac_ctrl_headamp_record_verify_c.v) is the Section hypothesis HHRV: it reads the record bytes
     Phi[18], Phi[19] and the 6 bytes [Phi + 34, Phi + 40) (all addressable) and writes only its 16 stack bytes
     [sp - 16, sp); a0 = 0 when hv holds, else -1, which is t_want_v. FRA crosses the call by f22_fra (a disjoint
     stack-scratch write, as F20's ckv_fra).
   All three cuts are SlotInv's official ones: Inv_B827f8_at (F21's loop exit), Inv_B8283c_at (the loop's exit
   and the call's entry) and Inv_B82844_at (the call's return; F21's skip path exits there as well). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Import ListNotations.
(* lib.Prog's RcParse / RcFrag chain loads lib/Reusable/YK11.v, so the short name YK11 would resolve to that copy;
   this file's registers, mkst and FPState must be image B's, as SlotInv's and Tac_slot's are. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Mem.
Module UEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.
Module LEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module HRV := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_headamp_record_verify_c.
(* The stepping engine's value functions (the short name PropExec may resolve to lib/Lib/PropExec.v, which
   Tac_ro's chain loads after the engine). *)
Module UPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.PropExec.

(* A Lib.Exec run is a UL run: the two step relations have the same body. *)
Lemma f22_lu_msteps : forall s s', LEx.msteps rsegs s s' -> UEx.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UEx.msteps_refl|].
  eapply UEx.msteps_cons; [exact Hs | exact IH].
Qed.
Lemma f22_lu_evt : forall Q ms, LEx.evt rsegs Q ms -> UEx.evt rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (f22_lu_msteps _ _ H) | exact HQ]. Qed.

(* Z_to_bv 64 is injective on [-340, 2^64) x [0, 2^64 - 340): a spill base read twice is the same base. The
   window covers every LK / FLI spill offset (0 .. 336), whose base A' is at or above -336 by the byte bound of
   the spill's own eight bytes. *)
Lemma f22_bv64_inj_near : forall x y, -340 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 - 340 ->
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

(* Every runtime cell of rt_disjoint lies in the image, below HIGHMEM_BEG: a write above HIGHMEM_BEG misses them. *)
Lemma f22_rt_disjoint_hi : forall lo hi, HIGHMEM_BEG <= lo -> rt_disjoint [(lo, hi)].
Proof.
  intros lo hi H. unfold rt_disjoint. simpl.
  repeat match goal with
  | |- _ /\ _ => split
  | |- True => exact I
  | |- _ \/ _ => left; apply (Z.le_trans _ HIGHMEM_BEG _); [apply Z.leb_le; vm_compute; reflexivity | exact H]
  end.
Qed.

(* A spill A + off survives a write [lo, hi) below it (the run keeps s1). *)
Lemma f22_spill_keep : forall regs regs' m m' off v A lo hi,
  spill regs m off v -> rg regs 9 A -> getr regs' 9 = getr regs 9 ->
  0 <= off <= 336 -> 0 <= A -> A + 344 <= 2 ^ 64 -> hi <= A + off ->
  LFr.munch [(lo, hi)] m m' -> spill regs' m' off v.
Proof.
  intros regs regs' m m' off v A lo hi (A' & HA' & Hq) HA E9 Hoff HA0 HA1 Hhi MU.
  pose proof (LMem.bytes_at_bound rsegs m _ _ Hq) as Hb. rewrite LMem.length_le8 in Hb.
  assert (EA : A' = A).
  { apply f22_bv64_inj_near; [lia | lia |]. unfold rg in *. transitivity (getr regs 9); [symmetry; exact HA' | exact HA]. }
  subst A'. exists A. split; [unfold rg in *; rewrite E9; exact HA'|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite LMem.length_le8.
  intros x Hx. simpl. split; [lia | exact I].
Qed.

(* A spill read through s1 survives a register change that keeps s1. *)
Lemma f22_spill_reg : forall regs regs' m off v, getr regs' 9 = getr regs 9 -> spill regs m off v -> spill regs' m off v.
Proof. intros regs regs' m off v E (A & HA & Hq). exists A. split; [unfold rg in *; rewrite E; exact HA | exact Hq]. Qed.

(* ---- Byte facts. ---- *)
Lemma f22_rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (ULMem.wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (ULMem.bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma f22_ubyte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H. exact H. Qed.
(* `lbu` zero-extends: zxb b is the word of the unsigned byte value. *)
Lemma f22_zxb_u : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply MState.unsigned_lit. pose proof (f22_ubyte b). lia. Qed.
Lemma f22_nth_firstn : forall (l : list byte) N i d, (i < N)%nat -> nth i (firstn N l) d = nth i l d.
Proof.
  induction l as [|x l IH]; intros N i d Hi.
  - rewrite firstn_nil. reflexivity.
  - destruct N as [|N]; [lia|]. destruct i as [|i]; cbn; [reflexivity|]. apply IH. lia.
Qed.
Lemma f22_nth_skipn : forall (l : list byte) K i d, nth i (skipn K l) d = nth (K + i) l d.
Proof.
  induction l as [|x l IH]; intros K i d.
  - rewrite skipn_nil, !nth_overflow by (cbn; lia). reflexivity.
  - destruct K as [|K]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma f22_bsl_nth : forall g k n i d, (i < Z.to_nat n)%nat -> nth i (bsl g k n) d = nth (Z.to_nat k + i) g d.
Proof. intros g k n i d Hi. unfold bsl. rewrite f22_nth_firstn by exact Hi. apply f22_nth_skipn. Qed.
(* The record bytes: t_g is 50 bytes, so its slices below 50 have their full length. *)
Lemma f22_bsl_len : forall inp j k n, 0 <= k -> 0 <= n -> k + n <= 50 ->
  length (bsl (t_g inp j) k n) = Z.to_nat n.
Proof.
  intros inp j k n Hk Hn Hkn. unfold bsl, t_g. rewrite length_firstn, length_skipn, fr50_length. lia.
Qed.
(* The byte at a + t of a byte run at a. *)
Lemma f22_byte : forall m a bs t, (t < length bs)%nat -> LMem.bytes_at rsegs m a bs ->
  LMem.bytes_at rsegs m (a + Z.of_nat t) [nth t bs (Z_to_bv 8 0)].
Proof.
  intros m a bs t Ht (H0 & H1 & H2).
  unfold LMem.bytes_at. cbn [length].
  split; [lia|]. split; [lia|]. intros i Hi. destruct i as [|i]; [|lia].
  change (Z.of_nat 0) with 0%Z. rewrite Z.add_0_r. rewrite (H2 t Ht).
  transitivity (Some (nth t bs (Z_to_bv 8 0))); [apply nth_error_nth'; exact Ht | reflexivity].
Qed.
(* The first two bytes of a byte run. *)
Lemma f22_b2 : forall m a bs, (2 <= length bs)%nat -> LMem.bytes_at rsegs m a bs ->
  LMem.bytes_at rsegs m a [nth 0 bs (Z_to_bv 8 0); nth 1 bs (Z_to_bv 8 0)].
Proof.
  intros m a bs Hl (H0 & H1 & H2).
  unfold LMem.bytes_at. cbn [length].
  split; [lia|]. split; [lia|]. intros i Hi.
  destruct i as [|[|i]].
  - rewrite (H2 0%nat) by lia.
    transitivity (Some (nth 0 bs (Z_to_bv 8 0))); [apply nth_error_nth'; lia | reflexivity].
  - rewrite (H2 1%nat) by lia.
    transitivity (Some (nth 1 bs (Z_to_bv 8 0))); [apply nth_error_nth'; lia | reflexivity].
  - cbn in Hi. lia.
Qed.

(* ---- The sum loop model. ---- *)
Lemma f22_psum_range : forall rec n, 0 <= RcModel.psum rec n <= 255 * Z.of_nat n.
Proof.
  intros rec n. induction n as [|n IH]; cbn [RcModel.psum]; [lia|].
  pose proof (f22_ubyte (nth n rec (Z_to_bv 8 0))). lia.
Qed.
(* 0x82830 andi a0,a1,127 ; seqz s7,a0 ; addi s7,s7,-1: s7 = 0 when the sum is 0 mod 128, else -1. *)
Lemma f22_s7 : forall S, 0 <= S < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (UPE.v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 S)) 127)) 1) + -1)
  = Z_to_bv 64 (if S mod 128 =? 0 then 0 else -1).
Proof.
  intros S HS. rewrite (MState.unsigned_lit S) by lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
  pose proof (Z.mod_pos_bound S 128 ltac:(lia)) as Hb.
  unfold UPE.v_sltiu. rewrite (MState.unsigned_lit (S mod 128)) by lia. change (bv_wrap 64 1) with 1%Z.
  destruct (Z.eqb_spec (S mod 128) 0) as [E|E].
  - rewrite E. reflexivity.
  - replace (S mod 128 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* With the record bytes 4 / 3, t_want_v is the sum test of the 6 bytes at Phi + 34. *)
Lemma f22_want : forall inp j, cp_v (t_g inp j) 18 = 4 -> cp_v (t_g inp j) 19 = 3 ->
  t_want_v inp j = if RcModel.psum (bsl (t_g inp j) 34 6) 6 mod 128 =? 0 then 0 else -1.
Proof.
  intros inp j H18 H19. unfold cp_v in H18, H19. unfold t_want_v, RcLeaf.hv, RcLeaf.rsum.
  rewrite H18, H19. reflexivity.
Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map; exposing it lets `step` read a slot we have
   rewritten to a concrete value. *)
Lemma f22_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried concrete value, from H : rg regs r v. *)
Ltac f22_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.
(* After `srli x,a,3` on a = Phi + c: expose the unsigned value of the literal word. *)
Ltac f22_ush := match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3] => rewrite (MState.unsigned_lit X) by lia
  end.

(* The loop invariant of the 6-turn sum loop, by the number k of turns left: at the head 0x827f8 with a0 = i
   (i + k = 6, k > 0) and a1 = psum rec i, the run reaches 0x8283c with s7 = (psum rec 6 mod 128 = 0 ? 0 : -1),
   the other registers but a0, a1, a4, a5 unchanged and the memory unchanged. Each turn reads the byte
   Phi + 34 + i and its shadow byte ((Phi + 34 + i) >> 3) + 0x7fff8000 (0, so the slow path is not taken). *)
Lemma f22_loop : forall (k i : nat) (Q : _ -> Prop)
  (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (rec : list byte),
  (i + k = 6)%nat -> (0 < k)%nat -> 0 < phi -> phi + 50 <= 2 ^ 64 ->
  (forall t, (t < 6)%nat -> bytes_at rsegs m (phi + 34 + Z.of_nat t) [nth t rec (Z_to_bv 8 0)]) ->
  (forall t, (t < 6)%nat -> b8 m (Z.shiftr (phi + 34 + Z.of_nat t) 3 + ASAN_K) 0) ->
  (forall a0' a1' a4' a5' : word,
     Q (MS (Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' (Z_to_bv 64 (phi + 34))
          (Z_to_bv 64 (2 ^ 64 - (phi + 35))) a4' a5' a6 (Z_to_bv 64 6) s2 s3 s4 s5 s6
          (Z_to_bv 64 (if RcModel.psum rec 6 mod 128 =? 0 then 0 else -1)) s8 s9
          (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8283c) fc None m (seg_rom rsegs))) ->
  UEx.evt rsegs Q (MS (Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat i))
     (Z_to_bv 64 (RcModel.psum rec i)) (Z_to_bv 64 (phi + 34)) (Z_to_bv 64 (2 ^ 64 - (phi + 35))) a4 a5 a6
     (Z_to_bv 64 6) s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x827f8) fc None m
     (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros i Q ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    F fc m phi rec Hik Hk Hphi0 Hphi50 HB HS HQ; [lia|].
  assert (Hi : (i < 6)%nat) by lia.
  pose proof (f22_rd1 m _ _ (HB i Hi)) as RB.
  pose proof (f22_rd1 m _ _ (HS i Hi)) as RS.
  pose proof (f22_psum_range rec i) as Rp.
  pose proof (f22_psum_range rec 6) as Rp6.
  pose proof (f22_ubyte (nth i rec (Z_to_bv 8 0))) as Rb.
  assert (U3 : bv_unsigned (Z_to_bv 64 (2 ^ 64 - (phi + 35))) = 2 ^ 64 - (phi + 35))
    by (apply MState.unsigned_lit; lia).
  assert (Ui : bv_unsigned (Z_to_bv 64 (Z.of_nat i)) = Z.of_nat i) by (apply MState.unsigned_lit; lia).
  assert (Ui1 : bv_unsigned (Z_to_bv 64 (Z.of_nat (S i))) = Z.of_nat (S i)) by (apply MState.unsigned_lit; lia).
  (* 0x827f8 bltu a3,a0 (T54: 2^64 - (Phi + 35) >= i, so Phi + 34 + i does not wrap; not taken) *)
  step. if_false.
  (* add a4,a2,a0 ; srli a5,a4,3 ; add a5,a5,s10 ; lb a5 = shadow(Phi + 34 + i) = 0 ; bnez a5 (not taken) *)
  step. step. f22_ush. step. step. step. if_false.
  (* lbu a4 = rec[i] ; addi a0,a0,1 ; add a1,a1,a4 ; bne a0,a7,82778 *)
  step. step. step. step.
  rewrite (f22_zxb_u (nth i rec (Z_to_bv 8 0))).
  change (RcModel.psum rec i + bv_unsigned (nth i rec (Z_to_bv 8 0))) with (RcModel.psum rec (S i)).
  replace (Z.of_nat i + 1) with (Z.of_nat (S i)) by lia.
  destruct k as [|k].
  - (* i = 5: the last turn; the back edge is not taken *)
    assert (E5 : i = 5%nat) by lia. subst i.
    if_false.
    (* 0x82820 j 82830 ; andi a0,a1,127 ; seqz s7,a0 ; addi s7,s7,-1 *)
    step. step. step. step.
    rewrite (f22_s7 (RcModel.psum rec 6)) by lia.
    apply UEx.evt_done. apply HQ.
  - (* i < 5: the back edge to 0x827f8 *)
    if_true.
    apply (IH (S i)); [lia | lia | exact Hphi0 | exact Hphi50 | exact HB | exact HS | exact HQ].
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract of reac_ctrl_headamp_record_verify (lib/B/Prog/reac_ctrl_headamp_record_verify_c.v). *)
Hypothesis HHRV : HRV.reac_ctrl_headamp_record_verify_contract.

(* The FRA facts the loop reads: s10 = 0x7fff8000 and the model not halted. Read by name (tauto). *)
Lemma f22_fra_get : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  rg regs 26 ASAN_K /\ m_halted md = None.
Proof. intros g fr hb regs mem md H. destruct H as (A & sp & s5 & H). tauto. Qed.

(* FRA across the head-amp record call: the callee writes only its stack scratch W = [sp - 16, sp) (below the
   spill base A, above the image and the shadow, disjoint from the frame by the cut's disjunction), keeps the FRA
   registers, keeps the entry-anchored slot window [S - SLOT_STACK, S) (outside W from the entry window, inside W
   from the call's stk post on [sp - FN_STACK, sp)), and materializes pages (mat_le). The run's memory carries
   ro_agree (Tac_slot.sl_ro_keep at the call site), and the side arm's FakeStack frame record FSREC moves by
   Tac_slot.fsrec_munch_lo (W is above stklo). The same move as F20's ckv_fra. *)
Lemma f22_fra : forall g fr hb regs regs' mem mem' md md',
  FRA B APIf ra g fr hb regs mem md ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  (fr + FRAME_BYTES <= AC.aspZ regs - 16 \/ AC.aspZ regs <= fr) ->
  AC.aspZ regs <= APPMEM_END ->
  LFr.munch [(AC.aspZ regs - 16, AC.aspZ regs)] mem mem' ->
  LFr.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  LFr.stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md'.
Proof.
  intros g fr hb regs regs' mem mem' md md' HFRA Hfrapp Hdisjfr HaspB MU WM HroM HSTKW
    E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhi.
  rewrite Haspz in Hdisjfr, HaspB, MU, HSTKW.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (HOW : forall x, (x < sp - 16 \/ sp <= x) -> LFr.outside [(sp - 16, sp)] x)
    by (intros x Hx; simpl; split; [lia | exact I]).
  assert (Hallapp : all_app [(sp - 16, sp)]).
  { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
  assert (Hrtdj : rt_disjoint [(sp - 16, sp)]) by (apply f22_rt_disjoint_hi; unfold AF.SLOT_STACK in *; lia).
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. apply HOW.
    destruct (Z_lt_le_dec a (sp - 16)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec a sp) as [H2|H2]; [|right; exact H2].
    exfalso. apply Hns. unfold AC.a_store_ok. right; left. unfold AF.SLOT_STACK in *. split; lia. }
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH HstoreC HwmL) as [HAH' _ HSTKeq _].
  assert (HSTKS : LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
  { destruct (LFr.stk_split rsegs mem (g_S g - AF.SLOT_STACK) (sp - 16) (g_S g) Hwin ltac:(lia)) as (Hw1 & Hw2).
    destruct (LFr.stk_split rsegs mem (sp - 16) sp (g_S g) Hw2 ltac:(lia)) as (_ & Hw3).
    destruct (LFr.stk_split rsegs mem' (sp - FN_STACK) (sp - 16) sp HSTKW
                ltac:(unfold FN_STACK; lia)) as (_ & HwW).
    assert (Hw1' : LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) (sp - 16)).
    { eapply (LFr.stk_transport rsegs _ mem mem'); [exact Hw1 | exact MU | exact WM |].
      intros x Hx. left. apply HOW. lia. }
    assert (Hw3' : LFr.stk rsegs mem' sp (g_S g)).
    { eapply (LFr.stk_transport rsegs _ mem mem'); [exact Hw3 | exact MU | exact WM |].
      intros x Hx. left. apply HOW. lia. }
    apply (LFr.stk_merge rsegs mem' _ sp _); [| exact Hw3' | lia].
    apply (LFr.stk_merge rsegs mem' _ (sp - 16) _); [exact Hw1' | exact HwW | lia]. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. apply (KindBGlue.mbyte_munch sg [(sp - 16, sp)] mem mem' x MU).
    - unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
    - apply HOW. left. unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { exists A, sp, s5.
    split; [exact (AsanRTInv.RT_store sp sp mem mem' md md _ HRT MU WM Hallapp Hrtdj)|].
    split; [exact HAH'|].
    split; [exact HroM|].
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
        destruct Hil as [E|[]]; injection E as <- <-; lia.
      - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
        destruct Hil as [E|[]]; injection E as <- <-; lia. }
    split; [rewrite E2; exact Hr2|].
    split; [exact Hspm|].
    split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
    split; [rewrite HSTKeq; exact Hstklo|].
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
    split; [exact HA448|].
    split; [exact HS4|].
    split; [exact HAPP|].
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. right. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. right. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. right. lia. }
    split.
    { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
      - left. split; [exact H0|]. split; [exact Hspfr|].
        intros a Ha. rewrite HSTKeq. exact (Hreal a Ha).
      - right. split; [exact Hfr0|]. split; [|split].
        + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
          intros k Hk. rewrite <- KBlo.
          * exact (Hw k Hk).
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          * exact (Hw k Hk).
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
          * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        + eapply fsrec_munch_lo with (W := [(sp - 16, sp)]); [exact Hrec | exact HAH | exact MU |].
          intros x Hx _. apply HOW. left. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. lia. }
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
      rewrite LMem.length_le8. intros x Hx. apply HOW. lia. }
    split.
    { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
      eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen, Z2Nat.id by lia. intros x Hx. apply HOW. left.
      assert (Hin : in_shadow x).
      { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
        { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
        assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
        pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hinfr)) as His.
        replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
        unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
      unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
    split; [exact HSTKS|].
    split.
    { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx. apply HOW. right.
      unfold saved_bytes in Hx. rewrite !length_app, !LMem.length_le8 in Hx. cbn in Hx. lia. }
    split.
    { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
    split; [intros a Hin; exact (sl_addr_keep mem mem' [(sp - 16, sp)] a 1 (HAG a Hin) MU Hallapp)|].
    split; [intros a H1 H2; exact (sl_addr_keep mem mem' [(sp - 16, sp)] a 1 (HWA a H1 H2) MU Hallapp)|].
    split; [exact HSHI1|].
    split; [exact HSHI2|].
    split; [exact HSHI3|].
    split; [exact Hhb|]. split; [exact Hlive|].
    (* the input block is below stklo (fra_in_apart), so below [sp - 16, sp) *)
    apply (fra_in_keep g mem mem' [(sp - 16, sp)] Hinb Hinblk MU Hallapp).
    intros x Hx. destruct (Hinap x Hx) as (_ & Hxlo & _ & _). apply HOW. left. lia. }
  apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
Qed.

(* S_F22 (forms-asan-ubsan-v190.md (a working note, not in this delivery)). *)
Lemma seg_F22 : forall j,
  Hat B APIf ra (Inv_B8283c_at B APIf ra) j -> Hat B APIf ra (Inv_B827f8_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv. pose proof FRAME_BYTES_val as HFBv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & H20 & HFM &
    Ha0 & Ha1 & Ha2 & Ha3 & Ha7 & Hs2 & Hs8 & Hphi0 & Hphi50 & Hbig & Rtk & Hy18 & Hy19 & Hblk & Hrec & Hsh34 &
    Hsum & Hfrapp & Hdjphi).
  subst c. rewrite SEGS.
  destruct (f22_fra_get g fr _ regs mem md HFRA) as (Hr26 & Hhalt).
  assert (Hlen6 : length (bsl (t_g (g_in g) j) 34 6) = 6%nat) by (rewrite f22_bsl_len by lia; reflexivity).
  assert (HB6 : forall t, (t < 6)%nat ->
    bytes_at rsegs mem (phi + 34 + Z.of_nat t) [nth t (bsl (t_g (g_in g) j) 34 6) (Z_to_bv 8 0)]).
  { intros t Ht. apply f22_byte; [rewrite Hlen6; exact Ht | exact Hrec]. }
  assert (HS6 : forall t, (t < 6)%nat -> b8 mem (Z.shiftr (phi + 34 + Z.of_nat t) 3 + ASAN_K) 0).
  { intros t Ht. apply Hsh34. lia. }
  (* The one lazy-model run of this segment: Tac_slot.sl_run (AsanLift.evt_SR_canon_lazy). It reads the 6 record
     bytes [Phi + 34, Phi + 40) and their shadow bytes ((Phi + 34 .. Phi + 39) >> 3) + 0x7fff8000; it writes no
     memory. *)
  apply (sl_run regs (Z_to_bv 64 0x827f8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x8283c /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
       getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 25 = getr regs 25 /\
       getr R 23 = Z_to_bv 64 (t_want_v (g_in g) j))
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f22_mkR_of_expand.
    f22_slot Ha0. f22_slot Ha1. f22_slot Ha2. f22_slot Ha3. f22_slot Ha7. f22_slot Hr26.
    (* the 6 turns of the sum loop and the result test 0x82830-0x82838: f22_loop from turn 0 *)
    eapply f22_loop with (k := 6%nat) (i := 0%nat) (phi := phi) (rec := bsl (t_g (g_in g) j) 34 6);
      [reflexivity | lia | exact Hphi0 | exact Hphi50 | exact HB6 | exact HS6 |].
    intros a0' a1' a4' a5'. cbv beta. do 3 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    do 14 (split; [reflexivity|]).
    rewrite (f22_want (g_in g) j Hy18 Hy19). reflexivity.
  - (* continuation: rebuild the exit cut Inv_B8283c_at and apply it *)
    intros R pc' mem' regs' md'
      (Hpc & Hm & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E27 & E18 & E24 & E20 & E21 & E22 & E25 & E23) Hreg Hmat.
    subst pc' mem'.
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
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem md')
      by exact (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat).
    assert (Easp : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    (* LK: j and the FLI spills are read over s1, which the run keeps, and s11 is kept too, so Tac_ro.lk_keep
       moves the whole bundle on the unchanged memory (FLI's six memory facts as they are, KNT included). *)
    assert (HLK' : LK g fr j regs' mem).
    { destruct (Tac_ro.fli_mem _ _ _ _ (proj2 (proj2 (proj2 HLK)))) as (Hour6 & Hstkf & Hid38 & Hfg72 & HKNT & Hfst).
      eapply Tac_ro.lk_keep;
        [ exact HLK
        | unfold rg in *; rewrite Hreg, E27; exact (proj1 (proj2 (proj2 (proj2 HLK))))
        | exact Hour6
        | exact Hstkf
        | exact Hid38
        | exact Hfg72
        | exact HKNT
        | exact Hfst
        | exact (proj1 (proj2 (proj2 HLK)))
        | intros off v _ Hs; exact (f22_spill_reg regs regs' mem off v Fr9 Hs) ]. }
    rewrite <- SEGS. apply Hexit. exists phi, regs', mem, md', fr.
    split; [reflexivity|]. split; [exact HFRA'|].
    split; [eapply ent_mat; [exact HENT | exact Hmat]|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HLK'|].
    (* s4 = len and FM: s4 / s6 / s8 / s9 kept, the spills [A+184] / [A+312] read over the kept s1 *)
    split; [unfold rg in *; rewrite Fr20; exact H20|].
    split.
    { destruct HFM as (M184 & M24 & M22 & M25 & M312). unfold FM.
      split; [exact (f22_spill_reg regs regs' mem 184 _ Fr9 M184)|].
      split; [unfold rg in *; rewrite Fr24; exact M24|].
      split; [unfold rg in *; rewrite Fr22; exact M22|].
      split; [unfold rg in *; rewrite Fr25; exact M25 | exact (f22_spill_reg regs regs' mem 312 _ Fr9 M312)]. }
    split; [unfold rg in *; rewrite Fr18; exact Hs2|].
    split; [unfold rg; rewrite Hreg; exact E23|].
    split; [unfold rg in *; rewrite Fr24; exact Hs8|].
    split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hbig|]. split; [exact Rtk|].
    split; [exact Hblk|]. split; [exact Hrec|].
    split; [unfold rg in *; rewrite Fr25; exact Hsum|]. split; [exact Hfrapp|].
    destruct Hdjphi as (Hdj & HTURN & HIFS).
    split; [rewrite Easp; exact Hdj|].
    split; [exact (Tac_ro.turn_reg g j phi regs regs' mem Fr9 HTURN) | exact (Tac_ro.ifs_reg g fr (S j) regs regs' mem Fr9 HIFS)].
Qed.

(* S_F22t (forms-asan-ubsan-v190.md (a working note, not in this delivery)). *)
Lemma seg_F22t : forall j,
  Hat B APIf ra (Inv_B82844_at B APIf ra) j -> Hat B APIf ra (Inv_B8283c_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv. pose proof FRAME_BYTES_val as HFBv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & H20 & HFM &
    Hs2 & Hs7 & Hs8 & Hphi0 & Hphi50 & Hbig & Rtk & Hblk & Hrec & Hsum & Hfrapp & Hdjphi & HTURN & HIFS).
  subst c. rewrite SEGS.
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & HW0).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
    (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhi.
  (* the frame apart from the callee's 16 stack bytes (fra_frame) and sp below the top of app memory (FRA) *)
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (HfrK & _).
  pose proof (HfrK 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as Hdisjfr.
  assert (HaspB : AC.aspZ regs <= APPMEM_END) by (rewrite Haspz; lia).
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  pose proof HaspB as HaspB'. rewrite Haspz in HaspB'.
  pose proof Hdjphi as Hdjphi'. rewrite Haspz in Hdjphi'.
  assert (Esp : bv_unsigned (getr regs 2) = sp) by (unfold AC.aspZ in Haspz; exact Haspz).
  pose proof (LMem.bytes_at_bound rsegs mem _ _ Hspill) as HAb. rewrite LMem.length_le8 in HAb.
  (* The premises of the head-amp record contract at its entry (p = Phi, lo = sp - FN_STACK (fra_win),
     b0 / b1 = the record bytes Phi[18] / Phi[19], rec = the 6 bytes at Phi + 34). *)
  assert (Hlen6 : length (bsl (t_g (g_in g) j) 34 6) = 6%nat) by (rewrite f22_bsl_len by lia; reflexivity).
  assert (Hlen32 : length (t_blk (g_in g) j) = 32%nat)
    by (unfold t_blk; rewrite f22_bsl_len by lia; reflexivity).
  assert (HV1 : phi + 40 <= 2 ^ 64) by lia.
  assert (HV3 : bytes_at rsegs mem (phi + 18) [cp_b (t_g (g_in g) j) 18; cp_b (t_g (g_in g) j) 19]).
  { pose proof (f22_b2 mem (phi + 18) (t_blk (g_in g) j) ltac:(rewrite Hlen32; lia) Hblk) as H2b.
    unfold t_blk in H2b. rewrite !f22_bsl_nth in H2b by (cbn; lia). exact H2b. }
  assert (HV6 : LFr.stk rsegs mem (sp - FN_STACK) (bv_unsigned (getr regs 2)))
    by (rewrite Esp; rewrite Haspz in HW0; exact HW0).
  assert (HV7 : sp - FN_STACK + 16 <= bv_unsigned (getr regs 2))
    by (rewrite Esp; unfold FN_STACK, AF.SLOT_STACK; lia).
  assert (HV8 : phi + 20 <= bv_unsigned (getr regs 2) - 16 \/ bv_unsigned (getr regs 2) <= phi + 18)
    by (rewrite Esp; lia).
  assert (HV9 : phi + 40 <= bv_unsigned (getr regs 2) - 16 \/ bv_unsigned (getr regs 2) <= phi + 34)
    by (rewrite Esp; lia).
  assert (HV10 : asan_cells mem) by exact (RT_cells sp mem md HRT).
  assert (HV11 : shadow_rw mem) by exact (RT_shadow_rw sp mem md HRT).
  assert (HV12 : addressable mem (phi + 18) 2).
  { destruct HHB as (_ & Hphiad). apply (addressable_sub mem phi (AC.a_size (flen g j)) 18 2 Hphiad);
      unfold AC.a_size; lia. }
  assert (HV13 : addressable mem (phi + 34) 6).
  { destruct HHB as (_ & Hphiad). apply (addressable_sub mem phi (AC.a_size (flen g j)) 34 6 Hphiad);
      unfold AC.a_size; lia. }
  assert (HV14 : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            LFr.outside [(bv_unsigned (getr regs 2) - 16, bv_unsigned (getr regs 2))] x).
  { intros x Hx. rewrite Esp. simpl. split; [|exact I].
    unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, AF.SLOT_STACK in *.
    lia. }
  pose proof HHRV as HC.
  unfold HRV.reac_ctrl_headamp_record_verify_contract, HRV.REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME in HC.
  (* The one lazy-model run of this segment: Tac_slot.sl_run (AsanLift.evt_SR_canon_lazy). Pages it reads (in the
     callee): the record bytes Phi + 18, Phi + 19 and [Phi + 34, Phi + 40) with their shadow bytes, the runtime
     cells CELL_K / GOT_CELL_K. Pages it writes: only the callee's 16 stack bytes [sp - 16, sp). *)
  apply (sl_run regs (Z_to_bv 64 0x8283c) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x82844 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
       getr R 18 = Z_to_bv 64 phi /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\
       getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 25 = getr regs 25 /\
       getr R 10 = Z_to_bv 64 (t_want_v (g_in g) j) /\
       LFr.munch [(sp - 16, sp)] mem mem' /\ LFr.wmono rsegs mem mem' /\
       ro_agree rsegs mem' /\ LFr.stk rsegs mem' (sp - FN_STACK) sp)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f22_mkR_of_expand. f22_slot Hs2.
    (* 0x8283c mv a0,s2 ; 0x82840 jal reac_ctrl_headamp_record_verify *)
    step. step.
    (* the head-amp record call: the callee contract, back at 0x82844 *)
    eapply UEx.evt_cut.
    { apply f22_lu_evt. eapply HC with (p := phi) (lo := sp - FN_STACK)
        (b0 := cp_b (t_g (g_in g) j) 18) (b1 := cp_b (t_g (g_in g) j) 19) (rec := bsl (t_g (g_in g) j) 34 6).
      all: first [ reflexivity | assumption ]. }
    intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & Ems & MU & WM & MIi & ST).
    subst ms'. apply UEx.evt_done. cbv beta. do 3 eexists. split; [reflexivity|].
    split; [apply bv_eq; vm_compute; reflexivity|].
    do 16 (split; [reflexivity|]).
    rewrite Esp in MU, ST.
    split; [exact MU|]. split; [exact WM|].
    (* the callee asks for no mem_inv (its contract names it only in the post): ro_agree crosses its write,
       which lies above the image (Tac_slot.sl_ro_keep) *)
    split.
    { eapply sl_ro_keep with (W := [(sp - 16, sp)]); [exact Hro | exact MU |].
      intros x Hx. cbn [Frame.outside]. split; [|exact I]. unfold AC.GT in *. lia. }
    exact ST.
  - (* continuation: rebuild the exit cut Inv_B82844_at and apply it *)
    intros R pc' mem' regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er26 & Er27 & Er18 & Er23 & Er24 & Er20 & Er21 & Er22 & Er25 & Er10 &
       MU & WM & HRO' & ST')
      Hreg Hmat.
    subst pc'. rewrite <- SEGS. apply Hexit.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Easp : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    assert (HOW : forall x, (x < sp - 16 \/ sp <= x) -> LFr.outside [(sp - 16, sp)] x)
      by (intros x Hx; simpl; split; [lia | exact I]).
    assert (Hallapp : all_app [(sp - 16, sp)]).
    { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (f22_fra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md md' HFRA Hfrapp Hdisjfr HaspB);
        [ rewrite Haspz; exact MU | exact WM | exact HRO' | rewrite Haspz; exact ST'
        | exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat ]. }
    (* ENT crosses the call: the callee writes only its 16 stack bytes [sp - 16, sp), which lie inside the
       entry-anchored slot window [S - SLOT_STACK, S), so no byte ENT speaks of changes. *)
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
      cbn [LFr.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
      unfold AC.a_store_ok. right; left. unfold AF.SLOT_STACK in *. split; lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (lw_store (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH HstoreC HwmL)
      as [HAH2 Hown2 HSTK2 HSTKHI2].
    assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md).
    { eapply ent_store with (W := [(sp - 16, sp)]) (fr := fr) (regs := regs);
        [ exact HENT | exact HFRA | exact MU | | exact HSTK2 | exact HSTKHI2
        | intros a Hia Ho; exact (proj2 (Hown2 a) Ho) ].
      intros x Hx. destruct (Z_le_gt_dec (sp - 16) x) as [D1|D1];
        [destruct (Z_lt_ge_dec x sp) as [D2|D2]|].
      - right; left. unfold AF.SLOT_STACK in *. lia.
      - left. cbn [LFr.outside]. split; [lia | exact I].
      - left. cbn [LFr.outside]. split; [lia | exact I]. }
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|].
    split; [eapply ent_mat; [exact HENT' | exact Hmat]|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
      exact (sl_addr_keep mem mem' [(sp - 16, sp)] phi (AC.a_size (flen g j)) Hphiad MU Hallapp). }
    (* LK across the call: s11 and the spill base s1 are callee-saved, the callee's 16 stack bytes [sp - 16, sp)
       sit below the spill base (sp <= A) and above the our[] bytes, so every spill of j and of FLI survives
       (Tac_ro.lk_keep over f22_spill_keep). The kind-name table (KNT, 112 bytes at 0x9f580) is image data far
       below the callee's window, so its bytes and their shadow bytes are untouched. *)
    destruct (Tac_ro.fli_mem _ _ _ _ (proj2 (proj2 (proj2 HLK)))) as (Hour6 & Hstkf & Hid38 & Hfg72 & HKNT & Hfst).
    assert (Hfst' : addressable mem' (fr + 2880) 40)
      by exact (sl_addr_keep mem mem' [(sp - 16, sp)] (fr + 2880) 40 Hfst MU Hallapp).
    split.
    {
      assert (HKNT' : KNT mem').
      { split.
        - apply (fl_bytes _ mem mem' KNC.KIND_NAME KNC.kind_name_bytes (proj1 HKNT) MU).
          assert (HKL : Z.of_nat (length KNC.kind_name_bytes) = 112) by reflexivity.
          rewrite HKL. intros x Hx. apply HOW. left.
          unfold KNC.KIND_NAME, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
        - exact (sl_addr_keep mem mem' [(sp - 16, sp)] KNC.KIND_NAME 112 (proj2 HKNT) MU Hallapp). }
      eapply Tac_ro.lk_keep;
        [ exact HLK
        | unfold rg in *; rewrite Hreg, Er27; exact (proj1 (proj2 (proj2 (proj2 HLK))))
        | exact (sl_addr_keep mem mem' [(sp - 16, sp)] (fr + 2624) 6 Hour6 MU Hallapp)
        | eapply (LFr.stk_transport rsegs [(sp - 16, sp)] mem mem' fr (fr + FRAME_BYTES));
            [ exact Hstkf | exact MU | exact WM |];
          intros x Hx; left; apply HOW; destruct Hdisjfr; lia
        | exact (sl_addr_keep mem mem' [(sp - 16, sp)] (fr + 2688) 38 Hid38 MU Hallapp)
        | exact (sl_addr_keep mem mem' [(sp - 16, sp)] (fragb fr) 72 Hfg72 MU Hallapp)
        | exact HKNT'
        | exact Hfst'
        | unfold OURb in *;
          apply (fl_bytes _ mem mem' (fr + 2624) (OUR (g_in g)) (proj1 (proj2 (proj2 HLK))) MU);
          rewrite OUR_length; intros x Hx; apply HOW; lia
        | intros off v Hoff Hs;
          apply (f22_spill_keep regs regs' mem mem' off v A (sp - 16) sp Hs Hr9 Fr9); lia || exact MU ]. }
    (* s4 = len and FM across the call: s4 / s6 / s8 / s9 are callee-saved, the spills [A+184] / [A+312] lie
       above the callee's 16 stack bytes *)
    split; [unfold rg in *; rewrite Hreg, Er20; exact H20|].
    split.
    { destruct HFM as (M184 & M24 & M22 & M25 & M312). unfold FM.
      split; [apply (f22_spill_keep regs regs' mem mem' 184 _ A (sp - 16) sp M184 Hr9 Fr9); lia || exact MU|].
      split; [unfold rg in *; rewrite Hreg, Er24; exact M24|].
      split; [unfold rg in *; rewrite Hreg, Er22; exact M22|].
      split; [unfold rg in *; rewrite Hreg, Er25; exact M25|].
      apply (f22_spill_keep regs regs' mem mem' 312 _ A (sp - 16) sp M312 Hr9 Fr9); lia || exact MU. }
    split; [unfold rg; rewrite Hreg; exact Er10|].
    split; [unfold rg; rewrite Hreg; exact Er18|].
    split; [unfold rg in *; rewrite Hreg, Er23; exact Hs7|].
    split; [unfold rg in *; rewrite Hreg, Er24; exact Hs8|].
    split; [exact Hphi0|].
    split; [exact Hphi50|].
    split; [exact Hbig|].
    split; [exact Rtk|].
    split.
    { apply (fl_bytes _ mem mem' (phi + 18) (t_blk (g_in g) j) Hblk MU).
      rewrite Hlen32. intros x Hx. apply HOW. lia. }
    split.
    { apply (fl_bytes _ mem mem' (phi + 34) (bsl (t_g (g_in g) j) 34 6) Hrec MU).
      rewrite Hlen6. intros x Hx. apply HOW. lia. }
    split; [unfold rg in *; rewrite Hreg, Er25; exact Hsum|].
    split; [exact Hfrapp|].
    split; [rewrite Easp; exact Hdjphi|].
    (* FTURN and IFS (S j): the spills lie at or above A >= sp, the callee's 16 stack bytes; Phi's len bytes are a
       live heap block that ends at or below stklo <= S - SLOT_STACK < sp - 16; both records are inside the frame
       body, which fra_frame keeps apart from the window. *)
    assert (SPK : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hs. apply (f22_spill_keep regs regs' mem mem' off v A (sp - 16) sp Hs Hr9 Fr9); lia || exact MU. }
    assert (Hin : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
      by (unfold hb1; cbn; left; reflexivity).
    destruct (lw_blocks (APIf rc) _ mem md phi (AC.a_size (flen g j)) HAH Hin) as [_ _ Hbelow _ _].
    assert (Easz : AC.a_size (flen g j) = flen g j)
      by (unfold AC.a_size; rewrite Z.max_l by lia; reflexivity).
    rewrite Easz in Hbelow.
    split.
    { apply (Tac_ro.turn_munch g j phi regs regs' [(sp - 16, sp)] mem mem' HTURN SPK MU).
      intros x Hx. apply HOW. left. unfold flen in *. lia. }
    apply (Tac_ro.ifs_munch g fr (S j) regs regs' [(sp - 16, sp)] mem mem' HIFS MU); [|exact Hfst'].
    intros x Hx. apply HOW. destruct Hdisjfr; lia.
Qed.

End S.
