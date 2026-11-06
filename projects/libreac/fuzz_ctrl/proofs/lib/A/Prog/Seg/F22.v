(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its numbers changed; 495 of its 533 lines of code are new or changed and 358 lines of the source are left out. *)
(* Segment F22 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, patched image A), 0x82554-0x8259c: the head-amp record
   check. Entry cut SlotInv.Inv_A82554_at (frame[18] = 4, frame[19] = 3, a0 = a2 = phi + 34, a3 = 6, a1 = 0), exit
   cut SlotInv.Inv_A825a0_at (a0 = s4 = t_want_v), both on the B7CUT skeleton (FLSI, B7K and the body).
     0x82554-0x82578  the record-sum loop, 6 turns (a3 counts down from 6). Each turn does the instrumented check of
                      the byte at a0 = phi + 34 + i (the load of the shadow byte at (a0 >> 3) + s10 and `bnez`); the
                      shadow byte is 0, because phi is 16-aligned and the whole 8-byte granule [phi + 32, phi + 40) is
                      addressable (HB(phi) with 50 <= flen), so neither the slow path 0x82580-0x82588 nor the error
                      path 0x82c9c is reached. It then loads the byte at a2 and adds it to a1.
     0x8257c          j 0x8258c.
     0x8258c-0x82594  s4 = (if (sum & 127) = 0 then 0 else -1).
     0x82598          a0 = s7 = phi.
     0x8259c          jal reac_ctrl_headamp_record_verify (Section Hypothesis HARV, its contract
                      reac_ctrl_headamp_record_verify_c.v): it returns hv of the bytes phi + 18, phi + 19 and the six
                      record bytes, and writes only its own 16 stack bytes [sp - 16, sp).
   With frame[18] = 4 and frame[19] = 3, hv is "the six record bytes sum to 0 mod 128", which is the value of s4, so
   a0 = s4 = t_want_v at 0x825a0. The run is a Lib.Exec.evt (f22_run_lib, AsanLift.evt_SR_canon_lazy); FRA moves
   across the callee's window write W = [(sp - 16, sp)] by Tac_slot.sl_win_run (the callee window from fra_win, the
   frame placement from fra_frame, the side-arm frame record by Tac_slot.fsrec_munch_lo), as a Theorem Labs lane's F21 does
   for the same callee. The entry relation ENT moves across the same write by Tac_slot.ent_store and across the
   model step by Tac_slot.ent_mat; FLSI by B7Cuts.b7_flsi_win (W is app memory outside the spills, the frame and
   the heap blocks) and B7K by B7Cuts.b7_B7K_keep (W misses the spills, the live block and the frame).
   Tac_slot is only Require'd so the A.Tk.UL engine tactics do not shadow the Lib ones. The plain twin is
   a Theorem Labs lane's lib/Prog/Seg/E04.v (e04_s0, e04_hv). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcFrag RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_headamp_record_verify_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import B7Cuts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState Regs6ss RegisterBridge Exec Cells Step Tac Bytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* ---- Byte / word helpers for the Lib engine (its loads consume `ov_read_bytes _ _ (wa a) n = Some bs`). ---- *)
Lemma f22_rd1 : forall m a v, b8 m a v -> ov_read_bytes rsegs m (wa a) 1 = Some [Z_to_bv 8 v].
Proof.
  intros m a v H. unfold b8 in H.
  pose proof (bytes_at_ov_read rsegs m a [Z_to_bv 8 v] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma f22_ubyte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.
Lemma f22_firstn1 : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof.
  induction bs as [|b bs IH]; intros k d Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
(* The byte i of a carried byte run, in the form the load step consumes. *)
Lemma f22_rdb : forall m a bs i, bytes_at rsegs m a bs -> (i < length bs)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat i)) 1 = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  intros m a bs i H Hi. rewrite (bytes_at_ov_read rsegs m a bs i 1 H ltac:(lia)).
  f_equal. apply f22_firstn1. exact Hi.
Qed.
Lemma f22_ba_pre2 : forall m a b0 b1 l, bytes_at rsegs m a (b0 :: b1 :: l) -> bytes_at rsegs m a [b0; b1].
Proof. intros m a b0 b1 l H. exact (proj1 (proj1 (bytes_at_app rsegs m a [b0; b1] l) H)). Qed.

(* A zero shadow byte for the granule of p + t: p is 8-aligned and the granule's last byte p + 8(t/8) + 7 is in the
   addressable range, where shadow_ok with offset 7 forces the shadow byte to be 0. *)
Lemma f22_sh0 : forall m p L t, addressable m p L -> p mod 8 = 0 -> 0 <= t -> 8 * (t / 8) + 8 <= L ->
  b8 m (Z.shiftr (p + t) 3 + ASAN_K) 0.
Proof.
  intros m p L t (Hp0 & HL0 & HLe & HA) Hpm Ht HtL.
  pose proof (Z.div_pos t 8 Ht ltac:(lia)) as Ht8.
  destruct (HA (8 * (t / 8) + 7) ltac:(lia)) as (Happ & b & Hb & Hok).
  assert (Hm7 : (p + (8 * (t / 8) + 7)) mod 8 = 7).
  { assert (Ep : p = 8 * (p / 8)) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
    replace (p + (8 * (t / 8) + 7)) with (7 + (p / 8 + t / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  unfold shadow_ok in Hok. rewrite Hm7 in Hok.
  assert (Hs : bv_signed b = 0) by lia.
  assert (Eb : b = Z_to_bv 8 0).
  { apply bv_eq_signed. rewrite Hs. reflexivity. }
  assert (EX : Z.shiftr (p + t) 3 + ASAN_K = shadow_addr (p + (8 * (t / 8) + 7))).
  { assert (Ep : p = 8 * (p / 8)) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
    unfold shadow_addr. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. f_equal.
    replace (p + (8 * (t / 8) + 7)) with (7 + (p / 8 + t / 8) * 8) by lia.
    replace (p + t) with (t + (p / 8) * 8) by lia.
    rewrite !Z.div_add by lia. change (7 / 8) with 0. lia. }
  assert (Hlo : 0 <= Z.shiftr (p + t) 3) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
  assert (Hhi : Z.shiftr (p + t) 3 <= p + t).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. apply Z.div_le_upper_bound; lia. }
  unfold b8, bytes_at. cbn [length].
  split; [unfold ASAN_K; lia|]. split; [unfold ASAN_K, APPMEM_END in *; lia|].
  intros i Hi. destruct i as [|i]; [|lia]. cbn [nth_error]. change (Z.of_nat 0) with 0.
  rewrite Z.add_0_r, EX, Hb, Eb. reflexivity.
Qed.

(* ---- Record-sum facts (RcModel.psum; the plain twin's e04_s0 / e04_hv). ---- *)
Lemma f22_psum_range : forall bs k, 0 <= psum bs k <= 255 * Z.of_nat k.
Proof.
  intros bs k. induction k as [|k IH]; cbn [psum]; [lia|].
  pose proof (f22_ubyte (nth k bs (Z_to_bv 8 0))). lia.
Qed.
Lemma f22_psum_S_zxb : forall bs i,
  psum bs i + bv_unsigned (zxb (nth i bs (Z_to_bv 8 0))) = psum bs (S i).
Proof.
  intros bs i. cbn [psum]. unfold zxb. pose proof (f22_ubyte (nth i bs (Z_to_bv 8 0))).
  rewrite unsigned_lit by lia. reflexivity.
Qed.
Lemma f22_eqb_small : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap, !Z.mod_small by lia. reflexivity. Qed.

(* andi 127; seqz; addi -1 of the record sum S (plain twin e04_s0). *)
Lemma f22_s0 : forall S, 0 <= S < 2 ^ 64 ->
  Z_to_bv 64 (bv_unsigned (Lib.PropExec.v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 S)) 127)) 1) + -1) =
  Z_to_bv 64 (if S mod 128 =? 0 then 0 else -1).
Proof.
  intros S HS. rewrite (unsigned_lit S) by lia.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128.
  pose proof (Z.mod_pos_bound S 128 ltac:(lia)) as HM.
  unfold Lib.PropExec.v_sltiu. rewrite (unsigned_lit (S mod 128)) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec (S mod 128) 1); destruct (Z.eqb_spec (S mod 128) 0); try lia;
    rewrite unsigned_lit by lia; f_equal; lia.
Qed.

(* ---- The model facts the segment reads. ---- *)
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
Lemma f22_bsl_nth : forall g k n i, (i < Z.to_nat n)%nat ->
  nth i (bsl g k n) (Z_to_bv 8 0) = nth (Z.to_nat k + i) g (Z_to_bv 8 0).
Proof. intros g k n i Hi. unfold bsl. rewrite f22_nth_firstn by exact Hi. apply f22_nth_skipn. Qed.
Lemma f22_t_g_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.
Lemma f22_t_blk_len : forall inp j, length (t_blk inp j) = 32%nat.
Proof. intros inp j. unfold t_blk, bsl. rewrite length_firstn, length_skipn, f22_t_g_len. reflexivity. Qed.
Lemma f22_t_g6_len : forall inp j, length (bsl (t_g inp j) 34 6) = 6%nat.
Proof. intros inp j. unfold bsl. rewrite length_firstn, length_skipn, f22_t_g_len. reflexivity. Qed.
Lemma f22_blk_cp : forall inp j i, (i < 32)%nat -> nth i (t_blk inp j) (Z_to_bv 8 0) = cp_b (t_g inp j) (18 + i).
Proof. intros inp j i Hi. unfold t_blk, cp_b, cp_z. rewrite f22_bsl_nth by (cbn; lia). reflexivity. Qed.
(* t_want_v is hv of the first two block bytes and the six record bytes. *)
Lemma f22_want_hv : forall inp j,
  t_want_v inp j = (if hv (nth 0 (t_blk inp j) (Z_to_bv 8 0)) (nth 1 (t_blk inp j) (Z_to_bv 8 0))
                          (bsl (t_g inp j) 34 6) then 0 else -1).
Proof. intros inp j. unfold t_want_v. rewrite !f22_blk_cp by lia. reflexivity. Qed.
(* With the record type bytes 4 / 3, hv is the record-sum test (plain twin e04_hv). *)
Lemma f22_hv : forall b0 b1 rec, bv_unsigned b0 = 4 -> bv_unsigned b1 = 3 ->
  hv b0 b1 rec = (psum rec 6 mod 128 =? 0).
Proof. intros b0 b1 rec H0 H1. unfold hv, rsum. rewrite H0, H1. reflexivity. Qed.

Ltac ush := match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3] => rewrite (unsigned_lit X) by lia
  end.
Ltac outW := let x := fresh "x" in let Hx := fresh "Hx" in let H1 := fresh "HW1" in let H2 := fresh "HW2" in
  intros x Hx; cbn [outside]; split; [|exact I]; intros [H1 H2].
Ltac subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.
(* Replace the condition of the branch at the head of the goal by its value v, proved by pf from `c = v`. *)
Ltac f22_br v pf :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v by (symmetry; pf); cbv iota
  end.
Ltac f22_zdec :=
  repeat match goal with
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
  end; cbn [negb andb orb]; first [reflexivity | exfalso; lia].

(* Read-only image addresses lie below HIGHMEM_BEG (every image segment ends below it). *)
Lemma f22_rsegs_low : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? HIGHMEM_BEG) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- The record-sum loop, 0x82554 -> 0x8258c, by induction on the down-counter a3 = n (turn i = 6 - n). Each
   turn: `srli a4,a0,3 ; add a4,a4,s10 ; lb a4,0(a4)` loads the shadow byte of a0 = X + i, which is 0, so
   `bnez a4,0x82580` is not taken (the slow path and the error path are not reached); then `lbu a4,0(a2) ;
   addi a3,a3,-1 ; addi a0,a0,1 ; add a1,a1,a4 ; addi a2,a2,1 ; bnez a3,0x82554`, and after the last turn
   `j 0x8258c`. ---- *)
Lemma f22_loop : forall (Q : machine_state -> Prop)
    (ra0 sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X : Z) (rec : list byte),
  s10 = Z_to_bv 64 ASAN_K -> 0 <= X -> X + 6 <= 2 ^ 64 ->
  length rec = 6%nat -> bytes_at rsegs m X rec ->
  (forall i, (i < 6)%nat -> b8 m (Z.shiftr (X + Z.of_nat i) 3 + ASAN_K) 0) ->
  (forall a0' a2' a3' a4' : word,
     evt rsegs Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 (psum rec 6)) a2' a3' a4' a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     Fr (Z_to_bv 64 0x8258c) fc None m (seg_rom rsegs))) ->
  forall (n i : nat) (a0 a1 a2 a3 a4 : word),
    (i + n = 6)%nat -> (0 < n)%nat ->
    a0 = Z_to_bv 64 (X + Z.of_nat i) -> a2 = Z_to_bv 64 (X + Z.of_nat i) ->
    a3 = Z_to_bv 64 (Z.of_nat n) -> a1 = Z_to_bv 64 (psum rec i) ->
    evt rsegs Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    Fr (Z_to_bv 64 0x82554) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra0 sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m X rec
    E26 HX0 HX6 Lrec Hrec Hsh HK n.
  subst s10.
  induction n as [|n IH]; intros i a0 a1 a2 a3 a4 Hin Hpos E0 E2 E3 E1; [lia|]. subst a0 a1 a2 a3.
  pose proof (f22_rd1 m _ _ (Hsh i ltac:(lia))) as RDs.
  pose proof (f22_rdb m X rec i Hrec ltac:(lia)) as RDb.
  pose proof (f22_psum_range rec i) as PR.
  pose proof (f22_ubyte (nth i rec (Z_to_bv 8 0))) as RB.
  (* 0x82554 srli a4,a0,3 ; 0x82558 add a4,a4,s10 ; 0x8255c lb a4,0(a4) = 0 ; 0x82560 bnez a4 (not taken) *)
  step. step. ush. step. step. if_false.
  (* 0x82564 lbu a4,0(a2) ; 0x82568 addi a3,a3,-1 ; 0x8256c addi a0,a0,1 ; 0x82570 add a1,a1,a4 *)
  step. step. step. step. rewrite f22_psum_S_zxb.
  (* 0x82574 addi a2,a2,1 ; 0x82578 bnez a3,0x82554 *)
  step. step.
  destruct n as [|n'].
  - (* last turn: fall through, 0x8257c j 0x8258c *)
    f22_br false ltac:(rewrite f22_eqb_small by lia; f22_zdec).
    step.
    assert (Ei : i = 5%nat) by lia. subst i.
    apply HK.
  - f22_br true ltac:(rewrite f22_eqb_small by lia; f22_zdec).
    eapply (IH (S i)); [lia | lia | f_equal; lia | f_equal; lia | f_equal; lia | reflexivity].
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HARV : reac_ctrl_headamp_record_verify_contract.

Lemma f22_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* The facts of the allocator laws the segment reads, each law taken apart once here (a Theorem Labs lane 15:32Z: an inner list
   of a law is destructed in one lemma per law per file, so a new generation of Contract.v breaks one line). *)
Lemma f22_blk : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem md p n HAH Hin.
  destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md p n HAH Hin)
    as (Hal & _ & Hst & _).
  split; [exact Hal | exact Hst].
Qed.

Lemma f22_store : forall H mem mem' md,
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

(* Lib-engine analogue of Tac_slot.sl_run: prove the segment run as a Lib.Exec.evt (so the Lib-form reac
   contracts compose), then bridge to SR via evt_SR_canon_lazy. *)
Lemma f22_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (canonical_register_state (mkst regs pc mem (seg_rom rsegs))) ->
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
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* ---- 0x8258c -> 0x825a0: s4 from the record sum, a0 = s7 = phi, and the call of
   reac_ctrl_headamp_record_verify (HARV). ---- *)
Lemma f22_tail :
  forall (ra0 gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi lo sp : Z) (b0 b1 : byte) (rec : list byte),
    0 <= sp < 2 ^ 64 -> 0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    bytes_at rsegs m (phi + 18) [b0; b1] -> length rec = 6%nat -> bytes_at rsegs m (phi + 34) rec ->
    stk rsegs m lo sp -> asan_cells m -> shadow_rw m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if hv b0 b1 rec then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (if psum rec 6 mod 128 =? 0 then 0 else -1)) s5 s6 (Z_to_bv 64 phi)
                       s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x825a0) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\ stk rsegs m' lo sp)
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (psum rec 6)) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8258c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi lo sp b0 b1 rec Rsp Hp0 HpE Hpsp Hlo Hlo16 H18 Lrec Hrec Hstk HAC HSW Had2 Had6.
  assert (Esp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  pose proof (f22_psum_range rec 6) as PR. change (Z.of_nat 6) with 6 in PR.
  (* 0x8258c andi a0,a1,127 ; 0x82590 seqz s4,a0 ; 0x82594 addi s4,s4,-1 *)
  step. step. step.
  rewrite (f22_s0 (psum rec 6)) by lia.
  (* 0x82598 mv a0,s7 ; 0x8259c jal reac_ctrl_headamp_record_verify *)
  step. step.
  eapply evt_cut.
  { eapply HARV with (p := phi) (lo := lo) (b0 := b0) (b1 := b1) (rec := rec);
      unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME; rewrite ?Esp.
    - first [reflexivity | f_equal; lia].
    - lia.
    - unfold APPMEM_END in HpE. lia.
    - exact H18.
    - exact Lrec.
    - exact Hrec.
    - exact Hstk.
    - lia.
    - left. lia.
    - left. lia.
    - exact HAC.
    - exact HSW.
    - exact Had2.
    - exact Had6.
    - outW. unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
      lia. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & _ & ST'). subst ms'.
  unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME in MU, ST'. rewrite Esp in MU, ST'.
  match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
  apply evt_done.
  do 7 eexists. exists m'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact ST'].
Qed.

(* The segment, on the official cuts of SlotInv.v: entry Inv_A82554_at (F21's loop-head exit), exit
   Inv_A825a0_at (the record verifier returned), both on B7CUT with the live list hb1 phi (a_size len), which is
   hb1 phi len here (B7K: 50 <= len). *)
Lemma seg_F22 : forall j : nat,
  Hat B APIf ra (Inv_A825a0_at B APIf ra) j -> Hat B APIf ra (Inv_A82554_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  unfold Inv_A82554_at, B7CUT in HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HK &
    Hrec & Hcp18 & Hcp19 & Ha0 & Ha2 & Ha3 & Ha1).
  subst c. rewrite SEGS.
  pose proof (b7_asize_flen g j phi fr regs mem HK) as Hasz.
  rewrite Hasz in HFRA, HENT.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5v & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill304 & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAw &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof HK as (HLK & Hs7 & Hs6 & Hphi0 & Hphi50 & Hbig & Hblk & Hsp280 & Hs8 & Hreg18 & H152 & Hgph & Hph &
    Hlen & HLT & HSPL).
  pose proof HRT as (HAC0 & HSW0 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhi.
  assert (Hin : In (phi, flen g j) (hb1 phi (flen g j) ++ g_H g)) by (unfold hb1; cbn; left; reflexivity).
  destruct (f22_blk (hb1 phi (flen g j) ++ g_H g) mem md phi (flen g j) HAH Hin) as (Hal16 & Hbelow).
  pose proof HHB as (Hphinz & Hadr).
  unfold AC.a_size in Hadr. rewrite Z.max_l in Hadr by lia.
  pose proof Hadr as (_ & _ & HadrE & _).
  pose proof Hwin as (HwS0 & HwS1 & _).
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
  assert (HA416' : A + 416 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (Esp : bv_unsigned (getr regs 2) = sp) by exact Haspz.
  destruct (fra_win B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hwlo & Hwstk).
  unfold AC.aspZ in Hwlo, Hwstk. rewrite Esp in Hwlo, Hwstk.
  destruct (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hfrsep & HfrA & _ & _).
  unfold AC.aspZ in Hfrsep. rewrite Esp in Hfrsep.
  assert (HFN : FN_STACK = 1048576 - 4096) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hal8 : phi mod 8 = 0).
  { assert (Ep : phi = 16 * (phi / 16)) by (pose proof (Z.div_mod phi 16 ltac:(lia)); lia).
    rewrite Ep. replace (16 * (phi / 16)) with (0 + (2 * (phi / 16)) * 8) by lia. rewrite Z.mod_add by lia.
    reflexivity. }
  (* the six record bytes: their shadow bytes are 0 and they are addressable (HB(phi), 50 <= flen) *)
  assert (HSH : forall i, (i < 6)%nat -> b8 mem (Z.shiftr (phi + 34 + Z.of_nat i) 3 + ASAN_K) 0).
  { intros i Hi. replace (phi + 34 + Z.of_nat i) with (phi + (34 + Z.of_nat i)) by lia.
    apply (f22_sh0 mem phi (flen g j)); [exact Hadr | exact Hal8 | lia |].
    assert (E8 : (34 + Z.of_nat i) / 8 = 4)
      by (symmetry; apply (Z.div_unique (34 + Z.of_nat i) 8 4 (34 + Z.of_nat i - 32)); lia).
    rewrite E8. lia. }
  pose proof (addressable_sub mem phi (flen g j) 18 2 Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as Had2.
  pose proof (addressable_sub mem phi (flen g j) 34 6 Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as Had6.
  (* the two record type bytes b0 = frame[18] = 4, b1 = frame[19] = 3 *)
  assert (Hdec : exists b0 b1 rest, t_blk (g_in g) j = b0 :: b1 :: rest).
  { pose proof (f22_t_blk_len (g_in g) j) as L.
    destruct (t_blk (g_in g) j) as [|x [|y r]]; cbn [length] in L; try lia. eauto. }
  destruct Hdec as (b0 & b1 & rest & Eblk).
  pose proof (f22_blk_cp (g_in g) j 0 ltac:(lia)) as C0.
  pose proof (f22_blk_cp (g_in g) j 1 ltac:(lia)) as C1.
  rewrite Eblk in C0, C1. cbn [nth Nat.add] in C0, C1.
  assert (H18 : bytes_at rsegs mem (phi + 18) [b0; b1]).
  { apply (f22_ba_pre2 mem (phi + 18) b0 b1 rest). rewrite <- Eblk. exact Hblk. }
  assert (E18 : bv_unsigned b0 = 4) by (rewrite C0; exact Hcp18).
  assert (E19 : bv_unsigned b1 = 3) by (rewrite C1; exact Hcp19).
  assert (Ewant : t_want_v (g_in g) j = (if hv b0 b1 (bsl (t_g (g_in g) j) 34 6) then 0 else -1))
    by (rewrite f22_want_hv, Eblk; reflexivity).
  assert (Ehv : hv b0 b1 (bsl (t_g (g_in g) j) 34 6) = (psum (bsl (t_g (g_in g) j) 34 6) 6 mod 128 =? 0))
    by (apply f22_hv; assumption).
  set (W := [(sp - 16, sp)]).
  apply (f22_run_lib regs (Z_to_bv 64 0x82554) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x825a0 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 26 = getr regs 26 /\
       getr R 10 = Z_to_bv 64 (t_want_v (g_in g) j) /\ getr R 20 = Z_to_bv 64 (t_want_v (g_in g) j) /\
       munch W mem mem' /\ wmono rsegs mem mem' /\ stk rsegs mem' (sp - FN_STACK) sp)
    (Post B APIf ra g)).
  - exact Hhalt.
  - change (canonical_register_state (mkst regs (Z_to_bv 64 0x82554) mem (seg_rom rsegs)))
      with (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x82554) fp_csr None mem (seg_rom rsegs)).
    rewrite f22_mkR_of_expand.
    rewrite Hr2.
    subst_slot Ha0. subst_slot Ha1. subst_slot Ha2. subst_slot Ha3. subst_slot Hs7. subst_slot Hr26.
    eapply f22_loop with (X := phi + 34) (rec := bsl (t_g (g_in g) j) 34 6) (n := 6%nat) (i := 0%nat).
    + reflexivity.
    + lia.
    + lia.
    + apply f22_t_g6_len.
    + exact Hrec.
    + exact HSH.
    + intros a0' a2' a3' a4'.
      eapply evt_mono.
      { eapply f22_tail with (phi := phi) (lo := sp - FN_STACK) (sp := sp) (b0 := b0) (b1 := b1)
          (rec := bsl (t_g (g_in g) j) 34 6).
        - unfold APPMEM_END in *. lia.
        - lia.
        - unfold APPMEM_END in *. lia.
        - lia.
        - lia.
        - lia.
        - exact H18.
        - apply f22_t_g6_len.
        - exact Hrec.
        - exact Hwstk.
        - exact HAC0.
        - exact HSW0.
        - exact Had2.
        - exact Had6. }
      intros ms' (ra' & a1' & a2'' & a3'' & a4'' & a5' & a6' & m' & E & MU & WM & ST'). subst ms'.
      eexists _, _, m'. split; [reflexivity|].
      split; [reflexivity|].
      do 12 (split; [reflexivity|]).
      split; [rewrite Ewant; reflexivity|].
      split; [rewrite Ewant, Ehv; reflexivity|].
      split; [exact MU|]. split; [exact WM | exact ST'].
    + lia.
    + lia.
    + f_equal; lia.
    + f_equal; lia.
    + reflexivity.
    + reflexivity.
  - (* continuation: rebuild the exit cut Inv_A825a0_at and apply it *)
    intros R pc' mem' regs'' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E18r & E19r & E21 & E22 & E23 & E24 & E26 & E10 & E20 & MU & WM & ST')
      Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact E18r).
    assert (Fr19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact E19r).
    assert (Fr21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (Fr24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (OW : forall x, x < sp - 16 \/ sp <= x -> outside W x) by (subst W; outW; lia).
    assert (HroM : ro_agree rsegs mem').
    { apply (ro_agree_same rsegs mem mem' Hro). intros a Ha. apply MU. apply OW. left.
      unfold ro_addr in Ha. destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:Ef; [|discriminate].
      destruct (kb_find_segment rsegs (bv_unsigned a) 1 s Ef) as (Hs & _ & Hs2).
      pose proof (proj1 (forallb_forall _ rsegs) f22_rsegs_low s Hs) as Hb. cbn beta in Hb. apply Z.leb_le in Hb.
      unfold HIGHMEM_BEG in *. lia. }
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
    assert (Hrtdj : rt_disjoint W).
    { assert (Hwlo2 : AC.GT <= sp - 16) by (unfold AC.GT, HIGHMEM_BEG in *; lia).
      subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN, AC.GT in *.
      cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (flen g j) ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite unsigned_lit by lia. subst W.
      cbn [outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
      unfold AC.a_store_ok. right; left. unfold APPMEM_END in *. split; lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (f22_store (hb1 phi (flen g j) ++ g_H g) mem mem' md HAH HstoreC HwmL)
      as (HAH' & Hownst & HSTKeq & HSTKHeq).
    assert (HWblk : forall q n x, In (q, n) (g_H g) -> q <= x < q + n -> outside W x).
    { intros q n x Hinq Hx.
      destruct (f22_blk (hb1 phi (flen g j) ++ g_H g) mem md q n HAH (in_or_app _ _ _ (or_intror Hinq)))
        as (_ & Hqe).
      apply OW. left. unfold FN_STACK, AF.SLOT_STACK in *. lia. }
    assert (HSTKW : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { destruct (stk_split rsegs mem' (sp - FN_STACK) (sp - 16) sp ST' ltac:(lia)) as (_ & ST16).
      apply (Tac_slot.sl_win_stk B APIf ra g fr (hb1 phi (flen g j)) regs mem md mem' 16 HFRA ltac:(lia));
        [ rewrite Haspz; subst W; exact MU | exact WM | rewrite Haspz; exact ST16 ]. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs'' mem' md).
    { apply (Tac_slot.sl_win_run B APIf ra empty FF g fr (hb1 phi (flen g j)) regs regs'' mem mem' md W HFRA MU
        WM HroM Hallapp Hrtdj HAH' HSTKeq).
      - intros x Hx. apply OW. left. unfold HIGHMEM_BEG in *. lia.
      - intros x Hx. apply OW. destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia.
      - intros A' HA' HA'b x Hx. apply OW. right.
        assert (EA' : A' = A).
        { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in Hr9; rewrite <- HA'; exact Hr9).
          apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !unsigned_lit in E by lia. exact E. }
        subst A'. lia.
      - intros x Hx. apply OW. right. lia.
      - exact HSTKW.
      - intros HR. eapply Tac_slot.fsrec_munch_lo with (W := W);
          [exact HR | exact HAH | exact MU | |].
        + intros x Hx. apply OW. left. unfold HIGHMEM_BEG in *. lia.
        + intros x Hxa Hxf Hxs. apply OW. left. unfold FN_STACK, AF.SLOT_STACK in *. lia.
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs'' mem' md').
    { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs'' regs'' mem' md md' HFRA');
        try reflexivity; exact Hmat. }
    (* ENT: the record verifier wrote only its own 16 bytes inside the slot window; then the model step *)
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md).
    { apply (Tac_slot.ent_store B APIf ra g fr (hb1 phi (flen g j)) regs mem mem' md W HENT HFRA MU).
      - intros x Hx.
        destruct (Z_lt_le_dec x (sp - 16)) as [Hd|Hd]; [left; apply OW; left; exact Hd|].
        destruct (Z_lt_le_dec x sp) as [Hd2|Hd2]; [right; left; lia | left; apply OW; right; exact Hd2].
      - exact HSTKeq.
      - exact HSTKHeq.
      - intros a Hia Ho. exact (proj2 (Hownst a) Ho). }
    assert (HENT'' : ENT APIf g (hb1 phi (flen g j)) mem' md')
      by exact (Tac_slot.ent_mat APIf g (hb1 phi (flen g j)) mem' md md' HENT' Hmat).
    (* FLSI: W is app memory outside the spills, the frame and every entry heap block *)
    assert (HWA : forall x, A <= x < A + 416 -> outside W x) by (intros x Hx; apply OW; right; lia).
    assert (HFLSI' : FLSI g j fr regs'' mem').
    { apply (b7_flsi_win g j fr regs regs'' mem mem' W A HFLSI Hr9 ltac:(lia) HA416' Fr9 MU WM Hallapp HWA).
      - intros x Hx. apply OW.
        destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia.
      - exact HWblk. }
    (* B7K: W misses the spills, the live block [phi, phi + len), the frame's [fr + 2624, fr + 2840) and the FIRST
       body [fr + 2880, fr + 2915) with its shadow bytes (W is app memory) *)
    assert (HB7 : B7K g j phi fr regs'' mem').
    { apply (b7_B7K_keep g j phi fr regs regs'' mem mem' W A HK MU Hr9 ltac:(lia) HA416'
               Fr9 Fr18 Fr21 Fr22 Fr23 Fr24 HWA).
      - intros x Hx. apply OW. left. unfold FN_STACK, AF.SLOT_STACK in *. lia.
      - intros x Hx. apply OW.
        destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia.
      - intros x Hx. apply OW.
        destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia.
      - intros i Hi. apply (b7_app_shadow_out W _ Hallapp). apply shadow_of_app.
        apply (proj2 (fra_app B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA)). lia. }
    assert (HHB' : HB mem' phi (flen g j)).
    { split; [exact Hphinz|]. unfold AC.a_size. rewrite Z.max_l by lia.
      exact (addressable_kept mem mem' phi (flen g j) Hadr (munch_meta W mem mem' MU Hallapp)). }
    rewrite <- SEGS. apply Hexit.
    unfold Inv_A825a0_at, B7CUT.
    exists phi, regs'', mem', md', fr.
    rewrite ?Hasz.
    cbv beta.
    split; [reflexivity|].
    split; [exact HFRA''|].
    split; [exact HENT''|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|].
    split; [exact HFLSI'|]. split; [exact HB7|].
    split; [unfold rg; rewrite Hreg; exact E10 | unfold rg; rewrite Hreg; exact E20].
Qed.

End S.
