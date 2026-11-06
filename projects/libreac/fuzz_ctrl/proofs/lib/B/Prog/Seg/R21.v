(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1421 of its 1489 lines of code are new or changed and 943 lines of the source are left out. *)
(* Segment R21 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81aa0, 0x81c54], cut
   Inv_B81aa0 -> cuts Inv_B816ec (turn S b), Inv_B81c58 and Inv_B81ca8 (plan-asan-ubsan.md section 2, row R21;
   section 4, STRCMP = wrapper_strcmp 0x42aa0, SHf8 = meta_fill_f8 0x55144). rule 24: no function proved (a slot
   segment).

   The latch: 0x81aa0 .. 0x81abc sb s8 store the register s8 into the frame's own shadow bytes S(fr) + 300, 306,
   308, 312, 296 .. 299 (s3 = S(fr)); 0x81ac0 addiw s6,s6,1; 0x81ac4 li a0,7; 0x81ac8 bne s6,a0,816ec.
   - b <= 5: the branch is taken, back to the round-trip head with s6 = b + 1 (Inv_B816ec_at (S b): R6X at S b
     from RBE, SlotInv.r6x_of_rbe).
   - b = 6: 0x81acc j 81b00, the identity-record check against the catalogue row m = [A + 272]: the record's
     pointer [A + 144] = fr + 2176 is reloaded before each read; it holds RID_7 (RtmB: firmware, version and,
     with an identity record, the model name are the row's). Each check is a load of the record and of the row and
     a `bne`/`beq` that passes, so the sink jumps 0x81b0c, 0x81b48, 0x81b58, 0x81b88, 0x81bb8, 0x81be8, 0x81c1c are
     not reached; 0x81b10 ld a0,32(s1) reloads [A + 32] = 0 (RBE), so the branch to the trap routine 0x81b18
     `j 82fa0` is not taken; each instrumented check of a row granule reads shadow byte 0 (the catalogue row is a
     registered global), so the report branches 0x81b3c, 0x81b7c, 0x81bac, 0x81bdc, 0x81c04, 0x81c38 are not taken.
     0x81c0c beqz a0,81c60 tests has_identity_record (the s32 at m + 56):
     - h <> 0: the record's name byte is checked and wrapper_strcmp (on its lib/B contract) compares the record's
       model name at fr + 2176 + 3 with the row's name: equal (RtmB.rb_rtm_name), so it returns 0 at 0x81c58
       (Inv_B81c58);
     - h = 0: the branch goes to 0x81c60: li s2,-8, 14 sb s2 into S(fr) + 272 .. 276, 282 .. 290, li a1,187,
       ld a0,8(s1) (Q = S(fr) + 68, RBE) and jal meta_fill_f8 (on its lib/B contract asan_set_shadow_c.v, it sets
       the 187 shadow bytes [Q, Q + 187) to 0xf8), returning to 0x81ca8 (Inv_B81ca8).
   The callee contracts ask for mem_inv, so each call runs on the normalized memory (MemNorm.evt_normalize).
   FRA / ENT move across the latch and the meta_fill_f8 run by RHelp.rh_sh_move (every write is a frame shadow
   byte) and across wrapper_strcmp by Tac_slot.sl_callee_keep / ent_store. Entry and exits are the official cuts
   Inv_B81aa0_at, Inv_B816ec_at, Inv_B81c58, Inv_B81ca8 of lib/B/Prog/SlotInv.v.
   RBE's conjuncts move with RHelp's RBE lemmas; the P exits carry PRO (its spills from RBE, our[]'s shadow byte
   Sfr fr + 328 above every write: the latch's 296 .. 312, the P1 suffix's [Sfr fr, Sfr fr + 291)); s11 = 32 is
   kept to Inv_B816ec_at. seg_R21_a5c (S_R21_a5c) is the same run from the latch cut Inv_B81ac0_at
   (r21_a5c_next / r21_a5c_last, then r21_tail_evt), whose has_identity_record = 0 arm stops at Inv_B81c60 with
   a0 = 0.  v1.9.0 against the patched image: the pcs move +0x64, the spills are [A + 272] / [A + 144] / [A + 32]
   / [A + 8] (patched [A + 288] / [A + 136] / [A + 48] / [A + 16]), the latch stores s8 (patched s11), the 32 is
   in s11 (patched s2), CUR's n - c in s9 (patched s8), the frame is 3136 bytes (patched 3040). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcSynth RcEmit RcDecl RcParseLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import strcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_set_shadow_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot RHelp RtmB.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.
Module ASS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_set_shadow_c.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.

(* A byte store `sb r,k(s3)` into a cell run: le1 v is [Z_to_bv 8 (bv_unsigned v)] by conversion (the store
   hook of lib/B/Prog/Seg/R18.v). *)
Local Ltac fix_lit_store ::=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) => change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

(* ---- arithmetic and branch helpers (the image-A R21 copies, renamed r21_) ---- *)

Lemma r21_swrap32 : forall z, -2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.

Lemma r21_bv_eqb : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec a b) as [->|Hn]; [apply Z.eqb_refl|]. apply Z.eqb_neq.
  intros E. apply Hn. Z.div_mod_to_equations. lia.
Qed.

Lemma r21_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

Lemma r21_sx32_eqb0 : forall h, 0 <= h < 2 ^ 32 -> bv_eqb (sx32 (Z_to_bv 64 h)) (Z_to_bv 64 0) = (h =? 0).
Proof.
  intros h Hh. unfold sx32, bv_eqb. rewrite (MState.unsigned_lit h) by lia.
  rewrite !MState.unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (2 ^ 64) with 18446744073709551616.
  destruct (Z.eqb_spec h 0) as [->|Hn]; [reflexivity|]. apply Z.eqb_neq.
  Z.div_mod_to_equations. lia.
Qed.

Lemma r21_eqb0 : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x Hx. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

(* bv_eqb x y = true names one word. *)
Lemma r21_eqb_eq : forall x y : word, bv_eqb x y = true -> x = y.
Proof. intros x y H. unfold bv_eqb in H. apply bv_eq. apply Z.eqb_eq. exact H. Qed.

(* PRA (A4's eleven frame-pointer spills in v1.9.0) across a run that keeps every spill of the save area. *)
Lemma r21_PRA_keep : forall fr regs regs' m m',
  (forall off v, 0 <= off -> off + 8 <= 448 -> spill regs m off v -> spill regs' m' off v) ->
  PRA fr regs m -> PRA fr regs' m'.
Proof.
  intros fr regs regs' m m' K H. unfold PRA in *.
  destruct H as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
  do 10 (split; [apply K; [lia | lia | eassumption]|]). apply K; [lia | lia | eassumption].
Qed.

(* `beq` on two equal values: taken. *)
Ltac r21_beq_refl :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; apply r21_eqb_refl]
  end.

(* srli of the shadow address: the shifted value is a literal in range. *)
Ltac r21_shfix :=
  repeat match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (MState.unsigned_lit x) by lia
  end.

(* ---- byte-run helpers ---- *)

Lemma r21_first1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l (Z_to_bv 8 0)].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma r21_first2 : forall (l : list byte) k, (k + 2 <= length l)%nat ->
  firstn 2 (skipn k l) = [nth k l (Z_to_bv 8 0); nth (S k) l (Z_to_bv 8 0)].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k].
  - destruct l as [|y l]; cbn in Hk; [lia|]. reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma r21_rd1 : forall m a l k, bytes_at rsegs m a l -> (k < length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [nth k l (Z_to_bv 8 0)].
Proof.
  intros m a l k H Hk.
  pose proof (rh_ba_sub m a l k 1 H ltac:(lia)) as HB. rewrite r21_first1 in HB by lia.
  exact (rh_rdn m _ _ 1%nat HB eq_refl).
Qed.

Lemma r21_rd2 : forall m a l k, bytes_at rsegs m a l -> (k + 2 <= length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 2 =
  Some (le2 (Z_to_bv 64 (bv_unsigned (nth k l (Z_to_bv 8 0)) + 256 * bv_unsigned (nth (S k) l (Z_to_bv 8 0))))).
Proof.
  intros m a l k H Hk.
  pose proof (rh_ba_sub m a l k 2 H ltac:(lia)) as HB. rewrite r21_first2 in HB by lia.
  replace (le2 (Z_to_bv 64 (bv_unsigned (nth k l (Z_to_bv 8 0)) + 256 * bv_unsigned (nth (S k) l (Z_to_bv 8 0)))))
    with [nth k l (Z_to_bv 8 0); nth (S k) l (Z_to_bv 8 0)].
  - exact (rh_rdn m _ _ 2%nat HB eq_refl).
  - rewrite <- RcParseLib.rc_le2_pair. f_equal. f_equal. lia.
Qed.

Lemma r21_rd4 : forall m a l k, bytes_at rsegs m a l -> (k + 4 <= length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 4 = Some (firstn 4 (skipn k l)).
Proof.
  intros m a l k H Hk.
  pose proof (rh_ba_sub m a l k 4 H ltac:(lia)) as HB.
  apply (rh_rdn m _ _ 4%nat HB). rewrite length_firstn, length_skipn. lia.
Qed.

Lemma r21_rd8 : forall m a l k, bytes_at rsegs m a l -> (k + 8 <= length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 8 = Some (firstn 8 (skipn k l)).
Proof.
  intros m a l k H Hk.
  pose proof (rh_ba_sub m a l k 8 H ltac:(lia)) as HB.
  apply (rh_rdn m _ _ 8%nat HB). rewrite length_firstn, length_skipn. lia.
Qed.

Lemma r21_byte1 : forall b : byte, bv_unsigned b = 1 -> b = Z_to_bv 8 1.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

(* strcmp's index on two equal strings is their length. *)
Lemma r21_strcmp_k_refl : forall l : list byte, strcmp_k l l = length l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbn [strcmp_k length]. rewrite Z.eqb_refl, IH. reflexivity.
Qed.

(* The image's read-only bytes of a checked run are in memory (ro_agree). *)
Lemma r21_ro_bytes : forall (bs : list byte) (m : word -> option byte) A, MN.ro_agree rsegs m ->
  Image.ro_bytes_b rsegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs m A bs.
Proof.
  induction bs as [|b bs IH]; intros m A Hro HB HA Hl.
  - split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - change (Image.ro_bytes_b rsegs A (b :: bs)) with
      (match seg_rom rsegs (wa A) with
       | Some b' => (bv_eqb b b' && ro_addr rsegs (wa A) && Image.ro_bytes_b rsegs (A + 1) bs)%bool
       | None => false end) in HB.
    destruct (seg_rom rsegs (wa A)) as [b'|] eqn:E; [|discriminate HB].
    apply andb_prop in HB as [HB1 HB3]. apply andb_prop in HB1 as [HBe HBro].
    unfold bv_eqb in HBe. apply Z.eqb_eq in HBe. apply bv_eq in HBe. subst b'.
    cbn [length] in Hl.
    assert (HB' : bytes_at rsegs m (A + 1) bs) by (apply IH; [exact Hro | exact HB3 | lia | lia]).
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + replace (A + Z.of_nat 0) with A by lia. cbn [nth_error]. rewrite (Hro (wa A) HBro). exact E.
    + replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. cbn [nth_error].
      cbn [length] in Hi. exact (proj2 (proj2 HB') i ltac:(lia)).
Qed.

(* ---- the latch 0x81aa0 .. 0x81ac8 ---- *)

Lemma r21_latch_next :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z) (junk : list byte),
    s6 = Z_to_bv 64 bz -> 0 <= bz <= 5 ->
    rw_cells rsegs m (bv_unsigned s3v + 296) [CB 17 junk] ->
    stk rsegs m (bv_unsigned s3v + 296) (bv_unsigned s3v + 313) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x816ec) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\
         getr R 22 = Z_to_bv 64 (bz + 1) /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = s11 /\
         munch [(bv_unsigned s3v + 296, bv_unsigned s3v + 313)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned s3v + 296) (bv_unsigned s3v + 313))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81aa0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bz junk -> Hb RW ST.
  pose proof (rw_cells_bound _ _ _ _ RW) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (munch_refl [(bv_unsigned s3v + 296, bv_unsigned s3v + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step. step. step.   (* 81aa0 .. 81abc : the eight shadow stores *)
  step. step. step.                                (* 81ac0 addiw ; 81ac4 li a0,7 ; 81ac8 bne *)
  rewrite ?(MState.unsigned_lit bz) by lia. rewrite ?r21_swrap32 by lia. rewrite ?r21_bv_eqb by lia.
  if_true.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 15 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST].
Qed.

Lemma r21_latch_last : forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte),
    s6 = Z_to_bv 64 6 ->
    rw_cells rsegs m (bv_unsigned s3v + 296) [CB 17 junk] ->
    stk rsegs m (bv_unsigned s3v + 296) (bv_unsigned s3v + 313) ->
    (forall (a0' s6' : word) (m' : word -> option byte),
       munch [(bv_unsigned s3v + 296, bv_unsigned s3v + 313)] m m' -> wmono rsegs m m' ->
       stk rsegs m' (bv_unsigned s3v + 296) (bv_unsigned s3v + 313) ->
       evt rsegs Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81b00) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81aa0) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m junk -> RW ST HK.
  pose proof (rw_cells_bound _ _ _ _ RW) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (munch_refl [(bv_unsigned s3v + 296, bv_unsigned s3v + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step. step. step. step. step.   (* 81aa0 .. 81abc : the eight shadow stores *)
  step. step. step.                                (* 81ac0 addiw ; 81ac4 li a0,7 ; 81ac8 bne *)
  rewrite ?(MState.unsigned_lit 6) by lia. rewrite ?r21_swrap32 by lia. rewrite ?r21_bv_eqb by lia.
  if_false.
  step.                                            (* 81acc j 81b00 *)
  eapply HK; [exact MU | exact WM | exact ST].
Qed.

(* ---- the latch from its own cut 0x81ac0 (Inv_B81ac0_at, seg_R21_a5c): addiw s6,s6,1; li a0,7; bne ---- *)

Lemma r21_a5c_next :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bz : Z),
    s6 = Z_to_bv 64 bz -> 0 <= bz <= 5 ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x816ec) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 18 = s2 /\ getr R 19 = s3v /\ getr R 20 = s4 /\ getr R 21 = s5 /\
         getr R 22 = Z_to_bv 64 (bz + 1) /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\ getr R 27 = s11 /\ m' = m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bz -> Hb.
  step. step. step.                                (* 81ac0 addiw ; 81ac4 li a0,7 ; 81ac8 bne *)
  rewrite ?(MState.unsigned_lit bz) by lia. rewrite ?r21_swrap32 by lia. rewrite ?r21_bv_eqb by lia.
  if_true.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 15 (split; [reflexivity|]). reflexivity.
Qed.

Lemma r21_a5c_last : forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    s6 = Z_to_bv 64 6 ->
    (forall (a0' s6' : word),
       evt rsegs Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x81b00) fc None m (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81ac0) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m -> HK.
  step. step. step.                                (* 81ac0 addiw ; 81ac4 li a0,7 ; 81ac8 bne *)
  rewrite ?(MState.unsigned_lit 6) by lia. rewrite ?r21_swrap32 by lia. rewrite ?r21_bv_eqb by lia.
  if_false.
  step.                                            (* 81acc j 81b00 *)
  eapply HK.
Qed.

(* ---- the tail 0x81b00 .. 0x81c54 (b = 6) ---- *)

Lemma r21_tail_evt : strcmp_wrap_contract ->
  forall (Q : machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv lo A S5 mr fw maj mnr pat h nm : Z) (sx : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= spv < 2 ^ 64 -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 S5)) ->
    ov_read_bytes rsegs m (wa (A + 32)) 8 = Some (le8 (Z_to_bv 64 0)) ->
    ov_read_bytes rsegs m (wa (A + 272)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa S5) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (mr + 266)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (S5 + 36)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (S5 + 22)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (mr + 268)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (S5 + 24)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (mr + 270)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (S5 + 26)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 272)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 56)) 4 = Some (le4 (Z_to_bv 64 h)) ->
    (h <> 0 ->
       ov_read_bytes rsegs m (wa (S5 + 20)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs m (wa (mr + 280)) 8 = Some (le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64 /\
       bytes_at rsegs m (S5 + 3) (sx ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sx /\
       bytes_at rsegs m nm (sx ++ [Z_to_bv 8 0]) /\
       Z.of_nat (strcmp_k sx sx) + 1 <= 2^40 /\
       addressable m (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       end_in_app (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       addressable m nm (Z.of_nat (strcmp_k sx sx) + 1) /\ end_in_app nm (Z.of_nat (strcmp_k sx sx) + 1) /\
       app_mem (S5 + 3 + 7) /\ app_mem (nm + 7) /\
       stk rsegs m lo spv /\ lo + STRCMP_WRAP_K <= spv /\ HIGHMEM_BEG <= lo /\ spv <= APPMEM_END /\
       (S5 + 3 + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= S5 + 3) /\
       (nm + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= nm) /\
       asan_cells m /\ shadow_rw m /\ MN.ro_agree rsegs m /\
       bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
       bytes_at rsegs m (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 245) [Z_to_bv 8 0]) ->
    (h = 0 -> forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word), a0' = Z_to_bv 64 0 ->
       evt rsegs Q
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs))) ->
    (h <> 0 -> forall (R : bvmap 5 word) (m' : word -> option byte),
       getr R 10 = Z_to_bv 64 0 ->
       getr R 2 = sp -> getr R 3 = gp -> getr R 4 = tp -> getr R 8 = s0 -> getr R 9 = s1 ->
       getr R 19 = s3 -> getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 -> getr R 24 = s8 ->
       getr R 25 = s9 -> getr R 26 = s10 ->
       munch [(spv - STRCMP_WRAP_K, spv)] m m' -> wmono rsegs m m' -> stk rsegs m' lo spv ->
       Q (MS R F (Z_to_bv 64 0x81c58) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81b00) fc None m (seg_rom rsegs)).
Proof.
  intros SC Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo A S5 mr fw maj mnr pat h nm sx -> -> -> Hsp HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R144 R32 R272 R2 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN K0 Kbf.
  step. step. step. if_true.                    (* 81b00 ld 144; 81b04 lbu 2; 81b08 bnez *)
  step. step. if_true.                          (* 81b10 ld 32; 81b14 beqz *)
  step. step. step. step. r21_shfix.            (* 81b1c ld 272; addi 266; srli; add *)
  step. step. step. step. if_true.              (* 81b2c lb; 81b30 ld 144; 81b34 lhu 0; 81b38 beqz *)
  step. step. r21_beq_refl.                     (* 81b40 lhu; 81b44 beq *)
  step. step. step. if_true.                    (* 81b4c ld 144; 81b50 lbu 36; 81b54 bnez *)
  step. step. step. step. r21_shfix.            (* 81b5c ld 272; addi 268; srli; add *)
  step. step. step. step. if_true.              (* 81b6c lb; 81b70 ld 144; 81b74 lhu 22; 81b78 beqz *)
  step. step. r21_beq_refl.                     (* 81b80 lhu; 81b84 beq *)
  step. step. step. step. r21_shfix.            (* 81b8c ld 272; addi 270; srli; add *)
  step. step. step. step. if_true.              (* 81b9c lb; 81ba0 ld 144; 81ba4 lhu 24; 81ba8 beqz *)
  step. step. r21_beq_refl.                     (* 81bb0 lhu; 81bb4 beq *)
  step. step. step. step. r21_shfix.            (* 81bbc ld 272; addi 272; srli; add *)
  step. step. step. step. if_true.              (* 81bcc lb; 81bd0 ld 144; 81bd4 lhu 26; 81bd8 beqz *)
  step. step. r21_beq_refl.                     (* 81be0 lhu; 81be4 beq *)
  step. step. step. step. r21_shfix.            (* 81bec ld 272; addi 56; srli; add *)
  step. step. if_true.                          (* 81bfc lb; 81c00 beqz *)
  step. step.                                   (* 81c08 lw; 81c0c beqz a0,81c60 *)
  destruct (Z.eq_dec h 0) as [E0 | E0].
  - if_true_by (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0)).
    eapply (K0 E0).
    exact (r21_eqb_eq _ _ (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0))).
  - if_false_by (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_neq h 0) E0)).
    destruct (HN E0) as (R20 & R280 & Hnm & HS1x & HS0x & HS2x & HK & HAX & HEX & HAY & HEY & HX7 & HY7 &
                         HST & HLO & HHM & HAE & HSEPx & HSEPy & HAC & HSW & HMIx & HGOT & HCF1 & HCF2).
    step. step. step. if_true.                  (* 81c10 ld 144; 81c14 lbu 20; 81c18 bnez *)
    step. step. step. step. r21_shfix.          (* 81c20 ld 272; addi 280; srli; add *)
    step. step. if_true.                        (* 81c30 lbu (check); 81c34 beqz *)
    step. step. step. step.                     (* 81c3c ld a1,0(a0); 81c40 ld 144; 81c44 addi 3; 81c48 bnez *)
    if_true_by (f_equal negb (r21_eqb0 nm Hnm)).
    step.                                       (* 81c54 jal wrapper_strcmp *)
    (* the wrapper runs on the normalized memory, which has the mem_inv its contract asks for *)
    pose proof (MN.mem_rel_normalize rsegs m HMIx) as REL.
    eapply evt_mono.
    { eapply MN.evt_normalize; [vm_compute; reflexivity | exact HMIx |].
      eapply SC with (sx := sx) (sy := sx) (lo := lo);
        rewrite ?(MState.unsigned_lit (S5 + 3)) by lia; rewrite ?(MState.unsigned_lit nm) by lia;
        rewrite ?(MState.unsigned_lit spv) by lia.
      - apply MN.bytes_at_normalize; [exact HMIx | exact HS1x].
      - exact HS0x.
      - apply MN.bytes_at_normalize; [exact HMIx | exact HS2x].
      - exact HS0x.
      - exact HK.
      - exact (rh_addr_rel m _ _ _ REL HAX).
      - exact HEX.
      - exact (rh_addr_rel m _ _ _ REL HAY).
      - exact HEY.
      - exact HX7.
      - exact HY7.
      - apply rh_stk_norm; [exact HMIx | exact HST | apply rh_not_ro_hi; unfold AC.GT, HIGHMEM_BEG in *; lia].
      - exact HLO.
      - exact HHM.
      - exact HAE.
      - exact HSEPx.
      - exact HSEPy.
      - exact (rh_acells_rel m _ REL HAC).
      - exact (rh_shrw_rel m _ REL HSW).
      - apply MN.mem_inv_normalize.
      - apply MN.bytes_at_normalize; [exact HMIx | exact HGOT].
      - apply MN.bytes_at_normalize; [exact HMIx | exact HCF1].
      - apply MN.bytes_at_normalize; [exact HMIx | exact HCF2]. }
    intros msx (msx0 & Pn & MR & RS).
    unfold strcmp_wrap_post in Pn.
    destruct Pn as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E & Hr & Hr0 & MU0 & WM0 & _ & STq0 & _).
    assert (Er : r = Z_to_bv 64 0) by (apply Hr0; reflexivity).
    subst msx0.
    destruct msx as [regs1 fregs1 pcv1 svc1 resv1 fcsr1 mem1 rom1].
    destruct MR as (Hr1 & Hf1 & Hpc1 & Hsvc1 & Hres1 & Hfc1 & Hrom1 & Hmem).
    cbn in Hr1, Hf1, Hpc1, Hsvc1, Hres1, Hfc1, Hrom1, Hmem, RS.
    rewrite ?(MState.unsigned_lit spv) in MU0, STq0 by lia.
    match goal with |- Q ?x => replace x with (MS regs1 F (Z_to_bv 64 0x81c58) fc None mem1 (seg_rom rsegs)) end.
    2:{ symmetry. unfold MS. subst. f_equal.
        first [ apply ret_pc_even; [lia | reflexivity] | symmetry; apply ret_pc_even; [lia | reflexivity] ]. }
    try rewrite Er in Hr1. subst regs1.
    apply (Kbf E0); try reflexivity.
    + exact (MN.munch_rel rsegs _ m _ mem1 m0' REL Hmem RS MU0).
    + exact (MN.wmono_rel rsegs m _ mem1 m0' REL Hmem RS WM0).
    + exact (rh_stk_back mem1 m0' _ _ Hmem STq0).
Qed.

(* ---- the has_identity_record = 0 path 0x81c60 .. 0x81ca4 (the P1 suffix) ---- *)

Lemma r21_p1_evt_n : ASS.asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Q : Z) (junk : list byte),
    s1 = Z_to_bv 64 A ->
    AC.GT <= bv_unsigned s3v -> bv_unsigned s3v + 392 <= A -> A + 448 <= 2 ^ 64 ->
    bv_unsigned s3v <= Q -> Q + 187 <= bv_unsigned s3v + 291 ->
    (forall i, 0 <= i < 392 -> in_shadow (bv_unsigned s3v + i)) ->
    rw_cells rsegs m (bv_unsigned s3v + 272) [CB 19 junk] ->
    stk rsegs m (bv_unsigned s3v) (bv_unsigned s3v + 392) ->
    bytes_at rsegs m (A + 8) (le8 (Z_to_bv 64 Q)) ->
    mem_inv rsegs m -> asan_cells m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81ca8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3v /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(bv_unsigned s3v, bv_unsigned s3v + 291)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned s3v) (bv_unsigned s3v + 392))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Q junk -> HSgt HSA HA1 HQ1 HQ2 Hsh RW ST R8 HMI HAC.
  unfold ASS.asan_set_shadow_f8_contract, ASS.asan_set_shadow_contract, ASS.ASAN_SET_SHADOW_F8 in SET.
  cbv zeta in SET.
  unfold AC.GT in HSgt.
  pose proof (rw_cells_bound _ _ _ _ RW) as HB. cbn [cells_size csize Nat.add] in HB.
  pose proof (bv_unsigned_in_range 64 s3v) as HS3r. change (bv_modulus 64) with (2 ^ 64) in HS3r.
  pose proof (munch_refl [(bv_unsigned s3v, bv_unsigned s3v + 291)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.                                         (* 81c60 li s2,-8 *)
  step. step. step. step. step. step. step.     (* 81c64 .. 81c98 : the 14 shadow stores *)
  step. step. step. step. step. step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) => tryif constr_eq mm m1 then idtac else rename mm into m1
  end.
  pose proof (rh_rdn m1 (A + 8) _ 8 R8 (length_le8 _)) as RD16.
  step. step. step.                             (* 81c9c li a1,187 ; 81ca0 ld a0,8(s1) ; 81ca4 jal *)
  (* the 187 bytes [Q, Q + 187) as a cell run *)
  assert (HstkQ : stk rsegs m1 Q (Q + 187)).
  { destruct ST as (S0 & S1 & SH). split; [lia|]. split; [lia|]. intros a Ha. apply SH. lia. }
  destruct (rh_bytes_of_present 187%nat m1 Q ltac:(lia) ltac:(lia)) as (junkQ & HjQ & HjQl).
  { intros k Hk. destruct HstkQ as (_ & _ & SH). exact (proj2 (SH (Q + Z.of_nat k) ltac:(lia))). }
  assert (RWQ : rw_cells rsegs m1 Q [CB 187 junkQ]).
  { rewrite <- HjQl. apply rh_rwc_CB; [exact HjQ|]. rewrite HjQl.
    split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct HstkQ as (_ & _ & SH). exact (proj1 (SH (Q + i) ltac:(lia))). }
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (EQ1 : bv_unsigned (Z_to_bv 64 Q) = Q) by (apply MState.unsigned_lit; lia).
  assert (EQ2 : bv_unsigned (Z_to_bv 64 187) = 187) by reflexivity.
  eapply evt_cut.
  { eapply SET with (junk := junkQ).
    all: rewrite ?EQ1, ?EQ2.
    - intros i Hi. replace (Q + i) with (bv_unsigned s3v + (Q - bv_unsigned s3v + i)) by lia. apply Hsh. lia.
    - exact RWQ.
    - exact HAC1.
    - exact HMI. }
  intros ms' PO. unfold ASS.asan_set_shadow_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU2 & WM2 & MI2 & RW2).
  subst ms'.
  rewrite EQ1, EQ2 in MU2, RW2.
  change (Z.to_nat 187) with 187%nat in RW2.
  assert (HQb : bytes_at rsegs m' Q (repeat (Z_to_bv 8 0xf8) 187)).
  { destruct RW2 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (Hsub : sub_fp [(Q, Q + 187)] [(bv_unsigned s3v, bv_unsigned s3v + 291)]).
  { intros x Hx. cbn [outside] in Hx |- *. lia. }
  pose proof (munch_trans _ m m1 m' MU (munch_weaken _ _ m1 m' Hsub MU2)) as MUf.
  assert (STf : stk rsegs m' (bv_unsigned s3v) (bv_unsigned s3v + 392)).
  { apply (rh_stk_keep [(Q, Q + 187)] m1 m' _ _ ST MU2 WM2).
    intros x Hx Hnx. cbn [outside] in Hnx.
    exact (rh_ba_rd m' Q _ x HQb ltac:(rewrite repeat_length; lia)). }
  replace (ret_pc (Z_to_bv 64 0x81ca8)) with (Z_to_bv 64 0x81ca8)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 10 (split; [reflexivity|]).
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2) | exact STf].
Qed.

(* The same run from ro_agree: the body goes on the normalized memory. *)
Lemma r21_p1_evt : ASS.asan_set_shadow_f8_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A Q : Z) (junk : list byte),
    s1 = Z_to_bv 64 A ->
    AC.GT <= bv_unsigned s3v -> bv_unsigned s3v + 392 <= A -> A + 448 <= 2 ^ 64 ->
    bv_unsigned s3v <= Q -> Q + 187 <= bv_unsigned s3v + 291 ->
    (forall i, 0 <= i < 392 -> in_shadow (bv_unsigned s3v + i)) ->
    rw_cells rsegs m (bv_unsigned s3v + 272) [CB 19 junk] ->
    stk rsegs m (bv_unsigned s3v) (bv_unsigned s3v + 392) ->
    bytes_at rsegs m (A + 8) (le8 (Z_to_bv 64 Q)) ->
    MN.ro_agree rsegs m -> asan_cells m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81ca8) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3v /\ getr R 23 = s7 /\ getr R 24 = s8 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(bv_unsigned s3v, bv_unsigned s3v + 291)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' (bv_unsigned s3v) (bv_unsigned s3v + 392))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81c60) fc None m (seg_rom rsegs)).
Proof.
  intros SET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A Q junk Es1 HSgt HSA HA1 HQ1 HQ2 Hsh RW ST R8 HRO HAC.
  pose proof (MN.mem_rel_normalize rsegs m HRO) as REL.
  pose proof HSgt as HSgt'. unfold AC.GT in HSgt'.
  pose proof (bv_unsigned_in_range 64 s3v) as HS3r. change (bv_modulus 64) with (2 ^ 64) in HS3r.
  eapply evt_mono.
  { eapply MN.evt_normalize; [vm_compute; reflexivity | exact HRO |].
    eapply (r21_p1_evt_n SET) with (A := A) (Q := Q) (junk := junk).
    - exact Es1.
    - exact HSgt.
    - exact HSA.
    - exact HA1.
    - exact HQ1.
    - exact HQ2.
    - exact Hsh.
    - apply rh_rwc_norm; [exact HRO | exact RW | apply rh_not_ro_hi; cbn; unfold AC.GT; lia].
    - apply rh_stk_norm; [exact HRO | exact ST | apply rh_not_ro_hi; unfold AC.GT; lia].
    - apply MN.bytes_at_normalize; [exact HRO | exact R8].
    - apply MN.mem_inv_normalize.
    - exact (rh_acells_rel m _ REL HAC). }
  intros msx (msx0 & Pn & MR & RS).
  destruct Pn as (R & m0' & E & P2 & P3 & P4 & P8 & P9 & P19 & P23 & P24 & P25 & P26 & MU & WM & ST').
  subst msx0.
  destruct msx as [regs1 fregs1 pcv1 svc1 resv1 fcsr1 mem1 rom1].
  destruct MR as (Hr1 & Hf1 & Hpc1 & Hsvc1 & Hres1 & Hfc1 & Hrom1 & Hmem).
  cbn in Hr1, Hf1, Hpc1, Hsvc1, Hres1, Hfc1, Hrom1, Hmem, RS.
  exists R, mem1.
  split; [unfold MS; subst; reflexivity|].
  do 10 (split; [assumption|]).
  split; [exact (MN.munch_rel rsegs _ m _ mem1 m0' REL Hmem RS MU)|].
  split; [exact (MN.wmono_rel rsegs m _ mem1 m0' REL Hmem RS WM)|].
  exact (rh_stk_back mem1 m0' _ _ Hmem ST').
Qed.

(* The runtime cells the strcmp wrapper reads, from the runtime invariant RT. *)
Lemma r21_cells : forall sp mem md, AsanRTInv.RT sp mem md ->
  asan_cells mem /\ shadow_rw mem /\ bytes_at rsegs mem GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs mem (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs mem (CF + 245) [Z_to_bv 8 0].
Proof.
  intros sp mem md HRT.
  destruct HRT as (HAC0 & HSW0 & _ & HCF0 & _).
  destruct HCF0 as (HGOTCF & _ & _ & _ & _ & _ & HCF240 & _).
  split; [exact HAC0|]. split; [exact HSW0|]. split; [exact HGOTCF|].
  split.
  { pose proof (rh_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 10 1 HCF240
                  ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 10) with (CF + 250) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 10 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 1] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
  { pose proof (rh_ba_sub mem (RT_CF + 240) (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]) 5 1 HCF240
                  ltac:(cbn; lia)) as Hs.
    replace (RT_CF + 240 + Z.of_nat 5) with (CF + 245) in Hs by (unfold CF, RT_CF; lia).
    replace (firstn 1 (skipn 5 (cf_b [0;0;0;0;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;0]))) with [Z_to_bv 8 0] in Hs
      by (vm_compute; reflexivity).
    exact Hs. }
Qed.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* wrapper_strcmp (0x42aa0) and meta_fill_f8 (0x55144), taken on their lib/B contracts. *)
Hypothesis SC : strcmp_wrap_contract.
Hypothesis SET : ASS.asan_set_shadow_f8_contract.

(* The kind-name table (0x9f580, 112 bytes) is a registered global, so FRA makes it addressable. *)
Lemma r21_kind_addr : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md -> addressable mem KNC.KIND_NAME 112.
Proof.
  intros g fr hb regs mem md HFRA.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  apply rh_addr_join; [unfold KNC.KIND_NAME; lia | lia | unfold KNC.KIND_NAME, APPMEM_END; lia |].
  intros i Hi. apply HAG. exists 0x9f580, 112. split; [|unfold KNC.KIND_NAME in *; lia].
  unfold AF.frame_AG. cbn [In]. repeat (first [ left; reflexivity | right ]).
Qed.

Lemma seg_R21 : forall b : nat,
  Hat B APIf ra (Inv_B816ec_at B APIf ra) (S b) ->
  Hcut B APIf ra (Inv_B81c58 B APIf ra) ->
  Hcut B APIf ra (Inv_B81ca8 B APIf ra) ->
  Hat B APIf ra (Inv_B81aa0_at B APIf ra) b.
Proof.
  intros b Hnext Hbf4 Hc44 g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT &
                    (Hgn & Hb6 & H22 & HOUR & HRBE & H21 & HRB & H27)).
  subst c. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hfrpl & HfrA & _ & Hfrwr).
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGTfr & Happfr).
  pose proof (rh_sh_in B APIf ra g fr [] regs mem md HFRA) as Hshin.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKs : STRCMP_WRAP_K = 2272) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (W0 & W1 & _); split; [exact W0 | exact W1]).
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HA4 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  rewrite Haspz in Hwlo, Hwstk, Hfrpl.
  assert (Hspb : 0 <= sp <= APPMEM_END) by (unfold APPMEM_END in *; lia).
  unfold AC.GT in HGTfr.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HSfrhi : Sfr fr + 392 <= HIGHMEM_BEG).
  { pose proof (Hshin (Sfr fr + 391) ltac:(lia)) as (IS & _).
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  assert (HSfrGT : AC.GT <= Sfr fr) by (unfold Sfr, shadow_addr, ASAN_K, AC.GT; Z.div_mod_to_equations; lia).
  assert (Hs3 : bv_unsigned (getr regs 19) = Sfr fr).
  { unfold rg in Hr19. rewrite Hr19. apply MState.unsigned_lit. unfold AC.GT, HIGHMEM_BEG in *. lia. }
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HAlo : HIGHMEM_BEG <= A) by (unfold HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (Hfrhi : fr + 3136 <= 2 ^ 64).
  { pose proof (Happfr (fr + 3135) ltac:(lia)) as Hq.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hq. lia. }
  (* the latch's 17 shadow bytes S(fr) + 296 .. + 312 *)
  pose proof HRT as (HAC0 & HSW0 & _).
  assert (HSTl : stk rsegs mem (Sfr fr + 296) (Sfr fr + 313)).
  { split; [unfold AC.GT in HSfrGT; lia|]. split; [unfold HIGHMEM_BEG in HSfrhi; lia|].
    intros a Ha. destruct (Hshin a ltac:(lia)) as (Hsa & _). exact (HSW0 a Hsa). }
  assert (HRWl : exists junk, rw_cells rsegs mem (Sfr fr + 296) [CB 17 junk]).
  { destruct (rh_bytes_of_present 17%nat mem (Sfr fr + 296) ltac:(unfold AC.GT in HSfrGT; lia)
                ltac:(unfold HIGHMEM_BEG in HSfrhi; lia)) as (junk & Hj & Hjl).
    { intros k Hk. destruct (Hshin (Sfr fr + 296 + Z.of_nat k) ltac:(lia)) as (Hsa & _).
      exact (proj2 (HSW0 _ Hsa)). }
    exists junk. rewrite <- Hjl. apply rh_rwc_CB; [exact Hj|]. rewrite Hjl.
    split; [unfold AC.GT in HSfrGT; lia|]. split; [unfold HIGHMEM_BEG in HSfrhi; cbn; lia|].
    intros i Hi. cbn in Hi. destruct (Hshin (Sfr fr + 296 + i) ltac:(lia)) as (Hsa & _).
    exact (proj1 (HSW0 _ Hsa)). }
  destruct HRWl as (junk & HRWl).
  assert (HoutW1 : forall x, (x < Sfr fr + 296 \/ Sfr fr + 313 <= x) -> outside [(Sfr fr + 296, Sfr fr + 313)] x)
    by (intros x Hx; cbn [outside]; split; [lia | exact I]).
  assert (HappW1 : forall x, app_mem x -> outside [(Sfr fr + 296, Sfr fr + 313)] x).
  { intros x Hx. destruct (rh_out_dec [(Sfr fr + 296, Sfr fr + 313)] x) as [Ho|Ho]; [exact Ho|]. exfalso.
    cbn [outside] in Ho. destruct (Hshin x ltac:(lia)) as (Hsx & _). exact (app_not_shadow x Hx Hsx). }
  (* the model facts of the identity-record check *)
  pose proof (rb_istar_range (g_in g)) as Hi11.
  pose proof (rb_mrow_range (g_in g)) as (Hmr0 & Hmr1 & Hmr8).
  pose proof (rb_mb_len (g_in g)) as HROWL.
  pose proof (rb_RID_len (g_in g) 7) as HIDL.
  destruct (rb_rtm_fw (g_in g)) as (Ehf & Efw).
  destruct (rb_rtm_ver (g_in g)) as (Ehv & Emaj & Emin & Epat).
  destruct (rb_row_facts (istar (g_in g)) Hi11) as (Hh32 & Ehid & Hnmf).
  destruct (rb_row_le (istar (g_in g)) Hi11) as (L56 & L280).
  change (rowb (istar (g_in g))) with (rt_mb (g_in g)) in Hh32, Ehid, Hnmf, L56, L280.
  (* the run *)
  apply (sl_run_lib regs (Z_to_bv 64 0x81aa0) mem md
    (fun R pc' mem' =>
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       exists m1, munch [(Sfr fr + 296, Sfr fr + 313)] mem m1 /\ wmono rsegs mem m1 /\
         stk rsegs m1 (Sfr fr + 296) (Sfr fr + 313) /\
       (((b <= 5)%nat /\ pc' = Z_to_bv 64 0x816ec /\ mem' = m1 /\ getr R 21 = getr regs 21 /\
           getr R 22 = Z_to_bv 64 (Z.of_nat b + 1) /\ getr R 27 = getr regs 27) \/
        (b = 6%nat /\ pc' = Z_to_bv 64 0x81c58 /\ getr R 10 = Z_to_bv 64 0 /\
           munch [(sp - STRCMP_WRAP_K, sp)] m1 mem' /\ wmono rsegs m1 mem' /\
           stk rsegs mem' (g_S g - AF.SLOT_STACK) sp) \/
        (b = 6%nat /\ pc' = Z_to_bv 64 0x81ca8 /\
           munch [(Sfr fr, Sfr fr + 291)] m1 mem' /\ wmono rsegs m1 mem' /\
           stk rsegs mem' (Sfr fr) (Sfr fr + 392))))
    (Post B APIf ra g)).
  { exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg in H22.
    destruct (le_lt_dec b 5) as [Hb5 | Hb5].
    - (* b <= 5: back to the round-trip head *)
      eapply evt_mono.
      + apply (r21_latch_next) with (bz := Z.of_nat b) (junk := junk);
          try rewrite Hs3;
          repeat match goal with
          | |- context [bv_unsigned ?s] =>
              progress change (bv_unsigned s) with (bv_unsigned (getr regs 19)); rewrite Hs3
          end;
          [ exact H22 | lia | exact HRWl | exact HSTl ].
      + intros ms' (R & m' & E & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 &
                    P26 & P27 & MU & WM & ST).
        match type of MU with
        | context [bv_unsigned ?s] => change (bv_unsigned s) with (bv_unsigned (getr regs 19)) in MU, ST
        end.
        rewrite Hs3 in MU, ST.
        exists R, (Z_to_bv 64 0x816ec), m'. split; [exact E|].
        split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
        split; [exact P19|]. split; [exact P23|]. split; [exact P24|]. split; [exact P25|]. split; [exact P26|].
        exists m'. split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
        left. split; [exact Hb5|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact P21|]. split; [exact P22 | exact P27].
    - (* b = 6: the identity-record check *)
      assert (Eb : b = 6%nat) by lia. subst b.
      change (Z.of_nat 6) with 6 in H22.
      unfold rg in Hr9, Hr26. try unfold rg in Hr2.
      apply (r21_latch_last _) with (junk := junk);
        try rewrite Hs3;
        repeat match goal with
        | |- context [bv_unsigned ?s] =>
            progress change (bv_unsigned s) with (bv_unsigned (getr regs 19)); rewrite Hs3
        end;
        [ exact H22 | exact HRWl | exact HSTl | ].
      intros a0' s6' m1 MU1 WM1 ST1.
      (* the frame, RBE and the turn records at m1 *)
      destruct (rh_sh_move B APIf ra empty FF g fr [] regs regs mem m1 md 296 313 HFRA HENT
                  ltac:(lia) ltac:(lia) ltac:(lia) MU1 WM1
                  ltac:(intros qq Hqq; destruct ST1 as (_ & _ & HST1); exact (proj2 (HST1 qq Hqq)))
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (HFRA1 & HENT1).
      assert (HRBE1 : RBE g fr regs m1).
      { apply (rh_RBE_keep_sh g fr regs regs _ mem m1 A HRBE MU1 Hfr8 ltac:(unfold AC.GT; lia) Hr9 ltac:(lia)
                 HA4 eq_refl).
        - intros x Hx. apply HoutW1. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
        - intros x Hx. cbn [outside] in Hx. lia. }
      assert (HRB1 : RB g fr 6 (RID (g_in g) 7) (RFG (g_in g) 7) regs m1).
      { apply (rh_RB_keep g fr 6 (RID (g_in g) 7) (RFG (g_in g) 7) regs regs _ mem m1 MU1
                 (rb_RID_len (g_in g) 7) (rb_RFG_len (g_in g) 7 ltac:(lia)));
          [ intros x Hx; apply HappW1, Happfr; lia | reflexivity | reflexivity | reflexivity | exact HRB ]. }
      pose proof HRB1 as (_ & HCUR1 & HOUR1 & _ & HIDB1 & _).
      unfold IDBr in HIDB1.
      pose proof HRBE1 as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
        S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUTA1 & HA2176 & HNM1 & HOUR6 & HTBL & HBOX &
        HMROW & _).
      pose proof HFRA1 as HF1.
      destruct HF1 as (A1 & sp1 & s51 & HRT1 & HAH1 & Hro1 & Hsn1 & Hhalt1 & Hgimg1 & Hr2_1 & Hspm1 & Haspz1 &
        Hstklo1 & Hr4_1 & Hr8_1 & Hr9_1 & Hr3_1 & Hr19_1 & Hr26_1 & Hfrm1 & Hs5_1 & HAm1 & HAS1 & Hspa1 & Hfa1 &
        HA448_1 & HS4_1 & HAPP1 & Hspill1 & Hsel1 & Hfr56_1 & Hloc1 & Hhdr1_1 & Hhdr2_1 & Hsh1 & Hwin1 & Hsaved1 &
        Herrno1 & HAG1 & HWA1 & HSHI1_1 & HSHI2_1 & HSHI3_1 & Hhb1 & Hlive1).
      assert (Esp1 : sp1 = sp) by (rewrite Haspz in Haspz1; lia). subst sp1.
      pose proof (r21_cells sp m1 md HRT1) as (HAC1 & HSW1 & HGOT1 & HCF1 & HCF2).
      (* the spill words the tail loads *)
      pose proof (rh_spill_at regs m1 A 144 (fr + 2176) S144 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q144.
      pose proof (rh_spill_at regs m1 A 32 0 S32 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q32.
      pose proof (rh_spill_at regs m1 A 272 (mrow (g_in g)) S272 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q272.
      pose proof (rh_spill_at regs m1 A 8 (Sfr fr + 68) S8 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q8.
      assert (R144 := rh_rdn m1 _ _ 8 Q144 (length_le8 _)).
      assert (R32 := rh_rdn m1 _ _ 8 Q32 (length_le8 _)).
      assert (R272 := rh_rdn m1 _ _ 8 Q272 (length_le8 _)).
      (* the catalogue row's granules have shadow byte 0 *)
      assert (HADrow : forall p, CAT <= p -> p + 8 <= CAT + 3256 -> addressable m1 p 8).
      { intros p Hp1 Hp2. apply rh_addr_join; [unfold CAT in *; lia | lia | unfold CAT, APPMEM_END in *; lia |].
        intros i Hi. exact (rh_cat_addr B APIf ra g fr [] regs m1 md HFRA1 (p + i) ltac:(lia)). }
      assert (K266 : ov_read_bytes rsegs m1 (wa (Z.shiftr (mrow (g_in g) + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 m1 (mrow (g_in g) + 264));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      assert (K268 : ov_read_bytes rsegs m1 (wa (Z.shiftr (mrow (g_in g) + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 m1 (mrow (g_in g) + 264));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      assert (K270 : ov_read_bytes rsegs m1 (wa (Z.shiftr (mrow (g_in g) + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 m1 (mrow (g_in g) + 264));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      assert (K272 : ov_read_bytes rsegs m1 (wa (Z.shiftr (mrow (g_in g) + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 m1 (mrow (g_in g) + 272));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      assert (K56 : ov_read_bytes rsegs m1 (wa (Z.shiftr (mrow (g_in g) + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 m1 (mrow (g_in g) + 56));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      assert (K280 : ov_read_bytes rsegs m1 (wa (Z.shiftr (mrow (g_in g) + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 m1 (mrow (g_in g) + 280));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      (* the identity record's bytes (RID_7) *)
      assert (R2 : ov_read_bytes rsegs m1 (wa (fr + 2176 + 2)) 1 = Some [Z_to_bv 8 1]).
      { pose proof (r21_rd1 m1 (fr + 2176) (RID (g_in g) 7) 2 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 2) with (fr + 2176 + 2) in H by lia.
        rewrite (r21_byte1 (nth 2 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehf) in H. exact H. }
      assert (R36 : ov_read_bytes rsegs m1 (wa (fr + 2176 + 36)) 1 = Some [Z_to_bv 8 1]).
      { pose proof (r21_rd1 m1 (fr + 2176) (RID (g_in g) 7) 36 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 36) with (fr + 2176 + 36) in H by lia.
        rewrite (r21_byte1 (nth 36 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehv) in H. exact H. }
      assert (R0 : ov_read_bytes rsegs m1 (wa (fr + 2176)) 2 = Some (le2 (Z_to_bv 64 (fw_milli (RID (g_in g) 7))))).
      { pose proof (r21_rd2 m1 (fr + 2176) (RID (g_in g) 7) 0 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 0) with (fr + 2176) in H by lia. exact H. }
      assert (R22 : ov_read_bytes rsegs m1 (wa (fr + 2176 + 22)) 2 =
                    Some (le2 (Z_to_bv 64 (major (RID (g_in g) 7))))).
      { pose proof (r21_rd2 m1 (fr + 2176) (RID (g_in g) 7) 22 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 22) with (fr + 2176 + 22) in H by lia. exact H. }
      assert (R24 : ov_read_bytes rsegs m1 (wa (fr + 2176 + 24)) 2 =
                    Some (le2 (Z_to_bv 64 (minor (RID (g_in g) 7))))).
      { pose proof (r21_rd2 m1 (fr + 2176) (RID (g_in g) 7) 24 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 24) with (fr + 2176 + 24) in H by lia. exact H. }
      assert (R26 : ov_read_bytes rsegs m1 (wa (fr + 2176 + 26)) 2 =
                    Some (le2 (Z_to_bv 64 (patch (RID (g_in g) 7))))).
      { pose proof (r21_rd2 m1 (fr + 2176) (RID (g_in g) 7) 26 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 26) with (fr + 2176 + 26) in H by lia. exact H. }
      (* the catalogue row's bytes *)
      assert (M266 : ov_read_bytes rsegs m1 (wa (mrow (g_in g) + 266)) 2 =
                     Some (le2 (Z_to_bv 64 (fw_milli (RID (g_in g) 7))))).
      { pose proof (r21_rd2 m1 (mrow (g_in g)) (rt_mb (g_in g)) 266 HMROW ltac:(rewrite HROWL; lia)) as H.
        replace (mrow (g_in g) + Z.of_nat 266) with (mrow (g_in g) + 266) in H by lia.
        rewrite Efw. exact H. }
      assert (M268 : ov_read_bytes rsegs m1 (wa (mrow (g_in g) + 268)) 2 =
                     Some (le2 (Z_to_bv 64 (major (RID (g_in g) 7))))).
      { pose proof (r21_rd2 m1 (mrow (g_in g)) (rt_mb (g_in g)) 268 HMROW ltac:(rewrite HROWL; lia)) as H.
        replace (mrow (g_in g) + Z.of_nat 268) with (mrow (g_in g) + 268) in H by lia.
        rewrite Emaj. exact H. }
      assert (M270 : ov_read_bytes rsegs m1 (wa (mrow (g_in g) + 270)) 2 =
                     Some (le2 (Z_to_bv 64 (minor (RID (g_in g) 7))))).
      { pose proof (r21_rd2 m1 (mrow (g_in g)) (rt_mb (g_in g)) 270 HMROW ltac:(rewrite HROWL; lia)) as H.
        replace (mrow (g_in g) + Z.of_nat 270) with (mrow (g_in g) + 270) in H by lia.
        rewrite Emin. exact H. }
      assert (M272 : ov_read_bytes rsegs m1 (wa (mrow (g_in g) + 272)) 2 =
                     Some (le2 (Z_to_bv 64 (patch (RID (g_in g) 7))))).
      { pose proof (r21_rd2 m1 (mrow (g_in g)) (rt_mb (g_in g)) 272 HMROW ltac:(rewrite HROWL; lia)) as H.
        replace (mrow (g_in g) + Z.of_nat 272) with (mrow (g_in g) + 272) in H by lia.
        rewrite Epat. exact H. }
      assert (M56 : ov_read_bytes rsegs m1 (wa (mrow (g_in g) + 56)) 4 =
                    Some (le4 (Z_to_bv 64 (RcSynth.rw32 (rt_mb (g_in g)) 56)))).
      { pose proof (r21_rd4 m1 (mrow (g_in g)) (rt_mb (g_in g)) 56 HMROW ltac:(rewrite HROWL; lia)) as H.
        replace (mrow (g_in g) + Z.of_nat 56) with (mrow (g_in g) + 56) in H by lia.
        rewrite <- L56. exact H. }
      eapply (r21_tail_evt SC) with (spv := sp) (lo := g_S g - AF.SLOT_STACK) (A := A) (S5 := fr + 2176)
        (mr := mrow (g_in g)) (fw := fw_milli (RID (g_in g) 7)) (maj := major (RID (g_in g) 7))
        (mnr := minor (RID (g_in g) 7)) (pat := patch (RID (g_in g) 7))
        (h := RcSynth.rw32 (rt_mb (g_in g)) 56) (nm := RcSynth.rname (rt_mb (g_in g)))
        (sx := removelast (rt_nb (g_in g))).
      all: try first [ exact Hr2 | exact Hr9 | exact Hr26 | exact R144 | exact R32 | exact R272 | exact R2
                     | exact K266 | exact K268 | exact K270 | exact K272 | exact K56 | exact K280 | exact R0
                     | exact M266 | exact R36 | exact R22 | exact M268 | exact R24 | exact M270 | exact R26
                     | exact M272 | exact M56 | exact Hh32
                     | (unfold CAT, APPMEM_END in *; lia) ].
      { (* the name strings, when the row has an identity record *)
        intros Hh0.
        assert (Hhid : RcEmit.em_hid (rt_mb (g_in g)) <> 0) by (intros E; apply Hh0; apply Ehid; exact E).
        destruct (Hnmf Hhid) as (Hnm0 & Hnm1 & HROn & HAGnm).
        assert (Hn6 : rt_n (g_in g) 6 <> 0) by (apply (proj2 (rb_rtm_hid (g_in g))); exact Hhid).
        destruct (rb_rtm_name (g_in g) Hn6) as (Ehn & Efn & Elast & Hall & Hlen16).
        apply andb_true_iff in Hlen16 as [Hl1 Hl2]. apply Nat.leb_le in Hl1. apply Nat.leb_le in Hl2.
        assert (Enb : rt_nb (g_in g) = removelast (rt_nb (g_in g)) ++ [Z_to_bv 8 0]).
        { change (Z_to_bv 8 0) with (zb 0). rewrite <- Elast.
          apply app_removelast_last. intros E. rewrite E in Hl1. cbn [length] in Hl1. lia. }
        assert (HLsx : (length (removelast (rt_nb (g_in g))) + 1 = length (rt_nb (g_in g)))%nat)
          by (rewrite Enb at 2; rewrite length_app; cbn [length]; lia).
        rewrite r21_strcmp_k_refl.
        assert (R20 : ov_read_bytes rsegs m1 (wa (fr + 2176 + 20)) 1 = Some [Z_to_bv 8 1]).
        { pose proof (r21_rd1 m1 (fr + 2176) (RID (g_in g) 7) 20 HIDB1 ltac:(rewrite HIDL; lia)) as H.
          replace (fr + 2176 + Z.of_nat 20) with (fr + 2176 + 20) in H by lia.
          rewrite (r21_byte1 (nth 20 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehn) in H. exact H. }
        assert (R280 : ov_read_bytes rsegs m1 (wa (mrow (g_in g) + 280)) 8 =
                       Some (le8 (Z_to_bv 64 (RcSynth.rname (rt_mb (g_in g)))))).
        { pose proof (r21_rd8 m1 (mrow (g_in g)) (rt_mb (g_in g)) 280 HMROW ltac:(rewrite HROWL; lia)) as H.
          replace (mrow (g_in g) + Z.of_nat 280) with (mrow (g_in g) + 280) in H by lia.
          rewrite <- L280. exact H. }
        assert (HBX : bytes_at rsegs m1 (fr + 2176 + 3) (removelast (rt_nb (g_in g)) ++ [Z_to_bv 8 0])).
        { rewrite <- Enb.
          assert (Es : firstn (length (rt_nb (g_in g))) (skipn 3 (RID (g_in g) 7)) = rt_nb (g_in g)).
          { rewrite <- Efn at 2. unfold model_name, RcIdentModel.get, RcIdentModel.OFF_NAME,
              RcIdentModel.NAME_CAP. rewrite firstn_firstn. f_equal. lia. }
          pose proof (rh_ba_sub m1 (fr + 2176) (RID (g_in g) 7) 3 (length (rt_nb (g_in g))) HIDB1
                        ltac:(rewrite HIDL; lia)) as X.
          rewrite Es in X. replace (fr + 2176 + Z.of_nat 3) with (fr + 2176 + 3) in X by lia. exact X. }
        assert (HBY : bytes_at rsegs m1 (RcSynth.rname (rt_mb (g_in g))) (rt_nb (g_in g)))
          by (apply (r21_ro_bytes (rt_nb (g_in g)) m1 _ Hro1); [exact HROn | lia | lia]).
        assert (HNin : ~ In (Z_to_bv 8 0) (removelast (rt_nb (g_in g)))).
        { intros Hin. pose proof (proj1 (forallb_forall _ _) Hall (Z_to_bv 8 0) Hin) as X.
          vm_compute in X. discriminate X. }
        assert (HAY : addressable m1 (RcSynth.rname (rt_mb (g_in g)))
                        (Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1)).
        { apply rh_addr_join; [lia | lia | unfold APPMEM_END; lia |].
          intros i Hi. apply HAG1. replace (RcSynth.rname (rt_mb (g_in g)) + i)
            with (RcSynth.rname (rt_mb (g_in g)) + Z.of_nat (Z.to_nat i)) by lia.
          apply HAGnm.
          assert (HLen : length (img_cstr (RcSynth.rname (rt_mb (g_in g))) 16) = length (rt_nb (g_in g)))
            by reflexivity.
          rewrite HLen. lia. }
        assert (HAX : addressable m1 (fr + 2176 + 3) (Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1)).
        { apply (addressable_sub m1 (fr + 2176) 38 3 (Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1)
                   HA2176); lia. }
        split; [exact R20|]. split; [exact R280|]. split; [lia|].
        split; [exact HBX|]. split; [exact HNin|].
        split; [rewrite <- Enb; exact HBY|].
        split; [lia|]. split; [exact HAX|].
        split; [right; apply Happfr; lia|]. split; [exact HAY|].
        split; [right; unfold app_mem, LOWMEM_END; left; lia|].
        split; [apply Happfr; lia|].
        split; [unfold app_mem, LOWMEM_END; left; lia|].
        split; [exact (proj1 (LFr.stk_split rsegs m1 (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin1 ltac:(lia)))|].
        split; [lia|].
        split; [unfold APPMEM_END, HIGHMEM_BEG in *; lia|].
        split; [lia|].
        split; [destruct (Hfrpl STRCMP_WRAP_K ltac:(lia)) as [Hc|Hc]; [left | right]; lia|].
        split; [left; unfold HIGHMEM_BEG in *; lia|].
        split; [exact HAC1|]. split; [exact HSW1|]. split; [exact Hro1|].
        split; [exact HGOT1|]. split; [exact HCF1 | exact HCF2]. }
      { (* has_identity_record = 0: the meta_fill_f8 suffix to 0x81ca8 *)
        intros E0 t0' t1' t2' a0'' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' _.
        assert (HSTf : stk rsegs m1 (Sfr fr) (Sfr fr + 392)).
        { split; [unfold AC.GT in HSfrGT; lia|]. split; [unfold HIGHMEM_BEG in HSfrhi; lia|].
          intros a Ha. destruct (Hshin a ltac:(lia)) as (Hsa & _). exact (HSW1 a Hsa). }
        assert (HRWp : exists junk2, rw_cells rsegs m1 (Sfr fr + 272) [CB 19 junk2]).
        { destruct (rh_bytes_of_present 19%nat m1 (Sfr fr + 272) ltac:(unfold AC.GT in HSfrGT; lia)
                      ltac:(unfold HIGHMEM_BEG in HSfrhi; lia)) as (junk2 & Hj & Hjl).
          { intros k Hk. destruct (Hshin (Sfr fr + 272 + Z.of_nat k) ltac:(lia)) as (Hsa & _).
            exact (proj2 (HSW1 _ Hsa)). }
          exists junk2. rewrite <- Hjl. apply rh_rwc_CB; [exact Hj|]. rewrite Hjl.
          split; [unfold AC.GT in HSfrGT; lia|]. split; [unfold HIGHMEM_BEG in HSfrhi; cbn; lia|].
          intros i Hi. cbn in Hi. destruct (Hshin (Sfr fr + 272 + i) ltac:(lia)) as (Hsa & _).
          exact (proj1 (HSW1 _ Hsa)). }
        destruct HRWp as (junk2 & HRWp).
        eapply evt_mono.
        { eapply (r21_p1_evt SET) with (A := A) (Q := Sfr fr + 68) (junk := junk2);
            try rewrite Hs3;
            repeat match goal with
            | |- context [bv_unsigned ?s] =>
                progress change (bv_unsigned s) with (bv_unsigned (getr regs 19)); rewrite Hs3
            end;
            [ exact Hr9 | exact HSfrGT | lia | exact HA4 | lia | lia
            | intros i Hi; exact (proj1 (Hshin (Sfr fr + i) ltac:(lia)))
            | exact HRWp | exact HSTf | exact Q8 | exact Hro1 | exact HAC1 ]. }
        intros ms' (R & m' & E & P2 & P3 & P4 & P8 & P9 & P19 & P23 & P24 & P25 & P26 & MU2 & WM2 & ST2).
        match type of MU2 with
        | context [bv_unsigned ?s] => change (bv_unsigned s) with (bv_unsigned (getr regs 19)) in MU2, ST2
        end.
        rewrite Hs3 in MU2, ST2.
        exists R, (Z_to_bv 64 0x81ca8), m'. split; [exact E|].
        split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
        split; [exact P19|]. split; [exact P23|]. split; [exact P24|]. split; [exact P25|]. split; [exact P26|].
        exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [exact ST1|].
        right; right. split; [reflexivity|]. split; [reflexivity|].
        split; [exact MU2|]. split; [exact WM2 | exact ST2]. }
      { (* has_identity_record <> 0: wrapper_strcmp returns 0 at 0x81c58 *)
        intros E0 R m' P10 P2 P3 P4 P8 P9 P19 P21 P22 P23 P24 P25 P26 MU2 WM2 ST2.
        exists R, (Z_to_bv 64 0x81c58), m'. split; [reflexivity|].
        split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
        split; [exact P19|]. split; [exact P23|]. split; [exact P24|]. split; [exact P25|]. split; [exact P26|].
        exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [exact ST1|].
        right; left. split; [reflexivity|]. split; [reflexivity|]. split; [exact P10|].
        split; [exact MU2|]. split; [exact WM2 | exact ST2]. } }
  intros R pc' mem' regs' md' (P2 & P3 & P4 & P8 & P9 & P19 & P23 & P24 & P25 & P26 & m1 & MU1 & WM1 & ST1 & HARM)
    Hreg Hmat.
  assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact P2).
  assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact P3).
  assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact P4).
  assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact P8).
  assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact P9).
  assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact P19).
  assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact P23).
  assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact P24).
  assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact P25).
  assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact P26).
  (* hop 1: the latch's shadow stores *)
  destruct (rh_sh_move B APIf ra empty FF g fr [] regs regs mem m1 md 296 313 HFRA HENT
              ltac:(lia) ltac:(lia) ltac:(lia) MU1 WM1
              ltac:(intros qq Hqq; destruct ST1 as (_ & _ & HST1); exact (proj2 (HST1 qq Hqq)))
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (HFRA1 & HENT1).
  pose proof HRB as (_ & HCUR & HOURb & _ & HIDB & HFGB).
  assert (HOUR1 : OURb g fr m1).
  { unfold OURb in *. apply (rh_keep _ mem m1 _ _ MU1); [|exact HOUR].
    rewrite OUR_length. intros x Hx. apply HappW1, Happfr. lia. }
  assert (HCUR' : CUR g 7 regs').
  { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
    split; [exact Hc0|]. split; [rewrite Fr23; exact Hc23 | rewrite Fr25; exact Hc25]. }
  assert (Ec0 : c0 (g_in g) = 7) by (destruct HCUR as (Hc0 & _); unfold c0; unfold g_n in Hc0; lia).
  pose proof HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUTA0 & HA2176_0 & HNM0 & HOUR0 & HTBL0 & HBOX0 &
    HMROW0 & HPRA0 & S152 & S112 & HA2256 & S160).
  (* PRO's our[] addressability (adopt 9): our[]'s six bytes have the shadow byte Sfr fr + 328, above the latch's
     Sfr fr + 296 .. 312 *)
  assert (HOURsh : forall i, 0 <= i < 6 -> shadow_addr (fr + 2624 + i) = Sfr fr + 328)
    by (intros i Hi; unfold Sfr, shadow_addr; clear - Hfr8 Hi; Z.div_mod_to_equations; lia).
  assert (HOUR1a : addressable m1 (fr + 2624) 6).
  { apply (rh_addr_keep_rng mem m1 _ (fr + 2624) 6 HOUR0 MU1). intros i Hi. rewrite (HOURsh i Hi).
    apply HoutW1. right. lia. }
  destruct HARM as [(Hb5 & Hpc & Em & P21 & P22 & P27) | [(Eb & Hpc & P10 & MU2 & WM2 & ST2) | (Eb & Hpc & MU2 & WM2 & ST2)]].
  - (* b <= 5: Inv_B816ec_at at turn S b *)
    subst pc' mem'.
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact P21).
    assert (Fr22 : getr regs' 22 = Z_to_bv 64 (Z.of_nat b + 1)) by (rewrite Hreg; exact P22).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact P27).
    assert (HFRA' : FRA B APIf ra g fr [] regs' m1 md')
      by exact (sl_fra_move B APIf ra g fr [] regs regs' m1 md md' HFRA1 Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat).
    assert (HENT' : ENT APIf g [] m1 md') by exact (ent_mat APIf g [] m1 md md' HENT1 Hmat).
    assert (HRBE' : RBE g fr regs' m1).
    { apply (rh_RBE_keep_sh g fr regs regs' _ mem m1 A HRBE MU1 Hfr8 ltac:(unfold AC.GT; lia) Hr9 ltac:(lia)
               HA4 Fr9).
      - intros x Hx. apply HoutW1. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
      - intros x Hx. cbn [outside] in Hx. lia. }
    assert (HRB' : RB g fr (S b) (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs' m1).
    { split; [lia|]. split; [exact HCUR'|]. split; [exact HOUR1|].
      split; [unfold rg; rewrite Fr22; f_equal; lia|].
      split.
      { unfold IDBr in *. apply (rh_keep _ mem m1 _ _ MU1); [|exact HIDB].
        rewrite (rb_RID_len (g_in g) (S b)). intros x Hx. apply HappW1, Happfr. lia. }
      { unfold FGBr in *. apply (rh_keep _ mem m1 _ _ MU1); [|exact HFGB].
        rewrite (rb_RFG_len (g_in g) (S b) ltac:(lia)). intros x Hx. apply HappW1, Happfr. lia. } }
    rewrite <- SEGS. apply Hnext. exists regs', m1, md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split; [exact HRB'|].
    split; [exact HRBE'|].
    split; [unfold rg in *; rewrite Fr21; exact H21|].
    split; [exact (r6x_of_rbe _ _ _ _ _ HRBE')|].
    pose proof HRBE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      HNM' & _).
    split; [exact HNM' | unfold rg; rewrite Fr27; exact H27].
  - (* b = 6, has_identity_record <> 0: Inv_B81c58 *)
    subst pc' b.
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 0) by (rewrite Hreg; exact P10).
    pose proof HFRA1 as HF1.
    destruct HF1 as (A1 & sp1 & s51 & HRT1 & HAH1 & Hro1 & Hsn1 & Hhalt1 & Hgimg1 & Hr2_1 & Hspm1 & Haspz1 &
      Hstklo1 & Hr4_1 & Hr8_1 & Hr9_1 & Hr3_1 & Hr19_1 & Hr26_1 & Hfrm1 & Hs5_1 & HAm1 & HAS1 & Hspa1 & Hfa1 &
      HA448_1 & HS4_1 & HAPP1 & Hspill1 & Hsel1 & Hfr56_1 & Hloc1 & Hhdr1_1 & Hhdr2_1 & Hsh1 & Hwin1 & Hsaved1 &
      Herrno1 & HAG1 & HWA1 & HSHI1_1 & HSHI2_1 & HSHI3_1 & Hhb1 & Hlive1).
    assert (Esp1 : sp1 = sp) by (rewrite Haspz in Haspz1; lia). subst sp1.
    set (W := [(sp - STRCMP_WRAP_K, sp)]).
    assert (HoutW : forall x, (x < sp - STRCMP_WRAP_K \/ sp <= x) -> outside W x)
      by (intros x Hx; apply rh_out1; exact Hx).
    assert (Hallapp : all_app W).
    { unfold W. cbn [all_app app_ivl]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
    assert (HWin : forall x, ~ outside W x ->
              (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr + 24 <= x < fr + FRAME_BYTES) \/
              (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx. left. unfold W in Hx. cbn [outside] in Hx. unfold APPMEM_END in *. lia. }
    assert (HPres : forall x, 0 <= x < 2 ^ 64 -> (exists bb, mbyte rsegs m1 x = Some bb) ->
              exists bb, mbyte rsegs mem' x = Some bb).
    { intros x Hx Hb.
      destruct (rh_out_dec W x) as [Ho|Ho].
      - rewrite !rh_mbyte_mrd in Hb |- *. unfold mrd in *.
        rewrite (MU2 (wa x)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
      - unfold W in Ho. cbn [outside] in Ho. rewrite rh_mbyte_mrd.
        destruct ST2 as (_ & _ & HST). destruct (HST x ltac:(unfold APPMEM_END in *; lia)) as (_ & bb & Hbb).
        exists bb. exact Hbb. }
    destruct (rh_ah B APIf ra g fr [] regs m1 mem' md W HFRA1 MU2 WM2 HWin HPres)
      as (HAH' & HOWN' & HSTKeq & HSTKHeq).
    assert (HSTKfull : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (LFr.stk_merge rsegs mem' (g_S g - AF.SLOT_STACK) sp (g_S g) ST2); [|lia].
      eapply (LFr.stk_transport rsegs _ m1 mem');
        [ exact (proj2 (LFr.stk_split rsegs m1 (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin1 ltac:(lia)))
        | exact MU2 | exact WM2 |].
      intros x Hx. left. apply HoutW. right. lia. }
    assert (HFRA' : FRA B APIf ra g fr [] regs' mem' md').
    { apply (sl_callee_keep B APIf ra empty FF g fr [] regs regs' m1 mem' md md' STRCMP_WRAP_K HFRA1);
        [ rewrite Haspz; exact MU2 | exact WM2 | exact HSTKfull | lia | rewrite Haspz; lia
        | destruct (Hfrpl STRCMP_WRAP_K ltac:(lia)) as [Hc|Hc];
            [right; rewrite Haspz; lia | left; rewrite Haspz; lia]
        | unfold APPMEM_END in *; lia
        | exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat ]. }
    assert (HENT' : ENT APIf g [] mem' md).
    { apply (ent_store B APIf ra g fr [] regs m1 mem' md W HENT1 HFRA1 MU2);
        [ | exact HSTKeq | exact HSTKHeq | intros a _ Ho; exact (proj2 (HOWN' a) Ho) ].
      intros x Hx. destruct (rh_out_dec W x) as [Ho|Ho]; [left; exact Ho|].
      right; left. unfold W in Ho. cbn [outside] in Ho. unfold APPMEM_END in *. lia. }
    assert (HENT'' : ENT APIf g [] mem' md') by exact (ent_mat APIf g [] mem' md md' HENT' Hmat).
    assert (KS : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Ho0 Ho1 Hs.
      pose proof (rh_spill_keep regs regs mem m1 _ A off v Hs Hr9 ltac:(lia) HA4 Ho0 Ho1 eq_refl MU1
                    (fun x Hx => HoutW1 x ltac:(unfold HIGHMEM_BEG, APPMEM_END in *; lia))) as Hs1.
      exact (rh_spill_keep regs regs' m1 mem' W A off v Hs1 Hr9 ltac:(lia) HA4 Ho0 Ho1 Fr9 MU2
               (fun x Hx => HoutW x ltac:(lia))). }
    rewrite <- SEGS. apply Hbf4. exists regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|].
    split.
    { unfold OURb in *. apply (rh_keep W m1 mem' _ _ MU2); [|exact HOUR1].
      rewrite OUR_length. intros x Hx. apply HoutW.
      destruct (Hfrpl STRCMP_WRAP_K ltac:(lia)) as [Hc|Hc]; [left | right]; lia. }
    split; [unfold a0v, rg; exact Fr10|].
    split.
    { (* PRO: the spills stay, and the wrapper's window is app memory, so no shadow byte changes *)
      unfold PRO. split; [exact (r21_PRA_keep fr regs regs' mem mem' KS HPRA0)|].
      split; [apply KS; [lia | lia | exact S152]|].
      split; [apply KS; [lia | lia | exact S264]|].
      split; [exact (sl_addr_keep m1 mem' W (fr + 2624) 6 HOUR1a MU2 Hallapp)|].
      apply KS; [lia | lia | exact S160]. }
    split.
    { exists (Sfr fr + 68). split; [apply KS; [lia | lia | exact S8]|]. lia. }
    split; [apply KS; [lia | lia | exact S56]|].
    split; [apply KS; [lia | lia | exact S176]|].
    split; [apply KS; [lia | lia | exact S208]|].
    split; [apply KS; [lia | lia | exact S64]|].
    split; [rewrite Ec0; exact HCUR'|].
    exact (r21_kind_addr g fr [] regs' mem' md' HFRA').
  - (* b = 6, has_identity_record = 0: Inv_B81ca8 *)
    subst pc' b.
    assert (MU2' : munch [(Sfr fr + 0, Sfr fr + 291)] m1 mem') by (rewrite Z.add_0_r; exact MU2).
    destruct (rh_sh_move B APIf ra empty FF g fr [] regs regs' m1 mem' md 0 291 HFRA1 HENT1
                ltac:(lia) ltac:(lia) ltac:(lia) MU2' WM2
                ltac:(intros qq Hqq; destruct ST2 as (_ & _ & HST2); exact (proj2 (HST2 qq ltac:(lia))))
                Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26) as (HFRA2 & HENT2).
    assert (HFRA' : FRA B APIf ra g fr [] regs' mem' md')
      by exact (sl_fra_move B APIf ra g fr [] regs' regs' mem' md md' HFRA2
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat).
    assert (HENT' : ENT APIf g [] mem' md') by exact (ent_mat APIf g [] mem' md md' HENT2 Hmat).
    assert (HoutW2 : forall x, (x < Sfr fr \/ Sfr fr + 291 <= x) -> outside [(Sfr fr, Sfr fr + 291)] x)
      by (intros x Hx; apply rh_out1; exact Hx).
    assert (KS : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Ho0 Ho1 Hs.
      pose proof (rh_spill_keep regs regs mem m1 _ A off v Hs Hr9 ltac:(lia) HA4 Ho0 Ho1 eq_refl MU1
                    (fun x Hx => HoutW1 x ltac:(unfold HIGHMEM_BEG, APPMEM_END in *; lia))) as Hs1.
      exact (rh_spill_keep regs regs' m1 mem' _ A off v Hs1 Hr9 ltac:(lia) HA4 Ho0 Ho1 Fr9 MU2
               (fun x Hx => HoutW2 x ltac:(unfold HIGHMEM_BEG, APPMEM_END in *; lia))). }
    rewrite <- SEGS. apply Hc44. exists regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split.
    { unfold OURb in *. apply (rh_keep _ m1 mem' _ _ MU2); [|exact HOUR1].
      rewrite OUR_length. intros x Hx.
      destruct (rh_out_dec [(Sfr fr, Sfr fr + 291)] x) as [Ho|Ho]; [exact Ho|].
      exfalso. cbn [outside] in Ho. destruct (Hshin x ltac:(lia)) as (Hsx & _).
      exact (app_not_shadow x (Happfr x ltac:(lia)) Hsx). }
    split; [apply KS; [lia | lia | exact S56]|].
    split.
    { (* PRO: the spills stay, and our[]'s shadow byte Sfr fr + 328 is above the P1 suffix's writes
         [Sfr fr, Sfr fr + 291) (the 14 stores at + 272 .. 290, meta_fill_f8 on [Sfr fr + 68, Sfr fr + 255)) *)
      unfold PRO. split; [exact (r21_PRA_keep fr regs regs' mem mem' KS HPRA0)|].
      split; [apply KS; [lia | lia | exact S152]|].
      split; [apply KS; [lia | lia | exact S264]|].
      split; [|apply KS; [lia | lia | exact S160]].
      apply (rh_addr_keep_rng m1 mem' _ (fr + 2624) 6 HOUR1a MU2). intros i Hi. rewrite (HOURsh i Hi).
      apply HoutW2. right. lia. }
    split; [apply KS; [lia | lia | exact S176]|].
    split; [apply KS; [lia | lia | exact S208]|].
    split; [apply KS; [lia | lia | exact S64]|].
    split; [rewrite Ec0; exact HCUR'|].
    exact (r21_kind_addr g fr [] regs' mem' md' HFRA').
Qed.

(* S_R21_a5c: R21's run from the latch cut Inv_B81ac0_at b (0x81ac0, past the latch's eight shadow stores):
   b <= 5 back to Inv_B816ec_at (S b) with memory unchanged; b = 6 the identity-record check (r21_tail_evt), then
   wrapper_strcmp to Inv_B81c58 (has_identity_record <> 0), or the taken 0x81c0c `beqz a0,81c60` to Inv_B81c60
   (has_identity_record = 0, a0 = 0, memory unchanged). The cut's own IDBr / FGBr / CUR are turn b's records. *)
Lemma seg_R21_a5c : forall b : nat,
  Hat B APIf ra (Inv_B816ec_at B APIf ra) (S b) ->
  Hcut B APIf ra (Inv_B81c58 B APIf ra) ->
  Hcut B APIf ra (Inv_B81c60 B APIf ra) ->
  Hat B APIf ra (Inv_B81ac0_at B APIf ra) b.
Proof.
  intros b Hnext Hbf4 Hbfc g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT &
                    (Hgn & Hb6 & H22 & HCUR & HOUR & HIDB & HFGB & HRBE & H21 & _ & H27)).
  subst c. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hfrpl & HfrA & _ & Hfrwr).
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGTfr & Happfr).
  pose proof (rh_sh_in B APIf ra g fr [] regs mem md HFRA) as Hshin.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKs : STRCMP_WRAP_K = 2272) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (W0 & W1 & _); split; [exact W0 | exact W1]).
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HA4 : A + 448 <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  rewrite Haspz in Hwlo, Hwstk, Hfrpl.
  assert (Hspb : 0 <= sp <= APPMEM_END) by (unfold APPMEM_END in *; lia).
  unfold AC.GT in HGTfr.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HSfrhi : Sfr fr + 392 <= HIGHMEM_BEG).
  { pose proof (Hshin (Sfr fr + 391) ltac:(lia)) as (IS & _).
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  assert (HSfrGT : AC.GT <= Sfr fr) by (unfold Sfr, shadow_addr, ASAN_K, AC.GT; Z.div_mod_to_equations; lia).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HAlo : HIGHMEM_BEG <= A) by (unfold HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (Hfrhi : fr + 3136 <= 2 ^ 64).
  { pose proof (Happfr (fr + 3135) ltac:(lia)) as Hq.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hq. lia. }
  (* the model facts of the identity-record check *)
  pose proof (rb_istar_range (g_in g)) as Hi11.
  pose proof (rb_mrow_range (g_in g)) as (Hmr0 & Hmr1 & Hmr8).
  pose proof (rb_mb_len (g_in g)) as HROWL.
  pose proof (rb_RID_len (g_in g) 7) as HIDL.
  destruct (rb_rtm_fw (g_in g)) as (Ehf & Efw).
  destruct (rb_rtm_ver (g_in g)) as (Ehv & Emaj & Emin & Epat).
  destruct (rb_row_facts (istar (g_in g)) Hi11) as (Hh32 & Ehid & Hnmf).
  destruct (rb_row_le (istar (g_in g)) Hi11) as (L56 & L280).
  change (rowb (istar (g_in g))) with (rt_mb (g_in g)) in Hh32, Ehid, Hnmf, L56, L280.
  (* the run *)
  apply (sl_run_lib regs (Z_to_bv 64 0x81ac0) mem md
    (fun R pc' mem' =>
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       (((b <= 5)%nat /\ pc' = Z_to_bv 64 0x816ec /\ mem' = mem /\ getr R 21 = getr regs 21 /\
           getr R 22 = Z_to_bv 64 (Z.of_nat b + 1) /\ getr R 27 = getr regs 27) \/
        (b = 6%nat /\ pc' = Z_to_bv 64 0x81c58 /\ getr R 10 = Z_to_bv 64 0 /\
           munch [(sp - STRCMP_WRAP_K, sp)] mem mem' /\ wmono rsegs mem mem' /\
           stk rsegs mem' (g_S g - AF.SLOT_STACK) sp) \/
        (b = 6%nat /\ pc' = Z_to_bv 64 0x81c60 /\ mem' = mem /\ getr R 10 = Z_to_bv 64 0)))
    (Post B APIf ra g)).
  { exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg in H22.
    destruct (le_lt_dec b 5) as [Hb5 | Hb5].
    - (* b <= 5: back to the round-trip head *)
      eapply evt_mono.
      + apply (r21_a5c_next) with (bz := Z.of_nat b); [exact H22 | lia].
      + intros ms' (R & m' & E & P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 &
                    P26 & P27 & Em).
        subst m'.
        exists R, (Z_to_bv 64 0x816ec), mem. split; [exact E|].
        split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
        split; [exact P19|]. split; [exact P23|]. split; [exact P24|]. split; [exact P25|]. split; [exact P26|].
        left. split; [exact Hb5|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact P21|]. split; [exact P22 | exact P27].
    - (* b = 6: the identity-record check *)
      assert (Eb : b = 6%nat) by lia. subst b.
      change (Z.of_nat 6) with 6 in H22.
      unfold rg in Hr9, Hr26. try unfold rg in Hr2.
      apply (r21_a5c_last _); [exact H22 |].
      intros a0' s6'.
      pose proof HIDB as HIDB1. unfold IDBr in HIDB1.
      pose proof HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
        S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUTA1 & HA2176 & HNM1 & HOUR6 & HTBL & HBOX &
        HMROW & _).
      pose proof (r21_cells sp mem md HRT) as (HAC1 & HSW1 & HGOT1 & HCF1 & HCF2).
      (* the spill words the tail loads *)
      pose proof (rh_spill_at regs mem A 144 (fr + 2176) S144 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q144.
      pose proof (rh_spill_at regs mem A 32 0 S32 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q32.
      pose proof (rh_spill_at regs mem A 272 (mrow (g_in g)) S272 Hr9 ltac:(lia) HA4 ltac:(lia) ltac:(lia)) as Q272.
      assert (R144 := rh_rdn mem _ _ 8 Q144 (length_le8 _)).
      assert (R32 := rh_rdn mem _ _ 8 Q32 (length_le8 _)).
      assert (R272 := rh_rdn mem _ _ 8 Q272 (length_le8 _)).
      (* the catalogue row's granules have shadow byte 0 *)
      assert (HADrow : forall p, CAT <= p -> p + 8 <= CAT + 3256 -> addressable mem p 8).
      { intros p Hp1 Hp2. apply rh_addr_join; [unfold CAT in *; lia | lia | unfold CAT, APPMEM_END in *; lia |].
        intros i Hi. exact (rh_cat_addr B APIf ra g fr [] regs mem md HFRA (p + i) ltac:(lia)). }
      assert (K266 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 mem (mrow (g_in g) + 264));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      assert (K268 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 mem (mrow (g_in g) + 264));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      assert (K270 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 mem (mrow (g_in g) + 264));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      assert (K272 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 mem (mrow (g_in g) + 272));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      assert (K56 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 mem (mrow (g_in g) + 56));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      assert (K280 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0])
        by (apply (rh_meta0 mem (mrow (g_in g) + 280));
            [apply HADrow; unfold CAT in *; lia | clear - Hmr8; Z.div_mod_to_equations; lia | lia]).
      (* the identity record's bytes (RID_7) *)
      assert (R2 : ov_read_bytes rsegs mem (wa (fr + 2176 + 2)) 1 = Some [Z_to_bv 8 1]).
      { pose proof (r21_rd1 mem (fr + 2176) (RID (g_in g) 7) 2 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 2) with (fr + 2176 + 2) in H by lia.
        rewrite (r21_byte1 (nth 2 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehf) in H. exact H. }
      assert (R36 : ov_read_bytes rsegs mem (wa (fr + 2176 + 36)) 1 = Some [Z_to_bv 8 1]).
      { pose proof (r21_rd1 mem (fr + 2176) (RID (g_in g) 7) 36 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 36) with (fr + 2176 + 36) in H by lia.
        rewrite (r21_byte1 (nth 36 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehv) in H. exact H. }
      assert (R0 : ov_read_bytes rsegs mem (wa (fr + 2176)) 2 = Some (le2 (Z_to_bv 64 (fw_milli (RID (g_in g) 7))))).
      { pose proof (r21_rd2 mem (fr + 2176) (RID (g_in g) 7) 0 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 0) with (fr + 2176) in H by lia. exact H. }
      assert (R22 : ov_read_bytes rsegs mem (wa (fr + 2176 + 22)) 2 =
                    Some (le2 (Z_to_bv 64 (major (RID (g_in g) 7))))).
      { pose proof (r21_rd2 mem (fr + 2176) (RID (g_in g) 7) 22 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 22) with (fr + 2176 + 22) in H by lia. exact H. }
      assert (R24 : ov_read_bytes rsegs mem (wa (fr + 2176 + 24)) 2 =
                    Some (le2 (Z_to_bv 64 (minor (RID (g_in g) 7))))).
      { pose proof (r21_rd2 mem (fr + 2176) (RID (g_in g) 7) 24 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 24) with (fr + 2176 + 24) in H by lia. exact H. }
      assert (R26 : ov_read_bytes rsegs mem (wa (fr + 2176 + 26)) 2 =
                    Some (le2 (Z_to_bv 64 (patch (RID (g_in g) 7))))).
      { pose proof (r21_rd2 mem (fr + 2176) (RID (g_in g) 7) 26 HIDB1 ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 26) with (fr + 2176 + 26) in H by lia. exact H. }
      (* the catalogue row's bytes *)
      assert (M266 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 266)) 2 =
                     Some (le2 (Z_to_bv 64 (fw_milli (RID (g_in g) 7))))).
      { pose proof (r21_rd2 mem (mrow (g_in g)) (rt_mb (g_in g)) 266 HMROW ltac:(rewrite HROWL; lia)) as H.
        replace (mrow (g_in g) + Z.of_nat 266) with (mrow (g_in g) + 266) in H by lia.
        rewrite Efw. exact H. }
      assert (M268 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 268)) 2 =
                     Some (le2 (Z_to_bv 64 (major (RID (g_in g) 7))))).
      { pose proof (r21_rd2 mem (mrow (g_in g)) (rt_mb (g_in g)) 268 HMROW ltac:(rewrite HROWL; lia)) as H.
        replace (mrow (g_in g) + Z.of_nat 268) with (mrow (g_in g) + 268) in H by lia.
        rewrite Emaj. exact H. }
      assert (M270 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 270)) 2 =
                     Some (le2 (Z_to_bv 64 (minor (RID (g_in g) 7))))).
      { pose proof (r21_rd2 mem (mrow (g_in g)) (rt_mb (g_in g)) 270 HMROW ltac:(rewrite HROWL; lia)) as H.
        replace (mrow (g_in g) + Z.of_nat 270) with (mrow (g_in g) + 270) in H by lia.
        rewrite Emin. exact H. }
      assert (M272 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 272)) 2 =
                     Some (le2 (Z_to_bv 64 (patch (RID (g_in g) 7))))).
      { pose proof (r21_rd2 mem (mrow (g_in g)) (rt_mb (g_in g)) 272 HMROW ltac:(rewrite HROWL; lia)) as H.
        replace (mrow (g_in g) + Z.of_nat 272) with (mrow (g_in g) + 272) in H by lia.
        rewrite Epat. exact H. }
      assert (M56 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 56)) 4 =
                    Some (le4 (Z_to_bv 64 (RcSynth.rw32 (rt_mb (g_in g)) 56)))).
      { pose proof (r21_rd4 mem (mrow (g_in g)) (rt_mb (g_in g)) 56 HMROW ltac:(rewrite HROWL; lia)) as H.
        replace (mrow (g_in g) + Z.of_nat 56) with (mrow (g_in g) + 56) in H by lia.
        rewrite <- L56. exact H. }
      eapply (r21_tail_evt SC) with (spv := sp) (lo := g_S g - AF.SLOT_STACK) (A := A) (S5 := fr + 2176)
        (mr := mrow (g_in g)) (fw := fw_milli (RID (g_in g) 7)) (maj := major (RID (g_in g) 7))
        (mnr := minor (RID (g_in g) 7)) (pat := patch (RID (g_in g) 7))
        (h := RcSynth.rw32 (rt_mb (g_in g)) 56) (nm := RcSynth.rname (rt_mb (g_in g)))
        (sx := removelast (rt_nb (g_in g))).
      all: try first [ exact Hr2 | exact Hr9 | exact Hr26 | exact R144 | exact R32 | exact R272 | exact R2
                     | exact K266 | exact K268 | exact K270 | exact K272 | exact K56 | exact K280 | exact R0
                     | exact M266 | exact R36 | exact R22 | exact M268 | exact R24 | exact M270 | exact R26
                     | exact M272 | exact M56 | exact Hh32
                     | (unfold CAT, APPMEM_END in *; lia) ].
      { (* the name strings, when the row has an identity record *)
        intros Hh0.
        assert (Hhid : RcEmit.em_hid (rt_mb (g_in g)) <> 0) by (intros E; apply Hh0; apply Ehid; exact E).
        destruct (Hnmf Hhid) as (Hnm0 & Hnm1 & HROn & HAGnm).
        assert (Hn6 : rt_n (g_in g) 6 <> 0) by (apply (proj2 (rb_rtm_hid (g_in g))); exact Hhid).
        destruct (rb_rtm_name (g_in g) Hn6) as (Ehn & Efn & Elast & Hall & Hlen16).
        apply andb_true_iff in Hlen16 as [Hl1 Hl2]. apply Nat.leb_le in Hl1. apply Nat.leb_le in Hl2.
        assert (Enb : rt_nb (g_in g) = removelast (rt_nb (g_in g)) ++ [Z_to_bv 8 0]).
        { change (Z_to_bv 8 0) with (zb 0). rewrite <- Elast.
          apply app_removelast_last. intros E. rewrite E in Hl1. cbn [length] in Hl1. lia. }
        assert (HLsx : (length (removelast (rt_nb (g_in g))) + 1 = length (rt_nb (g_in g)))%nat)
          by (rewrite Enb at 2; rewrite length_app; cbn [length]; lia).
        rewrite r21_strcmp_k_refl.
        assert (R20 : ov_read_bytes rsegs mem (wa (fr + 2176 + 20)) 1 = Some [Z_to_bv 8 1]).
        { pose proof (r21_rd1 mem (fr + 2176) (RID (g_in g) 7) 20 HIDB1 ltac:(rewrite HIDL; lia)) as H.
          replace (fr + 2176 + Z.of_nat 20) with (fr + 2176 + 20) in H by lia.
          rewrite (r21_byte1 (nth 20 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehn) in H. exact H. }
        assert (R280 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 280)) 8 =
                       Some (le8 (Z_to_bv 64 (RcSynth.rname (rt_mb (g_in g)))))).
        { pose proof (r21_rd8 mem (mrow (g_in g)) (rt_mb (g_in g)) 280 HMROW ltac:(rewrite HROWL; lia)) as H.
          replace (mrow (g_in g) + Z.of_nat 280) with (mrow (g_in g) + 280) in H by lia.
          rewrite <- L280. exact H. }
        assert (HBX : bytes_at rsegs mem (fr + 2176 + 3) (removelast (rt_nb (g_in g)) ++ [Z_to_bv 8 0])).
        { rewrite <- Enb.
          assert (Es : firstn (length (rt_nb (g_in g))) (skipn 3 (RID (g_in g) 7)) = rt_nb (g_in g)).
          { rewrite <- Efn at 2. unfold model_name, RcIdentModel.get, RcIdentModel.OFF_NAME,
              RcIdentModel.NAME_CAP. rewrite firstn_firstn. f_equal. lia. }
          pose proof (rh_ba_sub mem (fr + 2176) (RID (g_in g) 7) 3 (length (rt_nb (g_in g))) HIDB1
                        ltac:(rewrite HIDL; lia)) as X.
          rewrite Es in X. replace (fr + 2176 + Z.of_nat 3) with (fr + 2176 + 3) in X by lia. exact X. }
        assert (HBY : bytes_at rsegs mem (RcSynth.rname (rt_mb (g_in g))) (rt_nb (g_in g)))
          by (apply (r21_ro_bytes (rt_nb (g_in g)) mem _ Hro); [exact HROn | lia | lia]).
        assert (HNin : ~ In (Z_to_bv 8 0) (removelast (rt_nb (g_in g)))).
        { intros Hin. pose proof (proj1 (forallb_forall _ _) Hall (Z_to_bv 8 0) Hin) as X.
          vm_compute in X. discriminate X. }
        assert (HAY : addressable mem (RcSynth.rname (rt_mb (g_in g)))
                        (Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1)).
        { apply rh_addr_join; [lia | lia | unfold APPMEM_END; lia |].
          intros i Hi. apply HAG. replace (RcSynth.rname (rt_mb (g_in g)) + i)
            with (RcSynth.rname (rt_mb (g_in g)) + Z.of_nat (Z.to_nat i)) by lia.
          apply HAGnm.
          assert (HLen : length (img_cstr (RcSynth.rname (rt_mb (g_in g))) 16) = length (rt_nb (g_in g)))
            by reflexivity.
          rewrite HLen. lia. }
        assert (HAX : addressable mem (fr + 2176 + 3) (Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1)).
        { apply (addressable_sub mem (fr + 2176) 38 3 (Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1)
                   HA2176); lia. }
        split; [exact R20|]. split; [exact R280|]. split; [lia|].
        split; [exact HBX|]. split; [exact HNin|].
        split; [rewrite <- Enb; exact HBY|].
        split; [lia|]. split; [exact HAX|].
        split; [right; apply Happfr; lia|]. split; [exact HAY|].
        split; [right; unfold app_mem, LOWMEM_END; left; lia|].
        split; [apply Happfr; lia|].
        split; [unfold app_mem, LOWMEM_END; left; lia|].
        split; [exact (proj1 (LFr.stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia)))|].
        split; [lia|].
        split; [unfold APPMEM_END, HIGHMEM_BEG in *; lia|].
        split; [lia|].
        split; [destruct (Hfrpl STRCMP_WRAP_K ltac:(lia)) as [Hc|Hc]; [left | right]; lia|].
        split; [left; unfold HIGHMEM_BEG in *; lia|].
        split; [exact HAC1|]. split; [exact HSW1|]. split; [exact Hro|].
        split; [exact HGOT1|]. split; [exact HCF1 | exact HCF2]. }
      { (* has_identity_record = 0: the taken 0x81c0c beqz a0,81c60, with a0 = 0 *)
        intros E0 t0' t1' t2' a0'' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ha0z.
        apply evt_done. do 3 eexists. split; [reflexivity|].
        do 10 (split; [reflexivity|]).
        right; right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        transitivity a0''; [reflexivity | exact Ha0z]. }
      { (* has_identity_record <> 0: wrapper_strcmp returns 0 at 0x81c58 *)
        intros E0 R m' P10 P2 P3 P4 P8 P9 P19 P21 P22 P23 P24 P25 P26 MU2 WM2 ST2.
        exists R, (Z_to_bv 64 0x81c58), m'. split; [reflexivity|].
        split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
        split; [exact P19|]. split; [exact P23|]. split; [exact P24|]. split; [exact P25|]. split; [exact P26|].
        right; left. split; [reflexivity|]. split; [reflexivity|]. split; [exact P10|].
        split; [exact MU2|]. split; [exact WM2 | exact ST2]. } }
  intros R pc' mem' regs' md' (P2 & P3 & P4 & P8 & P9 & P19 & P23 & P24 & P25 & P26 & HARM) Hreg Hmat.
  assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact P2).
  assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact P3).
  assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact P4).
  assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact P8).
  assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact P9).
  assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact P19).
  assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact P23).
  assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact P24).
  assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact P25).
  assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact P26).
  assert (HCUR' : CUR g 7 regs').
  { destruct HCUR as (Hc0 & Hc23 & Hc25). unfold CUR, rg in *.
    split; [exact Hc0|]. split; [rewrite Fr23; exact Hc23 | rewrite Fr25; exact Hc25]. }
  assert (Ec0 : c0 (g_in g) = 7) by (destruct HCUR as (Hc0 & _); unfold c0; unfold g_n in Hc0; lia).
  pose proof HRBE as (S128 & S312 & S272 & S264 & S256 & S248 & S56 & S184 & S144 & S8 & S32 & S24 & S16 &
    S96 & S120 & S240 & S232 & S224 & S176 & S208 & S64 & HOUTA0 & HA2176_0 & HNM0 & HOUR0 & HTBL0 & HBOX0 &
    HMROW0 & HPRA0 & S152 & S112 & HA2256 & S160).
  destruct HARM as [(Hb5 & Hpc & Em & P21 & P22 & P27) | [(Eb & Hpc & P10 & MU2 & WM2 & ST2) | (Eb & Hpc & Em & P10)]].
  - (* b <= 5: Inv_B816ec_at at turn S b, memory unchanged *)
    subst pc' mem'.
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact P21).
    assert (Fr22 : getr regs' 22 = Z_to_bv 64 (Z.of_nat b + 1)) by (rewrite Hreg; exact P22).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact P27).
    assert (HFRA' : FRA B APIf ra g fr [] regs' mem md')
      by exact (sl_fra_move B APIf ra g fr [] regs regs' mem md md' HFRA Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat).
    assert (HENT' : ENT APIf g [] mem md') by exact (ent_mat APIf g [] mem md md' HENT Hmat).
    assert (HRBE' : RBE g fr regs' mem).
    { apply (rh_RBE_keep g fr regs regs' [] mem mem A HRBE (munch_refl [] mem)); try assumption; try lia.
      - cbn [all_app]. exact I.
      - intros x _. cbn [outside]. exact I.
      - intros x _. cbn [outside]. exact I. }
    assert (HRB' : RB g fr (S b) (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs' mem).
    { split; [lia|]. split; [exact HCUR'|]. split; [exact HOUR|].
      split; [unfold rg; rewrite Fr22; f_equal; lia|].
      split; [exact HIDB | exact HFGB]. }
    rewrite <- SEGS. apply Hnext. exists regs', mem, md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split; [exact HRB'|].
    split; [exact HRBE'|].
    split; [unfold rg in *; rewrite Fr21; exact H21|].
    split; [exact (r6x_of_rbe _ _ _ _ _ HRBE')|].
    split; [exact HNM0 | unfold rg; rewrite Fr27; exact H27].
  - (* b = 6, has_identity_record <> 0: Inv_B81c58 *)
    subst pc' b.
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 0) by (rewrite Hreg; exact P10).
    set (W := [(sp - STRCMP_WRAP_K, sp)]).
    assert (HoutW : forall x, (x < sp - STRCMP_WRAP_K \/ sp <= x) -> outside W x)
      by (intros x Hx; apply rh_out1; exact Hx).
    assert (Hallapp : all_app W).
    { unfold W. cbn [all_app app_ivl]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
    assert (HWin : forall x, ~ outside W x ->
              (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr + 24 <= x < fr + FRAME_BYTES) \/
              (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx. left. unfold W in Hx. cbn [outside] in Hx. unfold APPMEM_END in *. lia. }
    assert (HPres : forall x, 0 <= x < 2 ^ 64 -> (exists bb, mbyte rsegs mem x = Some bb) ->
              exists bb, mbyte rsegs mem' x = Some bb).
    { intros x Hx Hb.
      destruct (rh_out_dec W x) as [Ho|Ho].
      - rewrite !rh_mbyte_mrd in Hb |- *. unfold mrd in *.
        rewrite (MU2 (wa x)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
      - unfold W in Ho. cbn [outside] in Ho. rewrite rh_mbyte_mrd.
        destruct ST2 as (_ & _ & HST). destruct (HST x ltac:(unfold APPMEM_END in *; lia)) as (_ & bb & Hbb).
        exists bb. exact Hbb. }
    destruct (rh_ah B APIf ra g fr [] regs mem mem' md W HFRA MU2 WM2 HWin HPres)
      as (HAH' & HOWN' & HSTKeq & HSTKHeq).
    assert (HSTKfull : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (LFr.stk_merge rsegs mem' (g_S g - AF.SLOT_STACK) sp (g_S g) ST2); [|lia].
      eapply (LFr.stk_transport rsegs _ mem mem');
        [ exact (proj2 (LFr.stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia)))
        | exact MU2 | exact WM2 |].
      intros x Hx. left. apply HoutW. right. lia. }
    assert (HFRA' : FRA B APIf ra g fr [] regs' mem' md').
    { apply (sl_callee_keep B APIf ra empty FF g fr [] regs regs' mem mem' md md' STRCMP_WRAP_K HFRA);
        [ rewrite Haspz; exact MU2 | exact WM2 | exact HSTKfull | lia | rewrite Haspz; lia
        | destruct (Hfrpl STRCMP_WRAP_K ltac:(lia)) as [Hc|Hc];
            [right; rewrite Haspz; lia | left; rewrite Haspz; lia]
        | unfold APPMEM_END in *; lia
        | exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat ]. }
    assert (HENT' : ENT APIf g [] mem' md).
    { apply (ent_store B APIf ra g fr [] regs mem mem' md W HENT HFRA MU2);
        [ | exact HSTKeq | exact HSTKHeq | intros a _ Ho; exact (proj2 (HOWN' a) Ho) ].
      intros x Hx. destruct (rh_out_dec W x) as [Ho|Ho]; [left; exact Ho|].
      right; left. unfold W in Ho. cbn [outside] in Ho. unfold APPMEM_END in *. lia. }
    assert (HENT'' : ENT APIf g [] mem' md') by exact (ent_mat APIf g [] mem' md md' HENT' Hmat).
    assert (KS : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Ho0 Ho1 Hs.
      exact (rh_spill_keep regs regs' mem mem' W A off v Hs Hr9 ltac:(lia) HA4 Ho0 Ho1 Fr9 MU2
               (fun x Hx => HoutW x ltac:(lia))). }
    rewrite <- SEGS. apply Hbf4. exists regs', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split; [exact Hgn|].
    split.
    { unfold OURb in *. apply (rh_keep W mem mem' _ _ MU2); [|exact HOUR].
      rewrite OUR_length. intros x Hx. apply HoutW.
      destruct (Hfrpl STRCMP_WRAP_K ltac:(lia)) as [Hc|Hc]; [left | right]; lia. }
    split; [unfold a0v, rg; exact Fr10|].
    split.
    { (* PRO: the spills stay, and the wrapper's window is app memory, so no shadow byte changes *)
      unfold PRO. split; [exact (r21_PRA_keep fr regs regs' mem mem' KS HPRA0)|].
      split; [apply KS; [lia | lia | exact S152]|].
      split; [apply KS; [lia | lia | exact S264]|].
      split; [exact (sl_addr_keep mem mem' W (fr + 2624) 6 HOUR0 MU2 Hallapp)|].
      apply KS; [lia | lia | exact S160]. }
    split.
    { exists (Sfr fr + 68). split; [apply KS; [lia | lia | exact S8]|]. lia. }
    split; [apply KS; [lia | lia | exact S56]|].
    split; [apply KS; [lia | lia | exact S176]|].
    split; [apply KS; [lia | lia | exact S208]|].
    split; [apply KS; [lia | lia | exact S64]|].
    split; [rewrite Ec0; exact HCUR'|].
    exact (r21_kind_addr g fr [] regs' mem' md' HFRA').
  - (* b = 6, has_identity_record = 0: Inv_B81c60, memory unchanged, a0 = 0 *)
    subst pc' mem' b.
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 0) by (rewrite Hreg; exact P10).
    assert (HFRA' : FRA B APIf ra g fr [] regs' mem md')
      by exact (sl_fra_move B APIf ra g fr [] regs regs' mem md md' HFRA Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat).
    assert (HENT' : ENT APIf g [] mem md') by exact (ent_mat APIf g [] mem md md' HENT Hmat).
    assert (KS : forall off v, 0 <= off -> off + 8 <= 448 -> spill regs mem off v -> spill regs' mem off v).
    { intros off v _ _ (A0 & HA0 & Hq). exists A0. split; [unfold rg in *; rewrite Fr9; exact HA0 | exact Hq]. }
    rewrite <- SEGS. apply Hbfc. exists regs', mem, md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split; [exact HOUR|].
    split; [unfold a0v, rg; exact Fr10|].
    split.
    { unfold PRO. split; [exact (r21_PRA_keep fr regs regs' mem mem KS HPRA0)|].
      split; [apply KS; [lia | lia | exact S152]|].
      split; [apply KS; [lia | lia | exact S264]|].
      split; [exact HOUR0 | apply KS; [lia | lia | exact S160]]. }
    split.
    { exists (Sfr fr + 68). split; [apply KS; [lia | lia | exact S8]|]. lia. }
    split; [apply KS; [lia | lia | exact S56]|].
    split; [apply KS; [lia | lia | exact S176]|].
    split; [apply KS; [lia | lia | exact S208]|].
    split; [apply KS; [lia | lia | exact S64]|].
    split; [rewrite Ec0; exact HCUR'|].
    exact (r21_kind_addr g fr [] regs' mem md' HFRA').
Qed.

End S.
