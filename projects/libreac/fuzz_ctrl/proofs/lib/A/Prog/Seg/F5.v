(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 1027 of its 1075 lines of code are new or changed and 348 lines of the source are left out. *)
(* Segment F5 (0x81e84-0x81ea0 short arm, 0x81ea4-0x81ebc long arm; plan-asan 2), stated with the official cuts
   of A/Prog/SlotInv.v (Inv_A<addr>_at): no local cut text at all.

   Short arm (the record is below 50 bytes).  From the F4 exit at 0x81e84 (the reac_ctrl_parse return,
   a0 = t_k j) the block moves a0 into s8 and falls into 0x81e88, the join with F4's `bgeu a0,s2` arm.  There the
   `bnez s8` is not taken (s8 = t_k j = 0, since t_len j < 50 makes ctrlparse return kind 0), s6 and s9 are
   cleared, the zero word goes to the two frame-loop spill slots [s1+240] and [s1+280], s4 becomes 1 and the block
   jumps to 0x81f54.  The two spill values are exactly the model flags of this arm ([s1+240] = b2z (t_8819 j),
   [s1+280] = b2z (t_sum_ok j), both false because t_big j is false), s6 is `if t_big j then phi + 18 else 0`,
   s9 is b2z (t_tfill j) and s4 is `1 - b2z (t_sum_ok j)`, so the exit is SlotInv's b5_K bundle, the same text the
   long arm (F6) reaches.  The word at fr + 176 that b5_K names (the parse output F4 or F3 left there) is carried
   from every entry cut: the segment never writes the frame.

   Long arm (50 bytes or more).  0x81ea4 stores the zero word to [s1+240] (F4 took that edge because the byte at
   phi+12 is not 0x88, so t_8819 j is false) and falls into 0x81ea8, which sets the block-sum registers
   (a0 = a2 = s6 = phi + 18, a1 = 0, a3 = 32) and falls into 0x81ec0, the loop head.

   The segment writes only the two spill words, so FRA moves by sl_stk_run (a write below the slot sp, outside the
   frame, the shadow, the saved registers and the A+304 / [A+16, A+32) words) plus sl_fra_move for the lazy-page model
   step, and ENT by ent_store.  What the cut skeleton carries - the frame-loop spills and the harness input block
   (FLSI), the turn's carry (b5_C, with [A + 232], the fragment record FGj and the first-fragment state FSj), the
   identity record IDj at fr + 2688 (38 bytes, f5_tID_len), F4's [A + 200] word (b5_F17), the loop bookkeeping (LK)
   and the harness block (HB) - lies below A + 240 or in [A + 248, A + 280), so f5_keep and f5_q64_keep move all
   of it across the write.  [A + 240] (b5_W240) is produced at 0x81f54 (short arm, 0x81e94) and 0x81ea8 (long arm,
   0x81ea4) with the value 0 under t_8819 j = false, or carried from F4's 0x81ea8 exit.  b5_PF (slot push 14) is
   carried on the long arm (f5_pf_keep: its cells lie below A + 240) and from 0x81e84 to 0x81e88, and is empty at
   0x81f54 on the short arm (flen j < 50 and t_8819 j = false). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* mkR_of regs is definitionally the explicit 31-slot register map; exposing it lets `step` read a slot we have
   rewritten to a concrete value (needed for the two base+offset stores through s1). *)
Lemma f5_mkR_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried concrete value, from H : rg regs r v. *)
Ltac f5_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* store_ok from a writable range (wview present), as reac_box_model_block.wv_store_ok. *)
Lemma f5_store_ok : forall m m' a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> wview rsegs m (wa (a + i)) <> None) -> wmono rsegs m m' ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' a n H Hw Ha Hn.
  assert (WR : wr_at rsegs m' a (Z.of_nat n)) by (split; [lia|]; split; [lia|]; intros i Hi; apply Hw, H, Hi).
  pose proof (wr_at_store_ok rsegs m' a (Z.of_nat n) 0 n WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* Two bv literals in range are equal only if their values are. *)
Lemma f5_id : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal (@bv_unsigned 64)) in E.
  rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.

(* An 8-byte cell survives a write whose footprint misses it. *)
Lemma f5_q64_keep : forall W m m' a v, q64 m a v -> Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> Frame.outside W x) -> q64 m' a v.
Proof.
  intros W m m' a v H MU HW. unfold q64 in *.
  apply (fl_bytes W m m' a (le8 (Z_to_bv 64 v)) H MU).
  rewrite length_le8. exact HW.
Qed.

(* A 4-byte cell survives a write whose footprint misses it. *)
Lemma f5_u32_keep : forall W m m' a v, u32 m a v -> Frame.munch W m m' ->
  (forall x, a <= x < a + 4 -> Frame.outside W x) -> u32 m' a v.
Proof.
  intros W m m' a v H MU HW. unfold u32 in *.
  apply (fl_bytes W m m' a (le4 (Z_to_bv 64 v)) H MU).
  rewrite length_le4. exact HW.
Qed.

(* A thread word survives a write whose footprint misses its eight bytes, and is read back unchanged. *)
Lemma f5_word_eq : forall W m m' a, Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> Frame.outside W x) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  forall v, word_mem rsegs m a v <-> word_mem rsegs m' a v.
Proof.
  intros W m m' a MU HW Ha Hhi v.
  assert (HE : forall k, (k < 8)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))).
  { intros k Hk. apply MU. rewrite MState.unsigned_lit by lia. apply HW; lia. }
  split; intros H k Hk; pose proof (H k Hk) as Hb; unfold mbyte in *.
  - rewrite (HE k Hk). exact Hb.
  - rewrite (HE k Hk) in Hb. exact Hb.
Qed.

(* A frame-loop spill word survives a write that misses its eight bytes. The spill's own existential base names
   the same A as FRA: the cell is inside [A, A + 416) and A is far below 2 ^ 64, so no other representative of
   register 9 can name that cell. *)
Lemma f5_spill_keep : forall regs regs' A off v m m' W,
  spill regs m off v -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= APPMEM_END -> 0 <= off <= 408 ->
  getr regs' 9 = getr regs 9 -> Frame.munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> Frame.outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' A off v m m' W HS H9 HA HAE Hoff E9 MU HW.
  destruct HS as (A' & H9' & Hq).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HP : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Hqb : 0 <= A' + off /\ A' + off + Z.of_nat (length (le8 (Z_to_bv 64 v))) <= 2 ^ 64)
    by (unfold q64 in Hq; exact (bytes_at_bound rsegs m (A' + off) _ Hq)).
  rewrite length_le8 in Hqb.
  assert (HAA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm.
    assert (Hdz : (A' - A) mod 2 ^ 64 = 0).
    { rewrite Zminus_mod, Hm, Z.sub_diag. apply Zmod_0_l. }
    destruct (proj1 (Zmod_divides (A' - A) (2 ^ 64) ltac:(lia)) Hdz) as (q & Hq2).
    rewrite HP in Hq2. lia. }
  subst A'.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  exact (f5_q64_keep W m m' (A + off) v Hq MU HW).
Qed.

(* The model flags of a short record: nothing the frame loop reads is set when the record is below 50 bytes. *)
Lemma f5_big : forall inp j, t_len inp j < 50 -> t_big inp j = false.
Proof. intros inp j H. unfold t_big. apply Z.leb_gt. lia. Qed.

Lemma f5_sum : forall inp j, t_len inp j < 50 -> t_sum_ok inp j = false.
Proof. intros inp j H. unfold t_sum_ok. rewrite (f5_big inp j H). reflexivity. Qed.

Lemma f5_8819 : forall inp j, t_len inp j < 50 -> t_8819 inp j = false.
Proof. intros inp j H. unfold t_8819. rewrite (f5_big inp j H). reflexivity. Qed.

Lemma f5_tfill : forall inp j, t_len inp j < 50 -> t_tfill inp j = false.
Proof. intros inp j H. unfold t_tfill. rewrite (f5_big inp j H). reflexivity. Qed.

Lemma f5_k : forall inp j, t_len inp j < 50 -> t_k inp j = 0.
Proof.
  intros inp j H.
  assert (Hh : cp_hdr (t_len inp j) (t_g inp j) = false).
  { unfold cp_hdr. replace (50 <=? t_len inp j) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  unfold t_k, ctrlparse. rewrite Hh. reflexivity.
Qed.

(* `and s6,a0,s9` with a0 = -1 (the `addi a0,s6,-1` of the long arm with s6 = 0) keeps s9's value. *)
Lemma f5_and_ones : forall v, 0 <= v < 2 ^ 64 ->
  Z_to_bv 64 (Z.land 18446744073709551615 (bv_unsigned (Z_to_bv 64 v))) = Z_to_bv 64 v.
Proof.
  intros v Hv. rewrite (MState.unsigned_lit v) by lia.
  replace 18446744073709551615 with (Z.ones 64) by (rewrite Z.ones_equiv; reflexivity).
  rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* An interval of the prologue save area is application memory. *)
Lemma f5_app_ivl : forall lo hi, HIGHMEM_BEG <= lo -> hi <= APPMEM_END -> app_ivl lo hi.
Proof. intros lo hi H1 H2 a Ha. unfold app_mem. right. lia. Qed.

(* The identity_reply argument check of b5_K: four non-null pointers. *)
Lemma f5_reply : forall phi fr, phi <> 0 -> 0 < fr -> reply_args phi (fr + 256) (fr + 272) (fr + 304) = true.
Proof.
  intros phi fr Hphi Hfr. unfold reply_args.
  rewrite (proj2 (Z.eqb_neq phi 0) Hphi).
  rewrite (proj2 (Z.eqb_neq (fr + 256) 0) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (fr + 272) 0) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq (fr + 304) 0) ltac:(lia)).
  reflexivity.
Qed.

(* The identity record of every turn is ID_SIZE = 38 bytes: ID0 is, and both ingests of a turn (the reply arm's
   rp_id and the fragment arm's fg_id) keep the length (RcIdentModel.ING_length). *)
Lemma f5_tID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH].
  - cbn [fst_at]. unfold fs0. cbn [fs_id]. unfold RcIdentModel.ID0. rewrite repeat_length. reflexivity.
  - cbn [fst_at]. unfold turn. cbv zeta.
    assert (H1 : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
    { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [exact (RcIdentModel.ING_length _ _ _ IH) | exact IH]. }
    assert (H2 : forall st, length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j))
                                   (t_len inp j) st (t_g inp j)) = 38%nat).
    { intros st. unfold fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
        [exact (RcIdentModel.ING_length _ _ _ H1) | exact H1]. }
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; apply H2.
Qed.

(* The first fragment's body of every turn is at most 23 bytes: fs0's is empty and an opening turn keeps at most
   the 23 bytes block[9 ..] of the 50-byte frame (SlotModel.turn), so FSb's body at fr + 2880 lies inside the
   35-byte first.sroa.7 of the frame. *)
Lemma f5_fsb_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at]. unfold fs0. cbn [fs_body length]. lia.
  - rewrite fst_at_S. unfold turn. cbv zeta.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
    rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* The identity record IDj (38 bytes at fr + 2688) survives a write that misses those bytes. *)
Lemma f5_idj_keep : forall g fr j W m m', IDj g fr j m -> Frame.munch W m m' ->
  (forall x, fr + 2688 <= x < fr + 2726 -> Frame.outside W x) -> IDj g fr j m'.
Proof.
  intros g fr j W m m' (Hb & Hok) MU HW. split; [|exact Hok].
  unfold IDBe in *. apply (fl_bytes W m m' (fr + 2688) _ Hb MU).
  rewrite f5_tID_len. intros x Hx. apply HW. lia.
Qed.

(* Any sub-range of the 416-byte prologue save area [A, A + 416) is byte-backed and writable: it lies inside
   FRA's entry-anchored slot window, because g_S g - 4096 < sp <= A and A + 416 <= g_S g. *)
Lemma f5_spill_stk : forall g fr hb regs mem md A lo hi,
  FRA B APIf ra g fr hb regs mem md -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  A <= lo -> lo <= hi -> hi <= A + 416 -> stk rsegs mem lo hi.
Proof.
  intros g fr hb regs mem md A lo hi HFRA Hr9 HA Hlo Hmid Hhi.
  pose proof HFRA as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hsp & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  destruct Hwin as (Hb0 & Hb1 & Hst).
  assert (HA' : 0 <= A' < 2 ^ 64) by lia.
  assert (EA : A = A').
  { pose proof (rg_eq64 regs 9 A A' Hr9 Hr9') as Hm.
    rewrite (Z.mod_small A (2 ^ 64)) in Hm by lia. rewrite (Z.mod_small A' (2 ^ 64)) in Hm by lia. exact Hm. }
  subst A'.
  split; [lia|]. split; [lia|]. intros a Ha. apply Hst. lia.
Qed.

(* A prefix of a carried byte list is carried at the same address (b5_PF states the record's 38 bytes and its
   six-byte compare operands with `<= length`, and a transport across a write needs an exact length). *)
Lemma f5_bytes_first : forall m a bs k, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof.
  intros m a bs k (H0 & H1 & H).
  assert (Hl : (length (firstn k bs) <= length bs)%nat) by (rewrite length_firstn; lia).
  split; [exact H0|]. split; [lia|].
  intros i Hi. rewrite H by lia.
  rewrite <- (firstn_skipn k bs) at 1. apply nth_error_app1. exact Hi.
Qed.

(* memcmp_model reads only the first n bytes of each list. *)
Lemma f5_mcmp_firstn : forall n l r, SFA.memcmp_model (firstn n l) (firstn n r) n = SFA.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros l r; [reflexivity|].
  destruct l as [|a l]; destruct r as [|b r]; cbn [firstn SFA.memcmp_model]; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

(* The frame body t_phi j is a firstn of flen j bytes, so it has at most flen j bytes. *)
Lemma f5_tphi_len : forall g j, 0 <= flen g j -> Z.of_nat (length (t_phi (g_in g) j)) <= flen g j.
Proof.
  intros g j H0. unfold flen, t_len, t_phi, f_phi in *.
  rewrite length_firstn, Nat2Z.inj_min, Z2Nat.id by lia. lia.
Qed.

(* The metadata byte of an app byte lies below every address from HIGHMEM_BEG on. *)
Lemma f5_sh_below : forall x A, 0 <= x < APPMEM_END -> HIGHMEM_BEG <= A -> Z.shiftr x 3 + ASAN_K + 1 <= A.
Proof.
  intros x A Hx HA. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (D : x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; [lia | unfold APPMEM_END in Hx; lia]).
  unfold ASAN_K, HIGHMEM_BEG in *. lia.
Qed.

(* Everything the span's cut skeleton carries and the identity record IDj, across a write confined to the
   prologue save area that misses [0, A + 240) and [A + 248, A + 280): FLSI (the A4 prologue spills, the loop
   spills [A + 128 / 144 / 216 / 224 / 248], out[]'s six bytes and the 17 bytes at fr + 2691, the harness input
   block, a heap block below stklo < A), the two first-fragment spills (104, 112) and the first fragment's body
   (fr + 2880, at most 23 bytes, f5_fsb_len), the frame body
   (fr + FRAME_BYTES <= A: the identity and fragment records), the ten b5_SPILL words and [A + 232], the record block
   (a_laws_blocks puts it below the real stack's low bound, which is below A), the kind-name table and the thread
   pointer word (both in the image, below HIGHMEM_BEG <= stklo < A). *)
Lemma f5_keep : forall g j phi fr A regs regs' mem mem' md W,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  HB mem phi (flen g j) -> FLSI g j fr regs mem -> LK g fr j regs mem ->
  b5_C g j phi fr regs mem -> IDj g fr j mem ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> all_app W ->
  (forall x, x < A + 240 -> Frame.outside W x) ->
  (forall x, A + 248 <= x < A + 280 -> Frame.outside W x) ->
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 21 = getr regs 21 -> getr regs' 23 = getr regs 23 ->
  HB mem' phi (flen g j) /\ FLSI g j fr regs' mem' /\ LK g fr j regs' mem' /\
  b5_C g j phi fr regs' mem' /\ IDj g fr j mem'.
Proof.
  intros g j phi fr A regs regs' mem mem' md W HFRA HHB HFLSI HLK HC HID H9 HA MU WM HAW Hlo Hmid
    E2 E9 E18 E21 E23.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof HFRA as HF.
  destruct HF as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = A0).
  { apply f5_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  assert (HfrL : 0 <= fr).
  { pose proof (bytes_at_bound rsegs mem fr (le8 (Z_to_bv 64 0x41b58ab3)) Hhdr1) as (Hf0 & _). lia. }
  (* the record block lies below the real stack, which is below the prologue save area *)
  assert (HIn : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (apply in_or_app; left; left; reflexivity).
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
              (AC.a_size (flen g j)) HAH HIn) as (_ & Hphi4096 & Hphistk & _ & _).
  assert (Hphilo : phi + AC.a_size (flen g j) <= A) by lia.
  (* the image constants are far below the save area *)
  assert (Htp0 : 0 <= AC.as_tp AC.ASYMS) by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
  assert (Htp1 : AC.as_tp AC.ASYMS + 16 <= LOWMEM_END) by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
  (* the kind-name table is image data far below LOWMEM_END (a bound, not the address: it holds on every image) *)
  assert (Hkn : 0 <= KIND_NAME <= 0x100000) by (unfold KIND_NAME; lia).
  assert (Hknl : (length kind_name_bytes <= 4096)%nat) by (vm_compute; lia).
  (* the frame, the record and the image all lie below A + 216 *)
  assert (Hfout : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) by (intros x Hx; apply Hlo; lia).
  assert (Hiout : forall x, 0 <= x < LOWMEM_END -> Frame.outside W x) by (intros x Hx; apply Hlo; lia).
  assert (Hpout : forall x, phi <= x < phi + AC.a_size (flen g j) -> Frame.outside W x)
    by (intros x Hx; apply Hlo; lia).
  pose proof HC as HC0.
  destruct HC0 as (Hs23 & Hs18 & (A1 & H9a & HA1 & HSP & H232) & HPH & HFR & HFS & HKN & HFG & HFSj).
  assert (HA1A : A1 = A).
  { apply f5_id; [lia | lia |]. unfold rg in H9, H9a. rewrite <- H9a. exact H9. }
  subst A1.
  assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite E9; exact H9).
  (* HB *)
  assert (HHB' : HB mem' phi (flen g j)).
  { destruct HHB as (Hnz & Had). split; [exact Hnz|].
    exact (sl_addr_keep mem mem' W phi (AC.a_size (flen g j)) Had MU HAW). }
  split; [exact HHB'|].
  (* FLSI *)
  destruct HFLSI as ((HPRO & Hf128 & Hfstk & Hf144 & Hfa17) & Hf216 & Hf224 & Hf248 & HIN & HFLC).
  destruct HPRO as (Hf40 & Hf120 & Hf136 & Hf160 & Hf168 & Hf176 & Hf208 & Hp248 & Hfout6 & Hinb & Hing &
    Hp184 & Hp256 & Hp264 & Hp272 & Hp32).
  destruct HIN as (HINi & HINa & HINb).
  (* the harness input block: a live heap block (when it exists), so below stklo < A *)
  assert (HINb' : bytes_at rsegs mem' (g_p g) (g_in g)).
  { apply (fl_bytes W mem mem' (g_p g) (g_in g) HINb MU). rewrite <- g_n_len. intros x Hx.
    apply Hlo. destruct (Z_lt_le_dec 0 (g_n g)) as [Hn|Hn]; [|lia].
    assert (HIn' : In (g_p g, g_n g) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
      by (apply in_or_app; right; exact (HINi Hn)).
    destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md (g_p g) (g_n g) HAH HIn') as (_ & _ & Hst & _ & _).
    lia. }
  assert (HINa' : addressable mem' (g_p g) (g_n g)) by exact (sl_addr_keep mem mem' W _ _ HINa MU HAW).
  assert (HFLSI' : FLSI g j fr regs' mem').
  { split.
    { split.
      { split; [exact (f5_spill_keep regs regs' A 40 _ mem mem' W Hf40 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hlo; lia))|].
        split; [exact (f5_spill_keep regs regs' A 120 _ mem mem' W Hf120 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hlo; lia))|].
        split; [exact (f5_spill_keep regs regs' A 136 _ mem mem' W Hf136 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hlo; lia))|].
        split; [exact (f5_spill_keep regs regs' A 160 _ mem mem' W Hf160 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hlo; lia))|].
        split; [exact (f5_spill_keep regs regs' A 168 _ mem mem' W Hf168 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hlo; lia))|].
        split; [exact (f5_spill_keep regs regs' A 176 _ mem mem' W Hf176 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hlo; lia))|].
        split; [exact (f5_spill_keep regs regs' A 208 _ mem mem' W Hf208 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hlo; lia))|].
        split; [exact (f5_spill_keep regs regs' A 248 _ mem mem' W Hp248 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hmid; lia))|].
        split; [exact (sl_addr_keep mem mem' W (fr + 2624) 6 Hfout6 MU HAW)|].
        split; [exact HINb'|].
        split.
        { intros Hn. destruct (Hing Hn) as (HH & _). split; [exact HH | exact HINa']. }
        (* push 14D: PRO's A4 spills [A + 184 / 256 / 264 / 272] *)
        split; [exact (f5_spill_keep regs regs' A 184 _ mem mem' W Hp184 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hlo; lia))|].
        split; [exact (f5_spill_keep regs regs' A 256 _ mem mem' W Hp256 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hmid; lia))|].
        split; [exact (f5_spill_keep regs regs' A 264 _ mem mem' W Hp264 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hmid; lia))|].
        split; [exact (f5_spill_keep regs regs' A 272 _ mem mem' W Hp272 H9 HA ltac:(lia) ltac:(lia) E9 MU
                         ltac:(intros x Hx; apply Hmid; lia))|].
        (* v1.9: PRO's [A + 32] = fr + 2880 (A4's 0x813cc) *)
        exact (f5_spill_keep regs regs' A 32 _ mem mem' W Hp32 H9 HA ltac:(lia) ltac:(lia) E9 MU
                 ltac:(intros x Hx; apply Hlo; lia)). }
      split; [exact (f5_spill_keep regs regs' A 128 _ mem mem' W Hf128 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hlo; lia))|].
      split.
      { apply (fl_stk W mem mem' fr (fr + FRAME_BYTES) Hfstk MU WM).
        intros x Hx. left. apply Hfout. lia. }
      split; [exact (f5_spill_keep regs regs' A 144 _ mem mem' W Hf144 H9 HA ltac:(lia) ltac:(lia) E9 MU
                       ltac:(intros x Hx; apply Hlo; lia))|].
      exact (sl_addr_keep mem mem' W (fr + 2691) 17 Hfa17 MU HAW). }
    split; [exact (f5_spill_keep regs regs' A 216 _ mem mem' W Hf216 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_spill_keep regs regs' A 224 _ mem mem' W Hf224 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_spill_keep regs regs' A 248 _ mem mem' W Hf248 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hmid; lia))|].
    split; [split; [exact HINi|]; split; [exact HINa' | exact HINb']|].
    (* FLC (push 14D / 14E, v1.9 slots): the pointer spills, the two record ranges, the compare spills
       [A + 72 / 64] and the two first.sroa.7 byte pointers [A + 56 / 48] *)
    destruct HFLC as (Hc256 & Hc184 & Hc192 & Hc80 & Hc88 & Hc96 & Hc272 & Hc264 & Hcfg & Hcid & Hc72 & Hc64 &
      Hc56 & Hc48).
    split; [exact (f5_spill_keep regs regs' A 256 _ mem mem' W Hc256 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hmid; lia))|].
    split; [exact (f5_spill_keep regs regs' A 184 _ mem mem' W Hc184 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_spill_keep regs regs' A 192 _ mem mem' W Hc192 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_spill_keep regs regs' A 80 _ mem mem' W Hc80 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_spill_keep regs regs' A 88 _ mem mem' W Hc88 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_spill_keep regs regs' A 96 _ mem mem' W Hc96 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_spill_keep regs regs' A 272 _ mem mem' W Hc272 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hmid; lia))|].
    split; [exact (f5_spill_keep regs regs' A 264 _ mem mem' W Hc264 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hmid; lia))|].
    split; [exact (sl_addr_keep mem mem' W (fragb fr) 72 Hcfg MU HAW)|].
    split; [exact (sl_addr_keep mem mem' W (fr + 2688) 38 Hcid MU HAW)|].
    split; [exact (f5_spill_keep regs regs' A 72 _ mem mem' W Hc72 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_spill_keep regs regs' A 64 _ mem mem' W Hc64 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_spill_keep regs regs' A 56 _ mem mem' W Hc56 H9 HA ltac:(lia) ltac:(lia) E9 MU
                     ltac:(intros x Hx; apply Hlo; lia))|].
    exact (f5_spill_keep regs regs' A 48 _ mem mem' W Hc48 H9 HA ltac:(lia) ltac:(lia) E9 MU
             ltac:(intros x Hx; apply Hlo; lia)). }
  split; [exact HFLSI'|].
  (* LK *)
  destruct HLK as (Hj255 & H21 & HOURb).
  assert (HLK' : LK g fr j regs' mem').
  { split; [exact Hj255|]. split; [unfold rg in *; rewrite E21; exact H21|].
    unfold OURb in *. apply (fl_bytes W mem mem' (fr + 2624) (OUR (g_in g)) HOURb MU).
    rewrite OUR_length. intros x Hx. apply Hfout. lia. }
  split; [exact HLK'|].
  (* IDj: the 38 identity bytes at fr + 2688 are frame body *)
  assert (HID' : IDj g fr j mem')
    by (apply (f5_idj_keep g fr j W mem mem' HID MU); intros x Hx; apply Hfout; lia).
  split; [|exact HID'].
  (* b5_C *)
  split; [unfold rg in *; rewrite E23; exact Hs23|].
  split; [unfold rg in *; rewrite E18; exact Hs18|].
  split.
  { exists A. split; [exact H9'|]. split; [exact HA|].
    split; [|exact (f5_q64_keep W mem mem' _ _ H232 MU ltac:(intros x Hx; apply Hlo; lia))].
    destruct HSP as (Hq248 & Hq256 & Hq144 & Hq184 & Hq192 & Hq80 & Hq88 & Hq96 & Hq272 & Hq264).
    split; [exact (f5_q64_keep W mem mem' _ _ Hq248 MU ltac:(intros x Hx; apply Hmid; lia))|].
    split; [exact (f5_q64_keep W mem mem' _ _ Hq256 MU ltac:(intros x Hx; apply Hmid; lia))|].
    split; [exact (f5_q64_keep W mem mem' _ _ Hq144 MU ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_q64_keep W mem mem' _ _ Hq184 MU ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_q64_keep W mem mem' _ _ Hq192 MU ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_q64_keep W mem mem' _ _ Hq80 MU ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_q64_keep W mem mem' _ _ Hq88 MU ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_q64_keep W mem mem' _ _ Hq96 MU ltac:(intros x Hx; apply Hlo; lia))|].
    split; [exact (f5_q64_keep W mem mem' _ _ Hq272 MU ltac:(intros x Hx; apply Hmid; lia))|].
    exact (f5_q64_keep W mem mem' _ _ Hq264 MU ltac:(intros x Hx; apply Hmid; lia)). }
  destruct HPH as (HPHb & HPHp & HPHfs).
  split.
  { split.
    { intros Hlen. pose proof (HPHb Hlen) as Hbs.
      apply (fl_bytes W mem mem' phi (t_g (g_in g) j) Hbs MU).
      unfold t_g. rewrite fr50_length. intros x Hx. apply Hpout.
      unfold AC.a_size in *. lia. }
    split.
    { intros Hlen. replace (AC.aspZ regs') with (AC.aspZ regs);
        [exact (HPHp Hlen) | unfold AC.aspZ; rewrite E2; reflexivity]. }
    { intros Hlen0 (b & Hb & Hw & Hr). apply (HPHfs Hlen0). exists b. split; [exact Hb|]. split; [|exact Hr].
      apply (proj2 (f5_word_eq W mem mem' (AC.as_tp AC.ASYMS) MU
                      ltac:(intros x Hx; apply Hiout; lia) ltac:(lia) ltac:(lia) b)).
      exact Hw. } }
  destruct HFR as (HFRa & HFRb & HFRc & HFRd).
  split.
  { split; [exact (sl_addr_keep mem mem' W (fragb fr) 72 HFRa MU HAW)|].
    split; [exact (sl_addr_keep mem mem' W (fr + 2688) 38 HFRb MU HAW)|].
    split; [|exact HFRd].
    apply (fl_bytes W mem mem' (fragb fr) (t_FG (g_in g) j) HFRc MU).
    rewrite HFRd. unfold fragb. intros x Hx. apply Hfout. lia. }
  destruct HFS as (HFSa & DB & HDB & HDB0 & HDB1).
  split.
  { split.
    { intros FS Hw HFSr Hin. apply (HFSa FS); [|exact HFSr|exact Hin].
      apply (proj2 (f5_word_eq W mem mem' (AC.as_tp AC.ASYMS) MU
                      ltac:(intros x Hx; apply Hiout; lia) ltac:(lia) ltac:(lia) FS)).
      exact Hw. }
    exists DB. split; [|split; [exact HDB0 | exact HDB1]].
    apply (proj1 (f5_word_eq W mem mem' (AC.as_tp AC.ASYMS + 8) MU
                    ltac:(intros x Hx; apply Hiout; lia) ltac:(lia) ltac:(lia) DB)).
    exact HDB. }
  destruct HKN as (HKNa & HKNb).
  split.
  { split.
    { apply (fl_bytes W mem mem' KIND_NAME kind_name_bytes HKNa MU).
      intros x Hx. apply Hiout. lia. }
    exact (sl_addr_keep mem mem' W KIND_NAME 112 HKNb MU HAW). }
  (* FGj: the 72 fragment bytes at fr + 2768 (= fragb fr, the b5_FR bytes) *)
  destruct HFG as (HFGb & HFGok).
  split.
  { split; [|exact HFGok]. unfold FGBe in *.
    apply (fl_bytes W mem mem' (fr + 2768) (t_FG (g_in g) j) HFGb MU).
    rewrite HFRd. intros x Hx. apply Hfout. lia. }
  (* FSj (v1.9): the two first-fragment spills [A + 104 / 112], the body at fr + 2880 (frame body, at most
     23 bytes) and its 35 addressable bytes *)
  destruct HFSj as (Hq104 & Hq112 & Hfsb & Hfsa & HFI).
  split; [exact (f5_spill_keep regs regs' A 104 _ mem mem' W Hq104 H9 HA ltac:(lia) ltac:(lia) E9 MU
                   ltac:(intros x Hx; apply Hlo; lia))|].
  split; [exact (f5_spill_keep regs regs' A 112 _ mem mem' W Hq112 H9 HA ltac:(lia) ltac:(lia) E9 MU
                   ltac:(intros x Hx; apply Hlo; lia))|].
  split.
  { apply (fl_bytes W mem mem' (fr + 2880) _ Hfsb MU).
    pose proof (f5_fsb_len (g_in g) j) as Hbl. intros x Hx. apply Hfout. lia. }
  split; [exact (sl_addr_keep mem mem' W (fr + 2880) 35 Hfsa MU HAW)|].
  exact HFI.
Qed.

(* b5_PF across a write that touches only app memory and misses [0, A + 240): every cell it names lies below
   A + 240 (the record block below stklo < A, the frame with fr + FRAME_BYTES <= A, the metadata bytes below
   HIGHMEM_BEG <= A, the compare spills [A + 72] / [A + 64]). The record's 38-byte prefix and the 6-byte compare
   operands are cut to their exact length first (f5_bytes_first). *)
Lemma f5_pf_keep : forall g j phi fr A regs regs' mem mem' md W,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  b5_PF g j phi fr regs mem -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  Frame.munch W mem mem' -> all_app W ->
  (forall x, x < A + 240 -> Frame.outside W x) ->
  getr regs' 9 = getr regs 9 ->
  b5_PF g j phi fr regs' mem'.
Proof.
  intros g j phi fr A regs regs' mem mem' md W HFRA HPF H9 HA MU HAW Hlo E9.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof HFRA as HF.
  destruct HF as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhigh.
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HA0r : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = A0).
  { apply f5_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  assert (HfrL : 0 <= fr).
  { pose proof (bytes_at_bound rsegs mem fr (le8 (Z_to_bv 64 0x41b58ab3)) Hhdr1) as (Hf0 & _). lia. }
  assert (HIn : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (apply in_or_app; left; left; reflexivity).
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
              (AC.a_size (flen g j)) HAH HIn) as (_ & Hphi4096 & Hphistk & _ & _).
  assert (Hasz : flen g j <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hasz1 : 1 <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hhi : HIGHMEM_BEG <= A) by lia.
  assert (Hphitop : phi + AC.a_size (flen g j) <= A) by lia.
  assert (Hfrtop : fr + FRAME_BYTES <= A) by lia.
  destruct HPF as (A1 & H9a & HA1 & Hlong & H8819).
  assert (HA1A : A1 = A) by (apply f5_id; [lia | lia |]; unfold rg in H9, H9a; rewrite <- H9a; exact H9).
  subst A1.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|]. split; [exact HA|].
  split.
  - intros Hle. destruct (Hlong Hle) as ((rb & Hrb & Hrbl) & Hphib).
    split.
    + exists (firstn 38 rb). split; [|rewrite length_firstn; lia].
      apply (fl_bytes W mem mem' phi _ (f5_bytes_first mem phi rb 38 Hrb) MU).
      rewrite length_firstn. intros x Hx. apply Hlo. lia.
    + apply (fl_bytes W mem mem' phi _ Hphib MU).
      pose proof (f5_tphi_len g j ltac:(lia)) as Hl. intros x Hx. apply Hlo. lia.
  - intros Ht. destruct (H8819 Ht) as
      ((field16 & v14 & v15 & v16 & v17 & Hu16 & Hb14 & Hb15 & Hb16 & Hb17 & Hv14 & Hv15 & Hv16 & Hv17 &
        Hs14 & Hs15 & Hs16 & Hs17 & Ef & Ek) &
       (ls & rs & Hq72 & Hls & Hlsl & Hrs & Hrsl & Hcm & Had) &
       (ls2 & rs2 & Hq64 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcm2 & Had2)).
    (* the metadata bytes of phi + 14 .. phi + 17 lie below HIGHMEM_BEG <= A *)
    assert (Hshk : forall k, 0 <= k < 50 -> Z.shiftr (phi + k) 3 + ASAN_K + 1 <= A)
      by (intros k Hk; apply f5_sh_below; [lia | exact Hhi]).
    pose proof (Hshk 14 ltac:(lia)) as Hk14. pose proof (Hshk 15 ltac:(lia)) as Hk15.
    pose proof (Hshk 16 ltac:(lia)) as Hk16. pose proof (Hshk 17 ltac:(lia)) as Hk17.
    split; [|split].
    + exists field16, v14, v15, v16, v17. unfold u16, b8 in *.
      split; [apply (fl_bytes W mem mem' _ _ Hu16 MU); rewrite length_le2; intros x Hx; apply Hlo; lia|].
      split; [apply (fl_bytes W mem mem' _ _ Hb14 MU); cbn [length]; intros x Hx; apply Hlo; lia|].
      split; [apply (fl_bytes W mem mem' _ _ Hb15 MU); cbn [length]; intros x Hx; apply Hlo; lia|].
      split; [apply (fl_bytes W mem mem' _ _ Hb16 MU); cbn [length]; intros x Hx; apply Hlo; lia|].
      split; [apply (fl_bytes W mem mem' _ _ Hb17 MU); cbn [length]; intros x Hx; apply Hlo; lia|].
      split; [exact Hv14|]. split; [exact Hv15|]. split; [exact Hv16|]. split; [exact Hv17|].
      split; [apply (fl_bytes W mem mem' _ _ Hs14 MU); cbn [length]; intros x Hx; apply Hlo; lia|].
      split; [apply (fl_bytes W mem mem' _ _ Hs15 MU); cbn [length]; intros x Hx; apply Hlo; lia|].
      split; [apply (fl_bytes W mem mem' _ _ Hs16 MU); cbn [length]; intros x Hx; apply Hlo; lia|].
      split; [apply (fl_bytes W mem mem' _ _ Hs17 MU); cbn [length]; intros x Hx; apply Hlo; lia|].
      split; [exact Ef | exact Ek].
    + exists (firstn 6 ls), (firstn 6 rs).
      split; [exact (f5_q64_keep W mem mem' _ _ Hq72 MU ltac:(intros x Hx; apply Hlo; lia))|].
      split; [apply (fl_bytes W mem mem' _ _ (f5_bytes_first mem (fr + 186) ls 6 Hls) MU);
              rewrite length_firstn; intros x Hx; apply Hlo; lia|].
      split; [rewrite length_firstn; lia|].
      split; [apply (fl_bytes W mem mem' _ _ (f5_bytes_first mem phi rs 6 Hrs) MU);
              rewrite length_firstn; intros x Hx; apply Hlo; lia|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite f5_mcmp_firstn; exact Hcm|].
      exact (sl_addr_keep mem mem' W (fr + 186) 6 Had MU HAW).
    + exists (firstn 6 ls2), (firstn 6 rs2).
      split; [exact (f5_q64_keep W mem mem' _ _ Hq64 MU ltac:(intros x Hx; apply Hlo; lia))|].
      split; [apply (fl_bytes W mem mem' _ _ (f5_bytes_first mem (fr + 180) ls2 6 Hls2) MU);
              rewrite length_firstn; intros x Hx; apply Hlo; lia|].
      split; [rewrite length_firstn; lia|].
      split; [apply (fl_bytes W mem mem' _ _ (f5_bytes_first mem (phi + 6) rs2 6 Hrs2) MU);
              rewrite length_firstn; intros x Hx; apply Hlo; lia|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite f5_mcmp_firstn; exact Hcm2|].
      exact (sl_addr_keep mem mem' W (fr + 180) 6 Had2 MU HAW).
Qed.

(* a_laws_store, taken apart once in this file (a Theorem Labs lane's rule for generated laws until N+1): the law is split by
   decompose and each fact is found by its type, not by its position, so a conjunct appended to the law is one
   more unused hypothesis here. *)
Lemma f5_store_law : forall H mem mem' md,
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
  intros H mem mem' md HAH Hmc Hw.
  pose proof (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hmc Hw)
    as L.
  decompose [and] L.
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* FRA and ENT move across a write confined to the spill words [A+240, A+248) and [A+280, A+288). The write is
   app memory above stklo (stklo <= S - SLOT_STACK < sp <= A, on both frame arms) and below the entry sp S, so it
   is a_store_ok for a_laws_store; it misses every FRA cell: the frame header and the FRAME_SHADOW frame shadow
   bytes (the frame is below A by FRA's fr + FRAME_BYTES <= A, and the shadow lies below HIGHMEM_BEG <= A), the
   A+304 and A+16..A+32 words, the saved registers [S-104, S) and the low runtime and image cells. It lies inside the
   entry-anchored slot window [S - SLOT_STACK, S) (whose mem' facts the caller gives from the concrete stores),
   so ent_store keeps ENT, and the FakeStack frame record lies below stklo, so fsrec_stklo keeps it. *)
Lemma f5_fra_spill : forall g fr hb regs regs' mem mem' md md' Asp,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  rg regs 9 Asp -> 0 <= Asp < 2 ^ 64 ->
  Frame.munch [(Asp + 240, Asp + 248); (Asp + 280, Asp + 288)] mem mem' ->
  Frame.wmono rsegs mem mem' ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  AsanLift.mat_le md md' ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  intros g fr hb regs regs' mem mem' md md' Asp HFRA HENT H9 HA MU WM HWIN' Hmat
    E2 E3 E4 E8 E9 E19 E26.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HAsr : 0 <= A0 < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HspN : HIGHMEM_BEG < sp) by lia.
  assert (HA0e : Asp = A0).
  { apply f5_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A0.
  assert (HfrL : 0 <= fr).
  { pose proof (bytes_at_bound rsegs mem fr (le8 (Z_to_bv 64 0x41b58ab3)) Hhdr1) as (Hf0 & _). lia. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = Asp).
  { intros A' HA' HA'r. apply f5_id; [lia | lia |]. rewrite <- HA'. exact H9. }
  set (W := [(Asp + 240, Asp + 248); (Asp + 280, Asp + 288)]) in MU.
  assert (HOUT : forall x, 0 <= x < HIGHMEM_BEG -> Frame.outside W x).
  { intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I; lia. }
  assert (HRO : ro_agree rsegs mem').
  { apply (sl_ro_keep W mem mem' Hro MU). intros x Hx. apply HOUT. lia. }
  assert (HAW : all_app W).
  { subst W. cbn [all_app].
    split; [apply f5_app_ivl; lia | split; [apply f5_app_ivl; lia | exact I]]. }
  assert (HD : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN. cbn [disjoint_from]. repeat split; first [exact I | left; lia]. }
  assert (Hwrit : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hmc : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    subst W. cbn [Frame.outside]. repeat split; try exact I; intro HC; apply Hns;
      right; left; lia. }
  destruct (f5_store_law (hb ++ g_H g) mem mem' md HAH Hmc Hwrit) as (HAH' & Hown & HSTKeq & HSTKhi).
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  { apply (sl_stk_run B APIf ra empty FF g fr hb regs regs' mem mem' md W
             HFRA MU WM HRO HAW HD HAH' HSTKeq).
    - (* frame header [fr, fr+24) *)
      intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - (* everything below HIGHMEM_BEG *)
      intros x Hx. apply HOUT. lia.
    - (* the frame-base spill [A+304, A+312) *)
      intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx.
      subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - (* the 13 saved caller registers [S-104, S) *)
      intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - (* the FRAME_SHADOW frame shadow bytes *)
      intros x Hx. subst W. cbn [Frame.outside]. repeat split; try exact I;
        revert Hx; unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia.
    - (* the fr reload and release-arm selector spills [A+16, A+32) *)
      intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx.
      subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - exact HWIN'.
    - (* the FakeStack frame record: its three cells are at or below stklo *)
      intros Hrec. eapply fsrec_stklo; [exact Hrec | exact HAH | exact MU |].
      intros x Hx _. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    - exact E2.
    - exact E3.
    - exact E4.
    - exact E8.
    - exact E9.
    - exact E19.
    - exact E26. }
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRA'); try reflexivity; exact Hmat.
  - eapply ent_mat; [| exact Hmat].
    eapply ent_store with (W := W); [exact HENT | exact HFRA | exact MU | | exact HSTKeq | exact HSTKhi |].
    + intros x Hx.
      destruct (Z_lt_le_dec x (Asp + 240)) as [H1|H1];
        [| destruct (Z_lt_le_dec x (Asp + 288)) as [H2|H2]].
      * left. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
      * right. left. lia.
      * left. subst W. cbn [Frame.outside]. repeat split; try exact I; lia.
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ---- The short-frame arm (t_len j < 50): the join at 0x81e88 and the entry at 0x81e84, both leaving to the
   model join 0x81f54. *)

Lemma seg_F5_df0 : forall j,
  Hat B APIf ra (Inv_A81f54_at B APIf ra) j -> Hat B APIf ra (Inv_A81e88_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & Hlen50 & Hs8 & Hu32 & HID & HF17 & _)). subst c.
  rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof HC as HC0.
  destruct HC0 as (Hs23 & Hs18 & (A & H9 & HA & HSP) & HPH & HFR & HFS & HKN).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGT & Happ).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hfr0 : 0 < fr) by (unfold AC.GT in HGT; lia).
  assert (HAeq : A = Asp).
  { apply f5_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A.
  destruct HF17 as (A7 & H97 & HA7 & Hq7).
  assert (EA7 : A7 = Asp) by (apply f5_id; [lia | lia |]; unfold rg in H97, Hr9; rewrite <- H97; exact Hr9).
  subst A7.
  assert (Hk0 : t_k (g_in g) j = 0) by (apply f5_k; exact Hlen50).
  rewrite Hk0 in Hs8.
  (* the two spill cells are byte-backed: they lie inside the 416-byte save area *)
  destruct (f5_spill_stk g fr (hb1 phi (AC.a_size (flen g j))) regs mem md Asp
              (Asp + 240) (Asp + 288) HFRA Hr9 HAspR ltac:(lia) ltac:(lia) ltac:(lia))
    as (HSTKl & HSTKh & HSTKf).
  assert (HS1 : store_ok rsegs mem (wa (Asp + 240)) 8 = true).
  { eapply (f5_store_ok mem mem (Asp + 240) 8); [ | apply wmono_refl | lia | lia ].
    intros i Hi. exact (proj1 (HSTKf (Asp + 240 + i) ltac:(lia))). }
  assert (HS2 : forall m', wmono rsegs mem m' -> store_ok rsegs m' (wa (Asp + 280)) 8 = true).
  { intros m' HW'. eapply (f5_store_ok mem m' (Asp + 280) 8); [ | exact HW' | lia | lia ].
    intros i Hi. exact (proj1 (HSTKf (Asp + 280 + i) ltac:(lia))). }
  apply (sl_run regs (Z_to_bv 64 0x81e88) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81f54 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 22 = Z_to_bv 64 0 /\ getr R 25 = Z_to_bv 64 0 /\ getr R 20 = Z_to_bv 64 1 /\
       mem' = write_to_mem (write_to_mem mem (wa (Asp + 240)) (le8 (Z_to_bv 64 0)))
                           (wa (Asp + 280)) (le8 (Z_to_bv 64 0)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f5_mkR_expand. f5_subst_slot Hs8. f5_subst_slot Hr9.
    (* 0x81e88 bnez s8 : s8 = t_k j = 0, not taken *)
    step. if_false.
    (* 0x81e8c li s6,0 ; 0x81e90 li s9,0 ; 0x81e94 sd zero,240(s1) *)
    step. step. step.
    lazymatch goal with |- Exec.evt _ _ (MState.MS _ _ _ _ _ ?mm _) =>
      pose proof (HS2 mm ltac:(apply wmono_write; apply wmono_refl)) as HS2' end.
    (* 0x81e98 sd zero,280(s1) ; 0x81e9c li s4,1 ; 0x81ea0 j 81f54 *)
    step. step. step.
    finish.
    all: simp_regs; try reflexivity.
    all: try (apply bv_eq; vm_compute; reflexivity).
  - intros R pc' mem' regs'' md'
      (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR24 & HR22 & HR25 & HR20 & Hmem)
      Hreg Hmat.
    subst pc'.
    set (W := [(Asp + 240, Asp + 248); (Asp + 280, Asp + 288)]).
    assert (MU1 : Frame.munch W mem (write_to_mem mem (wa (Asp + 240)) (le8 (Z_to_bv 64 0)))).
    { subst W. apply (munch_write _ mem mem (Asp + 240) (le8 (Z_to_bv 64 0)));
        [ apply munch_refl | lia | rewrite length_le8; lia
        | rewrite length_le8; cbn [inside]; left; lia ]. }
    assert (MU : Frame.munch W mem mem').
    { subst mem'. apply (munch_write _ mem _ (Asp + 280) (le8 (Z_to_bv 64 0)));
        [ exact MU1 | lia | rewrite length_le8; lia
        | subst W; rewrite length_le8; cbn [inside]; right; left; lia ]. }
    assert (WM : Frame.wmono rsegs mem mem')
      by (subst mem'; apply wmono_write; apply wmono_write; apply wmono_refl).
    assert (HAW : all_app W).
    { subst W. cbn [all_app].
      split; [apply f5_app_ivl; lia | split; [apply f5_app_ivl; lia | exact I]]. }
    assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { subst mem'. apply stk_write; [apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]
                                   | lia | rewrite length_le8; lia]. }
    assert (HFE : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs'' mem' md' /\
                  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { apply (f5_fra_spill g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem mem' md md' Asp
               HFRA HENT Hr9 HAspR MU WM HWIN' Hmat); rewrite Hreg; assumption. }
    destruct HFE as (HFRA'' & HENT'').
    (* the spill cell [A+280] after the stores *)
    assert (Hq280 : q64 mem' (Asp + 280) 0).
    { subst mem'. unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    (* the carried skeleton *)
    assert (HWout1 : forall x, x < Asp + 240 -> Frame.outside W x)
      by (intros x Hx; subst W; cbn [Frame.outside]; repeat split; try exact I; lia).
    assert (HWout2 : forall x, Asp + 248 <= x < Asp + 280 -> Frame.outside W x)
      by (intros x Hx; subst W; cbn [Frame.outside]; repeat split; try exact I; lia).
    assert (HE2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
    assert (HE9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9).
    assert (HE18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact HR18).
    assert (HE21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
    assert (HE23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact HR23).
    destruct (f5_keep g j phi fr Asp regs regs'' mem mem' md W HFRA HHB HFLSI HLK HC HID Hr9 HAspR
                MU WM HAW HWout1 HWout2 HE2 HE9 HE18 HE21 HE23)
      as (HHB' & HFLSI' & HLK' & HC' & HID').
    (* the four F17CARRY bundles of 0x81f54 on this arm: [A + 200] = phi + 18 (F4's store, missed here),
       [A + 240] = 0 (0x81e94) with t_8819 j false, and the record group, empty for a short record *)
    assert (Hq240 : q64 mem' (Asp + 240) 0).
    { subst mem'. unfold q64. apply bytes_at_write_other;
        [ apply bytes_at_write_same; [lia | rewrite length_le8; lia] | lia | rewrite length_le8; lia
        | rewrite !length_le8; lia ]. }
    assert (H9'' : rg regs'' 9 Asp) by (unfold rg; rewrite Hreg, HR9; unfold rg in Hr9; exact Hr9).
    assert (H8819f : t_8819 (g_in g) j = false) by (apply f5_8819; exact Hlen50).
    assert (HF17' : b5_F17 g j phi fr regs'' mem').
    { exists Asp. split; [exact H9''|]. split; [exact HAspR|].
      exact (f5_q64_keep W mem mem' _ _ Hq7 MU ltac:(intros x Hx; apply HWout1; lia)). }
    assert (HW240' : b5_W240 g j regs'' mem').
    { exists Asp. split; [exact H9''|]. split; [exact HAspR|].
      exists 0. split; [exact Hq240|]. split; [lia|].
      split; [intros E; rewrite H8819f in E; discriminate | intros _; reflexivity]. }
    (* b5_PF: every part is guarded off on the short arm (flen j < 50, t_8819 j false) *)
    assert (HPF' : b5_PF g j phi fr regs'' mem').
    { exists Asp. split; [exact H9''|]. split; [exact HAspR|].
      split; [intros Hl; exfalso; lia | intros E; rewrite H8819f in E; discriminate]. }
    (* the model flags of this arm *)
    assert (E22 : (if t_big (g_in g) j then phi + 18 else 0) = 0)
      by (rewrite (f5_big (g_in g) j Hlen50); reflexivity).
    assert (E25 : b2z (t_tfill (g_in g) j) = 0)
      by (rewrite (f5_tfill (g_in g) j Hlen50); reflexivity).
    assert (E20 : 1 - b2z (t_sum_ok (g_in g) j) = 1)
      by (rewrite (f5_sum (g_in g) j Hlen50); reflexivity).
    assert (E280 : b2z (t_sum_ok (g_in g) j) = 0)
      by (rewrite (f5_sum (g_in g) j Hlen50); reflexivity).
    rewrite <- SEGS. apply Hexit.
    exists phi, regs'', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA''|].
    split; [exact HENT''|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split; [|split; [exact HID'|]; split; [exact HF17'|]; split; [exact HW240' | exact HPF']].
    (* b5_K *)
    unfold b5_K. rewrite E20, E22, E25, E280.
    split; [unfold rg; rewrite Hreg; exact HR20|].
    split; [unfold rg; rewrite Hreg; exact HR22|].
    split; [unfold rg; rewrite Hreg, HR24, Hk0; unfold rg in Hs8; exact Hs8|].
    split; [unfold rg; rewrite Hreg; exact HR25|].
    split.
    { exists Asp. split; [unfold rg; rewrite Hreg, HR9; unfold rg in Hr9; exact Hr9|].
      split; [lia | exact Hq280]. }
    split; [exact (f5_u32_keep W mem mem' _ _ Hu32 MU ltac:(intros x Hx; apply HWout1; lia))|].
    apply f5_reply; [exact (proj1 HHB) | exact Hfr0].
Qed.

Lemma seg_F5 : forall j,
  Hat B APIf ra (Inv_A81f54_at B APIf ra) j -> Hat B APIf ra (Inv_A81e84_at B APIf ra) j.
Proof.
  intros j Hexit.
  pose proof (seg_F5_df0 j Hexit) as Hdf0.
  intros g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & Hlen50 & Ha0 & Hu32 & HID & HF17 & HPF)). subst c.
  rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hk0 : t_k (g_in g) j = 0) by (apply f5_k; exact Hlen50).
  rewrite Hk0 in Ha0.
  apply (sl_run regs (Z_to_bv 64 0x81e84) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81e88 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = Z_to_bv 64 0)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f5_mkR_expand. f5_subst_slot Ha0.
    (* 0x81e84 mv s8,a0 *)
    step. finish.
    all: simp_regs; try reflexivity.
    all: try (apply bv_eq; vm_compute; reflexivity).
  - intros R pc' mem' regs'' md'
      (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR24) Hreg Hmat.
    subst pc' mem'. rewrite <- SEGS. apply Hdf0.
    exists phi, regs'', mem, md', fr.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem md md' HFRA);
        [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
        | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
        | rewrite Hreg; exact HR26 | exact Hmat ]. }
    split; [ eapply ent_mat; [ exact HENT | exact Hmat ] |].
    (* the memory is unchanged; only the register file moved *)
    assert (MU0 : Frame.munch (@nil (Z * Z)) mem mem) by apply munch_refl.
    assert (WM0 : Frame.wmono rsegs mem mem) by apply wmono_refl.
    assert (HAW0 : all_app (@nil (Z * Z))) by (cbn [all_app]; exact I).
    assert (HO0 : forall x : Z, Frame.outside (@nil (Z * Z)) x) by (intros x; cbn [Frame.outside]; exact I).
    assert (HE2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
    assert (HE9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9).
    assert (HE18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact HR18).
    assert (HE21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
    assert (HE23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact HR23).
    destruct (f5_keep g j phi fr Asp regs regs'' mem mem md (@nil (Z * Z))
                HFRA HHB HFLSI HLK HC HID Hr9 HAspR MU0 WM0 HAW0
                (fun x (_ : x < Asp + 240) => HO0 x)
                (fun x (_ : Asp + 248 <= x < Asp + 280) => HO0 x)
                HE2 HE9 HE18 HE21 HE23)
      as (HHB' & HFLSI' & HLK' & HC' & HID').
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split; [exact Hlen50|].
    split; [unfold rg; rewrite Hreg, HR24, Hk0; reflexivity|].
    split; [exact Hu32|]. split; [exact HID'|].
    destruct HF17 as (A7 & H97 & HA7 & Hq7).
    split.
    { exists A7. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H97; exact H97|].
      split; [exact HA7 | exact Hq7]. }
    (* b5_PF: the memory is unchanged and s1 is kept *)
    destruct HPF as (A9 & H99 & HPF9).
    exists A9. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H99; exact H99 | exact HPF9].
Qed.

(* ---- The long-frame arm (t_len j >= 50): entries 0x81ea4 (F4's 0x81e28 edge, record byte 12 is not 0x88, so
   t_8819 j is false and [s1+240] is cleared here) and 0x81ea8 (F4's 0x81e50 edge, [s1+240] already holds
   b2z (t_8819 j)), both falling into 0x81ec0, the first turn of the 32-byte block-sum loop. *)

Lemma seg_F5_e10 : forall j,
  Hat B APIf ra (Inv_A81ec0_at B APIf ra) j -> Hat B APIf ra (Inv_A81ea8_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & Hlen50 & Hs6 & Hs8 & Hs9 & Hq240 & Hu32 & HID & HF17 & HW240 & HPF)).
  subst c.
  rewrite SEGS.
  pose proof HC as HC0.
  destruct HC0 as (Hs23 & Hs18 & (A & H9 & HA & HSP) & HPH & HFR & HFS & HKN).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hphi : 0 <= phi /\ phi + 50 <= 2 ^ 64).
  { destruct HHB as (_ & Had). destruct Had as (Hp0 & Hn0 & Hpn & _).
    unfold AC.a_size in Hpn, Hn0. lia. }
  apply (sl_run regs (Z_to_bv 64 0x81ea8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81ec0 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\
       getr R 22 = Z_to_bv 64 (Z.land 18446744073709551615 (bv_unsigned (Z_to_bv 64 (phi + 18)))) /\
       getr R 10 = Z_to_bv 64 (phi + 18) /\
       getr R 12 = Z_to_bv 64 (phi + 18) /\ getr R 11 = Z_to_bv 64 0 /\ getr R 13 = Z_to_bv 64 32)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f5_mkR_expand. f5_subst_slot Hs6. f5_subst_slot Hs23. f5_subst_slot Hs9.
    (* 0x81ea8 li a1,0 ; 0x81eac addi a0,s6,-1 ; 0x81eb0 addi a2,s7,18 ; 0x81eb4 and s6,a0,s9 ;
       0x81eb8 li a3,32 ; 0x81ebc mv a0,a2 ; fall into 0x81ec0 *)
    step. step. step. step. step. step.
    finish.
    all: simp_regs; try reflexivity.
  - intros R pc' mem' regs'' md'
      (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR24 & HR25 &
       HR22 & HR10 & HR12 & HR11 & HR13) Hreg Hmat.
    rewrite (f5_and_ones (phi + 18) ltac:(lia)) in HR22.
    subst pc' mem'. rewrite <- SEGS. apply Hexit.
    exists phi, regs'', mem, md', fr.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem md md' HFRA);
        [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
        | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
        | rewrite Hreg; exact HR26 | exact Hmat ]. }
    split; [ eapply ent_mat; [ exact HENT | exact Hmat ] |].
    assert (MU0 : Frame.munch (@nil (Z * Z)) mem mem) by apply munch_refl.
    assert (WM0 : Frame.wmono rsegs mem mem) by apply wmono_refl.
    assert (HAW0 : all_app (@nil (Z * Z))) by (cbn [all_app]; exact I).
    assert (HO0 : forall x : Z, Frame.outside (@nil (Z * Z)) x) by (intros x; cbn [Frame.outside]; exact I).
    assert (HE2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
    assert (HE9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9).
    assert (HE18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact HR18).
    assert (HE21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
    assert (HE23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact HR23).
    destruct (f5_keep g j phi fr Asp regs regs'' mem mem md (@nil (Z * Z))
                HFRA HHB HFLSI HLK HC HID Hr9 HAspR MU0 WM0 HAW0
                (fun x (_ : x < Asp + 240) => HO0 x)
                (fun x (_ : Asp + 248 <= x < Asp + 280) => HO0 x)
                HE2 HE9 HE18 HE21 HE23)
      as (HHB' & HFLSI' & HLK' & HC' & HID').
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split; [exact Hlen50|].
    split; [unfold rg; rewrite Hreg; exact HR10|].
    split; [unfold rg; rewrite Hreg; exact HR11|].
    split; [unfold rg; rewrite Hreg; exact HR12|].
    split; [unfold rg; rewrite Hreg; exact HR13|].
    split; [unfold rg; rewrite Hreg; exact HR22|].
    split; [unfold rg; rewrite Hreg, HR24; unfold rg in Hs8; exact Hs8|].
    split; [unfold rg; rewrite Hreg, HR25; unfold rg in Hs9; exact Hs9|].
    destruct Hq240 as (A' & H9' & HA' & Hq).
    split.
    { exists A'. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H9'; exact H9'|].
      split; [exact HA' | exact Hq]. }
    split; [exact Hu32|]. split; [exact HID'|].
    (* the memory is unchanged: [A + 200] and [A + 240] carry over with s1 *)
    destruct HF17 as (A7 & H97 & HA7 & Hq7).
    split.
    { exists A7. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H97; exact H97|].
      split; [exact HA7 | exact Hq7]. }
    destruct HW240 as (A8 & H98 & HA8 & HW8).
    split.
    { exists A8. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H98; exact H98|].
      split; [exact HA8 | exact HW8]. }
    destruct HPF as (A9 & H99 & HPF9).
    exists A9. split; [unfold rg; rewrite Hreg, HR9; unfold rg in H99; exact H99 | exact HPF9].
Qed.

Lemma seg_F5_e0c : forall j,
  Hat B APIf ra (Inv_A81ec0_at B APIf ra) j -> Hat B APIf ra (Inv_A81ea4_at B APIf ra) j.
Proof.
  intros j Hexit.
  pose proof (seg_F5_e10 j Hexit) as He10.
  intros g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & Hlen50 & Hs6 & Hs8 & Hs9 & H8819 & Hu32 & HID & HF17 & HPF)). subst c.
  rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof HC as HC0.
  destruct HC0 as (Hs23 & Hs18 & (A & H9 & HA & HSP) & HPH & HFR & HFS & HKN).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = Asp).
  { apply f5_id; [lia | lia |]. unfold rg in H9, Hr9. rewrite <- H9. exact Hr9. }
  subst A.
  destruct HF17 as (A7 & H97 & HA7 & Hq7).
  assert (EA7 : A7 = Asp) by (apply f5_id; [lia | lia |]; unfold rg in H97, Hr9; rewrite <- H97; exact Hr9).
  subst A7.
  destruct (f5_spill_stk g fr (hb1 phi (AC.a_size (flen g j))) regs mem md Asp
              (Asp + 240) (Asp + 288) HFRA Hr9 HAspR ltac:(lia) ltac:(lia) ltac:(lia))
    as (HSTKl & HSTKh & HSTKf).
  assert (HS1 : store_ok rsegs mem (wa (Asp + 240)) 8 = true).
  { eapply (f5_store_ok mem mem (Asp + 240) 8); [ | apply wmono_refl | lia | lia ].
    intros i Hi. exact (proj1 (HSTKf (Asp + 240 + i) ltac:(lia))). }
  apply (sl_run regs (Z_to_bv 64 0x81ea4) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81ea8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
       getr R 23 = getr regs 23 /\ getr R 18 = getr regs 18 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 22 = getr regs 22 /\
       mem' = write_to_mem mem (wa (Asp + 240)) (le8 (Z_to_bv 64 0)))
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f5_mkR_expand. f5_subst_slot Hr9.
    (* 0x81ea4 sd zero,240(s1) ; fall into 0x81ea8 *)
    step. finish.
    all: simp_regs; try reflexivity.
  - intros R pc' mem' regs'' md'
      (Hpc & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR21 & HR26 & HR23 & HR18 & HR24 & HR25 & HR22 & Hmem)
      Hreg Hmat.
    subst pc'.
    set (W := [(Asp + 240, Asp + 248); (Asp + 280, Asp + 288)]).
    assert (MU : Frame.munch W mem mem').
    { subst mem' W. apply (munch_write _ mem mem (Asp + 240) (le8 (Z_to_bv 64 0)));
        [ apply munch_refl | lia | rewrite length_le8; lia
        | rewrite length_le8; cbn [inside]; left; lia ]. }
    assert (WM : Frame.wmono rsegs mem mem') by (subst mem'; apply wmono_write; apply wmono_refl).
    assert (HAW : all_app W).
    { subst W. cbn [all_app].
      split; [apply f5_app_ivl; lia | split; [apply f5_app_ivl; lia | exact I]]. }
    assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { subst mem'. apply stk_write; [exact Hwin | lia | rewrite length_le8; lia]. }
    assert (HFE : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs'' mem' md' /\
                  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { apply (f5_fra_spill g fr (hb1 phi (AC.a_size (flen g j))) regs regs'' mem mem' md md' Asp
               HFRA HENT Hr9 HAspR MU WM HWIN' Hmat); rewrite Hreg; assumption. }
    destruct HFE as (HFRA'' & HENT'').
    assert (Hq240 : q64 mem' (Asp + 240) 0).
    { subst mem'. unfold q64. apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
    assert (HWout1 : forall x, x < Asp + 240 -> Frame.outside W x)
      by (intros x Hx; subst W; cbn [Frame.outside]; repeat split; try exact I; lia).
    assert (HWout2 : forall x, Asp + 248 <= x < Asp + 280 -> Frame.outside W x)
      by (intros x Hx; subst W; cbn [Frame.outside]; repeat split; try exact I; lia).
    assert (HE2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
    assert (HE9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9).
    assert (HE18 : getr regs'' 18 = getr regs 18) by (rewrite Hreg; exact HR18).
    assert (HE21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact HR21).
    assert (HE23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact HR23).
    destruct (f5_keep g j phi fr Asp regs regs'' mem mem' md W HFRA HHB HFLSI HLK HC HID Hr9 HAspR
                MU WM HAW HWout1 HWout2 HE2 HE9 HE18 HE21 HE23)
      as (HHB' & HFLSI' & HLK' & HC' & HID').
    (* b5_PF: its cells lie below A + 240, missed by the 0x81ea4 store *)
    pose proof (f5_pf_keep g j phi fr Asp regs regs'' mem mem' md W HFRA HPF Hr9 HAspR MU HAW HWout1 HE9)
      as HPF'.
    assert (E240 : b2z (t_8819 (g_in g) j) = 0) by (rewrite H8819; reflexivity).
    rewrite <- SEGS. apply He10.
    exists phi, regs'', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA''|].
    split; [exact HENT''|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB'|].
    split; [exact HFLSI'|].
    split; [exact HLK'|].
    split; [exact HC'|].
    split; [exact Hlen50|].
    split; [unfold rg; rewrite Hreg, HR22; unfold rg in Hs6; exact Hs6|].
    split; [unfold rg; rewrite Hreg, HR24; unfold rg in Hs8; exact Hs8|].
    split; [unfold rg; rewrite Hreg, HR25; unfold rg in Hs9; exact Hs9|].
    rewrite E240.
    split.
    { exists Asp. split; [unfold rg; rewrite Hreg, HR9; unfold rg in Hr9; exact Hr9|].
      split; [lia | exact Hq240]. }
    split; [exact (f5_u32_keep W mem mem' _ _ Hu32 MU ltac:(intros x Hx; apply HWout1; lia))|].
    split; [exact HID'|].
    (* b5_F17: F4's [A + 200] word, missed by the 0x81ea4 store; b5_W240: that store's 0 with t_8819 j false *)
    split.
    { exists Asp. split; [unfold rg; rewrite Hreg, HR9; unfold rg in Hr9; exact Hr9|].
      split; [lia | exact (f5_q64_keep W mem mem' _ _ Hq7 MU ltac:(intros x Hx; apply HWout1; lia))]. }
    split.
    { exists Asp. split; [unfold rg; rewrite Hreg, HR9; unfold rg in Hr9; exact Hr9|]. split; [lia|].
      exists 0. split; [exact Hq240|]. split; [lia|].
      split; [intros E; rewrite H8819 in E; discriminate | intros _; reflexivity]. }
    exact HPF'.
Qed.

End S.
