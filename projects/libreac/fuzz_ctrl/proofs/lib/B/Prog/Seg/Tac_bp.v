(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 685 of its 794 lines of code are new or changed and 902 lines of the source are left out. *)
(* Shared helpers for a Theorem Labs lane's image-B segments P1-P6 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B):
   rule 24: no function proved (slot segments).  The byte / shadow / stack helpers and the normalized-memory run
   lemma are Seg/R3.v's (a working branch eb5573148b), renamed; bp_fra is R3's r3_fra.  bp_post is
   R3's continuation made generic: FRA and ENT move across a run whose write set W lies in the frame's 392 shadow
   bytes, the frame body [fr + 24, fr + 3136) and a callee's own stack window [sp - K, sp) (K <= FN_STACK), when
   every written byte is readable afterwards and the FRA registers are kept.  libreac v1.9.0: the frame is
   FRAME_BYTES = 3136 bytes (FRAME_SHADOW = 392 shadow bytes; patched 3040 / 380) and FRA's fr reload and selector
   spills are [A + 40, A + 56) (patched [A + 56, A + 72)). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
Import ListNotations.
Open Scope Z_scope.

(* ---- byte and shadow helpers ---- *)

Lemma bp_le1_lit : forall z, 0 <= z < 2 ^ 64 -> le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof. intros z Hz. unfold le1. rewrite MState.unsigned_lit by lia. reflexivity. Qed.

Lemma bp_le1 : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. reflexivity. Qed.

(* A one-byte store `sb r,o(s3)` writes `le1 r`; the engine records it in the shadow cells once it is a byte list. *)
Ltac bp_fix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      first [rewrite (bp_le1_lit z) by lia | rewrite (bp_le1 (Z_to_bv 64 z))]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?v)) _) =>
      rewrite (bp_le1 v); mem_after_store
  | _ => idtac
  end.
Ltac bp_sb := step; bp_fix.

Lemma bp_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (H0 & H1 & H) Hx.
  pose proof (H (Z.to_nat (x - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (x - A))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:En; [exists b; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma bp_ba_sub : forall m A bs k j, bytes_at rsegs m A bs -> (k + j <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma bp_nth_repeat : forall (x : byte) n k, (k < n)%nat -> nth_error (repeat x n) k = Some x.
Proof. intros x n. induction n as [|n IH]; intros k Hk; [lia|]. destruct k; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma bp_shadow_rw : forall W m m', shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> outside W a \/ exists b, mrd rsegs m' (wa a) = Some b) -> shadow_rw m'.
Proof.
  intros W m m' HS MU WM H a Ha. destruct (HS a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (H a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. pose proof (in_shadow_range a Ha) as Hra.
  rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma bp_sh_add : forall p i, p mod 8 = 0 -> 0 <= i -> shadow_addr (p + i) = shadow_addr p + i / 8.
Proof. intros p i Hp Hi. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The shadow of 8 z bytes at p (p mod 8 = 0) is z zero bytes. *)
Lemma bp_addr_z : forall m p (z : nat) n, n = 8 * Z.of_nat z -> 0 <= p -> p mod 8 = 0 -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) (repeat (Z_to_bv 8 0) z) -> addressable m p n.
Proof.
  intros m p z n -> Hp Hp8 Hpe Happ (_ & _ & Hb).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|].
  exists (Z_to_bv 8 0). split; [|left; reflexivity].
  rewrite bp_sh_add by lia.
  assert (Hq : 0 <= i / 8 < Z.of_nat z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hk : (Z.to_nat (i / 8) < z)%nat) by lia.
  pose proof (Hb (Z.to_nat (i / 8))) as E. rewrite repeat_length in E. specialize (E Hk).
  rewrite Z2Nat.id in E by lia. rewrite E. apply bp_nth_repeat. exact Hk.
Qed.

(* The shadow of r < 8 bytes at p (p mod 8 = 0) is the byte r. *)
Lemma bp_addr_r : forall m p r (b : byte), 0 <= p -> p mod 8 = 0 -> 0 < r < 8 -> bv_signed b = r ->
  p + r <= APPMEM_END -> (forall i, 0 <= i < r -> app_mem (p + i)) ->
  bytes_at rsegs m (shadow_addr p) [b] -> addressable m p r.
Proof.
  intros m p r b Hp Hp8 Hr Hb Hpe Happ (_ & _ & H).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [exact (Happ i Hi)|]. exists b. split.
  - rewrite bp_sh_add by lia. replace (i / 8) with 0 by (symmetry; apply Z.div_small; lia).
    pose proof (H 0%nat ltac:(cbn; lia)) as E. cbn [Z.of_nat nth_error] in E. exact E.
  - right. rewrite Hb. assert (Hm : (p + i) mod 8 = i) by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma bp_addr_cat : forall m p n k, addressable m p n -> addressable m (p + n) k -> addressable m p (n + k).
Proof.
  intros m p n k (H1 & H2 & H3 & H) (K1 & K2 & K3 & K). split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n) as [Hl|Hg]; [apply H; lia|].
  replace (p + i) with (p + n + (i - n)) by lia. apply K. lia.
Qed.

(* The id record at idp (idp mod 8 = 0): its shadow S(idp) .. S(idp) + 4 = 00 00 00 00 06 (the stores 0x815f8 ..
   0x81608) makes its 38 bytes addressable (32 whole granules + 6). *)
Lemma bp_id_addr : forall m idp, 0 <= idp -> idp mod 8 = 0 -> idp + 38 <= APPMEM_END ->
  (forall i, 0 <= i < 38 -> app_mem (idp + i)) ->
  bytes_at rsegs m (shadow_addr idp) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 6] ->
  addressable m idp 38.
Proof.
  intros m idp H0 H8 He Happ Hb.
  pose proof (bp_ba_sub m _ _ 0 4 Hb ltac:(cbn [length]; lia)) as B4.
  pose proof (bp_ba_sub m _ _ 4 1 Hb ltac:(cbn [length]; lia)) as B1.
  cbn [firstn skipn] in B4, B1. change (Z.of_nat 0) with 0 in B4. change (Z.of_nat 4) with 4 in B1.
  rewrite Z.add_0_r in B4.
  apply (bp_addr_cat m idp 32 6).
  - apply (bp_addr_z m idp 4 32); [reflexivity | lia | exact H8 | lia | intros i Hi; apply Happ; lia | exact B4].
  - apply (bp_addr_r m (idp + 32) 6 (Z_to_bv 8 6)); [lia | Z.div_mod_to_equations; lia | lia | reflexivity | lia
      | intros i Hi; replace (idp + 32 + i) with (idp + (32 + i)) by lia; apply Happ; lia |].
    rewrite bp_sh_add by lia. change (32 / 8) with 4. exact B1.
Qed.

Lemma bp_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

Lemma bp_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma bp_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof. intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))). Qed.

Lemma bp_C1 : forall l, cells_wf (map C1 l) /\ cells_bytes (map C1 l) = l /\ cells_size (map C1 l) = length l.
Proof.
  induction l as [|b l (H1 & H2 & H3)]; cbn [map cells_wf cell_wf cells_bytes cbytes cells_size csize length];
    [split; [exact I | split; reflexivity]|].
  split; [split; [exact I | exact H1]|]. split; [cbn [app]; rewrite H2; reflexivity | rewrite H3; reflexivity].
Qed.

Lemma bp_rw_C1 : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A (map C1 l).
Proof.
  intros m A l Hb Hw. destruct (bp_C1 l) as (H1 & H2 & H3).
  split; [split; [exact H1 | rewrite H2; exact Hb] | rewrite H3; exact Hw].
Qed.

Lemma bp_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* A spilled word read by `ld`: its 8 bytes as one read-only cell. *)
Lemma bp_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma bp_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

Lemma bp_not_out : forall lo1 hi1 lo2 hi2 lo3 hi3 x, ~ outside [(lo1, hi1); (lo2, hi2); (lo3, hi3)] x ->
  lo1 <= x < hi1 \/ lo2 <= x < hi2 \/ lo3 <= x < hi3.
Proof. intros lo1 hi1 lo2 hi2 lo3 hi3 x H. cbn [outside] in H. lia. Qed.

(* The start register map of the run, written with mkR so the engine reads it. *)
Lemma bp_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* The bytes of a readable and writable range as one CB cell (the callee contracts' destination form). *)
Lemma bp_stk_rw : forall m lo hi, stk rsegs m lo hi -> lo <= hi ->
  exists bs, rw_cells rsegs m lo [CB (Z.to_nat (hi - lo)) bs].
Proof.
  intros m lo hi Hs Hle. destruct (stk_bytes rsegs m lo hi Hs ltac:(lia)) as (bs & Hl & Hb).
  exists bs. rewrite <- Hl. apply bp_rw_CB; [exact Hb|].
  rewrite Hl, Z2Nat.id by lia. exact (bp_wr_stk m lo hi Hs).
Qed.

(* The little-endian round trip of a byte list (lib/A/Prog/reac_box_model_block.v bytes_le_to_Z_nonneg',
   bytes_le_to_Z_cons', Z_to_le_bytes_to_Z'). *)
Lemma bp_le_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma bp_le_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bp_le_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  assert (D : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 256) = 0).
  { apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma bp_le_id : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bp_le_cons.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bp_le_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.

(* Eight readable bytes are the little-endian bytes of some word (lib/A/Prog/reac_box_model_block.v rd8_le8). *)
Lemma bp_rd8_le8 : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists b, mrd rsegs m (wa (a + i)) = Some b) -> exists w, bytes_at rsegs m a (le8 w).
Proof.
  intros m a Ha Hl H.
  destruct (H 0 ltac:(lia)) as [b0 E0]. destruct (H 1 ltac:(lia)) as [b1 E1].
  destruct (H 2 ltac:(lia)) as [b2 E2]. destruct (H 3 ltac:(lia)) as [b3 E3].
  destruct (H 4 ltac:(lia)) as [b4 E4]. destruct (H 5 ltac:(lia)) as [b5 E5].
  destruct (H 6 ltac:(lia)) as [b6 E6]. destruct (H 7 ltac:(lia)) as [b7 E7].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (EL : le8 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])) = [b0; b1; b2; b3; b4; b5; b6; b7]).
  { rewrite <- store_bytes_8. cbn [width_bytes]. rewrite MState.unsigned_lit_wrap.
    rewrite Z_to_le_bytes_mod by (cbn; lia).
    exact (bp_le_id [b0; b1; b2; b3; b4; b5; b6; b7]). }
  rewrite EL. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error]; simpl Z.of_nat;
    [rewrite Z.add_0_r in E0; replace (a + Z.of_nat 0) with a by lia; exact E0
    | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | lia].
Qed.

(* ---- The cut-level part: the frame helpers, the normalized memory a run with a mem_inv callee is stepped on,
   the run lemma bp_run, and the FRA / ENT transport bp_fra / bp_post. ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require RcAsanFP asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module FPm := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module ASM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Open Scope Z_scope.

Lemma bp_sh8 : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof. intros fr k. unfold Sfr, shadow_addr. replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma bp_sf8 : forall fr, fr mod 32 = 0 -> 8 * (Sfr fr - ASAN_K) = fr.
Proof. intros fr H. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma bp_m8 : forall fr k, fr mod 32 = 0 -> (fr + 8 * k) mod 8 = 0.
Proof. intros fr k H. Z.div_mod_to_equations. lia. Qed.

(* The shadow byte of the frame byte fr + off + i is Sfr fr + (off + i) / 8, written as the two bounds lia reads
   (adopt 7: RAD's records fr + 2688 and fr + 2768 have their shadow bytes at Sfr fr + 336 .. 340 / 346 .. 354). *)
Lemma bp_sh_in : forall fr off i, fr mod 32 = 0 -> 0 <= off + i ->
  8 * (shadow_addr (fr + off + i) - Sfr fr) <= off + i < 8 * (shadow_addr (fr + off + i) - Sfr fr) + 8.
Proof. intros fr off i Hf Hk. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma bp_fsh : forall fr k, (forall a, fr <= a < fr + 3136 -> app_mem a) -> 0 <= k < 392 -> in_shadow (Sfr fr + k).
Proof. intros fr k Happ Hk. rewrite <- bp_sh8. apply shadow_of_app. apply Happ. lia. Qed.

Lemma bp_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The instrumented globals of the image lie below GT = 0x5fe000, so their shadow bytes are the first 785408 bytes
   of the low shadow. *)
Lemma bp_ag_ok : forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 0x5fe000)) AF.frame_AG = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bp_ag_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < 0x5fe000.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) bp_ag_ok (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma bp_sa_lo : forall a, 0 <= a < 0x5fe000 -> ASAN_K <= shadow_addr a < ASAN_K + 785408.
Proof. intros a Ha. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The spill base named by a spill conjunct is the A of register 9. *)
Lemma bp_spill_A : forall (regs : bvmap 5 word) m off v A A1,
  rg regs 9 A1 -> q64 m (A1 + off) v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off -> A1 = A.
Proof.
  intros regs m off v A A1 H1 Hq H2 HA0 HAe Hoff.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. change (Z.of_nat 8) with 8 in Hq.
  pose proof (rg_eq64 regs 9 A1 A H1 H2) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* Two in-range values held by one register are equal. *)
Lemma bp_rg_inj : forall (regs : bvmap 5 word) (r : bv 5) a b,
  getr regs r = Z_to_bv 64 a -> getr regs r = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb Hra Hrb. rewrite Ha in Hb.
  apply (f_equal (bv_unsigned (n:=64))) in Hb. rewrite !MState.unsigned_lit in Hb by lia. exact Hb.
Qed.

(* ---- the normalized memory: every address at or above GT is read-write in the image ---- *)

Lemma bp_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bp_img_top : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0x5fe000) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma bp_ro_false : forall x : word, 0x5fe000 <= bv_unsigned x -> Lib.Mem.ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold Lib.Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|reflexivity].
  destruct (KindBGlue.kb_find_segment _ _ _ _ E) as (Hin & Hlo & Hhi).
  pose proof (proj1 (forallb_forall _ _) bp_img_top s Hin) as Hs. cbv beta in Hs. apply Z.leb_le in Hs.
  pose proof (N2Z.is_nonneg (seg_size s)). exfalso. lia.
Qed.

Lemma bp_ro_wa : forall a, 0x5fe000 <= a < 2 ^ 64 -> Lib.Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Ha. apply bp_ro_false. rewrite wa_unsigned by lia. lia. Qed.

Lemma bp_shadow_gt : forall a, in_shadow a -> 0x5fe000 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. Qed.

Lemma bp_srw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (bp_shadow_gt a Ha) as Hr. split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (bp_ro_wa a Hr)). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma bp_srw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hw & b & Hb). pose proof (bp_shadow_gt a Ha) as Hr. split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (bp_ro_wa a Hr)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma bp_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (bp_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma bp_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H1 & H2 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (bp_ro_wa a ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma bp_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 HR H. unfold asan_cells in *.
  assert (TB : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs Hb; exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) Hb)).
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply TB; assumption.
Qed.

(* addressable reads only shadow bytes through mrd, which mem_rel keeps (Seg/R4.v r4_addr_rel). *)
Lemma bp_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite <- (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

Lemma bp_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H1 & H2 & H3 & H). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite (mrd_rel rsegs m m0 _ HR). exact Hb.
Qed.

(* The thread cells and the side-stack package across a byte-wise agreeing memory (the MemNorm normalization;
   lib/B/Prog/Seg/R9.v r9_atls_tr / r9_fp_tr of prover a Theorem Labs lane, a working branch 1659ee9abe8). *)
Lemma bp_atls_tr : forall m m0 TP DT TS C T DB k,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  ASM.asan_tls_cells m TP DT TS C T DB k -> ASM.asan_tls_cells m0 TP DT TS C T DB k.
Proof.
  intros m m0 TP DT TS C T DB k TB H. unfold ASM.asan_tls_cells in *.
  destruct H as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
    & T19).
  split; [apply TB; exact T1|]. split; [apply TB; exact T2|]. split; [apply TB; exact T3|].
  split; [apply TB; exact T4|]. split; [apply TB; exact T5|]. split; [exact T6|].
  split; [apply TB; exact T7|]. split; [apply TB; exact T8|]. split; [apply TB; exact T9|].
  split; [apply TB; exact T10|].
  split; [destruct T11 as (tb & te & Hb); exists tb, te; apply TB; exact Hb|].
  split; [apply TB; exact T12|]. split; [apply TB; exact T13|]. split; [apply TB; exact T14|].
  split; [apply TB; exact T15|]. split; [apply TB; exact T16|]. split; [apply TB; exact T17|].
  split; [exact T18 | apply TB; exact T19].
Qed.

Lemma bp_fp_tr : forall cs m m0 TP FS lo hi W D,
  (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  (stk rsegs m FS (FS + ASM.FS_SIZE) -> stk rsegs m0 FS (FS + ASM.FS_SIZE)) ->
  FPm.fp cs m TP FS lo hi W D -> FPm.fp cs m0 TP FS lo hi W D.
Proof.
  intros cs m m0 TP FS lo hi W D TB TS0
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact (bp_atls_tr m m0 TP DT TS C T DB k TB HT)|].
  split; [apply TB; exact HTP|].
  split.
  { unfold ASM.fs_place in *. destruct HP as (P1 & P2 & P3 & P4 & P5).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. exact (TS0 P5). }
  split; [apply TB; exact H88|]. split; [apply TB; exact H96|].
  split.
  { apply Forall_forall. intros c Hc.
    pose proof (proj1 (Forall_forall _ _) HCL c Hc) as (Hcc & h & flags & HH & HF & HFl & HFb).
    split; [exact Hcc|].
    exists h, flags. split; [apply TB; exact HH|]. split; [apply TB; exact HF|].
    split; [exact HFl | exact HFb]. }
  split; [exact HFS|]. split; [exact HA|]. split; [exact HWd | exact HDd].
Qed.

(* ---- the run lemma: an evt on the normalized memory, lifted to SR on the real configuration ---- *)
Section Run.
Context {fx : FPState}.

Lemma bp_run : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> ro_agree rsegs mem ->
  evt rsegs (fun ms => exists R pc' m0', ms = MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs) /\ K R pc' m0')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' m0' regs' m' md', K R pc' m0' -> (forall r, getr regs' r = getr R r) ->
     mem_rel rsegs m' m0' -> ro_same rsegs mem m' -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' m' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh Hro HE HK.
  pose proof (evt_normalize rsegs _ (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs) bp_wx Hro HE)
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

(* ---- PRO (adopt 9 of a working branch, v1.9.0 refit: A4's eleven frame-pointer spills PRA, [A + 152] = fr + 64,
   [A + 264] = fr + 2624, our[]'s six bytes at fr + 2624 addressable and [A + 160] = fr + 32) across a segment:
   every spill of the save area [A, A + 448) is kept (no P1-P11 store and no callee window reaches [A, A + 448))
   and our[]'s shadow byte Sfr fr + 328 is not written. ---- *)
Lemma bp_PRO_keep : forall fr regs regs' m m',
  (forall off v, 0 <= off <= 440 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2624) 6 -> addressable m' (fr + 2624) 6) ->
  PRO fr regs m -> PRO fr regs' m'.
Proof.
  intros fr regs regs' m m' K KA (HPRA & S152 & S264 & HOA & S160).
  split; [|split; [apply K; [lia | exact S152] | split; [apply K; [lia | exact S264] |
    split; [exact (KA HOA) | apply K; [lia | exact S160]]]]].
  destruct HPRA as (P136 & P280 & P168 & P192 & P200 & P216 & P104 & P288 & P296 & P304 & P168b).
  unfold PRA.
  do 10 (split; [apply K; [lia | eassumption]|]). apply K; [lia | eassumption].
Qed.

(* our[]'s six bytes fr + 2624 .. fr + 2629 have the one shadow byte Sfr fr + 328. *)
Lemma bp_our_sh : forall fr i, fr mod 32 = 0 -> 0 <= i < 6 -> shadow_addr (fr + 2624 + i) = Sfr fr + 328.
Proof. intros fr i Hf Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* ---- v1.9.0: the local `first` (fr + 2880, 40 bytes) zeroed by P3's checked_memset is the turn-0 state FSj g fr 0
   (have = 0, n = 0, no body byte; FI holds since the fragment record z72 has byte 6 = 0). ---- *)
Lemma bp_bytes_eq : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
  induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma bp_le4_zero : le4 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 4.
Proof. apply bp_bytes_eq. vm_compute. reflexivity. Qed.

Lemma bp_fsj0 : forall g fr regs m,
  bytes_at rsegs m (fr + 2880) (repeat (Z_to_bv 8 0) 40) -> addressable m (fr + 2880) 40 ->
  FSj g fr 0 regs m.
Proof.
  intros g fr regs m Hb Had.
  unfold FSj, FSb, u32, b8. change (fst_at (g_in g) 0) with fs0. unfold fs0. cbn [fs_have fs_n fs_body].
  pose proof (bp_ba_sub m (fr + 2880) _ 0 4 Hb ltac:(rewrite repeat_length; lia)) as H4.
  pose proof (bp_ba_sub m (fr + 2880) _ 4 1 Hb ltac:(rewrite repeat_length; lia)) as H1.
  pose proof (bp_ba_sub m (fr + 2880) _ 5 0 Hb ltac:(rewrite repeat_length; lia)) as H0.
  cbn [firstn skipn repeat] in H4, H1, H0.
  replace (fr + 2880 + Z.of_nat 0) with (fr + 2880) in H4 by lia.
  replace (fr + 2880 + Z.of_nat 4) with (fr + 2884) in H1 by lia.
  replace (fr + 2880 + Z.of_nat 5) with (fr + 2885) in H0 by lia.
  split; [rewrite bp_le4_zero; exact H4|].
  split; [exact H1|]. split; [exact H0|]. split; [exact Had|].
  unfold FI. change (t_FG (g_in g) 0) with z72. intros H. exfalso. vm_compute in H. discriminate H.
Qed.

Section BP.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* FRA across a run whose write set W avoids the cells FRA reads outside the frame (low image, frame header, the
   spills [A + 40] / [A + 48] / [A + 336], the saved registers) and keeps every shadow byte readable (so
   RT_meta_write), given the new frame-shadow list, the run's heap invariant / stklo, the S-anchored window still
   backed, the frame_AG globals still addressable and the side arm's FakeStack frame record FSREC kept
   (fsrec_keep_app_lo).  W may contain shadow bytes and the callee window. *)
Lemma bp_fra : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = 392%nat) ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) ->
  (forall x, fr <= x < fr + 24 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 40 <= x < bv_unsigned (getr regs 9) + 56 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 336 <= x < bv_unsigned (getr regs 9) + 344 -> LF.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> LF.outside W x) ->
  (forall x, g_S g - AF.SLOT_STACK <= x < g_S g -> LF.outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall x, g_p g <= x < g_p g + g_n g -> LF.outside W x /\ LF.outside W (shadow_addr x)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' HREC' HWinp E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
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
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split; [|exact (HREC' Hrec)]].
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
        * unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (bp_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  exact (fra_in_keep_sh g mem mem' W Hinb Hinblk MU HWinp).
Qed.

(* The 3136 frame bytes are readable and writable (SlotInv.fra_stk): on the real arm they are in the entry-anchored
   window (sp = fr > S - 4096, fr + 3136 <= A <= S), on the side arm a_fs_ok gives them. *)
Lemma bp_frame_stk : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md -> stk rsegs mem fr (fr + 3136).
Proof. intros g fr hb regs mem md HFRA. exact (fra_stk B APIf ra g fr hb regs mem md HFRA). Qed.

(* A readable and writable 8-byte cell of the stack holds some 64-bit value (what a cut that names a spill's
   value existentially asks for). *)
Lemma bp_q64_stk : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 8 <= hi ->
  exists v, 0 <= v < 2 ^ 64 /\ q64 m a v.
Proof.
  intros m a0 hi a (Hl0 & Hl1 & Hv) Ha1 Ha2.
  destruct (bp_rd8_le8 m a ltac:(lia) ltac:(lia)
              ltac:(intros i Hi; exact (proj2 (Hv (a + i) ltac:(lia))))) as (w & Hw).
  exists (bv_unsigned w). split; [apply bv_unsigned_in_range|].
  unfold q64. rewrite MState.Z_to_bv_bv_unsigned. exact Hw.
Qed.

(* n bytes of one registered global are addressable (FRA's frame_AG conjunct, byte by byte). *)
Lemma bp_ag_addr : forall (m : word -> option byte) lo len p n,
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  In (lo, len) AF.frame_AG -> lo <= p -> 0 < n -> p + n <= lo + len -> addressable m p n.
Proof.
  intros m lo len p n HAG Hin Hp Hn Hpn.
  assert (Hb : forall i, 0 <= i < n -> addressable m (p + i) 1).
  { intros i Hi. apply HAG. exists lo, len. split; [exact Hin | lia]. }
  destruct (Hb 0 ltac:(lia)) as (Hp0 & _ & _ & _).
  destruct (Hb (n - 1) ltac:(lia)) as (_ & _ & Hhi & _).
  rewrite Z.add_0_r in Hp0.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Hb i Hi) as (_ & _ & _ & Hbb).
  pose proof (Hbb 0 ltac:(lia)) as Hb0. rewrite Z.add_0_r in Hb0. exact Hb0.
Qed.

(* The decidable split of "not outside W" for a write set covered by the frame shadow, the frame body and a callee
   window: what bp_post reads. *)
Definition bp_cover (fr lo hi : Z) (W : list ivl) : Prop :=
  forall x, ~ LF.outside W x ->
    (Sfr fr <= x < Sfr fr + 392) \/ (fr + 24 <= x < fr + 3136) \/ (lo <= x < hi).

(* FRA and ENT across a run of the segment (bp_fra, ent_store, ent_mat, sl_fra_move): the run writes W, inside the
   frame's 392 shadow bytes, the frame body and the callee window [sp - K, sp) (0 <= K <= FN_STACK); every written
   byte is readable afterwards; the read-only bytes are kept; the FRA registers are kept; and the model only
   materializes lazy pages.  The heap invariant moves by a_laws_store on the real arm (every written byte is
   a_store_ok: the frame and the window are at or above stklo, a frame-shadow byte is the shadow of a frame byte)
   and by a_fs_ok_store_AH on the side arm (the frame and its shadow are the FakeStack's, its metadata is below the
   frame and the window above it). *)
Lemma bp_post : forall g fr regs regs' mem mem' md md' W K,
  FRA B APIf ra g fr [] regs mem md -> ENT APIf g [] mem md -> 0 <= K <= FN_STACK ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> ro_same rsegs mem mem' -> rt_disjoint W ->
  bp_cover fr (AC.aspZ regs - K) (AC.aspZ regs) W ->
  (forall x, ~ LF.outside W x -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr [] regs' mem' md' /\ ENT APIf g [] mem' md'.
Proof.
  intros g fr regs regs' mem mem' md md' W K HFRA HENT HK MU WM Hsame HDJ HWc RDW E2 E3 E4 E8 E9 E19 E26 Hmat.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof (Hplace K HK) as Hsep.
  unfold bp_cover in HWc.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  rewrite Haspz in Hlo, Hstkw, Hsep, HWc.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  (* the frame is application memory above the image *)
  assert (Happ : forall a, fr <= a < fr + 3136 -> app_mem a /\ AC.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, AC.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo2 & Hhi2).
      destruct (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FSb HAH Hw HFSr) as [HGT _ _ HFapp].
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + 3136 -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (HLH : fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + 3135) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (Hfre : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + 3135) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HGT : AC.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  pose proof (bp_sf8 fr Hfrm) as HSf8.
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HSfrD : Sfr fr + 392 <= fr \/ fr + 3136 <= Sfr fr) by lia.
  assert (HShm : Sfr fr + 392 <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 + 785408 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  assert (HAhi : Sfr fr + 392 <= A) by lia.
  (* a written byte is in the frame shadow, the frame body or the callee window *)
  assert (HWx : forall x, ~ LF.outside W x ->
            (Sfr fr <= x < Sfr fr + 392) \/ (fr + 24 <= x < fr + 3136) \/ (sp - K <= x < sp)) by exact HWc.
  assert (HOUT : forall x, ((Sfr fr <= x < Sfr fr + 392) -> False) -> ((fr + 24 <= x < fr + 3136) -> False) ->
            ((sp - K <= x < sp) -> False) -> LF.outside W x).
  { intros x H1 H2 H3. destruct (bp_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. destruct (HWx x Hno) as [Hx|[Hx|Hx]]; auto. }
  (* the shadow after the run, and ro_agree *)
  assert (SW' : shadow_rw mem').
  { apply (bp_shadow_rw W mem mem' (AsanRTInv.RT_shadow_rw _ _ _ HRT) MU WM). intros a Ha.
    destruct (bp_out_dec W a) as [Ho|Hno]; [left; exact Ho | right; exact (RDW a Hno)]. }
  pose proof (ro_agree_same rsegs mem mem' Hro Hsame) as HRO'.
  (* the heap invariant and stklo after the run, by arm *)
  assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
    by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
  assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
                 (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
                            AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
                 AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                 AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5fr [Hfsb [Hfs _]]]].
    - (* real arm: every written byte is a_store_ok *)
      assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
      { intros x Hx Hnok.
        destruct (bp_out_dec W x) as [Ho|Hno].
        - apply MU. rewrite MState.unsigned_lit by exact Hx. exact Ho.
        - exfalso. apply Hnok. destruct (HWx x Hno) as [Hx1|[Hx1|Hx1]].
          + right; right; right. exists (fr + 8 * (x - Sfr fr)). split; [rewrite bp_sh8; lia|].
            right; left. apply Hreal. lia.
          + right; left. apply Hreal. lia.
          + right; left. lia. }
      destruct (lw_store (APIf rc) ([] ++ g_H g) mem mem' md HAH Hmc Hwrit) as [HAH' Hown' Hstk' Hhi'].
      split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hhi'].
    - (* side arm: the frame and its shadow are the FakeStack's *)
      destruct (Hfs (fr + 3135) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
      pose proof (Hfsb FS HwFS HFSr) as HFSfr.
      destruct (lw_fs_place (APIf rc) ([] ++ g_H g) mem md FS HAH HwFS HFSr) as [HGTFS HFSend _ HFSapp].
      assert (HFS64 : FS + AC.FS_SIZE <= 2 ^ 64).
      { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as H.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
      assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                exists b, mbyte rsegs mem' q = Some b).
      { intros q Hq (b & Hb).
        destruct (bp_out_dec W q) as [Ho|Hno].
        - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
          rewrite MState.unsigned_lit by exact Hq. exact Ho.
        - exact (RDW q Hno). }
      assert (Hmeta : forall q, fs_meta FS q -> LF.outside W q).
      { intros q Hq. pose proof (bp_fs_meta_range FS q Hq) as Hqr.
        assert (Hqa : app_mem q) by (apply HFSapp; lia).
        apply HOUT; intros Hin; [|lia|lia].
        apply (app_not_shadow q Hqa).
        replace q with (Sfr fr + (q - Sfr fr)) by lia. apply bp_fsh; [exact Happ' | lia]. }
      assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                ~ (FS <= q < FS + AC.FS_SIZE) ->
                ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hnok Hnfs Hnsh.
        destruct (bp_out_dec W q) as [Ho|Hno].
        - apply MU. rewrite MState.unsigned_lit by exact Hq. exact Ho.
        - exfalso. destruct (HWx q Hno) as [Hx1|[Hx1|Hx1]].
          + apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia | rewrite bp_sh8; lia].
          + apply Hnfs. lia.
          + apply Hnok. right; left. lia. }
      destruct (a_fs_ok_store_AH _ _ _ _ _ W ([] ++ g_H g) mem mem' md FS ALAWS HAH HwFS HFSr HFS64 MU Hwrit
                  Hpres Hmeta Hagree)
        as (HAH' & Hown' & Hstk' & Hhi').
      split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hhi']. }
  destruct HAHS as (HAH' & HOWN' & HSTK' & HHI').
  (* FRA at mem' *)
  assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = 392%nat).
  { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + 392)).
    { split; [lia|]. split; [lia|]. intros a Ha. apply SW'.
      replace a with (Sfr fr + (a - Sfr fr)) by lia. apply bp_fsh; [exact Happ' | lia]. }
    destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
    exists bs. split; [exact Hb|]. rewrite Hl. replace (Sfr fr + 392 - Sfr fr) with 392 by lia. reflexivity. }
  assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
  { intros a Ha. pose proof (bp_sa_lo a (bp_ag_lo a Ha)) as Hsa. unfold ASAN_K in Hsa.
    apply (bp_addr_keep W mem mem' a 1 (HAG a Ha) MU). intros i Hi.
    replace (a + i) with a by lia. apply HOUT; intros Hin; lia. }
  (* the slot window outside the frame is still addressable: a window byte's shadow byte is not written *)
  assert (HWA' : forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + 3136) ->
            addressable mem' a 1).
  { intros a Ha1 Ha2.
    assert (Hsa : 2147450880 <= shadow_addr a < 17592186044416 + 2147450880).
    { unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
    assert (Hsf : shadow_addr a < Sfr fr \/ Sfr fr + 392 <= shadow_addr a).
    { unfold Sfr, shadow_addr. revert Ha2 Hfrm. clear. intros H1 H2. Z.div_mod_to_equations. lia. }
    apply (bp_addr_keep W mem mem' a 1 (HWA a Ha1 Ha2) MU). intros i Hi.
    replace (a + i) with a by lia. apply HOUT; intros Hin; lia. }
  (* ENT across the run and the model step *)
  assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
            LF.outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/
            (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
  { intros x Hx.
    destruct (bp_out_dec W x) as [Ho|Hno]; [left; exact Ho|].
    destruct (HWx x Hno) as [Hx1|[Hx1|Hx1]].
    - right; right; right. lia.
    - right; right; left. lia.
    - right; left. lia. }
  assert (HOWNk : forall a, AC.a_in_img a ->
            AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a ->
            AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a)
    by (intros a _ Ho; exact (proj2 (HOWN' a) Ho)).
  assert (HENT' : ENT APIf g [] mem' md).
  { eapply ent_store with (W := W);
      try exact FF; try exact HENT; try exact HFRA; try exact MU; try exact HWcases;
      try exact HSTK'; try exact HHI'; try exact HOWNk. }
  (* the side arm's FakeStack frame record: the run writes no app byte below stklo off the frame *)
  assert (HREC' : FSREC fr mem -> FSREC fr mem').
  { intros Hrec. eapply fsrec_keep_app_lo; [exact Hrec | exact HAH | exact (proj1 (fr_munch_ul _ _ _) MU) |].
    intros x Hxa Hxlo Hxf. apply (proj2 (fr_outside_lib _ _)).
    apply HOUT; intros Hin; [|lia|lia].
    apply (app_not_shadow x Hxa).
    replace x with (Sfr fr + (x - Sfr fr)) by lia. apply bp_fsh; [exact Happ' | lia]. }
  (* the input block: app memory below stklo, off the frame (fra_in_apart); so it and its shadow miss W *)
  assert (HWinp : forall x, g_p g <= x < g_p g + g_n g -> LF.outside W x /\ LF.outside W (shadow_addr x)).
  { intros x Hx. destruct (fra_in_apart B APIf ra g fr [] regs mem md HFRA x Hx) as (Hxa & Hxlo & Hxf & _).
    assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
    pose proof (shadow_of_app x Hxa) as Hsx.
    split.
    - apply HOUT; [|lia|lia].
      intros Hin. apply (app_not_shadow x Hxa).
      replace x with (Sfr fr + (x - Sfr fr)) by lia. apply bp_fsh; [exact Happ' | lia].
    - apply HOUT.
      + intros Hin. apply Hxf. unfold Sfr, shadow_addr in Hin.
        clear - Hin Hfrm Hx0 Hfre HFBv. Z.div_mod_to_equations. lia.
      + intros Hin. assert (Happs : app_mem (shadow_addr x)) by (apply Happ'; lia).
        exact (app_not_shadow (shadow_addr x) Happs Hsx).
      + intros Hin. apply (app_not_shadow (shadow_addr x)); [|exact Hsx].
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. lia. }
  assert (HFRAm : FRA B APIf ra g fr [] regs' mem' md).
  { apply (bp_fra g fr [] regs regs' mem mem' md W
             HFRA MU WM HRO' HDJ HAH' HSTK' (fun a Ha => proj2 (SW' a Ha)) Hshnew);
      try assumption.
    - intros x Hx. apply HOUT; intros Hin; lia.
    - intros x Hx. apply HOUT; intros Hin; lia.
    - intros x Hx. rewrite HbvA in Hx. apply HOUT; intros Hin; lia.
    - intros x Hx. rewrite HbvA in Hx. apply HOUT; intros Hin; lia.
    - intros x Hx. apply HOUT; intros Hin; lia.
    - intros x Hx.
      destruct (bp_out_dec W x) as [Ho|Hno]; [left; exact Ho | right; exact (RDW x Hno)]. }
  split.
  - apply (sl_fra_move B APIf ra g fr [] regs' regs' mem' md md' HFRAm); try reflexivity. exact Hmat.
  - eapply ent_mat; [exact HENT' | exact Hmat].
Qed.

End BP.
