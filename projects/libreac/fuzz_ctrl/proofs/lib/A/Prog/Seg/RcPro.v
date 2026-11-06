(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths, module names, addresses and numbers changed; 462 of its 587 lines of code are new or changed and 1077 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R2.v, with its module names changed; 194 of its 230 lines of code are new or changed and 551 lines of the source are left out. *)
(* PRO (push 13B, SlotInv.v) across a run of the round-trip chain (image A, fuzz_ctrl entry function).
   rule 24: no function proved (helpers for the segment lemmas R1 .. R6 / R11 .. R13).
   PRO is thirteen spills in [A + 32, A + 280) (v1.9 appended [A + 32] = fr + 2880), our[]'s 6 bytes addressable
   (shadow S(fr) + 328) and the input pair (the input bytes at p and, when n > 0, the live block (p, n) of the entry
   heap, addressable). A run keeps it when its write set W misses the spill cells and our[]'s shadow byte, and W holds only bytes the input block can
   not share a byte or a shadow granule with:
   - bytes at or above stklo (callee windows, the save area, the frame body on the real arm): a live block ends at
     or below stklo (a_laws_blocks);
   - side-stack bytes (a_in_fs: the frame body on the side arm, the class-k frames a callee takes): a live block
     byte is not a_in_fs;
   - shadow bytes of such bytes, the stklo ones 8-aligned (the frame shadow, a callee window's shadow): the block's
     shadow granules are below stklo / 8, and the side stack is 4096-aligned with an 8-multiple size
     (a_laws_fs_place), so no granule is shared. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module ACp := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module LFp := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module AFp := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

Lemma rc_out_dec : forall W x, LFp.outside W x \/ ~ LFp.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [LFp.outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

(* An addressable range stays addressable when the run misses its shadow bytes. *)
Lemma rc_addr_keep : forall W m m' p n, addressable m p n -> LFp.munch W m m' ->
  (forall i, 0 <= i < n -> LFp.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

(* A spill cell [A + off] read through the spill base held in s1. *)
Lemma rc_spill_A : forall regs m A off v, rg regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v Hr HA0 Hoff HA1 (A0 & HA & Hq).
  assert (E : A0 = A).
  { pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
    pose proof (rg_eq64 regs 9 A0 A HA Hr) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
    Z.div_mod_to_equations. lia. }
  subst A0. exact Hq.
Qed.

(* A spill the run misses, read through a kept s1. *)
Lemma rc_spill_keep : forall W regs regs' m m' A off v,
  rg regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  LFp.munch W m m' -> (forall x, A + off <= x < A + off + 8 -> LFp.outside W x) ->
  spill regs m off v -> spill regs' m' off v.
Proof.
  intros W regs regs' m m' A off v Hr HA0 Hoff HA1 E9 MU HO Hs.
  pose proof (rc_spill_A regs m A off v Hr HA0 Hoff HA1 Hs) as Hq.
  exists A. split; [unfold rg in *; rewrite E9; exact Hr|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8. exact HO.
Qed.

Section RcPro.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACp.AsanAllocAPI ACp.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.

(* The bytes a run may write without touching the input block: at or above stklo, on the side stack, or the shadow
   of such a byte (8-aligned when it is at or above stklo). *)
Definition rc_away (mem : word -> option byte) (md : Model) (x : Z) : Prop :=
  ACp.aa_stklo ACp.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/ ACp.a_in_fs ACp.ASYMS mem x \/
  (exists y, app_mem y /\ x = shadow_addr y /\
     ((ACp.aa_stklo ACp.ASYMS AsanRTInv.RT (APIf rc) mem md <= y /\ y mod 8 = 0) \/ ACp.a_in_fs ACp.ASYMS mem y)).

(* The input pair of PRO (and of f1_IN) across a run whose write set is rc_away. *)
Lemma rc_in_keep : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  LFp.munch W mem mem' ->
  (forall x, ~ LFp.outside W x -> rc_away mem md x) ->
  bytes_at rsegs mem (g_p g) (g_in g) /\ (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem (g_p g) (g_n g)) ->
  bytes_at rsegs mem' (g_p g) (g_in g) /\ (0 < g_n g -> In (g_p g, g_n g) (g_H g) /\ addressable mem' (g_p g) (g_n g)).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem mem' md W HFRA MU HW (Hin & Hlive).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & _).
  pose proof (ACp.aa_laws ACp.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (ACp.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hhigh.
  set (lo := ACp.aa_stklo ACp.ASYMS AsanRTInv.RT (APIf rc) mem md) in *.
  assert (Hlen : g_n g = Z.of_nat (length (g_in g))) by reflexivity.
  (* the facts a_laws_blocks gives about the block, when n > 0 *)
  assert (Hblk : 0 < g_n g -> g_p g + g_n g <= lo /\
            forall a, g_p g <= a < g_p g + g_n g -> app_mem a /\ ~ ACp.a_in_fs ACp.ASYMS mem a).
  { intros Hn. destruct (Hlive Hn) as (HH & _).
    destruct (ACp.a_laws_blocks _ _ _ _ _ LAWS (hb ++ g_H g) mem md (g_p g) (g_n g) HAH
                (in_or_app _ _ _ (or_intror HH))) as (_ & _ & Hend & _ & Hall).
    split; [exact Hend|]. intros a Ha. destruct (Hall a Ha) as (Happ & _ & _ & _ & Hnfs). split; assumption. }
  (* a side-stack byte is application memory, on a 4096-aligned side stack *)
  assert (Hfs : forall y, ACp.a_in_fs ACp.ASYMS mem y ->
            exists FS, FS mod 4096 = 0 /\ FS <= y < FS + ACp.FS_SIZE /\
              (forall a, FS <= a < FS + ACp.FS_SIZE -> app_mem a) /\
              (forall a, FS <= a < FS + ACp.FS_SIZE -> ACp.a_in_fs ACp.ASYMS mem a)).
  { intros y (FS & HFSr & HwFS & Hy).
    destruct (ACp.a_laws_fs_place _ _ _ _ _ LAWS (hb ++ g_H g) mem md FS HAH HwFS HFSr) as (_ & _ & Hal & Happ).
    exists FS. split; [exact Hal|]. split; [exact Hy|]. split; [exact Happ|].
    intros a Ha. exists FS. split; [exact HFSr|]. split; [exact HwFS | exact Ha]. }
  assert (HFSz : ACp.FS_SIZE = 11571200) by reflexivity.
  split.
  - eapply fl_bytes; [exact Hin | exact MU |]. intros x Hx. rewrite <- Hlen in Hx.
    destruct (rc_out_dec W x) as [Ho|Hno]; [exact Ho|]. exfalso.
    assert (Hn : 0 < g_n g) by lia. destruct (Hblk Hn) as (Hend & Hall). destruct (Hall x Hx) as (Happ & Hnfs).
    destruct (HW x Hno) as [Hlo | [Hf | (y & Hy & -> & _)]].
    + lia.
    + exact (Hnfs Hf).
    + exact (app_not_shadow _ Happ (shadow_of_app _ Hy)).
  - intros Hn. destruct (Hlive Hn) as (HH & HAD). split; [exact HH|].
    apply (rc_addr_keep W mem mem' (g_p g) (g_n g) HAD MU). intros i Hi.
    destruct (Hblk Hn) as (Hend & Hall). destruct (Hall (g_p g + i) ltac:(lia)) as (Happ & Hnfs).
    pose proof (shadow_of_app _ Happ) as Hsh.
    destruct (rc_out_dec W (shadow_addr (g_p g + i))) as [Ho|Hno]; [exact Ho|]. exfalso.
    destruct (HW _ Hno) as [Hlo | [Hf | (y & Hy & Ey & Hyc)]].
    + unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh, Hhigh. lia.
    + destruct (Hfs _ Hf) as (FS & _ & HyFS & HappFS & _).
      exact (app_not_shadow _ (HappFS _ HyFS) Hsh).
    + unfold shadow_addr in Ey.
      destruct Hyc as [(Hly & Hy8) | Hf].
      * assert (g_p g + i < y) by lia. Z.div_mod_to_equations. lia.
      * destruct (Hfs _ Hf) as (FS & HFS4 & HyFS & _ & HinFS).
        assert (Hout : ~ (FS <= g_p g + i < FS + ACp.FS_SIZE)) by (intros Hc; exact (Hnfs (HinFS _ Hc))).
        rewrite HFSz in *. Z.div_mod_to_equations. lia.
Qed.

(* PRO across a run: its thirteen spills (push 14D added 184 / 256 / 264 / 272, v1.9 appended [A + 32]) and our[]'s
   shadow byte missed, the rest of W rc_away, s1 kept. *)
Lemma rc_pro_keep : forall g fr hb regs regs' mem mem' md W A,
  FRA B APIf ra g fr hb regs mem md ->
  PRO g fr regs mem ->
  LFp.munch W mem mem' ->
  rg regs 9 A -> 0 <= A -> A + 280 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  (forall x, (A + 32 <= x < A + 48 \/ A + 120 <= x < A + 128 \/ A + 136 <= x < A + 144 \/
              A + 160 <= x < A + 192 \/ A + 208 <= x < A + 216 \/ A + 248 <= x < A + 280) -> LFp.outside W x) ->
  (forall i, 0 <= i < 6 -> LFp.outside W (shadow_addr (fr + 2624 + i))) ->
  (forall x, ~ LFp.outside W x -> rc_away mem md x) ->
  PRO g fr regs' mem'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs regs' mem mem' md W A HFRA HP MU Hr9 HA0 HA1 E9 HSP HOUR HW.
  destruct HP as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pour & Pin & Plive &
                  P184 & P256 & P264 & P272 & P32).
  unfold PRO.
  split; [apply (rc_spill_keep W regs regs' mem mem' A 40 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P40];
          intros x Hx; apply HSP; lia|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 120 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P120];
          intros x Hx; apply HSP; lia|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 136 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P136];
          intros x Hx; apply HSP; lia|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 160 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P160];
          intros x Hx; apply HSP; lia|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 168 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P168];
          intros x Hx; apply HSP; lia|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 176 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P176];
          intros x Hx; apply HSP; lia|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 208 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P208];
          intros x Hx; apply HSP; lia|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 248 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P248];
          intros x Hx; apply HSP; lia|].
  split; [exact (rc_addr_keep W mem mem' (fr + 2624) 6 Pour MU HOUR)|].
  destruct (rc_in_keep g fr hb regs mem mem' md W HFRA MU HW (conj Pin Plive)) as (Pin' & Plive').
  split; [exact Pin'|]. split; [exact Plive'|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 184 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P184];
          intros x Hx; apply HSP; lia|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 256 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P256];
          intros x Hx; apply HSP; lia|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 264 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P264];
          intros x Hx; apply HSP; lia|].
  split; [apply (rc_spill_keep W regs regs' mem mem' A 272 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P272];
          intros x Hx; apply HSP; lia|].
  apply (rc_spill_keep W regs regs' mem mem' A 32 _ Hr9 HA0 ltac:(lia) ltac:(lia) E9 MU); [|exact P32].
  intros x Hx; apply HSP; lia.
Qed.

(* PRO across a step that keeps s1 and memory (rn_pro_regs of Seg/RNIng.v). *)
Lemma rc_pro_regs : forall g fr (regs regs' : bvmap 5 word) m,
  getr regs' 9 = getr regs 9 -> PRO g fr regs m -> PRO g fr regs' m.
Proof.
  intros g fr regs regs' m E9 HP. unfold PRO in *.
  assert (K : forall off v, spill regs m off v -> spill regs' m off v).
  { intros off v (A0 & HA0 & HQ). exists A0. split; [unfold rg in *; rewrite E9; exact HA0 | exact HQ]. }
  destruct HP as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pour & Pin & Plive &
                  P184 & P256 & P264 & P272 & P32).
  repeat (split; [first [apply K; eassumption | eassumption]|]). apply K; eassumption.
Qed.

(* The usual parts of a write set are rc_away: the frame body, the frame shadow, anything at or above the slot
   window's base S - SLOT_STACK (callee windows, the save area), and the shadow of an 8-aligned range there. *)
Lemma rc_away_frame : forall g fr hb regs mem md x,
  FRA B APIf ra g fr hb regs mem md -> fr <= x < fr + FRAME_BYTES -> rc_away mem md x.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md x HFRA Hx.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  unfold rc_away. destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
  - left. exact (proj1 (Hreal x Hx)).
  - right; left. exact (Hfs x Hx).
Qed.

Lemma rc_away_fsh : forall g fr hb regs mem md x,
  FRA B APIf ra g fr hb regs mem md -> Sfr fr <= x < Sfr fr + FRAME_SHADOW -> rc_away mem md x.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md x HFRA Hx.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  pose proof (ACp.aa_laws ACp.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (ACp.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hhigh.
  set (y := fr + 8 * (x - Sfr fr)).
  assert (Hy : fr <= y < fr + FRAME_BYTES) by (unfold y; lia).
  assert (Ey : x = shadow_addr y) by (unfold y, Sfr, shadow_addr in *; Z.div_mod_to_equations; lia).
  unfold rc_away. right; right. exists y. split; [|split; [exact Ey|]].
  - destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
    + pose proof (Hreal y Hy) as Hr. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. lia.
    + destruct (Hfs y Hy) as (FS & HFSr & HwFS & HyFS).
      destruct (ACp.a_laws_fs_place _ _ _ _ _ LAWS (hb ++ g_H g) mem md FS HAH HwFS HFSr) as (_ & _ & _ & Happ).
      exact (Happ y HyFS).
  - destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
    + left. split; [exact (proj1 (Hreal y Hy)) | unfold y; Z.div_mod_to_equations; lia].
    + right. exact (Hfs y Hy).
Qed.

Lemma rc_away_hi : forall g fr hb regs mem md x,
  FRA B APIf ra g fr hb regs mem md -> g_S g - AFp.SLOT_STACK <= x -> rc_away mem md x.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md x HFRA Hx.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & _).
  unfold rc_away. left. lia.
Qed.

Lemma rc_away_hish : forall g fr hb regs mem md lo hi x,
  FRA B APIf ra g fr hb regs mem md -> g_S g - AFp.SLOT_STACK <= lo -> lo mod 8 = 0 -> hi <= APPMEM_END ->
  shadow_addr lo <= x < shadow_addr hi -> rc_away mem md x.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem md lo hi x HFRA Hlo Hal Hhi Hx.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo & _).
  pose proof (ACp.aa_laws ACp.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (ACp.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AFp.SLOT_STACK = 1048576) by reflexivity.
  set (y := 8 * (x - ASAN_K)).
  unfold rc_away. right; right. exists y.
  unfold shadow_addr, y, app_mem, HIGHMEM_BEG, APPMEM_END, ASAN_K in *.
  Z.div_mod_to_equations. split; [lia|]. split; [lia|]. left. split; lia.
Qed.

End RcPro.
