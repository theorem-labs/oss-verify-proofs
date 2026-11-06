(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F4.v, with its addresses changed; 1141 of its 1278 lines of code are new or changed and 3098 lines of the source are left out. *)
(* Segment P12 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, libreac v1.9.0 image A): 0x81c84-0x81d3c, 47 instructions
   (v1.8 0x81bf8-0x81ca4, 44), the end of the init region and the entry of the frame loop.  rule 24: no function
   proved (a slot segment).  S_P12 is CHANGED (v190-segment-table.md section 5a); the v1.9 walk:
     81c84-81cb8  the instrumented check of the "?" string a0 = QMARK (both arms reach 81c94 / 81cb4; the error
                  calls at 82c04 / 82c10 are not reached), then lbu a1,0(a0); li a2,63; bne (not taken) and the
                  NUL check at 81cb4 (v1.8 81bf8-81c2c, EQUAL).
     81cbc-81cdc  li s11,-8 and the eight frame-shadow stores sb s11,K(s3), K in {382,383,384,385,370,372,376,380}
                  (v1.8 {372..375,360,362,366,370}: every K + 10, same order; 81cc0 .. 81cd0 are NEW-only by the
                  alignment), inside [S(fr) + 370, S(fr) + 386): FRA moves across them with Tac_slot's
                  sl_fr_meta.
     81ce0        beqz s9,82b04: s9 = n - c0 = t_left 0. Zero exits to Inv_A82b04 (v1.8 81c54 -> 82a58).
     81ce4-81d3c  li s5,0 (j = 0) and the twelve spill stores / four spill loads: stores inside [s1 + 48, s1 + 120)
                  and [s1 + 128, s1 + 136) (as in v1.8), loads [s1 + 192] = fragb fr, [s1 + 248] = fr + 176,
                  [s1 + 208] = fr + 448 and the NEW-only [s1 + 32] = fr + 2880 (PRO's position 16, A4's 0x813cc).
                  [s1 + 128] = [s1 + 208] + 4 = fr + 452 (FLSH's spill 128). FRA moves across the spill writes with
                  Tac_slot's sl_fr_cl; ENT with ent_store; the first-fragment zeros [s1+112] = n (NEW-only 81ce8)
                  and [s1+104] = have are FSj's two spills at turn 0 (fstate v1.9: have, n, body; v1.8 also zeroed
                  [s1+88] / [s1+96], which v1.9 drops).
   v1.8 -> v1.9 slots (section 7a): [A+208] fragb -> [A+192], [A+200] fr+448 -> [A+208], [A+80/72/64] fragb + 8 /
   19 / 15 -> [A+96/88/80], [A+56/48] fr + 186 / 180 -> [A+72/64]; NEW-only [A+56] / [A+48] = fr + 2889 / fr + 2890
   (81d2c-81d3c, FLC's positions 13 / 14).
   Entry cut (official): Inv_A81c84, whose PRO bundle carries the A4 prologue spills [A+40]=fr+32, [A+120]=fr+160,
   [A+136]=fr+128, [A+160]=fr+528, [A+168]=fr+2624, [A+176]=fr+64, [A+208]=fr+448, [A+248]=fr+176, [A+184]=fr+336,
   [A+256]=fr+256, [A+264]=fr+304, [A+272]=fr+272, [A+32]=fr+2880, out[] addressable (fr+2624, 6) and the guarded
   input pair; [A+192] = fragb fr and the record ranges (fragb fr, 72) / (fr+2688, 38). P12 writes none of them, so
   PRO moves to the loop head inside FLSH; the frame body stk fr (fr + FRAME_BYTES) is SlotInv's fra_stk, and the
   loop head's f1_IN is f1_IN_of_PRO on the arm where 0x81ce0 `beqz s9` is not taken (0 < n - c0 <= n). P12
   PRODUCES FLC at the loop head: the carried spills and ranges, plus its own stores [A+96] / [A+88] / [A+80] =
   fragb fr + 8 / 19 / 15 (from [A+192]), [A+72] / [A+64] = fr + 186 / fr + 180 (from [A+248] = fr + 176) and
   [A+56] / [A+48] = fr + 2889 / fr + 2890 (from [A+32] = fr + 2880).
   Exit cuts (official): Inv_A81d40_at g 0 (the frame-loop head at turn j = 0) and Inv_A82b04.
   The generic helpers this file used from P7 are copies here, so that P12 does not import P7 / P11 (another lane
   re-fits P7; P11 calls a callee): p12_run = P7's p7_run, p12_rg_inj = p7_rg_inj, p12_ro_keep = p7_ro_keep (with
   p12_tops / p12_rsegs_below_gt / p12_find_below / p12_ro_addr_hi = its helpers), p12_ba_sub = p7_ba_sub,
   p12_fra_A = fra_A, p12_fr_place = fr_place. Fold them back into P7's names once P7 builds on v1.9.
   v1.9 re-fit BUILT on v1.9 facts: rc=0 on a build machine workspace (internal path) (a copy of (internal path) at a working branch e3c0b7a9d6,
   FACTS ed6b6b7b0ab) with the cut base a working branch cf5ad0d7203, 2026-10-28. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---- copies of P7's generic helpers (Seg/P7.v p7_ba_sub, p7_rg_inj, p7_ro_keep with its ro_addr_hi /
   find_segment_below / rsegs_below_gt, p7_run; fra_A and fr_place are below, in Section S), word for word but
   for the names and FRAME_BYTES, so that P12 does not import P7; fold them back once P7 builds on v1.9. ---- *)

Lemma p12_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma p12_rg_inj : forall regs r A A', rg regs r A -> rg regs r A' -> 0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A = A'.
Proof.
  intros regs r A A' H H' HA HA'. unfold rg in *. rewrite H in H'.
  apply (f_equal (bv_unsigned (n:=64))) in H'. rewrite !MState.unsigned_lit in H' by lia. exact H'.
Qed.

Definition p12_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma p12_rsegs_below_gt : p12_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma p12_find_below : forall segs top x n s,
  p12_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold p12_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma p12_ro_addr_hi : forall a, 0x5fe000 <= a < 2 ^ 64 ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (p12_find_below sg 0x5fe000 x n s p12_rsegs_below_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma p12_ro_keep : forall W mem mem', ro_agree rsegs mem -> munch W mem mem' ->
  (forall x, 0 <= x < 0x5fe000 -> outside W x) -> ro_agree rsegs mem'.
Proof.
  intros W mem mem' Hro MU HW. apply (ro_agree_same rsegs mem mem' Hro). intros a Ha. apply MU.
  pose proof (u64_range a) as Hu.
  destruct (Z_lt_le_dec (bv_unsigned a) 0x5fe000) as [Hlt|Hge]; [apply HW; lia|].
  exfalso. pose proof (p12_ro_addr_hi (bv_unsigned a) ltac:(lia)) as Hf.
  unfold wa in Hf. rewrite Z_to_bv_bv_unsigned in Hf. rewrite Hf in Ha. discriminate.
Qed.

Section R.
Context {fx : FPState}.

(* Lib-evt -> SR bridge (P7's p7_run). *)
Lemma p12_run : forall regs pc mem md
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
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

End R.

(* ---- small byte / cell helpers ---- *)

Lemma p12_zxb63 : zxb (Z_to_bv 8 63) = Z_to_bv 64 63.
Proof. reflexivity. Qed.

Lemma p12_zxb0 : zxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Lemma p12_beq : forall (b : byte) c, 0 <= c < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. unfold bv_eqb, zxb.
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  rewrite !MState.unsigned_lit by lia. reflexivity.
Qed.

Lemma p12_le8_eq : forall u v : word, bv_unsigned u = bv_unsigned v -> le8 u = le8 v.
Proof. intros u v H. rewrite <- !store_bytes_8'. rewrite H. reflexivity. Qed.

(* The byte the frame-shadow stores write (the low byte of -8), in the shape cell_of_bytes needs. *)
Lemma p12_le1_m8 : le1 (Z_to_bv 64 (-8)) = [Z_to_bv 8 248].
Proof.
  unfold le1. cbn [Z_to_le_bytes]. f_equal; try reflexivity.
  apply Z_to_bv8_mod. vm_compute. reflexivity.
Qed.

#[local] Ltac mem_after_store_opt ::=
  try rewrite p12_le1_m8;
  try fix_lit_store;
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

(* A single readable byte is a one-byte read. *)
Lemma p12_rd1 : forall m a b, 0 <= a -> a + 1 <= 2 ^ 64 -> mrd rsegs m (wa a) = Some b ->
  ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b Ha Hb H.
  assert (HB : bytes_at rsegs m a [b]).
  { split; [exact Ha|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
    cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact H. }
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 HB ltac:(cbn [length]; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH. cbn [firstn] in HH. exact HH.
Qed.

(* The bytes of a cell block, and of one of its cells. *)
Lemma p12_cells_bytes : forall m A cs, rw_cells rsegs m A cs ->
  bytes_at rsegs m A (cells_bytes cs) /\ length (cells_bytes cs) = cells_size cs.
Proof.
  intros m A cs [[Hwf Hb] _]. split; [exact Hb | exact (cells_bytes_length cs Hwf)].
Qed.

Lemma p12_cell_at_bytes : forall m A cs k c, rw_cells rsegs m A cs -> cell_at cs k = Some c ->
  bytes_at rsegs m (A + Z.of_nat k) (cbytes c).
Proof.
  intros m A cs k c [[Hwf Hb] _] Hk.
  destruct (cell_at_split cs k c c Hk) as (pre & post & -> & Hsz & _).
  rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
  apply cells_wf_app in Hwf. destruct Hwf as (Hwf1 & Hwf2). cbn [cells_wf] in Hwf2.
  apply (proj1 (bytes_at_app rsegs m A _ _)) in Hb. destruct Hb as (_ & Hb2).
  rewrite (cells_bytes_length pre Hwf1), Hsz in Hb2.
  apply (proj1 (bytes_at_app rsegs m (A + Z.of_nat k) _ _)) in Hb2. exact (proj1 Hb2).
Qed.

Lemma p12_cell_q64 : forall m A cs (k : nat) (w : word) (v : Z),
  rw_cells rsegs m A cs -> cell_at cs k = Some (C8 w) -> bv_unsigned w = bv_unsigned (Z_to_bv 64 v) ->
  q64 m (A + Z.of_nat k) v.
Proof.
  intros m A cs k w v HC Hk Hw.
  pose proof (p12_cell_at_bytes m A cs k (C8 w) HC Hk) as HB.
  cbn [cbytes] in HB. unfold q64. rewrite <- (p12_le8_eq w (Z_to_bv 64 v) Hw). exact HB.
Qed.

(* A readable+writable window yields a cell block of junk bytes. *)
Lemma p12_cells : forall m lo hi a (n : nat),
  stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists junk, rw_cells rsegs m a [CB n junk].
Proof.
  intros m lo hi a n HST Hlo Hhi.
  destruct (stk_split rsegs m lo a hi HST ltac:(lia)) as (_ & H1).
  destruct (stk_split rsegs m a (a + Z.of_nat n) hi H1 ltac:(lia)) as (H2 & _).
  destruct (stk_carve rsegs m a (a + Z.of_nat n) n H2 ltac:(lia)) as (_ & junk & HR).
  replace (a + Z.of_nat n - Z.of_nat n) with a in HR by lia.
  exists junk. exact HR.
Qed.

Lemma p12_stk_sub : forall m lo hi a b, stk rsegs m lo hi -> lo <= a -> a <= b -> b <= hi -> stk rsegs m a b.
Proof.
  intros m lo hi a b HST Hlo Hab Hhi.
  destruct (stk_split rsegs m lo a hi HST ltac:(lia)) as (_ & H1).
  destruct (stk_split rsegs m a b hi H1 ltac:(lia)) as (H2 & _). exact H2.
Qed.

(* The FRAME_SHADOW = 392 frame-shadow bytes are shadow bytes (their granules are the frame, which is app memory). *)
Lemma p12_sh_in : forall fr a, (forall x, fr <= x < fr + FRAME_BYTES -> app_mem x) ->
  Sfr fr <= a < Sfr fr + FRAME_SHADOW -> in_shadow a.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr a Happ Ha.
  assert (Hdiv : (fr + 8 * (a - Sfr fr)) / 8 = fr / 8 + (a - Sfr fr)).
  { replace (8 * (a - Sfr fr)) with ((a - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Hin : fr <= fr + 8 * (a - Sfr fr) < fr + FRAME_BYTES) by lia.
  pose proof (shadow_of_app (fr + 8 * (a - Sfr fr)) (Happ _ Hin)) as His.
  replace (shadow_addr (fr + 8 * (a - Sfr fr))) with a in His; [exact His|].
  unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia.
Qed.

(* Route (C) (a Theorem Labs lane's frozen form): the shadow bytes p12_sh_stk reads are the window [lo, hi) itself. *)
Definition p12_sh_stk_shadow_R (lo hi : Z) : Z -> Prop := fun a => lo <= a < hi.

(* A shadow window present and writable is a stk window. *)
Lemma p12_sh_stk_on : forall m lo hi, A.ShadowRwOn.shadow_rw_on (p12_sh_stk_shadow_R lo hi) m ->
  (forall a, lo <= a < hi -> in_shadow a) -> 0 <= lo -> hi <= 2 ^ 64 -> stk rsegs m lo hi.
Proof.
  intros m lo hi HSW Hin Hlo Hhi. split; [exact Hlo|]. split; [exact Hhi|].
  intros a Ha. exact (HSW a Ha (Hin a Ha)).
Qed.

(* A shadow window is readable and writable (the asan runtime's shadow_rw). *)
Lemma p12_sh_stk : forall m lo hi, shadow_rw m -> (forall a, lo <= a < hi -> in_shadow a) ->
  0 <= lo -> hi <= 2 ^ 64 -> stk rsegs m lo hi.
Proof. intros m lo hi HSW. exact (p12_sh_stk_on m lo hi (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW)). Qed.

(* The 392 shadow bytes after a write confined to [S0 + 370, S0 + 386) (v1.8: 380 bytes, [S0 + 360, S0 + 376)). *)
Lemma p12_sh_rebuild : forall m m' W S0 sh sh16,
  bytes_at rsegs m S0 sh -> length sh = Z.to_nat FRAME_SHADOW ->
  munch W m m' ->
  disjoint_from W S0 370 -> disjoint_from W (S0 + 386) 6 ->
  bytes_at rsegs m' (S0 + 370) sh16 -> length sh16 = 16%nat ->
  exists sh', bytes_at rsegs m' S0 sh' /\ length sh' = Z.to_nat FRAME_SHADOW.
Proof.
  intros m m' W S0 sh sh16 Hsh Hlen MU Hd1 Hd2 HB16 HL16.
  assert (HFS : Z.to_nat FRAME_SHADOW = 392%nat) by reflexivity.
  rewrite HFS in Hlen.
  rewrite <- (firstn_skipn 370 sh) in Hsh.
  apply (proj1 (bytes_at_app rsegs m S0 _ _)) in Hsh. destruct Hsh as (Hpre & Hrest).
  assert (Lpre : length (firstn 370 sh) = 370%nat) by (rewrite length_firstn, Hlen; reflexivity).
  assert (Lrest : length (skipn 370 sh) = 22%nat) by (rewrite length_skipn, Hlen; reflexivity).
  rewrite Lpre in Hrest.
  rewrite <- (firstn_skipn 16 (skipn 370 sh)) in Hrest.
  apply (proj1 (bytes_at_app rsegs m (S0 + 370) _ _)) in Hrest. destruct Hrest as (_ & Hpost).
  assert (Lmid : length (firstn 16 (skipn 370 sh)) = 16%nat) by (rewrite length_firstn, Lrest; reflexivity).
  assert (Lpost : length (skipn 16 (skipn 370 sh)) = 6%nat) by (rewrite length_skipn, Lrest; reflexivity).
  rewrite Lmid in Hpost.
  assert (Hpre' : bytes_at rsegs m' S0 (firstn 370 sh)).
  { eapply bytes_at_transport; [exact Hpre | exact MU |].
    rewrite Lpre. change (Z.of_nat 370) with 370. exact Hd1. }
  assert (Hpost' : bytes_at rsegs m' (S0 + 370 + 16) (skipn 16 (skipn 370 sh))).
  { eapply bytes_at_transport; [exact Hpost | exact MU |].
    rewrite Lpost. change (Z.of_nat 6) with 6.
    replace (S0 + 370 + 16) with (S0 + 386) by lia. exact Hd2. }
  exists (firstn 370 sh ++ sh16 ++ skipn 16 (skipn 370 sh)).
  split.
  - apply (proj2 (bytes_at_app rsegs m' S0 _ _)). split; [exact Hpre'|].
    rewrite Lpre. apply (proj2 (bytes_at_app rsegs m' (S0 + 370) _ _)). split; [exact HB16|].
    rewrite HL16. replace (S0 + 370 + Z.of_nat 16) with (S0 + 370 + 16) by lia. exact Hpost'.
  - rewrite !length_app, Lpre, HL16, Lpost. reflexivity.
Qed.

(* Every registered global lies below the frame, so its shadow byte lies below the frame's shadow. *)
Lemma p12_ag_lt : forall a, in_globals AF.frame_AG a -> a < AC.GT.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (H : forallb (fun p => Z.leb (fst p + snd p) AC.GT) AF.frame_AG = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) H (lo, len) Hin) as HH.
  cbn [fst snd] in HH. apply Z.leb_le in HH. lia.
Qed.

Lemma p12_ag_keep : forall m m' W,
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) ->
  munch W m m' ->
  (forall a, in_globals AF.frame_AG a -> outside W (shadow_addr a)) ->
  forall a, in_globals AF.frame_AG a -> addressable m' a 1.
Proof.
  intros m m' W HAG MU Hout a Hin.
  destruct (HAG a Hin) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H4 i Hi) as (Hap & b & Hb & Hok).
  split; [exact Hap|]. exists b. split; [|exact Hok].
  assert (Hr : 0 <= shadow_addr (a + i) < 2 ^ 64).
  { pose proof (in_shadow_range (shadow_addr (a + i)) (shadow_of_app (a + i) Hap)). lia. }
  unfold mrd in *. rewrite (MU (wa (shadow_addr (a + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. replace i with 0 in * by lia. rewrite Z.add_0_r.
  exact (Hout a Hin).
Qed.

(* The frame-loop entry's model values at turn 0: the identity record is ID0, the fragment record is 72 zeros. *)
Lemma p12_nth_ID0 : forall j, RcIdentModel.nthb RcIdentModel.ID0 j = RcIdentModel.zb 0.
Proof.
  intros j. unfold RcIdentModel.nthb, RcIdentModel.ID0.
  destruct (Nat.lt_ge_cases j RcIdentModel.ID_SIZE) as [H|H].
  - apply (repeat_spec RcIdentModel.ID_SIZE (RcIdentModel.zb 0)).
    apply nth_In. rewrite repeat_length. exact H.
  - apply nth_overflow. rewrite repeat_length. exact H.
Qed.

Lemma p12_id_ok : RcIdentModel.id_ok RcIdentModel.ID0.
Proof.
  assert (HZ : forall j, RcIdentModel.bz (RcIdentModel.nthb RcIdentModel.ID0 j) = 0)
    by (intros j; rewrite p12_nth_ID0; reflexivity).
  unfold RcIdentModel.id_ok, RcIdentModel.has_fw, RcIdentModel.has_model_name, RcIdentModel.has_reac_version,
    RcIdentModel.fw_milli, RcIdentModel.major, RcIdentModel.minor, RcIdentModel.patch, RcIdentModel.be16.
  split; [left; apply HZ|].
  split; [left; apply HZ|].
  split; [left; apply HZ|].
  split; [apply HZ|].
  split; [intros _ j Hj; apply HZ|].
  split; [intros H; rewrite HZ in H; discriminate H|].
  split; [intros _; rewrite !HZ; reflexivity|].
  split; [intros H; rewrite HZ in H; discriminate H|].
  split; [intros _ j Hj; apply HZ|].
  split; [intros H; rewrite HZ in H; discriminate H|].
  split; [apply HZ | apply HZ].
Qed.

Lemma p12_frag_ok : frag_ok z72.
Proof. split; [left; reflexivity | intros H; vm_compute in H; discriminate H]. Qed.

(* v1.9 FI is one implication (SlotModel.v): byte 6 of z72 is 0, so it holds vacuously at turn 0. *)
Lemma p12_FI : FI z72 fs0.
Proof. intros H; vm_compute in H; discriminate H. Qed.

(* fs_body fs0 = [], so FSb's body conjunct at turn 0 is an empty bytes_at. *)
Lemma p12_ba_nil : forall m a, 0 <= a <= 2 ^ 64 -> bytes_at rsegs m a [].
Proof.
  intros m a Ha. split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn [length] in Hi. lia.
Qed.

(* ---- the instrumented one-byte check ---- *)

Ltac p12_join G :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) => exact (G (getr R (Z_to_bv 5 12)))
  end.

(* The check of a literal address whose granule offset is c and whose shadow byte is k (OK: k = 0, the fast
   path, or c < k, the slow path 82bfc / 82c08 (v1.8 82b3c / 82b48) -- andi a2,a0,7; blt a2,a1 back to the load).
   Both arms reach the join; the slow one has clobbered register 12, which the join generalises. *)
Ltac p12_chk k OK c :=
  step; step; step; step;
  unfold sxb; rewrite (RcAsanLib.rc_eqb0_signed (bv_signed k)) by (pose proof (RcAsanLib.rc_byte_signed k); lia);
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?Bc) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evt segs Q (MS (bvmap_set (Z_to_bv 5 12) rr R) F Bc fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ p12_join G
        | step; step;
          rewrite (RcAsanLib.rc_lts_signed c (bv_signed k))
            by (pose proof (RcAsanLib.rc_byte_signed k); lia);
          replace (c <? bv_signed k) with true
            by (symmetry; apply Z.ltb_lt; let O := fresh "O" in destruct OK as [O|O]; lia);
          p12_join G ]
      | intros ?; simp_regs ]
  end.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The allocator laws this file takes apart, each destructured ONCE here (a Theorem Labs lane's rule, 2026-10-28: append-only
   at every nesting level; the next generation adds named sub-projections, and then only these proofs move). *)
Lemma p12_laws_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md p n HAH Hin)
    as (_ & _ & Hpn & _ & Hbody).
  split; [exact Hpn|]. intros a Ha.
  destruct (Hbody a Ha) as (Hap & _ & _ & _ & Hnfs). exact (conj Hap Hnfs).
Qed.

Lemma p12_laws_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
     mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  (forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hmc Hw.
  destruct (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hmc Hw)
    as (H1 & H2 & H3 & H4).
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma p12_laws_fs_place : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Hw Hr.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hr)
    as (H1 & H2 & _ & H4).
  exact (conj H1 (conj H2 H4)).
Qed.

(* ---- generic transport helpers ---- *)

(* P7's fra_A (copy, see the header): the spill base A of FRA is in range, at or above sp and 416 bytes below the
   entry sp S. *)
Lemma p12_fra_A : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists A, rg regs 9 A /\ 0 <= A < 2 ^ 64 /\ AC.aspZ regs <= A /\ fr + FRAME_BYTES <= A /\ A + 416 <= g_S g.
Proof.
  intros g fr hb regs mem md HFRA.
  pose proof (u64_range (getr regs 2)) as Hu.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  unfold AC.aspZ in *. exists A.
  split; [exact Hr9|]. split; [unfold APPMEM_END in *; lia|].
  split; [lia|]. split; [exact Hfa | exact HA416].
Qed.

(* P7's fr_place (copy): the frame is app memory above the image's writable data (SlotInv.fra_app). *)
Lemma p12_fr_place : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  AC.GT <= fr /\ (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a).
Proof.
  intros g fr hb regs mem md HFRA. eapply fra_app. exact HFRA.
Qed.

(* A shadow byte inside [S(fr)+370, S(fr)+386) is the shadow of a frame byte in [fr + 2960, fr + 3088). *)
Lemma p12_sh_back : forall fr y, fr mod 8 = 0 -> 0 <= y ->
  Sfr fr + 370 <= shadow_addr y < Sfr fr + 386 -> fr + 2960 <= y < fr + 3088.
Proof.
  intros fr y Hm Hy H. unfold shadow_addr, Sfr, shadow_addr, ASAN_K in H.
  revert H Hm Hy. Z.div_mod_to_equations. lia.
Qed.

(* addressable survives a run that leaves the shadow byte of each of its bytes alone. *)
Lemma p12_addr_munch : forall W m m' p n,
  addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU Ho.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok).
  pose proof (in_shadow_range (shadow_addr (p + i)) (shadow_of_app (p + i) Happ)) as Hr.
  split; [exact Happ|]. exists b. split; [|exact Hok].
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. exact (Ho i Hi).
Qed.

(* A spill at FRA's base A carried across a munch W that keeps register 9 and misses the eight bytes at A+off. *)
Lemma p12_spill_keep : forall (regs regs' : bvmap 5 word) m m' W off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  getr regs' 9 = getr regs 9 -> munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A (A' & HA' & Hq) HA Hlo Hhi Hoff E9 MU HW.
  unfold q64 in Hq. pose proof Hq as Hqb. apply bytes_at_bound in Hqb. rewrite length_le8 in Hqb.
  assert (HA'A : A' = A).
  { unfold rg in HA', HA. rewrite HA in HA'. apply (f_equal (@bv_unsigned 64)) in HA'.
    rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap, bv_modulus in HA'.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in HA'. rewrite (Z.mod_small A (2 ^ 64)) in HA' by lia.
    revert Hqb HA'. Z.div_mod_to_equations. lia. }
  subst A'. exists A. split; [unfold rg in *; rewrite E9; exact HA|].
  unfold q64. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. exact (HW x ltac:(lia)).
Qed.

(* The value of a spill at FRA's base A. *)
Lemma p12_spill_q64 : forall (regs : bvmap 5 word) m off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA Hlo Hhi Hoff.
  unfold q64 in Hq. pose proof Hq as Hqb. apply bytes_at_bound in Hqb. rewrite length_le8 in Hqb.
  assert (HA'A : A' = A).
  { unfold rg in HA', HA. rewrite HA in HA'. apply (f_equal (@bv_unsigned 64)) in HA'.
    rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap, bv_modulus in HA'.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in HA'. rewrite (Z.mod_small A (2 ^ 64)) in HA' by lia.
    revert Hqb HA'. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* A readable+writable window holding f at a, v at a + 16 and o at a + 56, as a cell block
   [C8 f; CB 8 junk0; C8 v; CB 32 junk; C8 o] (v1.9 P12 reads [A + 192] = fragb fr, [A + 208] = fr + 448 and
   [A + 248] = fr + 176; v1.8 read [A + 208], [A + 200], [A + 248]). *)
Lemma p12_q64_rw4 : forall m lo hi a f v o,
  stk rsegs m lo hi -> lo <= a -> a + 64 <= hi -> q64 m a f -> q64 m (a + 16) v -> q64 m (a + 56) o ->
  exists junk0 junk, rw_cells rsegs m a
    [C8 (Z_to_bv 64 f); CB 8 junk0; C8 (Z_to_bv 64 v); CB 32 junk; C8 (Z_to_bv 64 o)].
Proof.
  intros m lo hi a f v o HST Hlo Hhi Hq0 Hq16 Hq56.
  destruct (p12_cells m lo hi (a + 8) 8 HST ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as (junk0 & HR8).
  destruct (p12_cells m lo hi (a + 24) 32 HST ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as (junk & HR32).
  exists junk0, junk.
  pose proof HST as (Hlo0 & Hhi2 & HSw).
  unfold q64 in Hq0, Hq16, Hq56.
  destruct HR8 as [[Hwf8 Hb8] _]. cbn [cells_wf cell_wf] in Hwf8. cbn [cells_bytes cbytes] in Hb8.
  rewrite app_nil_r in Hb8. destruct Hwf8 as (Hl8 & _).
  destruct HR32 as [[Hwf32 Hb32] _]. cbn [cells_wf cell_wf] in Hwf32. cbn [cells_bytes cbytes] in Hb32.
  rewrite app_nil_r in Hb32. destruct Hwf32 as (Hl32 & _).
  split.
  - split.
    + cbn [cells_wf cell_wf]. repeat split; try exact I; try exact Hl8; try exact Hl32.
    + cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply (proj2 (bytes_at_app rsegs m a _ _)). split; [exact Hq0|]. rewrite length_le8.
      replace (a + Z.of_nat 8) with (a + 8) by lia.
      apply (proj2 (bytes_at_app rsegs m (a + 8) _ _)). split; [exact Hb8|]. rewrite Hl8.
      replace (a + 8 + Z.of_nat 8) with (a + 16) by lia.
      apply (proj2 (bytes_at_app rsegs m (a + 16) _ _)). split; [exact Hq16|]. rewrite length_le8.
      replace (a + 16 + Z.of_nat 8) with (a + 24) by lia.
      apply (proj2 (bytes_at_app rsegs m (a + 24) _ _)). split; [exact Hb32|]. rewrite Hl32.
      replace (a + 24 + Z.of_nat 32) with (a + 56) by lia. exact Hq56.
  - split; [lia|]. split; [cbn [cells_size csize]; lia|].
    intros i Hi. assert (Hib : 0 <= i < 64) by (cbn [cells_size csize] in Hi; lia).
    destruct (HSw (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* One readable+writable spill word as a one-cell block (v1.9 P12's NEW-only load [A + 32] = fr + 2880). *)
Lemma p12_q64_rw1 : forall m lo hi a v,
  stk rsegs m lo hi -> lo <= a -> a + 8 <= hi -> q64 m a v -> rw_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m lo hi a v HST Hlo Hhi Hq.
  pose proof HST as (Hlo0 & Hhi2 & HSw). unfold q64 in Hq.
  split.
  - split; [cbn [cells_wf cell_wf]; repeat split; try exact I|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hq.
  - split; [lia|]. split; [cbn [cells_size csize]; lia|].
    intros i Hi. assert (Hib : 0 <= i < 8) by (cbn [cells_size csize] in Hi; lia).
    destruct (HSw (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* Every byte of a live heap block lies outside the frame body [fr, fr + FRAME_BYTES): real arm by the block being
   below stklo (a_laws_blocks) and the frame at or above it, side arm by the block being outside the FakeStack. *)
Lemma p12_in_fr_dj : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md -> In (g_p g, g_n g) (hb ++ g_H g) ->
  forall i, 0 <= i < g_n g -> ~ (fr <= g_p g + i < fr + FRAME_BYTES).
Proof.
  intros g fr hb regs mem md HFRA Hin i Hi.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  destruct (p12_laws_blocks (hb ++ g_H g) mem md (g_p g) (g_n g) HAH Hin) as (Hpn & Hbody).
  destruct (Hbody (g_p g + i) ltac:(lia)) as (_ & Hnfs).
  intros Hfr.
  destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5f [Hfsb [Hfs Hrec]]]].
  - destruct (Hreal (g_p g + i) ltac:(lia)) as (Hge & _). lia.
  - apply Hnfs. exact (Hfs (g_p g + i) ltac:(lia)).
Qed.

(* The heap invariant / ownership / stklo / stkhi survive the eight frame-shadow stores. Real arm: each written
   byte is the shadow of a frame byte in [stklo, APPMEM_END) (a_laws_store). Side arm: the frame is in the
   FakeStack above its metadata, so a_fs_ok_store_AH applies. *)
Lemma p12_ah_meta : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  munch [(Sfr fr + 370, Sfr fr + 386)] mem mem' ->
  wmono rsegs mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> exists b, mbyte rsegs mem' q = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md HFRA MU WM HPRES.
  destruct (p12_fr_place g fr hb regs mem md HFRA) as (HGT & Hfapp).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hgran : forall q, Sfr fr + 370 <= q < Sfr fr + 386 ->
            q = shadow_addr (fr + 8 * (q - Sfr fr)) /\ fr <= fr + 8 * (q - Sfr fr) < fr + FRAME_BYTES).
  { intros q Hq. split; [|lia].
    assert (Hdiv : (fr + 8 * (q - Sfr fr)) / 8 = fr / 8 + (q - Sfr fr)).
    { replace (8 * (q - Sfr fr)) with ((q - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5f [Hfsb [Hfs Hrec]]]].
  - assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
      cbn [outside]. split; [|exact I]. intros [H1 H2]. apply Hns.
      destruct (Hgran a ltac:(lia)) as (Heq & Hin).
      unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (a - Sfr fr)).
      split; [exact Heq|]. right; left. exact (Hreal _ Hin). }
    destruct (p12_laws_store (hb ++ g_H g) mem mem' md HAH HstoreC HwmL) as (HAH' & Hown' & HSTKeq & HSThi).
    split; [exact HAH'|]. split; [exact Hown'|]. split; [exact HSTKeq | exact HSThi].
  - destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (bb & Hb64 & Hwb & Hb1 & Hb2).
    pose proof (Hfsb bb Hwb Hb64) as Hbm.
    destruct (p12_laws_fs_place (hb ++ g_H g) mem md bb HAH Hwb Hb64) as (HGTb & Hbs & Happfs).
    assert (Hfsz : bb + AC.FS_SIZE <= 2 ^ 64).
    { assert (Ha : app_mem (bb + AC.FS_SIZE - 1)) by (apply Happfs; unfold AC.FS_SIZE; lia).
      unfold app_mem, APPMEM_END, LOWMEM_END, HIGHMEM_BEG in Ha. lia. }
    assert (Hmeta : forall q, fs_meta bb q -> outside [(Sfr fr + 370, Sfr fr + 386)] q).
    { intros q Hq. cbn [outside]. split; [|exact I]. intros [H1 H2].
      assert (Hqlo : bb <= q).
      { unfold fs_meta in Hq. destruct Hq as [H|[H|[(c & Hc & Hr)|(c & j & Hc & Hj & Heq)]]].
        - lia.
        - lia.
        - unfold AC.a_fs_hint in Hr. lia.
        - subst q. exact (proj1 (a_fs_flag_range bb c j Hc Hj)). }
      pose proof (fs_meta_below bb q Hq) as Hqhi.
      assert (Happq : app_mem q) by (apply Happfs; unfold AC.FS_SIZE; lia).
      exact (app_not_shadow q Happq (p12_sh_in fr q Hfapp ltac:(lia))). }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
      ~ (bb <= q < bb + AC.FS_SIZE) ->
      ~ (exists b0, bb <= b0 < bb + AC.FS_SIZE /\ q = shadow_addr b0) ->
      mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hns Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by lia.
      cbn [outside]. split; [|exact I]. intros [H1 H2]. apply Hnsh.
      destruct (Hgran q ltac:(lia)) as (Heq & Hin).
      exists (fr + 8 * (q - Sfr fr)). split; [|exact Heq]. lia. }
    destruct (a_fs_ok_store_AH _ _ _ _ _ [(Sfr fr + 370, Sfr fr + 386)]
      (hb ++ g_H g) mem mem' md bb LAWS HAH Hwb Hb64 Hfsz MU HwmL HPRES Hmeta Hagree)
      as (HAH' & Hown' & HSTKeq & HSThi).
    split; [exact HAH'|]. split; [exact Hown'|]. split; [exact HSTKeq | exact HSThi].
Qed.

(* The heap invariant / ownership / stklo / stkhi survive the spill stores in [A+48, A+136): every such byte is in
   [stklo, APPMEM_END), since stklo <= S - SLOT_STACK < sp <= A. *)
Lemma p12_ah_spill : forall g fr hb regs mem mem' md A,
  FRA B APIf ra g fr hb regs mem md -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  munch [(A + 48, A + 120); (A + 128, A + 136)] mem mem' -> wmono rsegs mem mem' ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md A HFRA HA9 HAr MU WM.
  destruct (p12_fra_A g fr hb regs mem md HFRA) as (A' & HA9' & HAr' & HspA & HfrA & HA416').
  rewrite (p12_rg_inj regs 9 A A' HA9 HA9' HAr HAr') in *.
  pose proof HFRA as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  unfold AC.aspZ in Haspz, HspA.
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
    mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
    cbn [outside]. split; [|split; [|exact I]]; intros [H1 H2]; apply Hns;
      unfold AC.a_store_ok; right; left; unfold APPMEM_END in *; lia. }
  destruct (p12_laws_store (hb ++ g_H g) mem mem' md HAH HstoreC HwmL) as (HAH' & Hown' & HSTKeq & HSThi).
  split; [exact HAH'|]. split; [exact Hown'|]. split; [exact HSTKeq | exact HSThi].
Qed.

(* ---- the run ---- *)

(* 0x81c84 - 0x81ce0: the two instrumented checks of the "?" string and the eight frame-shadow stores
   sb s11,K(s3), K in {382,383,384,385,370,372,376,380} = [SF + 370, SF + 386) (v1.8 0x81bf8 - 0x81c54, the window
   [SF + 360, SF + 376)). QMARK is unfolded, so the walk computes with whichever literal reac_ctrl_kind_name_c.v
   gives it (v1.9 0x211e0; both it and v1.8's 0x211c0 are 8-aligned, so the granule offsets are 0 and 1). *)
Lemma p12_evt_a :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SF : Z) (kb : byte) (junk : list byte),
    a0 = Z_to_bv 64 QMARK -> s10 = Z_to_bv 64 0x7fff8000 -> s3 = Z_to_bv 64 SF ->
    ov_read_bytes rsegs m (wa (QMARK / 8 + 0x7fff8000)) 1 = Some [kb] ->
    ov_read_bytes rsegs m (wa ((QMARK + 1) / 8 + 0x7fff8000)) 1 = Some [kb] ->
    (bv_signed kb = 0 \/ 0 < bv_signed kb) ->
    (bv_signed kb = 0 \/ 1 < bv_signed kb) ->
    ov_read_bytes rsegs m (wa QMARK) 1 = Some [Z_to_bv 8 63] ->
    ov_read_bytes rsegs m (wa (QMARK + 1)) 1 = Some [Z_to_bv 8 0] ->
    rw_cells rsegs m (SF + 370) [CB 16 junk] ->
    LE.evt rsegs
      (fun ms' => exists (a0' a1' a2' s11' : word) (m' : word -> option byte) (sh16 : list byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11'
                       t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81ce0) fc None m' (seg_rom rsegs) /\
         munch [(SF + 370, SF + 386)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (SF + 370) sh16 /\ length sh16 = 16%nat)
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c84) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m SF kb junk -> -> -> HK0 HK1 OK0 OK1 HQ0 HQ1 HC.
  unfold QMARK in *.
  pose proof (munch_refl [(SF + 370, SF + 386)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  p12_chk kb OK0 0.       (* 81c84 srli; 81c88 add; 81c8c lb; 81c90 bnez (slow path 82bfc / 82c00) *)
  step. step. step.       (* 81c94 lbu a1,0(a0); 81c98 li a2,63; 81c9c bne a1,a2,82bf4 *)
  rewrite p12_zxb63. if_false.
  step.                   (* 81ca0 addi a0,a0,1 *)
  p12_chk kb OK1 1.       (* 81ca4 srli; 81ca8 add; 81cac lb; 81cb0 bnez (slow path 82c08 / 82c0c) *)
  step. step.             (* 81cb4 lbu a0,0(a0); 81cb8 bnez a0,82bf4 *)
  rewrite p12_zxb0. if_false.
  step.                   (* 81cbc li s11,-8 *)
  step. step. step. step. step. step. step. step.  (* 81cc0 .. 81cdc: the eight sb s11,K(s3) *)
  apply evt_done.
  destruct (p12_cells_bytes _ _ _ HC) as (HB & HL).
  do 6 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact HB | exact HL].
Qed.

(* 0x81ce0 -> 0x82b04: the frame loop is not entered (s9 = n - c0 = 0). *)
Lemma p12_evt_b0 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    bv_unsigned s9 = 0 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                               t3 t4 t5 t6)
                           Fr (Z_to_bv 64 0x82b04) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ce0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m Hs9.
  step. if_true.
  apply evt_done. reflexivity.
Qed.

(* A stored sum read back against the literal sum (the spill stores of P12's run). *)
Ltac p12_addv :=
  first [ reflexivity
        | (rewrite MState.lit_add_lit; reflexivity)
        | (rewrite bv_add_unsigned, !Z_to_bv_unsigned; unfold bv_wrap;
           rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r; reflexivity) ].

(* 0x81ce0 - 0x81d3c: the frame loop is entered (s9 <> 0); j = 0 and the twelve spill stores. The write set is the
   two intervals [A+48, A+120) and [A+128, A+136): the prologue spill [A+120] is not written. [A+128] = [A+208] + 4,
   and (FLC) [A+96] / [A+88] / [A+80] = [A+192] + 8 / 19 / 15, [A+72] / [A+64] = [A+248] + 10 / 4 and the NEW-only
   [A+56] / [A+48] = [A+32] + 9 / 10; [A+112] = n and [A+104] = have are 0. *)
Lemma p12_evt_b1 :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f v o p : Z)
         (junk1 junk0 junk2 : list byte),
    s1 = Z_to_bv 64 A -> bv_unsigned s9 <> 0 ->
    rw_cells rsegs m (A + 48) [CB 88 junk1] ->
    rw_cells rsegs m (A + 192)
      [C8 (Z_to_bv 64 f); CB 8 junk0; C8 (Z_to_bv 64 v); CB 32 junk2; C8 (Z_to_bv 64 o)] ->
    rw_cells rsegs m (A + 32) [C8 (Z_to_bv 64 p)] ->
    LE.evt rsegs
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte) (bs88 : list byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 0) s6 s7 s8 s9
                       s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81d40) fc None m' (seg_rom rsegs) /\
         munch [(A + 48, A + 120); (A + 128, A + 136)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 48) bs88 /\ length bs88 = 88%nat /\
         q64 m' (A + 104) 0 /\ q64 m' (A + 112) 0 /\
         q64 m' (A + 128) (v + 4) /\
         q64 m' (A + 64) (o + 4) /\ q64 m' (A + 72) (o + 10) /\
         q64 m' (A + 80) (f + 15) /\ q64 m' (A + 88) (f + 19) /\ q64 m' (A + 96) (f + 8) /\
         q64 m' (A + 48) (p + 10) /\ q64 m' (A + 56) (p + 9))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81ce0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f v o p junk1 junk0 junk2 -> Hs9 HC1 HC2 HC3.
  pose proof (munch_refl [(A + 48, A + 120); (A + 128, A + 136)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_false.                                  (* 81ce0 beqz s9,82b04 *)
  step.                                            (* 81ce4 li s5,0 *)
  step. step.                                      (* 81ce8 sd zero,112(s1); 81cec sd zero,104(s1) *)
  step. step. step. step. step. step. step.        (* 81cf0 ld a0,192(s1) .. 81d08 sd a0,80(s1) *)
  step. step. step. step. step.                    (* 81d0c ld a0,248(s1) .. 81d1c sd a0,64(s1) *)
  step. step. step.                                (* 81d20 ld a0,208(s1) .. 81d28 sd a0,128(s1) *)
  step. step. step. step. step.                    (* 81d2c ld a0,32(s1) .. 81d3c sd a0,48(s1) *)
  apply evt_done.
  destruct (p12_cells_bytes _ _ _ HC1) as (HB & HL).
  do 4 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact HB|]. split; [exact HL|].
  split.
  { replace (A + 104) with (A + 48 + Z.of_nat 56) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 56%nat); [exact HC1 | reflexivity | vm_compute; reflexivity]. }
  split.
  { replace (A + 112) with (A + 48 + Z.of_nat 64) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 64%nat); [exact HC1 | reflexivity | vm_compute; reflexivity]. }
  split.
  { replace (A + 128) with (A + 48 + Z.of_nat 80) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 80%nat); [exact HC1 | reflexivity | p12_addv]. }
  split.
  { replace (A + 64) with (A + 48 + Z.of_nat 16) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 16%nat); [exact HC1 | reflexivity | p12_addv]. }
  split.
  { replace (A + 72) with (A + 48 + Z.of_nat 24) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 24%nat); [exact HC1 | reflexivity | p12_addv]. }
  split.
  { replace (A + 80) with (A + 48 + Z.of_nat 32) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 32%nat); [exact HC1 | reflexivity | p12_addv]. }
  split.
  { replace (A + 88) with (A + 48 + Z.of_nat 40) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 40%nat); [exact HC1 | reflexivity | p12_addv]. }
  split.
  { replace (A + 96) with (A + 48 + Z.of_nat 48) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 48%nat); [exact HC1 | reflexivity | p12_addv]. }
  split.
  { pose proof (p12_cell_q64 _ (A + 48) _ 0%nat _ (p + 10) HC1 eq_refl) as Hq.
    change (Z.of_nat 0) with 0 in Hq. rewrite Z.add_0_r in Hq. apply Hq. p12_addv. }
  { replace (A + 56) with (A + 48 + Z.of_nat 8) by lia.
    eapply (p12_cell_q64 _ (A + 48) _ 8%nat); [exact HC1 | reflexivity | p12_addv]. }
Qed.

(* ---- the segment lemma ---- *)

(* ent_store states its write set in Tac_slot's (UL) flavour of munch / outside; the run's facts are in lib.Lib's.
   p12_outU proves an `outside` goal on either flavour (fr_outside_lib bridges UL to lib). *)
Ltac p12_outU :=
  first [ (cbn [outside]; repeat split; first [lia | exact I])
        | (apply (proj2 (fr_outside_lib _ _)); cbn [outside]; repeat split; first [lia | exact I]) ].

Lemma seg_P12 :
  Hat B APIf ra (Inv_A81d40_at B APIf ra) 0%nat ->
  Hcut B APIf ra (Inv_A82b04 B APIf ra) ->
  Hcut B APIf ra (Inv_A81c84 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros Hexit1 Hexit0 g c HInv.
  pose proof (proj1 FF) as SEGS.
  (* The last binder HAD2880 is `addressable m (fr + 2880) 35`, appended last to Inv_A81b80 .. Inv_A81c84 by the
     cut bundle's round 4 (a working branch 73604325d3c): P3 makes it, P4 .. P11 carry it, and FSb's
     position 4 at this file's exit needs it. *)
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT &
    Hn & HOUR & Ha0 & HSTR & HAD2 & HXC & HCUR & HPRO & Hsp144 & HAD2691 & HSP192 & HADF & HADI & HID & HFG &
    HAD2880).
  (* PRO, v1.9: position 7 is [A + 208] = fr + 448 (v1.8 [A + 200]); position 16 (new, last) [A + 32] = fr + 2880 *)
  pose proof HPRO as (Hsp40 & Hsp120 & Hsp136 & Hsp160 & Hsp168 & Hsp176 & Hsp208 & Hsp248 & HAD2624 & _ & _ &
    Hsp184 & Hsp256 & Hsp264 & Hsp272 & Hsp32).
  pose proof (fra_stk B APIf ra g fr [] regs mem md HFRA) as Hstkfr.
  subst c. rewrite SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof HFRA as (A0 & sp0 & s50 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm2 & Haspz & Hstklo &
    Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof HRT as (HAC0 & HSW0 & _).
  destruct Hsh as (shold & Hshb & Hshl).
  destruct (p12_fr_place g fr [] regs mem md HFRA) as (HGT & Hfapp).
  destruct (p12_fra_A g fr [] regs mem md HFRA) as (A & HA9 & HAr & HspA & HfrA & HA416').
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  unfold AC.aspZ in HspA, Haspz.
  rewrite Haspz in HspA.
  assert (HAlo : HIGHMEM_BEG <= A) by lia.
  assert (Hfrm8 : fr mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
  assert (Hcase : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { destruct (Hfapp fr ltac:(lia)) as [Hl|Hh]; [|right; lia].
    destruct (Hfapp (fr + FRAME_BYTES - 1) ltac:(lia)) as [Hl2|Hh2]; [left; unfold LOWMEM_END in *; lia|].
    exfalso.
    pose proof (Hfapp LOWMEM_END ltac:(unfold LOWMEM_END, HIGHMEM_BEG in *; lia)) as Hx.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG in *. lia. }
  assert (HshIS : forall a, Sfr fr <= a < Sfr fr + FRAME_SHADOW -> in_shadow a)
    by (intros a Ha; exact (p12_sh_in fr a Hfapp Ha)).
  pose proof (HshIS (Sfr fr) ltac:(lia)) as His0.
  pose proof (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as HisL.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in His0, HisL.
  assert (HshB : 0x7fff8000 <= Sfr fr /\ Sfr fr + FRAME_SHADOW - 1 < 0x10007fff8000) by lia.
  (* app addresses are outside the frame-shadow write set W1 = [S(fr)+370, S(fr)+386) *)
  assert (Hout1app : forall x, app_mem x -> outside [(Sfr fr + 370, Sfr fr + 386)] x).
  { intros x Hxa. cbn [outside]. split; [|exact I]. intros Hc.
    apply (app_not_shadow x Hxa). apply (HshIS x). lia. }
  (* the shadow cell block for evt_a *)
  destruct (p12_cells mem (Sfr fr + 370) (Sfr fr + 386) (Sfr fr + 370) 16
              (p12_sh_stk mem (Sfr fr + 370) (Sfr fr + 386) HSW0
                 ltac:(intros a Ha; apply HshIS; lia) ltac:(lia) ltac:(unfold APPMEM_END in *; lia))
              ltac:(lia) ltac:(cbn [Z.of_nat]; lia)) as (junk & HCsh).
  (* the two shadow-byte reads and the string bytes *)
  assert (HQAD : addressable mem QMARK 2) by exact HAD2.
  destruct HQAD as (HQ1 & HQ2 & HQ3 & HQ4).
  destruct (HQ4 0 ltac:(lia)) as (Hap0 & kb & Hkb & Hok0).
  destruct (HQ4 1 ltac:(lia)) as (Hap1 & kb1 & Hkb1 & Hok1).
  assert (Heqsh : shadow_addr (QMARK + 1) = shadow_addr (QMARK + 0)) by (vm_compute; reflexivity).
  rewrite Heqsh, Hkb in Hkb1. injection Hkb1 as Ekb. subst kb1.
  assert (HKa : ov_read_bytes rsegs mem (wa (QMARK / 8 + 0x7fff8000)) 1 = Some [kb]).
  { apply p12_rd1; [unfold QMARK; lia | unfold QMARK; lia |].
    replace (QMARK / 8 + 0x7fff8000) with (shadow_addr (QMARK + 0)) by (vm_compute; reflexivity).
    exact Hkb. }
  assert (HKb : ov_read_bytes rsegs mem (wa ((QMARK + 1) / 8 + 0x7fff8000)) 1 = Some [kb]).
  { apply p12_rd1; [unfold QMARK; lia | unfold QMARK; lia |].
    replace ((QMARK + 1) / 8 + 0x7fff8000) with (shadow_addr (QMARK + 0)) by (vm_compute; reflexivity).
    exact Hkb. }
  assert (OKa : bv_signed kb = 0 \/ 0 < bv_signed kb).
  { assert (E0 : (QMARK + 0) mod 8 = 0) by (vm_compute; reflexivity).
    unfold shadow_ok in Hok0. destruct Hok0 as [H|H]; [left; exact H | right; lia]. }
  assert (OKb : bv_signed kb = 0 \/ 1 < bv_signed kb).
  { assert (E1 : (QMARK + 1) mod 8 = 1) by (vm_compute; reflexivity).
    unfold shadow_ok in Hok1. destruct Hok1 as [H|H]; [left; exact H | right; lia]. }
  pose proof (HSTR 14 ltac:(lia)) as HQS.
  replace (kind_name_addr 14) with QMARK in HQS by (vm_compute; reflexivity).
  replace (cstr_bytes (kind_name 14)) with [Z_to_bv 8 63; Z_to_bv 8 0] in HQS by (vm_compute; reflexivity).
  assert (HS0 : ov_read_bytes rsegs mem (wa QMARK) 1 = Some [Z_to_bv 8 63]).
  { pose proof (bytes_at_ov_read rsegs mem QMARK [Z_to_bv 8 63; Z_to_bv 8 0] 0 1 HQS ltac:(cbn [length]; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH. cbn [firstn] in HH. exact HH. }
  assert (HS1 : ov_read_bytes rsegs mem (wa (QMARK + 1)) 1 = Some [Z_to_bv 8 0]).
  { pose proof (bytes_at_ov_read rsegs mem QMARK [Z_to_bv 8 63; Z_to_bv 8 0] 1 1 HQS ltac:(cbn [length]; lia)) as HH.
    change (Z.of_nat 1) with 1 in HH. cbn [firstn skipn] in HH. exact HH. }
  assert (Ha0' : getr regs 10 = Z_to_bv 64 QMARK) by (unfold a0v, rg in Ha0; exact Ha0).
  assert (Hs10 : getr regs 26 = Z_to_bv 64 0x7fff8000).
  { unfold rg in Hr26. rewrite Hr26. reflexivity. }
  assert (Hs3 : getr regs 19 = Z_to_bv 64 (Sfr fr)) by (unfold rg in Hr19; exact Hr19).
  (* the cursor *)
  destruct HCUR as (Hc0 & Hr22 & Hr25).
  assert (Hs9u : bv_unsigned (getr regs 25) = g_n g - c0 (g_in g)).
  { unfold rg in Hr25. rewrite Hr25. apply MState.unsigned_lit. lia. }
  (* the spill windows *)
  assert (Hstk48 : stk rsegs mem (A + 48) (A + 136))
    by (apply (p12_stk_sub mem (g_S g - AF.SLOT_STACK) (g_S g)); [exact Hwin | lia | lia | lia]).
  assert (Hstk192 : stk rsegs mem (A + 192) (A + 256))
    by (apply (p12_stk_sub mem (g_S g - AF.SLOT_STACK) (g_S g)); [exact Hwin | lia | lia | lia]).
  assert (Hstk32 : stk rsegs mem (A + 32) (A + 40))
    by (apply (p12_stk_sub mem (g_S g - AF.SLOT_STACK) (g_S g)); [exact Hwin | lia | lia | lia]).
  (* the HPRES of p12_ah_meta: bytes present before the shadow stores are present after them *)
  assert (Hpres : forall m1 sh16, munch [(Sfr fr + 370, Sfr fr + 386)] mem m1 ->
            bytes_at rsegs m1 (Sfr fr + 370) sh16 -> length sh16 = 16%nat ->
            forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
            exists b, mbyte rsegs m1 q = Some b).
  { intros m1 sh16 MU1 HB1 HL1 q Hq (b & Hb).
    destruct (Z_lt_le_dec q (Sfr fr + 370)) as [Hlo|Hge].
    - exists b. unfold mbyte in *. rewrite (MU1 (Z_to_bv 64 q)); [exact Hb|].
      rewrite MState.unsigned_lit by lia. cbn [outside]. split; [lia | exact I].
    - destruct (Z_lt_le_dec q (Sfr fr + 386)) as [Hhi2|Hge2].
      + destruct HB1 as (_ & _ & Hbb).
        pose proof (Hbb (Z.to_nat (q - (Sfr fr + 370))) ltac:(rewrite HL1; lia)) as Hb'.
        rewrite Z2Nat.id in Hb' by lia.
        replace (Sfr fr + 370 + (q - (Sfr fr + 370))) with q in Hb' by lia.
        destruct (nth_error sh16 (Z.to_nat (q - (Sfr fr + 370)))) as [b2|] eqn:En.
        * exists b2. unfold mbyte. exact Hb'.
        * exfalso. apply nth_error_None in En. rewrite HL1 in En. lia.
      + exists b. unfold mbyte in *. rewrite (MU1 (Z_to_bv 64 q)); [exact Hb|].
        rewrite MState.unsigned_lit by lia. cbn [outside]. split; [lia | exact I]. }
  assert (Hrtd : rt_disjoint [(Sfr fr + 370, Sfr fr + 386)]).
  { unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
      RT_AGLOB, RT_AGLOB_LEN.
    cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
  (* the frame_AG globals keep their addressability across the shadow stores *)
  assert (HAGk : forall m1, munch [(Sfr fr + 370, Sfr fr + 386)] mem m1 ->
            forall a, in_globals AF.frame_AG a -> addressable m1 a 1).
  { intros m1 MU1. apply (p12_ag_keep mem m1 _ HAG MU1).
    intros a Hin. pose proof (p12_ag_lt a Hin) as Hlt.
    cbn [outside]. split; [|exact I]. intros [Hc1 Hc2].
    assert (Hd : a / 8 < fr / 8).
    { apply Z.div_lt_upper_bound; [lia|].
      assert (Hfe : 8 * (fr / 8) = fr) by (revert Hfrm8; Z.div_mod_to_equations; lia). lia. }
    unfold Sfr, shadow_addr in Hc1. lia. }
  (* FRA and ENT across the eight shadow stores (W1), from mem to m1 *)
  assert (Hmove1 : forall (regs1 : bvmap 5 word) m1 sh16,
            munch [(Sfr fr + 370, Sfr fr + 386)] mem m1 -> wmono rsegs mem m1 ->
            bytes_at rsegs m1 (Sfr fr + 370) sh16 -> length sh16 = 16%nat ->
            getr regs1 2 = getr regs 2 -> getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
            getr regs1 8 = getr regs 8 -> getr regs1 9 = getr regs 9 -> getr regs1 19 = getr regs 19 ->
            getr regs1 26 = getr regs 26 ->
            FRA B APIf ra g fr [] regs1 m1 md /\ ENT APIf g [] m1 md /\ ro_agree rsegs m1 /\
            AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) m1 md /\
            AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) m1 md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { intros regs1 m1 sh16 MU1 WM1 HB1 HL1 E2 E3 E4 E8 E9 E19 E26.
    assert (Hroa : ro_agree rsegs m1).
    { apply (p12_ro_keep [(Sfr fr + 370, Sfr fr + 386)] mem m1 Hro MU1).
      intros x Hx. cbn [outside]. split; [|exact I]. lia. }
    destruct (p12_ah_meta g fr [] regs mem m1 md HFRA MU1 WM1 (Hpres m1 sh16 MU1 HB1 HL1))
      as (HAH1 & Hown1 & HST1 & HSThi1).
    assert (Hshnew : exists sh', bytes_at rsegs m1 (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { apply (p12_sh_rebuild mem m1 [(Sfr fr + 370, Sfr fr + 386)] (Sfr fr) shold sh16 Hshb Hshl MU1);
        [ cbn [disjoint_from]; split; [left; lia | exact I]
        | cbn [disjoint_from]; split; [right; lia | exact I]
        | exact HB1 | exact HL1 ]. }
    split.
    { apply (sl_fr_meta B APIf ra empty FF g fr [] regs regs1 mem m1 md
               [(Sfr fr + 370, Sfr fr + 386)] HFRA MU1 WM1 Hroa Hrtd HAH1 HST1 Hfapp HGT Hshnew);
        [ intros x Hx Hx1 Hx2; cbn [outside]; split; [lia | exact I]
        | intros A' HA' HA'r x Hx; cbn [outside]; split; [|exact I];
          rewrite (p12_rg_inj regs 9 A' A HA' HA9 HA'r HAr) in Hx; lia
        | intros x Hx; cbn [outside]; split; [lia | exact I]
        | intros A' HA' HA'r x Hx; cbn [outside]; split; [|exact I];
          rewrite (p12_rg_inj regs 9 A' A HA' HA9 HA'r HAr) in Hx; lia
        | intros x Hx; left; cbn [outside]; split; [lia | exact I]
        | exact (HAGk m1 MU1)
        | exact E2 | exact E3 | exact E4 | exact E8 | exact E9 | exact E19 | exact E26 ]. }
    split.
    { eapply ent_store;
        [exact HENT | exact HFRA
        | first [exact MU1 | exact (proj1 (fr_munch_ul _ mem m1) MU1) | exact (proj2 (fr_munch_ul _ mem m1) MU1)]
        | | exact HST1 | exact HSThi1
        | exact (fun a _ Ho => proj2 (Hown1 a) Ho)].
      intros x Hx. destruct (Z.lt_ge_cases x (Sfr fr)) as [Hlt|Hge];
        [|destruct (Z.lt_ge_cases x (Sfr fr + FRAME_SHADOW)) as [Hlt2|Hge2]].
      - left. p12_outU.
      - right. right. right. lia.
      - left. p12_outU. }
    split; [exact Hroa|]. split; [exact HAH1 | exact HST1]. }
  destruct (Z.eq_dec (g_n g - c0 (g_in g)) 0) as [Hz | Hz].
  - (* ---- s9 = 0: the exit to 0x82b04 ---- *)
    apply (p12_run regs (Z_to_bv 64 0x81c84) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x82b04 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 26 = getr regs 26 /\
         (exists sh16 : list byte,
            munch [(Sfr fr + 370, Sfr fr + 386)] mem mem' /\ wmono rsegs mem mem' /\
            bytes_at rsegs mem' (Sfr fr + 370) sh16 /\ length sh16 = 16%nat))
      (Post B APIf ra g)).
    + exact Hhalt.
    + unfold Regs6ss.mkR_of.
      eapply evt_cut.
      { eapply p12_evt_a with (SF := Sfr fr) (kb := kb) (junk := junk);
          [exact Ha0' | exact Hs10 | exact Hs3 | exact HKa | exact HKb | exact OKa | exact OKb
           | exact HS0 | exact HS1 | exact HCsh]. }
      intros ms' (a0' & a1' & a2' & s11' & m1 & sh16 & E1 & MU1 & WM1 & HB1 & HL1).
      subst ms'.
      eapply LE.evt_mono.
      { eapply p12_evt_b0. exact (eq_trans Hs9u Hz). }
      { intros ms'' E2. cbv beta in E2. subst ms''.
        eexists _, (Z_to_bv 64 0x82b04), m1. split; [reflexivity|].
        split; [reflexivity|].
        do 7 (split; [reflexivity|]).
        exists sh16. split; [exact MU1|]. split; [exact WM1|].
        split; [exact HB1 | exact HL1]. }
    + intros R pc' mem' regs' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 &
        sh16 & MU1 & WM1 & HB1 & HL1) Hreg Hmat.
      subst pc'.
      assert (E9r : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
      destruct (Hmove1 regs' mem' sh16 MU1 WM1 HB1 HL1
                  ltac:(rewrite Hreg; exact K2) ltac:(rewrite Hreg; exact K3) ltac:(rewrite Hreg; exact K4)
                  ltac:(rewrite Hreg; exact K8) E9r ltac:(rewrite Hreg; exact K19) ltac:(rewrite Hreg; exact K26))
        as (HFRA1 & HENT1 & _ & _ & _).
      assert (HFRA' : FRA B APIf ra g fr [] regs' mem' md')
        by exact (sl_fra_move B APIf ra g fr [] regs' regs' mem' md md' HFRA1
                    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat).
      assert (HENT' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
      assert (HOUR' : OURb g fr mem').
      { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU1 |].
        intros x Hx. rewrite OUR_length in Hx. apply Hout1app. apply Hfapp. lia. }
      assert (Hsp144' : spill regs' mem' 144 (fr + 2688)).
      { apply (p12_spill_keep regs regs' mem mem' [(Sfr fr + 370, Sfr fr + 386)] 144 (fr + 2688) A
                 Hsp144 HA9 ltac:(lia) ltac:(lia) ltac:(lia) E9r MU1).
        intros x Hx. apply Hout1app. unfold app_mem. right. lia. }
      assert (HAD2691' : addressable mem' (fr + 2691) 17).
      { apply (p12_addr_munch [(Sfr fr + 370, Sfr fr + 386)] mem mem' (fr + 2691) 17 HAD2691 MU1).
        intros i Hi. cbn [outside]. split; [|exact I]. intros Hc.
        pose proof (p12_sh_back fr (fr + 2691 + i) Hfrm8 ltac:(lia) Hc) as Hbad. lia. }
      assert (Hnm : bytes_at rsegs mem' (fr + 2688) (firstn 21 RcIdentModel.ID0)).
      { pose proof (p12_ba_sub mem (fr + 2688) RcIdentModel.ID0 0 21 HID
          ltac:(unfold RcIdentModel.ID0; rewrite repeat_length; unfold RcIdentModel.ID_SIZE; lia)) as Hsub.
        rewrite Z.add_0_r, skipn_O in Hsub.
        eapply fl_bytes; [exact Hsub | exact MU1 |].
        intros x Hx. apply Hout1app. apply Hfapp.
        rewrite length_firstn in Hx. unfold RcIdentModel.ID0 in Hx. rewrite repeat_length in Hx.
        unfold RcIdentModel.ID_SIZE in Hx. lia. }
      assert (HIexit : Inv_A82b04 B APIf ra g
                (mkCfg (mkst regs' (Z_to_bv 64 0x82b04) mem' (seg_rom rsegs)) md')).
      { exists regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA'|]. split; [exact HENT'|].
        split; [exact Hn|]. split; [exact HOUR'|]. split; [exact Hsp144'|].
        split.
        { exists (firstn 21 RcIdentModel.ID0). split; [exact Hnm|].
          split; [ rewrite length_firstn; unfold RcIdentModel.ID0; rewrite repeat_length;
                   unfold RcIdentModel.ID_SIZE; reflexivity |].
          vm_compute. intros HH; discriminate HH. }
        exact HAD2691'. }
      pose proof (Hexit0 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
  - (* ---- s9 <> 0: the frame-loop head at turn 0 ---- *)
    (* the input block exists on this arm: 0 < n - c0 with 0 <= c0, so f1_IN from PRO (f1_IN_of_PRO) *)
    assert (HF1IN : f1_IN g mem) by (apply (f1_IN_of_PRO g fr regs mem); [lia | exact HPRO]).
    (* the cells p12_evt_b1 stores into / loads from, built at mem and moved across W1 *)
    destruct (p12_cells mem (A + 48) (A + 136) (A + 48) 88 Hstk48 ltac:(lia) ltac:(cbn [Z.of_nat]; lia))
      as (junk1 & HCm48).
    assert (Hq192 : q64 mem (A + 192) (fragb fr))
      by exact (p12_spill_q64 regs mem 192 (fragb fr) A HSP192 HA9 ltac:(lia) ltac:(lia) ltac:(lia)).
    assert (Hq208 : q64 mem (A + 192 + 16) (fr + 448)).
    { replace (A + 192 + 16) with (A + 208) by lia.
      exact (p12_spill_q64 regs mem 208 (fr + 448) A Hsp208 HA9 ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (Hq248 : q64 mem (A + 192 + 56) (fr + 176)).
    { replace (A + 192 + 56) with (A + 248) by lia.
      exact (p12_spill_q64 regs mem 248 (fr + 176) A Hsp248 HA9 ltac:(lia) ltac:(lia) ltac:(lia)). }
    destruct (p12_q64_rw4 mem (A + 192) (A + 256) (A + 192) (fragb fr) (fr + 448) (fr + 176) Hstk192
                ltac:(lia) ltac:(lia) Hq192 Hq208 Hq248) as (junk0 & junk2 & HCm192).
    assert (HCm32 : rw_cells rsegs mem (A + 32) [C8 (Z_to_bv 64 (fr + 2880))]).
    { apply (p12_q64_rw1 mem (A + 32) (A + 40)); [exact Hstk32 | lia | lia |].
      exact (p12_spill_q64 regs mem 32 (fr + 2880) A Hsp32 HA9 ltac:(lia) ltac:(lia) ltac:(lia)). }
    apply (p12_run regs (Z_to_bv 64 0x81c84) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x81d40 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 26 = getr regs 26 /\ getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
         getr R 21 = Z_to_bv 64 0 /\
         (exists (m1 : word -> option byte) (sh16 bs88 : list byte),
            munch [(Sfr fr + 370, Sfr fr + 386)] mem m1 /\ wmono rsegs mem m1 /\
            bytes_at rsegs m1 (Sfr fr + 370) sh16 /\ length sh16 = 16%nat /\
            munch [(A + 48, A + 120); (A + 128, A + 136)] m1 mem' /\ wmono rsegs m1 mem' /\
            bytes_at rsegs mem' (A + 48) bs88 /\ length bs88 = 88%nat /\
            q64 mem' (A + 104) 0 /\ q64 mem' (A + 112) 0 /\
            q64 mem' (A + 128) (fr + 452) /\
            q64 mem' (A + 64) (fr + 180) /\ q64 mem' (A + 72) (fr + 186) /\
            q64 mem' (A + 80) (fragb fr + 15) /\ q64 mem' (A + 88) (fragb fr + 19) /\
            q64 mem' (A + 96) (fragb fr + 8) /\
            q64 mem' (A + 48) (fr + 2890) /\ q64 mem' (A + 56) (fr + 2889)))
      (Post B APIf ra g)).
    + exact Hhalt.
    + unfold Regs6ss.mkR_of.
      eapply evt_cut.
      { eapply p12_evt_a with (SF := Sfr fr) (kb := kb) (junk := junk);
          [exact Ha0' | exact Hs10 | exact Hs3 | exact HKa | exact HKb | exact OKa | exact OKb
           | exact HS0 | exact HS1 | exact HCsh]. }
      intros ms' (a0' & a1' & a2' & s11' & m1 & sh16 & E1 & MU1 & WM1 & HB1 & HL1).
      subst ms'.
      assert (HC1' : rw_cells rsegs m1 (A + 48) [CB 88 junk1]).
      { apply (rw_cells_transport rsegs [(Sfr fr + 370, Sfr fr + 386)] mem m1 (A + 48) _ HCm48 MU1 WM1).
        cbn [disjoint_from cells_size csize]. split; [right; lia | exact I]. }
      assert (HC2' : rw_cells rsegs m1 (A + 192)
                       [C8 (Z_to_bv 64 (fragb fr)); CB 8 junk0; C8 (Z_to_bv 64 (fr + 448)); CB 32 junk2;
                        C8 (Z_to_bv 64 (fr + 176))]).
      { apply (rw_cells_transport rsegs [(Sfr fr + 370, Sfr fr + 386)] mem m1 (A + 192) _ HCm192 MU1 WM1).
        cbn [disjoint_from cells_size csize]. split; [right; lia | exact I]. }
      assert (HC3' : rw_cells rsegs m1 (A + 32) [C8 (Z_to_bv 64 (fr + 2880))]).
      { apply (rw_cells_transport rsegs [(Sfr fr + 370, Sfr fr + 386)] mem m1 (A + 32) _ HCm32 MU1 WM1).
        cbn [disjoint_from cells_size csize]. split; [right; lia | exact I]. }
      eapply LE.evt_mono.
      { eapply p12_evt_b1 with (A := A) (f := fragb fr) (v := fr + 448) (o := fr + 176) (p := fr + 2880)
          (junk1 := junk1) (junk0 := junk0) (junk2 := junk2);
          [unfold rg in HA9; exact HA9 | intros H9; apply Hz; rewrite <- Hs9u; exact H9
           | exact HC1' | exact HC2' | exact HC3']. }
      { intros ms'' (a0'' & a1'' & m2 & bs88 & E2 & MU2 & WM2 & HB2 & HL2 & Q104 & Q112 & Q128 &
          Q64 & Q72 & Q80 & Q88 & Q96 & Q48 & Q56).
        eexists _, (Z_to_bv 64 0x81d40), m2. split; [exact E2|].
        split; [reflexivity|].
        do 10 (split; [reflexivity|]).
        exists m1, sh16, bs88.
        split; [exact MU1|]. split; [exact WM1|].
        split; [exact HB1|]. split; [exact HL1|].
        split; [exact MU2|]. split; [exact WM2|].
        split; [exact HB2|]. split; [exact HL2|].
        split; [exact Q104|]. split; [exact Q112|].
        split; [replace (fr + 452) with (fr + 448 + 4) by lia; exact Q128|].
        split; [replace (fr + 180) with (fr + 176 + 4) by lia; exact Q64|].
        split; [replace (fr + 186) with (fr + 176 + 10) by lia; exact Q72|].
        split; [exact Q80|]. split; [exact Q88|]. split; [exact Q96|].
        split; [replace (fr + 2890) with (fr + 2880 + 10) by lia; exact Q48 |
                replace (fr + 2889) with (fr + 2880 + 9) by lia; exact Q56]. }
    + intros R pc' mem' regs' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K22 & K25 & K21 &
        m1 & sh16 & bs88 & MU1 & WM1 & HB1 & HL1 & MU2 & WM2 & HB2 & HL2 & Q104 & Q112 & Q128 &
        Q64 & Q72 & Q80 & Q88 & Q96 & Q48 & Q56)
        Hreg Hmat.
      subst pc'.
      assert (E9r : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
      (* FRA / ENT across the shadow stores, at the unchanged registers *)
      destruct (Hmove1 regs m1 sh16 MU1 WM1 HB1 HL1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl)
        as (HFRA1 & HENT1 & Hroa1 & HAH1 & HST1).
      (* FRA across the spill stores (W2) *)
      assert (Hroa2 : ro_agree rsegs mem').
      { apply (p12_ro_keep [(A + 48, A + 120); (A + 128, A + 136)] m1 mem' Hroa1 MU2).
        intros x Hx. cbn [outside]. split; [lia | split; [lia | exact I]]. }
      destruct (p12_ah_spill g fr [] regs m1 mem' md A HFRA1 HA9 HAr MU2 WM2) as (HAH2 & Hown2 & HST2 & HSThi2).
      assert (Hstkwin1 : stk rsegs m1 (g_S g - AF.SLOT_STACK) (g_S g)).
      { apply (stk_transport_disjoint rsegs [(Sfr fr + 370, Sfr fr + 386)] mem m1
                 (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU1 WM1).
        cbn [disjoint_from]. split; [right; lia | exact I]. }
      assert (Hstkwin' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
      { destruct Hstkwin1 as (Hw0 & Hw1 & Hw). split; [exact Hw0|]. split; [exact Hw1|].
        intros x Hx. destruct (Hw x Hx) as (Hwv & b & Hb). split; [exact (WM2 (wa x) Hwv)|].
        destruct (Z_lt_le_dec x (A + 48)) as [Hl|Hg].
        - exists b. unfold mrd in *. rewrite (MU2 (wa x)); [exact Hb|]. rewrite wa_unsigned by lia.
          cbn [outside]. split; [lia | split; [lia | exact I]].
        - destruct (Z_lt_le_dec x (A + 136)) as [Hl2|Hg2].
          + destruct HB2 as (_ & _ & Hbb).
            pose proof (Hbb (Z.to_nat (x - (A + 48))) ltac:(rewrite HL2; lia)) as Hb'.
            rewrite Z2Nat.id in Hb' by lia.
            replace (A + 48 + (x - (A + 48))) with x in Hb' by lia.
            destruct (nth_error bs88 (Z.to_nat (x - (A + 48)))) as [b2|] eqn:En.
            * exists b2. exact Hb'.
            * exfalso. apply nth_error_None in En. rewrite HL2 in En. lia.
          + exists b. unfold mrd in *. rewrite (MU2 (wa x)); [exact Hb|]. rewrite wa_unsigned by lia.
            cbn [outside]. split; [lia | split; [lia | exact I]]. }
      assert (HrecK : FSREC fr m1 -> FSREC fr mem').
      { (* fsrec_stklo states munch / outside in Tac_slot's (UL) flavour; fr_munch_ul / fr_outside_lib bridge *)
        intros Hrec. eapply fsrec_stklo with (W := [(A + 48, A + 120); (A + 128, A + 136)]);
          [exact Hrec | exact HAH1 | exact (proj1 (fr_munch_ul _ m1 mem') MU2) |].
        intros x Hx Hnf. apply (proj2 (fr_outside_lib _ x)). rewrite HST1 in Hx.
        cbn [outside]. split; [lia | split; [lia | exact I]]. }
      assert (HFRA2 : FRA B APIf ra g fr [] regs' mem' md).
      { apply (sl_fr_cl B APIf ra empty FF g fr [] regs regs' m1 mem' md
                 [(A + 48, A + 120); (A + 128, A + 136)] HFRA1 MU2 WM2 Hroa2).
        - cbn [all_app]. repeat split; try exact I; intros a Ha; unfold app_mem; right; lia.
        - unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
            RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
            RT_AGLOB, RT_AGLOB_LEN.
          cbn [disjoint_from]. repeat split; first [left; lia | exact I].
        - exact HAH2.
        - exact HST2.
        - intros x Hx. cbn [outside]. split; [lia | split; [lia | exact I]].
        - intros x Hx. cbn [outside]. split; [lia | split; [lia | exact I]].
        - intros A' HA' HA'r x Hx. rewrite (p12_rg_inj regs 9 A' A HA' HA9 HA'r HAr) in Hx.
          cbn [outside]. split; [lia | split; [lia | exact I]].
        - intros x Hx. cbn [outside]. split; [lia | split; [lia | exact I]].
        - intros x Hx. cbn [outside]. split; [lia | split; [lia | exact I]].
        - intros A' HA' HA'r x Hx. rewrite (p12_rg_inj regs 9 A' A HA' HA9 HA'r HAr) in Hx.
          cbn [outside]. split; [lia | split; [lia | exact I]].
        - exact Hstkwin'.
        - exact HrecK.
        - rewrite Hreg; exact K2.
        - rewrite Hreg; exact K3.
        - rewrite Hreg; exact K4.
        - rewrite Hreg; exact K8.
        - exact E9r.
        - rewrite Hreg; exact K19.
        - rewrite Hreg; exact K26. }
      assert (HFRA' : FRA B APIf ra g fr [] regs' mem' md')
        by exact (sl_fra_move B APIf ra g fr [] regs' regs' mem' md md' HFRA2
                    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat).
      (* ENT across the spill stores (the window [S - SLOT_STACK, S) holds [A+48, A+136)), then the model step *)
      assert (HENT' : ENT APIf g [] mem' md').
      { assert (HENT2 : ENT APIf g [] mem' md).
        { eapply ent_store;
            [exact HENT1 | exact HFRA1
            | first [exact MU2 | exact (proj1 (fr_munch_ul _ m1 mem') MU2) | exact (proj2 (fr_munch_ul _ m1 mem') MU2)]
            | | exact HST2 | exact HSThi2
            | exact (fun a _ Ho => proj2 (Hown2 a) Ho)].
          intros x Hx. destruct (Z_lt_le_dec x (A + 48)) as [Hl|Hg]; [ left; p12_outU |].
          destruct (Z_lt_le_dec x (A + 136)) as [Hl2|Hg2]; [ right; left; lia | left; p12_outU ]. }
        eapply ent_mat; [exact HENT2 | exact Hmat]. }
      (* the facts the exit reads, carried through W1 then W2 *)
      assert (HkeepA : forall (off v0 : Z), 0 <= off <= 272 ->
                 (forall x, A + off <= x < A + off + 8 -> outside [(A + 48, A + 120); (A + 128, A + 136)] x) ->
                 spill regs mem off v0 -> spill regs' mem' off v0).
      { intros off v0 Hoff HWx Hsp.
        assert (Hm1 : spill regs m1 off v0).
        { apply (p12_spill_keep regs regs mem m1 [(Sfr fr + 370, Sfr fr + 386)] off v0 A
                   Hsp HA9 ltac:(lia) ltac:(lia) ltac:(lia) eq_refl MU1).
          intros x Hx. apply Hout1app. unfold app_mem. right. lia. }
        apply (p12_spill_keep regs regs' m1 mem' [(A + 48, A + 120); (A + 128, A + 136)] off v0 A
                 Hm1 HA9 ltac:(lia) ltac:(lia) ltac:(lia) E9r MU2).
        exact HWx. }
      assert (Hkeepfr : forall a (bs : list byte), fr <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
                 bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs).
      { intros a bs Ha1 Ha2 Hb.
        assert (Hb1 : bytes_at rsegs m1 a bs).
        { eapply fl_bytes; [exact Hb | exact MU1 |]. intros x Hx. apply Hout1app. apply Hfapp. lia. }
        eapply fl_bytes; [exact Hb1 | exact MU2 |].
        intros x Hx. cbn [outside]. split; [lia | split; [lia | exact I]]. }
      assert (HOUR' : OURb g fr mem')
        by (unfold OURb in *; apply Hkeepfr; [lia | rewrite OUR_length; lia | exact HOUR]).
      assert (HID' : IDBe g fr RcIdentModel.ID0 mem').
      { unfold IDBe in *. apply Hkeepfr; [lia | | exact HID].
        unfold RcIdentModel.ID0. rewrite repeat_length. unfold RcIdentModel.ID_SIZE. lia. }
      assert (HFG' : FGBe g fr z72 mem').
      { unfold FGBe in *. apply Hkeepfr; [lia | | exact HFG]. rewrite z72_length. lia. }
      assert (HAD2624' : addressable mem' (fr + 2624) 6).
      { assert (Hm1 : addressable m1 (fr + 2624) 6).
        { apply (p12_addr_munch [(Sfr fr + 370, Sfr fr + 386)] mem m1 (fr + 2624) 6 HAD2624 MU1).
          intros i Hi. cbn [outside]. split; [|exact I]. intros Hc.
          pose proof (p12_sh_back fr (fr + 2624 + i) Hfrm8 ltac:(lia) Hc) as Hbad. lia. }
        apply (sl_addr_keep m1 mem' [(A + 48, A + 120); (A + 128, A + 136)] (fr + 2624) 6 Hm1 MU2).
        cbn [all_app]. repeat split; try exact I; intros a Ha; unfold app_mem; right; lia. }
      assert (Hstkfr' : stk rsegs mem' fr (fr + FRAME_BYTES)).
      { assert (Hm1 : stk rsegs m1 fr (fr + FRAME_BYTES)).
        { apply (stk_transport_disjoint rsegs [(Sfr fr + 370, Sfr fr + 386)] mem m1 fr (fr + FRAME_BYTES)
                   Hstkfr MU1 WM1). cbn [disjoint_from]. split; [|exact I].
          destruct Hcase as [Hc|Hc]; [left | right]; unfold LOWMEM_END, HIGHMEM_BEG in *; lia. }
        apply (stk_transport_disjoint rsegs [(A + 48, A + 120); (A + 128, A + 136)] m1 mem' fr (fr + FRAME_BYTES)
                 Hm1 MU2 WM2). cbn [disjoint_from]. split; [left; lia | split; [left; lia | exact I]]. }
      assert (HF1IN' : f1_IN g mem').
      { destruct HF1IN as (HI & HAddr & HBytes).
        assert (Hblk : 0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g ->
                  app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
        { intros Hgn0 x Hx.
          destruct (p12_laws_blocks ([] ++ g_H g) mem md (g_p g) (g_n g) HAH (HI Hgn0)) as (Hpn & Hbody).
          destruct (Hbody x Hx) as (Hap & _). split; [exact Hap | lia]. }
        split; [exact HI|].
        split.
        { assert (Hm1 : addressable m1 (g_p g) (g_n g)).
          { apply (p12_addr_munch [(Sfr fr + 370, Sfr fr + 386)] mem m1 (g_p g) (g_n g) HAddr MU1).
            intros i Hi. cbn [outside]. split; [|exact I]. intros Hc.
            assert (Hgp0 : 0 <= g_p g) by (destruct HAddr as (H0 & _); exact H0).
            pose proof (p12_sh_back fr (g_p g + i) Hfrm8 ltac:(lia) Hc) as Hbad.
            apply (p12_in_fr_dj g fr [] regs mem md HFRA (HI ltac:(lia)) i ltac:(lia)). lia. }
          apply (sl_addr_keep m1 mem' [(A + 48, A + 120); (A + 128, A + 136)] (g_p g) (g_n g) Hm1 MU2).
          cbn [all_app]. repeat split; try exact I; intros a Ha; unfold app_mem; right; lia. }
        assert (Hm1 : bytes_at rsegs m1 (g_p g) (g_in g)).
        { eapply fl_bytes; [exact HBytes | exact MU1 |].
          intros x Hx. rewrite <- g_n_len in Hx. apply Hout1app.
          exact (proj1 (Hblk ltac:(lia) x Hx)). }
        eapply fl_bytes; [exact Hm1 | exact MU2 |].
        intros x Hx. rewrite <- g_n_len in Hx.
        destruct (Hblk ltac:(lia) x Hx) as (_ & Hxs).
        cbn [outside]. split; [lia | split; [lia | exact I]]. }
      assert (Hsp40' : spill regs' mem' 40 (fr + 32))
        by (apply (HkeepA 40 (fr + 32) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp40]).
      assert (Hsp120' : spill regs' mem' 120 (fr + 160))
        by (apply (HkeepA 120 (fr + 160) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp120]).
      assert (Hsp136' : spill regs' mem' 136 (fr + 128))
        by (apply (HkeepA 136 (fr + 128) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp136]).
      assert (Hsp160' : spill regs' mem' 160 (fr + 528))
        by (apply (HkeepA 160 (fr + 528) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp160]).
      assert (Hsp168' : spill regs' mem' 168 (fr + 2624))
        by (apply (HkeepA 168 (fr + 2624) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp168]).
      assert (Hsp176' : spill regs' mem' 176 (fr + 64))
        by (apply (HkeepA 176 (fr + 64) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp176]).
      assert (Hsp208' : spill regs' mem' 208 (fr + 448))
        by (apply (HkeepA 208 (fr + 448) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp208]).
      assert (Hsp248' : spill regs' mem' 248 (fr + 176))
        by (apply (HkeepA 248 (fr + 176) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp248]).
      assert (Hsp144' : spill regs' mem' 144 (fr + 2688))
        by (apply (HkeepA 144 (fr + 2688) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp144]).
      (* PRO's spills 184 / 256 / 264 / 272 and (v1.9, position 16) [A + 32] = fr + 2880, and FLC's [A + 192]
         = fragb fr (P12 reads them, writes none) *)
      assert (Hsp184' : spill regs' mem' 184 (fr + 336))
        by (apply (HkeepA 184 (fr + 336) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp184]).
      assert (Hsp256' : spill regs' mem' 256 (fr + 256))
        by (apply (HkeepA 256 (fr + 256) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp256]).
      assert (Hsp264' : spill regs' mem' 264 (fr + 304))
        by (apply (HkeepA 264 (fr + 304) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp264]).
      assert (Hsp272' : spill regs' mem' 272 (fr + 272))
        by (apply (HkeepA 272 (fr + 272) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp272]).
      assert (Hsp32' : spill regs' mem' 32 (fr + 2880))
        by (apply (HkeepA 32 (fr + 2880) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact Hsp32]).
      assert (Hsp192' : spill regs' mem' 192 (fragb fr))
        by (apply (HkeepA 192 (fragb fr) ltac:(lia)); [intros x Hx; cbn [outside]; split; [lia | split; [lia | exact I]] | exact HSP192]).
      (* the record ranges keep their shadow bytes S(fr) + 346 .. 354 / 336 .. 340 and first.sroa.7's
         S(fr) + 360 .. 364 (W1 writes S(fr) + 370 .. 385, W2 is application memory) *)
      assert (HADF' : addressable mem' (fragb fr) 72).
      { unfold fragb in HADF |- *.
        assert (Hm1 : addressable m1 (fr + 2768) 72).
        { apply (p12_addr_munch [(Sfr fr + 370, Sfr fr + 386)] mem m1 (fr + 2768) 72 HADF MU1).
          intros i Hi. cbn [outside]. split; [|exact I]. intros Hc.
          pose proof (p12_sh_back fr (fr + 2768 + i) Hfrm8 ltac:(lia) Hc) as Hbad. lia. }
        apply (sl_addr_keep m1 mem' [(A + 48, A + 120); (A + 128, A + 136)] (fr + 2768) 72 Hm1 MU2).
        cbn [all_app]. repeat split; try exact I; intros a Ha; unfold app_mem; right; lia. }
      assert (HADI' : addressable mem' (fr + 2688) 38).
      { assert (Hm1 : addressable m1 (fr + 2688) 38).
        { apply (p12_addr_munch [(Sfr fr + 370, Sfr fr + 386)] mem m1 (fr + 2688) 38 HADI MU1).
          intros i Hi. cbn [outside]. split; [|exact I]. intros Hc.
          pose proof (p12_sh_back fr (fr + 2688 + i) Hfrm8 ltac:(lia) Hc) as Hbad. lia. }
        apply (sl_addr_keep m1 mem' [(A + 48, A + 120); (A + 128, A + 136)] (fr + 2688) 38 Hm1 MU2).
        cbn [all_app]. repeat split; try exact I; intros a Ha; unfold app_mem; right; lia. }
      assert (HAD2691' : addressable mem' (fr + 2691) 17).
      { assert (Hm1 : addressable m1 (fr + 2691) 17).
        { apply (p12_addr_munch [(Sfr fr + 370, Sfr fr + 386)] mem m1 (fr + 2691) 17 HAD2691 MU1).
          intros i Hi. cbn [outside]. split; [|exact I]. intros Hc.
          pose proof (p12_sh_back fr (fr + 2691 + i) Hfrm8 ltac:(lia) Hc) as Hbad. lia. }
        apply (sl_addr_keep m1 mem' [(A + 48, A + 120); (A + 128, A + 136)] (fr + 2691) 17 Hm1 MU2).
        cbn [all_app]. repeat split; try exact I; intros a Ha; unfold app_mem; right; lia. }
      assert (HAD2880' : addressable mem' (fr + 2880) 35).
      { assert (Hm1 : addressable m1 (fr + 2880) 35).
        { apply (p12_addr_munch [(Sfr fr + 370, Sfr fr + 386)] mem m1 (fr + 2880) 35 HAD2880 MU1).
          intros i Hi. cbn [outside]. split; [|exact I]. intros Hc.
          pose proof (p12_sh_back fr (fr + 2880 + i) Hfrm8 ltac:(lia) Hc) as Hbad. lia. }
        apply (sl_addr_keep m1 mem' [(A + 48, A + 120); (A + 128, A + 136)] (fr + 2880) 35 Hm1 MU2).
        cbn [all_app]. repeat split; try exact I; intros a Ha; unfold app_mem; right; lia. }
      assert (HA9' : rg regs' 9 A) by (unfold rg; rewrite E9r; exact HA9).
      assert (HIexit : Inv_A81d40_at B APIf ra g 0%nat
                (mkCfg (mkst regs' (Z_to_bv 64 0x81d40) mem' (seg_rom rsegs)) md')).
      { exists regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA'|]. split; [exact HENT'|].
        split; [exact Hn|].
        split.
        { (* LI g fr 0 *)
          split.
          { split; [lia|]. split; [unfold rg; rewrite Hreg; exact K21 | exact HOUR']. }
          split.
          { split; [exact Hc0|].
            split; [unfold rg in *; rewrite Hreg, K22; exact Hr22 | unfold rg in *; rewrite Hreg, K25; exact Hr25]. }
          split.
          { replace (t_left (g_in g) 0) with (g_n g - c0 (g_in g)) by reflexivity. lia. }
          split.
          { split; [exact HID' | exact p12_id_ok]. }
          split.
          { split; [exact HFG' | exact p12_frag_ok]. }
          (* FSj g fr 0 = FSb (fs0) (z72), v1.9: [A+104] = have = 0, [A+112] = n = 0, the body fs_body fs0 = []
             at fr + 2880, first.sroa.7's 35 bytes addressable, FI *)
          split; [exists A; split; [exact HA9' | exact Q104]|].
          split; [exists A; split; [exact HA9' | exact Q112]|].
          split; [exact (p12_ba_nil mem' (fr + 2880) ltac:(lia))|].
          split; [exact HAD2880'|].
          exact p12_FI. }
        split.
        { (* FLSH g 0 fr: PRO (pushes 13 / 14), then the loop part *)
          split.
          { destruct HF1IN' as (HI' & HAddr' & HBytes').
            split; [exact Hsp40'|]. split; [exact Hsp120'|]. split; [exact Hsp136'|].
            split; [exact Hsp160'|]. split; [exact Hsp168'|]. split; [exact Hsp176'|].
            split; [exact Hsp208'|]. split; [exact Hsp248'|].
            split; [exact HAD2624'|]. split; [exact HBytes'|].
            split; [intros Hgn; split; [exact (HI' Hgn) | exact HAddr']|].
            split; [exact Hsp184'|]. split; [exact Hsp256'|]. split; [exact Hsp264'|].
            split; [exact Hsp272' | exact Hsp32']. }
          split; [exists A; split; [exact HA9' | exact Q128]|].
          split; [exact Hstkfr'|]. split; [exact Hsp144' | exact HAD2691']. }
        split; [exact HF1IN'|]. split; [exact Hsp248'|].
        (* FLC (v1.9, 14 conjuncts): A4's spills (via PRO), [A + 192] = fragb fr, P12's own [A + 80 / 88 / 96]
           (from [A + 192]), [A + 72 / 64] (from [A + 248] = fr + 176), the two record ranges, and the NEW-only
           [A + 56 / 48] = fr + 2889 / fr + 2890 (from [A + 32] = fr + 2880) *)
        split; [exact Hsp256'|]. split; [exact Hsp184'|]. split; [exact Hsp192'|].
        split; [exists A; split; [exact HA9' | exact Q80]|].
        split; [exists A; split; [exact HA9' | exact Q88]|].
        split; [exists A; split; [exact HA9' | exact Q96]|].
        split; [exact Hsp272'|]. split; [exact Hsp264'|].
        split; [exact HADF'|]. split; [exact HADI'|].
        split; [exists A; split; [exact HA9' | exact Q72]|].
        split; [exists A; split; [exact HA9' | exact Q64]|].
        split; [exists A; split; [exact HA9' | exact Q56] | exists A; split; [exact HA9' | exact Q48]]. }
      pose proof (Hexit1 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
