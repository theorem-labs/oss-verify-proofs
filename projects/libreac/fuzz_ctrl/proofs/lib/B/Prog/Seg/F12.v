(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names and numbers changed; 1592 of its 1709 lines of code are new or changed and 894 lines of the source are left out. *)
(* Segments F12 and F12_298 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0; v1.8
   0x82294-0x822cc, segment table rows S_F12 / S_F12_298: CHANGED, the new `ld s5,208(s1)` at 0x82334 in place of
   `ld s7,240(s1)`, register renaming s7 -> s5) = 0x82304-0x8233c, 15 instructions ending with the call of
   __asan_memcpy (0x52164) at 0x8233c; FAIL branch 0x82304, no trap row, no shadow row.  Two official cuts enter
   the run: 0x82304 (the return of reac_identity_ingest at 0x82300, Inv_B82304_at; seg_F12 runs through 0x82308,
   whose cut states the ir-false arm and so does not hold here) and 0x82308 (F10's ir-false exit, Inv_B82308_at;
   seg_F12_298).  Both leave at 0x82340, the entry of F13 (Inv_B82340_at).  The two lemmas share f12_at, which runs
   from either pc and rebuilds the exit cut there.

   The branch `bltz a0,82fa4` at 0x82304 is not taken: the ingest result the entry cut carries is non-negative.
   The nine stores 0x82308-0x82328 write 0 to the bytes 42..50 of s3 = S(fr) = (fr >> 3) + 0x7fff8000, that is to
   the shadow bytes of [fr + 336, fr + 408): they mark those 72 frame bytes usable, which is what makes the copy's
   destination addressable.  The copy at 0x8233c is __asan_memcpy([s1+200] = fr + 336, [s1+208] = fragb fr, 72); it
   fills the before-call copy of the record that F14's compare reads, and `ld s5,208(s1)` leaves the record pointer
   in s5 for F13.  With both ranges addressable the error path of the copy is not reached.

   The write set of the whole segment is [S(fr) + 42, S(fr) + 51) (the nine shadow bytes), [fr + 336, fr + 408)
   (the copy's destination) and the copy's own stack window [sp - 2224, sp).  FRA moves across it with the local
   fra_run (Tac_slot's sl_fr_run / sl_fr_meta take either the frame body or its shadow, never the callee window as
   well): RT by RT_meta_write, the heap invariant and the stack-low value by lw_store (real arm) or
   Tac_fs.a_fs_ok_store_AH (side arm, where the frame and its shadow both belong to the side stack for frames), and
   the FRAME_SHADOW-byte frame-shadow list is rebuilt from the nine new bytes and the kept rest.  The copy's contract
   (lib/B/Prog/asan_memcpy_c.v) is a Section Hypothesis; the run lifts through AsanLift.evt_SR_canon_lazy
   (f12_run_lib).

   The exit's record bundle FRBA is built here: from FRA (the spill base and its window, the frame's place, the
   block's place below stklo), FM ([A+312] and s8 = k), FS9 ([A+248] = 1 - sum_ok), the Phi bytes under
   `50 <= flen g j`, FPS (the parse struct at fr + 176 and its 36 addressable bytes), F272 ([A+272] in the t_8819
   form) and FLI's spills [A+96] = fr + 180 / [A+112] = fr + 186, whose six bytes are the struct's fields 4 .. 9 and
   10 .. 15, that is the record's bytes 6 .. 11 and 0 .. 5 (RcParse.ctrlparse_fields).  FRB's first conjunct (the
   local `first` [fr + 2880, fr + 2920) app memory above GT) is FRA's frame placement (fra_app).  No local cut. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcFrag RcFragLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv asan_memcpy_c
  reac_ctrl_identity_fragment_c RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Import ListNotations.
(* Tac_ro's chain loads other modules named YK11 (lib.Reusable.YK11), so the short name would resolve to that copy;
   this file's registers and getr must be image B's. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.
(* The v1.9 frame size and its shadow length are the named constants FRAME_BYTES = 3136 and FRAME_SHADOW = 392 of
   SlotInv.v; every lia of this file gets their values. *)
Local Ltac lia := pose proof FRAME_BYTES_val; pose proof FRAME_SHADOW_val; Lia.lia.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.

(* The byte a `sb zero` writes, in whichever of its two forms the step tactic leaves. *)
Ltac f12_zb := first [ reflexivity | cbn; reflexivity | vm_compute; reflexivity ].

(* Proof speed (common.md:324-335): `lia` case-splits every disjunction and `mod` fact in the context, so the
   address-separation goals below hide the context's disjunctions and keep only the facts the goal is about. *)
Local Definition rs_hold (A : Prop) : Prop := A.
Local Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Local Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.

(* Fold the engine-form stack pointer `bv_unsigned (reg_get regs 2)` back to AC.aspZ regs (as
   lib/B/Prog/Seg/F13.v fold_sp). *)
Ltac fold_sp regs :=
  match goal with |- context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) end.

(* ---- the record's post bytes keep their length in every fragment class, so the turn's record is 72 bytes and
   its buffer 50 (copied from lib/B/Prog/Seg/F13.v, which this file cannot import while F13 is being re-fitted to
   the push-5c cuts). ---- *)

Lemma rf_first_length : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold fg_first, fg_body.
  rewrite !length_app, length_skipn, (rf_bsl_length g 6 6), (rf_bsl_length g 27 (fg_n g)) by lia.
  cbn [length]. lia.
Qed.

Lemma fr_fg_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (H & _). destruct H as (H & Hn2). destruct H as (_ & Hn1).
  apply Z.leb_le in Hn1. apply Z.leb_le in Hn2. lia.
Qed.

Lemma keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H.
  destruct H as (_ & H). apply Z.leb_le in H. lia.
Qed.

Lemma fg_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. apply rf_first_length; [exact HL | exact HG | apply (fr_fg_n len); exact FR].
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply rf_clear_length; exact HL].
    destruct (fg_close st g); cbn [negb fg_next]; apply rf_clear_length, rf_fg_join_length;
      solve [exact HL | exact HG | apply (fr_fg_n len); exact FR | apply keep_T; exact KEEP].
Qed.

Lemma t_g_length : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

Lemma t_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (fg_next_length 1 1 1 1 1); solve [exact IH | apply t_g_length].
Qed.

(* ---- the memory helpers of lib/B/Prog/Seg/F13.v, copied for the same reason. ---- *)

Lemma outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn [outside]; intros x; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [right; intros (C & _); lia | left; split; [lia | exact H]].
Qed.

Lemma ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (HA & HL & H) Hx.
  assert (Hi : (Z.to_nat (x - A) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (x - A)) Hi) as HH. rewrite Z2Nat.id in HH by lia.
  replace (A + (x - A)) with x in HH by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E; [exists b; exact HH|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* A stack window survives a run with write set W: outside W the bytes are unchanged, inside W the caller shows
   the post memory is readable. *)
Lemma stk_keep : forall W m m' lo hi,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) ->
  stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HR.
  split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  split; [apply WM; exact Hv|].
  destruct (outside_dec W a) as [Ho|Ho].
  - exists b. unfold mrd in *. rewrite (MU (wa a)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
  - exact (HR a Ha Ho).
Qed.

(* ---- shadow-byte arithmetic: shadow_addr is monotone, and on an 8-aligned base it turns a frame offset into a
   shadow index. ---- *)

Lemma f12_sh_ge : forall fr x c, fr mod 8 = 0 -> 0 <= fr -> fr + 8 * c <= x -> Sfr fr + c <= shadow_addr x.
Proof. intros fr x c H8 Hfr Hx. unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. Qed.

Lemma f12_sh_lt : forall fr x c, fr mod 8 = 0 -> 0 <= fr -> 0 <= x -> x < fr + 8 * c -> shadow_addr x < Sfr fr + c.
Proof. intros fr x c H8 Hfr Hx0 Hx. unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. Qed.

(* Backwards: a byte whose shadow byte is one of the nine the segment writes lies in [fr + 336, fr + 408), that is
   inside the frame body. *)
Lemma f12_sh_back : forall fr x, fr mod 8 = 0 -> 0 <= fr -> 0 <= x ->
  Sfr fr + 42 <= shadow_addr x < Sfr fr + 51 -> fr + 336 <= x < fr + 408.
Proof. intros fr x H8 Hfr Hx0 Hx. unfold Sfr, shadow_addr, ASAN_K in Hx. Z.div_mod_to_equations. lia. Qed.

(* A one-interval write set misses every address below it or at or above its top (as lib/B/Prog/Seg/F14.v out1). *)
Lemma f12_out1 : forall lo hi x, (x < lo \/ hi <= x) -> Frame.outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn [Frame.outside]. split; [lia | exact I]. Qed.

(* A carried bytes_at of 8 bytes in the form the load tactic consumes (as lib/B/Prog/Seg/F14.v rd8). *)
Lemma f12_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_read rsegs m a bs 0 8 H ltac:(lia) ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

(* The bytes of a CB cell, and the cell of a writable byte range. *)
Lemma f12_cb_bytes : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof.
  intros m a n bs ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

Lemma f12_cb_rw : forall m a n bs, bytes_at rsegs m a bs -> length bs = n ->
  wr_at rsegs m a (Z.of_nat n) -> rw_cells rsegs m a [CB n bs].
Proof.
  intros m a n bs Hb Hl Hw. split.
  - split; [cbn; split; [exact Hl | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* The spill base of a `spill` fact is the s1 of the cut: the cell it names lies in [0, 2^64), and two values of
   one register agree modulo 2^64. *)
Lemma f12_spill_base : forall regs A A' m off v,
  rg regs 9 A -> rg regs 9 A' -> 0 <= A < APPMEM_END -> 0 <= off <= 440 -> q64 m (A' + off) v -> A' = A.
Proof.
  intros regs A A' m off v HA HA' HAb Hoff Hq.
  pose proof (rg_eq64 _ _ _ _ HA' HA) as Hm.
  unfold q64, bytes_at in Hq. destruct Hq as (Hq0 & Hq1 & _).
  rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  unfold APPMEM_END in HAb. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* A spill of the save area survives a run whose write set misses its cell. *)
Lemma f12_spill_keep : forall regs regs' m m' W A off v,
  rg regs 9 A -> getr regs' 9 = getr regs 9 -> 0 <= A < APPMEM_END -> 0 <= off <= 440 ->
  spill regs m off v -> munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v H9 E9 HAb Hoff (A3 & HA3 & Hq) MU Hout.
  pose proof (f12_spill_base regs A A3 m off v H9 HA3 HAb Hoff Hq) as EA. subst A3.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply Hout. lia.
Qed.

(* addressable survives writes that miss the shadow bytes of its own range (as
   lib/B/Prog/reac_ctrl_classify_box_frame.v acl_addr_munch). *)
Lemma f12_addr_munch : forall W m m' p n, addressable m p n -> Frame.munch W m m' ->
  (forall i, 0 <= i < n -> Frame.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as His.
  assert (Hr : 0 <= shadow_addr (p + i) < 2 ^ 64)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in His; lia).
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. exact (HW i Hi).
Qed.

(* Nine zero shadow bytes at (D >> 3) + 0x7fff8000 make the 72 bytes at D addressable: every byte's shadow byte is
   one of the nine, and a zero shadow byte passes the check at every offset of its granule. *)
Lemma f12_addr72 : forall m D K,
  0 <= D -> D + 72 <= APPMEM_END -> D mod 8 = 0 -> D / 8 + ASAN_K = K ->
  (forall t, 0 <= t < 72 -> app_mem (D + t)) ->
  (forall k, 0 <= k < 9 -> b8 m (K + k) 0) ->
  addressable m D 72.
Proof.
  intros m D K HD0 HDE HD8 HDK Happ Hsh.
  split; [exact HD0|]. split; [lia|]. split; [exact HDE|].
  intros i Hi. split; [apply Happ; lia|].
  assert (Hk : 0 <= i / 8 < 9) by (Z.div_mod_to_equations; lia).
  destruct (Hsh (i / 8) Hk) as (Hb0 & Hb1 & Hb2).
  pose proof (Hb2 0%nat ltac:(cbn; lia)) as Hrd.
  change (Z.of_nat 0) with 0 in Hrd. rewrite Z.add_0_r in Hrd. cbn [nth_error] in Hrd.
  assert (Esh : shadow_addr (D + i) = K + i / 8).
  { unfold shadow_addr. rewrite <- HDK.
    replace (D + i) with (i + (D / 8) * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. lia. }
  exists (Z_to_bv 8 0). rewrite Esh. split; [exact Hrd|].
  unfold shadow_ok. left. first [reflexivity | vm_compute; reflexivity].
Qed.

(* One shadow store: the byte it wrote reads back as zero; a later store at another address keeps it. *)
Lemma f12_wsame : forall m a (bs : list byte), bs = [Z_to_bv 8 0] -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  b8 (write_to_mem m (wa a) bs) a 0.
Proof.
  intros m a bs -> Ha Hl. unfold b8. apply bytes_at_write_same; [exact Ha | cbn [length]; lia].
Qed.

Lemma f12_wother : forall m a (bs : list byte) c v, length bs = 1%nat -> b8 m c v ->
  0 <= a -> a + 1 <= 2 ^ 64 -> (c + 1 <= a \/ a + 1 <= c) -> b8 (write_to_mem m (wa a) bs) c v.
Proof.
  intros m a bs c v Hl Hb Ha Hal Hd. unfold b8 in *.
  apply (bytes_at_write_other rsegs m a bs c [Z_to_bv 8 v] Hb); [exact Ha | rewrite Hl; cbn; lia|].
  rewrite Hl. cbn [length]. lia.
Qed.

(* Build a list from a function defined on [0, n) (as lib/B/Prog/Seg/F17.v ex_list). *)
Lemma f12_ex_list : forall (f : nat -> option byte) n, (forall i, (i < n)%nat -> f i <> None) ->
  exists l, length l = n /\ forall i, (i < n)%nat -> f i = nth_error l i.
Proof.
  intros f n. induction n as [|n IH]; intros H.
  - exists []. split; [reflexivity|]. intros i Hi. lia.
  - assert (H' : forall i, (i < n)%nat -> f i <> None) by (intros i Hi; apply H; lia).
    destruct (IH H') as (l & Hl & Hf).
    destruct (f n) as [b|] eqn:Eb; [|exfalso; exact (H n ltac:(lia) Eb)].
    exists (l ++ [b]). split; [rewrite length_app, Hl; cbn; lia|].
    intros i Hi. destruct (Nat.lt_ge_cases i n) as [Hlt|Hge].
    + rewrite nth_error_app1 by lia. exact (Hf i Hlt).
    + assert (Ei : i = n) by lia. subst i.
      rewrite nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. cbn. exact Eb.
Qed.

(* A byte-backed stack range holds a writable CB cell of any sub-range (the copy's destination at fr + 336). *)
Lemma f12_stk_cb : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists bs, length bs = n /\ rw_cells rsegs m a [CB n bs].
Proof.
  intros m lo hi a n (H0 & H1 & H) Ha Hn.
  destruct (f12_ex_list (fun i => mrd rsegs m (wa (a + Z.of_nat i))) n) as (bs & Hl & Hf).
  { intros i Hi. destruct (H (a + Z.of_nat i) ltac:(lia)) as (_ & b & Hb). rewrite Hb. discriminate. }
  exists bs. split; [exact Hl|].
  apply f12_cb_rw; [| exact Hl |].
  - split; [lia|]. split; [rewrite Hl; lia|]. intros i Hi. apply Hf. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. destruct (H (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* ---- Byte-level readers of a carried byte range, and the model facts the exit's FRB needs. ---- *)
(* A sub-range of a carried byte range (as lib/B/Prog/Seg/F11.v f11_sub). *)
Lemma f12_nth_sub : forall (l : list byte) k n i, (i < n)%nat ->
  nth_error (firstn n (skipn k l)) i = nth_error l (k + i).
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l n i Hi.
  - cbn [skipn Nat.add]. revert n i Hi. induction l as [|x l IHl]; intros n i Hi.
    + rewrite firstn_nil. destruct i; reflexivity.
    + destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth_error]. apply IHl. lia.
  - destruct l as [|x l].
    + rewrite skipn_nil, firstn_nil. destruct i; reflexivity.
    + cbn [skipn Nat.add nth_error]. apply IH. exact Hi.
Qed.
Lemma f12_sub : forall m a (bs : list byte) k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n (H0 & H1 & H) Hkn.
  assert (HL : length (firstn n (skipn k bs)) = n) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite HL; lia|].
  intros i Hi. rewrite HL in Hi. rewrite f12_nth_sub by exact Hi.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  apply H. lia.
Qed.
(* One byte, and two consecutive bytes, of a carried byte range. *)
Lemma f12_zb : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma f12_ubv : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H. exact H. Qed.
Lemma f12_b8_of : forall m a (bs : list byte) k, bytes_at rsegs m a bs -> (k < length bs)%nat ->
  b8 m (a + Z.of_nat k) (bv_unsigned (nth k bs cp_z)).
Proof.
  intros m a bs k (H0 & H1 & H) Hk. unfold b8. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. cbn [nth_error]. rewrite f12_zb.
  rewrite (H k Hk). apply nth_error_nth'. exact Hk.
Qed.
Lemma f12_b2_of : forall m a (bs : list byte) k, bytes_at rsegs m a bs -> (k + 2 <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) [nth k bs cp_z; nth (S k) bs cp_z].
Proof.
  intros m a bs k (H0 & H1 & H) Hk. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  assert (Ei : i = 0%nat \/ i = 1%nat) by lia. destruct Ei as [-> | ->].
  - change (Z.of_nat 0) with 0. rewrite Z.add_0_r. cbn [nth_error].
    rewrite (H k ltac:(lia)). apply nth_error_nth'. lia.
  - change (Z.of_nat 1) with 1. cbn [nth_error].
    replace (a + Z.of_nat k + 1) with (a + Z.of_nat (S k)) by lia.
    rewrite (H (S k) ltac:(lia)). apply nth_error_nth'. lia.
Qed.
(* The u16 of two carried bytes (as lib/B/Prog/Seg/F11.v f11_le2). *)
Lemma f12_le2 : forall b0 b1 : byte,
  [b0; b1] = le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1)).
Proof.
  intros b0 b1. pose proof (f12_ubv b0) as R0. pose proof (f12_ubv b1) as R1.
  unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace ((bv_unsigned b0 + 256 * bv_unsigned b1) / 256) with (bv_unsigned b1)
    by (rewrite Z.mul_comm, Z.div_add, Z.div_small by lia; lia).
  f_equal; [|f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N];
    change (2 ^ 8) with 256.
  - rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia. reflexivity.
  - rewrite Z.mod_small by lia. reflexivity.
Qed.
(* A 6-byte range compares equal with itself. *)
Lemma f12_memcmp_self : forall (bs : list byte) n, (n <= length bs)%nat -> SF.memcmp_model bs bs n = Some 0.
Proof.
  intros bs n. revert bs. induction n as [|n IH]; intros [|b bs] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.
(* The parse struct's three field groups the F13 / F14 compares read: bytes 10 .. 15 are the record's bytes
   0 .. 5, bytes 4 .. 9 are its bytes 6 .. 11, and bytes 20 / 21 are its bytes 14 / 15 (RcParse.cp_struct). *)
Lemma f12_B_fields : forall (G : list byte), (16 <= length G)%nat ->
  firstn 6 (skipn 10 (cp_struct G (cp_kind G))) = firstn 6 G /\
  firstn 6 (skipn 4 (cp_struct G (cp_kind G))) = firstn 6 (skipn 6 G) /\
  firstn 2 (skipn 20 (cp_struct G (cp_kind G))) = [cp_b G 14; cp_b G 15].
Proof.
  intros G HL. do 16 (destruct G as [|? G]; [cbn in HL; lia|]).
  split; [reflexivity|]. split; reflexivity.
Qed.
(* The shadow byte of phi + c (7 <= c <= 42) is 0 when the block (phi, len) with len >= 50 is addressable: the
   whole granule of phi + c lies in [phi, phi + 50) (as lib/B/Prog/Seg/F11.v f11_sh). *)
Lemma f12_sh : forall m phi L c, addressable m phi (AC.a_size L) -> 50 <= L -> 7 <= c <= 42 ->
  b8 m (Z.shiftr (phi + c) 3 + ASAN_K) 0.
Proof.
  intros m phi L c HA HL Hc.
  pose proof HA as (Hp0 & _ & _ & _).
  pose proof (Z.mod_pos_bound (phi + c) 8 ltac:(lia)) as Hr.
  assert (H8 : addressable m (phi + (c - (phi + c) mod 8)) 8)
    by (apply (addressable_sub m phi (AC.a_size L)); [exact HA | lia | lia | unfold AC.a_size; lia]).
  destruct (meta8 m _ H8) as [[_ RB] _].
  assert (E : Z.shiftr (phi + (c - (phi + c) mod 8)) 3 = Z.shiftr (phi + c) 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (Z.div_mod (phi + c) 8 ltac:(lia)) as D.
    replace (phi + (c - (phi + c) mod 8)) with ((phi + c) / 8 * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite E in RB. exact RB.
Qed.

(* The segment's write set: the nine shadow bytes, the copy's destination and the copy's stack window. *)
Definition f12_W (K D sp : Z) : list Frame.ivl :=
  [(K + 42, K + 51); (D, D + 72); (sp - ASAN_MEMCPY_K, sp)].

Lemma f12_out3 : forall K D sp x,
  (x < K + 42 \/ K + 51 <= x) -> (x < D \/ D + 72 <= x) -> (x < sp - ASAN_MEMCPY_K \/ sp <= x) ->
  Frame.outside (f12_W K D sp) x.
Proof.
  intros K D sp x H1 H2 H3. unfold f12_W. cbn [Frame.outside].
  split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

(* ... and an address the write set does hold lies in one of its three intervals. *)
Lemma f12_in3 : forall K D sp x, ~ Frame.outside (f12_W K D sp) x ->
  (K + 42 <= x < K + 51) \/ (D <= x < D + 72) \/ (sp - ASAN_MEMCPY_K <= x < sp).
Proof.
  intros K D sp x H.
  destruct (Z_le_gt_dec (K + 42) x) as [G1|L1];
    [destruct (Z_lt_ge_dec x (K + 51)) as [L2|G2]; [left; lia|]|];
  (destruct (Z_le_gt_dec D x) as [G3|L3];
    [destruct (Z_lt_ge_dec x (D + 72)) as [L4|G4]; [right; left; lia|]|]);
  (destruct (Z_le_gt_dec (sp - ASAN_MEMCPY_K) x) as [G5|L5];
    [destruct (Z_lt_ge_dec x sp) as [L6|G6]; [right; right; lia|]|]);
  exfalso; apply H; apply f12_out3; lia.
Qed.

(* The side stack's metadata region starts at its base (the companion of Tac_fs.fs_meta_below). *)
Lemma f12_fs_meta_above : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [ (c & Hc & Hr) | (c & jj & Hc & Hj & Heq) ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. assert (Z.of_nat c <= 10)%Z by lia. lia.
  - subst q. exact (proj1 (Tac_fs.a_fs_flag_range FS c jj Hc Hj)).
Qed.

(* Every runtime cell of rt_disjoint lies below AC.GT, so a write set above it misses them (as
   lib/B/Prog/Seg/F13.v rt_dj_fp). *)
Lemma f12_rt_dj1 : forall lo hi, 6283264 <= lo -> rt_disjoint [(lo, hi)].
Proof.
  intros lo hi H.
  unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
    RT_AGLOB, RT_AGLOB_LEN.
  cbn [disjoint_from]. repeat split; first [left; lia | exact I].
Qed.

Lemma f12_rt_dj : forall K D sp,
  6283264 <= K + 42 -> 6283264 <= D -> 6283264 <= sp - ASAN_MEMCPY_K -> rt_disjoint (f12_W K D sp).
Proof.
  intros K D sp H1 H2 H3.
  unfold f12_W, rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
    RT_AGLOB, RT_AGLOB_LEN.
  cbn [disjoint_from]. repeat split; first [left; lia | exact I].
Qed.

Section S.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The callee contract (lib/B/Prog/asan_memcpy_c.v), taken as a Section Hypothesis. *)
Hypothesis HMCPY : asan_memcpy_contract.

(* ---- The Lib-level run lemma: the ONE place of this file that uses the lazy-model lemma
   AsanLift.evt_SR_canon_lazy.  It is used once, by seg_F12, for the run 0x82304 -> 0x8233c (the call) -> 0x82340
   (f12_evt).  That run reads the spills [s1+200, s1+208) and [s1+240, s1+248) of the entry function's save area and
   the record [fr + 2768, fr + 2840); it writes the nine shadow bytes [S(fr) + 42, S(fr) + 51), the copy's
   destination [fr + 336, fr + 408) and the copy's own stack window [sp - 2224, sp). *)
Lemma f12_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = MState.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF' & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF', Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* FRA transports across the segment's memory change (mem -> mem'), at a fixed md and fixed registers.  Unlike
   Tac_slot's sl_fr_run the write set may cover the callee's own stack window below sp, and unlike sl_fr_meta it may
   do that as well as the frame's FRAME_SHADOW shadow bytes; it must miss the frame header [fr, fr + 24), the spill s1+336,
   the selector s1+64, the saved registers [S - 104, S) and the whole low image [0, AC.GT).  RT survives by
   RT_meta_write; the heap invariant, the stklo equality, the entry-anchored stack window, ro_agree, the new
   FRAME_SHADOW-byte shadow list and the addressability of the frame_AG globals come from the caller.  The side arm's
   FakeStack frame record FSREC moves by Tac_slot's fsrec_keep_app_lo: the write set holds no app byte below stklo
   outside the frame (the shadow bytes are not app memory, the copy's destination is in the frame, the callee's
   window is above stklo).  (The body is lib/B/Prog/Seg/F13.v fra_mem_call with those three changes.) *)
Lemma fra_run : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  rt_disjoint W -> ro_agree rsegs mem' ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall A, 0 <= A < 2 ^ 64 -> getr regs 9 = Z_to_bv 64 A ->
     forall x, A + 336 <= x < A + 344 -> outside W x) ->
  (forall A, 0 <= A < 2 ^ 64 -> getr regs 9 = Z_to_bv 64 A ->
     forall x, A + 40 <= x < A + 56 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, 0 <= x < AC.GT -> outside W x) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (forall x, app_mem x -> x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (fr <= x < fr + FRAME_BYTES) -> outside W x) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  FRA B APIf ra g fr hb regs mem' md.
Proof.
  intros g fr hb regs mem mem' md W HFRA MU WM HD HRO' HshR HAH' HSTK HWIN' Hshnew HAG'
    HWhdr HWspill HWsel HWsaved HWlow HWA' HWfs HWin.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold AC.GT in *; lia).
      apply HWlow. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO'|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [exact Hr2|].
  split; [exact Hspm|].
  split; [exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [exact Hr4|].
  split; [exact Hr8|].
  split; [exact Hr9|].
  split; [exact Hr3|].
  split; [exact Hr19|].
  split; [exact Hr26|].
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
    rewrite length_le8. intros x Hx. exact (HWspill A HA64 Hr9 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A HA64 Hr9 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A HA64 Hr9 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [|exact HFSr].
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
      + eapply fsrec_keep_app_lo with (W := W); [exact Hrec | exact HAH | exact MU | exact HWfs]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact HWIN'|].
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
  split; [exact Hhb|]. split; [exact Hlive|].
  exact (fra_in_keep_sh g mem mem' W Hinb Hinblk MU HWin).
Qed.

(* ---- The run pc -> 0x8233c (the call) -> 0x82340 for pc = 0x82304 (the branch `bltz a0` that is not taken,
   with the ingest result r in a0) and for pc = 0x82308 (F10's ir-false arm, which enters at the first shadow
   store): the nine shadow stores, the count, the two spill loads (a0 = [s1+200] = D, s5 = [s1+208] = S) and the
   jal.  The nine stores make the 72 bytes at D addressable, which is the copy's destination premise; the copy's
   post lands at the return pc with a0 = D, s5 = S and every other callee-saved register unchanged. ---- *)
Lemma f12_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A r K3 D S0 lo pc : Z) (src junk : list byte),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 K3 ->
    (pc = 0x82308 \/ (pc = 0x82304 /\ a0v = Z_to_bv 64 r /\ 0 <= r < 2 ^ 63)) ->
    0 <= K3 -> K3 + 51 <= 2 ^ 64 ->
    0 <= D -> 0 <= S0 < 2 ^ 64 -> D + 72 <= S0 ->
    D mod 8 = 0 -> D / 8 + ASAN_K = K3 + 42 ->
    S0 mod 8 = 0 -> S0 / 8 + ASAN_K = K3 + 346 ->
    (forall t, 0 <= t <= 72 -> app_mem (D + t)) ->
    app_mem (S0 + 7) -> app_mem (S0 + 72) ->
    K3 + 51 <= A -> K3 + 51 <= lo ->
    (K3 + 51 <= D \/ D + 72 <= K3 + 42) ->
    (K3 + 51 <= S0 \/ S0 + 72 <= K3 + 42) ->
    wr_at rsegs m (K3 + 42) 9 ->
    shadow_rw m ->
    (forall mm, munch [(K3 + 42, K3 + 51)] m mm -> wmono rsegs m mm ->
       (forall a, in_shadow a -> exists b, mrd rsegs mm (wa a) = Some b) ->
       asan_cells mm /\ shadow_rw mm) ->
    bytes_at rsegs m (A + 200) (le8 (Z_to_bv 64 D)) ->
    bytes_at rsegs m (A + 208) (le8 (Z_to_bv 64 S0)) ->
    bytes_at rsegs m S0 src -> length src = 72%nat ->
    rw_cells rsegs m D [CB 72 junk] ->
    addressable m S0 72 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + ASAN_MEMCPY_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    RT_HI <= D ->
    (D + 72 <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= D) ->
    (S0 + 72 <= bv_unsigned sp - ASAN_MEMCPY_K \/ bv_unsigned sp <= S0) ->
    evt rsegs
      (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1v a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3v s4 (Z_to_bv 64 S0) s6 s7v s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82340) fc None m' (seg_rom rsegs)
         /\ munch (f12_W K3 D (bv_unsigned sp)) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m'
         /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m'
         /\ bytes_at rsegs m' D src /\ bytes_at rsegs m' S0 src
         /\ (forall k, 0 <= k < 9 -> b8 m' (K3 + 42 + k) 0))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0v a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A r K3 D S0 lo pc src junk -> -> Hpc HK0 HK1 HD0 HS0b HDS HD8 HDK HS8 HSK HappD HapS7 HapS72
    HKA HKlo HdjD HdjS HWR HSWm HRTnew H200 H240 HbS Lsrc HRWD HADS HMI HST Hlo1 Hlo2 Hspa HRTD HdjDW HdjSW.
  assert (HDE : D + 72 <= APPMEM_END).
  { pose proof (HappD 72 ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. lia. }
  (* the FAIL branch at 0x82304 is not taken, so both entries reach the first shadow store at 0x82308 *)
  cut (evt rsegs
         (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                            (m' : word -> option byte),
            ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A) a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 (Z_to_bv 64 K3) s4 (Z_to_bv 64 S0) s6 s7v s8 s9 s10 s11 t3' t4' t5' t6')
                     Fr (Z_to_bv 64 0x82340) fc None m' (seg_rom rsegs)
            /\ munch (f12_W K3 D (bv_unsigned sp)) m m'
            /\ wmono rsegs m m' /\ mem_inv rsegs m'
            /\ stk rsegs m' lo (bv_unsigned sp)
            /\ asan_cells m' /\ shadow_rw m'
            /\ bytes_at rsegs m' D src /\ bytes_at rsegs m' S0 src
            /\ (forall k, 0 <= k < 9 -> b8 m' (K3 + 42 + k) 0))
         (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0v a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 K3) s4 s5 s6
                  s7v s8 s9 s10 s11 t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x82308) fc None m (seg_rom rsegs))).
  { intros E298. destruct Hpc as [->|(-> & -> & Hr)]; [exact E298|].
    assert (Hbltz : bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false).
    { unfold bv_lts. rewrite (signed_lit r) by lia. rewrite (signed_lit 0) by lia. apply Z.ltb_ge. lia. }
    step.
    replace (bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0)) with false by (symmetry; exact Hbltz). cbv iota.
    exact E298. }
  (* the nine shadow stores 0x82308-0x82328, in program order 46 47 48 49 42 43 44 45 50 *)
  assert (HS46 : store_ok rsegs m (wa (K3 + 46)) 1 = true).
  { replace (K3 + 46) with (K3 + 42 + 4) by lia.
    apply (wr_at_store_ok rsegs m (K3 + 42) 9 4 1%nat HWR); [lia | cbn; lia]. }
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS47 : store_ok rsegs mm (wa (K3 + 47)) 1 = true) by
      (replace (K3 + 47) with (K3 + 42 + 5) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 5 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS48 : store_ok rsegs mm (wa (K3 + 48)) 1 = true) by
      (replace (K3 + 48) with (K3 + 42 + 6) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 6 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS49 : store_ok rsegs mm (wa (K3 + 49)) 1 = true) by
      (replace (K3 + 49) with (K3 + 42 + 7) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 7 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS42 : store_ok rsegs mm (wa (K3 + 42)) 1 = true) by
      (replace (K3 + 42) with (K3 + 42 + 0) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 0 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS43 : store_ok rsegs mm (wa (K3 + 43)) 1 = true) by
      (replace (K3 + 43) with (K3 + 42 + 1) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 1 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS44 : store_ok rsegs mm (wa (K3 + 44)) 1 = true) by
      (replace (K3 + 44) with (K3 + 42 + 2) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 2 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS45 : store_ok rsegs mm (wa (K3 + 45)) 1 = true) by
      (replace (K3 + 45) with (K3 + 42 + 3) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 3 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS50 : store_ok rsegs mm (wa (K3 + 50)) 1 = true) by
      (replace (K3 + 50) with (K3 + 42 + 8) by lia;
       apply (wr_at_store_ok rsegs mm (K3 + 42) 9 8 1%nat); [repeat apply wr_at_write; exact HWR | lia | cbn; lia])
  end.
  step.
  (* the memory after the nine stores: the write set, the readable cells and the new shadow bytes *)
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MU9 : munch [(K3 + 42, K3 + 51)] m mm) by
      (repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; slia ]);
       apply munch_refl);
    assert (WM9 : wmono rsegs m mm) by (repeat apply wmono_write; apply wmono_refl);
    assert (ST9 : stk rsegs mm lo (bv_unsigned sp)) by
      (repeat (apply stk_write; [ | lia | simpl_sizes; lia ]); exact HST);
    assert (MI9 : mem_inv rsegs mm) by
      (apply mem_inv_store; [|simpl_sizes; exact HS50];
       apply mem_inv_store; [|simpl_sizes; exact HS45];
       apply mem_inv_store; [|simpl_sizes; exact HS44];
       apply mem_inv_store; [|simpl_sizes; exact HS43];
       apply mem_inv_store; [|simpl_sizes; exact HS42];
       apply mem_inv_store; [|simpl_sizes; exact HS49];
       apply mem_inv_store; [|simpl_sizes; exact HS48];
       apply mem_inv_store; [|simpl_sizes; exact HS47];
       apply mem_inv_store; [|simpl_sizes; exact HS46]; exact HMI);
    assert (B46 : b8 mm (K3 + 46) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B47 : b8 mm (K3 + 47) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B48 : b8 mm (K3 + 48) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B49 : b8 mm (K3 + 49) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B42 : b8 mm (K3 + 42) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B43 : b8 mm (K3 + 43) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B44 : b8 mm (K3 + 44) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B45 : b8 mm (K3 + 45) 0) by
      (repeat (apply f12_wother; [f12_zb | | lia | lia | lia]); apply f12_wsame; [f12_zb | lia | lia]);
    assert (B50 : b8 mm (K3 + 50) 0) by
      (apply f12_wsame; [f12_zb | lia | lia]);
    assert (SH9 : forall k, 0 <= k < 9 -> b8 mm (K3 + 42 + k) 0) by
      (intros k Hk;
       assert (Hk9 : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8) by lia;
       decompose [or] Hk9; subst k;
       first [ replace (K3 + 42 + 0) with (K3 + 42) by lia; exact B42
             | replace (K3 + 42 + 1) with (K3 + 43) by lia; exact B43
             | replace (K3 + 42 + 2) with (K3 + 44) by lia; exact B44
             | replace (K3 + 42 + 3) with (K3 + 45) by lia; exact B45
             | replace (K3 + 42 + 4) with (K3 + 46) by lia; exact B46
             | replace (K3 + 42 + 5) with (K3 + 47) by lia; exact B47
             | replace (K3 + 42 + 6) with (K3 + 48) by lia; exact B48
             | replace (K3 + 42 + 7) with (K3 + 49) by lia; exact B49
             | replace (K3 + 42 + 8) with (K3 + 50) by lia; exact B50 ]);
    assert (RD200 : ov_read_bytes rsegs mm (wa (A + 200)) 8 = Some (le8 (Z_to_bv 64 D))) by
      (apply f12_rd8; [ repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]);
                        exact H200 | apply length_le8 ]);
    assert (RD240 : ov_read_bytes rsegs mm (wa (A + 208)) 8 = Some (le8 (Z_to_bv 64 S0))) by
      (apply f12_rd8; [ repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]);
                        exact H240 | apply length_le8 ]);
    assert (BS9 : bytes_at rsegs mm S0 src) by
      (repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | rewrite Lsrc; simpl_sizes; lia ]);
       exact HbS);
    assert (RW9 : rw_cells rsegs mm D [CB 72 junk]) by
      (repeat (apply rw_cells_frame; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]); exact HRWD);
    assert (AD9 : addressable mm D 72) by
      (apply (f12_addr72 mm D (K3 + 42)); [lia | lia | exact HD8 | exact HDK | intros t Ht; apply HappD; lia
                                          | exact SH9]);
    assert (AS9 : addressable mm S0 72) by
      (apply (f12_addr_munch [(K3 + 42, K3 + 51)] m mm S0 72 HADS MU9);
       intros i Hi; apply f12_out1;
       assert (Ei : shadow_addr (S0 + i) = K3 + 346 + i / 8) by
         (unfold shadow_addr; rewrite <- HSK;
          replace (S0 + i) with (i + (S0 / 8) * 8) by (Z.div_mod_to_equations; lia);
          rewrite Z.div_add by lia; lia);
       rewrite Ei; right; Z.div_mod_to_equations; lia);
    assert (RT9 : asan_cells mm /\ shadow_rw mm) by
      (apply (HRTnew mm MU9 WM9); intros a Hin;
       assert (Hab : 0 <= a < 2 ^ 64) by
         (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin; lia);
       destruct (Z_lt_le_dec a (K3 + 42)) as [Hlo|Hge];
       [ destruct (HSWm a Hin) as (_ & b & Hb); exists b; unfold mrd in *;
         rewrite (MU9 (wa a)); [exact Hb | rewrite wa_unsigned by lia; apply f12_out1; left; exact Hlo]
       | destruct (Z_lt_le_dec a (K3 + 51)) as [Hhi|Hge2];
         [ destruct (SH9 (a - K3 - 42) ltac:(lia)) as (_ & _ & Hrd);
           pose proof (Hrd 0%nat ltac:(cbn; lia)) as Hb;
           change (Z.of_nat 0) with 0 in Hb; rewrite Z.add_0_r in Hb; cbn [nth_error] in Hb;
           replace (K3 + 42 + (a - K3 - 42)) with a in Hb by lia; exists (Z_to_bv 8 0); exact Hb
         | destruct (HSWm a Hin) as (_ & b & Hb); exists b; unfold mrd in *;
           rewrite (MU9 (wa a)); [exact Hb | rewrite wa_unsigned by lia; apply f12_out1; right; exact Hge2] ] ])
  end.
  destruct RT9 as (AC9 & SW9).
  (* 0x8232c .. 0x8233c: the count, the two spill loads, the argument move and the call *)
  do 5 step.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S0) = S0) by (apply unsigned_lit; lia).
  assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by reflexivity.
  pose proof HMCPY as HM. unfold asan_memcpy_contract, ASAN_MEMCPY_K in HM. cbv zeta in HM.
  eapply evt_cut.
  { eapply HM with (src := src) (junk := junk) (lo := lo).
    all: rewrite ?ED, ?ES, ?E72.
    - exact BS9.
    - rewrite Lsrc. reflexivity.
    - change (Z.to_nat 72) with 72%nat. exact RW9.
    - right; right; lia.
    - clear; lia.
    - exact AS9.
    - exact AD9.
    - right. exact HapS72.
    - right. apply HappD. lia.
    - right. split; [exact HapS7 | apply HappD; lia].
    - right. unfold RT_HI in *. lia.
    - exact HdjDW.
    - exact HdjSW.
    - exact ST9.
    - unfold ASAN_MEMCPY_K in Hlo1. lia.
    - exact Hlo2.
    - exact Hspa.
    - exact AC9.
    - exact SW9.
    - exact MI9. }
  intros ms2 Hp. unfold asan_memcpy_post in Hp.
  destruct Hp as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MUc & WMc & MIc & STc & RWc & BSc & ACc & SWc).
  subst ms2.
  replace (ret_pc (Z_to_bv 64 0x82340)) with (Z_to_bv 64 0x82340)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done.
  exists (Z_to_bv 64 0x82340), (Z_to_bv 64 D), a1', a2', a3', a4', a5', a6', a7',
         t0', t1', t2', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split.
  { eapply munch_trans.
    - apply (munch_weaken [(K3 + 42, K3 + 51)]); [|exact MU9].
      unfold sub_fp, f12_W, ASAN_MEMCPY_K. cbn [Frame.outside]. intros x (Hx & _). split; [lia | exact I].
    - apply (munch_weaken [(bv_unsigned (Z_to_bv 64 D),
                            bv_unsigned (Z_to_bv 64 D) + bv_unsigned (Z_to_bv 64 72));
                           (bv_unsigned sp - ASAN_MEMCPY_K, bv_unsigned sp)]); [|exact MUc].
      unfold sub_fp, f12_W. cbn [Frame.outside]. intros x (_ & Hx2 & Hx3 & _).
      split; [lia|]. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs m _ m' WM9 WMc)|].
  split; [exact MIc|].
  split; [exact STc|].
  split; [exact ACc|].
  split; [exact SWc|].
  split.
  { rewrite <- ED. exact (f12_cb_bytes m' _ _ _ RWc). }
  split; [rewrite <- ES; exact BSc|].
  intros k Hk. unfold b8. eapply fl_bytes; [exact (SH9 k Hk) | exact MUc |].
  cbn [length]. intros x Hx. cbn [Frame.outside]. split; [lia|]. split; [lia | exact I].
Qed.

(* ---- Push 5c: no cut carries mem_inv (FRA has ro_agree only), but the asan_memcpy contract asks for it. seg_F12
   runs f12_evt on MemNorm.normalize mem (mem_inv_normalize) and carries the run back to mem by
   MemNorm.evt_normalize. These lemmas move f12_evt's premises to the normalized memory and its post back. Every
   address they speak of is at or above GT, where no segment lies, so normalizing changes nothing there
   (lib/B/Prog/Seg/F18.v makes the same moves for the bcmp wrapper). ---- *)
Lemma f12_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f12_ro_ge_GT : forall x, AC.GT <= x < 2 ^ 64 -> ro_addr rsegs (wa x) = false.
Proof.
  intros x Hx. assert (HGT : AC.GT = 0x5fe000) by reflexivity. unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. assert (Ex : bv_unsigned (wa x) = x) by (rewrite wa_unsigned by lia; reflexivity).
  rewrite Ex in E.
  destruct (sl_find_below rsegs AC.GT x 1 s ltac:(vm_compute; reflexivity) E ltac:(lia)) as [L|L]; lia.
Qed.

Lemma f12_addr_norm : forall m p n, ro_agree rsegs m -> addressable m p n -> addressable (normalize rsegs m) p n.
Proof.
  intros m p n HRO (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ (mem_rel_normalize rsegs m HRO)). exact Hb.
Qed.

Lemma f12_stk_norm : forall m lo hi, ro_agree rsegs m -> AC.GT <= lo -> stk rsegs m lo hi ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi HRO Hlo (H1 & H2 & H). pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as [Hv [b Hb]].
  assert (RO : ro_addr rsegs (wa a) = false) by (apply f12_ro_ge_GT; lia).
  split.
  - rewrite (wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma f12_shadow_rw_norm : forall m, ro_agree rsegs m -> shadow_rw m -> shadow_rw (normalize rsegs m).
Proof.
  intros m HRO H a Ha. pose proof (mem_rel_normalize rsegs m HRO) as REL.
  destruct (H a Ha) as [Hv [b Hb]].
  assert (RO : ro_addr rsegs (wa a) = false).
  { apply f12_ro_ge_GT. assert (HGT : AC.GT = 0x5fe000) by reflexivity.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. }
  split.
  - rewrite (wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma f12_cells_norm : forall m, ro_agree rsegs m -> asan_cells m -> asan_cells (normalize rsegs m).
Proof.
  intros m HRO H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply bytes_at_normalize; assumption.
Qed.

Lemma f12_rw_norm : forall m a cs, ro_agree rsegs m -> AC.GT <= a -> rw_cells rsegs m a cs ->
  rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs HRO Ha ((Hw & Hb) & Hwr). pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [split; [exact Hw | exact (bytes_at_normalize rsegs m a _ HRO Hb)]|].
  apply (wr_at_norm rsegs m (normalize rsegs m) a _ REL Hwr).
  intros i Hi. apply f12_ro_ge_GT. destruct Hwr as (H0 & H1 & _). lia.
Qed.

Lemma f12_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hv [b Hb]]. pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma f12_shadow_rw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 REL H a Ha. destruct (H a Ha) as [Hv [b Hb]].
  pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma f12_cells_back : forall m m0, mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 REL H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end;
    apply (proj2 (bytes_at_rel rsegs m m0 _ _ REL)); assumption.
Qed.

(* A state related to an MS state by evt_normalize's ms_rel is that state with its own memory. *)
Lemma f12_ms_rel_MS : forall s R F pc fc rv m0 ro,
  ms_rel rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [r f p sv rv' fc' m ro'] R F pc fc rv m0 ro (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hm).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in *.
  subst. split; [reflexivity | exact Hm].
Qed.

(* ---- The entry facts both entries of this segment give. At 0x82304 (the return of the ingest call at 0x82300)
   the official Inv_B82304_at states them, with the ingest result in a0 besides; at 0x82308 (F10's ir-false arm)
   the official Inv_B82308_at does, with f10_K spelling FM, FS9 and the FLI / FLV spills out. Everything else the
   run and the exit cut need comes from FRA (the spill base and its window, the frame's place and its app memory,
   the block's place below stklo, the frame's byte-backed body) and from the write set. No cut carries mem_inv
   (push 5c): the copy's mem_inv premise comes from FRA's ro_agree by MemNorm.evt_normalize in f12_at. *)
Definition f12_pre (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\
  rg regs 18 phi /\ rg regs 20 (flen g j) /\ FTURN g j phi regs m /\
  LK g fr j regs m /\ FM g j phi fr regs m /\ FSj g fr j regs m /\ RECR g fr j m /\
  (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
  FPS g fr j m /\ F272 g j regs m /\ RCA fr m /\ FS9 g j regs m.

(* ---- The segment body, shared by this segment's two entries: 0x82304 (the return of the reply-path ingest at
   0x82300, Inv_B82304_at, where the `bltz a0` is not taken) and 0x82308 (the ir-false arm of F10,
   Inv_B82308_at). Its exit at 0x82340 (post-copy; the entry of F13) is the official Inv_B82340_at: LK, the
   before-call copy at fr + 336, FM and FSj, s5 = the record, the record's and Phi's bytes, the addressability of
   Phi, the record, the copy and the three output cells, Phi against the frame and against the fragment call's
   stack window, RECR, FRBA and FS9. ---- *)
Lemma f12_at : forall (j : nat) (g : ghost) (phi fr pc r : Z) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model),
  Hat B APIf ra (Inv_B82340_at B APIf ra) j ->
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem md ->
  f12_pre g j phi fr regs mem ->
  (pc = 0x82308 \/ (pc = 0x82304 /\ rg regs 10 r /\ 0 <= r < 2 ^ 63)) ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md) (Post B APIf ra g).
Proof.
  intros j g phi fr pc r regs mem md Hexit HFRA HENT HPRE Hpc.
  pose proof (proj1 FF) as SEGS.
  destruct HPRE as (Hgn & Hj & HHB & H18 & H20 & HFT & HLK & HFM & HFSj & HRECR & Hphig & HFPS & H272 &
    (Hapa & Happ8 & Hapn) & HS9).
  destruct HHB as (Hphinz & HAd).
  destruct (fra_fr_spill B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
    as (A & H9 & HAb & _).
  pose proof HLK as HLK0. destruct HLK0 as (Hj255 & Hs232 & HOURb & HFLI).
  pose proof HFLI as HFLI0.
  destruct HFLI0 as (H27 & P168 & P96 & P112 & P120 & P128 & P136 & P144 & P152 & P280 & P160 & P176 & P192 &
    P200 & P216 & P208 & P104 & P256 & P264 & P288 & P296 & P304 & HadOur & HstkF & (HRid & HRfg & HRfst) & HKNT &
    P168b & P88).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
    as (Hplace & HfrA & Hfsmeta & Hfrwr).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspillq & Hselq & Hfr56q & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof HRT as HRT0. destruct HRT0 as (HAC0 & HSW0 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HA2b : 0 <= A2 < 2 ^ 64) by lia.
  assert (HA2 : A2 = A).
  { assert (E : Z_to_bv 64 A2 = Z_to_bv 64 A) by (unfold rg in *; rewrite <- Hr9; exact H9).
    apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !MState.unsigned_lit in E by lia. exact E. }
  subst A2.
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)).
  assert (HK : 0 <= ASAN_MEMCPY_K <= FN_STACK) by (unfold ASAN_MEMCPY_K; lia).
  pose proof (Hplace ASAN_MEMCPY_K HK) as Hfrsep.
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in H9; rewrite H9; apply MState.unsigned_lit; lia).
  rewrite HbvA in HfrA.
  assert (HaspH : HIGHMEM_BEG <= AC.aspZ regs - FN_STACK) by lia.
  assert (HaspE : AC.aspZ regs <= APPMEM_END) by lia.
  assert (HspA : AC.aspZ regs <= A) by lia.
  (* the frame body is app memory above AC.GT, on both arms *)
  assert (Hframe : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ AC.GT <= a).
  { destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - intros a Ha. destruct (Hreal a Ha) as (Hlo2 & Hhi2).
      split; [right; unfold APPMEM_END, HIGHMEM_BEG in *; lia | unfold AC.GT, HIGHMEM_BEG in *; lia].
    - intros a Ha. destruct (Hfs a Ha) as (FSa & HFSr & Hw & Hlo2 & Hhi2).
      destruct (lw_fs_place (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FSa HAH Hw HFSr)
        as [HG Hend _ Happ2].
      split; [exact (Happ2 a ltac:(lia)) | lia]. }
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; apply (Hframe a Ha)).
  assert (HGT : AC.GT <= fr) by (apply (Hframe fr ltac:(lia))).
  assert (Hfrb : 0 <= fr /\ fr + FRAME_BYTES < 2 ^ 64).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in H1, H2. lia. }
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  (* the FLI spills, read at the cut's own spill base s1 = A *)
  assert (HAE : 0 <= A < APPMEM_END) by (unfold APPMEM_END in *; lia).
  assert (Hspq : forall off v, 0 <= off <= 440 -> spill regs mem off v -> q64 mem (A + off) v).
  { intros off v Hoff (A3 & HA3 & Hq3).
    pose proof (f12_spill_base regs A A3 mem off v H9 HA3 HAE Hoff Hq3) as EA. subst A3. exact Hq3. }
  pose proof (Hspq 200 (fr + 336) ltac:(lia) P200) as H200.
  pose proof (Hspq 208 (fragb fr) ltac:(lia) P208) as H240.
  (* a byte of the record buffer phi is never a byte of the frame: on the real arm the block ends below stklo and
     the frame starts at it, on the side arm the frame is inside the side stack and no block byte is *)
  destruct (lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
              (AC.a_size (flen g j)) HAH ltac:(left; reflexivity)) as [Hal16 Hp4096 Hpst Hpend Hpbyte].
  assert (Hblk : forall a, phi <= a < phi + AC.a_size (flen g j) -> ~ (fr <= a < fr + FRAME_BYTES)).
  { intros a Ha Hfrm2.
    destruct (Hpbyte a Ha) as (_ & _ & _ & _ & Hnfs).
    destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - destruct (Hreal a Hfrm2) as (Hlo2 & _). lia.
    - exact (Hnfs (Hfs a Hfrm2)). }
  (* so the block lies wholly below the frame or wholly above it *)
  assert (Hblkfr : phi + AC.a_size (flen g j) <= fr \/ fr + FRAME_BYTES <= phi).
  { destruct (Z_le_gt_dec (phi + AC.a_size (flen g j)) fr) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [L2|L2]; [right; exact L2|].
    exfalso. apply (Hblk (Z.max phi fr)); unfold AC.a_size in *; lia. }
  assert (Hasz : flen g j <= AC.a_size (flen g j) /\ 1 <= AC.a_size (flen g j))
    by (unfold AC.a_size; lia).
  assert (Hphi0 : 0 <= phi /\ phi + AC.a_size (flen g j) <= APPMEM_END)
    by (pose proof HAd as (Hx1 & _ & Hx3 & _); unfold AC.a_size in *; lia).
  (* the frame apart from the compare wrapper's stack window (F13 / F14 read the two 6-byte operands there) *)
  assert (Hfrsepb : fr + FRAME_BYTES <= AC.aspZ regs - BW.BCMP_WRAP_K \/ AC.aspZ regs <= fr)
    by (apply Hplace; unfold BW.BCMP_WRAP_K, FN_STACK, AF.SLOT_STACK; lia).
  (* the copy's destination [fr + 336, fr + 408): present and writable, from the frame's byte-backed body *)
  destruct (f12_stk_cb mem fr (fr + FRAME_BYTES) (fr + 336) 72 HstkF ltac:(lia) ltac:(cbn; lia))
    as (jk & Hjkl & HRWD).
  (* the copy's source: the fragment record of RECR *)
  pose proof HRECR as ((HIDb0 & HIDok0) & (HFGb0 & HFGok0)).
  assert (Hsrc : bytes_at rsegs mem (fragb fr) (t_FG (g_in g) j)) by exact HFGb0.
  assert (HIDrL : length (t_IDr (g_in g) j) = 38%nat).
  { unfold t_IDr. rewrite (rp_id_length (t_ID (g_in g) j) (t_len (g_in g) j) (t_g (g_in g) j)
      (t_ID_length (g_in g) j)). reflexivity. }
  (* the spill words the exit's FRBA reads: [A+272] (F272), [A+312] (FM), [A+248] (FS9), [A+96] / [A+112] (FLI) *)
  pose proof (Hspq 272 _ ltac:(lia) H272) as H272q.
  pose proof HFM as (M184 & M24 & M22 & M25 & M312).
  pose proof (Hspq 248 (1 - b2z (t_sum_ok (g_in g) j)) ltac:(lia) HS9) as H288q.
  pose proof (Hspq 312 _ ltac:(lia) M312) as H312q.
  pose proof (Hspq 112 _ ltac:(lia) P112) as H88q.
  pose proof (Hspq 96 _ ltac:(lia) P96) as H80q.
  (* the frame's FRAME_SHADOW shadow bytes are shadow addresses, and they lie below the high application memory *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HK3b : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (HshIS (Sfr fr) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as H2.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in H1, H2.
    unfold LOWMEM_END, HIGHMEM_BEG. lia. }
  assert (HWR : wr_at rsegs mem (Sfr fr + 42) 9).
  { split; [unfold LOWMEM_END in *; lia|]. split; [unfold HIGHMEM_BEG in *; lia|].
    intros i Hi.
    destruct (HSW0 (Sfr fr + 42 + i) (HshIS (Sfr fr + 42 + i) ltac:(lia))) as (Hw & _). exact Hw. }
  (* the copy's two ranges, their shadow indexes and their placement *)
  assert (HDK : (fr + 336) / 8 + ASAN_K = Sfr fr + 42).
  { unfold Sfr, shadow_addr. replace (fr + 336) with (336 + (fr / 8) * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. lia. }
  assert (HSK : fragb fr / 8 + ASAN_K = Sfr fr + 346).
  { unfold fragb, Sfr, shadow_addr.
    replace (fr + 2768) with (2768 + (fr / 8) * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. lia. }
  assert (HD8 : (fr + 336) mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (HS8 : fragb fr mod 8 = 0) by (unfold fragb; Z.div_mod_to_equations; lia).
  assert (Hfb : 0 <= fragb fr < 2 ^ 64).
  { assert (Ha : app_mem (fr + 2768)) by (apply Happ; lia).
    unfold fragb, app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG, AC.GT in *. lia. }
  (* the nine shadow bytes lie below the high application memory, so below the save area and the stack window *)
  assert (HKA : Sfr fr + 51 <= A) by (unfold HIGHMEM_BEG in *; lia).
  assert (HKlo : Sfr fr + 51 <= AC.aspZ regs - FN_STACK) by (unfold HIGHMEM_BEG in *; lia).
  assert (HdjD : Sfr fr + 51 <= fr + 336 \/ fr + 336 + 72 <= Sfr fr + 42).
  { pose proof (HshIS (Sfr fr + 42) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + 50) ltac:(lia)) as H1b.
    pose proof (Happ (fr + 336) ltac:(lia)) as H2. pose proof (Happ (fr + 407) ltac:(lia)) as H3.
    unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HdjS : Sfr fr + 51 <= fragb fr \/ fragb fr + 72 <= Sfr fr + 42).
  { pose proof (HshIS (Sfr fr + 42) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + 50) ltac:(lia)) as H1b.
    pose proof (Happ (fr + 2768) ltac:(lia)) as H2. pose proof (Happ (fr + 2839) ltac:(lia)) as H3.
    unfold fragb, in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
      APPMEM_END in *. lia. }
  (* the callee's stack window, carved out of the FRA window *)
  assert (Hstkcall : stk rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs)) by exact Hwstk.
  (* the facts the run reads, on the normalized memory it starts from (push 5c, see f12_wx above), and the
     runtime cells after the shadow stores *)
  pose proof (mem_rel_normalize rsegs mem Hro) as REL0.
  assert (HSW0n : shadow_rw (normalize rsegs mem)) by exact (f12_shadow_rw_norm mem Hro HSW0).
  assert (HWRn : wr_at rsegs (normalize rsegs mem) (Sfr fr + 42) 9).
  { split; [unfold LOWMEM_END in *; lia|]. split; [unfold HIGHMEM_BEG in *; lia|].
    intros i Hi.
    destruct (HSW0n (Sfr fr + 42 + i) (HshIS (Sfr fr + 42 + i) ltac:(lia))) as (Hw & _). exact Hw. }
  assert (HRTnewN : forall mm, munch [(Sfr fr + 42, Sfr fr + 51)] (normalize rsegs mem) mm ->
            wmono rsegs (normalize rsegs mem) mm ->
            (forall a, in_shadow a -> exists b, mrd rsegs mm (wa a) = Some b) ->
            asan_cells mm /\ shadow_rw mm).
  { intros mm MU WM HSH. split.
    - apply (asan_cells_kept [(Sfr fr + 42, Sfr fr + 51)] (normalize rsegs mem) mm (f12_cells_norm mem Hro HAC0) MU).
      pose proof (HshIS (Sfr fr + 42) ltac:(lia)) as H1.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in H1.
      unfold RT_LO, RT_HI. cbn [disjoint_from]. split; [lia | exact I].
    - intros a Ha. split; [apply WM; exact (proj1 (HSW0n a Ha)) | exact (HSH a Ha)]. }
  (* run the segment *)
  apply (f12_run_lib regs (Z_to_bv 64 pc) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82340 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 26 = getr regs 26 /\
       getr R0 27 = getr regs 27 /\
       getr R0 23 = getr regs 23 /\ getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\
       getr R0 21 = Z_to_bv 64 (fragb fr) /\
       munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' /\
       wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) /\
       asan_cells mem' /\ shadow_rw mem' /\
       bytes_at rsegs mem' (fr + 336) (t_FG (g_in g) j) /\
       bytes_at rsegs mem' (fragb fr) (t_FG (g_in g) j) /\
       (forall k, 0 <= k < 9 -> b8 mem' (Sfr fr + 42 + k) 0))
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* The copy's contract asks for mem_inv, which the cut does not carry (push 5c): run f12_evt on the
       normalized memory (mem_inv_normalize) and carry the run back to mem by MemNorm.evt_normalize from FRA's
       ro_agree. *)
    eapply evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply (evt_normalize rsegs); [exact f12_wx | exact Hro |].
      eapply f12_evt with (A := A) (r := r) (K3 := Sfr fr) (D := fr + 336) (S0 := fragb fr)
        (lo := AC.aspZ regs - FN_STACK) (src := t_FG (g_in g) j) (junk := jk).
      - unfold rg in H9; exact H9.
      - unfold rg in Hr19; exact Hr19.
      - destruct Hpc as [->|(-> & H10 & Hrng)];
          [left; reflexivity
           | right; split; [reflexivity | split; [unfold rg in H10; exact H10 | exact Hrng]]].
      - unfold LOWMEM_END in *; lia.
      - unfold HIGHMEM_BEG in *; lia.
      - lia.
      - exact Hfb.
      - unfold fragb; lia.
      - exact HD8.
      - exact HDK.
      - exact HS8.
      - exact HSK.
      - intros t Ht. apply Happ. lia.
      - apply Happ; unfold fragb in *; lia.
      - apply Happ; unfold fragb in *; lia.
      - exact HKA.
      - exact HKlo.
      - exact HdjD.
      - exact HdjS.
      - exact HWRn.
      - exact HSW0n.
      - exact HRTnewN.
      - unfold q64 in H200; exact (bytes_at_normalize rsegs mem _ _ Hro H200).
      - unfold q64 in H240; exact (bytes_at_normalize rsegs mem _ _ Hro H240).
      - exact (bytes_at_normalize rsegs mem _ _ Hro Hsrc).
      - apply t_FG_length.
      - apply (f12_rw_norm mem _ _ Hro); [unfold AC.GT in *; lia | exact HRWD].
      - exact (f12_addr_norm mem _ _ Hro HRfg).
      - exact (mem_inv_normalize rsegs mem).
      - fold_sp regs. apply (f12_stk_norm mem _ _ Hro); [unfold AC.GT, HIGHMEM_BEG in *; lia | exact Hstkcall].
      - fold_sp regs. unfold ASAN_MEMCPY_K in *. lia.
      - exact HaspH.
      - fold_sp regs. exact HaspE.
      - unfold RT_HI, AC.GT in *. lia.
      - fold_sp regs. unfold ASAN_MEMCPY_K in *. lia.
      - fold_sp regs. unfold fragb, ASAN_MEMCPY_K in *. lia. }
    { intros ms' (s0 & (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5'
                  & t6' & m' & E & MU & WM & MI' & ST' & AC' & SW' & HbD & HbS & HSH) & REL & SAME).
      subst s0.
      destruct (f12_ms_rel_MS ms' _ _ _ _ _ _ _ REL) as (Ems & HREL).
      eexists _, (Z_to_bv 64 0x82340), (ms_mem ms'). split; [exact Ems|].
      split; [reflexivity|].
      do 15 (split; [reflexivity|]).
      match type of ST' with context [bv_unsigned ?s] => change (bv_unsigned s) with (AC.aspZ regs) in MU, ST' end.
      split; [exact (munch_rel rsegs _ mem (normalize rsegs mem) (ms_mem ms') m' REL0 HREL SAME MU)|].
      split; [exact (wmono_rel rsegs mem (normalize rsegs mem) (ms_mem ms') m' REL0 HREL SAME WM)|].
      split; [exact (ro_agree_of_mem_rel rsegs (ms_mem ms') m' HREL)|].
      split; [exact (f12_stk_back (ms_mem ms') m' _ _ HREL ST')|].
      split; [exact (f12_cells_back (ms_mem ms') m' HREL AC')|].
      split; [exact (f12_shadow_rw_back (ms_mem ms') m' HREL SW')|].
      split; [exact (proj2 (bytes_at_rel rsegs (ms_mem ms') m' _ _ HREL) HbD)|].
      split; [exact (proj2 (bytes_at_rel rsegs (ms_mem ms') m' _ _ HREL) HbS)|].
      intros k Hk. unfold b8 in *. exact (proj2 (bytes_at_rel rsegs (ms_mem ms') m' _ _ HREL) (HSH k Hk)). }
  - intros R0 pc' mem' regs' md' (Hpcx & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er26 & Er27 &
      Er23 & Er22 & Er24 & Er25 & Er21 &
      MU & WM & HroM & ST' & AC' & SW' & HbD & HbS & HSH) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr21 : getr regs' 21 = Z_to_bv 64 (fragb fr)) by (rewrite Hreg; exact Er21).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    (* the write set: clear of the runtime's cells, and the addresses it misses *)
    assert (Hrtdj : rt_disjoint (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs))).
    { apply f12_rt_dj; unfold AC.GT, ASAN_MEMCPY_K, LOWMEM_END, HIGHMEM_BEG in *; lia. }
    assert (Hwmon : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
      by (intros q Hqb Hw; exact (WM (Z_to_bv 64 q) Hw)).
    (* a frame byte outside the copy's destination is outside the write set: it is app memory (so not one of the
       nine shadow bytes) and the frame is apart from the copy's stack window (fra_frame) *)
    assert (Hfrout : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 336 <= x < fr + 336 + 72) ->
              Frame.outside (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) x).
    { intros x Hx Hnd. apply f12_out3.
      - pose proof (HshIS (Sfr fr + 42) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + 50) ltac:(lia)) as H2.
        pose proof (Happ x Hx) as Hap.
        revert H1 H2 Hap; rs_hide_all; intros H1 H2 Hap.
        unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia.
      - lia.
      - unfold ASAN_MEMCPY_K in *. lia. }
    (* a byte of the record buffer is outside the write set: it is app memory, apart from the frame (so apart from
       the copy's destination) and below the fragment call's window, which is wider than the copy's *)
    assert (Hphiout : forall x, phi <= x < phi + AC.a_size (flen g j) ->
              Frame.outside (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) x).
    { intros x Hx. apply f12_out3.
      - pose proof (HshIS (Sfr fr + 42) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + 50) ltac:(lia)) as H2.
        destruct (Hpbyte x Hx) as (Hap & _).
        revert H1 H2 Hap; rs_hide_all; intros H1 H2 Hap.
        unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia.
      - destruct Hblkfr as [Hd|Hd]; lia.
      - unfold ASAN_MEMCPY_K in *. lia. }
    assert (HoutA : forall x, A <= x -> x < A + 448 ->
              Frame.outside (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) x).
    { intros x Hx1 Hx2. apply f12_out3; [lia | lia | unfold ASAN_MEMCPY_K in *; lia]. }
    (* the spill moves and the q64 transports this cut's rebuild makes *)
    assert (SPK : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hs. eapply f12_spill_keep;
        [exact H9 | exact Fr9 | exact HAE | exact Hoff | exact Hs | exact MU |
         intros x Hx; apply HoutA; lia]. }
    assert (QK : forall off v, 0 <= off <= 440 -> q64 mem (A + off) v -> q64 mem' (A + off) v).
    { intros off v Hoff Hq. unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
      rewrite length_le8. intros x Hx. apply HoutA; lia. }
    assert (Hshout : forall x, in_shadow x -> ~ (Sfr fr + 42 <= x < Sfr fr + 51) ->
              Frame.outside (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) x).
    { intros x Hin Hnot. apply f12_out3; [lia | |].
      - pose proof (Happ (fr + 336) ltac:(lia)) as H2. pose proof (Happ (fr + 407) ltac:(lia)) as H3.
        revert Hin H2 H3; rs_hide_all; intros Hin H2 H3.
        unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia.
      - revert Hin; rs_hide_all; intros Hin.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, ASAN_MEMCPY_K in *. lia. }
    (* AH and stklo across the segment's stores, by arm *)
    assert (HAHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem' md /\
                     (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem' md a
                        <-> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md a) /\
                     AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                       = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                     AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                       = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs _]]]].
      - (* real arm: the frame body, the callee window and the frame's shadow are all a_store_ok *)
        assert (Hmc : forall q, 0 <= q < 2 ^ 64 ->
                  ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns. apply MU. rewrite MState.unsigned_lit by exact Hq.
          apply f12_out3.
          - destruct (Z_lt_le_dec q (Sfr fr + 42)) as [Hl|Hg]; [left; exact Hl|].
            destruct (Z_lt_le_dec q (Sfr fr + 51)) as [Hl2|Hg2]; [|right; exact Hg2].
            exfalso. apply Hns. right. right. right.
            exists (fr + 8 * (q - Sfr fr)). split.
            + unfold shadow_addr.
              replace (fr + 8 * (q - Sfr fr)) with ((q - Sfr fr) * 8 + (fr / 8) * 8)
                by (Z.div_mod_to_equations; lia).
              rewrite Z.div_add by lia. rewrite Z.div_mul by lia. unfold Sfr, shadow_addr. lia.
            + right. left. specialize (Hreal (fr + 8 * (q - Sfr fr)) ltac:(lia)). lia.
          - destruct (Z_lt_le_dec q (fr + 336)) as [Hl|Hg]; [left; exact Hl|].
            destruct (Z_lt_le_dec q (fr + 336 + 72)) as [Hl2|Hg2]; [|right; exact Hg2].
            exfalso. apply Hns. right. left. specialize (Hreal q ltac:(lia)). lia.
          - destruct (Z_lt_le_dec q (AC.aspZ regs - ASAN_MEMCPY_K)) as [Hl|Hg]; [left; exact Hl|].
            destruct (Z_lt_le_dec q (AC.aspZ regs)) as [Hl2|Hg2]; [|right; exact Hg2].
            exfalso. apply Hns. right. left.
            unfold APPMEM_END, ASAN_MEMCPY_K, FN_STACK, AF.SLOT_STACK in *. lia. }
        destruct (lw_store (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH Hmc Hwmon)
          as [HAH2 Hown2 Hstk2 Hhi2].
        split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2].
      - (* side arm: the frame body and its shadow belong to the side stack for frames *)
        destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSc & HFScr & HwFSc & HFSlo & HFShi).
        destruct (lw_fs_place (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FSc HAH HwFSc HFScr)
          as [HFSgt HFSend _ HFSapp].
        pose proof (Hfsmeta FSc HwFSc HFScr) as HFSmeta.
        assert (Hstore : forall q, 0 <= q < 2 ^ 64 ->
                  ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
                      (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                  ~ (FSc <= q < FSc + AC.FS_SIZE) ->
                  ~ (exists b, FSc <= b < FSc + AC.FS_SIZE /\ q = shadow_addr b) ->
                  mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
          apply f12_out3.
          - destruct (Z_lt_le_dec q (Sfr fr + 42)) as [Hl|Hg]; [left; exact Hl|].
            destruct (Z_lt_le_dec q (Sfr fr + 51)) as [Hl2|Hg2]; [|right; exact Hg2].
            exfalso. apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia|].
            unfold shadow_addr.
            replace (fr + 8 * (q - Sfr fr)) with ((q - Sfr fr) * 8 + (fr / 8) * 8)
              by (Z.div_mod_to_equations; lia).
            rewrite Z.div_add by lia. rewrite Z.div_mul by lia. unfold Sfr, shadow_addr. lia.
          - destruct (Z_lt_le_dec q (fr + 336)) as [Hl|Hg]; [left; exact Hl|].
            destruct (Z_lt_le_dec q (fr + 336 + 72)) as [Hl2|Hg2]; [|right; exact Hg2].
            exfalso. apply Hnfs. lia.
          - destruct (Z_lt_le_dec q (AC.aspZ regs - ASAN_MEMCPY_K)) as [Hl|Hg]; [left; exact Hl|].
            destruct (Z_lt_le_dec q (AC.aspZ regs)) as [Hl2|Hg2]; [|right; exact Hg2].
            exfalso. apply Hns. right. left.
            unfold APPMEM_END, ASAN_MEMCPY_K, FN_STACK, AF.SLOT_STACK in *. lia. }
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  (exists b, mbyte rsegs mem' q = Some b)).
        { intros q Hq Hb.
          destruct (outside_dec (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) q) as [Ho|Ho].
          - unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
            rewrite MState.unsigned_lit by exact Hq. exact Ho.
          - pose proof (f12_in3 (Sfr fr) (fr + 336) (AC.aspZ regs) q Ho) as Hin.
            assert (Hrd : exists b, mrd rsegs mem' (wa q) = Some b).
            { destruct Hin as [Hsl|[Hdd|Hst]].
              - destruct (HSH (q - Sfr fr - 42) ltac:(lia)) as (_ & _ & Hrdz).
                pose proof (Hrdz 0%nat ltac:(cbn; lia)) as Hb2.
                change (Z.of_nat 0) with 0 in Hb2. rewrite Z.add_0_r in Hb2. cbn [nth_error] in Hb2.
                replace (Sfr fr + 42 + (q - Sfr fr - 42)) with q in Hb2 by lia.
                exists (Z_to_bv 8 0). exact Hb2.
              - apply (ba_rd mem' (fr + 336) (t_FG (g_in g) j) q HbD).
                rewrite t_FG_length. lia.
              - destruct ST' as (_ & _ & HS).
                destruct (HS q ltac:(unfold ASAN_MEMCPY_K, FN_STACK in *; lia)) as (_ & b2 & Hb2).
                exists b2. exact Hb2. }
            destruct Hrd as (b2 & Hb2). unfold mbyte, mrd, wa in *.
            destruct (mem' (Z_to_bv 64 q)) as [b'|] eqn:Em; [exists b'; reflexivity | exists b2; exact Hb2]. }
        destruct (Tac_fs.a_fs_ok_store_AH AC.ASYMS _ _ _ _
                    (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs))
                    (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md FSc
                    LAWS HAH HwFSc HFScr ltac:(unfold APPMEM_END in *; lia) MU Hwmon Hpres
                    ltac:(intros q Hq; pose proof (Tac_fs.fs_meta_below FSc q Hq) as HB';
                          pose proof (f12_fs_meta_above FSc q Hq) as HB2';
                          pose proof (HFSapp q ltac:(unfold AC.FS_SIZE in *; lia)) as Hapq;
                          pose proof (HshIS (Sfr fr + 42) ltac:(lia)) as Hsh42;
                          pose proof (HshIS (Sfr fr + 50) ltac:(lia)) as Hsh50;
                          apply f12_out3;
                          [ unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG,
                              HIGHMEM_BEG, APPMEM_END in *; lia
                          | unfold AC.FS_SIZE in *; lia
                          | unfold ASAN_MEMCPY_K, FN_STACK, AF.SLOT_STACK, AC.FS_SIZE in *; lia ])
                    Hstore)
          as (HAH2 & Hown2 & Hstk2 & Hhi2).
        split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2]. }
    destruct HAHSTK as (HAH' & HOWN' & HSTK' & HSTKHI').
    (* the frame's FRAME_SHADOW shadow bytes afterwards: the nine the segment wrote and the rest, kept *)
    assert (Hshnew : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
    { rewrite FRAME_SHADOW_val in Hshf |- *. change (Z.to_nat 392) with 392%nat in Hshf |- *.
      destruct Hshf as (sh & Hb & Hl).
      assert (Hsome : forall i, (i < 392)%nat -> mrd rsegs mem' (wa (Sfr fr + Z.of_nat i)) <> None).
      { intros i Hi.
        destruct (Z_le_gt_dec (Sfr fr + 42) (Sfr fr + Z.of_nat i)) as [Hg1|Hl1];
          [destruct (Z_lt_ge_dec (Sfr fr + Z.of_nat i) (Sfr fr + 51)) as [Hl2|Hg2]|].
        - destruct (HSH (Z.of_nat i - 42) ltac:(lia)) as (_ & _ & Hrd).
          pose proof (Hrd 0%nat ltac:(cbn; lia)) as Hb2.
          change (Z.of_nat 0) with 0 in Hb2. rewrite Z.add_0_r in Hb2. cbn [nth_error] in Hb2.
          replace (Sfr fr + 42 + (Z.of_nat i - 42)) with (Sfr fr + Z.of_nat i) in Hb2 by lia.
          rewrite Hb2. discriminate.
        - destruct Hb as (_ & _ & Hrd). pose proof (Hrd i ltac:(lia)) as Hb2.
          assert (Hkeep : mrd rsegs mem' (wa (Sfr fr + Z.of_nat i)) = mrd rsegs mem (wa (Sfr fr + Z.of_nat i))).
          { unfold mrd. rewrite (MU (wa (Sfr fr + Z.of_nat i))); [reflexivity|].
            rewrite wa_unsigned by (unfold HIGHMEM_BEG, LOWMEM_END in *; lia).
            apply Hshout; [apply HshIS; lia | lia]. }
          rewrite Hkeep, Hb2. destruct (nth_error sh i) eqn:En; [discriminate|].
          exfalso. apply nth_error_None in En. lia.
        - destruct Hb as (_ & _ & Hrd). pose proof (Hrd i ltac:(lia)) as Hb2.
          assert (Hkeep : mrd rsegs mem' (wa (Sfr fr + Z.of_nat i)) = mrd rsegs mem (wa (Sfr fr + Z.of_nat i))).
          { unfold mrd. rewrite (MU (wa (Sfr fr + Z.of_nat i))); [reflexivity|].
            rewrite wa_unsigned by (unfold HIGHMEM_BEG, LOWMEM_END in *; lia).
            apply Hshout; [apply HshIS; lia | lia]. }
          rewrite Hkeep, Hb2. destruct (nth_error sh i) eqn:En; [discriminate|].
          exfalso. apply nth_error_None in En. lia. }
      destruct (f12_ex_list (fun i => mrd rsegs mem' (wa (Sfr fr + Z.of_nat i))) 392 Hsome) as (l & Hl2 & Hf).
      exists l. split; [|exact Hl2]. split; [unfold LOWMEM_END in *; lia|].
      split; [rewrite Hl2; unfold HIGHMEM_BEG in *; lia|].
      intros i Hi. rewrite Hl2 in Hi. exact (Hf i Hi). }
    (* the globals of frame_AG stay addressable: they lie below AC.GT, so below the frame's shadow *)
    assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
    { intros a Hin. pose proof (HAG a Hin) as HA1.
      apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' a 1 HA1 MU).
      intros i Hi. destruct HA1 as (Ha0 & _ & _ & HAb1). destruct (HAb1 i Hi) as (Hap & _).
      replace (a + i) with a in * by lia.
      apply Hshout; [apply shadow_of_app; exact Hap|].
      assert (Haglow : a < AC.GT).
      { destruct Hin as (lo2 & len2 & Hil & Hr2'). unfold AF.frame_AG in Hil. cbn in Hil.
        unfold AC.GT. repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]). destruct Hil. }
      pose proof (f12_sh_lt fr a 0 Hfr8 ltac:(lia) ltac:(lia) ltac:(unfold AC.GT in *; lia)) as Hlt.
      lia. }
    (* rebuild FRA at mem', then move it to regs' / md' *)
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem' md).
    { apply (fra_run g fr (hb1 phi (AC.a_size (flen g j))) regs mem mem' md _ HFRA MU WM Hrtdj HroM).
      - intros a Hin.
        destruct (Z_le_gt_dec (Sfr fr + 42) a) as [Hg1|Hl1];
          [destruct (Z_lt_ge_dec a (Sfr fr + 51)) as [Hl2|Hg2]|].
        + destruct (HSH (a - Sfr fr - 42) ltac:(lia)) as (_ & _ & Hrd).
          pose proof (Hrd 0%nat ltac:(cbn; lia)) as Hb2.
          change (Z.of_nat 0) with 0 in Hb2. rewrite Z.add_0_r in Hb2. cbn [nth_error] in Hb2.
          replace (Sfr fr + 42 + (a - Sfr fr - 42)) with a in Hb2 by lia.
          exists (Z_to_bv 8 0). exact Hb2.
        + destruct (HSW0 a Hin) as (_ & b & Hb). exists b. unfold mrd in *.
          assert (Hab : 0 <= a < 2 ^ 64) by
            (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin; lia).
          rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. apply Hshout; [exact Hin | lia].
        + destruct (HSW0 a Hin) as (_ & b & Hb). exists b. unfold mrd in *.
          assert (Hab : 0 <= a < 2 ^ 64) by
            (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin; lia).
          rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. apply Hshout; [exact Hin | lia].
      - exact HAH'.
      - exact HSTK'.
      - apply (stk_keep (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem'
                 (g_S g - AF.SLOT_STACK) (g_S g)); [exact Hwin | exact MU | exact WM |].
        intros x Hx Ho.
        pose proof (f12_in3 (Sfr fr) (fr + 336) (AC.aspZ regs) x Ho) as Hin3.
        destruct Hin3 as [Hsl|[Hdd|Hst]].
        + (* the window is high application memory, the nine shadow bytes are below it *)
          exfalso. unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
        + (* the copy's destination: its post bytes are the record *)
          apply (ba_rd mem' (fr + 336) (t_FG (g_in g) j) x HbD). rewrite t_FG_length. lia.
        + (* the copy's own stack window: readable by the contract's stk post *)
          destruct ST' as (_ & _ & HS).
          destruct (HS x ltac:(unfold ASAN_MEMCPY_K, FN_STACK in *; lia)) as (_ & b & Hb).
          exists b. exact Hb.
      - exact Hshnew.
      - exact HAG'.
      - intros x Hx. apply Hfrout; lia.
      - intros A' HA'b HA' x Hx.
        assert (EA' : A' = A).
        { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in H9; rewrite <- HA'; exact H9).
          apply (f_equal (bv_unsigned (n := 64))) in E.
          rewrite !MState.unsigned_lit in E by lia. exact E. }
        subst A'. apply HoutA; lia.
      - intros A' HA'b HA' x Hx.
        assert (EA' : A' = A).
        { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in H9; rewrite <- HA'; exact H9).
          apply (f_equal (bv_unsigned (n := 64))) in E.
          rewrite !MState.unsigned_lit in E by lia. exact E. }
        subst A'. apply HoutA; lia.
      - intros x Hx. apply f12_out3.
        + unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
        + lia.
        + unfold ASAN_MEMCPY_K in *. lia.
      - intros x Hx. apply f12_out3.
        + unfold LOWMEM_END, AC.GT in *. lia.
        + unfold AC.GT in *. lia.
        + unfold AC.GT, ASAN_MEMCPY_K, HIGHMEM_BEG in *. lia.
      - intros a Ha1 Ha2. pose proof (HWA a Ha1 Ha2) as HA1. pose proof HA1 as HA2.
        apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' a 1 HA1 MU).
        intros i Hi. destruct HA2 as (Ha0 & _ & _ & HAb1). destruct (HAb1 i Hi) as (Hap & _).
        replace (a + i) with a in * by lia.
        apply Hshout; [apply shadow_of_app; exact Hap|].
        intros Hsl. pose proof (f12_sh_back fr a Hfr8 ltac:(lia) ltac:(lia) Hsl) as Hfin.
        apply Ha2. lia.
      - (* FSREC: no app byte below stklo outside the frame is written *)
        intros x Happx Hxlo Hxnf.
        destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo2 & _).
        apply f12_out3.
        + destruct (Z_lt_ge_dec x (Sfr fr + 42)) as [Dq1|Dq1]; [left; exact Dq1|].
          destruct (Z_lt_ge_dec x (Sfr fr + 51)) as [Dq2|Dq2]; [|right; lia].
          exfalso. exact (app_not_shadow x Happx (HshIS x ltac:(lia))).
        + lia.
        + unfold ASAN_MEMCPY_K, FN_STACK, AF.SLOT_STACK in *. lia.
      - (* the input block: app memory below stklo and apart from the frame (fra_in_apart); its shadow bytes are
           not the frame's nine (those shadow [fr + 336, fr + 408)) *)
        intros x Hx.
        destruct (fra_in_apart B APIf ra g fr _ regs mem md HFRA x Hx) as (Hxa & Hxlo & Hxfr & _).
        destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo3 & _).
        pose proof (shadow_of_app x Hxa) as Hsx.
        pose proof (HshIS (Sfr fr + 42) ltac:(lia)) as Hs1. pose proof (HshIS (Sfr fr + 50) ltac:(lia)) as Hs2.
        pose proof (Happ (fr + 336) ltac:(lia)) as Hd1. pose proof (Happ (fr + 407) ltac:(lia)) as Hd2.
        assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
        unfold in_shadow, app_mem, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END
          in Hxa, Hsx, Hs1, Hs2, Hd1, Hd2.
        revert Hx Hxa Hxlo Hxfr Hwlo3 Hsx Hs1 Hs2 Hd1 Hd2 Hx0; rs_hide_all;
          intros Hx Hxa Hxlo Hxfr Hwlo3 Hsx Hs1 Hs2 Hd1 Hd2 Hx0.
        split; apply f12_out3.
        + lia.
        + lia.
        + unfold ASAN_MEMCPY_K. lia.
        + destruct (Z_lt_ge_dec (shadow_addr x) (Sfr fr + 42)) as [Dq1|Dq1]; [left; exact Dq1|].
          destruct (Z_lt_ge_dec (shadow_addr x) (Sfr fr + 51)) as [Dq2|Dq2]; [|right; lia].
          exfalso. pose proof (f12_sh_back fr x Hfr8 ltac:(lia) Hx0 ltac:(lia)) as Hin. lia.
        + lia.
        + pose proof HaspH as Hh. unfold HIGHMEM_BEG in Hh. unfold ASAN_MEMCPY_K. lia. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (Tac_slot.sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem' md md' HFRA');
        [exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat]. }
    (* ENT moves across the run: every byte the segment writes is in the frame, in the frame's shadow or in the
       slot window below the entry sp, so no byte of an entry block, of the image or of the stack at or above S
       changes; the model only materializes pages. *)
    assert (HENT'' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { eapply ent_mat; [|exact Hmat].
      eapply ent_store with (W := f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)).
      all: try exact FF.
      all: try exact HENT.
      all: try exact HFRA.
      all: try exact MU.
      all: try exact HSTK'.
      all: try exact HSTKHI'.
      - intros x Hx.
        destruct (outside_dec (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) x) as [Ho|Ho]; [left; exact Ho|].
        pose proof (f12_in3 (Sfr fr) (fr + 336) (AC.aspZ regs) x Ho) as Hin.
        destruct Hin as [Hsl|[Hdd|Hst]].
        + right. right. right. lia.
        + right. right. left. lia.
        + right. left. unfold ASAN_MEMCPY_K, FN_STACK, AF.SLOT_STACK in *. lia.
      - intros a Hia Hown. apply (proj2 (HOWN' a)). exact Hown. }
    (* the carried data: everything the exit cut names lies outside the write set, except the copy's destination.
       Phi's block crosses it: the nine shadow bytes shadow [fr + 336, fr + 408) (f12_sh_back), which is inside the
       frame, and the block is not (Hblk). *)
    assert (HAd' : addressable mem' phi (AC.a_size (flen g j))).
    { pose proof HAd as HAd2.
      apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' phi _ HAd MU).
      intros i Hi. destruct HAd2 as (Hp0 & _ & _ & HAb1). destruct (HAb1 i Hi) as (Hap & _).
      apply Hshout; [apply shadow_of_app; exact Hap|].
      intros Hsl. pose proof (f12_sh_back fr (phi + i) Hfr8 ltac:(lia) ltac:(lia) Hsl) as Hfrin.
      apply (Hblk (phi + i)); lia. }
    (* the local `first` [fr + 2880, fr + 2920) (RAD's third range, FSj's bytes) stays addressable: its shadow
       bytes are S(fr) + 360 .. 364, not the nine *)
    assert (Hfst' : addressable mem' (fr + 2880) 40).
    { apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' (fr + 2880) 40 HRfst MU).
      intros i Hi. apply Hshout.
      - apply shadow_of_app. apply Happ. lia.
      - pose proof (f12_sh_ge fr (fr + 2880 + i) 360 Hfr8 ltac:(lia) ltac:(lia)) as H1. lia. }
    assert (HIexit : Inv_B82340_at B APIf ra g j
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82340) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|].
      split; [exact Hj|].
      split; [split; [exact Hphinz | exact HAd']|].
      (* s2 = Phi, s4 = len *)
      split; [unfold rg in H18 |- *; rewrite Fr18; exact H18|].
      split; [unfold rg in H20 |- *; rewrite Fr20; exact H20|].
      (* FTURN: the two cursor spills and the frame's bytes at Phi, inside Phi's block *)
      split.
      { pose proof HFT as (T224 & T232 & TPB & TPL).
        split; [exact (SPK 224 _ ltac:(lia) T224)|].
        split; [exact (SPK 232 _ ltac:(lia) T232)|].
        split; [|exact TPL].
        eapply fl_bytes; [exact TPB | exact MU |].
        intros x Hx. apply Hphiout. unfold flen in *. lia. }
      (* LK (Tac_ro.lk_keep: the turn index and FLI's spills over the kept s1, our[], and FLI's memory facts on
         mem'), the copy's result, FM and FSj *)
      split.
      { split.
        { apply (Tac_ro.lk_keep g fr j regs regs' mem mem' HLK).
          - unfold rg in H27 |- *; rewrite Fr27; exact H27.
          - apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' (fr + 2624) 6
                     HadOur MU).
            intros i Hi. apply Hshout.
            + apply shadow_of_app. apply Happ. lia.
            + pose proof (f12_sh_ge fr (fr + 2624 + i) 328 Hfr8 ltac:(lia) ltac:(lia)) as H1. lia.
          - apply (stk_keep (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' fr (fr + FRAME_BYTES));
              [exact HstkF | exact MU | exact WM |].
            intros x Hx Ho.
            destruct (Z_lt_ge_dec x (fr + 336)) as [Dq1|Dq1];
              [|destruct (Z_lt_ge_dec x (fr + 336 + 72)) as [Dq2|Dq2]].
            + exfalso. apply Ho. apply Hfrout; lia.
            + apply (ba_rd mem' (fr + 336) (t_FG (g_in g) j) x HbD). rewrite t_FG_length. lia.
            + exfalso. apply Ho. apply Hfrout; lia.
          - (* RAD: the identity record's addressable bytes *)
            apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' (fr + 2688) 38 HRid MU).
            intros i Hi. apply Hshout.
            + apply shadow_of_app. apply Happ. lia.
            + pose proof (f12_sh_ge fr (fr + 2688 + i) 336 Hfr8 ltac:(lia) ltac:(lia)) as H1. lia.
          - (* RAD: the fragment record's addressable bytes *)
            apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' (fragb fr) 72 HRfg MU).
            intros i Hi. apply Hshout.
            + apply shadow_of_app. apply Happ. unfold fragb in *. lia.
            + pose proof (f12_sh_ge fr (fragb fr + i) 346 Hfr8 ltac:(lia) ltac:(unfold fragb in *; lia))
                as H1. lia.
          - (* KNT: the kind-name table is image data below GT <= fr, so below the write set; its shadow bytes lie
               below the frame's shadow S(fr) (f12_sh_lt), so they are not the nine *)
            destruct HKNT as (HKb & HKa). split.
            + eapply fl_bytes; [exact HKb | exact MU |].
              change (length KNC.kind_name_bytes) with 112%nat.
              intros x Hx. pose proof HK3b as (HK3l & _).
              apply f12_out3; [left | left | left];
                unfold KNC.KIND_NAME, AC.GT, LOWMEM_END, HIGHMEM_BEG, ASAN_MEMCPY_K in *; lia.
            + pose proof HKa as (_ & _ & _ & HKa1).
              apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' KNC.KIND_NAME 112
                       HKa MU).
              intros i Hi. destruct (HKa1 i Hi) as (Hap & _).
              apply Hshout; [apply shadow_of_app; exact Hap|].
              pose proof (f12_sh_lt fr (KNC.KIND_NAME + i) 0 Hfr8 ltac:(lia)
                            ltac:(unfold KNC.KIND_NAME; lia) ltac:(unfold KNC.KIND_NAME, AC.GT in *; lia)) as H1.
              lia.
          - exact Hfst'.
          - unfold OURb in *. eapply fl_bytes; [exact HOURb | exact MU |].
            rewrite OUR_length. intros x Hx. apply Hfrout; lia.
          - intros off v Hoff Hs. exact (SPK off v ltac:(lia) Hs). }
      (* the copy's result: the before-call copy of the record at fr + 336 *)
      split; [exact HbD|].
      (* FM (v1.9): [A+184], s8, s6, s9 and [A+312] *)
      split.
      { split; [exact (SPK 184 _ ltac:(lia) M184)|].
        split; [unfold rg in M24 |- *; rewrite Fr24; exact M24|].
        split; [unfold rg in M22 |- *; rewrite Fr22; exact M22|].
        split; [unfold rg in M25 |- *; rewrite Fr25; exact M25 | exact (SPK 312 _ ltac:(lia) M312)]. }
      (* FSj: the local `first`, frame bytes outside the copy's destination *)
      { apply (Tac_ro.fsj_keep g fr j regs regs' mem mem' HFSj); [|exact Hfst'].
        intros a bs Ha Hab Hb. eapply fl_bytes; [exact Hb | exact MU |].
        intros x Hx. apply Hfrout; lia. } }
      (* s5 = the record buffer (0x82334 ld s5,208(s1)) *)
      split; [unfold rg; exact Fr21|].
      (* the long-frame group: Phi apart from the frame and from the fragment call's window, its 50 bytes and
         their addressability *)
      split.
      { intros H50.
        split; [destruct Hblkfr as [Hd|Hd]; [left | right]; unfold AC.a_size, flen in *; lia|].
        split; [left; rewrite HaspEq;
                unfold REAC_CTRL_IDENTITY_FRAGMENT_K, AC.a_size, flen, FN_STACK, AF.SLOT_STACK in *; lia|].
        split.
        { eapply fl_bytes; [exact (Hphig H50) | exact MU |].
          rewrite t_g_length. intros x Hx. apply Hphiout. unfold AC.a_size, flen in *; lia. }
        apply (addressable_prefix mem' phi (AC.a_size (flen g j)) 50);
          [exact HAd' | unfold AC.a_size; lia]. }
      split; [exact HbS|].
      split.
      { apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' (fragb fr) 72 HRfg MU).
        intros i Hi. apply Hshout.
        - apply shadow_of_app. apply Happ. unfold fragb in *. lia.
        - pose proof (f12_sh_ge fr (fragb fr + i) 346 Hfr8 ltac:(lia) ltac:(unfold fragb in *; lia)) as H1.
          lia. }
      split.
      { apply (f12_addr72 mem' (fr + 336) (Sfr fr + 42)); [lia | | exact HD8 | exact HDK | |].
        - pose proof (Happ (fr + 407) ltac:(lia)) as Hap.
          unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Hap. unfold APPMEM_END. lia.
        - intros t Ht. apply Happ. lia.
        - exact HSH. }
      split.
      { apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' (fr + 256) 2 Hapa MU).
        intros i Hi. apply Hshout.
        - apply shadow_of_app. apply Happ. lia.
        - pose proof (f12_sh_lt fr (fr + 256 + i) 33 Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as H1. lia. }
      split.
      { apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' (fr + 272) 8 Happ8 MU).
        intros i Hi. apply Hshout.
        - apply shadow_of_app. apply Happ. lia.
        - pose proof (f12_sh_lt fr (fr + 272 + i) 35 Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as H1. lia. }
      split.
      { apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' (fr + 304) 8 Hapn MU).
        intros i Hi. apply Hshout.
        - apply shadow_of_app. apply Happ. lia.
        - pose proof (f12_sh_lt fr (fr + 304 + i) 39 Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as H1. lia. }
      (* RECR: both frame records are in the frame body, outside the copy's destination *)
      split.
      { pose proof HRECR as ((HIDb & HIDok) & (HFGb & HFGok)).
        split; [split|split].
        - unfold IDBe in *. eapply fl_bytes; [exact HIDb | exact MU |].
          rewrite HIDrL. intros x Hx. apply Hfrout; lia.
        - exact HIDok.
        - unfold FGBe in *. eapply fl_bytes; [exact HFGb | exact MU |].
          rewrite t_FG_length. intros x Hx. apply Hfrout; unfold fragb in *; lia.
        - exact HFGok. }
      (* FRBA: F13 / F14's record bundle, built here from FRA, FM, FS9, the Phi bytes, FPS, F272 and FLI's spills
         [A+96] / [A+112] *)
      split.
      { exists A. split; [unfold rg in *; rewrite Fr9; exact H9|]. split; [exact HAb|].
        (* the local `first` [fr + 2880, fr + 2920) is frame memory: app memory above GT (FRA, both arms) *)
        split.
        { intros a Ha. exact (Hframe a ltac:(lia)). }
        (* [A+272] in the t_8819 form (F272) *)
        split.
        { exists (b2z (t_8819 (g_in g) j)).
          split; [exact (QK 272 _ ltac:(lia) H272q)|].
          split; [destruct (t_8819 (g_in g) j); cbn [b2z]; lia|].
          split; intros E8; rewrite E8; cbn [b2z]; [lia | reflexivity]. }
        (* the record pointer kp = fr + 176 against `first`, the wrapper's scratch and the id record *)
        split; [left; lia|].
        split; [rewrite HaspEq; destruct Hfrsepb as [Hd|Hd]; [left | right]; lia|].
        split; [left; lia|].
        (* Phi against `first` (Phi's block is apart from the frame) and the wrapper's scratch, on a long frame *)
        split.
        { intros H50. split; [destruct Hblkfr as [Hd|Hd]; [left | right]; unfold AC.a_size, flen in *; lia|].
          left. rewrite HaspEq. unfold BW.BCMP_WRAP_K, AC.a_size, flen in *. lia. }
        (* the parsed-header arm: the record invariant and the two 6-byte compare operands *)
        intros H8819.
        assert (Hbig : t_big (g_in g) j = true).
        { unfold t_8819 in H8819. apply andb_prop in H8819. destruct H8819 as (H1 & _).
          apply andb_prop in H1. exact (proj1 H1). }
        assert (Hflen : 50 <= flen g j) by (unfold flen; apply Z.leb_le; exact Hbig).
        assert (Hhdr : cp_hdr (t_len (g_in g) j) (t_g (g_in g) j) = true) by exact H8819.
        assert (HGL : length (t_g (g_in g) j) = 50%nat) by apply t_g_length.
        assert (HBlen : length (t_B (g_in g) j) = 36%nat) by apply ctrlparse_length.
        assert (Hknz : fst (ctrlparse (t_len (g_in g) j) (t_g (g_in g) j)) <> 0).
        { unfold ctrlparse. rewrite Hhdr. cbn [fst]. pose proof (cp_kind_range (t_g (g_in g) j)). lia. }
        pose proof (ctrlparse_fields (t_len (g_in g) j) (t_g (g_in g) j) Hknz) as HBf. cbv zeta in HBf.
        destruct HBf as (_ & _ & _ & E20 & E21 & _).
        assert (EB : t_B (g_in g) j = cp_struct (t_g (g_in g) j) (cp_kind (t_g (g_in g) j)))
          by (unfold t_B, ctrlparse; rewrite Hhdr; reflexivity).
        destruct (f12_B_fields (t_g (g_in g) j) ltac:(rewrite HGL; lia)) as (E6a & E6b & _).
        assert (HGphi : bytes_at rsegs mem' phi (t_g (g_in g) j)).
        { eapply fl_bytes; [exact (Hphig Hflen) | exact MU |].
          rewrite HGL. intros x Hx. apply Hphiout. unfold AC.a_size, flen in *; lia. }
        pose proof HFPS as (HpB0 & HaB0).
        assert (HpB : bytes_at rsegs mem' (fr + 176) (t_B (g_in g) j)).
        { unfold pBb in HpB0. eapply fl_bytes; [exact HpB0 | exact MU |].
          rewrite HBlen. intros x Hx. apply Hfrout; lia. }
        assert (HaB : addressable mem' (fr + 176) 36).
        { apply (f12_addr_munch (f12_W (Sfr fr) (fr + 336) (AC.aspZ regs)) mem mem' (fr + 176) 36 HaB0 MU).
          intros i Hi. apply Hshout.
          - apply shadow_of_app. apply Happ. lia.
          - pose proof (f12_sh_lt fr (fr + 176 + i) 27 Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as H1. lia. }
        assert (HA50 : addressable mem' phi 50)
          by (apply (addressable_prefix mem' phi (AC.a_size (flen g j)) 50);
              [exact HAd' | unfold AC.a_size; lia]).
        split.
        { (* rec_inv *)
          split; [lia|]. split; [unfold APPMEM_END, AC.a_size, flen in *; lia|]. split; [exact Hflen|].
          split; [pose proof (ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)); unfold t_k; lia|].
          split.
          { intros a Ha. pose proof HA50 as (_ & _ & _ & HAb50).
            destruct (HAb50 (a - phi) ltac:(lia)) as (Hap & _).
            replace (phi + (a - phi)) with a in Hap by lia. exact Hap. }
          split.
          { pose proof (QK 312 _ ltac:(lia) H312q) as Hq. rewrite Hbig in Hq. exact Hq. }
          split.
          { unfold t_blk, bsl. replace (phi + 18) with (phi + Z.of_nat 18) by (cbn; lia).
            apply f12_sub; [exact HGphi | rewrite HGL; lia]. }
          split.
          { unfold bsl. replace (phi + 34) with (phi + Z.of_nat 34) by (cbn; lia).
            apply f12_sub; [exact HGphi | rewrite HGL; lia]. }
          exists (cp_v (t_g (g_in g) j) 14 + 256 * cp_v (t_g (g_in g) j) 15),
                 (cp_v (t_g (g_in g) j) 14), (cp_v (t_g (g_in g) j) 15),
                 (cp_v (t_g (g_in g) j) 16), (cp_v (t_g (g_in g) j) 17).
          split; [exact (QK 248 _ ltac:(lia) H288q)|].
          split.
          { unfold u16. replace (fr + 176 + 20) with (fr + 176 + Z.of_nat 20) by (cbn; lia).
            pose proof (f12_b2_of mem' (fr + 176) (t_B (g_in g) j) 20 HpB ltac:(rewrite HBlen; lia)) as HU.
            unfold t_B in HU. rewrite E20, E21 in HU. unfold cp_v. rewrite <- f12_le2. exact HU. }
          split; [lia|]. split; [lia|].
          split; [replace (phi + 14) with (phi + Z.of_nat 14) by (cbn; lia);
                  exact (f12_b8_of mem' phi _ 14 HGphi ltac:(rewrite HGL; lia))|].
          split; [replace (phi + 15) with (phi + Z.of_nat 15) by (cbn; lia);
                  exact (f12_b8_of mem' phi _ 15 HGphi ltac:(rewrite HGL; lia))|].
          split; [replace (phi + 16) with (phi + Z.of_nat 16) by (cbn; lia);
                  exact (f12_b8_of mem' phi _ 16 HGphi ltac:(rewrite HGL; lia))|].
          split; [replace (phi + 17) with (phi + Z.of_nat 17) by (cbn; lia);
                  exact (f12_b8_of mem' phi _ 17 HGphi ltac:(rewrite HGL; lia))|].
          split; [unfold cp_v; pose proof (f12_ubv (cp_b (t_g (g_in g) j) 14)); lia|].
          split; [unfold cp_v; pose proof (f12_ubv (cp_b (t_g (g_in g) j) 15)); lia|].
          split; [unfold cp_v; pose proof (f12_ubv (cp_b (t_g (g_in g) j) 16)); lia|].
          split; [unfold cp_v; pose proof (f12_ubv (cp_b (t_g (g_in g) j) 17)); lia|].
          split; [exact (f12_sh mem' phi (flen g j) 14 HAd' Hflen ltac:(lia))|].
          split; [exact (f12_sh mem' phi (flen g j) 15 HAd' Hflen ltac:(lia))|].
          split; [exact (f12_sh mem' phi (flen g j) 16 HAd' Hflen ltac:(lia))|].
          split; [exact (f12_sh mem' phi (flen g j) 17 HAd' Hflen ltac:(lia))|].
          split; [reflexivity|].
          assert (Hk1 : t_k (g_in g) j = 1 <->
                        (cp_v (t_g (g_in g) j) 16 = 0 /\ cp_v (t_g (g_in g) j) 17 = 0)).
          { unfold t_k. rewrite (ctrlparse_filler (t_len (g_in g) j) (t_g (g_in g) j)). split.
            - intros (_ & A1 & A2). split; assumption.
            - intros (A1 & A2). split; [exact Hhdr | split; assumption]. }
          destruct (Z.eqb_spec (cp_v (t_g (g_in g) j) 16) 0) as [E16|E16].
          - destruct (Z.eqb_spec (cp_v (t_g (g_in g) j) 17) 0) as [E17|E17].
            + rewrite (proj2 (Z.eqb_eq (t_k (g_in g) j) 1) (proj2 Hk1 (conj E16 E17))). reflexivity.
            + replace (t_k (g_in g) j =? 1) with false; [reflexivity|].
              symmetry. apply Z.eqb_neq. intros HKk. exact (E17 (proj2 (proj1 Hk1 HKk))).
          - replace (t_k (g_in g) j =? 1) with false; [reflexivity|].
            symmetry. apply Z.eqb_neq. intros HKk. exact (E16 (proj1 (proj1 Hk1 HKk))). }
        (* the first compare operand: [A+112] = fr + 186, the struct bytes 10 .. 15 = Phi's bytes 0 .. 5 *)
        split.
        { exists (fr + 186), (firstn 6 (skipn 10 (t_B (g_in g) j))), (firstn 6 (t_g (g_in g) j)).
          split; [exact (QK 112 _ ltac:(lia) H88q)|].
          split.
          { replace (fr + 186) with (fr + 176 + Z.of_nat 10) by (cbn; lia).
            apply f12_sub; [exact HpB | rewrite HBlen; lia]. }
          split; [rewrite length_firstn, length_skipn, HBlen; reflexivity|].
          split.
          { pose proof (f12_sub mem' phi (t_g (g_in g) j) 0 6 HGphi ltac:(rewrite HGL; lia)) as HS.
            change (Z.of_nat 0) with 0 in HS. rewrite Z.add_0_r in HS. exact HS. }
          split; [rewrite length_firstn, HGL; reflexivity|].
          split; [rewrite EB, E6a; apply f12_memcmp_self; rewrite length_firstn, HGL; lia|].
          split.
          { replace (fr + 186) with (fr + 176 + 10) by lia.
            apply (addressable_sub mem' (fr + 176) 36); [exact HaB | lia | lia | lia]. }
          split; [apply Happ; lia|].
          split; [apply Happ; lia|].
          split; [rewrite HaspEq; destruct Hfrsepb as [Hd|Hd]; [left | right]; lia|].
          split; [left; lia|].
          left; lia. }
        (* the second compare operand: [A+96] = fr + 180, the struct bytes 4 .. 9 = Phi's bytes 6 .. 11 *)
        exists (fr + 180), (firstn 6 (skipn 4 (t_B (g_in g) j))), (firstn 6 (skipn 6 (t_g (g_in g) j))).
        split; [exact (QK 96 _ ltac:(lia) H80q)|].
        split.
        { replace (fr + 180) with (fr + 176 + Z.of_nat 4) by (cbn; lia).
          apply f12_sub; [exact HpB | rewrite HBlen; lia]. }
        split; [rewrite length_firstn, length_skipn, HBlen; reflexivity|].
        split.
        { pose proof (f12_sub mem' phi (t_g (g_in g) j) 6 6 HGphi ltac:(rewrite HGL; lia)) as HS.
          change (Z.of_nat 6) with 6 in HS. exact HS. }
        split; [rewrite length_firstn, length_skipn, HGL; reflexivity|].
        split; [rewrite EB, E6b; apply f12_memcmp_self; rewrite length_firstn, length_skipn, HGL; lia|].
        split.
        { replace (fr + 180) with (fr + 176 + 4) by lia.
          apply (addressable_sub mem' (fr + 176) 36); [exact HaB | lia | lia | lia]. }
        split; [apply Happ; lia|].
        split; [apply Happ; lia|].
        split; [rewrite HaspEq; destruct Hfrsepb as [Hd|Hd]; [left | right]; lia|].
        split; [left; lia|].
        left; lia. }
      (* FS9: [A+248] = 1 - sum_ok, a spill outside the write set *)
      unfold FS9. exact (SPK 248 _ ltac:(lia) HS9). }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

(* S_F12: the segment that runs through 0x82308 (the owner's form: the `bltz a0` of 0x82304 is not taken, and the
   state there is not the ir-false cut Inv_B82308_at). *)
Lemma seg_F12 : forall j : nat,
  Hat B APIf ra (Inv_B82340_at B APIf ra) j -> Hat B APIf ra (Inv_B82304_at B APIf ra) j.
Proof.
  intros j Hexit g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & H18 & H20 & HFT &
    HLK & HFM & HFSj & HRECR & Hphig & HFPS & H272 & HRCA & (r & H10 & Hrng) & HS9).
  pose proof (proj1 FF) as SEGS. subst c. rewrite SEGS.
  apply (f12_at j g phi fr 0x82304 r regs mem md Hexit HFRA HENT);
    [ repeat (split; [eassumption|]); exact HS9
    | right; split; [reflexivity | split; [exact H10 | exact Hrng]] ].
Qed.

(* S_F12_298: the ir-false / short-frame path from F10, which shares the run from 0x82308 to 0x82340. *)
Lemma seg_F12_298 : forall j : nat,
  Hat B APIf ra (Inv_B82340_at B APIf ra) j -> Hat B APIf ra (Inv_B82308_at B APIf ra) j.
Proof.
  intros j Hexit g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & HK & HFSj & Hphig & Hir & HFT &
    HRECR & HFPS & H272 & HRCA).
  pose proof (proj1 FF) as SEGS. subst c. rewrite SEGS.
  pose proof HK as (Hgn & Hj & HHB & HLK & (A & HFL & HAb & H280 & H184 & H200 & H240 & H288 & H312) &
    H18 & H20 & Hs9 & Hs8 & Hs5 & Hs6 & Hargs).
  pose proof HFL as (Hs1 & _).
  (* v1.9 f10_K: H288 = [A+248] = 1 - sum_ok, Hs9 = s9 = sum_ok, Hs5 = [A+184] = the fill flag, Hs6 = s6 = 1 *)
  assert (HFM : FM g j phi fr regs mem).
  { split; [exact Hs5|]. split; [exact Hs8|]. split; [exact Hs6|]. split; [exact Hs9|].
    exists A. split; [exact Hs1 | exact H312]. }
  assert (HS9 : FS9 g j regs mem) by (exists A; split; [exact Hs1 | exact H288]).
  apply (f12_at j g phi fr 0x82308 0 regs mem md Hexit HFRA HENT);
    [ repeat (split; [eassumption|]); exact HS9 | left; reflexivity ].
Qed.

End S.
