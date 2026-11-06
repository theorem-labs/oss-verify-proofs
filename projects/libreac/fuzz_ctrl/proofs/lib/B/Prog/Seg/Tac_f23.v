(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 613 of its 717 lines of code are new or changed and 907 lines of the source are left out. *)
(* Shared helpers of the image-B segments F23, F24 and F25 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, patched
   image B; lib/B/Prog/Seg/F23.v, F24.v, F25.v): the window 0x82844-0x828a4 over the checked_memcpy (0x82870),
   reac_ports_parse (0x82884) and reac_ports_unknown (0x828a0) calls.  Each of the three segments writes frame bytes
   (the ports words [fr + 128, fr + 140), the first byte fr + 160), frame shadow bytes (S(fr) + 16, + 17, + 20), a
   callee's stack window below sp and (F23) the spill [A + 272, A + 280) of the save area.  One transport,
   tf_fra_ent, moves FRA and ENT across such a write set W from a classification of the addresses W holds.  Its body
   is lib/B/Prog/Seg/F12.v's fra_run (copied here as tf_fra_run: F12 is a segment file, not a helper file) and
   seg_F12's heap / stack-bound / shadow-list steps, made generic in W.  The memory helpers below are F12's and F26's,
   copied for the same reason. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Exec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag.
Import ListNotations.
(* lib/Lib's chain may load lib/Reusable/YK11.v, so the short name YK11 could resolve to that copy; the registers
   and FPState here must be image B's, as SlotInv's are (lib/B/Prog/Seg/F26.v). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module BZB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.BzBridge.
Module UEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.
Module LEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---- runs: a Lib.Exec run is a UL run (the two step relations have the same body; lib/B/Prog/Seg/F26.v). ---- *)

Lemma tf_lu_msteps : forall s s', LEx.msteps rsegs s s' -> UEx.msteps rsegs s s'.
Proof.
  intros s s' H. induction H as [s|s s1 s2 Hs _ IH]; [apply UEx.msteps_refl|].
  eapply UEx.msteps_cons; [exact Hs | exact IH].
Qed.
Lemma tf_lu_evt : forall Q ms, LEx.evt rsegs Q ms -> UEx.evt rsegs Q ms.
Proof. intros Q ms (ms' & H & HQ). exists ms'. split; [exact (tf_lu_msteps _ _ H) | exact HQ]. Qed.

(* ---- memory helpers (lib/B/Prog/Seg/F12.v) ---- *)

Lemma tf_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn [outside]; intros x; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [right; intros (C & _); lia | left; split; [lia | exact H]].
Qed.

Lemma tf_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
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
Lemma tf_stk_keep : forall W m m' lo hi,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) ->
  stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HR.
  split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  split; [apply WM; exact Hv|].
  destruct (tf_outside_dec W a) as [Ho|Ho].
  - exists b. unfold mrd in *. rewrite (MU (wa a)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
  - exact (HR a Ha Ho).
Qed.

(* shadow_addr on an 8-aligned base: monotone, and a frame offset gives a shadow index. *)
Lemma tf_sh_ge : forall fr x c, fr mod 8 = 0 -> 0 <= fr -> fr + 8 * c <= x -> Sfr fr + c <= shadow_addr x.
Proof. intros fr x c H8 Hfr Hx. unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. Qed.

Lemma tf_sh_lt : forall fr x c, fr mod 8 = 0 -> 0 <= fr -> 0 <= x -> x < fr + 8 * c -> shadow_addr x < Sfr fr + c.
Proof. intros fr x c H8 Hfr Hx0 Hx. unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. Qed.

(* A byte whose shadow byte is one of the frame's FRAME_SHADOW (392) lies in the frame. *)
Lemma tf_sh_back : forall fr x, fr mod 8 = 0 -> 0 <= fr -> 0 <= x ->
  Sfr fr <= shadow_addr x < Sfr fr + FRAME_SHADOW -> fr <= x < fr + FRAME_BYTES.
Proof.
  intros fr x H8 Hfr Hx0 Hx. rewrite FRAME_SHADOW_val in Hx. rewrite FRAME_BYTES_val.
  unfold Sfr, shadow_addr, ASAN_K in Hx. Z.div_mod_to_equations. lia.
Qed.

Lemma tf_sh_idx : forall D t, D mod 8 = 0 -> 0 <= t -> shadow_addr (D + t) = shadow_addr D + t / 8.
Proof.
  intros D t H8 Ht. unfold shadow_addr.
  replace (D + t) with (t + (D / 8) * 8) by (Z.div_mod_to_equations; lia).
  rewrite Z.div_add by lia. lia.
Qed.

(* A one-interval write set misses every address below it or at or above its top. *)
Lemma tf_out1 : forall lo hi x, (x < lo \/ hi <= x) -> outside [(lo, hi)] x.
Proof. intros lo hi x H. cbn [outside]. split; [lia | exact I]. Qed.

(* A carried bytes_at of 8 bytes in the form the load tactic consumes. *)
Lemma tf_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_read rsegs m a bs 0 8 H ltac:(lia) ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

(* The bytes of a CB cell, and the cell of a writable byte range. *)
Lemma tf_cb_bytes : forall m a n bs, rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof.
  intros m a n bs ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

(* Z_to_bv 64 is injective on [0, 2^64): the spill base read twice is the same base. *)
Lemma tf_spill_base : forall regs A A' m off v,
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
Lemma tf_spill_keep : forall regs regs' m m' W A off v,
  rg regs 9 A -> getr regs' 9 = getr regs 9 -> 0 <= A < APPMEM_END -> 0 <= off <= 440 ->
  spill regs m off v -> munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v H9 E9 HAb Hoff (A3 & HA3 & Hq) MU Hout.
  pose proof (tf_spill_base regs A A3 m off v H9 HA3 HAb Hoff Hq) as EA. subst A3.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply Hout. lia.
Qed.

(* A spill read at the cut's own base. *)
Lemma tf_spill_q : forall regs m A off v, rg regs 9 A -> 0 <= A < APPMEM_END -> 0 <= off <= 440 ->
  spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HAb Hoff (A3 & HA3 & Hq).
  pose proof (tf_spill_base regs A A3 m off v H9 HA3 HAb Hoff Hq) as EA. subst A3. exact Hq.
Qed.

(* addressable survives writes that miss the shadow bytes of its own range. *)
Lemma tf_addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as His.
  assert (Hr : 0 <= shadow_addr (p + i) < 2 ^ 64)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in His; lia).
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. exact (HW i Hi).
Qed.

(* A small shadow value reads back as itself. *)
Lemma tf_signed8 : forall v, 0 <= v <= 7 -> bv_signed (Z_to_bv 8 v) = v.
Proof.
  intros v Hv.
  assert (E : v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7) by lia.
  decompose [or] E; subst v; reflexivity.
Qed.

(* The bytes [D, D + n) of an 8-aligned range are addressable when each byte's shadow byte (the granule's metadata
   byte at shadow_addr D + t / 8) is 0, or is v with t mod 8 < v <= 7: the instrumented check passes for each. *)
Lemma tf_addr_sh : forall m D n,
  0 <= D -> 0 <= n -> D + n <= APPMEM_END -> D mod 8 = 0 ->
  (forall t, 0 <= t < n -> app_mem (D + t)) ->
  (forall t, 0 <= t < n -> exists v, b8 m (shadow_addr D + t / 8) v /\ 0 <= v <= 7 /\
     (v = 0 \/ t mod 8 < v)) ->
  addressable m D n.
Proof.
  intros m D n HD0 Hn HDE HD8 Happ Hsh.
  split; [exact HD0|]. split; [exact Hn|]. split; [exact HDE|].
  intros i Hi. split; [apply Happ; lia|].
  destruct (Hsh i Hi) as (v & (Hb0 & Hb1 & Hb2) & Hv & Hok).
  pose proof (Hb2 0%nat ltac:(cbn; lia)) as Hrd.
  change (Z.of_nat 0) with 0 in Hrd. rewrite Z.add_0_r in Hrd. cbn [nth_error] in Hrd.
  exists (Z_to_bv 8 v). rewrite (tf_sh_idx D i HD8 ltac:(lia)). split; [exact Hrd|].
  unfold shadow_ok. rewrite (tf_signed8 v Hv).
  destruct Hok as [E|E]; [left; exact E|]. right. split; [|lia].
  replace (D + i) with (i + (D / 8) * 8) by (Z.div_mod_to_equations; lia).
  rewrite Z.mod_add by lia. exact E.
Qed.

(* One byte store: the byte reads back; a store at another address keeps a byte. *)
Lemma tf_wsame : forall m a v (bs : list byte), bs = [Z_to_bv 8 v] -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  b8 (write_to_mem m (wa a) bs) a v.
Proof.
  intros m a v bs -> Ha Hl. unfold b8. apply bytes_at_write_same; [exact Ha | cbn [length]; lia].
Qed.

Lemma tf_wother : forall m a (bs : list byte) c v, length bs = 1%nat -> b8 m c v ->
  0 <= a -> a + 1 <= 2 ^ 64 -> (c + 1 <= a \/ a + 1 <= c) -> b8 (write_to_mem m (wa a) bs) c v.
Proof.
  intros m a bs c v Hl Hb Ha Hal Hd. unfold b8 in *.
  apply (bytes_at_write_other rsegs m a bs c [Z_to_bv 8 v] Hb); [exact Ha | rewrite Hl; cbn; lia|].
  rewrite Hl. cbn [length]. lia.
Qed.

(* Build a list from a function defined on [0, n). *)
Lemma tf_ex_list : forall (f : nat -> option byte) n, (forall i, (i < n)%nat -> f i <> None) ->
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

(* The frame's FRAME_SHADOW shadow bytes, readable in a memory, form a list of that length there. *)
Lemma tf_shF : forall fr mem',
  LOWMEM_END <= Sfr fr -> Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG ->
  (forall i, 0 <= i < FRAME_SHADOW -> exists b, mrd rsegs mem' (wa (Sfr fr + i)) = Some b) ->
  exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW.
Proof.
  intros fr mem' H1 H2 Hrd.
  rewrite FRAME_SHADOW_val in *. change (Z.to_nat 392) with 392%nat.
  assert (Hsome : forall i, (i < 392)%nat -> mrd rsegs mem' (wa (Sfr fr + Z.of_nat i)) <> None).
  { intros i Hi. destruct (Hrd (Z.of_nat i) ltac:(lia)) as (b & Hb). rewrite Hb. discriminate. }
  destruct (tf_ex_list (fun i => mrd rsegs mem' (wa (Sfr fr + Z.of_nat i))) 392 Hsome) as (l & Hl & Hf).
  exists l. split; [|exact Hl]. split; [unfold LOWMEM_END in *; lia|].
  split; [rewrite Hl; unfold HIGHMEM_BEG in *; lia|].
  intros i Hi. rewrite Hl in Hi. exact (Hf i Hi).
Qed.

(* The side stack's metadata region starts at its base (the companion of Tac_fs.fs_meta_below). *)
Lemma tf_fs_meta_above : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [ (c & Hc & Hr) | (c & jj & Hc & Hj & Heq) ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. assert (Z.of_nat c <= 10)%Z by lia. lia.
  - subst q. exact (proj1 (Tac_fs.a_fs_flag_range FS c jj Hc Hj)).
Qed.

(* Every runtime cell of rt_disjoint lies below AC.GT, so an interval above it misses them. *)
Lemma tf_rt_dj1 : forall lo hi, 6283264 <= lo -> rt_disjoint [(lo, hi)].
Proof.
  intros lo hi H.
  unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
    RT_AGLOB, RT_AGLOB_LEN.
  cbn [disjoint_from]. repeat split; first [left; lia | exact I].
Qed.

(* ... and the same for the two-, three- and four-interval write sets of F23, F24 and F25. *)
Lemma tf_rt_dj2 : forall a b c d, 6283264 <= a -> 6283264 <= c -> rt_disjoint [(a, b); (c, d)].
Proof.
  intros a b c d H1 H2.
  unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
    RT_AGLOB, RT_AGLOB_LEN.
  cbn [disjoint_from]. repeat split; first [left; lia | exact I].
Qed.

Lemma tf_rt_dj3 : forall a b c d e f, 6283264 <= a -> 6283264 <= c -> 6283264 <= e ->
  rt_disjoint [(a, b); (c, d); (e, f)].
Proof.
  intros a b c d e f H1 H2 H3.
  unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
    RT_AGLOB, RT_AGLOB_LEN.
  cbn [disjoint_from]. repeat split; first [left; lia | exact I].
Qed.

Lemma tf_rt_dj4 : forall a b c d e f u v, 6283264 <= a -> 6283264 <= c -> 6283264 <= e -> 6283264 <= u ->
  rt_disjoint [(a, b); (c, d); (e, f); (u, v)].
Proof.
  intros a b c d e f u v H1 H2 H3 H4.
  unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
    RT_AGLOB, RT_AGLOB_LEN.
  cbn [disjoint_from]. repeat split; first [left; lia | exact I].
Qed.

(* A byte range inside a stack window is writable, and its bytes read back as a list of its length. *)
Lemma tf_wr_of_stk : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi ->
  wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Hlo Hn Hhi.
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma tf_stk_bytes : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi ->
  exists bs, bytes_at rsegs m a bs /\ length bs = Z.to_nat n.
Proof.
  intros m lo hi a n (H0 & H1 & H) Hlo Hn Hhi.
  assert (Hsome : forall i, (i < Z.to_nat n)%nat -> mrd rsegs m (wa (a + Z.of_nat i)) <> None).
  { intros i Hi. destruct (H (a + Z.of_nat i) ltac:(lia)) as (_ & b & Hb). rewrite Hb. discriminate. }
  destruct (tf_ex_list (fun i => mrd rsegs m (wa (a + Z.of_nat i))) (Z.to_nat n) Hsome) as (l & Hl & Hf).
  exists l. split; [|exact Hl].
  split; [lia|]. split; [rewrite Hl; lia|].
  intros i Hi. rewrite Hl in Hi. exact (Hf i Hi).
Qed.

(* ---- ro_agree across a write set above GT (lib/B/Prog/Seg/F26.v): every read-only byte is a byte of a loaded
   segment and every loaded segment ends below GT (Tac_slot.img_tops_true). ---- *)
Lemma tf_ro_lt_GT : forall x, ro_addr rsegs x = true -> bv_unsigned x < AC.GT.
Proof.
  intros x H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|discriminate H].
  destruct (BZB.find_segment_below rsegs AC.GT (bv_unsigned x) 1 s img_tops_true E ltac:(lia))
    as [L|L]; [exact L | lia].
Qed.
Lemma tf_out_GT : forall (W : list (Z * Z)) x,
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> x < AC.GT -> outside W x.
Proof.
  intros W. induction W as [|[lo hi] W IH]; cbn; intros x H Hx; [exact I|].
  split.
  - pose proof (H lo hi ltac:(left; reflexivity)) as Hlo. lia.
  - apply IH; [intros lo' hi' Hin; apply (H lo' hi'); right; exact Hin | exact Hx].
Qed.
Lemma tf_ro_keep : forall (W : list (Z * Z)) m m',
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> munch W m m' ->
  ro_agree rsegs m -> ro_agree rsegs m'.
Proof.
  intros W m m' HGT MU Hro a Ha.
  pose proof (Hro a Ha) as H. unfold mrd in H |- *.
  rewrite (MU a (tf_out_GT W (bv_unsigned a) HGT (tf_ro_lt_GT a Ha))). exact H.
Qed.

(* The cut's heap block (phi, a_size n) at n >= 50. *)
Lemma tf_asize : forall n, 50 <= n -> AC.a_size n = n.
Proof. intros n H. unfold AC.a_size. lia. Qed.

(* The turn's frame bytes at Phi are at most its length, and the 50-byte prefix is 50 bytes. *)
Lemma tf_phi_len : forall inp j, (length (t_phi inp j) <= Z.to_nat (t_len inp j))%nat.
Proof.
  intros inp j. unfold t_phi, t_len, f_phi. rewrite length_firstn. lia.
Qed.
Lemma tf_g_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.

(* The turn's record bytes: t_g is 50 bytes, so its slices below 50 have their full length; the 20 ports bytes the
   two ports callees read are the first 20 of the 32 block bytes at blk = phi + 18. *)
Lemma tf_bsl_len : forall inp j k n, 0 <= k -> 0 <= n -> k + n <= 50 ->
  length (bsl (t_g inp j) k n) = Z.to_nat n.
Proof.
  intros inp j k n Hk Hn Hkn. unfold bsl, t_g. rewrite length_firstn, length_skipn, fr50_length. lia.
Qed.
Lemma tf_blk_len : forall inp j, length (t_blk inp j) = 32%nat.
Proof. intros inp j. unfold t_blk. rewrite tf_bsl_len by lia. reflexivity. Qed.
Lemma tf_pbs_len : forall inp j, length (t_pbs inp j) = 20%nat.
Proof. intros inp j. unfold t_pbs. rewrite tf_bsl_len by lia. reflexivity. Qed.
Lemma tf_pbs : forall inp j, t_pbs inp j = firstn 20 (t_blk inp j).
Proof. intros inp j. unfold t_pbs, t_blk, bsl. rewrite firstn_firstn. reflexivity. Qed.
Lemma tf_bytes_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n H. rewrite <- (firstn_skipn n bs) in H.
  exact (proj1 (proj1 (bytes_at_app rsegs m a _ _) H)).
Qed.

(* F27K (SlotInv) reads only s1 (the spills), s2, s8 (the sum flag, v1.9), s11 and memory. *)
Lemma tf_K : forall g j phi fr (regs regs' : bvmap 5 word) m,
  F27K g j phi fr regs m ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 24 = getr regs 24 ->
  getr regs' 27 = getr regs 27 ->
  F27K g j phi fr regs' m.
Proof.
  intros g j phi fr regs regs' m H E9 E18 E24 E27.
  unfold F27K, LK, FLI, spill, rg in *. rewrite E9, E18, E24, E27. exact H.
Qed.

(* KNT (FLI's kind-name table, 112 image bytes at KNC.KIND_NAME = 0x9f580, and their shadow bytes
   [0x8000beb0, 0x8000bebe)) across a write set that misses both ranges.  The segments of this window write
   shadow bytes of the frame, so Tac_ro.knt_munch (which asks that no shadow byte changes) does not apply. *)
Lemma tf_knt_munch : forall W (m m' : word -> option byte), KNT m -> munch W m m' ->
  (forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 -> outside W x) ->
  (forall x, 0x8000beb0 <= x < 0x8000bebe -> outside W x) -> KNT m'.
Proof.
  intros W m m' (Hb & Had) MU HO1 HO2.
  assert (HL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
  split.
  - apply (fl_bytes W m m' KNC.KIND_NAME KNC.kind_name_bytes Hb MU).
    rewrite HL. intros x Hx. apply HO1. lia.
  - apply (tf_addr_munch W m m' KNC.KIND_NAME 112 Had MU). intros i Hi. apply HO2.
    unfold shadow_addr, KNC.KIND_NAME, ASAN_K. Z.div_mod_to_equations. lia.
Qed.

Section TF.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* A byte of a live heap block of the cut is never a frame byte: on the real arm the block ends below stklo and
   the frame starts at it, on the side arm the frame is inside the side stack and no block byte is
   (lib/B/Prog/Seg/F12.v, seg_F12's Hblk). *)
Lemma tf_blk_apart : forall g fr phi n regs mem md,
  FRA B APIf ra g fr (hb1 phi n) regs mem md ->
  forall a, phi <= a < phi + n -> ~ (fr <= a < fr + FRAME_BYTES).
Proof.
  intros g fr phi n regs mem md HFRA a Ha Hfrm2.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & _).
  destruct (lw_blocks (APIf rc) (hb1 phi n ++ g_H g) mem md phi n HAH ltac:(left; reflexivity))
    as [_ _ Hend _ Hbyte].
  destruct (Hbyte a Ha) as (_ & _ & _ & _ & Hnfs).
  destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
  - destruct (Hreal a Hfrm2) as (Hlo2 & _). lia.
  - exact (Hnfs (Hfs a Hfrm2)).
Qed.

(* A byte of the cut's live block is app memory below the real stack's low bound and outside the frame: the
   heap laws place every live block below stklo (a_laws_blocks), and tf_blk_apart keeps it off the frame.  Every
   write set of this window lies in the frame, in the frame's shadow, in a callee window below sp (and
   stklo <= sp - FN_STACK, fra_win) or in the save area (above sp), so no block byte is written. *)
Lemma tf_blk_out : forall g fr phi n regs mem md,
  FRA B APIf ra g fr (hb1 phi n) regs mem md ->
  forall a, phi <= a < phi + n ->
    app_mem a /\ a < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (fr <= a < fr + FRAME_BYTES).
Proof.
  intros g fr phi n regs mem md HFRA a Ha.
  pose proof (tf_blk_apart g fr phi n regs mem md HFRA a Ha) as Hfr.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & _).
  destruct (lw_blocks (APIf rc) (hb1 phi n ++ g_H g) mem md phi n HAH ltac:(left; reflexivity))
    as [_ _ Hend _ Hbyte].
  destruct (Hbyte a Ha) as (Hap & _).
  split; [exact Hap|]. split; [lia | exact Hfr].
Qed.

(* FRA transports across a memory change (mem -> mem'), at a fixed md and fixed registers, whose write set W misses
   the frame header [fr, fr + 24), the spills s1+336 / s1+40..56, the saved registers [S - 104, S) and the low image
   [0, AC.GT) (lib/B/Prog/Seg/F12.v fra_run, verbatim). *)
Lemma tf_fra_run : forall g fr hb regs mem mem' md W,
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
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
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
  { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
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

(* FRA and ENT across a write set W of the window's kind.  Every address W holds is a frame body byte above the
   header [fr + 24, fr + FRAME_BYTES), one of the frame's FRAME_SHADOW shadow bytes [S(fr), S(fr) + FRAME_SHADOW),
   a byte of a callee's stack window [sp - FN_STACK, sp), or a spill of the save area between the fr reload /
   selector cells and the fr spill, [A + 72, A + 336) with A = s1; and the post memory is readable at each of
   them.  Then:
   - the heap invariant, the ownership of every byte and the two stack bounds move by a_laws_store (real arm: all
     four kinds are a_store_ok, the frame and the window being above stklo, the shadow bytes being the frame's) or
     by Tac_fs.a_fs_ok_store_AH (side arm: the frame and its shadow are side-stack bytes, the window and the save
     area are above stklo, and the side stack's metadata is below the frame);
   - FRA moves by tf_fra_run: the runtime's shadow map stays readable, the entry-anchored window and the frame's
     FRAME_SHADOW shadow bytes are rebuilt from the readable post, the registered globals and the window's bytes
     outside the frame keep their shadow bytes (theirs are not the frame's), and no app byte below stklo outside
     the frame (FSREC, the input block) or shadow byte of one is written;
   - ENT moves by Tac_slot.ent_store: each written byte is in the slot window [S - SLOT_STACK, S), in the frame or
     in the frame's shadow. *)
Lemma tf_fra_ent : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  ENT APIf g hb mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  rt_disjoint W -> ro_agree rsegs mem' ->
  (forall q, ~ outside W q ->
     (fr + 24 <= q < fr + FRAME_BYTES) \/ (Sfr fr <= q < Sfr fr + FRAME_SHADOW) \/
     (AC.aspZ regs - FN_STACK <= q < AC.aspZ regs) \/
     (bv_unsigned (getr regs 9) + 72 <= q < bv_unsigned (getr regs 9) + 336)) ->
  (forall q, ~ outside W q -> exists b, mrd rsegs mem' (wa q) = Some b) ->
  FRA B APIf ra g fr hb regs mem' md /\ ENT APIf g hb mem' md.
Proof.
  intros g fr hb regs mem mem' md W HFRA HENT MU WM HD HRO' HCL HRD.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  destruct (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hplace & HfrA & Hfsmeta & _).
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspillq & Hselq & Hfr40q & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof HRT as HRT0. destruct HRT0 as (HAC0 & HSW0 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; lia).
  rewrite HbvA in HCL, HfrA.
  rewrite Haspz in HCL, Hwlo, Hplace.
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH).
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (Hfrb : 0 <= fr /\ fr + FRAME_BYTES < 2 ^ 64).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in H1, H2. lia. }
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  (* the frame's FRAME_SHADOW shadow bytes are shadow addresses, below the high application memory *)
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
  (* the addresses W misses *)
  assert (Hout : forall q, (q < fr + 24 \/ fr + FRAME_BYTES <= q) -> (q < Sfr fr \/ Sfr fr + FRAME_SHADOW <= q) ->
            (q < sp - FN_STACK \/ sp <= q) -> (q < A + 72 \/ A + 336 <= q) -> outside W q).
  { intros q H1 H2 H3 H4. destruct (tf_outside_dec W q) as [Ho|Ho]; [exact Ho|].
    exfalso. destruct (HCL q Ho) as [C|[C|[C|C]]]; lia. }
  assert (HoutSh : forall x, in_shadow x -> ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) -> outside W x).
  { intros x Hin Hn. apply Hout.
    - destruct (Z_lt_le_dec x (fr + 24)) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec x (fr + FRAME_BYTES)) as [H2|H2]; [|right; exact H2].
      exfalso. exact (app_not_shadow x (Happ x ltac:(lia)) Hin).
    - lia.
    - left. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hin. lia.
    - left. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hin. lia. }
  assert (HoutApp : forall x, app_mem x -> ~ (fr <= x < fr + FRAME_BYTES) -> x < sp - FN_STACK -> outside W x).
  { intros x Hap Hn Hlo. apply Hout.
    - lia.
    - destruct (Z_lt_le_dec x (Sfr fr)) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec x (Sfr fr + FRAME_SHADOW)) as [H2|H2]; [|right; exact H2].
      exfalso. exact (app_not_shadow x Hap (HshIS x ltac:(lia))).
    - left. exact Hlo.
    - left. lia. }
  assert (Hwmon : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q Hqb Hw; exact (WM (Z_to_bv 64 q) Hw)).
  (* AH, ownership and the two stack bounds across the write set, by arm *)
  assert (HAHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                   (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a
                      <-> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
                   AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                     = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                   AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                     = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs _]]]].
    - (* real arm: the frame body, its shadow, the callee window and the save area are all a_store_ok *)
      assert (Hmc : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hns. apply MU. rewrite MState.unsigned_lit by exact Hq.
        apply Hout.
        - destruct (Z_lt_le_dec q (fr + 24)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (fr + FRAME_BYTES)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. left. specialize (Hreal q ltac:(lia)). lia.
        - destruct (Z_lt_le_dec q (Sfr fr)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (Sfr fr + FRAME_SHADOW)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. right. right.
          exists (fr + 8 * (q - Sfr fr)). split.
          + unfold shadow_addr.
            replace (fr + 8 * (q - Sfr fr)) with ((q - Sfr fr) * 8 + (fr / 8) * 8)
              by (Z.div_mod_to_equations; lia).
            rewrite Z.div_add by lia. rewrite Z.div_mul by lia. unfold Sfr, shadow_addr. lia.
          + right. left. specialize (Hreal (fr + 8 * (q - Sfr fr)) ltac:(lia)). lia.
        - destruct (Z_lt_le_dec q (sp - FN_STACK)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q sp) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. left. lia.
        - destruct (Z_lt_le_dec q (A + 72)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (A + 336)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. left. lia. }
      destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH Hmc Hwmon) as [HAH2 Hown2 Hstk2 Hhi2].
      split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2].
    - (* side arm: the frame body and its shadow belong to the side stack for frames *)
      destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSc & HFScr & HwFSc & HFSlo & HFShi).
      destruct (lw_fs_place (APIf rc) (hb ++ g_H g) mem md FSc HAH HwFSc HFScr) as [HFSgt HFSend _ HFSapp].
      pose proof (Hfsmeta FSc HwFSc HFScr) as HFSmeta.
      assert (Hstore : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                ~ (FSc <= q < FSc + AC.FS_SIZE) ->
                ~ (exists b, FSc <= b < FSc + AC.FS_SIZE /\ q = shadow_addr b) ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hns Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
        apply Hout.
        - destruct (Z_lt_le_dec q (fr + 24)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (fr + FRAME_BYTES)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hnfs. lia.
        - destruct (Z_lt_le_dec q (Sfr fr)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (Sfr fr + FRAME_SHADOW)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia|].
          unfold shadow_addr.
          replace (fr + 8 * (q - Sfr fr)) with ((q - Sfr fr) * 8 + (fr / 8) * 8)
            by (Z.div_mod_to_equations; lia).
          rewrite Z.div_add by lia. rewrite Z.div_mul by lia. unfold Sfr, shadow_addr. lia.
        - destruct (Z_lt_le_dec q (sp - FN_STACK)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q sp) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. left. lia.
        - destruct (Z_lt_le_dec q (A + 72)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (A + 336)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. left. lia. }
      assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                (exists b, mbyte rsegs mem' q = Some b)).
      { intros q Hq Hb.
        destruct (tf_outside_dec W q) as [Ho|Ho].
        - unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
          rewrite MState.unsigned_lit by exact Hq. exact Ho.
        - destruct (HRD q Ho) as (b2 & Hb2). unfold mbyte, mrd, wa in *.
          destruct (mem' (Z_to_bv 64 q)) as [b'|] eqn:Em; [exists b'; reflexivity | exists b2; exact Hb2]. }
      destruct (Tac_fs.a_fs_ok_store_AH AC.ASYMS _ _ _ _ W (hb ++ g_H g) mem mem' md FSc
                  LAWS HAH HwFSc HFScr ltac:(unfold APPMEM_END in *; lia) MU Hwmon Hpres
                  ltac:(intros q Hq; pose proof (Tac_fs.fs_meta_below FSc q Hq) as HB';
                        pose proof (tf_fs_meta_above FSc q Hq) as HB2';
                        pose proof (HFSapp q ltac:(lia)) as Hapq;
                        apply HoutApp; [exact Hapq | lia | lia])
                  Hstore)
        as (HAH2 & Hown2 & Hstk2 & Hhi2).
      split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2]. }
  destruct HAHSTK as (HAH2 & Hown2 & Hstk2 & Hhi2).
  (* the runtime's shadow map stays readable *)
  assert (HshR : forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b).
  { intros a Hin. destruct (tf_outside_dec W a) as [Ho|Ho]; [|exact (HRD a Ho)].
    destruct (HSW0 a Hin) as (_ & b & Hb). exists b. unfold mrd in *.
    assert (Hab : 0 <= a < 2 ^ 64)
      by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin; lia).
    rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho. }
  assert (HFRA' : FRA B APIf ra g fr hb regs mem' md).
  { apply (tf_fra_run g fr hb regs mem mem' md W HFRA MU WM HD HRO' HshR HAH2 Hstk2).
    - apply (tf_stk_keep W mem mem' _ _ Hwin MU WM). intros x _ Ho. exact (HRD x Ho).
    - apply (tf_shF fr mem' (proj1 HK3b) (proj2 HK3b)). intros i Hi. apply HshR. apply HshIS. lia.
    - intros a Hin. pose proof (HAG a Hin) as HA1. pose proof HA1 as HA2.
      apply (tf_addr_munch W mem mem' a 1 HA1 MU).
      intros i Hi. destruct HA2 as (Ha0 & _ & _ & HAb1). destruct (HAb1 i Hi) as (Hap & _).
      replace (a + i) with a in * by lia.
      assert (Haglow : a < AC.GT).
      { destruct Hin as (lo2 & len2 & Hil & Hr2'). unfold AF.frame_AG in Hil. cbn in Hil.
        unfold AC.GT. repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]). destruct Hil. }
      apply HoutSh; [apply shadow_of_app; exact Hap|].
      pose proof (tf_sh_lt fr a 0 Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as Hlt. lia.
    - intros x Hx. apply Hout; [lia | | | left; lia].
      + destruct (Z_lt_le_dec x (Sfr fr)) as [H1|H1]; [left; exact H1|].
        destruct (Z_lt_le_dec x (Sfr fr + FRAME_SHADOW)) as [H2|H2]; [|right; exact H2].
        exfalso. exact (app_not_shadow x (Happ x ltac:(lia)) (HshIS x ltac:(lia))).
      + destruct (Hplace FN_STACK ltac:(lia)) as [P1|P1]; [left | right]; lia.
    - intros A' HA'b HA' x Hx.
      assert (EA' : A' = A).
      { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in Hr9; rewrite <- HA'; exact Hr9).
        apply (f_equal (bv_unsigned (n := 64))) in E.
        rewrite !MState.unsigned_lit in E by lia. exact E. }
      subst A'. apply Hout; [right; lia | right; lia | right; lia | right; lia].
    - intros A' HA'b HA' x Hx.
      assert (EA' : A' = A).
      { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in Hr9; rewrite <- HA'; exact Hr9).
        apply (f_equal (bv_unsigned (n := 64))) in E.
        rewrite !MState.unsigned_lit in E by lia. exact E. }
      subst A'. apply Hout; [right; lia | right; lia | right; lia | left; lia].
    - intros x Hx. apply Hout; [right; lia | right; lia | right; lia | right; lia].
    - intros x Hx. apply Hout; [left; lia | left; unfold LOWMEM_END in *; lia | left; lia | left; lia].
    - intros a Ha1 Ha2. pose proof (HWA a Ha1 Ha2) as HA1. pose proof HA1 as HA2.
      apply (tf_addr_munch W mem mem' a 1 HA1 MU).
      intros i Hi. destruct HA2 as (Ha0 & _ & _ & HAb1). destruct (HAb1 i Hi) as (Hap & _).
      replace (a + i) with a in * by lia.
      apply HoutSh; [apply shadow_of_app; exact Hap|].
      intros Hsl. pose proof (tf_sh_back fr a Hfr8 ltac:(lia) ltac:(lia) Hsl) as Hfin.
      apply Ha2. lia.
    - intros x Happx Hxlo Hxnf. apply HoutApp; [exact Happx | exact Hxnf | lia].
    - intros x Hx.
      destruct (Hinap x Hx) as (Hxa & Hxlo & Hxfr & _).
      assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
      split.
      + apply HoutApp; [exact Hxa | exact Hxfr | lia].
      + apply HoutSh; [apply shadow_of_app; exact Hxa|].
        intros Hsl. apply Hxfr. exact (tf_sh_back fr x Hfr8 ltac:(lia) Hx0 Hsl). }
  assert (HENT' : ENT APIf g hb mem' md).
  { eapply ent_store with (W := W) (fr := fr) (regs := regs).
    all: try exact FF.
    all: try exact HENT.
    all: try exact HFRA.
    all: try exact MU.
    all: try exact Hstk2.
    all: try exact Hhi2.
    - intros x Hx. destruct (tf_outside_dec W x) as [Ho|Ho]; [left; exact Ho|].
      destruct (HCL x Ho) as [H1|[H1|[H1|H1]]].
      + right. right. left. lia.
      + right. right. right. exact H1.
      + right. left. lia.
      + right. left. lia.
    - intros a Hia Ho. exact (proj2 (Hown2 a) Ho). }
  split; [exact HFRA' | exact HENT'].
Qed.

(* The window's cuts are the official ones of lib/B/Prog/SlotInv.v: Inv_B82844_at (F23's entry), Inv_B82878_at
   (F23 / F24), Inv_B82888_at (F24 / F25) and Inv_B828a4_at (F25's exit), with SlotInv's F27K, FTL, F23GAP and
   FTURN.  At 50 <= flen g j (F27K) the frame bytes at Phi carry their 50-byte prefix (SlotInv.fturn_g).  With
   50 <= len the cut's block (phi, len) lies apart from the frame (tf_blk_apart at the first byte of the overlap). *)
Lemma tf_order : forall g fr phi n regs mem md, FRA B APIf ra g fr (hb1 phi n) regs mem md -> 50 <= n ->
  fr + FRAME_BYTES <= phi \/ phi + 50 <= fr.
Proof.
  intros g fr phi n regs mem md HFRA Hn.
  pose proof FRAME_BYTES_val as HFBv.
  destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (phi + 50) fr) as [R|R]; [right; exact R|].
  exfalso. apply (tf_blk_apart g fr phi n regs mem md HFRA (Z.max phi fr) ltac:(lia)). lia.
Qed.

End TF.
