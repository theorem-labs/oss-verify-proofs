(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 594 of its 661 lines of code are new or changed and 2490 lines of the source are left out. *)
(* Segment F21 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): the cut-to-cut range 0x824b4 .. 0x82554 /
   0x825a0 (slot-plan-asan section 2 row F21). From F20's exit cut at 0x824b4 (a0 = the checksum call's result):
   0x824b4-0x824bc the result is compared with the sum_ok spill [s1+280] - 1 and the branch to the failure block is
   shown NOT taken (the spill is exactly "the block sum of the 32 record bytes is 0", which is what the callee
   returns); 0x824c0-0x82500 when s8 = k = 6 the record bytes phi+18 / phi+19 are 4 / 3 (ctrlparse_headamp), so
   those two branches are not taken either; 0x82504-0x82550 loads the two record bytes again, sets s4 = -1 and
   either falls through to the head-amp sum loop at 0x82554 (exit 1, bytes 4 / 3) or, when a byte differs, jumps to
   0x82598 `mv a0,s7` / 0x8259c `jal reac_ctrl_headamp_record_verify` (Section Hypothesis HARV) and lands at
   0x825a0 (exit 2) with a0 = s4 = -1 = t_want_v. Every one-byte load is preceded by the instrumented check (a load
   of the shadow byte at (a >> 3) + 0x7fff8000 and a compare); the shadow byte is 0 because phi is 16-aligned and
   the granule of the byte lies inside the addressable block (shadow_ok at the granule's last byte forces 0), so
   the error path (0x82a14, 0x82a50, 0x82a5c, 0x82a68 -> __asan_report_load1) is not reached.
   The run is a Lib.Exec.evt (sl_run_lib); FRA moves across the HARV frame write [sp - 16, sp) by
   Tac_slot.sl_win_run, with the callee window from fra_win, the frame placement from fra_frame and the side-arm
   frame record from Tac_slot.fsrec_munch_lo; FLSI moves by F20.flsi_win. The cuts are the official SlotInv.v
   Inv_A824b4_at (entry, F20's exit) and Inv_A82554_at / Inv_A825a0_at (the two exits, on B7CUT). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Tac_slot F20.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame MState Regs6ss RegisterBridge Exec Cells Step Tac Bytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* ---- Byte / word helpers for the Lib engine. ---- *)
Lemma rd1 : forall m a v, b8 m a v -> ov_read_bytes rsegs m (wa a) 1 = Some [Z_to_bv 8 v].
Proof.
  intros m a v H. unfold b8 in H.
  pose proof (bytes_at_ov_read rsegs m a [Z_to_bv 8 v] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma rd8 : forall m a v, q64 m a v -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros m a v H. unfold q64 in H.
  pose proof (bytes_at_ov_read rsegs m a _ 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by (rewrite length_le8; lia).
  exact HH.
Qed.
Lemma zxb8 : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; cbn; lia.
Qed.
Lemma neqb_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a <> b ->
  negb (bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b)) = true.
Proof.
  intros a b Ha Hb Hab. apply Bool.negb_true_iff, Bool.not_true_iff_false. intro HC. apply bv_eqb_eq in HC.
  apply (f_equal bv_unsigned) in HC. rewrite !unsigned_lit in HC by lia. lia.
Qed.
Lemma ubyte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.
Lemma b8_nth : forall m a bs i x, bytes_at rsegs m a bs -> (i < length bs)%nat -> x = a + Z.of_nat i ->
  b8 m x (bv_unsigned (nth i bs (Z_to_bv 8 0))).
Proof.
  intros m a bs i x (H0 & H1 & H2) Hi ->. unfold b8, bytes_at. cbn [length].
  split; [lia|]. split; [lia|]. intros i' Hi'. destruct i' as [|i']; [|lia]. cbn [nth_error].
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r, stdpp.bitvector.definitions.Z_to_bv_bv_unsigned, H2 by exact Hi.
  apply nth_error_nth'. exact Hi.
Qed.
Lemma ba_pre2 : forall m a b0 b1 l, bytes_at rsegs m a (b0 :: b1 :: l) -> bytes_at rsegs m a [b0; b1].
Proof.
  intros m a b0 b1 l (H0 & H1 & H2). split; [exact H0|]. split.
  - cbn [length] in H1 |- *. lia.
  - intros i Hi. cbn [length] in Hi. destruct i as [|[|i]]; try lia.
    + rewrite (H2 0%nat) by (cbn [length]; lia). reflexivity.
    + rewrite (H2 1%nat) by (cbn [length]; lia). reflexivity.
Qed.
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
  nth i (bsl g k n) (Z_to_bv 8 0) = nth (Z.to_nat k + i) g (Z_to_bv 8 0).
Proof. intros g k n i Hi. unfold bsl. rewrite f21_nth_firstn by exact Hi. apply f21_nth_skipn. Qed.

(* ---- The model facts the segment reads. ---- *)
Lemma t_g_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.
Lemma t_blk_len : forall inp j, length (t_blk inp j) = 32%nat.
Proof. intros inp j. unfold t_blk, bsl. rewrite length_firstn, length_skipn, t_g_len. reflexivity. Qed.
Lemma t_g6_len : forall inp j, length (bsl (t_g inp j) 34 6) = 6%nat.
Proof. intros inp j. unfold bsl. rewrite length_firstn, length_skipn, t_g_len. reflexivity. Qed.
Lemma t_blk_skip : forall inp j, t_blk inp j = skipn 18 (t_g inp j).
Proof.
  intros inp j. unfold t_blk, bsl. change (Z.to_nat 18) with 18%nat. change (Z.to_nat 32) with 32%nat.
  apply firstn_all2. rewrite length_skipn, t_g_len. lia.
Qed.
Lemma sumok_b2z : forall inp j, 50 <= t_len inp j ->
  b2z (t_sum_ok inp j) = if blocksum (t_blk inp j) =? 0 then 1 else 0.
Proof.
  intros inp j H. unfold b2z, t_sum_ok, t_big. rewrite (proj2 (Z.leb_le 50 _) H), t_blk_skip. reflexivity.
Qed.
Lemma blk_cp : forall inp j i, (i < 32)%nat -> nth i (t_blk inp j) (Z_to_bv 8 0) = cp_b (t_g inp j) (18 + i).
Proof. intros inp j i Hi. unfold t_blk, cp_b, cp_z. rewrite bsl_nth by (cbn; lia). reflexivity. Qed.
(* k = 6 (headamp) carries the record type bytes 4 / 3 at g[18], g[19]. *)
Lemma k6_rec : forall inp j, t_k inp j = 6 -> cp_v (t_g inp j) 18 = 4 /\ cp_v (t_g inp j) 19 = 3.
Proof.
  intros inp j H. unfold t_k in H. apply ctrlparse_headamp in H. destruct H as (_ & Hr & _).
  unfold cp_rec in Hr. apply andb_prop in Hr as [Hr H19]. apply andb_prop in Hr as [_ H18].
  apply Z.eqb_eq in H18, H19. split; assumption.
Qed.
(* The head-amp verifier's result is the model's t_want_v. *)
Lemma want_hv : forall inp j,
  t_want_v inp j = (if hv (nth 0 (t_blk inp j) (Z_to_bv 8 0)) (nth 1 (t_blk inp j) (Z_to_bv 8 0))
                          (bsl (t_g inp j) 34 6) then 0 else -1).
Proof. intros inp j. unfold t_want_v. rewrite !blk_cp by lia. reflexivity. Qed.
Lemma hv_false : forall b0 b1 rec, bv_unsigned b0 <> 4 \/ bv_unsigned b1 <> 3 -> hv b0 b1 rec = false.
Proof.
  intros b0 b1 rec [H|H]; unfold hv.
  - rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H), Bool.andb_false_r, Bool.andb_false_l. reflexivity.
Qed.
Lemma ckv_sub : forall (c : bool), Z_to_bv 64 (if c then 0 else -1) = Z_to_bv 64 ((if c then 1 else 0) + -1).
Proof. intros c. destruct c; reflexivity. Qed.

(* A zero shadow byte for the granule of p + t: p is 8-aligned and the granule's last byte p + 8(t/8) + 7 lies in
   the addressable range, where shadow_ok with offset 7 forces the shadow byte to be 0. *)
Lemma sh0 : forall m p L t, addressable m p L -> p mod 8 = 0 -> 0 <= t -> 8 * (t / 8) + 8 <= L ->
  b8 m (Z.shiftr (p + t) 3 + ASAN_K) 0.
Proof.
  intros m p L t (Hp0 & HL0 & HLe & HA) Hpm Ht HtL.
  pose proof (Z.div_pos t 8 Ht ltac:(lia)) as Ht8.
  destruct (HA (8 * (t / 8) + 7) ltac:(lia)) as (Happ & b & Hb & Hok).
  assert (Ep : p = 8 * (p / 8)) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
  assert (Hm7 : (p + (8 * (t / 8) + 7)) mod 8 = 7).
  { replace (p + (8 * (t / 8) + 7)) with (7 + (p / 8 + t / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  unfold shadow_ok in Hok. rewrite Hm7 in Hok.
  assert (Hs : bv_signed b = 0) by lia.
  assert (Eb : b = Z_to_bv 8 0) by (apply bv_eq_signed; rewrite Hs; reflexivity).
  assert (EX : Z.shiftr (p + t) 3 + ASAN_K = shadow_addr (p + (8 * (t / 8) + 7))).
  { unfold shadow_addr. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. f_equal.
    replace (p + (8 * (t / 8) + 7)) with (7 + (p / 8 + t / 8) * 8) by lia.
    replace (p + t) with (t + (p / 8) * 8) by lia.
    rewrite !Z.div_add by lia. change (7 / 8) with 0. lia. }
  unfold b8, bytes_at. cbn [length].
  assert (Hlo : 0 <= Z.shiftr (p + t) 3) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; lia).
  assert (Hhi : Z.shiftr (p + t) 3 < 2 ^ 61).
  { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [lia|]. unfold APPMEM_END in HLe. lia. }
  split; [unfold ASAN_K; lia|]. split; [unfold ASAN_K; lia|].
  intros i Hi. destruct i as [|i]; [|lia]. cbn [nth_error]. change (Z.of_nat 0) with 0.
  rewrite Z.add_0_r, EX, Hb, Eb. reflexivity.
Qed.

(* A one-byte shadow fact below HIGHMEM_BEG survives a run whose writes are all at or above HIGHMEM_BEG. *)
Lemma sh_keep : forall m m' W phi t, b8 m (Z.shiftr (phi + t) 3 + ASAN_K) 0 -> munch W m m' ->
  0 <= phi -> 0 <= t -> phi + t < APPMEM_END -> (forall x, 0 <= x < HIGHMEM_BEG -> outside W x) ->
  b8 m' (Z.shiftr (phi + t) 3 + ASAN_K) 0.
Proof.
  intros m m' W phi t H MU H0 Ht Hlt HW. unfold b8 in *. eapply fl_bytes; [exact H | exact MU |].
  cbn [length]. intros x Hx. apply HW. rewrite Z.shiftr_div_pow2 in Hx by lia. change (2 ^ 3) with 8 in Hx.
  assert ((phi + t) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia | unfold APPMEM_END in Hlt; lia]).
  pose proof (Z.div_pos (phi + t) 8 ltac:(lia) ltac:(lia)).
  unfold HIGHMEM_BEG, ASAN_K in *. lia.
Qed.

(* Read-only image addresses lie below HIGHMEM_BEG. *)
Lemma rsegs_low : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? HIGHMEM_BEG) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Ltac ush := match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3] => rewrite (unsigned_lit X) by lia
  end.
Ltac zx := match goal with
  | |- context [zxb (Z_to_bv 8 ?v)] => rewrite (zxb8 v) by lia
  end.
Ltac outW := let x := fresh "x" in let Hx := fresh "Hx" in let H1 := fresh "HW1" in let H2 := fresh "HW2" in
  intros x Hx; cbn [outside]; split; [|exact I]; intros [H1 H2].
Ltac subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HARV : reac_ctrl_headamp_record_verify_contract.

Lemma mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

Lemma sl_run_lib : forall regs pc mem md
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

Lemma sl_spill_at : forall regs m A off v, rg regs 9 A -> 0 <= A -> A + 416 <= 2 ^ 64 -> 0 <= off -> off + 8 <= 416 ->
  spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HA0 HA Ho0 Ho (A' & H9' & Hq).
  assert (E : A' = A).
  { pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1. cbn in Hq1.
    unfold rg in H9, H9'. rewrite H9 in H9'. apply (f_equal bv_unsigned) in H9'.
    rewrite (unsigned_lit A) in H9' by lia. rewrite Z_to_bv_unsigned in H9'. unfold bv_wrap, bv_modulus in H9'.
    change (2 ^ Z.of_N 64) with (2 ^ 64) in H9'.
    pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound A' (2 ^ 64) ltac:(lia)).
    lia. }
  subst A'. exact Hq.
Qed.

(* ---- The run from 0x82504 (both 0x824c4 arms join there) to 0x82554 or, through the record verifier, 0x825a0. ---- *)
Lemma f21_t2 :
  forall (ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi lo sp : Z) (b0 b1 : byte) (rest g6 : list byte),
    s7 = Z_to_bv 64 phi -> s10 = Z_to_bv 64 ASAN_K -> 0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    bytes_at rsegs m (phi + 18) (b0 :: b1 :: rest) ->
    length g6 = 6%nat -> bytes_at rsegs m (phi + 34) g6 ->
    stk rsegs m lo sp ->
    asan_cells m -> shadow_rw m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    b8 m (Z.shiftr (phi + 18) 3 + ASAN_K) 0 -> b8 m (Z.shiftr (phi + 19) 3 + ASAN_K) 0 ->
    evt rsegs
      (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte) (pcv : Z),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (-1)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 pcv) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp /\
         ((pcv = 0x82554 /\ a0' = Z_to_bv 64 (phi + 34) /\ a1' = Z_to_bv 64 0 /\
           a2' = Z_to_bv 64 (phi + 34) /\ a3' = Z_to_bv 64 6 /\
           bv_unsigned b0 = 4 /\ bv_unsigned b1 = 3)
          \/ (pcv = 0x825a0 /\ a0' = Z_to_bv 64 (if hv b0 b1 g6 then 0 else -1) /\ hv b0 b1 g6 = false)))
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 (phi + 18)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82504) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi lo sp b0 b1 rest g6 Es7 Es10 Rsp Hp0 HpE Hpsp Hlo Hlo16 Hblk Lg6 Hg6 Hstk HAC HSW Hadr2 Hadr6 Hs18 Hs19.
  subst s7 s10.
  assert (Esp : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply unsigned_lit; lia).
  pose proof (ubyte b0) as Rb0. pose proof (ubyte b1) as Rb1.
  pose proof (b8_nth m (phi + 18) (b0 :: b1 :: rest) 0 (phi + 18) Hblk ltac:(cbn; lia) ltac:(lia)) as Hy0.
  pose proof (b8_nth m (phi + 18) (b0 :: b1 :: rest) 1 (phi + 19) Hblk ltac:(cbn; lia) ltac:(cbn; lia)) as Hy1.
  cbn [nth] in Hy0, Hy1.
  apply rd1 in Hy0, Hy1, Hs18, Hs19.
  (* the record verifier call at 0x82598 / 0x8259c, used by both failure arms *)
  assert (HARVC : forall (ra1 c0 c1 c2 c3 c4 c5 : word),
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if hv b0 b1 g6 then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (-1)) s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x825a0) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp)
      (MS (mkR ra1 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 c0 c1 c2 c3 c4 c5 a6 a7
               s2 s3 (Z_to_bv 64 (-1)) s5 s6 (Z_to_bv 64 phi) s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82598) fc None m (seg_rom rsegs))).
  { intros ra1 c0 c1 c2 c3 c4 c5.
    (* 0x82598 mv a0,s7 ; 0x8259c jal reac_ctrl_headamp_record_verify *)
    step. step.
    eapply evt_cut.
    { eapply HARV with (p := phi) (lo := lo) (b0 := b0) (b1 := b1) (rec := g6);
        unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME; rewrite ?Esp.
      - reflexivity.
      - lia.
      - unfold APPMEM_END in HpE. lia.
      - exact (ba_pre2 m (phi + 18) b0 b1 rest Hblk).
      - exact Lg6.
      - exact Hg6.
      - exact Hstk.
      - lia.
      - left. lia.
      - left. lia.
      - exact HAC.
      - exact HSW.
      - exact Hadr2.
      - exact Hadr6.
      - outW. unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
        lia. }
    intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & _ & ST'). subst ms'.
    unfold REAC_CTRL_HEADAMP_RECORD_VERIFY_FRAME in MU, ST'. rewrite Esp in MU, ST'.
    match goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
    end.
    apply evt_done.
    do 7 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM | exact ST']. }
  (* 0x82504 srli ; add ; lb shadow(phi+18) ; bnez (0, not taken) *)
  step. step. ush. step. step. if_false.
  (* 0x82514 lbu a0 = b0 ; li s4,-1 ; li a1,4 ; bne a0,a1,824ec *)
  step. zx. step. step. step.
  destruct (Z.eq_dec (bv_unsigned b0) 4) as [Ey0|Ny0].
  2: { assert (C : negb (bv_eqb (Z_to_bv 64 (bv_unsigned b0)) (Z_to_bv 64 4)) = true) by (apply neqb_lit; lia).
       rewrite C; cbv iota.
       eapply evt_mono; [apply HARVC|].
       intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & ST'). subst ms'.
       do 8 eexists. exists m', 0x825a0. split; [reflexivity|].
       split; [exact MU|]. split; [exact WM|]. split; [exact ST'|].
       right. split; [reflexivity|]. split; [reflexivity | apply hv_false; left; lia]. }
  rewrite Ey0. if_false.
  (* 0x82524 addi a0,s7,19 ; srli ; add ; lb shadow(phi+19) ; bnez (0) *)
  step. step. step. ush. step. step. if_false.
  (* 0x82538 lbu a0 = b1 ; li a1,3 ; bne a0,a1,824ec *)
  step. zx. step. step.
  destruct (Z.eq_dec (bv_unsigned b1) 3) as [Ey1|Ny1].
  2: { assert (C : negb (bv_eqb (Z_to_bv 64 (bv_unsigned b1)) (Z_to_bv 64 3)) = true) by (apply neqb_lit; lia).
       rewrite C; cbv iota.
       eapply evt_mono; [apply HARVC|].
       intros ms' (ra' & a1' & a2' & a3' & a4' & a5' & a6' & m' & E & MU & WM & ST'). subst ms'.
       do 8 eexists. exists m', 0x825a0. split; [reflexivity|].
       split; [exact MU|]. split; [exact WM|]. split; [exact ST'|].
       right. split; [reflexivity|]. split; [reflexivity | apply hv_false; right; lia]. }
  rewrite Ey1. if_false.
  (* 0x82544 li a1,0 ; addi a2,s7,34 ; li a3,6 ; mv a0,a2 : the loop head 0x82554 *)
  step. step. step. step.
  apply evt_done.
  do 8 eexists. exists m, 0x82554. split; [reflexivity|].
  split; [apply munch_refl|]. split; [intros x Hx; exact Hx|]. split; [exact Hstk|].
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; first [reflexivity | assumption].
Qed.

(* ---- The run from 0x824b4 (the checksum call returned) to 0x82554 / 0x825a0. ---- *)
Lemma f21_evt :
  forall (ra0 gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi A k sv lo sp : Z) (b0 b1 : byte) (rest g6 : list byte),
    s1 = Z_to_bv 64 A -> s8 = Z_to_bv 64 k -> s10 = Z_to_bv 64 ASAN_K -> 0 <= sp < 2 ^ 64 ->
    0 < phi -> phi + 50 <= APPMEM_END -> phi + 50 <= sp - 16 ->
    sp <= A -> A + 288 <= 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
    HIGHMEM_BEG <= lo -> lo + 16 <= sp ->
    bytes_at rsegs m (phi + 18) (b0 :: b1 :: rest) ->
    length g6 = 6%nat -> bytes_at rsegs m (phi + 34) g6 ->
    q64 m (A + 280) sv ->
    stk rsegs m lo sp ->
    asan_cells m -> shadow_rw m ->
    addressable m (phi + 18) 2 -> addressable m (phi + 34) 6 ->
    b8 m (Z.shiftr (phi + 18) 3 + ASAN_K) 0 -> b8 m (Z.shiftr (phi + 19) 3 + ASAN_K) 0 ->
    (k = 6 -> bv_unsigned b0 = 4 /\ bv_unsigned b1 = 3) ->
    evt rsegs
      (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' a6' : word) (m' : word -> option byte) (pcv : Z),
         ms' = MS (mkR ra' (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7
                       s2 s3 (Z_to_bv 64 (-1)) s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 pcv) fc None m' (seg_rom rsegs) /\
         munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\
         stk rsegs m' lo sp /\
         ((pcv = 0x82554 /\ a0' = Z_to_bv 64 (phi + 34) /\ a1' = Z_to_bv 64 0 /\
           a2' = Z_to_bv 64 (phi + 34) /\ a3' = Z_to_bv 64 6 /\
           bv_unsigned b0 = 4 /\ bv_unsigned b1 = 3)
          \/ (pcv = 0x825a0 /\ a0' = Z_to_bv 64 (if hv b0 b1 g6 then 0 else -1) /\ hv b0 b1 g6 = false)))
      (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sv + -1)) a1 a2 a3 a4 a5 a6 a7
               s2 s3 (Z_to_bv 64 (phi + 18)) s5 s6 (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x824b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m
    phi A k sv lo sp b0 b1 rest g6 Es1 Es8 Es10 Rsp Hp0 HpE Hpsp HspA HA Hk Hlo Hlo16 Hblk Lg6 Hg6 Hq Hstk HAC
    HSW Hadr2 Hadr6 Hs18 Hs19 Hk6.
  subst s1 s8 s10.
  pose proof (ubyte b0) as Rb0. pose proof (ubyte b1) as Rb1.
  pose proof Hs18 as Sh18. pose proof Hs19 as Sh19.
  pose proof (b8_nth m (phi + 18) (b0 :: b1 :: rest) 0 (phi + 18) Hblk ltac:(cbn; lia) ltac:(lia)) as Hy0.
  pose proof (b8_nth m (phi + 18) (b0 :: b1 :: rest) 1 (phi + 19) Hblk ltac:(cbn; lia) ltac:(cbn; lia)) as Hy1.
  cbn [nth] in Hy0, Hy1.
  pose proof (rd8 m _ _ Hq) as RDq.
  pose proof (rd1 m _ _ Hy0) as RDy0. pose proof (rd1 m _ _ Hy1) as RDy1.
  pose proof (rd1 m _ _ Hs18) as RD18. pose proof (rd1 m _ _ Hs19) as RD19.
  (* 0x824b4 ld a1,280(s1) ; addi a1,a1,-1 ; bne a0,a1 (equal: not taken) *)
  step. step. step. if_false.
  (* 0x824c0 li a0,6 ; bne s8,a0,82458 *)
  step. step.
  destruct (Z.eq_dec k 6) as [Ek|Hk6n].
  - subst k. destruct (Hk6 eq_refl) as [Ey0 Ey1]. if_false.
    (* k = 6: srli ; add ; lb shadow(phi+18) ; bnez ; lbu a0 = 4 ; li a1,4 ; bne (not taken) *)
    step. step. ush. step. step. if_false.
    step. zx. step. step.
    assert (C0 : negb (bv_eqb (Z_to_bv 64 (bv_unsigned b0)) (Z_to_bv 64 4)) = false)
      by (rewrite Ey0, bv_eqb_refl; reflexivity).
    rewrite C0; cbv iota.
    (* addi a0,s7,19 ; srli ; add ; lb shadow(phi+19) ; bnez ; lbu a0 = 3 ; li a1,3 ; bne (not taken) *)
    step. step. step. ush. step. step. if_false.
    step. zx. step. step.
    assert (C1 : negb (bv_eqb (Z_to_bv 64 (bv_unsigned b1)) (Z_to_bv 64 3)) = false)
      by (rewrite Ey1, bv_eqb_refl; reflexivity).
    rewrite C1; cbv iota.
    eapply f21_t2 with (b0 := b0) (b1 := b1) (rest := rest) (g6 := g6) (lo := lo) (sp := sp);
      try eassumption; reflexivity.
  - assert (C : negb (bv_eqb (Z_to_bv 64 k) (Z_to_bv 64 6)) = true) by (apply neqb_lit; lia).
    rewrite C; cbv iota.
    eapply f21_t2 with (b0 := b0) (b1 := b1) (rest := rest) (g6 := g6) (lo := lo) (sp := sp);
      try eassumption; reflexivity.
Qed.


(* The segment, on the official cuts of SlotInv.v: entry Inv_A824b4_at (F20's exit), exits Inv_A82554_at (the
   head-amp sum loop head) and Inv_A825a0_at (the record verifier returned), both on the B7CUT skeleton. All
   three carry the live list hb1 phi (a_size len), which is hb1 phi len here (50 <= len). *)
Lemma seg_F21 : forall j : nat,
  Hat B APIf ra (Inv_A82554_at B APIf ra) j -> Hat B APIf ra (Inv_A825a0_at B APIf ra) j ->
  Hat B APIf ra (Inv_A824b4_at B APIf ra) j.
Proof.
  intros j Hloop Hver g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK &
    Ha0 & Hs7 & Hs4 & Hs6 & Hs8 & Hphi0 & Hphi50 & Hbig & Rtk & Hblk & Hrec & Hsp280 & Hb136 & Hb120 & Hb176 &
    H18 & H152 & Hgb & Hpb & Hpl & HLT).
  subst c.
  assert (Esz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  rewrite Esz in HFRA, HENT.
  rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5v & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill304 & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof HRT as (HAC0 & HSW0 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhi.
  assert (Hin : In (phi, flen g j) (hb1 phi (flen g j) ++ g_H g)) by (unfold hb1; cbn; left; reflexivity).
  pose proof (lw_blocks (APIf rc) _ mem md phi (flen g j) HAH Hin) as LWr1.
  pose proof (lwb_align _ _ _ _ _ _ LWr1) as Hal16.
  pose proof (lwb_end _ _ _ _ _ _ LWr1) as Hbelow.
  pose proof HHB as (Hphinz & Hadr).
  unfold AC.a_size in Hadr. rewrite Z.max_l in Hadr by lia.
  pose proof Hadr as (_ & _ & HadrE & _).
  pose proof Hwin as (HwS0 & HwS1 & _).
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
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
  pose proof (sl_spill_at regs mem A 280 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsp280) as Hq280.
  pose proof (sh0 mem phi (flen g j) 18 Hadr Hal8 ltac:(lia) ltac:(change (8 * (18 / 8) + 8) with 24; lia)) as Sh18.
  pose proof (sh0 mem phi (flen g j) 19 Hadr Hal8 ltac:(lia) ltac:(change (8 * (19 / 8) + 8) with 24; lia)) as Sh19.
  pose proof (addressable_sub mem phi (flen g j) 18 2 Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as Hadr2.
  pose proof (addressable_sub mem phi (flen g j) 34 6 Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as Hadr6.
  (* the record bytes as a cons pair *)
  assert (Hdec : exists b0 b1 rest, t_blk (g_in g) j = b0 :: b1 :: rest).
  { pose proof (t_blk_len (g_in g) j) as L.
    destruct (t_blk (g_in g) j) as [|x [|y r]]; cbn [length] in L; try lia. eauto. }
  destruct Hdec as (b0 & b1 & rest & Eblk).
  assert (Hblk2 : bytes_at rsegs mem (phi + 18) (b0 :: b1 :: rest)) by (rewrite <- Eblk; exact Hblk).
  assert (Ey0 : bv_unsigned b0 = cp_v (t_g (g_in g) j) 18).
  { pose proof (blk_cp (g_in g) j 0 ltac:(lia)) as X. rewrite Eblk in X. cbn [nth Nat.add] in X.
    unfold cp_v. rewrite <- X. reflexivity. }
  assert (Ey1 : bv_unsigned b1 = cp_v (t_g (g_in g) j) 19).
  { pose proof (blk_cp (g_in g) j 1 ltac:(lia)) as X. rewrite Eblk in X. cbn [nth Nat.add] in X.
    unfold cp_v. rewrite <- X. reflexivity. }
  assert (Ewant : t_want_v (g_in g) j = (if hv b0 b1 (bsl (t_g (g_in g) j) 34 6) then 0 else -1))
    by (rewrite want_hv, Eblk; reflexivity).
  (* a0 carries the checksum result, in the form the compare at 0x824bc needs *)
  pose proof (sumok_b2z (g_in g) j Hbig) as Esum.
  rewrite Esum in Hsp280, Hq280.
  assert (Ha0' : rg regs 10 ((if blocksum (t_blk (g_in g) j) =? 0 then 1 else 0) + -1)).
  { unfold rg in *. rewrite Ha0. apply ckv_sub. }
  set (W := [(sp - 16, sp)]).
  apply (sl_run_lib regs (Z_to_bv 64 0x824b4) mem md
    (fun R pc' mem' =>
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 26 = getr regs 26 /\
       getr R 23 = Z_to_bv 64 phi /\ getr R 24 = Z_to_bv 64 (t_k (g_in g) j) /\ getr R 18 = getr regs 18 /\
       munch W mem mem' /\ wmono rsegs mem mem' /\ stk rsegs mem' (sp - FN_STACK) sp /\
       ((pc' = Z_to_bv 64 0x82554 /\ getr R 10 = Z_to_bv 64 (phi + 34) /\ getr R 11 = Z_to_bv 64 0 /\
         getr R 12 = Z_to_bv 64 (phi + 34) /\ getr R 13 = Z_to_bv 64 6 /\
         cp_v (t_g (g_in g) j) 18 = 4 /\ cp_v (t_g (g_in g) j) 19 = 3)
        \/ (pc' = Z_to_bv 64 0x825a0 /\ getr R 10 = Z_to_bv 64 (t_want_v (g_in g) j) /\
            getr R 20 = Z_to_bv 64 (t_want_v (g_in g) j))))
    (Post B APIf ra g)).
  - exact Hhalt.
  - change (canonical_register_state (mkst regs (Z_to_bv 64 0x824b4) mem (seg_rom rsegs)))
      with (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x824b4) fp_csr None mem (seg_rom rsegs)).
    rewrite mkR_of_expand.
    rewrite Hr2.
    subst_slot Ha0'. subst_slot Hs7. subst_slot Hs4. subst_slot Hr9. subst_slot Hs8. subst_slot Hr26.
    eapply evt_mono.
    { eapply f21_evt with (phi := phi) (A := A) (k := t_k (g_in g) j) (lo := sp - FN_STACK) (sp := sp)
        (b0 := b0) (b1 := b1) (rest := rest) (g6 := bsl (t_g (g_in g) j) 34 6)
        (sv := if blocksum (t_blk (g_in g) j) =? 0 then 1 else 0).
      all: unfold AF.SLOT_STACK, FN_STACK in *.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold APPMEM_END in *. lia.
      - lia.
      - unfold APPMEM_END in *. lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact Hblk2.
      - apply t_g6_len.
      - exact Hrec.
      - exact Hq280.
      - exact Hwstk.
      - exact HAC0.
      - exact HSW0.
      - exact Hadr2.
      - exact Hadr6.
      - exact Sh18.
      - exact Sh19.
      - intros Hk. destruct (k6_rec (g_in g) j Hk) as (K1 & K2). split; [rewrite Ey0 | rewrite Ey1]; assumption. }
    intros ms' (ra' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & m' & pcv & E & MU & WM & ST' & Harm).
    subst ms'.
    eexists _, _, m'. split; [reflexivity|].
    do 12 (split; [reflexivity|]).
    split; [exact MU|]. split; [exact WM|]. split; [exact ST'|].
    destruct Harm as [(Epc & E10 & E11 & E12 & E13 & Eb0 & Eb1)|(Epc & E10 & Ehv)].
    + left. subst pcv a0' a1' a2' a3'. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite <- Ey0; exact Eb0 | rewrite <- Ey1; exact Eb1].
    + right. subst pcv a0'. split; [reflexivity|].
      split; [rewrite Ewant; reflexivity|].
      rewrite Ewant, Ehv. reflexivity.
  - (* continuation: rebuild the exit cut that the arm reached and apply it *)
    intros R pc' mem' regs'' md'
      (E2 & E3 & E4 & E8 & E9 & E19 & E21 & E22 & E26 & E23 & E24 & E18 & MU & WM & ST' & Harm) Hreg Hmat.
    assert (Fr2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (OW : forall x, x < sp - 16 \/ sp <= x -> outside W x) by (subst W; outW; lia).
    assert (HroM : ro_agree rsegs mem').
    { apply (ro_agree_same rsegs mem mem' Hro). intros a Ha. apply MU. apply OW. left.
      unfold ro_addr in Ha. destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:Ef; [|discriminate].
      destruct (kb_find_segment rsegs (bv_unsigned a) 1 s Ef) as (Hs & _ & Hs2).
      pose proof (proj1 (forallb_forall _ rsegs) rsegs_low s Hs) as Hb. cbn beta in Hb. apply Z.leb_le in Hb.
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
    pose proof (lw_store (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem mem' md HAH HstoreC HwmL) as LWr2.
    pose proof (lws_ah _ _ _ _ _ LWr2) as HAH'.
    pose proof (lws_own _ _ _ _ _ LWr2) as Hownst.
    pose proof (lws_lo _ _ _ _ _ LWr2) as HSTKeq.
    pose proof (lws_hi _ _ _ _ _ LWr2) as HSTKHeq.
    assert (HWblk : forall q n x, In (q, n) (g_H g) -> q <= x < q + n -> outside W x).
    { intros q n x Hinq Hx.
      pose proof (lw_blocks (APIf rc) (hb1 phi (flen g j) ++ g_H g) mem md q n HAH
        (in_or_app _ _ _ (or_intror Hinq))) as LWr3.
      pose proof (lwb_end _ _ _ _ _ _ LWr3) as Hqe.
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
    (* ENT: the record verifier wrote only its own 16 bytes inside the slot window, so no byte the entry
       relation speaks of changed; then the model step of sl_run_lib. *)
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md).
    { apply (Tac_slot.ent_store B APIf ra g fr (hb1 phi (flen g j)) regs mem mem' md W HENT HFRA MU).
      - intros x Hx.
        destruct (Z_lt_le_dec x (sp - 16)) as [Hd|Hd]; [left; apply OW; left; exact Hd|].
        destruct (Z_lt_le_dec x sp) as [Hd2|Hd2]; [right; left; lia | left; apply OW; right; exact Hd2].
      - exact HSTKeq.
      - exact HSTKHeq.
      - intros a Hia Ho. exact (proj2 (Hownst a) Ho). }
    assert (HENT'' : ENT APIf g (hb1 phi (flen g j)) mem' md').
    { exact (Tac_slot.ent_mat APIf g (hb1 phi (flen g j)) mem' md md' HENT' Hmat). }
    assert (OWA : forall off, 0 <= off -> forall x, A + off <= x -> outside W x)
      by (intros off Hoff x Hx; apply OW; right; lia).
    assert (Kq : forall off v, 0 <= off -> q64 mem (A + off) v -> spill regs'' mem' off v).
    { intros off v Hoff Hq. exists A. split; [unfold rg; rewrite Fr9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU | rewrite length_le8; intros x Hx; apply (OWA off); lia]. }
    assert (HFLSI' : FLSI g j fr regs'' mem').
    { apply (F20.flsi_win g j fr regs regs'' mem mem' W A HFLSI Hr9 ltac:(lia) ltac:(lia) Fr9 MU WM Hallapp).
      - intros x Hx. apply OW. right. lia.
      - intros x Hx. apply OW.
        destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia.
      - exact HWblk. }
    destruct HLK as (Hj255 & H21 & HOUR).
    assert (HB7 : B7K g j phi fr regs'' mem').
    { unfold B7K, B7SPL. split.
      { split; [exact Hj255|]. split; [unfold rg; rewrite Hreg, E21; exact H21|].
        unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
        intros x Hx. apply OW.
        destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia. }
      split; [unfold rg; rewrite Hreg; exact E23|].
      split; [unfold rg in *; rewrite Hreg, E22; exact Hs6|].
      split; [exact Hphi0|]. split; [exact Hphi50|]. split; [exact Hbig|].
      split.
      { eapply fl_bytes; [exact Hblk | exact MU |]. rewrite t_blk_len.
        intros x Hx. apply OW. left. lia. }
      split; [rewrite Esum; apply Kq; [lia | exact Hq280]|].
      split; [unfold rg; rewrite Hreg; exact E24|].
      (* push 12: the five FLS facts and LT, which the segment does not write (the verifier's 16 bytes are below
         sp, the frame and the spill area are not, and the record block ends below stklo) *)
      split; [unfold rg; rewrite Hreg, E18; exact H18|].
      split.
      { apply Kq; [lia | exact (sl_spill_at regs mem A 152 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H152)]. }
      split.
      { eapply fl_bytes; [exact Hgb | exact MU |]. rewrite t_g_len. intros x Hx. apply OW. left. lia. }
      split.
      { eapply fl_bytes; [exact Hpb | exact MU |]. intros x Hx. apply OW. left. lia. }
      split; [exact Hpl|].
      split.
      { unfold LT in HLT |- *.
        eapply F20.ifs_keep; [exact HLT | exact Hr9 | lia | lia | exact Fr9 | exact MU
                             | exact (munch_meta W mem mem' MU Hallapp) | | |].
        - intros x Hx. apply OW. destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia.
        - intros x Hx. apply OW. right. lia.
        - intros x Hx. apply OW. destruct (Hfrsep 16 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; lia. }
      split.
      { apply Kq; [lia | exact (sl_spill_at regs mem A 136 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb136)]. }
      split.
      { apply Kq; [lia | exact (sl_spill_at regs mem A 120 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb120)]. }
      { apply Kq; [lia | exact (sl_spill_at regs mem A 176 _ Hr9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hb176)]. } }
    assert (HHB' : HB mem' phi (flen g j)).
    { split; [exact Hphinz|]. unfold AC.a_size. rewrite Z.max_l by lia.
      exact (addressable_kept mem mem' phi (flen g j) Hadr (munch_meta W mem mem' MU Hallapp)). }
    rewrite <- Esz in HFRA'', HENT''.
    destruct Harm as [(Epc & E10 & E11 & E12 & E13 & Ecp0 & Ecp1)|(Epc & E10 & E20)].
    + subst pc'. rewrite <- SEGS. apply Hloop.
      exists phi, regs'', mem', md', fr.
      split; [reflexivity|].
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|].
      split; [exact HFLSI'|]. split; [exact HB7|].
      split.
      { eapply fl_bytes; [exact Hrec | exact MU |]. rewrite t_g6_len. intros x Hx. apply OW. left. lia. }
      split; [exact Ecp0|]. split; [exact Ecp1|].
      split; [unfold rg; rewrite Hreg; exact E10|].
      split; [unfold rg; rewrite Hreg; exact E12|].
      split; [unfold rg; rewrite Hreg; exact E13 | unfold rg; rewrite Hreg; exact E11].
    + subst pc'. rewrite <- SEGS. apply Hver.
      exists phi, regs'', mem', md', fr.
      split; [reflexivity|].
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|].
      split; [exact HFLSI'|]. split; [exact HB7|].
      split; [unfold rg; rewrite Hreg; exact E10 | unfold rg; rewrite Hreg; exact E20].
Qed.

End S.
