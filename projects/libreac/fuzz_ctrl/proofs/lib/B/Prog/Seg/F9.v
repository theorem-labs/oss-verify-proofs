(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F4.v, with its module paths and module names changed; 2763 of its 3239 lines of code are new or changed and 2759 lines of the source are left out. *)
(* Segment F9 of LLVMFuzzerTestOneInput, image B (the asan-ubsan build of libreac v1.9.0), range 0x82180-0x821e8
   (v1.8 0x82108-0x82170; segment table row S_F9: IDENTICAL-RENUMBER, [A+280] -> [A+288] at 0x821c0), through the
   call REPLY@0x821e8 to its return point 0x821ec (F10's entry), with the out-of-line slow paths 0x82d38-0x82d40
   (back to 0x82190) and 0x82d50-0x82d58 (back to 0x821b0). The image-B port of lib/A/Prog/Seg/F9.v; the two
   listings agree instruction for instruction, with image B's registers (phi = s2 = reg 18, len = s4 = reg 20) and
   spill offsets ([s1+288] = pa, [s1+304] = pp, [s1+296] = pn).

   0x82180-0x8218c is an instrumented 1-byte check of the name byte at a0 = kind_name_addr (t_k ...) (the result of
   the reac_ctrl_kind_name call at 0x8217c): it loads the shadow byte at (a0 >> 3) + s10 (s10 = ASAN_K) and compares
   it with 0; when that byte is not 0 the slow path 0x82d38 compares (a0 land 7) with it and returns to 0x82190.
   Both arms are proved and the error path 0x83078 is NOT reached, because the name bytes are addressable: the name
   address is one of the registered globals (AF.frame_AG), whose bytes the cut carries as addressable.
   0x82190 lbu a1,0(a0) reads the first name byte; it is not 63 ('?') because the kind is t_k (g_in g) j <= 13
   (RcParse.ctrlparse_kind_range) and no kind_names entry starts with '?', so `bne a1,63` at 0x82198 goes to
   0x821b8 and neither the second checked byte (0x8219c-0x821ac, slow path 0x82d50) nor the `beqz a0,0x82fa4` at
   0x821b4 is reached.
   0x821b8-0x821dc writes the three frame shadow bytes S(fr)+32, +34, +38 (byte 2, then 0, 0) and the three frame
   cells [s1+288] = fr+256 (2 bytes), [s1+304] = fr+272 (8), [s1+296] = fr+304 (8), all zero; then 0x821e0-0x821e4
   put a0 = s2 = phi and a1 = s4 = len and 0x821e8 calls reac_ctrl_identity_reply, composed on its lib/B contract
   (reac_ctrl_identity_reply_c.v, a Section Hypothesis), landing at the F10 entry 0x821ec.

   Cuts: the official Inv_B82180_at (entry) and Inv_B821ec_at (exit, F10's entry) of lib/B/Prog/SlotInv.v (S_F9),
   used as they stand. The entry's body is f9_E plus the six conjuncts f9_X ([A+248] = 1 - sum_ok, the 50 record
   bytes at Phi, FTURN, REC0, FPS, F272), all carried to the exit. FRA gives the rest of what the run needs: the
   frame's place in the class-6 area of the side stack (f9_fra_fs6), the thread's DTLS word (f9_fra_dtls) and, for
   an empty record, Phi outside the side stack (f9_fra_phi_nfs). LK crosses by Tac_ro.lk_keep and FSj (the local
   `first` at fr + 2880) by Tac_ro.fsj_keep. No cut carries mem_inv (push 5c): the stores
   need none, and the callee's mem_inv premise comes from FRA's ro_agree through MemNorm.evt_normalize (f9_evtB runs
   f9_evtB_n on the normalized memory). The exit's RCA (the three reply cells addressable) comes from this segment's
   shadow stores 0x821bc / 0x821c8 / 0x821d4 (f9_addr_out). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcReply RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib RcAsanFP
  asan_stack_malloc_c reac_ctrl_kind_name_c reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_f9.
(* Tac_ro: the record lengths tr_ID_length / tr_FG_length (Required, used qualified). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Import ListNotations.
(* Requiring Tac_ro loads lib/Reusable/YK11.v as well, so the short name YK11 is ambiguous: import this unit's
   copy by its path, and name FPState unqualified. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.
(* The v1.9 frame size and its shadow length are the named constants FRAME_BYTES = 3136 and FRAME_SHADOW = 392 of
   SlotInv.v; every lia of this file gets their values. *)
Local Ltac lia := pose proof FRAME_BYTES_val; pose proof FRAME_SHADOW_val; Lia.lia.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* `Frame` and `MState` alone can resolve to the UL copies that Seg/F10 loads; pin them to lib/Lib. *)
Module Frame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
(* The stack-allocation contract's FakeStack layout, which FRA's FSREC record reads (as SlotInv's SMC). *)
Module ASMf := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.

Ltac f9_bjoin G r := lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => exact (G (Sem.reg_get R r)) end.

Ltac f9_until_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; f9_until_if
  | _ => idtac
  end.

(* One instrumented 1-byte check of the byte X (srli; add s10; lb; bnez; slow path andi/bge/j), the error call not
   reached: the register r is generalized at the join. *)

Ltac f9_chk X r k RK OK :=
  step; rewrite ?(unsigned_lit X) by lia; rewrite rc_shr3;
  step; step; clear RK; f9_until_if;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (pose proof (rc_byte_signed k); lia);
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else ?Bb) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evt segs Q (MS (bvmap_set r rr R) F Bb fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ f9_bjoin G r
        | step; rewrite ?(unsigned_lit X) by lia; rewrite rc_land7;
          step;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k))
            by (pose proof (Z.mod_pos_bound X 8 ltac:(lia)); pose proof (rc_byte_signed k); lia);
          replace (X mod 8 <? bv_signed k) with true by (symmetry; apply Z.ltb_lt; destruct OK; lia);
          cbn [negb]; cbv iota; step;
          f9_bjoin G r ]
      | intros ?; simp_regs; clear OK ]
  end.

(* One instrumented 1-byte shadow read of an addressable byte X: the shadow byte b is readable at
   (X >> 3) + ASAN_K and passes the check (b = 0, or X mod 8 < b). The body of lib/A/Prog/Seg/Tac_b5.v's
   sl_shadow1, which lib/B/Prog/Seg/Tac_slot.v does not carry. *)
Lemma sl_shadow1 : forall m X, addressable m X 1 ->
  exists b : byte, ov_read_bytes rsegs m (wa (Z.shiftr X 3 + ASAN_K)) 1 = Some [b]
    /\ (bv_signed b = 0 \/ X mod 8 < bv_signed b) /\ -128 <= bv_signed b < 128.
Proof.
  intros m X HA. destruct (meta_byte m X 1 HA ltac:(lia)) as (b & RO & OK & IS).
  exists b. split; [| split].
  - pose proof (cells_at_read rsegs m (Z.shiftr X 3 + ASAN_K) [C1 b] 0%nat (C1 b) RO eq_refl) as H.
    cbn [csize cbytes] in H. rewrite Z.add_0_r in H. exact H.
  - destruct OK as [H|H]; [left; exact H | right; lia].
  - pose proof (sbyte_range b); lia.
Qed.

(* The six byte ranges F9 writes before the call (0x821bc-0x821dc). *)

Definition f9_WA (S3 fr : Z) : list ivl :=
  [(S3 + 32, S3 + 33); (fr + 256, fr + 258); (S3 + 34, S3 + 35); (fr + 272, fr + 280);
   (S3 + 38, S3 + 39); (fr + 304, fr + 312)].

Lemma f9_neq63 : forall c : byte, bv_unsigned c <> 63 -> bv_eqb (zxb c) (Z_to_bv 64 63) = false.
Proof.
  intros c H. apply Bool.not_true_iff_false. intro HC. apply bv_eqb_eq in HC.
  apply (f_equal (bv_unsigned (n:=64))) in HC. unfold zxb in HC.
  pose proof (bv_unsigned_in_range 8 c) as Hr. unfold bv_modulus in Hr.
  change (2 ^ Z.of_N 8) with 256 in Hr.
  rewrite !MState.unsigned_lit in HC by lia. lia.
Qed.

(* A spill base A' read through s1 with a cell q64 at A' + off (off < 448) is the spill base A of FRA, when
   0 <= A and A + 448 <= 2^64 (FRA: sp <= A, and A + 448 <= S with the saved registers below S). The cut fixes
   the base only modulo 2^64; this pins it (the body of lib/B/Prog/Seg/F8.v's f8_base_eq). *)
Lemma f9_base_eq : forall (A A' off v : Z) (m : word -> option byte),
  Z_to_bv 64 A' = Z_to_bv 64 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off < 448 ->
  q64 m (A' + off) v -> A' = A.
Proof.
  intros A A' off v m E HA0 HA1 Hoff Hq.
  unfold q64, bytes_at in Hq. destruct Hq as (Hq0 & Hq1 & _).
  rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit_wrap in E.
  rewrite (Z.mod_small A) in E by lia.
  Z.div_mod_to_equations. lia.
Qed.

(* A spill of SlotInv (exists A', s1 = A' and a cell at A' + off) read over the named base A: the two bases agree
   by f9_base_eq. *)
Lemma f9_sp : forall (regs : bvmap 5 word) (m : word -> option byte) (A off v : Z),
  rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off < 448 ->
  spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HA0 HA1 Hoff (A' & H9' & Hq).
  assert (E : A' = A).
  { apply (f9_base_eq A A' off v m); [| exact HA0 | exact HA1 | exact Hoff | exact Hq].
    unfold rg in H9, H9'. rewrite <- H9', <- H9. reflexivity. }
  rewrite <- E. exact Hq.
Qed.

(* No image segment lies at or above GT (Tac_slot.img_below_GT), so a byte there reads from memory alone: a
   readable byte (mrd) of such an address is a defined memory byte. *)
Lemma f9_noseg : forall x, AC.GT <= x -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|reflexivity]. exfalso.
  destruct (kb_find_segment _ _ _ _ E) as (Hin & H1 & H2).
  assert (Himg : AC.a_in_img x) by (exists s; split; [exact Hin | lia]).
  pose proof (img_below_GT x Himg). lia.
Qed.

Lemma f9_raw : forall m x, AC.GT <= x < 2 ^ 64 -> (exists b, mrd rsegs m (wa x) = Some b) ->
  exists b, m (wa x) = Some b.
Proof.
  intros m x Hx (b & Hb). unfold mrd in Hb. destruct (m (wa x)) as [c|] eqn:E; [exists c; reflexivity|].
  exfalso. rewrite (seg_rom_unmapped rsegs) in Hb; [discriminate Hb|].
  rewrite wa_unsigned by (unfold AC.GT in Hx; lia). apply f9_noseg. lia.
Qed.

Lemma f9_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by lia. exact HH.
Qed.

Lemma f9_pres_one : forall bs m (a x : word) v, m x = Some v ->
  exists w, write_to_mem m a bs x = Some w.
Proof.
  induction bs as [|b bs IH]; intros m a x v H; cbn; [exists v; exact H|].
  destruct (bv_eqb x a) eqn:E.
  - apply (IH _ _ _ b). rewrite E. reflexivity.
  - apply (IH _ _ _ v). rewrite E. exact H.
Qed.

Lemma f9_pres : forall m (a : word) bs q,
  (exists b, mbyte rsegs m q = Some b) -> exists b, mbyte rsegs (write_to_mem m a bs) q = Some b.
Proof.
  intros m a bs q H. unfold mbyte in *.
  destruct (m (Z_to_bv 64 q)) as [v|] eqn:E.
  - destruct (f9_pres_one bs m a (Z_to_bv 64 q) v E) as (w & Hw). rewrite Hw. exists w. reflexivity.
  - destruct (write_to_mem m a bs (Z_to_bv 64 q)) as [w|] eqn:E2; [exists w; reflexivity | exact H].
Qed.

(* Three names of lib/A/Prog/RcAsanFPLib.v that image B's copy does not carry (fl_col, fl_stk, fl_tls_same);
   the bodies are image A's, over image B's rsegs. *)

Ltac f9_col :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; rewrite ?length_app, ?length_le8, ?length_le4 in Hx; cbn [length] in Hx;
  match goal with O : forall y, _ <= y < _ -> outside _ y |- _ => apply O; lia end.

Lemma fl_stk : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) Hm Hw HX. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  destruct (HX a Ha) as [Ho | Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma fl_tls_same : forall m m' W' TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k,
  asan_tls_cells m TP DT0 TS0 C0 T0 DB0 k0 -> asan_tls_cells m' TP DT TS C T DB k -> munch W' m m' ->
  Forall (fun d => forall x, fst d <= x < snd d -> outside W' x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0) ->
  DT0 = DT /\ TS0 = TS /\ C0 = C /\ T0 = T /\ DB0 = DB /\ k0 = k.
Proof.
  intros m m' W' TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc.
  cbn [fp_tls] in Hc.
  repeat (let O := fresh "O" in apply Forall_cons_iff in Hc; destruct Hc as [O Hc]; cbn [fst snd] in O).
  destruct HT0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17
    & A18 & A19).
  destruct HT as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17
    & B18 & B19).
  assert (EDT : DT0 = DT) by (apply (fl_le8_eq W' m m' (TP - 8) DT0 DT A3 B3 Hm); f9_col).
  assert (Ek : k0 = k) by (apply (fl_le4_eq W' m m' TSD_KEY k0 k A6 B6 A7 B7 Hm); f9_col).
  assert (ETS : TS0 = TS) by (apply (fl_le8_eq W' m m' (TP - 88) TS0 TS A8 B8 Hm); f9_col).
  subst DT0 k0 TS0.
  assert (EC : C0 = C) by (apply (fl_le8_eq W' m m' (bv_unsigned TS + 8 * k) C0 C A9 B9 Hm); f9_col).
  subst C0.
  assert (ET : T0 = T) by (apply (fl_le8_eq W' m m' (bv_unsigned C + 152) T0 T A10 B10 Hm); f9_col).
  assert (EDB : DB0 = DB) by (apply (fl_le8_eq W' m m' (TP + 8) DB0 DB A17 B17 Hm); f9_col).
  subst T0 DB0. repeat split.
Qed.

(* store_ok for the current memory, from a wr_at of the original memory. *)

Ltac f9_sok W a k n :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa (a + k)) n = true)
        by (eapply (wr_at_store_ok rsegs mm a _ k n); [repeat apply wr_at_write; exact W | lia | lia]);
      rewrite ?Z.add_0_r in H
  end.

(* Drop the store_ok hypothesis of the store just done (the stores need no mem_inv). *)

Ltac f9_cl :=
  match goal with
  | HS : store_ok rsegs ?m0 _ _ = true
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 _ _) _) => clear HS
  end.

(* Every byte of [a, a + n) readable gives a byte list there. *)

Lemma f9_bytes_ex : forall m (n : nat) a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat i)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b & Hb). change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hl).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as (b' & Hb'). exists b'.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact Hb'. }
    exists (b :: bs). split; [|cbn; lia].
    destruct Hbs as (H0 & H1 & H2). split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact Hb.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply H2. cbn in Hi. lia.
Qed.

(* A spill read in the current memory, from a bytes_at of the original memory. *)

Ltac f9_rdcur a v H :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let R := fresh "RL" in
      assert (R : ov_read_bytes rsegs mm (wa a) 8 = Some (le8 (Z_to_bv 64 v)))
        by (apply f9_rd8;
            [ repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]); exact H
            | apply length_le8 ])
  end.

Ltac f9_bw :=
  repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]).

(* 0x82180 - 0x821dc: the checked read of the name byte at a0 = X (not '?'), then the three frame shadow bytes and
   the three frame cells. *)

Lemma f9_evtA :
  forall (ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Q : machine_state -> Prop)
         (X A S3 fr phi len : Z) (b c0 : byte),
    0 <= X < 2 ^ 47 -> 0 <= S3 -> 0 <= fr -> 0 <= A ->
    fr + FRAME_BYTES <= A -> A + 448 <= 2 ^ 64 -> S3 + FRAME_SHADOW <= A ->
    (S3 + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= S3) ->
    ov_read_bytes rsegs m (wa (X / 8 + ASAN_K)) 1 = Some [b] ->
    (bv_signed b = 0 \/ X mod 8 < bv_signed b) ->
    ov_read_bytes rsegs m (wa X) 1 = Some [c0] -> bv_unsigned c0 <> 63 ->
    wr_at rsegs m S3 FRAME_SHADOW ->
    wr_at rsegs m (fr + 256) 2 -> wr_at rsegs m (fr + 272) 8 -> wr_at rsegs m (fr + 304) 8 ->
    bytes_at rsegs m (A + 288) (le8 (Z_to_bv 64 (fr + 256))) ->
    bytes_at rsegs m (A + 304) (le8 (Z_to_bv 64 (fr + 272))) ->
    bytes_at rsegs m (A + 296) (le8 (Z_to_bv 64 (fr + 304))) ->
    (forall (m1 : word -> option byte),
       munch (f9_WA S3 fr) m m1 -> wmono rsegs m m1 ->
       (forall q, (exists bq, mbyte rsegs m q = Some bq) -> exists bq, mbyte rsegs m1 q = Some bq) ->
       bytes_at rsegs m1 (S3 + 32) (le1 (Z_to_bv 64 2)) ->
       bytes_at rsegs m1 (S3 + 34) (le1 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (S3 + 38) (le1 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 256) (le2 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 272) (le8 (Z_to_bv 64 0)) ->
       bytes_at rsegs m1 (fr + 304) (le8 (Z_to_bv 64 0)) ->
       wr_at rsegs m1 (fr + 256) 2 -> wr_at rsegs m1 (fr + 272) 8 -> wr_at rsegs m1 (fr + 304) 8 ->
       Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 2) (zxb c0) (Z_to_bv 64 (fr + 256))
                  (Z_to_bv 64 (fr + 272)) (Z_to_bv 64 (fr + 304)) a5 a6 a7
                  (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11
                  t3 t4 t5 t6)
             Fr (Z_to_bv 64 0x821e0) fc None m1 (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 X) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11
               t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82180) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
    Fr fc m Q X A S3 fr phi len b c0 HX HS30 Hfr0 HA0 HfrA HA64 HS3A HS3fr
    RK OK RC0 HC0 Wsh Wa Wp Wn Q256 Q272 Q264 HQ.
  (* 0x82180-0x8218c the instrumented check of the byte X *)
  f9_chk X (Z_to_bv 5 12) b RK OK.
  (* 0x82190 lbu a1,0(a0) ; 0x82194 li a2,63 ; 0x82198 bne a1,a2 taken to 0x821b8 *)
  step. step. step. rewrite (f9_neq63 c0 HC0). cbn [negb]. cbv iota.
  (* 0x821b8 li a0,2 ; 0x821bc sb a0,32(s3) *)
  step.
  f9_sok Wsh S3 32 1%nat. step. f9_cl.
  (* 0x821c0 ld a2,288(s1) ; 0x821c4 sh zero,0(a2) *)
  f9_rdcur (A + 288) (fr + 256) Q256. step.
  f9_sok Wa (fr + 256) 0 2%nat. step. f9_cl.
  (* 0x821c8 sb zero,34(s3) *)
  f9_sok Wsh S3 34 1%nat. step. f9_cl.
  (* 0x821cc ld a3,272(s1) ; 0x821d0 sd zero,0(a3) *)
  f9_rdcur (A + 304) (fr + 272) Q272. step.
  f9_sok Wp (fr + 272) 0 8%nat. step. f9_cl.
  (* 0x821d4 sb zero,38(s3) *)
  f9_sok Wsh S3 38 1%nat. step. f9_cl.
  (* 0x821d8 ld a4,264(s1) ; 0x821dc sd zero,0(a4) *)
  f9_rdcur (A + 296) (fr + 304) Q264. step.
  f9_sok Wn (fr + 304) 0 8%nat. step. f9_cl.
  apply evt_done. apply HQ.
  - cbv [f9_WA].
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl.
  - repeat apply wmono_write. apply wmono_refl.
  - intros q Hq. repeat apply f9_pres. exact Hq.
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - f9_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
  - repeat apply wr_at_write. exact Wa.
  - repeat apply wr_at_write. exact Wp.
  - repeat apply wr_at_write. exact Wn.
Qed.

Lemma l5_addr_keep : forall m m' W p n,
  addressable m p n -> Frame.munch W m m' ->
  (forall i, 0 <= i < n -> Frame.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros m m' W p n (H1 & H2 & H3 & H) MU HW.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|].
  exists b. split; [|exact Hk].
  assert (Hr : 0 <= shadow_addr (p + i) < 2 ^ 64).
  { unfold shadow_addr, ASAN_K. unfold APPMEM_END in H3. Z.div_mod_to_equations. lia. }
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by exact Hr. exact (HW i Hi).
Qed.

(* The shadow map is monotone, and strictly so across a whole granule. *)

Lemma l5_sh_mono : forall x y, 0 <= x <= y -> shadow_addr x <= shadow_addr y.
Proof.
  intros x y H. unfold shadow_addr. pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma l5_sh_lt : forall x y, 0 <= x -> x + 8 <= y -> shadow_addr x < shadow_addr y.
Proof.
  intros x y H0 H. unfold shadow_addr.
  pose proof (Z.div_le_mono (x + 1 * 8) y 8 ltac:(lia) ltac:(lia)) as Hm.
  rewrite Z.div_add in Hm by lia. lia.
Qed.

(* word_mem only sees its value mod 2^64. *)

Lemma l5_wm_mod : forall mem a b, word_mem rsegs mem a b -> word_mem rsegs mem a (b mod 2 ^ 64).
Proof.
  intros mem a b H k Hk. rewrite (H k Hk). unfold le_byte. change (8 * Z.of_nat 8) with 64.
  rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Section S_l5.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Definition f9_PL (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\ AC.GT <= fr /\
  (fr + FRAME_BYTES <= AC.aspZ regs - FN_STACK \/ AC.aspZ regs <= fr) /\
  (forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 -> fr + FRAME_BYTES <= A) /\
  (forall FS, word_mem rsegs m (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS <= fr < FS + AC.FS_SIZE ->
     FS + 36864 + 6 * 2 ^ 20 <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE).

(* The heap block (phi, len) lies below stklo <= sp - SLOT_STACK, so it is apart from the callee's stack window and
   below 2^64; 4096 <= phi. Holds for any 0 <= len. *)

Lemma l5_dj0 : forall g fr phi len hb regs mem md,
  FRA B APIf ra g fr ((phi, AC.a_size len) :: hb) regs mem md -> 0 <= len ->
  (phi + 50 <= AC.aspZ regs - 9072 \/ AC.aspZ regs <= phi) /\
  phi + 50 <= 2 ^ 64 /\ 0 < phi.
Proof.
  intros g fr phi len hb regs mem md HFRA Hlen.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & Hsp4096 & HSapp & Hspill & Hsel & Hq56 & Hloc &
    Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWINa & Hhi1 & Hhi2 & Hhi3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (lw_blocks (APIf rc) _ _ _ phi (AC.a_size len) HAH ltac:(cbn; left; reflexivity))
    as [_ Hp4096 Hpst _ _].
  rewrite Haspz. unfold AC.a_size in *. pose proof (Z.le_max_r len 1).
  unfold AF.SLOT_STACK, APPMEM_END in *.
  split; [left; lia|]. split; lia.
Qed.

(* A nonempty heap block's first byte is not in the side stack (a_laws_blocks: no block byte is a_in_fs). *)

Lemma l5_notfs : forall g fr phi len hb regs mem md,
  FRA B APIf ra g fr ((phi, AC.a_size len) :: hb) regs mem md -> 0 < len -> ~ AC.a_in_fs AC.ASYMS mem phi.
Proof.
  intros g fr phi len hb regs mem md HFRA Hlen.
  destruct HFRA as (A & sp & s5 & HRT & HAH & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (lw_blocks (APIf rc) _ _ _ phi (AC.a_size len) HAH ltac:(cbn; left; reflexivity))
    as [_ _ _ _ Hbyte].
  destruct (Hbyte phi ltac:(unfold AC.a_size; pose proof (Z.le_max_r len 1); lia)) as (_ & _ & _ & _ & Hn).
  exact Hn.
Qed.

(* The full disjointness: the block is also apart from the frame cells [fr + 256, fr + 312). Real arm: phi + len <=
   stklo <= fr. Side arm (frame in the side stack FS): phi is not a_in_fs, so phi is below FS (hence below the frame)
   or at or above FS + FS_SIZE (hence above the frame). *)

Lemma l5_dj1 : forall g fr phi len hb regs mem md,
  FRA B APIf ra g fr ((phi, AC.a_size len) :: hb) regs mem md -> f9_PL fr regs mem -> 0 <= len ->
  ~ AC.a_in_fs AC.ASYMS mem phi ->
  (phi + 50 <= fr + 256 \/ fr + 312 <= phi) /\
  (phi + 50 <= AC.aspZ regs - 9072 \/ AC.aspZ regs <= phi) /\
  phi + 50 <= 2 ^ 64 /\ 0 < phi.
Proof.
  intros g fr phi len hb regs mem md HFRA HPL Hlen Hnfs.
  split; [|exact (l5_dj0 g fr phi len hb regs mem md HFRA Hlen)].
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & Hsp4096 & HSapp & Hspill & Hsel & Hq56 & Hloc &
    Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWINa & Hhi1 & Hhi2 & Hhi3 & Hhb & Hlive).
  destruct HPL as (Happ & Hgt & _ & _ & HFSb).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (lw_blocks (APIf rc) _ _ _ phi (AC.a_size len) HAH ltac:(cbn; left; reflexivity))
    as [_ Hp4096 Hpst _ _].
  assert (Hspb : sp <= 2 ^ 64) by (unfold APPMEM_END in HSapp; lia).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  pose proof (Z.le_max_r len 1) as Hsz. unfold AC.a_size in Hpst.
  destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
  - (* real arm: phi + a_size len <= stklo <= fr *)
    left. destruct (Hreal fr ltac:(lia)) as (Hr & _). lia.
  - (* side arm: the FS base b at tp, with the frame in [b + 36864 + 6 * 2^20, b + FS_SIZE) *)
    destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hwb & Hblo & Hbhi).
    destruct (HFSb b Hwb Hbr ltac:(lia)) as (Hlo36 & Hhi36).
    destruct (Z_lt_le_dec phi b) as [Hl|Hg].
    + left. lia.
    + destruct (Z_lt_le_dec phi (b + AC.FS_SIZE)) as [Hl2|Hg2].
      * exfalso. apply Hnfs. exists b. split; [exact Hbr|]. split; [exact Hwb | lia].
      * right. lia.
Qed.

(* The nonempty-block case: l5_dj1 with l5_notfs. *)

Lemma l5_dj : forall g fr phi len hb regs mem md,
  FRA B APIf ra g fr ((phi, AC.a_size len) :: hb) regs mem md -> f9_PL fr regs mem -> 0 < len ->
  (phi + 50 <= fr + 256 \/ fr + 312 <= phi) /\
  (phi + 50 <= AC.aspZ regs - 9072 \/ AC.aspZ regs <= phi) /\
  phi + 50 <= 2 ^ 64 /\ 0 < phi.
Proof.
  intros g fr phi len hb regs mem md HFRA HPL Hlen.
  exact (l5_dj1 g fr phi len hb regs mem md HFRA HPL ltac:(lia) (l5_notfs g fr phi len hb regs mem md HFRA Hlen)).
Qed.

End S_l5.

(* The callee contract's premises at the call 0x821e8. MI is the memory fact: the contract asks for mem_inv (f9_pre_n,
   the form f9_evtB_n runs on); the cut's memory has ro_agree (f9_pre, the form f9_evtB takes and runs on the
   normalized memory). *)
Definition f9_pre_g (MI : Prop) (phi len pa pp pn S FS TP : Z) (m : word -> option byte) (G ja jp jn : list byte)
    : Prop :=
  0 <= phi < 2^64 /\ 0 <= len < 2^64 /\ 0 <= pa < 2^64 /\ 0 <= pp < 2^64 /\ 0 <= pn < 2^64 /\
  S < 2^64 /\ S mod 16 = 0 /\
  REAC_CTRL_IDENTITY_REPLY_K <= S /\ stk rsegs m (S - REAC_CTRL_IDENTITY_REPLY_K) S /\
  MI /\ length G = 50%nat /\
  (reply_args phi pa pp pn = true -> 50 <= len ->
     phi + 50 <= 2^64 /\ bytes_at rsegs m phi G /\
     (phi + 50 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= phi)) /\
  (reply_args phi pa pp pn = true ->
     pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
     rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
     (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
     (pa + 2 <= phi \/ phi + 50 <= pa) /\ (pp + 8 <= phi \/ phi + 50 <= pp) /\ (pn + 8 <= phi \/ phi + 50 <= pn) /\
     (pa + 2 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pa) /\
     (pp + 8 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pp) /\
     (pn + 8 <= S - REAC_CTRL_IDENTITY_REPLY_K \/ S <= pn)) /\
  asan_cells m /\ shadow_rw m /\
  HIGHMEM_BEG <= S - REAC_CTRL_IDENTITY_REPLY_K /\ S <= APPMEM_END /\
  addressable m (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
  (reply_args phi pa pp pn = true -> 50 <= len -> addressable m phi 50) /\
  (reply_args phi pa pp pn = true ->
     addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
     (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) /\
  addressable m REAC_CTRL_PARSE_BC 6 /\
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] /\
  fp [1%nat] m TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
    (reac_ctrl_identity_reply_W phi pa pp pn S) (reac_ctrl_identity_reply_D phi len pa pp pn) /\
  reac_ctrl_identity_reply_tls m TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S.

Definition f9_pre_n (phi len pa pp pn S FS TP : Z) (m : word -> option byte) (G ja jp jn : list byte) : Prop :=
  f9_pre_g (mem_inv rsegs m) phi len pa pp pn S FS TP m G ja jp jn.

Definition f9_pre (phi len pa pp pn S FS TP : Z) (m : word -> option byte) (G ja jp jn : list byte) : Prop :=
  f9_pre_g (ro_agree rsegs m) phi len pa pp pn S FS TP m G ja jp jn.

(* The call on its contract, over a memory with mem_inv (the contract's form). *)
Lemma f9_evtB_n :
  forall (ra0 sp gp tp t0 t1 t2 s0 a0 a1 s5 s6 s7 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
         (A S3 fr phi len S FS TP : Z) (G ja jp jn : list byte),
    reac_ctrl_identity_reply_contract ->
    sp = Z_to_bv 64 S -> tp = Z_to_bv 64 TP -> 0 <= TP < 2 ^ 64 ->
    f9_pre_n phi len (fr + 256) (fr + 272) (fr + 304) S FS TP m G ja jp jn ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       munch (reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) S G ++
              fp_w [1%nat] FS ++
              [(shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S)]) m m' ->
       wmono rsegs m m' -> mem_inv rsegs m' ->
       stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
       (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G = true ->
          rw_cells rsegs m' (fr + 256) [CB 2 (reply_addr G)] /\
          rw_cells rsegs m' (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
          rw_cells rsegs m' (fr + 304) [CB 8 (le8 (Z_to_bv 64 (ir_s G - 13)))]) ->
       asan_cells m' -> shadow_rw m' ->
       addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
       fp [1%nat] m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
         (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) S)
         (reac_ctrl_identity_reply_D phi len (fr + 256) (fr + 272) (fr + 304)) ->
       reac_ctrl_identity_reply_tls m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
       Q (MS (mkR (Z_to_bv 64 0x821ec) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                  (Z_to_bv 64 (reply_ret phi len (fr + 256) (fr + 272) (fr + 304) G))
                  a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7
                  s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
             Fr (Z_to_bv 64 0x821ec) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 (Z_to_bv 64 (fr + 256)) (Z_to_bv 64 (fr + 272))
               (Z_to_bv 64 (fr + 304)) a5 a6 a7 (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7
               s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x821e0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a0 a1 s5 s6 s7 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 Fr fc m Q A S3 fr phi len S0 FS TP
    G ja jp jn HIR Hsp Htp HTP Hpre HK.
  destruct Hpre as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 &
    P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28).
  assert (Etp : bv_unsigned tp = TP) by (rewrite Htp; apply MState.unsigned_lit; exact HTP).
  pose proof HIR as HC. unfold reac_ctrl_identity_reply_contract, REAC_CTRL_IDENTITY_REPLY in HC.
  (* 0x821e0 mv a0,s2 ; 0x821e4 mv a1,s4 ; 0x821e8 jal reac_ctrl_identity_reply *)
  step. step. step.
  eapply evt_cut.
  { eapply HC with (fr := phi) (len := len) (pa := fr + 256) (pp := fr + 272) (pn := fr + 304) (S := S0)
      (FS := FS) (g := G) (ja := ja) (jp := jp) (jn := jn);
      first [ reflexivity | exact Hsp | (rewrite Etp; assumption) | assumption ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM &
    MI & ST & HR & HAC' & HSW' & HAD' & HFP' & HTLS').
  subst ms'. rewrite Etp in HFP', HTLS'.
  replace (ret_pc (Z_to_bv 64 0x821ec)) with (Z_to_bv 64 0x821ec)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done.
  exact (HK t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM MI ST HR HAC' HSW' HAD' HFP' HTLS').
Qed.

(* ---- Push 5c: no cut carries mem_inv (FRA has ro_agree only), but the reply contract asks for it. f9_evtB runs
   f9_evtB_n on MemNorm.normalize m (mem_inv_normalize) and carries the run back to m by MemNorm.evt_normalize.
   These lemmas move f9_pre to the normalized memory and the contract's post back. Every address they speak of
   either is read through mrd (bytes_at, addressable: the same on both memories, mrd_rel) or is a writable byte at
   or above GT, where no segment lies (stk, wr_at: f9n_ro), so normalizing changes nothing there (as F12's
   f12_*_norm / f12_*_back). ---- *)
Lemma f9n_ro : forall x, AC.GT <= x < 2 ^ 64 -> ro_addr rsegs (wa x) = false.
Proof.
  intros x Hx. unfold ro_addr. assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  assert (Ex : bv_unsigned (wa x) = x) by (rewrite wa_unsigned by lia; reflexivity).
  rewrite Ex, (f9_noseg x ltac:(lia)). reflexivity.
Qed.

Lemma f9n_addr : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n REL. split; intros (H0 & H1 & H2 & H); (split; [exact H0|]); (split; [exact H1|]);
    (split; [exact H2|]); intros i Hi; destruct (H i Hi) as (Ha & b & Hb & Hok); (split; [exact Ha|]);
    exists b; (split; [|exact Hok]).
  - rewrite <- (mrd_rel rsegs m m0 _ REL). exact Hb.
  - rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma f9n_stk_norm : forall m lo hi, ro_agree rsegs m -> AC.GT <= lo -> stk rsegs m lo hi ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi HRO Hlo (H1 & H2 & H). pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as [Hv [b Hb]].
  assert (RO : ro_addr rsegs (wa a) = false) by (apply f9n_ro; lia).
  split.
  - rewrite (wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma f9n_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi REL (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as [Hv [b Hb]]. pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma f9n_shrw_norm : forall m, ro_agree rsegs m -> shadow_rw m -> shadow_rw (normalize rsegs m).
Proof.
  intros m HRO H a Ha. pose proof (mem_rel_normalize rsegs m HRO) as REL.
  destruct (H a Ha) as [Hv [b Hb]].
  assert (RO : ro_addr rsegs (wa a) = false).
  { apply f9n_ro. assert (HGT : AC.GT = 0x5fe000) by reflexivity.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia. }
  split.
  - rewrite (wview_rel_rw rsegs m _ _ REL RO). exact Hv.
  - exists b. rewrite <- (mrd_rel rsegs m _ _ REL). exact Hb.
Qed.

Lemma f9n_shrw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 REL H a Ha. destruct (H a Ha) as [Hv [b Hb]].
  pose proof (ro_false_of_wview rsegs m m0 _ REL Hv) as RO. split.
  - rewrite <- (wview_rel_rw rsegs m m0 _ REL RO). exact Hv.
  - exists b. rewrite (mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma f9n_cells : forall m m0, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  asan_cells m -> asan_cells m0.
Proof.
  intros m m0 BA H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end; apply BA; assumption.
Qed.

Lemma f9n_rw_norm : forall m a cs, ro_agree rsegs m -> AC.GT <= a -> rw_cells rsegs m a cs ->
  rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs HRO Ha ((Hw & Hb) & Hwr). pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [split; [exact Hw | exact (bytes_at_normalize rsegs m a _ HRO Hb)]|].
  apply (wr_at_norm rsegs m (normalize rsegs m) a _ REL Hwr).
  intros i Hi. apply f9n_ro. destruct Hwr as (H0 & H1 & _). lia.
Qed.

Lemma f9n_rw_back : forall m m0 a cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 a cs -> rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR ((Hwf & Hb) & Hw). split; [split; [exact Hwf|]|].
  - exact (proj2 (bytes_at_rel rsegs m m0 a _ HR) Hb).
  - exact (wr_at_rel rsegs m m0 a _ HR Hw).
Qed.

Lemma f9n_tls : forall m m0, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  forall TP DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k -> asan_tls_cells m0 TP DT TS C T DB k.
Proof.
  intros m m0 BA TP DT TS C T DB k H. unfold asan_tls_cells in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15 &
    H16 & H17 & HDB & H19).
  exact (conj (BA _ _ H1) (conj (BA _ _ H2) (conj (BA _ _ H3) (conj (BA _ _ H4) (conj (BA _ _ H5) (conj Hk
    (conj (BA _ _ H7) (conj (BA _ _ H8) (conj (BA _ _ H9) (conj (BA _ _ H10)
    (conj (ex_intro _ tb (ex_intro _ te (BA _ _ H11))) (conj (BA _ _ H12) (conj (BA _ _ H13) (conj (BA _ _ H14)
    (conj (BA _ _ H15) (conj (BA _ _ H16) (conj (BA _ _ H17) (conj HDB (BA _ _ H19))))))))))))))))))).
Qed.

Lemma f9n_fp : forall m m0, (forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs) ->
  (forall lo hi, AC.GT <= lo -> stk rsegs m lo hi -> stk rsegs m0 lo hi) ->
  forall cs TP FS lo hi W D, fp cs m TP FS lo hi W D -> fp cs m0 TP FS lo hi W D.
Proof.
  intros m m0 BA KS cs TP FS lo hi W D (DT & TS & C & T & DB & k & F1 & F2 & F3 & F4 & F5 & F6 & F7).
  exists DT, TS, C, T, DB, k.
  split; [exact (f9n_tls m m0 BA _ _ _ _ _ _ _ F1)|].
  split; [exact (BA _ _ F2)|].
  split.
  { destruct F3 as (A1 & A2 & A3 & A4 & A5). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    split; [exact A4|]. apply KS; [unfold ASAN_GT, AC.GT in *; lia | exact A5]. }
  split; [exact (BA _ _ F4)|].
  split; [exact (BA _ _ F5)|].
  split; [|exact F7].
  eapply Forall_impl; [|exact F6].
  intros c Hc. unfold fp_cls in Hc |- *. destruct Hc as (Hc6 & h & flags & Hh & Hf & Hl & Hfl).
  split; [exact Hc6|]. exists h, flags. split; [exact (BA _ _ Hh)|]. split; [exact (BA _ _ Hf)|].
  split; [exact Hl | exact Hfl].
Qed.

Lemma f9n_rtls : forall m m0, (forall a bs, bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs) ->
  forall TP FS lo hi, reac_ctrl_identity_reply_tls m TP FS lo hi -> reac_ctrl_identity_reply_tls m0 TP FS lo hi.
Proof.
  intros m m0 BA TP FS lo hi H DT TS C T DB k Hc. exact (H DT TS C T DB k (f9n_tls m0 m BA _ _ _ _ _ _ _ Hc)).
Qed.

Lemma f9n_pre : forall phi len fr S FS TP m G ja jp jn, AC.GT <= fr ->
  f9_pre phi len (fr + 256) (fr + 272) (fr + 304) S FS TP m G ja jp jn ->
  f9_pre_n phi len (fr + 256) (fr + 272) (fr + 304) S FS TP (normalize rsegs m) G ja jp jn.
Proof.
  intros phi len fr S FS TP m G ja jp jn HGT Hpre. unfold f9_pre, f9_pre_n, f9_pre_g in *.
  destruct Hpre as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & HRO & P11 & P12 & P13 & P14 & P15 & P16 & P17 &
    P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28).
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (BA : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs (normalize rsegs m) a bs)
    by (intros a bs H; exact (bytes_at_normalize rsegs m a bs HRO H)).
  assert (BA' : forall a bs, bytes_at rsegs (normalize rsegs m) a bs -> bytes_at rsegs m a bs)
    by (intros a bs H; exact (proj2 (bytes_at_rel rsegs m _ a bs REL) H)).
  assert (AD : forall p n, addressable m p n -> addressable (normalize rsegs m) p n)
    by (intros p n H; exact (proj1 (f9n_addr m _ p n REL) H)).
  do 8 (split; [assumption|]).
  split; [apply f9n_stk_norm; [exact HRO | unfold HIGHMEM_BEG, AC.GT in *; lia | exact P9]|].
  split; [apply mem_inv_normalize|].
  split; [exact P11|].
  split; [intros Ha Hl; destruct (P12 Ha Hl) as (X1 & X2 & X3); split; [exact X1|];
          split; [exact (BA _ _ X2) | exact X3]|].
  split.
  { intros Ha. destruct (P13 Ha) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7).
    split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|].
    split; [apply f9n_rw_norm; [exact HRO | lia | exact Y4]|].
    split; [apply f9n_rw_norm; [exact HRO | lia | exact Y5]|].
    split; [apply f9n_rw_norm; [exact HRO | lia | exact Y6] | exact Y7]. }
  split; [exact (f9n_cells m _ BA P14)|].
  split; [exact (f9n_shrw_norm m HRO P15)|].
  split; [exact P16|]. split; [exact P17|].
  split; [exact (AD _ _ P18)|].
  split; [intros Ha Hl; exact (AD _ _ (P19 Ha Hl))|].
  split.
  { intros Ha. destruct (P20 Ha) as (Z1 & Z2 & Z3 & Z4).
    split; [exact (AD _ _ Z1)|]. split; [exact (AD _ _ Z2)|]. split; [exact (AD _ _ Z3) | exact Z4]. }
  split; [exact (AD _ _ P21)|].
  split; [exact (BA _ _ P22)|]. split; [exact (BA _ _ P23)|]. split; [exact (BA _ _ P24)|].
  split; [exact (BA _ _ P25)|]. split; [exact (BA _ _ P26)|].
  split.
  - apply (f9n_fp m _ BA); [|exact P27].
    intros lo hi Hlo Hs. exact (f9n_stk_norm m lo hi HRO Hlo Hs).
  - exact (f9n_rtls m _ BA' _ _ _ _ P28).
Qed.

(* A state related to an MS state by evt_normalize's ms_rel is that state with its own memory (F12's
   f12_ms_rel_MS). *)
Lemma f9n_ms_rel_MS : forall s R F pc fc rv m0 ro,
  ms_rel rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel rsegs (ms_mem s) m0.
Proof.
  intros [r f p sv rv' fc' m ro'] R F pc fc rv m0 ro (Hr & Hf & Hpc & Hsvc & Hres & Hfc & Hrom & Hm).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in *.
  subst. split; [reflexivity | exact Hm].
Qed.

(* The call on its contract from a memory with ro_agree (the cuts' form): f9_evtB_n on the normalized memory,
   carried back by MemNorm.evt_normalize; the post's facts come back across mem_rel / ro_same. *)
Lemma f9_evtB :
  forall (ra0 sp gp tp t0 t1 t2 s0 a0 a1 s5 s6 s7 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
         (A S3 fr phi len S FS TP : Z) (G ja jp jn : list byte),
    reac_ctrl_identity_reply_contract ->
    sp = Z_to_bv 64 S -> tp = Z_to_bv 64 TP -> 0 <= TP < 2 ^ 64 -> AC.GT <= fr ->
    f9_pre phi len (fr + 256) (fr + 272) (fr + 304) S FS TP m G ja jp jn ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
       munch (reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) S G ++
              fp_w [1%nat] FS ++
              [(shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S)]) m m' ->
       wmono rsegs m m' -> ro_agree rsegs m' ->
       stk rsegs m' (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
       (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G = true ->
          rw_cells rsegs m' (fr + 256) [CB 2 (reply_addr G)] /\
          rw_cells rsegs m' (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
          rw_cells rsegs m' (fr + 304) [CB 8 (le8 (Z_to_bv 64 (ir_s G - 13)))]) ->
       asan_cells m' -> shadow_rw m' ->
       addressable m' (S - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
       fp [1%nat] m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S
         (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) S)
         (reac_ctrl_identity_reply_D phi len (fr + 256) (fr + 272) (fr + 304)) ->
       reac_ctrl_identity_reply_tls m' TP FS (S - REAC_CTRL_IDENTITY_REPLY_K) S ->
       Q (MS (mkR (Z_to_bv 64 0x821ec) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                  (Z_to_bv 64 (reply_ret phi len (fr + 256) (fr + 272) (fr + 304) G))
                  a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7
                  s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
             Fr (Z_to_bv 64 0x821ec) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0 a1 (Z_to_bv 64 (fr + 256)) (Z_to_bv 64 (fr + 272))
               (Z_to_bv 64 (fr + 304)) a5 a6 a7 (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7
               s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x821e0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 a0 a1 s5 s6 s7 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 Fr fc m Q A S3 fr phi len S0 FS TP
    G ja jp jn HIR Hsp Htp HTP HGT Hpre HK.
  assert (HRO : ro_agree rsegs m).
  { unfold f9_pre, f9_pre_g in Hpre. destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. }
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  pose proof (f9n_pre phi len fr S0 FS TP m G ja jp jn HGT Hpre) as Hn.
  pose (WC := reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) S0 G ++ fp_w [1%nat] FS ++
              [(shadow_addr (S0 - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S0)]).
  pose (K0 := fun m0' : word -> option byte =>
    munch WC (normalize rsegs m) m0' /\ wmono rsegs (normalize rsegs m) m0' /\
    stk rsegs m0' (S0 - REAC_CTRL_IDENTITY_REPLY_K) S0 /\
    (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G = true ->
       rw_cells rsegs m0' (fr + 256) [CB 2 (reply_addr G)] /\
       rw_cells rsegs m0' (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
       rw_cells rsegs m0' (fr + 304) [CB 8 (le8 (Z_to_bv 64 (ir_s G - 13)))]) /\
    asan_cells m0' /\ shadow_rw m0' /\
    addressable m0' (S0 - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
    fp [1%nat] m0' TP FS (S0 - REAC_CTRL_IDENTITY_REPLY_K) S0
      (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) S0)
      (reac_ctrl_identity_reply_D phi len (fr + 256) (fr + 272) (fr + 304)) /\
    reac_ctrl_identity_reply_tls m0' TP FS (S0 - REAC_CTRL_IDENTITY_REPLY_K) S0).
  pose (Q0 := fun s0' : machine_state =>
    exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m0' : word -> option byte),
      s0' = MS (mkR (Z_to_bv 64 0x821ec) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                  (Z_to_bv 64 (reply_ret phi len (fr + 256) (fr + 272) (fr + 304) G))
                  a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 phi) (Z_to_bv 64 S3) (Z_to_bv 64 len) s5 s6 s7
                  s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
             Fr (Z_to_bv 64 0x821ec) fc None m0' (seg_rom rsegs) /\ K0 m0').
  eapply LE.evt_mono.
  { apply (evt_normalize rsegs Q0); [vm_compute; reflexivity | exact HRO |].
    apply (f9_evtB_n ra0 sp gp tp t0 t1 t2 s0 a0 a1 s5 s6 s7 s8 s9 s11 a5 a6 a7 t3 t4 t5 t6 Fr fc
             (normalize rsegs m) Q0 A S3 fr phi len S0 FS TP G ja jp jn HIR Hsp Htp HTP Hn).
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m0' MU WM _ ST HR HAC HSW HAD HFP HTLS.
    unfold Q0, K0. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m0'.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact HR|].
    split; [exact HAC|]. split; [exact HSW|]. split; [exact HAD|]. split; [exact HFP | exact HTLS]. }
  intros s Hs. unfold Q0, K0 in Hs.
  destruct Hs as (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
    Es0 & MU & WM & ST & HR & HAC & HSW & HAD & HFP & HTLS) & Hrel & Hros).
  subst s0'. destruct (f9n_ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as (Es & Hmr). rewrite Es.
  set (m' := ms_mem s) in *.
  assert (BA : forall a bs, bytes_at rsegs m0' a bs -> bytes_at rsegs m' a bs)
    by (intros a bs H; exact (proj2 (bytes_at_rel rsegs m' m0' a bs Hmr) H)).
  assert (BA' : forall a bs, bytes_at rsegs m' a bs -> bytes_at rsegs m0' a bs)
    by (intros a bs H; exact (proj1 (bytes_at_rel rsegs m' m0' a bs Hmr) H)).
  apply HK.
  - exact (munch_rel rsegs _ m (normalize rsegs m) m' m0' REL Hmr Hros MU).
  - exact (wmono_rel rsegs m (normalize rsegs m) m' m0' REL Hmr Hros WM).
  - exact (ro_agree_of_mem_rel rsegs m' m0' Hmr).
  - exact (f9n_stk_back m' m0' _ _ Hmr ST).
  - intros Hok. destruct (HR Hok) as (R1 & R2 & R3).
    split; [exact (f9n_rw_back m' m0' _ _ Hmr R1)|].
    split; [exact (f9n_rw_back m' m0' _ _ Hmr R2) | exact (f9n_rw_back m' m0' _ _ Hmr R3)].
  - exact (f9n_cells m0' m' BA HAC).
  - exact (f9n_shrw_back m' m0' Hmr HSW).
  - exact (proj2 (f9n_addr m' m0' _ _ Hmr) HAD).
  - apply (f9n_fp m0' m' BA); [|exact HFP].
    intros lo hi _ Hs. exact (f9n_stk_back m' m0' lo hi Hmr Hs).
  - exact (f9n_rtls m0' m' BA' _ _ _ _ HTLS).
Qed.

Lemma l1_dj_pt : forall (Q : Z -> Prop) a b c d, a < b -> c < d ->
  (forall x, a <= x < b -> Q x) -> (forall x, c <= x < d -> ~ Q x) -> RcLay.ly_dj a b c d.
Proof.
  intros Q a b c d Hab Hcd HQ HnQ. unfold RcLay.ly_dj.
  destruct (Z_le_gt_dec b c) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec d a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (HnQ (Z.max a c) ltac:(lia)). apply HQ. lia.
Qed.

Lemma l1_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma l1_word_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia.
Qed.

Lemma l1_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (l1_byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs).
  { rewrite bytes_le_to_Z_le_val. exact (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2 ^ 8)%Z.
    change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma l1_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by (cbn; lia).
  rewrite <- L at 1. apply l1_le_bytes_to_Z.
Qed.

(* A single present byte is a one-byte bytes_at. *)

Lemma l1_byte_at : forall m a b, 0 <= a -> a + 1 <= 2 ^ 64 -> mbyte rsegs m a = Some b ->
  bytes_at rsegs m a [b].
Proof.
  intros m a b H0 H1 Hb. split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
  cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact Hb.
Qed.

(* A range of present bytes, all satisfying P, is a bytes_at of a list of that length. *)

Lemma l1_bytes_PN : forall (P : byte -> Prop) m a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = k /\ Forall P bs.
Proof.
  intros P m a k. revert a. induction k as [|k IH]; intros a H0 H1 H.
  - exists []. split; [|split; [reflexivity | constructor]].
    split; [exact H0|]. split; [cbn [length]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - destruct (H 0 ltac:(lia)) as (b & Hb & HPb).
    assert (Hrec : forall i, 0 <= i < Z.of_nat k -> exists b', mbyte rsegs m (a + 1 + i) = Some b' /\ P b').
    { intros i Hi. destruct (H (1 + i) ltac:(lia)) as (b' & Hb' & HP'). exists b'.
      split; [|exact HP']. replace (a + 1 + i) with (a + (1 + i)) by lia. exact Hb'. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrec) as (bs & Hbs & Hlen & HPbs).
    exists (b :: bs). split; [|split; [cbn [length]; lia | constructor; assumption]].
    destruct Hbs as (_ & _ & Hnth).
    split; [exact H0|]. split; [cbn [length]; rewrite Hlen; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + replace (a + Z.of_nat 0) with (a + 0) by lia. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hnth. cbn [length] in Hi. lia.
Qed.

Lemma l1_bytes_P : forall (P : byte -> Prop) m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ Z.of_nat (length bs) = n /\ Forall P bs.
Proof.
  intros P m a n H0 Hn H1 H.
  destruct (l1_bytes_PN P m a (Z.to_nat n) H0 ltac:(rewrite Z2Nat.id by lia; lia)
              ltac:(rewrite Z2Nat.id by lia; exact H)) as (bs & Hbs & Hlen & HP).
  exists bs. split; [exact Hbs|]. split; [rewrite Hlen, Z2Nat.id by lia; reflexivity | exact HP].
Qed.

(* Eight present bytes read as some word. *)

Lemma l1_word_present : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b) ->
  exists w : word, bytes_at rsegs m a (le8 w).
Proof.
  intros m a H0 H1 H.
  assert (HP : forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b /\ True).
  { intros i Hi. destruct (H i Hi) as (b & Hb). exists b. split; [exact Hb | exact I]. }
  destruct (l1_bytes_P (fun _ => True) m a 8 H0 ltac:(lia) H1 HP) as (bs & Hbs & Hlen & _).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite l1_le8_of_bytes by lia. exact Hbs.
Qed.

(* word_mem pins the value only modulo 2^64. *)

Lemma l1_word_mem_eq : forall m a v1 v2, word_mem rsegs m a v1 -> word_mem rsegs m a v2 ->
  v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (E : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (EB : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    rewrite <- (kb_byte_unsigned v1 8 k), <- (kb_byte_unsigned v2 8 k), EB. reflexivity. }
  assert (M : forall v k, le_byte (v mod 2 ^ 64) 8 k = le_byte v 8 k).
  { intros v k. unfold le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. }
  pose proof (kb_le8_digits (v1 mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as D1.
  pose proof (kb_le8_digits (v2 mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as D2.
  rewrite !M in D1. rewrite !M in D2.
  rewrite D1 at 1. rewrite D2 at 1.
  rewrite (E 0%nat ltac:(lia)), (E 1%nat ltac:(lia)), (E 2%nat ltac:(lia)), (E 3%nat ltac:(lia)),
    (E 4%nat ltac:(lia)), (E 5%nat ltac:(lia)), (E 6%nat ltac:(lia)), (E 7%nat ltac:(lia)).
  reflexivity.
Qed.

Lemma l1_wm_norm : forall m a x y, word_mem rsegs m a x -> word_mem rsegs m a y ->
  0 <= y < 2 ^ 64 -> - (2 ^ 64) < x < 2 ^ 64 -> x = y \/ x = y - 2 ^ 64.
Proof.
  intros m a x y Hx Hy Hy0 Hx0.
  pose proof (l1_word_mem_eq m a x y Hx Hy) as E.
  rewrite (Z.mod_small y (2 ^ 64)) in E by lia.
  destruct (Z_le_gt_dec 0 x) as [Hs|Hs].
  - left. rewrite (Z.mod_small x (2 ^ 64)) in E by lia. exact E.
  - right.
    assert (EM : (x + 2 ^ 64) mod 2 ^ 64 = x mod 2 ^ 64).
    { replace (x + 2 ^ 64) with (x + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full. }
    rewrite (Z.mod_small (x + 2 ^ 64) (2 ^ 64)) in EM by lia. lia.
Qed.

Lemma l1_sh_lo : forall a, 0 <= a -> LOWMEM_END <= shadow_addr a.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, LOWMEM_END.
  assert (0 <= a / 8) by (apply Z.div_pos; lia). lia.
Qed.

(* The class-1 ranges of the side stack, as plain offsets of FS. *)

Lemma l1_fs_M1 : fs_M 1%nat = 8192.
Proof. reflexivity. Qed.

Lemma l1_fs_B1 : fs_B 1%nat = 128.
Proof. reflexivity. Qed.

Lemma l1_fs_hint1 : forall FS, fs_hint FS 1%nat = FS + 8.
Proof. intros FS. unfold fs_hint. cbn [Z.of_nat]. lia. Qed.

Lemma l1_fs_flag1 : forall FS, fs_flag FS 1%nat 0 = FS + 20480.
Proof.
  intros FS. unfold fs_flag. cbn [Z.of_nat]. change (2 ^ 15) with 32768.
  change (2 ^ (15 - 1)) with 16384. lia.
Qed.

Lemma l1_afs_flag1 : forall FS j, AC.a_fs_flag FS 1%nat j = FS + 20480 + j.
Proof.
  intros FS j. unfold AC.a_fs_flag.
  change (2 ^ (15 - Z.of_nat 1)) with 16384. change (2 ^ 15) with 32768. lia.
Qed.

Lemma l1_fs_frame1_0 : forall FS, fs_frame FS 1%nat 0 = FS + 1085440.
Proof.
  intros FS. unfold fs_frame. rewrite l1_fs_B1. cbn [Z.of_nat]. change (2 ^ 20) with 1048576. lia.
Qed.

Lemma l1_fs_frame1_M : forall FS, fs_frame FS 1%nat (fs_M 1%nat) = FS + 2134016.
Proof.
  intros FS. unfold fs_frame. rewrite l1_fs_B1, l1_fs_M1. cbn [Z.of_nat].
  change (2 ^ 20) with 1048576. lia.
Qed.

Lemma l1_fpw1 : forall FS, fp_w [1%nat] FS =
  [(FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016))].
Proof.
  intros FS. unfold fp_w. cbn [flat_map]. rewrite app_nil_r. unfold fp_w1.
  rewrite l1_fs_hint1, l1_fs_flag1, l1_fs_frame1_0, l1_fs_frame1_M, l1_fs_M1.
  replace (FS + 8 + 8) with (FS + 16) by lia.
  replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

Lemma l1_fs_frame0 : forall FS, fs_frame FS 0%nat 0 = FS + 36864.
Proof.
  intros FS. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576.
  change (2 ^ 0) with 1. lia.
Qed.

Lemma l1_sh_hi : forall a, a <= APPMEM_END -> shadow_addr a <= HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; unfold APPMEM_END in *; lia).
  lia.
Qed.

(* Each disjointness leaf names image constants, FS / fr / sp offsets and shadow endpoints: unfold the constants
   and let lia use the range facts of the context. *)

Ltac l1_num :=
  cbv [RcLay.ly_dj TLS_INDEX REAL_TLS_GET_ADDR TSD_KEY_INITED TSD_KEY GOT_CF CF GOT_VERBOSITY VERBOSITY DTLS_TPOFF
       RT_TP RT_TSDMAIN RT_GT ASAN_GT AC.as_tp AC.ASYMS AC.GT AC.FS_SIZE FS_SIZE RT_FS_SIZE
       REAC_CTRL_IDENTITY_REPLY_K AF.SLOT_STACK HIGHMEM_BEG APPMEM_END LOWMEM_END LOWSHADOW_END HIGHSHADOW_BEG
       ASAN_K] in *; lia.

Ltac l1_dj_split := repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd].

(* a_fs_ok's five parts, taken apart once here (a Theorem Labs lane 15:32Z). *)
Local Lemma f9_fs_ok_parts : forall mem FS, AC.a_fs_ok mem FS ->
  (forall a, FS <= a < FS + AC.FS_SIZE -> writable_at rsegs mem a /\ exists b, mbyte rsegs mem a = Some b) /\
  word_mem rsegs mem (FS + 88) 20 /\ mbyte rsegs mem (FS + 96) = Some (Z_to_bv 8 0) /\
  (forall c, (c <= 10)%nat -> exists h, word_mem rsegs mem (AC.a_fs_hint FS c) h) /\
  (forall c j, (c <= 10)%nat -> 0 <= j < AC.a_fs_M c ->
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 0) \/
     mbyte rsegs mem (AC.a_fs_flag FS c j) = Some (Z_to_bv 8 1)).
Proof.
  intros mem FS H. unfold AC.a_fs_ok in H. destruct H as (H1 & H2 & H3 & H4 & H5).
  exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.

Section S_l1.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Definition f9_W9 (fr : Z) : list ivl :=
  [(Sfr fr + 32, Sfr fr + 33); (fr + 256, fr + 258); (Sfr fr + 34, Sfr fr + 35); (fr + 272, fr + 280);
   (Sfr fr + 38, Sfr fr + 39); (fr + 304, fr + 312)].

(* The frame placement facts the F9 cut carries (P7's XC convention). *)

Lemma f9_fp_call : forall g fr phi len regs mem md,
  FRA B APIf ra g fr [(phi, AC.a_size len)] regs mem md -> f9_PL fr regs mem ->
  AC.aspZ regs <= APPMEM_END ->
  (exists DB, word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) DB /\ 0 <= DB /\ DB + 32 <= 2 ^ 64) ->
  exists FS,
    word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
    fp [1%nat] mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs)
      (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) (AC.aspZ regs))
      (reac_ctrl_identity_reply_D phi len (fr + 256) (fr + 272) (fr + 304)) /\
    reac_ctrl_identity_reply_tls mem (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K)
      (AC.aspZ regs).
Proof.
  intros g fr phi len regs mem md HFRA HPL HspA (DBp & HDBp & HDBp0 & HDBp1).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & Hsp4096 & HSapp & Hspill & Hsel & Hq56 & Hloc &
    Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWINa & Hhi1 & Hhi2 & Hhi3 & Hhb & Hlive).
  destruct HPL as (Happ & Hgt & Hdisj & HA9 & Hfs9).
  rewrite Haspz in HspA |- *.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof Hloc as Hloc'.
  (* ---- the side stack's base FS ---- *)
  destruct (AsanRTInv.RT_fs_cells _ _ _ HRT)
    as (Htlsidx & Hdtpoff & Hdt & Hdt8 & (FSw & HFSb & HFSok) & (DBw & HDBb & HDBnz)).
  pose proof (bytes_at_le8_word rsegs mem RT_TP FSw HFSb) as HFSwm.
  remember (bv_unsigned FSw) as FS eqn:EFS.
  assert (HFS64 : 0 <= FS < 2 ^ 64) by (rewrite EFS; apply l1_word_range).
  destruct HFSok as (HFSpos & HFSalign & HFSgt & HFSapp).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as NSTK1.
  destruct (lw_fs_place (APIf rc) _ _ _ _ HAH HFSwm HFS64) as [_ NFS1 _ _].
  destruct (fsf_fs_state_fields (APIf rc) _ _ _ _ HAH HFSwm HFS64)
    as (DBz & [HFSokz HDBzw HDBzr HDBznz HDBztp HDBzp HT48app]).
  destruct (f9_fs_ok_parts _ _ HFSokz) as (HFSpres & HFS88 & HFS96 & HFShint & HFSflag).
  assert (NAPP : APPMEM_END < 2 ^ 64) by (unfold APPMEM_END; lia).
  assert (NFSB : FS + 11571200 <= APPMEM_END)
    by (unfold AC.FS_SIZE in NFS1; unfold AF.SLOT_STACK in Hstklo; lia).
  (* ---- the thread record ---- *)
  destruct (fsf_thread_fields (APIf rc) _ _ _ HAH) as (C0 & T0 & [_ HC0wm HT0wm HC0rng HT0rng HC152 HT48]).
  destruct (AsanRTInv.RT_uw_cells _ _ _ HRT) as (Htsdi & Htsdk & _ & Htp88 & (Cw & HCwb)).
  pose proof (bytes_at_le8_word rsegs mem RT_TSDMAIN Cw HCwb) as HCwm.
  assert (ECw : bv_unsigned Cw = C0).
  { pose proof (l1_word_range Cw) as HR.
    destruct (l1_wm_norm mem RT_TSDMAIN (bv_unsigned Cw) C0 HCwm HC0wm ltac:(lia) ltac:(lia)) as [E|E];
      [exact E | lia]. }
  assert (HCapp : forall x, C0 + 152 <= x < C0 + 160 -> app_mem x).
  { intros x Hx. pose proof (proj2 (HC152 (x - (C0 + 152)) ltac:(lia))) as H.
    replace (C0 + 152 + (x - (C0 + 152))) with x in H by lia. exact H. }
  assert (HCpt : forall x, C0 + 152 <= x < C0 + 160 ->
            x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HC152 (x - (C0 + 152)) ltac:(lia)) as (Hown & Hap).
    replace (C0 + 152 + (x - (C0 + 152))) with x in Hown by lia.
    pose proof (HCapp x Hx) as Hax.
    pose proof (fun Hor => lwn_byte (lw_not_owned (APIf rc) _ _ _ x HAH Hor)) as HNO.
    split.
    - destruct (Z_lt_le_dec x (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END)
        by (unfold APPMEM_END; lia).
      exact (HNO (or_intror (or_intror (or_intror Hst))) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x) by (exists FS; split; [assumption|]; split; [exact HFSwm | exact Hin]).
      exact (HNO (or_intror (or_intror (or_introl HFSin))) Hown). }
  assert (HTapp : forall x, T0 + 48 <= x < T0 + 64 -> app_mem x).
  { intros x Hx. pose proof (HT48app C0 T0 HC0wm ltac:(lia) HT0wm ltac:(lia) (x - (T0 + 48)) ltac:(lia)) as H.
    replace (T0 + 48 + (x - (T0 + 48))) with x in H by lia. exact H. }
  assert (HTpt : forall x, T0 + 48 <= x < T0 + 64 ->
            x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct (HT48 (x - (T0 + 48)) ltac:(lia)) as (Hown & _).
    replace (T0 + 48 + (x - (T0 + 48))) with x in Hown by lia.
    pose proof (HTapp x Hx) as Hax.
    pose proof (fun Hor => lwn_byte (lw_not_owned (APIf rc) _ _ _ x HAH Hor)) as HNO.
    split.
    - destruct (Z_lt_le_dec x (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)) as [H|H]; [exact H|].
      exfalso. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Hst : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x < APPMEM_END)
        by (unfold APPMEM_END; lia).
      exact (HNO (or_intror (or_intror (or_intror Hst))) Hown).
    - intros Hin.
      assert (HFSin : AC.a_in_fs AC.ASYMS mem x) by (exists FS; split; [assumption|]; split; [exact HFSwm | exact Hin]).
      exact (HNO (or_intror (or_intror (or_introl HFSin))) Hown). }
  assert (HTpres : forall i, 0 <= i < 16 -> exists b, mbyte rsegs mem (T0 + 48 + i) = Some b).
  { intros i Hi. exact (proj2 (HT48 i Hi)). }
  (* ---- the thread's DTLS word ---- *)
  assert (EDBz : DBz = DBp).
  { pose proof (proj1 (HDBzp (DBz + 24) ltac:(lia))) as Ha1.
    pose proof (proj1 (HDBzp (DBz + 31) ltac:(lia))) as Ha2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha1, Ha2.
    destruct (l1_wm_norm mem (AC.as_tp AC.ASYMS + 8) DBz DBp HDBzw HDBp ltac:(lia) ltac:(lia)) as [E|E];
      [exact E | lia]. }
  assert (EDBw : bv_unsigned DBw = DBp).
  { pose proof (l1_word_range DBw) as HR.
    pose proof (bytes_at_le8_word rsegs mem (RT_TP + 8) DBw HDBb) as HDBwm.
    destruct (l1_wm_norm mem (AC.as_tp AC.ASYMS + 8) (bv_unsigned DBw) DBp HDBwm HDBp ltac:(lia) ltac:(lia))
      as [E|E]; [exact E | lia]. }
  assert (HDBpt : forall x, DBp + 24 <= x < DBp + 32 ->
            app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
            ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. rewrite <- EDBz in Hx. destruct (HDBzp x Hx) as (H1 & H2 & H4).
    split; [exact H1|]. split; [exact H2|]. intros Hin. apply H4.
    exists FS. split; [assumption|]. split; [exact HFSwm | exact Hin]. }
  assert (HDB24 : bytes_at rsegs mem (bv_unsigned DBw + 24) (le8 (Z_to_bv 64 (AC.as_tp AC.ASYMS)))).
  { rewrite EDBw, <- EDBz.
    apply (word_mem_le8 rsegs mem (DBz + 24) (AC.as_tp AC.ASYMS) HDBztp);
      [cbv [AC.as_tp AC.ASYMS]; lia | lia | lia]. }
  (* ---- numeric bounds of the thread cells ---- *)
  assert (NC0 : C0 + 160 <= APPMEM_END).
  { pose proof (HCapp (C0 + 159) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NT0 : T0 + 64 <= APPMEM_END).
  { pose proof (HTapp (T0 + 63) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. unfold APPMEM_END. lia. }
  assert (NC : C0 + 160 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (HCpt (C0 + 159) ltac:(lia))); lia).
  assert (NT : T0 + 64 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (HTpt (T0 + 63) ltac:(lia))); lia).
  assert (NDB : DBp + 32 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (pose proof (proj1 (proj2 (HDBpt (DBp + 31) ltac:(lia)))); lia).
  (* ---- the words the tls cells name ---- *)
  assert (EDTu : bv_unsigned (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) = AC.as_tp AC.ASYMS + 32)
    by (apply MState.unsigned_lit; cbv [AC.as_tp AC.ASYMS]; lia).
  assert (ETSu : bv_unsigned (Z_to_bv 64 RT_TSDMAIN) = RT_TSDMAIN)
    by (apply MState.unsigned_lit; unfold RT_TSDMAIN; lia).
  assert (ETu : bv_unsigned (Z_to_bv 64 T0) = T0) by (apply MState.unsigned_lit; lia).
  pose proof (word_mem_le8 rsegs mem (C0 + 152) T0 HT0wm ltac:(lia) ltac:(lia)
                ltac:(unfold APPMEM_END in *; lia)) as HT0b.
  destruct (l1_word_present mem (T0 + 48) ltac:(lia) ltac:(unfold APPMEM_END in *; lia)
      ltac:(intros i Hi; exact (HTpres i ltac:(lia)))) as (tb & Htb).
  assert (HTpres2 : forall i, 0 <= i < 8 -> exists b, mbyte rsegs mem (T0 + 56 + i) = Some b).
  { intros i Hi. replace (T0 + 56 + i) with (T0 + 48 + (8 + i)) by lia. exact (HTpres (8 + i) ltac:(lia)). }
  destruct (l1_word_present mem (T0 + 56) ltac:(lia) ltac:(unfold APPMEM_END in *; lia) HTpres2) as (te & Hte).
  assert (HTBE : bytes_at rsegs mem (T0 + 48) (le8 tb ++ le8 te)).
  { apply (proj2 (bytes_at_app rsegs mem (T0 + 48) (le8 tb) (le8 te))).
    split; [exact Htb|]. rewrite length_le8.
    replace (T0 + 48 + Z.of_nat 8) with (T0 + 56) by lia. exact Hte. }
  destruct (AsanRTInv.RT_cf_cells _ _ _ HRT) as (Hcf1 & _ & _ & _ & _ & Hcf137 & _ & _).
  destruct (AsanRTInv.RT_opt_cells _ _ _ HRT) as (_ & _ & Hopt3 & Hopt4).
  pose proof (AsanRTInv.RT_real_cells _ _ _ HRT) as HREAL.
  assert (HTLS : asan_tls_cells mem (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                   (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0).
  { unfold asan_tls_cells. rewrite EDTu, ETSu, ETu, ECw.
    split; [exact Htlsidx|].
    split; [exact (AsanRTInv.real_cell_of mem REAL_TLS_GET_ADDR MUSL_TLS_GET_ADDR HREAL
                     ltac:(vm_compute; reflexivity))|].
    split; [exact Hdt|].
    split; [exact Hdt8|].
    split; [exact Htsdi|].
    split; [lia|].
    split; [exact Htsdk|].
    split; [exact Htp88|].
    split; [exact HCwb|].
    split; [exact HT0b|].
    split; [exists tb, te; exact HTBE|].
    split; [exact Hcf1|].
    split; [exact Hcf137|].
    split; [exact Hopt3|].
    split; [exact Hopt4|].
    split; [exact Hdtpoff|].
    split; [exact HDBb|].
    split; [exact (proj1 HDBnz)|].
    exact HDB24. }
  (* ---- the frame's placement: real stack or side stack ---- *)
  assert (HFSuniq : forall b x, word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> b <= x < b + AC.FS_SIZE ->
            0 <= x < APPMEM_END -> b = FS).
  { intros b x Hb Hbx Hx.
    destruct (l1_wm_norm mem (AC.as_tp AC.ASYMS) b FS Hb HFSwm HFS64
                ltac:(unfold AC.FS_SIZE, APPMEM_END in *; lia)) as [E|E];
      [exact E | unfold AC.FS_SIZE, APPMEM_END in *; lia]. }
  assert (HFRQ : forall x, fr <= x < fr + FRAME_BYTES ->
            AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/ (FS <= x < FS + AC.FS_SIZE)).
  { intros x Hx. destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
    - left. exact (proj1 (Hreal x Hx)).
    - right. destruct (Hfs x Hx) as (b & _ & Hb & Hbx).
      pose proof (Happ x Hx) as Hax. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      rewrite <- (HFSuniq b x Hb Hbx ltac:(unfold APPMEM_END; lia)). exact Hbx. }
  assert (HFRFS : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= fr \/
                  (FS + 36864 + 6 * 2 ^ 20 <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE)).
  { destruct Hloc' as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
    - left. exact (proj1 (Hreal fr ltac:(lia))).
    - right. destruct (Hfs fr ltac:(lia)) as (b & _ & Hb & Hbx).
      pose proof (Happ fr ltac:(lia)) as Hax. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hax.
      assert (Eb : b = FS) by (apply (HFSuniq b fr Hb Hbx); unfold APPMEM_END; lia).
      rewrite Eb in Hbx. exact (Hfs9 FS HFSwm HFS64 Hbx). }
  (* ---- app memory and shadow memory are apart ---- *)
  assert (HGAP : forall x, LOWMEM_END <= x < HIGHMEM_BEG -> ~ app_mem x).
  { intros x Hx Hap. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (AS_C : RcLay.ly_dj (C0 + 152) (C0 + 160) LOWMEM_END HIGHMEM_BEG).
  { apply (l1_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HCapp | exact HGAP]. }
  assert (AS_T : RcLay.ly_dj (T0 + 48) (T0 + 64) LOWMEM_END HIGHMEM_BEG).
  { apply (l1_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact HTapp | exact HGAP]. }
  assert (AS_DB : RcLay.ly_dj (DBp + 24) (DBp + 32) LOWMEM_END HIGHMEM_BEG).
  { apply (l1_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
    | intros x Hx; exact (proj1 (HDBpt x Hx)) | exact HGAP]. }
  assert (AS_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) LOWMEM_END HIGHMEM_BEG).
  { apply (l1_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia | exact Happ | exact HGAP]. }
  (* ---- the shadow of the class-1 frames and of the callee's window lies between the app ranges ---- *)
  assert (SB1a : LOWMEM_END <= shadow_addr (FS + 1085440)) by (apply l1_sh_lo; lia).
  assert (SB1b : shadow_addr (FS + 2134016) <= HIGHMEM_BEG)
    by (apply l1_sh_hi; unfold APPMEM_END in *; lia).
  assert (SB2a : LOWMEM_END <= shadow_addr (sp - REAC_CTRL_IDENTITY_REPLY_K)).
  { apply l1_sh_lo. unfold REAC_CTRL_IDENTITY_REPLY_K, AF.SLOT_STACK, HIGHMEM_BEG in *. lia. }
  assert (SB2b : shadow_addr sp <= HIGHMEM_BEG) by (apply l1_sh_hi; lia).
  (* ---- the thread cells are apart from the frame and from the side stack ---- *)
  assert (DJ_C_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) (C0 + 152) (C0 + 160)).
  { apply (l1_dj_pt (fun x => AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/
                              (FS <= x < FS + AC.FS_SIZE)));
      [lia | lia | exact HFRQ |].
    intros x Hx Hq. destruct (HCpt x Hx) as (H1 & H2). destruct Hq as [Hq|Hq]; [lia | exact (H2 Hq)]. }
  assert (DJ_T_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) (T0 + 48) (T0 + 64)).
  { apply (l1_dj_pt (fun x => AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/
                              (FS <= x < FS + AC.FS_SIZE)));
      [lia | lia | exact HFRQ |].
    intros x Hx Hq. destruct (HTpt x Hx) as (H1 & H2). destruct Hq as [Hq|Hq]; [lia | exact (H2 Hq)]. }
  assert (DJ_DB_FR : RcLay.ly_dj fr (fr + FRAME_BYTES) (DBp + 24) (DBp + 32)).
  { apply (l1_dj_pt (fun x => AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= x \/
                              (FS <= x < FS + AC.FS_SIZE)));
      [lia | lia | exact HFRQ |].
    intros x Hx Hq. destruct (HDBpt x Hx) as (_ & H1 & H2). destruct Hq as [Hq|Hq]; [lia | exact (H2 Hq)]. }
  assert (DJ_C_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (C0 + 152) (C0 + 160)).
  { apply (l1_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (HCpt x Hx)). }
  assert (DJ_T_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (T0 + 48) (T0 + 64)).
  { apply (l1_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (HTpt x Hx)). }
  assert (DJ_DB_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) (DBp + 24) (DBp + 32)).
  { apply (l1_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
      [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
    intros x Hx. exact (proj2 (proj2 (HDBpt x Hx))). }
  (* ---- the heap block of the reply arguments ---- *)
  assert (HPHI : 50 <= len -> forall x, phi <= x < phi + 50 ->
            app_mem x /\ ~ (FS <= x < FS + AC.FS_SIZE)).
  { intros Hlen x Hx.
    destruct (lw_blocks (APIf rc) _ _ _ phi (AC.a_size len) HAH
                ltac:(apply in_or_app; left; left; reflexivity)) as [_ _ _ _ Hb].
    destruct (Hb x ltac:(unfold AC.a_size; pose proof (Z.le_max_l len 1); lia)) as (Hap & _ & _ & _ & Hnfs).
    split; [exact Hap|]. intros Hin. apply Hnfs. exists FS. split; [assumption|]. split; [exact HFSwm | exact Hin]. }
  (* ---- the goal ---- *)
  clear Hloc Hloc' Hs5 Hdisj HFRQ HFSuniq Hfrm Hspm HAm.
  exists FS.
  split; [exact HFSwm|].
  split; [exact HFS64|].
  split.
  { (* fp *)
    exists (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)), (Z_to_bv 64 RT_TSDMAIN), Cw, (Z_to_bv 64 T0), DBw, 0.
    split; [exact HTLS|].
    split; [rewrite EFS, MState.Z_to_bv_bv_unsigned; exact HFSb|].
    split.
    { unfold fs_place. split; [lia|]. split; [exact HFSalign|].
      split; [unfold ASAN_GT, RT_GT in *; lia|].
      split; [intros a Ha; apply HFSapp; unfold FS_SIZE, RT_FS_SIZE in *; lia|].
      split; [lia|]. split; [unfold FS_SIZE in *; lia|].
      intros a Ha. destruct (HFSpres a ltac:(unfold AC.FS_SIZE, FS_SIZE in *; lia)) as (Hw & b & Hb).
      split; [exact Hw | exists b; exact Hb]. }
    split; [exact (word_mem_le8 rsegs mem (FS + 88) 20 HFS88 ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [apply l1_byte_at; [lia | lia | exact HFS96]|].
    split.
    { apply Forall_cons; [|apply Forall_nil].
      unfold fp_cls. split; [lia|].
      destruct (l1_word_present mem (FS + 8) ltac:(lia) ltac:(lia)
          ltac:(intros i Hi;
                destruct (HFSpres (FS + 8 + i) ltac:(unfold AC.FS_SIZE in *; lia)) as (_ & bb & Hbb);
                exists bb; exact Hbb)) as (h & Hh).
      destruct (l1_bytes_P (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) mem (FS + 20480) 8192
          ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(intros i Hi;
                pose proof (HFSflag 1%nat i ltac:(lia) ltac:(change (AC.a_fs_M 1%nat) with 8192; lia)) as Hf;
                rewrite l1_afs_flag1 in Hf;
                destruct Hf as [Hf|Hf]; [exists (Z_to_bv 8 0) | exists (Z_to_bv 8 1)];
                  (split; [exact Hf | first [left; reflexivity | right; reflexivity]])))
                as (flags & Hfl & Hfllen & Hflb).
      exists h, flags.
      rewrite l1_fs_hint1, l1_fs_flag1, l1_fs_M1.
      split; [exact Hh|]. split; [exact Hfl|]. split; [exact Hfllen | exact Hflb]. }
    split; [l1_num|].
    split; [intros a Ha; unfold app_mem; right; l1_num|].
    split.
    { (* the caller's writes are apart from the tls cells and the side stack's header *)
      rewrite l1_fs_frame0. unfold reac_ctrl_identity_reply_W, fp_dj.
      cbn [fp_tls app]. rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
      clear AS_C AS_T AS_DB AS_FR DJ_C_FS DJ_T_FS DJ_DB_FS HFSalign.
      destruct (reply_args phi (fr + 256) (fr + 272) (fr + 304)); l1_dj_split; l1_num. }
    { (* the caller's data ranges are apart from the class-1 side-stack bytes *)
      clear AS_C AS_T AS_DB DJ_C_FR DJ_T_FR DJ_DB_FR DJ_C_FS DJ_T_FS DJ_DB_FS HFSalign.
      rewrite l1_fpw1. unfold reac_ctrl_identity_reply_D.
      destruct (reply_args phi (fr + 256) (fr + 272) (fr + 304)) eqn:ERA;
        [|unfold fp_dj; apply Forall_nil].
      destruct (len <? 50) eqn:EL.
      - cbn [app]. unfold fp_dj. l1_dj_split; l1_num.
      - apply Z.ltb_ge in EL.
        assert (AS_PHI : RcLay.ly_dj phi (phi + 50) LOWMEM_END HIGHMEM_BEG).
        { apply (l1_dj_pt app_mem); [lia | unfold LOWMEM_END, HIGHMEM_BEG; lia
          | intros x Hx; exact (proj1 (HPHI EL x Hx)) | exact HGAP]. }
        assert (DJ_PHI_FS : RcLay.ly_dj FS (FS + AC.FS_SIZE) phi (phi + 50)).
        { apply (l1_dj_pt (fun x => FS <= x < FS + AC.FS_SIZE));
            [unfold AC.FS_SIZE; lia | lia | intros x Hx; exact Hx |].
          intros x Hx. exact (proj2 (HPHI EL x Hx)). }
        cbn [app]. unfold fp_dj. l1_dj_split; l1_num. } }
  { (* the tls clause: any witnesses are the ones above *)
    intros DT' TS' C' T' DB' k' HT'.
    assert (HOUT : Forall (fun d => forall x, fst d <= x < snd d -> outside (@nil ivl) x)
                     (fp_tls (AC.as_tp AC.ASYMS) (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32))
                        (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0)).
    { apply Forall_forall. intros d _ x _. exact I. }
    destruct (fl_tls_same mem mem [] (AC.as_tp AC.ASYMS)
                (Z_to_bv 64 (AC.as_tp AC.ASYMS + 32)) (Z_to_bv 64 RT_TSDMAIN) Cw (Z_to_bv 64 T0) DBw 0
                DT' TS' C' T' DB' k' HTLS HT' (munch_refl (@nil ivl) mem) HOUT)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT' TS' C' T' DB' k'.
    rewrite l1_fpw1. unfold fp_dj. cbn [fp_tls app].
    rewrite ?EDTu, ?ETSu, ?ETu, ?ECw, ?EDBw.
    clear HFRFS AS_FR DJ_C_FR DJ_T_FR DJ_DB_FR HFSalign.
    l1_dj_split; l1_num. }
Qed.

End S_l1.

Section S_l2.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Ltac l2_k := unfold app_mem, Sfr, shadow_addr in *;
  unfold AC.GT, AC.FS_SIZE, FS_SIZE, ASAN_GT, HIGHMEM_BEG, LOWMEM_END, APPMEM_END, ASAN_K,
    REAC_CTRL_IDENTITY_REPLY_K, AF.SLOT_STACK in *.

(* Two word values read at the same address agree modulo 2^64. *)

Lemma l2_wm_eq : forall m a v v', word_mem rsegs m a v -> word_mem rsegs m a v' -> v mod 2 ^ 64 = v' mod 2 ^ 64.
Proof.
  intros m a v v' H H'.
  assert (P : 2 ^ 64 <> 0) by lia.
  assert (E : forall k, (k < 8)%nat -> le_byte (v mod 2 ^ 64) 8 k = le_byte (v' mod 2 ^ 64) 8 k).
  { intros k Hk. pose proof (H k Hk) as H1. pose proof (H' k Hk) as H2.
    assert (H3 : Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (le_byte v' 8 k)) by congruence.
    apply (f_equal bv_unsigned) in H3. rewrite !kb_byte_unsigned in H3. clear H1 H2. rename H3 into H2.
    unfold le_byte in H2 |- *. change (8 * Z.of_nat 8) with 64 in H2 |- *. rewrite !Z.mod_mod by exact P.
    exact H2. }
  assert (R1 : 0 <= v mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (R2 : 0 <= v' mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  rewrite (kb_le8_digits _ R1), (kb_le8_digits _ R2).
  rewrite !E by lia. reflexivity.
Qed.

Lemma l2_dj_hi : forall (W : list (Z * Z)) a n, (forall lo hi, In (lo, hi) W -> a + n <= lo) -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
  split; [left; exact (H lo hi (or_introl eq_refl))|].
  apply IH. intros lo' hi' Hin. exact (H lo' hi' (or_intror Hin)).
Qed.

(* Every range at or above GT is apart from the runtime's cells (all below GT). *)

Lemma l2_rt : forall W, (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> rt_disjoint W.
Proof.
  intros W H. unfold rt_disjoint.
  repeat split; apply l2_dj_hi; intros lo hi Hin; pose proof (H lo hi Hin) as Hl; unfold AC.GT in Hl;
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN; lia.
Qed.

(* The class-1 layout of the side stack. *)

Lemma l2_fsc : forall FS, fs_hint FS 1 = FS + 8 /\ fs_flag FS 1 0 = FS + 20480 /\ fs_M 1 = 8192 /\
  fs_frame FS 1 0 = FS + 1085440 /\ fs_frame FS 1 (fs_M 1) = FS + 2134016.
Proof.
  intros FS. unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B.
  change (Z.of_nat 1) with 1. change (2 ^ (15 - 1)) with 16384. change (2 ^ (14 - 1)) with 8192.
  repeat split; lia.
Qed.

(* The call's write list. *)

Definition l2_W (phi len fr sp : Z) (G : list byte) (FS : Z) : list (Z * Z) :=
  reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) sp G ++ fp_w [1%nat] FS ++
  [(shadow_addr (sp - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr sp)].

Lemma l2_W_eq : forall phi len fr sp G FS, l2_W phi len fr sp G FS =
  (if reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G
   then [(fr + 256, fr + 256 + 2); (fr + 272, fr + 272 + 8); (fr + 304, fr + 304 + 8)] else []) ++
  [(sp - 9072, sp); (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016)); (shadow_addr (sp - 9072), shadow_addr sp)].
Proof.
  intros phi len fr sp G FS. destruct (l2_fsc FS) as (F1 & F2 & F3 & F4 & F5).
  unfold l2_W, reac_ctrl_identity_reply_fp, fp_w, fp_w1, REAC_CTRL_IDENTITY_REPLY_K. cbn [flat_map].
  rewrite F5, F4, F1, F2, F3. rewrite <- !app_assoc. cbn [app].
  replace (FS + 8 + 8) with (FS + 16) by lia. replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

Lemma l2_W_lo : forall phi len fr sp G FS lo hi,
  AC.GT <= fr -> AC.GT <= FS -> AC.GT + 9072 <= sp ->
  In (lo, hi) (l2_W phi len fr sp G FS) -> AC.GT <= lo.
Proof.
  intros phi len fr sp G FS lo hi H1 H2 H3 Hin. rewrite l2_W_eq in Hin.
  unfold AC.GT, shadow_addr, ASAN_K in *.
  destruct (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G); cbn [app In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); contradiction.
Qed.

Lemma l2_out : forall phi len fr sp G FS x,
  ~ (fr + 256 <= x < fr + 312) -> ~ (sp - 9072 <= x < sp) -> ~ (FS + 8 <= x < FS + 16) ->
  ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (sp - 9072) <= x < shadow_addr sp) ->
  Frame.outside (l2_W phi len fr sp G FS) x.
Proof.
  intros phi len fr sp G FS x N1 N2 N3 N4 N5 N6 N7. rewrite l2_W_eq.
  destruct (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G); cbn [app Frame.outside];
    repeat split; lia.
Qed.

(* l2_out with the three reply cells excluded only when the call writes them (reply_ok). *)
Lemma l2_out2 : forall phi len fr sp G FS x,
  (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G = true ->
     ~ (fr + 256 <= x < fr + 258) /\ ~ (fr + 272 <= x < fr + 280) /\ ~ (fr + 304 <= x < fr + 312)) ->
  ~ (sp - 9072 <= x < sp) -> ~ (FS + 8 <= x < FS + 16) ->
  ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (sp - 9072) <= x < shadow_addr sp) ->
  Frame.outside (l2_W phi len fr sp G FS) x.
Proof.
  intros phi len fr sp G FS x N1 N2 N3 N4 N5 N6 N7. rewrite l2_W_eq.
  destruct (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G);
    [destruct (N1 eq_refl) as (M1 & M2 & M3)|]; cbn [app Frame.outside]; repeat split; lia.
Qed.

(* The shadow byte of an app address y is outside the call's writes when y misses the class-1 frames and the
   callee's window granule-wise (both ends of either range are 8-aligned). *)
Lemma l2_sh_out : forall phi len fr sp G FS y,
  0 <= y < APPMEM_END -> (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
  HIGHMEM_BEG + 9072 <= sp -> sp mod 16 = 0 ->
  (FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS) -> 0 <= FS -> FS mod 4096 = 0 ->
  (y < FS + 1085440 \/ FS + 2134016 <= y) -> (y < sp - 9072 \/ sp <= y) ->
  Frame.outside (l2_W phi len fr sp G FS) (shadow_addr y).
Proof.
  intros phi len fr sp G FS y Hy Hfr Hsp Hspm HFS HFS0 HFSa Hy1 Hy2.
  apply l2_out; unfold shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, AC.FS_SIZE in *;
    Z.div_mod_to_equations; lia.
Qed.

(* A byte of a carried byte list is readable. *)
Lemma l2_bytes_rd : forall m a bs x, bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a bs x (_ & _ & H) Hx.
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (H _ Hi) as Hr. rewrite Z2Nat.id in Hr by lia. replace (a + (x - a)) with x in Hr by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E.
  - exists b. exact Hr.
  - apply nth_error_None in E. lia.
Qed.

Lemma l2_rw_rd : forall m a n bs x, rw_cells rsegs m a [CB n bs] ->
  a <= x < a + Z.of_nat (length bs) -> exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a n bs x [[_ H] _] Hx. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H.
  exact (l2_bytes_rd m a bs x H Hx).
Qed.

(* The registered globals lie in the image, below GT. *)
Lemma l2_glob_lt : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & n & Hin & Hr). unfold AF.frame_AG in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; unfold AC.GT; lia|]). contradiction.
Qed.

(* A flag byte of a class other than 1 lies at or above FS + 4096 and apart from the class-1 flag bytes
   [FS + 20480, FS + 28672). *)

Lemma l2_flag_other : forall FS c j, (c <= 10)%nat -> c <> 1%nat -> 0 <= j < AC.a_fs_M c ->
  FS + 4096 <= AC.a_fs_flag FS c j /\ (AC.a_fs_flag FS c j < FS + 20480 \/ FS + 28672 <= AC.a_fs_flag FS c j).
Proof.
  intros FS c j Hc Hc1 Hj. unfold AC.a_fs_flag, AC.a_fs_M in *.
  destruct c as [|[|c]].
  - change (2 ^ (14 - Z.of_nat 0)) with 16384 in Hj. change (2 ^ (15 - Z.of_nat 0)) with 32768. lia.
  - exfalso. apply Hc1. reflexivity.
  - assert (P : 2 ^ (15 - Z.of_nat (S (S c))) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* FSREC (the side arm's class-6 frame record, push 5b) across a run that misses its three byte groups: the tp word
   (in the image, below GT), the class-6 flag byte FS + 36352 + j and the slot's last word [fr + 4088, fr + 4096)
   (the body of Tac_slot.fsrec_munch_lo, with the byte groups named instead of `below stklo`: F9's call writes
   class-1 side-stack frames, which are below stklo too). *)
Lemma f9_fsrec_keep : forall mem mem' W fr,
  FSREC fr mem -> Frame.munch W mem mem' ->
  (forall FS j, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> 0 <= j < 256 ->
     fr = FS + 6328320 + j * 4096 ->
     forall x, 0 <= x < AC.GT \/ FS + 36352 <= x < FS + 36352 + 256 \/ fr + 4088 <= x < fr + 4096 ->
     Frame.outside W x) ->
  FSREC fr mem'.
Proof.
  intros mem mem' W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) MU HW.
  assert (HB6 : ASMf.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : ASMf.fs_M 6 = 256) by reflexivity.
  assert (Hfl : ASMf.fs_flag FS 6 j = FS + 36352 + j) by (unfold ASMf.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold ASMf.fs_frame, ASMf.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  pose proof (HW FS j Htp HFSr Hj Hfrv) as HWo.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 2 ^ 64) by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by exact Hx. apply HWo. left.
      unfold AC.as_tp, AC.ASYMS, AC.GT; cbn; lia. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|]. split; [rewrite HM6; exact Hj|]. split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx. apply HWo. right; left. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx. apply HWo. right; right.
    rewrite HB6 in Hx. lia. }
Qed.

(* FRA across a write list that may also write shadow bytes: Tac_f9.f9_fr_cl, with the spill premises in the
   shape this file's callers hold them (the spill base read through s1, bounded by sp and the save area). *)

Lemma l2_run : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (forall x, 0 <= x < AC.GT -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> AC.aspZ regs <= A -> A + 344 <= 2 ^ 64 ->
     forall x, A + 336 <= x < A + 344 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> AC.aspZ regs <= A -> A + 344 <= 2 ^ 64 ->
     forall x, A + 40 <= x < A + 56 -> Frame.outside W x) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall x, g_p g <= x < g_p g + g_n g -> Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  FRA B APIf ra g fr hb regs mem' md.
Proof.
  intros g fr hb regs mem mem' md W HFRA MU WM HRO HD HSH HAH' HSTK HWhdr HWimg HWspill HWsaved HWsh
    HWsel HWwin HAG' HWINa' HREC HWin.
  pose proof HFRA as HF2.
  destruct HF2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo &
    Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA448 & Hsp4096 & HSapp &
    Hq336 & Hq64 & Hq56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWINa & Hhi1 &
    Hhi2 & Hhi3 & Hhb & Hlive).
  assert (HSb : g_S g <= 2 ^ 64).
  { destruct Hsaved as (_ & Hb & _). unfold saved_bytes in Hb. rewrite !length_app, !length_le8 in Hb.
    cbn [length Z.of_nat] in Hb. lia. }
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & _). unfold AC.GT in Hgt.
  assert (Hbase : forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 -> A = A0).
  { intros A HA HAb. unfold rg in Hr9. rewrite Hr9 in HA.
    apply (f_equal (bv_unsigned (n:=64))) in HA. rewrite !MState.unsigned_lit in HA by lia. lia. }
  apply (f9_fr_cl B APIf ra empty FF g fr hb regs regs mem mem' md W HFRA MU WM HRO HD HSH HAH' HSTK);
    try reflexivity.
  - unfold AC.GT in HWimg. exact HWimg.
  - exact HWhdr.
  - intros A HA HAb. pose proof (Hbase A HA HAb) as EA. subst A.
    apply (HWspill A0 HA); [rewrite Haspz; lia | lia].
  - exact HWsaved.
  - exact HWsh.
  - intros A HA HAb. pose proof (Hbase A HA HAb) as EA. subst A.
    apply (HWsel A0 HA); [rewrite Haspz; lia | lia].
  - exact HWwin.
  - exact HAG'.
  - exact HWINa'.
  - exact HREC.
  - exact HWin.
Qed.

(* L2: FRA and ENT across the identity_reply call (its post's munch over its window, the class-1 side-stack bytes
   and their shadow, the shadow of its window and, under reply_ok, the three reply cells), and across the lazy-page
   step md -> md'. *)

Lemma f9_fra_call : forall g fr phi len regs regs' mem mem' md md' FS G,
  FRA B APIf ra g fr [(phi, AC.a_size len)] regs mem md -> ENT APIf g [(phi, AC.a_size len)] mem md ->
  f9_PL fr regs mem ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  munch (reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) (AC.aspZ regs) G ++
         fp_w [1%nat] FS ++
         [(shadow_addr (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr (AC.aspZ regs))]) mem mem' ->
  wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  stk rsegs mem' (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs) ->
  (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G = true ->
     rw_cells rsegs mem' (fr + 256) [CB 2 (reply_addr G)] /\
     rw_cells rsegs mem' (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
     rw_cells rsegs mem' (fr + 304) [CB 8 (le8 (Z_to_bv 64 (ir_s G - 13)))]) ->
  asan_cells mem' -> shadow_rw mem' ->
  addressable mem' (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K ->
  fp [1%nat] mem' (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs)
    (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) (AC.aspZ regs))
    (reac_ctrl_identity_reply_D phi len (fr + 256) (fr + 272) (fr + 304)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr [(phi, AC.a_size len)] regs' mem' md' /\ ENT APIf g [(phi, AC.a_size len)] mem' md'.
Proof.
  intros g fr phi len regs regs' mem mem' md md' FS G HFRA HENT HPL Htp HFS MU WM HINV Hstkw Hreply HAC HSRW
    HADw HFP E2 E3 E4 E8 E9 E19 E26 Hmat.
  change (munch (l2_W phi len fr (AC.aspZ regs) G FS) mem mem') in MU.
  enough (HK : FRA B APIf ra g fr [(phi, AC.a_size len)] regs mem' md /\
               ENT APIf g [(phi, AC.a_size len)] mem' md).
  { destruct HK as (HK1 & HK2). split.
    - exact (sl_fra_move B APIf ra g fr [(phi, AC.a_size len)] regs regs' mem' md md' HK1
               E2 E3 E4 E8 E9 E19 E26 Hmat).
    - eapply ent_mat; [exact HK2 | exact Hmat]. }
  clear HAC E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & Hsp4096 & HSapp & Hspill & Hsel & Hq56 & Hloc &
    Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWINa & Hhi1 & Hhi2 & Hhi3 & Hhb & Hlive).
  clear HRT Hro Hsn Hhalt Hgimg Hr4 Hr8 Hr3 Hr19 Hr26 Hs5 Hsel Hhdr1 Hhdr2 Hsh Hsaved Herrno Hhb Hlive.
  destruct HPL as (Happ & Hgt & Hwd & HAge & HPLfs).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhi.
  destruct (lw_fs_place (APIf rc) _ _ _ FS HAH Htp HFS) as [HFSgt HFSst HFSal HFSapp].
  pose proof (lw_fs_ok (APIf rc) _ _ _ FS HAH Htp HFS) as Hok.
  destruct HFP as (DT & TS & C & T & DB & k & _ & _ & Hplace & _ & _ & Hcls & Hlo & Happw & _ & _).
  destruct Hplace as (_ & _ & _ & _ & HFSstk).
  apply Forall_inv in Hcls.
  rewrite Haspz in *.
  unfold FN_STACK, AF.SLOT_STACK in Hstklo, Hwd.
  (* layout facts *)
  assert (HspA : sp <= APPMEM_END /\ HIGHMEM_BEG + 1044480 <= sp).
  { pose proof (Happw (sp - 1) ltac:(unfold REAC_CTRL_IDENTITY_REPLY_K; lia)) as P. l2_k. lia. }
  assert (HAb : 0 < A /\ A + 344 <= 2 ^ 64).
  { destruct Hspill as (_ & Hb & _). rewrite length_le8 in Hb. split; [l2_k; lia | lia]. }
  assert (HAfr : fr + FRAME_BYTES <= A) by (apply HAge; [exact Hr9 | lia]).
  assert (Hfrlo : (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as P1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as P2. l2_k. lia. }
  assert (HFSlo : FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(l2_k; lia)) as P1.
    pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(l2_k; lia)) as P2. l2_k. lia. }
  assert (Hfrhi : FS + 6328320 <= fr /\
    ((AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= fr /\ fr + FRAME_BYTES <= APPMEM_END) \/
     (FS <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE))).
  { destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - pose proof (Hreal fr ltac:(lia)) as R1. pose proof (Hreal (fr + FRAME_BYTES - 1) ltac:(lia)) as R2.
      split; [l2_k; lia | left; split; lia].
    - destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hb & Hb1 & Hb2).
      pose proof (l2_wm_eq _ _ _ _ Hb Htp) as Heq.
      assert (HbFS : b = FS) by (l2_k; lia).
      subst b. destruct (HPLfs FS Htp HFS ltac:(lia)) as [P1 P2].
      split; [lia | right; split; lia]. }
  destruct Hfrhi as [Hfrhi Harm].
  (* the frame is at sp (real arm) or wholly below stklo (side arm) *)
  assert (Hfrw : sp <= fr \/ fr + FRAME_BYTES <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [[_ [Hspfr _]]|[_ [_ [Hfs _]]]]; [left; lia|right].
    destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (b & Hbr & Hb & Hb1 & Hb2).
    pose proof (l2_wm_eq _ _ _ _ Hb Htp) as Heq.
    assert (HbFS : b = FS) by (l2_k; lia). subst b. lia. }
  clear Hloc Happw HPLfs.
  (* the side stack's state after the call *)
  assert (Hokp : AC.a_fs_ok mem' FS).
  { destruct (f9_fs_ok_parts _ _ Hok) as (O1 & O2 & O3 & O4 & O5).
    destruct HFSstk as (_ & _ & HS).
    destruct Hcls as (_ & h1 & fl & Hh1 & Hfl & Hfll & Hflb).
    destruct (l2_fsc FS) as (F1 & F2 & F3 & F4 & F5).
    split; [|split; [|split; [|split]]].
    - intros a Ha. exact (HS a ltac:(l2_k; lia)).
    - apply (kb_word_munch rsegs mem mem' _ (FS + 88) 20 O2 MU). intros j Hj.
      split; [l2_k; lia|]. apply l2_out; l2_k; lia.
    - rewrite (mbyte_munch rsegs _ mem mem' (FS + 96) MU); [exact O3 | l2_k; lia |].
      apply l2_out; l2_k; lia.
    - intros c Hc. destruct (Nat.eq_dec c 1) as [->|Hc1].
      + exists (bv_unsigned h1). exact (bytes_at_le8_word rsegs mem' (fs_hint FS 1) h1 Hh1).
      + destruct (O4 c Hc) as [h Hh]. exists h. apply (kb_word_munch rsegs mem mem' _ _ h Hh MU).
        intros j Hj. unfold AC.a_fs_hint. split; [l2_k; lia|]. apply l2_out; l2_k; lia.
    - intros c j Hc Hj. destruct (Nat.eq_dec c 1) as [->|Hc1].
      + destruct Hfl as (_ & _ & Hfl).
        assert (Hj' : (Z.to_nat j < length fl)%nat).
        { change (AC.a_fs_M 1) with (fs_M 1) in Hj. rewrite F3 in Hfll, Hj. lia. }
        destruct (nth_error fl (Z.to_nat j)) as [b|] eqn:En; [|apply nth_error_None in En; lia].
        pose proof (Hfl (Z.to_nat j) Hj') as Hb. rewrite En, Z2Nat.id in Hb by lia.
        assert (Hin : In b fl) by exact (nth_error_In fl _ En).
        rewrite Forall_forall in Hflb.
        replace (AC.a_fs_flag FS 1 j) with (fs_flag FS 1 0 + j)
          by (rewrite F2; unfold AC.a_fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
        destruct (Hflb b Hin) as [-> | ->]; [left | right]; exact Hb.
      + pose proof (a_fs_flag_range FS c j Hc Hj) as Hr.
        pose proof (l2_flag_other FS c j Hc Hc1 Hj) as Ho.
        rewrite (mbyte_munch rsegs _ mem mem' (AC.a_fs_flag FS c j) MU); [exact (O5 c j Hc Hj) | l2_k; lia |].
        apply l2_out; l2_k; lia. }
  (* AH and stklo across the call (law: stores into the side stack and its Shadow) *)
  assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok ([(phi, AC.a_size len)] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by exact Ha.
    apply l2_out.
    - intro Hin. destruct Harm as [[R1 R2]|[S1 S2]].
      + apply Hns. right. left. l2_k; lia.
      + apply Hnf. l2_k; lia.
    - intro Hin. apply Hns. right. left. l2_k; lia.
    - intro Hin. apply Hnf. l2_k; lia.
    - intro Hin. apply Hnf. l2_k; lia.
    - intro Hin. apply Hnf. l2_k; lia.
    - intro Hin. apply Hnsh. exists (8 * (a - ASAN_K)). l2_k. split; lia.
    - intro Hin. apply Hns. right. right. right. exists (8 * (a - ASAN_K)). l2_k. split; [lia | right; left; lia]. }
  assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a).
  { intros a _ Hw. exact (WM (Z_to_bv 64 a) Hw). }
  destruct (lw_fs_store (APIf rc) ([(phi, AC.a_size len)] ++ g_H g) mem mem' md FS HAH Htp HFS Hagree Hwm Hokp)
    as [HAH' Hown Hstkeq Hstkhi].
  clear Hagree Hwm Hokp Hok Hcls HFSstk.
  (* ENT across the call: every written byte is a reply cell (frame), in the callee's window (slot window), a
     side-stack byte, the shadow of a side-stack byte, or the shadow of a window byte below sp *)
  assert (HENT' : ENT APIf g [(phi, AC.a_size len)] mem' md).
  { apply (f9_ent_W B APIf ra g fr _ regs mem mem' md _ HENT HFRA MU WM).
    - intros x Hx.
      assert (Hd : (fr + 256 <= x < fr + 312) \/ (sp - 9072 <= x < sp) \/
                   (FS + 8 <= x < FS + 16 \/ FS + 20480 <= x < FS + 28672 \/ FS + 1085440 <= x < FS + 2134016) \/
                   (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) \/
                   (shadow_addr (sp - 9072) <= x < shadow_addr sp) \/
                   (~ (fr + 256 <= x < fr + 312) /\ ~ (sp - 9072 <= x < sp) /\ ~ (FS + 8 <= x < FS + 16) /\
                    ~ (FS + 20480 <= x < FS + 28672) /\ ~ (FS + 1085440 <= x < FS + 2134016) /\
                    ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) /\
                    ~ (shadow_addr (sp - 9072) <= x < shadow_addr sp))) by lia.
      destruct Hd as [Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]].
      + right; right; left. lia.
      + right; left. unfold AF.SLOT_STACK in *. lia.
      + right; right; right; right; right; left. exists FS. split; [exact HFS|]. split; [exact Htp|].
        unfold AC.FS_SIZE. lia.
      + right; right; right; right; right; right. exists (8 * (x - ASAN_K)). split.
        * exists FS. split; [exact HFS|]. split; [exact Htp|].
          unfold shadow_addr, ASAN_K, AC.FS_SIZE in *. Z.div_mod_to_equations. lia.
        * unfold shadow_addr. Z.div_mod_to_equations. lia.
      + right; right; right; right; left. exists (8 * (x - ASAN_K)). split.
        * rewrite Haspz. unfold shadow_addr, ASAN_K, AF.SLOT_STACK in *. Z.div_mod_to_equations. lia.
        * unfold shadow_addr. Z.div_mod_to_equations. lia.
      + left. destruct Hc as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
        exact (l2_out phi len fr sp G FS x N1 N2 N3 N4 N5 N6 N7).
    - exact Hstkeq.
    - exact Hstkhi.
    - intros a _ Ho. exact (proj2 (Hown a) Ho). }
  split; [|exact HENT'].
  apply (l2_run g fr [(phi, AC.a_size len)] regs mem mem' md (l2_W phi len fr sp G FS) HFRA MU WM HINV).
  - apply l2_rt. intros lo hi Hin.
    apply (l2_W_lo phi len fr sp G FS lo hi); [exact Hgt | l2_k; lia | l2_k; lia | exact Hin].
  - intros a Ha. destruct (HSRW a Ha) as (_ & b & Hb). exists b. exact Hb.
  - exact HAH'.
  - exact Hstkeq.
  - intros x Hx. apply l2_out; l2_k; lia.
  - intros x Hx. apply l2_out; l2_k; lia.
  - intros A' HA' Hle Hb x Hx. rewrite Haspz in Hle.
    assert (fr + FRAME_BYTES <= A') by (apply HAge; [exact HA' | l2_k; lia]).
    apply l2_out; l2_k; lia.
  - intros x Hx. apply l2_out; l2_k; lia.
  - intros x Hx. apply l2_out; l2_k; lia.
  - intros A' HA' Hle Hb x Hx. rewrite Haspz in Hle.
    assert (fr + FRAME_BYTES <= A') by (apply HAge; [exact HA' | l2_k; lia]).
    apply l2_out; l2_k; lia.
  - (* the entry-anchored window [S - SLOT_STACK, S) on mem': below the callee's window it is not written (the
       frame is at sp or below stklo), the callee's window is the callee's stk post, and above sp only the reply
       cells are written, which the post gives as readable cells *)
    apply (fl_stk _ mem mem' (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU WM).
    intros x Hx.
    destruct (Z_lt_le_dec x (sp - REAC_CTRL_IDENTITY_REPLY_K)) as [Hl|Hl];
      [|destruct (Z_lt_le_dec x sp) as [Hl2|Hl2]].
    + left. apply l2_out2; [intros _; l2_k; lia | l2_k; lia ..].
    + right. destruct Hstkw as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))).
    + destruct (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G) eqn:Hok.
      * destruct (Hreply eq_refl) as (R1 & R2 & R3).
        assert (Hdec : (fr + 256 <= x < fr + 258 \/ fr + 272 <= x < fr + 280 \/ fr + 304 <= x < fr + 312) \/
                       (~ (fr + 256 <= x < fr + 258) /\ ~ (fr + 272 <= x < fr + 280) /\
                        ~ (fr + 304 <= x < fr + 312))) by lia.
        destruct Hdec as [[Hc|[Hc|Hc]]|Hc].
        -- right. apply (l2_rw_rd mem' (fr + 256) 2 (reply_addr G) x R1). cbn [length reply_addr]. lia.
        -- right. apply (l2_rw_rd mem' (fr + 272) 8 _ x R2). rewrite length_le8. cbn. lia.
        -- right. apply (l2_rw_rd mem' (fr + 304) 8 _ x R3). rewrite length_le8. cbn. lia.
        -- left. apply l2_out2; [intros _; exact Hc | l2_k; lia ..].
      * left. apply l2_out2; [intros HC; congruence | l2_k; lia ..].
  - (* the registered globals: their shadow bytes are below the class-1 frames' and the window's *)
    intros a Hin. destruct (l2_glob_lt a Hin) as (Ha0 & HaGT).
    apply (l5_addr_keep mem mem' _ a 1 (HAG a Hin) MU). intros i Hi.
    apply (l2_sh_out phi len fr sp G FS (a + i)); unfold AC.GT in *; l2_k; lia.
  - (* the window outside the frame: below / above the callee's window its shadow is not written; the callee's
       window is addressable by the callee's post *)
    intros a Ha Hnf.
    destruct (Z_lt_le_dec a (sp - REAC_CTRL_IDENTITY_REPLY_K)) as [Hl|Hl];
      [|destruct (Z_lt_le_dec a sp) as [Hl2|Hl2]].
    + apply (l5_addr_keep mem mem' _ a 1 (HWINa a Ha Hnf) MU). intros i Hi.
      apply (l2_sh_out phi len fr sp G FS (a + i)); l2_k; lia.
    + replace a with ((sp - REAC_CTRL_IDENTITY_REPLY_K) + (a - (sp - REAC_CTRL_IDENTITY_REPLY_K))) by lia.
      apply (addressable_sub mem' _ _ _ 1 HADw); unfold REAC_CTRL_IDENTITY_REPLY_K in *; lia.
    + apply (l5_addr_keep mem mem' _ a 1 (HWINa a Ha Hnf) MU). intros i Hi.
      apply (l2_sh_out phi len fr sp G FS (a + i)); l2_k; lia.
  - (* FSREC: its tp word is in the image, its class-6 flag byte FS + 36352 + j lies between the class-1 flags and
       the class-1 frames, and the slot's last word fr + 4088 is in the side stack above the class-1 frames and
       below stklo; the call writes none of them *)
    intros Hrec. apply (f9_fsrec_keep mem mem' _ fr Hrec MU).
    intros FS6 j6 Htp6 HFS6 Hj6 Hfr6 x Hx.
    assert (E6 : FS6 = FS) by (pose proof (l2_wm_eq _ _ _ _ Htp6 Htp) as Heq; l2_k; lia).
    subst FS6. destruct Hx as [Hx|[Hx|Hx]]; apply l2_out; l2_k; lia.
  - (* the input block: a live block of g_H g, so app memory below stklo, outside the frame and outside the side
       stack (a_laws_blocks); so it and its shadow bytes miss the call's writes *)
    intros x Hx.
    destruct (fra_in_apart B APIf ra g fr _ regs mem md HFRA x Hx) as (Hxa & Hxlo & Hxfr & _).
    assert (Hn0 : 0 < g_n g) by lia.
    destruct (proj2 (fra_in B APIf ra g fr _ regs mem md HFRA) Hn0) as (Hin & _).
    destruct (lw_blocks (APIf rc) ([(phi, AC.a_size len)] ++ g_H g) mem md (g_p g) (g_n g) HAH
                (in_or_app _ _ _ (or_intror Hin))) as [_ _ _ _ Hblk].
    destruct (Hblk x Hx) as (_ & _ & _ & _ & Hnfs).
    assert (HnFS : ~ (FS <= x < FS + AC.FS_SIZE)).
    { intros HxF. apply Hnfs. exists FS. split; [exact HFS|]. split; [exact Htp | exact HxF]. }
    split.
    + apply l2_out; l2_k; lia.
    + apply (l2_sh_out phi len fr sp G FS x); l2_k; lia.
Qed.

End S_l2.

Section S_l3.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Lemma l3_sh : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof.
  intros fr k. unfold Sfr, shadow_addr.
  replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

(* An address is outside f9_W9 fr, or one of its three shadow bytes, or in the frame cells [fr + 256, fr + 312). *)

Lemma l3_W_cases : forall fr x,
  outside (f9_W9 fr) x \/ x = Sfr fr + 32 \/ x = Sfr fr + 34 \/ x = Sfr fr + 38 \/ (fr + 256 <= x < fr + 312).
Proof.
  intros fr x. unfold f9_W9. cbn [outside].
  destruct (Z.eq_dec x (Sfr fr + 32)) as [E|N1]; [right; left; exact E|].
  destruct (Z.eq_dec x (Sfr fr + 34)) as [E|N2]; [right; right; left; exact E|].
  destruct (Z.eq_dec x (Sfr fr + 38)) as [E|N3]; [right; right; right; left; exact E|].
  destruct (Z_le_gt_dec (fr + 256) x); [destruct (Z_lt_ge_dec x (fr + 312))|].
  - right; right; right; right; lia.
  - left. repeat split; try exact I; lia.
  - left. repeat split; try exact I; lia.
Qed.

(* word_mem only sees its value mod 2^64. *)

Lemma l3_wm_mod : forall mem a b, word_mem rsegs mem a b -> word_mem rsegs mem a (b mod 2 ^ 64).
Proof.
  intros mem a b H k Hk. rewrite (H k Hk). unfold le_byte. change (8 * Z.of_nat 8) with 64.
  rewrite Z.mod_mod by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

(* Every FakeStack metadata cell is at or above FS. *)

Lemma l3_fs_meta_lo : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* AH and stklo across F9's six stores: real arm by a_laws_store (frame bytes real stack, frame shadow bytes the
   shadow of real-stack bytes); side arm by a_fs_ok_store_AH (frame bytes in FS above the metadata, shadow bytes the
   shadow of FS bytes and not app, so not metadata). *)

Lemma l3_ah : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md -> f9_PL fr regs mem ->
  munch (f9_W9 fr) mem mem' -> wmono rsegs mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> exists b, mbyte rsegs mem' q = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros g fr hb regs mem mem' md HFRA HPL MU WM HPRES.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & Hsp4096 & HSapp & Hspill & Hsel & Hq56 & Hloc &
    Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWINa & Hhi1 & Hhi2 & Hhi3 & Hhb & Hlive).
  destruct HPL as (Happ & Hgt & _ & _ & HFSb).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (Hw2 : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a _ Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hspb : sp <= 2 ^ 64) by (destruct Hwin as (_ & Hb & _); lia).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  unfold AC.GT in Hgt.
  destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
  - (* real arm: every written address is a_store_ok *)
    assert (P1 : forall a, 0 <= a < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
              mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hn. apply MU. rewrite MState.unsigned_lit by exact Ha.
      destruct (l3_W_cases fr a) as [Ho | [E | [E | [E | Hb]]]]; [exact Ho | exfalso ..];
        apply Hn; unfold AC.a_store_ok.
      - right; right; right. exists (fr + 8 * 32).
        split; [rewrite l3_sh; exact E | right; left; apply Hreal; lia].
      - right; right; right. exists (fr + 8 * 34).
        split; [rewrite l3_sh; exact E | right; left; apply Hreal; lia].
      - right; right; right. exists (fr + 8 * 38).
        split; [rewrite l3_sh; exact E | right; left; apply Hreal; lia].
      - right; left; apply Hreal; lia. }
    destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH P1 Hw2) as [S1 S2 S3 S4].
    exact (conj S1 (conj S2 (conj S3 S4))).
  - (* side arm: the FS word at tp, the frame inside FS above the class-6 frames *)
    destruct (Hfs fr ltac:(lia)) as (b & _ & Hwb & Hblo & Hbhi).
    assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) (b mod 2 ^ 64)) by exact (l3_wm_mod mem _ b Hwb).
    assert (Hm0 : 0 <= b mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    pose proof (lw_fs_place (APIf rc) _ _ _ (b mod 2 ^ 64) HAH Hwm Hm0) as [_ Hstkm _ _].
    assert (Hb0 : 0 <= b).
    { destruct (Z_lt_le_dec b 0) as [Hn|Hp]; [exfalso|exact Hp].
      assert (E : b mod 2 ^ 64 = b + 2 ^ 64).
      { rewrite <- (Z.mod_add b 1 (2 ^ 64)) by lia. rewrite Z.mul_1_l. apply Z.mod_small.
        unfold AC.FS_SIZE in *. lia. }
      rewrite E in Hstkm. unfold AC.FS_SIZE, AF.SLOT_STACK in *. lia. }
    assert (Hbr : 0 <= b < 2 ^ 64) by (unfold APPMEM_END in Hub; lia).
    destruct (HFSb b Hwb Hbr ltac:(lia)) as (Hlo36 & Hhi36).
    pose proof (lw_fs_place (APIf rc) _ _ _ b HAH Hwb Hbr) as [_ Hstkb _ Happfs].
    assert (Hsz : b + AC.FS_SIZE <= 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
    assert (Hmeta : forall q, fs_meta b q -> outside (f9_W9 fr) q).
    { intros q Hq. pose proof (fs_meta_below b q Hq) as Hq1. pose proof (l3_fs_meta_lo b q Hq) as Hq0.
      assert (Hqa : app_mem q) by (apply Happfs; unfold AC.FS_SIZE; lia).
      destruct (l3_W_cases fr q) as [Ho | [E | [E | [E | Hb]]]]; [exact Ho | exfalso ..].
      - apply (AsanRTFacts.app_not_shadow q Hqa). rewrite E, <- (l3_sh fr 32).
        apply AsanRTFacts.shadow_of_app, Happ. lia.
      - apply (AsanRTFacts.app_not_shadow q Hqa). rewrite E, <- (l3_sh fr 34).
        apply AsanRTFacts.shadow_of_app, Happ. lia.
      - apply (AsanRTFacts.app_not_shadow q Hqa). rewrite E, <- (l3_sh fr 38).
        apply AsanRTFacts.shadow_of_app, Happ. lia.
      - lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (b <= q < b + AC.FS_SIZE) ->
              ~ (exists c, b <= c < b + AC.FS_SIZE /\ q = shadow_addr c) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq _ Hnr Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
      destruct (l3_W_cases fr q) as [Ho | [E | [E | [E | Hb]]]]; [exact Ho | exfalso ..].
      - apply Hnsh. exists (fr + 8 * 32). split; [unfold AC.FS_SIZE in *; lia | rewrite l3_sh; exact E].
      - apply Hnsh. exists (fr + 8 * 34). split; [unfold AC.FS_SIZE in *; lia | rewrite l3_sh; exact E].
      - apply Hnsh. exists (fr + 8 * 38). split; [unfold AC.FS_SIZE in *; lia | rewrite l3_sh; exact E].
      - apply Hnr. unfold AC.FS_SIZE in *; lia. }
    exact (a_fs_ok_store_AH AC.ASYMS _ _ _ _ (f9_W9 fr) (hb ++ g_H g) mem mem' md b LAWS HAH Hwb Hbr Hsz MU
      Hw2 HPRES Hmeta Hagree).
Qed.

(* L3: FRA across F9's six stores. *)

Lemma f9_fra_st : forall g fr hb regs regs' mem mem' md,
  FRA B APIf ra g fr hb regs mem md -> f9_PL fr regs mem ->
  munch (f9_W9 fr) mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> exists b, mbyte rsegs mem' q = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md HFRA HPL MU WM HINV HPRES HSHN E2 E3 E4 E8 E9 E19 E26.
  destruct (l3_ah g fr hb regs mem mem' md HFRA HPL MU WM HPRES) as (HAH' & _ & HSTK & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & Hsp4096 & HSapp & Hspill & Hsel & Hq56 & Hloc &
    Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWINa & Hhi1 & Hhi2 & Hhi3 & Hhb & Hlive).
  pose proof HPL as (Happ & Hgt & Hwinpl & HAb & _).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhi.
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  assert (Hgt' : 6283264 <= fr) by (unfold AC.GT in Hgt; lia).
  pose proof (Z.div_mod fr 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound fr 8 ltac:(lia)) as Hmb.
  assert (HSfr : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { unfold Sfr, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG. unfold APPMEM_END in Hub. lia. }
  assert (HSb : g_S g <= 2 ^ 64).
  { destruct Hsaved as (_ & Hb & _). unfold saved_bytes in Hb. rewrite !length_app, !length_le8 in Hb.
    cbn [length Z.of_nat] in Hb. lia. }
  assert (Hspb : 0 <= sp - AF.SLOT_STACK /\ sp <= 2 ^ 64) by (unfold AF.SLOT_STACK, HIGHMEM_BEG in *; lia).
  assert (HAr : 0 <= A < 2 ^ 64) by (unfold AF.SLOT_STACK in Hspb; lia).
  assert (HAfr : fr + FRAME_BYTES <= A) by (apply HAb; [exact Hr9 | exact HAr]).
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hout : forall x, (x < fr + 256 \/ fr + 312 <= x) -> (x < Sfr fr + 32 \/ Sfr fr + 39 <= x) ->
                   outside (f9_W9 fr) x).
  { intros x Hx1 Hx2. unfold f9_W9. cbn [outside]. repeat split; try exact I; lia. }
  assert (HA'eq : forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' + 32 <= x < A' + 448 ->
                    outside (f9_W9 fr) x).
  { intros A' HA' x Hx.
    destruct (Z_lt_le_dec A' 0) as [Hn|Hp]; [apply Hout; [left | left]; unfold LOWMEM_END in HSfr; lia|].
    destruct (Z_lt_le_dec A' (2 ^ 64)) as [Hl|Hg];
      [|apply Hout; [right | right]; unfold HIGHMEM_BEG in HSfr; unfold APPMEM_END in Hub; lia].
    assert (EA : A' = A).
    { assert (Eb : Z_to_bv 64 A' = Z_to_bv 64 A) by (rewrite <- HA'; exact Hr9).
      apply (f_equal bv_unsigned) in Eb. rewrite !MState.unsigned_lit in Eb by lia. exact Eb. }
    subst A'. apply Hout; [right | right]; lia. }
  apply (sl_fr_meta B APIf ra empty FF g fr hb regs regs' mem mem' md (f9_W9 fr) HFRA MU WM).
  - exact HINV.
  - unfold rt_disjoint, f9_W9. cbn [disjoint_from].
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
    unfold LOWMEM_END in HSfr.
    repeat split; first [left; lia | exact I].
  - exact HAH'.
  - exact HSTK.
  - exact Happ.
  - exact Hgt.
  - exact HSHN.
  - intros x _ Hnb Hns.
    destruct (l3_W_cases fr x) as [Ho | [E | [E | [E | Hb]]]]; [exact Ho | exfalso; lia ..].
  - intros A' HA' _ x Hx. apply (HA'eq A' HA'). lia.
  - intros x Hx. apply Hout; [right | right]; lia.
  - intros A' HA' _ x Hx. apply (HA'eq A' HA'). lia.
  - (* the window: a byte outside the six stores is kept; a stored frame cell is a defined memory byte *)
    intros x Hx. destruct (l3_W_cases fr x) as [Ho | Hin]; [left; exact Ho | right].
    apply f9_raw; [unfold AC.GT, AF.SLOT_STACK, HIGHMEM_BEG in *; lia|].
    destruct Hwin as (_ & _ & Hw). destruct (Hw x Hx) as (_ & b & Hb).
    exact (HPRES x ltac:(unfold AF.SLOT_STACK, HIGHMEM_BEG in *; lia) (ex_intro _ b Hb)).
  - (* the registered globals: their shadow bytes are below the frame's shadow *)
    intros a Hin. destruct (l2_glob_lt a Hin) as (Ha0 & HaGT).
    pose proof (Happ fr ltac:(lia)) as Pa1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Pa2.
    apply (l5_addr_keep mem mem' _ a 1 (HAG a Hin) MU). intros i Hi.
    apply Hout; unfold app_mem, Sfr, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, AC.GT in *;
      Z.div_mod_to_equations; lia.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.

End S_l3.

Lemma l9_rg_eq : forall regs (r : bv 5) x y, rg regs r x -> rg regs r y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  x = y.
Proof.
  intros regs r x y Hx Hy Bx By. unfold rg in *. rewrite Hx in Hy.
  apply (f_equal (bv_unsigned (n:=64))) in Hy. rewrite !MState.unsigned_lit in Hy by lia. exact Hy.
Qed.

(* A kind-name address is QMARK or a table entry. *)

Lemma l9_kn_in : forall x, In (kind_name_addr x) (QMARK :: kind_name_addrs).
Proof.
  intros x. unfold kind_name_addr. destruct (x <=? 13).
  - destruct (nth_in_or_default (Z.to_nat x) kind_name_addrs QMARK) as [H|H];
      [right; exact H | rewrite H; left; reflexivity].
  - left. reflexivity.
Qed.

(* Each of them is below 2^47 and starts a registered global (AF.frame_AG). *)

Lemma l9_kn_glob : forall a, In a (QMARK :: kind_name_addrs) -> 0 <= a < 2 ^ 47 /\ in_globals AF.frame_AG a.
Proof.
  intros a Hin. unfold QMARK, kind_name_addrs in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E | Hin];
    [split; [lia | exists a; eexists; split;
       [rewrite <- E; unfold AF.frame_AG; cbn [In]; repeat (first [left; reflexivity | right]) | lia]] |]).
  destruct Hin.
Qed.

(* The first name byte of a kind 0..13 is not '?' (63). *)

Local Ltac l9_nm := eexists; split; [reflexivity | let Hc := fresh "Hc" in intro Hc; vm_compute in Hc; discriminate Hc].

Lemma l9_name0 : forall v, 0 <= v <= 13 ->
  exists c, firstn 1 (skipn 0 (cstr_bytes (kind_name v))) = [c] /\ bv_unsigned c <> 63.
Proof.
  intros v Hv.
  assert (H : v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7 \/ v = 8 \/ v = 9 \/ v = 10 \/
              v = 11 \/ v = 12 \/ v = 13) by lia.
  repeat (destruct H as [-> | H]; [l9_nm |]). subst v. l9_nm.
Qed.

Section S_l9.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The official entry cut Inv_B82180_at (lib/B/Prog/SlotInv.v) is f9_E and f9_X: f9_E is its body up to the
   kind-name table, then the existential part; f9_X its six adopt-6 / adopt-7 conjuncts, which sit between the two
   in the cut (f9_E_split). LK carries the frame-loop spill bundle FLI, FM (v1.9) the fill flag [A+184], s8 = k,
   s6 = 1, s9 = sum_ok and the block [A+312], and FSj the local `first`. *)

Definition f9_E (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
  rg regs 18 phi /\ rg regs 20 (t_len (g_in g) j) /\ FM g j phi fr regs m /\ FSj g fr j regs m /\
  bytes_at rsegs m KIND_NAME kind_name_bytes /\ addressable m KIND_NAME 112 /\
  exists A v, FLVsp A fr regs m /\
    rg regs 10 (kind_name_addr v) /\ rg regs 24 v /\ 0 <= v < 2 ^ 31 /\
    q64 m (A + 280) (fr + 176) /\ u32 m (fr + 176) v /\
    bytes_at rsegs m (kind_name_addr v) (cstr_bytes (kind_name v)).

(* [A+248] = 1 - sum_ok (v1.9 0x82148, FS9), the 50 record bytes at Phi for a long frame, the per-turn bundle FTURN,
   the records REC0, the parse struct FPS and the [A+272] spill F272. The run keeps all six; F10's entry cut reads
   them. *)
Definition f9_X (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 248 (1 - b2z (t_sum_ok (g_in g) j)) /\ (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
  FTURN g j phi regs m /\ REC0 g fr j m /\ FPS g fr j m /\ F272 g j regs m.

Lemma f9_E_split : forall g j phi fr regs m,
  (g_n g < 2 ^ 26 /\ (j <= 255)%nat /\ HB m phi (flen g j) /\ LK g fr j regs m /\
   rg regs 18 phi /\ rg regs 20 (t_len (g_in g) j) /\ FM g j phi fr regs m /\ FSj g fr j regs m /\
   bytes_at rsegs m KIND_NAME kind_name_bytes /\ addressable m KIND_NAME 112 /\
   spill regs m 248 (1 - b2z (t_sum_ok (g_in g) j)) /\ (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
   FTURN g j phi regs m /\ REC0 g fr j m /\ FPS g fr j m /\ F272 g j regs m /\
   exists A v, FLVsp A fr regs m /\
     rg regs 10 (kind_name_addr v) /\ rg regs 24 v /\ 0 <= v < 2 ^ 31 /\
     q64 m (A + 280) (fr + 176) /\ u32 m (fr + 176) v /\
     bytes_at rsegs m (kind_name_addr v) (cstr_bytes (kind_name v))) ->
  f9_E g j phi fr regs m /\ f9_X g j phi fr regs m.
Proof.
  intros g j phi fr regs m (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & X1 & X2 & X3 & X4 & X5 & X6 & EX).
  split.
  - exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E6 (conj E7 (conj E8 (conj E9 (conj E10 EX)))))))))).
  - exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 X6))))).
Qed.

(* ---- What FRA alone gives the run (the proofs of lib/B/Prog/Seg/F8.v's f8_fra_fs6 / f8_fra_dtls /
   f8_fra_phi_nfs, with the side-stack base read off the runtime cells, AsanRTInv.RT_fs_cells). ---- *)

(* On the side-stack arm the frame is the class-6 slot of the side stack whose base is the word at tp, so it lies
   in the class-6 area (above the metadata and classes 0 .. 5) and ends inside it. The real arm (sp = fr) cannot
   satisfy the premise: there the frame is at or above stklo, and the side stack ends at or below stklo. *)
Lemma f9_fra_fs6 : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  forall FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> FS <= fr < FS + AC.FS_SIZE ->
    FS + 36864 + 6 * 2 ^ 20 <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE.
Proof.
  intros g fr hb regs mem md HFRA FS Hw HFSr Hin.
  pose proof HFRA as (A & sp & s5 & HF).
  assert (HAH : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md) by tauto.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (lw_fs_place (APIf rc) _ mem md FS HAH Hw HFSr) as [_ Hend _ _].
  assert (Hwin : stk rsegs mem (g_S g - AF.SLOT_STACK) (g_S g)) by tauto.
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (Hstklo : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= g_S g - AF.SLOT_STACK) by tauto.
  assert (Harm : (sp = fr /\
                    (forall a, fr <= a < fr + FRAME_BYTES ->
                       AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END)) \/
                 FSREC fr mem) by tauto.
  destruct Harm as [(Hsfr & Hreal) | Hrec].
  - exfalso. destruct (Hreal fr ltac:(lia)) as (Hlo & _). lia.
  - destruct Hrec as (FS' & jj & Htp' & HFS'r & Hjj & Hfr' & _ & _).
    assert (EFS : FS' = FS).
    { pose proof (l2_wm_eq mem _ FS' FS Htp' Hw) as E.
      rewrite (Z.mod_small FS') in E by lia. rewrite (Z.mod_small FS) in E by lia. exact E. }
    subst FS'. change (ASMf.fs_M 6) with 256 in Hjj.
    assert (Hfrv : fr = FS + 36864 + 6 * 2 ^ 20 + jj * 4096)
      by (rewrite Hfr'; unfold ASMf.fs_frame, ASMf.fs_B; cbn; lia).
    lia.
Qed.

(* The thread's DTLS word at tp + 8 (a_laws_fs_state's DB), with room for its 8 bytes at DB + 24: those bytes are
   app memory, hence below APPMEM_END < 2^64. *)
Lemma f9_fra_dtls : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists DB, word_mem rsegs mem (AC.as_tp AC.ASYMS + 8) DB /\ 0 <= DB /\ DB + 32 <= 2 ^ 64.
Proof.
  intros g fr hb regs mem md HFRA.
  pose proof HFRA as (A & sp & s5 & HF).
  assert (HAH : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md) by tauto.
  assert (HRT : AsanRTInv.RT sp mem md) by tauto.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (AsanRTInv.RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FSw & HFSb & _) & _).
  pose proof (bytes_at_le8_word rsegs mem RT_TP FSw HFSb) as HFSwm.
  pose proof (l1_word_range FSw) as HFS64.
  destruct (fsf_fs_state_fields (APIf rc) _ _ _ _ HAH HFSwm HFS64) as (DB & [_ HDBw HDBr _ _ HDBp _]).
  exists DB. split; [exact HDBw|]. split; [lia|].
  destruct (HDBp (DB + 31) ltac:(lia)) as (Happ & _).
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happ. lia.
Qed.

(* The record buffer Phi is a live block of the cut's heap, and no byte of a live block is in the side stack
   (a_laws_blocks). The block's size is AC.a_size (flen g j) >= 1, so Phi itself is one of its bytes. *)
Lemma f9_fra_phi_nfs : forall g fr hb regs mem md phi n,
  FRA B APIf ra g fr hb regs mem md -> In (phi, AC.a_size n) (hb ++ g_H g) ->
  ~ AC.a_in_fs AC.ASYMS mem phi.
Proof.
  intros g fr hb regs mem md phi n HFRA Hin.
  pose proof HFRA as (A & sp & s5 & HF).
  assert (HAH : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md) by tauto.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (lw_blocks (APIf rc) _ mem md phi (AC.a_size n) HAH Hin) as [_ _ _ _ Hall].
  destruct (Hall phi ltac:(unfold AC.a_size; lia)) as (_ & _ & _ & _ & Hnfs). exact Hnfs.
Qed.

(* The working bundle of the proof: what FRA, LK / FLI, FM, FSj and f9_X give (f9_GAP_of). *)

Definition f9_GAP (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (* G1 (v1.9): [A+288] = pa = fr+256, [A+176] = fr+2688, [A+200] = fr+336, [A+208] = fragb fr (all in FLI),
     [A+248] = 1 - sum_ok (f9_X), [A+312] = blk and [A+184] = the fill flag (both in FM) *)
  (forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 ->
     q64 m (A + 288) (fr + 256) /\ q64 m (A + 176) (fr + 2688) /\ q64 m (A + 200) (fr + 336) /\
     q64 m (A + 208) (fr + 2768) /\ q64 m (A + 248) (1 - b2z (t_sum_ok (g_in g) j)) /\
     q64 m (A + 312) (if t_big (g_in g) j then phi + 18 else 0) /\
     q64 m (A + 184) (b2z (t_tfill (g_in g) j))) /\
  (* G2 (v1.9, FM): s9 = sum_ok, s8 = k and s6 = 1 *)
  rg regs 25 (b2z (t_sum_ok (g_in g) j)) /\ rg regs 24 (t_k (g_in g) j) /\ rg regs 22 1 /\
  (* G3: the 50 record bytes at phi *)
  (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) /\
  (* G4: the registered globals' bytes are addressable (FRA) *)
  (forall a, in_globals AF.frame_AG a -> addressable m a 1) /\
  (* G5 *)
  f9_PL fr regs m /\
  (* G6: the frame cells the stores 0x821c4 / 0x821d0 / 0x821dc write *)
  wr_at rsegs m (fr + 256) 2 /\ wr_at rsegs m (fr + 272) 8 /\ wr_at rsegs m (fr + 304) 8 /\
  (* G7: the callee's stack window is addressable (FRA's window conjunct with fra_frame) *)
  (forall a, AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K <= a < AC.aspZ regs -> addressable m a 1) /\
  (* G8: the thread's DTLS word at tp+8 is a 64-bit value with room for its 8 bytes at +24 *)
  (exists DB, word_mem rsegs m (AC.as_tp AC.ASYMS + 8) DB /\ 0 <= DB /\ DB + 32 <= 2 ^ 64).

(* Every name of f9_GAP comes from FRA (fra_app / fra_frame / the window and globals conjuncts, f9_fra_dtls), from
   the entry cut's LK / FLI / FM or from f9_X. *)

Lemma f9_GAP_of : forall g j phi fr regs mem md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  f9_E g j phi fr regs mem -> f9_X g j phi fr regs mem ->
  f9_GAP g j phi fr regs mem.
Proof.
  intros g j phi fr regs mem md HFRA HE HX.
  destruct (fra_app B APIf ra g fr _ regs mem md HFRA) as (Hgt & Happ).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hdj & HAfr & Hfs36 & Hwr).
  destruct HE as (_ & _ & _ & (_ & _ & _ & HFLI) & _ & _ & HFM & _).
  destruct HX as (H248 & Hrec & _).
  pose proof (f9_fra_fs6 g fr _ regs mem md HFRA) as Hfs6.
  pose proof (f9_fra_dtls g fr _ regs mem md HFRA) as HDB.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo &
    Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA448 & Hsp4096 & HSap &
    Hq336 & Hq64 & Hq56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWINa & Hstkhi1 &
    Hstkhi2 & Hstkhi3 & Hhb & Hlive).
  assert (HSb : g_S g <= 2 ^ 64).
  { destruct Hsaved as (_ & Hb & _). unfold saved_bytes in Hb. rewrite !length_app, !length_le8 in Hb.
    cbn [length Z.of_nat] in Hb. lia. }
  assert (HA0b : 0 <= A0 /\ A0 + 448 <= 2 ^ 64) by (unfold AC.GT in Hgt; lia).
  assert (Hbase : forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 -> A = A0).
  { intros A HA HAb. unfold rg in HA. rewrite Hr9 in HA.
    apply (f_equal (bv_unsigned (n:=64))) in HA. rewrite !MState.unsigned_lit in HA by lia. lia. }
  destruct HFLI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp176 & _ & Hp200 & _ & Hp208 & _ & _ & _ &
    Hp288 & _).
  destruct HFM as (Hm184 & Hm24 & Hm22 & Hm25 & Hp312).
  split.
  { intros A HA HAb. pose proof (Hbase A HA HAb) as EA.
    split; [exact (f9_sp regs mem A 288 _ HA ltac:(lia) ltac:(lia) ltac:(lia) Hp288)|].
    split; [exact (f9_sp regs mem A 176 _ HA ltac:(lia) ltac:(lia) ltac:(lia) Hp176)|].
    split; [exact (f9_sp regs mem A 200 _ HA ltac:(lia) ltac:(lia) ltac:(lia) Hp200)|].
    split; [exact (f9_sp regs mem A 208 _ HA ltac:(lia) ltac:(lia) ltac:(lia) Hp208)|].
    split; [exact (f9_sp regs mem A 248 _ HA ltac:(lia) ltac:(lia) ltac:(lia) H248)|].
    split; [exact (f9_sp regs mem A 312 _ HA ltac:(lia) ltac:(lia) ltac:(lia) Hp312)|].
    exact (f9_sp regs mem A 184 _ HA ltac:(lia) ltac:(lia) ltac:(lia) Hm184). }
  split; [exact Hm25|].
  split; [exact Hm24|].
  split; [exact Hm22|].
  split; [exact Hrec|].
  split; [exact HAG|].
  split.
  { split; [exact Happ|]. split; [exact Hgt|].
    split; [apply Hdj; unfold FN_STACK, AF.SLOT_STACK; lia|].
    split.
    - intros A HA HAb. pose proof (Hbase A HA HAb) as EA.
      assert (E : bv_unsigned (getr regs 9) = A0)
        by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; lia).
      rewrite E in HAfr. lia.
    - exact Hfs6. }
  pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Pfr. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Pfr.
  pose proof Hgt as Hgt0. unfold AC.GT in Hgt0.
  split; [split; [lia|]; split; [lia|]; intros i Hi; exact (Hwr (fr + 256 + i) ltac:(lia))|].
  split; [split; [lia|]; split; [lia|]; intros i Hi; exact (Hwr (fr + 272 + i) ltac:(lia))|].
  split; [split; [lia|]; split; [lia|]; intros i Hi; exact (Hwr (fr + 304 + i) ltac:(lia))|].
  split.
  { intros a Ha. unfold AC.aspZ in Ha. rewrite Hr2 in Ha.
    rewrite MState.unsigned_lit in Ha by lia.
    apply HWINa; [unfold REAC_CTRL_IDENTITY_REPLY_K, AF.SLOT_STACK in *; lia|].
    intro HC.
    destruct (Hdj REAC_CTRL_IDENTITY_REPLY_K
                ltac:(unfold FN_STACK, AF.SLOT_STACK, REAC_CTRL_IDENTITY_REPLY_K; lia)) as [Hd|Hd];
      unfold AC.aspZ in Hd; rewrite Hr2, MState.unsigned_lit in Hd by lia; lia. }
  exact HDB.
Qed.

(* The entry facts of segment F9. NOTE: the premise 0 <= A < 2 ^ 64 is added to the requested statement: rg regs 9 A
   fixes A only modulo 2^64 (A + 2^64 satisfies every other premise and violates A + 448 <= 2^64). *)

Lemma f9_entry_of : forall g j phi fr regs mem md A v,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  f9_E g j phi fr regs mem -> f9_GAP g j phi fr regs mem ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 -> rg regs 24 v -> 0 <= v < 2 ^ 31 ->
  0 <= kind_name_addr v < 2 ^ 47 /\ 0 <= Sfr fr /\ 0 <= fr /\ 0 <= A /\
  fr + FRAME_BYTES <= A /\ A + 448 <= 2 ^ 64 /\ Sfr fr + FRAME_SHADOW <= A /\
  (Sfr fr + FRAME_SHADOW <= fr \/ fr + FRAME_BYTES <= Sfr fr) /\
  wr_at rsegs mem (Sfr fr) FRAME_SHADOW /\
  (exists b, ov_read_bytes rsegs mem (wa (kind_name_addr v / 8 + ASAN_K)) 1 = Some [b] /\
             (bv_signed b = 0 \/ kind_name_addr v mod 8 < bv_signed b)) /\
  (exists c, ov_read_bytes rsegs mem (wa (kind_name_addr v)) 1 = Some [c] /\ bv_unsigned c <> 63) /\
  bytes_at rsegs mem (A + 288) (le8 (Z_to_bv 64 (fr + 256))) /\
  bytes_at rsegs mem (A + 304) (le8 (Z_to_bv 64 (fr + 272))) /\
  bytes_at rsegs mem (A + 296) (le8 (Z_to_bv 64 (fr + 304))).
Proof.
  intros g j phi fr regs mem md A v HFRA HE HG Hr9 HAb Hr24 Hvb.
  destruct HFRA as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9' & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & Hsp4096 & HSapp & Hspill & Hsel & Hq56 & Hloc &
    Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWINa & Hhi1 & Hhi2 & Hhi3 & Hhb & Hlive).
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A1 & v1 &
    (Hr9a & Hq96 & _ & _ & Hq272 & Hq264) & _ & Hr24a & Hv1 & _ & _ & Hname).
  destruct HG as (G1 & _ & G2k & _ & _ & G4 & G5 & _).
  destruct G5 as (Happ & Hgt & _ & HAge & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhi.
  (* the spill base A: FRA's A0, 64-bit with room for the 416-byte save area *)
  assert (HSb : g_S g <= 2 ^ 64).
  { destruct Hsaved as (_ & Hb & _). unfold saved_bytes in Hb. rewrite !length_app, !length_le8 in Hb.
    cbn [length Z.of_nat] in Hb. lia. }
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hspr.
  unfold AC.aspZ in Haspz. rewrite Haspz in Hspr.
  assert (HA0b : 0 <= A0 < 2 ^ 64) by lia.
  assert (EA : A = A0) by exact (l9_rg_eq regs 9 A A0 Hr9 Hr9' HAb HA0b).
  subst A0.
  assert (EA1 : A1 = A).
  { apply (f9_base_eq A A1 120 (fragb fr + 15) mem); [| lia | lia | lia | exact Hq96].
    unfold rg in Hr9a, Hr9. rewrite <- Hr9a, <- Hr9. reflexivity. }
  subst A1.
  assert (Ev1 : v1 = v) by (apply (l9_rg_eq regs 24 v1 v Hr24a Hr24); lia).
  subst v1.
  pose proof (ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)) as Hk.
  assert (Ev : v = t_k (g_in g) j) by (apply (l9_rg_eq regs 24 _ _ Hr24 G2k); unfold t_k; lia).
  assert (Hv13 : 0 <= v <= 13) by (rewrite Ev; unfold t_k; lia).
  (* the FRAME_SHADOW frame shadow bytes are shadow memory *)
  assert (HshIS : forall i, 0 <= i < FRAME_SHADOW -> in_shadow (Sfr fr + i)).
  { intros i Hi. replace (Sfr fr + i) with (shadow_addr (fr + 8 * i)).
    - apply shadow_of_app. apply Happ. lia.
    - unfold Sfr, shadow_addr. replace (fr + 8 * i) with (fr + i * 8) by lia. rewrite Z.div_add by lia. lia. }
  assert (HshB : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (HshIS 0 ltac:(lia)) as S0. pose proof (HshIS (FRAME_SHADOW - 1) ltac:(lia)) as S1.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in S0, S1 |- *. lia. }
  (* the kind-name address and its shadow byte *)
  destruct (l9_kn_glob (kind_name_addr v) (l9_kn_in v)) as (Hkb & Hkg).
  destruct (sl_shadow1 mem (kind_name_addr v) (G4 _ Hkg)) as (b & Hb & Hck & _).
  rewrite Z.shiftr_div_pow2 in Hb by lia. change (2 ^ 3) with 8 in Hb.
  (* the first name byte *)
  pose proof (bytes_at_ov_read rsegs mem (kind_name_addr v) (cstr_bytes (kind_name v)) 0 1 Hname
    ltac:(unfold cstr_bytes; rewrite length_app; cbn [length]; lia)) as Hrd.
  destruct (l9_name0 v Hv13) as (c & Hc1 & Hc2).
  rewrite Hc1 in Hrd. cbn [Z.of_nat] in Hrd. rewrite Z.add_0_r in Hrd.
  destruct (G1 A Hr9 HAb) as (Hq256 & _).
  unfold q64 in Hq256, Hq272, Hq264.
  unfold AC.GT in Hgt.
  split; [exact Hkb|].
  split; [unfold LOWMEM_END in HshB; lia|].
  split; [lia|].
  split; [lia|].
  split; [exact (HAge A Hr9 HAb)|].
  split; [lia|].
  split.
  { unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
  split.
  { pose proof (Happ fr ltac:(lia)) as Ap0. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ap1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ap0, Ap1, HshB. lia. }
  split.
  { refine (conj _ (conj _ _)).
    - unfold LOWMEM_END in HshB. lia.
    - unfold HIGHMEM_BEG in HshB. lia.
    - intros i Hi. exact (proj1 (AsanRTInv.RT_shadow_rw _ _ _ HRT _ (HshIS i Hi))). }
  split; [exists b; split; [exact Hb | exact Hck]|].
  split; [exists c; split; [exact Hrd | exact Hc2]|].
  split; [exact Hq256|].
  split; [exact Hq272 | exact Hq264].
Qed.

End S_l9.

Lemma l7_flen0 : forall g j, 0 <= flen g j.
Proof.
  intros g j. unfold flen, t_len, f_len, f_L, f_h, inb, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcIdentModel.bz.
  match goal with |- context [bv_unsigned ?b1] =>
    match goal with |- context [bv_unsigned ?b2] =>
      assert_fails (constr_eq b1 b2);
      pose proof (bv_unsigned_in_range _ b1) as H1; pose proof (bv_unsigned_in_range _ b2) as H2
    end
  end.
  unfold bv_modulus in H1, H2. change (2 ^ Z.of_N 8) with 256 in H1, H2.
  destruct (Z.leb_spec 2 (f_left (g_in g) (fc (g_in g) j))); lia.
Qed.

(* The shadow byte of an app byte is shadow memory; an app byte is not shadow memory. *)

Lemma l7_app_sh : forall a, app_mem a -> in_shadow (shadow_addr a).
Proof.
  intros a Ha.
  unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
    APPMEM_END in *.
  destruct Ha as [Ha|Ha]; [left|right]; Z.div_mod_to_equations; lia.
Qed.

Lemma l7_app_nsh : forall a, app_mem a -> ~ in_shadow a.
Proof.
  intros a Ha Hs.
  unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* An app byte apart from the three frame cells is outside the six store ranges. *)

Lemma l7_app_out : forall fr x, 0 <= fr -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> app_mem x ->
  (x < fr + 256 \/ fr + 312 <= x) -> outside (f9_WA (Sfr fr) fr) x.
Proof.
  intros fr x H0 Happ Hx Hpos.
  assert (S1 : in_shadow (Sfr fr + 32)).
  { replace (Sfr fr + 32) with (shadow_addr (fr + 256))
      by (unfold Sfr, shadow_addr; clear - H0; Z.div_mod_to_equations; lia).
    apply l7_app_sh, Happ. lia. }
  assert (S2 : in_shadow (Sfr fr + 34)).
  { replace (Sfr fr + 34) with (shadow_addr (fr + 272))
      by (unfold Sfr, shadow_addr; clear - H0; Z.div_mod_to_equations; lia).
    apply l7_app_sh, Happ. lia. }
  assert (S3 : in_shadow (Sfr fr + 38)).
  { replace (Sfr fr + 38) with (shadow_addr (fr + 304))
      by (unfold Sfr, shadow_addr; clear - H0; Z.div_mod_to_equations; lia).
    apply l7_app_sh, Happ. lia. }
  pose proof (l7_app_nsh x Hx) as Hnx.
  unfold f9_WA. cbn [outside].
  repeat split; intro Hr.
  - apply Hnx. replace x with (Sfr fr + 32) by lia. exact S1.
  - lia.
  - apply Hnx. replace x with (Sfr fr + 34) by lia. exact S2.
  - lia.
  - apply Hnx. replace x with (Sfr fr + 38) by lia. exact S3.
  - lia.
Qed.

(* The shadow byte of an app byte y apart from the frame cells' granules is outside the six store ranges. *)

Lemma l7_sh_out : forall fr y, 0 <= fr -> fr mod 32 = 0 -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  app_mem y -> (y < fr + 256 \/ fr + 312 <= y) -> outside (f9_WA (Sfr fr) fr) (shadow_addr y).
Proof.
  intros fr y H0 Hm Happ Hy Hpos.
  pose proof (l7_app_sh y Hy) as Hs.
  assert (Hy0 : 0 <= y) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hy; lia).
  assert (Hc : forall x, fr + 256 <= x < fr + 312 -> x <> shadow_addr y).
  { intros x Hx E. apply (l7_app_nsh x); [apply Happ; lia | rewrite E; exact Hs]. }
  unfold f9_WA. cbn [outside].
  repeat split; intro Hr;
    first [ exact (Hc (shadow_addr y) ltac:(lia) eq_refl)
          | (unfold Sfr, shadow_addr in Hr; clear - Hr Hm Hpos H0 Hy0; Z.div_mod_to_equations; lia) ].
Qed.

(* A byte kept by munch. *)

Lemma l7_mbyte_keep : forall W (m m' : word -> option byte) a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  mbyte rsegs m' a = mbyte rsegs m a.
Proof.
  intros W m m' a MU Ha Ho. unfold mbyte. rewrite (MU (Z_to_bv 64 a)); [reflexivity|].
  rewrite MState.unsigned_lit by lia. exact Ho.
Qed.

(* A word kept by munch, both ways. *)

Lemma l7_wm_keep : forall W (m m' : word -> option byte) a v, munch W m m' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> outside W x) ->
  (word_mem rsegs m a v <-> word_mem rsegs m' a v).
Proof.
  intros W m m' a v MU H0 H1 HO.
  assert (E : forall k, (k < 8)%nat -> mbyte rsegs m' (a + Z.of_nat k) = mbyte rsegs m (a + Z.of_nat k)).
  { intros k Hk. apply (l7_mbyte_keep W); [exact MU | lia | apply HO; lia]. }
  unfold word_mem. split; intros H k Hk.
  - rewrite E by exact Hk. exact (H k Hk).
  - rewrite <- E by exact Hk. exact (H k Hk).
Qed.

(* One byte of a byte list. *)

Lemma l7_byte_of : forall m a bs i b, bytes_at rsegs m a bs -> nth_error bs i = Some b ->
  bytes_at rsegs m (a + Z.of_nat i) [b].
Proof.
  intros m a bs i b (H0 & H1 & H) E.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; congruence).
  split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. assert (Ek : k = 0%nat) by lia. subst k. cbn [nth_error].
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite (H i Hi). exact E.
Qed.

(* A frame cell offset k (a multiple of 8) of a 32-aligned frame keeps the alignments the callee asks. *)

Lemma l7_mod : forall fr k d, fr mod 32 = 0 -> d = 2 \/ d = 8 -> k mod 8 = 0 -> (fr + k) mod d = 0.
Proof. intros fr k d H Hd Hk. destruct Hd as [-> | ->]; Z.div_mod_to_equations; lia. Qed.

(* A CB cell from its bytes and its writability. *)

Lemma l7_rw : forall m a bs n, bytes_at rsegs m a bs -> length bs = n -> wr_at rsegs m a (Z.of_nat n) ->
  rw_cells rsegs m a [CB n bs].
Proof.
  intros m a bs n Hb Hl Hw. split.
  - split.
    + cbn [cells_wf cell_wf]. split; [exact Hl | exact I].
    + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

(* The n bytes at fr + k (in one granule of a 32-aligned frame) are addressable when their shadow byte b is 0 or
   at least n. *)

Lemma l7_addr_cell : forall m fr k n (b : byte), fr mod 32 = 0 -> 0 <= fr -> k mod 8 = 0 -> 0 <= k -> 0 <= n <= 8 ->
  (forall a, fr + k <= a < fr + k + n -> app_mem a) -> fr + k + n <= APPMEM_END ->
  bytes_at rsegs m (Sfr fr + k / 8) [b] ->
  (bv_signed b = 0 \/ n <= bv_signed b <= 7) ->
  addressable m (fr + k) n.
Proof.
  intros m fr k n b Hm H0 Hk Hk0 Hn Happ Hend (_ & _ & Hb) Hv.
  pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as E. cbn [nth_error] in E.
  change (Z.of_nat 0) with 0 in E. rewrite Z.add_0_r in E.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|]. exists b. split.
  - replace (shadow_addr (fr + k + i)) with (Sfr fr + k / 8); [exact E|].
    unfold Sfr, shadow_addr. clear - Hm Hk Hk0 H0 Hi Hn. Z.div_mod_to_equations. lia.
  - unfold shadow_ok. destruct Hv as [Hv|Hv]; [left; exact Hv | right].
    split; [|lia]. clear - Hm Hk Hk0 H0 Hi Hn Hv. Z.div_mod_to_equations. lia.
Qed.

(* Addressability survives writes W that miss the shadow bytes of the buffer (F9_L5's l5_addr_keep, stated with
   this file's munch / outside). *)

Lemma l7_addr_keep : forall m m' W p n,
  addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros m m' W p n (H1 & H2 & H3 & H) MU HW.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|].
  exists b. split; [|exact Hk].
  assert (Hr : 0 <= shadow_addr (p + i) < 2 ^ 64).
  { unfold shadow_addr, ASAN_K. unfold APPMEM_END in H3. Z.div_mod_to_equations. lia. }
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by exact Hr. exact (HW i Hi).
Qed.

Section S_l7.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Lemma f9_pre_of : forall g j phi fr regs mem m1 md A,
  f9_E g j phi fr regs mem -> f9_GAP g j phi fr regs mem -> rg regs 9 A ->
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md ->
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m1 md ->
  munch (f9_WA (Sfr fr) fr) mem m1 -> wmono rsegs mem m1 -> ro_agree rsegs m1 ->
  bytes_at rsegs m1 (Sfr fr + 32) (le1 (Z_to_bv 64 2)) ->
  bytes_at rsegs m1 (Sfr fr + 34) (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (Sfr fr + 38) (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (fr + 256) (le2 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (fr + 272) (le8 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (fr + 304) (le8 (Z_to_bv 64 0)) ->
  wr_at rsegs m1 (fr + 256) 2 -> wr_at rsegs m1 (fr + 272) 8 -> wr_at rsegs m1 (fr + 304) 8 ->
  (flen g j = 0 -> ~ AC.a_in_fs AC.ASYMS mem phi) ->
  exists FS, word_mem rsegs m1 (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\ AC.GT <= FS /\
    f9_pre phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (AC.aspZ regs) FS (AC.as_tp AC.ASYMS) m1
      (t_g (g_in g) j) (le2 (Z_to_bv 64 0)) (le8 (Z_to_bv 64 0)) (le8 (Z_to_bv 64 0)).
Proof.
  intros g j phi fr regs mem m1 md A HE HG HA9 HFRA0 HFRA1 HMU HWM HMI1 Bs32 Bs34 Bs38 Ba Bp Bn Wa Wp Wn HNFS.
  pose proof HE as (Hgn & Hj & (Hphi0 & HHBa) & HLK & Hr23 & Hr18 & HFM0 & HFSj0 & HKN & HKNa & HEx).
  pose proof HG as (G1 & G2a & G2b & G2c & G3 & G4 & G5 & G6a & G6b & G6c & G7 & G8).
  pose proof HFRA1 as (A1 & sp1 & s51 & HRT1 & HAH1 & Hro1 & Hsn1 & Hhalt1 & Hgimg1 & Hr21 & Hspm1 & Haspz1 &
    Hstklo1 & Hr41 & Hr81 & Hr91 & Hr31 & Hr191 & Hr261 & Hfrm & Hs51 & HAm1 & HAS1 & Hspa1 & HfrA1 & HA4161 &
    Hsp40961 & HSapp1 & Hspill1 & Hsel1 & Hq561 & Hloc1 & Hhdr11 & Hhdr21 & Hsh1 & Hwin1 & Hsaved1 & Herrno1 &
    HAG1 & HWINa1 & Hhi11 & Hhi21 & Hhi31 & Hhb1 & Hlive1 & Hinb1 & Hinblk1).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (l7_flen0 g j) as HL0.
  pose proof G5 as (Happ & Hgt & _ & _ & _).
  assert (Hfr0 : 0x5fe000 <= fr) by (unfold AC.GT in Hgt; exact Hgt).
  assert (HspA : AC.aspZ regs <= APPMEM_END) by (rewrite Haspz1; lia).
  assert (Hfrub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  pose proof HHBa as (Hpa0 & Hpa1 & Hpa2 & Hpa3).
  (* ---- the record (phi, len) apart from the frame cells and the callee's window ---- *)
  assert (HDJ : (phi + 50 <= fr + 256 \/ fr + 312 <= phi) /\
                (phi + 50 <= AC.aspZ regs - 9072 \/ AC.aspZ regs <= phi) /\ phi + 50 <= 2 ^ 64 /\ 0 < phi).
  { destruct (Z.eq_dec (flen g j) 0) as [E0|E0].
    - exact (l5_dj1 B APIf ra g fr phi (flen g j) [] regs mem md HFRA0 G5 HL0 (HNFS E0)).
    - exact (l5_dj B APIf ra g fr phi (flen g j) [] regs mem md HFRA0 G5 ltac:(lia)). }
  destruct HDJ as (Hdj & Hdw & H64 & Hp0).
  (* ---- the callee's window [S - K, S) in the slot window, above HIGHMEM_BEG ---- *)
  assert (HHI : HIGHMEM_BEG <= AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K).
  { pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ m1 md HAH1) as Hh.
    unfold REAC_CTRL_IDENTITY_REPLY_K. unfold AF.SLOT_STACK in Hstklo1. lia. }
  (* ---- the thread words at tp and tp + 8 are outside the stores ---- *)
  assert (Htp_out : forall x, AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 16 -> outside (f9_WA (Sfr fr) fr) x).
  { intros x Hx. change (AC.as_tp AC.ASYMS) with 0x5dc650 in Hx.
    apply l7_app_out; [lia | exact Happ | left; unfold LOWMEM_END; lia | left; lia]. }
  assert (HPL1 : f9_PL fr regs m1).
  { destruct G5 as (P1 & P2 & P3 & P4 & P5).
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
    intros FS0 HW HF0 HF1. apply P5; [|exact HF0 | exact HF1].
    refine (proj2 (l7_wm_keep _ mem m1 (AC.as_tp AC.ASYMS) FS0 HMU _ _ _) HW).
    - change (AC.as_tp AC.ASYMS) with 0x5dc650. lia.
    - change (AC.as_tp AC.ASYMS) with 0x5dc650. lia.
    - intros x Hx. apply Htp_out. lia. }
  assert (HDB1 : exists DB, word_mem rsegs m1 (AC.as_tp AC.ASYMS + 8) DB /\ 0 <= DB /\ DB + 32 <= 2 ^ 64).
  { destruct G8 as (DB & HDB & HDB0 & HDB1). exists DB. split; [|split; assumption].
    refine (proj1 (l7_wm_keep _ mem m1 (AC.as_tp AC.ASYMS + 8) DB HMU _ _ _) HDB).
    - change (AC.as_tp AC.ASYMS) with 0x5dc650. lia.
    - change (AC.as_tp AC.ASYMS) with 0x5dc650. lia.
    - intros x Hx. apply Htp_out. lia. }
  destruct (f9_fp_call B APIf ra g fr phi (flen g j) regs m1 md HFRA1 HPL1 HspA HDB1)
    as (FS & HWFS & HFS64 & HFP & HTLS).
  pose proof (lw_fs_place (APIf rc) _ m1 md FS HAH1 HWFS HFS64) as [HFSgt _ _ _].
  exists FS. split; [exact HWFS|]. split; [exact HFS64|]. split; [exact HFSgt|]. unfold f9_pre, f9_pre_g.
  (* 0 <= phi, len, pa, pp, pn < 2^64 *)
  split. { unfold AC.a_size, APPMEM_END in Hpa2. lia. }
  split. { unfold AC.a_size, APPMEM_END in Hpa2. lia. }
  split. { unfold APPMEM_END in Hfrub. lia. }
  split. { unfold APPMEM_END in Hfrub. lia. }
  split. { unfold APPMEM_END in Hfrub. lia. }
  (* S < 2^64, S mod 16 = 0, K <= S *)
  split. { unfold APPMEM_END in HspA. lia. }
  split. { rewrite Haspz1. exact Hspm1. }
  split. { unfold HIGHMEM_BEG in HHI. lia. }
  (* stk m1 (S - K) S *)
  split.
  { destruct (fra_win B APIf ra g fr _ regs m1 md HFRA1) as (_ & Hw).
    destruct (stk_split rsegs m1 (AC.aspZ regs - FN_STACK) (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K)
                (AC.aspZ regs) Hw)
      as (_ & Hs); [unfold REAC_CTRL_IDENTITY_REPLY_K, FN_STACK, AF.SLOT_STACK; lia | exact Hs]. }
  split. { exact HMI1. }
  split. { unfold t_g. apply fr50_length. }
  (* the record clause *)
  split.
  { intros _ H50L.
    split; [exact H64|]. split.
    - apply (fl_bytes _ mem m1 phi _ (G3 H50L) HMU).
      intros x Hx. unfold t_g in Hx. rewrite fr50_length in Hx. change (Z.of_nat 50) with 50 in Hx.
      apply l7_app_out; [lia | exact Happ | | lia].
      destruct (Hpa3 (x - phi) ltac:(unfold AC.a_size; lia)) as (Hx' & _).
      replace (phi + (x - phi)) with x in Hx' by lia. exact Hx'.
    - unfold REAC_CTRL_IDENTITY_REPLY_K. exact Hdw. }
  (* the reply_args clause *)
  split.
  { intros _.
    split; [apply l7_mod; [exact Hfrm | left; reflexivity | reflexivity]|].
    split; [apply l7_mod; [exact Hfrm | right; reflexivity | reflexivity]|].
    split; [apply l7_mod; [exact Hfrm | right; reflexivity | reflexivity]|].
    split; [apply l7_rw; [exact Ba | apply length_le2 | exact Wa]|].
    split; [apply l7_rw; [exact Bp | apply length_le8 | exact Wp]|].
    split; [apply l7_rw; [exact Bn | apply length_le8 | exact Wn]|].
    destruct G5 as (_ & _ & P3 & _ & _).
    unfold REAC_CTRL_IDENTITY_REPLY_K, FN_STACK, AF.SLOT_STACK in *.
    repeat split; lia. }
  (* asan_cells, shadow_rw *)
  split. { exact (RT_cells _ _ _ HRT1). }
  split. { exact (RT_shadow_rw _ _ _ HRT1). }
  split. { exact HHI. }
  split. { exact HspA. }
  (* addressable m1 (S - K) K *)
  split.
  { unfold REAC_CTRL_IDENTITY_REPLY_K in *.
    split; [unfold HIGHMEM_BEG in HHI; lia|]. split; [lia|]. split; [lia|].
    intros i Hi.
    assert (H1 : addressable mem (AC.aspZ regs - 9072 + i) 1) by (apply G7; lia).
    assert (H1' : addressable m1 (AC.aspZ regs - 9072 + i) 1).
    { apply (l7_addr_keep mem m1 _ _ 1 H1 HMU). intros i' Hi'.
      apply l7_sh_out; [lia | exact Hfrm | exact Happ | |].
      - right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
      - destruct G5 as (_ & _ & P3 & _ & _). unfold FN_STACK, AF.SLOT_STACK in P3. lia. }
    destruct H1' as (_ & _ & _ & Ha). pose proof (Ha 0 ltac:(lia)) as Ha0. rewrite Z.add_0_r in Ha0. exact Ha0. }
  (* addressable m1 phi 50 *)
  split.
  { intros _ H50L.
    apply (l7_addr_keep mem m1 (f9_WA (Sfr fr) fr) phi 50); [| exact HMU |].
    - split; [lia|]. split; [lia|]. split; [unfold AC.a_size in Hpa2; lia|].
      intros i Hi. apply Hpa3. unfold AC.a_size; lia.
    - intros i Hi. destruct (Hpa3 i ltac:(unfold AC.a_size; lia)) as (Happi & _).
      apply l7_sh_out; [lia | exact Hfrm | exact Happ | exact Happi | lia]. }
  (* the three frame cells addressable, apart from the runtime *)
  split.
  { intros _.
    split.
    { apply (l7_addr_cell m1 fr 256 2 (Z_to_bv 8 2));
        [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs32 |].
      right. change (bv_signed (Z_to_bv 8 2)) with 2. lia. }
    split.
    { apply (l7_addr_cell m1 fr 272 8 (Z_to_bv 8 0));
        [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs34 |].
      left. reflexivity. }
    split.
    { apply (l7_addr_cell m1 fr 304 8 (Z_to_bv 8 0));
        [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs38 |].
      left. reflexivity. }
    unfold RT_LO, RT_HI.
    split; [right; lia|]. split; [right; lia|]. right; lia. }
  (* addressable m1 BC 6 *)
  split.
  { assert (HBC : addressable mem 0x21200 6).
    { split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
      intros i Hi.
      assert (Hg : addressable mem (0x21200 + i) 1).
      { apply G4. exists 0x21200, 7. split; [|lia].
        unfold AF.frame_AG. cbn [In]. repeat (first [left; reflexivity | right]). }
      destruct Hg as (_ & _ & _ & Hg). pose proof (Hg 0 ltac:(lia)) as Hg0. rewrite Z.add_0_r in Hg0. exact Hg0. }
    apply (l7_addr_keep mem m1 _ _ 6 HBC HMU).
    intros i Hi. apply l7_sh_out; [lia | exact Hfrm | exact Happ | left; unfold LOWMEM_END; lia | left; lia]. }
  (* the image cells *)
  split. { apply real_cell_of; [exact (RT_real_cells _ _ _ HRT1) | vm_compute; reflexivity]. }
  split. { apply real_cell_of; [exact (RT_real_cells _ _ _ HRT1) | vm_compute; reflexivity]. }
  pose proof (RT_cf_cells _ _ _ HRT1) as (CF1 & _ & _ & _ & _ & _ & CF7 & _).
  split. { exact CF1. }
  split. { exact (l7_byte_of m1 (RT_CF + 240) _ 14 (Z_to_bv 8 1) CF7 eq_refl). }
  split. { exact (l7_byte_of m1 (RT_CF + 240) _ 15 (Z_to_bv 8 1) CF7 eq_refl). }
  (* fp and the tls clause *)
  split; [exact HFP | exact HTLS].
Qed.

End S_l7.

Definition f9_WC (phi len fr S FS : Z) (G : list byte) : list ivl :=
  reac_ctrl_identity_reply_fp phi len (fr + 256) (fr + 272) (fr + 304) S G ++ fp_w [1%nat] FS ++
  [(shadow_addr (S - REAC_CTRL_IDENTITY_REPLY_K), shadow_addr S)].

Lemma l8_out_WA : forall fr x, ~ (fr + 256 <= x < fr + 312) ->
  x <> Sfr fr + 32 -> x <> Sfr fr + 34 -> x <> Sfr fr + 38 -> outside (f9_WA (Sfr fr) fr) x.
Proof.
  intros fr x H1 H2 H3 H4. unfold f9_WA. cbn [outside]. repeat split; lia.
Qed.

Lemma l8_out_WC : forall phi len fr S FS G x,
  ~ (fr + 256 <= x < fr + 312) -> ~ (S - 9072 <= x < S) -> ~ (FS + 8 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (S - 9072) <= x < shadow_addr S) ->
  outside (f9_WC phi len fr S FS G) x.
Proof.
  intros phi len fr S FS G x H1 H2 H3 H4 H5. unfold f9_WC, reac_ctrl_identity_reply_fp. rewrite l1_fpw1.
  unfold REAC_CTRL_IDENTITY_REPLY_K.
  destruct (reply_ok phi len (fr + 256) (fr + 272) (fr + 304) G); cbn [app outside]; repeat split; lia.
Qed.

(* A word read survives a write list that misses its 8 bytes, in both directions. *)

Lemma l8_wm : forall W m m' a v, munch W m m' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> outside W x) ->
  (word_mem rsegs m a v <-> word_mem rsegs m' a v).
Proof.
  intros W m m' a v MU H0 H1 HW.
  assert (E : forall k, (k < 8)%nat -> mbyte rsegs m' (a + Z.of_nat k) = mbyte rsegs m (a + Z.of_nat k)).
  { intros k Hk. unfold mbyte. rewrite (MU (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|].
    rewrite MState.unsigned_lit by lia. apply HW. lia. }
  split; intros H k Hk; [rewrite (E k Hk) | rewrite <- (E k Hk)]; apply H; exact Hk.
Qed.

(* Bytes carried across two write lists that both miss them. *)

Lemma l8_tr : forall W1 W2 m m1 m2 a bs, bytes_at rsegs m a bs -> munch W1 m m1 -> munch W2 m1 m2 ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside W1 x /\ outside W2 x) -> bytes_at rsegs m2 a bs.
Proof.
  intros W1 W2 m m1 m2 a bs H M1 M2 HW.
  eapply fl_bytes;
    [eapply fl_bytes; [exact H | exact M1 | intros x Hx; exact (proj1 (HW x Hx))]
    | exact M2 | intros x Hx; exact (proj2 (HW x Hx))].
Qed.

Lemma l8_q64 : forall W1 W2 m m1 m2 a v, q64 m a v -> munch W1 m m1 -> munch W2 m1 m2 ->
  (forall x, a <= x < a + 8 -> outside W1 x /\ outside W2 x) -> q64 m2 a v.
Proof.
  intros W1 W2 m m1 m2 a v H M1 M2 HW. unfold q64 in *. apply (l8_tr W1 W2 m m1 m2 a _ H M1 M2).
  intros x Hx. apply HW. rewrite length_le8 in Hx. change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

(* A spill of SlotInv over the named base A, moved across two write lists that miss its eight bytes. *)
Lemma f9_spill_mv : forall regs regs2 mem m1 m2 W1 W2 A off v,
  spill regs mem off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off < 448 ->
  getr regs2 9 = getr regs 9 -> munch W1 mem m1 -> munch W2 m1 m2 ->
  (forall x, A + off <= x < A + off + 8 -> outside W1 x /\ outside W2 x) ->
  spill regs2 m2 off v.
Proof.
  intros regs regs2 mem m1 m2 W1 W2 A off v Hs H9 HA0 HA1 Hoff E9 M1 M2 HO.
  pose proof (f9_sp regs mem A off v H9 HA0 HA1 Hoff Hs) as Hq.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  exact (l8_q64 W1 W2 mem m1 m2 _ _ Hq M1 M2 HO).
Qed.

Lemma l8_sh_hi : forall a, 0 <= a < APPMEM_END -> shadow_addr a < HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG. unfold APPMEM_END in Ha.
  assert (D : a / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* The shadow byte k of the frame base is the shadow of the frame granule [fr + 8k, fr + 8k + 8) only. *)

Lemma l8_sh_ne : forall a fr k, fr mod 32 = 0 -> ~ (fr + 8 * k <= a < fr + 8 * k + 8) ->
  shadow_addr a <> Sfr fr + k.
Proof.
  intros a fr k Hf Hn E. apply Hn. unfold Sfr, shadow_addr in E. Z.div_mod_to_equations. lia.
Qed.

Lemma l8_flen_nn : forall g j, 0 <= flen g j.
Proof.
  intros g j. unfold flen, t_len, f_len, f_L, f_h.
  assert (Hb : forall k, 0 <= inb (g_in g) k) by (intros k; unfold inb; exact (proj1 (bv_unsigned_in_range 8 _))).
  pose proof (Hb (fc (g_in g) j)). pose proof (Hb (fc (g_in g) j + 1)).
  destruct (2 <=? f_left (g_in g) (fc (g_in g) j)); lia.
Qed.

(* The thread word at tp (below GT and below the shadow) is outside both write lists. *)

Lemma l8_Otp : forall fr sp FS phi len G x,
  AC.GT <= fr -> AC.GT <= FS -> HIGHMEM_BEG + 9072 <= sp -> LOWMEM_END <= Sfr fr ->
  LOWMEM_END <= shadow_addr (FS + 1085440) -> LOWMEM_END <= shadow_addr (sp - 9072) ->
  AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 8 ->
  outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi len fr sp FS G) x.
Proof.
  intros fr sp FS phi len G x H1 H2 H3 H4 H5 H6 Hx. change (AC.as_tp AC.ASYMS) with 0x5dc650 in Hx.
  unfold AC.GT, HIGHMEM_BEG, LOWMEM_END in *.
  split; [apply l8_out_WA | apply l8_out_WC]; lia.
Qed.

(* The spill block [A, ...) (A >= sp >= stklo >= HIGHMEM_BEG, A >= fr + FRAME_BYTES) is outside both write lists. *)

Lemma l8_OA : forall fr sp FS lo A phi len G x,
  HIGHMEM_BEG <= lo -> lo <= sp -> FS + AC.FS_SIZE <= lo -> sp <= A -> fr + FRAME_BYTES <= A -> A <= x ->
  Sfr fr + 39 <= HIGHMEM_BEG -> shadow_addr (FS + 2134016) <= HIGHMEM_BEG -> shadow_addr sp <= HIGHMEM_BEG ->
  outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi len fr sp FS G) x.
Proof.
  intros fr sp FS lo A phi len G x H1 H2 H3 H4 H5 H6 H7 H8 H9. unfold AC.FS_SIZE in *.
  split; [apply l8_out_WA | apply l8_out_WC]; lia.
Qed.

(* A frame byte off the three cells is outside both write lists. *)

Lemma l8_OF : forall fr sp FS phi len G x,
  fr <= x < fr + FRAME_BYTES -> ~ (fr + 256 <= x < fr + 312) ->
  (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
  (fr + FRAME_BYTES <= sp - FN_STACK \/ sp <= fr) -> FS + 2134016 <= fr ->
  LOWMEM_END <= Sfr fr -> Sfr fr + 39 <= HIGHMEM_BEG ->
  LOWMEM_END <= shadow_addr (FS + 1085440) -> shadow_addr (FS + 2134016) <= HIGHMEM_BEG ->
  LOWMEM_END <= shadow_addr (sp - 9072) -> shadow_addr sp <= HIGHMEM_BEG ->
  outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi len fr sp FS G) x.
Proof.
  intros fr sp FS phi len G x H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. unfold FN_STACK, AF.SLOT_STACK in *.
  split; [apply l8_out_WA | apply l8_out_WC]; lia.
Qed.

(* A heap-block byte (app memory, at most stklo, off the side stack, off the frame cells) is outside both lists. *)

Lemma l8_OB : forall fr sp FS lo phi len G x,
  app_mem x -> x <= lo -> ~ (FS <= x < FS + AC.FS_SIZE) -> ~ (fr + 256 <= x < fr + 312) ->
  lo <= sp - FN_STACK ->
  LOWMEM_END <= Sfr fr -> Sfr fr + 39 <= HIGHMEM_BEG ->
  LOWMEM_END <= shadow_addr (FS + 1085440) -> shadow_addr (FS + 2134016) <= HIGHMEM_BEG ->
  LOWMEM_END <= shadow_addr (sp - 9072) -> shadow_addr sp <= HIGHMEM_BEG ->
  outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi len fr sp FS G) x.
Proof.
  intros fr sp FS lo phi len G x H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  unfold app_mem, AC.FS_SIZE, FN_STACK, AF.SLOT_STACK in *.
  split; [apply l8_out_WA | apply l8_out_WC]; lia.
Qed.

(* The shadow byte of such a heap-block byte is outside both lists. *)

Lemma l8_OS : forall fr sp FS lo phi len G a,
  0 <= a < APPMEM_END -> a <= lo -> ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (fr + 256 <= a < fr + 312) ->
  fr mod 32 = 0 -> lo <= sp - FN_STACK -> 0 <= FS ->
  (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
  (FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS) ->
  HIGHMEM_BEG <= sp - 9072 ->
  outside (f9_WA (Sfr fr) fr) (shadow_addr a) /\ outside (f9_WC phi len fr sp FS G) (shadow_addr a).
Proof.
  intros fr sp FS lo phi len G a Ha Hlo Hfs Hc Hfrm Hsp HFS0 Hfr HFSr Hw.
  pose proof (l1_sh_lo a ltac:(lia)) as Y1. pose proof (l8_sh_hi a Ha) as Y2.
  unfold AC.FS_SIZE, FN_STACK, AF.SLOT_STACK in *.
  split.
  - apply l8_out_WA.
    + lia.
    + apply l8_sh_ne; [exact Hfrm | lia].
    + apply l8_sh_ne; [exact Hfrm | lia].
    + apply l8_sh_ne; [exact Hfrm | lia].
  - apply l8_out_WC.
    + lia.
    + lia.
    + lia.
    + destruct (Z_lt_le_dec a FS) as [Hl|Hg].
      * pose proof (l5_sh_lt a (FS + 1085440) ltac:(lia) ltac:(lia)). lia.
      * pose proof (l5_sh_mono (FS + 2134016) a ltac:(lia)). lia.
    + pose proof (l5_sh_lt a (sp - 9072) ltac:(lia) ltac:(lia)). lia.
Qed.

(* The shadow byte of a frame byte at or above fr + 2624 is outside both write lists: of the three shadow cells
   the segment writes it is none (they shadow fr + 256 / fr + 272 / fr + 304), it is not app memory (so it misses
   the frame cells, the callee's window and the side stack), it is at or above the shadow of the class-1 frames
   (FS + 2134016 <= fr) and it is apart from the shadow of the callee's window (the frame is apart from the
   window, both ends 8-aligned). Used for FLI's our[] bytes at [fr + 2624, fr + 2630), RAD's two records and FPS's
   parse struct [fr + 176, fr + 212). *)
Lemma f9_sh_fr_out : forall fr sp FS phi len G a,
  (fr <= a < fr + 256 \/ fr + 312 <= a < fr + FRAME_BYTES) -> fr + FRAME_BYTES <= APPMEM_END -> 0 <= fr -> fr mod 32 = 0 ->
  (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
  (FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS) -> 0 <= FS -> FS + 2134016 <= fr ->
  HIGHMEM_BEG + 9072 <= sp -> sp mod 16 = 0 -> (fr + FRAME_BYTES <= sp - FN_STACK \/ sp <= fr) ->
  outside (f9_WA (Sfr fr) fr) (shadow_addr a) /\ outside (f9_WC phi len fr sp FS G) (shadow_addr a).
Proof.
  intros fr sp FS phi len G a Ha Htop Hfr0 Hfrm Hfrr HFSr HFS0 HfrFS Hw Hspm Hdj.
  assert (KLO : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (KHI : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KAP : APPMEM_END = 0x800000000000) by reflexivity.
  pose proof (l1_sh_lo a ltac:(lia)) as Y1. pose proof (l8_sh_hi a ltac:(lia)) as Y2.
  unfold AC.FS_SIZE, FN_STACK, AF.SLOT_STACK in *.
  split.
  - apply l8_out_WA.
    + lia.
    + apply l8_sh_ne; [exact Hfrm | lia].
    + apply l8_sh_ne; [exact Hfrm | lia].
    + apply l8_sh_ne; [exact Hfrm | lia].
  - apply l8_out_WC.
    + lia.
    + lia.
    + lia.
    + pose proof (l5_sh_mono (FS + 2134016) a ltac:(lia)). lia.
    + destruct Hdj as [Hd|Hd].
      * pose proof (l5_sh_lt a (sp - 9072) ltac:(lia) ltac:(lia)). lia.
      * pose proof (l5_sh_mono sp a ltac:(lia)). lia.
Qed.

(* The call's write list misses the shadow byte of every frame byte (the second half of f9_sh_fr_out, for the
   whole frame: the call writes no frame shadow byte). *)
Lemma f9_sh_wc_out : forall fr sp FS phi len G a,
  fr <= a < fr + FRAME_BYTES -> fr + FRAME_BYTES <= APPMEM_END -> 0 <= fr -> (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) ->
  (FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS) -> 0 <= FS -> FS + 2134016 <= fr ->
  HIGHMEM_BEG + 9072 <= sp -> (fr + FRAME_BYTES <= sp - FN_STACK \/ sp <= fr) ->
  outside (f9_WC phi len fr sp FS G) (shadow_addr a).
Proof.
  intros fr sp FS phi len G a Ha Htop Hfr0 Hfrr HFSr HFS0 HfrFS Hw Hdj.
  assert (KLO : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (KHI : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KAP : APPMEM_END = 0x800000000000) by reflexivity.
  pose proof (l1_sh_lo a ltac:(lia)) as Y1. pose proof (l8_sh_hi a ltac:(lia)) as Y2.
  unfold AC.FS_SIZE, FN_STACK, AF.SLOT_STACK in *.
  apply l8_out_WC.
  - lia.
  - lia.
  - lia.
  - pose proof (l5_sh_mono (FS + 2134016) a ltac:(lia)). lia.
  - destruct Hdj as [Hd|Hd].
    + pose proof (l5_sh_lt a (sp - 9072) ltac:(lia) ltac:(lia)). lia.
    + pose proof (l5_sh_mono sp a ltac:(lia)). lia.
Qed.

(* RCA at the call's return 0x821ec: the three shadow stores 0x821bc / 0x821c8 / 0x821d4 make the reply cells
   [fr + 256, fr + 258), [fr + 272, fr + 280), [fr + 304, fr + 312) addressable (shadow bytes 2, 0, 0 at
   S(fr) + 32 / 34 / 38), and the call writes none of those shadow bytes. *)
Lemma f9_addr_out : forall fr sp FS phi len G m1 m2,
  fr + FRAME_BYTES <= APPMEM_END -> 0 <= fr -> fr mod 32 = 0 -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  (FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS) -> 0 <= FS -> FS + 2134016 <= fr ->
  HIGHMEM_BEG + 9072 <= sp -> (fr + FRAME_BYTES <= sp - FN_STACK \/ sp <= fr) ->
  bytes_at rsegs m1 (Sfr fr + 32) (le1 (Z_to_bv 64 2)) ->
  bytes_at rsegs m1 (Sfr fr + 34) (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (Sfr fr + 38) (le1 (Z_to_bv 64 0)) ->
  munch (f9_WC phi len fr sp FS G) m1 m2 ->
  RCA fr m2.
Proof.
  intros fr sp FS phi len G m1 m2 Htop Hfr0 Hfrm Happ HFSr HFS0 HfrFS Hw Hdj Bs32 Bs34 Bs38 MU.
  assert (Hfrr : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem in H1, H2. unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (SO : forall a, fr <= a < fr + FRAME_BYTES -> outside (f9_WC phi len fr sp FS G) (shadow_addr a))
    by (intros a Ha; exact (f9_sh_wc_out fr sp FS phi len G a Ha Htop Hfr0 Hfrr HFSr HFS0 HfrFS Hw Hdj)).
  unfold RCA. split; [|split].
  - apply (l5_addr_keep m1 m2 (f9_WC phi len fr sp FS G) (fr + 256) 2); [| exact MU | intros i Hi; apply SO; lia].
    apply (l7_addr_cell m1 fr 256 2 (Z_to_bv 8 2));
      [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs32 |].
    right. change (bv_signed (Z_to_bv 8 2)) with 2. lia.
  - apply (l5_addr_keep m1 m2 (f9_WC phi len fr sp FS G) (fr + 272) 8); [| exact MU | intros i Hi; apply SO; lia].
    apply (l7_addr_cell m1 fr 272 8 (Z_to_bv 8 0));
      [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs34 |].
    left. reflexivity.
  - apply (l5_addr_keep m1 m2 (f9_WC phi len fr sp FS G) (fr + 304) 8); [| exact MU | intros i Hi; apply SO; lia].
    apply (l7_addr_cell m1 fr 304 8 (Z_to_bv 8 0));
      [exact Hfrm | lia | reflexivity | lia | lia | intros a Ha; apply Happ; lia | lia | exact Bs38 |].
    left. reflexivity.
Qed.

Section S_l8.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Lemma f9_exit_of : forall g j phi fr regs regs2 mem m1 m2 md2 A FS,
  f9_E g j phi fr regs mem -> f9_GAP g j phi fr regs mem -> rg regs 9 A ->
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs2 m2 md2 ->
  ENT APIf g (hb1 phi (AC.a_size (flen g j))) m2 md2 ->
  munch (f9_WA (Sfr fr) fr) mem m1 -> munch (f9_WC phi (flen g j) fr (AC.aspZ regs) FS (t_g (g_in g) j)) m1 m2 ->
  wmono rsegs mem m1 -> wmono rsegs m1 m2 ->
  (forall a, fr + 256 <= a < fr + 258 \/ fr + 272 <= a < fr + 280 \/ fr + 304 <= a < fr + 312 ->
     exists b, mrd rsegs m1 (wa a) = Some b) ->
  word_mem rsegs m1 (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> AC.GT <= FS ->
  getr regs2 2 = getr regs 2 -> getr regs2 9 = getr regs 9 -> getr regs2 18 = getr regs 18 ->
  getr regs2 20 = getr regs 20 -> getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 ->
  getr regs2 23 = getr regs 23 -> getr regs2 24 = getr regs 24 -> getr regs2 25 = getr regs 25 ->
  getr regs2 27 = getr regs 27 ->
  getr regs2 10 = Z_to_bv 64 (reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)) ->
  (reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true ->
     rw_cells rsegs m2 (fr + 256) [CB 2 (reply_addr (t_g (g_in g) j))] /\
     rw_cells rsegs m2 (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
     rw_cells rsegs m2 (fr + 304) [CB 8 (le8 (Z_to_bv 64 (ir_s (t_g (g_in g) j) - 13)))]) ->
  (flen g j = 0 -> ~ AC.a_in_fs AC.ASYMS mem phi) ->
  f9_X g j phi fr regs mem ->
  bytes_at rsegs m1 (Sfr fr + 32) (le1 (Z_to_bv 64 2)) ->
  bytes_at rsegs m1 (Sfr fr + 34) (le1 (Z_to_bv 64 0)) ->
  bytes_at rsegs m1 (Sfr fr + 38) (le1 (Z_to_bv 64 0)) ->
  Inv_B821ec_at B APIf ra g j (mkCfg (mkst regs2 (Z_to_bv 64 0x821ec) m2 (seg_rom rsegs)) md2).
Proof.
  intros g j phi fr regs regs2 mem m1 m2 md2 A FS HE HG HA9 HFRA HENT2 MU1 MU2 WM1 WM2 HRD HWM HFS HGTFS
    E2 E9 E18 E20 E21 E22 E23 E24 E25 E27 E10 HRP HZ0 HX Bs32 Bs34 Bs38.
  assert (KSL : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (KFS : AC.FS_SIZE = 11571200) by reflexivity.
  assert (KGT : AC.GT = 0x5fe000) by reflexivity.
  assert (KLO : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (KHI : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (KAP : APPMEM_END = 0x800000000000) by reflexivity.
  assert (Ktp : AC.as_tp AC.ASYMS = 0x5dc650) by reflexivity.
  destruct HE as (Hgn & Hj & HHB & HLK & H23 & H18 & HFM & HFSj & HKN & HKNa &
    A0 & v & HFLV & H10v & H24v & Hv & Hq280 & Hu32 & Hkn).
  clear H10v H24v Hv Hu32 Hkn Hq280.
  destruct HG as (HG1 & HG25 & HG24 & HG22 & HG3 & HG4 & HPL & HW256 & HW272 & HW304 & HG7 & HG8).
  clear HG4 HW256 HW272 HW304 HG7 HG8.
  destruct HPL as (Happ & HGTfr & HPLc & HPLd & HPLe). unfold AC.GT in HGTfr.
  pose proof HFRA as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & Hsp4096 & HSapp & Hspill & Hsel & Hq56 & Hloc &
    Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWINa & Hhi1 & Hhi2 & Hhi3 & Hhb & Hlive & Hinb & Hinblk).
  clear HRT Hro Hsn Hhalt Hgimg Hr2 Hr4 Hr8 Hr3 Hr19 Hr26 Hs5 HAm Hspill Hsel Hhdr1 Hhdr2 Hsh Herrno Hhb
    Hlive.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (l8_flen_nn g j) as Hlen0.
  destruct HHB as (Hphi0 & HAd).
  destruct HFLV as (HrA0 & HQ64 & HQ72 & HQ80 & HQ272 & HQ264).
  (* sp, the stack bounds at m2, the spill base A0 *)
  assert (Hsp : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; unfold AC.aspZ; apply l1_word_range).
  assert (HS : AC.aspZ regs = sp) by (rewrite <- Haspz; unfold AC.aspZ; rewrite E2; reflexivity).
  assert (HspE2 : sp <= APPMEM_END) by lia.
  rewrite HS in MU2, HPLc.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhigh.
  assert (Hw0 : HIGHMEM_BEG + 9072 <= sp) by lia.
  assert (Lsb : length (saved_bytes ra g) = 104%nat)
    by (unfold saved_bytes; rewrite !length_app, !length_le8; reflexivity).
  assert (EA : A' = A0).
  { symmetry. apply (f9_base_eq A' A0 120 (fragb fr + 15) mem); [| lia | lia | lia | exact HQ64].
    unfold rg in Hr9, HrA0. rewrite <- HrA0, <- E9. exact Hr9. }
  subst A'.
  assert (HA0 : 0 <= A0 < 2 ^ 64) by lia.
  pose proof (HPLd A0 HrA0 HA0) as HA0fr.
  (* frame bounds *)
  assert (HSfr1 : LOWMEM_END <= Sfr fr) by (unfold Sfr; apply l1_sh_lo; lia).
  assert (Hfrapp : fr + FRAME_BYTES <= APPMEM_END /\ (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr)).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem in H1, H2. lia. }
  destruct Hfrapp as (Hfrtop & Hfr_reg).
  assert (HSfr2 : Sfr fr + 39 <= HIGHMEM_BEG).
  { replace (Sfr fr + 39) with (shadow_addr (fr + 39 * 8))
      by (unfold Sfr, shadow_addr; rewrite Z.div_add by lia; lia).
    apply l1_sh_hi. lia. }
  assert (HshW1 : LOWMEM_END <= shadow_addr (sp - 9072)) by (apply l1_sh_lo; lia).
  assert (HshF1 : LOWMEM_END <= shadow_addr (FS + 1085440)) by (apply l1_sh_lo; lia).
  (* the tp word names FS in mem, m1 and m2 *)
  assert (Otp : forall x, AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 8 ->
      outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) x)
    by (intros x Hx; exact (l8_Otp fr sp FS phi (flen g j) (t_g (g_in g) j) x HGTfr HGTFS Hw0 HSfr1 HshF1 HshW1 Hx)).
  assert (HWMmem : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { apply (proj2 (l8_wm (f9_WA (Sfr fr) fr) mem m1 (AC.as_tp AC.ASYMS) FS MU1 ltac:(lia) ltac:(lia)
      (fun x Hx => proj1 (Otp x Hx)))). exact HWM. }
  assert (HWM2 : word_mem rsegs m2 (AC.as_tp AC.ASYMS) FS).
  { apply (proj1 (l8_wm _ m1 m2 (AC.as_tp AC.ASYMS) FS MU2 ltac:(lia) ltac:(lia)
      (fun x Hx => proj2 (Otp x Hx)))). exact HWM. }
  destruct (lw_fs_place (APIf rc) _ _ _ FS HAH HWM2 HFS) as [_ HFSlo HFS4096 HFSapp].
  assert (HFS_reg : FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(lia)) as H1. pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as H2.
    unfold app_mem in H1, H2. lia. }
  assert (HshF2 : shadow_addr (FS + 2134016) <= HIGHMEM_BEG) by (apply l1_sh_hi; lia).
  assert (HshW2 : shadow_addr sp <= HIGHMEM_BEG) by (apply l1_sh_hi; lia).
  (* the frame: above stklo (real arm) or in FS above its class-1 frames (side arm) *)
  assert (HFRM : AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) m2 md2 <= fr \/
                 (FS + 36864 + 6 * 2 ^ 20 <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE)).
  { destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hside _]]]].
    - left. destruct (Hreal fr ltac:(lia)) as (H & _). exact H.
    - right. destruct (Hside fr ltac:(lia)) as (b & _ & Hwb & Hb1 & Hb2).
      destruct (l1_wm_norm m2 _ b FS Hwb HWM2 HFS ltac:(lia)) as [Eb|Eb].
      + subst b. apply (HPLe FS HWMmem HFS). lia.
      + exfalso. subst b. lia. }
  assert (HfrFS : FS + 2134016 <= fr) by lia.
  destruct (fra_win B APIf ra g fr _ regs2 m2 md2 HFRA) as (Hstklo' & _).
  assert (Hasp2 : AC.aspZ regs2 = sp) by (unfold AC.aspZ in *; rewrite E2; exact HS).
  rewrite Hasp2 in Hstklo'.
  (* the heap block (phi, len): app memory, at most stklo, off FS *)
  assert (HBLK : forall a, phi <= a < phi + AC.a_size (flen g j) ->
      app_mem a /\ a <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) m2 md2 /\ ~ (FS <= a < FS + AC.FS_SIZE)).
  { intros a Ha. unfold AC.a_size in Ha.
    destruct (lw_blocks (APIf rc) _ _ _ phi (AC.a_size (flen g j)) HAH
      ltac:(apply in_or_app; left; left; reflexivity)) as [_ _ Hpst _ Hbyte].
    unfold AC.a_size in Hpst, Hbyte.
    destruct (Z_lt_le_dec 0 (flen g j)) as [Hp|Hz].
    - destruct (Hbyte a ltac:(lia)) as (Hap & _ & _ & _ & Hnf). split; [exact Hap|]. split; [lia|].
      intro Hin. apply Hnf. exists FS. split; [assumption|]. split; [exact HWM2 | exact Hin].
    - assert (Ea : a = phi) by lia. subst a.
      destruct HAd as (_ & _ & _ & Hab). destruct (Hab 0 ltac:(unfold AC.a_size; lia)) as (Hap & _).
      rewrite Z.add_0_r in Hap. split; [exact Hap|]. split; [lia|].
      intro Hin. apply (HZ0 ltac:(lia)). exists FS. split; [assumption|]. split; [exact HWMmem | exact Hin]. }
  assert (HBc : forall a, phi <= a < phi + AC.a_size (flen g j) -> ~ (fr + 256 <= a < fr + 312)).
  { intros a Ha. destruct (HBLK a Ha) as (_ & Hle & Hnf). lia. }
  (* the outside facts *)
  assert (HOA : forall x, A0 <= x < A0 + 416 ->
      outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) x).
  { intros x Hx.
    exact (l8_OA fr sp FS (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) m2 md2) A0 phi (flen g j) (t_g (g_in g) j) x
      Hhigh ltac:(lia) HFSlo Hspa HA0fr ltac:(lia) HSfr2 HshF2 HshW2). }
  assert (HOS : forall i, 0 <= i < AC.a_size (flen g j) ->
      outside (f9_WA (Sfr fr) fr) (shadow_addr (phi + i)) /\
      outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) (shadow_addr (phi + i))).
  { intros i Hi. destruct (HBLK (phi + i) ltac:(lia)) as (Hxa & Hxl & Hxf).
    assert (Hxr : 0 <= phi + i < APPMEM_END) by (unfold app_mem in Hxa; lia).
    exact (l8_OS fr sp FS _ phi (flen g j) (t_g (g_in g) j) (phi + i) Hxr Hxl Hxf (HBc (phi + i) ltac:(lia))
      Hfrm Hstklo' ltac:(lia) Hfr_reg HFS_reg ltac:(lia)). }
  (* every SlotInv spill over s1 below A0 + 416 moves to (regs2, m2): the two runs miss [A0, A0 + 416) *)
  assert (MV : forall off w, 0 <= off <= 408 -> spill regs mem off w -> spill regs2 m2 off w).
  { intros off w Hoff Hs.
    apply (f9_spill_mv regs regs2 mem m1 m2 _ _ A0 off w Hs HrA0 ltac:(lia) ltac:(lia) ltac:(lia) E9 MU1 MU2).
    intros x Hx. apply HOA. lia. }
  (* a frame range addressable at entry stays addressable when it misses the three cells [fr + 256, fr + 312):
     its shadow bytes are none of the three the stores write and none the call writes (f9_sh_fr_out) *)
  assert (AK : forall p n, addressable mem p n ->
      (forall i, 0 <= i < n -> fr <= p + i < fr + 256 \/ fr + 312 <= p + i < fr + FRAME_BYTES) -> addressable m2 p n).
  { intros p n Hp Hin.
    apply (l5_addr_keep m1 m2 (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) p n).
    - apply (l5_addr_keep mem m1 (f9_WA (Sfr fr) fr) p n Hp MU1).
      intros i Hi. exact (proj1 (f9_sh_fr_out fr sp FS phi (flen g j) (t_g (g_in g) j) (p + i)
        (Hin i Hi) ltac:(lia) ltac:(lia) Hfrm Hfr_reg HFS_reg ltac:(lia) HfrFS Hw0 Hspm HPLc)).
    - exact MU2.
    - intros i Hi. exact (proj2 (f9_sh_fr_out fr sp FS phi (flen g j) (t_g (g_in g) j) (p + i)
        (Hin i Hi) ltac:(lia) ltac:(lia) Hfrm Hfr_reg HFS_reg ltac:(lia) HfrFS Hw0 Hspm HPLc)). }
  (* bytes inside the frame and outside the three cells keep their values *)
  assert (BK : forall a bs, bytes_at rsegs mem a bs ->
      (forall x, a <= x < a + Z.of_nat (length bs) -> fr <= x < fr + 256 \/ fr + 312 <= x < fr + FRAME_BYTES) ->
      bytes_at rsegs m2 a bs).
  { intros a bs Hb Hin. apply (l8_tr _ _ mem m1 m2 a bs Hb MU1 MU2). intros x Hx.
    exact (l8_OF fr sp FS phi (flen g j) (t_g (g_in g) j) x ltac:(pose proof (Hin x Hx); lia)
      ltac:(pose proof (Hin x Hx); lia) Hfr_reg HPLc HfrFS HSfr1 HSfr2 HshF1 HshF2 HshW1 HshW2). }
  (* KNT (adopt 11): the kind-name table, 112 bytes at KIND_NAME = 0x9f580. The table is image data below GT, so
     it lies below the frame (GT <= fr), below the side stack (GT <= FS) and below every byte the two runs write
     that is not in the image; its own shadow bytes lie in [0x8000beb0, 0x8000bebe], which is below the frame's
     shadow bytes, below the side stack's and below the stack window's, and the frame cells are either below
     LOWMEM_END or above HIGHMEM_BEG. *)
  assert (KKN : KNC.KIND_NAME = 0x9f580) by reflexivity.
  assert (OKN : forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 ->
      outside (f9_WA (Sfr fr) fr) x /\ outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) x).
  { intros x Hx. split; [apply l8_out_WA | apply l8_out_WC]; lia. }
  assert (HSfrlb : 0x7fff8000 + 785408 <= Sfr fr).
  { unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
  assert (HshFlb : 0x7fff8000 + 921088 <= shadow_addr (FS + 1085440)).
  { unfold shadow_addr, ASAN_K. unfold AC.GT in HGTFS. Z.div_mod_to_equations. lia. }
  assert (HshWlb : 0x100000000 <= shadow_addr (sp - 9072)).
  { unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
  assert (OKNs : forall i, 0 <= i < 112 ->
      outside (f9_WA (Sfr fr) fr) (shadow_addr (KNC.KIND_NAME + i)) /\
      outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) (shadow_addr (KNC.KIND_NAME + i))).
  { intros i Hi.
    assert (Hsb : 0x8000beb0 <= shadow_addr (KNC.KIND_NAME + i) <= 0x8000bebe).
    { unfold shadow_addr, ASAN_K. rewrite KKN. Z.div_mod_to_equations. lia. }
    split; [apply l8_out_WA | apply l8_out_WC]; lia. }
  assert (HKNT2 : KNT m2).
  { split.
    - apply (l8_tr _ _ mem m1 m2 KNC.KIND_NAME KNC.kind_name_bytes HKN MU1 MU2).
      assert (HKL : Z.of_nat (length KNC.kind_name_bytes) = 112) by reflexivity.
      rewrite HKL. exact OKN.
    - apply (l5_addr_keep m1 m2 (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) KNC.KIND_NAME 112).
      + apply (l5_addr_keep mem m1 (f9_WA (Sfr fr) fr) KNC.KIND_NAME 112 HKNa MU1).
        intros i Hi. exact (proj1 (OKNs i Hi)).
      + exact MU2.
      + intros i Hi. exact (proj2 (OKNs i Hi)). }
  (* the cut *)
  unfold Inv_B821ec_at, CUTST.
  exists phi, regs2, m2, md2, fr.
  split; [pose proof FF as (HSG & _); rewrite HSG; reflexivity|].
  split; [exact HFRA|].
  split; [exact HENT2|].
  cbv beta.
  split; [|split; [|split; [|split]]].
  - unfold f10_K.
    split; [exact Hgn|]. split; [exact Hj|].
    split.
    { split; [exact Hphi0|].
      apply (l5_addr_keep m1 m2 (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) phi (AC.a_size (flen g j))).
      - apply (l5_addr_keep mem m1 (f9_WA (Sfr fr) fr) phi (AC.a_size (flen g j)) HAd MU1).
        intros i Hi. exact (proj1 (HOS i Hi)).
      - exact MU2.
      - intros i Hi. exact (proj2 (HOS i Hi)). }
    split.
    (* LK: Tac_ro.lk_keep over the spill transport MV, with FLI's six memory facts moved by AK / BK / HKNT2 *)
    { destruct (Tac_ro.fli_mem _ _ _ _ (proj2 (proj2 (proj2 HLK)))) as (Had6 & Hstkfr & HRid & HRfg & _ & Hfst).
      pose proof HLK as (_ & _ & HLour & HFLI0).
      apply (Tac_ro.lk_keep g fr j regs regs2 mem m2 HLK).
      - unfold rg in *. rewrite E27. exact (proj1 HFLI0).
      - apply (AK _ _ Had6). intros i Hi. lia.
      (* the frame's stk: writable by wmono, readable outside the three frame cells the runs write *)
      - destruct Hstkfr as (K0 & K1 & Kfr). split; [exact K0|]. split; [exact K1|].
        assert (Kkeep : forall x, fr <= x < fr + FRAME_BYTES -> outside (f9_WA (Sfr fr) fr) x ->
                  outside (f9_WC phi (flen g j) fr sp FS (t_g (g_in g) j)) x ->
                  exists b, mrd rsegs m2 (wa x) = Some b).
        { intros x Hx O1 O2. destruct (Kfr x Hx) as (_ & b & Hb). exists b. unfold mrd in Hb |- *.
          rewrite (MU2 (wa x)) by (rewrite wa_unsigned by lia; exact O2).
          rewrite (MU1 (wa x)) by (rewrite wa_unsigned by lia; exact O1). exact Hb. }
        assert (HRD2 : forall x, fr + 256 <= x < fr + 258 \/ fr + 272 <= x < fr + 280 \/
                         fr + 304 <= x < fr + 312 -> exists b, mrd rsegs m2 (wa x) = Some b).
        { intros x Hx.
          destruct (reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)) eqn:Hok.
          - destruct (HRP eq_refl) as (Rc1 & Rc2 & Rc3).
            destruct Hx as [Hx|[Hx|Hx]].
            + apply (l2_rw_rd m2 (fr + 256) 2 _ x Rc1). cbn [length reply_addr]. lia.
            + apply (l2_rw_rd m2 (fr + 272) 8 _ x Rc2). rewrite length_le8. cbn. lia.
            + apply (l2_rw_rd m2 (fr + 304) 8 _ x Rc3). rewrite length_le8. cbn. lia.
          - destruct (HRD x Hx) as (b & Hb). exists b. unfold mrd in Hb |- *.
            rewrite (MU2 (wa x)); [exact Hb|].
            rewrite wa_unsigned by lia.
            apply l2_out2; [intros HC; congruence | unfold FN_STACK, AF.SLOT_STACK in *; lia ..]. }
        intros a Ha. split; [apply WM2, WM1; exact (proj1 (Kfr a Ha))|].
        assert (Hcells : fr + 256 <= a < fr + 258 \/ fr + 272 <= a < fr + 280 \/
                         fr + 304 <= a < fr + 312 \/
                         (~ (fr + 256 <= a < fr + 258) /\ ~ (fr + 272 <= a < fr + 280) /\
                          ~ (fr + 304 <= a < fr + 312))) by lia.
        destruct Hcells as [Hc|[Hc|[Hc|(Hc1 & Hc2 & Hc3)]]].
        + exact (HRD2 a ltac:(lia)).
        + exact (HRD2 a ltac:(lia)).
        + exact (HRD2 a ltac:(lia)).
        + apply (Kkeep a Ha).
          * unfold f9_WA. cbn [outside]. repeat split; try exact I; lia.
          * apply l2_out2;
              [intros _; split; [exact Hc1 | split; [exact Hc2 | exact Hc3]]
              | unfold FN_STACK, AF.SLOT_STACK in *; lia ..].
      (* RAD: the records' bytes and the local `first` stay addressable; KNT from HKNT2 *)
      - apply (AK _ _ HRid). intros i Hi. lia.
      - apply (AK _ _ HRfg). intros i Hi. unfold fragb in *. lia.
      - exact HKNT2.
      - apply (AK _ _ Hfst). intros i Hi. lia.
      - unfold OURb in *. apply (l8_tr _ _ mem m1 m2 _ _ HLour MU1 MU2).
        intros x Hx. rewrite OUR_length in Hx. change (Z.of_nat 6) with 6 in Hx.
        exact (l8_OF fr sp FS phi (flen g j) (t_g (g_in g) j) x ltac:(lia) ltac:(lia) Hfr_reg HPLc HfrFS
          HSfr1 HSfr2 HshF1 HshF2 HshW1 HshW2).
      - intros off w Hoff Hs. exact (MV off w ltac:(lia) Hs). }
    split.
    { exists A0. destruct (HG1 A0 HrA0 HA0) as (Q288 & Q176 & Q200 & Q208 & Q248 & Q312 & _).
      split; [|split; [exact HA0|]].
      - unfold FLVsp. split; [unfold rg in HrA0 |- *; rewrite E9; exact HrA0|].
        split; [apply (l8_q64 _ _ mem m1 m2 _ _ HQ64 MU1 MU2); intros x Hx; apply HOA; lia|].
        split; [apply (l8_q64 _ _ mem m1 m2 _ _ HQ72 MU1 MU2); intros x Hx; apply HOA; lia|].
        split; [apply (l8_q64 _ _ mem m1 m2 _ _ HQ80 MU1 MU2); intros x Hx; apply HOA; lia|].
        split; [apply (l8_q64 _ _ mem m1 m2 _ _ HQ272 MU1 MU2); intros x Hx; apply HOA; lia|].
        apply (l8_q64 _ _ mem m1 m2 _ _ HQ264 MU1 MU2); intros x Hx; apply HOA; lia.
      - split; [apply (l8_q64 _ _ mem m1 m2 _ _ Q288 MU1 MU2); intros x Hx; apply HOA; lia|].
        split; [apply (l8_q64 _ _ mem m1 m2 _ _ Q176 MU1 MU2); intros x Hx; apply HOA; lia|].
        split; [apply (l8_q64 _ _ mem m1 m2 _ _ Q200 MU1 MU2); intros x Hx; apply HOA; lia|].
        split; [apply (l8_q64 _ _ mem m1 m2 _ _ Q208 MU1 MU2); intros x Hx; apply HOA; lia|].
        split; [apply (l8_q64 _ _ mem m1 m2 _ _ Q248 MU1 MU2); intros x Hx; apply HOA; lia|].
        apply (l8_q64 _ _ mem m1 m2 _ _ Q312 MU1 MU2); intros x Hx; apply HOA; lia. }
    split; [unfold rg in H23 |- *; rewrite E18; exact H23|].
    split; [unfold rg in H18 |- *; rewrite E20; exact H18|].
    split; [unfold rg in HG25 |- *; rewrite E25; exact HG25|].
    split; [unfold rg in HG24 |- *; rewrite E24; exact HG24|].
    split; [destruct HFM as (M184 & _); exact (MV 184 _ ltac:(lia) M184)|].
    split; [unfold rg in HG22 |- *; rewrite E22; exact HG22|].
    unfold reply_args.
    destruct (Z.eqb_spec phi 0) as [E|_]; [exfalso; exact (Hphi0 E)|].
    destruct (Z.eqb_spec (fr + 256) 0) as [E|_]; [exfalso; lia|].
    destruct (Z.eqb_spec (fr + 272) 0) as [E|_]; [exfalso; lia|].
    destruct (Z.eqb_spec (fr + 304) 0) as [E|_]; [exfalso; lia|].
    reflexivity.
  - (* FSj: the local `first` [fr + 2880, fr + 2920) is frame memory outside the three cells *)
    pose proof HFSj as HFS0. unfold FSj, FSb in HFS0. destruct HFS0 as (_ & _ & _ & Hfst0 & _).
    apply (Tac_ro.fsj_keep g fr j regs regs2 mem m2 HFSj).
    + intros a bs Ha Hab Hb. apply (BK a bs Hb). intros x Hx. lia.
    + apply (AK _ _ Hfst0). intros i Hi. lia.
  - intros H50. apply (l8_tr _ _ mem m1 m2 phi _ (HG3 H50) MU1 MU2).
    intros x Hx.
    assert (Lg : length (t_g (g_in g) j) = 50%nat) by (unfold t_g; apply fr50_length).
    rewrite Lg in Hx. change (Z.of_nat 50) with 50 in Hx.
    assert (Hxb : phi <= x < phi + AC.a_size (flen g j)) by (unfold AC.a_size; lia).
    destruct (HBLK x Hxb) as (Hxa & Hxl & Hxf).
    exact (l8_OB fr sp FS _ phi (flen g j) (t_g (g_in g) j) x Hxa Hxl Hxf (HBc x Hxb) Hstklo'
      HSfr1 HSfr2 HshF1 HshF2 HshW1 HshW2).
  - unfold rg. exact E10.
  - split; [intros Hok; exact (HRP Hok)|].
    destruct HX as (_ & _ & HT & HR0 & HFPS & H272).
    (* FTURN: the two cursor spills move (MV); Phi's len bytes are a live block, below stklo and off FS *)
    split.
    { destruct HT as (T216 & T224 & Tphi & Tlen).
      split; [apply MV; [lia | exact T216]|]. split; [apply MV; [lia | exact T224]|].
      split; [|exact Tlen].
      apply (l8_tr _ _ mem m1 m2 phi _ Tphi MU1 MU2). intros x Hx.
      assert (Hxb : phi <= x < phi + AC.a_size (flen g j)) by (unfold AC.a_size, flen in *; lia).
      destruct (HBLK x Hxb) as (Hxa & Hxl & Hxf).
      exact (l8_OB fr sp FS _ phi (flen g j) (t_g (g_in g) j) x Hxa Hxl Hxf (HBc x Hxb) Hstklo'
        HSfr1 HSfr2 HshF1 HshF2 HshW1 HshW2). }
    (* REC0: both records are frame bytes outside the three cells (38 and 72 bytes) *)
    split.
    { destruct HR0 as ((Hid & Hidok) & (Hfg & Hfgok)).
      split; split; try assumption.
      - unfold IDBe in *. apply (BK _ _ Hid). rewrite Tac_ro.tr_ID_length. intros x Hx.
        change (Z.of_nat 38) with 38 in Hx. lia.
      - unfold FGBe in *. apply (BK _ _ Hfg). rewrite Tac_ro.tr_FG_length. intros x Hx.
        change (Z.of_nat 72) with 72 in Hx. lia. }
    (* FPS: the parse struct (36 bytes at fr + 176) and its addressability *)
    split.
    { destruct HFPS as (HpB & HadB). split.
      - unfold pBb in *. apply (BK _ _ HpB).
        assert (Lb : length (t_B (g_in g) j) = 36%nat) by (apply ctrlparse_length).
        rewrite Lb. intros x Hx. change (Z.of_nat 36) with 36 in Hx. lia.
      - apply (AK _ _ HadB). intros i Hi. lia. }
    (* F272: the spill [A+272] moves *)
    split; [unfold F272 in *; apply MV; [lia | exact H272]|].
    (* RCA: the three shadow stores (f9_addr_out) *)
    exact (f9_addr_out fr sp FS phi (flen g j) (t_g (g_in g) j) m1 m2 Hfrtop ltac:(lia) Hfrm Happ HFS_reg
      ltac:(lia) HfrFS Hw0 HPLc Bs32 Bs34 Bs38 MU2).
Qed.

End S_l8.


Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract (lib/B/Prog/reac_ctrl_identity_reply_c.v), taken as a Section Hypothesis. *)
Hypothesis HIR : reac_ctrl_identity_reply_contract.

Lemma f9_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried value, from H : rg regs r v. *)

Ltac f9_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

Lemma seg_F9 : forall j, Hat B APIf ra (Inv_B821ec_at B APIf ra) j ->
  Hat B APIf ra (Inv_B82180_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & HBody).
  destruct (f9_E_split g j phi fr regs mem HBody) as (HE & HX).
  pose proof (f9_GAP_of B APIf ra g j phi fr regs mem md HFRA HE HX) as HG.
  (* an empty record's buffer is not in the side stack: Phi is a live block of the cut's heap *)
  assert (G9 : flen g j = 0 -> ~ AC.a_in_fs AC.ASYMS mem phi).
  { intros _. apply (f9_fra_phi_nfs B APIf ra g fr _ regs mem md phi (flen g j) HFRA).
    apply in_or_app. left. unfold hb1. cbn [In]. left. reflexivity. }
  subst c. rewrite SEGS.
  pose proof HE as (Hgn & Hj & HHB & HLK & Hp18 & Hl20 & HFMe & HFSje & HKB & HKAD &
                    A & v & HFL & Ha0 & Hs8 & Hv & H22kp & Hu32 & HNB).
  pose proof (proj1 HFL) as H9.
  pose proof HG as (G1 & G2a & G2b & G2c & G3 & G4 & G5 & G6a & G6b & G6c & G7 & G8).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz & Hstklo &
    Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & Hsp4096 & HSap &
    Hspillq & Hsel & Hq56 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWINa & Hstkhi1 &
    Hstkhi2 & Hstkhi3 & Hhb & Hlive).
  (* The spill base of the cut is FRA's: the cut fixes it only modulo 2^64 (F8.f9_base_eq). *)
  assert (HSb : g_S g <= 2 ^ 64).
  { destruct Hsaved as (_ & Hb & _). unfold saved_bytes in Hb. rewrite !length_app, !length_le8 in Hb.
    cbn [length Z.of_nat] in Hb. lia. }
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hspr.
  assert (Haspz' : AC.aspZ regs = sp) by exact Haspz.
  unfold AC.aspZ in Haspz'. rewrite Haspz' in Hspr.
  assert (HA2b : 0 <= A2 < 2 ^ 64) by lia.
  assert (HAb : 0 <= A < 2 ^ 64).
  { assert (EA : A = A2).
    { apply (f9_base_eq A2 A 120 (fragb fr + 15) mem); [| lia | lia | lia | exact (proj1 (proj2 HFL))].
      unfold rg in H9, Hr9. rewrite <- H9, <- Hr9. reflexivity. }
    lia. }
  edestruct f9_entry_of as
    (HXb & HS30 & Hfr0 & HA0 & HfrA9 & HA64 & HS3A & HS3fr & Wsh & (b & RK & OK) & (c0 & RC0 & HC0) &
     Q256 & Q272 & Q264);
    [exact HFRA | exact HE | exact HG | exact H9 | exact HAb | exact Hs8 | exact Hv |].
  (* ---- phase A: 0x82180 - 0x821dc ---- *)
  apply (sl_run_lib regs (Z_to_bv 64 0x82180) mem md
    (fun R pc' mem1 =>
       pc' = Z_to_bv 64 0x821e0 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 27 = getr regs 27 /\
       getr R 9 = Z_to_bv 64 A /\ getr R 18 = Z_to_bv 64 phi /\ getr R 19 = Z_to_bv 64 (Sfr fr) /\
       getr R 20 = Z_to_bv 64 (flen g j) /\ getr R 26 = Z_to_bv 64 ASAN_K /\
       getr R 12 = Z_to_bv 64 (fr + 256) /\ getr R 13 = Z_to_bv 64 (fr + 272) /\
       getr R 14 = Z_to_bv 64 (fr + 304) /\
       munch (f9_WA (Sfr fr) fr) mem mem1 /\ wmono rsegs mem mem1 /\ ro_agree rsegs mem1 /\
       (forall q, (exists bq, mbyte rsegs mem q = Some bq) -> exists bq, mbyte rsegs mem1 q = Some bq) /\
       bytes_at rsegs mem1 (Sfr fr + 32) (le1 (Z_to_bv 64 2)) /\
       bytes_at rsegs mem1 (Sfr fr + 34) (le1 (Z_to_bv 64 0)) /\
       bytes_at rsegs mem1 (Sfr fr + 38) (le1 (Z_to_bv 64 0)) /\
       bytes_at rsegs mem1 (fr + 256) (le2 (Z_to_bv 64 0)) /\
       bytes_at rsegs mem1 (fr + 272) (le8 (Z_to_bv 64 0)) /\
       bytes_at rsegs mem1 (fr + 304) (le8 (Z_to_bv 64 0)) /\
       wr_at rsegs mem1 (fr + 256) 2 /\ wr_at rsegs mem1 (fr + 272) 8 /\ wr_at rsegs mem1 (fr + 304) 8)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f9_mkR_of_expand.
    f9_subst_slot H9. f9_subst_slot Ha0. f9_subst_slot Hl20. f9_subst_slot Hr19. f9_subst_slot Hp18.
    f9_subst_slot Hr26.
    apply f9_evtA with (X := kind_name_addr v) (A := A) (S3 := Sfr fr) (fr := fr) (phi := phi)
                       (len := flen g j) (b := b) (c0 := c0); try assumption.
    intros mem1 MU WM PR Bs32 Bs34 Bs38 Ba Bp Bn Wa1 Wp1 Wn1.
    (* the six stores are above GT (the frame and its shadow bytes), so ro_agree crosses them *)
    assert (MI : ro_agree rsegs mem1).
    { apply (sl_ro_keep (f9_WA (Sfr fr) fr) mem mem1 Hro MU). intros x Hx.
      pose proof G5 as (_ & HGTfr0 & _).
      assert (HSlo0 : LOWMEM_END <= Sfr fr) by (unfold Sfr; apply l1_sh_lo; lia).
      cbv [f9_WA]. cbn [Frame.outside]. unfold AC.GT, LOWMEM_END in *. repeat split; try exact I; lia. }
    eexists _, _, _. split; [reflexivity|].
    repeat (split; [solve [reflexivity | assumption] | ]); solve [reflexivity | assumption].
  - intros R pc' mem1 regs1 md1 HK Hreg Hmat.
    destruct HK as (Hpc & E2 & E3 & E4 & E8 & E21 & E22 & E23 & E24 & E25 & E27 & E9 & E18 & E19 & E20 & E26 &
      E12 & E13 & E14 & MU & WM & MI & PR & Bs32 & Bs34 & Bs38 & Ba & Bp & Bn & Wa1 & Wp1 & Wn1).
    subst pc'.
    assert (Fr2 : getr regs1 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs1 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs1 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs1 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr23 : getr regs1 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (Fr21 : getr regs1 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr22 : getr regs1 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr24 : getr regs1 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr25 : getr regs1 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (Fr27 : getr regs1 27 = getr regs 27) by (rewrite Hreg; exact E27).
    assert (R9 : rg regs1 9 A) by (unfold rg; rewrite Hreg; exact E9).
    assert (R18 : rg regs1 18 phi) by (unfold rg; rewrite Hreg; exact E18).
    assert (R19 : rg regs1 19 (Sfr fr)) by (unfold rg; rewrite Hreg; exact E19).
    assert (R20 : rg regs1 20 (flen g j)) by (unfold rg; rewrite Hreg; exact E20).
    assert (R26 : rg regs1 26 ASAN_K) by (unfold rg; rewrite Hreg; exact E26).
    assert (R12 : rg regs1 12 (fr + 256)) by (unfold rg; rewrite Hreg; exact E12).
    assert (R13 : rg regs1 13 (fr + 272)) by (unfold rg; rewrite Hreg; exact E13).
    assert (R14 : rg regs1 14 (fr + 304)) by (unfold rg; rewrite Hreg; exact E14).
    assert (Fr9 : getr regs1 9 = getr regs 9)
      by (unfold rg in R9, H9; rewrite R9; symmetry; exact H9).
    assert (Fr18 : getr regs1 18 = getr regs 18)
      by (unfold rg in R18, Hp18; rewrite R18; symmetry; exact Hp18).
    assert (Fr19 : getr regs1 19 = getr regs 19)
      by (unfold rg in R19, Hr19; rewrite R19; symmetry; exact Hr19).
    assert (Fr20 : getr regs1 20 = getr regs 20)
      by (unfold rg in R20, Hl20; rewrite R20; symmetry; exact Hl20).
    assert (Fr26 : getr regs1 26 = getr regs 26)
      by (unfold rg in R26, Hr26; rewrite R26; symmetry; exact Hr26).
    assert (Haspz1 : AC.aspZ regs1 = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    (* the tp word is outside the six stores *)
    assert (MUsym : munch (f9_WA (Sfr fr) fr) mem1 mem)
      by (intros x Hx; symmetry; apply MU; exact Hx).
    assert (G5' : f9_PL fr regs1 mem1).
    { destruct G5 as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|].
      split; [rewrite Haspz1; exact P3|].
      split. { intros A' HA' HA'b. apply P4; [|exact HA'b]. unfold rg in *. rewrite Fr9 in HA'. exact HA'. }
      intros FS0 HW HB0 HR0. apply P5; [|exact HB0|exact HR0].
      apply (kb_word_munch rsegs mem1 mem (f9_WA (Sfr fr) fr) (AC.as_tp AC.ASYMS) FS0 HW MUsym).
      intros k Hk.
      assert (Etp : AC.as_tp AC.ASYMS = 0x5dc650) by reflexivity.
      rewrite Etp. split; [lia|].
      pose proof (shadow_of_app fr (P1 fr ltac:(lia))) as Hsh0.
      assert (HSlo : 0x7fff8000 <= Sfr fr).
      { unfold Sfr. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh0. lia. }
      assert (HGT' : 0x5fe000 <= fr) by (unfold AC.GT in P2; exact P2).
      cbv [f9_WA]. cbn [Frame.outside].
      repeat split; try exact I; intro HC; lia. }
    assert (Hsh1 : exists sh, bytes_at rsegs mem1 (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
    { destruct Hshf as (sh0 & Hb0 & Hl0).
      apply (f9_bytes_ex mem1 (Z.to_nat FRAME_SHADOW) (Sfr fr)); [lia | | ].
      - destruct Hb0 as (_ & Hb1 & _). rewrite Hl0 in Hb1. exact Hb1.
      - intros i Hi. apply PR. destruct Hb0 as (_ & _ & Hb2).
        destruct (nth_error sh0 i) as [bb|] eqn:Enth.
        + exists bb. rewrite <- Enth. apply Hb2. lia.
        + apply nth_error_None in Enth. lia. }
    assert (HFRA1 : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs1 mem1 md).
    { eapply f9_fra_st; try eassumption.
      all: try (intros q Hq0 Hq; apply PR; exact Hq).
      all: try exact Hsh1. }
    assert (HFRA1' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs1 mem1 md1).
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs1 regs1 mem1 md md1 HFRA1);
        try reflexivity. exact Hmat. }
    (* ENT across the six stores (three frame cells, three frame shadow bytes) and the page step *)
    assert (HENT1 : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem1 md1).
    { destruct (l3_ah B APIf ra g fr _ regs mem mem1 md HFRA G5 MU WM (fun q _ Hq => PR q Hq))
        as (_ & Hown & Hlo & Hhi).
      eapply ent_mat; [|exact Hmat].
      apply (ent_store B APIf ra g fr _ regs mem mem1 md (f9_W9 fr) HENT HFRA MU).
      - intros x Hx. destruct (l3_W_cases fr x) as [Ho | [E | [E | [E | Hb]]]].
        + left. exact Ho.
        + right; right; right. unfold Sfr in *. lia.
        + right; right; right. unfold Sfr in *. lia.
        + right; right; right. unfold Sfr in *. lia.
        + right; right; left. lia.
      - exact Hlo.
      - exact Hhi.
      - intros a _ Ho. exact (proj2 (Hown a) Ho). }
    (* ---- phase B: 0x821e0 - 0x821e8, through the call ---- *)
    assert (HFRA1r : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem1 md).
    { eapply f9_fra_st with (regs := regs) (mem := mem) (regs' := regs) (mem' := mem1);
        try eassumption; try reflexivity.
      all: try (intros q Hq0 Hq; apply PR; exact Hq).
      all: try exact Hsh1. }
    destruct (f9_pre_of B APIf ra g j phi fr regs mem mem1 md A HE HG H9 HFRA HFRA1r MU WM MI
                Bs32 Bs34 Bs38 Ba Bp Bn Wa1 Wp1 Wn1 G9) as (FS & HWMtp & HFSb & HGTFS & HPRE).
    assert (Hsp1 : getr regs1 2 = Z_to_bv 64 (AC.aspZ regs))
      by (rewrite Fr2, Haspz; exact Hr2).
    assert (Htp1 : getr regs1 4 = Z_to_bv 64 (AC.as_tp AC.ASYMS)) by (rewrite Fr4; exact Hr4).
    apply (sl_run_lib regs1 (Z_to_bv 64 0x821e0) mem1 md1
      (fun R pc' mem2 =>
         pc' = Z_to_bv 64 0x821ec /\
         getr R 2 = getr regs1 2 /\ getr R 3 = getr regs1 3 /\ getr R 4 = getr regs1 4 /\
         getr R 8 = getr regs1 8 /\ getr R 21 = getr regs1 21 /\ getr R 22 = getr regs1 22 /\
         getr R 23 = getr regs1 23 /\ getr R 24 = getr regs1 24 /\ getr R 25 = getr regs1 25 /\
         getr R 27 = getr regs1 27 /\
         getr R 9 = Z_to_bv 64 A /\ getr R 18 = Z_to_bv 64 phi /\
         getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 20 = Z_to_bv 64 (flen g j) /\
         getr R 26 = Z_to_bv 64 ASAN_K /\
         getr R 10 = Z_to_bv 64 (reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)) /\
         munch (f9_WC phi (flen g j) fr (AC.aspZ regs) FS (t_g (g_in g) j)) mem1 mem2 /\
         wmono rsegs mem1 mem2 /\ ro_agree rsegs mem2 /\
         stk rsegs mem2 (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs) /\
         (reply_ok phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j) = true ->
            rw_cells rsegs mem2 (fr + 256) [CB 2 (reply_addr (t_g (g_in g) j))] /\
            rw_cells rsegs mem2 (fr + 272) [CB 8 (le8 (Z_to_bv 64 (phi + 38)))] /\
            rw_cells rsegs mem2 (fr + 304) [CB 8 (le8 (Z_to_bv 64 (ir_s (t_g (g_in g) j) - 13)))]) /\
         asan_cells mem2 /\ shadow_rw mem2 /\
         addressable mem2 (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) REAC_CTRL_IDENTITY_REPLY_K /\
         fp [1%nat] mem2 (AC.as_tp AC.ASYMS) FS (AC.aspZ regs - REAC_CTRL_IDENTITY_REPLY_K) (AC.aspZ regs)
           (reac_ctrl_identity_reply_W phi (fr + 256) (fr + 272) (fr + 304) (AC.aspZ regs))
           (reac_ctrl_identity_reply_D phi (flen g j) (fr + 256) (fr + 272) (fr + 304)))
      (Post B APIf ra g)).
    + destruct HFRA1' as (_ & _ & _ & _ & _ & _ & _ & Hh1 & _). exact Hh1.
    + rewrite f9_mkR_of_expand.
      f9_subst_slot R9. f9_subst_slot R12. f9_subst_slot R13. f9_subst_slot R14.
      f9_subst_slot R18. f9_subst_slot R19. f9_subst_slot R20. f9_subst_slot R26.
      apply f9_evtB with (A := A) (S3 := Sfr fr) (fr := fr) (phi := phi) (len := flen g j)
                         (S := AC.aspZ regs) (FS := FS) (TP := AC.as_tp AC.ASYMS)
                         (G := t_g (g_in g) j) (ja := le2 (Z_to_bv 64 0)) (jp := le8 (Z_to_bv 64 0))
                         (jn := le8 (Z_to_bv 64 0)).
      * exact HIR.
      * exact Hsp1.
      * exact Htp1.
      * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      * pose proof G5 as (_ & HGTfr1 & _). exact HGTfr1.
      * exact HPRE.
      * intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' mem2
          MUc WMc MIc STc RPc ACc SHc ADc FPc TLc.
        eexists _, _, _. split; [reflexivity|].
        repeat (split; [solve [reflexivity | assumption] | ]); solve [reflexivity | assumption].
    + intros R2 pc2 mem2 regs2 md2 HK2 Hreg2 Hmat2.
      destruct HK2 as (Hpc2 & F2 & F3 & F4 & F8' & F21 & F22 & F23 & F24 & F25 & F27 & F9' & F18 & F19 & F20 &
        F26 & F10' & MUc & WMc & MIc & STc & RPc & ACc & SHc & ADc & FPc).
      subst pc2.
      pose proof MUc as MUc1. rewrite <- Haspz1 in MUc1. cbv [f9_WC] in MUc1.
      pose proof ADc as ADc1. rewrite <- Haspz1 in ADc1.
      pose proof STc as STc1. rewrite <- Haspz1 in STc1.
      pose proof FPc as FPc1. rewrite <- Haspz1 in FPc1.
      assert (K9 : getr regs2 9 = getr regs1 9)
        by (rewrite Hreg2, F9'; unfold rg in R9; symmetry; exact R9).
      assert (K19 : getr regs2 19 = getr regs1 19)
        by (rewrite Hreg2, F19; unfold rg in R19; symmetry; exact R19).
      assert (K26 : getr regs2 26 = getr regs1 26)
        by (rewrite Hreg2, F26; unfold rg in R26; symmetry; exact R26).
      assert (K2' : getr regs2 2 = getr regs1 2) by (rewrite Hreg2; exact F2).
      assert (K3 : getr regs2 3 = getr regs1 3) by (rewrite Hreg2; exact F3).
      assert (K4 : getr regs2 4 = getr regs1 4) by (rewrite Hreg2; exact F4).
      assert (K8 : getr regs2 8 = getr regs1 8) by (rewrite Hreg2; exact F8').
      assert (HFE2 : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs2 mem2 md2 /\
                     ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem2 md2).
      { eapply f9_fra_call with (regs := regs1) (mem := mem1) (md := md1) (FS := FS)
                                (G := t_g (g_in g) j);
          try eassumption; try (rewrite Hreg2; assumption). }
      destruct HFE2 as (HFRA2 & HENT2).
      assert (Eq2 : getr regs2 2 = getr regs 2) by (rewrite Hreg2, F2; exact Fr2).
      assert (Eq9 : getr regs2 9 = getr regs 9)
        by (rewrite Hreg2, F9'; unfold rg in H9; symmetry; exact H9).
      assert (Eq18 : getr regs2 18 = getr regs 18)
        by (rewrite Hreg2, F18; unfold rg in Hp18; symmetry; exact Hp18).
      assert (Eq20 : getr regs2 20 = getr regs 20)
        by (rewrite Hreg2, F20; unfold rg in Hl20; symmetry; exact Hl20).
      assert (Eq21 : getr regs2 21 = getr regs 21) by (rewrite Hreg2, F21; exact Fr21).
      assert (Eq22 : getr regs2 22 = getr regs 22) by (rewrite Hreg2, F22; exact Fr22).
      assert (Eq23 : getr regs2 23 = getr regs 23) by (rewrite Hreg2, F23; exact Fr23).
      assert (Eq24 : getr regs2 24 = getr regs 24) by (rewrite Hreg2, F24; exact Fr24).
      assert (Eq25 : getr regs2 25 = getr regs 25) by (rewrite Hreg2, F25; exact Fr25).
      assert (Eq27 : getr regs2 27 = getr regs 27) by (rewrite Hreg2, F27; exact Fr27).
      assert (Eq10 : getr regs2 10 =
                Z_to_bv 64 (reply_ret phi (flen g j) (fr + 256) (fr + 272) (fr + 304) (t_g (g_in g) j)))
        by (rewrite Hreg2; exact F10').
      assert (HIexit : Inv_B821ec_at B APIf ra g j
                 (mkCfg (mkst regs2 (Z_to_bv 64 0x821ec) mem2 (seg_rom rsegs)) md2)).
      { (* the three frame cells the segment writes are readable in mem1 (its own stores) *)
        assert (HRDc : forall a, fr + 256 <= a < fr + 258 \/ fr + 272 <= a < fr + 280 \/
                         fr + 304 <= a < fr + 312 -> exists b, mrd rsegs mem1 (wa a) = Some b).
        { intros a Ha. destruct Ha as [Ha|[Ha|Ha]].
          - apply (l2_bytes_rd mem1 (fr + 256) _ a Ba). rewrite length_le2. cbn. lia.
          - apply (l2_bytes_rd mem1 (fr + 272) _ a Bp). rewrite length_le8. cbn. lia.
          - apply (l2_bytes_rd mem1 (fr + 304) _ a Bn). rewrite length_le8. cbn. lia. }
        eapply f9_exit_of with (regs := regs) (mem := mem) (m1 := mem1) (A := A) (FS := FS);
          try eassumption. }
      pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.



End S.
