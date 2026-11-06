(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module paths and module names changed; 342 of its 407 lines of code are new or changed and 700 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/io_send_seg_csf.v; 576 of its 677 lines of code are new or changed and 306 lines of the source are left out. *)
(* io_send_seg_e2: the head and the 0xe2 test of the E2 / DATA arm of the image-B walk of io_send
   (fuzz_transport.asan-ubsan 41113a03c82f, entry 0x82ffc = TImgB.v ti_io_send timg_B; the statement is
   lib/B/Prog/io_send_cg.v transport_io_send_cg_holds_stmt), the two stretches 0x830cc .. 0x830d0 and
   0x83108 .. 0x8310c (transportb_text + IOS_E2DATA and + IOS_E2T, lib/B/Prog/io_send_seg_cut.v).

   The code (io_send_cg.v header; iosend-B-listing), with sp = the walk's sp (the entry sp less IOSEND_FRAME = 160):
     0x830cc  lhu a1, 38(sp)            f.retry (struct offset 30 of the struct spec_frame f at sp + 8, read through
                                         check_sent_frame_cg.v trans_sframe_at), io_send's own frame, no instrumented
                                         check;
     0x830d0  beq a1, zero, 0x83108     f.retry = 0 goes to IOS_E2T, else on to IOS_RTY (0x830d4);
     0x83108  addi a1, zero, 226
     0x8310c  bne a0, a1, 0x83148       a0 = f.cmd <> 0xe2 goes to IOS_DATA, else on to IOS_E2ARM (0x83110).
   Image B keeps f.cmd in a0 across the dispatch (image A keeps it in s5).

   Proved as the image-A twin lib/A/Prog/io_send_seg_e2.v proves its ios_e2_head / ios_e2_test: one symbolic run of
   lib/A/Prog/PaShadow.v over the G journal to the branch (lib/B/Prog/TransportGRunB.v paj_run_x, DgnTransportBPaLib.v
   paj_run_tok), psrr_branch_tok at the branch, and a run to the branch's target (paj_run_to_x / paj_run_to_tok). The
   symbolic state has one read-only region, the 2 bytes of f.retry at sp + 38 (atom 32), and no write window: neither
   stretch stores, so the run's frame_of keeps every byte of the view (YC4b.v kept_of_frame with an empty set), and
   ie2h_keep carries every fact of the cut (io_send_seg_cut.v ios_e2_at, any fail, any world Bx) to the run's memory;
   the running kept fact by ie2h_kept_step (lib/A/Prog/io_send_seg_csf.v ics_kept_step at image B's names). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB m_set_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_frm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* A field of the struct spec_frame, as the engine reads it            *)
(* ------------------------------------------------------------------ *)

(* Byte k of the little-endian value of a byte list is the list's byte k (0 past its end). *)
Lemma ie2h_ble_shiftr : forall (l : list byte) (k : nat),
  Z.shiftr (bytes_le_to_Z l) (8 * Z.of_nat k) mod 256 = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof.
  induction l as [|b r IH]; intros k.
  - cbn [bytes_le_to_Z nth]. destruct k; rewrite Z.shiftr_0_l, Z_to_bv_unsigned; reflexivity.
  - assert (Hb : 0 <= bv_unsigned b < 256)
      by (pose proof (bv_unsigned_in_range 8 b) as Hr; change (bv_modulus 8) with 256 in Hr; lia).
    assert (HL : Z.log2 (bv_unsigned b) < 8).
    { destruct (Z.eq_dec (bv_unsigned b) 0) as [E|Hne];
        [rewrite E, Z.log2_nonpos by lia; lia | apply Z.log2_lt_pow2; lia]. }
    cbn [bytes_le_to_Z].
    destruct k as [|k'].
    + cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
      change 256 with (2 ^ 8).
      apply Z.bits_inj'. intros i Hi.
      destruct (Z_lt_le_dec i 8) as [Hl|Hl].
      * rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
        rewrite (Z.testbit_neg_r (bytes_le_to_Z r) (i - 8)) by lia. apply orb_false_r.
      * rewrite Z.mod_pow2_bits_high by lia. symmetry. apply Z.bits_above_log2; lia.
    + cbn [nth]. rewrite <- (IH k').
      f_equal.
      apply Z.bits_inj'. intros i Hi.
      rewrite !Z.shiftr_spec by lia.
      rewrite Z.lor_spec, Z.shiftl_spec by lia.
      rewrite (Z.bits_above_log2 (bv_unsigned b) (i + 8 * Z.of_nat (S k'))) by lia.
      cbn [orb]. f_equal. lia.
Qed.

(* The sub-list TW.sub reads is the list's own bytes (TWorldLemmas.v ne_sub, as nth). *)
Lemma ie2h_nth_sub : forall (l : list byte) (off : Z) (n k : nat), 0 <= off -> (k < n)%nat ->
  (Z.to_nat off + n <= length l)%nat ->
  nth k (TW.sub l off n) (Z_to_bv 8 0) = nth (Z.to_nat off + k) l (Z_to_bv 8 0).
Proof.
  intros l off n k H0 Hk Hn.
  assert (HS : (k < length (TW.sub l off n))%nat)
    by (unfold TW.sub; rewrite length_firstn, length_skipn; lia).
  assert (HL : (Z.to_nat off + k < length l)%nat) by lia.
  pose proof (TWL.ne_sub l off n k H0) as E.
  replace (k <? n)%nat with true in E by (symmetry; apply Nat.ltb_lt; lia).
  rewrite (nth_error_nth' (TW.sub l off n) (Z_to_bv 8 0) HS),
          (nth_error_nth' l (Z_to_bv 8 0) HL) in E.
  injection E as E. exact E.
Qed.

(* One byte, read as a one-byte little-endian value. *)
Lemma ie2h_le_byte1 : forall b : byte, YO0f.le_byte (bv_unsigned b) 1 0 = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.

(* A field of a garr8 byte array, as YI04.val_mem of its little-endian value. *)
Lemma ie2h_val_of_garr8 : forall (m : word -> option byte) (fp off : Z) (SB : list byte) (n : nat),
  garr8 tfibsegs m fp (map (fun b : byte => bv_unsigned b) SB) -> 0 <= off ->
  (Z.to_nat off + n <= length SB)%nat ->
  YI04.val_mem tfibsegs m (fp + off) n (TW.u_at SB off n).
Proof.
  intros m fp off SB n HG H0 Hn k Hk.
  assert (Hj : ((Z.to_nat off + k) < length (map (fun b : byte => bv_unsigned b) SB))%nat)
    by (rewrite length_map; lia).
  destruct (HG (Z.to_nat off + k)%nat Hj) as [Hv _].
  specialize (Hv 0%nat ltac:(lia)). rewrite Nat2Z.inj_0, Z.add_0_r in Hv.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv by exact Hj.
  rewrite map_nth in Hv.
  replace (fp + off + Z.of_nat k) with (fp + Z.of_nat (Z.to_nat off + k)) by lia.
  rewrite Hv. f_equal. f_equal.
  rewrite ie2h_le_byte1.
  unfold YO0f.le_byte, TW.u_at.
  rewrite (Z.mod_small (bytes_le_to_Z (TW.sub SB off n)) (2 ^ (8 * Z.of_nat n)))
    by (apply TWL.ble_small, TWL.length_sub_le).
  rewrite ie2h_ble_shiftr, (ie2h_nth_sub SB off n k H0 Hk Hn). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic state of the two stretches                             *)
(* ------------------------------------------------------------------ *)

(* Atom 32: f.retry (sp + 38, 2 bytes). One region, io_send's own frame cells sp + 38 .. sp + 40, read only (no
   write window: neither stretch stores). *)
Definition ie2h_rstk : YP09.region :=
  YP09.mkRegion (Some 2%nat) 38 40 38 38 [YP09.mkChunk 38 (CVal 2 (SOff 32 0))].
Definition ie2h_facts : facts := mkFacts [] [] [].
(* No instrumented check on either stretch: the empty shadow entry, at the shadow base s4. *)
Definition ie2h_Bx : sv := SOff 20 0.
Definition ie2h_ss (pc : Z) : sstate := mkSS pc sr_atoms [ie2h_rstk] None ie2h_facts.

(* Where the token engine stops on each stretch, decided over the listing (lib/B/Prog/DgnTransportBList.v). *)
Definition ie2h_run (pc : Z) :=
  let ss := ie2h_ss pc in
  let K := run_K A_LIM ie2h_Bx (@nil shent) ss in
  match sym_runN_pi_tok transportb_tpi transportb_tw K ie2h_Bx YC4b.Bspan (@nil shent) FUEL ss with
  | (st, r) => (ss_pc (sh_ss st), r)
  end.
(* f.retry at sp + 38, then the branch of 0x830d0. *)
Lemma ie2h_stop_head :
  ie2h_run IOS_E2DATA = (IOS_AT 0x0d4, PTS_stopped (SR_branch BC_EQ (SExt false 16 (SOff 32 0)) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
(* a1 = 0xe2, then the branch of 0x8310c on a0 = f.cmd. *)
Lemma ie2h_stop_test :
  ie2h_run IOS_E2T = (IOS_AT 0x110, PTS_stopped (SR_branch BC_NE (SOff 10 0) (SLit 226))).
Proof. vm_compute. reflexivity. Qed.

(* The windows a run wrote: the windows of the state's regions, computed, each case closed by tac. *)
Ltac ie2h_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write right of a run over this state: its one region has no write window. *)
Ltac ie2h_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* The two branches: a 16-bit value against 0, a byte against 0xe2. *)
Lemma ie2h_eqb0 : forall x, 0 <= x < 2 ^ 32 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec x 0) as [->|Hne]; [reflexivity|].
  apply Z.eqb_neq. rewrite Zmod_0_l. intro E. Z.div_mod_to_equations. lia.
Qed.

Lemma ie2h_eqb_lit : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. change (2 ^ 32) with 4294967296 in Hx, Hy.
  unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* The `lhu` of f.retry is the zero-extension of its 16-bit atom (YP0m.v zext_low_sound). *)
Lemma ie2h_den_zext16 : forall (E : env) n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 16 ->
  sv_denot E (SExt false 16 (SOff n 0)) = Z_to_bv 64 u.
Proof.
  intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite (zext_low_sound false 16 u). f_equal.
  assert (C : zcanon u = u) by (unfold zcanon, M64; apply Z.mod_small; lia).
  unfold zext_low. rewrite C. change (2 ^ Z.of_N 16) with 65536.
  rewrite (Z.mod_small u 65536) by lia. exact C.
Qed.

Lemma ie2h_den_off0 : forall (E : env) n u, ew E n = Z_to_bv 64 u ->
  sv_denot E (SOff n 0) = Z_to_bv 64 u.
Proof.
  intros E n u Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* The registers the two runs keep: sp, gp, tp, s0 = len, s1 = p, a0 = f.cmd, s3 = the g_fail_next byte, s4 = the
   shadow base, and s8 .. s11, which io_send never writes. a1 is the scratch register of both stretches. *)
Definition ie2h_kept : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 10%bv; 19%bv; 20%bv; 24%bv; 25%bv; 26%bv; 27%bv].

Lemma ie2h_regs_step : forall regs (r3 r4 : bvmap 5 word) p frame fail cmd,
  ios_regs regs r3 p frame fail -> YK11.getr r3 10 = w64 cmd ->
  (forall r, 24 <= r <= 27 -> YK11.getr r3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (forall r : bv 5, In r ie2h_kept -> YK11.getr r4 r = YK11.getr r3 r) ->
  ios_regs regs r4 p frame fail /\ YK11.getr r4 10 = w64 cmd /\
  (forall r, 24 <= r <= 27 -> YK11.getr r4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
Proof.
  intros regs r3 r4 p frame fail cmd HR G10 G24 M.
  destruct HR as (G2 & G3 & G4 & G8 & G9 & G19 & G20).
  split; [|split].
  - unfold ios_regs.
    rewrite (M 2%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)),
            (M 3%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)),
            (M 4%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)),
            (M 8%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)),
            (M 9%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)),
            (M 19%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)),
            (M 20%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)).
    split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|].
    split; [exact G9|]. split; [exact G19 | exact G20].
  - rewrite (M 10%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)). exact G10.
  - assert (E24 : Z_to_bv 5 24 = 24%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E25 : Z_to_bv 5 25 = 25%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E26 : Z_to_bv 5 26 = 26%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E27 : Z_to_bv 5 27 = 27%bv) by (apply bv_eq; vm_compute; reflexivity).
    intros r Hr.
    assert (HR4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct HR4 as [E|[E|[E|E]]]; subst r.
    + rewrite E24, (M 24%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)), <- E24.
      exact (G24 24 ltac:(lia)).
    + rewrite E25, (M 25%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)), <- E25.
      exact (G24 25 ltac:(lia)).
    + rewrite E26, (M 26%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)), <- E26.
      exact (G24 26 ltac:(lia)).
    + rewrite E27, (M 27%bv ltac:(unfold ie2h_kept; cbn [In]; tauto)), <- E27.
      exact (G24 27 ltac:(lia)).
Qed.

Section e2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The walk's valuation: the 32 registers of the cut, then f.retry. *)
Definition ie2h_E (regs : bvmap 5 word) (rty : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 rty]).

Lemma ie2h_agree : forall regs rty, env_agree 32 (Ereg regs [Z_to_bv 64 rty]) (ie2h_E regs rty).
Proof.
  intros. split; [intros n Hn; unfold ie2h_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

(* The state the token engine runs from: the one region at sp and the registers as atoms. *)
Lemma ie2h_state : forall (pc sp rty : Z) (W : world segs) (regs : bvmap 5 word) mem,
  YK11.getr regs 2 = w64 sp -> 2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 -> 0 <= rty < 2 ^ 16 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (sp + 38) 2 rty ->
  st_ok_pi segs VAL (ie2h_E regs rty) (ie2h_ss pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros pc sp rty W regs mem Hsp2 Hlo Hhi Hrty V38.
  set (E := ie2h_E regs rty).
  assert (E2 : ew E 2 = YK11.getr regs 2)
    by (unfold E, ie2h_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew E 2) = sp)
    by (rewrite E2, Hsp2; apply unsigned_lit_small; lia).
  assert (X32 : ew E 32 = Z_to_bv 64 rty)
    by (unfold E, ie2h_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  rewrite restrict_mkst_fx. unfold ie2h_ss.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold ie2h_rstk, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp 38 2 (SOff 32 0) rty);
      [cbn [sv_denot]; rewrite X32, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia | exact V38].
  - exact (conj I I).
  - exact (conj I (conj I I)).
Qed.

(* ------------------------------------------------------------------ *)
(* Carrying a cut across a stretch that stores nothing                  *)
(* ------------------------------------------------------------------ *)

(* A visible byte of two memories with the same view is the same byte, whatever world each is read at. *)
Lemma ie2h_mbyte_keep : forall (W W' : world segs) m m' a (b : byte),
  aview segs (w_H W') m' a = aview segs (w_H W) m a ->
  mbyte segs (mrestrict (w_H W) m) a = Some b ->
  mbyte segs (mrestrict (w_H W') m') a = Some b.
Proof.
  intros W W' m m' a b E H. unfold aview in E. rewrite H in E. cbn [option_map] in E.
  destruct (mbyte segs (mrestrict (w_H W') m') a) as [b'|] eqn:E'; [|discriminate E].
  cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A garr8 array of the view survives a stretch that keeps its bytes. *)
Lemma ie2h_garr8_keep : forall (W W' : world segs) m m' base (l : list Z),
  (forall j, (j < length l)%nat ->
     aview segs (w_H W') m' (base + Z.of_nat j) = aview segs (w_H W) m (base + Z.of_nat j)) ->
  garr8 segs (mrestrict (w_H W) m) base l -> garr8 segs (mrestrict (w_H W') m') base l.
Proof.
  intros W W' m m' base l KV HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
  intros kk Hkk. assert (Ek : kk = 0%nat) by lia. subst kk.
  specialize (Hv 0%nat ltac:(lia)).
  rewrite Nat2Z.inj_0, Z.add_0_r in Hv |- *.
  exact (ie2h_mbyte_keep W W' m m' _ _ (KV j Hj) Hv).
Qed.

(* A step of the walk that changes only bytes of io_send's stack window or bytes of G in its written range keeps the
   running kept fact (lib/A/Prog/io_send_seg_csf.v ics_kept_step, at image B's names). *)
Lemma ie2h_kept_step : forall G lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 mem3 slo shi
    (E Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B G ->
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, Zs a -> (slo <= a < shi) \/ (inG G a /\ E a)) ->
  YM05.alloc_ceiling <= slo -> shi <= 2 ^ 47 ->
  acall_kept_g segs B G lyc Sc W memc W2 mem3 slo shi E.
Proof.
  intros G lyc Sc W memc mdc W2 mem2 mem3 slo shi E Zs LAWS HGX HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZ Hce Hhi.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (GLOW : forall a, inG G a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (inG_low segs B transportb_segs_low G a HGX Ha)).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hkp; [apply K1; [exact Ha | exact Hw] | lia |].
    intros HZa. destruct (HZ a HZa) as [Hs | [Hg _]]; [exact (Hw Hs) | pose proof (GLOW a Hg); lia].
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hlow.
    rewrite Hkp; [apply K3; [exact Hi | exact HnG | exact Hno | exact He] | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [Hg _]]; [lia | exact (HnG Hg)].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < YM05.alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Ha Hw Hp. apply Hgr. apply K5; [exact Ha | exact Hw | exact Hp].
  - intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

(* A stretch whose memory has the cut's view at every address keeps every memory fact of the cut: the saved words
   and the struct above sp, the frame wherever trans_src_ok places it, the shadow band and the harness globals. The
   journal and the registers the stretch moves to come from the stretch itself. *)
Lemma ie2h_keep : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) mem4 md4 (regs4 : bvmap 5 word) Bx,
  AR_laws segs B ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) mem4 a = aview segs (w_H W3) mem3 a) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly3 S3 W3 mem4 md4 ->
  ios_regs regs regs4 p frame fail ->
  (forall r, 24 <= r <= 27 -> YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem4 md4 regs4 Bx.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 mem4 md4 regs4 Bx LAWS HSP KV AT CUR RG R24.
  destruct AT as (CUR3 & SAVED & RG3 & R243 & SFR & SRCS & GARR & SRCF & HTW).
  assert (EF : IOSEND_FRAME = 160) by reflexivity.
  assert (EO : IOS_F_OFF = 8) by reflexivity.
  assert (ES : SF_SIZE = 80) by reflexivity.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof CUR3 as (HJ3 & _).
  assert (HAR3 : @AR rc segs B ly3 S3 W3 mem3 md3) by (eapply ajournal_gx_AR; exact HJ3).
  assert (KSH : forall s, kLowMemEnd <= s < kHighShadowEnd ->
                  aview segs (w_H W3) mem4 s = aview segs (w_H W3) mem3 s)
    by (intros s Hs; apply KV; lia).
  assert (KFR : forall a, p <= a < p + Z.of_nat (length frame) ->
                  aview segs (w_H W3) mem4 a = aview segs (w_H W3) mem3 a).
  { intros a Ha. apply KV.
    destruct (trans_src_ok_place B LAWS ly3 S3 W3 mem3 md3 p (Z.of_nat (length frame)) HAR3 SRCF
                ltac:(lia)) as [Pl|Pl]; lia. }
  split; [exact CUR|].
  split.
  { (* the saved words *)
    unfold ios_saved in SAVED |- *. rewrite Forall_forall in SAVED |- *. intros o Ho.
    assert (Hfo : 0 < fst o <= 72).
    { unfold IOS_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [Ho|Ho]; [subst o; cbn [fst]; lia|]). destruct Ho. }
    rewrite <- (SAVED o Ho). apply rdword_ext. intros kk Hkk. apply KV; lia. }
  split; [exact RG|]. split; [exact R24|].
  split.
  { (* the struct *)
    destruct SFR as (Hfp0 & Hfp8 & SB & HG & HL & HR). split; [exact Hfp0|]. split; [exact Hfp8|].
    exists SB. split; [|exact (conj HL HR)].
    refine (ie2h_garr8_keep W3 W3 mem3 mem4 _ _ _ HG). intros j Hj. rewrite length_map in Hj.
    apply KV; lia. }
  split.
  { exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4
            (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE SRCS
            (fun a Ha => KV a ltac:(lia)) KSH). }
  split.
  { (* the frame *)
    refine (ie2h_garr8_keep W3 W3 mem3 mem4 _ _ _ GARR). intros j Hj. rewrite length_map in Hj.
    apply KFR. lia. }
  split.
  { exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4 p (Z.of_nat (length frame)) SRCF KFR KSH). }
  (* the world *)
  apply (tw_kept TMAP_B (aview segs (w_H W3) mem3) _ Bx HTW).
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KV; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The fixed facts of the walk the two stretches read, and f.retry      *)
(* ------------------------------------------------------------------ *)

(* io_send's stack window, from the entry journal of io_send_seg_cut.v ios_fix. *)
Lemma ie2h_fix_of : forall STK sp0 FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs) memc mdc k
    regs p frame Bw,
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  YM05.alloc_ceiling <= spZ regs - IOSEND_STK /\ spZ regs <= 2 ^ 47.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HF.
  destruct HF as (HJ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite ?Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     (Hs16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
  split; lia.
Qed.

(* f.retry where the engine reads it: the struct's field through check_sent_frame_cg.v trans_sframe_at. *)
Lemma ie2h_cut_rty : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx,
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  YI04.val_mem segs (mrestrict (w_H W3) mem3) (spZ regs - IOSEND_FRAME + 38) 2 (ios_e2_rty frame) /\
  0 <= ios_e2_rty frame < 2 ^ 16.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail ly3 S3 W3 mem3 md3 regs3 Bx AT.
  destruct AT as (_ & _ & _ & _ & SFR & _).
  destruct SFR as (_ & _ & SB & HG & HL & _ & _ & _ & _ & _ & _ & HRTY & _).
  assert (EO : IOS_F_OFF = 8) by reflexivity.
  assert (ERTY : ios_e2_rty frame = TW.u_at SB 30 2) by (unfold ios_e2_rty; rewrite HRTY; reflexivity).
  pose proof (ie2h_val_of_garr8 (mrestrict (w_H W3) mem3) (spZ regs - IOSEND_FRAME + IOS_F_OFF) 30 SB 2 HG
                ltac:(lia) ltac:(rewrite HL; cbn; lia)) as R30.
  split.
  { rewrite ERTY. replace (spZ regs - IOSEND_FRAME + 38)
      with (spZ regs - IOSEND_FRAME + IOS_F_OFF + 30) by lia. exact R30. }
  pose proof (TWL.u_at_range SB 30 2) as Q1. change (8 * Z.of_nat 2) with 16 in Q1.
  rewrite ERTY. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The head: f.retry and its branch (0x830cc .. 0x830d0)                *)
(* ------------------------------------------------------------------ *)

Lemma ios_e2_head : @ios_e2_head_stmt fx rc B MT.
Proof.
  unfold ios_e2_head_stmt.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw fail cmd
    ly3 S3 W3 mem3 md3 regs3 Bx Q HL HFIX AT R10 KNZ KZ.
  pose proof HL as (_ & _ & _ & _ & LAWS & _ & HGX & _).
  destruct (ie2h_fix_of STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFIX) as (Hce & H47).
  pose proof HFIX as (HJc & _).
  assert (HARc : @AR rc segs B lyc Sc W memc mdc) by (eapply ajournal_gx_AR; exact HJc).
  clear HJc HFIX HL.
  pose proof AT as AT0.
  destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
  destruct (ie2h_cut_rty STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
              ly3 S3 W3 mem3 md3 regs3 Bx AT0) as (V38 & Z1).
  pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
  pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : IOSEND_STK = 8512) by reflexivity.
  assert (FF : IOSEND_FRAME = 160) by reflexivity.
  assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
  pose proof (ie2h_state IOS_E2DATA (spZ regs - IOSEND_FRAME) (ios_e2_rty frame)
                W3 regs3 mem3 R2 ltac:(lia) ltac:(lia) Z1 V38) as HS.
  set (E0 := ie2h_E regs3 (ios_e2_rty frame)) in HS.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ie2h_E; apply Eimg_env).
  assert (SHOK : sh_ok segs ie2h_Bx [] E0 (mrestrict (w_H W3) mem3)) by apply Forall_nil.
  assert (X32 : ew E0 32 = Z_to_bv 64 (ios_e2_rty frame))
    by (unfold E0, ie2h_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
  assert (ZR : 0 <= ios_e2_rty frame < 2 ^ 32)
    by (change (2 ^ 16) with 65536 in Z1; change (2 ^ 32) with 4294967296; lia).
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
                TG.G_HARNESS_B HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
                TG.G_HARNESS_B HGX 0 []) as RUNTO.
  pose proof (paj_branch (PI := PI_transportb)) as BR.
  unfold cfg_at.
  lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_E2DATA)) mem3
      (YK11.seg_rom segs)) md3) Qx) end.
  (* 0x830cc: the load of f.retry; it stops at `beq a1, zero` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ie2h_awr. }
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  rename ms into ms1.
  assert (KV : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
  { intros a Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx. cbv beta. ie2h_win Hin Hx ltac:(lia). }
  assert (GA : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (CUR1 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 (ms_mem ms1) md4).
  { unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ie2h_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 mem3 (ms_mem ms1)
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
      LAWS HGX HARc HKEPT ltac:(intros a Ha _; exact (KV a Ha)) GA ltac:(intros a []) Hce H47). }
  pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ie2h_kept HS (ie2h_agree regs3 _)
                ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  destruct (ie2h_regs_step regs regs3 (ms_regs ms1) p frame fail cmd RG R10 R24 KR)
    as (RG1 & R101 & R241).
  assert (AT1 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                  ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) Bx).
  { exact (ie2h_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
             ly3 S3 W3 mem3 md3 regs3 (ms_mem ms1) md4 (ms_regs ms1) Bx
             LAWS HSP KV AT0 CUR1 RG1 R241). }
  pose proof CUR1 as (HJ1 & HFR1 & HPM1 & HMO1 & HKEPT1).
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* f.retry = 0: the branch is taken, on to the 0xe2 test at 0x83108 *)
    rewrite (ie2h_den_zext16 E0 32 (ios_e2_rty frame) X32 Z1) in Hc.
    cbn [branch_taken sv_denot] in Hc. rewrite (ie2h_eqb0 _ ZR) in Hc. apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_E2T.
    { ie2h_awr. }
    set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
    rename ms into ms2.
    assert (KV2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. cbv beta. ie2h_win Hin Hx ltac:(lia). }
    assert (GA2 : forall a, apresent (w_H W3) (ms_mem ms1) a -> apresent (w_H W3) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    clear HF HFr HG.
    assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                     ly3 S3 W3 (ms_mem ms2) md5).
    { unfold ios_cur. split; [exact HJ|]. split; [exact HFR1|]. split; [exact HPM1|]. split; [exact HMO1|].
      apply (ie2h_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 (ms_mem ms1) (ms_mem ms2)
        (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
        LAWS HGX HARc HKEPT1 ltac:(intros a Ha _; exact (KV2 a Ha)) GA2 ltac:(intros a []) Hce H47). }
    pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ie2h_kept HS
                  (ie2h_agree regs3 _) ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    destruct (ie2h_regs_step regs regs3 (ms_regs ms2) p frame fail cmd RG R10 R24 KR2)
      as (RG2 & R102 & R242).
    assert (AT2 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                    ly3 S3 W3 (ms_mem ms2) md5 (ms_regs ms2) Bx).
    { exact (ie2h_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
               ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) (ms_mem ms2) md5 (ms_regs ms2) Bx
               LAWS HSP KV2 AT1 CUR2 RG2 R242). }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      change (SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_E2T) rg mm mdx) Q) end.
    exact (KZ _ _ _ AT2 R102 Hc).
  - (* f.retry <> 0: on to the retry arm at 0x830d4 *)
    rewrite (ie2h_den_zext16 E0 32 (ios_e2_rty frame) X32 Z1) in Hc.
    cbn [branch_taken sv_denot] in Hc. rewrite (ie2h_eqb0 _ ZR) in Hc. apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_RTY.
    { ie2h_awr. }
    set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
    rename ms into ms2.
    assert (KV2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. cbv beta. ie2h_win Hin Hx ltac:(lia). }
    assert (GA2 : forall a, apresent (w_H W3) (ms_mem ms1) a -> apresent (w_H W3) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    clear HF HFr HG.
    assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                     ly3 S3 W3 (ms_mem ms2) md5).
    { unfold ios_cur. split; [exact HJ|]. split; [exact HFR1|]. split; [exact HPM1|]. split; [exact HMO1|].
      apply (ie2h_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 (ms_mem ms1) (ms_mem ms2)
        (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
        LAWS HGX HARc HKEPT1 ltac:(intros a Ha _; exact (KV2 a Ha)) GA2 ltac:(intros a []) Hce H47). }
    pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ie2h_kept HS
                  (ie2h_agree regs3 _) ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    destruct (ie2h_regs_step regs regs3 (ms_regs ms2) p frame fail cmd RG R10 R24 KR2)
      as (RG2 & R102 & R242).
    assert (AT2 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                    ly3 S3 W3 (ms_mem ms2) md5 (ms_regs ms2) Bx).
    { exact (ie2h_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
               ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) (ms_mem ms2) md5 (ms_regs ms2) Bx
               LAWS HSP KV2 AT1 CUR2 RG2 R242). }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      change (SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_RTY) rg mm mdx) Q) end.
    exact (KNZ _ _ _ AT2 Hc).
Qed.

(* ------------------------------------------------------------------ *)
(* The 0xe2 test (0x83108 .. 0x8310c)                                   *)
(* ------------------------------------------------------------------ *)

Lemma ios_e2_test : @ios_e2_test_stmt fx rc B MT.
Proof.
  unfold ios_e2_test_stmt.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw fail cmd
    ly3 S3 W3 mem3 md3 regs3 Bx Q HL HFIX AT R10 HC256 KDATA KE2.
  pose proof HL as (_ & _ & _ & _ & LAWS & _ & HGX & _).
  destruct (ie2h_fix_of STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFIX) as (Hce & H47).
  pose proof HFIX as (HJc & _).
  assert (HARc : @AR rc segs B lyc Sc W memc mdc) by (eapply ajournal_gx_AR; exact HJc).
  clear HJc HFIX HL.
  pose proof AT as AT0.
  destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
  destruct (ie2h_cut_rty STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
              ly3 S3 W3 mem3 md3 regs3 Bx AT0) as (V38 & Z1).
  pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
  pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : IOSEND_STK = 8512) by reflexivity.
  assert (FF : IOSEND_FRAME = 160) by reflexivity.
  assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
  pose proof (ie2h_state IOS_E2T (spZ regs - IOSEND_FRAME) (ios_e2_rty frame)
                W3 regs3 mem3 R2 ltac:(lia) ltac:(lia) Z1 V38) as HS.
  set (E0 := ie2h_E regs3 (ios_e2_rty frame)) in HS.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ie2h_E; apply Eimg_env).
  assert (SHOK : sh_ok segs ie2h_Bx [] E0 (mrestrict (w_H W3) mem3)) by apply Forall_nil.
  assert (X10 : ew E0 10 = Z_to_bv 64 cmd)
    by (unfold E0, ie2h_E; rewrite (ew_Eimg_Ereg_nat regs3 _ 10%nat 10%bv eq_refl); exact R10).
  assert (DC : sv_denot E0 (SOff 10 0) = Z_to_bv 64 cmd) by exact (ie2h_den_off0 E0 10 cmd X10).
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
                TG.G_HARNESS_B HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
                TG.G_HARNESS_B HGX 0 []) as RUNTO.
  pose proof (paj_branch (PI := PI_transportb)) as BR.
  unfold cfg_at.
  lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_E2T)) mem3
      (YK11.seg_rom segs)) md3) Qx) end.
  (* 0x83108: a1 = 0xe2; it stops at `bne a0, a1` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ie2h_awr. }
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  rename ms into ms1.
  assert (KV : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
  { intros a Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx. cbv beta. ie2h_win Hin Hx ltac:(lia). }
  assert (GA : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (CUR1 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 (ms_mem ms1) md4).
  { unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ie2h_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 mem3 (ms_mem ms1)
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
      LAWS HGX HARc HKEPT ltac:(intros a Ha _; exact (KV a Ha)) GA ltac:(intros a []) Hce H47). }
  pose proof CUR1 as (HJ1 & HFR1 & HPM1 & HMO1 & HKEPT1).
  pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ie2h_kept HS (ie2h_agree regs3 _)
                ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  destruct (ie2h_regs_step regs regs3 (ms_regs ms1) p frame fail cmd RG R10 R24 KR)
    as (RG1 & R101 & R241).
  assert (AT1 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                  ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) Bx).
  { exact (ie2h_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
             ly3 S3 W3 mem3 md3 regs3 (ms_mem ms1) md4 (ms_regs ms1) Bx
             LAWS HSP KV AT0 CUR1 RG1 R241). }
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* f.cmd <> 0xe2: the branch is taken, the DATA arm's head at 0x83148 *)
    rewrite DC in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (ie2h_eqb_lit cmd 226 ltac:(lia) ltac:(lia)) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_DATA.
    { ie2h_awr. }
    set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
    rename ms into ms2.
    assert (KV2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. cbv beta. ie2h_win Hin Hx ltac:(lia). }
    assert (GA2 : forall a, apresent (w_H W3) (ms_mem ms1) a -> apresent (w_H W3) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    clear HF HFr HG.
    assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                     ly3 S3 W3 (ms_mem ms2) md5).
    { unfold ios_cur. split; [exact HJ|]. split; [exact HFR1|]. split; [exact HPM1|]. split; [exact HMO1|].
      apply (ie2h_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 (ms_mem ms1) (ms_mem ms2)
        (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
        LAWS HGX HARc HKEPT1 ltac:(intros a Ha _; exact (KV2 a Ha)) GA2 ltac:(intros a []) Hce H47). }
    pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ie2h_kept HS
                  (ie2h_agree regs3 _) ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    destruct (ie2h_regs_step regs regs3 (ms_regs ms2) p frame fail cmd RG R10 R24 KR2)
      as (RG2 & R102 & R242).
    assert (AT2 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                    ly3 S3 W3 (ms_mem ms2) md5 (ms_regs ms2) Bx).
    { exact (ie2h_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
               ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) (ms_mem ms2) md5 (ms_regs ms2) Bx
               LAWS HSP KV2 AT1 CUR2 RG2 R242). }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      change (SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_DATA) rg mm mdx) Q) end.
    exact (KDATA _ _ _ AT2 Hc).
  - (* f.cmd = 0xe2: on to the E2 arm (check_state_wake at 0x83110) *)
    rewrite DC in Hc. cbn [branch_taken sv_denot] in Hc.
    rewrite (ie2h_eqb_lit cmd 226 ltac:(lia) ltac:(lia)) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_E2ARM.
    { ie2h_awr. }
    set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
    rename ms into ms2.
    assert (KV2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin Hx. cbv beta. ie2h_win Hin Hx ltac:(lia). }
    assert (GA2 : forall a, apresent (w_H W3) (ms_mem ms1) a -> apresent (w_H W3) (ms_mem ms2) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    clear HF HFr HG.
    assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                     ly3 S3 W3 (ms_mem ms2) md5).
    { unfold ios_cur. split; [exact HJ|]. split; [exact HFR1|]. split; [exact HPM1|]. split; [exact HMO1|].
      apply (ie2h_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 (ms_mem ms1) (ms_mem ms2)
        (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) (fun _ => False)
        LAWS HGX HARc HKEPT1 ltac:(intros a Ha _; exact (KV2 a Ha)) GA2 ltac:(intros a []) Hce H47). }
    pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ie2h_kept HS
                  (ie2h_agree regs3 _) ltac:(vm_compute; reflexivity)) as KR2.
    cbn [ms_regs restrict] in KR2.
    destruct (ie2h_regs_step regs regs3 (ms_regs ms2) p frame fail cmd RG R10 R24 KR2)
      as (RG2 & R102 & R242).
    assert (AT2 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                    ly3 S3 W3 (ms_mem ms2) md5 (ms_regs ms2) Bx).
    { exact (ie2h_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
               ly3 S3 W3 (ms_mem ms1) md4 (ms_regs ms1) (ms_mem ms2) md5 (ms_regs ms2) Bx
               LAWS HSP KV2 AT1 CUR2 RG2 R242). }
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      change (SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_E2ARM) rg mm mdx) Q) end.
    exact (KE2 _ _ _ AT2 Hc).
Qed.

End e2.
