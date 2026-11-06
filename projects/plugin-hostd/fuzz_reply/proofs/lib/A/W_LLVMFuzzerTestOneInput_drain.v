(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput - the
   jump table's arm 2 (op_drain, fuzz_reply.c:596-609), from the arm's entry 0x84520 to the latch 0x84490, in the
   form of lib/A/W_LLVMFuzzerTestOneInput_cut.v's worked dispatch lf_seg_jt and of the loop walk
   lib/A/W_check_bounded.v (cb_loopX: a loop from a fresh symbolic state at its head, by induction on the trips
   left, spliced back with jafter_stretch_pi).
   The arm: relay_source(s->fd) scans g_src[0 .. g_nsrc) for the entry whose fd is the picked source's
   (0x84520-0x84584); with no entry, or with r->eof set, the operation is a no-op (0x846c8 / 0x84a40, both joining
   at 0x84a80); otherwise pthread_mutex_lock(&g_lock), drain(r), pthread_mutex_unlock(&g_lock),
   check_no_loss_read(s), check_no_loss(s, &at), check_shape_done(at) (0x84a44-0x84a7c), then the same join.
   The out-parameter `at` is the frame cell F+192: check_no_loss runs under its journal at XO = 208 with
   OUT = [(F+192, F+200)] (W_journal.v; the cell is inside the caller's own window, and ajournal_gx_sub carries it).
   The eof = 0 path is cut at the six return points into stages dc_stA .. dc_stF over dc_at (composed in dc_calls).
   What this file takes, and from whom (all Section hypotheses, none proved here):
     LAWS / HG / RINV / LS / the contract parameters - _cut's Section w, verbatim; GWR / ERR - _cut's glob_wr_law
       / errno_law, verbatim;
     TL : PALib B - the allocator instance (W_kit.v);
     DRAIN - W7's dr_spec B MT MMAX fr_RG, verbatim (lib/A/W_contract.v);
     ALOCK / AUNLOCK - W6's alock_realizes / aunlock_realizes (lib/A/W_sites.v), proved by R5
       (rt_pthread_mutex_lock / rt_pthread_mutex_unlock, a working branch);
     CSD - check_shape_done, proved (W_check_shape_done.v pb_check_shape_done);
     CNLR - W_contract.v's cnlr_spec, proved (W_check_no_loss_read.v pb_check_no_loss_read);
     CNL - check_no_loss, W3's cnl_spec as lib/A/W_contract.v Section w3n publishes it (the readable-stack premise
       LAST, passed from the cut's STKR by dr_stkr), at every G with gx_ok / gx_rt, taken at the slot's two list headers;
     the G-coverage and image facts (HGs, HG_DR, HGlock, HG_GK, HERR_HI, DR_ROM_OUT, HZS, HAP), and
     the model obligations RI_* / LS_* (pure, over lmod and the plain records). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the arm's addresses (offsets from fr_B0) *)
Definition A_dr_arm : Z := AF_arm_drain.                                (* 0x84520 the arm's entry *)
Definition A_dr_loop : Z := AF_fr_LLVMFuzzerTestOneInput + 0x4a0.       (* 0x84550 the table scan's head *)
Definition A_dr_nf : Z := AF_fr_LLVMFuzzerTestOneInput + 0x618.         (* 0x846c8 no entry for this fd *)
Definition A_dr_found : Z := AF_fr_LLVMFuzzerTestOneInput + 0x970.      (* 0x84a20 the entry found *)
Definition A_dr_join : Z := AF_fr_LLVMFuzzerTestOneInput + 0x9d0.       (* 0x84a80 the arm's join *)
(* the frame cells this arm uses: `at` (the out-parameter of check_no_loss) and in.n *)
Definition DR_AT : Z := 192.
Definition DR_N : Z := 144.
Definition DR_LK : Z := 40.
Definition DR_XO : Z := 208.

(* ------------------------------------------------------------------ the model side (plain records only) *)
Definition dr_e0 : rentry := RE 0 0 0 [] 0 0 0 0 0 [] [] [] [].
Fixpoint set_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | O, _ :: l' => x :: l'
  | S n', y :: l' => y :: set_nth n' x l'
  | _, [] => []
  end.
Lemma set_nth_length : forall (A : Type) n (x : A) l, length (set_nth n x l) = length l.
Proof.
  intros A n x l. revert n. induction l as [|y l IH]; intros [|n]; cbn [set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma set_nth_same : forall (A : Type) n (x : A) l d, (n < length l)%nat -> nth n (set_nth n x l) d = x.
Proof.
  intros A n x l d. revert n. induction l as [|y l IH]; intros [|n] Hn; cbn [set_nth length nth] in *;
    try lia; [reflexivity | apply IH; lia].
Qed.
Lemma set_nth_other : forall (A : Type) n p (x : A) l d, n <> p -> nth p (set_nth n x l) d = nth p l d.
Proof.
  intros A n. induction n as [|n IH]; intros [|p] x l d Hnp; destruct l as [|y l];
    cbn [set_nth nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.
(* ---- the bytes of the relay's table: entry i's 4-byte fd field, read out of atable_at ---- *)
(* With 4-byte paddings a source_t is 56 bytes. *)
Lemma entry_bytes_length : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.
Lemma concat_entry_length : forall es,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat length]. rewrite length_app, entry_bytes_length, IH by assumption. lia.
Qed.
(* byte k of entry i of the table is byte k of that entry *)
Lemma concat_entry_nth : forall es i k d,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (i < length es)%nat -> (k < 56)%nat ->
  nth (56 * i + k) (concat (map entry_bytes es)) d = nth k (entry_bytes (nth i es dr_e0)) d.
Proof.
  induction es as [|e es IH]; intros i k d HF Hi Hk; cbn [length] in Hi; [lia|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat]. destruct i as [|i].
  - replace (56 * 0 + k)%nat with k by lia. cbn [nth].
    apply app_nth1. rewrite entry_bytes_length by assumption. exact Hk.
  - rewrite app_nth2 by (rewrite entry_bytes_length by assumption; lia).
    rewrite entry_bytes_length by assumption.
    replace (56 * S i + k - 56)%nat with (56 * i + k)%nat by lia.
    cbn [nth]. apply IH; [exact HF | lia | exact Hk].
Qed.
Lemma nth_Z_to_le_bytes : forall n z k d, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k d Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
(* byte k of the 4-byte little-endian store of v, as val_mem reads it *)
Lemma le4_le_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0)) = YO0f.le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold Mem.le4. rewrite nth_Z_to_le_bytes by exact Hk.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 v) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by exact Hv. reflexivity.
Qed.
Lemma le_byte_1_byte : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by exact Hr. reflexivity.
Qed.
Lemma nth_bzs : forall l n, nth n (bzs l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  unfold bzs. induction l as [|b l IH]; intros [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.

(* ---- check_no_loss: W3's published contract is lib/A/W_contract.v Section w3n (capstep, capb, tbytes, hbytes,
   cnl_cap, cnl_room, gmc, cnl_go, cnl_cost, CNL_FRAME, CNL_STK, cnl_post, cnl_spec, A_g_s), cited; the STUB copied
   here from a working branch 553dcc19240 is gone (the published text adds the readable-stack premise LAST and an
   errno-view conjunct to cnl_post after apres_kept). ---- *)

(* ---- the transport kit, copied from W_LLVMFuzzerTestOneInput_latch.v Section kit (lt_ -> dr_, CEIL8 -> DR_CEIL8) ---- *)
Section dr_kit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* copied from W_LLVMFuzzerTestOneInput_latch.v CEIL8 *)
Definition DR_CEIL8 : Z := alloc_ceiling + 8.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low *)
Definition dr_fp_low (fp : list (Z * Z)) : Prop := Forall (fun r => 0 <= fst r /\ snd r <= DR_CEIL8) fp.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_ceil_lo *)
Lemma dr_ceil_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof asan_consts as (C1 & _). lia. Qed.
(* a bound on a range of fuzz_reply.asan's globals, or on errno from the premises *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_low *)
Ltac dr_low :=
  cbn [fst snd gfp]; unfold DR_CEIL8 in *;
  cbn [fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof dr_ceil_lo; lia.

(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_nil *)
Lemma dr_fp_low_nil : dr_fp_low []. Proof. constructor. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_cons *)
Lemma dr_fp_low_cons : forall r fp, 0 <= fst r -> snd r <= DR_CEIL8 -> dr_fp_low fp -> dr_fp_low (r :: fp).
Proof. intros r fp H1 H2 H3. constructor; [split; assumption | exact H3]. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_app *)
Lemma dr_fp_low_app : forall f1 f2, dr_fp_low f1 -> dr_fp_low f2 -> dr_fp_low (f1 ++ f2).
Proof. intros f1 f2 H1 H2. apply Forall_app. split; assumption. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_forall *)
Lemma dr_fp_low_forall : forall fp, dr_fp_low fp <-> (forall r, In r fp -> 0 <= fst r /\ snd r <= DR_CEIL8).
Proof. intros fp. unfold dr_fp_low. apply Forall_forall. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_fp_low_sub *)
Lemma dr_fp_low_sub : forall f1 f2, dr_fp_low f2 -> (forall r, In r f1 -> In r f2) -> dr_fp_low f1.
Proof. intros f1 f2 H Hs. rewrite dr_fp_low_forall in *. intros r Hr. exact (H r (Hs r Hr)). Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_akept_of_low *)
Lemma dr_akept_of_low : forall (W : world segs) mem (W' : world segs) mem' fp,
  (forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W' mem' a) -> dr_fp_low fp -> akept W mem W' mem' fp.
Proof.
  intros W mem W' mem' fp HK Hl r Hr a Ha. rewrite dr_fp_low_forall in Hl.
  destruct (Hl r Hr) as [H1 H2]. apply HK. lia.
Qed.

(* a live block: its bytes, and the 7 bytes of alignment slack a key's text may carry past them *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_blk *)
Lemma dr_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_bzs_len *)
Lemma dr_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_text_rec_len *)
Lemma dr_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_concat_len *)
Lemma dr_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, dr_text_rec_len, IH. cbn [length]. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_key_ptrs_len *)
Lemma dr_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.

(* ---- struct list ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_alist *)
Lemma dr_alist : forall ly S (W : world segs) mem md LA l lines,
  AR segs B ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= DR_CEIL8 ->
  dr_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : dr_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite dr_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (dr_blk ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite dr_bzs_len, length_app. cbn [length].
      unfold DR_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply dr_fp_low_cons; [cbn; lia | cbn; lia|]. apply dr_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply dr_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (dr_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply dr_fp_low_cons; [cbn; lia | | apply dr_fp_low_nil].
    cbn [gfp fst snd]. rewrite dr_bzs_len, length_app, dr_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold DR_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- struct source ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_asrc *)
Lemma dr_asrc : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= DR_CEIL8 ->
  dr_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (dr_alist ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (dr_alist ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (dr_alist ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (dr_blk ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply dr_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply dr_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite dr_bzs_len, Hpj. unfold APARTIAL, DR_CEIL8 in *. lia.
    + apply dr_fp_low_app; [exact A1|]. apply dr_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* ---- one source_t of the relay's table ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_aentry *)
Lemma dr_aentry : forall ly S (W : world segs) mem md e,
  AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  dr_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : dr_fp_low (map (fun k => gfp (gestures_end_b_c.key_addr k)
                  (bzs (gestures_end_b_c.key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (gestures_end_b_c.key_addr k,
                     Z.of_nat (length (gestures_end_b_c.key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite dr_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (dr_blk ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite dr_bzs_len, length_app. cbn [length].
      unfold DR_CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply dr_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply dr_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (dr_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply dr_fp_low_cons; [cbn; lia | | apply dr_fp_low_nil].
      cbn [gfp snd]. rewrite dr_bzs_len, length_app. unfold DR_CEIL8 in *. lia.
    + apply dr_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (dr_blk ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite dr_bzs_len, dr_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold DR_CEIL8. pose proof dr_ceil_lo. lia. }
        destruct (dr_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold DR_CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan's globals ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_arelay *)
Lemma dr_arelay : forall ly S (W : world segs) mem md G es,
  AR segs B ly S W mem md -> arelay_at B fr_globals ly S W mem G es ->
  dr_fp_low (arelay_fp fr_globals G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (dr_blk ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : dr_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite dr_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (dr_aentry ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite dr_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (dr_aentry ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply dr_fp_low_cons; [dr_low | dr_low|].
    apply dr_fp_low_cons; [dr_low | dr_low|].
    apply dr_fp_low_cons; [dr_low | dr_low|].
    apply dr_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, DR_CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_aout *)
Lemma dr_aout : forall ly S (W : world segs) mem md c O mx no cap out,
  AR segs B ly S W mem md -> aout_at B fr_globals ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= DR_CEIL8 ->
  dr_fp_low (aout_fp B fr_globals cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply dr_fp_low_cons; [dr_low | dr_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply dr_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (dr_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply dr_fp_low_cons; [cbn; lia | cbn; unfold DR_CEIL8 in *; lia | apply dr_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.
End dr_kit.

Section dr.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- _cut's Section w, verbatim ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* ------------------------------------------------------------------ the arm's own model notions *)
(* the input cursor after the operation's two bytes (lregs_D's k'), and the byte pick() took *)
Definition dr_k' (cx : lfcx) (m : lmod) : Z := if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1.
Definition dr_kb (cx : lfcx) (m : lmod) : Z := if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0.
(* the operation this arm runs: op = 2 at the cursor, nothing read yet in it *)
Definition dr_at_op (cx : lfcx) (m : lmod) : Prop :=
  0 <= lm_k m < c_n cx /\ lm_O m = [] /\ in_byte cx (lm_k m) mod 10 = 2.
(* the source pick() returned: slot si, holding h *)
Definition dr_pick (cx : lfcx) (m : lmod) (si : nat) (h : hsrc) : Prop :=
  pick (lm_hs m) (dr_kb cx m) = Some si /\ (si < 4)%nat /\ nth si (lm_hs m) None = Some h.
(* no relay entry before index i has the source's fd *)
Definition dr_nomatch (m : lmod) (h : hsrc) (i : Z) : Prop :=
  forall q, 0 <= q < i -> re_fd (nth (Z.to_nat q) (lm_es m) dr_e0) <> hs_fd h.
(* the model after an operation that did nothing but consume its input bytes *)
Definition dr_skip (m : lmod) (k : Z) : lmod :=
  LM k (lm_hs m) (lm_G m) (lm_es m) (lm_c m) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
(* the model after a drain of slot si / entry j *)
Definition dr_step (m : lmod) (k : Z) (si : nat) (h' : hsrc) (j : nat) (e' : rentry)
  (c' : ctl) (O' : list byte) (cap' out' : Z) : lmod :=
  LM k (set_nth si (Some h') (lm_hs m)) (lm_G m) (set_nth j e' (lm_es m)) c' O' (lm_mx m) cap' out'
     (lm_gn m) (lm_nfd m).

(* ------------------------------------------------------------------ the arm's register predicates *)
(* every state inside the arm keeps the loop's registers and the operation's number *)
Definition lregs_base (cx : lfcx) (t : Z) (FF : Z) (regs : bvmap 5 word) : Prop :=
  lregs_common B cx FF regs /\ getr regs 27 = w64 t /\ 0 <= t < OPS_MAX.
(* 0x84550, the table scan's head: a0 = s6 = &g_src[i], a1 = entries left, a2 = s->fd, a3 = its shadow;
   n is the trip count the induction runs on *)
Definition lregs_scan (cx : lfcx) (t : Z) (n : nat) (i : Z) (m : lmod) (FF : Z)
  (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) : Prop :=
  lregs_base cx t FF regs /\ dr_at_op cx m /\
  getr regs 28 = w64 (c_p cx + dr_k' cx m) /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
  (exists si h, dr_pick cx m si h /\
     getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\
     getr regs 12 = w64 (hs_fd h) /\ dr_nomatch m h i) /\
  0 <= i < Z.of_nat (length (lm_es m)) /\ Z.of_nat n = Z.of_nat (length (lm_es m)) - i /\
  getr regs 10 = w64 (lm_G m + AENT * i) /\ getr regs 22 = w64 (lm_G m + AENT * i) /\
  getr regs 11 = w64 (Z.of_nat (length (lm_es m)) - i) /\
  getr regs 13 = w64 (SB + lm_G m / 8 + 7 * i).
(* 0x846c8, no entry carries the source's fd *)
Definition lregs_nf (cx : lfcx) (t : Z) (m : lmod) (FF : Z)
  (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) : Prop :=
  lregs_base cx t FF regs /\ dr_at_op cx m /\
  getr regs 28 = w64 (c_p cx + dr_k' cx m) /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
  (exists si h, dr_pick cx m si h /\ dr_nomatch m h (Z.of_nat (length (lm_es m)))).
(* 0x84a20, the entry at index j carries the source's fd *)
Definition lregs_found (cx : lfcx) (t : Z) (j : nat) (m : lmod) (FF : Z)
  (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) : Prop :=
  lregs_base cx t FF regs /\ dr_at_op cx m /\
  getr regs 28 = w64 (c_p cx + dr_k' cx m) /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\
  (exists si h, dr_pick cx m si h /\
     getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\
     re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ dr_nomatch m h (Z.of_nat j)) /\
  (j < length (lm_es m))%nat /\
  getr regs 10 = w64 (lm_G m + AENT * Z.of_nat j) /\ getr regs 22 = w64 (lm_G m + AENT * Z.of_nat j).
(* 0x84a80, the arm's join: s9 carries the new in.p, s6 is about to take it, F+144 the new in.n;
   this is lregs_K's content with s9 not yet restored from F+104 *)
Definition lregs_join (cx : lfcx) (t : Z) (m : lmod) (FF : Z)
  (regs : bvmap 5 word) (W : world segs) (mem : word -> option byte) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (FF + 32) /\ getr regs 20 = w64 10 /\
  getr regs 23 = w64 HI_G_NSRC /\ getr regs 24 = w64 (SB + FF / 8) /\
  getr regs 26 = w64 SB /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 27 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 25 = w64 (c_p cx + lm_k m) /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - lm_k m) /\ 0 <= lm_k m <= c_n cx.


(* a state of the arm: a pc, the journal and the model of lcut, and a register predicate *)
Definition DST (pc : Z) (cx : lfcx) (t : Z)
  (R : lmod -> Z -> bvmap 5 word -> world segs -> (word -> option byte) -> Prop)
  : world segs -> config -> Prop :=
  fun W c => exists regs mem md, c = cfg_at segs (fr_B0 + pc) regs mem md /\
    jt_rom W mem /\ lcut B G_fr fr_FP LS RINV cx t true R regs mem md W.

(* ------------------------------------------------------------------ what the other lanes owe *)
Variable MMAX : Z.                                  (* W7's request bound, dr_spec's parameter *)
Hypothesis TL : PALib B.                            (* the allocator instance (W_kit.v) *)
(* W7, lib/A/W_contract.v, verbatim *)
Hypothesis DRAIN : dr_spec B MT MMAX fr_RG (BASE + AF_fr_drain).
(* W6's W_sites.v forms, proved by R5 (a working branch b1c048a98a5) *)
Hypothesis ALOCK : alock_realizes B (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes B (SIGMA WS_pthread_mutex_unlock).
(* proved: lib/A/W_check_shape_done.v pb_check_shape_done *)
Hypothesis CSD : csd_spec B (BASE + AF_fr_check_shape_done).
(* W_contract.v's cnlr_spec (W3's restated check_no_loss_read), verbatim: proved on this base by
   lib/A/W_check_no_loss_read.v:250 pb_check_no_loss_read (Qed). *)
Hypothesis CNLR : cnlr_spec B (BASE + AF_fr_check_no_loss_read).
(* check_no_loss: W3's cnl_spec (lib/A/W_contract.v Section w3n), at every G its proof takes:
   the G-dependent Section hypotheses of pb_check_no_loss are gx_ok SEGS B G and gx_rt B G (W_check_no_loss.v
   Section c).  The call site takes it at the slot's two list headers G = [(HA + 64, 32)]: a G covering the other
   three slots would let the callee change their bytes, and the other slots' asrc_at could not be carried. *)
Hypothesis CNL : forall G, gx_ok segs B G -> gx_rt B G -> cnl_spec B MT G MMAX (BASE + AF_fr_check_no_loss).

(* ---- the G-coverage facts: every global a callee writes is one of the entry's G_fr ---- *)
Hypothesis HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Hypothesis HG_DR : forall a, inG (G_DR B fr_RG) a -> inG G_fr a.
Hypothesis HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
(* the other cells of amodel_at are G_fr's too (so they are no allocator static: gx_ok); a callee's journal keeps
   them through its image clause *)
Definition DR_GK : list (Z * Z) :=
  [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4); (rg_send_max fr_RG, 8); (rg_client fr_RG, 4);
   (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1); (rg_wake fr_RG, 8); (AG_NFD, 4); (AG_THREAD_UP, 1);
   (AG_LISTEN, 4)].
Hypothesis HG_GK : forall a, inG DR_GK a -> inG G_fr a.
(* errno's cell (tp - 164, musl's static TLS: 0x5d93cc on image A) lies above every program global amodel_at
   names (g_out, the highest, ends at 0x5d8b48) *)
Hypothesis HERR_HI : rg_out fr_RG + 8 <= as_errno B.
(* _cut's errno_law, verbatim: errno's cell is readable and writable in every AR state.  check_no_loss_read,
   check_no_loss and check_shape_done keep no errno byte (their journals exclude it), so the stream's errno value
   is re-read after them *)
Hypothesis ERR : errno_law B.
(* W_journal.v's rom_out at G_fr (a working branch 45a3cc9bdd0's text): ROM is outside G_fr, errno and the
   sink's overflow head, and an owned ROM byte is pinned; so rom_view survives every callee's journal *)
Hypothesis DR_ROM_OUT : rom_out segs B G_fr.
(* _cut's glob_wr_law at G_fr, verbatim: a byte of G_fr is writable in every memory (so a kept view keeps it
   writable) *)
Hypothesis GWR : glob_wr_law G_fr.
(* g_s and the relay's buffers lie in the instance's zero-shadow ranges (globals of the image) *)
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
(* the image objects this arm reads are apart; vm_compute at PB_fr *)
Hypothesis HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
                 (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= rg_s fr_RG).

(* ---- the arm's open model obligations (pure, over lmod and the plain records) ---- *)
(* the operation did nothing: the relay has no entry for the source's fd, or its entry is at end of file *)
Hypothesis RI_drain_skip : forall cx t m si h,
  RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
   (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
      re_eof (nth j (lm_es m) dr_e0) = 1)) ->
  RINV cx (t + 1) (dr_skip m (dr_k' cx m)).
(* the operation drained entry j into slot si: the functional halves of W7's dr_post and W3's cnl_post.  The new
   entry's paddings (dr_post's aentry_ok), the expected list's capacity (dr_post) and the held list's capacity bound
   (cnl_post) are here because RINV's step needs them (W8Entry-2: the weaker step was measured false). *)
Definition dr_step_ok (cx : lfcx) (m : lmod) (si : nat) (h : hsrc) (j : nat)
  (e' : rentry) (h' : hsrc) (c' : ctl) (O' : list byte) (cap' out' : Z) (ev' : Z) (LB : list byte)
  (E' H' : hlist) : Prop :=
  let e := nth j (lm_es m) dr_e0 in
  let c := lm_c m in let mx := lm_mx m in let no := Z.of_nat (length (lm_O m)) in
  let cap := lm_cap m in let out := lm_out m in
  let fin := dr_fin c mx no cap e h in
  let live := dr_live c h in
  (* drain's functional half *)
  re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
  re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
  re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
  drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
  NoDup (drain_b_c.keys_texts (re_keys e')) /\
  same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
  hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
  hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
  hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
  map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
  hs_held h' = hs_held h /\
  re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
  bzs LB = with_nul (dr_lines h) /\
  c' = dr_ctl c h ev' /\ O' = (if live then lm_O m ++ LB else lm_O m) /\
  cap' = (if live then drain_b_c.ds_ocap fin else cap) /\
  length (re_pad1 e') = 4%nat /\ length (re_pad2 e') = 4%nat /\
  hl_cap (hs_expected h') = drain_b_c.ds_ecap fin /\
  (* check_no_loss's functional half, over the drained source *)
  hl_recs E' = [] /\ hl_v E' = hl_v (hs_expected h') /\ hl_cap E' = hl_cap (hs_expected h') /\
  NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h')) (texts (hs_expected h')) /\
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h'))
                              (2 * (hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h')))))).
Hypothesis RI_drain_step : forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
  RINV cx t m -> 0 <= t < OPS_MAX ->
  hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h'))) < 2 ^ 22 ->
  dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
  RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out').
(* ---- the model facts the callees' premises need, read off RINV (projections, not steps) ---- *)
(* the picked source at the top of an operation: check_no_loss emptied its expected list, its held texts are
   distinct (the plain proof's pair_ok, Prog/SlotInv.v:253-263) *)
Hypothesis RI_src : forall cx t m si h,
  RINV cx t m -> dr_pick cx m si h ->
  hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31.
(* the open sources have distinct fds (so drain's aothers_at holds of the other three slots) *)
Hypothesis RI_fds : forall cx t m i1 i2 h1 h2,
  RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
(* the relay's entry for an open source it still reads, and the source, agree (pair_ok's re_eof = 0 clauses) *)
Hypothesis RI_pair : forall cx t m si h j,
  RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
  re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
  (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
  length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat.
(* the controller went away exactly when it is closed, broken or dead (the plain proof's slot invariant over the
   output flags: g_gone = 0 means a live, unbroken, connected controller), so check_no_loss's `gone = 0` stream
   premise and check_shape_done's at = g_nout hold after the drain *)
Hypothesis RI_gone : forall cx t m,
  RINV cx t m ->
  (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
  (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1).
(* an entry holds re_nheld keys by definition (RelayRep.v re_nheld), so aentry_ok's 8 * re_nheld <= re_kh puts the
   key pointer array inside its block *)
Lemma dr_keys_le : forall e, Z.of_nat (length (re_keys e)) <= re_nheld e.
Proof. intros e. unfold re_nheld. lia. Qed.

(* ---- the allocator-state facts the two calls take, read off LS; the instance discharges them ---- *)
(* the peak form (a Theorem Labs lane's ROOM-ROUND row #19; dr_spec's byte premise is the drain trace's byte PEAK, C3): conjunct 5
   is s5-r1d's fr_LS_drain_pre_c5p (lib/A/ReplyTrPeak.v:927), and the three premises after re_eof are the ones its
   rows take (fr_LS3_drain_pre_c4 ReplyLS3Arms.v:791, fr_LS_drain_pre_c5p): dc_regs' Ht, aentry_ok's |re_U| bound and
   the drained blocks' sizes (dc_stB's HXP).  The sum form (tr_alloc) was FALSE at reachable states. *)
Hypothesis LS_drain_pre : forall cx t m ly S si h j,
  LS cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  0 <= t < OPS_MAX ->
  Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
  (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
     0 < snd b) ->
  Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  hl_cap (hs_expected h) < 2 ^ 26 /\
  re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
  tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < MMAX /\
  blocks_bytes S +
    tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
    <= LIVE_MAX /\
  mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h).
(* after the drain: what check_no_loss takes of the state it is called in *)
Hypothesis LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'',
  LS cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
  (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
  re_eof (nth j (lm_es m) dr_e0) = 0 ->
  mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                   (nth j (lm_es m) dr_e0) h) ->
  hl_cap (hs_expected h'') = drain_b_c.ds_ecap
    (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  map snd (hl_recs (hs_expected h'')) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
  hs_held h'' = hs_held h ->
  NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
  hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
  cnl_room MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h'')) (hl_recs (hs_expected h'')) /\
  mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h'')) /\
  AREC * capb (hs_held h'') (hs_expected h'') < 2 ^ 32.
(* the two steps of the allocator-state invariant *)
Hypothesis LS_drain_skip : forall cx t m ly S,
  LS cx t m ly S -> LS cx (t + 1) (dr_skip m (dr_k' cx m)) ly S.
(* the drain charges the meter dr_cost of the entry and source it was called with (S to S1), check_no_loss
   cnl_cost of the lists it was called with (S1 to S'); lock, unlock, check_no_loss_read and check_shape_done
   keep the allocator state *)
Hypothesis LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
    si h j h'' e' c' O' cap' out' (E H : hlist),
  LS cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
  mo_le MT S S1
    (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
  mo_le MT S1 S' (cnl_cost MT E H) ->
  LS cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'.


(* ------------------------------------------------------------------ the pieces *)
(* ---- the transport kit, part 2: copied from W_LLVMFuzzerTestOneInput_latch.v Section w (lt_ -> dr_) ---- *)
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_akept_rng *)
Lemma dr_akept_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= DR_CEIL8 ->
  akept W mem W' mem' [(lo, hi)].
Proof.
  intros W W' mem mem' lo hi HK H1 H2. apply dr_akept_of_low; [exact HK|].
  apply dr_fp_low_cons; [cbn; lia | cbn; lia | apply dr_fp_low_nil].
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_akept_of_rng *)
Lemma dr_akept_of_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= DR_CEIL8 ->
  forall x, lo <= x < hi -> abyte_kept W mem W' mem' x.
Proof. intros W W' mem mem' lo hi HK H1 H2 x Hx. apply HK. lia. Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_amodel_kept *)
Lemma dr_amodel_kept : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= DR_CEIL8 ->
  (forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= DR_CEIL8)
      by (unfold fr_RG, DR_CEIL8; cbn; unfold ASRC; pose proof dr_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (dr_asrc B LAWS ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (dr_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (dr_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (dr_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (dr_arelay B LAWS ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_globals ly S W mem ly S W' mem' _ _ M3
             (dr_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (dr_aout B LAWS ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_globals ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (dr_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_globals W mem W' mem' _ M5).
    apply dr_akept_rng; [exact KEEP | cbn; lia | unfold DR_CEIL8; cbn; pose proof dr_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_globals W mem W' mem' _ M6).
    apply dr_akept_rng; [exact KEEP | cbn; lia | unfold DR_CEIL8; cbn; pose proof dr_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_globals W mem W' mem' M7).
    apply dr_akept_rng; [exact KEEP | cbn; lia | unfold DR_CEIL8; cbn; pose proof dr_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, DR_CEIL8 in *. pose proof dr_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, DR_CEIL8 in *. pose proof dr_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, DR_CEIL8 in *. pose proof dr_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, DR_CEIL8 in *. pose proof dr_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, DR_CEIL8 in *. pose proof dr_ceil_lo. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_sv8_kept *)
Lemma dr_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_ainput_kept *)
Lemma dr_ainput_kept : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR segs B ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (dr_blk B LAWS ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold DR_CEIL8. lia.
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_rom_kept *)
Lemma dr_rom_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> (forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W' mem' a) ->
  rom_view segs W' mem'.
Proof.
  intros W W' mem mem' HR KEEP a Ha. rewrite <- (HR a Ha).
  assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
  pose proof (pa_segs_low a Hin) as Hlow. pose proof dr_ceil_lo.
  exact (proj1 (KEEP a ltac:(unfold DR_CEIL8, kLowMemEnd in *; lia))).
Qed.
(* copied from W_LLVMFuzzerTestOneInput_latch.v lt_jt_kept *)
Lemma dr_jt_kept : forall (W W' : world segs) mem mem',
  jt_rom W mem -> (forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W' mem' a) -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HJ KEEP i Hi. apply (akept_vm W mem); [|exact (HJ i Hi)].
  intros x Hx. apply KEEP. unfold fr_jtab, DR_CEIL8 in *. pose proof dr_ceil_lo. cbn in Hx. lia.
Qed.

(* ---- dr_entry's own helpers (de_) ---- *)
(* a byte present before a run that only grows the memory is present after it
   (the proof of W_LLVMFuzzerTestOneInput_small.v sm_pres_grows) *)
Lemma de_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.
(* pick() returns an open slot *)
Lemma de_pick_from : forall hs j k i, pick_from hs j k = Some i ->
  (j <= i < j + length hs)%nat /\ exists h, nth (i - j) hs None = Some h.
Proof.
  induction hs as [|o hs IH]; intros j k i Hp; [discriminate Hp|].
  cbn [pick_from] in Hp. destruct o as [h|].
  - destruct (k =? 0).
    + injection Hp as <-. cbn [length]. split; [lia|]. exists h. rewrite Nat.sub_diag. reflexivity.
    + destruct (IH (S j) (k - 1) i Hp) as [Hr [h' Hh']]. cbn [length]. split; [lia|].
      exists h'. replace (i - j)%nat with (S (i - S j)) by lia. exact Hh'.
  - destruct (IH (S j) k i Hp) as [Hr [h' Hh']]. cbn [length]. split; [lia|].
    exists h'. replace (i - j)%nat with (S (i - S j)) by lia. exact Hh'.
Qed.
Lemma de_pick_some : forall hs kb i, pick hs kb = Some i ->
  (i < length hs)%nat /\ exists h, nth i hs None = Some h.
Proof.
  intros hs kb i Hp. unfold pick in Hp. destruct (nopen hs =? 0); [discriminate Hp|].
  destruct (de_pick_from hs 0 (kb mod nopen hs) i Hp) as [Hr [h Hh]].
  rewrite Nat.sub_0_r in Hh. split; [lia | exists h; exact Hh].
Qed.
(* the frame across a run whose only store is the in.n cell [F+144, F+152) (the shape of
   W_LLVMFuzzerTestOneInput_latch.v lt_aframe_kept, with this arm's window) *)
Lemma de_aframe_kept : forall cx full FF (W W' : world segs) mem mem',
  aframe_at cx full FF W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) -> abyte_kept W mem W' mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  DR_CEIL8 <= lf_F cx -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= DR_CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= DR_CEIL8 ->
  aframe_at cx full FF W' mem'.
Proof.
  intros cx full FF W W' mem mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    HK WK HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof dr_ceil_lo as HCL. unfold DR_N, DR_CEIL8 in *.
  assert (KW : forall a n, awr W mem a n -> awr W' mem' a n) by (intros a n Hw i Hi; apply WK; exact (Hw i Hi)).
  assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= lf_F cx + 144 \/ lf_F cx + 152 <= a) ->
             sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 H2 Hv. apply (dr_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply HK; lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | exact (A1 o r Hin)]. }
  split; [exact (KW _ _ A2)|].
  do 9 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    do 6 (split; [apply KV; [lia | lia | lia | assumption]|]).
    apply KV; [lia | lia | lia | assumption]. }
  do 3 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split; [exact (KW _ _ A16)|].
  split; [|exact (KW _ _ (proj2 A17))].
  apply (akept_garr8 W mem); [|exact (proj1 A17)]. intros x Hx.
  unfold fake_shadow in Hx. cbn [length] in Hx. apply HK; lia.
Qed.
(* the arm's entry state 0x84520: the in.n cell F+144 (written), s->fd at s5, g_nsrc and g_src (the listing's
   PLdHi loads through s7 = auipc 74 and s2 = auipc 75, so those two registers hold their A_HI atoms); s10 = SB
   is the shadow base; atoms 32-34 hold s->fd, g_nsrc and g_src *)
Lemma de_hi : VAL (A_HI 74) = HI_G_NSRC /\ VAL (A_HI 75) = HI_G_SRC /\ VAL (A_OBJ 7) = rg_nsrc fr_RG /\
  VAL (A_OBJ 8) = rg_src fr_RG.
Proof. vm_compute. repeat split. Qed.
Definition de_sr : list sv := sr_set (sr_set sr_atoms 23 (SOff (A_HI 74) 0)) 18 (SOff (A_HI 75) 0).
Definition de_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 144 152 144 152 [];
    YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
    YP09.mkRegion (Some (A_OBJ 7)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))];
    YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))] ].
Definition de_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (21%nat, mkAF 4096 140737479966720 3); (26%nat, mkAF SB SB 0);
            (32%nat, mkAF 0 (2 ^ 31 - 1) 0); (33%nat, mkAF 0 16 0) ] [] [].
Definition ss_de : sstate := mkSS A_dr_arm de_sr de_regions None de_facts.
Definition de_SH : list shent := [ mkSHE 21 0 4 ].
Definition de_Bx : sv := SOff 26 0.
Definition de_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition de_extra (fd n G : Z) : list word := map (Z_to_bv 64) [fd; n; G].
(* the registers the entry does not write on either path (s2 and s7 hold image atoms, read with prreg) *)
Definition DE_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 21; 24; 25; 26; 27; 28; 29]%bv.
Let de_RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let de_RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let de_BR := paj_branch (PI := PB_fr).
(* a run's write obligation: the in.n cell is in the function's own stack window, the other regions are read-only *)
Ltac de_awr U9 :=
  cbn [ss_mem add_cond ss_de de_regions];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the in.n cell is outside every region's writable window *)
Ltac de_nowr U9 Hna :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_de de_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr; unfold DR_N in Hna; lia | ]);
  destruct Hin.


(* everything lcut says of the memory, carried across the entry's runs (their only store is the in.n cell) *)
Lemma de_carry : forall cx (W : world segs) mem mem' md ly3 S3 fpos m,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx W mem mem' md ly3 S3 fpos m HAR Hfin Hlen Hsp HFR HMOD HIN HRV HJT KEEP WK.
  pose proof dr_ceil_lo as HCL. pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold DR_N, DR_CEIL8 in *; lia. }
  split.
  { apply (de_aframe_kept cx true _ W W mem mem' HFR KEEP WK); unfold DR_CEIL8, SB in *; lia. }
  split; [exact (dr_amodel_kept ly3 S3 W mem md W mem' m HAR HMOD HE0
                   ltac:(unfold DR_CEIL8, kLowMemEnd in *; lia) KL)|].
  split; [exact (dr_ainput_kept cx ly3 S3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (dr_rom_kept W W mem mem' HRV KL)|].
  exact (dr_jt_kept W W mem mem' HJT KL).
Qed.
(* the fake frame's flag word (lcut's conjunct after aframe_at), across the same keep as de_carry's *)
Lemma de_flag_kept : forall cx (W : world segs) mem mem' md ly3 S3 fpos,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) -> abyte_kept W mem W mem' a) ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  sv8 W mem' (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos).
Proof.
  intros cx W mem mem' md ly3 S3 fpos HAR Hfin Hsp KEEP Hv.
  pose proof dr_ceil_lo as HCL.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. cbn in Hx. apply KEEP; unfold DR_N, DR_CEIL8 in *; lia.
Qed.

(* (1) the relay's table in memory: the fd field of entry i, from atable_at. *)
Lemma dr_tbl_fd : forall (W : world segs) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (i : nat),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  (i < length es)%nat ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat i) 4 (re_fd (nth i es dr_e0)).
Proof.
  intros W mem G es tail i [_ [_ Hg]] Hpad Hfd Hi.
  assert (Hv : 0 <= re_fd (nth i es dr_e0) < 2 ^ 31).
  { rewrite Forall_forall in Hfd. apply Hfd. apply nth_In. exact Hi. }
  pose proof (concat_entry_length es Hpad) as Hcl.
  unfold val_mem. intros k Hk.
  assert (Hj : (56 * i + k < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
  { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
  unfold garr8 in Hg. destruct (Hg _ Hj) as [Hb _]. unfold val_mem in Hb.
  specialize (Hb 0%nat ltac:(lia)).
  replace (G + AENT * Z.of_nat i + Z.of_nat k) with (G + Z.of_nat (56 * i + k) + Z.of_nat 0)
    by (unfold AENT; lia).
  rewrite Hb. f_equal.
  assert (Hn : nth (56 * i + k) (bzs (concat (map entry_bytes es) ++ tail)) 0 =
               bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 (re_fd (nth i es dr_e0)))) (Z_to_bv 8 0))).
  { rewrite nth_bzs. f_equal.
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite concat_entry_nth by (first [exact Hpad | exact Hi | lia]).
    unfold entry_bytes. rewrite app_nth1 by (rewrite Mem.length_le4; exact Hk). reflexivity. }
  rewrite Hn, le_byte_1_byte.
  apply bv_eq. rewrite Z_to_bv_unsigned, le4_le_byte by lia.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* the paddings and the fd range of every entry, from the relay's representation (aentry_ok) *)
Lemma dr_pads_of_relay : forall ly S W mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es /\
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es.
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  split; rewrite Forall_forall in HE |- *; intros e He;
    destruct (HE e He) as (_ & _ & H3 & H4 & H5 & _); [split; assumption | exact H5].
Qed.

(* ---- (DrainScan) the entry state of the scan's head 0x84550 ----
   a0 = s6 = &g_src[i] (the body reads only the 4-byte fd at its start), a1 = the entries left, a2 = s->fd,
   a3 = SB + (G + 56 i)/8 the shadow cell of the entry.  The entry lies inside the table's 896-byte block, so
   its granule is addressable and the shadow check at 0x84550-0x84554 is decided inside the run: the partial
   test at 0x84578 never appears. *)
Let ds_RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let ds_RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let ds_BR := paj_branch (PI := PB_fr).
Definition ds_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ds_Bx : sv := SOff 26 0.
Definition ds_sr : list sv :=
  sr_set sr_atoms 13 (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 22 0) (SLit 3))).
Definition ds_regions : smem :=
  [ YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))] ].
Definition ds_facts : facts :=
  mkFacts [ (22%nat, mkAF 4096 140737479966720 3); (26%nat, mkAF SB SB 0);
            (32%nat, mkAF 0 (2 ^ 31 - 1) 0) ] [] [].
Definition ss_ds : sstate := mkSS A_dr_loop ds_sr ds_regions None ds_facts.
Definition ds_SH : list shent := [ mkSHE 22 0 8 ].
Definition ds_extra (u : Z) : list word := map (Z_to_bv 64) [u].
(* the registers the body leaves alone: a0, a1, a3, a4 and s6 move *)
Definition DS_KEPT : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* a run over read-only regions leaves the memory as it was *)
Ltac ds_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Lemma ds_add_lit : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma ds_common_kept : forall cx FF (regs regs' : bvmap 5 word),
  (forall r, In r DS_KEPT -> getr regs' r = getr regs r) ->
  lregs_common B cx FF regs -> lregs_common B cx FF regs'.
Proof.
  intros cx FF regs regs' HK H. unfold lregs_common in H |- *.
  destruct H as (A2 & A8 & A9 & A18 & A19 & A20 & A23 & A24 & A25 & A26 & A3 & A4).
  rewrite (HK 2%bv ltac:(cbv; tauto)), (HK 8%bv ltac:(cbv; tauto)), (HK 9%bv ltac:(cbv; tauto)),
          (HK 18%bv ltac:(cbv; tauto)), (HK 19%bv ltac:(cbv; tauto)), (HK 20%bv ltac:(cbv; tauto)),
          (HK 23%bv ltac:(cbv; tauto)), (HK 24%bv ltac:(cbv; tauto)), (HK 25%bv ltac:(cbv; tauto)),
          (HK 26%bv ltac:(cbv; tauto)), (HK 3%bv ltac:(cbv; tauto)), (HK 4%bv ltac:(cbv; tauto)).
  repeat split; assumption.
Qed.
Lemma ds_base_kept : forall cx t FF (regs regs' : bvmap 5 word),
  (forall r, In r DS_KEPT -> getr regs' r = getr regs r) ->
  lregs_base cx t FF regs -> lregs_base cx t FF regs'.
Proof.
  intros cx t FF regs regs' HK H. unfold lregs_base in H |- *.
  destruct H as (HC & H27 & Ht).
  split; [exact (ds_common_kept cx FF regs regs' HK HC)|].
  split; [rewrite (HK 27%bv ltac:(cbv; tauto)); exact H27 | exact Ht].
Qed.
(* no entry before i + 1 carries the fd, from no entry before i and entry i's own fd *)
Lemma ds_nomatch_step : forall m h i,
  dr_nomatch m h i -> 0 <= i -> re_fd (nth (Z.to_nat i) (lm_es m) dr_e0) <> hs_fd h ->
  dr_nomatch m h (i + 1).
Proof.
  intros m h i HN Hi Hne q Hq. destruct (Z.eq_dec q i) as [->|Hq2]; [exact Hne|].
  apply HN. lia.
Qed.

(* (2) the table scan 0x84550-0x84584, by induction on the entries left. *)
Lemma dr_scan : forall n cx t i W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  DST A_dr_loop cx t (lregs_scan cx t n i) W c ->
  SRr segs W c (fun W' c' => (exists j, DST A_dr_found cx t (lregs_found cx t j) W' c') \/
                             DST A_dr_nf cx t (lregs_nf cx t) W' c').
Proof.
  intros n. induction n as [|n IH]; intros cx t i W c HB HD;
    destruct HD as (regs & mem & md & -> & HROM & HLC);
    destruct HLC as (own & ly3 & S3 & kk & m & fpos & HJ & Hown & HFRM & HFLM & HMOD & HINP & HRV & HBLK & HLS & HRI & HREG);
    unfold lregs_scan in HREG;
    destruct HREG as (HBASEr & HATOP & H28 & HSV8 & (sl & h & HPICK & H21 & H12 & HNM) & Hi & Hnn & H10 & H22 & H11 & H13).
  { exfalso. lia. }
  (* ---- the model side: the table's block, the fd of entry i, the picked source's fd ---- *)
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof (proj1 (proj2 (proj2 HMOD))) as HREL.
  pose proof HREL as HREL2.
  destruct HREL2 as (_ & _ & _ & _ & _ & _ & Hle16 & HGin & (tl & HTAB) & _ & _).
  destruct (dr_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS).
  assert (Hle16Z : Z.of_nat (length (lm_es m)) <= 16) by lia.
  assert (Hin : (Z.to_nat i < length (lm_es m))%nat) by lia.
  pose proof (dr_tbl_fd W mem (lm_G m) (lm_es m) tl (Z.to_nat i) HTAB HPAD HFDS Hin) as Mu.
  rewrite Z2Nat.id in Mu by lia.
  assert (Hfdb : 0 <= re_fd (nth (Z.to_nat i) (lm_es m) dr_e0) < 2 ^ 31)
    by (rewrite Forall_forall in HFDS; apply HFDS, nth_In; lia).
  destruct (RI_src cx t m sl h HRI HPICK) as (_ & _ & Hhfd).
  unfold AENT in Mu, H10, H22.
  destruct (al_blocks _ _ LAWS ly3 S3 W mem md (lm_G m) ATABLE HAR HGin) as (HP16 & HP4096 & HPceil & HPapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity.
  rewrite RQ in HPceil, HPapp.
  assert (G8 : lm_G m = 8 * (lm_G m / 8)).
  { pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
    rewrite D at 2. replace (16 * (lm_G m / 16)) with ((2 * (lm_G m / 16)) * 8) by ring.
    rewrite Z.div_mul by lia. lia. }
  assert (XQ : (lm_G m + 56 * i) / 8 = lm_G m / 8 + 7 * i).
  { rewrite G8 at 1. replace (8 * (lm_G m / 8) + 56 * i) with ((lm_G m / 8 + 7 * i) * 8) by ring.
    apply Z.div_mul. lia. }
  pose proof HBASEr as HBASE2. unfold lregs_base in HBASE2.
  destruct HBASE2 as (HCOM & H27 & Ht).
  pose proof HCOM as HCOM2. unfold lregs_common in HCOM2.
  destruct HCOM2 as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4).
  (* ---- the entry state at the head ---- *)
  remember (Eimg (Ereg regs (ds_extra (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0))))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (ds_extra (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0)))) E)
    by (rewrite HE; split; [intros mm Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall mm (rr : bv 5), Z.of_nat mm = bv_unsigned rr -> ew E mm = getr regs rr)
    by (intros mm rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hm).
  assert (E10 : ew E 10 = Z_to_bv 64 (lm_G m + 56 * i)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat (length (lm_es m)) - i))
    by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 (hs_fd h)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
  assert (E22 : ew E 22 = Z_to_bv 64 (lm_G m + 56 * i)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 22 0) (SLit 3)))
                = SB + lm_G m / 8 + 7 * i).
  { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 22 _ E22), U_lit by (unfold SB; lia). cbn [zalu_raw].
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
    rewrite XQ. rewrite (Z.mod_small (lm_G m / 8 + 7 * i)) by lia.
    rewrite Z.mod_small by (unfold SB; lia). lia. }
  assert (HS : st_ok_pi segs VAL E ss_ds
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_loop)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_ds. apply pa_entry_st_ok_full.
    - unfold ds_sr. rewrite HE. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
      rewrite <- HE, H13. apply bv_eq.
      fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 22 0) (SLit 3)))). rewrite USH.
      apply unsigned_lit_small. unfold SB; lia.
    - vm_compute. reflexivity.
    - unfold ds_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite E22, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ (lm_G m + 56 * i) 0 4 (SOff 32 0)
               (re_fd (nth (Z.to_nat i) (lm_es m) dr_e0)));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Mu.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [ds_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E22, E26, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia).
      rewrite G8. replace (8 * (lm_G m / 8) + 56 * i) with ((lm_G m / 8 + 7 * i) * 8) by ring.
      apply Z_mod_mult. }
  clear HE.
  assert (HBx : U E ds_Bx = SHADOW_OFF)
    by (unfold ds_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs ds_Bx ds_SH E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    + apply (range_addressable_of_block segs B LAWS ly3 S3 W mem md (lm_G m) ATABLE
               (lm_G m + 56 * i) 8 HAR HGin); rewrite ?RQ; lia.
    + exact HBx.
    + rewrite (U_atom E 22 _ E22) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  unfold cfg_at. change (w64 (fr_B0 + A_dr_loop)) with (Z_to_bv 64 (BASE + A_dr_loop)).
  (* ---- 0x84550-0x8455c: the shadow check, the load of the entry's fd, and the match test ---- *)
  paj_run_tok ds_RUN HS HJ SHOK ds_span.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  ds_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok ds_RUN ds_BR HS SHOK ds_span.
  - (* 0x8455c beq taken: entry i carries the source's fd - on to 0x84a20 *)
    rewrite branch_eq_U, (U_atom E 32 _ E32), (U_atom E 12 _ E12) in Hc by lia.
    apply Z.eqb_eq in Hc.
    paj_run_to_tok ds_RUNTO HS HJ SHOK ds_span A_dr_found.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    ds_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DS_KEPT HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (10%bv : bv 5) N10. prreg HS (22%bv : bv 5) N22.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply SRr_ret. left. exists (Z.to_nat i).
    lazymatch goal with |- DST _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
    split; [reflexivity|]. split; [exact HROM|].
    exists own, ly3, S3, kk, m, fpos.
    split; [exact HJ|]. split; [exact Hown|]. split; [exact HFRM|]. split; [exact HFLM|]. split; [exact HMOD|].
    split; [exact HINP|]. split; [exact HRV|]. split; [exact HBLK|]. split; [exact HLS|].
    split; [exact HRI|].
    unfold lregs_found.
    split; [exact (ds_base_kept cx t _ regs _ KR HBASEr)|].
    split; [exact HATOP|].
    split; [rewrite (KR 28%bv ltac:(cbv; tauto)); exact H28|].
    split; [exact HSV8|].
    split.
    { exists sl, h. split; [exact HPICK|].
      split; [rewrite (KR 21%bv ltac:(cbv; tauto)); exact H21|].
      split; [exact Hc|]. rewrite Z2Nat.id by lia. exact HNM. }
    split; [exact Hin|].
    split.
    + rewrite N10, E10. unfold w64, AENT. rewrite Z2Nat.id by lia. reflexivity.
    + rewrite N22, E22. unfold w64, AENT. rewrite Z2Nat.id by lia. reflexivity.
  - (* 0x8455c beq not taken: entry i is not the one *)
    rewrite branch_eq_U, (U_atom E 32 _ E32), (U_atom E 12 _ E12) in Hc by lia.
    apply Z.eqb_neq in Hc.
    paj_run_tok ds_RUN HS HJ SHOK ds_span.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    ds_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok ds_RUN ds_BR HS SHOK ds_span.
    + (* 0x84570 bnez taken: entries left, back to the head at i + 1 *)
      rewrite branch_ne_U, (U_atom_off E 11 _ (-1) E11), U_lit in Hc0 by lia.
      assert (Hlt : i + 1 < Z.of_nat (length (lm_es m)))
        by (destruct (Z.eqb_spec (Z.of_nat (length (lm_es m)) - i + -1) 0); [discriminate | lia]).
      paj_run_to_tok ds_RUNTO HS HJ SHOK ds_span A_dr_loop.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      ds_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DS_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
      prreg HS (13%bv : bv 5) N13. prreg HS (22%bv : bv 5) N22.
      rewrite E10, unsigned_lit_small in N10 by lia.
      rewrite E11, unsigned_lit_small in N11 by lia.
      rewrite E22, unsigned_lit_small in N22 by lia.
      assert (Q3 : alu64 ALU_SRL (Z_to_bv 64 (lm_G m + 56 * i)) (Z_to_bv 64 3)
                   = Z_to_bv 64 (lm_G m / 8 + 7 * i)).
      { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
        change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
        rewrite XQ. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
      rewrite E26, E22, Q3, !ds_add_lit in N13.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      eapply (IH cx t (i + 1)); [exact HB|].
      lazymatch goal with |- DST _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM|].
      exists own, ly3, S3, kk, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFRM|]. split; [exact HFLM|]. split; [exact HMOD|].
      split; [exact HINP|]. split; [exact HRV|]. split; [exact HBLK|]. split; [exact HLS|].
      split; [exact HRI|].
      unfold lregs_scan.
      split; [exact (ds_base_kept cx t _ regs _ KR HBASEr)|].
      split; [exact HATOP|].
      split; [rewrite (KR 28%bv ltac:(cbv; tauto)); exact H28|].
      split; [exact HSV8|].
      split.
      { exists sl, h. split; [exact HPICK|].
        split; [rewrite (KR 21%bv ltac:(cbv; tauto)); exact H21|].
        split; [rewrite (KR 12%bv ltac:(cbv; tauto)); exact H12|].
        apply ds_nomatch_step; [exact HNM | lia | exact Hc]. }
      split; [lia|].
      split; [lia|].
      split; [rewrite N10; unfold w64, AENT; f_equal; lia|].
      split; [rewrite N22; unfold w64, AENT; f_equal; lia|].
      split; [rewrite N11; unfold w64; f_equal; lia|].
      rewrite N13; unfold w64; f_equal; lia.
    + (* 0x84570 bnez not taken: no entry carries the fd - 0x84574 j 0x846c8 *)
      rewrite branch_ne_U, (U_atom_off E 11 _ (-1) E11), U_lit in Hc0 by lia.
      assert (Hend : i + 1 = Z.of_nat (length (lm_es m)))
        by (destruct (Z.eqb_spec (Z.of_nat (length (lm_es m)) - i + -1) 0); [lia | discriminate]).
      paj_run_to_tok ds_RUNTO HS HJ SHOK ds_span A_dr_nf.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      ds_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ DS_KEPT HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      apply SRr_ret. right.
      lazymatch goal with |- DST _ _ _ _ _ (mkCfg (mkst ?r _ ?mm _) ?d) => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM|].
      exists own, ly3, S3, kk, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFRM|]. split; [exact HFLM|]. split; [exact HMOD|].
      split; [exact HINP|]. split; [exact HRV|]. split; [exact HBLK|]. split; [exact HLS|].
      split; [exact HRI|].
      unfold lregs_nf.
      split; [exact (ds_base_kept cx t _ regs _ KR HBASEr)|].
      split; [exact HATOP|].
      split; [rewrite (KR 28%bv ltac:(cbv; tauto)); exact H28|].
      split; [exact HSV8|].
      exists sl, h. split; [exact HPICK|].
      rewrite <- Hend. apply ds_nomatch_step; [exact HNM | lia | exact Hc].
Qed.

(* (3) the arm's entry 0x84520-0x8453c: the source's fd, g_nsrc, the store of in.n, and the empty-table test. *)
Lemma dr_entry : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  INV_A B G_fr fr_FP LS RINV 2 cx t W c ->
  SRr segs W c (fun W' c' => (exists n, DST A_dr_loop cx t (lregs_scan cx t n 0) W' c') \/
                             DST A_dr_nf cx t (lregs_nf cx t) W' c').
Proof.
  intros cx t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR).
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as ((C2 & C8 & C9 & C18 & C19 & C20 & C23 & C24 & C25 & C26 & C3 & C4) & R6 & R7 & R27 & Ht & Hk & HO
    & R11 & HPK).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof dr_ceil_lo as HCL.
  (* the operation is 2, and pick() gave slot si, which holds h *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 2).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 2) with true in HPK.
  destruct HPK as (R28 & R29 & [(si & Hpk & R21) | (Hf & _)]); [|lia].
  change (if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1) with (dr_k' cx m) in R28, R29.
  change (if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0) with (dr_kb cx m) in Hpk.
  assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
    by (unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  pose proof HMOD as (Hlen4 & HSL & HREL & _).
  destruct (de_pick_some (lm_hs m) (dr_kb cx m) si Hpk) as [Hsi [h Hh]].
  rewrite Hlen4 in Hsi.
  assert (HPICK : dr_pick cx m si h) by (split; [exact Hpk | split; [exact Hsi | exact Hh]]).
  pose proof (HSL si Hsi) as HSRC. unfold aslot in HSRC. rewrite Hh in HSRC.
  pose proof HSRC as (Mfd & _ & _ & _ & _ & _ & _ & _ & Rfd & _).
  pose proof HREL as (Msrc & _ & Mnsrc & _ & _ & _ & Hl16 & HGin & _).
  (* AR, the relay's block, the stack window, errno, the fake frame *)
  pose proof (ajournal_gx_AR segs B G_fr 0 [] LLVMF_STK _ _ _ _ _ _ _ own ly3 S3 W mem md k HJ) as HAR.
  destruct (al_blocks _ _ LAWS ly3 S3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HE1' : as_errno B + 4 <= DR_CEIL8) by (unfold DR_CEIL8, kLowMemEnd in *; lia).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs, Hown. left. reflexivity. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (VS : rg_s fr_RG = 0x5d88e0) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (HAr : 0x5d88e0 <= HA <= 0x5d88e0 + 288 /\ HA mod 8 = 0).
  { unfold HA. rewrite VS. unfold ASRC. split; [lia|].
    replace (0x5d88e0 + 96 * Z.of_nat si) with ((0xbb11c + 12 * Z.of_nat si) * 8) by lia. apply Z_mod_mult. }
  (* the entry state *)
  remember (Eimg (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx))
    by (rewrite (EEo 9%nat 9%bv eq_refl), (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (VN : rg_nsrc fr_RG = 0x5d87a0) by reflexivity.
  assert (VG : rg_src fr_RG = 0x5d87c0) by reflexivity.
  assert (EO7 : ew E (A_OBJ 7) = Z_to_bv 64 (rg_nsrc fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj1 (proj2 (proj2 de_hi))); reflexivity).
  assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (rg_src fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj2 (proj2 (proj2 de_hi))); reflexivity).
  assert (E21 : ew E 21 = Z_to_bv 64 HA)
    by (rewrite (EEo 21%nat 21%bv eq_refl), (KR0 21%bv ltac:(cbv; tauto)); exact R21).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (rewrite (EEo 26%nat 26%bv eq_refl), (KR0 26%bv ltac:(cbv; tauto)); exact C26).
  assert (E29 : ew E 29 = Z_to_bv 64 (c_n cx - dr_k' cx m))
    by (rewrite (EEo 29%nat 29%bv eq_refl), (KR0 29%bv ltac:(cbv; tauto)); exact R29).
  assert (E32 : ew E 32 = Z_to_bv 64 (hs_fd h))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length (lm_es m))))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (lm_G m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew E 21) = HA) by (rewrite E21; apply unsigned_lit_small; lia).
  assert (UO7 : bv_unsigned (ew E (A_OBJ 7)) = rg_nsrc fr_RG) by (rewrite EO7; apply unsigned_lit_small; lia).
  assert (UO8 : bv_unsigned (ew E (A_OBJ 8)) = rg_src fr_RG) by (rewrite EO8; apply unsigned_lit_small; lia).
  pose proof HFR as (_ & HAWR & _).
  assert (HS : st_ok_pi segs VAL E ss_de
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_arm)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold ss_de. apply pa_entry_st_ok_full.
    - unfold de_sr. rewrite HE.
      apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                         | intros X; discriminate X |]; rewrite <- HE.
      + rewrite (KR0 23%bv ltac:(cbv; tauto)), C23. apply bv_eq. fold (U E (SOff (A_HI 74) 0)).
        rewrite (U_img_atom E HEI (A_HI 74)) by (unfold A_HI, A_TEXT, A_LIM; lia).
        rewrite (proj1 de_hi). unfold w64. apply unsigned_lit_small. unfold HI_G_NSRC; lia.
      + rewrite (KR0 18%bv ltac:(cbv; tauto)), C18. apply bv_eq. fold (U E (SOff (A_HI 75) 0)).
        rewrite (U_img_atom E HEI (A_HI 75)) by (unfold A_HI, A_TEXT, A_LIM; lia).
        rewrite (proj1 (proj2 de_hi)). unfold w64. apply unsigned_lit_small. unfold HI_G_SRC; lia.
    - vm_compute. reflexivity.
    - unfold de_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. exact (HAWR o ltac:(lia)).
      + rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ HA 0 4 (SOff 32 0) (hs_fd h));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mfd.
      + rewrite UO7. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_nsrc fr_RG) 0 4 (SOff 33 0) (Z.of_nat (length (lm_es m))));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mnsrc.
      + rewrite UO8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_src fr_RG) 0 8 (SOff 34 0) (lm_G m));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Msrc.
    - unfold de_regions. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U21, UO7, UO8.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [de_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E21, E26, E32, E33, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (EH74 : ew E 354 = Z_to_bv 64 HI_G_NSRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) (proj1 de_hi))).
  assert (EH75 : ew E 355 = Z_to_bv 64 HI_G_SRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); exact (f_equal (Z_to_bv 64) (proj1 (proj2 de_hi)))).
  clear HE.
  assert (HBx : U E de_Bx = SHADOW_OFF)
    by (unfold de_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs de_Bx de_SH E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    - apply (azs_range_addressable B LAWS ly3 S3 W mem md HA 4 HAR).
      destruct HZS as (zr & Hzin & Hz8 & Hzlo & Hzhi). unfold ASRC in Hzhi.
      exists zr. refine (conj Hzin (conj Hz8 _)). lia.
    - exact HBx.
    - rewrite (U_atom E 21 _ E21) by lia. reflexivity.
    - lia.
    - lia.
    - intros x Hx. unfold SHADOW_OFF in *. lia. }
  unfold cfg_at. change (w64 (fr_B0 + fr_arm 2)) with (Z_to_bv 64 (BASE + A_dr_arm)).
  (* 0x84520-0x84538: the shadow check of s5, lw a1 = g_nsrc, sd t4 -> F+144, to the blez *)
  paj_run_tok de_RUN HS HJ SHOK de_span.
  { de_awr U9. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFr1 a Ha); de_nowr U9 Hna).
  assert (P1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Hp; exact (de_pres_grows W _ _ a HG1 Hp)).
  clear HFr1 HG1.
  lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
    assert (S33 : bv_signed (sv_denot Ev (SOff 33 0)) = Z.of_nat (length (lm_es m)))
      by (assert (U33 : U Ev (SOff 33 0) = Z.of_nat (length (lm_es m)))
            by (apply U_atom; [rewrite !ew_ewset_other by lia; exact E33 | lia]);
          unfold U in U33; rewrite bv_signed_small; [exact U33 | rewrite U33; lia]);
    assert (S0 : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity
  end.
  (* blez a1: g_nsrc <= 0 *)
  psrr_branch_tok de_RUN de_BR HS SHOK de_span.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S33 in Hc.
    apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    assert (Hn0 : length (lm_es m) = 0%nat) by lia.
    (* 0x846c8 *)
    paj_run_to_tok de_RUNTO HS HJ SHOK de_span A_dr_nf.
    { de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr a Ha) by (de_nowr U9 Hna); exact (K1 a Ha Hna)).
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (P1 a Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (de_carry cx W mem (ms_mem ms0) md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    pose proof (de_flag_kept cx W mem (ms_mem ms0) md ly3 S3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    assert (SVN : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { unfold sv8, DR_N.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 29 0) (c_n cx - dr_k' cx m) RG0) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DE_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (KK : forall rr, In rr DE_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
    { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [DE_KEPT In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. rewrite EH75 in Q18. rewrite EH74 in Q23.
    assert (LB : lregs_base cx t FF (ms_regs ms0)).
    { split; [|split; [rewrite (KK 27%bv ltac:(cbv; tauto)); exact R27 | exact Ht]].
      split; [rewrite (KK 2%bv ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (KK 8%bv ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (KK 9%bv ltac:(cbv; tauto)); exact C9|].
      split; [exact Q18|].
      split; [rewrite (KK 19%bv ltac:(cbv; tauto)); exact C19|].
      split; [rewrite (KK 20%bv ltac:(cbv; tauto)); exact C20|].
      split; [exact Q23|].
      split; [rewrite (KK 24%bv ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (KK 25%bv ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (KK 26%bv ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (KK 3%bv ltac:(cbv; tauto)); exact C3|].
      rewrite (KK 4%bv ltac:(cbv; tauto)); exact C4. }
    assert (L28 : getr (ms_regs ms0) 28 = w64 (c_p cx + dr_k' cx m))
      by (rewrite (KK 28%bv ltac:(cbv; tauto)); exact R28).
    pmkst HS. apply SRr_ret.
    right.
      lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM2|].
      exists own, ly3, S3, k, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
      split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HRI|].
      split; [exact LB|]. split; [exact (conj Hk (conj HO Hop))|]. split; [exact L28|]. split; [exact SVN|].
      exists si, h. split; [exact HPICK|]. intros q Hq. rewrite Hn0 in Hq. cbn in Hq. lia.
  - cbn [branch_taken] in Hc. rewrite bv_lts_signed, S0, S33 in Hc.
    apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    (* 0x8453c-0x8454c: g_src, s->fd, the shadow address of g_src[0], to the scan's head *)
    paj_run_to_tok de_RUNTO HS HJ SHOK de_span A_dr_loop.
    { de_awr U9. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a)
      by (intros a Ha Hna; rewrite (aview_kept_out _ _ _ _ _ HFr a Ha) by (de_nowr U9 Hna); exact (K1 a Ha Hna)).
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (P1 a Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + DR_N <= a < lf_F cx + DR_N + 8) ->
        abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (de_carry cx W mem (ms_mem ms0) md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    pose proof (de_flag_kept cx W mem (ms_mem ms0) md ly3 S3 fpos HAR Hfin ltac:(lia) KEEP HFL) as HFL2.
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    assert (SVN : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { unfold sv8, DR_N.
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 144 8%N (SOff 29 0) (c_n cx - dr_k' cx m) RG0) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (de_extra (hs_fd h) (Z.of_nat (length (lm_es m))) (lm_G m))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DE_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (KK : forall rr, In rr DE_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
    { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [DE_KEPT In] in Hrr.
      repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. rewrite EH75 in Q18. rewrite EH74 in Q23.
    assert (LB : lregs_base cx t FF (ms_regs ms0)).
    { split; [|split; [rewrite (KK 27%bv ltac:(cbv; tauto)); exact R27 | exact Ht]].
      split; [rewrite (KK 2%bv ltac:(cbv; tauto)); exact C2|].
      split; [rewrite (KK 8%bv ltac:(cbv; tauto)); exact C8|].
      split; [rewrite (KK 9%bv ltac:(cbv; tauto)); exact C9|].
      split; [exact Q18|].
      split; [rewrite (KK 19%bv ltac:(cbv; tauto)); exact C19|].
      split; [rewrite (KK 20%bv ltac:(cbv; tauto)); exact C20|].
      split; [exact Q23|].
      split; [rewrite (KK 24%bv ltac:(cbv; tauto)); exact C24|].
      split; [rewrite (KK 25%bv ltac:(cbv; tauto)); exact C25|].
      split; [rewrite (KK 26%bv ltac:(cbv; tauto)); exact C26|].
      split; [rewrite (KK 3%bv ltac:(cbv; tauto)); exact C3|].
      rewrite (KK 4%bv ltac:(cbv; tauto)); exact C4. }
    assert (L28 : getr (ms_regs ms0) 28 = w64 (c_p cx + dr_k' cx m))
      by (rewrite (KK 28%bv ltac:(cbv; tauto)); exact R28).
    pmkst HS. apply SRr_ret.
    prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
    prreg HS (13%bv : bv 5) Q13. prreg HS (22%bv : bv 5) Q22.
    rewrite E34 in Q10, Q22. rewrite E33 in Q11. rewrite E32 in Q12.
    assert (G8 : 0 <= lm_G m / 8 /\ 8 * (lm_G m / 8) <= lm_G m)
      by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) = SB + lm_G m / 8).
    { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 34 _ E34), U_lit by (unfold SB; lia). cbn [zalu_raw].
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
      rewrite (Z.mod_small (lm_G m / 8)) by lia. rewrite Z.mod_small by (unfold SB; lia). reflexivity. }
    assert (Hsd : sv_denot E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3))) =
                  alu64 ALU_ADD (ew E 26) (alu64 ALU_SRL (ew E 34) (Z_to_bv 64 3)))
      by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
    rewrite <- Hsd in Q13.
    left. exists (length (lm_es m)).
      lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
      split; [reflexivity|]. split; [exact HROM2|].
      exists own, ly3, S3, k, m, fpos.
      split; [exact HJ|]. split; [exact Hown|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
      split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HRI|].
      split; [exact LB|]. split; [exact (conj Hk (conj HO Hop))|]. split; [exact L28|]. split; [exact SVN|].
      split.
      { exists si, h. split; [exact HPICK|].
        split; [rewrite (KK 21%bv ltac:(cbv; tauto)); exact R21|].
        split; [exact Q12|]. intros q Hq. lia. }
      split; [lia|]. split; [lia|].
      split; [rewrite Q10; f_equal; unfold AENT; lia|].
      split; [rewrite Q22; f_equal; unfold AENT; lia|].
      split; [rewrite Q11; f_equal; lia|].
      rewrite Q13. apply bv_eq. fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 34 0) (SLit 3)))).
      rewrite USH. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). lia.
Qed.

(* ---- the two joins' entry states (0x846c8 and 0x84a80): registers only, and the frame slot F+104 that
   0x84b28 reloads s9 from.  Neither join writes memory, so both runs are over read-only regions. *)
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Definition DRspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition drBx : sv := SOff 26 0.
Definition dr_facts : facts := mkFacts [ (26%nat, mkAF SB SB 0) ] [] [].
Definition ss_dr_nf : sstate := mkSS A_dr_nf sr_atoms [] None dr_facts.
Definition dr_jn_rF : YP09.region :=
  YP09.mkRegion (Some 9%nat) 104 112 0 0 [YP09.mkChunk 104 (CVal 8 (SLit HI_G_NOUT))].
Definition ss_dr_jn : sstate := mkSS A_dr_join sr_atoms [dr_jn_rF] None dr_facts.
(* the registers neither join writes *)
Definition DR_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 26; 27]%bv.
(* after a run whose regions have no writable window, the memory is the one it began in *)
Ltac dr_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
Lemma dr_nf_entry : forall (W : world segs) regs mem,
  getr regs 26 = w64 SB ->
  st_ok_pi segs VAL (Eimg (Ereg regs [])) ss_dr_nf
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_nf)) mem (seg_rom segs)))
  /\ sh_ok segs drBx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem R26.
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  split.
  - unfold ss_dr_nf. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + constructor.
    + cbn [pairwise_disjoint all_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [dr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E26, unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.

(* (4) 0x846c8: the no-entry path joins the arm's tail. *)
Lemma dr_nf_join : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  DST A_dr_nf cx t (lregs_nf cx t) W c ->
  SRr segs W c (DST A_dr_join cx (t + 1) (lregs_join cx t)).
Proof.
  intros cx t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR)).
  destruct HR as (((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Ht)
    & Hatop & R28 & SVN & (si & h & Hpick & Hnom)).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof Hatop as (Hk0 & _ & _).
  assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
    by (unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  destruct (dr_nf_entry W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + dr_k' cx m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl); exact R28).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_nf)) with (Z_to_bv 64 (BASE + A_dr_nf)).
  (* mv s9,t3 ; j 0x84a80 *)
  paj_run_to_tok RUNTO HS HJ SHOK DRspan A_dr_join.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DR_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (25%bv : bv 5) Q25. rewrite E28 in Q25.
  pmkst HS. rewrite Em in *.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HROM|].
  exists [(1, fpos)], ly3, S3, k, (dr_skip m (dr_k' cx m)), fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|].
  split; [apply LS_drain_skip; exact HLS|].
  split; [apply (RI_drain_skip cx t m si h HRI Hatop Hpick); left; exact Hnom|].
  split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
  split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
  split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
  split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
  split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
  split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
  split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
  split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite Q25; reflexivity|].
  split; [exact SVN|]. exact Hk'.
Qed.

(* ---- (5)'s entry state at 0x84a20.  Three regions: the two frame cells the arm writes (F+192 takes the
   out-parameter `at` = 0 at 0x84a24, F+40 &g_lock at 0x84a4c) and the eof field of the relay's entry j that
   0x84a3c reads through s6 (its value the atom 32, never a Coq term inside the symbolic state); one shadow
   entry, for the byte 0x84a34 loads for that field (the check at 0x84a38). *)
Definition dc_rA : YP09.region := YP09.mkRegion (Some 9%nat) 192 200 192 200 [].
Definition dc_rL : YP09.region := YP09.mkRegion (Some 9%nat) 40 48 40 48 [].
Definition dc_rE : YP09.region :=
  YP09.mkRegion (Some 22%nat) 4 8 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 32 0))].
Definition dc_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, mkAF 4096 140737488355312 3);
            (22%nat, mkAF 4096 140737488355312 3); (26%nat, mkAF SB SB 0); (32%nat, mkAF 0 1 0) ] [] [].
Definition ss_dc_found : sstate := mkSS A_dr_found sr_atoms [dc_rA; dc_rL; dc_rE] None dc_facts.
Definition dc_extra (ef : Z) : list word := map (Z_to_bv 64) [ef].
Definition dc_SH : list shent := [ mkSHE 10 4 8 ].
(* Reusable/YCbq.v:2524 shent_ok_of_block, for a range INSIDE a live block rather than at its base: the
   shadow-checked field is at G + AENT * j + 4, the block is the relay's table at G. *)
Lemma dc_shent_block : forall ly S (W : world segs) mem md E Bx (m : nat) p n q lo hi,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> p <= q + lo -> lo <= hi -> q + hi <= p + req_size n ->
  shent_ok segs Bx E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
  intros ly S W mem md E Bx m p n q lo hi HAR Hin HB Hm Hlo Hle Hhi.
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of segs).
  destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [Hbs _].
  split.
  - destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
    eapply block_shadow_range; [exact Hbs | lia | lia].
  - destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
    intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma dc_found_entry : forall ly S (W : world segs) mem md regs F G (j : nat) ef,
  AR segs B ly S W mem md ->
  getr regs 9 = w64 F -> getr regs 10 = w64 (G + AENT * Z.of_nat j) ->
  getr regs 22 = w64 (G + AENT * Z.of_nat j) -> getr regs 26 = w64 SB ->
  2 ^ 46 <= F -> F + 200 <= 2 ^ 47 -> F mod 32 = 0 ->
  (forall a, F + 40 <= a < F + 48 -> writable_at segs (arm W mem) a) ->
  (forall a, F + 192 <= a < F + 200 -> writable_at segs (arm W mem) a) ->
  In (G, ATABLE) (ablocks B ly S) ->
  4096 <= G + AENT * Z.of_nat j -> (G + AENT * Z.of_nat j) mod 8 = 0 ->
  G + AENT * Z.of_nat j + 8 <= F ->
  G <= G + AENT * Z.of_nat j -> AENT * Z.of_nat j + 8 <= ATABLE ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat j + 4) 4 ef -> 0 <= ef <= 1 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (dc_extra ef))) ss_dc_found
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_found)) mem (seg_rom segs)))
  /\ sh_ok segs drBx dc_SH (Eimg (Ereg regs (dc_extra ef))) (mrestrict (w_H W) mem).
Proof.
  intros ly S W mem md regs F G j ef HAR R9 R10 R22 R26 HF0 HF1 HF32 HWL HWA Hin Hq0 Hq8 Hqhi HGq Hjt Mef Hef.
  pose proof (req_size_pos ATABLE ltac:(unfold ATABLE; lia)) as [Hr1 Hr2].
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs (dc_extra ef))) as E eqn:HE.
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E10 : ew E 10 = Z_to_bv 64 (G + AENT * Z.of_nat j)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
  assert (E22 : ew E 22 = Z_to_bv 64 (G + AENT * Z.of_nat j)) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 ef)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - unfold ss_dc_found. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, dc_rA, dc_rL, dc_rE;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|].
        split; [intros o Ho; apply HWA; lia | apply Forall_nil].
      * rewrite E9, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|].
        split; [intros o Ho; apply HWL; lia | apply Forall_nil].
      * rewrite E22, unsigned_lit_small by lia.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (G + AENT * Z.of_nat j) 4 4 (SOff 32 0) ef);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mef].
    + apply pairwise_disjoint_of_extents. unfold dc_rA, dc_rL, dc_rE, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E22, !unsigned_lit_small by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [dc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E10, E22, E26, E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. change (2 ^ 3) with 8.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok, dc_SH. constructor; [|constructor].
    apply (dc_shent_block ly S W mem md E drBx 10 G ATABLE (G + AENT * Z.of_nat j) 4 8 HAR Hin).
    + unfold U, drBx. cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by lia. reflexivity.
    + lia.
    + lia.
    + lia.
Qed.

Lemma dr_tbl_eof : forall (W : world segs) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (i : nat),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (i < length es)%nat -> 0 <= re_eof (nth i es dr_e0) < 2 ^ 32 ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat i + 4) 4 (re_eof (nth i es dr_e0)).
Proof.
  intros W mem G es tail i [_ [_ Hg]] Hpad Hi Hv.
  pose proof (concat_entry_length es Hpad) as Hcl.
  unfold val_mem. intros k Hk.
  assert (Hj : (56 * i + (4 + k) < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
  { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
  unfold garr8 in Hg. destruct (Hg _ Hj) as [Hb _]. unfold val_mem in Hb.
  specialize (Hb 0%nat ltac:(lia)).
  replace (G + AENT * Z.of_nat i + 4 + Z.of_nat k) with (G + Z.of_nat (56 * i + (4 + k)) + Z.of_nat 0)
    by (unfold AENT; lia).
  rewrite Hb. f_equal.
  assert (Hn : nth (56 * i + (4 + k)) (bzs (concat (map entry_bytes es) ++ tail)) 0 =
               bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 (re_eof (nth i es dr_e0)))) (Z_to_bv 8 0))).
  { rewrite nth_bzs. f_equal.
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite concat_entry_nth by (first [exact Hpad | exact Hi | lia]).
    unfold entry_bytes. rewrite app_nth2 by (rewrite Mem.length_le4; lia).
    rewrite Mem.length_le4. replace (4 + k - 4)%nat with k by lia.
    rewrite app_nth1 by (rewrite Mem.length_le4; exact Hk). reflexivity. }
  rewrite Hn, le_byte_1_byte.
  apply bv_eq. rewrite Z_to_bv_unsigned, le4_le_byte by lia.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* the frame across a run whose only stores are the two scratch cells [F+40, F+48) and [F+192, F+200)
   (de_aframe_kept's proof, with this run's two windows) *)
Definition dc_out (cx : lfcx) (a : Z) : Prop :=
  ~ (lf_F cx + 40 <= a < lf_F cx + 48) /\ ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8).
Lemma dc_aframe_kept : forall cx full FF (W W' : world segs) mem mem',
  aframe_at cx full FF W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> abyte_kept W mem W' mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  DR_CEIL8 <= lf_F cx -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= DR_CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= DR_CEIL8 ->
  aframe_at cx full FF W' mem'.
Proof.
  intros cx full FF W W' mem mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    HK WK HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof dr_ceil_lo as HCL. unfold dc_out, DR_AT, DR_CEIL8 in *.
  assert (KW : forall a n, awr W mem a n -> awr W' mem' a n) by (intros a n Hw i Hi; apply WK; exact (Hw i Hi)).
  assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
             (a + 8 <= lf_F cx + 40 \/ lf_F cx + 48 <= a) -> (a + 8 <= lf_F cx + 192 \/ lf_F cx + 200 <= a) ->
             sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 H2 H3 Hv. apply (dr_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply HK; lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | lia | exact (A1 o r Hin)]. }
  split; [exact (KW _ _ A2)|].
  do 9 (split; [apply KV; [lia | lia | lia | lia | assumption]|]).
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    do 6 (split; [apply KV; [lia | lia | lia | lia | assumption]|]).
    apply KV; [lia | lia | lia | lia | assumption]. }
  do 3 (split; [apply KV; [lia | lia | lia | lia | assumption]|]).
  split; [exact (KW _ _ A16)|].
  split; [|exact (KW _ _ (proj2 A17))].
  apply (akept_garr8 W mem); [|exact (proj1 A17)]. intros x Hx.
  unfold fake_shadow in Hx. cbn [length] in Hx. apply HK; lia.
Qed.
Lemma dc_carry : forall cx (W : world segs) mem mem' md ly3 S3 fpos m,
  AR segs B ly3 S3 W mem md -> In (1, fpos) (frames S3) ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem -> amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  aframe_at cx true (frame_addr ly3 1 fpos) W mem' /\ amodel_at B ly3 S3 W mem' m /\
  ainput_at B cx ly3 S3 W mem' /\ rom_view segs W mem' /\ jt_rom W mem'.
Proof.
  intros cx W mem mem' md ly3 S3 fpos m HAR Hfin Hlen Hsp HFR HMOD HIN HRV HJT KEEP WK.
  pose proof dr_ceil_lo as HCL. pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < DR_CEIL8 -> abyte_kept W mem W mem' a).
  { intros a Ha. apply KEEP; unfold dc_out, DR_AT, DR_CEIL8 in *; lia. }
  split.
  { apply (dc_aframe_kept cx true _ W W mem mem' HFR KEEP WK); unfold DR_CEIL8, SB in *; lia. }
  split; [exact (dr_amodel_kept ly3 S3 W mem md W mem' m HAR HMOD HE0
                   ltac:(unfold DR_CEIL8, kLowMemEnd in *; lia) KL)|].
  split; [exact (dr_ainput_kept cx ly3 S3 W mem md W mem' HAR HIN Hlen KL)|].
  split; [exact (dr_rom_kept W W mem mem' HRV KL)|].
  exact (dr_jt_kept W W mem mem' HJT KL).
Qed.

Lemma dj_in_img_dec : forall a, in_img segs a \/ ~ in_img segs a.
Proof.
  intros a. unfold in_img.
  destruct (existsb (fun sg => (Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs)
    eqn:Eb.
  - left. apply existsb_exists in Eb as (sg & Hs & Hb). apply andb_prop in Hb as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists sg. split; [exact Hs | lia].
  - right. intros (sg & Hs & Hr). assert (Hx : existsb (fun sg => (Z.of_N (seg_base sg) <=? a) &&
      (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs = true).
    { apply existsb_exists. exists sg. split; [exact Hs|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Hx in Eb. discriminate.
Qed.

(* ---- (5)'s journal kit ---- *)
(* a byte whose ASan view is kept is kept (writable_at reads the memory only at the byte) *)
Lemma dj_bk : forall (W W' : world segs) mem mem' a, 0 <= a < 2 ^ 64 -> (in_img segs a -> inG G_fr a) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Hr Hg Ha. split; [exact Ha|]. intros Hw.
  destruct (dj_in_img_dec a) as [Hi | Hi]; [exact (GWR _ _ a (Hg Hi))|].
  pose proof (mbyte_of_aview segs (w_H W) (w_H W') mem mem' a Ha) as Hm. unfold mbyte in Hm.
  rewrite (seg_rom_none segs a Hr Hi) in Hm.
  unfold writable_at, wview, arm in *.
  destruct (mrestrict (w_H W') mem' (Z_to_bv 64 a)) eqn:E1, (mrestrict (w_H W) mem (Z_to_bv 64 a)) eqn:E2;
    try discriminate; try exact Hw; try (intros X; discriminate X).
Qed.
(* what a callee's journal keeps, outside its G: the stack above its window, its out window outside the out
   cells, the blocks live before and after outside its footprint, the image bytes that are no allocator static
   and not errno, and the fake frames outside its footprint *)
Lemma dj_keep : forall G XO OUT STK sp FP ly S (W : world segs) mem md own ly' S' (W' : world segs) mem' md' k a,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
  0 <= a < 2 ^ 64 -> ~ inG G a ->
  ((alloc_ceiling <= a /\ ~ (sp - STK <= a < sp + XO)) \/
   (sp <= a < sp + XO /\ ~ inFP OUT a) \/
   (exists p n, In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n /\
      ~ inFP FP a) \/
   (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
      fp_spares FP a) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) /\
      ~ inFP FP a)) ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof.
  intros G XO OUT STK sp FP ly S W mem md own ly' S' W' mem' md' k a HGx HJX Ha HnG Hc.
  pose proof HJX as (HS0 & HX0 & (memS & HJi & Hag) & Hout).
  assert (HmS : aview segs (w_H W) memS a = aview segs (w_H W) mem a).
  { apply (aview_gagree segs G _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG. }
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
  destruct Hc as [(H1 & H2) | [(H1 & H2) | [(p & n & H1 & H2 & H3 & H4) | [(H1 & H2 & H3 & H4) | (cid & pos & H1 & H2 & H3)]]]].
  - rewrite (F1 a ltac:(lia) ltac:(lia)). exact HmS.
  - exact (Hout a H1 H2).
  - replace a with (p + (a - p)) in * by lia.
    rewrite (F2 p n (a - p) H1 H2 ltac:(lia) H4). exact HmS.
  - rewrite (F3 a H1 H2 H3 H4). exact HmS.
  - rewrite (F4 cid pos a H1 H2 H3). exact HmS.
Qed.
(* the live blocks are pairwise distinct (W_gesture_end.v ablocks_nodup, W4Gesture) *)
Lemma dj_nodup : forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  assert (Hpos : Forall (fun b => 1 <= req_size (snd b)) (ablocks B ly S)).
  { apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    cbn [snd]. apply req_size_pos. lia. }
  destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
  revert Hpos Hp. induction (ablocks B ly S) as [|b l IH]; intros Hpos Hp; [constructor|].
  inversion Hpos as [|b0 l0 Hb Hl]; subst.
  cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. constructor; [|exact (IH Hl Hp)].
  intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
(* two distinct live blocks share no byte *)
Lemma dj_apart : forall ly S (W : world segs) mem md p n q r a,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, r) (ablocks B ly S) -> (p, n) <> (q, r) ->
  p <= a < p + req_size n -> ~ (q <= a < q + req_size r).
Proof.
  intros ly S W mem md p n q r a HAR H1 H2 Hne Ha Hb.
  pose proof (sep_blocks segs B LAWS ly S W mem md p n q r HAR H1 H2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.


(* ---- the entry states at the return points 0x84a54, 0x84a64, 0x84a6c (no memory read before the next call),
   0x84a5c (ld a0,40(s1)) and 0x84a78 (ld a0,192(s1)) ---- *)
Definition A_dc_r1 : Z := A_dr_found + 0x34.   (* 0x84a54 back from pthread_mutex_lock *)
Definition A_dc_r2 : Z := A_dr_found + 0x3c.   (* 0x84a5c back from drain *)
Definition A_dc_r3 : Z := A_dr_found + 0x44.   (* 0x84a64 back from pthread_mutex_unlock *)
Definition A_dc_r4 : Z := A_dr_found + 0x4c.   (* 0x84a6c back from check_no_loss_read *)
Definition A_dc_r5 : Z := A_dr_found + 0x58.   (* 0x84a78 back from check_no_loss *)
Definition ss_plain (pc : Z) : sstate := mkSS pc sr_atoms [] None dr_facts.
Lemma dc_plain_entry : forall pc (W : world segs) regs mem,
  getr regs 26 = w64 SB ->
  st_ok_pi segs VAL (Eimg (Ereg regs [])) (ss_plain pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)))
  /\ sh_ok segs drBx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
  intros pc W regs mem R26.
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  split.
  - unfold ss_plain. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + constructor.
    + cbn [pairwise_disjoint all_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [dr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E26, unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.

(* 0x84a5c (ld a0,40(s1)) and 0x84a78 (ld a0,192(s1)): one 8-byte frame cell, its value the atom 32 *)
Definition dc_cell (off : Z) : YP09.region := YP09.mkRegion (Some 9%nat) off (off + 8) 0 0 [YP09.mkChunk off (CVal 8 (SOff 32 0))].
Definition dc_facts9a : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (26%nat, mkAF SB SB 0); (32%nat, mkAF 0 (2 ^ 64 - 1) 0) ] [] [].
Definition ss_dc_cell (pc off : Z) : sstate := mkSS pc sr_atoms [dc_cell off] None dc_facts9a.
Definition dc_cell_extra (A : Z) : list word := map (Z_to_bv 64) [A].
Lemma dc_cell_entry : forall pc off (W : world segs) regs mem F A,
  getr regs 9 = w64 F -> getr regs 26 = w64 SB -> 2 ^ 46 <= F -> F + 200 <= 2 ^ 47 -> F mod 32 = 0 ->
  0 <= off -> off + 8 <= 200 -> regions_wf [dc_cell off] = true ->
  sv8 W mem (F + off) A -> 0 <= A < 2 ^ 64 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (dc_cell_extra A))) (ss_dc_cell pc off)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)))
  /\ sh_ok segs drBx [] (Eimg (Ereg regs (dc_cell_extra A))) (mrestrict (w_H W) mem).
Proof.
  intros pc off W regs mem F A R9 R26 HF0 HF1 HF32 Ho0 Ho1 Hwf MA HA.
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs (dc_cell_extra A))) as E eqn:HE.
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 A)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  split.
  - unfold ss_dc_cell. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + exact Hwf.
    + apply Forall_cons; [|constructor]. unfold region_ok, dc_cell.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|constructor].
      apply (chunk_ok_val segs E _ F off 8 (SOff 32 0) A);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MA].
    + cbn [pairwise_disjoint all_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [dc_facts9a f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E26, E32, !unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.

(* a list around its entry j, and set_nth j as the same split with x in the middle *)
Lemma dra_split : forall (A : Type) (l : list A) (j : nat) (d : A),
  (j < length l)%nat -> l = firstn j l ++ nth j l d :: skipn (S j) l.
Proof.
  intros A l. induction l as [|a l IH]; intros [|j] d Hj; cbn [length] in Hj.
  - lia.
  - lia.
  - reflexivity.
  - cbn [firstn nth skipn app]. f_equal. apply IH. lia.
Qed.
Lemma dra_set_nth_split : forall (A : Type) (l : list A) (j : nat) (x : A),
  (j < length l)%nat -> set_nth j x l = firstn j l ++ x :: skipn (S j) l.
Proof.
  intros A l. induction l as [|a l IH]; intros [|j] x Hj; cbn [length] in Hj.
  - lia.
  - lia.
  - reflexivity.
  - cbn [set_nth firstn skipn app]. f_equal. apply IH. lia.
Qed.
Lemma dra_concat_split : forall (A C : Type) (f : A -> list C) (l : list A) (j : nat) (d : A),
  (j < length l)%nat ->
  concat (map f l) = concat (map f (firstn j l)) ++ f (nth j l d) ++ concat (map f (skipn (S j) l)).
Proof.
  intros A C f l j d Hj. rewrite (dra_split A l j d Hj) at 1. rewrite map_app, concat_app. reflexivity.
Qed.
Lemma dra_concat_set_split : forall (A C : Type) (f : A -> list C) (l : list A) (j : nat) (x : A),
  (j < length l)%nat ->
  concat (map f (set_nth j x l)) = concat (map f (firstn j l)) ++ f x ++ concat (map f (skipn (S j) l)).
Proof.
  intros A C f l j x Hj. rewrite (dra_set_nth_split A l j x Hj). rewrite map_app, concat_app. reflexivity.
Qed.
Lemma dr_concat_nth_perm : forall (A C : Type) (f : A -> list C) (l : list A) (j : nat) (d : A),
  (j < length l)%nat ->
  Permutation (concat (map f l)) (f (nth j l d) ++ concat (map f (firstn j l ++ skipn (S j) l))).
Proof.
  intros A C f l j d Hj. rewrite (dra_concat_split A C f l j d Hj), map_app, concat_app, !app_assoc.
  apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma dr_concat_set_nth_perm : forall (A C : Type) (f : A -> list C) (l : list A) (j : nat) (x : A),
  (j < length l)%nat ->
  Permutation (concat (map f (set_nth j x l))) (f x ++ concat (map f (firstn j l ++ skipn (S j) l))).
Proof.
  intros A C f l j x Hj. rewrite (dra_concat_set_split A C f l j x Hj), map_app, concat_app, !app_assoc.
  apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma dr_map_set_nth : forall (A C : Type) (f : A -> C) (j : nat) (x : A) (l : list A),
  map f (set_nth j x l) = set_nth j (f x) (map f l).
Proof.
  intros A C f j x l. revert j. induction l as [|a l IH]; intros [|j]; cbn [set_nth map]; try reflexivity.
  f_equal. apply IH.
Qed.
Lemma dr_in_set_nth : forall (A : Type) (j : nat) (x y : A) (l : list A),
  In y (set_nth j x l) -> y = x \/ In y (firstn j l ++ skipn (S j) l).
Proof.
  intros A j x y l. revert j. induction l as [|a l IH]; intros [|j] H; cbn [set_nth firstn skipn app In] in H |- *.
  - destruct H.
  - destruct H.
  - destruct H as [E|H]; [left; symmetry; exact E | right; exact H].
  - destruct H as [E|H]; [right; left; exact E|].
    destruct (IH j H) as [E|H']; [left; exact E | right; right; exact H'].
Qed.
Lemma dr_in_rm : forall (A : Type) (j : nat) (y : A) (l : list A),
  In y (firstn j l ++ skipn (S j) l) -> In y l.
Proof.
  intros A j y l H. apply in_app_or in H. destruct H as [H|H].
  - rewrite <- (firstn_skipn j l). apply in_or_app. left. exact H.
  - rewrite <- (firstn_skipn (S j) l). apply in_or_app. right. exact H.
Qed.
Lemma dra_len_split : forall (A : Type) (l : list A) (j : nat), (j < length l)%nat ->
  length (firstn j l) = j /\ length (skipn (S j) l) = (length l - S j)%nat.
Proof.
  intros A l. induction l as [|a l IH]; intros [|j] Hj; cbn [length firstn skipn] in Hj |- *.
  - lia.
  - lia.
  - split; [reflexivity | change (skipn 0 l) with l; lia].
  - destruct (IH j ltac:(lia)) as [H1 H2]. split; lia.
Qed.
Lemma dra_Forall_firstn : forall (A : Type) (P : A -> Prop) (j : nat) (l : list A), Forall P l -> Forall P (firstn j l).
Proof. intros A P j l H. rewrite <- (firstn_skipn j l) in H. apply Forall_app in H. exact (proj1 H). Qed.
Lemma dra_Forall_skipn : forall (A : Type) (P : A -> Prop) (j : nat) (l : list A), Forall P l -> Forall P (skipn j l).
Proof. intros A P j l H. rewrite <- (firstn_skipn j l) in H. apply Forall_app in H. exact (proj2 H). Qed.
Lemma dra_bzs_app : forall l1 l2, bzs (l1 ++ l2) = bzs l1 ++ bzs l2.
Proof. intros l1 l2. unfold bzs. apply map_app. Qed.
Lemma dra_bzs_length : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
(* the entry j of the relay's table, as a byte array *)
Lemma dr_tbl_entry : forall (W : world segs) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (j : nat),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (j < length es)%nat ->
  garr8 segs (arm W mem) (G + AENT * Z.of_nat j) (bzs (entry_bytes (nth j es dr_e0))).
Proof.
  intros W mem G es tail j (_ & _ & Hg) Hpad Hj.
  destruct (dra_len_split rentry es j Hj) as [Hfl _].
  assert (HX : length (bzs (concat (map entry_bytes (firstn j es)))) = (56 * j)%nat).
  { rewrite dra_bzs_length, concat_entry_length, Hfl by (apply dra_Forall_firstn; exact Hpad). reflexivity. }
  rewrite (dra_concat_split _ _ entry_bytes es j dr_e0 Hj) in Hg. rewrite !dra_bzs_app in Hg.
  apply garr8_app in Hg as [Hg1 _]. apply garr8_app in Hg1 as [_ Hg2]. apply garr8_app in Hg2 as [Hg3 _].
  rewrite HX in Hg3. replace (G + AENT * Z.of_nat j) with (G + Z.of_nat (56 * j)) by (unfold AENT; lia).
  exact Hg3.
Qed.
(* the bytes of a range inside a live block are writable (they are present) *)
Lemma dr_awr_of_garr8 : forall ly S (W : world segs) mem md p n a (l : list Z),
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> p <= a -> a + Z.of_nat (length l) <= p + req_size n ->
  garr8 segs (arm W mem) a l -> awr W mem a (Z.of_nat (length l)).
Proof.
  intros ly S W mem md p n a l HAR Hin Hp Hq _ i Hi. unfold arm. apply (apresent_writable segs).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & Hpr & _).
  exact (proj1 (Hpr (a + i) ltac:(lia))).
Qed.
(* the table after entry j is rewritten and the rest of its 896 bytes kept *)
Lemma dr_tbl_upd : forall (W W' : world segs) (mem mem' : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (j : nat) (e' : rentry),
  atable_at W mem G es tail ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  length (re_pad1 e') = 4%nat -> length (re_pad2 e') = 4%nat ->
  (j < length es)%nat ->
  garr8 segs (arm W' mem') (G + AENT * Z.of_nat j) (bzs (entry_bytes e')) ->
  (forall a, G <= a < G + ATABLE -> ~ (G + AENT * Z.of_nat j <= a < G + AENT * Z.of_nat j + AENT) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  atable_at W' mem' G (set_nth j e' es) tail.
Proof.
  intros W W' mem mem' G es tail j e' (Htl & Htot & Hg) Hpad Hp1 Hp2 Hj Hge Hview.
  assert (Hall : forall y, In y es -> length (re_pad1 y) = 4%nat /\ length (re_pad2 y) = 4%nat)
    by (apply Forall_forall; exact Hpad).
  assert (Hpad' : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (set_nth j e' es)).
  { apply Forall_forall. intros y Hy. cbv beta. destruct (dr_in_set_nth rentry j e' y es Hy) as [-> | Hy'].
    - split; assumption.
    - apply Hall. exact (dr_in_rm rentry j y es Hy'). }
  rewrite length_app, (concat_entry_length es Hpad) in Htot.
  destruct (dra_len_split rentry es j Hj) as [Hfl Hsl].
  assert (HX : length (bzs (concat (map entry_bytes (firstn j es)))) = (56 * j)%nat).
  { rewrite dra_bzs_length, concat_entry_length, Hfl by (apply dra_Forall_firstn; exact Hpad). reflexivity. }
  assert (HZ : length (bzs (concat (map entry_bytes (skipn (S j) es)))) = (56 * (length es - S j))%nat).
  { rewrite dra_bzs_length, concat_entry_length, Hsl by (apply dra_Forall_skipn; exact Hpad). reflexivity. }
  assert (HE0 : length (bzs (entry_bytes (nth j es dr_e0))) = 56%nat).
  { assert (Hin : In (nth j es dr_e0) es) by (apply nth_In; exact Hj).
    destruct (Hall _ Hin) as [H1 H2]. rewrite dra_bzs_length. apply entry_bytes_length; assumption. }
  assert (HE' : length (bzs (entry_bytes e')) = 56%nat)
    by (rewrite dra_bzs_length; apply entry_bytes_length; assumption).
  pose proof (dra_bzs_length tail) as HT.
  assert (Hfr : forall a, G <= a < G + ATABLE -> ~ (G + AENT * Z.of_nat j <= a < G + AENT * Z.of_nat j + AENT) ->
     mbyte segs (arm W' mem') a = mbyte segs (arm W mem) a).
  { intros a Ha Hn. unfold arm. apply mbyte_of_aview. exact (Hview a Ha Hn). }
  split; [rewrite set_nth_length; exact Htl|].
  split; [rewrite length_app, (concat_entry_length _ Hpad'), set_nth_length; exact Htot|].
  rewrite (dra_concat_set_split _ _ entry_bytes es j e' Hj).
  rewrite (dra_concat_split _ _ entry_bytes es j dr_e0 Hj) in Hg.
  rewrite !dra_bzs_app in Hg |- *.
  apply garr8_app in Hg as [Hg1 HgT]. apply garr8_app in Hg1 as [HgX Hg2]. apply garr8_app in Hg2 as [_ HgZ].
  apply garr8_app. split; [apply garr8_app; split; [|apply garr8_app; split]|].
  - apply (garr8_frame segs _ _ G _ HgX). intros a Ha. apply Hfr; unfold ATABLE, AENT in *; lia.
  - replace (G + Z.of_nat (length (bzs (concat (map entry_bytes (firstn j es))))))
      with (G + AENT * Z.of_nat j) by (unfold AENT; lia).
    exact Hge.
  - rewrite HE'. rewrite HE0 in HgZ. apply (garr8_frame segs _ _ _ _ HgZ). intros a Ha.
    apply Hfr; unfold ATABLE, AENT in *; lia.
  - rewrite !length_app, HE'. rewrite !length_app, HE0 in HgT. apply (garr8_frame segs _ _ _ _ HgT). intros a Ha.
    apply Hfr; unfold ATABLE, AENT in *; lia.
Qed.


(* one byte of a val_mem, as an aview; every byte of a val_mem is visible (W_relay_event.v re_av1 / re_av_ne) *)
Lemma dj_av1 : forall (W : world segs) (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict (w_H W) m) a n v -> (0 < n)%nat ->
  aview segs (w_H W) m a = Some (YO0f.le_byte v n 0).
Proof.
  intros W m a n v Hv Hn. specialize (Hv 0%nat Hn). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
  unfold aview. rewrite Hv. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 8) with 256. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma dj_av_ne : forall (W : world segs) (m : word -> option byte) a (n : nat) v x,
  val_mem segs (mrestrict (w_H W) m) a n v -> a <= x < a + Z.of_nat n -> aview segs (w_H W) m x <> None.
Proof.
  intros W m a n v x Hv Hx. unfold aview.
  assert (Hk : (Z.to_nat (x - a) < n)%nat) by lia.
  specialize (Hv (Z.to_nat (x - a)) Hk). rewrite Z2Nat.id in Hv by lia.
  replace (a + (x - a)) with x in Hv by lia. rewrite Hv. discriminate.
Qed.

(* copied from W_LLVMFuzzerTestOneInput_exit.v lx_afn_pre_at (W8SegExit) *)
Lemma dr_afn_pre_at : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  aframe_at cx false (frame_addr ly3 1 fpos) W mem ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HFR Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  (* the frame base is 320 or 336 below the entry sp, and 32-aligned *)
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { pose proof (Z.mod_divide (sp0 - 320) 16 ltac:(lia)) as _.
      assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  (* the chain: the entry's, with this frame pushed *)
  pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
  pose proof HFR as (HSV & _).
  assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
  { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
    pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
  clear Hpres0.
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hsp8 : sp0 mod 8 = 0).
  { assert (Hq : sp0 = 16 * (sp0 / 16)) by (pose proof (Z.div_mod sp0 16 ltac:(lia)); lia).
    rewrite Hq. replace (16 * (sp0 / 16)) with ((2 * (sp0 / 16)) * 8) by ring. apply Z_mod_mult. }
  assert (HCH : exists ch, achain ly3 (aview segs (w_H W) mem) (lf_F cx) sp0 ch).
  { destruct (Z_lt_ge_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
    - exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
      apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
      eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
        sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
        [ exact Hch0 | lia
        | intros a Ha; rewrite (HAB a ltac:(lia)); apply HSG; rewrite unsigned_lit_small by lia; intros HGa;
          pose proof (inG_low segs B pa_segs_low G_fr a HG HGa); lia
        | exact Hra8 | exact Hs016
        | unfold raZ in Hra40; lia | lia | exact Hsp8 | exact Hlt | rewrite HF32; lia ].
    - exists []. left. split; [right; left; rewrite HTOPeq; lia | reflexivity]. }
  destruct HCH as (ch & HCH).
  exists ch.
  eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
    [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
    | exact Hgp | exact Htp | ].
  rewrite Hsp. replace (s0Z regs) with sp0 by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  exact HCH.
Qed.
(* the cut's STKR (fr_lib_pre_cf's last conjunct) at a callee's sp F = lf_F cx: the arm's own window
   [sp0 - LLVMF_STK, sp0) is present (the journal's presence clause), and above sp0 the journal keeps the entry's view
   (its view clause above alloc_ceiling outside the window; G_fr is image, below it) *)
Lemma dr_stkr : forall cx fpos ly S (W : world segs) mem md k,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k ->
  forall a, lf_F cx <= a < ly_top ly -> aview segs (w_H W) mem a <> None.
Proof.
  intros cx fpos ly S W mem md k HB HJ a Ha.
  pose proof dr_ceil_lo as HCL.
  destruct HB as (_ & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STKR & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
  unfold LLVMF_STK in Hslo.
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k HJ) as (memS & HJ0 & HSG).
  rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & HLY & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & Hpres & _).
  assert (Etop : ly_top ly = ly_top (c_ly cx)) by (pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx) by (unfold lf_F; lia).
  destruct (Z_lt_le_dec a (spZ (c_regs cx))) as [Hlt | Hge].
  - apply aview_some_of_apresent. apply Hpres. unfold LLVMF_STK. lia.
  - rewrite (F1 a ltac:(lia) ltac:(lia)). rewrite HSG.
    + apply STKR. rewrite <- Etop. lia.
    + rewrite unsigned_lit_small by lia. intros HGa. pose proof (pa_segs_low a (proj1 (HG a HGa))).
      unfold kLowMemEnd in *. lia.
Qed.

Lemma dr_aframe_false : forall cx FF (W : world segs) mem, aframe_at cx true FF W mem -> aframe_at cx false FF W mem.
Proof.
  intros cx FF W mem (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13).
  repeat (split; [assumption|]). split; [intros H; discriminate H|]. exact A13.
Qed.

(* A call to a program function inside this walk (W_gesture_end.v gx_callS, W4Gesture), with the callee's afn_pre
   given (dr_afn_pre_at builds it at sp = F): the callee's contract applied at its entry, and its journal - with XO /
   OUT, an out-parameter cell of the caller's frame inside the callee's raised window - composed into the caller's
   (W_journal.v ajournal_gx_sub). *)
Lemma dr_callZ : forall G W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1
  XO1 OUT1 (o : Z) raw ch1
  (K : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  gx_ok segs B G ->
  ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o <= 0 -> STK1 - o <= STK ->
  0 <= XO1 -> o + XO1 <= 0 -> (forall a, inFP OUT1 a -> sp0 - STK <= a < sp0) ->
  getr regsc 1 = raw ->
  afn_pre segs B STK1 lyc Sc W regsc memc mdc ch1 ->
  SRr segs W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
   (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
    ajournal_gx segs B G XO1 OUT1 STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 /\
    aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
   in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  SRr segs W (mkCfg (mkst regsc pc memc (seg_rom segs)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2 k1,
   c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
   ajournal_gx segs B G 0 [] STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + k1) /\
   ajournal_gx segs B G XO1 OUT1 STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 /\
   aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
  intros G W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 XO1 OUT1 o raw ch1 K
    HGx HJ Hsp Hneg Hbud HXO HXO2 HOUT Hra HPRE Hcallee HF.
  eapply SRr_mono; [exact Hcallee|].
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HK).
  exists ly2, S2, regs2, mem2, md2, k1. split; [reflexivity|].
  rewrite Hsp in HJ1.
  split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
  change own with ([] ++ own).
  pose proof HJ as (HS0 & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & (_ & HS1 & _) & _).
  eapply (ajournal_gx_sub segs B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | lia | | exact HGx | exact HF].
  intros a Ha. left. exact (HOUT a Ha).
Qed.


(* a callee-saved register across a call (W_LLVMFuzzerTestOneInput_latch.v lt_pres) *)
Lemma dj_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac dj_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.
(* every byte of every range of fp is a byte the predicate glob names, or a byte of one of the blocks bl, inside
   its requested size *)
Definition fp_in (fp : list (Z * Z)) (glob : Z -> Prop) (bl : list (Z * Z)) : Prop :=
  forall r, In r fp -> forall a, fst r <= a < snd r -> glob a \/ exists b, In b bl /\ fst b <= a < fst b + snd b.
(* fp_in grows with its two arguments *)
Lemma dj_fp_in_mono : forall fp (g1 g2 : Z -> Prop) bl1 bl2,
  fp_in fp g1 bl1 -> (forall a, g1 a -> g2 a) -> (forall b, In b bl1 -> In b bl2) -> fp_in fp g2 bl2.
Proof.
  intros fp g1 g2 bl1 bl2 H Hg Hb r Hr a Ha. destruct (H r Hr a Ha) as [Ga | (b & Hb1 & Hb2)].
  - left. exact (Hg a Ga).
  - right. exists b. split; [exact (Hb b Hb1) | exact Hb2].
Qed.
Lemma dj_fp_in_app : forall f1 f2 g bl, fp_in f1 g bl -> fp_in f2 g bl -> fp_in (f1 ++ f2) g bl.
Proof.
  intros f1 f2 g bl H1 H2 r Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr]; [exact (H1 r Hr) | exact (H2 r Hr)].
Qed.
Lemma dra_fp_in_nil : forall (g : Z -> Prop) bl, fp_in [] g bl.
Proof. intros g bl r Hr. destruct Hr. Qed.
Lemma dra_fp_in_cons : forall lo hi fp (g : Z -> Prop) bl,
  (forall a, lo <= a < hi -> g a \/ exists b, In b bl /\ fst b <= a < fst b + snd b) -> fp_in fp g bl ->
  fp_in ((lo, hi) :: fp) g bl.
Proof. intros lo hi fp g bl H1 H2 r [<- | Hr]; [exact H1 | exact (H2 r Hr)]. Qed.
Lemma dra_fp_in_map : forall (X : Type) (f : X -> Z * Z) (xs : list X) (g : Z -> Prop) bl,
  (forall x, In x xs -> forall a, fst (f x) <= a < snd (f x) -> g a \/ exists b, In b bl /\ fst b <= a < fst b + snd b) ->
  fp_in (map f xs) g bl.
Proof. intros X f xs g bl H r Hr. apply in_map_iff in Hr as (x & <- & Hx). exact (H x Hx). Qed.
Lemma dra_fp_in_concat : forall (X : Type) (f : X -> list (Z * Z)) (xs : list X) (g : Z -> Prop) bl,
  (forall x, In x xs -> fp_in (f x) g bl) -> fp_in (concat (map f xs)) g bl.
Proof.
  intros X f xs g bl H r Hr. apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (x & <- & Hx).
  exact (H x Hx r Hr).
Qed.
(* the lengths of a vector's records and of a key-pointer array (local copies of dr_concat_len / dr_key_ptrs_len) *)
Lemma dra_concat_text_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, IH.
  replace (length (text_rec r)) with 16%nat by (unfold text_rec; rewrite length_app; reflexivity). cbn [length]. lia.
Qed.
Lemma dra_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8. cbn [length]. lia.
Qed.
Lemma dj_alist_fp : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> fp_in (alist_fp LA l) (fun a => LA <= a < LA + 16) (alist_blks l).
Proof.
  intros ly S W mem LA l lines (_ & _ & _ & _ & H5 & H6 & _).
  unfold alist_fp, alist_blks, gfp.
  apply dra_fp_in_cons; [intros a Ha; left; exact Ha|].
  apply dj_fp_in_app.
  - destruct (Z.eqb_spec (hl_cap l) 0) as [E | E]; [apply dra_fp_in_nil|].
    destruct H6 as [(Hc & _) | (Hc & Hin & Hj & Hg)]; [lia|].
    apply dra_fp_in_cons; [|apply dra_fp_in_nil].
    intros a Ha. right. exists (hl_v l, AREC * hl_cap l).
    split; [apply in_or_app; left; left; reflexivity|]. cbn [fst snd].
    rewrite dra_bzs_length, length_app, dra_concat_text_len in Ha. unfold hl_n in Hj. unfold AREC in *. lia.
  - apply dra_fp_in_map. intros r Hr a Ha. cbn [fst snd] in Ha.
    rewrite dra_bzs_length, length_app in Ha. cbn [length] in Ha.
    right. exists (fst r, Z.of_nat (length (snd r)) + 1).
    split; [apply in_or_app; right; apply in_map_iff; exists r; split; [reflexivity | exact Hr]|].
    cbn [fst snd]. lia.
Qed.
Lemma dj_asrc_fp : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> fp_in (asrc_fp HA h) (fun a => HA <= a < HA + ASRC) (asrc_blks h).
Proof.
  intros ly S W mem HA h
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & _ & H19 & _ & _ & H22 & H23 & _).
  unfold asrc_fp, asrc_blks.
  apply dra_fp_in_cons; [intros a Ha; left; exact Ha|].
  unfold gfp at 1. apply dra_fp_in_cons.
  { intros a Ha. right. exists (hs_partial h, APARTIAL). split; [left; reflexivity|]. cbn [fst snd].
    rewrite dra_bzs_length in Ha. lia. }
  apply dj_fp_in_app; [|apply dj_fp_in_app].
  - apply (dj_fp_in_mono _ _ _ _ _ (dj_alist_fp ly S W mem (HA + 16) (hs_pending h) false H10)).
    + intros a Ha. unfold ASRC. lia.
    + intros b Hb. right. apply in_or_app. left. exact Hb.
  - apply (dj_fp_in_mono _ _ _ _ _ (dj_alist_fp ly S W mem (HA + 64) (hs_expected h) true H22)).
    + intros a Ha. unfold ASRC. lia.
    + intros b Hb. right. apply in_or_app. right. apply in_or_app. left. exact Hb.
  - apply (dj_fp_in_mono _ _ _ _ _ (dj_alist_fp ly S W mem (HA + 80) (hs_held h) true H23)).
    + intros a Ha. unfold ASRC. lia.
    + intros b Hb. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
Qed.
Lemma dj_aentry_fp : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> Z.of_nat (length (re_keys e)) <= re_nheld e ->
  fp_in (aentry_fp e) (fun _ => False) (aentry_blks e).
Proof.
  intros ly S W mem e (_ & _ & _ & _ & _ & _ & H7 & _ & _ & H10 & _ & H12 & _ & _ & _) Hk.
  unfold aentry_fp, aentry_blks, gfp.
  apply dj_fp_in_app.
  - destruct (Z.eqb_spec (re_cap e) 0) as [E | E]; [apply dra_fp_in_nil|].
    destruct H10 as [(Hc & _) | (Hc & Hin & Hj & Hg)]; [lia|].
    apply dra_fp_in_cons; [|apply dra_fp_in_nil].
    intros a Ha. right. exists (re_buf e, re_cap e).
    split; [apply in_or_app; left; left; reflexivity|]. cbn [fst snd].
    rewrite dra_bzs_length, length_app in Ha. lia.
  - apply dra_fp_in_cons.
    + intros a Ha. rewrite dra_bzs_length, dra_key_ptrs_len in Ha.
      destruct H12 as [(Hz & Hkeys) | (Hz & Hin & Hk1 & Hk2 & Hg)].
      * rewrite Hkeys in Ha. cbn [length] in Ha. lia.
      * right. exists (re_hp e, re_kh e). split.
        -- apply in_or_app. right. apply in_or_app. left. rewrite (proj2 (Z.eqb_neq _ _) Hz). left. reflexivity.
        -- cbn [fst snd]. lia.
    + apply dra_fp_in_map. intros k Hk' a Ha. cbn [fst snd] in Ha.
      rewrite dra_bzs_length, length_app in Ha. cbn [length] in Ha.
      right. eexists.
      split; [apply in_or_app; right; apply in_or_app; right; apply in_map_iff; exists k; split; [reflexivity | exact Hk']|].
      cbn [fst snd]. lia.
Qed.
Lemma dj_arelay_fp : forall ly S (W : world segs) mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) es ->
  fp_in (arelay_fp fr_RG G es)
    (fun a => rg_src fr_RG <= a < rg_src fr_RG + 8 \/ rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 \/
              rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4)
    (arelay_blks G es).
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _) Hk.
  unfold arelay_fp, arelay_blks.
  apply dra_fp_in_cons; [intros a Ha; left; left; exact Ha|].
  apply dra_fp_in_cons; [intros a Ha; left; right; left; exact Ha|].
  apply dra_fp_in_cons; [intros a Ha; left; right; right; exact Ha|].
  apply dra_fp_in_cons; [intros a Ha; right; exists (G, ATABLE); split; [left; reflexivity | cbn [fst snd]; lia]|].
  apply dra_fp_in_concat. intros e He. rewrite Forall_forall in H10, Hk.
  apply (dj_fp_in_mono _ _ _ _ _ (dj_aentry_fp ly S W mem e (H10 e He) (Hk e He))).
  - intros a Ha. destruct Ha.
  - intros b Hb. right. apply in_concat. exists (aentry_blks e).
    split; [apply in_map_iff; exists e; split; [reflexivity | exact He] | exact Hb].
Qed.
Lemma dj_aout_fp : forall ly S (W : world segs) mem c O mx no cap out,
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  fp_in (aout_fp B fr_RG cap out) (fun a => exists r, In r (aout_fp B fr_RG 0 0) /\ fst r <= a < snd r)
    (aout_blks cap out).
Proof.
  intros ly S W mem c O mx no cap out _.
  assert (E : aout_fp B fr_RG cap out = aout_fp B fr_RG 0 0 ++ (if cap =? 0 then [] else [(out, out + cap)]))
    by reflexivity.
  rewrite E. apply dj_fp_in_app.
  - intros r Hr a Ha. left. exists r. split; [exact Hr | exact Ha].
  - unfold aout_blks. destruct (Z.eqb_spec cap 0) as [Ec | Ec]; [apply dra_fp_in_nil|].
    apply dra_fp_in_cons; [|apply dra_fp_in_nil].
    intros a Ha. right. exists (out, cap). split; [left; reflexivity | cbn [fst snd]; lia].
Qed.

(* ---- the state at `jal pthread_mutex_lock` (0x84a50) on the eof = 0 path: lcut's facts at the found entry,
   with s9 = the new in.p, F+192 = 0 (at), F+40 = &g_lock, a0 = &g_lock, ra = 0x84a54 ---- *)
Definition DLK (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
  c = mkCfg (mkst regs (Z_to_bv 64 (SIGMA WS_pthread_mutex_lock)) mem (seg_rom segs)) md /\
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k /\
  aframe_at cx true (frame_addr ly3 1 fpos) W mem /\ sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
  amodel_at B ly3 S3 W mem m /\
  ainput_at B cx ly3 S3 W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly3 S3 /\ LS cx t m ly3 S3 /\ RINV cx t m /\
  dr_at_op cx m /\ dr_pick cx m si h /\ (j < length (lm_es m))%nat /\
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ re_eof (nth j (lm_es m) dr_e0) = 0 /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) 0 /\
  sv8 W mem (lf_F cx + 40) (rg_lock fr_RG) /\
  getr regs 1 = Z_to_bv 64 (BASE + A_dc_r1) /\ getr regs 10 = w64 (rg_lock fr_RG) /\
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (frame_addr ly3 1 fpos + 32) /\ getr regs 20 = w64 10 /\
  getr regs 23 = w64 HI_G_NSRC /\ getr regs 24 = w64 (SB + frame_addr ly3 1 fpos / 8) /\ getr regs 26 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 27 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\ getr regs 22 = w64 (lm_G m + AENT * Z.of_nat j) /\
  getr regs 25 = w64 (c_p cx + dr_k' cx m).

(* ---- the eof = 0 path, cut at each return point.  dc_regs: the registers the six calls keep (all callee-saved);
   amodel_ne: amodel_at with g_lock's state a parameter and errno's value free (check_no_loss_read,
   check_no_loss and check_shape_done keep no errno byte, so the stream's ctl takes errno's value at the end) ---- *)
Definition dc_regs (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (FF : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (FF + 32) /\ getr regs 20 = w64 10 /\
  getr regs 23 = w64 HI_G_NSRC /\ getr regs 24 = w64 (SB + FF / 8) /\ getr regs 26 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 27 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\ getr regs 22 = w64 (lm_G m + AENT * Z.of_nat j) /\
  getr regs 25 = w64 (c_p cx + dr_k' cx m).
Definition dc_ctl (c : ctl) (ev : Z) : ctl := CTL (ct_cl c) (ct_br c) (ct_dd c) (ct_ei c) ev.
Definition amodel_ne (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (m : lmod)
  (held : bool) : Prop :=
  length (lm_hs m) = 4%nat /\ (forall i, (i < 4)%nat -> aslot B ly S W mem i (nth i (lm_hs m) None)) /\
  arelay_at B fr_RG ly S W mem (lm_G m) (lm_es m) /\
  (exists ev, aout_at B fr_RG ly S W mem (dc_ctl (lm_c m) ev) (lm_O m) (lm_mx m) (Z.of_nat (length (lm_O m)))
                (lm_cap m) (lm_out m)) /\
  agone_at fr_RG W mem (lm_gn m) /\ alock_at fr_RG W mem held /\ awake_at fr_RG W mem /\
  val_mem segs (arm W mem) AG_NFD 4 (lm_nfd m) /\ awr W mem AG_NFD 4 /\ 0 <= lm_nfd m <= OPS_MAX /\
  val_mem segs (arm W mem) AG_THREAD_UP 1 0 /\
  (exists lst, val_mem segs (arm W mem) AG_LISTEN 4 lst) /\ awr W mem AG_LISTEN 4.
(* a state of the eof = 0 path at BASE + pc: the journal from the entry, the frame and fake frame (with lcut's flag
   word at FF + 120), the input, the ROM and the jump table, in.n at F+144, `at` = A at F+192, &g_lock at F+40, the
   model mc (lock state held), its blocks' separation, and the entries' key-count bound *)
Definition dc_at (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (fpos FF pc : Z) (ly : alayout) (S : astate)
  (mc : lmod) (held : bool) (A : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md k,
    c = mkCfg (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom segs)) md /\
    dc_regs cx t m j si FF regs /\
    ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k /\
    frame_addr ly 1 fpos = FF /\
    aframe_at cx true FF W mem /\ sv8 W mem (FF + 120) (flag_addr ly 1 fpos) /\
    ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
    sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) A /\
    sv8 W mem (lf_F cx + 40) (rg_lock fr_RG) /\
    amodel_ne ly S W mem mc held /\ ablocks_sep B fr_FP cx mc ly S /\
    Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es mc).

(* the drain's functional half (dr_step_ok's first part, with the new entry's paddings from dr_post's aentry_ok) and
   check_no_loss's (its second part, with cnl_post's bound on the held list's capacity) *)
Definition dr_dfun (m : lmod) (si : nat) (h : hsrc) (j : nat) (e' : rentry) (h' : hsrc) (LB : list byte) : Prop :=
  let e := nth j (lm_es m) dr_e0 in
  let fin := dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) e h in
  re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
  re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
  re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
  drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
  NoDup (drain_b_c.keys_texts (re_keys e')) /\
  same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
  hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
  hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
  hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
  map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
  hs_held h' = hs_held h /\
  re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
  bzs LB = with_nul (dr_lines h) /\
  hl_cap (hs_expected h') = drain_b_c.ds_ecap fin /\
  length (re_pad1 e') = 4%nat /\ length (re_pad2 e') = 4%nat.
Definition dr_cfun (h' : hsrc) (E' H' : hlist) : Prop :=
  hl_recs E' = [] /\ hl_v E' = hl_v (hs_expected h') /\ hl_cap E' = hl_cap (hs_expected h') /\
  NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h')) (texts (hs_expected h')) /\
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h'))
                              (2 * (hl_n (hs_held h') + Z.of_nat (count_begin (texts (hs_expected h')))))).
(* the stream and the controller's buffer after the drain, and the model after it (in.k not yet advanced) *)
Definition dr_O1 (m : lmod) (h : hsrc) (LB : list byte) : list byte :=
  if dr_live (lm_c m) h then lm_O m ++ LB else lm_O m.
Definition dr_cap1 (m : lmod) (j : nat) (h : hsrc) : Z :=
  if dr_live (lm_c m) h
  then drain_b_c.ds_ocap (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
  else lm_cap m.
Definition dr_m1 (m : lmod) (j si : nat) (h h' : hsrc) (e' : rentry) (ev' : Z) (LB : list byte) (out' : Z) : lmod :=
  dr_step m (lm_k m) si h' j e' (dr_ctl (lm_c m) h ev') (dr_O1 m h LB) (dr_cap1 m j h) out'.
Definition dc_setsrc (mc : lmod) (si : nat) (h : hsrc) : lmod :=
  LM (lm_k mc) (set_nth si (Some h) (lm_hs mc)) (lm_G mc) (lm_es mc) (lm_c mc) (lm_O mc) (lm_mx mc) (lm_cap mc)
     (lm_out mc) (lm_gn mc) (lm_nfd mc).
Definition dc_fin (cx : lfcx) (m mc : lmod) (ev : Z) : lmod :=
  LM (dr_k' cx m) (lm_hs mc) (lm_G mc) (lm_es mc) (dc_ctl (lm_c mc) ev) (lm_O mc) (lm_mx mc) (lm_cap mc)
     (lm_out mc) (lm_gn mc) (lm_nfd mc).
Definition dc_static (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (h : hsrc) : Prop :=
  dr_at_op cx m /\ dr_pick cx m si h /\ (j < length (lm_es m))%nat /\
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ re_eof (nth j (lm_es m) dr_e0) = 0 /\ RINV cx t m.


(* ---- the composition's pure facts ---- *)
Lemma dc_set_nth_twice : forall (A : Type) n (x y : A) l, set_nth n x (set_nth n y l) = set_nth n x l.
Proof.
  intros A n. induction n as [|n IH]; intros x y [|z l]; cbn [set_nth]; try reflexivity. f_equal. apply IH.
Qed.
Lemma dc_ctl_dr : forall c h ev' ev, dc_ctl (dr_ctl c h ev') ev = dr_ctl c h ev.
Proof. intros c h ev' ev. reflexivity. Qed.
Lemma dc_bzs_inj : forall l1 l2, bzs l1 = bzs l2 -> l1 = l2.
Proof.
  induction l1 as [|b l1 IH]; intros [|b2 l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
(* the stream of the expected lines the drain appended is the bytes it relayed *)
Lemma dc_bstream_LB : forall (E : hlist) (L : list (list Z)) (LB : list byte),
  map snd (hl_recs E) = map (map (Z_to_bv 8)) L -> bzs LB = with_nul L -> bstream E = LB.
Proof.
  intros E L LB HM HB. apply dc_bzs_inj. rewrite HB. unfold bstream, with_nul.
  assert (HR : Forall (fun l => Forall (fun z => 0 <= z < 256) l) L).
  { assert (HZ : Forall (fun z => 0 <= z < 256) (with_nul L)).
    { rewrite <- HB. unfold bzs. apply Forall_map. apply Forall_forall. intros b _. unfold bz.
      pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr. exact Hr. }
    unfold with_nul in HZ. clear - HZ. induction L as [|l L IH]; [constructor|].
    cbn [map concat] in HZ. apply Forall_app in HZ as [H1 H2]. apply Forall_app in H1 as [H1 _].
    constructor; [exact H1 | exact (IH H2)]. }
  replace (map (fun r : Z * list byte => snd r ++ [Z_to_bv 8 0]) (hl_recs E))
    with (map (fun l => l ++ [Z_to_bv 8 0]) (map snd (hl_recs E))) by (rewrite map_map; reflexivity).
  rewrite HM. clear HM HB. induction L as [|l L IH]; [reflexivity|].
  inversion HR as [|l0 L0 Hl HL]; subst. cbn [map concat]. unfold bzs in *. rewrite !map_app.
  rewrite IH by exact HL. f_equal. f_equal. rewrite map_map.
  rewrite <- (map_id l) at 2. apply map_ext_in. intros z Hz. rewrite Forall_forall in Hl.
  unfold bz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. exact (Hl z Hz).
Qed.
Lemma dc_LB_len : forall (LB : list byte) L, bzs LB = with_nul L -> Z.of_nat (length LB) = Z.of_nat (length (with_nul L)).
Proof. intros LB L H. rewrite <- H. unfold bzs. rewrite length_map. reflexivity. Qed.

(* ---- transports shared by the stages ---- *)
(* the facts of dc_at that are not the model: the frame, the fake frame's flag word (FL), the input, the ROM, the
   jump table and the three cells *)
Definition dc_ctxp (cx : lfcx) (m : lmod) (FF A FL : Z) (ly : alayout) (S : astate) (W : world segs)
  (mem : word -> option byte) : Prop :=
  aframe_at cx true FF W mem /\ sv8 W mem (FF + 120) FL /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) A /\
  sv8 W mem (lf_F cx + 40) (rg_lock fr_RG).

(* ---------------- dt_: the kit the five transports share ---------------- *)
(* membership in a literal list (W_rep.v w_infp, which its Section keeps) *)
Ltac dt_infp := repeat (first [left; reflexivity | right]).
(* (a) a range that lies inside one read-only segment of the pinned image *)
Definition dt_romb (lo hi : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) &&
    ((Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))) segs.
Lemma dt_rom_of : forall lo hi a, dt_romb lo hi = true -> lo <= a < hi -> in_rom segs a.
Proof.
  intros lo hi a H Ha. unfold dt_romb in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [H0 Hb]. apply andb_prop in Hb as [H1 H2].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hs | split; [exact H0 | lia]].
Qed.
(* the jump table's 36 bytes are read-only image bytes (vm_compute over the pinned segments) *)
Lemma dj_jt_rom : forall a, fr_jtab <= a < fr_jtab + 36 -> in_rom segs a.
Proof. intros a Ha. exact (dt_rom_of fr_jtab (fr_jtab + 36) a ltac:(vm_compute; reflexivity) Ha). Qed.

(* (b) the addresses of the globals the model names, as literals, for the apartness side conditions *)
Lemma dt_rgv : rg_s fr_RG = 0x5d88e0 /\ rg_src fr_RG = 0x5d87c0 /\ rg_nsrc fr_RG = 0x5d87a0 /\
  rg_capsrc fr_RG = 0x5d8800 /\ rg_out fr_RG = 0x5d8b40 /\ rg_nout fr_RG = 0x5d88c0 /\
  rg_capout fr_RG = 0x5d8b20 /\ rg_send_max fr_RG = 0x5d8840 /\ rg_send_eintr fr_RG = 0x5d88a0 /\
  rg_send_dead fr_RG = 0x5d8880 /\ rg_gone fr_RG = 0x5d8860 /\ rg_client fr_RG = 0xa1fe0 /\
  rg_client_broken fr_RG = 0x5d87e0 /\ rg_lock fr_RG = 0x5d8ac0 /\ rg_wake fr_RG = 0xa1fa0.
Proof. repeat split; reflexivity. Qed.
Lemma dt_cst : ASRC = 96 /\ AG_NFD = 0x5d8820 /\ AG_THREAD_UP = 0x5d8760 /\ AG_LISTEN = 0xa1fc0.
Proof. repeat split; reflexivity. Qed.
(* every arithmetic side condition of this block: the literals, errno's place, and lia *)
Ltac dt_num :=
  let V := fresh "V" in pose proof dt_rgv as V; destruct V as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&?);
  let C := fresh "C" in pose proof dt_cst as C; destruct C as (?&?&?&?);
  pose proof HERR_HI; lia.

(* (c) each global cell the model reads is one of the entry's G_fr *)
Lemma dt_G_s : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Proof. exact HGs. Qed.
Lemma dt_G_lock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a.
Proof. exact HGlock. Qed.
Lemma dt_G_src : forall a, rg_src fr_RG <= a < rg_src fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_src fr_RG, 8).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_nsrc : forall a, rg_nsrc fr_RG <= a < rg_nsrc fr_RG + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_nsrc fr_RG, 4).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_capsrc : forall a, rg_capsrc fr_RG <= a < rg_capsrc fr_RG + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_capsrc fr_RG, 4).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_smax : forall a, rg_send_max fr_RG <= a < rg_send_max fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_send_max fr_RG, 8).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_client : forall a, rg_client fr_RG <= a < rg_client fr_RG + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_client fr_RG, 4).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_sdead : forall a, rg_send_dead fr_RG <= a < rg_send_dead fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_send_dead fr_RG, 1).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_gone : forall a, rg_gone fr_RG <= a < rg_gone fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_gone fr_RG, 1).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_wake : forall a, rg_wake fr_RG <= a < rg_wake fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (rg_wake fr_RG, 8).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_nfd : forall a, AG_NFD <= a < AG_NFD + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (AG_NFD, 4).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_up : forall a, AG_THREAD_UP <= a < AG_THREAD_UP + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (AG_THREAD_UP, 1).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_listen : forall a, AG_LISTEN <= a < AG_LISTEN + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_GK, Exists_exists. exists (AG_LISTEN, 4).
  split; [unfold DR_GK; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_cbr : forall a, rg_client_broken fr_RG <= a < rg_client_broken fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_client_broken fr_RG, 1).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_sei : forall a, rg_send_eintr fr_RG <= a < rg_send_eintr fr_RG + 1 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_send_eintr fr_RG, 1).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_nout : forall a, rg_nout fr_RG <= a < rg_nout fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_nout fr_RG, 8).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_capout : forall a, rg_capout fr_RG <= a < rg_capout fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_capout fr_RG, 8).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_out : forall a, rg_out fr_RG <= a < rg_out fr_RG + 8 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (rg_out fr_RG, 8).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Lemma dt_G_err : forall a, as_errno B <= a < as_errno B + 4 -> inG G_fr a.
Proof. intros a Ha. apply HG_DR, Exists_exists. exists (as_errno B, 4).
  split; [unfold G_DR, G_SL; dt_infp | unfold in_zr; cbn [fst snd]; lia]. Qed.
Ltac dt_ing := solve
  [ apply dt_G_s; dt_num | apply dt_G_src; lia | apply dt_G_nsrc; lia | apply dt_G_capsrc; lia
  | apply dt_G_smax; lia | apply dt_G_client; lia | apply dt_G_sdead; lia | apply dt_G_gone; lia
  | apply dt_G_wake; lia | apply dt_G_nfd; lia | apply dt_G_up; lia | apply dt_G_listen; lia
  | apply dt_G_cbr; lia | apply dt_G_sei; lia | apply dt_G_nout; lia | apply dt_G_capout; lia
  | apply dt_G_out; lia | apply dt_G_err; lia | apply dt_G_lock; lia ].

(* (d) a byte whose view is kept, and which is a G_fr byte or lies off the image, is kept *)
Lemma dt_G_rng : forall a, inG G_fr a -> 0x10000 <= a < 0x5fb000.
Proof. intros a Hg. exact (pa_img_range a (proj1 (HG a Hg))). Qed.
Lemma dt_rom_rng : forall a, in_rom segs a -> 0x10000 <= a < 0x5fb000.
Proof. intros a (sg & Hs & _ & Hr). apply pa_img_range. exists sg. split; [exact Hs | exact Hr]. Qed.
Lemma dt_bkG : forall (W W' : world segs) mem mem' a, inG G_fr a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Hg Ha. pose proof (dt_G_rng a Hg).
  apply dj_bk; [lia | intros _; exact Hg | exact Ha].
Qed.
Lemma dt_bkN : forall (W W' : world segs) mem mem' a, 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W') mem' a = aview segs (w_H W) mem a -> abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Hr Hi Ha. apply dj_bk; [exact Hr | intros H; exfalso; exact (Hi H) | exact Ha].
Qed.
(* the requested size of a block covers its own bytes *)
Lemma dt_reqr : forall p n a, p <= a < p + n -> p <= a < p + req_size n.
Proof. intros p n a H. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma dt_reqi : forall p n a, p <= a < p + n -> 0 <= a - p < req_size n.
Proof. intros p n a H. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
Lemma dt_akept1 : forall (W W' : world segs) mem mem' lo hi,
  (forall x, lo <= x < hi -> abyte_kept W mem W' mem' x) -> akept W mem W' mem' [(lo, hi)].
Proof. intros W W' mem mem' lo hi H r Hr a Ha. destruct Hr as [<- | []]. exact (H a Ha). Qed.
(* a ROM byte's view is the image's at both ends *)
Lemma dt_romkeep : forall (W W' : world segs) mem mem', rom_view segs W mem -> rom_view segs W' mem' ->
  forall a, in_rom segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Proof. intros W W' mem mem' R R' a Ha. rewrite (R' a Ha), (R a Ha). reflexivity. Qed.
Lemma dt_shadow : forall x, SB + x / 8 = shadow_addr x.
Proof. intros x. reflexivity. Qed.

(* (e) the two keepers the model's transport runs on *)
Definition dt_KG (W : world segs) (mem : word -> option byte) (W' : world segs)
  (mem' : word -> option byte) : Prop :=
  forall a, inG G_fr a -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
    ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W mem W' mem' a.
Definition dt_KB (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
  (W' : world segs) (mem' : word -> option byte) : Prop :=
  forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + n -> abyte_kept W mem W' mem' a.

(* (f) the blocks each component of the model names are live *)
Lemma dt_alist_blks : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem LA l lines (_ & _ & _ & _ & _ & H6 & _ & _ & H9) b Hb.
  unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct H6 as [(Hc & _) | (Hcp & Hin & _)].
    + rewrite (proj2 (Z.eqb_eq (hl_cap l) 0) Hc) in Hb. destruct Hb.
    + assert (Ec : (hl_cap l =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite Ec in Hb. destruct Hb as [<- | []]. exact Hin.
  - apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in H9. exact (proj1 (H9 r Hr)).
Qed.
Lemma dt_asrc_blks : forall ly S (W : world segs) mem HA h,
  asrc_at B ly S W mem HA h -> forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem HA h
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & H18 & _ & _ & _ & H22 & H23 & _) b Hb.
  destruct Hb as [<- | Hb]; [exact H18|].
  apply in_app_or in Hb as [Hb | Hb];
    [exact (dt_alist_blks ly S W mem (HA + 16) (hs_pending h) false H10 b Hb)|].
  apply in_app_or in Hb as [Hb | Hb];
    [exact (dt_alist_blks ly S W mem (HA + 64) (hs_expected h) true H22 b Hb)
    | exact (dt_alist_blks ly S W mem (HA + 80) (hs_held h) true H23 b Hb)].
Qed.
Lemma dt_aentry_blks : forall ly S (W : world segs) mem e,
  aentry_ok B ly S W mem e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem e (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & H12 & _ & _ & H15) b Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct H10 as [(Hc & _) | (Hcp & Hin & _)].
    + rewrite (proj2 (Z.eqb_eq (re_cap e) 0) Hc) in Hb. destruct Hb.
    + assert (Ec : (re_cap e =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite Ec in Hb. destruct Hb as [<- | []]. exact Hin.
  - apply in_app_or in Hb as [Hb | Hb].
    + destruct H12 as [(Hz & _) | (Hz & Hin & _)].
      * rewrite (proj2 (Z.eqb_eq (re_hp e) 0) Hz) in Hb. destruct Hb.
      * assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz).
        rewrite Ez in Hb. destruct Hb as [<- | []]. exact Hin.
    + apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
Lemma dt_arelay_blks : forall ly S (W : world segs) mem G es,
  arelay_at B fr_RG ly S W mem G es -> forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & H8 & _ & H10 & _) b Hb.
  destruct Hb as [<- | Hb]; [exact H8|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  rewrite Forall_forall in H10. exact (dt_aentry_blks ly S W mem e (H10 e He) b Hb).
Qed.
Lemma dt_aout_blks : forall ly S (W : world segs) mem c O mx no cap out,
  aout_at B fr_RG ly S W mem c O mx no cap out -> forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
  intros ly S W mem c O mx no cap out
    (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& H26) b Hb.
  unfold aout_blks in Hb. destruct H26 as [(Hc & _) | (Hcp & _ & Hin & _)].
  - rewrite (proj2 (Z.eqb_eq cap 0) Hc) in Hb. destruct Hb.
  - assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Ec in Hb. destruct Hb as [<- | []]. exact Hin.
Qed.

(* (g) the output stream, with errno re-read at the new state *)
Lemma dt_aoutg : forall a, (exists r, In r (aout_fp B fr_RG 0 0) /\ fst r <= a < snd r) ->
  inG G_fr a /\ ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8).
Proof.
  intros a (r & Hin & Ha). unfold aout_fp in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd] in Ha;
    (split; [dt_ing | dt_num]).
Qed.
Lemma dt_aout_ne : forall ly S (W : world segs) mem (W' : world segs) mem' c O mx no cap out ev,
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  dt_KG W mem W' mem' -> dt_KB ly S W mem W' mem' ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  aout_at B fr_RG ly S W' mem' (dc_ctl c ev) O mx no cap out.
Proof.
  intros ly S W mem W' mem' c O mx no cap out ev HO KG KB HEV HEW HEB.
  assert (AK : forall lo hi, In (lo, hi) (aout_fp B fr_RG cap out) ->
                 (forall x, lo <= x < hi -> ~ (as_errno B <= x < as_errno B + 4)) ->
                 forall x, lo <= x < hi -> abyte_kept W mem W' mem' x).
  { intros lo hi Hin Hne x Hx.
    destruct (dj_aout_fp ly S W mem c O mx no cap out HO (lo, hi) Hin x Hx) as [Hg | ([p n] & Hb & Hab)].
    - destruct (dt_aoutg x Hg) as (P1 & P2). exact (KG x P1 P2 (Hne x Hx)).
    - cbn [fst snd] in Hab.
      exact (KB p n x (dt_aout_blks ly S W mem c O mx no cap out HO (p, n) Hb) Hab). }
  pose proof HO as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 &
                    _ & _ & _ & H20 & H21 & H22 & H23 & H24 & H25 & H26).
  unfold dc_ctl. cbn [ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_send_max fr_RG) (rg_send_max fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H1]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_send_max fr_RG) (rg_send_max fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_nout fr_RG) (rg_nout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H3]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_nout fr_RG) (rg_nout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_capout fr_RG) (rg_capout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H5]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_capout fr_RG) (rg_capout fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_out fr_RG) (rg_out fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H7]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_out fr_RG) (rg_out fr_RG + 8));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_client fr_RG) (rg_client fr_RG + 4));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H9]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_client fr_RG) (rg_client fr_RG + 4));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx;
    apply (AK (rg_client_broken fr_RG) (rg_client_broken fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H11]|].
  split; [apply (akept_awr W mem); [intros x Hx;
    apply (AK (rg_client_broken fr_RG) (rg_client_broken fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_send_dead fr_RG) (rg_send_dead fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H13]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_send_dead fr_RG) (rg_send_dead fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (AK (rg_send_eintr fr_RG) (rg_send_eintr fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | dt_num] | exact H15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply (AK (rg_send_eintr fr_RG) (rg_send_eintr fr_RG + 1));
    [unfold aout_fp; dt_infp | intros y Hy; dt_num | lia] | exact H16]|].
  split; [exact HEV|]. split; [exact HEW|]. split; [exact HEB|].
  split; [exact H20|]. split; [exact H21|]. split; [exact H22|]. split; [exact H23|].
  split; [exact H24|]. split; [exact H25|].
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|]. split; [exact Hno|]. split; [exact Hin|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  exact (KB out cap x (dt_aout_blks ly S W mem c O mx no cap out HO (out, cap)
           ltac:(unfold aout_blks; rewrite Ec; left; reflexivity)) ltac:(lia)).
Qed.

(* (h) the model, under the two keepers, with the lock and errno given at the new state *)
Lemma dt_ne_core : forall ly S (W : world segs) mem (W' : world segs) mem' m (held held' : bool) ev,
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m) ->
  amodel_ne ly S W mem m held ->
  dt_KG W mem W' mem' -> dt_KB ly S W mem W' mem' ->
  alock_at fr_RG W' mem' held' ->
  val_mem segs (arm W' mem') (as_errno B) 4 ev -> awr W' mem' (as_errno B) 4 -> 0 <= ev < 2 ^ 32 ->
  amodel_ne ly S W' mem' m held'.
Proof.
  intros ly S W mem W' mem' m held held' ev HK
    (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13) KG KB HLK HEV HEW HEB.
  split; [exact M1|].
  split.
  { intros i Hi. pose proof (M2 i Hi) as Mi. assert (Hi4 : Z.of_nat i < 4) by lia.
    unfold aslot in Mi |- *. destruct (nth i (lm_hs m) None) as [h|].
    - apply (asrc_at_kept B ly S W mem ly S W' mem' (rg_s fr_RG + ASRC * Z.of_nat i) h Mi).
      + intros r Hr a Ha.
        destruct (dj_asrc_fp ly S W mem (rg_s fr_RG + ASRC * Z.of_nat i) h Mi r Hr a Ha)
          as [Hg | ([p n] & Hb & Hab)].
        * apply KG; [apply dt_G_s; dt_num | dt_num | dt_num].
        * cbn [fst snd] in Hab.
          exact (KB p n a (dt_asrc_blks ly S W mem _ h Mi (p, n) Hb) Hab).
      + intros b Hb. exact (dt_asrc_blks ly S W mem _ h Mi b Hb).
    - destruct Mi as (G1 & G2).
      assert (HL : length (repeat 0 (Z.to_nat ASRC)) = 96%nat) by (vm_compute; reflexivity).
      split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite HL in Hx.
        apply KG; [apply dt_G_s; dt_num | dt_num | dt_num].
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply KG; [apply dt_G_s; dt_num | dt_num | dt_num]. }
  split.
  { apply (arelay_at_kept B fr_RG ly S W mem ly S W' mem' (lm_G m) (lm_es m) M3).
    - intros r Hr a Ha.
      destruct (dj_arelay_fp ly S W mem (lm_G m) (lm_es m) M3 HK r Hr a Ha) as [Hg | ([p n] & Hb & Hab)].
      + destruct Hg as [Hg | [Hg | Hg]]; apply KG; solve [dt_ing | dt_num].
      + cbn [fst snd] in Hab.
        exact (KB p n a (dt_arelay_blks ly S W mem (lm_G m) (lm_es m) M3 (p, n) Hb) Hab).
    - intros b Hb. exact (dt_arelay_blks ly S W mem (lm_G m) (lm_es m) M3 b Hb). }
  split.
  { destruct M4 as (ev0 & HO). exists ev.
    exact (dt_aout_ne ly S W mem W' mem' (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
             (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) ev HO KG KB HEV HEW HEB). }
  split.
  { apply (agone_at_kept fr_RG W mem W' mem' (lm_gn m) M5).
    apply dt_akept1. intros x Hx. apply KG; [apply dt_G_gone; lia | dt_num | dt_num]. }
  split; [exact HLK|].
  split.
  { apply (awake_at_kept fr_RG W mem W' mem' M7).
    apply dt_akept1. intros x Hx. apply KG; [apply dt_G_wake; lia | dt_num | dt_num]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx.
    apply KG; [apply dt_G_nfd; dt_num | dt_num | dt_num]. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx.
    apply KG; [apply dt_G_nfd; lia | dt_num | dt_num]. }
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx.
    apply KG; [apply dt_G_up; dt_num | dt_num | dt_num]. }
  split.
  { destruct M12 as (lst & Hlst). exists lst. apply (akept_vm W mem); [|exact Hlst]. intros x Hx.
    apply KG; [apply dt_G_listen; dt_num | dt_num | dt_num]. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx.
  apply KG; [apply dt_G_listen; lia | dt_num | dt_num].
Qed.

(* a pthread_mutex_lock / _unlock step (aj_gx_entry_at's post): every byte but the lock word and the entry's
   scratch [sp - ESTACK, sp) keeps its view *)
Lemma dj_ne_lockstep : forall ly S (W : world segs) mem md mem' m (held held' : bool) sp,
  AR segs B ly S W mem md ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m) ->
  amodel_ne ly S W mem m held ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) -> ~ (sp - ESTACK <= a < sp) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  alloc_ceiling + 8 <= sp - ESTACK ->
  val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 (if held' then 16 else 0) ->
  amodel_ne ly S W mem' m held'.
Proof.
  intros ly S W mem md mem' m held held' sp HAR HK HM KV Hsp HLW.
  pose proof asan_consts as ((HCL & HCU) & _).
  (* every G_fr byte but the lock word keeps its view, so it is kept *)
  assert (KGall : forall a, inG G_fr a -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
                    abyte_kept W mem W mem' a).
  { intros a Hg Hl. pose proof (dt_G_rng a Hg) as Hr.
    apply dt_bkG; [exact Hg|]. apply KV; [lia | exact Hl | lia]. }
  assert (KG : dt_KG W mem W mem') by (intros a Hg Hl _; exact (KGall a Hg Hl)).
  (* a live block's bytes are no image bytes, so they are no lock word either *)
  assert (KB : dt_KB ly S W mem W mem').
  { intros p n a Hin Ha.
    destruct (dr_blk B LAWS ly S W mem md p n HAR Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img segs B LAWS ly S W mem md p n a HAR Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; apply Hni; exact (proj1 (HG a (dt_G_lock a ltac:(lia)))) | lia]. }
  pose proof HM as (_ & _ & _ & (ev0 & HO) & _ & M6 & _).
  (* the lock: its two other words are kept, its lock word is the premise, its cells stay writable *)
  assert (HLK : alock_at fr_RG W mem' held').
  { destruct M6 as (L1 & L2 & L3 & L4).
    split; [apply (akept_vm W mem); [|exact L1]; intros x Hx;
      apply KGall; [apply dt_G_lock; dt_num | dt_num]|].
    split; [exact HLW|].
    split; [apply (akept_vm W mem); [|exact L3]; intros x Hx;
      apply KGall; [apply dt_G_lock; dt_num | dt_num]|].
    intros i Hi. exact (GWR _ _ (rg_lock fr_RG + i) (dt_G_lock (rg_lock fr_RG + i) ltac:(lia))). }
  (* errno keeps its view (it is above every global the lock step touches) *)
  pose proof HO as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& E1 & E2 & E3 & _).
  assert (KE : forall x, as_errno B <= x < as_errno B + 4 -> abyte_kept W mem W mem' x)
    by (intros x Hx; apply KGall; [apply dt_G_err; lia | dt_num]).
  exact (dt_ne_core ly S W mem W mem' m held held' (ct_ev (dc_ctl (lm_c m) ev0)) HK HM KG KB HLK
           (akept_vm W mem W mem' (as_errno B) 4 (ct_ev (dc_ctl (lm_c m) ev0))
              ltac:(intros x Hx; apply KE; dt_num) E1)
           (akept_awr W mem W mem' (as_errno B) 4 ltac:(intros x Hx; apply KE; lia) E2) E3).
Qed.

(* (i) the context: the frame, the input, the ROM, the jump table and the three cells *)
Lemma dt_aframe_kept : forall cx full FF (W W' : world segs) mem mem',
  aframe_at cx full FF W mem ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W' mem' a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  lf_F cx + 320 <= spZ (c_regs cx) ->
  aframe_at cx full FF W' mem'.
Proof.
  intros cx full FF W W' mem mem'
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    KS KF KFS HF.
  assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) -> sv8 W mem a v -> sv8 W' mem' a v)
    by (intros a v H1 H2 Hv; apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KS; lia | exact Hv]).
  assert (KVF : forall a v, FF <= a -> a + 8 <= FF + 128 -> sv8 W mem a v -> sv8 W' mem' a v)
    by (intros a v H1 H2 Hv; apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KF; lia | exact Hv]).
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | exact (A1 o r Hin)]. }
  split; [apply (akept_awr W mem); [intros x Hx; apply KS; lia | exact A2]|].
  do 9 (split; [apply KV; [lia | lia | assumption]|]).
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    do 6 (split; [apply KV; [lia | lia | assumption]|]).
    apply KV; [lia | lia | assumption]. }
  split; [apply KVF; [lia | lia | exact A13]|].
  split; [apply KVF; [lia | lia | exact A14]|].
  split; [apply KVF; [lia | lia | exact A15]|].
  split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact A16]|].
  split; [|apply (akept_awr W mem); [intros x Hx; apply KFS; lia | exact (proj2 A17)]].
  apply (akept_garr8 W mem); [|exact (proj1 A17)]. intros x Hx.
  unfold fake_shadow in Hx. cbn [length] in Hx. apply KFS. lia.
Qed.
Lemma dt_ainput_kept : forall cx ly S (W : world segs) mem (W' : world segs) mem',
  ainput_at B cx ly S W mem -> Z.of_nat (length (c_pl cx)) = c_n cx ->
  dt_KB ly S W mem W' mem' -> ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem W' mem' (H1 & H2) Hlen KB.
  split; [exact H1|]. apply (akept_garr8 W mem); [|exact H2].
  intros x Hx. rewrite length_map, Hlen in Hx.
  destruct H1 as [(Hn0 & _) | (Hn & Hin)]; [lia|]. exact (KB (c_p cx) (c_n cx) x Hin Hx).
Qed.
(* sp and the frame base of this call, from the entry's contract *)
Lemma dt_spF : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  alloc_ceiling + 32768 <= spZ (c_regs cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 352 < lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) /\
  Z.of_nat (length (c_pl cx)) = c_n cx.
Proof.
  intros cx (_ & HP & _ & _ & _ & _ & Hlen & _).
  destruct HP as (_ & _ & _ & _ & _ & (_ & _ & H3 & H4 & H5 & H6 & _) & _).
  unfold LLVMF_STK in H4. unfold lf_F.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)).
  repeat split; lia.
Qed.
Lemma dt_ctx_core : forall cx m FF A FL ly S (W : world segs) mem (W' : world segs) mem',
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  dc_ctxp cx m FF A FL ly S W mem ->
  (forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  dt_KB ly S W mem W' mem' -> rom_view segs W' mem' ->
  dc_ctxp cx m FF A FL ly S W' mem'.
Proof.
  intros cx m FF A FL ly S W mem W' mem' HLB (HFR & HFL & HIN & HRV & HJT & HN & HAT & HL) KS KF KFS KB HRV'.
  destruct (dt_spF cx HLB) as (Q1 & Q2 & Q3 & Q4 & Q5).
  assert (KS' : forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W' mem' a)
    by (intros a Ha; apply KS; lia).
  split; [exact (dt_aframe_kept cx true FF W W' mem mem' HFR KS' KF KFS Q4)|].
  split; [apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KF; lia | exact HFL]|].
  split; [exact (dt_ainput_kept cx ly S W mem W' mem' HIN Q5 KB)|].
  split; [exact HRV'|].
  split.
  { intros i Hi k Hk.
    assert (Hrm : in_rom segs (fr_jtab + 4 * i + Z.of_nat k)) by (apply dj_jt_rom; lia).
    rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (fr_jtab + 4 * i + Z.of_nat k)
               (dt_romkeep W W' mem mem' HRV HRV' (fr_jtab + 4 * i + Z.of_nat k) Hrm)).
    exact (HJT i Hi k Hk). }
  split; [apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KS; unfold DR_N in *; lia | exact HN]|].
  split; [apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KS; unfold DR_AT in *; lia | exact HAT]|].
  apply (dr_sv8_kept W W' mem mem'); [intros x Hx; apply KS; lia | exact HL].
Qed.

Lemma dj_ctx_lockstep : forall cx m FF A FL ly S (W : world segs) mem md mem',
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  AR segs B ly S W mem md -> (exists pos, In (1, pos) (frames S) /\ FF = frame_addr ly 1 pos) ->
  dc_ctxp cx m FF A FL ly S W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) ->
     ~ (lf_F cx - ESTACK <= a < lf_F cx) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  dc_ctxp cx m FF A FL ly S W mem'.
Proof.
  intros cx m FF A FL ly S W mem md mem' HLB HAR (pos & Hfin & HFF) HCX KV HPR.
  pose proof asan_consts as ((HCL & HCU) & HSE & _ & HME & HLE).
  assert (HES : ESTACK = 4096) by reflexivity.
  destruct (dt_spF cx HLB) as (Q1 & Q2 & Q3 & Q4 & Q5).
  destruct (frames_bounds segs B LAWS ly S W mem md 1 pos HAR Hfin) as (HF1 & HF2 & _).
  change (fs_frame_bytes 1) with 128 in HF2. rewrite <- HFF in HF1, HF2.
  pose proof (dt_shadow FF) as Hsh.
  pose proof (shadow_addr_bounds FF ltac:(lia)) as Hsb.
  pose proof (shadow_addr_bounds (FF + 128) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end FF 128 ltac:(lia)) as Hsr.
  assert (Hlockimg : forall a, rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8 -> in_img segs a)
    by (intros a Ha; exact (proj1 (HG a (dt_G_lock a ltac:(lia))))).
  (* the stack above the frame base: off the image, above the entry's scratch *)
  assert (KS : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  (* the fake frame and its shadow: both off the image, both below the entry's scratch *)
  assert (KF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a)
      by (apply (frm_img segs B LAWS ly S W mem md 1 pos a HAR Hfin);
          rewrite <- HFF; change (fs_frame_bytes 1) with 128; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  assert (KFS : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  (* the live blocks: off the image, below the entry's scratch *)
  assert (KB : dt_KB ly S W mem W mem').
  { intros p n a Hin Ha.
    destruct (dr_blk B LAWS ly S W mem md p n HAR Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img segs B LAWS ly S W mem md p n a HAR Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    apply KV; [lia | intros Hc; exact (Hni (Hlockimg a Hc)) | lia]. }
  (* the read-only image: no G_fr byte is read-only, and it is far below the entry's scratch *)
  assert (HRV' : rom_view segs W mem').
  { pose proof HCX as (_ & _ & _ & HRV & _). intros a Ha. pose proof (dt_rom_rng a Ha) as Hr.
    rewrite (KV a ltac:(lia) ltac:(intros Hc; exact (proj1 (DR_ROM_OUT a Ha) (dt_G_lock a ltac:(lia))))
               ltac:(lia)).
    exact (HRV a Ha). }
  exact (dt_ctx_core cx m FF A FL ly S W mem W mem' HLB HCX KS KF KFS KB HRV').
Qed.

(* a leaf callee (aleaf_post's journal: no footprint, the allocator state kept) called at sp = F *)
Lemma dj_ne_plain : forall ly S (W W' : world segs) mem mem' md md' m held STK sp,
  ajournal segs B STK sp [] ly S W mem md [] ly S W' mem' md' 0 -> alloc_ceiling + 8 <= sp - STK ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m) ->
  amodel_ne ly S W mem m held -> amodel_ne ly S W' mem' m held.
Proof.
  intros ly S W W' mem mem' md md' m held STK sp HJ Hsp HK HM.
  pose proof asan_consts as ((HCL & HCU) & _).
  pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & F3 & _).
  (* every G_fr byte but errno is an image byte the journal keeps *)
  assert (KGall : forall a, ~ (as_errno B <= a < as_errno B + 4) -> inG G_fr a ->
                    abyte_kept W mem W' mem' a).
  { intros a He Hg. destruct (HG a Hg) as (Hi & Ho & _).
    apply dt_bkG; [exact Hg|].
    apply F3; [exact Hi | exact Ho | exact He |].
    apply fp_spares_closed. intros (r & Hr & _). destruct Hr. }
  assert (KG : dt_KG W mem W' mem') by (intros a Hg _ He; exact (KGall a He Hg)).
  (* every live block's bytes: nothing is in the empty footprint *)
  assert (KB : dt_KB ly S W mem W' mem').
  { intros p n a Hin Ha.
    destruct (dr_blk B LAWS ly S W' mem' md' p n HAR' Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img segs B LAWS ly S W' mem' md' p n a HAR' Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    replace a with (p + (a - p)) by lia.
    apply (F2 p n (a - p) Hin Hin (dt_reqi p n a Ha)). intros Hc. exact (inFP_nil _ Hc). }
  pose proof HM as (_ & _ & _ & _ & _ & M6 & _).
  assert (HLK : alock_at fr_RG W' mem' held).
  { apply (alock_at_kept fr_RG W mem W' mem' held M6). apply dt_akept1. intros x Hx.
    apply KGall; [dt_num | apply dt_G_lock; lia]. }
  destruct (ERR ly S W' mem' md' HAR') as ((ev & HEV & HEB) & HEW).
  exact (dt_ne_core ly S W mem W' mem' m held held ev HK HM KG KB HLK HEV HEW HEB).
Qed.
Lemma dj_ctx_plain : forall cx m FF A FL ly S (W W' : world segs) mem mem' md md' STK,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal segs B STK (lf_F cx) [] ly S W mem md [] ly S W' mem' md' 0 -> 0 <= STK <= 16384 ->
  (exists pos, In (1, pos) (frames S) /\ FF = frame_addr ly 1 pos) ->
  dc_ctxp cx m FF A FL ly S W mem -> dc_ctxp cx m FF A FL ly S W' mem'.
Proof.
  intros cx m FF A FL ly S W W' mem mem' md md' STK HLB HJ HSTK (pos & Hfin & HFF) HCX.
  pose proof asan_consts as ((HCL & HCU) & HSE & _ & HME & HLE).
  destruct (dt_spF cx HLB) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
  destruct (frames_bounds segs B LAWS ly S W' mem' md' 1 pos HAR' Hfin) as (HF1 & HF2 & _).
  change (fs_frame_bytes 1) with 128 in HF2. rewrite <- HFF in HF1, HF2.
  pose proof (dt_shadow FF) as Hsh.
  pose proof (shadow_addr_bounds FF ltac:(lia)) as Hsb.
  pose proof (shadow_addr_bounds (FF + 128) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end FF 128 ltac:(lia)) as Hsr.
  (* the stack above the frame base *)
  assert (KS : forall a, lf_F cx <= a < 2 ^ 64 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|]. apply F1; lia. }
  (* the fake frame of class 1 and its shadow, both outside the empty footprint *)
  assert (KF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a)
      by (apply (frm_img segs B LAWS ly S W' mem' md' 1 pos a HAR' Hfin);
          rewrite <- HFF; change (fs_frame_bytes 1) with 128; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply (F4 1 pos a Hfin); [left | intros Hc; exact (inFP_nil _ Hc)].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- HFF.
    change (fs_frame_bytes 1) with 128. lia. }
  assert (KFS : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (pa_segs_low a Hi) as Hb; lia).
    apply dt_bkN; [lia | exact Hni|].
    apply (F4 1 pos a Hfin); [right | intros Hc; exact (inFP_nil _ Hc)].
    unfold in_zr. cbn [fst snd]. rewrite <- HFF.
    change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. rewrite <- dt_shadow. lia. }
  assert (KB : dt_KB ly S W mem W' mem').
  { intros p n a Hin Ha.
    destruct (dr_blk B LAWS ly S W' mem' md' p n HAR' Hin) as (P1 & P2 & P3).
    assert (Hni : ~ in_img segs a)
      by exact (blk_img segs B LAWS ly S W' mem' md' p n a HAR' Hin (dt_reqr p n a Ha)).
    apply dt_bkN; [lia | exact Hni|].
    replace a with (p + (a - p)) by lia.
    apply (F2 p n (a - p) Hin Hin (dt_reqi p n a Ha)). intros Hc. exact (inFP_nil _ Hc). }
  (* the ROM: the journal's own rom_view, at G = [] (W_journal.v ajournal_gx_rom_view) *)
  assert (HRO : rom_out segs B []).
  { intros a Ha. destruct (DR_ROM_OUT a Ha) as (_ & R2 & R3 & R4).
    split; [intros Hc; exact (inG_nil a Hc)|]. split; [exact R2 | split; [exact R3 | exact R4]]. }
  assert (HJx : ajournal_gx segs B [] 0 [] STK (lf_F cx) [] ly S W mem md [] ly S W' mem' md' 0)
    by (apply ajournal_gx_nil; exact HJ).
  assert (HRV' : rom_view segs W' mem').
  { pose proof HCX as (_ & _ & _ & HRV & _).
    eapply ajournal_gx_rom_view; first [exact HJx | exact HRO | exact HRV | exact LAWS | exact pa_segs_low]. }
  exact (dt_ctx_core cx m FF A FL ly S W mem W' mem' HLB HCX KS KF KFS KB HRV').
Qed.


Lemma dc_ctl_eta : forall c, dc_ctl c (ct_ev c) = c.
Proof. intros [cl br dd ei ev]. reflexivity. Qed.
Lemma dj_ne_of_at : forall ly S (W : world segs) mem m, amodel_at B ly S W mem m -> amodel_ne ly S W mem m false.
Proof.
  intros ly S W mem m (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
  split; [exists (ct_ev (lm_c m)); rewrite dc_ctl_eta; exact M4|].
  repeat (split; [assumption|]). exact M13.
Qed.

(* ---- the six stages ---- *)

Lemma dc_stA : forall cx t m j si h fpos ly3 S3 k W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  DLK cx t m j si h fpos ly3 S3 k W c ->
  SRr segs W c (dc_at cx t m j si fpos (frame_addr ly3 1 fpos) A_dc_r1 ly3 S3 m true 0).
Proof.
  intros cx t m j si h fpos ly3 S3 k W c HB
    (regs & mem & md & -> & HJ & HFR & HFL & HMOD & HIN & HRV & HROM & HSEP & HLS & HRI & Hatop & Hpick & Hj & Hfdj & Hef0 &
     SVN & S192 & S40 & Q1 & Q10 & R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof HMOD as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (FF := frame_addr ly3 1 fpos) in *.
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  assert (VLK : rg_lock fr_RG = 0x5d8ac0) by reflexivity.
  pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.

  assert (Ho16 : (F - sp0) mod 16 = 0).
  { assert (HF32' : F = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
    pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
    rewrite HF32'.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }

  (* ---- pthread_mutex_lock(&g_lock) ---- *)
  assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly3 S3 a).
  { intros a Ha Ho. destruct (HG a (HGlock a Ha)) as (Hi & Hno & _).
    apply Hno. exact (proj1 (al_owned_image _ _ LAWS ly3 S3 W mem _ a HAR Hi) Ho). }
  assert (AVL : aview segs (w_H W) mem (rg_lock fr_RG) = Some 0).
  { pose proof (dj_av1 W mem (rg_lock fr_RG) 4%nat 0 LK0 ltac:(lia)) as HA.
    replace (YO0f.le_byte 0 4 0) with 0 in HA by (vm_compute; reflexivity). exact HA. }
  eapply SRr_bind.
  { eapply (aj_gx_entry_at B LAWS G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
      (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
      (fun _ mem' => val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 16)
      W regs mem LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly3 S3 md k (F - sp0) _ HG eq_refl HJ
      ltac:(rewrite Hsp; lia) Ho16
      ltac:(lia) ltac:(lia) ltac:(unfold ESTACK, LLVMF_STK; lia) R3 R4 Q1
      (ret_ok_codeptr_v A_dc_r1 ltac:(unfold A_dc_r1, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl)).
    - intros a. lia.
    - intros a Hwa _. exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 0 a LK4 ltac:(cbn; lia)).
    - intros a Hwa HnG. exfalso. apply HnG. apply HGlock. lia.
    - intros HPRE2 HSC2.
      exact (ALOCK ly3 S3 W regs mem _ (rg_lock fr_RG) 0 HPRE2
        Q10 ltac:(lia) ltac:(rewrite VLK; reflexivity) ltac:(lia) AVL eq_refl LK4
        ltac:(intros a Ha; split;
              [ destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [Hlt | Hge];
                [ exact (dj_av_ne W mem (rg_lock fr_RG) 4%nat 0 a LK0 ltac:(cbn; lia))
                | exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 0 a LK4 ltac:(cbn; lia)) ]
              | rewrite Hsp; unfold ESTACK, DR_CEIL8 in *; lia ])
        ltac:(intros a Ha; split;
              [ replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; exact (LKW (a - rg_lock fr_RG) ltac:(lia))
              | split; [ apply HNOWN; lia | rewrite Hsp; unfold ESTACK, DR_CEIL8 in *; lia ] ])). }
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJa & HPa & Hlk2 & Hfra & Hpresa).

  assert (PR2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r)
    by (intros r Hr; exact (dj_pres regs regs2 r HPa Hr)).
  assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) -> ~ (F - ESTACK <= a < F) ->
      aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha H1 H2; apply Hfra; [exact Ha | exact H1 | replace (sp0 + (F - sp0)) with F by lia; exact H2]).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  assert (HKY : Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es m))
    by (apply Forall_forall; intros e _; apply dr_keys_le).
  pose proof (dj_ne_lockstep ly3 S3 W mem md mem2 m false true F HAR HKY (dj_ne_of_at ly3 S3 W mem m HMOD) KL
                ltac:(unfold ESTACK, DR_CEIL8 in *; lia) Hlk2) as HNE2.
  pose proof (dj_ctx_lockstep cx m FF 0 (flag_addr ly3 1 fpos) ly3 S3 W mem md mem2 HB HAR
                (ex_intro _ fpos (conj Hfin eq_refl))
                (conj HFR (conj HFL (conj HIN (conj HRV (conj HROM (conj SVN (conj S192 S40))))))) KL Hpresa)
    as (HFR2 & HFL2 & HIN2 & HRV2 & HROM2 & SVN2 & S1922 & S402).
  apply SRr_ret.
  exists regs2, mem2, md2, k. split; [reflexivity|].
  split.
  { unfold dc_regs.
    rewrite !PR2 by dj_cs.
    repeat (split; [assumption|]). exact R25. }
  split; [exact HJa|]. split; [reflexivity|].
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HROM2|].
  split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
  split; [exact HNE2|]. split; [exact HSEP|]. exact HKY.
Qed.
(* ---- dc_stB's helpers (dcB_) ---- *)
(* permutations of block lists, by counting occurrences *)
Definition dcB_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
Lemma dcB_cnt_cons : forall g l x,
  count_occ dcB_dec (g :: l) x = ((if dcB_dec g x then 1 else 0) + count_occ dcB_dec l x)%nat.
Proof. intros g l x. cbn [count_occ]. destruct (dcB_dec g x); reflexivity. Qed.
Ltac dcB_perm := apply (Permutation_count_occ dcB_dec); intros ?x;
  repeat first [rewrite count_occ_app | rewrite dcB_cnt_cons]; lia.
(* the live blocks at the call, split as drain's contract takes them *)
Lemma dcB_perm_pre : forall (L I CA CS OB R0 ea hb CA' CS' : list (Z * Z)) g,
  Permutation L (I ++ (g :: CA ++ CS ++ OB) ++ R0) ->
  Permutation CA (ea ++ CA') -> Permutation CS (hb ++ CS') ->
  Permutation L (g :: ea ++ hb ++ OB ++ (CA' ++ CS' ++ I ++ R0)).
Proof. intros L I CA CS OB R0 ea hb CA' CS' g H HA HS. rewrite H, HA, HS. dcB_perm. Qed.
(* drain's `rest` is everything the call did not name *)
Lemma dcB_perm_rest : forall (L ea hb ob T rest : list (Z * Z)) g,
  Permutation L (g :: ea ++ hb ++ ob ++ T) -> Permutation L (ea ++ hb ++ ob ++ rest) ->
  Permutation rest (g :: T).
Proof.
  intros L ea hb ob T rest g H1 H2. apply (Permutation_app_inv_l (ea ++ hb ++ ob)).
  transitivity L; [rewrite <- !app_assoc; symmetry; exact H2|].
  rewrite H1. dcB_perm.
Qed.
(* the live blocks after the call, as the model after it names them *)
Lemma dcB_perm_post : forall (L2 I R0 CA2 CS2 OB' ea' hb' CA' CS' rest : list (Z * Z)) g,
  Permutation L2 (ea' ++ hb' ++ OB' ++ rest) -> Permutation rest (g :: CA' ++ CS' ++ I ++ R0) ->
  Permutation CA2 (ea' ++ CA') -> Permutation CS2 (hb' ++ CS') ->
  Permutation L2 (I ++ (g :: CA2 ++ CS2 ++ OB') ++ R0).
Proof. intros L2 I R0 CA2 CS2 OB' ea' hb' CA' CS' rest g H1 H2 H3 H4. rewrite H1, H2, H3, H4. dcB_perm. Qed.
(* duplicate-free lists *)
Lemma dcB_nd_app : forall (X R : list (Z * Z)) b, List.NoDup (X ++ R) -> In b X -> In b R -> False.
Proof.
  induction X as [|x X IH]; intros R b Hnd Hx Hr; [destruct Hx|].
  inversion Hnd as [|y l Hni Hnd' Heq]; subst.
  destruct Hx as [<- | Hx]; [apply Hni; apply in_or_app; right; exact Hr | exact (IH R b Hnd' Hx Hr)].
Qed.
Lemma dcB_nd_r : forall (X R : list (Z * Z)), List.NoDup (X ++ R) -> List.NoDup R.
Proof. induction X as [|x X IH]; intros R H; [exact H|]. inversion H; subst. apply IH. assumption. Qed.
Lemma dcB_in_rest : forall (L X rest : list (Z * Z)) b, List.NoDup L -> Permutation L (X ++ rest) -> In b rest ->
  ~ In b X /\ In b L.
Proof.
  intros L X rest b Hnd HP Hb. split.
  - intros Hx. exact (dcB_nd_app X rest b (Permutation_NoDup HP Hnd) Hx Hb).
  - apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hb.
Qed.
Lemma dcB_T_ne : forall (L X rest T : list (Z * Z)) g b, List.NoDup L -> Permutation L (X ++ rest) ->
  Permutation rest (g :: T) -> In b T -> b <> g.
Proof.
  intros L X rest T g b Hnd HP HR Hb ->.
  pose proof (dcB_nd_r X rest (Permutation_NoDup HP Hnd)) as H1.
  pose proof (Permutation_NoDup HR H1) as H2. inversion H2 as [|y l Hni _]; subst. exact (Hni Hb).
Qed.
Lemma dcB_in_rm_nth : forall (A : Type) (l : list A) (i j : nat) (d : A), (i < length l)%nat -> i <> j ->
  In (nth i l d) (firstn j l ++ skipn (S j) l).
Proof.
  intros A l. induction l as [|x l IH]; intros i j d Hi Hne; cbn [length] in Hi; [lia|].
  destruct i as [|i], j as [|j].
  - lia.
  - cbn [nth firstn skipn app]. left. reflexivity.
  - cbn [nth firstn skipn app]. change (skipn 0 l) with l. apply nth_In. lia.
  - cbn [nth firstn skipn app]. right. apply IH; lia.
Qed.
Lemma dcB_set_nth_nth : forall (A : Type) (l : list A) n d, set_nth n (nth n l d) l = l.
Proof. intros A l. induction l as [|x l IH]; intros [|n] d; cbn [set_nth nth]; try reflexivity. f_equal. apply IH. Qed.
(* every block the representation names has a positive size *)
Lemma dcB_pos_alist : forall ly S (W : world segs) mem LA l lines b,
  alist_at B ly S W mem LA l lines -> In b (alist_blks l) -> 0 < snd b.
Proof.
  intros ly S W mem LA l lines b (_ & _ & _ & _ & _ & H6 & _) Hb. unfold alist_blks in Hb.
  apply in_app_or in Hb as [Hb | Hb].
  - destruct (hl_cap l =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
    destruct Hb as [<- | []]. cbn [snd]. destruct H6 as [(Hc & _) | (Hc & _)]; [lia|]. unfold AREC. lia.
  - apply in_map_iff in Hb as (r & <- & _). cbn [snd]. lia.
Qed.
Lemma dcB_pos_asrc : forall ly S (W : world segs) mem HA h b,
  asrc_at B ly S W mem HA h -> In b (asrc_blks h) -> 0 < snd b.
Proof.
  intros ly S W mem HA h b
    (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H22 & H23 & _) Hb.
  unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [cbn [snd]; unfold APARTIAL; lia|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (dcB_pos_alist _ _ _ _ _ _ _ _ H10 Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (dcB_pos_alist _ _ _ _ _ _ _ _ H22 Hb) | exact (dcB_pos_alist _ _ _ _ _ _ _ _ H23 Hb)].
Qed.
Lemma dcB_pos_aentry : forall ly S (W : world segs) mem e b,
  aentry_ok B ly S W mem e -> In b (aentry_blks e) -> 0 < snd b.
Proof.
  intros ly S W mem e b (_ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _ & K12 & _ & _ & _) Hb.
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  - destruct (re_cap e =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
    destruct Hb as [<- | []]. cbn [snd]. destruct K10 as [(Hc & _) | (Hc & _)]; lia.
  - apply in_app_or in Hb as [Hb | Hb].
    + destruct (re_hp e =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
      destruct Hb as [<- | []]. cbn [snd]. destruct K12 as [(Hz & _) | (_ & _ & _ & Hk & _)]; lia.
    + apply in_map_iff in Hb as (kk & <- & _). cbn [snd]. lia.
Qed.
Lemma dcB_pos_aout : forall ly S (W : world segs) mem c O mx no cap out b,
  aout_at B fr_RG ly S W mem c O mx no cap out -> In b (aout_blks cap out) -> 0 < snd b.
Proof.
  intros ly S W mem c O mx no cap out b HO Hb.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
  unfold aout_blks in Hb. destruct (cap =? 0) eqn:E; [destruct Hb|]. apply Z.eqb_neq in E.
  destruct Hb as [<- | []]. cbn [snd]. destruct Hblk as [(Hc & _) | (Hc & _)]; lia.
Qed.
(* drain's G is the entry's; ROM is outside it; the cells amodel_ne keeps beside drain's G are outside it and errno *)
Lemma dcB_GDR_ok : gx_ok segs B (G_DR B fr_RG).
Proof. intros a Ha. exact (HG a (HG_DR a Ha)). Qed.
Lemma dcB_rom_out : rom_out segs B (G_DR B fr_RG).
Proof.
  intros a Ha. destruct (DR_ROM_OUT a Ha) as (H1 & H2 & H3 & H4).
  split; [intros HGa; exact (H1 (HG_DR a HGa))|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.
Lemma dcB_GK_out : forall a, inG DR_GK a \/ rg_lock fr_RG <= a < rg_lock fr_RG + 12 ->
  ~ inG (G_DR B fr_RG) a /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. pose proof HERR_HI as He.
  unfold inG, DR_GK, G_DR, G_SL in *. rewrite !Exists_cons, Exists_nil in *.
  unfold in_zr, AG_NFD, AG_THREAD_UP, AG_LISTEN, ASRC in *. cbn [fst snd] in *.
  cbn [fr_RG fr_globals rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *.
  lia.
Qed.
(* a model block of the call's footprint is the entry's footprint's or new since the entry *)
Lemma dcB_fp_blk : forall cx m ly S b a,
  ablocks_sep B fr_FP cx m ly S -> In b (model_blks m) -> 0 < snd b -> fst b <= a < fst b + req_size (snd b) ->
  (inFP (lf_FP fr_FP cx) a /\ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
  in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly S) a.
Proof.
  intros cx m ly S [p n] a ((rest & HP) & H2) Hb Hpos Ha. cbn [fst snd] in Hpos, Ha.
  assert (HbL : In (p, n) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
  destruct (in_dec dcB_dec (p, n) (ablocks B (c_ly cx) (c_S cx))) as [Hin | Hnin].
  - left. split; [|exists p, n; split; [exact HbL | exact Ha]].
    destruct (H2 _ Hb) as [Hc | Hc]; [exfalso; exact (Hc Hin)|].
    exact (Hc a Ha).
  - right. exists p, n. split; [exact HbL|]. split; [exact Hnin | exact Ha].
Qed.
(* a byte outside drain's footprint dr_fp SA e h cap out = (SA, SA + AENT) :: ablocks_fp X *)
Lemma dcB_nfp : forall G SA (X : list (Z * Z)) a,
  G <= SA -> SA + AENT <= G + ATABLE ->
  ~ (G <= a < G + ATABLE /\ SA <= a < SA + AENT) ->
  (forall b, In b X -> ~ (fst b <= a < fst b + req_size (snd b))) ->
  ~ inFP ((SA, SA + AENT) :: ablocks_fp X) a.
Proof.
  intros G SA X a H1 H2 H3 H4 (r & Hr & Ha). destruct Hr as [<- | Hr].
  - cbn [fst snd] in Ha. apply H3. split; lia.
  - unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha. exact (H4 b Hb Ha).
Qed.
Lemma dcB_nfp_blk : forall ly S (W : world segs) mem md G SA X p0 n0 a,
  AR segs B ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
  (forall b, In b X -> In b (ablocks B ly S)) ->
  In (p0, n0) (ablocks B ly S) -> ~ In (p0, n0) X -> p0 <= a < p0 + req_size n0 ->
  ((p0, n0) <> (G, ATABLE) \/ ~ (SA <= a < SA + AENT)) ->
  ~ inFP ((SA, SA + AENT) :: ablocks_fp X) a.
Proof.
  intros ly S W mem md G SA X p0 n0 a HAR HGin H1 H2 HXL Hb0 HnX Ha Hor.
  apply (dcB_nfp G); [exact H1 | exact H2 | |].
  - intros (Ht & Hs). destruct Hor as [Hne | Hn]; [|exact (Hn Hs)].
    apply (dj_apart ly S W mem md p0 n0 G ATABLE a HAR Hb0 HGin Hne Ha).
    replace (req_size ATABLE) with ATABLE by reflexivity. exact Ht.
  - intros [q r] Hb Hq. cbn [fst snd] in Hq.
    assert (Hne : (p0, n0) <> (q, r)) by (intros E; apply HnX; rewrite E; exact Hb).
    exact (dj_apart ly S W mem md p0 n0 q r a HAR Hb0 (HXL _ Hb) Hne Ha Hq).
Qed.
Lemma dcB_nfp_frm : forall ly S (W : world segs) mem md G SA X cid pos a,
  AR segs B ly S W mem md -> In (G, ATABLE) (ablocks B ly S) -> G <= SA -> SA + AENT <= G + ATABLE ->
  (forall b, In b X -> In b (ablocks B ly S)) -> In (cid, pos) (frames S) ->
  (frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8) ->
  ~ inFP ((SA, SA + AENT) :: ablocks_fp X) a.
Proof.
  intros ly S W mem md G SA X cid pos a HAR HGin H1 H2 HXL Hfr Ha.
  assert (HNB : forall p n, In (p, n) (ablocks B ly S) -> ~ (p <= a < p + req_size n)).
  { intros p n Hin Hpa.
    destruct (frames_bounds segs B LAWS ly S W mem md cid pos HAR Hfr) as (Hf0 & Hfc & _).
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
    pose proof (sep_block_frame segs B LAWS ly S W mem md p n cid pos HAR Hin Hfr) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(lia)) as Hs1.
    pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2.
    pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfb) as Hs3.
    unfold in_app, kLowShadowBeg in Happ.
    destruct Ha as [Ha | Ha]; lia. }
  apply (dcB_nfp G); [exact H1 | exact H2 | |].
  - intros (Ht & _). apply (HNB G ATABLE HGin). replace (req_size ATABLE) with ATABLE by reflexivity. exact Ht.
  - intros [q r] Hb Hq. exact (HNB q r (HXL _ Hb) Hq).
Qed.
(* the frame and the fake frame across a callee that keeps the frame's window, the fake frame and its shadow *)
Lemma dcB_aframe_kept : forall cx full FF (W W' : world segs) mem mem',
  aframe_at cx full FF W mem ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W' mem' a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  lf_F cx + 320 <= spZ (c_regs cx) ->
  aframe_at cx full FF W' mem'.
Proof.
  intros cx full FF W W' mem mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    KS KF KSh HF1.
  assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 Hv. apply (dr_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply KS. lia. }
  assert (KVF : forall a v, FF <= a -> a + 8 <= FF + 128 -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 Hv. apply (dr_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply KF. lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | exact (A1 o r Hin)]. }
  split; [apply (akept_awr W mem); [intros x Hx; apply KS; lia | exact A2]|].
  do 9 (split; [apply KV; [lia | lia | assumption]|]).
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    do 6 (split; [apply KV; [lia | lia | assumption]|]).
    apply KV; [lia | lia | assumption]. }
  do 3 (split; [apply KVF; [lia | lia | assumption]|]).
  split; [apply (akept_awr W mem); [intros x Hx; apply KF; lia | exact A16]|].
  split; [apply (akept_garr8 W mem); [|exact (proj1 A17)] | apply (akept_awr W mem); [|exact (proj2 A17)]].
  - intros x Hx. unfold fake_shadow in Hx. cbn [length] in Hx. apply KSh. lia.
  - intros x Hx. apply KSh. lia.
Qed.
(* the jump table is ROM: two ROM views read it alike *)
Lemma dcB_jt : forall (W W' : world segs) mem mem', rom_view segs W mem -> rom_view segs W' mem' ->
  jt_rom W mem -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' H1 H2 HJ i Hi kk Hk.
  rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (fr_jtab + 4 * i + Z.of_nat kk)); [exact (HJ i Hi kk Hk)|].
  assert (Hr : in_rom segs (fr_jtab + 4 * i + Z.of_nat kk)) by (apply dj_jt_rom; lia).
  rewrite (H2 _ Hr), (H1 _ Hr). reflexivity.
Qed.
(* a closed slot's 96 zero bytes read 0 in any 4-byte field *)
Lemma dcB_zero_vm : forall (mm : word -> option byte) a N o,
  garr8 segs mm a (repeat 0 N) -> 0 <= o -> o + 4 <= Z.of_nat N -> val_mem segs mm (a + o) 4 0.
Proof.
  intros mm a N o Hg Ho HN kk Hk.
  destruct (Hg (Z.to_nat o + kk)%nat ltac:(rewrite repeat_length; lia)) as [Hv _].
  specialize (Hv 0%nat ltac:(lia)). rewrite nth_repeat in Hv.
  replace (a + o + Z.of_nat kk) with (a + Z.of_nat (Z.to_nat o + kk) + Z.of_nat 0) by lia.
  rewrite Hv. do 4 (destruct kk as [|kk]; [reflexivity|]). lia.
Qed.
(* the model's blocks the call does not touch: the other entries', the other slots', the input, the driver's *)
Definition dcB_CA (es : list rentry) (j : nat) : list (Z * Z) := concat (map aentry_blks (firstn j es ++ skipn (S j) es)).
Definition dcB_CS (hs : list (option hsrc)) (si : nat) : list (Z * Z) :=
  concat (map slot_blks (firstn si hs ++ skipn (S si) hs)).
Definition dcB_T (cx : lfcx) (m : lmod) (j si : nat) (rest0 : list (Z * Z)) : list (Z * Z) :=
  dcB_CA (lm_es m) j ++ dcB_CS (lm_hs m) si ++ input_blks cx ++ rest0.
(* dr_post without the return configuration, the composed journal at G_fr and the callee-saved registers *)
Definition dcB_post (regs : bvmap 5 word) ly S (W : world segs) (mem : word -> option byte) (md : Model)
  (SA HA : Z) (e : rentry) (h : hsrc) (c : ctl) (O : list byte) (mx no cap out : Z)
  (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  : Prop :=
exists k (e' : rentry) (h' : hsrc) (out' ev' : Z) (LB : list byte) rest,
let fin := dr_fin c mx no cap e h in
let live := dr_live c h in
let cap' := if live then drain_b_c.ds_ocap fin else cap in
ajournal_gx segs B (G_DR B fr_RG) 0 [] DRAIN_STK (spZ regs) (dr_fp SA e h cap out) ly S W mem md [] ly' S' W' mem' md' k /\
apres_kept B W mem W' mem' /\
mo_le MT S S' (dr_cost MT c mx no cap e h) /\
Permutation (ablocks B ly S) (aentry_blks e ++ asrc_blks h ++ aout_blks cap out ++ rest) /\
Permutation (ablocks B ly' S') (aentry_blks e' ++ asrc_blks h' ++ aout_blks cap' out' ++ rest) /\
garr8 segs (arm W' mem') SA (bzs (entry_bytes e')) /\ awr W' mem' SA AENT /\ aentry_ok B ly' S' W' mem' e' /\
Z.of_nat (length (re_keys e')) <= re_nheld e' /\
re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
((re_hp e' = re_hp e /\ re_kh e' = re_kh e) \/ re_kh e' <= 2 ^ 30) /\
NoDup (drain_b_c.keys_texts (re_keys e')) /\
same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
asrc_at B ly' S' W' mem' HA h' /\
(forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> ~ (HA <= a < HA + ASRC) -> abyte_kept W mem W' mem' a) /\
hl_cap (hs_expected h') = drain_b_c.ds_ecap fin /\
hl_cap (hs_expected h') <= Z.max 8 (Z.max (hl_cap (hs_expected h)) (2 * hl_n (hs_expected h'))) /\
hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
hs_partial h' = hs_partial h /\
hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
hs_held h' = hs_held h /\
re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
bzs LB = with_nul (dr_lines h) /\
aout_at B fr_RG ly' S' W' mem' (dr_ctl c h ev') (if live then O ++ LB else O) mx (if live then no + dr_tot h else no) cap' out'.
Lemma dcB_post_of : forall regs ly S (W : world segs) mem md SA HA e h c O mx no cap out (W' : world segs) c',
  dr_post B MT fr_RG regs ly S W mem md SA HA e h c O mx no cap out W' c' ->
  exists ly' S' regs' mem' md' k, c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    ajournal_gx segs B G_fr 0 [] DRAIN_STK (spZ regs) (dr_fp SA e h cap out) ly S W mem md [] ly' S' W' mem' md' k /\
    aregs_preserved regs regs' /\
    dcB_post regs ly S W mem md SA HA e h c O mx no cap out ly' S' W' regs' mem' md'.
Proof.
  intros regs ly S W mem md SA HA e h c O mx no cap out W' c'
    (ly' & S' & regs' & mem' & md' & k & e' & h' & out' & ev' & LB & rest & HP).
  cbv zeta in HP. destruct HP as (Hc & HJ & HPR & HAPK & HMO & HP1 & HP2 & HG8 & HAW & HEOK & REST).
  exists ly', S', regs', mem', md', k. split; [exact Hc|].
  split; [exact (ajournal_gx_G_mono segs B (G_DR B fr_RG) G_fr 0 [] DRAIN_STK (spZ regs) _ ly S W mem md [] ly' S' W' mem' md'
                   k HG_DR HJ)|].
  split; [exact HPR|].
  exists k, e', h', out', ev', LB, rest. cbv zeta. split; [exact HJ|].
  exact (conj HAPK (conj HMO (conj HP1 (conj HP2 (conj HG8 (conj HAW (conj HEOK (conj (dr_keys_le e') REST)))))))).
Qed.
(* drain's functional values do not read the stream's errno value (dc_ctl's last field) *)
Lemma dcB_live_ctl : forall c ev h, dr_live (dc_ctl c ev) h = dr_live c h.
Proof. reflexivity. Qed.
Lemma dcB_fin_ctl : forall c ev mx no cap e h, dr_fin (dc_ctl c ev) mx no cap e h = dr_fin c mx no cap e h.
Proof. intros. unfold dr_fin. rewrite dcB_live_ctl. reflexivity. Qed.
Lemma dcB_tr_ctl : forall c ev mx no cap e h, dr_tr (dc_ctl c ev) mx no cap e h = dr_tr c mx no cap e h.
Proof. intros. unfold dr_tr. rewrite dcB_live_ctl. reflexivity. Qed.
Lemma dcB_cost_ctl : forall c ev mx no cap e h, dr_cost MT (dc_ctl c ev) mx no cap e h = dr_cost MT c mx no cap e h.
Proof. intros. unfold dr_cost. rewrite dcB_tr_ctl. reflexivity. Qed.
Lemma dcB_dctl_ctl : forall c ev h ev', dr_ctl (dc_ctl c ev) h ev' = dc_ctl (dr_ctl c h ev') ev'.
Proof. reflexivity. Qed.
(* a member of a literal list *)
Ltac dcB_in := repeat (first [left; reflexivity | right]).
(* a byte of one of DR_GK's cells (the cell's range is the hypothesis H) *)
Ltac dcB_gk H := left; unfold inG, DR_GK;
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; clear - H; lia | apply Exists_cons_tl]).

Lemma dc_stB : forall cx t m j si h fpos FF ly S W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  dc_static cx t m j si h -> LS cx t m ly S ->
  dc_at cx t m j si fpos FF A_dc_r1 ly S m true 0 W c ->
  SRr segs W c (fun W' c' => exists ly' S' e' h' out' ev' LB,
    dc_at cx t m j si fpos FF A_dc_r2 ly' S' (dr_m1 m j si h h' e' ev' LB out') true 0 W' c' /\
    mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) /\
    dr_dfun m si h j e' h' LB).
Proof.
  intros cx t m j si h fpos FF ly S W c HB (Hatop & Hpick & Hj & Hfdj & Hef0 & HRI) HLS
    (regs & mem & md & k & -> & HR & HJ & HFFe & HFR & HFL & HIN & HRV & HJT & SVN & S192 & S40 & HNE & HSEP & HKY).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : AR segs B ly S W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof HNE as (Hlen4 & HSL & HREL & (ev0 & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (Hsp : spZ regs = lf_F cx)
    by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  (* ---- 0x84a54: mv a0,s6 ; jal drain ---- *)
  destruct (dc_plain_entry A_dc_r1 W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK DRspan AF_fr_drain.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
                HS HAE ltac:(vm_compute; reflexivity)) as KR3.
  cbn [ms_regs restrict] in KR3.
  prreg HS (1%bv : bv 5) Q1d. prreg HS (10%bv : bv 5) Q10d.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (mdD := with_vm_backing (m_vm_lazy md) mat md) in *.
  rewrite (proj1 HAE 22%nat ltac:(lia)), (ew_Ereg_nat regs [] 22 22%bv eq_refl), R22 in Q10d.
  assert (HspD : spZ (ms_regs ms) = lf_F cx) by (unfold spZ; rewrite (KR3 2%bv ltac:(dcB_in)); exact Hsp).
  (* ---- the journal at the call: the fake frame, the blocks freed since the entry ---- *)
  assert (Hfin : In (1, fpos) (frames S)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  assert (HGONE0 : forall p n i, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> ~ In (p, n) (ablocks B ly S) ->
      0 <= i < req_size n -> inFP (lf_FP fr_FP cx) (p + i)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _).
    pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hg & _). exact Hg. }
  (* ---- drain's premises ---- *)
  pose proof Hpick as (_ & Hsi4 & Hhsi).
  destruct (dr_pads_of_relay ly S W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS).
  pose proof HREL as (RL1 & RL2 & RL3 & RL4 & RL5 & RL6 & RL7 & HGin & (tl & HTAB) & HENT & HNDF & HTBN).
  (* drain's entry pointer is 8-aligned: the table is a live block (16-aligned) and an entry is 56 bytes *)
  assert (HSA8 : (lm_G m + AENT * Z.of_nat j) mod 8 = 0).
  { destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR HGin) as (HG16 & _).
    pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as HGd. rewrite HG16, Z.add_0_r in HGd.
    rewrite HGd. unfold AENT.
    replace (16 * (lm_G m / 16) + 56 * Z.of_nat j) with ((2 * (lm_G m / 16) + 7 * Z.of_nat j) * 8) by ring.
    apply Z_mod_mult. }
  assert (HEOK : aentry_ok B ly S W mem (nth j (lm_es m) dr_e0))
    by (rewrite Forall_forall in HENT; apply HENT, nth_In; exact Hj).
  destruct (RI_pair cx t m si h j HRI Hpick Hj Hfdj Hef0) as (HSK & HSKU & _ & _).
  destruct (dr_blk B LAWS ly S W mem md (lm_G m) ATABLE HAR HGin) as (HG4096 & HGceil & _).
  assert (HSA : lm_G m <= lm_G m + AENT * Z.of_nat j /\ lm_G m + AENT * Z.of_nat j + AENT <= lm_G m + ATABLE)
    by (unfold AENT, ATABLE; lia).
  assert (HSRC0 : asrc_at B ly S W mem (rg_s fr_RG + ASRC * Z.of_nat si) h).
  { pose proof (HSL si Hsi4) as Hs. rewrite Hhsi in Hs. exact Hs. }
  pose proof (dr_tbl_entry W mem (lm_G m) (lm_es m) tl j HTAB HPAD Hj) as HEB.
  assert (HEL : length (bzs (entry_bytes (nth j (lm_es m) dr_e0))) = 56%nat).
  { pose proof HEOK as (_ & _ & Hq1 & Hq2 & _). rewrite dra_bzs_length. apply entry_bytes_length; assumption. }
  assert (HEW : awr W mem (lm_G m + AENT * Z.of_nat j) AENT).
  { pose proof (dr_awr_of_garr8 ly S W mem md (lm_G m) ATABLE (lm_G m + AENT * Z.of_nat j)
                  (bzs (entry_bytes (nth j (lm_es m) dr_e0))) HAR HGin ltac:(lia)
                  ltac:(rewrite HEL; replace (req_size ATABLE) with ATABLE by reflexivity; unfold AENT, ATABLE in *; lia)
                  HEB) as Hw.
    rewrite HEL in Hw. exact Hw. }
  assert (HOTH : aothers_at fr_RG W mem si (re_fd (nth j (lm_es m) dr_e0))).
  { intros i Hi Hne. pose proof (HSL i Hi) as Hs. revert Hs.
    destruct (nth i (lm_hs m) None) as [hi|] eqn:Ehi; intros Hs; cbn [aslot] in Hs.
    - exists (hs_fd hi), (hs_open hi). pose proof Hs as (V1 & V2 & _).
      split; [exact V1|]. split; [exact V2|]. right. rewrite Hfdj.
      assert (Fi : 0 <= hs_fd hi < 2 ^ 31) by (unfold asrc_at in Hs; tauto).
      assert (Fh : 0 <= hs_fd h < 2 ^ 31) by (unfold asrc_at in HSRC0; tauto).
      rewrite !Z.mod_small by lia.
      exact (RI_fds cx t m i si hi h HRI Hi Hsi4 Hne Ehi Hhsi).
    - exists 0, 0. destruct Hs as (Hz & _).
      pose proof (dcB_zero_vm _ _ (Z.to_nat ASRC) 0 Hz ltac:(lia)
                    ltac:(rewrite Z2Nat.id by (unfold ASRC; lia); unfold ASRC; lia)) as Hz0.
      rewrite Z.add_0_r in Hz0.
      split; [exact Hz0|]. split; [|left; reflexivity].
      exact (dcB_zero_vm _ _ (Z.to_nat ASRC) 4 Hz ltac:(lia)
               ltac:(rewrite Z2Nat.id by (unfold ASRC; lia); unfold ASRC; lia)). }
  assert (HXM : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      In b (model_blks m)).
  { intros b Hb. unfold model_blks. right. apply in_app_or in Hb as [Hb | Hb].
    - apply in_or_app. left. apply in_concat. exists (aentry_blks (nth j (lm_es m) dr_e0)).
      split; [apply in_map, nth_In; exact Hj | exact Hb].
    - apply in_or_app. right. apply in_app_or in Hb as [Hb | Hb].
      + apply in_or_app. left. apply in_concat. exists (slot_blks (Some h)). split; [|exact Hb].
        rewrite <- Hhsi. apply in_map, nth_In. lia.
      + apply in_or_app. right. exact Hb. }
  pose proof HSEP as HSEPc.
  destruct HSEP as ((rest0 & HP0) & HSEP2).
  assert (HXL : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP0)).
    apply in_or_app. right. apply in_or_app. left. exact (HXM b Hb). }
  assert (HXP : forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
      0 < snd b).
  { intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [exact (dcB_pos_aentry _ _ _ _ _ _ HEOK Hb)|].
    apply in_app_or in Hb as [Hb | Hb];
      [exact (dcB_pos_asrc _ _ _ _ _ _ _ HSRC0 Hb) | exact (dcB_pos_aout _ _ _ _ _ _ _ _ _ _ _ HOUT Hb)]. }
  unfold model_blks in HP0.
  pose proof (dr_concat_nth_perm _ _ aentry_blks (lm_es m) j dr_e0 Hj) as HCA.
  pose proof (dr_concat_nth_perm _ _ slot_blks (lm_hs m) si None ltac:(lia)) as HCS.
  rewrite Hhsi in HCS. cbn [slot_blks] in HCS.
  pose proof (dcB_perm_pre _ _ _ _ _ _ _ _ _ _ _ HP0 HCA HCS) as HPERM0.
  assert (HU : Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL)
    by (pose proof HEOK as (_ & _ & _ & _ & _ & _ & Hu1 & Hu2 & _); lia).
  destruct (LS_drain_pre cx t m ly S si h j HLS HRI Hatop Hpick Hj Hfdj Hef0 Ht HU HXP) as (L1 & L2 & L3 & L4 & L5 & L6).
  rewrite <- (dcB_tr_ctl (lm_c m) ev0) in L4, L5. rewrite <- (dcB_cost_ctl (lm_c m) ev0) in L6.
  destruct (dr_afn_pre_at cx ly S fpos k W mem mdD (ms_regs ms) DRAIN_STK HB HJ) as (ch & HPRED).
  { rewrite HFFe. exact (dr_aframe_false cx FF W mem HFR). }
  { exact HspD. }
  { rewrite Q1d. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1d, unsigned_lit_small by lia. lia. }
  { rewrite (KR3 3%bv ltac:(dcB_in)). exact R3. }
  { rewrite (KR3 4%bv ltac:(dcB_in)). exact R4. }
  { rewrite (KR3 8%bv ltac:(dcB_in)). exact R8. }
  { unfold DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK. lia. }
  { unfold DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK. lia. }
  (* ---- drain(r), composed into the function's journal ---- *)
  eapply SRr_mono.
  { apply (dr_callZ G_fr W (ms_regs ms) mem (Z_to_bv 64 (BASE + 3568)) LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S mdD k DRAIN_STK
      (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m)) 0 []
      (lf_F cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + 10096)) ch
      (fun ly2 S2 W2 regs2 mem2 md2 => dcB_post (ms_regs ms) ly S W mem mdD (lm_G m + AENT * Z.of_nat j)
         (rg_s fr_RG + ASRC * Z.of_nat si) (nth j (lm_es m) dr_e0) h (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
         (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) ly2 S2 W2 regs2 mem2 md2)
      HG HJ).
    - rewrite HspD. lia.
    - lia.
    - unfold DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK. lia.
    - lia.
    - lia.
    - intros a Ha. exfalso. exact (inFP_nil a Ha).
    - exact Q1d.
    - exact HPRED.
    - eapply SRr_mono.
      { exact (DRAIN W ly S (ms_regs ms) mem mdD ch (lm_G m) (lm_G m + AENT * Z.of_nat j)
                 (nth j (lm_es m) dr_e0) si h (dc_ctl (lm_c m) ev0) (lm_O m) (lm_mx m)
                 (Z.of_nat (length (lm_O m))) (lm_cap m) (lm_out m) HPRED Q10d HGin (proj1 HSA) (proj2 HSA) HSA8
                 HEB HEW HEOK Hsi4 HSRC0 HOTH (eq_sym Hfdj) HSK HSKU HOUT HRV (ex_intro _ _ HPERM0)
                 L1 L2 L3 L4 L5 L6). }
      cbv beta. intros W2 c2 _ HPOST.
      destruct (dcB_post_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST)
        as (ly2 & S2 & regs2 & mem2 & md2 & k2 & Hc2 & HJ2 & HPR2 & HK2).
      exists ly2, S2, regs2, mem2, md2, k2. rewrite Q1d in Hc2.
      split; [exact Hc2|]. split; [exact HJ2|]. split; [exact HPR2 | exact HK2].
    - intros a (r & Hr & Ha). destruct Hr as [<- | Hr].
      + cbn [fst snd] in Ha.
        apply (dcB_fp_blk cx m ly S (lm_G m, ATABLE) a HSEPc);
          [unfold model_blks; left; reflexivity | cbn [snd]; unfold ATABLE; lia
          | cbn [fst snd]; replace (req_size ATABLE) with ATABLE by reflexivity; unfold AENT, ATABLE in *; lia].
      + unfold ablocks_fp in Hr. apply in_map_iff in Hr as (b & <- & Hb). cbn [fst snd] in Ha.
        exact (dcB_fp_blk cx m ly S b a HSEPc (HXM b Hb) (HXP b Hb) Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HPR & HK).
  destruct HK as (k2 & e' & h' & out' & ev' & LB & rest & HK). cbv zeta in HK.
  destruct HK as (HJD & HPK & HMO & HP1 & HP2 & HN1 & HN2 & HN3 & HKE & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16
                  & D17 & D18 & D19 & HSRC & HGS & D22 & D23 & D24 & D25 & D26 & D27 & D28 & D29 & D30 & D31 & D32 & D33
                  & D34 & D35 & D36 & D37 & D38 & HOUT2).
  rewrite HspD in HJD.
  rewrite dcB_cost_ctl in HMO. rewrite dcB_fin_ctl in D12, D13, D14, D15, D16, D22.
  rewrite ?dcB_live_ctl, ?dcB_fin_ctl, ?dcB_dctl_ctl in HOUT2. rewrite ?dcB_live_ctl, ?dcB_fin_ctl in HP2.
  (* ---- the blocks across the call ---- *)
  pose proof dcB_GDR_ok as HGDR.
  pose proof (dj_nodup ly S W mem md HAR) as HNDS.
  assert (HAR2 : AR segs B ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR; exact HJD).
  pose proof (dj_nodup ly2 S2 W2 mem2 md2 HAR2) as HNDS2.
  assert (HP1' : Permutation (ablocks B ly S)
      ((aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ++ rest))
    by (rewrite <- !app_assoc; exact HP1).
  assert (HRT : Permutation rest ((lm_G m, ATABLE) :: dcB_T cx m j si rest0))
    by exact (dcB_perm_rest _ _ _ _ _ _ _ HPERM0 HP1).
  assert (KTR : forall b, In b (dcB_T cx m j si rest0) -> In b rest)
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HRT)); right; exact Hb).
  assert (KTL2 : forall b, In b rest -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)).
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb. }
  assert (HGr : In (lm_G m, ATABLE) rest) by (apply (Permutation_in _ (Permutation_sym HRT)); left; reflexivity).
  assert (HCSin : forall i hi b, (i < 4)%nat -> i <> si -> nth i (lm_hs m) None = Some hi -> In b (asrc_blks hi) ->
      In b (dcB_T cx m j si rest0)).
  { intros i hi b Hi Hne Ehi Hb. unfold dcB_T. apply in_or_app. right. apply in_or_app. left. unfold dcB_CS.
    apply in_concat. exists (slot_blks (Some hi)). split; [|exact Hb]. apply in_map. rewrite <- Ehi.
    apply dcB_in_rm_nth; lia. }
  assert (HCAin : forall y b, In y (firstn j (lm_es m) ++ skipn (Datatypes.S j) (lm_es m)) -> In b (aentry_blks y) ->
      In b (dcB_T cx m j si rest0)).
  { intros y b Hy Hb. unfold dcB_T. apply in_or_app. left. unfold dcB_CA.
    apply in_concat. exists (aentry_blks y). split; [apply in_map; exact Hy | exact Hb]. }
  (* ---- the bytes drain keeps ---- *)
  assert (KBLK : forall p n a, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n ->
      ~ inFP (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m)) a ->
      abyte_kept W mem W2 mem2 a).
  { intros p n a H1 H2 Ha Hnf.
    pose proof (blk_img segs B LAWS ly S W mem md p n a HAR H1 Ha) as Hni.
    destruct (dr_blk B LAWS ly S W mem md p n HAR H1) as (Hp1 & Hp2 & _).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; left. exists p, n. split; [exact H1|]. split; [exact H2|]. split; [exact Ha | exact Hnf]. }
  assert (KT : forall b a, In b (dcB_T cx m j si rest0) -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a).
  { intros [p n] a HbT Ha. cbn [fst snd] in Ha.
    destruct (dcB_in_rest _ _ _ _ HNDS HP1' (KTR _ HbT)) as (HnX & HbL).
    pose proof (dcB_T_ne _ _ _ _ _ _ HNDS HP1' HRT HbT) as Hng.
    destruct (dr_blk B LAWS ly S W mem md p n HAR HbL) as (_ & _ & Hn0).
    apply (KBLK p n a HbL (KTL2 _ (KTR _ HbT)) ltac:(lia)).
    exact (dcB_nfp_blk ly S W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ p n a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL HbL HnX ltac:(lia) (or_introl Hng)). }
  assert (KTAB : forall a, lm_G m <= a < lm_G m + ATABLE ->
      ~ (lm_G m + AENT * Z.of_nat j <= a < lm_G m + AENT * Z.of_nat j + AENT) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn.
    destruct (dcB_in_rest _ _ _ _ HNDS HP1' HGr) as (HnX & HbL).
    apply (KBLK (lm_G m) ATABLE a HbL (KTL2 _ HGr) ltac:(replace (req_size ATABLE) with ATABLE by reflexivity; lia)).
    exact (dcB_nfp_blk ly S W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ (lm_G m) ATABLE a HAR HGin (proj1 HSA)
             (proj2 HSA) HXL HbL HnX ltac:(replace (req_size ATABLE) with ATABLE by reflexivity; lia) (or_intror Hn)). }
  assert (KSTK : forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (Hsegs a Hi); lia).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    left. split; [lia | lia]. }
  assert (FFb : 4096 <= FF /\ FF + 128 <= alloc_ceiling).
  { destruct (frames_bounds segs B LAWS ly S W mem md 1 fpos HAR Hfin) as (Hf0 & Hfc & _).
    rewrite HFFe in Hf0, Hfc. replace (fs_frame_bytes 1) with 128 in Hfc by reflexivity. lia. }
  assert (KFF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (Hfr : frame_addr ly 1 fpos <= a < frame_addr ly 1 fpos + fs_frame_bytes 1)
      by (rewrite HFFe; replace (fs_frame_bytes 1) with 128 by reflexivity; exact Ha).
    pose proof (frm_img segs B LAWS ly S W mem md 1 fpos a HAR Hfin Hfr) as Hni.
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; right; right. exists 1, fpos. split; [exact Hfin|].
    split; [left; unfold in_zr, frame_rng; cbn [fst snd]; exact Hfr|].
    exact (dcB_nfp_frm ly S W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ 1 fpos a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL Hfin (or_introl Hfr)). }
  assert (KSH : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha.
    assert (FF8 : 0 <= FF / 8 /\ 8 * (FF / 8) <= FF) by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
    unfold SB in Ha.
    assert (Hni : ~ in_img segs a) by (intros Hi; pose proof (Hsegs a Hi); lia).
    apply dj_bk; [lia | intros Hi; exfalso; exact (Hni Hi) |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | intros HGa; exact (Hni (proj1 (HGDR a HGa))) |].
    right; right; right; right. exists 1, fpos. split; [exact Hfin|].
    assert (Hsh : shadow_addr (frame_addr ly 1 fpos) <= a < shadow_addr (frame_addr ly 1 fpos) + fs_frame_bytes 1 / 8).
    { rewrite HFFe. replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr, SHADOW_OFF. lia. }
    split; [right; unfold in_zr; cbn [fst snd]; exact Hsh|].
    exact (dcB_nfp_frm ly S W mem md (lm_G m) (lm_G m + AENT * Z.of_nat j) _ 1 fpos a HAR HGin (proj1 HSA) (proj2 HSA)
             HXL Hfin (or_intror Hsh)). }
  assert (HFPpos : Forall (fun r => 0 < fst r)
      (dr_fp (lm_G m + AENT * Z.of_nat j) (nth j (lm_es m) dr_e0) h (lm_cap m) (lm_out m))).
  { unfold dr_fp. constructor; [cbn [fst]; lia|]. apply Forall_forall. intros r Hr. unfold ablocks_fp in Hr.
    apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst].
    destruct (dr_blk B LAWS ly S W mem md p n HAR (HXL _ Hb)) as (Hp & _).
    lia. }
  assert (KIMG : forall a, inG DR_GK a \/ rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. destruct (dcB_GK_out a Ha) as (HnD & Hne).
    assert (HGa : inG G_fr a) by (destruct Ha as [Ha | Ha]; [exact (HG_GK a Ha) | exact (HGlock a Ha)]).
    destruct (HG a HGa) as (Hi & Hno & _). pose proof (Hsegs a Hi) as Hlo.
    apply dj_bk; [lia | intros _; exact HGa |].
    eapply dj_keep; [exact HGDR | exact HJD | lia | exact HnD |].
    right; right; right; left. split; [exact Hi|]. split; [exact Hno|]. split; [exact Hne|].
    apply fp_spares_closed. apply sink_closed_pos. exact HFPpos. }
  (* ---- the context after the call ---- *)
  assert (HFF2 : frame_addr ly2 1 fpos = FF).
  { pose proof HJD as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
    pose proof Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. exact HFFe. }
  assert (HFR2 : aframe_at cx true FF W2 mem2) by (apply (dcB_aframe_kept cx true FF W W2 mem mem2 HFR KSTK KFF KSH); lia).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly2 1 fpos)).
  { pose proof HJD as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & Hly & _).
    pose proof Hly as (_ & _ & _ & _ & _ & EF & _). unfold flag_addr. rewrite EF.
    apply (dr_sv8_kept W W2 mem mem2); [intros x Hx; apply KFF; lia | exact HFL]. }
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { destruct HIN as (Hn & Hpl).
    assert (HbT : 0 < c_n cx -> In (c_p cx, c_n cx) (dcB_T cx m j si rest0)).
    { intros Hn1. unfold dcB_T. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      unfold input_blks. rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    split.
    - destruct Hn as [Hn | (Hn1 & Hin)]; [left; exact Hn | right; split; [exact Hn1|]].
      exact (KTL2 _ (KTR _ (HbT (proj1 Hn1)))).
    - apply (akept_garr8 W mem); [|exact Hpl]. intros x Hx. rewrite length_map, <- Hnlen in Hx.
      destruct Hn as [(Hn0 & _) | (Hn1 & _)]; [lia|].
      exact (KT (c_p cx, c_n cx) x (HbT (proj1 Hn1)) ltac:(cbn [fst snd]; lia)). }
  assert (HRV2 : rom_view segs W2 mem2)
    by exact (ajournal_gx_rom_view segs B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJD dcB_rom_out HRV).
  pose proof (dcB_jt W W2 mem mem2 HRV HRV2 HJT) as HJT2.
  assert (SVN2 : sv8 W2 mem2 (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply KSTK. unfold DR_N in Hx. lia. }
  assert (S1922 : sv8 W2 mem2 (lf_F cx + DR_AT) 0).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact S192]. intros x Hx. apply KSTK. unfold DR_AT in Hx. lia. }
  assert (S402 : sv8 W2 mem2 (lf_F cx + 40) (rg_lock fr_RG)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact S40]. intros x Hx. apply KSTK. lia. }
  (* ---- the model after the call ---- *)
  assert (HLEN1 : Z.of_nat (length (dr_O1 m h LB)) =
      (if dr_live (lm_c m) h then Z.of_nat (length (lm_O m)) + dr_tot h else Z.of_nat (length (lm_O m)))).
  { unfold dr_O1. destruct (dr_live (lm_c m) h); [|reflexivity].
    rewrite length_app, Nat2Z.inj_add, (dc_LB_len LB _ D38). reflexivity. }
  assert (HO1 : aout_at B fr_RG ly2 S2 W2 mem2 (dc_ctl (dr_ctl (lm_c m) h ev') ev') (dr_O1 m h LB) (lm_mx m)
                  (Z.of_nat (length (dr_O1 m h LB))) (dr_cap1 m j h) out').
  { rewrite HLEN1. unfold dr_O1, dr_cap1. exact HOUT2. }
  assert (HREL2 : arelay_at B fr_RG ly2 S2 W2 mem2 (lm_G m) (set_nth j e' (lm_es m))).
  { pose proof HN3 as (_ & _ & Hq1 & Hq2 & _).
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL1]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL2]|].
    split; [rewrite set_nth_length; apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL3]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL4]|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL5]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact RL6]|].
    split; [rewrite set_nth_length; exact RL7|].
    split; [exact (KTL2 _ HGr)|].
    split.
    { exists tl. apply (dr_tbl_upd W W2 mem mem2 (lm_G m) (lm_es m) tl j e' HTAB HPAD Hq1 Hq2 Hj HN1).
      intros a Ha Hn. exact (proj1 (KTAB a Ha Hn)). }
    split.
    { apply Forall_forall. intros y Hy.
      destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy']; [exact HN3|].
      assert (HyE : In y (lm_es m)) by exact (dr_in_rm rentry j y (lm_es m) Hy').
      rewrite Forall_forall in HENT, HKY.
      apply (aentry_ok_kept B ly S W mem ly2 S2 W2 mem2 y (HENT y HyE)).
      - intros r Hr x Hx.
        destruct (dj_aentry_fp ly S W mem y (HENT y HyE) (HKY y HyE) r Hr x Hx) as [[] | (b & Hb & Hbx)].
        exact (KT b x (HCAin y b Hy' Hb) Hbx).
      - intros b Hb. exact (KTL2 b (KTR b (HCAin y b Hy' Hb))). }
    rewrite dr_map_set_nth, D9.
    assert (Hfe : re_fd (nth j (lm_es m) dr_e0) = nth j (map re_fd (lm_es m)) (re_fd dr_e0))
      by (rewrite map_nth; reflexivity).
    split; [rewrite Hfe, dcB_set_nth_nth; exact HNDF|].
    (* arelay_at's twelfth conjunct: no entry block is the table.  The new entry's blocks are drain's post's first
       part of the live blocks, the table is in its `rest` (HGr), and the live blocks are distinct *)
    apply Forall_forall. intros y Hy b Hb Heq. subst b.
    destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy'].
    - apply (dcB_nd_app (aentry_blks e') _ (lm_G m, ATABLE) (Permutation_NoDup HP2 HNDS2) Hb).
      apply in_or_app. right. apply in_or_app. right. exact HGr.
    - rewrite Forall_forall in HTBN. exact (HTBN y (dr_in_rm rentry j y (lm_es m) Hy') _ Hb eq_refl). }
  assert (HNE2 : amodel_ne ly2 S2 W2 mem2 (dr_m1 m j si h h' e' ev' LB out') true).
  { unfold dr_m1, dr_step, amodel_ne. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [rewrite set_nth_length; exact Hlen4|].
    split.
    { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
      - rewrite set_nth_same by lia. exact HSRC.
      - rewrite set_nth_other by lia.
        pose proof (HSL i Hi) as Hs. revert Hs.
        destruct (nth i (lm_hs m) None) as [hi|] eqn:Ehi; intros Hs; cbn [aslot] in Hs |- *.
        + apply (asrc_at_kept B ly S W mem ly2 S2 W2 mem2 _ hi Hs).
          * intros r Hr x Hx. destruct (dj_asrc_fp ly S W mem _ hi Hs r Hr x Hx) as [Hin | (b & Hb & Hbx)].
            -- cbv beta in Hin. apply HGS; unfold ASRC in *; lia.
            -- exact (KT b x (HCSin i hi b Hi Hne Ehi Hb) Hbx).
          * intros b Hb. exact (KTL2 b (KTR b (HCSin i hi b Hi Hne Ehi Hb))).
        + destruct Hs as (Hz & Hw). split.
          * apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx.
            rewrite Z2Nat.id in Hx by (unfold ASRC; lia). apply HGS; unfold ASRC in *; lia.
          * apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply HGS; unfold ASRC in *; lia. }
    split; [exact HREL2|].
    split; [exists ev'; exact HO1|].
    split; [apply (agone_at_kept fr_RG W mem W2 mem2 (lm_gn m) HGONE); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; dcB_gk Hx|].
    split; [apply (alock_at_kept fr_RG W mem W2 mem2 true HLOCK); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; right; exact Hx|].
    split; [apply (awake_at_kept fr_RG W mem W2 mem2 HWAKE); intros r [<- | []] x Hx;
            cbn [fst snd] in Hx; apply KIMG; dcB_gk Hx|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HNFD]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HNFDW]|].
    split; [exact HNFDr|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HTUP]|].
    split; [destruct HLST as (lst & Hl); exists lst; apply (akept_vm W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact Hl]|].
    apply (akept_awr W mem); [intros x Hx; apply KIMG; dcB_gk Hx | exact HLSTW]. }
  assert (HPm1 : Permutation (ablocks B ly2 S2)
      (input_blks cx ++ model_blks (dr_m1 m j si h h' e' ev' LB out') ++ rest0)).
  { unfold dr_m1, dr_step, model_blks. cbn [lm_G lm_es lm_hs lm_cap lm_out]. unfold dr_cap1.
    apply (dcB_perm_post _ _ _ _ _ _ _ _ (dcB_CA (lm_es m) j) (dcB_CS (lm_hs m) si) rest _ HP2 HRT).
    - exact (dr_concat_set_nth_perm _ _ aentry_blks (lm_es m) j e' Hj).
    - pose proof (dr_concat_set_nth_perm _ _ slot_blks (lm_hs m) si (Some h') ltac:(lia)) as Hq.
      cbn [slot_blks] in Hq. exact Hq. }
  assert (HSEP1 : ablocks_sep B fr_FP cx (dr_m1 m j si h h' e' ev' LB out') ly2 S2).
  { split; [exists rest0; exact HPm1|].
    intros b Hb.
    assert (HbL2 : In b (ablocks B ly2 S2)).
    { apply (Permutation_in _ (Permutation_sym HPm1)). apply in_or_app. right. apply in_or_app. left. exact Hb. }
    destruct (in_dec dcB_dec b (ablocks B ly S)) as [HbS | HbS].
    - apply HSEP2.
      apply (Permutation_in _ HP1') in HbS. apply in_app_or in HbS as [HbX | HbR]; [exact (HXM b HbX)|].
      apply (Permutation_in _ HRT) in HbR. destruct HbR as [<- | HbT]; [unfold model_blks; left; reflexivity|].
      unfold dcB_T in HbT. apply in_app_or in HbT as [HbA | HbT].
      + unfold model_blks. right. apply in_or_app. left.
        apply (Permutation_in _ (Permutation_sym HCA)). apply in_or_app. right. exact HbA.
      + apply in_app_or in HbT as [HbC | HbT].
        * unfold model_blks. right. apply in_or_app. right. apply in_or_app. left.
          apply (Permutation_in _ (Permutation_sym HCS)). apply in_or_app. right. exact HbC.
        * exfalso. pose proof (Permutation_NoDup HPm1 HNDS2) as Hnd.
          apply in_app_or in HbT as [HbI | HbR0].
          -- exact (dcB_nd_app _ _ b Hnd HbI (in_or_app _ _ _ (or_introl Hb))).
          -- apply (dcB_nd_app (input_blks cx ++ model_blks (dr_m1 m j si h h' e' ev' LB out')) rest0 b);
               [rewrite <- app_assoc; exact Hnd | apply in_or_app; right; exact Hb | exact HbR0].
    - destruct (in_dec dcB_dec b (ablocks B (c_ly cx) (c_S cx))) as [HbE | HbE]; [right | left; exact HbE].
      intros a Ha. destruct b as [p n]. cbn [fst snd] in Ha.
      destruct (dr_blk B LAWS ly2 S2 W2 mem2 md2 p n HAR2 HbL2) as (_ & _ & Hn0).
      replace a with (p + (a - p)) by lia. apply (HGONE0 p n (a - p) HbE HbS). lia. }
  assert (HKY1 : Forall (fun e0 => Z.of_nat (length (re_keys e0)) <= re_nheld e0)
      (lm_es (dr_m1 m j si h h' e' ev' LB out'))).
  { unfold dr_m1, dr_step. cbn [lm_es]. apply Forall_forall. intros y Hy.
    destruct (dr_in_set_nth rentry j e' y (lm_es m) Hy) as [-> | Hy']; [exact HKE|].
    rewrite Forall_forall in HKY. exact (HKY y (dr_in_rm rentry j y (lm_es m) Hy')). }
  (* ---- the state at 0x84a5c ---- *)
  exists ly2, S2, e', h', out', ev', LB.
  split; [|split].
  - exists regs2, mem2, md2, (k + k1). split; [reflexivity|].
    split.
    { assert (PR2 : forall r : bv 5, acallee_saved (bv_unsigned r) ->
          In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs r)
        by (intros r H1 H2; rewrite (dj_pres _ _ r HPR H1); exact (KR3 r H2)).
      unfold dc_regs. rewrite !PR2 by first [dj_cs | dcB_in].
      repeat (split; [assumption|]). exact R25. }
    split; [exact HJ2|]. split; [exact HFF2|].
    split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HJT2|].
    split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
    split; [exact HNE2|]. split; [exact HSEP1 | exact HKY1].
  - exact HMO.
  - unfold dr_dfun. cbv zeta.
    split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|]. split; [exact D13|].
    split; [exact D14|]. split; [exact D15|]. split; [exact D16|]. split; [exact D18|]. split; [exact D19|].
    split; [exact D24|]. split; [exact D25|]. split; [exact D26|]. split; [exact D27|]. split; [exact D28|].
    split; [exact D32|]. split; [exact D33|]. split; [exact D35|]. split; [exact D36|]. split; [exact D37|].
    split; [exact D38|]. split; [exact D22|].
    pose proof HN3 as (_ & _ & Hpd1 & Hpd2 & _). split; [exact Hpd1 | exact Hpd2].
Qed.

(* the frame base F = lf_F cx against the entry sp *)
Lemma dcF_F : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320 /\ lf_F cx mod 32 = 0 /\
  (lf_F cx - spZ (c_regs cx)) mod 16 = 0 /\ alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47.
Proof.
  intros cx HB.
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (Ho16 : (F - sp0) mod 16 = 0).
  { assert (HF32' : F = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
    pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
    rewrite HF32'.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  repeat split; try lia; exact Ho16.
Qed.
(* the walk's own frame is the one live frame of its journal *)
Lemma dcF_fin : forall cx fpos ly S (W : world segs) mem md k,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md k ->
  In (1, fpos) (frames S).
Proof.
  intros cx fpos ly S W mem md k HJ.
  pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
  rewrite Hfrs. left. reflexivity.
Qed.
(* the registers the three calls keep: every one dc_regs names, all callee-saved *)
Definition dcF_K : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma dcF_pres_K : forall regs regs', aregs_preserved regs regs' ->
  forall r, In r dcF_K -> getr regs' r = getr regs r.
Proof.
  intros regs regs' HP r Hr. apply (dj_pres regs regs' r HP). unfold dcF_K in Hr.
  repeat (destruct Hr as [<- | Hr]; [dj_cs|]). destruct Hr.
Qed.
Lemma dcF_regs_kept : forall cx t m j si FF regs regs',
  (forall r, In r dcF_K -> getr regs' r = getr regs r) ->
  dc_regs cx t m j si FF regs -> dc_regs cx t m j si FF regs'.
Proof.
  intros cx t m j si FF regs regs' HK
    (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  unfold dc_regs. rewrite !HK by (cbv; tauto).
  exact (conj R2 (conj R8 (conj R9 (conj R18 (conj R19 (conj R20 (conj R23 (conj R24 (conj R26 (conj R3 (conj R4
    (conj R27 (conj Ht (conj R21 (conj R22 R25))))))))))))))).
Qed.
(* a part of a zero-shadow range is one *)
Lemma dcF_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof. intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2. exists r. split; [exact Hin|]. repeat split; lia. Qed.

Lemma dc_stC : forall cx t m j si fpos FF ly S mc W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  dc_at cx t m j si fpos FF A_dc_r2 ly S mc true 0 W c ->
  SRr segs W c (dc_at cx t m j si fpos FF A_dc_r3 ly S mc false 0).
Proof.
  intros cx t m j si fpos FF ly S mc W c HB
    (regs & mem & md & k & -> & HR & HJ & HFF & HFR & HFL & HIN & HROM & HJT & SVN & S192 & S40 & HNE & HSEP & HKB).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (dcF_F cx HB) as (HFb & HF32 & Ho16 & Hsp0).
  assert (HAR : AR segs B ly S W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof (dcF_fin cx fpos ly S W mem md k HJ) as Hfin.
  assert (HCTX : dc_ctxp cx m FF 0 (flag_addr ly 1 fpos) ly S W mem)
    by exact (conj HFR (conj HFL (conj HIN (conj HROM (conj HJT (conj SVN (conj S192 S40))))))).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (VLK : rg_lock fr_RG = 0x5d8ac0) by reflexivity.
  pose proof HNE as (_ & _ & _ & _ & _ & HLOCK & _).
  pose proof HLOCK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8.
  assert (HNOWN : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> ~ aowned B ly S a).
  { intros a Ha Ho. destruct (HG a (HGlock a Ha)) as (Hi & Hno & _).
    apply Hno. exact (proj1 (al_owned_image _ _ LAWS ly S W mem _ a HAR Hi) Ho). }
  (* 0x84a5c-0x84a60: ld a0,40(s1) ; jal pthread_mutex_unlock *)
  destruct (dc_cell_entry A_dc_r2 40 W regs mem F (rg_lock fr_RG) R9 R26 ltac:(lia) ltac:(lia) HF32
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) S40 ltac:(rewrite VLK; lia)) as [HS SHOK].
  remember (Eimg (Ereg regs (dc_cell_extra (rg_lock fr_RG)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (dc_cell_extra (rg_lock fr_RG))) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E32 : ew E 32 = Z_to_bv 64 (rg_lock fr_RG))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  paj_run_tok RUN HS HJ SHOK DRspan.
  { unfold ss_dc_cell. cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [dc_cell YP09.r_wlo YP09.r_whi] in Ha. lia. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok segs _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite E32 in Q10.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dc_r3)) by exact Q1.
  eapply SRr_bind.
  { eapply (aj_gx_entry_at B LAWS G_fr 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
      (fun a => rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8)
      (fun regs' mem' => getr regs' 10 = w64 0 /\ val_mem segs (mrestrict (w_H W) mem') (rg_lock fr_RG + 4) 4 0)
      W regs1 mem LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(1, fpos)] ly S md1 k (F - sp0) _ HG eq_refl HJ
      ltac:(rewrite Hsp1; lia) Ho16
      ltac:(lia) ltac:(lia) ltac:(unfold ESTACK, LLVMF_STK; lia)
      ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3) ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4) Q1'
      (ret_ok_codeptr_v A_dc_r3 ltac:(unfold A_dc_r3, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl)).
    - intros a. lia.
    - intros a Hwa _. exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 16 a LK4 ltac:(cbn; lia)).
    - intros a Hwa HnG. exfalso. apply HnG. apply HGlock. lia.
    - intros HPRE2 HSC2.
      exact (AUNLOCK ly S W regs1 mem md1 (rg_lock fr_RG) HPRE2 Q10 ltac:(lia) ltac:(rewrite VLK; reflexivity) ltac:(lia)
        LK0 LK4 LK8
        ltac:(intros a Ha; split;
              [ destruct (Z_lt_le_dec a (rg_lock fr_RG + 4)) as [Hlt | Hge];
                [ exact (dj_av_ne W mem (rg_lock fr_RG) 4%nat 0 a LK0 ltac:(cbn; lia))
                | destruct (Z_lt_le_dec a (rg_lock fr_RG + 8)) as [Hlt2 | Hge2];
                  [ exact (dj_av_ne W mem (rg_lock fr_RG + 4) 4%nat 16 a LK4 ltac:(cbn; lia))
                  | exact (dj_av_ne W mem (rg_lock fr_RG + 8) 4%nat 0 a LK8 ltac:(cbn; lia)) ] ]
              | rewrite Hsp1; unfold ESTACK; lia ])
        ltac:(intros a Ha; split;
              [ replace a with (rg_lock fr_RG + (a - rg_lock fr_RG)) by lia; exact (LKW (a - rg_lock fr_RG) ltac:(lia))
              | split; [ apply HNOWN; lia | rewrite Hsp1; unfold ESTACK; lia ] ])). }
  (* back at 0x84a64, g_lock free *)
  cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJa & HPa & (Ha0 & Hlk2) & Hfra & Hpresa).
  assert (KL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock fr_RG + 4 <= a < rg_lock fr_RG + 8) -> ~ (F - ESTACK <= a < F) ->
      aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha H1 H2; apply Hfra; [exact Ha | exact H1 | replace (sp0 + (F - sp0)) with F by lia; exact H2]).
  pose proof (dj_ne_lockstep ly S W mem md mem2 mc true false F HAR HKB HNE KL ltac:(unfold ESTACK; lia) Hlk2) as HNE2.
  destruct (dj_ctx_lockstep cx m FF 0 (flag_addr ly 1 fpos) ly S W mem md mem2 HB HAR
              (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX KL Hpresa)
    as (HFR2 & HFL2 & HIN2 & HROM2 & HJT2 & SVN2 & S1922 & S402).
  apply SRr_ret.
  exists regs2, mem2, md2, k.
  split; [reflexivity|].
  split; [exact (dcF_regs_kept cx t m j si FF regs regs2
                   (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HPa r Hr) (KR r Hr)) HR)|].
  split; [exact HJa|]. split; [exact HFF|].
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HROM2|]. split; [exact HJT2|].
  split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
  split; [exact HNE2|]. split; [exact HSEP|]. exact HKB.
Qed.

Lemma dc_stD : forall cx t m j si fpos FF ly S mc h1 W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (si < 4)%nat -> nth si (lm_hs mc) None = Some h1 -> hl_recs (hs_pending h1) = [] ->
  dc_at cx t m j si fpos FF A_dc_r3 ly S mc false 0 W c ->
  SRr segs W c (dc_at cx t m j si fpos FF A_dc_r4 ly S mc false 0).
Proof.
  intros cx t m j si fpos FF ly S mc h1 W c HB Hsi Hh1 Hpend
    (regs & mem & md & k & -> & HR & HJ & HFF & HFR & HFL & HIN & HROM & HJT & SVN & S192 & S40 & HNE & HSEP & HKB).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (dcF_F cx HB) as (HFb & HF32 & Ho16 & Hsp0).
  pose proof (dcF_fin cx fpos ly S W mem md k HJ) as Hfin.
  assert (HCTX : dc_ctxp cx m FF 0 (flag_addr ly 1 fpos) ly S W mem)
    by exact (conj HFR (conj HFL (conj HIN (conj HROM (conj HJT (conj SVN (conj S192 S40))))))).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  (* s = &g_s[si]; check_no_loss_read reads its pending.n at s + 24, 0 here *)
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (VS : rg_s fr_RG = 0x5d88e0) by reflexivity.
  pose proof HNE as (_ & HSL & _).
  pose proof (HSL si Hsi) as HSLi. rewrite Hh1 in HSLi.
  destruct HSLi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPL & _).
  destruct HPL as (_ & HPn & _).
  assert (HV0 : val_mem segs (mrestrict (w_H W) mem) (HA + 24) 4 0).
  { replace (HA + 24) with (HA + 16 + 8) by lia. unfold hl_n in HPn. rewrite Hpend in HPn. exact HPn. }
  assert (HPm : HA mod 16 = 0).
  { unfold HA. rewrite VS. unfold ASRC.
    replace (0x5d88e0 + 96 * Z.of_nat si) with ((0x5d88e + 6 * Z.of_nat si) * 16) by lia. apply Z_mod_mult. }
  assert (HAZ : azs B HA 28) by (apply (dcF_azs_sub _ _ _ _ HZS); unfold HA, ASRC; lia).
  destruct HAP as (HAP0 & HAP32).
  (* 0x84a64-0x84a68: mv a0,s5 ; jal check_no_loss_read *)
  destruct (dc_plain_entry A_dc_r3 W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK DRspan AF_fr_check_no_loss_read.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite (EEo 21%nat 21%bv eq_refl), R21 in Q10.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dc_r4)) by exact Q1.
  destruct (dr_afn_pre_at cx ly S fpos k W mem md1 regs1 CNLR_STK HB HJ
              ltac:(rewrite HFF; exact (dr_aframe_false cx FF W mem HFR)) Hsp1
              ltac:(rewrite Q1'; exact (ret_ok_codeptr_v A_dc_r4
                      ltac:(unfold A_dc_r4, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl))
              ltac:(unfold raZ; rewrite Q1', unsigned_lit_small; unfold A_dc_r4, A_dr_found, AF_fr_LLVMFuzzerTestOneInput; lia)
              ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3) ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
              ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
              ltac:(unfold CNLR_STK; lia) ltac:(unfold CNLR_STK, LLVMF_STK; lia)) as (ch & HPRE1).
  eapply SRr_mono.
  { eapply (dr_callZ G_fr W regs1 mem (Z_to_bv 64 (BASE + AF_fr_check_no_loss_read)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S md1 k CNLR_STK [] 0 [] (F - sp0)
      (Z_to_bv 64 (BASE + A_dc_r4)) ch
      (fun ly2 S2 W2 _ mem2 md2 => ly2 = ly /\ S2 = S /\ ajournal segs B CNLR_STK F [] ly S W mem md1 [] ly S W2 mem2 md2 0)
      HG HJ ltac:(rewrite Hsp1; lia) ltac:(lia) ltac:(unfold CNLR_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
      ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) Q1' HPRE1).
    - eapply SRr_mono;
        [exact (CNLR W ly S regs1 mem md1 ch HA 0 HPRE1 Q10 HPm ltac:(unfold HA, ASRC; lia) ltac:(unfold HA, ASRC; lia) HAZ
                  ltac:(unfold HA, ASRC in *; lia) ltac:(unfold HA, ASRC in *; lia) HV0 ltac:(lia) ltac:(left; reflexivity))|].
      cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & _).
      rewrite Hsp1 in HJc.
      exists ly, S, regs2, mem2, md2, 0.
      split; [rewrite Q1'; reflexivity|].
      split; [rewrite Hsp1; apply (ajournal_gx_G_mono segs B [] G_fr);
              [intros a Ha; exfalso; exact (inG_nil a Ha) | apply ajournal_gx_nil; exact HJc]|].
      split; [exact HP2|]. split; [reflexivity|]. split; [reflexivity|]. exact HJc.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  (* back at 0x84a6c *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HP2 & (-> & -> & HJp)).
  pose proof (dj_ne_plain ly S W W2 mem mem2 md1 md2 mc false CNLR_STK F HJp ltac:(unfold CNLR_STK; lia) HKB HNE) as HNE2.
  destruct (dj_ctx_plain cx m FF 0 (flag_addr ly 1 fpos) ly S W W2 mem mem2 md1 md2 CNLR_STK HB HJp
              ltac:(unfold CNLR_STK; lia) (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX)
    as (HFR2 & HFL2 & HIN2 & HROM2 & HJT2 & SVN2 & S1922 & S402).
  exists regs2, mem2, md2, (k + k1).
  split; [reflexivity|].
  split; [exact (dcF_regs_kept cx t m j si FF regs regs2
                   (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HP2 r Hr) (KR r Hr)) HR)|].
  split; [exact HJ2|]. split; [exact HFF|].
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HROM2|]. split; [exact HJT2|].
  split; [exact SVN2|]. split; [exact S1922|]. split; [exact S402|].
  split; [exact HNE2|]. split; [exact HSEP|]. exact HKB.
Qed.

Lemma dc_stF : forall cx t m j si fpos FF ly S mc W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  dr_at_op cx m ->
  (forall ev, RINV cx (t + 1) (dc_fin cx m mc ev)) -> (forall ev, LS cx (t + 1) (dc_fin cx m mc ev) ly S) ->
  dc_at cx t m j si fpos FF A_dc_r5 ly S mc false (Z.of_nat (length (lm_O mc))) W c ->
  SRr segs W c (DST A_dr_join cx (t + 1) (lregs_join cx t)).
Proof.
  intros cx t m j si fpos FF ly S mc W c HB Hatop HRI HLS
    (regs & mem & md & k & -> & HR & HJ & HFF & HFR & HFL & HIN & HROM & HJT & SVN & S192 & S40 & HNE & HSEP & HKB).
  pose proof HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (dcF_F cx HB) as (HFb & HF32 & Ho16 & Hsp0).
  assert (HAR : AR segs B ly S W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof (dcF_fin cx fpos ly S W mem md k HJ) as Hfin.
  assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
    by (pose proof Hatop as (Hk0 & _ & _); unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
  (* at = |O| = g_nout *)
  pose proof HNE as (_ & _ & _ & (ev0 & HOUT0) & _).
  destruct HOUT0 as (_ & _ & HNO & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     _ & Hcap).
  unfold arm in HNO.
  assert (HA : 0 <= Z.of_nat (length (lm_O mc)) < 2 ^ 64).
  { destruct Hcap as [(_ & _ & Hz) | (Hc0 & Hle & Hin & _)]; [lia|].
    destruct (dr_blk B LAWS ly S W mem md _ _ HAR Hin) as (Hb1 & Hb2 & Hb3). lia. }
  assert (VN : VAL A_g_nout = rg_nout fr_RG) by (vm_compute; reflexivity).
  assert (HCTX : dc_ctxp cx m FF (Z.of_nat (length (lm_O mc))) (flag_addr ly 1 fpos) ly S W mem)
    by exact (conj HFR (conj HFL (conj HIN (conj HROM (conj HJT (conj SVN (conj S192 S40))))))).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  set (NO := Z.of_nat (length (lm_O mc))) in *.
  (* 0x84a78-0x84a7c: ld a0,192(s1) ; jal check_shape_done *)
  destruct (dc_cell_entry A_dc_r5 192 W regs mem F NO R9 R26 ltac:(lia) ltac:(lia) HF32
              ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) S192 HA) as [HS SHOK].
  remember (Eimg (Ereg regs (dc_cell_extra NO))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (dc_cell_extra NO)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E32 : ew E 32 = Z_to_bv 64 NO)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK DRspan AF_fr_check_shape_done.
  { unfold ss_dc_cell. cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [dc_cell YP09.r_wlo YP09.r_whi] in Ha. lia. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ dcF_K HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
  rewrite E32 in Q10.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *.
  set (regs1 := ms_regs ms) in *.
  assert (Hsp1 : spZ regs1 = F)
    by (unfold spZ; rewrite (KR 2%bv ltac:(cbv; tauto)), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regs1 1 = Z_to_bv 64 (BASE + A_dr_join)) by exact Q1.
  destruct (dr_afn_pre_at cx ly S fpos k W mem md1 regs1 CSD_STK HB HJ
              ltac:(rewrite HFF; exact (dr_aframe_false cx FF W mem HFR)) Hsp1
              ltac:(rewrite Q1'; exact (ret_ok_codeptr_v A_dr_join
                      ltac:(unfold A_dr_join, AF_fr_LLVMFuzzerTestOneInput; lia) eq_refl))
              ltac:(unfold raZ; rewrite Q1', unsigned_lit_small; unfold A_dr_join, AF_fr_LLVMFuzzerTestOneInput; lia)
              ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3) ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
              ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
              ltac:(unfold CSD_STK; lia) ltac:(unfold CSD_STK, LLVMF_STK; lia)) as (ch & HPRE1).
  eapply SRr_mono.
  { eapply (dr_callZ G_fr W regs1 mem (Z_to_bv 64 (BASE + AF_fr_check_shape_done)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S md1 k CSD_STK [] 0 [] (F - sp0)
      (Z_to_bv 64 (BASE + A_dr_join)) ch
      (fun ly2 S2 W2 _ mem2 md2 => ly2 = ly /\ S2 = S /\ ajournal segs B CSD_STK F [] ly S W mem md1 [] ly S W2 mem2 md2 0)
      HG HJ ltac:(rewrite Hsp1; lia) ltac:(lia) ltac:(unfold CSD_STK, LLVMF_STK; lia) ltac:(lia) ltac:(lia)
      ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) Q1' HPRE1).
    - eapply SRr_mono;
        [exact (CSD W ly S regs1 mem md1 ch NO HPRE1 Q10 HA ltac:(rewrite VN; exact HNO))|].
      cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJc & HP2 & _ & _).
      rewrite Hsp1 in HJc.
      exists ly, S, regs2, mem2, md2, 0.
      split; [rewrite Q1'; reflexivity|].
      split; [rewrite Hsp1; apply (ajournal_gx_G_mono segs B [] G_fr);
              [intros a Ha; exfalso; exact (inG_nil a Ha) | apply ajournal_gx_nil; exact HJc]|].
      split; [exact HP2|]. split; [reflexivity|]. split; [reflexivity|]. exact HJc.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  (* back at 0x84a80, the arm's join *)
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HP2 & (-> & -> & HJp)).
  pose proof (dj_ne_plain ly S W W2 mem mem2 md1 md2 mc false CSD_STK F HJp ltac:(unfold CSD_STK; lia) HKB HNE) as HNE2.
  destruct (dj_ctx_plain cx m FF NO (flag_addr ly 1 fpos) ly S W W2 mem mem2 md1 md2 CSD_STK HB HJp
              ltac:(unfold CSD_STK; lia) (ex_intro _ fpos (conj Hfin (eq_sym HFF))) HCTX)
    as (HFR2 & HFL2 & HIN2 & HROM2 & HJT2 & SVN2 & S1922 & S402).
  destruct HNE2 as (N1 & N2 & N3 & (ev & N4) & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
  pose proof (dcF_regs_kept cx t m j si FF regs regs2
                (fun r Hr => eq_trans (dcF_pres_K regs1 regs2 HP2 r Hr) (KR r Hr)) HR)
    as (R2' & R8' & R9' & R18' & R19' & R20' & R23' & R24' & R26' & R3' & R4' & R27' & Ht' & R21' & R22' & R25').
  exists regs2, mem2, md2.
  split; [reflexivity|].
  split; [exact HJT2|].
  exists [(1, fpos)], ly, S, (k + k1), (dc_fin cx m mc ev), fpos.
  split; [exact HJ2|]. split; [reflexivity|]. split; [rewrite HFF; exact HFR2|]. split; [rewrite HFF; exact HFL2|].
  split; [exact (conj N1 (conj N2 (conj N3 (conj N4 (conj N5 (conj N6 (conj N7 (conj N8 (conj N9 (conj N10
                   (conj N11 (conj N12 N13))))))))))))|].
  split; [exact HIN2|]. split; [exact HROM2|].
  split; [exact HSEP|]. split; [exact (HLS ev)|]. split; [exact (HRI ev)|].
  rewrite HFF.
  exact (conj R2' (conj R8' (conj R9' (conj R18' (conj R19' (conj R20' (conj R23' (conj R24' (conj R26' (conj R3'
    (conj R4' (conj R27' (conj Ht' (conj R25' (conj SVN2 Hk'))))))))))))))).
Qed.

(* ---- dc_stE's helpers (dcE_) ---- *)
Definition dcE_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.
(* the live blocks around the call: slot si's two lists (LE ++ LH) moved to the front *)
Lemma dcE_perm_shape : forall (IB GE ENT OTH AO RS PP LE LH CS : list (Z * Z)),
  Permutation CS ((PP ++ LE ++ LH) ++ OTH) ->
  Permutation (IB ++ (GE ++ ENT ++ CS ++ AO) ++ RS) ((LE ++ LH) ++ PP ++ IB ++ GE ++ ENT ++ OTH ++ AO ++ RS).
Proof.
  intros IB GE ENT OTH AO RS PP LE LH CS HP.
  rewrite (Permutation_count_occ dcE_dec) in HP |- *. intros x. specialize (HP x).
  rewrite !count_occ_app in HP. rewrite !count_occ_app. lia.
Qed.
Lemma dcE_nodup_app : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x Hnd H1 H2; [destruct H1|].
  inversion Hnd as [|y0 l0 Hn Hnd']; subst.
  destruct H1 as [<- | H1]; [apply Hn; apply in_or_app; right; exact H2 | exact (IH l2 x Hnd' H1 H2)].
Qed.
Lemma dcE_nodup_r : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 Hnd; [exact Hnd|].
  inversion Hnd as [|y0 l0 Hn Hnd']; subst. exact (IH l2 Hnd').
Qed.
Lemma dcE_nth_rm : forall (T : Type) (l : list T) i j d, (i < length l)%nat -> i <> j ->
  In (nth i l d) (firstn j l ++ skipn (S j) l).
Proof.
  intros T l. induction l as [|a l IH]; intros i j d Hi Hij; cbn [length] in Hi; [lia|].
  destruct i as [|i], j as [|j].
  - lia.
  - cbn [nth firstn app]. left. reflexivity.
  - cbn [nth firstn skipn app]. change (skipn 0 l) with l. apply nth_In. lia.
  - cbn [nth firstn skipn app]. right. apply IH; lia.
Qed.
Lemma dcE_inG1 : forall x n a, inG [(x, n)] a <-> x <= a < x + n.
Proof.
  intros x n a. unfold inG. split; intros H.
  - inversion H as [r l Hr Hl | r l Hr Hl]; subst; [unfold in_zr in Hr; cbn [fst snd] in Hr; lia | inversion Hr].
  - constructor. unfold in_zr. cbn [fst snd]. lia.
Qed.
Lemma dcE_inG_mem : forall G x n a, In (x, n) G -> x <= a < x + n -> inG G a.
Proof. intros G x n a Hin Ha. unfold inG. apply Exists_exists. exists (x, n). split; [exact Hin | unfold in_zr; cbn; lia]. Qed.
(* a list's blocks have a positive size *)
Lemma dcE_blks_pos : forall ly S (W : world segs) mem LA l lines,
  alist_at B ly S W mem LA l lines -> forall b, In b (alist_blks l) -> 0 < snd b.
Proof.
  intros ly S W mem LA l lines (_ & _ & _ & _ & H5 & H6 & _) b Hb. unfold alist_blks in Hb.
  apply in_app_or in Hb as [Hb | Hb].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [Ec | Ec]; [destruct Hb|].
    destruct Hb as [<- | []]. cbn [snd]. unfold AREC. unfold hl_n in H5. lia.
  - apply in_map_iff in Hb as (r & <- & _). cbn [snd]. lia.
Qed.
(* a block address of a source is the address of one of its blocks *)
Lemma dcE_hs_blocks : forall h x, In x (hs_blocks h) -> exists n, In (x, n) (asrc_blks h).
Proof.
  intros h x Hx. unfold hs_blocks, list_blocks in Hx. unfold asrc_blks, alist_blks.
  repeat rewrite in_app_iff in Hx.
  destruct Hx as [[Hx | Hx] | [[<- | []] | [[Hx | Hx] | [Hx | Hx]]]].
  - destruct (hl_cap (hs_pending h) =? 0); [destruct Hx|]. destruct Hx as [<- | []].
    eexists. right. apply in_or_app. left. apply in_or_app. left. left. reflexivity.
  - apply in_map_iff in Hx as (r & <- & Hr). eexists. right. apply in_or_app. left. apply in_or_app. right.
    apply in_map_iff. exists r. split; [reflexivity | exact Hr].
  - eexists. left. reflexivity.
  - destruct (hl_cap (hs_expected h) =? 0); [destruct Hx|]. destruct Hx as [<- | []].
    eexists. right. apply in_or_app. right. apply in_or_app. left. apply in_or_app. left. left. reflexivity.
  - apply in_map_iff in Hx as (r & <- & Hr). eexists. right. apply in_or_app. right. apply in_or_app. left.
    apply in_or_app. right. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
  - destruct (hl_cap (hs_held h) =? 0); [destruct Hx|]. destruct Hx as [<- | []].
    eexists. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity.
  - apply in_map_iff in Hx as (r & <- & Hr). eexists. right. apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
Qed.
Lemma dcE_lb1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.
(* the stream's bytes, read out of the out block's garr8 *)
Lemma dcE_ob_at : forall (W : world segs) mem out (O junk : list byte),
  garr8 segs (arm W mem) out (bzs (O ++ junk)) -> ob_at W mem out O.
Proof.
  intros W mem out O junk Hg i Hi.
  assert (Hj : (Z.to_nat i < length (bzs (O ++ junk)))%nat) by (unfold bzs; rewrite length_map, length_app; lia).
  destruct (Hg _ Hj) as [Hv Hr]. unfold arm in Hv.
  pose proof (dj_av1 W mem _ 1%nat _ Hv ltac:(lia)) as Ha. rewrite Z2Nat.id in Ha by lia.
  rewrite Ha. f_equal. rewrite nth_bzs, app_nth1 by lia.
  pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) O (Z_to_bv 8 0))) as Hb. change (bv_modulus 8) with 256 in Hb.
  apply dcE_lb1. exact Hb.
Qed.
(* the jump table's words across a state change that keeps the read-only view *)
Lemma dcE_jt_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> rom_view segs W' mem' -> jt_rom W mem -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HR HR' HJ i Hi k Hk. specialize (HJ i Hi k Hk).
  rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem'); [exact HJ|].
  assert (Hrom : in_rom segs (fr_jtab + 4 * i + Z.of_nat k)) by (apply dj_jt_rom; lia).
  rewrite (HR' _ Hrom), (HR _ Hrom). reflexivity.
Qed.
(* a read-only literal, as the ASan view reads it *)
Lemma dcE_in_rom_b : forall a,
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs = true -> in_rom segs a.
Proof.
  intros a H. apply existsb_exists in H as (sg & Hs & Hb). apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply Bool.negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists sg. split; [exact Hs|]. split; [exact H0 | lia].
Qed.
Definition dcE_litb (base : Z) (l : list Z) : bool :=
  forallb (fun j => existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? base + Z.of_nat j) &&
    (base + Z.of_nat j <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs &&
    match seg_rom segs (Z_to_bv 64 (base + Z.of_nat j)) with Some b => bv_unsigned b =? nth j l 0 | None => false end)
  (seq 0 (length l)).
Lemma dcE_lit : forall (W : world segs) mem base l,
  rom_view segs W mem -> dcE_litb base l = true -> garr8 segs (arm W mem) base l.
Proof.
  intros W mem base l HR Hb j Hj. unfold dcE_litb in Hb. rewrite forallb_forall in Hb.
  specialize (Hb j ltac:(apply in_seq; lia)). apply andb_prop in Hb as [Hrb Hv].
  pose proof (dcE_in_rom_b _ Hrb) as Hrom. pose proof (HR _ Hrom) as Ha.
  destruct (seg_rom segs (Z_to_bv 64 (base + Z.of_nat j))) as [b|] eqn:Eb; [|discriminate].
  apply Z.eqb_eq in Hv. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|lia].
  intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r. unfold arm.
  unfold aview in Ha. cbn [option_map] in Ha.
  destruct (mbyte segs (mrestrict (w_H W) mem) (base + Z.of_nat j)) as [b'|] eqn:Eb'; [|discriminate].
  injection Ha as Ha. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Ha, Hv.
  rewrite dcE_lb1 by lia. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
Lemma dcE_lits : dcE_litb (VAL A_lit_gesture) RelayModel.K_GESTURE = true /\
  dcE_litb (VAL A_lit_begin) RelayModel.W_BEGIN = true /\ dcE_litb (VAL A_lit_end) RelayModel.W_END = true.
Proof. vm_compute. repeat split. Qed.
Lemma dcE_vals : VAL A_g_nout = rg_nout fr_RG /\ VAL A_g_out = rg_out fr_RG /\ VAL A_g_gone = rg_gone fr_RG /\
  VAL A_g_s = rg_s fr_RG.
Proof. vm_compute. repeat split. Qed.
Lemma dcE_rg : rg_s fr_RG = 0x5d88e0 /\ rg_src fr_RG = 0x5d87c0 /\ rg_nsrc fr_RG = 0x5d87a0 /\
  rg_capsrc fr_RG = 0x5d8800 /\ rg_out fr_RG = 0x5d8b40 /\ rg_nout fr_RG = 0x5d88c0 /\ rg_capout fr_RG = 0x5d8b20 /\
  rg_send_max fr_RG = 0x5d8840 /\ rg_send_eintr fr_RG = 0x5d88a0 /\ rg_send_dead fr_RG = 0x5d8880 /\
  rg_gone fr_RG = 0x5d8860 /\ rg_client fr_RG = 0xa1fe0 /\ rg_client_broken fr_RG = 0x5d87e0 /\
  rg_lock fr_RG = 0x5d8ac0 /\ rg_wake fr_RG = 0xa1fa0.
Proof. repeat split. Qed.
Lemma dcE_cnl_stk : CNL_STK = 16656.
Proof. reflexivity. Qed.
(* what a callee's journal (empty own) keeps, as abyte_kept: dj_keep and dj_bk *)
Lemma dcE_kept : forall Gc XO OUT STK sp FP ly S (W : world segs) mem md ly' S' (W' : world segs) mem' md' kk a,
  gx_ok segs B Gc ->
  ajournal_gx segs B Gc XO OUT STK sp FP ly S W mem md [] ly' S' W' mem' md' kk ->
  0 <= a < 2 ^ 64 -> ~ inG Gc a -> (in_img segs a -> inG G_fr a) ->
  ((alloc_ceiling <= a /\ ~ (sp - STK <= a < sp + XO)) \/
   (sp <= a < sp + XO /\ ~ inFP OUT a) \/
   (exists p n, In (p, n) (ablocks B ly S) /\ In (p, n) (ablocks B ly' S') /\ p <= a < p + req_size n /\
      ~ inFP FP a) \/
   (in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
      fp_spares FP a) \/
   (exists cid pos, In (cid, pos) (frames S) /\
      (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) /\
      ~ inFP FP a)) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros Gc XO OUT STK sp FP ly S W mem md ly' S' W' mem' md' kk a HGx HJX Ha HnG Hig Hc.
  apply (dj_bk W W' mem mem' a Ha Hig).
  exact (dj_keep Gc XO OUT STK sp FP ly S W mem md [] ly' S' W' mem' md' kk a HGx HJX Ha HnG Hc).
Qed.
(* a footprint of live blocks does not reach the sink's token at 0 *)
Lemma dcE_fp_closed : forall ly S (W : world segs) mem md L,
  AR segs B ly S W mem md -> (forall b, In b L -> In b (ablocks B ly S)) -> ~ YI16.sink_open_fp (blk_FP L).
Proof.
  intros ly S W mem md L HAR HL (r & Hr & H0). unfold blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb).
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HL _ Hb)) as (_ & H4 & _). cbn [fst snd] in H0. lia.
Qed.
(* a byte of another live block is outside the footprint of the blocks L *)
Lemma dcE_notFP : forall ly S (W : world segs) mem md L p n a,
  AR segs B ly S W mem md -> (forall b, In b L -> In b (ablocks B ly S)) -> In (p, n) (ablocks B ly S) ->
  ~ In (p, n) L -> p <= a < p + req_size n -> ~ inFP (blk_FP L) a.
Proof.
  intros ly S W mem md L p n a HAR HL Hpn Hnot Ha (r & Hr & Hra). unfold blk_FP in Hr.
  apply in_map_iff in Hr as ([q m] & <- & Hb). cbn [fst snd] in Hra.
  apply (dj_apart ly S W mem md p n q m a HAR Hpn (HL _ Hb)); [| exact Ha | exact Hra].
  intros E. apply Hnot. rewrite E. exact Hb.
Qed.
Section dcE_keep.
Variables (Gc : list (Z * Z)) (XO : Z) (OUT : list (Z * Z)) (STK sp : Z) (L : list (Z * Z)).
Variables (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model).
Variables (ly' : alayout) (S' : astate) (W' : world segs) (mem' : word -> option byte) (md' : Model) (kk : Z).
Hypothesis KGx : gx_ok segs B Gc.
Hypothesis KJ : ajournal_gx segs B Gc XO OUT STK sp (blk_FP L) ly S W mem md [] ly' S' W' mem' md' kk.
Hypothesis KAR : AR segs B ly S W mem md.
Hypothesis KL : forall b, In b L -> In b (ablocks B ly S).
Lemma dcE_nG_img : forall a, inG Gc a -> in_img segs a.
Proof. intros a Ha. exact (proj1 (KGx a Ha)). Qed.
(* a live block's byte, the block live after and none of L *)
Lemma dcE_kept_blk : forall p n a,
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> ~ In (p, n) L -> p <= a < p + req_size n ->
  abyte_kept W mem W' mem' a.
Proof.
  intros p n a H1 H2 Hnot Ha.
  destruct (al_blocks _ _ LAWS ly S W mem md p n KAR H1) as (_ & H4 & Hc & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hni : ~ in_img segs a) by exact (blk_img segs B LAWS ly S W mem md p n a KAR H1 Ha).
  apply (dcE_kept Gc XO OUT STK sp (blk_FP L) ly S W mem md ly' S' W' mem' md' kk a KGx KJ);
    [lia | intros HGa; exact (Hni (dcE_nG_img a HGa)) | intros Hi; exact (False_ind _ (Hni Hi)) |].
  right; right; left. exists p, n. repeat split; try assumption; try lia.
  exact (dcE_notFP ly S W mem md L p n a KAR KL H1 Hnot Ha).
Qed.
(* an image byte of G_fr, outside Gc and errno *)
Lemma dcE_kept_img : forall a, inG G_fr a -> ~ inG Gc a -> ~ (as_errno B <= a < as_errno B + 4) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros a HGa HnG He. destruct (HG a HGa) as (Hi & Hno & _).
  pose proof (pa_segs_low a Hi) as Hlo. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (dcE_kept Gc XO OUT STK sp (blk_FP L) ly S W mem md ly' S' W' mem' md' kk a KGx KJ);
    [lia | exact HnG | intros _; exact HGa |].
  right; right; right; left. split; [exact Hi|]. split; [exact Hno|]. split; [exact He|].
  apply fp_spares_closed. exact (dcE_fp_closed ly S W mem md L KAR KL).
Qed.
(* a byte of a fake frame or of its shadow *)
Lemma dcE_kept_frame : forall cid pos a, In (cid, pos) (frames S) ->
  (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  abyte_kept W mem W' mem' a.
Proof.
  intros cid pos a Hfr Hr.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (frames_bounds segs B LAWS ly S W mem md cid pos KAR Hfr) as (Hf0 & Hfc & Hfh).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  pose proof (shadow_addr_bounds (frame_addr ly cid pos) ltac:(zlia)) as SB1.
  pose proof (shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(zlia)) as SB2.
  pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as SB3.
  assert (Hni : ~ in_img segs a).
  { intros Hi. destruct Hr as [Hr | Hr].
    - exact (frm_img segs B LAWS ly S W mem md cid pos a KAR Hfr Hr Hi).
    - pose proof (pa_segs_low a Hi). unfold in_zr in Hr. cbn [fst snd] in Hr. zlia. }
  apply (dcE_kept Gc XO OUT STK sp (blk_FP L) ly S W mem md ly' S' W' mem' md' kk a KGx KJ);
    [ unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; destruct Hr as [Hr | Hr]; zlia
    | intros HGa; exact (Hni (dcE_nG_img a HGa)) | intros Hi; exact (False_ind _ (Hni Hi)) |].
  right; right; right; right. exists cid, pos. split; [exact Hfr|]. split; [exact Hr|].
  intros (r & Hrin & Hra). unfold blk_FP in Hrin. apply in_map_iff in Hrin as ([b m] & <- & Hb). cbn [fst snd] in Hra.
  pose proof (KL _ Hb) as Hbin.
  destruct (al_blocks _ _ LAWS ly S W mem md b m KAR Hbin) as (_ & _ & _ & [Hh1 Hh2] & _).
  pose proof (sep_block_frame segs B LAWS ly S W mem md b m cid pos KAR Hbin Hfr) as Hd.
  unfold zdisjoint, frame_rng, in_zr in Hd, Hr. cbn [fst snd] in Hd, Hr.
  destruct Hr as [Hr|Hr]; zlia.
Qed.
End dcE_keep.
(* the controller's stream across a callee that keeps every byte of it but errno, which it re-reads *)
Ltac dcE_infp := repeat (first [left; reflexivity | right]).
Definition dcE_ofp (cap out : Z) : list (Z * Z) :=
  [(rg_send_max fr_RG, rg_send_max fr_RG + 8); (rg_nout fr_RG, rg_nout fr_RG + 8);
   (rg_capout fr_RG, rg_capout fr_RG + 8); (rg_out fr_RG, rg_out fr_RG + 8); (rg_client fr_RG, rg_client fr_RG + 4);
   (rg_client_broken fr_RG, rg_client_broken fr_RG + 1); (rg_send_dead fr_RG, rg_send_dead fr_RG + 1);
   (rg_send_eintr fr_RG, rg_send_eintr fr_RG + 1)] ++ (if cap =? 0 then [] else [(out, out + cap)]).
Lemma dcE_aout : forall ly S (W : world segs) mem ly' S' (W' : world segs) mem' c O mx no cap out v,
  aout_at B fr_RG ly S W mem c O mx no cap out ->
  akept W mem W' mem' (dcE_ofp cap out) ->
  (forall b, In b (aout_blks cap out) -> In b (ablocks B ly' S')) ->
  val_mem segs (arm W' mem') (as_errno B) 4 v -> awr W' mem' (as_errno B) 4 -> 0 <= v < 2 ^ 32 ->
  aout_at B fr_RG ly' S' W' mem' (dc_ctl c v) O mx no cap out.
Proof.
  intros ly S W mem ly' S' W' mem' c O mx no cap out v
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 &
     H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26) HK HB Hv Hw Hvr.
  assert (KC : forall a n, In (a, a + n) (dcE_ofp cap out) -> forall x, a <= x < a + n -> abyte_kept W mem W' mem' x)
    by (intros a n Hin x Hx; exact (HK (a, a + n) Hin x Hx)).
  cbn [dc_ctl ct_cl ct_br ct_dd ct_ei ct_ev].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_max fr_RG) 8); [unfold dcE_ofp; dcE_infp | lia] | exact H1]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_max fr_RG) 8); unfold dcE_ofp; dcE_infp | exact H2]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_nout fr_RG) 8); [unfold dcE_ofp; dcE_infp | lia] | exact H3]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_nout fr_RG) 8); unfold dcE_ofp; dcE_infp | exact H4]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_capout fr_RG) 8); [unfold dcE_ofp; dcE_infp | lia] | exact H5]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_capout fr_RG) 8); unfold dcE_ofp; dcE_infp | exact H6]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_out fr_RG) 8); [unfold dcE_ofp; dcE_infp | lia] | exact H7]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_out fr_RG) 8); unfold dcE_ofp; dcE_infp | exact H8]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_client fr_RG) 4); [unfold dcE_ofp; dcE_infp | lia] | exact H9]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_client fr_RG) 4); unfold dcE_ofp; dcE_infp | exact H10]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_client_broken fr_RG) 1); [unfold dcE_ofp; dcE_infp | lia] | exact H11]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_client_broken fr_RG) 1); unfold dcE_ofp; dcE_infp | exact H12]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_dead fr_RG) 1); [unfold dcE_ofp; dcE_infp | lia] | exact H13]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_dead fr_RG) 1); unfold dcE_ofp; dcE_infp | exact H14]|].
  split; [apply (akept_vm W mem); [intros x Hx; apply (KC (rg_send_eintr fr_RG) 1); [unfold dcE_ofp; dcE_infp | lia] | exact H15]|].
  split; [apply (akept_awr W mem); [apply (KC (rg_send_eintr fr_RG) 1); unfold dcE_ofp; dcE_infp | exact H16]|].
  split; [exact Hv|]. split; [exact Hw|]. split; [exact Hvr|].
  do 6 (split; [assumption|]).
  destruct H26 as [H26 | (Hc & Hno & Hin & junk & Hj & Hg)]; [left; exact H26|right].
  assert (Ec : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
  split; [exact Hc|]. split; [exact Hno|].
  split; [apply HB; unfold aout_blks; rewrite Ec; left; reflexivity|].
  exists junk. split; [exact Hj|].
  apply (akept_garr8 W mem); [|exact Hg].
  intros x Hx. unfold bzs in Hx. rewrite length_map, length_app, Nat2Z.inj_add in Hx.
  apply (KC out cap); [unfold dcE_ofp; rewrite Ec; dcE_infp | lia].
Qed.
(* the frame across a callee that keeps [F, sp0) but the `at` cell, leaves [F, sp0) writable, and keeps the fake
   frame and its shadow *)
Lemma dcE_aframe_kept : forall cx full FF (W W' : world segs) mem mem',
  aframe_at cx full FF W mem -> lf_F cx + 320 <= spZ (c_regs cx) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> ~ (lf_F cx + DR_AT <= a < lf_F cx + DR_AT + 8) ->
     abyte_kept W mem W' mem' a) ->
  (forall a, lf_F cx <= a < spZ (c_regs cx) -> writable_at segs (arm W' mem') a) ->
  (forall a, FF <= a < FF + 128 -> abyte_kept W mem W' mem' a) ->
  (forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W' mem' a) ->
  aframe_at cx full FF W' mem'.
Proof.
  intros cx full FF W W' mem mem' (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17)
    HF KF WF KFF KSH.
  unfold DR_AT in *.
  assert (KV : forall a v, lf_F cx <= a -> a + 8 <= spZ (c_regs cx) -> (a + 8 <= lf_F cx + 192 \/ lf_F cx + 200 <= a) ->
             sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 H2 Hv. apply (dr_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply KF; lia. }
  assert (KVF : forall a v, FF <= a -> a + 8 <= FF + 128 -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 Hv. apply (dr_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply KFF; lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | exact (A1 o r Hin)]. }
  split; [intros i Hi; apply WF; lia|].
  do 9 (split; [apply KV; [lia | lia | lia | assumption]|]).
  split.
  { intros Hfull. destruct (A12 Hfull) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
    do 6 (split; [apply KV; [lia | lia | lia | assumption]|]).
    apply KV; [lia | lia | lia | assumption]. }
  do 3 (split; [apply KVF; [lia | lia | assumption]|]).
  split; [apply (akept_awr W mem); [intros x Hx; apply KFF; lia | exact A16]|].
  split.
  - apply (akept_garr8 W mem); [|exact (proj1 A17)].
    intros x Hx. unfold fake_shadow in Hx. cbn [length] in Hx. apply KSH; lia.
  - apply (akept_awr W mem); [intros x Hx; apply KSH; lia | exact (proj2 A17)].
Qed.

(* the registers the arm keeps across the run and the call (all callee-saved) *)
Lemma dcE_regs_kept : forall cx t m j si FF (regs regs1 regs2 : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs1 r = getr regs r) ->
  aregs_preserved regs1 regs2 -> dc_regs cx t m j si FF regs -> dc_regs cx t m j si FF regs2.
Proof.
  intros cx t m j si FF regs regs1 regs2 KR HP
    (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) ->
      In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs r)
    by (intros r Hr Hin; rewrite (dj_pres regs1 regs2 r HP Hr); exact (KR r Hin)).
  unfold dc_regs.
  rewrite (PR 2%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 8%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 9%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 18%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 19%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 20%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 23%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 24%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 26%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 3%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 4%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 27%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 21%bv ltac:(dj_cs) ltac:(dcE_infp)), (PR 22%bv ltac:(dj_cs) ltac:(dcE_infp)),
    (PR 25%bv ltac:(dj_cs) ltac:(dcE_infp)).
  repeat (split; [assumption|]). exact R25.
Qed.
(* the model after check_no_loss: slot si is the callee's, every other byte the model reads is kept (the other
   slots, the relay, the stream with errno re-read, g_gone, g_lock, g_wake, g_nfd, g_thread_up, g_listen) *)
Lemma dcE_model_kept : forall ly S (W : world segs) mem ly2 S2 (W2 : world segs) mem2 md2 mc si h' R HA,
  AR segs B ly2 S2 W2 mem2 md2 -> (si < 4)%nat -> HA = rg_s fr_RG + ASRC * Z.of_nat si ->
  amodel_ne ly S W mem mc false ->
  Forall (fun e => Z.of_nat (length (re_keys e)) <= re_nheld e) (lm_es mc) ->
  asrc_at B ly2 S2 W2 mem2 HA h' ->
  (forall i b, (i < 4)%nat -> i <> si -> In b (slot_blks (nth i (lm_hs mc) None)) -> In b R) ->
  (forall b, In b (arelay_blks (lm_G mc) (lm_es mc)) -> In b R) ->
  (forall b, In b (aout_blks (lm_cap mc) (lm_out mc)) -> In b R) ->
  (forall b, In b R -> In b (ablocks B ly2 S2)) ->
  (forall b a, In b R -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a) ->
  (forall a, inG G_fr a -> ~ inG [(HA + 64, 32)] a -> ~ (as_errno B <= a < as_errno B + 4) ->
     abyte_kept W mem W2 mem2 a) ->
  amodel_ne ly2 S2 W2 mem2 (dc_setsrc mc si h') false.
Proof.
  intros ly S W mem ly2 S2 W2 mem2 md2 mc si h' R HA AR2 Hsi EHA HMOD HKY HSRC2 HOi HGER HAOR Rin2 KBLK KI0.
  pose proof dcE_rg as (Es & Esrc & Ensrc & Ecap & Eout & Enout & Ecapout & Esmax & Eseintr & Esdead & Egone & Eclient
    & Ecb & Elock & Ewake).
  assert (EASRC : ASRC = 96) by reflexivity.
  assert (EHA' : HA = rg_s fr_RG + 96 * Z.of_nat si) by (rewrite EHA, EASRC; reflexivity).
  pose proof HERR_HI as HEH.
  pose proof HMOD as (Hlen4 & HSL & HREL & (ev & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  assert (KGL : forall a, inG G_fr a -> (a < rg_s fr_RG \/ rg_s fr_RG + 4 * ASRC <= a) -> a < rg_out fr_RG + 8 ->
      abyte_kept W mem W2 mem2 a).
  { intros a HGa Hs He. apply KI0; [exact HGa | rewrite dcE_inG1; lia | lia]. }
  assert (KGS : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> ~ (HA + 64 <= a < HA + 96) ->
      abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn. apply KI0; [apply HGs; exact Ha | rewrite dcE_inG1; lia | lia]. }
  assert (KDG : forall x n a, In (x, n) DR_GK -> x <= a < x + n -> abyte_kept W mem W2 mem2 a).
  { intros x n a Hx Ha. apply KGL; [apply HG_GK; exact (dcE_inG_mem _ x n a Hx Ha) | |];
      unfold DR_GK in Hx; cbn [In] in Hx;
      repeat (destruct Hx as [Hx | Hx]; [injection Hx as <- <-; unfold AG_NFD, AG_THREAD_UP, AG_LISTEN in *; lia|]);
      destruct Hx. }
  assert (KSL : forall x n a, In (x, n) [(rg_client_broken fr_RG, 1); (rg_send_eintr fr_RG, 1); (rg_nout fr_RG, 8);
      (rg_capout fr_RG, 8); (rg_out fr_RG, 8)] -> x <= a < x + n -> abyte_kept W mem W2 mem2 a).
  { intros x n a Hx Ha. apply KGL.
    - apply HG_DR. apply (dcE_inG_mem _ x n a); [|exact Ha]. unfold G_DR, G_SL. right. cbn [In] in Hx |- *. tauto.
    - cbn [In] in Hx. repeat (destruct Hx as [Hx | Hx]; [injection Hx as <- <-; lia|]). destruct Hx.
    - cbn [In] in Hx. repeat (destruct Hx as [Hx | Hx]; [injection Hx as <- <-; lia|]). destruct Hx. }
  assert (HSL2 : forall i, (i < 4)%nat -> aslot B ly2 S2 W2 mem2 i (nth i (set_nth si (Some h') (lm_hs mc)) None)).
  { intros i Hi. destruct (Nat.eq_dec i si) as [-> | Hne].
    - rewrite set_nth_same by lia. cbn [aslot]. rewrite <- EHA. exact HSRC2.
    - rewrite set_nth_other by lia.
      pose proof (HOi i) as HOi'. pose proof (HSL i Hi) as Hs.
      destruct (nth i (lm_hs mc) None) as [hi|] eqn:Ehi; rewrite ?Ehi in Hs, HOi'; cbn [aslot slot_blks] in Hs, HOi' |- *.
      + apply (asrc_at_kept B ly S W mem ly2 S2 W2 mem2 _ hi Hs).
        * intros r Hr a Ha. destruct (dj_asrc_fp ly S W mem _ hi Hs r Hr a Ha) as [Hin | (b & Hb & Hab)].
          -- cbv beta in Hin. rewrite EASRC in Hin. apply KGS; lia.
          -- exact (KBLK b a (HOi' b Hi Hne Hb) Hab).
        * intros b Hb. exact (Rin2 _ (HOi' b Hi Hne Hb)).
      + destruct Hs as [G1 G2]. split.
        * apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx. rewrite EASRC in Hx.
          apply KGS; lia.
        * apply (akept_awr W mem); [|exact G2]. intros x Hx. rewrite EASRC in Hx. apply KGS; lia. }
  assert (HREL2 : arelay_at B fr_RG ly2 S2 W2 mem2 (lm_G mc) (lm_es mc)).
  { apply (arelay_at_kept B fr_RG ly S W mem ly2 S2 W2 mem2 _ _ HREL).
    - intros r Hr a Ha. destruct (dj_arelay_fp ly S W mem _ _ HREL HKY r Hr a Ha) as [Hg | (b & Hb & Hab)].
      + destruct Hg as [Hg | [Hg | Hg]].
        * apply (KDG (rg_src fr_RG) 8 a); [unfold DR_GK; dcE_infp | exact Hg].
        * apply (KDG (rg_nsrc fr_RG) 4 a); [unfold DR_GK; dcE_infp | exact Hg].
        * apply (KDG (rg_capsrc fr_RG) 4 a); [unfold DR_GK; dcE_infp | exact Hg].
      + exact (KBLK b a (HGER b Hb) Hab).
    - intros b Hb. exact (Rin2 _ (HGER b Hb)). }
  destruct (ERR ly2 S2 W2 mem2 md2 AR2) as ((ev2 & Mev2 & Hev2) & Wev2).
  assert (HOUT2 : aout_at B fr_RG ly2 S2 W2 mem2 (dc_ctl (lm_c mc) ev2) (lm_O mc) (lm_mx mc)
                    (Z.of_nat (length (lm_O mc))) (lm_cap mc) (lm_out mc)).
  { apply (dcE_aout ly S W mem ly2 S2 W2 mem2 _ _ _ _ _ _ ev2 HOUT);
      [| intros b Hb; exact (Rin2 _ (HAOR b Hb)) | exact Mev2 | exact Wev2 | exact Hev2].
    intros r Hr a Ha. unfold dcE_ofp in Hr. apply in_app_or in Hr as [Hr | Hr].
    - cbn [In] in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]; cbn [fst snd] in Ha.
      + apply (KDG (rg_send_max fr_RG) 8 a); [unfold DR_GK; dcE_infp | lia].
      + apply (KSL (rg_nout fr_RG) 8 a); [dcE_infp | lia].
      + apply (KSL (rg_capout fr_RG) 8 a); [dcE_infp | lia].
      + apply (KSL (rg_out fr_RG) 8 a); [dcE_infp | lia].
      + apply (KDG (rg_client fr_RG) 4 a); [unfold DR_GK; dcE_infp | lia].
      + apply (KSL (rg_client_broken fr_RG) 1 a); [dcE_infp | lia].
      + apply (KDG (rg_send_dead fr_RG) 1 a); [unfold DR_GK; dcE_infp | lia].
      + apply (KSL (rg_send_eintr fr_RG) 1 a); [dcE_infp | lia].
    - revert Hr. destruct (Z.eqb_spec (lm_cap mc) 0) as [Ec | Ec]; intros Hr; cbn in Hr.
      + destruct Hr.
      + destruct Hr as [<- | []]. cbn [fst snd] in Ha.
        apply (KBLK (lm_out mc, lm_cap mc) a); [|cbn [fst snd]; lia].
        apply HAOR. unfold aout_blks. rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) Ec). left. reflexivity. }
  assert (HGONE2 : agone_at fr_RG W2 mem2 (lm_gn mc)).
  { apply (agone_at_kept fr_RG W mem W2 mem2 _ HGONE). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KDG (rg_gone fr_RG) 1 a); [unfold DR_GK; dcE_infp | lia]. }
  assert (HLOCK2 : alock_at fr_RG W2 mem2 false).
  { apply (alock_at_kept fr_RG W mem W2 mem2 _ HLOCK). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply KGL; [apply HGlock; lia | lia | lia]. }
  assert (HWAKE2 : awake_at fr_RG W2 mem2).
  { apply (awake_at_kept fr_RG W mem W2 mem2 HWAKE). intros r [<- | []] a Ha. cbn [fst snd] in Ha.
    apply (KDG (rg_wake fr_RG) 8 a); [unfold DR_GK; dcE_infp | lia]. }
  unfold amodel_ne. cbn [dc_setsrc lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
  split; [rewrite set_nth_length; exact Hlen4|].
  split; [exact HSL2|]. split; [exact HREL2|]. split; [exists ev2; exact HOUT2|].
  split; [exact HGONE2|]. split; [exact HLOCK2|]. split; [exact HWAKE2|].
  split; [apply (akept_vm W mem); [|exact HNFD]; intros x Hx; apply (KDG AG_NFD 4 x); [unfold DR_GK; dcE_infp | lia]|].
  split; [apply (akept_awr W mem); [|exact HNFDW]; intros x Hx; apply (KDG AG_NFD 4 x); [unfold DR_GK; dcE_infp | lia]|].
  split; [exact HNFDr|].
  split; [apply (akept_vm W mem); [|exact HTUP]; intros x Hx; apply (KDG AG_THREAD_UP 1 x); [unfold DR_GK; dcE_infp | lia]|].
  split; [destruct HLST as (lst & HL); exists lst; apply (akept_vm W mem); [|exact HL]; intros x Hx;
          apply (KDG AG_LISTEN 4 x); [unfold DR_GK; dcE_infp | lia]|].
  apply (akept_awr W mem); [|exact HLSTW]. intros x Hx. apply (KDG AG_LISTEN 4 x); [unfold DR_GK; dcE_infp | lia].
Qed.

Lemma dc_stE : forall cx t m j si fpos FF ly S mc h1 W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (si < 4)%nat -> nth si (lm_hs mc) None = Some h1 ->
  NoDup (texts (hs_held h1)) -> hl_n (hs_expected h1) < 2 ^ 26 ->
  hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1))) < 2 ^ 22 ->
  cnl_room MMAX (blocks_bytes S) (texts (hs_held h1)) (hl_cap (hs_held h1)) (hl_recs (hs_expected h1)) ->
  mo_ok MT S (cnl_cost MT (hs_expected h1) (hs_held h1)) ->
  AREC * capb (hs_held h1) (hs_expected h1) < 2 ^ 32 ->
  (lm_gn mc = 0 -> exists rest, lm_O mc = bstream (hs_expected h1) ++ rest) ->
  dc_at cx t m j si fpos FF A_dc_r4 ly S mc false 0 W c ->
  SRr segs W c (fun W' c' => exists ly' S' E' H',
    dc_at cx t m j si fpos FF A_dc_r5 ly' S' (dc_setsrc mc si (set_exp_held h1 E' H')) false
      (if lm_gn mc =? 0 then Z.of_nat (length (bstream (hs_expected h1))) else 0) W' c' /\
    mo_le MT S S' (cnl_cost MT (hs_expected h1) (hs_held h1)) /\
    dr_cfun h1 E' H').
Proof.
  intros cx t m j si fpos FF ly S mc h1 W c HB Hsi Hh1 HND HnE HnH HROOM HMO HCAPB HOB
    (regs & mem & md & k & -> & DR & HJ & HFF & HFR & HFL & HIN & HRV & HROM & SVN & SAT & SLK & HMOD & HSEP & HKY).
  pose proof DR as DR0.
  destruct DR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R21 & R22 & R25).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : AR segs B ly S W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & _ & Hnlen & _).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  set (sp0 := spZ (c_regs cx)) in *.
  set (F := lf_F cx) in *.
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  destruct (dc_plain_entry A_dc_r4 W regs mem R26) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK DRspan AF_fr_check_no_loss.
  { apply awr_ok_x_nil. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
                HS HAE ltac:(vm_compute; reflexivity)) as KR3.
  cbn [ms_regs restrict] in KR3.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  pmkst HS. rewrite Em in *. clear HF HFr HG0.
  (* ---- the call's registers ---- *)
  set (regsc := ms_regs ms) in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  pose proof dcE_rg as (Es & Esrc & Ensrc & Ecap & Eout & Enout & Ecapout & Esmax & Eseintr & Esdead & Egone & Eclient
    & Ecb & Elock & Ewake).
  pose proof dcE_vals as (Vnout & Vout & Vgone & Vs).
  assert (EASRC : ASRC = 96) by reflexivity.
  set (HA := rg_s fr_RG + ASRC * Z.of_nat si) in *.
  assert (EHA : HA = rg_s fr_RG + ASRC * Z.of_nat si) by reflexivity.
  assert (HFlo : DR_CEIL8 + 32000 <= F) by (unfold DR_CEIL8; lia).
  assert (E21 : ew E 21 = getr regs 21)
    by (rewrite (proj1 HAE 21%nat ltac:(apply Nat.ltb_lt; reflexivity)); apply ew_Ereg_nat; reflexivity).
  assert (E9 : ew E 9 = getr regs 9)
    by (rewrite (proj1 HAE 9%nat ltac:(apply Nat.ltb_lt; reflexivity)); apply ew_Ereg_nat; reflexivity).
  assert (Rc10 : getr regsc 10 = w64 HA) by (rewrite Q10, E21; exact R21).
  assert (Rc11 : getr regsc 11 = w64 (F + 192)).
  { rewrite Q11, E9, R9. unfold w64. rewrite unsigned_lit_small by (unfold DR_CEIL8 in *; lia). reflexivity. }
  assert (Hspc : spZ regsc = F).
  { unfold spZ. rewrite (KR3 2%bv ltac:(dcE_infp)). exact Hsp. }
  assert (HJin : exists memS, ajournal segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly S W mem mdc k).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0. exists memS. exact HJ0. }
  destruct HJin as (memS & HJ0).
  pose proof HJ0 as (HARc & HLY & _ & _ & _ & HFRS0 & _ & _ & _ & _ & _ & _ & HJgone & HJpres & _).
  assert (Etop : ly_top ly = ly_top (c_ly cx)) by (pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
  assert (Hfin : In (1, fpos) (frames S)) by (rewrite HFRS0; left; reflexivity).
  (* ---- the model at the call ---- *)
  pose proof HMOD as (Hlen4 & HSL & HREL & (ev & HOUT) & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  assert (HSRC : asrc_at B ly S W mem HA h1) by (pose proof (HSL si Hsi) as X; rewrite Hh1 in X; exact X).
  pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLE & HLH & _).
  set (LE := list_blks (hs_expected h1)). set (LH := list_blks (hs_held h1)).
  set (PP := (hs_partial h1, APARTIAL) :: alist_blks (hs_pending h1)).
  set (OTH := concat (map slot_blks (firstn si (lm_hs mc) ++ skipn (Datatypes.S si) (lm_hs mc)))).
  set (ENT := concat (map aentry_blks (lm_es mc))).
  set (AO := aout_blks (lm_cap mc) (lm_out mc)).
  set (GE := [(lm_G mc, ATABLE)]).
  destruct HSEP as ((RS & HP0) & HSEP2).
  set (R := PP ++ input_blks cx ++ GE ++ ENT ++ OTH ++ AO ++ RS).
  assert (HCS : Permutation (concat (map slot_blks (lm_hs mc))) ((PP ++ LE ++ LH) ++ OTH)).
  { pose proof (dr_concat_nth_perm _ _ slot_blks (lm_hs mc) si None ltac:(lia)) as X. rewrite Hh1 in X. exact X. }
  assert (HP1 : Permutation (ablocks B ly S) ((LE ++ LH) ++ R)).
  { apply (Permutation_trans HP0).
    exact (dcE_perm_shape (input_blks cx) GE ENT OTH AO RS PP LE LH (concat (map slot_blks (lm_hs mc))) HCS). }
  assert (HND1 : List.NoDup ((LE ++ LH) ++ R)) by exact (Permutation_NoDup HP1 (dj_nodup ly S W mem md HAR)).
  assert (LEHin : forall b, In b (LE ++ LH) -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. left. exact Hb. }
  assert (Rin : forall b, In b R -> In b (ablocks B ly S)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP1)). apply in_or_app. right. exact Hb. }
  assert (RnLEH : forall b, In b R -> ~ In b (LE ++ LH)) by (intros b H1 H2; exact (dcE_nodup_app _ _ b HND1 H2 H1)).
  assert (CSmodel : forall b, In b (concat (map slot_blks (lm_hs mc))) -> In b (model_blks mc)).
  { intros b Hb. unfold model_blks. right. apply in_or_app. right. apply in_or_app. left. exact Hb. }
  assert (H1CS : forall b, In b (PP ++ LE ++ LH) -> In b (concat (map slot_blks (lm_hs mc)))).
  { intros b Hb. apply in_concat. exists (slot_blks (Some h1)). split; [apply in_map; rewrite <- Hh1; apply nth_In; lia|].
    exact Hb. }
  assert (LEHmodel : forall b, In b (LE ++ LH) -> In b (model_blks mc)).
  { intros b Hb. apply CSmodel, H1CS. apply in_or_app. right. exact Hb. }
  assert (LEHpos : forall b, In b (LE ++ LH) -> 0 < snd b).
  { intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    - exact (dcE_blks_pos ly S W mem _ _ _ HLE b Hb).
    - exact (dcE_blks_pos ly S W mem _ _ _ HLH b Hb). }
  (* ---- check_no_loss's G: slot si's two list headers ---- *)
  assert (HGcG : forall a, inG [(HA + 64, 32)] a -> inG G_fr a).
  { intros a Ha. apply dcE_inG1 in Ha. apply HGs. lia. }
  assert (HGc : gx_ok segs B [(HA + 64, 32)]) by exact (gx_ok_sub segs B _ _ HGcG HG).
  assert (HGrt : gx_rt B [(HA + 64, 32)]).
  { intros a Ha. apply dcE_inG1 in Ha. destruct HAP as [HAP0 HAP32]. split; [|split]; lia. }
  assert (HZc : azs B (HA + 64) 32).
  { destruct HZS as (r & Hr & H8 & H1 & H2). exists r. split; [exact Hr|]. split; [exact H8|]. split; lia. }
  (* ---- check_no_loss's premises ---- *)
  pose proof HOUT as (_ & _ & O3 & _ & _ & _ & O7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                      _ & _ & _ & _ & _ & _ & _ & O26).
  assert (HAOR : forall b, In b AO -> In b R)
    by (intros b Hb; unfold R; do 5 (apply in_or_app; right); apply in_or_app; left; exact Hb).
  assert (HPPR : forall b, In b PP -> In b R) by (intros b Hb; unfold R; apply in_or_app; left; exact Hb).
  assert (HOBX : ob_at W mem (lm_out mc) (lm_O mc) /\
     Z.of_nat (length (lm_O mc)) <= 2 ^ 40 /\ (0 < Z.of_nat (length (lm_O mc)) -> Z.of_nat (length (lm_O mc)) < 2 ^ 32) /\
     amem_range (lm_out mc) (Z.of_nat (length (lm_O mc)) + 8) /\
     (lm_O mc = [] \/ exists CO, Z.of_nat (length (lm_O mc)) <= CO /\ In (lm_out mc, CO) (ablocks B ly S) /\
        ~ In (lm_out mc) (hs_blocks h1))).
  { destruct O26 as [(Hc0 & Hout0 & Hno0) | (Hcp & Hno & Hin & junk & Hj & Hg)].
    - assert (HO0 : lm_O mc = []) by (apply length_zero_iff_nil; lia).
      rewrite HO0, Hout0. cbn [length]. split; [intros i Hi; cbn in Hi; lia|].
      split; [lia|]. split; [lia|]. split; [left; unfold kLowMemEnd; lia | left; reflexivity].
    - destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & _ & _ & Happ & _ & _ & Hmx).
      assert (Ers : req_size (lm_cap mc) = lm_cap mc) by (unfold req_size; rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) ltac:(lia)); reflexivity).
      rewrite Ers in Happ. unfold MALLOC_MAX in Hmx.
      split; [exact (dcE_ob_at W mem _ _ _ Hg)|].
      split; [lia|]. split; [lia|].
      split; [zlia|].
      right. exists (lm_cap mc). split; [lia|]. split; [exact Hin|].
      intros Hx. destruct (dcE_hs_blocks h1 _ Hx) as (n & Hn).
      assert (HnPP : In (lm_out mc, n) (PP ++ LE ++ LH)) by exact Hn.
      assert (HAOc : In (lm_out mc, lm_cap mc) AO)
        by (unfold AO, aout_blks; rewrite (proj2 (Z.eqb_neq (lm_cap mc) 0) ltac:(lia)); left; reflexivity).
      assert (Hn1 : In (lm_out mc, n) (ablocks B ly S)).
      { apply in_app_or in HnPP as [Hp | Hp]; [exact (Rin _ (HPPR _ Hp)) | exact (LEHin _ Hp)]. }
      destruct (dcE_dec (lm_out mc, n) (lm_out mc, lm_cap mc)) as [Heq | Hne].
      + rewrite Heq in HnPP. apply in_app_or in HnPP as [Hp | Hp].
        * apply (dcE_nodup_app PP (input_blks cx ++ GE ++ ENT ++ OTH ++ AO ++ RS) (lm_out mc, lm_cap mc)
            (dcE_nodup_r _ _ HND1) Hp). do 4 (apply in_or_app; right). apply in_or_app. left. exact HAOc.
        * exact (RnLEH _ (HAOR _ HAOc) Hp).
      + destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hn1) as (_ & _ & _ & _ & _ & _ & Hn0).
        pose proof (req_size_pos n ltac:(lia)) as [Hr1 _]. pose proof (req_size_pos (lm_cap mc) ltac:(lia)) as [Hr2 _].
        exact (dj_apart ly S W mem md _ _ _ _ (lm_out mc) HAR Hin Hn1 (fun E => Hne (eq_sym E)) ltac:(lia) ltac:(lia)). }
  destruct HOBX as (HOBAT & HNO40 & HNO32 & HMR & HOB0). clear O26.
  assert (P5 : forall a, spZ regsc <= a < spZ regsc + 208 -> apresent (w_H W) mem a).
  { intros a Ha. apply HJpres. rewrite Hspc in Ha. unfold LLVMF_STK. lia. }
  assert (P21 : val_mem segs (arm W mem) (VAL A_g_gone) 1 (lm_gn mc)) by (rewrite Vgone; exact (proj1 HGONE)).
  assert (P22 : 0 <= lm_gn mc < 256) by (destruct HGONE as (_ & _ & [G0 | G0]); lia).
  assert (P23 : val_mem segs (arm W mem) (VAL A_g_nout) 8 (Z.of_nat (length (lm_O mc)))) by (rewrite Vnout; exact O3).
  assert (P24 : val_mem segs (arm W mem) (VAL A_g_out) 8 (lm_out mc)) by (rewrite Vout; exact O7).
  assert (HF8 : (F + 192) mod 8 = 0).
  { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite HF32, Z.add_0_r in D. rewrite D.
    replace (32 * (F / 32) + 192) with ((4 * (F / 32) + 24) * 8) by ring. apply Z_mod_mult. }
  (* ---- check_no_loss's afn_pre at sp = F ---- *)
  destruct (dr_afn_pre_at cx ly S fpos k W mem mdc regsc CNL_STK HB HJ) as (ch & HPREc).
  { rewrite HFF. exact (dr_aframe_false cx FF W mem HFR). }
  { exact Hspc. }
  { rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  { unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia. }
  { rewrite (KR3 3%bv ltac:(dcE_infp)). exact R3. }
  { rewrite (KR3 4%bv ltac:(dcE_infp)). exact R4. }
  { rewrite (KR3 8%bv ltac:(dcE_infp)). exact R8. }
  { rewrite dcE_cnl_stk. lia. }
  { rewrite dcE_cnl_stk. unfold LLVMF_STK. lia. }
  assert (P4 : spZ regsc + 208 <= ly_top ly) by (rewrite Hspc, Etop; lia).
  assert (P8 : HA = VAL A_g_s + ASRC * Z.of_nat si) by (rewrite Vs; reflexivity).
  assert (P11 : spZ regsc <= F + 192) by (rewrite Hspc; lia).
  assert (P12 : F + 192 + 8 <= spZ regsc + 208) by (rewrite Hspc; lia).
  assert (P14 : forall a, HA + 64 <= a < HA + 96 -> inG [(HA + 64, 32)] a) by (intros a Ha; apply dcE_inG1; lia).
  pose proof (dcE_lit W mem _ _ HRV (proj1 dcE_lits)) as L1.
  pose proof (dcE_lit W mem _ _ HRV (proj1 (proj2 dcE_lits))) as L2.
  pose proof (dcE_lit W mem _ _ HRV (proj2 (proj2 dcE_lits))) as L3.
  assert (P20 : 0 <= 0 <= Z.of_nat (length (lm_O mc))) by lia.
  (* ---- the call ---- *)
  set (FPc := blk_FP (LE ++ LH)).
  set (K := fun (ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word)
      (mem2 : word -> option byte) (md2 : Model) =>
    exists kk (E' H' : hlist),
      ajournal_gx segs B [(HA + 64, 32)] 208 [(F + 192, F + 192 + 8)] CNL_STK (spZ regsc) FPc ly S W mem mdc []
        ly2 S2 W2 mem2 md2 kk /\
      asrc_at B ly2 S2 W2 mem2 HA (set_exp_held h1 E' H') /\
      hl_recs E' = [] /\ hl_v E' = hl_v (hs_expected h1) /\ hl_cap E' = hl_cap (hs_expected h1) /\
      NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h1)) (texts (hs_expected h1)) /\
      hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h1))
                                  (2 * (hl_n (hs_held h1) + Z.of_nat (count_begin (texts (hs_expected h1)))))) /\
      val_mem segs (arm W2 mem2) (F + 192) 8
        (if lm_gn mc =? 0 then 0 + Z.of_nat (length (bstream (hs_expected h1))) else 0) /\
      (forall rest, Permutation (ablocks B ly S) (LE ++ LH ++ rest) ->
         Permutation (ablocks B ly2 S2) (list_blks E' ++ list_blks H' ++ rest)) /\
      mo_le MT S S2 (cnl_cost MT (hs_expected h1) (hs_held h1))).
  eapply SRr_mono.
  { apply (dr_callZ G_fr W regsc mem (Z_to_bv 64 (BASE + 13932)) LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S mdc k CNL_STK FPc 208
      [(F + 192, F + 192 + 8)] (F - sp0) (getr regsc 1) ch K HG HJ).
    - rewrite Hspc. lia.
    - lia.
    - rewrite dcE_cnl_stk. unfold LLVMF_STK. lia.
    - lia.
    - lia.
    - intros a (r & [<- | []] & Hr). cbn [fst snd] in Hr. unfold LLVMF_STK. lia.
    - reflexivity.
    - exact HPREc.
    - eapply SRr_mono.
      { exact (CNL [(HA + 64, 32)] HGc HGrt W ly S regsc mem mdc ch 208 HA si (F + 192) h1 (lm_gn mc) 0
          (Z.of_nat (length (lm_O mc))) (lm_out mc) (lm_O mc)
          HPREc ltac:(lia) eq_refl P4 P5 Rc10 Rc11 P8 Hsi HF8 P11 P12 HSRC P14 HZc
          HND HnE HnH SAT P20 P21 P22 P23 P24 HOBAT eq_refl HNO40 HNO32 HMR HOB0 HOB HRV L1 L2 L3 HROOM HMO HCAPB
          ltac:(intros a Ha; rewrite Hspc in Ha; exact (dr_stkr cx fpos ly S W mem mdc k HB HJ a Ha))). }
      cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & kk & E' & H' & -> & JC & HPR & HPK & _ & HSRC2 & ER & EV & EC &
        HNDH & HTX & HCAPH & MAT & MGN & MNO & MOUT & HOB2 & HPERM & HFRS & HMO2 & _ & _).
      exists ly2, S2, regs2, mem2, md2, kk. split; [reflexivity|].
      split; [eapply ajournal_gx_G_mono; [exact HGcG | exact JC]|].
      split; [exact HPR|].
      unfold K. exists kk, E', H'. split; [exact JC|]. split; [exact HSRC2|].
      do 6 (split; [assumption|]). split; [exact MAT|]. split; [exact HPERM | exact HMO2].
    - intros a (r & Hr & Hra). unfold FPc, blk_FP in Hr. apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Hra.
      pose proof (LEHin _ Hb) as Hbl.
      destruct (in_dec dcE_dec (p, n) (ablocks B (c_ly cx) (c_S cx))) as [Hc | Hc].
      + left. destruct (HSEP2 _ (LEHmodel _ Hb)) as [Hn | Hfp]; [exfalso; exact (Hn Hc)|].
        split; [exact (Hfp a Hra)|].
        exists p, n. split; [exact Hbl | exact Hra].
      + right. exists p, n. split; [exact Hbl|]. split; [exact Hc | exact Hra]. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & _ & HPR2 & HK2).
  unfold K in HK2.
  destruct HK2 as (kk & E' & H' & JC & HSRC2 & ER & EV & EC & HNDH & HTX & HCAPH & MAT & HPERM & HMO2).
  rewrite Hspc in JC. clear HOB0.
  assert (AR2 : AR segs B ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR; exact JC).
  assert (EHA' : HA = rg_s fr_RG + 96 * Z.of_nat si) by (rewrite EHA, EASRC; reflexivity).
  set (h' := set_exp_held h1 E' H') in *.
  set (LE' := list_blks E'). set (LH' := list_blks H').
  assert (HP2 : Permutation (ablocks B ly2 S2) ((LE' ++ LH') ++ R)).
  { rewrite <- app_assoc. apply HPERM. rewrite app_assoc. exact HP1. }
  assert (HND2 : List.NoDup ((LE' ++ LH') ++ R)) by exact (Permutation_NoDup HP2 (dj_nodup ly2 S2 W2 mem2 md2 AR2)).
  assert (Rin2 : forall b, In b R -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. exact Hb. }
  assert (LEHin2 : forall b, In b (LE' ++ LH') -> In b (ablocks B ly2 S2)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. left. exact Hb. }
  (* ---- what check_no_loss keeps ---- *)
  pose proof (dcE_kept_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KB0.
  pose proof (dcE_kept_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KI0.
  pose proof (dcE_kept_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HGc JC HARc LEHin) as KF0.
  assert (KBLK : forall b a, In b R -> fst b <= a < fst b + snd b -> abyte_kept W mem W2 mem2 a).
  { intros [p n] a HbR Ha. cbn [fst snd] in Ha. pose proof (Rin _ HbR) as Hin1.
    destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin1) as (_ & _ & _ & _ & _ & _ & Hn).
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrs].
    exact (KB0 p n a Hin1 (Rin2 _ HbR) (RnLEH _ HbR) ltac:(lia)). }
  assert (HOi : forall i b, (i < 4)%nat -> i <> si -> In b (slot_blks (nth i (lm_hs mc) None)) -> In b R).
  { intros i b Hi Hne Hb. assert (Hb' : In b OTH).
    { unfold OTH. apply in_concat. exists (slot_blks (nth i (lm_hs mc) None)). split; [|exact Hb].
      apply in_map. apply dcE_nth_rm; [rewrite Hlen4; exact Hi | exact Hne]. }
    unfold R. do 4 (apply in_or_app; right). apply in_or_app. left. exact Hb'. }
  assert (HGER : forall b, In b (arelay_blks (lm_G mc) (lm_es mc)) -> In b R).
  { intros b [<- | Hb]; unfold R.
    - do 2 (apply in_or_app; right). apply in_or_app. left. unfold GE. left. reflexivity.
    - do 3 (apply in_or_app; right). apply in_or_app. left. exact Hb. }
  pose proof (dcE_model_kept ly S W mem ly2 S2 W2 mem2 md2 mc si h' R HA AR2 Hsi EHA HMOD HKY HSRC2 HOi HGER HAOR
    Rin2 KBLK KI0) as HMOD2.
  (* ---- the blocks after the call ---- *)
  assert (HCS' : Permutation (concat (map slot_blks (set_nth si (Some h') (lm_hs mc)))) ((PP ++ LE' ++ LH') ++ OTH))
    by exact (dr_concat_set_nth_perm _ _ slot_blks (lm_hs mc) si (Some h') ltac:(lia)).
  assert (HP3 : Permutation (input_blks cx ++ model_blks (dc_setsrc mc si h') ++ RS) ((LE' ++ LH') ++ R))
    by exact (dcE_perm_shape (input_blks cx) GE ENT OTH AO RS PP LE' LH' _ HCS').
  assert (HSEP' : ablocks_sep B fr_FP cx (dc_setsrc mc si h') ly2 S2).
  { split; [exists RS; exact (Permutation_trans HP2 (Permutation_sym HP3))|].
    intros b Hb.
    assert (Hcase : In b (LE' ++ LH') \/ In b (model_blks mc)).
    { unfold model_blks in Hb. cbn [dc_setsrc lm_G lm_es lm_hs lm_cap lm_out] in Hb.
      destruct Hb as [<- | Hb]; [right; unfold model_blks; left; reflexivity|].
      apply in_app_or in Hb as [Hb | Hb]; [right; unfold model_blks; right; apply in_or_app; left; exact Hb|].
      apply in_app_or in Hb as [Hb | Hb];
        [|right; unfold model_blks; right; apply in_or_app; right; apply in_or_app; right; exact Hb].
      apply (Permutation_in _ HCS') in Hb. apply in_app_or in Hb as [Hb | Hb].
      - apply in_app_or in Hb as [Hb | Hb]; [right; apply CSmodel, H1CS, in_or_app; left; exact Hb | left; exact Hb].
      - right. apply CSmodel. unfold OTH in Hb. apply in_concat in Hb as (l & Hl & Hbl). apply in_concat.
        exists l. split; [|exact Hbl]. apply in_map_iff in Hl as (o & <- & Ho). apply in_map.
        exact (dr_in_rm _ si o (lm_hs mc) Ho). }
    destruct Hcase as [Hnew | Hold]; [|exact (HSEP2 b Hold)].
    destruct (in_dec dcE_dec b (ablocks B (c_ly cx) (c_S cx))) as [Hc | Hc]; [|left; exact Hc]. right.
    destruct (in_dec dcE_dec b (ablocks B ly S)) as [Hb1 | Hb1].
    - apply (Permutation_in _ HP1) in Hb1. apply in_app_or in Hb1 as [Hb1 | Hb1].
      + destruct (HSEP2 b (LEHmodel b Hb1)) as [Hn | Hfp]; [exfalso; exact (Hn Hc) | exact Hfp].
      + exfalso. exact (dcE_nodup_app _ _ b HND2 Hnew Hb1).
    - destruct b as [p n]. intros a Ha. cbn [fst snd] in Ha.
      pose proof (LEHin2 _ Hnew) as Hb2.
      destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 p n AR2 Hb2) as (_ & _ & _ & _ & _ & _ & Hn).
      pose proof (req_size_pos n ltac:(lia)) as [_ Hrs].
      replace a with (p + (a - p)) by lia. exact (HJgone p n (a - p) Hc Hb1 ltac:(lia)). }
  (* ---- the frame, the input, the ROM, the cells ---- *)
  assert (KOUT : forall a, F <= a < sp0 -> ~ (F + DR_AT <= a < F + DR_AT + 8) -> abyte_kept W mem W2 mem2 a).
  { intros a Ha Hn. unfold DR_AT in Hn.
    apply (dcE_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HGc JC).
    - unfold DR_CEIL8 in *. lia.
    - rewrite dcE_inG1. unfold DR_CEIL8 in *. lia.
    - intros Hi. pose proof (Hsegs a Hi). unfold DR_CEIL8 in *. lia.
    - destruct (Z_lt_le_dec a (F + 208)) as [Hlt | Hge].
      + right; left. split; [lia|]. intros (r & [<- | []] & Hr). cbn [fst snd] in Hr. lia.
      + left. unfold DR_CEIL8 in *. split; lia. }
  assert (WF : forall a, F <= a < sp0 -> writable_at segs (arm W2 mem2) a).
  { pose proof HJ2 as (_ & _ & (memS2 & HJ20 & _) & _). rewrite !Z.add_0_r in HJ20.
    pose proof HJ20 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
    intros a Ha. apply (apresent_writable segs). apply HJ2pres. unfold LLVMF_STK. lia. }
  assert (KFF : forall a, FF <= a < FF + 128 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. apply (KF0 1 fpos a Hfin). left. unfold in_zr, frame_rng. cbn [fst snd].
    rewrite HFF. replace (fs_frame_bytes 1) with 128 by reflexivity. lia. }
  assert (KSH : forall a, SB + FF / 8 <= a < SB + FF / 8 + 16 -> abyte_kept W mem W2 mem2 a).
  { intros a Ha. apply (KF0 1 fpos a Hfin). right. unfold in_zr. cbn [fst snd].
    rewrite HFF. replace (fs_frame_bytes 1 / 8) with 16 by reflexivity. unfold shadow_addr.
    unfold SB, SHADOW_OFF in *. lia. }
  assert (H320 : lf_F cx + 320 <= spZ (c_regs cx)) by (change (F + 320 <= sp0); lia).
  assert (HFR2 : aframe_at cx true FF W2 mem2) by exact (dcE_aframe_kept cx true FF W W2 mem mem2 HFR H320 KOUT WF KFF KSH).
  assert (HFL2 : sv8 W2 mem2 (FF + 120) (flag_addr ly2 1 fpos)).
  { pose proof JC as (_ & _ & (memC & JC0 & _) & _). pose proof JC0 as (_ & HLY2 & _).
    pose proof HLY2 as (_ & _ & _ & _ & _ & EF & _). unfold flag_addr. rewrite EF.
    apply (dr_sv8_kept W W2 mem mem2); [intros x Hx; apply KFF; lia | exact HFL]. }
  assert (HIN2 : ainput_at B cx ly2 S2 W2 mem2).
  { destruct HIN as (Hcase & Hg).
    assert (HINR : c_n cx <> 0 -> In (c_p cx, c_n cx) R).
    { intros Hn0. unfold R. apply in_or_app. right. apply in_or_app. left. unfold input_blks.
      rewrite (proj2 (Z.eqb_neq (c_n cx) 0) Hn0). left. reflexivity. }
    split.
    - destruct Hcase as [Hc | (Hn & Hin)]; [left; exact Hc | right; split; [exact Hn|]].
      exact (Rin2 _ (HINR ltac:(lia))).
    - apply (akept_garr8 W mem); [|exact Hg]. intros x Hx. rewrite length_map in Hx.
      destruct Hcase as [(Hc & _) | (Hn & Hin)].
      + lia.
      + apply (KBLK (c_p cx, c_n cx) x (HINR ltac:(lia))). cbn [fst snd]. lia. }
  assert (HRO : rom_out segs B [(HA + 64, 32)]).
  { intros a Ha. destruct (DR_ROM_OUT a Ha) as (H1 & H2 & H3 & H4).
    split; [intros HGa; exact (H1 (HGcG a HGa))|]. split; [exact H2|]. split; [exact H3 | exact H4]. }
  assert (HRV2 : rom_view segs W2 mem2)
    by exact (ajournal_gx_rom_view segs B pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ JC HRO HRV).
  assert (HROM2 : jt_rom W2 mem2) by exact (dcE_jt_kept W W2 mem mem2 HRV HRV2 HROM).
  assert (SVN2 : sv8 W2 mem2 (F + DR_N) (c_n cx - dr_k' cx m)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SVN]. intros x Hx. apply KOUT; unfold DR_N, DR_AT in *; lia. }
  assert (SLK2 : sv8 W2 mem2 (F + 40) (rg_lock fr_RG)).
  { apply (dr_sv8_kept W W2 mem mem2); [|exact SLK]. intros x Hx. apply KOUT; unfold DR_AT in *; lia. }
  assert (SAT2 : sv8 W2 mem2 (F + DR_AT) (if lm_gn mc =? 0 then Z.of_nat (length (bstream (hs_expected h1))) else 0)).
  { replace (0 + Z.of_nat (length (bstream (hs_expected h1)))) with (Z.of_nat (length (bstream (hs_expected h1))))
      in MAT by lia. exact MAT. }
  pose proof (dcE_regs_kept cx t m j si FF regs regsc regs2 KR3 HPR2 DR0) as DR2.
  (* ---- the state at 0x84a78 ---- *)
  exists ly2, S2, E', H'.
  split; [|split; [exact HMO2 | split; [exact ER | split; [exact EV | split; [exact EC |
    split; [exact HNDH | split; [exact HTX | exact HCAPH]]]]]]].
  exists regs2, mem2, md2, (k + k1).
  split; [rewrite Q1; reflexivity|].
  split; [exact DR2|].
  split; [exact HJ2|].
  split.
  { pose proof JC as (_ & _ & (memC & JC0 & _) & _). pose proof JC0 as (_ & HLY2 & _).
    pose proof HLY2 as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr in HFF |- *. rewrite EF. exact HFF. }
  split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HROM2|].
  split; [exact SVN2|]. split; [exact SAT2|]. split; [exact SLK2|].
  split; [exact HMOD2|]. split; [exact HSEP'|]. exact HKY.
Qed.



Lemma dc_calls : forall cx t m j si h fpos ly3 S3 k W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  DLK cx t m j si h fpos ly3 S3 k W c ->
  SRr segs W c (DST A_dr_join cx (t + 1) (lregs_join cx t)).
Proof.
  intros cx t m j si h fpos ly3 S3 k W c HB HD.
  pose proof HD as (regs & mem & md & -> & HJ & HFR & _ & HMOD & HIN & HRV & HROM & HSEP & HLS & HRI & Hatop & Hpick & Hj &
                    Hfdj & Hef0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ht & _).
  pose proof HMOD as (Hlen4 & _ & _ & _ & (_ & _ & Hgn01) & _).
  pose proof Hpick as (_ & Hsi & Hhsi).
  pose proof Hatop as (_ & HO0 & _).
  assert (HST : dc_static cx t m j si h) by exact (conj Hatop (conj Hpick (conj Hj (conj Hfdj (conj Hef0 HRI))))).
  set (FF := frame_addr ly3 1 fpos).
  eapply SRr_bind; [exact (dc_stA cx t m j si h fpos ly3 S3 k W _ HB HD)|]. intros W1 c1 _ H1.
  eapply SRr_bind; [exact (dc_stB cx t m j si h fpos FF ly3 S3 W1 c1 HB HST HLS H1)|].
  intros W2 c2 _ (ly4 & S4 & e' & h' & out' & ev' & LB & H2 & HMO1 & HDF).
  eapply SRr_bind; [exact (dc_stC cx t m j si fpos FF ly4 S4 _ W2 c2 HB H2)|]. intros W3 c3 _ H3.
  set (m1 := dr_m1 m j si h h' e' ev' LB out') in *.
  pose proof HDF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 &
                     D19 & D20 & D21 & D22 & D23 & D24).
  assert (Hh1 : nth si (lm_hs m1) None = Some h').
  { unfold m1, dr_m1, dr_step. cbn [lm_hs]. apply set_nth_same. lia. }
  eapply SRr_bind; [exact (dc_stD cx t m j si fpos FF ly4 S4 m1 h' W3 c3 HB Hsi Hh1 D14 H3)|]. intros W4 c4 _ H4.
  destruct (RI_src cx t m si h HRI Hpick) as (Hexp0 & _ & _).
  destruct (LS_cnl_pre cx t m ly3 S3 ly4 S4 si h j h' HLS HRI Hpick Hj Hfdj Hef0 HMO1 D22 D17 D18)
    as (N1 & N2 & N3 & N4 & N5 & N6).
  (* the stream after the drain is the expected lines' bytes, when the controller is there *)
  assert (HBS : bstream (hs_expected h') = LB) by (rewrite Hexp0 in D17; exact (dc_bstream_LB _ _ LB D17 D21)).
  destruct (RI_gone cx t m HRI) as (G0 & G1).
  assert (HOB : lm_gn m1 = 0 -> exists rest, lm_O m1 = bstream (hs_expected h') ++ rest).
  { intros Hg. exists []. rewrite app_nil_r, HBS. cbn [m1 dr_m1 dr_step lm_gn lm_O] in Hg |- *. unfold dr_O1.
    rewrite HO0. cbn [app]. destruct (G0 Hg) as (C3 & C0 & D0).
    unfold dr_live, sl_live, send_line_c.send_live, send_line_c.send_off. rewrite C3, C0, D0. cbn.
    destruct (Z.eqb_spec (dr_tot h) 0) as [Ht0 | Ht0]; cbn; [|reflexivity].
    pose proof (dc_LB_len LB _ D21) as HL. unfold dr_tot in Ht0. rewrite Ht0 in HL.
    destruct LB; [reflexivity | cbn [length] in HL; lia]. }
  eapply SRr_bind; [exact (dc_stE cx t m j si fpos FF ly4 S4 m1 h' W4 c4 HB Hsi Hh1 N1 N2 N3 N4 N5 N6 HOB H4)|].
  intros W5 c5 _ (ly6 & S6 & E' & H' & H5 & HMO2 & HCF).
  set (m2 := dc_setsrc m1 si (set_exp_held h' E' H')) in *.
  (* the at cell: |bstream| when the controller is there, 0 else; g_nout: |O1| *)
  assert (HA : (if lm_gn m1 =? 0 then Z.of_nat (length (bstream (hs_expected h'))) else 0) = Z.of_nat (length (lm_O m2))).
  { cbn [m2 dc_setsrc m1 dr_m1 dr_step lm_gn lm_O]. unfold dr_O1. rewrite HO0. cbn [app].
    destruct Hgn01 as [Hg | Hg]; rewrite Hg; cbn [Z.eqb].
    - destruct (HOB ltac:(cbn [m1 dr_m1 dr_step lm_gn]; exact Hg)) as (rest & Hr).
      cbn [m1 dr_m1 dr_step lm_O] in Hr. unfold dr_O1 in Hr. rewrite HO0 in Hr. cbn [app] in Hr.
      rewrite HBS. destruct (dr_live (lm_c m) h); [reflexivity|].
      rewrite HBS in Hr. destruct LB; [reflexivity | cbn in Hr; discriminate].
    - assert (Hlv : dr_live (lm_c m) h = false).
      { destruct (G1 Hg) as [C | [C | C]]; unfold dr_live, sl_live, send_line_c.send_live, send_line_c.send_off;
          rewrite C; cbn; [reflexivity | rewrite orb_true_r; reflexivity | rewrite andb_false_r; reflexivity]. }
      rewrite Hlv. reflexivity. }
  rewrite HA in H5.
  assert (Hfin : forall ev, dc_fin cx m m2 ev =
    dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' (dr_ctl (lm_c m) h ev) (dr_O1 m h LB) (dr_cap1 m j h) out').
  { intros ev. unfold dc_fin, m2, dc_setsrc, m1, dr_m1, dr_step. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    rewrite dc_set_nth_twice, dc_ctl_dr. reflexivity. }
  apply (dc_stF cx t m j si fpos FF ly6 S6 m2 W5 c5 HB Hatop).
  - intros ev. rewrite Hfin.
    apply (RI_drain_step cx t m si h j e' h' (dr_ctl (lm_c m) h ev) (dr_O1 m h LB) (dr_cap1 m j h) out' ev LB E' H'
             HRI Ht N3 Hatop Hpick Hj Hfdj Hef0).
    unfold dr_step_ok. cbv zeta.
    destruct HCF as (F1 & F2 & F3 & F4 & F5 & F6).
    repeat (split; [first [assumption | reflexivity]|]). first [assumption | reflexivity].
  - intros ev. rewrite Hfin.
    exact (LS_drain_step cx t m ly3 S3 S4 ly6 S6 si h j (set_exp_held h' E' H') e' (dr_ctl (lm_c m) h ev)
             (dr_O1 m h LB) (dr_cap1 m j h) out' (hs_expected h') (hs_held h') HLS Hpick Hj HMO1 HMO2).
  - exact H5.
Qed.

(* (5) 0x84a20-0x84a7c: the eof test and, when the relay still reads the source, the six calls. *)

Lemma dr_found_join : forall cx t j W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  DST A_dr_found cx t (lregs_found cx t j) W c ->
  SRr segs W c (DST A_dr_join cx (t + 1) (lregs_join cx t)).
Proof.
  intros cx t j W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR)).
  destruct HR as (((R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R25 & R26 & R3 & R4) & R27 & Ht)
    & Hatop & R28 & SVN & (si & h & Hpick & R21 & Hfdj & Hnom) & Hj & R10 & R22).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dr_ceil_lo as HCL.
  assert (HAR : AR segs B ly3 S3 W mem md) by (eapply ajournal_gx_AR; exact HJ).
  pose proof HMOD as (Hlen4 & HSL & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDr & HTUP & HLST & HLSTW).
  pose proof HREL as (Msrc & Wsrc & Mnsrc & Wnsrc & Mcap & Wcap & Hle16 & HGin & (tl & HTAB) & HENT & HNDF & _).
  destruct (dr_pads_of_relay ly3 S3 W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS).
  remember (nth j (lm_es m) dr_e0) as e eqn:Hedef.
  assert (HEOK : aentry_ok B ly3 S3 W mem e) by (rewrite Hedef; rewrite Forall_forall in HENT; apply HENT, nth_In; exact Hj).
  pose proof HEOK as (Heof01 & _).
  pose proof (dr_tbl_eof W mem (lm_G m) (lm_es m) tl j HTAB HPAD Hj ltac:(rewrite <- Hedef; lia)) as Mef.
  rewrite <- Hedef in Mef.

  pose proof HB as (HAI & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  assert (Hn26 : c_n cx < 2 ^ 26) by (destruct Hnrng as [(Hz & _) | (Hz & _)]; lia).
  pose proof HFNP as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold LLVMF_STK in Hslo.
  assert (HFb : spZ (c_regs cx) - 352 < lf_F cx <= spZ (c_regs cx) - 320).
  { unfold lf_F. pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)). lia. }
  assert (HF32 : lf_F cx mod 32 = 0).
  { unfold lf_F. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
  pose proof (pal_env B TL) as ((HE0 & HE1) & _).
  assert (Hfin : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJ0 & _) & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs, Hown. left. reflexivity. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hfin) as (HFF1 & HFF2 & _).
  replace (fs_frame_bytes 1) with 128 in HFF2 by reflexivity.
  set (FF := frame_addr ly3 1 fpos) in *.
  pose proof HFR as (_ & HAWR & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W mem md (lm_G m) ATABLE HAR HGin) as (HG16 & HG4096 & HGceil & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity. rewrite RQ in HGceil.
  assert (Hj16 : Z.of_nat j < 16) by lia.
  assert (HSA8 : (lm_G m + AENT * Z.of_nat j) mod 8 = 0).
  { unfold AENT. pose proof (Z.div_mod (lm_G m) 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D.
    rewrite D. replace (16 * (lm_G m / 16) + 56 * Z.of_nat j) with ((2 * (lm_G m / 16) + 7 * Z.of_nat j) * 8) by ring.
    apply Z_mod_mult. }
  destruct (dc_found_entry ly3 S3 W mem md regs (lf_F cx) (lm_G m) j (re_eof e) HAR R9 R10 R22 R26)
    as [HS SHOK].
  { unfold DR_CEIL8 in *. lia. }
  { lia. }
  { exact HF32. }
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply HAWR. lia. }
  { intros a Ha. replace a with (lf_F cx + (a - lf_F cx)) by lia. apply HAWR. lia. }
  { exact HGin. }
  { unfold AENT; lia. }
  { exact HSA8. }
  { unfold AENT, DR_CEIL8 in *; lia. }
  { unfold AENT; lia. }
  { unfold AENT, ATABLE; lia. }
  { exact Mef. }
  { lia. }

  remember (Eimg (Ereg regs (dc_extra (re_eof e)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (dc_extra (re_eof e))) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
    by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
  assert (E9 : ew E 9 = Z_to_bv 64 (lf_F cx)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
  assert (E32 : ew E 32 = Z_to_bv 64 (re_eof e))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx) by (rewrite E9; apply unsigned_lit_small; unfold DR_CEIL8 in *; lia).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_found)) with (Z_to_bv 64 (BASE + A_dr_found)).
  paj_run_tok RUN HS HJ SHOK DRspan.
  { unfold ss_dc_found, dc_rA, dc_rL, dc_rE. cbn [ss_mem].
    repeat (apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U9 in Ha;
        first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
      | ]).
    apply awr_ok_x_nil. }
  rename HFr into HFr1, HG0 into HG1. clear HF.
  psrr_branch_tok RUN de_BR HS SHOK DRspan.

  - (* 0x84a40 bnez a0 taken: the relay's entry is at end of file, the operation is a no-op - to 0x84a80 *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e) by (apply U_atom; [rewrite !ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    assert (Hef1 : re_eof e = 1) by lia.
    paj_run_to_tok RUNTO HS HJ SHOK DRspan A_dr_join.
    { unfold dc_rA, dc_rL, dc_rE. cbn [ss_mem add_cond].
      repeat (apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
          first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
        | ]).
      apply awr_ok_x_nil. }

    assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
      by (pose proof Hatop as (Hk0 & _ & _); unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
    { intros a Ha (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
      intros (r & Hin & Hr). cbn [ss_mem ss_dc_found In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val dc_rA dc_rL dc_rE] in Hr; rewrite ?U9 in Hr; unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hno. rewrite <- (K1 a Ha Hno). destruct Hno as (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr;
          unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG0 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (dc_carry cx W mem (ms_mem ms0) md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact SVN].
      intros x Hx. apply KEEP; [unfold DR_N, DR_CEIL8 in *; lia | unfold dc_out, DR_N, DR_AT in *; lia]. }
    assert (HFL2 : sv8 W (ms_mem ms0) (FF + 120) (flag_addr ly3 1 fpos)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact HFL].
      intros x Hx. apply KEEP; [unfold DR_CEIL8 in *; lia | unfold dc_out, DR_AT in *; lia]. }
    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + dr_k' cx m)) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28).
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (dc_extra (re_eof e))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DR_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (25%bv : bv 5) Q25. rewrite ?ew_ewset_other in Q25 by lia. rewrite E28 in Q25.
    pmkst HS.
    apply SRr_ret.
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|]. split; [exact HROM2|].
    exists own, ly3, S3, k, (dr_skip m (dr_k' cx m)), fpos.
    split; [exact HJ|]. split; [exact Hown|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|].
    split; [exact HIN2|]. split; [exact HRV2|]. split; [exact HSEP|].
    split; [apply LS_drain_skip; exact HLS|].
    split; [apply (RI_drain_skip cx t m si h HRI Hatop Hpick); right; exists j;
            split; [exact Hj|]; rewrite <- Hedef; split; [exact Hfdj | exact Hef1]|].
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite Q25; reflexivity|].
    split; [exact SVN2|]. exact Hk'.

  - (* 0x84a40 bnez a0 not taken: the relay still reads the source - the six calls *)
    lazymatch type of Hc with branch_taken _ (sv_denot ?Ev _) _ = _ =>
      assert (U32 : U Ev (SOff 32 0) = re_eof e) by (apply U_atom; [rewrite !ew_ewset_other by lia; exact E32 | lia]) end.
    rewrite branch_ne_U, U32, U_lit in Hc by lia. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    rename Hc into Hef0.
    (* 0x84a44-0x84a50: a0 = &g_lock, sd a0,40(s1), jal pthread_mutex_lock *)
    paj_run_tok RUN HS HJ SHOK DRspan.
    { unfold dc_rA, dc_rL, dc_rE. cbn [ss_mem add_cond].
      repeat (apply awr_ok_x_cons;
        [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
          first [ lia | left; split; [left; unfold LLVMF_STK; lia | lia] ]
        | ]).
      apply awr_ok_x_nil. }

    rename HFr into HFr2, HG0 into HG2. clear HF.
    assert (Hk' : 0 <= dr_k' cx m <= c_n cx)
      by (pose proof Hatop as (Hk0 & _ & _); unfold dr_k'; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
    { intros a Ha (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr1 a Ha).
      intros (r & Hin & Hr). cbn [ss_mem ss_dc_found In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val dc_rA dc_rL dc_rE] in Hr; rewrite ?U9 in Hr; unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
    { intros a Ha Hno. rewrite <- (K1 a Ha Hno). destruct Hno as (Hn1 & Hn2). apply (aview_kept_out _ _ _ _ _ HFr2 a Ha).
      intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin.
      repeat (destruct Hin as [<- | Hin];
        [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr;
          unfold DR_AT in Hn2; lia | ]).
      destruct Hin. }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
    { intros a Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [|exact Hw].
      intros Hp. exact (de_pres_grows W _ _ a HG2 (de_pres_grows W _ _ a HG1 Hp)). }
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> dc_out cx a -> abyte_kept W mem W (ms_mem ms0) a)
      by (intros a Ha Hna; split; [exact (K2 a Ha Hna) | apply WK]).
    destruct (dc_carry cx W mem (ms_mem ms0) md ly3 S3 fpos m HAR Hfin (eq_sym Hnlen) ltac:(lia)
                HFR HMOD HIN HRV HROM KEEP WK) as (HFR2 & HMOD2 & HIN2 & HRV2 & HROM2).
    assert (SVN2 : sv8 W (ms_mem ms0) (lf_F cx + DR_N) (c_n cx - dr_k' cx m)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact SVN].
      intros x Hx. apply KEEP; [unfold DR_N, DR_CEIL8 in *; lia | unfold dc_out, DR_N, DR_AT in *; lia]. }
    assert (HFL2 : sv8 W (ms_mem ms0) (FF + 120) (flag_addr ly3 1 fpos)).
    { apply (dr_sv8_kept W W mem (ms_mem ms0)); [|exact HFL].
      intros x Hx. apply KEEP; [unfold DR_CEIL8 in *; lia | unfold dc_out, DR_AT in *; lia]. }
    pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
    pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.

    assert (S192 : sv8 W (ms_mem ms0) (lf_F cx + DR_AT) 0).
    { unfold sv8, DR_AT.
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 192 8%N (SLit 0) 0 RG0) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - reflexivity.
      - lia.
      - lia. }
    assert (VLK : rg_lock fr_RG = 0x5d8ac0) by reflexivity.
    assert (E247 : ew E 247 = Z_to_bv 64 (rg_lock fr_RG)).
    { change 247%nat with (A_OBJ 6). apply bv_eq. rewrite (HEI (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
      rewrite unsigned_lit_small by (rewrite VLK; lia). vm_compute. reflexivity. }
    assert (S40 : sv8 W (ms_mem ms0) (lf_F cx + 40) (rg_lock fr_RG)).
    { unfold sv8.
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 40 8%N (SOff 247 0) (rg_lock fr_RG) RG1) end.
      - rewrite !ew_ewset_other by lia. exact U9.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite !ew_ewset_other by lia. rewrite E247, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - rewrite VLK; lia.
      - lia. }

    assert (E28 : ew E 28 = Z_to_bv 64 (c_p cx + dr_k' cx m)) by (rewrite (EEo 28%nat 28%bv eq_refl); exact R28).
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HAE2 : env_agree 32 (Ereg regs (dc_extra (re_eof e))) Ev)
        by (split; [intros q Hq; rewrite !ew_ewset_other by lia; exact (proj1 HAE q Hq)
                   | rewrite !ed_ewset; exact (proj2 HAE)]) end.
    pose proof (regs_kept_of_st_ok segs _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%bv
                  HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (25%bv : bv 5) Q25.
    rewrite ?ew_ewset_other in Q10, Q25 by lia. rewrite E247 in Q10. rewrite E28 in Q25.
    pmkst HS. subst own.
    apply (dc_calls cx t m j si h fpos ly3 S3 k W _ HB).
    lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
    split; [reflexivity|].
    split; [exact HJ|]. split; [exact HFR2|]. split; [exact HFL2|]. split; [exact HMOD2|]. split; [exact HIN2|].
    split; [exact HRV2|]. split; [exact HROM2|]. split; [exact HSEP|]. split; [exact HLS|]. split; [exact HRI|].
    split; [exact Hatop|]. split; [exact Hpick|]. split; [exact Hj|].
    rewrite <- Hedef. split; [exact Hfdj|]. split; [exact Hef0|].
    split; [exact SVN2|]. split; [exact S192|]. split; [exact S40|].
    split; [exact Q1|]. split; [exact Q10|].
    split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    split; [rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [exact Ht|].
    split; [rewrite (KR 21%bv ltac:(cbv; tauto)); exact R21|].
    split; [rewrite (KR 22%bv ltac:(cbv; tauto)); exact R22|].
    exact Q25.
Qed.

(* (6) 0x84a80-0x84b2c: s6 takes the new in.p, s9 is restored from F+104, and the arm reaches the latch. *)
Lemma dr_jn_entry : forall (W : world segs) regs mem F,
  getr regs 9 = w64 F -> getr regs 26 = w64 SB ->
  0 <= F -> F + 112 <= 2 ^ 64 -> sv8 W mem (F + 104) HI_G_NOUT ->
  st_ok_pi segs VAL (Eimg (Ereg regs [])) ss_dr_jn
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_dr_join)) mem (seg_rom segs)))
  /\ sh_ok segs drBx [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F R9 R26 HF0 HF1 M104.
  rewrite restrict_mkst_fx.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (E26 : ew E 26 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
  split.
  - unfold ss_dr_jn. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|constructor]. unfold region_ok, dr_jn_rF.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E9, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|constructor].
      apply (chunk_ok_val segs E _ F 104 8 (SLit HI_G_NOUT) HI_G_NOUT);
        [reflexivity | unfold HI_G_NOUT; zside | zside |].
      exact M104.
    + cbn [pairwise_disjoint all_disjoint]. repeat split.
    + split; [|split; [exact I | exact I]].
      cbn [dr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E26, unsigned_lit_small by (unfold SB; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
Lemma dr_join_latch : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  DST A_dr_join cx (t + 1) (lregs_join cx t) W c ->
  SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t W c HB (regs & mem & md & -> & HROM &
    (own & ly3 & S3 & k & m & fpos & HJ & -> & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR)).
  destruct HR as (R2 & R8 & R9 & R18 & R19 & R20 & R23 & R24 & R26 & R3 & R4 & R27 & Ht & R25 & SVN & Hk).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HB as (HAI & HPRE & _).
  pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as HFm.
  assert (HFb : spZ (c_regs cx) - 352 <= lf_F cx <= spZ (c_regs cx) - 320) by (unfold lf_F; lia).
  unfold LLVMF_STK in *.
  pose proof HFR as (FS & FW & F24 & F48 & F56 & F64 & F72 & F80 & F88 & F96 & F184 & Ffull & _).
  destruct (Ffull eq_refl) as (F32 & F104 & F112 & F120 & F128 & F136 & F152).
  destruct (dr_jn_entry W regs mem (lf_F cx) R9 R26 ltac:(lia) ltac:(lia) F104) as [HS SHOK].
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (E25 : ew E 25 = Z_to_bv 64 (c_p cx + lm_k m))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
        rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + A_dr_join)) with (Z_to_bv 64 (BASE + A_dr_join)).
  (* mv s6,s9 ; j 0x84b28 ; ld s9,104(s1) ; j 0x84490 *)
  paj_run_to_tok RUNTO HS HJ SHOK DRspan AF_LLVM_latch.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  dr_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DR_KEPT HS HAE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (22%bv : bv 5) Q22. rewrite E25 in Q22.
  prreg HS (25%bv : bv 5) Q25.
  pmkst HS. rewrite Em in *.
  apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst ?r _ ?mm _) ?d] => exists r, mm, d end.
  split; [reflexivity|]. split; [exact HROM|].
  exists [(1, fpos)], ly3, S3, k, m, fpos.
  split; [exact HJ|]. split; [reflexivity|]. split; [exact HFR|]. split; [exact HFL|]. split; [exact HMOD|].
  split; [exact HIN|]. split; [exact HRV|]. split; [exact HSEP|]. split; [exact HLS|].
  split; [exact HRI|].
  split.
  { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite (KR 18%bv ltac:(cbv; tauto)); exact R18|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite (KR 20%bv ltac:(cbv; tauto)); exact R20|].
    split; [rewrite (KR 23%bv ltac:(cbv; tauto)); exact R23|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite Q25; reflexivity|].
    split; [rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
  split; [exact Ht|].
  split; [rewrite Q22; reflexivity|].
  split; [exact SVN|]. exact Hk.
Qed.

(* ------------------------------------------------------------------ the arm *)
Theorem lf_arm_drain : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  INV_A B G_fr fr_FP LS RINV 2 cx t W c -> SRr segs W c (INV_K B G_fr fr_FP LS RINV cx t).
Proof.
  intros cx t W c HB HA.
  eapply SRr_bind; [exact (dr_entry cx t W c HB HA)|].
  intros W1 c1 _ [(n & HL) | HN].
  - eapply SRr_bind; [exact (dr_scan n cx t 0 W1 c1 HB HL)|].
    intros W2 c2 _ [(j & HF) | HN].
    + eapply SRr_bind; [exact (dr_found_join cx t j W2 c2 HB HF)|].
      intros W3 c3 _ HJ. exact (dr_join_latch cx t W3 c3 HB HJ).
    + eapply SRr_bind; [exact (dr_nf_join cx t W2 c2 HB HN)|].
      intros W3 c3 _ HJ. exact (dr_join_latch cx t W3 c3 HB HJ).
  - eapply SRr_bind; [exact (dr_nf_join cx t W1 c1 HB HN)|].
    intros W3 c3 _ HJ. exact (dr_join_latch cx t W3 c3 HB HJ).
Qed.
End dr.
