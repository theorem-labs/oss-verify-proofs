(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 12453 of its 12546 lines of code are new or changed and 1136 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/drain_b.v, with its module paths, module names, addresses and numbers changed; 2024 of its 2247 lines of code are new or changed and 12323 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04 YO10 YK14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import gestures_end_seg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma vm_twice : forall v1 v2 md, with_vmmaps v2 (with_vmmaps v1 md) = with_vmmaps v2 md.
Proof. intros v1 v2 md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma vm_self : forall md, md = with_vmmaps (m_vmmaps md) md.
Proof. intros md. destruct md as [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma ub_nonneg : forall s p n, WF s -> In (p, n) (user_blocks s) -> 0 <= n.
Proof.
  intros s p n HW Hin.
  destruct (YO10.in_user_blocks_inv s (p, n) Hin) as (g & am & i & fr & Hg & Hi & Hfr & _ & E).
  apply (YO10.used_metas_usedX s g am HW) in Hg.
  destruct (YO10.block_in_slot s g am i fr HW Hg Hi Hfr) as (_ & _ & H).
  injection E as _ ->. exact H.
Qed.

Lemma blocks_In2 : forall L A a n, In (a, n) (blocks L A) <-> exists p, ptr_addr L p = a /\ In (p, n) (user_blocks A).
Proof.
  intros L A a n. unfold blocks. rewrite in_map_iff. split.
  - intros ([p k] & H & Hin). cbn in H. injection H as <- <-. exists p. auto.
  - intros (p & <- & Hin). exists (p, n). auto.
Qed.

Lemma nodup_fst : forall {X Y} (l : list (X * Y)) x a b, NoDup (map fst l) -> In (x, a) l -> In (x, b) l -> a = b.
Proof.
  intros X Y l x a b ND. apply NoDup_ListNoDup in ND. revert x a b ND.
  induction l as [|[y c] l IH]; intros x a b ND Ha Hb; [destruct Ha|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND as [Hn ND].
  destruct Ha as [Ea|Ha], Hb as [Eb|Hb].
  - congruence.
  - injection Ea as E1 E2. subst. exfalso. apply Hn. exact (in_map fst _ _ Hb).
  - injection Eb as E1 E2. subst. exfalso. apply Hn. exact (in_map fst _ _ Ha).
  - exact (IH x a b ND Ha Hb).
Qed.

Lemma nodup_fst_eq : forall {X Y} (l : list (X * Y)) x a y b, NoDup (map fst l) -> In (x, a) l -> In (y, b) l ->
  x = y -> a = b.
Proof. intros X Y l x a y b ND Ha Hb ->. exact (nodup_fst l y a b ND Ha Hb). Qed.

Lemma bytes_at_transfer2 : forall segs m m' a bs, bytes_at segs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (a + i) = mbyte segs m (a + i)) ->
  bytes_at segs m' a bs.
Proof.
  intros segs m m' a bs (H1 & H2 & H) E. split; [exact H1|]. split; [exact H2|].
  intros i Hi. change (mbyte segs m' (a + Z.of_nat i) = nth_error bs i).
  rewrite E by lia. exact (H i Hi).
Qed.

Lemma rw_cells_transfer2 : forall segs m m' a cs, rw_cells segs m a cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte segs m' (a + i) = mbyte segs m (a + i) /\
     (writable_at segs m (a + i) -> writable_at segs m' (a + i))) ->
  rw_cells segs m' a cs.
Proof.
  intros segs m m' a cs [[Hwf Hb] (Ha & Hn & Hw)] E.
  pose proof (cells_bytes_length cs Hwf) as L.
  split; [split; [exact Hwf|]|].
  - apply (bytes_at_transfer2 segs m); [exact Hb|]. intros i Hi. apply E. rewrite <- L. exact Hi.
  - split; [exact Ha|]. split; [exact Hn|]. intros i Hi. apply (proj2 (E i Hi)). exact (Hw i Hi).
Qed.

Lemma present_writable2 : forall segs m a, present m a -> writable_at segs m a.
Proof. intros segs m a [b E]. unfold writable_at, wview. rewrite E. discriminate. Qed.

Lemma present_mbyte : forall segs m a, present m a -> exists b, mbyte segs m a = Some b.
Proof. intros segs m a [b E]. exists b. unfold mbyte. rewrite E. reflexivity. Qed.

Lemma bytes_of_mbytes : forall segs m a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> exists b, mbyte segs m (a + i) = Some b) ->
  exists bs, length bs = n /\ bytes_at segs m a bs.
Proof.
  intros segs m a n. revert a. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [reflexivity|]. split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (H 0 ltac:(lia)) as [b Eb]. rewrite Z.add_0_r in Eb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Lb & Hb).
    { intros i Hi. replace (a + 1 + i) with (a + (i + 1)) by lia. apply H. lia. }
    exists (b :: bs). split; [cbn; lia|].
    change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
    + split; [exact Ha|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i as [|i]; [|lia].
      cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Eb.
    + cbn [length Z.of_nat]. exact Hb.
Qed.

Lemma c4_of_bytes : forall segs m A b0 b1 b2 b3,
  bytes_at segs m A [b0; b1; b2; b3] -> wr_at segs m A 4 ->
  rw_cells segs m A [C4 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3]))].
Proof.
  intros segs m A b0 b1 b2 b3 HB HW.
  pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as B1. pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3]) as B0.
  cbn [length Z.of_nat] in B1.
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le4. rewrite unsigned_lit by lia.
    change 4%nat with (length [b0; b1; b2; b3]). rewrite StrFun.Z_to_le_bytes_to_Z. exact HB.
  - cbn [cells_size csize]. exact HW.
Qed.

Lemma find_segment_in2 : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s segs IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  match type of H with context [if ?c then _ else _] => destruct c eqn:E end.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity|]. lia.
  - destruct (IH a n seg H) as (Hi & H1 & H2). split; [right; exact Hi|]. lia.
Qed.

Lemma rsegs_top2 : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 20) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_res_top2 :
  forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 21) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rsegs_wr_rd : forallb (fun s => implb (seg_writable s) (seg_readable s)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma writable_mbyte : forall m a, writable_at rsegs m a -> exists b, mbyte rsegs m a = Some b.
Proof.
  intros m a W. revert W. unfold writable_at, wview, mbyte.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  destruct (find_segment rsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Fs; [|intros W; exfalso; exact (W eq_refl)].
  destruct (seg_writable seg) eqn:Wr; [|intros W; exfalso; exact (W eq_refl)].
  assert (Rd : seg_readable seg = true).
  { pose proof (proj1 (forallb_forall _ rsegs) rsegs_wr_rd seg (proj1 (find_segment_in2 _ _ _ _ Fs))) as H.
    cbv beta in H. rewrite Wr in H. exact H. }
  unfold YK11.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite Fs. cbv beta iota. rewrite Rd.
  cbv beta iota zeta. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes seg) _) as [b|]; [intros _; exists b; reflexivity|].
  intros W. exfalso. exact (W eq_refl).
Qed.

Lemma err_cells : forall m A, 0 <= A -> A + 4 <= 2 ^ 64 ->
  (forall i, 0 <= i < 4 -> writable_at rsegs m (A + i)) -> exists v, rw_cells rsegs m A [C4 v].
Proof.
  intros m A H0 H1 W.
  destruct (bytes_of_mbytes rsegs m A 4 H0 H1) as (bs & Lb & Hb).
  { intros i Hi. apply writable_mbyte. apply W. cbn in Hi. lia. }
  destruct bs as [|b0 [|b1 [|b2 [|b3 [|b4 bs]]]]]; cbn in Lb; try discriminate.
  eexists. apply c4_of_bytes; [exact Hb|].
  split; [exact H0|]. split; [exact H1|]. intros i Hi. exact (W i Hi).
Qed.

Lemma canon_mkst2 : forall {fx : YK11.FPState} regs pc mem rom,
  RegisterBridge.canonical_register_state (YK11.mkst regs pc mem rom) = MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem rom.
Proof. reflexivity. Qed.

Lemma eqv_mkst2 : forall {fx : YK11.FPState} R F pc fc m ro ms, Regs6ss.ms_eqv (MS R F pc fc None m ro) ms ->
  F = fp_regs -> fc = fp_csr ->
  exists R', ms = YK11.mkst R' pc m ro /\ Regs6ss.xregs_eqv R R'.
Proof.
  intros fx R F pc fc m ro [r f p sv rv c mm o] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) -> ->.
  cbn in *. subst. exists r. split; [reflexivity | exact H1].
Qed.

Lemma getr_mkR2 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 R,
  Regs6ss.xregs_eqv (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31) R -> forall n, (0 < n < 32)%nat ->
  getr R (Z_to_bv 5 (Z.of_nat n)) = nth n [Z_to_bv 64 0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14;
    x15; x16; x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31] (Z_to_bv 64 0).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 R H n Hn.
  assert (NZ : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. change (bv_unsigned 0) with 0. lia. }
  unfold getr. rewrite NZ. rewrite <- (H _ NZ).
  do 32 (destruct n as [|n]; [try lia; reflexivity|]). lia.
Qed.

Lemma mkR_of_getr : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. reflexivity. Qed.

Lemma getr_of_eqv2 : forall M R (r : bv 5), Regs6ss.xregs_eqv M R -> bv_eqb r 0 = false -> getr R r = reg_get M r.
Proof. intros M R r H NZ. unfold getr. rewrite NZ. symmetry. apply H. exact NZ. Qed.

Lemma ret_pc_of_ok2 : forall k, YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H. unfold YK0s.ret_ok, YK14.v_jalr, YK11.jalr_tgtZ in H. rewrite Z.add_0_r in H.
  pose proof (bv_unsigned_in_range 64 k) as R. unfold bv_modulus in R.
  assert (T : Z.testbit (bv_unsigned k) 0 = false).
  { rewrite <- H at 1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite Z.mod_pow2_bits_low by lia. rewrite Z.land_spec. apply Bool.andb_false_r. }
  assert (E : bv_unsigned k mod 2 = 0) by (rewrite Zmod_odd, <- Z.bit0_odd, T; reflexivity).
  rewrite <- (Z_to_bv_bv_unsigned k). apply ret_pc_even; [exact R | exact E].
Qed.

Lemma ret_ok_13268 : YK0s.ret_ok (Z_to_bv 64 0x13268).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ret_ok_1329c : YK0s.ret_ok (Z_to_bv 64 0x1329c).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma ret_ok_132b4 : YK0s.ret_ok (Z_to_bv 64 0x132b4).
Proof. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Definition klen (k : Z * list byte * list byte) : Z := Z.of_nat (length (key_text k)).

Lemma keys_total_app : forall k1 k2, keys_total (k1 ++ k2) = keys_total k1 + keys_total k2.
Proof. intros k1 k2. unfold keys_total. induction k1 as [|k k1 IH]; cbn [app fold_right]; lia. Qed.

Lemma keys_total_cons : forall k ks, keys_total (k :: ks) = klen k + 5 + keys_total ks.
Proof. reflexivity. Qed.

Lemma keys_total_nonneg : forall ks, 0 <= keys_total ks.
Proof. intros ks. unfold keys_total. induction ks as [|k ks IH]; cbn [fold_right]; lia. Qed.

Lemma keys_total_pos : forall ks, ks <> [] -> 0 < keys_total ks.
Proof.
  intros [|k ks] H; [congruence|]. rewrite keys_total_cons. pose proof (keys_total_nonneg ks).
  unfold klen. lia.
Qed.

Lemma keys_out_app : forall k1 k2, keys_out (k1 ++ k2) = keys_out k1 ++ keys_out k2.
Proof. intros k1 k2. unfold keys_out. rewrite map_app, concat_app. reflexivity. Qed.

Lemma keys_out_one : forall k, keys_out [k] = key_text k ++ END5.
Proof. intros k. unfold keys_out. cbn [map concat]. apply app_nil_r. Qed.

Lemma key_ptrs_app : forall k1 k2, key_ptrs (k1 ++ k2) = key_ptrs k1 ++ key_ptrs k2.
Proof. intros k1 k2. unfold key_ptrs. rewrite map_app, concat_app. reflexivity. Qed.

Lemma key_ptrs_cons : forall k ks, key_ptrs (k :: ks) = le8 (Z_to_bv 64 (key_addr k)) ++ key_ptrs ks.
Proof. reflexivity. Qed.

Lemma key_ptrs_length : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|]. rewrite key_ptrs_cons, length_app, length_le8, IH. cbn [length]. lia.
Qed.

Lemma key_slice : forall segs m HP ks1 k ks2, bytes_at segs m HP (key_ptrs (ks1 ++ k :: ks2)) ->
  ov_read_bytes segs m (Z_to_bv 64 (HP + 8 * Z.of_nat (length ks1))) 8 = Some (le8 (Z_to_bv 64 (key_addr k))).
Proof.
  intros segs m HP ks1 k ks2 H. rewrite key_ptrs_app, key_ptrs_cons in H.
  pose proof (bytes_at_ov_read segs m HP _ (length (key_ptrs ks1)) 8 H) as R.
  rewrite skipn_app_exact in R.
  rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in R by (rewrite length_le8; lia).
  rewrite key_ptrs_length, Nat2Z.inj_mul in R. change (Z.of_nat 8) with 8 in R. unfold wa in R. rewrite R; [reflexivity|].
  rewrite !length_app, length_le8, !key_ptrs_length. lia.
Qed.

Lemma off_nz2 : forall cl br X, X <> 0 -> send_off cl br X = (cl <? 0) || (br =? 1).
Proof. intros cl br X H. unfold send_off. rewrite (proj2 (Z.eqb_neq X 0) H). apply orb_false_r. Qed.

Lemma live_nz3 : forall cl br dd X, X <> 0 -> send_live cl br dd X = negb ((cl <? 0) || (br =? 1)) && (dd =? 0).
Proof. intros cl br dd X H. unfold send_live. rewrite off_nz2 by exact H. reflexivity. Qed.

Lemma live_step2 : forall cl br dd T LEN X, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  LEN <> 0 -> X <> 0 ->
  send_live cl (if send_off cl br T then br else dd) dd LEN = send_live cl br dd X.
Proof.
  intros cl br dd T LEN X Hcl Hbr Hdd HL HX. rewrite !live_nz3 by assumption. unfold send_off.
  destruct (T =? 0); destruct Hcl as [-> | ->]; destruct Hbr as [-> | ->]; destruct Hdd as [-> | ->]; reflexivity.
Qed.

Lemma br_step2 : forall cl br dd T LEN, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  LEN <> 0 -> T + LEN <> 0 ->
  (if send_off cl (if send_off cl br T then br else dd) LEN then (if send_off cl br T then br else dd) else dd) =
  (if send_off cl br (T + LEN) then br else dd).
Proof.
  intros cl br dd T LEN Hcl Hbr Hdd HL HX. rewrite (off_nz2 _ _ LEN HL), (off_nz2 _ _ (T + LEN) HX). unfold send_off.
  destruct (T =? 0); destruct Hcl as [-> | ->]; destruct Hbr as [-> | ->]; destruct Hdd as [-> | ->]; reflexivity.
Qed.

Lemma ei_step2 : forall cl br dd ei T LEN, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  LEN <> 0 -> T + LEN <> 0 ->
  (if send_off cl (if send_off cl br T then br else dd) LEN then (if send_off cl br T then ei else 0) else 0) =
  (if send_off cl br (T + LEN) then ei else 0).
Proof.
  intros cl br dd ei T LEN Hcl Hbr Hdd HL HX. rewrite (off_nz2 _ _ LEN HL), (off_nz2 _ _ (T + LEN) HX). unfold send_off.
  destruct (T =? 0); destruct Hcl as [-> | ->]; destruct Hbr as [-> | ->]; destruct Hdd as [-> | ->]; reflexivity.
Qed.

Lemma rm_in : forall (l b1 b2 : list (Z * Z)) x y, NoDup (map fst l) -> l = b1 ++ x :: b2 ->
  (In y (b1 ++ b2) <-> In y l /\ fst y <> fst x).
Proof.
  intros l b1 b2 x y ND E. subst l. apply NoDup_ListNoDup in ND. rewrite map_app in ND. cbn [map] in ND.
  apply List.NoDup_remove_2 in ND. split.
  - intros H. split.
    + apply in_app_or in H. apply in_or_app. destruct H as [H|H]; [left; exact H | right; right; exact H].
    + intros Ef. apply ND. rewrite <- Ef, <- map_app. apply in_map. exact H.
  - intros [H Hf]. apply in_app_or in H. apply in_or_app. destruct H as [H|[H|H]].
    + left. exact H.
    + exfalso. apply Hf. rewrite H. reflexivity.
    + right. exact H.
Qed.

Lemma in_mid_iff : forall {T} (c1 c2 : list T) x y, In y (c1 ++ x :: c2) <-> In y (c1 ++ c2) \/ x = y.
Proof. intros T c1 c2 x y. rewrite !in_app_iff. cbn [In]. tauto. Qed.

Lemma nodup_split : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND H2 H1; [destruct H1|].
  cbn [app] in ND. apply List.NoDup_cons_iff in ND as [Hy ND].
  destruct H1 as [E|H1]; [subst y; apply Hy; apply in_or_app; right; exact H2 | exact (IH l2 x ND H2 H1)].
Qed.

Lemma frame32 : forall m a, 0 <= a -> a + 32 <= 2 ^ 64 -> (forall i, 0 <= i < 32 -> writable_at rsegs m (a + i)) ->
  exists j0 j1 j2 j3, length j0 = 8%nat /\ length j1 = 8%nat /\ length j2 = 8%nat /\ length j3 = 8%nat /\
    rw_cells rsegs m a [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3].
Proof.
  intros m a H0 H1 W.
  assert (G : forall c, 0 <= c -> c + 8 <= 32 -> exists j, length j = 8%nat /\ bytes_at rsegs m (a + c) j).
  { intros c Hc1 Hc2. apply (bytes_of_mbytes rsegs m (a + c) 8); [lia | lia |].
    intros i Hi. apply writable_mbyte. replace (a + c + i) with (a + (c + i)) by lia. apply W. lia. }
  destruct (G 0 ltac:(lia) ltac:(lia)) as (j0 & L0 & B0). rewrite Z.add_0_r in B0.
  destruct (G 8 ltac:(lia) ltac:(lia)) as (j1 & L1 & B1).
  destruct (G 16 ltac:(lia) ltac:(lia)) as (j2 & L2 & B2).
  destruct (G 24 ltac:(lia) ltac:(lia)) as (j3 & L3 & B3).
  exists j0, j1, j2, j3. split; [exact L0|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|].
  split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_app. split; [exact B0|]. rewrite L0.
    apply bytes_at_app. split; [replace (a + Z.of_nat 8) with (a + 8) by lia; exact B1|]. rewrite L1.
    apply bytes_at_app. split; [replace (a + Z.of_nat 8 + Z.of_nat 8) with (a + 16) by lia; exact B2|]. rewrite L2.
    replace (a + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (a + 24) by lia. exact B3.
  - split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. exact (W i ltac:(lia)).
Qed.

(* Lane p3b helpers: a callee's pack3 trace run inside its caller's numbering. A trace function at base j + k with
   the buffer at o runs, in the caller's address list qs, as the same function at base k with the buffer at o' in
   the callee's list qc, when qs holds qc's addresses from index j and o resolves as o' does. *)
Abbreviation p3b_rn F qs b j t := (run_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) qs b j t).
Abbreviation p3b_rm F qs b j t :=
  (room_from (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) (rt_room F) qs b j t).

(* a is a start address or one of the first n returned addresses. *)
Definition p3b_inr (n : nat) (a : adrF) : Prop := match a with Known _ => True | Ret i => (i < n)%nat end.

Lemma p3b_inr_app : forall (qd post : list sptr) a, p3b_inr (length qd) a -> resolveF (qd ++ post) a = resolveF qd a.
Proof. intros qd post [p|i] H; cbn in H |- *; [reflexivity | apply app_nth1; exact H]. Qed.

Lemma p3b_inr_le : forall n n' a, (n <= n')%nat -> p3b_inr n a -> p3b_inr n' a.
Proof. intros n n' [p|i] H1 H2; cbn in H2 |- *; [exact I | lia]. Qed.

Lemma p3b_nret_cons : forall (e : rev sptr) l, nretF (e :: l) = (rets sptr e + nretF l)%nat.
Proof. reflexivity. Qed.

Lemma p3b_nret_free : forall n (a : adrF), nretF [RFree n a] = 0%nat.
Proof. reflexivity. Qed.

Lemma p3b_sl_shape : forall fuel mx no cap rem j o j' o',
  nretF (fst (sl_run fuel mx no cap rem j o)) = nretF (fst (sl_run fuel mx no cap rem j' o')) /\
  fst (snd (sl_run fuel mx no cap rem j o)) = fst (snd (sl_run fuel mx no cap rem j' o')).
Proof.
  induction fuel as [|f IH]; intros mx no cap rem j o j' o'; cbn [sl_run]; [split; reflexivity|].
  destruct (rem <=? 0); [split; reflexivity|].
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  destruct (cap <? no + n); [|apply IH].
  destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (Ret j) (S j') (Ret j')) as [H1 H2].
  cbn [fst snd]. rewrite !p3b_nret_cons, H1. split; [|exact H2].
  destruct (cap =? 0); reflexivity.
Qed.

Lemma p3b_sl_out : forall fuel mx no cap rem j o,
  snd (snd (sl_run fuel mx no cap rem j o)) = o \/
  exists i, snd (snd (sl_run fuel mx no cap rem j o)) = Ret i /\
    (j <= i < j + nretF (fst (sl_run fuel mx no cap rem j o)))%nat.
Proof.
  induction fuel as [|f IH]; intros mx no cap rem j o; cbn [sl_run]; [left; reflexivity|].
  destruct (rem <=? 0); [left; reflexivity|].
  set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
  destruct (cap <? no + n); [|apply IH].
  right. cbn [fst snd]. rewrite p3b_nret_cons.
  destruct (IH mx (no + n) ((no + n) * 2) (rem - n) (S j) (Ret j)) as [E|(i & E & Hi)].
  - exists j. split; [exact E|]. destruct (cap =? 0); cbn [rets]; lia.
  - exists i. split; [exact E|]. destruct (cap =? 0); cbn [rets]; lia.
Qed.

Lemma p3b_snd_shape : forall live mx no c len j o j' o',
  nretF (send_line_tr live mx no c len j o) = nretF (send_line_tr live mx no c len j' o').
Proof.
  intros live mx no c len j o j' o'. unfold send_line_tr.
  destruct live; [exact (proj1 (p3b_sl_shape _ _ _ _ _ _ _ _ _)) | reflexivity].
Qed.

Lemma p3b_snd_out : forall live mx no c len j o,
  send_line_out live mx no c len j o = o \/
  exists i, send_line_out live mx no c len j o = Ret i /\ (j <= i < j + nretF (send_line_tr live mx no c len j o))%nat.
Proof. intros. unfold send_line_out, send_line_tr. destruct live; [apply p3b_sl_out | left; reflexivity]. Qed.

Lemma p3b_ge_shape : forall live mx no c xl j o j' o',
  nretF (gesture_end_tr live mx no c xl j o) = nretF (gesture_end_tr live mx no c xl j' o').
Proof. intros. unfold gesture_end_tr. cbv zeta. rewrite !nret_app. f_equal; apply p3b_snd_shape. Qed.

Lemma p3b_ge_out : forall live mx no c xl j o,
  gesture_end_out live mx no c xl j o = o \/
  exists i, gesture_end_out live mx no c xl j o = Ret i /\ (j <= i < j + nretF (gesture_end_tr live mx no c xl j o))%nat.
Proof.
  intros live mx no c xl j o. unfold gesture_end_out, gesture_end_tr. cbv zeta. rewrite nret_app.
  destruct (p3b_snd_out live mx no c xl j o) as [E1|(i1 & E1 & H1)];
  destruct (p3b_snd_out live mx (no + xl) (send_line_cap live mx no c xl) 5
              (j + nretF (send_line_tr live mx no c xl j o)) (send_line_out live mx no c xl j o)) as [E2|(i2 & E2 & H2)].
  - left. rewrite E2. exact E1.
  - right. exists i2. split; [exact E2 | lia].
  - right. exists i1. rewrite E2. split; [exact E1 | lia].
  - right. exists i2. split; [exact E2 | lia].
Qed.

(* The capacity after a keys' run does not depend on the addresses. *)
Lemma p3b_ker_cap : forall live mx (xks xks' : list (Z * adrF)) no c j o j' o', map fst xks = map fst xks' ->
  fst (snd (keys_end_run live mx no c xks j o)) = fst (snd (keys_end_run live mx no c xks' j' o')).
Proof.
  intros live mx xks. induction xks as [|[xl ka] r IH]; intros [|[xl' ka'] r'] no c j o j' o' E;
    cbn [map fst] in E; try discriminate; [reflexivity|].
  injection E as <- E. cbn [keys_end_run fst snd]. apply IH. exact E.
Qed.

Lemma p3b_nodup_inj : forall {X Y : Type} (g : X -> Y) (l : list X) x y,
  List.NoDup (map g l) -> In x l -> In y l -> g x = g y -> x = y.
Proof.
  intros X Y g l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn [map] in ND. apply List.NoDup_cons_iff in ND as [Ha ND].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - reflexivity.
  - exfalso. apply Ha. rewrite E. apply in_map. exact Hy.
  - exfalso. apply Ha. rewrite <- E. apply in_map. exact Hx.
  - exact (IH x y ND Hx Hy E).
Qed.

(* With the block addresses distinct, one model pointer is live at an address. *)
Lemma p3b_live_uniq : forall L A p p' a n n', NoDup (map fst (blocks L A)) ->
  live_at L A p a n -> live_at L A p' a n' -> p = p'.
Proof.
  intros L A p p' a n n' ND [H1 E1] [H2 E2]. apply NoDup_ListNoDup in ND. unfold blocks in ND. rewrite map_map in ND.
  assert (X : (p, n) = (p', n')).
  { apply (p3b_nodup_inj (fun b => ptr_addr L (fst b)) (user_blocks A)); [exact ND | exact H1 | exact H2 |].
    change (ptr_addr L p = ptr_addr L p'). rewrite E1, E2. reflexivity. }
  congruence.
Qed.

Lemma p3b_sptr_of_eq : forall L A p a n, NoDup (map fst (blocks L A)) -> live_at L A p a n -> sptr_of L A a = p.
Proof.
  intros L A p a n ND LA. pose proof LA as [H1 E1].
  assert (IB : In (a, n) (blocks L A)) by (apply blocks_In2; exists p; split; [exact E1 | exact H1]).
  destruct (sptr_of_spec L A a n ND IB) as [S1 S2].
  exact (p3b_live_uniq L A _ _ a n n ND (conj S1 S2) LA).
Qed.

Lemma p3b_live_of_blocks : forall L A a n, NoDup (map fst (blocks L A)) -> In (a, n) (blocks L A) ->
  live_at L A (sptr_of L A a) a n.
Proof. intros L A a n ND IB. exact (sptr_of_spec L A a n ND IB). Qed.

Section P3B.
Variable F : ResFormT.

Lemma p3b_sl_sim : forall fuel mx no cap rem (qs qc : list sptr) (j k : nat) (o o' : adrF) (b : rt_R F),
  (forall i, (k <= i < k + nretF (fst (sl_run fuel mx no cap rem k o')))%nat ->
     nth (j + i) qs (SP 0 0) = nth i qc (SP 0 0)) ->
  (cap <> 0 -> resolveF qs o = resolveF qc o') ->
  p3b_rn F qs b (j + k) (fst (sl_run fuel mx no cap rem (j + k) o)) =
    p3b_rn F qc b k (fst (sl_run fuel mx no cap rem k o')) /\
  (p3b_rm F qs b (j + k) (fst (sl_run fuel mx no cap rem (j + k) o)) <->
     p3b_rm F qc b k (fst (sl_run fuel mx no cap rem k o'))) /\
  (fst (snd (sl_run fuel mx no cap rem k o')) <> 0 ->
     resolveF qs (snd (snd (sl_run fuel mx no cap rem (j + k) o))) =
       resolveF qc (snd (snd (sl_run fuel mx no cap rem k o')))).
Proof using.
  induction fuel as [|f IH]; intros mx no cap rem qs qc j k o o' b; cbn [sl_run].
  - intros HN HR. cbn [fst snd run_from room_from]. split; [reflexivity|]. split; [tauto | exact HR].
  - destruct (rem <=? 0).
    + intros HN HR. cbn [fst snd run_from room_from]. split; [reflexivity|]. split; [tauto | exact HR].
    + set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
      destruct (cap <? no + n); [|exact (IH mx (no + n) cap (rem - n) qs qc j k o o' b)].
      intros HN HR. cbn [fst snd] in HN |- *. rewrite p3b_nret_cons in HN.
      assert (HK : nth (j + k) qs (SP 0 0) = nth k qc (SP 0 0))
        by (apply HN; destruct (cap =? 0); cbn [rets]; lia).
      assert (HN' : forall i,
                 (S k <= i < S k + nretF (fst (sl_run f mx (no + n) ((no + n) * 2) (rem - n) (S k) (Ret k))))%nat ->
                 nth (j + i) qs (SP 0 0) = nth i qc (SP 0 0))
        by (intros i Hi; apply HN; destruct (cap =? 0); cbn [rets]; lia).
      destruct (cap =? 0) eqn:Ec; cbn [run_from room_from]; replace (S (j + k)) with (j + S k)%nat by lia.
      * destruct (IH mx (no + n) ((no + n) * 2) (rem - n) qs qc j (S k) (Ret (j + k)) (Ret k)
                    (rt_malloc F b ((no + n) * 2)) HN' (fun _ => HK)) as (R1 & R2 & R3).
        split; [exact R1|]. split; [clear - R2; tauto | exact R3].
      * rewrite HK, (HR (proj1 (Z.eqb_neq _ _) Ec)).
        destruct (IH mx (no + n) ((no + n) * 2) (rem - n) qs qc j (S k) (Ret (j + k)) (Ret k)
                    (rt_realloc F b cap ((no + n) * 2) (resolveF qc o') (nth k qc (SP 0 0))) HN' (fun _ => HK))
          as (R1 & R2 & R3).
        split; [exact R1|]. split; [clear - R2; tauto | exact R3].
Qed.

Lemma p3b_snd_sim : forall live mx no c len (qs qc : list sptr) (j k : nat) (o o' : adrF) (b : rt_R F),
  (forall i, (k <= i < k + nretF (send_line_tr live mx no c len k o'))%nat ->
     nth (j + i) qs (SP 0 0) = nth i qc (SP 0 0)) ->
  (c <> 0 -> resolveF qs o = resolveF qc o') ->
  p3b_rn F qs b (j + k) (send_line_tr live mx no c len (j + k) o) =
    p3b_rn F qc b k (send_line_tr live mx no c len k o') /\
  (p3b_rm F qs b (j + k) (send_line_tr live mx no c len (j + k) o) <->
     p3b_rm F qc b k (send_line_tr live mx no c len k o')) /\
  (send_line_cap live mx no c len <> 0 ->
     resolveF qs (send_line_out live mx no c len (j + k) o) = resolveF qc (send_line_out live mx no c len k o')).
Proof using.
  intros live mx no c len qs qc j k o o' b HN HR. unfold send_line_tr, send_line_out, send_line_cap in *.
  destruct live.
  - destruct (p3b_sl_sim (Z.to_nat len) mx no c len qs qc j k o o' b HN HR) as (R1 & R2 & R3).
    split; [exact R1|]. split; [exact R2|]. intros Hc. apply R3.
    rewrite (proj2 (p3b_sl_shape (Z.to_nat len) mx no c len k o' 0 adr0)). exact Hc.
  - cbn [run_from room_from]. split; [reflexivity|]. split; [tauto | exact HR].
Qed.

Lemma p3b_ge_sim : forall live mx no c xl (qs qc : list sptr) (j k : nat) (o o' : adrF) (b : rt_R F),
  (forall i, (k <= i < k + nretF (gesture_end_tr live mx no c xl k o'))%nat ->
     nth (j + i) qs (SP 0 0) = nth i qc (SP 0 0)) ->
  (c <> 0 -> resolveF qs o = resolveF qc o') ->
  p3b_rn F qs b (j + k) (gesture_end_tr live mx no c xl (j + k) o) =
    p3b_rn F qc b k (gesture_end_tr live mx no c xl k o') /\
  (p3b_rm F qs b (j + k) (gesture_end_tr live mx no c xl (j + k) o) <->
     p3b_rm F qc b k (gesture_end_tr live mx no c xl k o')) /\
  (gesture_end_cap live mx no c xl <> 0 ->
     resolveF qs (gesture_end_out live mx no c xl (j + k) o) = resolveF qc (gesture_end_out live mx no c xl k o')).
Proof using.
  intros live mx no c xl qs qc j k o o' b HN HR.
  unfold gesture_end_tr, gesture_end_out, gesture_end_cap in *. cbv zeta in HN |- *.
  rewrite nret_app in HN.
  assert (EN : nretF (send_line_tr live mx no c xl (j + k) o) = nretF (send_line_tr live mx no c xl k o'))
    by apply p3b_snd_shape.
  destruct (p3b_snd_sim live mx no c xl qs qc j k o o' b) as (R1 & R2 & R3); [intros i Hi; apply HN; lia | exact HR |].
  destruct (p3b_snd_sim live mx (no + xl) (send_line_cap live mx no c xl) 5 qs qc j
              (k + nretF (send_line_tr live mx no c xl k o')) (send_line_out live mx no c xl (j + k) o)
              (send_line_out live mx no c xl k o') (p3b_rn F qc b k (send_line_tr live mx no c xl k o')))
    as (S1 & S2 & S3); [intros i Hi; apply HN; lia | exact R3 |].
  rewrite !run_from_app, !room_from_app, EN, R1.
  replace (j + k + nretF (send_line_tr live mx no c xl k o'))%nat
    with (j + (k + nretF (send_line_tr live mx no c xl k o')))%nat by lia.
  split; [exact S1|]. split; [clear - R2 S2; tauto | exact S3].
Qed.
End P3B.

Section GSP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Local Notation segs := (ms_segs Bm).
Local Notation MR := (aa_MR API).

Lemma blk_lo : forall L A mem md q m, MR L A mem md -> In (q, m) (blocks L A) -> 4096 <= q /\ q + m <= YM05.alloc_ceiling.
Proof using.
  intros L A mem md q m HM H. apply blocks_In2 in H as (p & <- & Hp).
  exact (mr_blocks_range Bm MR (aa_laws API) L A mem md p m HM Hp).
Qed.

Lemma blk_al : forall L A mem md q m, MR L A mem md -> In (q, m) (blocks L A) -> q mod 8 = 0.
Proof using.
  intros L A mem md q m HM H. apply blocks_In2 in H as (p & <- & Hp).
  pose proof (mr_blocks_aligned Bm MR (aa_laws API) L A mem md p m HM Hp) as H16.
  Z.div_mod_to_equations. lia.
Qed.

Lemma owned_lo : forall L A mem md a, MR L A mem md -> owned Bm L A a -> 0 <= a < YM05.alloc_ceiling.
Proof using. intros L A mem md a HM Ho. exact (mr_owned_low Bm MR (aa_laws API) L A mem md a HM Ho). Qed.

Lemma blk_facts : forall L A mem md q k i, MR L A mem md -> In (q, k) (blocks L A) -> 0 <= i < k ->
  present mem (q + i) /\ 4096 <= q /\ q + k <= YM05.alloc_ceiling /\ ~ owned Bm L A (q + i).
Proof using.
  intros L A mem md q k i HM Hin Hi. apply blocks_In2 in Hin as (p & <- & Hp).
  exact (mr_blocks Bm MR (aa_laws API) L A mem md p k i HM Hp Hi).
Qed.

Definition chain (K : Z) (E F : Z -> Prop)
    (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ F (ptr_addr L p) ->
     ptr_addr L' p = ptr_addr L p) /\
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> ~ F (ptr_addr L p) -> In (p, n) (user_blocks A')) /\
  (forall p, In (p, 0) (user_blocks A) -> In (p, 0) (user_blocks A') /\ ptr_addr L' p = ptr_addr L p) /\
  (forall a, in_img Bm a -> owned Bm L' A' a -> owned Bm L A a) /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (YM05.alloc_ceiling <= a < 2 ^ 64 \/ in_img Bm a) ->
     ~ owned Bm L A a -> ~ owned Bm L' A' a -> ~ scratch_k Bm K regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ~ F (ptr_addr L p) -> 0 <= i < n ->
     ~ E (ptr_addr L p + i) ->
     mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, scratch_k Bm K regs a -> writable_at segs mem' a).

Lemma relay_of_chain : forall K E F L A regs mem md L' A' regs' mem' md',
  chain K E F L A regs mem md L' A' mem' md' -> regs_preserved regs regs' ->
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md'.
Proof using.
  intros K E F L A regs mem md L' A' regs' mem' md'
    (M & W & B & LE & RG & AD & SV & Z0 & IO & VM & FR & BY & SW) RP.
  repeat (split; [eassumption|]). exact SW.
Qed.

Lemma in_chain : forall K E F L A regs mem md L1 A1 m1 md1 p n,
  WF A -> chain K E F L A regs mem md L1 A1 m1 md1 -> In (p, n) (user_blocks A) -> ~ F (ptr_addr L p) ->
  In (p, n) (user_blocks A1) /\ ptr_addr L1 p = ptr_addr L p.
Proof using.
  intros K E F L A regs mem md L1 A1 m1 md1 p n HW
    (M & W & B & LE & RG & AD & SV & Z0 & IO & VM & FR & BY & SW) H0 HF.
  pose proof (ub_nonneg A p n HW H0) as Hn.
  destruct (Z.eq_dec n 0) as [->|Hn'].
  - exact (Z0 p H0).
  - assert (H1 : In (p, n) (user_blocks A1)) by (apply SV; [exact H0 | lia | exact HF]).
    split; [exact H1 | exact (AD p n H0 H1 HF)].
Qed.

Lemma chain_ge : forall K E F L A regs mem md L1 A1 m1 md1 K' E' F' R1 L2 A2 R2 m2 md2,
  WF A ->
  chain K E F L A regs mem md L1 A1 m1 md1 ->
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  (forall a, scratch_k Bm K' R1 a -> scratch_k Bm K regs a) ->
  (forall a, scratch_k Bm K regs a -> ~ scratch_k Bm K' R1 a -> YM05.alloc_ceiling <= a < 2 ^ 64) ->
  (forall a, E' a -> a < YM05.alloc_ceiling /\ (in_img Bm a -> E a)) ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> ~ F (ptr_addr L p) ->
     ~ F' (ptr_addr L p) /\ (forall i, 0 <= i < n -> ~ E (ptr_addr L p + i) -> ~ E' (ptr_addr L p + i))) ->
  chain K E F L A regs mem md L2 A2 m2 md2.
Proof using.
  intros K E F L A regs mem md L1 A1 m1 md1 K' E' F' R1 L2 A2 R2 m2 md2 HW CH RP SC SC2 EH FB.
  pose proof (fun p n => in_chain K E F L A regs mem md L1 A1 m1 md1 p n HW CH) as IN1.
  destruct CH as (M1 & W1 & B1 & LE1 & RG1 & AD1 & SV1 & Z1 & IO1 & VM1 & FR1 & BY1 & SW1).
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split.
  { destruct LE1 as (c1 & s1 & b1 & r1). destruct LE2 as (c2 & s2 & b2 & r2).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite r2 by lia. apply r1. exact Hr. }
  split; [lia|].
  split.
  { intros p n H0 H2 HF. destruct (IN1 p n H0 HF) as [H1 E1]. rewrite <- E1.
    apply (AD2 p n H1 H2). rewrite E1. exact (proj1 (FB p n H0 H1 HF)). }
  split.
  { intros p n H0 Hn HF. destruct (IN1 p n H0 HF) as [H1 E1].
    apply (SV2 p n H1 Hn). rewrite E1. exact (proj1 (FB p n H0 H1 HF)). }
  split.
  { intros p H0. destruct (Z1 p H0) as [H1 E1]. destruct (Z2 p H1) as [H2 E2]. split; [exact H2 | congruence]. }
  split.
  { intros a Ha Ho. apply IO1; [exact Ha|]. apply IO2; assumption. }
  split.
  { destruct VM1 as [v1 ->]. destruct VM2 as [v2 ->]. exists v2. apply vm_twice. }
  split.
  { intros a Ha NO0 NO2 NS NE.
    assert (NO1 : ~ owned Bm L1 A1 a).
    { intros Ho. destruct Ha as [Ha|Ha].
      - pose proof (owned_lo _ _ _ _ _ M1 Ho). lia.
      - exact (NO0 (IO1 a Ha Ho)). }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E1 W1'].
    assert (NE' : ~ E' a).
    { intros He. destruct (EH a He) as [Hlt Himg]. destruct Ha as [Ha|Ha]; [lia | exact (NE (Himg Ha))]. }
    destruct (FR2 a Ha NO1 NO2 (fun H => NS (SC a H)) NE') as [E2 W2'].
    split; [congruence | tauto]. }
  split.
  { intros p n i H0 H2 HF Hi HE.
    destruct (IN1 p n H0 HF) as [H1 E1].
    destruct (FB p n H0 H1 HF) as [HF' HE'].
    rewrite <- (BY1 p n i H0 H1 HF Hi HE). rewrite <- E1.
    apply (BY2 p n i H1 H2); [rewrite E1; exact HF' | exact Hi | rewrite E1; exact (HE' i Hi HE)]. }
  intros a Ha.
  assert (D : scratch_k Bm K' R1 a \/ ~ scratch_k Bm K' R1 a) by (unfold scratch_k; lia).
  destruct D as [D|D]; [exact (SW2 a D)|].
  pose proof (SC2 a Ha D) as Hhi.
  assert (NO1 : ~ owned Bm L1 A1 a) by (intros Ho; pose proof (owned_lo _ _ _ _ _ M1 Ho); lia).
  assert (NO2 : ~ owned Bm L2 A2 a) by (intros Ho; pose proof (owned_lo _ _ _ _ _ M2 Ho); lia).
  assert (NE' : ~ E' a) by (intros He; pose proof (proj1 (EH a He)); lia).
  destruct (FR2 a (or_introl Hhi) NO1 NO2 D NE') as [_ Wq]. apply Wq. exact (SW1 a Ha).
Qed.

Hypothesis AXg : AllocExtra Bm MR.
Hypothesis CTXg : ctx_owned Bm API.
Hypothesis NODUP : forall L A mem md, aa_MR API L A mem md -> NoDup (map fst (blocks L A)).
Hypothesis SLACK : block_slack_present Bm API.
Hypothesis FREEPC : ms_free Bm = 0x15f4c.

Section Img.
Hypothesis SEGS : ms_segs Bm = rsegs.

Lemma in_img_of_seg2 : forall a seg, 0 <= a -> find_segment rsegs a 1 = Some seg -> in_img Bm a.
Proof using SEGS.
  intros a seg Ha F. destruct (find_segment_in2 _ _ _ _ F) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ rsegs) rsegs_top2 seg Hin) as T. apply Z.leb_le in T.
  unfold in_img. rewrite SEGS. split; [intro E; rewrite E in Hin; destruct Hin|].
  exists (segment_reservation seg). split; [apply in_map; exact Hin|].
  unfold segment_reservation, page_round_down_Z, page_round_up_Z. cbn [fst snd].
  change page_size with 4096.
  pose proof (N2Z.is_nonneg (seg_base seg)) as P1. pose proof (N2Z.is_nonneg (seg_size seg)) as P2.
  set (bs := Z.of_N (seg_base seg)) in *. set (sz := Z.of_N (seg_size seg)) in *.
  pose proof (Z.mul_div_le bs 4096 ltac:(lia)) as D1.
  pose proof (Z.div_pos bs 4096 ltac:(lia) ltac:(lia)) as D2.
  pose proof (Z.mul_div_le (bs + sz + 4096 - 1) 4096 ltac:(lia)) as D3.
  pose proof (Z.mul_succ_div_gt (bs + sz + 4096 - 1) 4096 ltac:(lia)) as D4.
  rewrite !unsigned_lit by lia. lia.
Qed.

Lemma in_img_low2 : forall a, in_img Bm a -> 0 <= a < 2 ^ 21.
Proof using SEGS.
  intros a (_ & s & Hin & H1 & H2). rewrite SEGS in Hin.
  pose proof (proj1 (forallb_forall _ _) rsegs_res_top2 s Hin) as T. apply Z.leb_le in T.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma present_of_wr : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img Bm a -> writable_at rsegs m a -> present m a.
Proof using SEGS.
  intros m a Ha NI. unfold writable_at, wview, present.
  destruct (m (Z_to_bv 64 a)) as [b|]; [intros _; exists b; reflexivity|].
  rewrite unsigned_lit by lia.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F.
  - exfalso. apply NI. eapply in_img_of_seg2; [lia | exact F].
  - intros W. exfalso. apply W. reflexivity.
Qed.

Lemma chain_free : forall K E F L A regs mem md L1 A1 m1 md1 R1 E' L2 A2 R2 m2 md2 p nk,
  WF A -> MR L A mem md -> ctx_owned Bm API -> AllocExtra Bm MR ->
  chain K E F L A regs mem md L1 A1 m1 md1 ->
  call_post Bm MR L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 ->
  (length (st_regions A1) <= length (st_regions A2))%nat ->
  (forall q k, In (q, k) (user_blocks A1) -> q <> p -> In (q, k) (user_blocks A2)) ->
  In (p, nk) (user_blocks A1) -> 0 < nk ->
  (forall a, scratch Bm R1 a -> scratch_k Bm K regs a) ->
  (forall a, scratch_k Bm K regs a -> ~ scratch Bm R1 a -> YM05.alloc_ceiling <= a < 2 ^ 64) ->
  (forall a, E' a -> a < YM05.alloc_ceiling /\ ~ in_img Bm a) ->
  (forall q n, In (q, n) (user_blocks A) -> In (q, n) (user_blocks A1) -> ~ F (ptr_addr L q) -> q <> p) ->
  chain K E F L A regs mem md L2 A2 m2 md2.
Proof using.
  intros K E F L A regs mem md L1 A1 m1 md1 R1 E' L2 A2 R2 m2 md2 p nk HW HM0 CTX AX CH CP RG2 SV2 PIN PN SC SC2 EH PNE.
  pose proof (fun p n => in_chain K E F L A regs mem md L1 A1 m1 md1 p n HW CH) as IN1.
  destruct CH as (M1 & W1 & B1 & LE1 & RG1 & AD1 & SV1 & Z1 & IO1 & VM1 & FR1 & BY1 & SW1).
  destruct CP as (M2 & W2 & B2 & LE2 & AD2 & RPr & VM2 & FR2 & BY2 & SW2).
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split.
  { destruct LE1 as (c1 & s1 & b1 & r1). destruct LE2 as (c2 & s2 & b2 & r2).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite r2 by lia. apply r1. exact Hr. }
  split; [lia|].
  split.
  { intros q n H0 H2 HF. destruct (IN1 q n H0 HF) as [H1 E1]. rewrite <- E1. exact (AD2 q n H1 H2). }
  split.
  { intros q n H0 Hn HF. destruct (IN1 q n H0 HF) as [H1 E1]. apply SV2; [exact H1|]. exact (PNE q n H0 H1 HF). }
  split.
  { intros q H0. destruct (Z1 q H0) as [H1 E1].
    assert (Hq : q <> p).
    { intros ->. pose proof (nodup_fst _ p 0 nk (proj2 (NoDup_ListNoDup _) (YO10.user_block_ptrs_NoDup A1 W1)) H1 PIN).
      lia. }
    pose proof (SV2 q 0 H1 Hq) as H2. split; [exact H2|]. rewrite (AD2 q 0 H1 H2). exact E1. }
  split.
  { intros a Ha Ho. destruct Ho as [Ho|Ho].
    - exact (CTX L A mem md a HM0 (ax_img AX L2 A2 m2 md2 a M2 Ha Ho)).
    - right. exact Ho. }
  split.
  { destruct VM1 as [v1 ->]. destruct VM2 as [v2 ->]. exists v2. apply vm_twice. }
  split.
  { intros a Ha NO0 NO2 NS NE.
    assert (NO1 : ~ owned Bm L1 A1 a).
    { intros Ho. destruct Ha as [Ha|Ha].
      - pose proof (owned_lo _ _ _ _ _ M1 Ho). lia.
      - exact (NO0 (IO1 a Ha Ho)). }
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E1 W1'].
    assert (NE' : ~ E' a).
    { intros He. destruct (EH a He) as [Hl Hi]. destruct Ha as [Ha|Ha]; [lia | exact (Hi Ha)]. }
    destruct (FR2 a Ha NO1 NO2 (fun H => NS (SC a H)) NE') as [E2 W2'].
    split; [etransitivity; [exact E2 | exact E1] | tauto]. }
  split.
  { intros q n i H0 H2 HF Hi HE. destruct (IN1 q n H0 HF) as [H1 E1].
    rewrite <- (BY1 q n i H0 H1 HF Hi HE). rewrite <- E1. exact (BY2 q n i H1 H2 Hi). }
  intros a Ha.
  assert (D : scratch Bm R1 a \/ ~ scratch Bm R1 a) by (unfold scratch; lia).
  destruct D as [D|D]; [exact (SW2 a D)|].
  pose proof (SC2 a Ha D) as Hhi.
  assert (NO1 : ~ owned Bm L1 A1 a) by (intros Ho; pose proof (owned_lo _ _ _ _ _ M1 Ho); lia).
  assert (NO2 : ~ owned Bm L2 A2 a) by (intros Ho; pose proof (owned_lo _ _ _ _ _ M2 Ho); lia).
  assert (NE' : ~ E' a) by (intros He; pose proof (proj1 (EH a He)); lia).
  destruct (FR2 a (or_introl Hhi) NO1 NO2 D NE') as [_ Wq]. apply Wq. exact (SW1 a Ha).
Qed.

Lemma chain_mem : forall K E F L A regs mem md L1 A1 m1 md1 m2 W,
  AllocExtra Bm MR ->
  chain K E F L A regs mem md L1 A1 m1 md1 ->
  munch W m1 m2 -> wmono segs m1 m2 ->
  (forall a, 0 <= a < 2 ^ 64 -> outside W a \/ (scratch_k Bm K regs a /\ YM05.alloc_ceiling <= a) \/
     (E a /\ exists q k, In (q, k) (blocks L1 A1) /\ q <= a < q + k)) ->
  chain K E F L A regs mem md L1 A1 m2 md1.
Proof using SEGS.
  intros K E F L A regs mem md L1 A1 m1 md1 m2 W AX CH MU WM HWr.
  destruct CH as (M1 & W1 & B1 & LE1 & RG1 & AD1 & SV1 & Z1 & IO1 & VM1 & FR1 & BY1 & SW1).
  pose proof (aa_laws API) as LAWS. pose proof YM05.alloc_ceiling_lt as ACL.
  destruct (mr_model Bm MR LAWS _ _ _ _ M1) as (Hh & Hl & Hmat).
  assert (OWN : forall a, owned Bm L1 A1 a -> outside W a).
  { intros a Ho. pose proof (owned_lo _ _ _ _ _ M1 Ho) as Hr.
    destruct (HWr a ltac:(lia)) as [Hout | [[_ Hc] | [_ (q & k & Hq & Hqa)]]]; [exact Hout | lia |].
    exfalso. destruct (blk_facts _ _ _ _ q k (a - q) M1 Hq ltac:(lia)) as (_ & _ & _ & Hno).
    replace (q + (a - q)) with a in Hno by lia. exact (Hno Ho). }
  assert (MU' : forall a, 0 <= a < 2 ^ 64 -> outside W a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
  { intros a Ha Ho. apply MU. rewrite unsigned_lit by lia. exact Ho. }
  assert (M2 : MR L1 A1 m2 md1).
  { eapply (mr_frame Bm MR LAWS L1 A1 m1 m2 md1 md1 M1).
    - intros a Ho. pose proof (owned_lo _ _ _ _ _ M1 Ho) as Hr.
      unfold mbyte. rewrite (MU' a ltac:(lia) (OWN a Ho)). reflexivity.
    - intros a Ho [b Hb]. pose proof (owned_lo _ _ _ _ _ M1 Ho) as Hr.
      exists b. rewrite (MU' a ltac:(lia) (OWN a Ho)). exact Hb.
    - intros p n i Hin Hi. destruct (mr_blocks Bm MR LAWS L1 A1 m1 md1 p n i M1 Hin Hi) as (Hp & H4 & Hc & _).
      destruct (HWr (ptr_addr L1 p + i) ltac:(lia)) as [Hout | _].
      + destruct Hp as [b Hb]. exists b. rewrite (MU' (ptr_addr L1 p + i) ltac:(lia) Hout). exact Hb.
      + apply (present_of_wr m2 (ptr_addr L1 p + i) ltac:(lia)).
        * exact (ax_blocks_img AX L1 A1 m1 md1 p n i M1 Hin Hi).
        * rewrite <- SEGS. apply WM. exact (present_writable2 segs m1 _ Hp).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  split; [exact M2|]. split; [exact W1|]. split; [exact B1|]. split; [exact LE1|]. split; [exact RG1|].
  split; [exact AD1|]. split; [exact SV1|]. split; [exact Z1|]. split; [exact IO1|]. split; [exact VM1|].
  split.
  { intros a Ha NO0 NO1 NS NE.
    pose proof (@YM05.alloc_ceiling_value rc) as ACV.
    assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | pose proof (in_img_low2 a Ha); lia]).
    destruct (HWr a Hr) as [Hout | [[Hs _] | [He _]]]; [| exact (False_ind _ (NS Hs)) | exact (False_ind _ (NE He))].
    destruct (FR1 a Ha NO0 NO1 NS NE) as [E1 W1'].
    pose proof (MU' a Hr Hout) as Eq.
    split.
    - unfold mbyte in *. rewrite Eq. exact E1.
    - unfold writable_at, wview in *. rewrite Eq. exact W1'. }
  split.
  { intros p n i H0 H2 HF Hi HE.
    rewrite <- (BY1 p n i H0 H2 HF Hi HE).
    destruct (mr_blocks Bm MR LAWS L1 A1 m1 md1 p n i M1 H2 Hi) as (_ & H4 & Hc & _).
    rewrite <- (AD1 p n H0 H2 HF) in HE |- *.
    destruct (HWr (ptr_addr L1 p + i) ltac:(lia)) as [Hout | [[_ Hcl] | [He _]]]; [| lia | exact (False_ind _ (HE He))].
    unfold mbyte. rewrite (MU' (ptr_addr L1 p + i) ltac:(lia) Hout). reflexivity. }
  intros a Ha. apply WM. exact (SW1 a Ha).
Qed.

Lemma img_plain_unowned : AllocExtra Bm MR -> forall L A mem md a, MR L A mem md -> img_plain Bm a -> ~ owned Bm L A a.
Proof using.
  intros AX L A mem md a HM (Hi & Hs & Hc & He) [Ho|Ho];
    [exact (Hc (ax_img AX L A mem md a HM Hi Ho)) | exact (Hs Ho)].
Qed.

Lemma ge_keeps : forall K' l O C L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k,
  (forall a, G_RELAY_LO <= a < G_RELAY_HI -> in_img Bm a) ->
  MR L1 A1 m1 md1 ->
  relay_post Bm API K' (send_writes l O C) (fun q => l = true /\ q = O) L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  In (q, k) (blocks L1 A1) -> 0 < k -> (forall i, 0 <= i < k -> ~ in_img Bm (q + i)) ->
  (l = true -> q <> O /\ (0 < C -> In (O, C) (blocks L1 A1))) ->
  In (q, k) (blocks L2 A2) /\ (forall i, 0 <= i < k -> mbyte segs m2 (q + i) = mbyte segs m1 (q + i)).
Proof using.
  intros K' l O C L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k GI M1 RP Hq Hk NI HO.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  destruct (proj1 (blocks_In2 _ _ _ _) Hq) as (p & Ep & Hp).
  assert (NF : ~ (l = true /\ ptr_addr L1 p = O)) by (intros [Hl Hx]; destruct (HO Hl) as [Hne _]; congruence).
  pose proof (SV2 p k Hp Hk NF) as Hp2.
  pose proof (AD2 p k Hp Hp2 NF) as E2.
  split.
  { apply blocks_In2. exists p. split; [congruence | exact Hp2]. }
  intros i Hi. rewrite <- Ep.
  apply (BY2 p k i Hp Hp2 NF Hi). rewrite Ep.
  unfold send_writes. intros [H|[H|[H|(Hl & H)]]].
  - apply (NI i Hi). apply GI. unfold G_BROKEN, G_RELAY_LO, G_RELAY_HI in *. lia.
  - apply (NI i Hi). apply GI. unfold G_EINTR, G_RELAY_LO, G_RELAY_HI in *. lia.
  - apply (NI i Hi). apply GI. unfold G_OUTV, G_RELAY_LO, G_RELAY_HI in *. lia.
  - destruct (HO Hl) as [Hne HC]. assert (Cp : 0 < C) by lia.
    destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 Hq (HC Cp) Hne); lia.
Qed.

Lemma free_keeps : forall L1 A1 m1 L2 A2 m2 a0 n0 q k,
  (exists b1 b2, blocks L1 A1 = b1 ++ (a0, n0) :: b2 /\ blocks L2 A2 = b1 ++ b2) ->
  blocks_kept Bm L1 A1 m1 m2 (fun a => a = a0) ->
  In (q, k) (blocks L1 A1) -> q <> a0 ->
  In (q, k) (blocks L2 A2) /\ (forall i, 0 <= i < k -> mbyte segs m2 (q + i) = mbyte segs m1 (q + i)).
Proof using.
  intros L1 A1 m1 L2 A2 m2 a0 n0 q k (b1 & b2 & E1 & E2) BK Hq Hne.
  split.
  - rewrite E2. rewrite E1 in Hq. apply in_app_or in Hq as [Hq|[Hq|Hq]]; apply in_or_app;
      [left; exact Hq | congruence | right; exact Hq].
  - intros i Hi. exact (BK q k i Hq Hne Hi).
Qed.

Lemma cells_in_block : forall L A m1 m2 md q k c cs, MR L A m2 md -> In (q, k) (blocks L A) -> q <= c ->
  c + Z.of_nat (cells_size cs) <= q + k ->
  (forall i, 0 <= i < k -> mbyte segs m2 (q + i) = mbyte segs m1 (q + i)) ->
  rw_cells segs m1 c cs -> rw_cells segs m2 c cs.
Proof using.
  intros L A m1 m2 md q k c cs HM Hq H1 H2 HB HC. apply (rw_cells_transfer2 _ m1); [exact HC|].
  intros i Hi. replace (c + i) with (q + (c + i - q)) by lia. split.
  - apply HB. lia.
  - intros _. apply present_writable2. exact (proj1 (blk_facts _ _ _ _ _ _ (c + i - q) HM Hq ltac:(lia))).
Qed.

Lemma bytes_in_block : forall q k m1 m2 c bs, q <= c -> c + Z.of_nat (length bs) <= q + k ->
  (forall i, 0 <= i < k -> mbyte segs m2 (q + i) = mbyte segs m1 (q + i)) ->
  bytes_at segs m1 c bs -> bytes_at segs m2 c bs.
Proof using.
  intros q k m1 m2 c bs H1 H2 HB HC. apply (bytes_at_transfer2 _ m1); [exact HC|].
  intros i Hi. replace (c + i) with (q + (c + i - q)) by lia. apply HB. lia.
Qed.

Lemma img_cells_free : forall L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 c cs,
  AllocExtra Bm MR -> MR L1 A1 m1 md1 -> call_post Bm MR L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_plain Bm (c + i) /\ ~ E' (c + i) /\ ~ scratch Bm R1 (c + i)) ->
  rw_cells segs m1 c cs -> rw_cells segs m2 c cs.
Proof using.
  intros L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 c cs AX M1 CP H HC.
  destruct CP as (M2 & W2 & B2 & LE2 & AD2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply (rw_cells_transfer2 _ m1); [exact HC|]. intros i Hi. destruct (H i Hi) as (Hp & HE & HS).
  destruct (FR2 (c + i) (or_intror (proj1 Hp)) (img_plain_unowned AX _ _ _ _ _ M1 Hp)
              (img_plain_unowned AX _ _ _ _ _ M2 Hp) HS HE) as [E W].
  split; [exact E | apply W].
Qed.

Lemma high_cells_ge : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 c cs,
  MR L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     YM05.alloc_ceiling <= c + i < 2 ^ 64 /\ ~ scratch_k Bm K' R1 (c + i) /\ ~ E' (c + i)) ->
  rw_cells segs m1 c cs -> rw_cells segs m2 c cs.
Proof using.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 c cs M1 RP H HC.
  destruct RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply (rw_cells_transfer2 _ m1); [exact HC|]. intros i Hi. destruct (H i Hi) as (Hh & HS & HE).
  assert (N1 : ~ owned Bm L1 A1 (c + i)) by (intros Ho; pose proof (owned_lo _ _ _ _ _ M1 Ho); lia).
  assert (N2 : ~ owned Bm L2 A2 (c + i)) by (intros Ho; pose proof (owned_lo _ _ _ _ _ M2 Ho); lia).
  destruct (FR2 (c + i) (or_introl Hh) N1 N2 HS HE) as [E W]. split; [exact E | apply W].
Qed.

Lemma high_cells_free : forall L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 c cs,
  MR L1 A1 m1 md1 -> call_post Bm MR L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     YM05.alloc_ceiling <= c + i < 2 ^ 64 /\ ~ scratch Bm R1 (c + i) /\ ~ E' (c + i)) ->
  rw_cells segs m1 c cs -> rw_cells segs m2 c cs.
Proof using.
  intros L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 c cs M1 CP H HC.
  destruct CP as (M2 & W2 & B2 & LE2 & AD2 & RPr & VM2 & FR2 & BY2 & SW2).
  apply (rw_cells_transfer2 _ m1); [exact HC|]. intros i Hi. destruct (H i Hi) as (Hh & HS & HE).
  assert (N1 : ~ owned Bm L1 A1 (c + i)) by (intros Ho; pose proof (owned_lo _ _ _ _ _ M1 Ho); lia).
  assert (N2 : ~ owned Bm L2 A2 (c + i)) by (intros Ho; pose proof (owned_lo _ _ _ _ _ M2 Ho); lia).
  destruct (FR2 (c + i) (or_introl Hh) N1 N2 HS HE) as [E W]. split; [exact E | apply W].
Qed.

Lemma fresh_sep : forall q n lo hi, fresh_block Bm q n -> 0 < n -> lo < hi ->
  (forall a, lo <= a < hi -> in_img Bm a) -> q + n <= lo \/ hi <= q.
Proof using.
  intros q n lo hi (_ & _ & Hf) Hn Hlh Himg.
  destruct (Z_le_gt_dec (q + n) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi q) as [D'|D']; [right; exact D'|]. exfalso.
  apply (Hf (Z.max q lo - q)); [lia|]. replace (q + (Z.max q lo - q)) with (Z.max q lo) by lia. apply Himg. lia.
Qed.

Lemma slack_round : forall N, 8 * ((N + 7) / 8) = N + (- N) mod 8.
Proof using. intros N. Z.div_mod_to_equations. lia. Qed.

Lemma slack_bytes : forall L A mem md a XL, block_slack_present Bm API -> MR L A mem md ->
  In (a, XL + 1) (blocks L A) -> 0 <= a -> 0 <= XL -> a + XL + 1 + 8 <= 2 ^ 64 ->
  exists sl, Z.of_nat (length sl) = (- (a + XL + 1)) mod 8 /\ bytes_at segs mem (a + XL + 1) sl.
Proof using.
  intros L A mem md a XL SL HM Hin Ha HX Hb.
  pose proof (Z.mod_pos_bound (- (a + XL + 1)) 8 ltac:(lia)) as R8.
  destruct (bytes_of_mbytes segs mem (a + XL + 1) (Z.to_nat ((- (a + XL + 1)) mod 8))) as (sl & Ls & Hs).
  - lia.
  - lia.
  - intros i Hi. apply present_mbyte. apply (SL L A mem md a (XL + 1) _ HM Hin).
    pose proof (slack_round (a + (XL + 1))) as E. lia.
  - exists sl. split; [lia | exact Hs].
Qed.

Lemma ro_false_noimg : forall x, 0 <= bv_unsigned x -> ~ in_img Bm (bv_unsigned x) -> Mem.ro_addr segs x = false.
Proof using SEGS.
  intros x H0 H1. unfold Mem.ro_addr. rewrite SEGS.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:F; [|reflexivity].
  exfalso. apply H1. exact (in_img_of_seg2 _ s H0 F).
Qed.

Lemma ro_agree_munch1 : forall m m' lo hi, ro_agree segs m -> munch [(lo, hi)] m m' ->
  (forall x : word, lo <= bv_unsigned x < hi -> Mem.ro_addr segs x = false) -> ro_agree segs m'.
Proof using.
  intros m m' lo hi H MU HR a Hro.
  destruct (Z_le_gt_dec lo (bv_unsigned a)) as [D1|D1]; [destruct (Z_lt_ge_dec (bv_unsigned a) hi) as [D2|D2]|].
  - rewrite (HR a (conj D1 D2)) in Hro. discriminate.
  - unfold mrd. rewrite (MU a ltac:(cbn; split; [lia | exact I])). exact (H a Hro).
  - unfold mrd. rewrite (MU a ltac:(cbn; split; [lia | exact I])). exact (H a Hro).
Qed.

Lemma live_tot : forall cl br dd T, 0 <= T -> send_live cl br dd T = true -> 0 < T.
Proof using.
  intros cl br dd T HT HL. destruct (Z.eq_dec T 0) as [->|]; [|lia].
  unfold send_live, send_off in HL. rewrite orb_true_r in HL. discriminate.
Qed.

Ltac rgx_ne := match goal with Hc : ?x <> ?x |- _ => exact (False_ind _ (Hc eq_refl)) end.

Ltac geq X := etransitivity; [apply (getr_of_eqv2 _ _ _ X); reflexivity|]; reflexivity.

Ltac rgx_one X RFH :=
  lazymatch goal with |- getr ?R (Z_to_bv 5 ?rr) = _ =>
    rewrite (getr_of_eqv2 _ R (Z_to_bv 5 rr) X eq_refl); simp_regs;
    first [ reflexivity | apply Z_to_bv_bv_unsigned
          | exact (RFH rr ltac:(unfold callee_saved; lia))
          | exact (RFH rr ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)) ]
  end.

Ltac rgx_all X RFH :=
  let r := fresh "r" in let Hr := fresh "Hr" in let C := fresh "C" in
  intros r Hr; repeat (let h := fresh "Hne" in intro h); unfold callee_saved in Hr;
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct C as [C|C]; [subst r; first [rgx_ne | rgx_one X RFH] |]); subst r;
  first [rgx_ne | rgx_one X RFH].

(* A disjunction that lia does not split: lia case-splits every disjunctive hypothesis in its context. *)
Definition GOr (P Q : Prop) : Prop := P \/ Q.
Ltac hide_ors := repeat match goal with H : ?P \/ ?Q |- _ => change (GOr P Q) in H end.

(* A live block that a callee does not free stays live at the same address. *)
Lemma p3b_live_rp : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p a n,
  relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> live_at L1 A1 p a n -> 0 < n -> ~ F' a ->
  live_at L2 A2 p a n.
Proof using.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p a n RP [H1 E1] Hn HF.
  destruct RP as (_ & _ & _ & _ & _ & AD & SV & _). rewrite <- E1 in HF.
  assert (H2 : In (p, n) (user_blocks A2)) by exact (SV p n H1 Hn HF).
  split; [exact H2|]. rewrite (AD p n H1 H2 HF). exact E1.
Qed.

(* A live block other than the freed one stays live at the same address. *)
Lemma p3b_live_free : forall L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 p q a n,
  call_post Bm MR L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 ->
  (forall q' k, In (q', k) (user_blocks A1) -> q' <> p -> In (q', k) (user_blocks A2)) ->
  live_at L1 A1 q a n -> a <> ptr_addr L1 p -> live_at L2 A2 q a n.
Proof using.
  intros L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 p q a n CP SURV [H1 E1] Hne.
  pose proof CP as (_ & _ & _ & _ & AD & _).
  assert (H2 : In (q, n) (user_blocks A2)) by (apply SURV; [exact H1 | intros ->; exact (Hne (eq_sym E1))]).
  split; [exact H2|]. rewrite (AD q n H1 H2). exact E1.
Qed.

Section Run.
Variable RFm : ResFormT.
Hypothesis GEC : gesture_end_contract Bm API RFm.
Hypothesis FRC : free_contract_rt Bm API RFm.
Hypothesis FNC : free_null_contract Bm.

Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (bnd : rt_R RFm) (ks : list (Z * list byte * list byte)) (HP KH : Z) (O junk : list byte)
  (cl br dd ei : Z) (mx nout cap out ev : word) (qS kS : Z).

Local Notation S0 := (bv_unsigned (getr regs 2)).
Local Notation SA := (bv_unsigned (getr regs 10)).
Local Notation NH := (Z.of_nat (length ks)).
Local Notation TOT := (keys_total ks).
Local Notation ERR := (errno_addr Bm).
Local Notation NO := (bv_unsigned nout).
Local Notation CAP := (bv_unsigned cap).
Local Notation OUT := (bv_unsigned out).
Local Notation live := (send_live cl br dd (keys_total ks)).
Local Notation EE := (gestures_writes (send_live cl br dd (keys_total ks)) (bv_unsigned out) (bv_unsigned cap)
  (bv_unsigned (getr regs 10))).
Local Notation FF := (fun q : Z => (send_live cl br dd (keys_total ks) = true /\ q = bv_unsigned out) \/ q = HP \/
  In q (map key_addr ks)).
(* The statement's trace of the whole run and its final g_out. *)
Local Notation GTR := (gestures_end_tr (send_live cl br dd (keys_total ks)) (bv_unsigned mx) (bv_unsigned nout)
  (bv_unsigned cap) (key_runs (known_at L A) ks) HP KH 0 (known_at L A (bv_unsigned out)) (known_at L A HP)).
Local Notation GOUT := (gestures_end_out (send_live cl br dd (keys_total ks)) (bv_unsigned mx) (bv_unsigned nout)
  (bv_unsigned cap) (key_runs (known_at L A) ks) 0 (known_at L A (bv_unsigned out))).

Hypothesis PRE : call_pre_k Bm MR GESTURES_END_K L A regs mem md.
Hypothesis INIT : st_init_done A = true.
Hypothesis TPE : ms_tp Bm + ERRNO_OFF = ERR.
Hypothesis EAL : ERR mod 4 = 0.
Hypothesis EHI : G_RELAY_HI <= ERR.
Hypothesis RO0 : ro_agree segs mem.
Hypothesis GRP : forall a, G_RELAY_LO <= a < G_RELAY_HI -> img_plain Bm a.
Hypothesis GCP : forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a.
Hypothesis GEI : forall a, ERR <= a < ERR + 4 -> in_img Bm a.
Hypothesis G5P : forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain Bm a.
Hypothesis SAB : In (qS, kS) (blocks L A) /\ fresh_block Bm qS kS /\ qS <= SA /\ SA + 56 <= qS + kS /\
  qS <> OUT /\ qS <> HP /\ ~ In qS (map key_addr ks).
Hypothesis SAM : SA mod 8 = 0.
Hypothesis HS0 : rw_cells segs mem (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)].
Hypothesis NHB : NH < 2 ^ 31 - 1.
Hypothesis HPD : (HP = 0 /\ ks = []) \/
  (In (HP, KH) (blocks L A) /\ fresh_block Bm HP KH /\ 8 * NH <= KH /\ 8 <= KH /\ HP <> OUT /\
   ~ In HP (map key_addr ks) /\ bytes_at segs mem HP (key_ptrs ks)).
Hypothesis NDK : NoDup (map key_addr ks).
Hypothesis KF : Forall (fun k =>
  In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A) /\
  fresh_block Bm (key_addr k) (Z.of_nat (length (key_text k)) + 1) /\
  bytes_at segs mem (key_addr k) (key_text k ++ Z_to_bv 8 0 :: key_slack k) /\
  ~ In (Z_to_bv 8 0) (key_text k) /\ 1 <= Z.of_nat (length (key_text k)) <= 6000 /\
  (- (key_addr k + Z.of_nat (length (key_text k)) + 1)) mod 8 <= Z.of_nat (length (key_slack k)) /\
  key_addr k <> OUT) ks.
Hypothesis Hcl : cl = 3 \/ cl = -1.
Hypothesis Hbr : br = 0 \/ br = 1.
Hypothesis Hdd : dd = 0 \/ dd = 1.
Hypothesis Hei : ei = 0 \/ ei = 1.
Hypothesis CCL : rw_cells segs mem G_CLIENT [C4 (Z_to_bv 64 cl)].
Hypothesis CBR : rw_cells segs mem G_BROKEN [C1 (Z_to_bv 8 br)].
Hypothesis CDD : rw_cells segs mem G_DEAD [C1 (Z_to_bv 8 dd)].
Hypothesis CEI : rw_cells segs mem G_EINTR [C1 (Z_to_bv 8 ei)].
Hypothesis COUT : rw_cells segs mem G_OUTV [C8 mx; C8 nout; C8 cap; C8 out].
Hypothesis CERR : rw_cells segs mem ERR [C4 ev].
Hypothesis OUTD : (CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
  (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L A) /\ fresh_block Bm OUT CAP /\
   bytes_at segs mem OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO).
Hypothesis MGQ : 2 * (NO + TOT) < 2 ^ 63.
Hypothesis RES0 : rt_ok RFm A bnd.
Hypothesis ROOM : forall qs, length qs = nretF GTR -> roomF RFm qs bnd GTR.

Definition NOf (ks1 : list (Z * list byte * list byte)) : Z := if live then NO + keys_total ks1 else NO.
Definition Of (ks1 : list (Z * list byte * list byte)) : list byte := if live then O ++ keys_out ks1 else O.
Definition brf (ks1 : list (Z * list byte * list byte)) : Z := if send_off cl br (keys_total ks1) then br else dd.
Definition eif (ks1 : list (Z * list byte * list byte)) : Z := if send_off cl br (keys_total ks1) then ei else 0.
Definition rval (r i : Z) : word :=
  if r =? 2 then Z_to_bv 64 (S0 + -32) else if r =? 8 then Z_to_bv 64 SA else if r =? 9 then Z_to_bv 64 (8 * i)
  else if r =? 18 then Z_to_bv 64 i else getr regs (Z_to_bv 5 r).
Definition RF (R : bvmap 5 word) (i : Z) : Prop := forall r, callee_saved r -> getr R (Z_to_bv 5 r) = rval r i.
Definition RFx (R : bvmap 5 word) : Prop :=
  forall r, callee_saved r -> r <> 9 -> r <> 18 -> getr R (Z_to_bv 5 r) = rval r 0.

Definition OUTP (ks1 : list (Z * list byte * list byte)) (m1 : word -> option byte) (OUT1 CAP1 : Z)
    (junk1 : list byte) : Prop :=
  (CAP1 = 0 /\ OUT1 = 0 /\ NOf ks1 = 0 /\ Of ks1 = []) \/
  (0 < CAP1 /\ NOf ks1 <= CAP1 /\ fresh_block Bm OUT1 CAP1 /\ bytes_at segs m1 OUT1 (Of ks1 ++ junk1) /\
   Z.of_nat (length (Of ks1)) = NOf ks1 /\ Z.of_nat (length junk1) = CAP1 - NOf ks1).

Definition GLB (ks1 : list (Z * list byte * list byte)) (m1 : word -> option byte) : Prop :=
  rw_cells segs m1 G_CLIENT [C4 (Z_to_bv 64 cl)] /\ rw_cells segs m1 G_BROKEN [C1 (Z_to_bv 8 (brf ks1))] /\
  rw_cells segs m1 G_DEAD [C1 (Z_to_bv 8 dd)] /\ rw_cells segs m1 G_EINTR [C1 (Z_to_bv 8 (eif ks1))] /\
  (exists ev1, rw_cells segs m1 ERR [C4 ev1]).

Definition CNT (OUT1 CAP1 : Z) (junk1 : list byte) : Prop :=
  live = false -> OUT1 = OUT /\ CAP1 = CAP /\ junk1 = junk.

(* free (s->held) at the end of the run. *)
Definition held_tr : trF := if HP =? 0 then [] else [RFree KH (known_at L A HP)].

(* The requests of ending the held keys ks2 from g_nout = no, g_capout = c, from base j with g_out at o, then
   free (s->held); and the final g_capout and g_out. *)
Definition kr (ks2 : list (Z * list byte * list byte)) (no c : Z) (j : nat) (o : adrF) : trF * (Z * adrF) :=
  (fst (keys_end_run live (bv_unsigned mx) no c (key_runs (known_at L A) ks2) j o) ++ held_tr,
   snd (keys_end_run live (bv_unsigned mx) no c (key_runs (known_at L A) ks2) j o)).

(* The resource state after the requests tp made so far, which returned qd, with g_out at o1; and the requests
   rr (length qd) o1 still to come: together the whole trace of gestures_end, with its final g_capout and g_out.
   The current buffer, the held keys still to end and the held array are live at the blocks the trace names. *)
Definition RSt (L1 : layout) (A1 : astate) (OUT1 CAP1 : Z) (ks2 : list (Z * list byte * list byte))
    (rr : nat -> adrF -> trF * (Z * adrF)) : Prop :=
  exists tp qd o1, length qd = nretF tp /\
    (forall post, runF RFm (qd ++ post) bnd tp = runF RFm qd bnd tp) /\
    rt_ok RFm A1 (runF RFm qd bnd tp) /\
    tp ++ fst (rr (length qd) o1) = GTR /\
    (live = true -> fst (snd (rr (length qd) o1)) = gestures_end_cap live (bv_unsigned mx) NO CAP (key_lens ks)) /\
    snd (snd (rr (length qd) o1)) = GOUT /\
    p3b_inr (length qd) o1 /\
    (0 < CAP1 -> live_at L1 A1 (resolveF qd o1) OUT1 CAP1) /\
    Forall (fun k => live_at L1 A1 (sptr_of L A (key_addr k)) (key_addr k) (klen k + 1)) ks2 /\
    (HP <> 0 -> live_at L1 A1 (sptr_of L A HP) HP KH).

Definition Jg (ks1 ks2 ksd : list (Z * list byte * list byte)) (L1 : layout) (A1 : astate)
    (m1 : word -> option byte) (md1 : Model) (rr : nat -> adrF -> trF * (Z * adrF)) (OUT1 CAP1 : Z)
    (junk1 : list byte) : Prop :=
  ks = ks1 ++ ks2 /\
  chain GESTURES_END_K EE FF L A regs mem md L1 A1 m1 md1 /\
  st_init_done A1 = true /\
  RSt L1 A1 OUT1 CAP1 ks2 rr /\
  CNT OUT1 CAP1 junk1 /\
  ro_agree segs m1 /\
  rw_cells segs m1 (S0 + -32) [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] /\
  rw_cells segs m1 (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)] /\
  (HP <> 0 -> In (HP, KH) (blocks L1 A1) /\ bytes_at segs m1 HP (key_ptrs ks)) /\
  Forall (fun k => In (key_addr k, klen k + 1) (blocks L1 A1) /\
                   bytes_at segs m1 (key_addr k) (key_text k ++ [Z_to_bv 8 0])) ks2 /\
  (forall q m, In (q, m) (blocks L1 A1) <->
     ((In (q, m) (blocks L A) /\ q <> OUT /\ ~ In q (map key_addr ks1)) \/ (0 < CAP1 /\ q = OUT1 /\ m = CAP1))) /\
  (forall q m, In (q, m) (blocks L A) -> q <> OUT -> ~ In q (map key_addr ks1) -> 0 < m -> q <> OUT1) /\
  rw_cells segs m1 G_OUTV [C8 mx; C8 (Z_to_bv 64 (NOf ksd)); C8 (Z_to_bv 64 CAP1); C8 (Z_to_bv 64 OUT1)] /\
  OUTP ksd m1 OUT1 CAP1 junk1 /\
  GLB ksd m1.

Definition JE (L2 : layout) (A2 : astate) (R2 : bvmap 5 word) (m2 : word -> option byte) (md2 : Model)
    (OUTf CAPf : Z) (junkf : list byte) : Prop :=
  chain GESTURES_END_K EE FF L A regs mem md L2 A2 m2 md2 /\
  st_init_done A2 = true /\
  (exists qs, length qs = nretF GTR /\ rt_ok RFm A2 (runF RFm qs bnd GTR) /\
     (live = true -> live_at L2 A2 (resolveF qs GOUT) OUTf CAPf)) /\
  CNT OUTf CAPf junkf /\
  (live = true -> CAPf = gestures_end_cap live (bv_unsigned mx) NO CAP (key_lens ks)) /\
  ro_agree segs m2 /\
  RFx R2 /\
  rw_cells segs m2 (S0 + -32) [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] /\
  rw_cells segs m2 (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)] /\
  In (qS, kS) (blocks L2 A2) /\
  (forall q m, In (q, m) (blocks L2 A2) <->
     ((In (q, m) (blocks L A) /\ q <> OUT /\ q <> HP /\ ~ In q (map key_addr ks)) \/
      (0 < CAPf /\ q = OUTf /\ m = CAPf))) /\
  (forall q m, In (q, m) (blocks L A) -> q <> OUT -> q <> HP -> ~ In q (map key_addr ks) -> 0 < m -> q <> OUTf) /\
  rw_cells segs m2 G_OUTV [C8 mx; C8 (Z_to_bv 64 (NOf ks)); C8 (Z_to_bv 64 CAPf); C8 (Z_to_bv 64 OUTf)] /\
  OUTP ks m2 OUTf CAPf junkf /\
  GLB ks m2.

Definition GPOST (c' : config) : Prop :=
  exists L' A' regs' mem' md' (OUT' CAP' : Z) (junk' : list byte),
    c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    relay_post Bm API GESTURES_END_K EE FF L A regs mem md L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF GTR /\ rt_ok RFm A' (runF RFm qs bnd GTR) /\
       (live = true -> live_at L' A' (resolveF qs GOUT) OUT' CAP')) /\
    ro_agree segs mem' /\
    rw_cells segs mem' (SA + 40) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
    rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
    rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 (if send_off cl br TOT then br else dd))] /\
    rw_cells segs mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
    rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 (if send_off cl br TOT then ei else 0))] /\
    (exists ev'', rw_cells segs mem' ERR [C4 ev'']) /\
    (forall q m, In (q, m) (blocks L' A') <->
       ((In (q, m) (blocks L A) /\ q <> OUT /\ q <> HP /\ ~ In q (map key_addr ks)) \/
        (live = true /\ q = OUT' /\ m = CAP') \/
        (live = false /\ 0 < CAP /\ q = OUT /\ m = CAP))) /\
    (live = false -> rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out]) /\
    (live = true ->
       NO + TOT <= CAP' /\ CAP' = gestures_end_cap live (bv_unsigned mx) NO CAP (key_lens ks) /\
       fresh_block Bm OUT' CAP' /\
       (forall q m, In (q, m) (blocks L A) -> q <> OUT -> q <> HP -> ~ In q (map key_addr ks) -> 0 < m -> q <> OUT') /\
       bytes_at segs mem' OUT' (O ++ keys_out ks ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - TOT /\
       rw_cells segs mem' G_OUTV
         [C8 mx; C8 (Z_to_bv 64 (NO + TOT)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]).

Lemma sab_sep : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> in_img Bm a) -> qS + kS <= lo \/ hi <= qS.
Proof using O SAB junk.
  intros lo hi Hlh Hi. destruct SAB as (_ & SF & SL1 & SL2 & _).
  apply (fresh_sep qS kS lo hi SF ltac:(lia) Hlh Hi).
Qed.

Lemma pre_facts : MR L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (getr regs 1) /\ S0 mod 16 = 0 /\
  YM05.alloc_ceiling + 8416 <= S0 /\ S0 < 2 ^ 63 /\ (forall a, S0 - 8416 <= a < S0 -> writable_at segs mem a) /\
  getr regs 4 = Z_to_bv 64 (ms_tp Bm) /\ (forall a, ERR <= a < ERR + 4 -> writable_at segs mem a).
Proof using PRE.
  destruct PRE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. exact H10.
Qed.

Lemma rp_getr : forall R R', regs_preserved R R' -> forall r, callee_saved r -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).
Proof using. intros R R' H r Hr. exact (H r Hr). Qed.

Lemma RF_pres : forall R R' i, RF R i -> regs_preserved R R' -> RF R' i.
Proof using. intros R R' i H P r Hr. rewrite (rp_getr R R' P r Hr). exact (H r Hr). Qed.

Lemma epi : forall L2 A2 R2 m2 md2 OUTf CAPf junkf,
  JE L2 A2 R2 m2 md2 OUTf CAPf junkf ->
  SR segs (mkCfg (YK11.mkst R2 (Z_to_bv 64 0x132b4) m2 (seg_rom segs)) md2) GPOST.
Proof using AXg EAL EHI GCP GEI GRP HPD OUTD PRE ROOM SAB SAM SEGS.
  intros L2 A2 R2 m2 md2 OUTf CAPf junkf
    (CH & IN2 & RS2 & LV0 & CAPE & RO2 & RF2 & FRC2 & SAC2 & QIN & BLK & FRS & COV & OUTD2 &
     (CCL2 & CBR2 & CDD2 & CEI2 & (ev2 & CER2))).
  pose proof pre_facts as (HM0 & HW0 & HB0 & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof (proj1 CH) as M2. destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M2) as (Hh & Hl & _).
  pose proof SAB as (SQ & (SF1 & SF2 & SF3) & SL1 & SL2 & SO & SH & SK).
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RS. change (bv_modulus 64) with (2 ^ 64) in RS.
  pose proof (keys_total_nonneg ks) as TN.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst2, mkR_of_getr.
    assert (G2 : getr R2 2 = Z_to_bv 64 (S0 + -32))
      by exact (RF2 2 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
    assert (G8 : getr R2 8 = Z_to_bv 64 SA) by exact (RF2 8 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
    rewrite G2, G8. rewrite SEGS.
    pose proof FRC2 as F'. rewrite SEGS in F'. pose proof SAC2 as H'. rewrite SEGS in H'.
    eapply ge_segE; [exact F' | exact H' | lia | lia | lia]. }
  intros ms3 (can3 & (m3 & -> & MU3 & WM3 & SAC3 & FRC3) & EQ3).
  destruct (eqv_mkst2 _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3).
  rewrite (ret_pc_of_ok2 _ HRA).
  apply SR_ret. unfold GPOST.
  assert (WM3' : wmono segs m2 m3) by (rewrite SEGS; exact WM3).
  assert (DJ : forall c n, (forall a, c <= a < c + n -> in_img Bm a) -> 0 < n ->
             disjoint_from [(SA + 40, SA + 52)] c n).
  { intros c n Hi Hn. destruct (sab_sep c (c + n) ltac:(lia) Hi) as [D|D]; cbn; split; [lia | exact I | lia | exact I]. }
  assert (DJR : disjoint_from [(SA + 40, SA + 52)] G_RELAY_LO (G_RELAY_HI - G_RELAY_LO)).
  { apply DJ; [intros a Ha; apply GRP; lia | unfold G_RELAY_LO, G_RELAY_HI; lia]. }
  cbn [disjoint_from] in DJR.
  assert (TR : forall c cs, rw_cells segs m2 c cs -> G_RELAY_LO <= c -> c + Z.of_nat (cells_size cs) <= G_RELAY_HI ->
             rw_cells segs m3 c cs).
  { intros c cs Hc H1 H2. apply (rw_cells_transport segs _ m2 m3 c cs Hc MU3 WM3'). cbn. split; [lia | exact I]. }
  exists L2, A2, R3, m3, md2, OUTf, CAPf, junkf.
  split; [rewrite SEGS; reflexivity|].
  split.
  { apply relay_of_chain.
    - eapply chain_mem; [exact AXg | exact CH | exact MU3 | exact WM3' |].
      intros a Ha. destruct (Z_le_gt_dec (SA + 40) a) as [D1|D1]; [destruct (Z_lt_ge_dec a (SA + 52)) as [D2|D2]|].
      + right. right. split; [unfold gestures_writes; right; lia|]. exists qS, kS. split; [exact QIN | lia].
      + left. cbn. split; [lia | exact I].
      + left. cbn. split; [lia | exact I].
    - intros r Hr. change (getr R3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)). revert r Hr. rgx_all X3 RF2. }
  split; [exact IN2|].
  split; [exact RS2|].
  split.
  { apply (ro_agree_munch1 m2 m3 (SA + 40) (SA + 52) RO2 MU3). intros x Hx.
    apply ro_false_noimg; [lia|]. replace (bv_unsigned x) with (qS + (bv_unsigned x - qS)) by lia. apply SF3. lia. }
  split; [rewrite SEGS; exact SAC3|].
  split.
  { apply (rw_cells_transport segs _ m2 m3 _ _ CCL2 MU3 WM3').
    apply DJ; [intros a Ha; exact (proj1 (GCP a Ha)) | cbn; lia]. }
  split; [apply TR; [exact CBR2 | unfold G_BROKEN, G_RELAY_LO; lia | cbn; unfold G_BROKEN, G_RELAY_HI; lia]|].
  split; [apply TR; [exact CDD2 | unfold G_DEAD, G_RELAY_LO; lia | cbn; unfold G_DEAD, G_RELAY_HI; lia]|].
  split; [apply TR; [exact CEI2 | unfold G_EINTR, G_RELAY_LO; lia | cbn; unfold G_EINTR, G_RELAY_HI; lia]|].
  split.
  { exists ev2. apply (rw_cells_transport segs _ m2 m3 _ _ CER2 MU3 WM3').
    apply DJ; [intros a Ha; apply GEI; exact Ha | cbn; lia]. }
  assert (CP : live = true -> 0 < CAPf).
  { intros LV. pose proof (live_tot _ _ _ _ TN LV) as TP.
    destruct OUTD2 as [(_ & _ & E & _)|(Hc & _)]; [|exact Hc].
    unfold NOf in E. rewrite LV in E. pose proof (bv_unsigned_in_range 64 nout). lia. }
  split.
  { intros q m. rewrite BLK. destruct live eqn:LV.
    - pose proof (CP eq_refl) as Cp. split.
      + intros [H|(_ & H)]; [left; exact H | right; left; auto].
      + intros [H|[(_ & H)|(H & _)]]; [left; exact H | right; auto | discriminate].
    - destruct (LV0 LV) as (-> & -> & _). split.
      + intros [H|H]; [left; exact H | right; right; auto].
      + intros [H|[(H & _)|(_ & H)]]; [left; exact H | discriminate | right; exact H]. }
  assert (COV3 : rw_cells segs m3 G_OUTV [C8 mx; C8 (Z_to_bv 64 (NOf ks)); C8 (Z_to_bv 64 CAPf); C8 (Z_to_bv 64 OUTf)])
    by (apply TR; [exact COV | unfold G_OUTV, G_RELAY_LO; lia | cbn; unfold G_OUTV, G_RELAY_HI; lia]).
  split.
  { intros LV. destruct (LV0 LV) as (-> & -> & ->).
    unfold NOf in COV3. rewrite LV in COV3. rewrite !Z_to_bv_bv_unsigned in COV3. exact COV3. }
  intros LV. pose proof (CP LV) as Cp.
  destruct OUTD2 as [(Hc & _)|(_ & HN & HF & HB & HLO & HLJ)]; [lia|].
  unfold NOf, Of in *. rewrite LV in *.
  split; [lia|]. split; [exact (CAPE eq_refl)|]. split; [exact HF|]. split; [exact FRS|].
  split.
  { rewrite <- app_assoc in HB. apply (bytes_at_transport segs _ m2 m3 _ _ HB MU3).
    assert (IO : In (OUTf, CAPf) (blocks L2 A2)) by (apply BLK; right; auto).
    assert (NE : qS <> OUTf) by (apply (FRS qS kS); [exact SQ | exact SO | exact SH | exact SK | lia]).
    rewrite !length_app in HLO.
    destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M2 QIN IO NE) as [D|D];
      cbn [disjoint_from]; rewrite !length_app; (split; [|exact I]); lia. }
  split; [lia|]. exact COV3.
Qed.

Lemma RFx_pres : forall R R', RFx R -> regs_preserved R R' -> RFx R'.
Proof using. intros R R' H P r Hr H9 H18. rewrite (rp_getr R R' P r Hr). exact (H r Hr H9 H18). Qed.

Lemma rval_ne : forall r i j, r <> 9 -> r <> 18 -> rval r i = rval r j.
Proof using.
  intros r i j H9 H18. unfold rval. rewrite (proj2 (Z.eqb_neq r 9) H9), (proj2 (Z.eqb_neq r 18) H18). reflexivity.
Qed.

Lemma RF_RFx : forall R i, RF R i -> RFx R.
Proof using. intros R i H r Hr H9 H18. rewrite (H r Hr). apply rval_ne; assumption. Qed.

Lemma gfacts : YM05.alloc_ceiling + 8416 <= S0 /\ S0 < 2 ^ 63 /\ S0 mod 16 = 0 /\ 2 ^ 46 <= YM05.alloc_ceiling /\
  YM05.alloc_ceiling < 2 ^ 47 /\ 4096 <= qS /\ qS <= SA /\ SA + 56 <= qS + kS /\ qS + kS <= YM05.alloc_ceiling /\
  G_RELAY_HI <= ERR /\ ERR + 4 <= 2 ^ 21 /\ GESTURES_END_K = 8416 /\ GESTURE_END_K = 8384.
Proof using EHI GEI PRE SAB SEGS.
  pose proof pre_facts as (_ & _ & _ & _ & HAL & HCEIL & H63 & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof SAB as (_ & (SF1 & SF2 & _) & SL1 & SL2 & _). hide_ors.
  pose proof (in_img_low2 _ (GEI (ERR + 3) ltac:(lia))) as EL.
  unfold GESTURES_END_K, GESTURES_END_FRAME, GESTURE_END_K, GESTURE_END_FRAME, SEND_LINE_K, SEND_LINE_FRAME,
    REALLOC_STACK, ALLOC_STACK.
  repeat split; lia.
Qed.

Lemma NOf_nonneg : forall ks1, 0 <= NOf ks1.
Proof using Bm ROOM regs.
  intros ks1. hide_ors. pose proof (keys_total_nonneg ks1). pose proof (bv_unsigned_in_range 64 nout) as RN.
  unfold NOf. destruct live; lia.
Qed.

Lemma NOf_live : forall ks1, live = true -> NOf ks1 = NO + keys_total ks1.
Proof using. intros ks1 LV. unfold NOf. rewrite LV. reflexivity. Qed.

Lemma NOf_dead : forall ks1, live = false -> NOf ks1 = NO.
Proof using. intros ks1 LV. unfold NOf. rewrite LV. reflexivity. Qed.

Lemma Of_live : forall ks1, live = true -> Of ks1 = O ++ keys_out ks1.
Proof using. intros ks1 LV. unfold Of. rewrite LV. reflexivity. Qed.

Lemma Of_dead : forall ks1, live = false -> Of ks1 = O.
Proof using. intros ks1 LV. unfold Of. rewrite LV. reflexivity. Qed.

Lemma NOf_nil : NOf [] = NO.
Proof using ROOM. unfold NOf. change (keys_total []) with 0. rewrite Z.add_0_r. destruct live; reflexivity. Qed.

Lemma Of_nil : Of [] = O.
Proof using ROOM. unfold Of. change (keys_out []) with (@nil byte). rewrite app_nil_r. destruct live; reflexivity. Qed.

Lemma brf_nil : brf [] = br.
Proof using. unfold brf, send_off. change (keys_total []) with 0. rewrite Z.eqb_refl, orb_true_r. reflexivity. Qed.

Lemma eif_nil : eif [] = ei.
Proof using. unfold eif, send_off. change (keys_total []) with 0. rewrite Z.eqb_refl, orb_true_r. reflexivity. Qed.

Lemma chain_refl : chain GESTURES_END_K EE FF L A regs mem md L A mem md.
Proof using EHI GEI PRE SAB SEGS.
  pose proof pre_facts as (HM0 & HW0 & HB0 & _ & _ & _ & _ & HWS & _ & HERR).
  pose proof gfacts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GK & _). hide_ors.
  split; [exact HM0|]. split; [exact HW0|]. split; [exact HB0|].
  split; [apply layout_le_refl|]. split; [lia|].
  split; [intros; reflexivity|].
  split; [intros p n H _ _; exact H|].
  split; [intros p H; split; [exact H | reflexivity]|].
  split; [intros a _ H; exact H|].
  split; [exists (m_vmmaps md); apply vm_self|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|].
  intros a [Ha|Ha]; [apply HWS; change (spZ regs) with S0 in Ha; rewrite GK in Ha; lia | apply HERR; exact Ha].
Qed.

Lemma free_img : forall L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 c cs,
  MR L1 A1 m1 md1 -> call_post Bm MR L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 ->
  (forall a, E' a -> ~ in_img Bm a) -> YM05.alloc_ceiling <= spZ R1 - ALLOC_STACK ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_plain Bm (c + i)) ->
  rw_cells segs m1 c cs -> rw_cells segs m2 c cs.
Proof using AXg EHI GEI PRE SAB SEGS.
  intros L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 c cs M1 CP HE HSc HPl HC.
  pose proof gfacts as (_ & _ & _ & F4 & _). hide_ors.
  apply (img_cells_free L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 c cs AXg M1 CP); [|exact HC].
  intros i Hi. pose proof (HPl i Hi) as P. pose proof P as (Pi & _ & _ & Pe). pose proof (in_img_low2 _ Pi).
  split; [exact P|]. split; [intros X; exact (HE _ X Pi)|].
  unfold scratch. intros [X|X]; [lia | exact (Pe X)].
Qed.

Lemma free_err : forall L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2,
  call_post Bm MR L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 -> exists v, rw_cells segs m2 ERR [C4 v].
Proof using EHI GEI PRE SAB SEGS.
  intros L1 A1 R1 m1 md1 E' L2 A2 R2 m2 md2 CP. pose proof CP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SW).
  pose proof gfacts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F10 & F11 & _). unfold G_RELAY_HI in F10. hide_ors.
  destruct (err_cells m2 ERR ltac:(lia) ltac:(lia)) as [v Hv].
  { intros i Hi. rewrite <- SEGS. apply SW. right. lia. }
  exists v. rewrite SEGS. exact Hv.
Qed.

Lemma ge_tr_nof : forall ks1 c x j o,
  gesture_end_tr live (bv_unsigned mx) (NOf ks1) c x j o =
  gesture_end_tr live (bv_unsigned mx) (NO + keys_total ks1) c x j o.
Proof using ROOM. intros ks1 c x j o. unfold NOf. destruct live; reflexivity. Qed.

Lemma ge_out_nof : forall ks1 c x j o,
  gesture_end_out live (bv_unsigned mx) (NOf ks1) c x j o =
  gesture_end_out live (bv_unsigned mx) (NO + keys_total ks1) c x j o.
Proof using ROOM. intros ks1 c x j o. unfold NOf. destruct live; reflexivity. Qed.

Lemma ge_cap_nof : forall ks1 c x,
  gesture_end_cap live (bv_unsigned mx) (NOf ks1) c x = gesture_end_cap live (bv_unsigned mx) (NO + keys_total ks1) c x.
Proof using ROOM. intros ks1 c x. unfold NOf. destruct live; reflexivity. Qed.

Lemma ge_cap_dead : live = false -> forall no c x, gesture_end_cap live (bv_unsigned mx) no c x = c.
Proof using. intros LV no c x. rewrite LV. reflexivity. Qed.

(* The requests after gesture_end (k): free (k), then the keys ks2 and the held array. *)
Definition krk (k : Z * list byte * list byte) (ks2 : list (Z * list byte * list byte)) (no c : Z) (j : nat)
    (o : adrF) : trF * (Z * adrF) :=
  (RFree (Z.of_nat (length (key_text k)) + 1) (known_at L A (key_addr k)) :: fst (kr ks2 no c j o),
   snd (kr ks2 no c j o)).

Lemma kr_cons : forall k ks2 no c j o,
  kr (k :: ks2) no c j o =
  (gesture_end_tr live (bv_unsigned mx) no c (Z.of_nat (length (key_text k))) j o ++
     fst (krk k ks2 (no + Z.of_nat (length (key_text k)) + 5)
            (gesture_end_cap live (bv_unsigned mx) no c (Z.of_nat (length (key_text k))))
            (j + nretF (gesture_end_tr live (bv_unsigned mx) no c (Z.of_nat (length (key_text k))) j o))
            (gesture_end_out live (bv_unsigned mx) no c (Z.of_nat (length (key_text k))) j o)),
   snd (krk k ks2 (no + Z.of_nat (length (key_text k)) + 5)
          (gesture_end_cap live (bv_unsigned mx) no c (Z.of_nat (length (key_text k))))
          (j + nretF (gesture_end_tr live (bv_unsigned mx) no c (Z.of_nat (length (key_text k))) j o))
          (gesture_end_out live (bv_unsigned mx) no c (Z.of_nat (length (key_text k))) j o))).
Proof using.
  intros k ks2 no c j o. unfold krk, kr, key_runs. cbn [map keys_end_run fst snd]. rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma kr_nil : forall no c j o, kr [] no c j o = (held_tr, (c, o)).
Proof using. reflexivity. Qed.

Lemma held_tr_0 : HP = 0 -> held_tr = [].
Proof using. intros H. unfold held_tr. rewrite H. reflexivity. Qed.

Lemma held_tr_n : HP <> 0 -> held_tr = [RFree KH (known_at L A HP)].
Proof using. intros H. unfold held_tr. rewrite (proj2 (Z.eqb_neq HP 0) H). reflexivity. Qed.

Lemma ge_step : forall ks1 k ks2 L1 A1 R1 m1 md1 OUT1 CAP1 junk1,
  Jg ks1 (k :: ks2) ks1 L1 A1 m1 md1 (kr (k :: ks2) (NO + keys_total ks1) CAP1) OUT1 CAP1 junk1 ->
  RF R1 (Z.of_nat (length ks1)) ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13234) m1 (seg_rom segs)) md1)
    (fun c => exists L2 A2 R2 m2 md2 OUT2 CAP2 junk2,
       c = mkCfg (YK11.mkst R2 (Z_to_bv 64 0x13268) m2 (seg_rom segs)) md2 /\
       Jg ks1 (k :: ks2) (ks1 ++ [k]) L2 A2 m2 md2
         (krk k ks2 (NO + keys_total (ks1 ++ [k])) CAP2) OUT2 CAP2 junk2 /\
       RF R2 (Z.of_nat (length ks1))).
Proof using EAL EHI G5P GCP GEC GEI GRP HPD Hbr Hcl Hdd Hei KF NDK NODUP PRE ROOM SAB SAM SEGS SLACK TPE.
  intros ks1 k ks2 L1 A1 R1 m1 md1 OUT1 CAP1 junk1 JJ RF1.
  pose proof JJ as (EKS & CH & IN1 & RS1 & CN0 & RO1 & FR1 & SA1 & HP1 & KS1 & BI1 & FO1 & COV1 & OP1 &
    (CCL1 & CBR1 & CDD1 & CEI1 & (ev1 & CER1))).
  pose proof pre_facts as (HM0 & HW0 & HB0 & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & GK & GK').
  pose proof CH as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW1).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  pose proof (NODUP _ _ _ _ M1) as ND1.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RS. change (bv_modulus 64) with (2 ^ 64) in RS.
  pose proof (bv_unsigned_in_range 64 nout) as RNO. change (bv_modulus 64) with (2 ^ 64) in RNO.
  pose proof (keys_total_nonneg ks1) as KT1. pose proof (keys_total_nonneg ks2) as KT2.
  pose proof (NOf_nonneg ks1) as NN1. hide_ors.
  assert (LKS : NH = Z.of_nat (length ks1) + 1 + Z.of_nat (length ks2))
    by (rewrite EKS, length_app; cbn [length]; lia).
  assert (KIN : In k ks) by (rewrite EKS; apply in_or_app; right; left; reflexivity).
  destruct (proj1 (Forall_forall _ _) KF k KIN) as (KB0 & KFR & KBY0 & KNZ & KLEN & KSLK & KNO).
  pose proof KFR as (KF1 & KF2 & KF3).
  pose proof (Forall_inv KS1) as (KB1 & KBY1). pose proof (Forall_inv_tail KS1) as KS2.
  assert (NDL : List.NoDup (map key_addr (ks1 ++ k :: ks2)))
    by (rewrite <- EKS; apply NoDup_ListNoDup; exact NDK).
  rewrite map_app in NDL. cbn [map] in NDL.
  assert (NDL2 : List.NoDup ((map key_addr ks1 ++ [key_addr k]) ++ map key_addr ks2))
    by (rewrite <- app_assoc; exact NDL).
  assert (KNI1 : ~ In (key_addr k) (map key_addr ks1)) by (apply (nodup_split _ _ _ NDL); left; reflexivity).
  assert (KSNE : ks <> []) by (rewrite EKS; destruct ks1; discriminate).
  pose proof (keys_total_pos ks KSNE) as TOTP.
  assert (ETOT : TOT = keys_total ks1 + (klen k + 5) + keys_total ks2)
    by (rewrite EKS, keys_total_app, keys_total_cons; lia).
  unfold klen in ETOT.
  assert (NOFLE : NOf ks1 <= NO + keys_total ks1) by (unfold NOf; destruct live; lia).
  assert (NKS1 : forall q, ~ In q (map key_addr ks) -> ~ In q (map key_addr ks1)).
  { intros q H X. apply H. rewrite EKS, map_app. apply in_or_app. left. exact X. }
  assert (HPn : HP <> 0)
    by (destruct HPD as [(HZ & EZ)|(_ & (HQ1 & _) & _)]; [exfalso; exact (KSNE EZ) | lia]).
  destruct HPD as [(HZ & _)|(HPB0 & HPF & HK1 & HK2 & HPO & HPK & HPBY0)]; [exfalso; exact (HPn HZ)|].
  pose proof HPF as (HPF1 & HPF2 & HPF3). pose proof (blk_al L A mem md HP KH HM0 HPB0) as HP8.
  destruct (HP1 HPn) as (HPB1 & HPBY1).
  pose proof HPBY1 as HPBY1'. rewrite EKS in HPBY1'.
  pose proof (key_slice segs m1 HP ks1 k ks2 HPBY1') as KSL.
  assert (QO : forall q m, In (q, m) (blocks L A) -> q <> OUT -> ~ In q (map key_addr ks1) ->
             In (q, m) (blocks L1 A1) -> q <> OUT1).
  { intros q m Hq H1 H2 Hq1 E. destruct (Z_lt_le_dec 0 m) as [Mp|Mn].
    - exact (FO1 q m Hq H1 H2 Mp E).
    - destruct OP1 as [(C0 & O0 & _)|(Cp & _)].
      + destruct (blk_lo L A mem md q m HM0 Hq) as [Q1 _]. lia.
      + assert (INO : In (OUT1, CAP1) (blocks L1 A1)) by (apply BI1; right; auto).
        subst q. pose proof (nodup_fst _ OUT1 m CAP1 ND1 Hq1 INO). lia. }
  assert (KNE : key_addr k <> OUT1) by exact (QO _ _ KB0 KNO KNI1 KB1).
  assert (RNG : 0 <= CAP1 /\ 0 <= OUT1 /\ OUT1 + CAP1 <= YM05.alloc_ceiling /\ NOf ks1 <= CAP1 /\
                Z.of_nat (length (Of ks1)) = NOf ks1).
  { destruct OP1 as [(C0 & O0 & N0 & OE)|(Cp & NL & (FQ1 & FQ2 & _) & _ & LO & _)].
    - rewrite OE. cbn [length Z.of_nat]. lia.
    - lia. }
  destruct RNG as (RN1 & RN2 & RN3 & RN4 & LOf1).
  assert (G2 : getr R1 2 = Z_to_bv 64 (S0 + -32)) by exact (RF1 2 ltac:(unfold callee_saved; lia)).
  assert (G4 : getr R1 4 = getr regs 4) by exact (RF1 4 ltac:(unfold callee_saved; lia)).
  assert (G8 : getr R1 8 = Z_to_bv 64 SA) by exact (RF1 8 ltac:(unfold callee_saved; lia)).
  assert (G9 : getr R1 9 = Z_to_bv 64 (8 * Z.of_nat (length ks1))) by exact (RF1 9 ltac:(unfold callee_saved; lia)).
  pose proof SA1 as SA1'. rewrite SEGS in SA1'. pose proof KSL as KSL'. rewrite SEGS in KSL'.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst2, mkR_of_getr, G8, G9, SEGS.
    eapply ge_segG; [exact SA1' | exact KSL' | lia | lia | exact HP8 | lia | lia]. }
  intros ms1 (can1 & (a1' & a2' & a3' & ->) & EQ1).
  destruct (eqv_mkst2 _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1' & -> & X1).
  assert (E1_1 : getr R1' 1 = Z_to_bv 64 0x13268) by geq X1.
  assert (E1_2 : getr R1' 2 = Z_to_bv 64 (S0 + -32)) by (transitivity (getr R1 2); [geq X1 | exact G2]).
  assert (E1_4 : getr R1' 4 = getr regs 4) by (transitivity (getr R1 4); [geq X1 | exact G4]).
  assert (E1_10 : getr R1' 10 = Z_to_bv 64 (key_addr k)) by geq X1.
  assert (RF1' : RF R1' (Z.of_nat (length ks1))) by (unfold RF; rgx_all X1 RF1).
  assert (U2 : bv_unsigned (getr R1' 2) = S0 + -32) by (rewrite E1_2; apply unsigned_lit; lia).
  assert (U2s : spZ R1' = S0 + -32) by exact U2.
  assert (U10 : bv_unsigned (getr R1' 10) = key_addr k) by (rewrite E1_10; apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (NOf ks1)) = NOf ks1) by (apply unsigned_lit; lia).
  assert (UC : bv_unsigned (Z_to_bv 64 CAP1) = CAP1) by (apply unsigned_lit; lia).
  assert (UO : bv_unsigned (Z_to_bv 64 OUT1) = OUT1) by (apply unsigned_lit; lia).
  destruct (slack_bytes L1 A1 m1 md1 (key_addr k) (klen k) SLACK M1 KB1 ltac:(lia) ltac:(unfold klen; lia)
              ltac:(unfold klen; lia)) as (sl & LSL & SLB).
  assert (LVE : send_live cl (brf ks1) dd (Z.of_nat (length (key_text k)) + 5) = live).
  { unfold brf. apply live_step2; [exact Hcl | exact Hbr | exact Hdd | lia | lia]. }
  assert (EKT : keys_total (ks1 ++ [k]) = keys_total ks1 + (Z.of_nat (length (key_text k)) + 5)).
  { rewrite keys_total_app. change (keys_total [k]) with (Z.of_nat (length (key_text k)) + 5 + 0). lia. }
  assert (EBR : brf (ks1 ++ [k]) =
                (if send_off cl (brf ks1) (Z.of_nat (length (key_text k)) + 5) then brf ks1 else dd)).
  { unfold brf. rewrite EKT. symmetry. apply br_step2; [exact Hcl | exact Hbr | exact Hdd | lia | lia]. }
  assert (EEI : eif (ks1 ++ [k]) =
                (if send_off cl (brf ks1) (Z.of_nat (length (key_text k)) + 5) then eif ks1 else 0)).
  { unfold eif, brf. rewrite EKT. symmetry. apply ei_step2; [exact Hcl | exact Hbr | exact Hdd | lia | lia]. }
  destruct RS1 as (tp & qd & o1 & RL & RIND & ROK & RT3 & RT4 & RT5 & RIN & RLO & RLK & RLH).
  rewrite kr_cons in RT3, RT4, RT5. cbn [fst snd] in RT3, RT4, RT5.
  unfold runF, run_tr in RIND.
  assert (RES1 : forall post, CAP1 <> 0 -> resolveF (qd ++ post) o1 = sptr_of L1 A1 OUT1).
  { intros post Hc. rewrite (p3b_inr_app qd post o1 RIN). symmetry.
    apply (p3b_sptr_of_eq L1 A1 _ OUT1 CAP1 ND1). apply RLO. lia. }
  pose proof GEC as G. unfold gesture_end_contract in G.
  specialize (G L1 A1 R1' m1 md1 (runF RFm qd bnd tp) (key_text k) sl (Of ks1) junk1 cl (brf ks1) dd (eif ks1) mx
                (Z_to_bv 64 (NOf ks1)) (Z_to_bv 64 CAP1) (Z_to_bv 64 OUT1) ev1).
  cbv zeta in G. rewrite U2, U10, UN, UC, UO, E1_1 in G.
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  eapply SR_bind.
  { apply G.
    - exact SEGS.
    - split; [exact M1|]. split; [exact W1|]. split; [exact B1|].
      split; [exact (eq_ind_r YK0s.ret_ok ret_ok_13268 E1_1)|].
      rewrite U2s.
      split; [clear - F3; Z.div_mod_to_equations; lia|].
      split; [rewrite GK'; lia|].
      split; [lia|].
      split; [intros a Ha; apply SW1; unfold scratch_k; left; change (spZ regs) with S0; rewrite GK;
              rewrite GK' in Ha; lia|].
      split; [exact (eq_trans E1_4 HTP)|].
      split; [intros a Ha; apply SW1; unfold scratch_k; right; exact Ha|].
      intros X. rewrite IN1 in X. discriminate.
    - exact IN1.
    - exact TPE.
    - exact EAL.
    - exact EHI.
    - exact RO1.
    - change (key_text k ++ Z_to_bv 8 0 :: sl) with (key_text k ++ [Z_to_bv 8 0] ++ sl). rewrite app_assoc.
      apply bytes_at_app. split; [exact KBY1|].
      rewrite length_app. cbn [length].
      replace (key_addr k + Z.of_nat (length (key_text k) + 1)) with (key_addr k + klen k + 1) by (unfold klen; lia).
      exact SLB.
    - exact KNZ.
    - unfold klen in LSL. lia.
    - lia.
    - destruct (fresh_sep (key_addr k) (klen k + 1) G_RELAY_LO G_RELAY_HI KFR ltac:(unfold klen; lia)
                  ltac:(unfold G_RELAY_LO, G_RELAY_HI; lia) (fun a Ha => proj1 (GRP a Ha))) as [D|D];
        [left; unfold klen in D; lia | right; exact D].
    - destruct (fresh_sep (key_addr k) (klen k + 1) ERR (ERR + 4) KFR ltac:(unfold klen; lia) ltac:(lia) GEI)
        as [D|D]; [left; unfold klen in D; lia | right; exact D].
    - left. rewrite GK'. lia.
    - exact GRP.
    - exact GCP.
    - exact GEI.
    - exact G5P.
    - exists (key_addr k), (klen k + 1). split; [exact KB1|]. split; [exact KFR|]. split; [lia|].
      split; [unfold klen; lia | exact KNE].
    - exact Hcl.
    - unfold brf. destruct (send_off cl br (keys_total ks1)); [exact Hbr | exact Hdd].
    - exact Hdd.
    - unfold eif. destruct (send_off cl br (keys_total ks1)); [exact Hei | left; reflexivity].
    - exact CCL1.
    - exact CBR1.
    - exact CDD1.
    - exact CEI1.
    - exact COV1.
    - exact CER1.
    - destruct OP1 as [(C0 & O0 & N0 & OE)|(Cp & NL & FRO & OB & LO & LJ)].
      + left. exact (conj C0 (conj O0 (conj N0 OE))).
      + right. assert (INO : In (OUT1, CAP1) (blocks L1 A1)) by (apply BI1; right; auto).
        split; [exact Cp|]. split; [exact NL|]. split; [exact INO|]. split; [exact FRO|]. split; [exact OB|].
        split; [exact LO|]. split; [exact LJ|].
        destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 KB1 INO KNE) as [D|D];
          [left; unfold klen in D; lia | right; lia].
    - lia.
    - exact ROK.
    - rewrite LVE, ge_tr_nof. intros qc Hqc.
      set (pad := repeat (SP 0 0) (nretF GTR - length qd - length qc)).
      assert (EN : nretF (gesture_end_tr live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k)))
                            (length qd) o1) = length qc) by (rewrite Hqc; apply p3b_ge_shape).
      assert (LQ : length (qd ++ qc ++ pad) = nretF GTR).
      { unfold pad. rewrite !length_app, repeat_length. rewrite <- RT3, !nret_app, EN. lia. }
      pose proof (ROOM _ LQ) as RQ. rewrite <- RT3 in RQ. unfold roomF, room_run in RQ. rewrite !room_from_app in RQ.
      destruct RQ as (_ & RQ & _). rewrite RIND, Nat.add_0_l, <- RL in RQ.
      destruct (p3b_ge_sim RFm live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k)))
                  (qd ++ qc ++ pad) qc (length qd) 0 o1 (known_at L1 A1 OUT1) (runF RFm qd bnd tp)) as (_ & S2 & _).
      { intros i Hi. rewrite app_nth2 by lia. replace (length qd + i - length qd)%nat with i by lia.
        apply app_nth1. lia. }
      { intros Hc. rewrite (RES1 (qc ++ pad) Hc). reflexivity. }
      rewrite !Nat.add_0_r in S2. exact (proj1 S2 RQ). }
  intros c2 (L2 & A2 & R2 & m2 & md2 & OUT' & CAP' & junk' & -> & RP2 & INI2 & RS2 & RO2 & XB2 & CCL2 &
    CBR2 & CDD2 & CEI2 & NL2 & LV2).
  rewrite LVE in RP2, NL2, LV2, RS2.
  rewrite <- EBR in CBR2. rewrite <- EEI in CEI2.
  rewrite ge_tr_nof, ge_out_nof in RS2.
  destruct RS2 as (qc & LQC & ROK2 & RLK2).
  assert (EN : nretF (gesture_end_tr live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k)))
                        (length qd) o1) = length qc) by (rewrite LQC; apply p3b_ge_shape).
  assert (SIMR : forall post,
    p3b_rn RFm (qd ++ qc ++ post) (p3b_rn RFm qd bnd 0 tp) (length qd)
      (gesture_end_tr live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k))) (length qd) o1) =
    p3b_rn RFm qc (p3b_rn RFm qd bnd 0 tp) 0
      (gesture_end_tr live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k))) 0
         (known_at L1 A1 OUT1)) /\
    (gesture_end_cap live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k))) <> 0 ->
     resolveF (qd ++ qc ++ post)
       (gesture_end_out live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k))) (length qd) o1) =
     resolveF qc
       (gesture_end_out live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k))) 0
          (known_at L1 A1 OUT1)))).
  { intros post.
    destruct (p3b_ge_sim RFm live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k)))
                (qd ++ qc ++ post) qc (length qd) 0 o1 (known_at L1 A1 OUT1) (p3b_rn RFm qd bnd 0 tp)) as (S1 & _ & S3).
    { intros i Hi. rewrite app_nth2 by lia. replace (length qd + i - length qd)%nat with i by lia.
      apply app_nth1. lia. }
    { intros Hc. rewrite (RES1 (qc ++ post) Hc). reflexivity. }
    rewrite !Nat.add_0_r in S1, S3. split; [exact S1 | exact S3]. }
  assert (RSN : forall C2 OUT2, C2 = gesture_end_cap live (bv_unsigned mx) (NO + keys_total ks1) CAP1
                                       (Z.of_nat (length (key_text k))) ->
            (0 < C2 -> live_at L2 A2 (resolveF (qd ++ qc)
               (gesture_end_out live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k)))
                  (length qd) o1)) OUT2 C2) ->
            Forall (fun k0 => live_at L2 A2 (sptr_of L A (key_addr k0)) (key_addr k0) (klen k0 + 1)) (k :: ks2) ->
            (HP <> 0 -> live_at L2 A2 (sptr_of L A HP) HP KH) ->
            RSt L2 A2 OUT2 C2 (k :: ks2) (krk k ks2 (NO + keys_total (ks1 ++ [k])) C2)).
  { intros C2 OUT2 EC2 LK2 KL2 HL2. subst C2. unfold RSt.
    exists (tp ++ gesture_end_tr live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k)))
                    (length qd) o1), (qd ++ qc),
      (gesture_end_out live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k))) (length qd) o1).
    assert (LQD : length (qd ++ qc) = (length qd + nretF (gesture_end_tr live (bv_unsigned mx) (NO + keys_total ks1)
                    CAP1 (Z.of_nat (length (key_text k))) (length qd) o1))%nat) by (rewrite length_app, EN; reflexivity).
    assert (RUN : forall post, p3b_rn RFm ((qd ++ qc) ++ post) bnd 0 (tp ++ gesture_end_tr live (bv_unsigned mx)
                    (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k))) (length qd) o1) =
                  p3b_rn RFm qc (p3b_rn RFm qd bnd 0 tp) 0 (gesture_end_tr live (bv_unsigned mx) (NO + keys_total ks1)
                    CAP1 (Z.of_nat (length (key_text k))) 0 (known_at L1 A1 OUT1))).
    { intros post. rewrite run_from_app, <- app_assoc, RIND, Nat.add_0_l, <- RL. exact (proj1 (SIMR post)). }
    split; [rewrite LQD, nret_app, RL; reflexivity|].
    split.
    { intros post. unfold runF, run_tr. rewrite (RUN post).
      rewrite <- (app_nil_r (qd ++ qc)), (RUN []). reflexivity. }
    split.
    { unfold runF, run_tr. rewrite <- (app_nil_r (qd ++ qc)), (RUN []). exact ROK2. }
    rewrite LQD, EKT.
    replace (NO + (keys_total ks1 + (Z.of_nat (length (key_text k)) + 5)))
      with (NO + keys_total ks1 + Z.of_nat (length (key_text k)) + 5) by lia.
    split; [rewrite <- app_assoc; exact RT3|].
    split; [exact RT4|]. split; [exact RT5|].
    split.
    { destruct (p3b_ge_out live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k)))
                  (length qd) o1) as [E|(i & E & Hi)]; rewrite E;
        [apply (p3b_inr_le (length qd)); [lia | exact RIN] | cbn; lia]. }
    split; [exact LK2|]. split; [exact KL2 | exact HL2]. }
  pose proof RP2 as (M2 & W2 & B2 & _ & _ & AD2 & SV2 & Z2 & IO2 & RPr2 & VM2 & FR2' & BY2 & SW2).
  pose proof (RF_pres R1' R2 _ RF1' RPr2) as RF2.
  pose proof (NODUP _ _ _ _ M2) as ND2.
  apply SR_ret.
  assert (NEh : forall a, YM05.alloc_ceiling <= a -> ~ send_writes live OUT1 CAP1 a).
  { intros a Ha. unfold send_writes, G_BROKEN, G_EINTR, G_OUTV. intros [X|[X|[X|(_ & X)]]]; lia. }
  assert (KEEP : forall q m, In (q, m) (blocks L1 A1) -> 0 < m -> (forall i, 0 <= i < m -> ~ in_img Bm (q + i)) ->
             (live = true -> q <> OUT1) ->
             In (q, m) (blocks L2 A2) /\ (forall i, 0 <= i < m -> mbyte segs m2 (q + i) = mbyte segs m1 (q + i))).
  { intros q m Hq Hm NI HO.
    apply (ge_keeps GESTURE_END_K live OUT1 CAP1 L1 A1 R1' m1 md1 L2 A2 R2 m2 md2 q m
             (fun a Ha => proj1 (GRP a Ha)) M1 RP2 Hq Hm NI).
    intros LVt. split; [exact (HO LVt)|]. intros Cp. apply BI1. right. auto. }
  assert (CH2 : chain GESTURES_END_K EE FF L A regs mem md L2 A2 m2 md2).
  { eapply chain_ge; [exact HW0 | exact CH | exact RP2 | | | | ].
    - intros a [Ha|Ha]; [left | right; exact Ha]. rewrite U2s, GK' in Ha. change (spZ regs) with S0. rewrite GK.
      lia.
    - intros a [Ha|Ha] Hn; [| exfalso; apply Hn; right; exact Ha].
      change (spZ regs) with S0 in Ha. rewrite GK in Ha.
      assert (X : ~ (S0 + -32 - 8384 <= a < S0 + -32))
        by (intros X; apply Hn; left; rewrite U2s, GK'; exact X).
      lia.
    - intros a Ha. unfold send_writes in Ha.
      destruct Ha as [Ha|[Ha|[Ha|(_ & Ha)]]].
      + split; [unfold G_BROKEN in Ha; lia | intros _; left; left; exact Ha].
      + split; [unfold G_EINTR in Ha; lia | intros _; left; right; left; exact Ha].
      + split; [unfold G_OUTV in Ha; lia | intros _; left; right; right; left; exact Ha].
      + destruct OP1 as [(C0 & _)|(_ & _ & (FQ1 & FQ2 & FQ3) & _)]; [lia|].
        split; [lia|]. intros Hi. exfalso. apply (FQ3 (a - OUT1)); [lia|].
        replace (OUT1 + (a - OUT1)) with a by lia. exact Hi.
    - intros p n Hp Hp1 NF.
      assert (QB : In (ptr_addr L p, n) (blocks L A))
        by (apply blocks_In2; exists p; split; [reflexivity | exact Hp]).
      destruct (in_chain _ _ _ L A regs mem md L1 A1 m1 md1 p n HW0 CH Hp NF) as [_ EA1].
      assert (QB1 : In (ptr_addr L p, n) (blocks L1 A1))
        by (apply blocks_In2; exists p; split; [exact EA1 | exact Hp1]).
      assert (NQ : live = true -> ptr_addr L p <> OUT1).
      { intros LVt. apply (QO _ n QB); [intros E; apply NF; left; split; [exact LVt | exact E] | | exact QB1].
        intros X. apply NF. right. right. rewrite EKS, map_app. apply in_or_app. left. exact X. }
      split; [intros (LVt & E); exact (NQ LVt E)|].
      intros i Hi NE Hs. apply NE. unfold gestures_writes, send_writes. unfold send_writes in Hs.
      destruct Hs as [Hs|[Hs|[Hs|(LVt & Hs)]]];
        [left; left; exact Hs | left; right; left; exact Hs | left; right; right; left; exact Hs |].
      exfalso. assert (INO : In (OUT1, CAP1) (blocks L1 A1)) by (apply BI1; right; split; [lia | auto]).
      destruct (blocks_disjoint Bm API _ _ _ _ _ _ _ _ M1 QB1 INO (NQ LVt)); lia. }
  assert (FR2 : rw_cells segs m2 (S0 + -32) [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (high_cells_ge GESTURE_END_K (send_writes live OUT1 CAP1) (fun q => live = true /\ q = OUT1)
             L1 A1 R1' m1 md1 L2 A2 R2 m2 md2 _ _ M1 RP2); [|exact FR1].
    intros i Hi. cbn in Hi. split; [lia|]. split; [|apply NEh; lia].
    unfold scratch_k. rewrite U2s, GK'. intros [X|X]; lia. }
  pose proof SAB as (SQ & SFR & SL1 & SL2 & SO & SH & SK).
  assert (QSB1 : In (qS, kS) (blocks L1 A1))
    by (apply BI1; left; split; [exact SQ|]; split; [exact SO | exact (NKS1 _ SK)]).
  destruct (KEEP qS kS QSB1 ltac:(lia) (proj2 (proj2 SFR)) (fun _ => QO qS kS SQ SO (NKS1 _ SK) QSB1))
    as (QSB2 & QSM).
  assert (SA2 : rw_cells segs m2 (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)]).
  { apply (cells_in_block L2 A2 m1 m2 md2 qS kS); [exact M2 | exact QSB2 | lia | cbn; lia | exact QSM | exact SA1]. }
  assert (HPO1 : HP <> OUT1) by exact (QO HP KH HPB0 HPO (NKS1 _ HPK) HPB1).
  destruct (KEEP HP KH HPB1 ltac:(lia) HPF3 (fun _ => HPO1)) as (HPB2 & HPM).
  destruct (KEEP (key_addr k) (klen k + 1) KB1 ltac:(unfold klen; lia) KF3 (fun _ => KNE)) as (KB2 & _).
  assert (KS2' : Forall (fun k0 => In (key_addr k0, klen k0 + 1) (blocks L2 A2) /\
                   bytes_at segs m2 (key_addr k0) (key_text k0 ++ [Z_to_bv 8 0])) ks2).
  { apply Forall_forall. intros k' Hk'.
    destruct (proj1 (Forall_forall _ _) KS2 k' Hk') as (KB1' & KBY1').
    assert (KIN' : In k' ks) by (rewrite EKS; apply in_or_app; right; right; exact Hk').
    destruct (proj1 (Forall_forall _ _) KF k' KIN') as (KB0' & (KF1' & KF2' & KF3') & _ & _ & _ & _ & KNO').
    assert (NI' : ~ In (key_addr k') (map key_addr ks1 ++ [key_addr k]))
      by (apply (nodup_split _ _ _ NDL2); apply in_map; exact Hk').
    assert (NI1' : ~ In (key_addr k') (map key_addr ks1)) by (intros X; apply NI'; apply in_or_app; left; exact X).
    destruct (KEEP (key_addr k') (klen k' + 1) KB1' ltac:(unfold klen; lia) KF3'
                (fun _ => QO _ _ KB0' KNO' NI1' KB1')) as (KB2' & KM').
    split; [exact KB2'|].
    apply (bytes_in_block (key_addr k') (klen k' + 1) m1 m2);
      [lia | rewrite length_app; cbn [length]; unfold klen; lia | exact KM' | exact KBY1']. }
  assert (HPBY2 : bytes_at segs m2 HP (key_ptrs ks))
    by (apply (bytes_in_block HP KH m1 m2); [lia | rewrite key_ptrs_length; lia | exact HPM | exact HPBY1]).
  assert (KL2 : Forall (fun k0 => live_at L2 A2 (sptr_of L A (key_addr k0)) (key_addr k0) (klen k0 + 1)) (k :: ks2)).
  { constructor.
    - apply (p3b_live_rp _ _ _ L1 A1 R1' m1 md1 L2 A2 R2 m2 md2 _ _ _ RP2 (Forall_inv RLK)); [unfold klen; lia|].
      intros (_ & E). exact (KNE E).
    - apply Forall_forall. intros k' Hk'.
      pose proof (proj1 (Forall_forall _ _) (Forall_inv_tail RLK) k' Hk') as LK'. cbv beta in LK'.
      destruct (proj1 (Forall_forall _ _) KS2 k' Hk') as (KB1' & _).
      assert (KIN' : In k' ks) by (rewrite EKS; apply in_or_app; right; right; exact Hk').
      destruct (proj1 (Forall_forall _ _) KF k' KIN') as (KB0' & _ & _ & _ & _ & _ & KNO').
      assert (NI' : ~ In (key_addr k') (map key_addr ks1 ++ [key_addr k]))
        by (apply (nodup_split _ _ _ NDL2); apply in_map; exact Hk').
      assert (NI1' : ~ In (key_addr k') (map key_addr ks1)) by (intros X; apply NI'; apply in_or_app; left; exact X).
      apply (p3b_live_rp _ _ _ L1 A1 R1' m1 md1 L2 A2 R2 m2 md2 _ _ _ RP2 LK'); [unfold klen; lia|].
      intros (_ & E). exact (QO _ _ KB0' KNO' NI1' KB1' E). }
  assert (HL2 : HP <> 0 -> live_at L2 A2 (sptr_of L A HP) HP KH).
  { intros _. apply (p3b_live_rp _ _ _ L1 A1 R1' m1 md1 L2 A2 R2 m2 md2 _ _ _ RP2 (RLH HPn)); [lia|].
    intros (_ & E). exact (HPO1 E). }
  destruct (Bool.bool_dec live true) as [LV|LV].
  - destruct (LV2 LV) as (NLE & ECAP & FR3 & (ev2 & CER2) & FRS2 & (b1 & b2 & c1 & c2 & EB2 & EC & EB1) & OB2 & LJ2 &
      COV2). hide_ors.
    assert (ENO : NOf (ks1 ++ [k]) = NOf ks1 + (Z.of_nat (length (key_text k)) + 5))
      by (rewrite !NOf_live by exact LV; rewrite EKT; lia).
    assert (EOf : Of (ks1 ++ [k]) = Of ks1 ++ key_text k ++ END5)
      by (rewrite !Of_live by exact LV; rewrite keys_out_app, keys_out_one, <- !app_assoc; reflexivity).
    exists L2, A2, R2, m2, md2, OUT', CAP', junk'.
    split; [reflexivity|]. split; [|exact RF2].
    split; [exact EKS|]. split; [exact CH2|]. split; [exact INI2|].
    assert (LK2 : 0 < CAP' -> live_at L2 A2 (resolveF (qd ++ qc)
               (gesture_end_out live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k)))
                  (length qd) o1)) OUT' CAP').
    { intros Cp. rewrite <- (app_nil_r (qd ++ qc)), <- app_assoc.
      rewrite (proj2 (SIMR []) ltac:(rewrite <- ge_cap_nof, <- ECAP; lia)). exact (RLK2 LV). }
    split; [exact (RSN CAP' OUT' (eq_trans ECAP (ge_cap_nof ks1 _ _)) LK2 KL2 HL2)|].
    split; [intros LF; rewrite LV in LF; discriminate|].
    split; [exact RO2|]. split; [exact FR2|]. split; [exact SA2|].
    split; [intros _; split; [exact HPB2 | exact HPBY2]|].
    split; [constructor; [split; [exact KB2 | exact XB2] | exact KS2']|].
    split.
    { intros q m. rewrite EB2. split.
      - intros H. apply in_mid_iff in H. destruct H as [H|E].
        + rewrite EC in H.
          assert (H' : In (q, m) (blocks L1 A1) /\ (0 < CAP1 -> q <> OUT1)).
          { destruct EB1 as [(C0 & E1)|(Cp & E1)].
            - rewrite <- E1 in H. split; [exact H | intros; lia].
            - pose proof (rm_in _ b1 b2 (OUT1, CAP1) (q, m) ND1 E1) as R. cbn [fst] in R.
              apply R in H. destruct H as [H1 H2]. split; [exact H1 | intros _; exact H2]. }
          destruct H' as [H1 H2]. apply BI1 in H1.
          destruct H1 as [H1|(Cp & E1 & _)]; [left; exact H1 | exfalso; exact (H2 Cp E1)].
        + right. injection E as E1 E2. subst q m. split; [lia | split; reflexivity].
      - intros [H|(Cp & -> & ->)].
        + apply in_mid_iff. left. rewrite EC.
          destruct H as (Hq & H1 & H2).
          assert (Hq1 : In (q, m) (blocks L1 A1)) by (apply BI1; left; split; [exact Hq|]; split; [exact H1 | exact H2]).
          destruct EB1 as [(C0 & E1)|(Cp & E1)]; [rewrite <- E1; exact Hq1|].
          apply (rm_in _ b1 b2 (OUT1, CAP1) (q, m) ND1 E1). split; [exact Hq1|]. cbn [fst].
          exact (QO q m Hq H1 H2 Hq1).
        + apply in_mid_iff. right. reflexivity. }
    split.
    { intros q m Hq H1 H2 Hm.
      assert (Hq1 : In (q, m) (blocks L1 A1)) by (apply BI1; left; split; [exact Hq|]; split; [exact H1 | exact H2]).
      exact (FRS2 q m Hq1 (QO q m Hq H1 H2 Hq1) Hm). }
    split; [rewrite ENO; exact COV2|].
    split.
    { right. rewrite ENO, EOf. split; [lia|]. split; [lia|]. split; [exact FR3|].
      split; [rewrite <- !app_assoc; exact OB2|].
      split; [rewrite !length_app; change (length END5) with 5%nat; lia | lia]. }
    split; [exact CCL2|]. split; [exact CBR2|]. split; [exact CDD2|]. split; [exact CEI2|].
    exists ev2. exact CER2.
  - apply Bool.not_true_is_false in LV.
    destruct (NL2 LV) as (EBL & CER2 & COV2).
    destruct (CN0 LV) as (EO1 & EC1 & EJ1).
    assert (ENO : NOf (ks1 ++ [k]) = NOf ks1) by (rewrite !NOf_dead by exact LV; reflexivity).
    assert (EOf : Of (ks1 ++ [k]) = Of ks1) by (rewrite !Of_dead by exact LV; reflexivity).
    exists L2, A2, R2, m2, md2, OUT1, CAP1, junk1.
    split; [reflexivity|]. split; [|exact RF2].
    split; [exact EKS|]. split; [exact CH2|]. split; [exact INI2|].
    assert (LK2 : 0 < CAP1 -> live_at L2 A2 (resolveF (qd ++ qc)
               (gesture_end_out live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k)))
                  (length qd) o1)) OUT1 CAP1).
    { intros Cp.
      replace (gesture_end_out live (bv_unsigned mx) (NO + keys_total ks1) CAP1 (Z.of_nat (length (key_text k)))
                 (length qd) o1) with o1 by (rewrite LV; reflexivity).
      rewrite (p3b_inr_app qd qc o1 RIN).
      apply (p3b_live_rp _ _ _ L1 A1 R1' m1 md1 L2 A2 R2 m2 md2 _ OUT1 CAP1 RP2 (RLO Cp) Cp).
      intros (LT & _). rewrite LV in LT. discriminate. }
    split; [exact (RSN CAP1 OUT1 (eq_sym (ge_cap_dead LV _ _ _)) LK2 KL2 HL2)|].
    split; [intros _; exact (conj EO1 (conj EC1 EJ1))|].
    split; [exact RO2|]. split; [exact FR2|]. split; [exact SA2|].
    split; [intros _; split; [exact HPB2 | exact HPBY2]|].
    split; [constructor; [split; [exact KB2 | exact XB2] | exact KS2']|].
    split; [intros q m; rewrite EBL; exact (BI1 q m)|].
    split; [exact FO1|].
    split; [rewrite ENO; exact COV2|].
    split.
    { unfold OUTP. rewrite ENO, EOf.
      destruct OP1 as [H|(Cp & NL & FRO & OB & LO & LJ)]; [left; exact H | right].
      pose proof FRO as (FQ1 & FQ2 & FQ3).
      assert (HO : live = true -> OUT1 <> OUT1) by (intros LT; rewrite LV in LT; discriminate).
      destruct (KEEP OUT1 CAP1 ltac:(apply BI1; right; auto) Cp FQ3 HO) as (_ & OM).
      split; [exact Cp|]. split; [exact NL|]. split; [exact FRO|].
      split; [apply (bytes_in_block OUT1 CAP1 m1 m2); [lia | rewrite length_app; lia | exact OM | exact OB]|].
      split; [exact LO | exact LJ]. }
    split; [exact CCL2|]. split; [exact CBR2|]. split; [exact CDD2|]. split; [exact CEI2|].
    eexists. exact CER2.
Qed.

Lemma fr_step : forall ks1 k ks2 L2 A2 R2 m2 md2 OUT2 CAP2 junk2,
  Jg ks1 (k :: ks2) (ks1 ++ [k]) L2 A2 m2 md2
    (krk k ks2 (NO + keys_total (ks1 ++ [k])) CAP2) OUT2 CAP2 junk2 ->
  RF R2 (Z.of_nat (length ks1)) ->
  SR segs (mkCfg (YK11.mkst R2 (Z_to_bv 64 0x13268) m2 (seg_rom segs)) md2)
    (fun c => exists L3 A3 R3 m3 md3,
       c = mkCfg (YK11.mkst R3 (Z_to_bv 64 (match ks2 with [] => 0x132ac | _ => 0x13234 end)) m3 (seg_rom segs)) md3 /\
       Jg (ks1 ++ [k]) ks2 (ks1 ++ [k]) L3 A3 m3 md3 (kr ks2 (NO + keys_total (ks1 ++ [k])) CAP2) OUT2 CAP2 junk2 /\
       RF R3 (Z.of_nat (length ks1) + 1)).
Proof using AXg CTXg EHI FRC FREEPC GCP GEI GRP HPD KF NDK NHB NODUP PRE SAB SAM SEGS.
  intros ks1 k ks2 L2 A2 R2 m2 md2 OUT2 CAP2 junk2 JJ RF2.
  pose proof JJ as (EKS & CH & IN2 & RS2 & CN2 & RO2 & FR2 & SA2 & HP2 & KS2 & BI2 & FO2 & COV2 & OP2 &
    (CCL2 & CBR2 & CDD2 & CEI2 & (ev2 & CER2))).
  pose proof pre_facts as (HM0 & HW0 & HB0 & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & GK & GK').
  pose proof CH as (M2 & W2 & B2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW2).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M2) as (Hh & Hl & _).
  pose proof (NODUP _ _ _ _ M2) as ND2.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RS. change (bv_modulus 64) with (2 ^ 64) in RS. hide_ors.
  assert (LKS : NH = Z.of_nat (length ks1) + 1 + Z.of_nat (length ks2))
    by (rewrite EKS, length_app; cbn [length]; lia).
  assert (KIN : In k ks) by (rewrite EKS; apply in_or_app; right; left; reflexivity).
  destruct (proj1 (Forall_forall _ _) KF k KIN) as (KB0 & KFR & KBY0 & KNZ & KLEN & KSLK & KNO).
  pose proof KFR as (KF1 & KF2 & KF3).
  pose proof (Forall_inv KS2) as (KB2 & _). pose proof (Forall_inv_tail KS2) as KS3.
  assert (NDL : List.NoDup (map key_addr (ks1 ++ k :: ks2)))
    by (rewrite <- EKS; apply NoDup_ListNoDup; exact NDK).
  rewrite map_app in NDL. cbn [map] in NDL.
  assert (NDL2 : List.NoDup ((map key_addr ks1 ++ [key_addr k]) ++ map key_addr ks2))
    by (rewrite <- app_assoc; exact NDL).
  assert (KNI1 : ~ In (key_addr k) (map key_addr ks1)) by (apply (nodup_split _ _ _ NDL); left; reflexivity).
  assert (KSNE : ks <> []) by (rewrite EKS; destruct ks1; discriminate).
  assert (NKS1 : forall q, ~ In q (map key_addr ks) -> ~ In q (map key_addr ks1)).
  { intros q H X. apply H. rewrite EKS, map_app. apply in_or_app. left. exact X. }
  assert (HPn : HP <> 0)
    by (destruct HPD as [(HZ & EZ)|(_ & (HQ1 & _) & _)]; [exfalso; exact (KSNE EZ) | lia]).
  destruct HPD as [(HZ & _)|(HPB0 & HPF & HK1 & HK2 & HPO & HPK & HPBY0)]; [exfalso; exact (HPn HZ)|].
  pose proof HPF as (HPF1 & HPF2 & HPF3). pose proof (blk_al L A mem md HP KH HM0 HPB0) as HP8.
  destruct (HP2 HPn) as (HPB2 & HPBY2).
  pose proof HPBY2 as HPBY2'. rewrite EKS in HPBY2'.
  pose proof (key_slice segs m2 HP ks1 k ks2 HPBY2') as KSL.
  assert (KO2 : key_addr k <> OUT2) by (apply (FO2 _ _ KB0 KNO KNI1); lia).
  assert (G2 : getr R2 2 = Z_to_bv 64 (S0 + -32)) by exact (RF2 2 ltac:(unfold callee_saved; lia)).
  assert (G4 : getr R2 4 = getr regs 4) by exact (RF2 4 ltac:(unfold callee_saved; lia)).
  assert (G8 : getr R2 8 = Z_to_bv 64 SA) by exact (RF2 8 ltac:(unfold callee_saved; lia)).
  assert (G9 : getr R2 9 = Z_to_bv 64 (8 * Z.of_nat (length ks1))) by exact (RF2 9 ltac:(unfold callee_saved; lia)).
  pose proof SA2 as SA2'. rewrite SEGS in SA2'. pose proof KSL as KSL'. rewrite SEGS in KSL'.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst2, mkR_of_getr, G8, G9, SEGS.
    eapply ge_segF; [exact SA2' | exact KSL' | lia | lia | exact HP8 | lia | lia]. }
  intros ms1 (can1 & (a1' & a2' & a3' & ->) & EQ1).
  destruct (eqv_mkst2 _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2' & -> & X2).
  assert (E2_1 : getr R2' 1 = Z_to_bv 64 0x1329c) by geq X2.
  assert (E2_2 : getr R2' 2 = Z_to_bv 64 (S0 + -32)) by (transitivity (getr R2 2); [geq X2 | exact G2]).
  assert (E2_4 : getr R2' 4 = getr regs 4) by (transitivity (getr R2 4); [geq X2 | exact G4]).
  assert (E2_10 : getr R2' 10 = Z_to_bv 64 (key_addr k)) by geq X2.
  assert (RF2' : RF R2' (Z.of_nat (length ks1))) by (unfold RF; rgx_all X2 RF2).
  assert (U2 : bv_unsigned (getr R2' 2) = S0 + -32) by (rewrite E2_2; apply unsigned_lit; lia).
  assert (U2s : spZ R2' = S0 + -32) by exact U2.
  destruct RS2 as (trp & qd & o1 & RL & RIND & ROK & RT3 & RT4 & RT5 & RIN & RLO & RLK & RLH).
  pose proof (Forall_inv RLK) as (Hp & Ep). set (p := sptr_of L A (key_addr k)) in *.
  pose proof FRC as FR. unfold free_contract_rt in FR. rewrite FREEPC in FR.
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  eapply SR_bind.
  { apply (FR L2 A2 R2' m2 md2 p (klen k + 1) (runF RFm qd bnd trp)).
    - split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
      split; [exact (eq_ind_r YK0s.ret_ok ret_ok_1329c E2_1)|].
      rewrite U2s.
      split; [clear - F3; Z.div_mod_to_equations; lia|].
      split; [unfold ALLOC_STACK; lia|].
      split; [lia|].
      split; [intros a Ha; apply SW2; unfold scratch_k; left; change (spZ regs) with S0; rewrite GK;
              unfold ALLOC_STACK in Ha; lia|].
      split; [exact (eq_trans E2_4 HTP)|].
      split; [intros a Ha; apply SW2; unfold scratch_k; right; exact Ha|].
      intros X. rewrite IN2 in X. discriminate.
    - exact RO2.
    - exact Hp.
    - rewrite Ep. exact E2_10.
    - exact ROK. }
  intros c3 (L3 & A3 & R3 & m3 & md3 & -> & CP3 & (b1 & b2 & EB2 & EB3) & BK & RO3 & GK3 & SURV & INI3 & LN3 & RS3).
  rewrite (E2_1 : YK11.getr R2' 1 = Z_to_bv 64 0x1329c). rewrite Ep in EB2, BK, CP3.
  pose proof CP3 as (M3 & W3 & B3 & LE3 & AD3 & RPr3 & VM3 & FR3 & BY3 & SW3).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M3) as (Hh3 & Hl3 & _).
  pose proof (RF_pres R2' R3 _ RF2' RPr3) as RF3.
  assert (H3_8 : getr R3 8 = Z_to_bv 64 SA) by exact (RF3 8 ltac:(unfold callee_saved; lia)).
  assert (H3_9 : getr R3 9 = Z_to_bv 64 (8 * Z.of_nat (length ks1))) by exact (RF3 9 ltac:(unfold callee_saved; lia)).
  assert (H3_18 : getr R3 18 = Z_to_bv 64 (Z.of_nat (length ks1))) by exact (RF3 18 ltac:(unfold callee_saved; lia)).
  assert (KEEPF : forall q m, In (q, m) (blocks L2 A2) -> q <> key_addr k ->
             In (q, m) (blocks L3 A3) /\ (forall i, 0 <= i < m -> mbyte segs m3 (q + i) = mbyte segs m2 (q + i))).
  { intros q m Hq Hne. exact (free_keeps L2 A2 m2 L3 A3 m3 (key_addr k) (klen k + 1) q m
                                (ex_intro _ b1 (ex_intro _ b2 (conj EB2 EB3))) BK Hq Hne). }
  assert (KNI : forall a, key_addr k <= a < key_addr k + (klen k + 1) -> ~ in_img Bm a).
  { intros a Ha Hi. apply (KF3 (a - key_addr k)); [unfold klen in Ha; lia|].
    replace (key_addr k + (a - key_addr k)) with a by lia. exact Hi. }
  assert (SPH : YM05.alloc_ceiling <= spZ R2' - ALLOC_STACK) by (rewrite U2s; unfold ALLOC_STACK; lia).
  assert (FI : forall c cs, (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_plain Bm (c + i)) ->
             rw_cells segs m2 c cs -> rw_cells segs m3 c cs)
    by (intros c cs H1 H2; exact (free_img L2 A2 R2' m2 md2 _ L3 A3 R3 m3 md3 c cs M2 CP3 KNI SPH H1 H2)).
  pose proof SAB as (SQ & SFR & SL1 & SL2 & SO & SH & SK).
  assert (QSB2 : In (qS, kS) (blocks L2 A2))
    by (apply BI2; left; split; [exact SQ|]; split; [exact SO | exact (NKS1 _ SK)]).
  assert (SKK : qS <> key_addr k) by (intros E; apply SK; rewrite E; apply in_map; exact KIN).
  destruct (KEEPF qS kS QSB2 SKK) as (QSB3 & QSM).
  assert (SA3 : rw_cells segs m3 (SA + 40) [C8 (Z_to_bv 64 HP); C4 (Z_to_bv 64 NH)]).
  { apply (cells_in_block L3 A3 m2 m3 md3 qS kS); [exact M3 | exact QSB3 | lia | cbn; lia | exact QSM | exact SA2]. }
  assert (J3 : Jg (ks1 ++ [k]) ks2 (ks1 ++ [k]) L3 A3 m3 md3 (kr ks2 (NO + keys_total (ks1 ++ [k])) CAP2)
                 OUT2 CAP2 junk2).
  { split; [rewrite EKS, <- app_assoc; reflexivity|].
    split.
    { eapply chain_free; [exact HW0 | exact HM0 | exact CTXg | exact AXg | exact CH | exact CP3 | exact LN3 |
                          exact SURV | exact Hp | unfold klen; lia | | | | ].
      - intros a [Ha|Ha]; [left | right; exact Ha]. rewrite U2s in Ha. change (spZ regs) with S0. rewrite GK.
        unfold ALLOC_STACK in Ha. lia.
      - intros a [Ha|Ha] Hn; [|exfalso; apply Hn; right; exact Ha]. change (spZ regs) with S0 in Ha.
        rewrite GK in Ha.
        assert (X : ~ (S0 + -32 - 8192 <= a < S0 + -32))
          by (intros X; apply Hn; left; rewrite U2s; unfold ALLOC_STACK; exact X).
        lia.
      - intros a Ha. cbv beta in Ha. split; [unfold klen in Ha; lia | exact (KNI a Ha)].
      - intros q n Hq Hq2 NF E. subst q.
        destruct (in_chain _ _ _ L A regs mem md L2 A2 m2 md2 p n HW0 CH Hq NF) as [_ EA].
        apply NF. right. right. rewrite <- EA, Ep. apply in_map. exact KIN. }
    split; [exact (INI3 IN2)|].
    split.
    { unfold RSt. exists (trp ++ [RFree (Z.of_nat (length (key_text k)) + 1) (known_at L A (key_addr k))]), qd, o1.
      split; [rewrite nret_app, p3b_nret_free, Nat.add_0_r; exact RL|].
      split.
      { intros post. unfold runF, run_tr in *. rewrite !run_from_app. cbn [run_from resolve known_at].
        rewrite RIND. reflexivity. }
      split; [unfold runF, run_tr; rewrite run_from_app; cbn [run_from resolve known_at]; exact RS3|].
      split; [rewrite <- app_assoc; exact RT3|].
      split; [exact RT4|]. split; [exact RT5|]. split; [exact RIN|].
      split.
      { intros Cp. apply (p3b_live_free L2 A2 R2' m2 md2 _ L3 A3 R3 m3 md3 p _ OUT2 CAP2 CP3 SURV (RLO Cp)).
        rewrite Ep. exact (fun E => KO2 (eq_sym E)). }
      split.
      { apply Forall_forall. intros k' Hk'.
        pose proof (proj1 (Forall_forall _ _) (Forall_inv_tail RLK) k' Hk') as LK'. cbv beta in LK'.
        apply (p3b_live_free L2 A2 R2' m2 md2 _ L3 A3 R3 m3 md3 p _ _ _ CP3 SURV LK'). rewrite Ep.
        assert (NI' : ~ In (key_addr k') (map key_addr ks1 ++ [key_addr k]))
          by (apply (nodup_split _ _ _ NDL2); apply in_map; exact Hk').
        intros E. apply NI'. rewrite E. apply in_or_app. right. left. reflexivity. }
      intros HPn'. apply (p3b_live_free L2 A2 R2' m2 md2 _ L3 A3 R3 m3 md3 p _ _ _ CP3 SURV (RLH HPn')). rewrite Ep.
      intros E. apply HPK. rewrite E. apply in_map. exact KIN. }
    split; [exact CN2|].
    split; [exact RO3|].
    split.
    { apply (high_cells_free L2 A2 R2' m2 md2 _ L3 A3 R3 m3 md3 _ _ M2 CP3); [|exact FR2].
      intros i Hi. cbn in Hi. split; [lia|]. split.
      - unfold scratch. rewrite U2s. unfold ALLOC_STACK. intros [X|X]; lia.
      - cbv beta. unfold klen. lia. }
    split; [exact SA3|].
    split.
    { intros _. assert (HK : HP <> key_addr k) by (intros E; apply HPK; rewrite E; apply in_map; exact KIN).
      destruct (KEEPF HP KH HPB2 HK) as (HPB3 & HPM).
      split; [exact HPB3|].
      apply (bytes_in_block HP KH m2 m3); [lia | rewrite key_ptrs_length; lia | exact HPM | exact HPBY2]. }
    split.
    { apply Forall_forall. intros k' Hk'.
      destruct (proj1 (Forall_forall _ _) KS3 k' Hk') as (KB2' & KBY2').
      assert (NI' : ~ In (key_addr k') (map key_addr ks1 ++ [key_addr k]))
        by (apply (nodup_split _ _ _ NDL2); apply in_map; exact Hk').
      assert (NE' : key_addr k' <> key_addr k)
        by (intros E; apply NI'; rewrite E; apply in_or_app; right; left; reflexivity).
      destruct (KEEPF _ _ KB2' NE') as (KB3' & KM').
      split; [exact KB3'|].
      apply (bytes_in_block (key_addr k') (klen k' + 1) m2 m3);
        [lia | rewrite length_app; cbn [length]; unfold klen; lia | exact KM' | exact KBY2']. }
    split.
    { intros q m. rewrite EB3. pose proof (rm_in _ b1 b2 (key_addr k, klen k + 1) (q, m) ND2 EB2) as R.
      cbn [fst] in R. split.
      - intros H. apply R in H. destruct H as [H Hq]. apply BI2 in H. destruct H as [(H0 & H1 & H2)|H].
        + left. split; [exact H0|]. split; [exact H1|]. rewrite map_app. intros X. apply in_app_or in X.
          destruct X as [X|[X|[]]]; [exact (H2 X) | exact (Hq (eq_sym X))].
        + right. exact H.
      - intros [(H0 & H1 & H2)|(Cp & E1 & E2)].
        + apply R. split.
          * apply BI2. left. split; [exact H0|]. split; [exact H1|]. intros X. apply H2. rewrite map_app.
            apply in_or_app. left. exact X.
          * intros E. apply H2. rewrite map_app. apply in_or_app. right. left. symmetry. exact E.
        + apply R. split; [apply BI2; right; exact (conj Cp (conj E1 E2))|]. rewrite E1. intros E.
          exact (KO2 (eq_sym E)). }
    split.
    { intros q m Hq H1 H2 Hm. apply (FO2 q m Hq H1); [|exact Hm]. intros X. apply H2. rewrite map_app.
      apply in_or_app. left. exact X. }
    split; [apply FI; [intros i Hi; cbn in Hi; apply GRP; unfold G_OUTV, G_RELAY_LO, G_RELAY_HI; lia | exact COV2]|].
    split.
    { destruct OP2 as [H|(Cp & NL & FRO & OB & LO & LJ)]; [left; exact H | right].
      assert (INO : In (OUT2, CAP2) (blocks L2 A2)) by (apply BI2; right; auto).
      destruct (KEEPF OUT2 CAP2 INO (fun E => KO2 (eq_sym E))) as (_ & OM).
      split; [exact Cp|]. split; [exact NL|]. split; [exact FRO|].
      split; [apply (bytes_in_block OUT2 CAP2 m2 m3); [lia | rewrite length_app; lia | exact OM | exact OB]|].
      split; [exact LO | exact LJ]. }
    split; [apply FI; [intros i Hi; cbn in Hi; apply GCP; lia | exact CCL2]|].
    split; [apply FI; [intros i Hi; cbn in Hi; apply GRP; unfold G_BROKEN, G_RELAY_LO, G_RELAY_HI; lia | exact CBR2]|].
    split; [apply FI; [intros i Hi; cbn in Hi; apply GRP; unfold G_DEAD, G_RELAY_LO, G_RELAY_HI; lia | exact CDD2]|].
    split; [apply FI; [intros i Hi; cbn in Hi; apply GRP; unfold G_EINTR, G_RELAY_LO, G_RELAY_HI; lia | exact CEI2]|].
    exact (free_err L2 A2 R2' m2 md2 _ L3 A3 R3 m3 md3 CP3). }
  pose proof SA3 as SA3'. rewrite SEGS in SA3'.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst2, mkR_of_getr, H3_8, H3_9, H3_18, SEGS.
    eapply ge_segN; [exact SA3' | lia | lia | lia]. }
  intros ms4 (can4 & (a0' & [(LT & ->)|(EQN & ->)]) & EQ4);
    destruct (eqv_mkst2 _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R4 & -> & X4);
    apply SR_ret; exists L3, A3, R4, m3, md3.
  - split; [|split; [exact J3 | unfold RF; rgx_all X4 RF3]].
    destruct ks2 as [|k' ks2']; [exfalso; cbn [length Z.of_nat] in LKS; lia|]. rewrite SEGS. reflexivity.
  - split; [|split; [exact J3 | unfold RF; rgx_all X4 RF3]].
    destruct ks2 as [|k' ks2']; [rewrite SEGS; reflexivity|]. exfalso. cbn [length] in LKS. lia.
Qed.

Lemma fin : forall L1 A1 R1 m1 md1 OUT1 CAP1 junk1,
  Jg ks [] ks L1 A1 m1 md1 (kr [] (NO + keys_total ks) CAP1) OUT1 CAP1 junk1 -> RFx R1 ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x132ac) m1 (seg_rom segs)) md1) GPOST.
Proof using AXg CTXg EAL EHI FNC FRC FREEPC GCP GEI GRP HPD NODUP OUTD PRE ROOM SAB SAM SEGS.
  intros L1 A1 R1 m1 md1 OUT1 CAP1 junk1 JJ RX1.
  pose proof JJ as (EKS & CH & IN1 & RS1 & CN1 & RO1 & FR1 & SA1 & HP1 & _ & BI1 & FO1 & COV1 & OP1 &
    (CCL1 & CBR1 & CDD1 & CEI1 & (ev1 & CER1))).
  destruct RS1 as (trp & qd & o1 & RL & RIND & ROK & RT3 & RT4 & RT5 & RIN & RLO & RLK & RLH).
  rewrite kr_nil in RT3, RT4, RT5. cbn [fst snd] in RT3, RT4, RT5.
  assert (CP1 : live = true -> 0 < CAP1).
  { intros LV. pose proof (live_tot _ _ _ _ (keys_total_nonneg ks) LV) as TP.
    destruct OP1 as [(_ & _ & E & _)|(Hc & _)]; [|exact Hc].
    unfold NOf in E. rewrite LV in E. pose proof (bv_unsigned_in_range 64 nout). lia. }
  pose proof pre_facts as (HM0 & HW0 & HB0 & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & GK & GK').
  pose proof CH as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW1).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M1) as (Hh & Hl & _).
  pose proof (NODUP _ _ _ _ M1) as ND1.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RS. change (bv_modulus 64) with (2 ^ 64) in RS. hide_ors.
  pose proof SAB as (SQ & SFR & SL1 & SL2 & SO & SH & SK).
  assert (QSB1 : In (qS, kS) (blocks L1 A1))
    by (apply BI1; left; split; [exact SQ|]; split; [exact SO | exact SK]).
  assert (G2 : getr R1 2 = Z_to_bv 64 (S0 + -32))
    by exact (RX1 2 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  assert (G4 : getr R1 4 = getr regs 4) by exact (RX1 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  assert (G8 : getr R1 8 = Z_to_bv 64 SA) by exact (RX1 8 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia)).
  pose proof SA1 as SA1'. rewrite SEGS in SA1'.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst2, mkR_of_getr, G8, SEGS. eapply ge_segT; [exact SA1' | lia]. }
  intros ms1 (can1 & -> & EQ1).
  destruct (eqv_mkst2 _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 0x132b4) by geq X2.
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (S0 + -32)) by (transitivity (getr R1 2); [geq X2 | exact G2]).
  assert (E2_4 : getr R2 4 = getr regs 4) by (transitivity (getr R1 4); [geq X2 | exact G4]).
  assert (E2_10 : getr R2 10 = Z_to_bv 64 HP) by geq X2.
  assert (RX2 : RFx R2) by (unfold RFx; rgx_all X2 RX1).
  assert (U2 : bv_unsigned (getr R2 2) = S0 + -32) by (rewrite E2_2; apply unsigned_lit; lia).
  assert (U2s : spZ R2 = S0 + -32) by exact U2.
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  destruct (Z.eq_dec HP 0) as [HZ|HPn].
  - pose proof FNC as FN. unfold free_null_contract in FN. rewrite FREEPC in FN.
    eapply SR_bind; [apply FN; [exact (eq_ind_r YK0s.ret_ok ret_ok_132b4 E2_1) |
                                exact (eq_trans E2_10 (f_equal (Z_to_bv 64) HZ)) | exact Hh | exact Hl]|].
    intros c' ->. rewrite (E2_1 : YK11.getr R2 1 = Z_to_bv 64 0x132b4).
    apply (epi L1 A1 R2 m1 md1 OUT1 CAP1 junk1).
    split; [exact CH|]. split; [exact IN1|].
    split.
    { rewrite held_tr_0, app_nil_r in RT3 by exact HZ. exists qd. rewrite <- RT3.
      split; [exact RL|]. split; [exact ROK|]. intros LV. rewrite <- RT5. exact (RLO (CP1 LV)). }
    split; [exact CN1|]. split; [exact RT4|]. split; [exact RO1|].
    split; [exact RX2|]. split; [exact FR1|]. split; [exact SA1|]. split; [exact QSB1|].
    split.
    { intros q m. split.
      - intros H. apply BI1 in H. destruct H as [(H0 & H1 & H2)|H]; [left | right; exact H].
        split; [exact H0|]. split; [exact H1|]. split; [|exact H2].
        destruct (blk_lo L A mem md q m HM0 H0). lia.
      - intros [(H0 & H1 & _ & H2)|H]; apply BI1; [left; auto | right; exact H]. }
    split; [intros q m Hq H1 _ H2 Hm; exact (FO1 q m Hq H1 H2 Hm)|].
    split; [exact COV1|]. split; [exact OP1|].
    split; [exact CCL1|]. split; [exact CBR1|]. split; [exact CDD1|]. split; [exact CEI1|]. exists ev1. exact CER1.
  - destruct HPD as [(HZ & _)|(HPB0 & HPF & HK1 & HK2 & HPO & HPK & HPBY0)]; [exfalso; exact (HPn HZ)|].
    pose proof HPF as (HPF1 & HPF2 & HPF3).
    destruct (HP1 HPn) as (HPB1 & HPBY1).
    pose proof (RLH HPn) as (Hp & Ep). set (p := sptr_of L A HP) in *.
    pose proof FRC as FR. unfold free_contract_rt in FR. rewrite FREEPC in FR.
    eapply SR_bind.
    { apply (FR L1 A1 R2 m1 md1 p KH (runF RFm qd bnd trp)).
      - split; [exact M1|]. split; [exact W1|]. split; [exact B1|].
        split; [exact (eq_ind_r YK0s.ret_ok ret_ok_132b4 E2_1)|].
        rewrite U2s.
        split; [clear - F3; Z.div_mod_to_equations; lia|].
        split; [unfold ALLOC_STACK; lia|].
        split; [lia|].
        split; [intros a Ha; apply SW1; unfold scratch_k; left; change (spZ regs) with S0; rewrite GK;
                unfold ALLOC_STACK in Ha; lia|].
        split; [exact (eq_trans E2_4 HTP)|].
        split; [intros a Ha; apply SW1; unfold scratch_k; right; exact Ha|].
        intros X. rewrite IN1 in X. discriminate.
      - exact RO1.
      - exact Hp.
      - rewrite Ep. exact E2_10.
      - exact ROK. }
    intros c3 (L3 & A3 & R3 & m3 & md3 & -> & CP3 & (b1 & b2 & EB1 & EB3) & BK & RO3 & GK3 & SURV & INI3 & LN3 & RS3).
    rewrite (E2_1 : YK11.getr R2 1 = Z_to_bv 64 0x132b4). rewrite Ep in EB1, BK, CP3.
    pose proof CP3 as (M3 & W3 & B3 & LE3 & AD3 & RPr3 & VM3 & FR3 & BY3 & SW3).
    assert (KEEPF : forall q m, In (q, m) (blocks L1 A1) -> q <> HP ->
               In (q, m) (blocks L3 A3) /\ (forall i, 0 <= i < m -> mbyte segs m3 (q + i) = mbyte segs m1 (q + i)))
      by (intros q m Hq Hne; exact (free_keeps L1 A1 m1 L3 A3 m3 HP KH q m
                                      (ex_intro _ b1 (ex_intro _ b2 (conj EB1 EB3))) BK Hq Hne)).
    assert (KNI : forall a, HP <= a < HP + KH -> ~ in_img Bm a).
    { intros a Ha Hi. apply (HPF3 (a - HP)); [lia|]. replace (HP + (a - HP)) with a by lia. exact Hi. }
    assert (SPH : YM05.alloc_ceiling <= spZ R2 - ALLOC_STACK) by (rewrite U2s; unfold ALLOC_STACK; lia).
    assert (FI : forall c cs, (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_plain Bm (c + i)) ->
               rw_cells segs m1 c cs -> rw_cells segs m3 c cs)
      by (intros c cs H1 H2; exact (free_img L1 A1 R2 m1 md1 _ L3 A3 R3 m3 md3 c cs M1 CP3 KNI SPH H1 H2)).
    assert (HPO1 : HP <> OUT1) by (apply (FO1 _ _ HPB0 HPO HPK); lia).
    destruct (KEEPF qS kS QSB1 SH) as (QSB3 & QSM).
    apply (epi L3 A3 R3 m3 md3 OUT1 CAP1 junk1).
    split.
    { eapply chain_free; [exact HW0 | exact HM0 | exact CTXg | exact AXg | exact CH | exact CP3 | exact LN3 |
                          exact SURV | exact Hp | lia | | | | ].
      - intros a [Ha|Ha]; [left | right; exact Ha]. rewrite U2s in Ha. change (spZ regs) with S0. rewrite GK.
        unfold ALLOC_STACK in Ha. lia.
      - intros a [Ha|Ha] Hn; [|exfalso; apply Hn; right; exact Ha]. change (spZ regs) with S0 in Ha.
        rewrite GK in Ha.
        assert (X : ~ (S0 + -32 - 8192 <= a < S0 + -32))
          by (intros X; apply Hn; left; rewrite U2s; unfold ALLOC_STACK; exact X).
        lia.
      - intros a Ha. cbv beta in Ha. split; [lia | exact (KNI a Ha)].
      - intros q n Hq Hq2 NF E. subst q.
        destruct (in_chain _ _ _ L A regs mem md L1 A1 m1 md1 p n HW0 CH Hq NF) as [_ EA].
        apply NF. right. left. rewrite <- EA. exact Ep. }
    split; [exact (INI3 IN1)|].
    split.
    { rewrite held_tr_n in RT3 by exact HPn. exists qd. rewrite <- RT3.
      split; [rewrite nret_app, p3b_nret_free, Nat.add_0_r; exact RL|].
      split; [unfold runF, run_tr; rewrite run_from_app; cbn [run_from resolve known_at]; exact RS3|].
      intros LV. rewrite <- RT5.
      apply (p3b_live_free L1 A1 R2 m1 md1 _ L3 A3 R3 m3 md3 p _ OUT1 CAP1 CP3 SURV (RLO (CP1 LV))).
      rewrite Ep. exact (fun E => HPO1 (eq_sym E)). }
    split; [exact CN1|]. split; [exact RT4|].
    split; [exact RO3|]. split; [exact (RFx_pres R2 R3 RX2 RPr3)|].
    split.
    { apply (high_cells_free L1 A1 R2 m1 md1 _ L3 A3 R3 m3 md3 _ _ M1 CP3); [|exact FR1].
      intros i Hi. cbn in Hi. split; [lia|]. split.
      - unfold scratch. rewrite U2s. unfold ALLOC_STACK. intros [X|X]; lia.
      - cbv beta. lia. }
    split.
    { apply (cells_in_block L3 A3 m1 m3 md3 qS kS); [exact M3 | exact QSB3 | lia | cbn; lia | exact QSM | exact SA1]. }
    split; [exact QSB3|].
    split.
    { intros q m. rewrite EB3. pose proof (rm_in _ b1 b2 (HP, KH) (q, m) ND1 EB1) as R. cbn [fst] in R. split.
      - intros H. apply R in H. destruct H as [H Hq]. apply BI1 in H.
        destruct H as [(H0 & H1 & H2)|H]; [left | right; exact H].
        split; [exact H0|]. split; [exact H1|]. split; [exact Hq | exact H2].
      - intros [(H0 & H1 & H2 & H3)|(Cp & E1 & E2)]; apply R.
        + split; [apply BI1; left; auto | exact H2].
        + split; [apply BI1; right; auto|]. rewrite E1. intros E. exact (HPO1 (eq_sym E)). }
    split; [intros q m Hq H1 _ H2 Hm; exact (FO1 q m Hq H1 H2 Hm)|].
    split; [apply FI; [intros i Hi; cbn in Hi; apply GRP; unfold G_OUTV, G_RELAY_LO, G_RELAY_HI; lia | exact COV1]|].
    split.
    { destruct OP1 as [H|(Cp & NL & FRO & OB & LO & LJ)]; [left; exact H | right].
      assert (INO : In (OUT1, CAP1) (blocks L1 A1)) by (apply BI1; right; auto).
      destruct (KEEPF OUT1 CAP1 INO (fun E => HPO1 (eq_sym E))) as (_ & OM).
      split; [exact Cp|]. split; [exact NL|]. split; [exact FRO|].
      split; [apply (bytes_in_block OUT1 CAP1 m1 m3); [lia | rewrite length_app; lia | exact OM | exact OB]|].
      split; [exact LO | exact LJ]. }
    split; [apply FI; [intros i Hi; cbn in Hi; apply GCP; lia | exact CCL1]|].
    split; [apply FI; [intros i Hi; cbn in Hi; apply GRP; unfold G_BROKEN, G_RELAY_LO, G_RELAY_HI; lia | exact CBR1]|].
    split; [apply FI; [intros i Hi; cbn in Hi; apply GRP; unfold G_DEAD, G_RELAY_LO, G_RELAY_HI; lia | exact CDD1]|].
    split; [apply FI; [intros i Hi; cbn in Hi; apply GRP; unfold G_EINTR, G_RELAY_LO, G_RELAY_HI; lia | exact CEI1]|].
    exact (free_err L1 A1 R2 m1 md1 _ L3 A3 R3 m3 md3 CP3).
Qed.

Lemma loop : forall ks2 ks1 L1 A1 R1 m1 md1 OUT1 CAP1 junk1,
  Jg ks1 ks2 ks1 L1 A1 m1 md1 (kr ks2 (NO + keys_total ks1) CAP1) OUT1 CAP1 junk1 -> RF R1 (Z.of_nat (length ks1)) ->
  ks2 <> [] ->
  SR segs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x13234) m1 (seg_rom segs)) md1) GPOST.
Proof using AXg CTXg EAL EHI FNC FRC FREEPC G5P GCP GEC GEI GRP HPD Hbr Hcl Hdd Hei KF NDK NHB NODUP OUTD PRE ROOM SAB SAM SEGS SLACK TPE.
  induction ks2 as [|k ks2 IH]; intros ks1 L1 A1 R1 m1 md1 OUT1 CAP1 junk1 JJ RF1 NE; [congruence|].
  eapply SR_bind; [exact (ge_step ks1 k ks2 L1 A1 R1 m1 md1 OUT1 CAP1 junk1 JJ RF1)|].
  intros c (L2 & A2 & R2 & m2 & md2 & OUT2 & CAP2 & junk2 & -> & JM & RF2).
  eapply SR_bind; [exact (fr_step ks1 k ks2 L2 A2 R2 m2 md2 OUT2 CAP2 junk2 JM RF2)|].
  intros c (L3 & A3 & R3 & m3 & md3 & -> & J3 & RF3).
  replace (Z.of_nat (length ks1) + 1) with (Z.of_nat (length (ks1 ++ [k]))) in RF3
    by (rewrite length_app; cbn [length]; lia).
  destruct ks2 as [|k' ks2'].
  - pose proof J3 as (EKS3 & _). rewrite app_nil_r in EKS3. rewrite <- EKS3 in J3.
    exact (fin L3 A3 R3 m3 md3 OUT2 CAP2 junk2 J3 (RF_RFx R3 _ RF3)).
  - apply (IH (ks1 ++ [k]) L3 A3 R3 m3 md3 OUT2 CAP2 junk2 J3 RF3). discriminate.
Qed.

Lemma run_main : SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 GESTURES_END) mem (seg_rom segs)) md) GPOST.
Proof using All.
  pose proof pre_facts as (HM0 & HW0 & HB0 & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR).
  pose proof gfacts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & GK & GK').
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ HM0) as (Hh & Hl & _).
  pose proof (NODUP _ _ _ _ HM0) as ND0.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RS. change (bv_modulus 64) with (2 ^ 64) in RS. hide_ors.
  assert (Z1 : 0 <= S0 + -32) by lia. assert (Z2 : S0 + -32 + 32 <= 2 ^ 64) by lia.
  destruct (frame32 mem (S0 + -32) Z1 Z2) as (j0 & j1 & j2 & j3 & Lj0 & Lj1 & Lj2 & Lj3 & FRM).
  { intros i Hi. rewrite <- SEGS. apply HWS. lia. }
  pose proof HS0 as HS0'. rewrite SEGS in HS0'.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst2, mkR_of_getr. rewrite <- (Z_to_bv_bv_unsigned (getr regs 10)). rewrite SEGS.
    eapply ge_segP; [exact Lj0 | exact Lj1 | exact Lj2 | exact Lj3 | exact FRM | exact HS0' | lia | lia | exact SAM |
                     lia | lia]. }
  intros ms1 (can1 & (a0' & m1 & HC & MU & WM & FR1 & SA1) & EQ1). hide_ors.
  pose proof SA1 as SA1n. rewrite <- SEGS in SA1n. pose proof FR1 as FR1n. rewrite <- SEGS in FR1n.
  assert (WM' : wmono segs mem m1) by (rewrite SEGS; exact WM).
  assert (CH1 : chain GESTURES_END_K EE FF L A regs mem md L A m1 md).
  { eapply chain_mem; [exact AXg | exact chain_refl | exact MU | exact WM' |].
    intros a Ha. destruct (Z_le_gt_dec (S0 + -32) a) as [D1|D1]; [destruct (Z_lt_ge_dec a S0) as [D2|D2]|].
    - right. left. split; [unfold scratch_k; left; change (spZ regs) with S0; rewrite GK; lia | lia].
    - left. cbn. split; [lia | exact I].
    - left. cbn. split; [lia | exact I]. }
  assert (TRc : forall c cs, rw_cells segs mem c cs -> c + Z.of_nat (cells_size cs) <= S0 + -32 ->
             rw_cells segs m1 c cs).
  { intros c cs Hc H1. apply (rw_cells_transport segs _ mem m1 c cs Hc MU WM'). cbn. split; [lia | exact I]. }
  assert (TRb : forall c bs, bytes_at segs mem c bs -> c + Z.of_nat (length bs) <= S0 + -32 -> bytes_at segs m1 c bs).
  { intros c bs Hc H1. apply (bytes_at_transport segs _ mem m1 c bs Hc MU). cbn. split; [lia | exact I]. }
  assert (J0 : Jg [] ks [] L A m1 md (kr ks (NO + keys_total []) CAP) OUT CAP junk).
  { split; [reflexivity|]. split; [exact CH1|]. split; [exact INIT|].
    split.
    { unfold RSt. exists [], [], (known_at L A OUT). change (keys_total []) with 0. rewrite Z.add_0_r.
      split; [reflexivity|]. split; [intros post; reflexivity|]. split; [exact RES0|].
      split; [reflexivity|].
      split.
      { intros _. unfold kr, gestures_end_cap. cbn [fst snd]. apply p3b_ker_cap.
        unfold key_runs, key_lens. rewrite !map_map. reflexivity. }
      split; [reflexivity|]. split; [exact I|].
      split.
      { intros Cp. destruct OUTD as [(C0 & _)|(_ & _ & IN & _)]; [lia|]. exact (p3b_live_of_blocks L A OUT CAP ND0 IN). }
      split.
      { apply Forall_forall. intros k Hk. destruct (proj1 (Forall_forall _ _) KF k Hk) as (KB & _).
        exact (p3b_live_of_blocks L A _ _ ND0 KB). }
      intros HPn. destruct HPD as [(HZ & _)|(HPB0 & _)]; [exfalso; exact (HPn HZ)|].
      exact (p3b_live_of_blocks L A HP KH ND0 HPB0). }
    split; [intros _; repeat split|].
    split.
    { apply (ro_agree_munch1 mem m1 (S0 + -32) S0 RO0 MU). intros x Hx. apply ro_false_noimg; [lia|].
      intros Hi. pose proof (in_img_low2 _ Hi). lia. }
    split; [exact FR1n|]. split; [exact SA1n|].
    split.
    { intros HPn. destruct HPD as [(HZ & _)|(HPB0 & (HPF1 & HPF2 & _) & HK1 & _ & _ & _ & HPBY0)];
        [exfalso; exact (HPn HZ)|].
      split; [exact HPB0|]. apply TRb; [exact HPBY0|]. rewrite key_ptrs_length. lia. }
    split.
    { apply Forall_forall. intros k Hk.
      destruct (proj1 (Forall_forall _ _) KF k Hk) as (KB & (KF1 & KF2 & _) & KBY & _ & _ & _ & _).
      split; [exact KB|].
      change (key_text k ++ Z_to_bv 8 0 :: key_slack k) with (key_text k ++ [Z_to_bv 8 0] ++ key_slack k) in KBY.
      rewrite app_assoc in KBY. apply bytes_at_app in KBY as [KBY _].
      apply TRb; [exact KBY|]. rewrite length_app. cbn [length]. lia. }
    split.
    { intros q m. split.
      - intros H. destruct (Z.eq_dec q OUT) as [E|NE].
        + right. subst q. destruct OUTD as [(C0 & O0 & _)|(Cp & _ & IN & _)].
          * exfalso. destruct (blk_lo L A mem md _ _ HM0 H). lia.
          * split; [exact Cp|]. split; [reflexivity|]. exact (nodup_fst _ OUT m CAP ND0 H IN).
        + left. split; [exact H|]. split; [exact NE|]. intros [].
      - intros [(H & _)|(Cp & -> & ->)]; [exact H|].
        destruct OUTD as [(C0 & _)|(_ & _ & IN & _)]; [lia | exact IN]. }
    split; [intros q m _ NE _ _; exact NE|].
    split; [rewrite NOf_nil, !Z_to_bv_bv_unsigned; apply TRc; [exact COUT | cbn; unfold G_OUTV; lia]|].
    split.
    { unfold OUTP. rewrite NOf_nil, Of_nil.
      destruct OUTD as [H|(Cp & NL & IN & FRO & OB & LO & LJ)]; [left; exact H | right].
      pose proof FRO as (FQ1 & FQ2 & _).
      split; [exact Cp|]. split; [exact NL|]. split; [exact FRO|].
      split; [apply TRb; [exact OB | rewrite length_app; lia]|]. split; [exact LO | exact LJ]. }
    unfold GLB. rewrite brf_nil, eif_nil.
    split; [apply TRc; [exact CCL | cbn; unfold G_CLIENT; lia]|].
    split; [apply TRc; [exact CBR | cbn; unfold G_BROKEN; lia]|].
    split; [apply TRc; [exact CDD | cbn; unfold G_DEAD; lia]|].
    split; [apply TRc; [exact CEI | cbn; unfold G_EINTR; lia]|].
    exists ev. apply TRc; [exact CERR | cbn; lia]. }
  destruct HC as [(NHZ & ->)|(NHP & ->)].
  - destruct (eqv_mkst2 _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    assert (KS0 : ks = []) by (apply length_zero_iff_nil; lia).
    assert (RX1 : RFx R1) by (unfold RFx; rgx_all X1 I).
    rewrite KS0 in J0.
    apply (fin L A R1 m1 md OUT CAP junk); [|exact RX1].
    rewrite KS0. exact J0.
  - destruct (eqv_mkst2 _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    assert (RF1 : RF R1 (Z.of_nat (length (@nil (Z * list byte * list byte))))) by (unfold RF; rgx_all X1 I).
    apply (loop ks [] L A R1 m1 md OUT CAP junk J0 RF1).
    intros E. rewrite E in NHP. cbn [length] in NHP. lia.
Qed.

End Run.

End Img.

Theorem gestures_end_holds (Fm : ResFormT) : gesture_end_contract Bm API Fm -> free_contract_rt Bm API Fm ->
  free_null_contract Bm -> gestures_end_contract Bm API Fm.
Proof using AXg CTXg FREEPC NODUP SLACK.
  intros GEC FRC FNC. unfold gestures_end_contract. cbv zeta.
  intros L A regs mem md bnd ks HP KH O junk cl br dd ei mx nout cap out ev
    SEG PRE INIT TPE EAL EHI RO GRP GCP GEI G5P SAB SAM HS NHB HPD NDK KF Hcl Hbr Hdd Hei CCL CBR CDD CEI COUT CERR
    OUTD MGQ RES ROOM.
  destruct SAB as (qS & kS & SAB).
  exact (run_main SEG Fm GEC FRC FNC L A regs mem md bnd ks HP KH O junk cl br dd ei mx nout cap out ev qS kS
    PRE INIT TPE EAL EHI RO GRP GCP GEI G5P SAB SAM HS NHB HPD NDK KF Hcl Hbr Hdd Hei CCL CBR CDD CEI COUT CERR
    OUTD MGQ RES ROOM).
Qed.

End GSP.
