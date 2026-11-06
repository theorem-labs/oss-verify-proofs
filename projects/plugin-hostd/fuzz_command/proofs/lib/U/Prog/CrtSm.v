(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 483 of its 548 lines of code are new or changed and 952 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_worker_list.v, with its module paths, addresses and numbers changed; 1213 of its 1275 lines of code are new or changed and 486 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/send_message.v, with its module paths and module names changed; 7 of its 164 lines of code are new or changed and 1118 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB VerbsB.
Local Open Scope Z_scope.

(* Memory, image and frame-interval facts shared by the check_round_trip proof files. *)

Lemma sm_cells_bytes_app : forall l1 l2, cells_bytes (l1 ++ l2) = cells_bytes l1 ++ cells_bytes l2.
Proof.
  induction l1 as [|c l1 IH]; intros l2; cbn [app cells_bytes]; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma sm_cells_wf_app : forall l1 l2, cells_wf (l1 ++ l2) -> cells_wf l1.
Proof.
  induction l1 as [|c l1 IH]; intros l2 H; [exact I|].
  destruct H as [H1 H2]. split; [exact H1 | exact (IH l2 H2)].
Qed.

Lemma sm_cell_get : forall segs m A pre c post, rw_cells segs m A (pre ++ c :: post) ->
  bytes_at segs m (A + Z.of_nat (cells_size pre)) (cbytes c).
Proof.
  intros segs m A pre c post [[Hwf Hb] _].
  rewrite sm_cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb].
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb as [Hb _].
  rewrite (cells_bytes_length pre (sm_cells_wf_app _ _ Hwf)) in Hb. exact Hb.
Qed.

Lemma sm_cell_get2 : forall segs m A pre c post k, rw_cells segs m A (pre ++ c :: post) -> cells_size pre = k ->
  bytes_at segs m (A + Z.of_nat k) (cbytes c).
Proof. intros segs m A pre c post k H <-. exact (sm_cell_get segs m A pre c post H). Qed.

Lemma sm_le_of_bytes : forall (B : malloc_syms) m a bs, ms_segs B = rsegs -> bytes_at rsegs m a bs -> le_at B m a bs.
Proof.
  intros B0 m a bs HS (H0 & H1 & H2). unfold le_at, blk_data. cbv zeta. rewrite HS. intros i Hi.
  rewrite mbyte_mrd. replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia.
  apply H2. lia.
Qed.

Lemma sm_bytes_of_le : forall (B : malloc_syms) m a bs, ms_segs B = rsegs -> 0 <= a ->
  a + Z.of_nat (length bs) <= 2 ^ 64 -> le_at B m a bs -> bytes_at rsegs m a bs.
Proof.
  intros B0 m a bs HS H0 H1 H. apply bytes_at_of_mbyte; [exact H0 | exact H1 |].
  intros i Hi. unfold le_at, blk_data in H. cbv zeta in H. rewrite HS in H.
  rewrite (H (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

Lemma sm_le_keep : forall (B : malloc_syms) m m' a bs, le_at B m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  le_at B m' a bs.
Proof.
  intros B0 m m' a bs H K. unfold le_at, blk_data in *. cbv zeta in *. intros i Hi.
  rewrite K by exact Hi. exact (H i Hi).
Qed.

Lemma sm_bytes_of_image : forall segs m n A bs, image_bytes segs A n = Some bs ->
  (forall i, 0 <= i < Z.of_nat n -> mbyte segs m (A + i) = seg_rom segs (Z_to_bv 64 (A + i))) ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 -> bytes_at segs m A bs.
Proof.
  intros segs m n. induction n as [|n IH]; intros A bs HI HM H0 H1; cbn [image_bytes] in HI.
  - injection HI as <-. split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
  - destruct (PropExec.seg_rom segs (wa A)) as [b0|] eqn:E0; [|discriminate].
    destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E1; [|discriminate].
    injection HI as <-.
    change (b0 :: bs') with ([b0] ++ bs'). apply bytes_at_app. split.
    + split; [exact H0|]. split; [cbn; lia|]. intros i Hi. cbn [length] in Hi.
      destruct i as [|i]; [|lia]. cbn [nth_error].
      replace (A + Z.of_nat 0) with A by lia. rewrite <- mbyte_mrd.
      pose proof (HM 0 ltac:(lia)) as H. rewrite Z.add_0_r in H. rewrite H. exact E0.
    + replace (A + Z.of_nat (length [b0])) with (A + 1) by (cbn; lia).
      apply IH; [exact E1 | | lia | lia]. intros i Hi.
      replace (A + 1 + i) with (A + (1 + i)) by lia. apply HM. lia.
Qed.

Lemma sm_img_res : forall (B : malloc_syms) k lo sz a, ms_segs B = rsegs ->
  nth_error (map (fun s => (bv_unsigned (fst s), bv_unsigned (snd s))) (segments_reserved rsegs)) k = Some (lo, sz) ->
  lo <= a < lo + sz -> in_img B a.
Proof.
  intros B0 k lo sz a HS E Ha. unfold in_img. rewrite HS. split.
  - assert (L : length rsegs = 4%nat) by (vm_compute; reflexivity).
    intros H. rewrite H in L. discriminate.
  - rewrite nth_error_map in E. destruct (nth_error (segments_reserved rsegs) k) as [s|] eqn:E2; [|discriminate].
    cbv beta iota delta [option_map] in E. injection E as E3 E4.
    exists s. split; [exact (nth_error_In _ _ E2) | lia].
Qed.

Lemma sm_img_iv : forall (B : malloc_syms) a, ms_segs B = rsegs -> 0x10000 <= a < 0x55000 -> in_img B a.
Proof.
  intros B0 a HS Ha.
  destruct (Z_lt_ge_dec a 0x13000).
  { apply (sm_img_res B0 0 0x10000 0x3000); [exact HS | vm_compute; reflexivity | lia]. }
  destruct (Z_lt_ge_dec a 0x22000).
  { apply (sm_img_res B0 1 0x13000 0xF000); [exact HS | vm_compute; reflexivity | lia]. }
  destruct (Z_lt_ge_dec a 0x23000).
  { apply (sm_img_res B0 2 0x22000 0x1000); [exact HS | vm_compute; reflexivity | lia]. }
  apply (sm_img_res B0 3 0x23000 0x32000); [exact HS | vm_compute; reflexivity | lia].
Qed.

Lemma sm_relro_iv : forall a, in_globals frame_RELRO a -> 0x226b0 <= a < 0x23000.
Proof. intros a (lo & len & Hin & Hb). unfold frame_RELRO in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. Qed.

Lemma sm_relro_of : forall a, 0x226b0 <= a < 0x22d40 -> in_globals frame_RELRO a.
Proof. intros a Ha. exists 140976, 1680. split; [left; reflexivity | lia]. Qed.

Lemma sm_g_iv : forall a, in_globals frame_G a -> 0x33ff0 <= a < 0x343ec.
Proof. intros a (lo & len & Hin & Hb). unfold frame_G in Hin. destruct Hin as [E|[]]. injection E as <- <-. lia. Qed.

Lemma sm_g_of : forall a, 0x33ff0 <= a < 0x343ec -> in_globals frame_G a.
Proof. intros a Ha. exists 212976, 1020. split; [left; reflexivity | lia]. Qed.

Lemma sm_ro_low : forall x, ro_addr rsegs x = true -> bv_unsigned x < 2 ^ 20.
Proof.
  intros x Hx. destruct (Z_lt_ge_dec (bv_unsigned x) (2 ^ 20)) as [H|H]; [exact H|].
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
  rewrite <- (Z_to_bv_bv_unsigned x) in Hx. rewrite ro_addr_hi in Hx by lia. discriminate.
Qed.

Lemma sm_ro_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 20 -> Frame.outside W x) -> ro_agree rsegs m'.
Proof.
  intros W m m' H HM HW x Hx. unfold mrd. rewrite (HM x); [exact (H x Hx)|].
  pose proof (sm_ro_low x Hx). pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
  apply HW. lia.
Qed.

Lemma sm_got_img : image_bytes rsegs 0x22d10 8 = Some (le8 (Z_to_bv 64 0x343e8)).
Proof. vm_compute. repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ]. Qed.

Lemma sm_image_nth : forall segs n A bs i, image_bytes segs A n = Some bs -> (i < n)%nat ->
  PropExec.seg_rom segs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  intros segs n. induction n as [|n IH]; intros A bs i HI Hi; [lia|].
  cbn [image_bytes] in HI.
  destruct (PropExec.seg_rom segs (wa A)) as [b0|] eqn:E0; [|discriminate].
  destruct (image_bytes segs (A + 1) n) as [bs'|] eqn:E1; [|discriminate].
  injection HI as <-.
  destruct i as [|i]; cbn [nth_error].
  - rewrite Z.add_0_r. exact E0.
  - replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IH; [exact E1 | lia].
Qed.

Lemma sm_got_rom_img : image_bytes rsegs 0x22d40 8 = Some (le8 (Z_to_bv 64 0x54730)).
Proof. vm_compute. repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ]. Qed.

Lemma sm_got_rom : forall m a, word_mem rsegs m SSP_GOT_B SSP_GUARD_B -> SSP_GOT_B <= a < SSP_GOT_B + 8 ->
  mbyte rsegs m a = seg_rom rsegs (Z_to_bv 64 a).
Proof.
  intros m a W Ha.
  pose proof (KindBGlue.word_mem_le8 rsegs m SSP_GOT_B SSP_GUARD_B W ltac:(unfold SSP_GUARD_B; lia)
    ltac:(unfold SSP_GOT_B; lia) ltac:(unfold SSP_GOT_B; lia)) as (_ & _ & H).
  rewrite Mem.length_le8 in H.
  assert (Ei : a = SSP_GOT_B + Z.of_nat (Z.to_nat (a - SSP_GOT_B))) by lia.
  rewrite Ei, mbyte_mrd. rewrite (H (Z.to_nat (a - SSP_GOT_B)) ltac:(unfold SSP_GOT_B in *; lia)).
  symmetry. exact (sm_image_nth rsegs 8 _ _ (Z.to_nat (a - SSP_GOT_B)) sm_got_rom_img ltac:(unfold SSP_GOT_B in *; lia)).
Qed.

Lemma sm_guard_wr : forall m i, 0 <= i < 8 -> writable_at rsegs m (SSP_GUARD_B + i).
Proof.
  intros m i Hi. unfold SSP_GUARD_B.
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  repeat (destruct C as [C|C];
    [subst i; unfold writable_at, wview; destruct (m _); [discriminate | vm_compute; discriminate]|]).
  subst i; unfold writable_at, wview; destruct (m _); [discriminate | vm_compute; discriminate].
Qed.

Lemma sm_pw_mid : forall l1 x l2, pairwise ranges_disjoint (l1 ++ x :: l2) -> 1 <= snd x -> ~ In x (l1 ++ l2).
Proof.
  intros l1 x l2 HP Hs Hin. destruct (pairwise_app_mid' _ _ _ _ _ HP Hin) as [R|R]; unfold ranges_disjoint in R; lia.
Qed.

Lemma sm_out_sep : forall (B : malloc_syms) a k, ms_segs B = rsegs -> 1 <= k ->
  (forall i, 0 <= i < k -> ~ in_img B (a + i)) -> a + k <= 0x10000 \/ 0x55000 <= a.
Proof.
  intros B0 a k HS Hk H.
  destruct (Z_le_gt_dec (a + k) 0x10000) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec 0x55000 a) as [E'|E']; [right; exact E'|].
  exfalso. apply (H (Z.max 0 (0x10000 - a))); [lia|]. apply (sm_img_iv B0); [exact HS | lia].
Qed.
