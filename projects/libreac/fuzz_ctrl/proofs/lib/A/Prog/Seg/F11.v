(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F4.v, with its module names, addresses and numbers changed; 1179 of its 1302 lines of code are new or changed and 3112 lines of the source are left out. *)
(* Segment F11 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A), plan-asan 2 row F11: 0x8206c-0x820f4, which
   ends in `jal reac_identity_ingest@0x820f4`, with the out-of-line slow paths 0x82098-0x820a0 (error call
   0x82c94), 0x829b4-0x829bc (error call 0x82cc8) and 0x829c0-0x829c8 (error call 0x82ccc), none of them reached.

   0x8206c-0x82090 is the inlined record-sum loop, a down-counter over the n0 = ir_s - 8 record bytes at
   [phi+34, phi+34+n0): each turn runs the instrumented check of the byte at a0 (a load of the shadow byte at
   (a0 >> 3) + s10 and a compare; its slow path 0x82098 compares (a0 land 7) with that byte), then
   `lbu a6,0(a5)`, a1 -= 1, a0 += 1, a4 += a6, a5 += 1, `bnez a1` back.  f11_loop proves it by induction on the
   turn with the invariant a0 = a5 = phi+34+i, a1 = n0-i, a4 = psum (skipn 34 G) i; every byte read lies in
   [phi, phi+50), which the heap block HB m phi (flen g j) with 50 <= flen g j makes an addressable range, so no
   turn reaches 0x82098 or the error call 0x82c94 behind it.

   0x820a4 `andi a0,a4,127; bnez a0,82bf4`: the abort pair is NOT reached.  The sum of those n0 bytes is
   0 mod 128 because F10's exit carries reply_ok = true, hence ir (flen g j) (t_g (g_in g) j) = true, whose
   conjunct recsum (ir_rec (t_g (g_in g) j)) = 0 is exactly that sum mod 128 (f11_sum128); no extra entry fact is
   needed for it.

   0x820ac-0x820ec checks the two record bytes phi+36 and phi+37 (slow paths 0x829b4 / 0x829c0, neither reached:
   both granules lie in the addressable range) and compares the 16-bit value (byte phi+36) << 8 | (byte phi+37)
   with the u16 at pa = [s1+256] = fr+256.  The compare at 0x820ec is NOT taken: the reply post the entry cuts
   carry (SlotInv.b5_RPost) puts reply_addr G = [cp_b G 37; cp_b G 36] at fr+256, and a little-endian `lhu` of
   those two bytes is cp_v G 36 * 256 + cp_v G 37, the value the two record bytes build.  The cell is read in
   its `le2` form, so the step engine's load post-processing does not evaluate a symbolic byte list.

   0x820f0 `ld a0,144(s1)` loads the identity record id = fr+2688 and 0x820f4 calls reac_identity_ingest on the
   lib/A contract (A/Prog/reac_identity_ingest_c.v), taken as a Section Hypothesis, with a1 = the 16-bit reply
   address, a2 = phi+38 and a3 = ir_s-13 (the payload and its length, set by F10).  The segment ends at the
   return point 0x820f8.  The callee writes its window [sp-32, sp) and the 38 identity bytes [id, id+38): FRA
   moves across that two-interval write with the canonical Tac_slot.sl_fr_cl (the frame body is one of the two
   regions sl_fr_cl allows) plus sl_fra_move for the lazy-page step, and ENT with ent_store / ent_mat.  The
   result is 0 or 1 (RcIdentModel.ING_ret), so the exit's `0 <= a0 < 2^63` holds and F12's `bltz a0` at 0x820f8
   is not taken.

   Cuts.  The three cuts are SlotInv's official texts: ENTRY 1 Inv_A8206c_at (the loop head, F10's exit with the
   loop taken), ENTRY 2 Inv_A820ac_at (F10's exit with the loop skipped) and the EXIT Inv_A820f8_at (F12's entry).
   The span carry (FLSI, LK, b5_C with the fragment record FGj and the first-fragment spills FSj, b5_K, b5_RC)
   moves across the ingest write by munch transport.  The identity record is the one stage change: the entries
   carry IDj (the bytes t_ID j at fr + 2688, with id_ok), the ingest call takes them as its record (38 bytes,
   f11_tID_len), and its post's record snd (ING (t_ID j) (r_addr G) (r_pl G)) is ID1 g j because ir holds on this
   arm (SlotModel.rp_id); id_ok across the call is RcIdentLib.ING_id_ok, the lemma that
   reac_identity_ingest_id_ok_kept_holds wraps.  So the exit carries IDb1.

   No memory outside [sp-32, sp) and [fr+2688, fr+2726) changes, and the segment writes nothing itself. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcParse RcParseLib
  RcReply RcReplyLib RcAsanLib RcIdentModel RcKind.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib
  reac_identity_ingest_c reac_ctrl_identity_fragment_c reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* ---- ghost-level facts of the record ---- *)

(* The 50-byte record of the model has 50 bytes. *)
Lemma f11_tg_len : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g, fr50. rewrite length_firstn, length_app, repeat_length. lia. Qed.

(* The identity record of every turn has the model's 38 bytes: ID0 at turn 0, and the ingests of rp_id and
   fg_id keep the length (RcIdentModel.ING_length). *)
Lemma f11_tID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  assert (Hr : forall idb len g, length idb = 38%nat -> length (rp_id idb len g) = 38%nat)
    by (intros idb len g Hl; unfold rp_id; destruct (ir len g); [apply ING_length|]; exact Hl).
  assert (Hf : forall idb len st g, length idb = 38%nat -> length (fg_id idb len st g) = 38%nat)
    by (intros idb len st g Hl; unfold fg_id; destruct (fg_rf len st g =? 1); [apply ING_length|]; exact Hl).
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens _ _); cbn [fs_id]; apply Hf; apply Hr; exact IH.
Qed.

(* The FIRST body a frame-loop state carries has at most 23 bytes: fs0's is empty and an opening turn takes at
   most the 23 bytes of the 50-byte record from offset 27 (SlotModel.turn). FSb's bytes_at at fr + 2880 so lies
   inside the 35-byte object first.sroa.7. *)
Lemma f11_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens _ _); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* nth of a tail. *)
Lemma f11_nth_skipn : forall (A : Type) (d : A) (n : nat) (l : list A) (i : nat),
  nth i (skipn n l) d = nth (n + i) l d.
Proof.
  intros A d n. induction n as [|n IH]; intros l i; [reflexivity|].
  destruct l as [|x l]; [cbn; destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

(* nth of a prefix, and psum of a prefix, for the record checksum below. *)
Lemma f11_nth_firstn : forall (A : Type) (d : A) (n : nat) (l : list A) (i : nat), (i < n)%nat ->
  nth i (firstn n l) d = nth i l d.
Proof.
  intros A d n. induction n as [|n IH]; intros l i Hi; [lia|].
  destruct l as [|x l]; [destruct i; reflexivity|].
  destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma f11_psum_firstn : forall (bs : list byte) (n k : nat), (k <= n)%nat ->
  psum (firstn n bs) k = psum bs k.
Proof.
  intros bs n k. induction k as [|k IH]; intros Hk; [reflexivity|].
  cbn [psum]. rewrite IH by lia. rewrite f11_nth_firstn by lia. reflexivity.
Qed.

(* The record checksum: the n0 = ir_s - 8 bytes the loop reads, from offset 34, sum to 0 mod 128. It is the
   conjunct recsum (ir_rec g) = 0 of ir (RcReply.v:17), read through rc_len_rec and psum_firstn. *)
Lemma f11_sum128 : forall len g, length g = 50%nat -> ir len g = true ->
  psum (skipn 34 g) (Z.to_nat (ir_s g - 8)) mod 128 = 0.
Proof.
  intros len g Hg Hir.
  destruct (ir_bytes len g Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _ & _ & _ & Hrec).
  unfold recsum in Hrec. rewrite (rc_len_rec g Hg Hs) in Hrec.
  unfold ir_rec in Hrec. rewrite f11_psum_firstn in Hrec by lia. exact Hrec.
Qed.

(* The payload the ingest call reads: the len bytes of the record at offset 38. *)
Lemma f11_pb_len : forall (g : list byte) (n : Z), length g = 50%nat -> 0 <= n <= 10 ->
  length (firstn (Z.to_nat n) (skipn 38 g)) = Z.to_nat n.
Proof.
  intros g n Hg Hn. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, Hg. lia.
Qed.

(* ---- small memory helpers (the carried byte facts, in the form the step engine consumes) ---- *)

Lemma f11_rd2 : forall m a bs, bytes_at rsegs m a bs -> length bs = 2%nat ->
  ov_read_bytes rsegs m (wa a) 2 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 2 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

Lemma f11_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

(* An 8-byte cell of the reply post (lib/Lib cells) as carried bytes. *)
Lemma f11_lrwB : forall m a n (bs : list byte), rw_cells rsegs m a [CB n bs] -> bytes_at rsegs m a bs.
Proof. intros m a n bs [[_ H] _]. cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

Lemma f11_wr_of_stk : forall (m : word -> option byte) (a n lo hi : Z),
  stk rsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at rsegs m a n.
Proof.
  intros m a n lo hi (Hl0 & Hh0 & Hb) Hlo Hn Hhi. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Hb (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

(* The identity record as the ingest contract asks for it: the k carried bytes at a, readable and writable
   inside a stk range (the frame body). *)
Lemma f11_rwb : forall (m : word -> option byte) (a : Z) (k : nat) (bs : list byte) (lo hi : Z),
  stk rsegs m lo hi -> lo <= a -> a + Z.of_nat k <= hi -> length bs = k -> bytes_at rsegs m a bs ->
  rw_cells rsegs m a [CB k bs].
Proof.
  intros m a k bs lo hi HS Hlo Hhi Hlen Hbs. split.
  - split; [cbn; split; [exact Hlen | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hbs.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
    apply (f11_wr_of_stk m a (Z.of_nat k) lo hi HS Hlo ltac:(lia) ltac:(lia)).
Qed.

(* A prefix of a carried byte list is carried at the same address (b5_PF states the record's 38 bytes and its
   six-byte compare operands with `<= length`, and a transport across a write needs an exact length). *)
Lemma f11_bytes_first : forall m a bs k, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof.
  intros m a bs k H. rewrite <- (firstn_skipn k bs) in H.
  apply bytes_at_app in H. exact (proj1 H).
Qed.

(* memcmp_model reads only the first n bytes of each list. *)
Lemma f11_mcmp_firstn : forall n l r, SFA.memcmp_model (firstn n l) (firstn n r) n = SFA.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros l r; [reflexivity|].
  destruct l as [|a l]; destruct r as [|b r]; cbn [firstn SFA.memcmp_model]; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

(* A metadata address lies between the end of the low app range and the start of the high app range. *)
Lemma f11_sh_lt : forall x, in_shadow x -> LOWMEM_END <= x /\ x < HIGHMEM_BEG.
Proof.
  intros x H. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
Qed.

(* The metadata address of an in-range byte is itself in range (the step engine's load side-conditions read it). *)
Lemma f11_sh_range : forall x, 0 <= x < 2 ^ 64 -> 0 <= Z.shiftr x 3 + ASAN_K < 2 ^ 64.
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (H1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (H2 : x / 8 <= x) by (apply Z.div_le_upper_bound; lia).
  unfold ASAN_K. lia.
Qed.

(* The 16-bit zero-extension of a small literal word is the word (the `lhu` of the reply cell leaves zx16 v in
   the result register; the reply cell is carried in `le2` form so load_post's fold_lit_load does not vm_compute
   a symbolic byte list). *)
Lemma f11_zx16 : forall V, 0 <= V < 2 ^ 16 -> zx16 (Z_to_bv 64 V) = Z_to_bv 64 V.
Proof.
  intros V HV. unfold zx16. rewrite unsigned_lit by (change (2 ^ 16) with 65536 in HV; lia).
  rewrite Z.mod_small by (change (2 ^ 16) with 65536 in HV; lia). reflexivity.
Qed.

(* The kind-name table is 112 bytes (the b5_KN carry of the exit cut is transported across the ingest write). *)
Lemma f11_kn_len : length kind_name_bytes = 112%nat.
Proof.
  unfold kind_name_bytes, kind_name_addrs. cbn [map concat].
  rewrite !length_app, !length_le8. reflexivity.
Qed.

(* Every read-only image byte lies below GT, the top of the image's writable data: the loaded segments' tops,
   checked by computation (Tac_slot.img_tops_ok's bound, read through a find_segment). The frame is at or above
   GT (fra_app), so a write into the frame keeps ro_agree -- the low-memory form sl_ro_keep asks for does not
   hold of a frame in the side stack, which may lie below LOWMEM_END. *)
Lemma f11_ro_gt : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < AC.GT.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  assert (Htops : seg_tops_below rsegs AC.GT = true) by (vm_compute; reflexivity).
  destruct (find_segment_below rsegs AC.GT (bv_unsigned a) 1 s Htops E ltac:(lia)) as [L|L];
    [exact L | discriminate L].
Qed.

Lemma f11_ro_keep : forall W mem mem',
  ro_agree rsegs mem -> Frame.munch W mem mem' -> (forall x, 0 <= x < AC.GT -> Frame.outside W x) ->
  ro_agree rsegs mem'.
Proof.
  intros W mem mem' Hro MU Hlo. apply (ro_agree_same rsegs mem mem' Hro).
  intros a Ha. apply f11_ro_gt in Ha. apply MU. apply Hlo.
  pose proof (bv_unsigned_in_range 64 a) as Hr. lia.
Qed.

(* From here on `getr` is A.Reusable.YK11.getr, the one SlotInv's `rg` and Contract's `aspZ` unfold to (Lib's
   PropExec.getr, which the imports above make the short name, has the same body but is a different constant,
   so `rewrite` with an `rg` fact would not find it). *)
Local Abbreviation getr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.getr (only parsing).

(* mkR_of regs is definitionally the explicit 31-slot register map. *)
Lemma f11_mkR_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot `getr regs r` to its carried concrete value, from H : rg regs r v. *)
Ltac f11_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* ---- the record-sum loop 0x8206c -> 0x820a4 ---- *)

(* One turn of the loop at 0x8206c, by induction on the number of turns left: the instrumented check of the byte
   at a0 = phi+34+i (its slow path 0x82098 and the error call 0x82c94 behind it NOT reached, since the byte lies
   in the addressable range [phi, phi+50)), then a4 += that byte and the counter a1 = n0-i down to 0. *)
Lemma f11_loop : forall (ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi n0 : Z) (bs : list byte)
  (Q : machine_state -> Prop),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat -> 1 <= n0 <= 15 ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  (forall a0' a5' a6' a7' : word,
     LE.evt rsegs Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' (Z_to_bv 64 0) a2 a3
         (Z_to_bv 64 (psum (skipn 34 bs) (Z.to_nat n0))) a5' a6' a7'
         s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x820a4) fc None m (seg_rom rsegs))) ->
  forall (k i : nat) (a6' a7' : word), (i + k = Z.to_nat n0)%nat -> (0 < k)%nat ->
  LE.evt rsegs Q
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 34 + Z.of_nat i))
         (Z_to_bv 64 (n0 - Z.of_nat i)) a2 a3 (Z_to_bv 64 (psum (skipn 34 bs) i))
         (Z_to_bv 64 (phi + 34 + Z.of_nat i)) a6' a7'
         s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
       Fr (Z_to_bv 64 0x8206c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m phi n0 bs Q
    Hphi0 Hphi50 Hlen Hn0 HB HA Hjoin.
  induction k as [|k IH]; intros i a6' a7' Hik Hk; [lia|].
  (* the instrumented check of the byte at phi+34+i *)
  assert (Haddr1 : addressable m (phi + 34 + Z.of_nat i) 1).
  { replace (phi + 34 + Z.of_nat i) with (phi + (34 + Z.of_nat i)) by lia.
    apply (addressable_sub m phi 50 (34 + Z.of_nat i) 1 HA); lia. }
  destruct (sl_shadow1 m (phi + 34 + Z.of_nat i) Haddr1) as (sb & RDsb & OKsb & ISsb).
  pose proof (rd_byte rsegs m phi bs (34 + i)%nat HB ltac:(lia)) as RDb.
  replace (Z.of_nat (34 + i)) with (34 + Z.of_nat i) in RDb by lia.
  replace (phi + (34 + Z.of_nat i)) with (phi + 34 + Z.of_nat i) in RDb by lia.
  pose proof (psum_range (skipn 34 bs) i) as PR.
  (* the join at 0x8207c (the check passed), with the slow path's scratch register a7 generalized *)
  assert (G4 : forall y7 : word,
    LE.evt rsegs Q (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 34 + Z.of_nat i))
       (Z_to_bv 64 (n0 - Z.of_nat i)) a2 a3 (Z_to_bv 64 (psum (skipn 34 bs) i))
       (Z_to_bv 64 (phi + 34 + Z.of_nat i)) (sxb sb) y7
       s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 0x8207c) fc None m (seg_rom rsegs))).
  { intro y7.
    step. (* lbu a6,0(a5) *)
    step. (* addi a1,a1,-1 *)
    step. (* addi a0,a0,1 *)
    step. (* add a4,a4,a6 *)
    rewrite <- (f11_nth_skipn byte (Z_to_bv 8 0) 34 bs i).
    rewrite psum_S_zxb.
    step. (* addi a5,a5,1 *)
    step. (* bnez a1,8206c *)
    destruct k as [|k'].
    - (* last turn: a1 = 0, not taken; 0x82094 j 820a4 *)
      replace (n0 - Z.of_nat i + -1) with 0 by lia.
      rewrite bv_eqb_refl. cbn [negb]. cbv iota.
      step. (* j 820a4 *)
      assert (E : (S i = Z.to_nat n0)%nat) by lia. rewrite <- E in Hjoin.
      apply Hjoin.
    - (* more turns: a1 = n0-(i+1) <> 0, taken back to 0x8206c *)
      replace (n0 - Z.of_nat i + -1) with (n0 - Z.of_nat (S i)) by lia.
      rewrite (rc_neq0_64 (n0 - Z.of_nat (S i))) by lia. cbn [negb]. cbv iota.
      replace (phi + 34 + Z.of_nat i + 1) with (phi + 34 + Z.of_nat (S i)) by lia.
      apply (IH (S i)); lia. }
  (* 0x8206c-0x82078: the shadow byte of phi+34+i and the branch on it *)
  step. (* srli a6,a0,3 *)
  step. (* add a6,a6,s10 *)
  rewrite (unsigned_lit (phi + 34 + Z.of_nat i)) by lia.
  step. (* lb a6,0(a6) *)
  step. (* bnez a6,82098 *)
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb)) by (pose proof (rc_byte_signed sb); lia).
  destruct (Z.eqb_spec (bv_signed sb) 0) as [Z0|Z0].
  - (* the shadow byte is 0: not taken, the byte is in an addressable range *)
    cbn [negb]. cbv iota. apply (G4 a7').
  - (* the shadow byte is not 0: the slow path 0x82098, whose compare sends the error call 0x82c94 away *)
    cbn [negb]. cbv iota.
    step. (* andi a7,a0,7 *)
    rewrite (unsigned_lit (phi + 34 + Z.of_nat i)) by lia. rewrite rc_land7.
    step. (* bge a7,a6,82c94 *)
    unfold sxb. rewrite (rc_lts_signed ((phi + 34 + Z.of_nat i) mod 8) (bv_signed sb))
      by (pose proof (rc_byte_signed sb); pose proof (Z.mod_pos_bound (phi + 34 + Z.of_nat i) 8 ltac:(lia)); lia).
    replace ((phi + 34 + Z.of_nat i) mod 8 <? bv_signed sb) with true
      by (symmetry; apply Z.ltb_lt; destruct OKsb as [H|H]; lia).
    cbn [negb]. cbv iota.
    step. (* j 8207c *)
    apply (G4 (Z_to_bv 64 ((phi + 34 + Z.of_nat i) mod 8))).
Qed.

(* The whole loop plus the mod-128 test 0x820a4-0x820a8 (the abort pair at 0x82bf4 NOT reached), from the loop
   head 0x8206c to 0x820ac. *)
Lemma f11_fd4_evt : forall (ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
                            a6i a7i : word)
  (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi n0 : Z) (bs : list byte),
  0 <= phi -> phi + 50 <= 2 ^ 64 -> length bs = 50%nat -> 1 <= n0 <= 15 ->
  psum (skipn 34 bs) (Z.to_nat n0) mod 128 = 0 ->
  bytes_at rsegs m phi bs -> addressable m phi 50 ->
  LE.evt rsegs
    (fun ms' => exists (a0' a4' a5' a6' a7' : word),
       ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' (Z_to_bv 64 0) a2 a3 a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
                Fr (Z_to_bv 64 0x820ac) fc None m (seg_rom rsegs))
    (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (phi + 34)) (Z_to_bv 64 n0) a2 a3 (Z_to_bv 64 0)
             (Z_to_bv 64 (phi + 34)) a6i a7i
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x8206c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 a6i a7i Fr fc m phi n0 bs
    Hphi0 Hphi50 Hlen Hn0 Hsum HB HA.
  pose proof (psum_range (skipn 34 bs) (Z.to_nat n0)) as PR.
  (* 0x820a4 andi a0,a4,127 ; 0x820a8 bnez a0,82bf4 not taken: the record sum is 0 mod 128 *)
  match goal with
  | |- LE.evt _ ?P _ =>
    assert (Hjoin : forall a0' a5' a6' a7' : word,
      LE.evt rsegs P
        (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0' (Z_to_bv 64 0) a2 a3
             (Z_to_bv 64 (psum (skipn 34 bs) (Z.to_nat n0))) a5' a6' a7'
             s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
           Fr (Z_to_bv 64 0x820a4) fc None m (seg_rom rsegs)))
  end.
  { intros a0' a5' a6' a7'.
    step. (* andi a0,a4,127 *)
    step. (* bnez a0,82bf4 *)
    rewrite (rc_z127 (psum (skipn 34 bs) (Z.to_nat n0))) by lia.
    rewrite Hsum. cbn [Z.eqb negb]. cbv iota.
    apply evt_done. do 5 eexists. reflexivity. }
  replace (Z_to_bv 64 (phi + 34)) with (Z_to_bv 64 (phi + 34 + Z.of_nat 0)) by (f_equal; cbn; lia).
  replace (Z_to_bv 64 n0) with (Z_to_bv 64 (n0 - Z.of_nat 0)) by (f_equal; cbn; lia).
  exact (f11_loop ra0 sp gp tp t0 t1 t2 s0 s1v a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6
           Fr fc m phi n0 bs _ Hphi0 Hphi50 Hlen Hn0 HB HA Hjoin (Z.to_nat n0) 0%nat a6i a7i
           ltac:(lia) ltac:(lia)).
Qed.

(* The allocator laws this file takes apart (a_laws_blocks, a_laws_store), each taken apart once here and used by
   name at every site (a Theorem Labs lane's rule for generated laws until N+1). Each law is split by decompose and each fact
   is found by its type, not by its position: a conjunct appended at any level is one more unused hypothesis. *)
Section S_laws.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

Lemma f11_blocks : forall Bs AH own lo hi, AC.a_laws Bs AH own lo hi ->
  forall H mem md p n, AH H mem md -> In (p, n) H ->
  p + n <= lo mem md /\ (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs Bs mem a).
Proof.
  intros Bs AH own lo hi L H mem md p n HAH Hin.
  pose proof (AC.a_laws_blocks _ _ _ _ _ L H mem md p n HAH Hin) as X. decompose [and] X. clear X.
  split; [assumption|].
  intros a Ha.
  lazymatch goal with HP : forall x, p <= x < p + n -> _ |- _ => pose proof (HP a Ha) as Y end.
  decompose [and] Y. split; assumption.
Qed.

Lemma f11_store : forall Bs AH own lo hi, AC.a_laws Bs AH own lo hi ->
  forall H mem mem' md, AH H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (lo mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AH H mem' md /\ (forall a, own H mem' md a <-> own H mem md a) /\ lo mem' md = lo mem md /\
  hi mem' md = hi mem md.
Proof.
  intros Bs AH own lo hi L H mem mem' md HAH Hst Hwm.
  pose proof (AC.a_laws_store _ _ _ _ _ L H mem mem' md HAH Hst Hwm) as X. decompose [and] X. clear X.
  split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

End S_laws.

Section S.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract (lib/A/Prog/reac_identity_ingest_c.v), taken as a Section Hypothesis. *)
Hypothesis HING : reac_identity_ingest_contract.

(* ---- 0x820ac -> 0x820f8: the two checked record bytes, the 16-bit compare and the ingest call ---- *)
Lemma f11_014_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 a0i a1i a4i a5i a6i a7i : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (phi fr A lo len : Z) (G idb pb : list byte),
    length G = 50%nat -> 0 < phi -> phi + 50 <= 2 ^ 64 -> len = ir_s G - 13 -> 14 <= ir_s G <= 23 ->
    bytes_at rsegs m phi G -> addressable m phi 50 ->
    0 <= A < 2 ^ 64 -> q64 m (A + 256) (fr + 256) -> q64 m (A + 144) (fr + 2688) ->
    bytes_at rsegs m (fr + 256) (reply_addr G) ->
    0 < fr -> fr + FRAME_BYTES <= 2 ^ 64 -> (fr + 2688) mod 2 = 0 ->
    rw_cells rsegs m (fr + 2688) [CB 38 idb] ->
    length pb = Z.to_nat len -> bytes_at rsegs m (phi + 38) pb ->
    (phi + 38 + len <= fr + 2688 \/ fr + 2688 + 38 <= phi + 38) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    (fr + 2688 + 38 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= fr + 2688) ->
    (phi + 38 + len <= bv_unsigned sp - 32 \/ bv_unsigned sp <= phi + 38) ->
    asan_cells m -> shadow_rw m ->
    addressable m (fr + 2688) 38 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       Frame.outside (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) x) ->
    LE.evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ING idb (cp_v G 36 * 256 + cp_v G 37) pb)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x820f8) fc None m' (seg_rom rsegs) /\
         Frame.munch (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) m m' /\
         Frame.wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (fr + 2688) [CB 38 (snd (ING idb (cp_v G 36 * 256 + cp_v G 37) pb))])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 len)
               a4i a5i a6i a7i
               s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x820ac) fc None m (seg_rom rsegs)).
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros ra0 sp gp tp t0 t1 t2 s0 s2 s3 s4 s5 s7 s8 s9 s11 t3 t4 t5 t6 a0i a1i a4i a5i a6i a7i Fr fc m
    phi fr A lo len G idb pb HG Hphi0 Hphi50 Hlen Hs HB HA HAr Hq256 Hq144 Hra Hfr0 Hfrub Hid2 Hidrw Hpbl Hpb
    Hdj Hstk Hlo Hidw Hpw HAC HSW HidA HOUT.
  pose proof (cp_v_range' G 36) as R36. pose proof (cp_v_range' G 37) as R37.
  assert (Hlen0 : 1 <= len <= 10) by lia.
  (* the two instrumented checks: the bytes phi+36 and phi+37 lie in the addressable range [phi, phi+50) *)
  assert (Ha36 : addressable m (phi + 36) 1)
    by (apply (addressable_sub m phi 50 36 1 HA); lia).
  assert (Ha37 : addressable m (phi + 37) 1)
    by (apply (addressable_sub m phi 50 37 1 HA); lia).
  destruct (sl_shadow1 m (phi + 36) Ha36) as (sb1 & RD1 & OK1 & IS1).
  destruct (sl_shadow1 m (phi + 37) Ha37) as (sb2 & RD2 & OK2 & IS2).
  pose proof (rd_byte rsegs m phi G 36 HB ltac:(lia)) as RD36.
  pose proof (rd_byte rsegs m phi G 37 HB ltac:(lia)) as RD37.
  change (Z.of_nat 36) with 36 in RD36. change (Z.of_nat 37) with 37 in RD37.
  pose proof (f11_rd8 m (A + 256) _ Hq256 ltac:(apply length_le8)) as RD256.
  pose proof (f11_rd8 m (A + 144) _ Hq144 ltac:(apply length_le8)) as RD144.
  (* The reply cell in `le2` form, so the `lhu` at 0x820e8 does not make load_post's fold_lit_load vm_compute
     a symbolic byte list (the hang of the cons form [cp_b G 37; cp_b G 36]). *)
  assert (Hra2 : bytes_at rsegs m (fr + 256) (le2 (Z_to_bv 64 (cp_v G 36 * 256 + cp_v G 37)))).
  { unfold reply_addr in Hra. rewrite <- (rc_le2_pair (cp_b G 37) (cp_b G 36)) in Hra.
    change (bv_unsigned (cp_b G 36)) with (cp_v G 36) in Hra.
    change (bv_unsigned (cp_b G 37)) with (cp_v G 37) in Hra. exact Hra. }
  pose proof (f11_rd2 m (fr + 256) _ Hra2 ltac:(apply length_le2)) as RDa.
  (* the ingest call at 0x820f4, from the join at 0x820e0 *)
  assert (J48 : forall y6 : word,
    LE.evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ING idb (cp_v G 36 * 256 + cp_v G 37) pb)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x820f8) fc None m' (seg_rom rsegs) /\
         Frame.munch (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) m m' /\
         Frame.wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (fr + 2688) [CB 38 (snd (ING idb (cp_v G 36 * 256 + cp_v G 37) pb))])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 37))
               (Z_to_bv 64 (cp_v G 36 * 256 + cp_v G 37)) (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 len)
               (zxb (nth 36 G (Z_to_bv 8 0))) (sxb sb2) y6 a7i
               s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x820e0) fc None m (seg_rom rsegs))).
  { intro y6.
    step. (* lbu a0,0(a0) : the byte phi+37 *)
    step. (* slli a4,a4,8 *)
    step. (* or a0,a4,a0 *)
    rewrite (rc_pack2 (nth 37 G (Z_to_bv 8 0)) (nth 36 G (Z_to_bv 8 0))).
    step. (* bne a0,a1,82bf4 : not taken *)
    change (bv_unsigned (nth 36 G (Z_to_bv 8 0))) with (cp_v G 36).
    change (bv_unsigned (nth 37 G (Z_to_bv 8 0))) with (cp_v G 37).
    rewrite bv_eqb_refl. cbn [negb]. cbv iota.
    step. (* ld a0,144(s1) : the identity record fr+2688 *)
    step. (* jal reac_identity_ingest *)
    pose proof HING as HI. unfold reac_identity_ingest_contract, REAC_IDENTITY_INGEST in HI.
    eapply evt_cut.
    { eapply (HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m lo (fr + 2688)
                 (cp_v G 36 * 256 + cp_v G 37) (phi + 38) len idb pb).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - lia.
      - intros _. split; [exact Hid2 | exact Hidrw].
      - exact Hpbl.
      - intros _ _. exact Hpb.
      - intros _ _ _. lia.
      - exact Hstk.
      - unfold REAC_IDENTITY_INGEST_FRAME. lia.
      - intros _. unfold REAC_IDENTITY_INGEST_FRAME. lia.
      - intros _ _. unfold REAC_IDENTITY_INGEST_FRAME. lia.
      - exact HAC.
      - exact HSW.
      - intros _. exact HidA.
      - intros _ _. apply (addressable_sub m phi 50 38 len HA); lia.
      - exact HOUT. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      E & MU & WM & MI & ST & _ & HRW).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 532728)) with (Z_to_bv 64 532728)
      by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    assert (Href : ingest_refused (fr + 2688) (phi + 38) len = false).
    { unfold ingest_refused. rewrite (proj2 (Z.eqb_neq (fr + 2688) 0) ltac:(lia)).
      rewrite (proj2 (Z.eqb_neq (phi + 38) 0) ltac:(lia)). rewrite andb_false_r. reflexivity. }
    unfold ingest_ret. rewrite Href.
    apply evt_done.
    exists (Z_to_bv 64 532728), t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    exact (HRW Href). }
  (* the join at 0x820c8: the check of phi+36 passed (its slow path 0x829b4 writes a5) *)
  assert (J30 : forall y5 : word,
    LE.evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ING idb (cp_v G 36 * 256 + cp_v G 37) pb)))
                       a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x820f8) fc None m' (seg_rom rsegs) /\
         Frame.munch (reac_identity_ingest_W (bv_unsigned sp) (fr + 2688)) m m' /\
         Frame.wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\
         stk rsegs m' lo (bv_unsigned sp) /\
         rw_cells rsegs m' (fr + 2688) [CB 38 (snd (ING idb (cp_v G 36 * 256 + cp_v G 37) pb))])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 A) (Z_to_bv 64 (phi + 36))
               (Z_to_bv 64 (cp_v G 36 * 256 + cp_v G 37)) (Z_to_bv 64 (phi + 38)) (Z_to_bv 64 len)
               (sxb sb1) y5 a6i a7i
               s2 s3 s4 s5 (Z_to_bv 64 (phi + 18)) s7 s8 s9 (Z_to_bv 64 ASAN_K) s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x820c8) fc None m (seg_rom rsegs))).
  { intro y5.
    step. (* addi a0,s6,19 : phi+37 *)
    step. (* srli a4,a0,3 *)
    rewrite (unsigned_lit (phi + 37)) by lia.
    step. (* add a4,a4,s10 *)
    step. (* lb a5,0(a4) : the shadow byte of phi+37 *)
    step. (* lbu a4,18(s6) : the byte phi+36 *)
    step. (* bnez a5,829c0 *)
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb2)) by (pose proof (rc_byte_signed sb2); lia).
    destruct (Z.eqb_spec (bv_signed sb2) 0) as [Z2|Z2].
    - cbn [negb]. cbv iota. apply (J48 a6i).
    - cbn [negb]. cbv iota.
      step. (* andi a6,a0,7 *)
      rewrite (unsigned_lit (phi + 37)) by lia. rewrite rc_land7.
      step. (* bge a6,a5,82ccc *)
      unfold sxb. rewrite (rc_lts_signed ((phi + 37) mod 8) (bv_signed sb2))
        by (pose proof (rc_byte_signed sb2); pose proof (Z.mod_pos_bound (phi + 37) 8 ltac:(lia)); lia).
      replace ((phi + 37) mod 8 <? bv_signed sb2) with true
        by (symmetry; apply Z.ltb_lt; destruct OK2 as [H|H]; lia).
      cbn [negb]. cbv iota.
      step. (* j 820e0 *)
      apply (J48 (Z_to_bv 64 ((phi + 37) mod 8))). }
  (* 0x820ac-0x820c4: phi+36, its shadow byte, the u16 at pa = fr+256 and the branch *)
  step. (* addi a0,s6,18 : phi+36 *)
  step. (* srli a1,a0,3 *)
  rewrite (unsigned_lit (phi + 36)) by lia.
  step. (* add a1,a1,s10 *)
  step. (* lb a4,0(a1) : the shadow byte of phi+36 *)
  step. (* ld a1,256(s1) : pa = fr+256 *)
  step. (* lhu a1,0(a1) : the reply address (le2 form; load_post's zext_extract_le2 leaves zx16) *)
  rewrite (f11_zx16 (cp_v G 36 * 256 + cp_v G 37)) by (change (2 ^ 16) with 65536; lia).
  step. (* bnez a4,829b4 *)
  unfold sxb. rewrite (rc_eqb0_signed (bv_signed sb1)) by (pose proof (rc_byte_signed sb1); lia).
  destruct (Z.eqb_spec (bv_signed sb1) 0) as [Z1|Z1].
  - cbn [negb]. cbv iota. apply (J30 a5i).
  - cbn [negb]. cbv iota.
    step. (* andi a5,a0,7 *)
    rewrite (unsigned_lit (phi + 36)) by lia. rewrite rc_land7.
    step. (* bge a5,a4,82cc8 *)
    unfold sxb. rewrite (rc_lts_signed ((phi + 36) mod 8) (bv_signed sb1))
      by (pose proof (rc_byte_signed sb1); pose proof (Z.mod_pos_bound (phi + 36) 8 ltac:(lia)); lia).
    replace ((phi + 36) mod 8 <? bv_signed sb1) with true
      by (symmetry; apply Z.ltb_lt; destruct OK1 as [H|H]; lia).
    cbn [negb]. cbv iota.
    step. (* j 820c8 *)
    apply (J30 (Z_to_bv 64 ((phi + 36) mod 8))).
Qed.

(* ---- ENTRY 2 (0x820ac) to the EXIT (0x820f8). Cuts SlotInv.Inv_A820ac_at -> SlotInv.Inv_A820f8_at. The carry
   (FLSI, LK, b5_C, b5_K, b5_RC) is transported across the callee's two-interval write [sp-32, sp) and
   [fr+2688, fr+2726): FRA by sl_fr_cl (its old mem_inv slot is FSREC, via fsrec_stklo) and sl_fra_move; ENT by
   ent_store / ent_mat. The ingest contract needs no mem_inv premise. The record it writes at fr + 2688 is the
   exit's IDb1. ---- *)
Lemma seg_F11_014 : forall j,
  Hat B APIf ra (Inv_A820f8_at (fx := fx) B APIf ra) j -> Hat B APIf ra (Inv_A820ac_at (fx := fx) B APIf ra) j.
Proof. pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFShv.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    Hgn & Hj & HHB & HFLSI & HLK & HC & HbK & HbRC & H50 & Hsum & Hok & HbRP & Ha1 & Ha2 & Ha3 & HIDj &
    H17 & H240 & HPF).
  subst c. rewrite SEGS.
  assert (Hir : ir (flen g j) (t_g (g_in g) j) = true)
    by (unfold reply_ok in Hok; apply andb_prop in Hok; tauto).
  destruct (ir_bytes _ _ Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsr & _ & _ & _ & _).
  pose proof (f11_tg_len (g_in g) j) as HGl.
  pose proof (fra_win B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
    as (Hapart & HfrA9 & HFSfr & Hfrw).
  pose proof (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGTfr & Happfr).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  destruct HC as (Hs7 & Hr18 & (A & H9 & HA64 & HSPILL & Hq232) & HbPH & HbFR & HbFS & HbKN & HFGj & HFSj).
  destruct HSPILL as (Hq248 & Hq256 & Hq144 & Hq184 & Hq208 & Hq64 & Hq72 & Hq80 & Hq272 & Hq264).
  destruct HbPH as (HPHg & HPHpl & HPHfs).
  destruct HbFR as (HfgA & HidA & HFGb & HFGl).
  destruct HbFS as (HFScont & DB & HDBw & HDBr).
  destruct HbKN as (HKNb & HKNa).
  destruct HbK as (Hs4 & Hs6 & Hs8 & Hs9 & Hsp280 & Hu176 & Hargs).
  destruct HbRC as (Hpa2 & Hpp8 & Hpn8).
  destruct HLK as (Hj' & Hr21 & HOUR).
  destruct HFLSI as (((sp40 & sp120 & sp136 & sp160 & sp168 & sp176 & sp208 & sp248p & Hour6 & HINb0 & HINp0 &
                       sp184p & sp256p & sp264p & sp272p & sp32p)
    & sp128 & Hfrstk & sp144 & Hid17)
    & sp216 & sp224 & sp248 & HIN & HFLC).
  destruct HFLC as (fc256 & fc184 & fc192 & fc80 & fc88 & fc96 & fc272 & fc264 & fcfg & fcid & fc72 & fc64 & fc56 & fc48).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HFN : FN_STACK = 1044480) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HGTv : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HFGK : REAC_CTRL_IDENTITY_FRAGMENT_K = 4656) by (vm_compute; reflexivity).
  assert (HFSv : AC.FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (Hspu : bv_unsigned (getr regs 2) = sp) by (unfold AC.aspZ in Haspz; exact Haspz).
  rewrite Haspz in Hwlo.
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (Hspb : 0 <= sp < 2 ^ 64) by lia.
  (* FRA's spill base and the carry's are the same register value *)
  assert (HA0b : 0 <= A0 < 2 ^ 64) by lia.
  assert (EA0 : A0 = A)
    by (pose proof (rg_eq64 regs 9 A0 A Hr9 H9) as Hm; rewrite !Z.mod_small in Hm by lia; exact Hm).
  subst A0.
  assert (Hfr0 : 0 < fr) by lia.
  assert (Hfrub : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happfr (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. destruct Ha as [Ha|Ha]; lia. }
  assert (Hfrub2 : fr + FRAME_BYTES <= 2 ^ 64) by lia.
  (* the frame against the callee's window (fra_frame, K = 32) *)
  assert (Hfrsp : fr + FRAME_BYTES <= sp - 32 \/ sp <= fr).
  { destruct (Hapart 32 ltac:(unfold FN_STACK; lia)) as [Hd|Hd]; rewrite Haspz in Hd; [left|right]; lia. }
  (* the record placements of the long arm *)
  destruct (HPHpl H50) as (Hplfr & Hplsp).
  rewrite Haspz in Hplsp.
  pose proof (HPHg H50) as HG.
  (* s6 = phi + 18 (t_big holds on the long arm) *)
  assert (Hbig : t_big (g_in g) j = true) by (unfold t_big, flen in *; apply Z.leb_le; exact H50).
  rewrite Hbig in Hs6.
  (* the record block: 0 < phi, phi + 50 <= 2^64, 50 addressable bytes *)
  destruct HHB as (Hphinz & HAd).
  pose proof HAd as (Hp0 & _ & Hpe & _).
  unfold AC.a_size in Hpe. rewrite Z.max_l in Hpe by lia.
  assert (Hphi0 : 0 < phi) by lia.
  assert (Hphi50 : phi + 50 <= 2 ^ 64) by lia.
  assert (Haddr50 : addressable mem phi 50).
  { rewrite <- (Z.add_0_r phi).
    apply (addressable_sub mem phi (AC.a_size (flen g j)) 0 50 HAd); unfold AC.a_size; lia. }
  (* every frame metadata byte is the metadata byte of a frame byte, so it is not app memory *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happfr _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  (* the ingest arguments *)
  set (len := ir_s (t_g (g_in g) j) - 13).
  set (ad := cp_v (t_g (g_in g) j) 36 * 256 + cp_v (t_g (g_in g) j) 37).
  set (pb := firstn (Z.to_nat len) (skipn 38 (t_g (g_in g) j))).
  assert (Hlen1 : 1 <= len <= 10) by (unfold len; lia).
  assert (Hpbl : length pb = Z.to_nat len) by (unfold pb; apply f11_pb_len; [exact HGl | lia]).
  assert (Hpb : bytes_at rsegs mem (phi + 38) pb).
  { unfold pb. apply rc_bytes_first.
    pose proof (rc_bytes_skip rsegs mem phi (t_g (g_in g) j) 38 HG ltac:(lia)) as HH.
    change (Z.of_nat 38) with 38 in HH. exact HH. }
  assert (Hid2 : (fr + 2688) mod 2 = 0).
  { pose proof (Z.mod_eq fr 32 ltac:(lia)) as X. rewrite Hfrm in X.
    replace (fr + 2688) with ((16 * (fr / 32) + 1344) * 2) by lia. apply Z_mod_mult. }
  (* the identity record of turn j (IDj), as the ingest contract asks for it *)
  destruct HIDj as (HIDB & HIDok).
  set (idb := t_ID (g_in g) j).
  pose proof (f11_tID_len (g_in g) j) as Hidbl.
  pose proof (f11_rwb mem (fr + 2688) 38 idb fr (fr + FRAME_BYTES) Hfrstk ltac:(lia) ltac:(cbn; lia) Hidbl HIDB)
    as Hidrw.
  assert (HSTw : stk rsegs mem (sp - 32) sp).
  { destruct (stk_split rsegs mem (AC.aspZ regs - FN_STACK) (sp - 32) (AC.aspZ regs) Hwstk
                ltac:(unfold FN_STACK; lia)) as (_ & H). rewrite Haspz in H. exact H. }
  (* the window of the call: its two intervals *)
  set (W := reac_identity_ingest_W sp (fr + 2688)).
  assert (HWeq : W = [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)])
    by (unfold W, reac_identity_ingest_W, REAC_IDENTITY_INGEST_FRAME; reflexivity).
  assert (HWout : forall x, (x < sp - 32 \/ sp <= x) -> (x < fr + 2688 \/ fr + 2688 + 38 <= x) ->
            Frame.outside W x).
  { intros x H1 H2. rewrite HWeq. cbn [Frame.outside]. split; [lia|]. split; [lia | exact I]. }
  (* every byte below GT (the image) is outside W: the window is above HIGHMEM_BEG, the frame above GT *)
  assert (HWlo : forall x, 0 <= x < AC.GT -> Frame.outside W x).
  { intros x Hx. apply HWout; lia. }
  (* a frame-relative range is apart from the callee window on both frame arms *)
  assert (Hfrout : forall a n, fr <= a -> a + n <= fr + FRAME_BYTES -> 0 < n -> (a < sp - 32 \/ sp <= a)).
  { intros a n H1 H2 H3. destruct Hfrsp as [Hd|Hd]; [left | right]; lia. }
  assert (Hfrin : forall a n, fr <= a -> a + n <= fr + FRAME_BYTES -> (a + n <= sp - 32 \/ sp <= a)).
  { intros a n H1 H2. destruct Hfrsp as [Hd|Hd]; [left | right]; lia. }
  assert (HAW : all_app W).
  { rewrite HWeq. cbn [all_app]. split; [|split; [|exact I]].
    - intros a Ha. unfold app_mem. right. lia.
    - intros a Ha. apply Happfr. lia. }
  assert (HOUT : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            Frame.outside W x).
  { intros x Hx. apply HWout.
    - destruct Hx as [Hx|[Hx|Hx]];
        [ unfold GOT_CELL_K in Hx | unfold CELL_K in Hx | pose proof (f11_sh_lt x Hx) as Hs ];
        unfold LOWMEM_END in *; lia.
    - destruct Hx as [Hx|[Hx|Hx]].
      + unfold GOT_CELL_K in Hx. lia.
      + unfold CELL_K in Hx. lia.
      + (* a metadata byte lies between the low and high app ranges; the record is in one of them *)
        pose proof (f11_sh_lt x Hx) as (Hsl1 & Hsl2).
        pose proof (Happfr (fr + 2688) ltac:(lia)) as Hap1.
        pose proof (Happfr (fr + 2725) ltac:(lia)) as Hap2.
        unfold app_mem in Hap1, Hap2. lia. }
  (* the run *)
  apply (sl_run_lib regs (Z_to_bv 64 0x820ac) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x820f8 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\
       getr R0 10 = Z_to_bv 64 (fst (ING idb ad pb)) /\
       Frame.munch W mem mem' /\ Frame.wmono rsegs mem mem' /\
       stk rsegs mem' (sp - 32) sp /\
       rw_cells rsegs mem' (fr + 2688) [CB 38 (snd (ING idb ad pb))])
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f11_mkR_expand.
    f11_slot H9. f11_slot Hs6. f11_slot Ha2. f11_slot Ha3. f11_slot Hr26.
    eapply LE.evt_mono.
    { apply (f11_014_evt (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
               (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 27) (getr regs 28) (getr regs 29)
               (getr regs 30) (getr regs 31) (getr regs 10) (getr regs 11) (getr regs 14) (getr regs 15)
               (getr regs 16) (getr regs 17)
               _ _ mem phi fr A (sp - 32) len (t_g (g_in g) j) idb pb);
        rewrite ?Hspu.
      - exact HGl.
      - exact Hphi0.
      - exact Hphi50.
      - reflexivity.
      - lia.
      - exact HG.
      - exact Haddr50.
      - exact HA64.
      - exact Hq256.
      - exact Hq144.
      - exact (f11_lrwB mem (fr + 256) 2 _ (proj1 HbRP)).
      - exact Hfr0.
      - exact Hfrub2.
      - exact Hid2.
      - exact Hidrw.
      - exact Hpbl.
      - exact Hpb.
      - destruct Hplfr as [Hd|Hd]; [left; unfold len; lia | right; unfold len; lia].
      - exact HSTw.
      - lia.
      - destruct Hfrsp as [Hd|Hd]; [left | right]; lia.
      - destruct Hplsp as [Hd|Hd]; [left; unfold len; lia | right; lia].
      - exact (AsanRTInv.RT_cells _ _ _ HRT).
      - exact (AsanRTInv.RT_shadow_rw _ _ _ HRT).
      - exact HidA.
      - exact HOUT. }
    { intros ms' (ra' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
        E & MU & WM & _ & ST & HRW).
      rewrite Hspu in MU, ST.
      eexists _, (Z_to_bv 64 0x820f8), m'. split; [exact E|].
      repeat (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM|]. split; [exact ST | exact HRW]. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 & Er22 & Er23 &
      Er24 & Er25 & Er26 & Er10 & MU & WM & ST' & HRW) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (fst (ING idb ad pb))) by (rewrite Hreg; exact Er10).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    assert (Hkeep : forall a n, 0 <= n -> (a + n <= sp - 32 \/ sp <= a) -> (a + n <= fr + 2688 \/ fr + 2726 <= a) ->
              Frame.disjoint_from W a n).
    { intros a n Hn H1 H2. rewrite HWeq. cbn [Frame.disjoint_from]. split; [lia|]. split; [lia | exact I]. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
              (exists b, mbyte rsegs mem' q = Some b)).
    { intros q Hq (b & Hb).
      destruct (Z_lt_le_dec q (fr + 2688)) as [Hlt|Hge];
        [|destruct (Z_lt_le_dec q (fr + 2688 + 38)) as [Hlt2|Hge2]].
      - destruct (Z_lt_le_dec q (sp - 32)) as [Hs1|Hs1]; [|destruct (Z_lt_le_dec q sp) as [Hs2|Hs2]].
        + exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
          rewrite MState.unsigned_lit by lia. apply HWout; lia.
        + destruct (rc_stk_mrd rsegs mem' (sp - 32) sp q ST' ltac:(lia)) as (b2 & Hb2).
          exists b2. exact Hb2.
        + exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
          rewrite MState.unsigned_lit by lia. apply HWout; lia.
      - destruct (rc_rw_mrd rsegs mem' (fr + 2688) 38 _ q HRW ltac:(cbn; lia)) as (b2 & Hb2).
        exists b2. exact Hb2.
      - destruct (Z_lt_le_dec q (sp - 32)) as [Hs1|Hs1]; [|destruct (Z_lt_le_dec q sp) as [Hs2|Hs2]].
        + exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
          rewrite MState.unsigned_lit by lia. apply HWout; lia.
        + destruct (rc_stk_mrd rsegs mem' (sp - 32) sp q ST' ltac:(lia)) as (b2 & Hb2).
          exists b2. exact Hb2.
        + exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
          rewrite MState.unsigned_lit by lia. apply HWout; lia. }
    (* AH, image ownership, stklo, stkhi across the write *)
    assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem' md /\
      (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem' md a
             <-> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md a) /\
      AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
        AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
      AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
        AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [(Hs50 & Hspfr & Hreal)|(Hs5f & HfsbS & HinFS & Hrec)].
      - assert (HstoreR : forall a, 0 <= a < 2 ^ 64 ->
          ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
              (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
          mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
        { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
          apply HWout.
          - destruct (Z_lt_le_dec a (sp - 32)) as [H1|H1]; [left; exact H1|].
            destruct (Z_lt_le_dec a sp) as [H2|H2]; [|right; exact H2].
            exfalso. apply Hns. unfold AC.a_store_ok. right; left. unfold FN_STACK in Hwlo. lia.
          - destruct (Z_lt_le_dec a (fr + 2688)) as [H1|H1]; [left; exact H1|].
            destruct (Z_lt_le_dec a (fr + 2688 + 38)) as [H2|H2]; [|right; exact H2].
            exfalso. apply Hns. unfold AC.a_store_ok. right; left.
            destruct (Hreal a ltac:(lia)) as (Hlo1 & Hhi1). lia. }
        destruct (f11_store _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH
                    HstoreR HwmL) as (HA1 & HA2 & HA3 & HA4).
        split; [exact HA1|]. split; [exact HA2|]. split; [exact HA3 | exact HA4].
      - (* side arm: the frame is FakeStack slot jj of class 6 (FSREC); the metadata lies below FS + 36864 *)
        destruct Hrec as (FS & jj & HFSw & HFSr & Hjj & Hfre & _ & _).
        destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FS HAH
                    HFSw HFSr) as (_ & HFSst & _ & _).
        assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
        rewrite HM6 in Hjj.
        assert (Hfrv : fr = FS + 6328320 + jj * 4096)
          by (rewrite Hfre; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
        assert (Hmeta : forall q, fs_meta FS q -> Frame.outside W q).
        { intros q Hq. pose proof (fs_meta_below FS q Hq) as Hb.
          apply HWout; unfold FN_STACK in Hwlo; lia. }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
          ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
              (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
          ~ (FS <= q < FS + AC.FS_SIZE) ->
          ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
          mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns Hnf _. apply MU. rewrite MState.unsigned_lit by lia.
          apply HWout.
          - destruct (Z_lt_le_dec q (sp - 32)) as [H1|H1]; [left; exact H1|].
            destruct (Z_lt_le_dec q sp) as [H2|H2]; [|right; exact H2].
            exfalso. apply Hns. unfold AC.a_store_ok. right; left. unfold FN_STACK in Hwlo. lia.
          - destruct (Z_lt_le_dec q (fr + 2688)) as [H1|H1]; [left; exact H1|].
            destruct (Z_lt_le_dec q (fr + 2688 + 38)) as [H2|H2]; [|right; exact H2].
            exfalso. apply Hnf. lia. }
        destruct (a_fs_ok_store_AH AC.ASYMS (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
                    W (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md FS LAWS HAH HFSw
                    ltac:(lia) ltac:(lia) MU HwmL Hpres Hmeta Hagree)
          as (HA1 & HA2 & HA3 & HA4).
        split; [exact HA1|]. split; [exact HA2|]. split; [exact HA3 | exact HA4]. }
    destruct HAHS as (HAH' & Hown & HSTKlo & HSTKhi).
    assert (Hwin' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (rc_stk_after rsegs W mem mem' (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU WM).
      intros x Hx.
      destruct (Z_lt_le_dec x (fr + 2688)) as [Hlt|Hge];
        [|destruct (Z_lt_le_dec x (fr + 2688 + 38)) as [Hlt2|Hge2]].
      - destruct (Z_lt_le_dec x (sp - 32)) as [Hs1|Hs1]; [left; apply HWout; lia|].
        destruct (Z_lt_le_dec x sp) as [Hs2|Hs2]; [|left; apply HWout; lia].
        right. exact (rc_stk_mrd rsegs mem' (sp - 32) sp x ST' ltac:(lia)).
      - right. exact (rc_rw_mrd rsegs mem' (fr + 2688) 38 _ x HRW ltac:(cbn; lia)).
      - destruct (Z_lt_le_dec x (sp - 32)) as [Hs1|Hs1]; [left; apply HWout; lia|].
        destruct (Z_lt_le_dec x sp) as [Hs2|Hs2]; [|left; apply HWout; lia].
        right. exact (rc_stk_mrd rsegs mem' (sp - 32) sp x ST' ltac:(lia)). }
    (* FSREC across the write: it stays at or above stklo except the frame body *)
    assert (HWstklo : forall x, x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
              ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x).
    { intros x Hlt Hnf. apply HWout.
      - left. unfold FN_STACK in Hwlo. lia.
      - destruct (Z_lt_le_dec x (fr + 2688)) as [H1|H1]; [left; exact H1|].
        destruct (Z_lt_le_dec x (fr + 2688 + 38)) as [H2|H2]; [|right; exact H2].
        exfalso. apply Hnf. lia. }
    (* q64 transport for the 416-byte spill area (it is above sp and above the frame) *)
    assert (Hq : forall off val, 0 <= off -> q64 mem (A + off) val -> q64 mem' (A + off) val).
    { intros off val Hoff Hqv. unfold q64 in *.
      apply (bytes_at_transport rsegs W mem mem' (A + off) (le8 (Z_to_bv 64 val)) Hqv MU).
      rewrite length_le8. apply Hkeep; lia. }
    (* the FLSI spills (exists-A form): their base is A *)
    assert (Tsp : forall off v, 0 <= off <= 300 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff (A' & HA' & Hqv).
      pose proof Hqv as Hb. unfold q64 in Hb. destruct Hb as (Hb0 & Hb1 & _).
      rewrite length_le8 in Hb1. change (Z.of_nat 8) with 8 in Hb1.
      pose proof (rg_eq64 regs 9 A' A HA' H9) as Hm.
      rewrite (Z.mod_small A) in Hm by lia.
      assert (HA'0 : 0 <= A').
      { destruct (Z_le_gt_dec 0 A') as [Hp|Hneg]; [exact Hp|exfalso].
        assert (HmA : A' mod 2 ^ 64 = A' + 2 ^ 64)
          by (rewrite <- (Z.mod_add A' 1 (2 ^ 64)) by lia; rewrite Z.mod_small; lia).
        rewrite HmA in Hm. lia. }
      rewrite (Z.mod_small A') in Hm by lia. subst A'.
      exists A. split; [unfold rg; rewrite Fr9; exact H9 | apply Hq; [lia | exact Hqv]]. }
    assert (TOUR : bytes_at rsegs mem' (fr + 2624) (OUR (g_in g))).
    { apply (bytes_at_transport rsegs W mem mem' (fr + 2624) (OUR (g_in g)) HOUR MU).
      rewrite OUR_length. apply Hkeep; [lia | apply Hfrin; lia | lia]. }
    assert (Hfrstk' : stk rsegs mem' fr (fr + FRAME_BYTES)).
    { apply (rc_stk_after rsegs W mem mem' fr (fr + FRAME_BYTES) Hfrstk MU WM).
      intros x Hx.
      destruct (Z_lt_le_dec x (fr + 2688)) as [Hlt|Hge];
        [|destruct (Z_lt_le_dec x (fr + 2688 + 38)) as [Hlt2|Hge2]].
      - left. apply HWout; [apply (Hfrout x 1); lia | lia].
      - right. exact (rc_rw_mrd rsegs mem' (fr + 2688) 38 _ x HRW ltac:(cbn; lia)).
      - left. apply HWout; [apply (Hfrout x 1); lia | lia]. }
    assert (THB : addressable mem' phi (AC.a_size (flen g j)))
      by exact (sl_addr_keep mem mem' W phi _ HAd MU HAW).
    assert (TG : bytes_at rsegs mem' phi (t_g (g_in g) j)).
    { apply (bytes_at_transport rsegs W mem mem' phi (t_g (g_in g) j) HG MU).
      rewrite HGl. apply Hkeep; [lia | | ].
      - destruct Hplsp as [Hd|Hd]; lia.
      - destruct Hplfr as [Hd|Hd]; lia. }
    assert (TFG : bytes_at rsegs mem' (fragb fr) (t_FG (g_in g) j)).
    { apply (bytes_at_transport rsegs W mem mem' (fragb fr) (t_FG (g_in g) j) HFGb MU).
      rewrite HFGl. unfold fragb. apply Hkeep; [lia | apply Hfrin; lia | lia]. }
    (* ---- push 13 group C: [A + 192], the guarded [A + 240] and the record group across the write ---- *)
    assert (Hb : forall a bs, bytes_at rsegs mem a bs ->
              Frame.disjoint_from W a (Z.of_nat (length bs)) -> bytes_at rsegs mem' a bs)
      by (intros a bs Hbs Hd; exact (bytes_at_transport rsegs W mem mem' a bs Hbs MU Hd)).
    (* a metadata byte lies between the two app ranges, so it is outside both written ranges *)
    assert (Hsh1 : forall a, in_shadow a -> Frame.disjoint_from W a 1).
    { intros a Ha. rewrite HWeq. cbn [Frame.disjoint_from].
      pose proof (f11_sh_lt a Ha) as (Hs1 & Hs2).
      pose proof (Happfr (fr + 2688) ltac:(lia)) as Hap1.
      pose proof (Happfr (fr + 2725) ltac:(lia)) as Hap2.
      unfold app_mem, LOWMEM_END in *. split; [lia|]. split; [lia | exact I]. }
    (* the record at phi is a live block of the heap list, so it is apart from the frame and the window *)
    assert (HinHphi : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
      by (apply in_or_app; left; cbn [hb1 In]; left; reflexivity).
    destruct (f11_blocks _ _ _ _ _ LAWS _ mem md phi (AC.a_size (flen g j)) HAH HinHphi)
      as (Hphilo & Hphiin).
    assert (Hasz1 : 1 <= AC.a_size (flen g j)) by (unfold AC.a_size; apply Z.le_max_r).
    (* the block and the written record range are apart as sets *)
    assert (Hblkfr : phi + AC.a_size (flen g j) <= fr + 2688 \/ fr + 2726 <= phi).
    { destruct Hloc as [(_ & _ & Hreal)|(_ & _ & HinFS & _)].
      - left. pose proof (Hreal (fr + 2688) ltac:(lia)) as (Hr1 & _). lia.
      - destruct (Z_le_gt_dec (phi + AC.a_size (flen g j)) (fr + 2688)) as [Hle|Hgt]; [left; exact Hle|].
        destruct (Z_le_gt_dec (fr + 2726) phi) as [Hle2|Hgt2]; [right; exact Hle2|].
        exfalso. pose (x := Z.max phi (fr + 2688)).
        pose proof (proj2 (Hphiin x ltac:(unfold x; lia))) as Hnfs.
        exact (Hnfs (HinFS x ltac:(unfold x; lia))). }
    assert (Hphidj : forall a k, phi <= a -> 0 <= k -> a + k <= phi + AC.a_size (flen g j) ->
              Frame.disjoint_from W a k).
    { intros a k Ha Hk0 Hk. apply Hkeep; [lia | left; lia |].
      destruct Hblkfr as [Hd|Hd]; [left; lia | right; lia]. }
    assert (Hsize : flen g j <= AC.a_size (flen g j))
      by (unfold AC.a_size; apply Z.le_max_l).
    assert (T17 : b5_F17 g j phi fr regs' mem').
    { destruct H17 as (A17 & H9_17 & HA17 & Hq192).
      assert (EA : A17 = A)
        by (pose proof (rg_eq64 regs 9 A17 A H9_17 H9) as Hm; rewrite !Z.mod_small in Hm by lia; exact Hm).
      subst A17. exists A. split; [unfold rg in *; rewrite Fr9; exact H9|]. split; [exact HA64|].
      apply Hq; [lia | exact Hq192]. }
    assert (T240 : b5_W240 g j regs' mem').
    { destruct H240 as (A24 & H9_24 & HA24 & w240 & Hqw & Hw0 & Hwt & Hwf).
      assert (EA : A24 = A)
        by (pose proof (rg_eq64 regs 9 A24 A H9_24 H9) as Hm; rewrite !Z.mod_small in Hm by lia; exact Hm).
      subst A24. exists A. split; [unfold rg in *; rewrite Fr9; exact H9|]. split; [exact HA64|].
      exists w240. split; [apply Hq; [lia | exact Hqw]|]. split; [exact Hw0|].
      split; [exact Hwt | exact Hwf]. }
    (* push 14 group C: b5_PF across the write. The record block is apart from the written record range
       (Hphidj), the parse output cells and the compare operands at fr + 180 / fr + 186 are frame cells apart
       from it, and every metadata byte is outside both written ranges (Hsh1). *)
    assert (TPF : b5_PF g j phi fr regs' mem').
    { destruct HPF as (A1b & H9_1b & HA1b & Hrec & Hcmp).
      assert (EA : A1b = A)
        by (pose proof (rg_eq64 regs 9 A1b A H9_1b H9) as Hm; rewrite !Z.mod_small in Hm by lia; exact Hm).
      subst A1b. exists A. split; [unfold rg in *; rewrite Fr9; exact H9|]. split; [exact HA64|].
      split.
      - intros Hle. destruct (Hrec Hle) as (_ & Hphib).
        split; [exists (t_g (g_in g) j); split; [exact TG|]; rewrite HGl; lia |].
        apply Hb; [exact Hphib|]. apply Hphidj; [lia | lia |].
        (* t_phi j = firstn (Z.to_nat (flen g j)) (skipn ..), so it is at most flen g j bytes *)
        unfold flen, t_len, t_phi, f_phi in *. rewrite length_firstn.
        pose proof (Nat.le_min_l (Z.to_nat (f_len (g_in g) (fc (g_in g) j)))
                      (length (skipn (Z.to_nat (f_body (g_in g) (fc (g_in g) j))) (g_in g)))) as Hmin.
        pose proof (Z2Nat.id (f_len (g_in g) (fc (g_in g) j)) ltac:(lia)) as Hid.
        pose proof (Nat2Z.inj_le
          (Nat.min (Z.to_nat (f_len (g_in g) (fc (g_in g) j)))
             (length (skipn (Z.to_nat (f_body (g_in g) (fc (g_in g) j))) (g_in g))))
          (Z.to_nat (f_len (g_in g) (fc (g_in g) j)))) as Hinj.
        lia.
      - intros H8819. destruct (Hcmp H8819) as
          ((field16 & v14 & v15 & v16 & v17 & Hru16 & Hrb14 & Hrb15 & Hrb16 & Hrb17 &
            Hrv14 & Hrv15 & Hrv16 & Hrv17 & Hrs14 & Hrs15 & Hrs16 & Hrs17 & Erf & Erk)
          & (ls & rs & Hq56 & Hls & Hlsl & Hrs & Hrsl & Hcm & Haddr)
          & (ls2 & rs2 & Hq48 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcm2 & Haddr2)).
        (* phi + 14 .. phi + 17 are block bytes (flen j >= 50 here), so app bytes *)
        assert (Hrapp : forall a, phi <= a < phi + 50 -> app_mem a)
          by (intros a Ha; exact (proj1 (Hphiin a ltac:(lia)))).
        split; [|split].
        + exists field16, v14, v15, v16, v17.
          split; [unfold u16 in *; apply Hb; [exact Hru16|];
                  rewrite length_le2; apply Hkeep; [lia | apply Hfrin; lia | lia]|].
          split; [unfold b8 in *; apply Hb; [exact Hrb14|]; cbn [length]; apply Hphidj; lia|].
          split; [unfold b8 in *; apply Hb; [exact Hrb15|]; cbn [length]; apply Hphidj; lia|].
          split; [unfold b8 in *; apply Hb; [exact Hrb16|]; cbn [length]; apply Hphidj; lia|].
          split; [unfold b8 in *; apply Hb; [exact Hrb17|]; cbn [length]; apply Hphidj; lia|].
          split; [exact Hrv14|]. split; [exact Hrv15|]. split; [exact Hrv16|]. split; [exact Hrv17|].
          split; [unfold b8 in *; apply Hb; [exact Hrs14|]; cbn [length];
                  apply Hsh1; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
                  exact (shadow_of_app (phi + 14) (Hrapp (phi + 14) ltac:(lia)))|].
          split; [unfold b8 in *; apply Hb; [exact Hrs15|]; cbn [length];
                  apply Hsh1; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
                  exact (shadow_of_app (phi + 15) (Hrapp (phi + 15) ltac:(lia)))|].
          split; [unfold b8 in *; apply Hb; [exact Hrs16|]; cbn [length];
                  apply Hsh1; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
                  exact (shadow_of_app (phi + 16) (Hrapp (phi + 16) ltac:(lia)))|].
          split; [unfold b8 in *; apply Hb; [exact Hrs17|]; cbn [length];
                  apply Hsh1; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8;
                  exact (shadow_of_app (phi + 17) (Hrapp (phi + 17) ltac:(lia)))|].
          split; [exact Erf | exact Erk].
        + exists (firstn 6 ls), (firstn 6 rs). split; [apply Hq; [lia | exact Hq56]|].
          split; [apply Hb; [exact (f11_bytes_first mem (fr + 186) ls 6 Hls)|];
                  rewrite length_firstn; apply Hkeep; [lia | apply Hfrin; lia | lia]|].
          split; [rewrite length_firstn; lia|].
          split; [apply Hb; [exact (f11_bytes_first mem phi rs 6 Hrs)|];
                  rewrite length_firstn; apply Hphidj; lia|].
          split; [rewrite length_firstn; lia|].
          split; [rewrite f11_mcmp_firstn; exact Hcm|].
          exact (sl_addr_keep mem mem' W (fr + 186) 6 Haddr MU HAW).
        + exists (firstn 6 ls2), (firstn 6 rs2). split; [apply Hq; [lia | exact Hq48]|].
          split; [apply Hb; [exact (f11_bytes_first mem (fr + 180) ls2 6 Hls2)|];
                  rewrite length_firstn; apply Hkeep; [lia | apply Hfrin; lia | lia]|].
          split; [rewrite length_firstn; lia|].
          split; [apply Hb; [exact (f11_bytes_first mem (phi + 6) rs2 6 Hrs2)|];
                  rewrite length_firstn; apply Hphidj; lia|].
          split; [rewrite length_firstn; lia|].
          split; [rewrite f11_mcmp_firstn; exact Hcm2|].
          exact (sl_addr_keep mem mem' W (fr + 180) 6 Haddr2 MU HAW). }
    (* f1_IN: the harness input block. For 0 < n it is a live entry block, below stklo and outside the FakeStack
       (a_laws_blocks): the callee window lies above stklo, and the record bytes [fr + 2688, fr + 2726) lie above
       stklo on the real arm and in the FakeStack on the side arm. For n = 0 the byte list is empty. *)
    assert (TIN : f1_IN g mem').
    { destruct HIN as (HINl & HINa & HINb). split; [exact HINl|].
      split; [exact (sl_addr_keep mem mem' W (g_p g) (g_n g) HINa MU HAW)|].
      pose proof (g_n_len g) as Hgl.
      destruct (Z.eq_dec (g_n g) 0) as [Hn0|Hn0].
      - assert (Hl0 : length (g_in g) = 0%nat) by lia.
        destruct HINb as (Hb0 & Hb1 & _). split; [exact Hb0|]. split; [exact Hb1|].
        intros i Hi. rewrite Hl0 in Hi. lia.
      - assert (HinH : In (g_p g, g_n g) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
          by (apply in_or_app; right; apply HINl; lia).
        destruct (f11_blocks _ _ _ _ _ LAWS _ mem md (g_p g) (g_n g) HAH HinH)
          as (Hblo & Hbin).
        apply (bytes_at_transport rsegs W mem mem' (g_p g) (g_in g) HINb MU).
        rewrite <- Hgl. apply Hkeep; [lia | left; lia |].
        destruct Hloc as [(_ & _ & Hreal)|(_ & _ & HinFS & _)].
        + left. pose proof (Hreal (fr + 2688) ltac:(lia)) as (Hr1 & _). lia.
        + destruct (Z_le_gt_dec (g_p g + g_n g) (fr + 2688)) as [Hle|Hgt]; [left; exact Hle|].
          destruct (Z_le_gt_dec (fr + 2726) (g_p g)) as [Hle2|Hgt2]; [right; exact Hle2|].
          exfalso. pose (x := Z.max (g_p g) (fr + 2688)).
          pose proof (proj2 (Hbin x ltac:(unfold x; lia))) as Hnfs.
          exact (Hnfs (HinFS x ltac:(unfold x; lia))). }
    (* the tp words of b5_FS are image bytes, below GT *)
    assert (Htp : 0 <= AC.as_tp AC.ASYMS /\ AC.as_tp AC.ASYMS + 16 <= AC.GT)
      by (split; apply Z.leb_le; vm_compute; reflexivity).
    assert (Ttp : forall a v, 0 <= a -> a + 8 <= AC.GT ->
              (word_mem rsegs mem' a v <-> word_mem rsegs mem a v)).
    { intros a v Ha0 Ha8. unfold word_mem. split; intros Hw k Hk.
      - rewrite <- (KindBGlue.mbyte_munch rsegs W mem mem' (a + Z.of_nat k) MU ltac:(lia)
                     ltac:(apply HWlo; lia)). exact (Hw k Hk).
      - rewrite (KindBGlue.mbyte_munch rsegs W mem mem' (a + Z.of_nat k) MU ltac:(lia)
                   ltac:(apply HWlo; lia)). exact (Hw k Hk). }
    (* FRA across the call *)
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' regs' mem' md md');
        [| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
         | exact Hmat ].
      apply (sl_fr_cl B APIf ra empty FF g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md W
               HFRA MU WM).
      - apply (f11_ro_keep W mem mem' Hro MU). exact HWlo.
      - exact HAW.
      - rewrite HWeq. unfold rt_disjoint. cbn [Frame.disjoint_from].
        unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK,
          RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
        repeat split; left; lia.
      - exact HAH'.
      - exact HSTKlo.
      - intros x Hx. apply HWlo. lia.
      - intros x Hx. apply HWout; [apply (Hfrout x 1); lia | lia].
      - intros A' HA' HA'r x Hx.
        assert (A' = A) by (pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm; rewrite !Z.mod_small in Hm by lia;
                            exact Hm). subst A'. apply HWout; lia.
      - intros x Hx. apply HWout; lia.
      - intros x Hx. pose proof (HshIS x Hx) as Hs. pose proof (f11_sh_lt x Hs) as (Hs1 & Hs2).
        apply HWout; [left; lia|].
        destruct (Z_lt_le_dec x (fr + 2688)) as [H1|H1]; [left; exact H1|].
        destruct (Z_lt_le_dec x (fr + 2688 + 38)) as [H2|H2]; [|right; exact H2].
        exfalso. exact (app_not_shadow x (Happfr x ltac:(lia)) Hs).
      - intros A' HA' HA'r x Hx.
        assert (A' = A) by (pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm; rewrite !Z.mod_small in Hm by lia;
                            exact Hm). subst A'. apply HWout; lia.
      - exact Hwin'.
      - intros Hrec. eapply fsrec_stklo; [exact Hrec | exact HAH | exact MU | exact HWstklo].
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26. }
    (* ENT across the call *)
    assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { eapply ent_mat; [| exact Hmat].
      eapply ent_store with (W := W); [exact HENT | exact HFRA | exact MU | | exact HSTKlo | exact HSTKhi |].
      - intros x Hx.
        destruct (Z_lt_le_dec x (fr + 2688)) as [Hlt|Hge];
          [|destruct (Z_lt_le_dec x (fr + 2688 + 38)) as [Hlt2|Hge2]].
        + destruct (Z_lt_le_dec x (sp - 32)) as [Hs1|Hs1]; [left; apply HWout; lia|].
          destruct (Z_lt_le_dec x sp) as [Hs2|Hs2]; [|left; apply HWout; lia].
          right; left. lia.
        + right; right; left. lia.
        + destruct (Z_lt_le_dec x (sp - 32)) as [Hs1|Hs1]; [left; apply HWout; lia|].
          destruct (Z_lt_le_dec x sp) as [Hs2|Hs2]; [|left; apply HWout; lia].
          right; left. lia.
      - intros a _ Ho. exact (proj2 (Hown a) Ho). }
    (* the exit cut Inv_A820f8_at *)
    rewrite <- SEGS. apply (Hexit g).
    exists phi, regs', mem', md', fr. split; [reflexivity|].
    split; [exact HFRA'|].
    split; [exact HENT'|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [split; [exact Hphinz | exact THB]|].
    (* FLSI' *)
    split.
    { unfold FLSI. split.
      { unfold FLSH, PRO. split.
        { split; [apply Tsp; [lia | exact sp40]|].
          split; [apply Tsp; [lia | exact sp120]|].
          split; [apply Tsp; [lia | exact sp136]|].
          split; [apply Tsp; [lia | exact sp160]|].
          split; [apply Tsp; [lia | exact sp168]|].
          split; [apply Tsp; [lia | exact sp176]|].
          split; [apply Tsp; [lia | exact sp208]|].
          split; [apply Tsp; [lia | exact sp248p]|].
          split; [exact (sl_addr_keep mem mem' W (fr + 2624) 6 Hour6 MU HAW)|].
          split; [exact (proj2 (proj2 TIN))|].
          split.
          { intros Hn. destruct TIN as (TINl & TINa & _). split; [exact (TINl Hn) | exact TINa]. }
          (* push 14D: PRO's A4 spills [A + 184 / 256 / 264 / 272] *)
          split; [apply Tsp; [lia | exact sp184p]|].
          split; [apply Tsp; [lia | exact sp256p]|].
          split; [apply Tsp; [lia | exact sp264p]|].
          (* v1.9 PRO position 16: [A + 32] = fr + 2880, first.sroa.7 (A4's 0x813cc) *)
          split; [apply Tsp; [lia | exact sp272p] | apply Tsp; [lia | exact sp32p]]. }
        split; [apply Tsp; [lia | exact sp128]|].
        split; [exact Hfrstk'|].
        split; [apply Tsp; [lia | exact sp144]|].
        exact (sl_addr_keep mem mem' W (fr + 2691) 17 Hid17 MU HAW). }
      split; [apply Tsp; [lia | exact sp216]|].
      split; [apply Tsp; [lia | exact sp224]|].
      split; [apply Tsp; [lia | exact sp248]|].
      split; [exact TIN|].
      (* FLC (push 14D / 14E): the pointer spills, the two record ranges and the compare spills [A + 56 / 48] *)
      split; [apply Tsp; [lia | exact fc256]|].
      split; [apply Tsp; [lia | exact fc184]|].
      split; [apply Tsp; [lia | exact fc192]|].
      split; [apply Tsp; [lia | exact fc80]|].
      split; [apply Tsp; [lia | exact fc88]|].
      split; [apply Tsp; [lia | exact fc96]|].
      split; [apply Tsp; [lia | exact fc272]|].
      split; [apply Tsp; [lia | exact fc264]|].
      split; [exact (sl_addr_keep mem mem' W (fragb fr) 72 fcfg MU HAW)|].
      split; [exact (sl_addr_keep mem mem' W (fr + 2688) 38 fcid MU HAW)|].
      split; [apply Tsp; [lia | exact fc72]|].
      split; [apply Tsp; [lia | exact fc64]|].
      (* v1.9 FLC positions 13 / 14: [A + 56] = fr + 2889, [A + 48] = fr + 2890 (P12's 0x81d34 / 0x81d3c) *)
      split; [apply Tsp; [lia | exact fc56] | apply Tsp; [lia | exact fc48]]. }
    (* LK' *)
    split; [unfold LK; split; [exact Hj' | split; [unfold rg in *; rewrite Fr21; exact Hr21 | exact TOUR]]|].
    (* b5_C' *)
    split.
    { unfold b5_C. split; [unfold rg in *; rewrite Fr23; exact Hs7|].
      split; [unfold rg in *; rewrite Fr18; exact Hr18|].
      split.
      { exists A. split; [unfold rg in *; rewrite Fr9; exact H9|]. split; [exact HA64|].
        split.
        { unfold b5_SPILL.
          split; [apply Hq; [lia | exact Hq248]|].
          split; [apply Hq; [lia | exact Hq256]|].
          split; [apply Hq; [lia | exact Hq144]|].
          split; [apply Hq; [lia | exact Hq184]|].
          split; [apply Hq; [lia | exact Hq208]|].
          split; [apply Hq; [lia | exact Hq64]|].
          split; [apply Hq; [lia | exact Hq72]|].
          split; [apply Hq; [lia | exact Hq80]|].
          split; [apply Hq; [lia | exact Hq272] | apply Hq; [lia | exact Hq264]]. }
        (* push 13 group C: the length flag at [A + 232] *)
        apply Hq; [lia | exact Hq232]. }
      split.
      { unfold b5_PH. split; [intros _; exact TG|].
        split; [intros _; rewrite HaspEq, Haspz; exact (conj Hplfr Hplsp)|].
        intros Hz; exfalso; lia. }
      split.
      { unfold b5_FR. split; [exact (sl_addr_keep mem mem' W (fragb fr) 72 HfgA MU HAW)|].
        split; [exact (sl_addr_keep mem mem' W (fr + 2688) 38 HidA MU HAW)|].
        split; [exact TFG | exact HFGl]. }
      split.
      { unfold b5_FS. split.
        { intros FS HFSw' HFSr' Hcont.
          exact (HFScont FS (proj1 (Ttp (AC.as_tp AC.ASYMS) FS ltac:(lia) ltac:(lia)) HFSw') HFSr' Hcont). }
        exists DB. split; [|exact HDBr].
        exact (proj2 (Ttp (AC.as_tp AC.ASYMS + 8) DB ltac:(lia) ltac:(lia)) HDBw). }
      split.
      { unfold b5_KN. split.
        { apply (bytes_at_transport rsegs W mem mem' KIND_NAME kind_name_bytes HKNb MU).
          rewrite f11_kn_len. rewrite HWeq. cbn [Frame.disjoint_from]. unfold KIND_NAME.
          split; [lia|]. split; [lia | exact I]. }
        exact (sl_addr_keep mem mem' W KIND_NAME 112 HKNa MU HAW). }
      (* FGj: the fragment record at fragb fr, outside the write *)
      split.
      { destruct HFGj as (_ & HFGok). unfold FGj, FGb. split; [exact TFG | exact HFGok]. }
      (* FSj: the first-fragment state: two spills of the 416-byte save area and the body object *)
      destruct HFSj as (Hf104 & Hf112 & Hfbody & Hfaddr & HFI). unfold FSj, FSb.
      split; [apply Tsp; [lia | exact Hf104]|].
      split; [apply Tsp; [lia | exact Hf112]|].
      (* v1.9 FSb positions 3 / 4: the FIRST body at fr + 2880 (at most 23 bytes, f11_fs_body_len) and the
         35-byte object first.sroa.7, frame bytes above the identity record [fr + 2688, fr + 2726) *)
      split.
      { apply (bytes_at_transport rsegs W mem mem' (fr + 2880) _ Hfbody MU).
        pose proof (f11_fs_body_len (g_in g) j) as Hbl.
        apply Hkeep; [lia | apply Hfrin; lia | lia]. }
      split; [exact (sl_addr_keep mem mem' W (fr + 2880) 35 Hfaddr MU HAW) | exact HFI]. }
    (* b5_K' /\ b5_RC' /\ 50 <= flen /\ result *)
    split.
    { unfold b5_K. split; [unfold rg in *; rewrite Fr20; exact Hs4|].
      split; [unfold rg in *; rewrite Fr22, Hbig; exact Hs6|].
      split; [unfold rg in *; rewrite Fr24; exact Hs8|].
      split; [unfold rg in *; rewrite Fr25; exact Hs9|].
      split.
      { destruct Hsp280 as (A280 & H9280 & HA280 & Hq280).
        assert (A280 = A) by (pose proof (rg_eq64 regs 9 A280 A H9280 H9) as Hm;
                              rewrite !Z.mod_small in Hm by lia; exact Hm). subst A280.
        exists A. split; [unfold rg in *; rewrite Fr9; exact H9|]. split; [exact HA64|].
        apply Hq; [lia | exact Hq280]. }
      split.
      { unfold u32 in *.
        apply (bytes_at_transport rsegs W mem mem' (fr + 176) (le4 (Z_to_bv 64 (t_k (g_in g) j))) Hu176 MU).
        rewrite length_le4. apply Hkeep; [lia | apply Hfrin; lia | lia]. }
      exact Hargs. }
    split.
    { unfold b5_RC.
      split; [exact (sl_addr_keep mem mem' W (fr + 256) 2 Hpa2 MU HAW)|].
      split; [exact (sl_addr_keep mem mem' W (fr + 272) 8 Hpp8 MU HAW)
             | exact (sl_addr_keep mem mem' W (fr + 304) 8 Hpn8 MU HAW)]. }
    split; [exact H50|].
    split.
    { exists (fst (ING idb ad pb)). split; [unfold rg; exact Fr10|].
      destruct (ING_ret idb ad pb) as [E|E]; rewrite E; lia. }
    split.
    { (* IDb1: the record the ingest wrote is the stage-2 identity ID1 g j (ir holds on this arm) *)
      assert (EID : ID1 g j = snd (ING idb ad pb)) by (unfold ID1, rp_id; rewrite Hir; reflexivity).
      unfold IDb1. rewrite EID. split.
      - exact (f11_lrwB mem' (fr + 2688) 38 _ HRW).
      - exact (RcIdentLib.ING_id_ok idb ad pb Hidbl HIDok). }
    split; [exact T17|]. split; [exact T240 | exact TPF].
Qed.

(* ---- ENTRY 1 (0x8206c, the loop head) to ENTRY 2 (0x820ac): the record-sum loop. No memory is written, so
   the carry moves by sl_fra_move / ent_mat; the loop writes only a0, a1, a4, a5, a6, a7. ---- *)
Lemma seg_F11_fd4 : forall j,
  Hat B APIf ra (Inv_A820ac_at (fx := fx) B APIf ra) j -> Hat B APIf ra (Inv_A8206c_at (fx := fx) B APIf ra) j.
Proof.
  intros j Hx2 g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    Hgn & Hj & HHB & HFLSI & HLK & HC & HbK & HbRC & H50 & Hsum & Hok & HbRP &
    Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & HIDj & H17 & H240 & HPF).
  subst c. rewrite SEGS.
  assert (Hir : ir (flen g j) (t_g (g_in g) j) = true)
    by (unfold reply_ok in Hok; apply andb_prop in Hok; tauto).
  destruct (ir_bytes _ _ Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsr & _ & _ & _ & _).
  pose proof (f11_tg_len (g_in g) j) as HGl.
  pose proof (f11_sum128 (flen g j) (t_g (g_in g) j) HGl Hir) as H128.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof HHB as (Hphinz & HAd).
  pose proof HAd as (Hp0 & _ & Hpe & _).
  unfold AC.a_size in Hpe. rewrite Z.max_l in Hpe by lia.
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (Haddr50 : addressable mem phi 50).
  { rewrite <- (Z.add_0_r phi).
    apply (addressable_sub mem phi (AC.a_size (flen g j)) 0 50 HAd); unfold AC.a_size; lia. }
  assert (HG : bytes_at rsegs mem phi (t_g (g_in g) j))
    by (destruct HC as (_ & _ & _ & (HPHg & _ & _) & _); exact (HPHg H50)).
  assert (Hn0 : 1 <= ir_s (t_g (g_in g) j) - 8 <= 15) by lia.
  replace (ir_s (t_g (g_in g) j) - 13) with (ir_s (t_g (g_in g) j) - 8 - 5) in Ha3 by lia.
  apply (sl_run_lib regs (Z_to_bv 64 0x8206c) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x820ac /\ mem' = mem /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\
       getr R0 11 = Z_to_bv 64 0 /\ getr R0 12 = getr regs 12 /\ getr R0 13 = getr regs 13)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f11_mkR_expand.
    f11_slot Ha0. f11_slot Ha1. f11_slot Ha4. f11_slot Ha5. f11_slot Hr26.
    eapply LE.evt_mono.
    { apply (f11_fd4_evt (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 12) (getr regs 13) (getr regs 18)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
               (getr regs 25) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)
               (getr regs 16) (getr regs 17)
               _ _ mem phi (ir_s (t_g (g_in g) j) - 8) (t_g (g_in g) j));
        [ lia | lia | exact HGl | exact Hn0 | | exact HG | exact Haddr50 ].
      exact H128. }
    { intros ms' (a0' & a4' & a5' & a6' & a7' & E).
      eexists _, (Z_to_bv 64 0x820ac), mem. split; [exact E|].
      repeat (split; [reflexivity|]). reflexivity. }
  - intros R0 pc' mem' regs' md' (Hpc & Hmem & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 & Er22 &
      Er23 & Er24 & Er25 & Er26 & Er11 & Er12 & Er13) Hreg Hmat.
    subst pc' mem'. rewrite <- SEGS. apply Hx2.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    (* the carry reads only registers 2, 9, 18, 20-25 and the unchanged memory *)
    assert (Tsp : forall off v, spill regs mem off v -> spill regs' mem off v).
    { intros off v (A' & HA' & Hq'). exists A'. split; [unfold rg in *; rewrite Fr9; exact HA' | exact Hq']. }
    assert (TFLSI : FLSI g j fr regs' mem)
      by (unfold FLSI, FLSH, PRO, FLC, spill, rg in *; rewrite Fr9; exact HFLSI).
    assert (TLK : LK g fr j regs' mem).
    { destruct HLK as (Hj' & Hr21 & HOUR). unfold LK. split; [exact Hj'|].
      split; [unfold rg in *; rewrite Fr21; exact Hr21 | exact HOUR]. }
    assert (TC : b5_C g j phi fr regs' mem).
    { destruct HC as (Hs7 & Hs2 & (A' & H9' & HA' & HSP & Hq232) & HbPH & HbFR & HbFS & HbKN & HFGj & HFSj).
      unfold b5_C. split; [unfold rg in *; rewrite Fr23; exact Hs7|].
      split; [unfold rg in *; rewrite Fr18; exact Hs2|].
      split; [exists A'; split; [unfold rg in *; rewrite Fr9; exact H9'
                                | split; [exact HA' | split; [exact HSP | exact Hq232]]]|].
      split.
      { destruct HbPH as (HPHg & HPHpl & HPHfs). unfold b5_PH.
        split; [exact HPHg|]. split; [intros Hle; rewrite HaspEq; exact (HPHpl Hle) | exact HPHfs]. }
      split; [exact HbFR|]. split; [exact HbFS|]. split; [exact HbKN|]. split; [exact HFGj|].
      destruct HFSj as (Hf104 & Hf112 & Hfbody & Hfaddr & HFI). unfold FSj, FSb.
      split; [exact (Tsp _ _ Hf104)|]. split; [exact (Tsp _ _ Hf112)|].
      split; [exact Hfbody|]. split; [exact Hfaddr | exact HFI]. }
    assert (TK : b5_K g j phi fr regs' mem).
    { destruct HbK as (Hs4 & Hs6 & Hs8 & Hs9 & Hsp280 & Hu176 & Hargs). unfold b5_K.
      split; [unfold rg in *; rewrite Fr20; exact Hs4|].
      split; [unfold rg in *; rewrite Fr22; exact Hs6|].
      split; [unfold rg in *; rewrite Fr24; exact Hs8|].
      split; [unfold rg in *; rewrite Fr25; exact Hs9|].
      split; [|split; [exact Hu176 | exact Hargs]].
      destruct Hsp280 as (A' & H9' & HA' & Hq'). exists A'.
      split; [unfold rg in *; rewrite Fr9; exact H9' | split; [exact HA' | exact Hq']]. }
    exists phi, regs', mem, md', fr.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem md md' HFRA);
        [ rewrite Hreg; exact Er2 | rewrite Hreg; exact Er3 | rewrite Hreg; exact Er4
        | rewrite Hreg; exact Er8 | exact Fr9 | rewrite Hreg; exact Er19
        | rewrite Hreg; exact Er26 | exact Hmat ]. }
    split; [ eapply ent_mat; [ exact HENT | exact Hmat ] |].
    split; [exact Hgn|].
    split; [exact Hj|].
    split; [exact HHB|].
    split; [exact TFLSI|].
    split; [exact TLK|].
    split; [exact TC|].
    split; [exact TK|].
    split; [exact HbRC|].
    split; [exact H50|].
    split; [exact Hsum|].
    split; [exact Hok|].
    split; [exact HbRP|].
    split; [ unfold rg; rewrite Hreg; exact Er11 |].
    split; [ unfold rg; rewrite Hreg, Er12; exact Ha2 |].
    split.
    { unfold rg; rewrite Hreg, Er13;
        replace (ir_s (t_g (g_in g) j) - 13) with (ir_s (t_g (g_in g) j) - 8 - 5) by lia; exact Ha3. }
    split; [exact HIDj|].
    (* push 13 group C: the loop writes no memory and keeps reg 9, so the three bundles move unchanged *)
    assert (Treg : forall P : Z -> Prop, (exists A', rg regs 9 A' /\ P A') -> (exists A', rg regs' 9 A' /\ P A'))
      by (intros P (A' & H9' & HP); exists A'; split; [unfold rg in *; rewrite Fr9; exact H9' | exact HP]).
    split; [exact (Treg _ H17)|].
    split; [exact (Treg _ H240) | exact (Treg _ HPF)].
Qed.

Lemma seg_F11 : forall j, Hat B APIf ra (Inv_A820f8_at (fx := fx) B APIf ra) j ->
  Hat B APIf ra (Inv_A8206c_at (fx := fx) B APIf ra) j /\ Hat B APIf ra (Inv_A820ac_at (fx := fx) B APIf ra) j.
Proof.
  intros j Hexit.
  pose proof (seg_F11_014 j Hexit) as H2.
  split; [exact (seg_F11_fd4 j H2) | exact H2].
Qed.
End S.
