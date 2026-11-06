(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names and addresses changed; 1390 of its 1547 lines of code are new or changed and 1345 lines of the source are left out. *)
(* Segment R18 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x81858, 0x818d0], Inv_A81858 -> Inv_A818d0
   (turn b = 0).  0x81858 s2 := [s1+200] (= decl_slot fr); `beqz a0,81864` taken (a0 = 0, so the abort edge 0x81860
   is not reached); a4 := [s1+8] (= m + 16, the catalogue row of the round trip); a3 := the byte at (a4 >> 3) + s10,
   a0 := the u32 at [[s1+216]] (= fr + 2528, ports_parse's first output 4 n_in); `bnez a3,81960` NOT taken (the row
   is a registered global, FRA's frame_AG, so its granule's metadata byte is 0); a2 := the u32 at [a4] (= the row's
   word at + 16, box_ic); `beq a0,a2,8188c` taken (B3Rtm.a_rtm_in).  The same five steps again for [s1+0] (= m + 20)
   and fr + 2532 (4 n_out = box_oc, B3Rtm.a_rtm_out), so 0x818b0 is not reached.  Then the four 1-byte stores of 0
   into the frame's metadata bytes S(fr) + 320 .. + 323 (s3 = S(fr)), which are the metadata bytes of the 32 bytes at
   decl_slot fr = fr + 2560: after them those 32 bytes are marked usable.  Finally a0 := [s1+112] (= m), a1 := s2
   and the call of declaration_of at 0x818cc, which writes the 32 bytes at a1 (the declaration of row m, decl_ok m
   being true: B3Rtm.a_rtm_declok) plus its own 2304 stack bytes below sp, and returns 1 to 0x818d0.

   r18_evt is the Lib-level run of the twenty instructions plus the call by its contract (lib/A/Prog/declaration_of_c.v);
   push 5b: it starts from ro_agree (FRA carries no mem_inv), and the call runs on the normalized memory
   (MemNorm.evt_normalize, B3Norm's mem_rel transports), whose mem_inv the contract asks for.
   r18_sh_move is the FRA / ENT transport across the four metadata stores (Tac_slot.sl_fr_meta + ent_store, with the
   AH / stklo / stkhi / owned facts of the two frame-location arms); the FRA transport across the callee's write set
   W = [sp - 2304, sp) + [decl_slot fr, decl_slot fr + 32) is B3FrCl.b3_fr_cl; seg_R18 is the segment lemma from
   the official exit cut Inv_A818d0_at to the entry cut Inv_A81858_at (SlotInv.v push 6c). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import declaration_of_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv AsanRTFacts PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcDecl RcFrag RcSynth.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_rt_b2 Tac_rt2_b2 Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import B3Rtm B3Norm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3FrCl.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module ACx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module YKa := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

(* Two `munch` / `wmono` constants are in scope here: Lib.Frame's (the callee contracts' and this file's
   statements') and A.Tk.UL.Frame's (the one Tac_slot's transports are stated with).  They have the same
   definition, so each is the other read through `exact`; these four coercions name the step. *)
Lemma r18_munch_f : forall W m m', munch W m m' -> Frame.munch W m m'.
Proof. intros W m m' H. exact H. Qed.
Lemma r18_munch_b : forall W m m', Frame.munch W m m' -> munch W m m'.
Proof. intros W m m' H. exact H. Qed.
Lemma r18_wmono_f : forall m m', wmono rsegs m m' -> Frame.wmono rsegs m m'.
Proof. intros m m' H. exact H. Qed.
Lemma r18_outside_b : forall W x, Frame.outside W x -> outside W x.
Proof. intros W x H. exact H. Qed.

(* ---- small arithmetic / byte-run helpers ---- *)

Lemma r18_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

(* The metadata byte of an addressable granule reads as 0, so `bnez` on it is not taken. *)
Lemma r18_nz0 : negb (bv_eqb (sxb (Z_to_bv 8 0)) (Z_to_bv 64 0)) = false.
Proof.
  apply negb_false_iff. unfold sxb.
  replace (bv_signed (Z_to_bv 8 0)) with 0 by (vm_compute; reflexivity).
  apply r18_eqb_refl.
Qed.

Lemma r18_le1_0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. apply a_bytes_eq. vm_compute. reflexivity. Qed.

(* A whole byte run read in one access. *)
Lemma r18_rdn : forall m a bs (n : nat), bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H Hn.
  pose proof (bytes_at_ov_read rsegs m a bs 0 n H ltac:(lia)) as HR.
  replace (a + Z.of_nat 0) with a in HR by lia.
  assert (E : firstn n (skipn 0 bs) = bs).
  { change (skipn 0 bs) with bs. apply firstn_all2. lia. }
  rewrite E in HR. exact HR.
Qed.

(* A one-byte run is the byte at its address. *)
Lemma r18_b1_rd : forall m a (bb : byte), bytes_at rsegs m a [bb] -> mrd rsegs m (wa a) = Some bb.
Proof.
  intros m a bb (_ & _ & H). pose proof (H 0%nat ltac:(cbn [length]; lia)) as H0.
  replace (a + Z.of_nat 0) with a in H0 by lia. cbn [nth_error] in H0. exact H0.
Qed.

(* A slice of a byte run. *)
Lemma r18_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(* A present, writable byte run gives store_ok for each of its bytes. *)
Lemma r18_stk_store_ok : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 1 <= hi ->
  store_ok rsegs m (wa a) 1%nat = true.
Proof.
  intros m lo hi a (H1 & H2 & H) Hlo Hhi.
  assert (WR : wr_at rsegs m a 1).
  { split; [lia|]. split; [lia|]. intros i Hi. assert (Ei : i = 0) by lia. subst i.
    rewrite Z.add_0_r. exact (proj1 (H a ltac:(lia))). }
  pose proof (wr_at_store_ok rsegs m a 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* n addressable bytes from n single addressable bytes. *)
Lemma r18_addr_join : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> addressable m (p + i) 1) -> addressable m p n.
Proof.
  intros m p n Hp Hn Hend H. split; [exact Hp|]. split; [exact Hn|]. split; [exact Hend|].
  intros i Hi. destruct (H i Hi) as (_ & _ & _ & Hb). pose proof (Hb 0 ltac:(lia)) as Hb0.
  rewrite Z.add_0_r in Hb0. exact Hb0.
Qed.

(* An aligned addressable granule has metadata byte 0, read by the instrumented check of any of its 8 bytes. *)
Lemma r18_meta0 : forall m p q, addressable m p 8 -> p mod 8 = 0 -> p <= q < p + 8 ->
  ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m p q HA Hal Hq.
  assert (Hp0 : 0 <= p) by (destruct HA as (H & _); exact H).
  assert (E : Z.shiftr q 3 = Z.shiftr p 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. revert Hal Hq Hp0. Z.div_mod_to_equations. lia. }
  rewrite E.
  destruct (meta8 m p HA) as (RC & _). destruct RC as (_ & HB).
  cbn [cells_bytes cbytes app] in HB.
  exact (r18_rdn m _ _ 1%nat HB eq_refl).
Qed.

(* The image's bytes at an address range. *)
Lemma r18_img_nth : forall n A bs, Image.image_bytes rsegs A n = Some bs ->
  forall k, (k < n)%nat -> seg_rom rsegs (wa (A + Z.of_nat k)) = nth_error bs k.
Proof.
  induction n as [|n IH]; intros A bs H k Hk.
  - lia.
  - change (Image.image_bytes rsegs A (S n)) with
      (match seg_rom rsegs (wa A), Image.image_bytes rsegs (A + 1) n with
       | Some b, Some bs0 => Some (b :: bs0) | _, _ => None end) in H.
    destruct (seg_rom rsegs (wa A)) as [b|] eqn:E1; [|discriminate H].
    destruct (Image.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E2; [|discriminate H].
    injection H as <-. destruct k as [|k]; cbn [nth_error].
    + replace (A + Z.of_nat 0) with A by lia. exact E1.
    + replace (A + Z.of_nat (S k)) with (A + 1 + Z.of_nat k) by lia.
      exact (IH (A + 1) bs' E2 k ltac:(lia)).
Qed.

(* Image bytes the state keeps (G_img_c on the RELRO globals) are the state's bytes. *)
Lemma r18_img_bytes : forall (mem : word -> option byte) (A : Z) (n : nat) bs,
  (forall k, (k < n)%nat -> mbyte rsegs mem (A + Z.of_nat k) = seg_rom rsegs (wa (A + Z.of_nat k))) ->
  Image.image_bytes rsegs A n = Some bs -> 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  bytes_at rsegs mem A bs.
Proof.
  intros mem A n bs HG HI HA Hn.
  pose proof (Image.image_bytes_length rsegs n A bs HI) as HL.
  split; [lia|]. split; [rewrite HL; lia|].
  intros i Hi. rewrite HL in Hi.
  rewrite <- (r18_img_nth n A bs HI i Hi). exact (HG i Hi).
Qed.

(* n present bytes form a byte run. *)
Lemma r18_bytes_of_present : forall (n : nat) (m : word -> option byte) a,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, (k < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat k)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros m a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b & Hb). replace (a + Z.of_nat 0) with a in Hb by lia.
    destruct (IH m (a + 1) ltac:(lia) ltac:(lia)) as (bs & HBs & HL).
    { intros k Hk. replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (S k)) by lia. apply H. lia. }
    exists (b :: bs). split; [|cbn [length]; lia].
    change (b :: bs) with ([b] ++ bs).
    apply (proj2 (bytes_at_app rsegs m a [b] bs)). split.
    + split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
      intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
      replace (a + Z.of_nat 0) with a by lia. cbn [nth_error]. exact Hb.
    + cbn [length]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact HBs.
Qed.

(* ADDR-KEEP for a run whose write set misses the metadata bytes of the range. *)
Lemma r18_addr_keep_rng : forall m m' W p n,
  addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> Frame.outside W (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' W p n HA MU HO. pose proof HA as (H1 & H2 & H3 & H).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (shadow_of_app (p + i) Ha) as IS. pose proof (in_shadow_range _ IS) as IR.
  unfold mrd in Hb |- *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite Mem.wa_unsigned by lia. exact (HO i Hi).
Qed.

(* One CB cell's rw_cells across a run whose write set W misses the cell's bytes. *)
Lemma r18_rwcb_keep : forall W (m m' : word -> option byte) a n bs,
  munch W m m' -> wmono rsegs m m' ->
  (forall x, a <= x < a + Z.of_nat n -> Frame.outside W x) ->
  rw_cells rsegs m a [CB n bs] -> rw_cells rsegs m' a [CB n bs].
Proof.
  intros W m m' a n bs MU WM HO ((Hwf & Hb) & Hw).
  assert (Hlen : length bs = n) by (destruct Hwf as (Hl & _); exact Hl).
  split; [split; [exact Hwf|]|].
  - apply (a_keep W m m' a _ MU); [|exact Hb]. intros x Hx.
    cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hlen in Hx. exact (HO x Hx).
  - destruct Hw as (Hw0 & Hw1 & Hw). split; [exact Hw0|]. split; [exact Hw1|].
    intros i Hi. exact (WM _ (Hw i Hi)).
Qed.

(* RXS (push 10) across a run that keeps the spills [A + 0] .. [A + 224) and the fragment record's addressability. *)
Lemma r18_rxs_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 0 <= off <= 216 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2256) 72 -> addressable m' (fr + 2256) 72) ->
  RXS g fr regs m -> RXS g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha (H48 & H56 & H88 & H80 & H72 & H16 & H8 & H192 & H216 & HA).
  split; [exact (Hs 48 _ ltac:(lia) H48)|].
  split; [exact (Hs 56 _ ltac:(lia) H56)|].
  split; [exact (Hs 88 _ ltac:(lia) H88)|].
  split; [exact (Hs 80 _ ltac:(lia) H80)|].
  split; [exact (Hs 72 _ ltac:(lia) H72)|].
  split; [exact (Hs 8 _ ltac:(lia) H16)|].
  split; [exact (Hs 0 _ ltac:(lia) H8)|].
  split; [exact (Hs 200 _ ltac:(lia) H192)|].
  split; [exact (Hs 216 _ ltac:(lia) H216) | exact (Ha HA)].
Qed.

(* PRO (push 13B, push 14D) across a run that keeps the spills [A + 32] .. [A + 280), our[]'s 6 bytes addressable
   and the input block: its bytes, and its addressability when it is a live block of the entry heap. *)
Lemma r18_pro_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 32 <= off <= 272 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2624) 6 -> addressable m' (fr + 2624) 6) ->
  ((0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
     bytes_at rsegs m (g_p g) (g_in g) -> bytes_at rsegs m' (g_p g) (g_in g)) ->
  (In (g_p g, g_n g) (g_H g) -> addressable m (g_p g) (g_n g) -> addressable m' (g_p g) (g_n g)) ->
  PRO g fr regs m -> PRO g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha6 Hb Hia
    (H40 & H120 & H136 & H160 & H168 & H176 & H200 & H248 & HA6 & HIN & HG & H184 & H256 & H264 & H272 & H32).
  split; [exact (Hs 40 _ ltac:(lia) H40)|].
  split; [exact (Hs 120 _ ltac:(lia) H120)|].
  split; [exact (Hs 136 _ ltac:(lia) H136)|].
  split; [exact (Hs 160 _ ltac:(lia) H160)|].
  split; [exact (Hs 168 _ ltac:(lia) H168)|].
  split; [exact (Hs 176 _ ltac:(lia) H176)|].
  split; [exact (Hs 208 _ ltac:(lia) H200)|].
  split; [exact (Hs 248 _ ltac:(lia) H248)|].
  split; [exact (Ha6 HA6)|].
  split; [exact (Hb (fun Hn => proj1 (HG Hn)) HIN)|].
  split; [intros Hn; destruct (HG Hn) as (HH & HA); split; [exact HH | exact (Hia HH HA)]|].
  split; [exact (Hs 184 _ ltac:(lia) H184)|].
  split; [exact (Hs 256 _ ltac:(lia) H256)|].
  split; [exact (Hs 264 _ ltac:(lia) H264)|].
  split; [exact (Hs 272 _ ltac:(lia) H272) | exact (Hs 32 _ ltac:(lia) H32)].
Qed.

(* The frame's metadata byte at offset k is the metadata byte of the frame byte at offset 8 k. *)
Lemma r18_shadow_off : forall fr k, 0 <= k -> shadow_addr (fr + k * 8) = Sfr fr + k.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr k Hk. unfold Sfr, shadow_addr. rewrite Z.div_add by lia. lia.
Qed.

(* The metadata byte of a byte of [fr + 2560, fr + 2592) is one of S(fr) + 320 .. + 323. *)
Lemma r18_decl_meta : forall fr i, fr mod 8 = 0 -> 0 <= i < 32 ->
  shadow_addr (fr + 2560 + i) = Sfr fr + 320 + i / 8 /\ 0 <= i / 8 < 4.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr i Hfr Hi.
  split; [|split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]].
  unfold Sfr, shadow_addr. revert Hfr Hi. Z.div_mod_to_equations. lia.
Qed.

(* ro_agree is kept by a store whose write set avoids every read-only address (all in the low image). *)
Lemma r18_hull : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 6283264.
Proof.
  assert (H : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 6283264) rsegs = true)
    by (vm_compute; reflexivity).
  intros s Hin. apply Z.leb_le. rewrite forallb_forall in H. exact (H s Hin).
Qed.

Lemma r18_ro_lt : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 6283264.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  pose proof (YK1j.find_segment_in rsegs (bv_unsigned a) 1 s E) as Hin.
  pose proof (YK1j.find_segment_range rsegs (bv_unsigned a) 1 s E) as (_ & Hhi).
  pose proof (r18_hull s Hin) as Hb. lia.
Qed.

(* A byte run of the low image across a run that writes nothing below GT. *)
Lemma r18_keep_low : forall W m m' a bs, munch W m m' -> bytes_at rsegs m a bs ->
  (forall x, 0 <= x < 6283264 -> outside W x) -> a + Z.of_nat (length bs) <= 6283264 ->
  bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs MU HB Hout Hle.
  apply (fl_bytes W m m' a bs HB MU). intros x Hx. apply Hout.
  pose proof (proj1 HB) as Ha0. lia.
Qed.

(* Every registered global lies in the image, below GT. *)
Definition r18_AGb : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 6283264)) AFx.frame_AG.

Lemma r18_AGb_true : r18_AGb = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r18_AG_lt : forall a lo len, In (lo, len) AFx.frame_AG -> lo <= a < lo + len -> 0 <= a < 6283264.
Proof.
  intros a lo len Hin Hr.
  pose proof r18_AGb_true as HB. unfold r18_AGb in HB. rewrite forallb_forall in HB.
  pose proof (HB (lo, len) Hin) as H. cbn [fst snd] in H.
  apply andb_true_iff in H as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma r18_ro_keep : forall (mem mem' : word -> option byte) (W : list ivl),
  ro_agree rsegs mem -> munch W mem mem' ->
  (forall a : word, ro_addr rsegs a = true -> outside W (bv_unsigned a)) ->
  ro_agree rsegs mem'.
Proof.
  intros mem mem' W HRO MU Hout a Hro. unfold mrd. rewrite (MU a (Hout a Hro)). exact (HRO a Hro).
Qed.

(* A writable cell run above the image reads the same on both sides of mem_rel. *)
Lemma r18_rel_rw : forall m m0 a cs, mem_rel rsegs m m0 -> 0x5fe000 <= a ->
  (rw_cells rsegs m a cs <-> rw_cells rsegs m0 a cs).
Proof.
  intros m m0 a cs HR Ha. unfold rw_cells, cells_at.
  pose proof (bytes_at_rel rsegs m m0 a (cells_bytes cs) HR) as E1.
  pose proof (b3n_rel_wr m m0 a (Z.of_nat (cells_size cs)) HR Ha) as E2.
  tauto.
Qed.

Lemma r18_bv_mod : forall a a' d, Z_to_bv 64 a = Z_to_bv 64 a' -> Z_to_bv 64 (a + d) = Z_to_bv 64 (a' + d).
Proof.
  intros a a' d H. apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap in *.
  rewrite (Zplus_mod a d), (Zplus_mod a' d), H. reflexivity.
Qed.

Lemma r18_bytes_cong : forall m a a' bs,
  Z_to_bv 64 a = Z_to_bv 64 a' -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs m a' bs -> bytes_at rsegs m a bs.
Proof.
  intros m a a' bs Hcong Ha0 Hal (Ha'0 & Ha'l & Hr). split; [exact Ha0|]. split; [exact Hal|].
  intros i Hi.
  assert (Heq : wa (a + Z.of_nat i) = wa (a' + Z.of_nat i)).
  { unfold wa. apply r18_bv_mod. exact Hcong. }
  rewrite Heq. exact (Hr i Hi).
Qed.

(* A byte at [A0 + 8, A0 + 312) with Z_to_bv 64 A0 = Z_to_bv 64 A lies outside any [lo, hi) with 0 <= lo and
   hi <= A, for every 64-bit representative A0 of A. *)
Lemma r18_wrap_out : forall A A0 lo hi x, Z_to_bv 64 A = Z_to_bv 64 A0 -> 0 <= A -> A + 312 <= 2 ^ 64 ->
  0 <= lo -> hi <= A -> A0 + 8 <= x < A0 + 312 -> ~ (lo <= x < hi).
Proof.
  intros A A0 lo hi x E H0 H1 Hlo Hhi Hx.
  assert (Ew : A mod 2 ^ 64 = A0 mod 2 ^ 64).
  { apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. exact E. }
  rewrite (Z.mod_small A (2 ^ 64)) in Ew by lia.
  pose proof (Z.div_mod A0 (2 ^ 64) ltac:(lia)) as Hdm. rewrite <- Ew in Hdm.
  remember (A0 / 2 ^ 64) as qq eqn:Eq. clear Eq.
  change (2 ^ 64) with 18446744073709551616 in *. lia.
Qed.

(* A q64 spill, read as a single 8-byte read-only cell at the FRA spill base A + off. *)
Lemma r18_spill_ro : forall (regs : bvmap 5 word) m off v A,
  spill regs m off v -> getr regs 9 = Z_to_bv 64 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  ro_cells rsegs m (A + off) [C8 (Z_to_bv 64 v)].
Proof.
  intros regs m off v A (A1 & Hr9' & Hq) Hr9 HA0 HAb Hoff.
  unfold rg in Hr9'. assert (Hcong : Z_to_bv 64 A = Z_to_bv 64 A1) by (rewrite <- Hr9; exact Hr9').
  unfold ro_cells, cells_at. split; [cbn; tauto|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r.
  unfold q64 in Hq.
  eapply r18_bytes_cong; [ apply r18_bv_mod; exact Hcong | lia | rewrite length_le8; lia | exact Hq ].
Qed.

(* A q64 spill as an 8-byte read. *)
Lemma r18_spill_rd : forall (regs : bvmap 5 word) m off v A,
  spill regs m off v -> getr regs 9 = Z_to_bv 64 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  ov_read_bytes rsegs m (wa (A + off)) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros regs m off v A HS Hr9 HA0 HAb Hoff.
  destruct (r18_spill_ro regs m off v A HS Hr9 HA0 HAb Hoff) as (_ & HB).
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  exact (r18_rdn m _ _ 8%nat HB (length_le8 _)).
Qed.

(* A q64 spill transported across a run whose write set W avoids the spill's 8-byte footprint at A + off. *)
Lemma r18_spill_keep : forall (regs regs'' : bvmap 5 word) m m' off v A W,
  spill regs m off v -> getr regs 9 = Z_to_bv 64 A -> getr regs'' 9 = getr regs 9 ->
  0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) ->
  spill regs'' m' off v.
Proof.
  intros regs regs'' m m' off v A W (A1 & Hr9' & Hq) Hr9 K9 HA0 HAb Hoff MU Hout.
  unfold rg in Hr9'. assert (Hcong : Z_to_bv 64 A = Z_to_bv 64 A1) by (rewrite <- Hr9; exact Hr9').
  assert (Hq2 : q64 m (A + off) v).
  { unfold q64 in *.
    eapply r18_bytes_cong; [ apply r18_bv_mod; exact Hcong | lia | rewrite length_le8; lia | exact Hq ]. }
  exists A. split; [unfold rg; transitivity (getr regs 9); [exact K9 | exact Hr9]|].
  unfold q64 in *. eapply fl_bytes; [exact Hq2 | exact MU |]. rewrite length_le8. exact Hout.
Qed.

(* ---- the model facts of the two 4-byte compares and of the declaration ---- *)

(* The row's words at + 16 and + 20 as little-endian 4-byte runs (computed over the 11 catalogue rows). *)
Lemma r18_row_le : forall i, 0 <= i < 11 ->
  firstn 4 (skipn 16 (rowb i)) = le4 (Z_to_bv 64 (RcDecl.box_ic (rowb i))) /\
  firstn 4 (skipn 20 (rowb i)) = le4 (Z_to_bv 64 (RcDecl.box_oc (rowb i))).
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    split; apply a_bytes_eq; vm_compute; reflexivity.
Qed.

(* The round trip's row words at + 16 / + 20 are the two port counts ports_parse wrote (B3Rtm). *)
Lemma r18_row_ic : forall inp,
  firstn 4 (skipn 16 (rt_mb inp)) = le4 (Z_to_bv 64 (4 * RcLeaf.n_in (rt_pbs inp))).
Proof.
  intros inp. rewrite (a_rtm_in inp). unfold rt_mb.
  exact (proj1 (r18_row_le (istar inp) (a_istar_range inp))).
Qed.

Lemma r18_row_oc : forall inp,
  firstn 4 (skipn 20 (rt_mb inp)) = le4 (Z_to_bv 64 (4 * RcLeaf.n_out (rt_pbs inp))).
Proof.
  intros inp. rewrite (a_rtm_out inp). unfold rt_mb.
  exact (proj2 (r18_row_le (istar inp) (a_istar_range inp))).
Qed.

(* Each catalogue row has 296 bytes; its declaration has 32. *)
Lemma r18_row_len : forall inp, length (rt_mb inp) = 296%nat.
Proof. intros inp. a_rows inp; a_fin. Qed.

Lemma r18_decl_len : forall inp, length (RcDecl.decl (rt_mb inp)) = 32%nat.
Proof. intros inp. a_rows inp; a_fin. Qed.

(* ---- The Lib-level run of [0x81858, 0x818d0) with the declaration_of contract ---- *)

(* What the load at 0x818c4 and the call at 0x818cc need of the memory after the four metadata stores. *)
Definition r18_pre (m1 : word -> option byte) (A spv mr D : Z) (row : list byte) : Prop :=
  ov_read_bytes rsegs m1 (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr)) /\
  stk rsegs m1 (spv - DECLARATION_OF_K) spv /\
  bytes_at rsegs m1 mr row /\
  (exists ob, rw_cells rsegs m1 D [CB 32 ob]) /\
  asan_cells m1 /\ shadow_rw m1 /\ addressable m1 mr 296 /\ addressable m1 D 32.

(* One metadata store `sb zero,off(s3)`, with the munch / stk / wmono bookkeeping. *)
Ltac r18_sb SHv off STh MUh WMh :=
  let HS := fresh "HSok" in
  (lazymatch goal with
   | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
       assert (HS : store_ok rsegs mm (wa (SHv + off)) 1%nat = true)
         by (apply (r18_stk_store_ok mm (SHv + 320) (SHv + 324) (SHv + off) STh); lia)
   end);
  step;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bs) _) =>
       apply (munch_write [(SHv + 320, SHv + 324)] _ mm (SHv + off) bs) in MUh;
         [ | lia
           | rewrite length_le1; cbn [Z.of_nat]; lia
           | rewrite length_le1; cbn [inside Z.of_nat]; left; lia ];
       apply (stk_write rsegs mm (SHv + 320) (SHv + 324) (SHv + off) bs) in STh;
         [ | lia | rewrite length_le1; cbn [Z.of_nat]; lia ];
       apply (wmono_write rsegs _ mm aa bs) in WMh
   end);
  clear HS.

(* The byte just stored, as a one-byte run. *)
Ltac r18_newb SHv off Bn :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      assert (Bn : bytes_at rsegs (write_to_mem mm (wa (SHv + off)) bs) (SHv + off) [Z_to_bv 8 0]) by
        (rewrite <- r18_le1_0;
         apply (bytes_at_write_same rsegs mm (SHv + off) (le1 (Z_to_bv 64 0)));
         [ lia | rewrite length_le1; cbn [Z.of_nat]; lia ])
  end.

(* An earlier metadata byte across a later one-byte store. *)
Ltac r18_keepb SHv off Bn :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ ?bs) _) =>
      apply (bytes_at_write_other rsegs mm (SHv + off) bs) in Bn;
        [ | lia
          | rewrite length_le1; cbn [Z.of_nat]; lia
          | rewrite length_le1; cbn [length Z.of_nat]; lia ]
  end.

Ltac r18_shfix :=
  repeat match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (MState.unsigned_lit x) by lia
  end.

Lemma r18_evt : declaration_of_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A SHv D mr q v1 v2 : Z) (row : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s3 = Z_to_bv 64 SHv -> s10 = Z_to_bv 64 ASAN_K ->
    a0 = Z_to_bv 64 0 ->
    HIGHMEM_BEG + DECLARATION_OF_K <= spv -> spv <= APPMEM_END ->
    0 <= A -> A + 312 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 31 -> mr mod 8 = 0 ->
    6283264 <= SHv -> SHv + 324 <= 2 ^ 64 ->
    0 <= q -> q + 8 <= 2 ^ 64 ->
    6283264 <= D -> D + 32 <= 2 ^ 64 ->
    (D + 32 <= mr \/ mr + 296 <= D) ->
    (mr + 296 <= spv - DECLARATION_OF_K \/ spv <= mr) ->
    (D + 32 <= spv - DECLARATION_OF_K \/ spv <= D) ->
    (* the four metadata bytes are apart from the callee's write set (they are metadata, not application
       bytes, so one of the two orderings holds) *)
    (SHv + 324 <= spv - DECLARATION_OF_K \/ spv <= SHv + 320) ->
    (SHv + 324 <= D \/ D + 32 <= SHv + 320) ->
    (D + 32 <= RT_LO \/ RT_HI <= D) -> app_mem (D + 32) ->
    length row = 296%nat -> RcDecl.decl_ok row = true ->
    ov_read_bytes rsegs m (wa (A + 200)) 8 = Some (le8 (Z_to_bv 64 D)) ->
    ov_read_bytes rsegs m (wa (A + 8)) 8 = Some (le8 (Z_to_bv 64 (mr + 16))) ->
    ov_read_bytes rsegs m (wa (A + 0)) 8 = Some (le8 (Z_to_bv 64 (mr + 20))) ->
    ov_read_bytes rsegs m (wa (A + 216)) 8 = Some (le8 (Z_to_bv 64 q)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 16) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 20) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa q) 4 = Some (le4 (Z_to_bv 64 v1)) ->
    ov_read_bytes rsegs m (wa (q + 4)) 4 = Some (le4 (Z_to_bv 64 v2)) ->
    ov_read_bytes rsegs m (wa (mr + 16)) 4 = Some (le4 (Z_to_bv 64 v1)) ->
    ov_read_bytes rsegs m (wa (mr + 20)) 4 = Some (le4 (Z_to_bv 64 v2)) ->
    stk rsegs m (SHv + 320) (SHv + 324) ->
    ro_agree rsegs m ->
    (forall m1, munch [(SHv + 320, SHv + 324)] m m1 -> wmono rsegs m m1 ->
       stk rsegs m1 (SHv + 320) (SHv + 324) -> ro_agree rsegs m1 ->
       bytes_at rsegs m1 (SHv + 320) [Z_to_bv 8 0] -> bytes_at rsegs m1 (SHv + 321) [Z_to_bv 8 0] ->
       bytes_at rsegs m1 (SHv + 322) [Z_to_bv 8 0] -> bytes_at rsegs m1 (SHv + 323) [Z_to_bv 8 0] ->
       r18_pre m1 A spv mr D row) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m1 m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x818d0) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 27 = s11 /\
         getr R 18 = Z_to_bv 64 D /\ getr R 10 = Z_to_bv 64 1 /\
         munch [(SHv + 320, SHv + 324)] m m1 /\ wmono rsegs m m1 /\
         stk rsegs m1 (SHv + 320) (SHv + 324) /\
         munch [(spv - DECLARATION_OF_K, spv); (D, D + 32)] m1 m' /\ wmono rsegs m1 m' /\
         stk rsegs m' (spv - DECLARATION_OF_K) spv /\
         rw_cells rsegs m' D [CB 32 (RcDecl.decl row)] /\
         bytes_at rsegs m' mr row /\
         bytes_at rsegs m' (SHv + 320) [Z_to_bv 8 0] /\ bytes_at rsegs m' (SHv + 321) [Z_to_bv 8 0] /\
         bytes_at rsegs m' (SHv + 322) [Z_to_bv 8 0] /\ bytes_at rsegs m' (SHv + 323) [Z_to_bv 8 0])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81858) fc None m (seg_rom rsegs)).
Proof.
  intros DC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A SHv D mr q v1 v2 row -> -> -> -> -> Hsplo Hsphi HA0 HAb Hmr0 Hmrb Hmr8 HSH0 HSHb
    Hq0 Hqb HD0 HDb Hdm Hmsp Hdsp Hshsp Hshd Hrt Hdapp Hrowlen Hdecl
    R192 R16 R8 R216 K16 K20 Q1 Q2 M16 M20 ST HRO HPRE.
  assert (Hspv : 0 <= spv < 2 ^ 64) by (unfold HIGHMEM_BEG, DECLARATION_OF_K, APPMEM_END in *; lia).
  pose proof (munch_refl [(SHv + 320, SHv + 324)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* 81858 ld s2,200(s1) ; 8185c beqz a0,81864 (taken) *)
  step. step. if_true.
  (* 81864 ld a4,8(s1) ; 81868 srli a0,a4,3 ; 8186c add a0,a0,s10 *)
  step. step. step. r18_shfix.
  (* 81870 lb a3,0(a0) ; 81874 ld a0,216(s1) ; 81878 lw a0,0(a0) *)
  step. step. step.
  (* 8187c bnez a3,81960 (not taken) *)
  step. first [ if_false | if_false_by r18_nz0 ].
  (* 81880 lw a2,0(a4) ; 81884 beq a0,a2,8188c (taken) *)
  step. step. if_true_by (r18_eqb_refl (sx32 (Z_to_bv 64 v1))).
  (* 8188c ld a4,0(s1) ; 81890 srli ; 81894 add *)
  step. step. step. r18_shfix.
  (* 81898 lb a3,0(a0) ; 8189c ld a0,216(s1) ; 818a0 lw a0,4(a0) *)
  step. step. step.
  (* 818a4 bnez a3,81970 (not taken) *)
  step. first [ if_false | if_false_by r18_nz0 ].
  (* 818a8 lw a2,0(a4) ; 818ac beq a0,a2,818b4 (taken) *)
  step. step. if_true_by (r18_eqb_refl (sx32 (Z_to_bv 64 v2))).
  (* 818b4 .. 818c0 : the four metadata stores *)
  r18_sb SHv 320 ST MU WM. r18_newb SHv 320 B0.
  r18_sb SHv 321 ST MU WM. r18_keepb SHv 321 B0. r18_newb SHv 321 B1.
  r18_sb SHv 322 ST MU WM. r18_keepb SHv 322 B0. r18_keepb SHv 322 B1. r18_newb SHv 322 B2.
  r18_sb SHv 323 ST MU WM. r18_keepb SHv 323 B0. r18_keepb SHv 323 B1. r18_keepb SHv 323 B2.
  r18_newb SHv 323 B3.
  (* the four stores wrote metadata bytes only, above every read-only address *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MI : ro_agree rsegs mm)
        by (apply (r18_ro_keep m mm [(SHv + 320, SHv + 324)] HRO MU); intros x Hx;
            pose proof (r18_ro_lt x Hx) as Hlt; cbn [outside]; split; [lia | exact I])
  end.
  (* 818c4 ld a0,112(s1) ; 818c8 mv a1,s2 ; 818cc jal declaration_of *)
  destruct (HPRE _ MU WM ST MI B0 B1 B2 B3)
    as (R112 & STc & HROW & (ob & HOB) & HAC & HSW & HAmr & HAD).
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      change (ov_read_bytes rsegs mm (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr))) in R112
  end.
  step. step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm)
  end.
  (* declaration_of runs on the normalized memory, which has the mem_inv its contract asks for *)
  pose proof (mem_rel_normalize rsegs m1 MI) as REL.
  assert (STc0 : stk rsegs (normalize rsegs m1) (spv - DECLARATION_OF_K) spv)
    by exact (proj1 (b3n_rel_stk m1 (normalize rsegs m1) (spv - DECLARATION_OF_K) spv REL
                       ltac:(unfold HIGHMEM_BEG, DECLARATION_OF_K in *; lia) ltac:(lia)) STc).
  assert (HROW0 : bytes_at rsegs (normalize rsegs m1) mr row)
    by exact (proj1 (bytes_at_rel rsegs m1 _ _ _ REL) HROW).
  assert (HOB0 : rw_cells rsegs (normalize rsegs m1) D [CB 32 ob])
    by exact (proj1 (r18_rel_rw m1 (normalize rsegs m1) D _ REL ltac:(lia)) HOB).
  assert (HAC0 : asan_cells (normalize rsegs m1)) by exact (proj1 (b3n_rel_cells m1 _ REL) HAC).
  assert (HSW0 : shadow_rw (normalize rsegs m1)) by exact (proj1 (b3n_rel_sw m1 _ REL) HSW).
  assert (HAmr0 : addressable (normalize rsegs m1) mr 296) by exact (proj1 (b3n_rel_ad m1 _ _ _ REL) HAmr).
  assert (HAD0 : addressable (normalize rsegs m1) D 32) by exact (proj1 (b3n_rel_ad m1 _ _ _ REL) HAD).
  eapply evt_mono.
  { eapply (evt_normalize rsegs _ _ _ _ _ _ _ _ wx_apart_asan MI).
    eapply DC with (lo := spv - DECLARATION_OF_K) (row := row) (ob := ob);
      rewrite ?(MState.unsigned_lit spv) by lia; rewrite ?(MState.unsigned_lit mr) by lia;
      rewrite ?(MState.unsigned_lit D) by lia.
    - exact STc0.
    - lia.
    - exact Hmr8.
    - exact Hrowlen.
    - exact HROW0.
    - exact HOB0.
    - exact Hdm.
    - exact Hmsp.
    - exact Hdsp.
    - exact (mem_inv_normalize rsegs m1).
    - exact HAC0.
    - exact HSW0.
    - unfold HIGHMEM_BEG, DECLARATION_OF_K in *; lia.
    - lia.
    - exact HAmr0.
    - exact HAD0.
    - exact Hdapp.
    - exact Hrt. }
  intros ms' (s0' & PO & HREL & HROS). unfold declaration_of_post in PO. rewrite Hdecl in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MUc0 & WMc0 & _ & STq0 & HRW0 & HROWq0 & _ & _).
  subst s0'.
  destruct HREL as (ERg & EF & EP & ES & EV & EC & ERo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ERg, EF, EP, ES, EV, EC, ERo,
    HMR.
  pose proof (b3n_ms_eta ms' ES) as Ems.
  rewrite ERg, EF, EP, EC, EV, ERo in Ems.
  lazymatch type of Ems with
  | context [ret_pc (Z_to_bv 64 ?k)] =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) in Ems by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  remember (ms_mem ms') as m' eqn:Em'. clear Em'.
  rewrite ?(MState.unsigned_lit spv) in MUc0, STq0 by lia.
  rewrite ?(MState.unsigned_lit D) in MUc0, HRW0 by lia.
  rewrite ?(MState.unsigned_lit mr) in HROWq0 by lia.
  (* the post on the real memory *)
  assert (MUc : munch [(spv - DECLARATION_OF_K, spv); (D, D + 32)] m1 m')
    by exact (b3n_rel_munch _ m1 _ m' m0' REL HMR MUc0 HROS).
  assert (WMc : wmono rsegs m1 m').
  { apply (b3n_rel_wmono [(spv - DECLARATION_OF_K, spv); (D, D + 32)] m1 _ m' m0' REL HMR MUc WMc0).
    intros x E0. apply (b3n_W_ro _ x); [|exact E0].
    intros p Hp. cbn [In] in Hp. destruct Hp as [<-|[<-|[]]]; cbn [fst];
      unfold HIGHMEM_BEG, DECLARATION_OF_K in *; lia. }
  assert (STq : stk rsegs m' (spv - DECLARATION_OF_K) spv)
    by exact (proj2 (b3n_rel_stk m' m0' (spv - DECLARATION_OF_K) spv HMR
                       ltac:(unfold HIGHMEM_BEG, DECLARATION_OF_K in *; lia) ltac:(lia)) STq0).
  assert (HRW : rw_cells rsegs m' D [CB 32 (RcDecl.decl row)])
    by exact (proj2 (r18_rel_rw m' m0' D _ HMR ltac:(lia)) HRW0).
  assert (HROWq : bytes_at rsegs m' mr row) by exact (proj2 (bytes_at_rel rsegs m' m0' _ _ HMR) HROWq0).
  assert (HOUTD : forall k, 0 <= k < 4 ->
            disjoint_from [(spv - DECLARATION_OF_K, spv); (D, D + 32)] (SHv + 320 + k) 1).
  { intros k Hk. cbn [disjoint_from]. split; [|split; [|exact I]]; lia. }
  assert (HB0 : bytes_at rsegs m' (SHv + 320) [Z_to_bv 8 0]).
  { apply (bytes_at_transport rsegs _ _ m' (SHv + 320) [Z_to_bv 8 0] B0 MUc).
    cbn [length Z.of_nat]. replace (SHv + 320) with (SHv + 320 + 0) by lia. exact (HOUTD 0 ltac:(lia)). }
  assert (HB1 : bytes_at rsegs m' (SHv + 321) [Z_to_bv 8 0]).
  { apply (bytes_at_transport rsegs _ _ m' (SHv + 321) [Z_to_bv 8 0] B1 MUc).
    cbn [length Z.of_nat]. replace (SHv + 321) with (SHv + 320 + 1) by lia. exact (HOUTD 1 ltac:(lia)). }
  assert (HB2 : bytes_at rsegs m' (SHv + 322) [Z_to_bv 8 0]).
  { apply (bytes_at_transport rsegs _ _ m' (SHv + 322) [Z_to_bv 8 0] B2 MUc).
    cbn [length Z.of_nat]. replace (SHv + 322) with (SHv + 320 + 2) by lia. exact (HOUTD 2 ltac:(lia)). }
  assert (HB3 : bytes_at rsegs m' (SHv + 323) [Z_to_bv 8 0]).
  { apply (bytes_at_transport rsegs _ _ m' (SHv + 323) [Z_to_bv 8 0] B3 MUc).
    cbn [length Z.of_nat]. replace (SHv + 323) with (SHv + 320 + 3) by lia. exact (HOUTD 3 ltac:(lia)). }
  do 3 eexists. split; [exact Ems|].
  do 15 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|].
  split; [exact MUc|]. split; [exact WMc|]. split; [exact STq|].
  split; [exact HRW|]. split; [exact HROWq|].
  split; [exact HB0|]. split; [exact HB1|]. split; [exact HB2 | exact HB3].
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864). *)
Lemma r18_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold ACx.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* ---- the segment ---- *)

Section R18W.
Context {fx : YKa.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACx.AsanAllocAPI ACx.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis DC : declaration_of_contract.

(* The allocator laws whose inner lists this file takes apart (Contract.v, a Theorem Labs lane's v1.9 generation), each restated
   once here, so that a law that gains or moves a conjunct breaks this one proof and no use site (a Theorem Labs lane 15:32Z). *)
Local Notation law_AH := (ACx.aa_AH ACx.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_own := (ACx.aa_owned ACx.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_lo := (ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_hi := (ACx.aa_stkhi ACx.ASYMS AsanRTInv.RT (APIf rc)).

Lemma r18_law_blocks : forall H mem md p n, law_AH H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= law_lo mem md /\ end_in_app p n /\
  forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ ACx.a_in_img a /\ ~ ACx.a_on_img_page a /\
    ~ ACx.a_in_fs ACx.ASYMS mem a.
Proof. exact (ACx.a_laws_blocks _ _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r18_law_fs_place : forall H mem md b, law_AH H mem md -> word_mem rsegs mem (ACx.as_tp ACx.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  ACx.GT <= b /\ b + ACx.FS_SIZE <= law_lo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + ACx.FS_SIZE -> app_mem a.
Proof. exact (ACx.a_laws_fs_place _ _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r18_law_fs_ok : forall H mem md FS, law_AH H mem md -> word_mem rsegs mem (ACx.as_tp ACx.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> ACx.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw Hb.
  exact (proj1 (ACx.a_laws_fs_state _ _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hb)).
Qed.

Lemma r18_law_store : forall H mem mem' md, law_AH H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ACx.a_store_ok H (law_lo mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  law_AH H mem' md /\ (forall a, law_own H mem' md a <-> law_own H mem md a) /\ law_lo mem' md = law_lo mem md /\
  law_hi mem' md = law_hi mem md.
Proof. exact (ACx.a_laws_store _ _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r18_law_fs_store : forall H mem mem' md FS, law_AH H mem md -> word_mem rsegs mem (ACx.as_tp ACx.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ACx.a_store_ok H (law_lo mem md) a -> ~ (FS <= a < FS + ACx.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + ACx.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) -> ACx.a_fs_ok mem' FS ->
  law_AH H mem' md /\ (forall a, law_own H mem' md a <-> law_own H mem md a) /\ law_lo mem' md = law_lo mem md /\
  law_hi mem' md = law_hi mem md.
Proof. exact (ACx.a_laws_fs_store _ _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))). Qed.

(* Every frame byte is present in the state's memory: on the real arm the frame is inside the entry-anchored slot
   window, on the side arm it is inside the side stack, whose bytes a_fs_ok keeps mapped. *)
Lemma r18_frame_rd : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  forall a, fr <= a < fr + FRAME_BYTES -> exists b, mbyte rsegs mem a = Some b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA a Ha.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AFx.SLOT_STACK = 1048576) by reflexivity.
  destruct Hloc as [(H0 & Hspfr & Hreal)|(Hfr0 & HfsbS & Hfs & _)].
  - pose proof Hwin as Hw. unfold stk in Hw. destruct Hw as (_ & _ & Hwv).
    exact (proj2 (Hwv a ltac:(lia))).
  - destruct (Hfs a Ha) as (bb & Hb0 & Hwtp & Hbr).
    pose proof (r18_law_fs_ok
                (hb ++ g_H g) mem md bb HAH Hwtp Hb0) as Hfsok.
    exact (proj2 (proj1 Hfsok a Hbr)).
Qed.

(* The catalogue is one of the registered globals, so each of its bytes is addressable. *)
Lemma r18_cat_addr : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md -> forall a, CAT <= a < CAT + 3256 -> addressable mem a 1.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA a Ha.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  apply HAG. exists 0x9e800, 3256. split; [|unfold CAT in Ha; lia].
  unfold AFx.frame_AG. cbn [In]. repeat (first [ left; reflexivity | right ]).
Qed.

(* The catalogue's bytes are the image's: it is inside the RELRO range [0x9e348, 0x9e348 + 9344). *)
Lemma r18_cat_img : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  forall a, CAT <= a < CAT + 3256 -> mbyte rsegs mem a = seg_rom rsegs (wa a).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA a Ha.
  pose proof (proj1 FF) as SEGS.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  unfold G_img_c in Hgimg. rewrite SEGS in Hgimg.
  apply Hgimg. exists 0x9e348, 9344. split; [|unfold CAT in Ha; lia].
  unfold AFx.frame_RELRO. cbn [In]. repeat (first [ left; reflexivity | right ]).
Qed.

(* FRA and ENT across the four stores into the frame's own metadata bytes S(fr) + 320 .. + 323. *)
Lemma r18_sh_move : forall g fr hb regs regs' mem mem' md,
  FRA B APIf ra g fr hb regs mem md -> ENT (fx:=fx) APIf g hb mem md ->
  munch [(Sfr fr + 320, Sfr fr + 324)] mem mem' -> wmono rsegs mem mem' ->
  (forall qq, Sfr fr + 320 <= qq < Sfr fr + 324 -> exists b, mrd rsegs mem' (wa qq) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT (fx:=fx) APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md HFRA HENT MU WM HPres E2 E3 E4 E8 E9 E19 E26.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (ACx.a_laws_stack_high ACx.ASYMS _ _ _ _ ALAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  unfold ACx.GT in HGT.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hframe8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)); lia).
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= 2 ^ 64).
  { destruct Hsh as (sh0 & Hb0 & HL0).
    pose proof (bytes_at_bound rsegs mem (Sfr fr) sh0 Hb0) as Hbnd. rewrite HL0 in Hbnd. lia. }
  assert (HSfr0 : 0 <= Sfr fr) by (unfold ASAN_K in HSfrlo; lia).
  assert (HA64 : 0 <= A < 2 ^ 64) by (pose proof Hwin as Hw; unfold stk in Hw; lia).
  assert (HAhi : A + 312 <= 2 ^ 64).
  { unfold q64 in Hspill. apply bytes_at_bound in Hspill. rewrite length_le8 in Hspill. lia. }
  assert (HAlo : HIGHMEM_BEG <= A) by (unfold AFx.SLOT_STACK in Hstklo; lia).
  (* every written address is the metadata byte of a frame byte, so it is in the metadata map *)
  assert (Hinsh : forall x, Sfr fr + 320 <= x < Sfr fr + 324 -> in_shadow x).
  { intros x Hx. replace x with (shadow_addr (fr + (x - Sfr fr) * 8))
      by (rewrite r18_shadow_off by lia; lia).
    apply shadow_of_app. apply Happ. lia. }
  assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x).
  { intros x Hx Hwx. exact (WM (Z_to_bv 64 x) Hwx). }
  assert (Hout : forall x, 0 <= x < 2 ^ 64 -> ~ (Sfr fr + 320 <= x < Sfr fr + 324) ->
                   mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hx Hn. apply MU. rewrite MState.unsigned_lit by exact Hx.
    cbn [Frame.outside]. split; [exact Hn | exact I]. }
  assert (Hpres : forall q0, 0 <= q0 < 2 ^ 64 -> (exists b, mbyte rsegs mem q0 = Some b) ->
            exists b, mbyte rsegs mem' q0 = Some b).
  { intros q0 Hq0 Hb.
    destruct (Z_lt_le_dec q0 (Sfr fr + 320)) as [H1|H1].
    - unfold mbyte. rewrite (Hout q0 Hq0 ltac:(lia)). exact Hb.
    - destruct (Z_lt_le_dec q0 (Sfr fr + 324)) as [H2|H2].
      + exact (HPres q0 ltac:(lia)).
      + unfold mbyte. rewrite (Hout q0 Hq0 ltac:(lia)). exact Hb. }
  (* AH, the owned set, stklo and stkhi after the write, per frame-location arm *)
  assert (LAWS : ACx.aa_AH ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                 (forall a, ACx.aa_owned ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
                            ACx.aa_owned ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
                 ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem' md
                   = ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                 ACx.aa_stkhi ACx.ASYMS AsanRTInv.RT (APIf rc) mem' md
                   = ACx.aa_stkhi ACx.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [(Hs50 & Hspfr & Hreal)|(Hs5fr & HfsbS & Hfs & _)].
    - (* real arm: the written metadata bytes are the metadata of real-stack bytes (a_store_ok) *)
      assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                ~ ACx.a_store_ok (hb ++ g_H g) (ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
      { intros x Hx Hnok.
        destruct (Z_lt_le_dec x (Sfr fr + 320)) as [H1|H1]; [exact (Hout x Hx ltac:(lia))|].
        destruct (Z_lt_le_dec x (Sfr fr + 324)) as [H2|H2]; [|exact (Hout x Hx ltac:(lia))].
        exfalso. apply Hnok. right. right. right. exists (fr + (x - Sfr fr) * 8).
        split; [symmetry; rewrite r18_shadow_off by lia; lia|]. right. left.
        specialize (Hreal (fr + (x - Sfr fr) * 8) ltac:(lia)). lia. }
      exact (r18_law_store (hb ++ g_H g) mem mem' md HAH Hmc Hwrit).
    - (* side arm: the written metadata bytes are the metadata of side-stack bytes *)
      destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSb & HFSb0 & HwFSb & HFSbr).
      pose proof (HfsbS FSb HwFSb HFSb0) as HfrGE.
      pose proof (r18_law_fs_place (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0)
        as (HGTfs & HFSstk & _ & HFSapp).
      assert (HFSz : FSb + ACx.FS_SIZE <= 2 ^ 64)
        by (unfold APPMEM_END, AFx.SLOT_STACK in *; lia).
      pose proof (r18_law_fs_ok (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0)
        as Hfsok.
      assert (HFSsz : ACx.FS_SIZE = 11571200) by reflexivity.
      (* the base read off the frame's top byte covers the whole frame: the side stack's metadata region
         (36864 bytes) is below fr, and the top frame byte is inside [FSb, FSb + FS_SIZE). *)
      assert (HinFS : forall a0, fr <= a0 < fr + FRAME_BYTES -> FSb <= a0 < FSb + ACx.FS_SIZE).
      { intros a0 Ha0. lia. }
      assert (Hmeta : forall q0, fs_meta FSb q0 -> Frame.outside [(Sfr fr + 320, Sfr fr + 324)] q0).
      { intros q0 Hq0. pose proof (r18_fs_meta_range FSb q0 Hq0) as Hqr.
        assert (Hqa : app_mem q0) by (apply HFSapp; unfold ACx.FS_SIZE in *; lia).
        cbn [Frame.outside]. split; [|exact I]. intros Hqt.
        exact (AsanRTFacts.app_not_shadow q0 Hqa (Hinsh q0 Hqt)). }
      assert (Hfsok' : ACx.a_fs_ok mem' FSb).
      { apply (a_fs_ok_pres [(Sfr fr + 320, Sfr fr + 324)] mem mem' FSb Hfsok
                 (r18_munch_f _ _ _ MU) Hwrit Hpres Hmeta);
          unfold ACx.FS_SIZE; lia. }
      assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                ~ ACx.a_store_ok (hb ++ g_H g) (ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                ~ (FSb <= x < FSb + ACx.FS_SIZE) ->
                ~ (exists b, FSb <= b < FSb + ACx.FS_SIZE /\ x = shadow_addr b) ->
                mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
      { intros x Hx Hnok HnFS Hnsh.
        destruct (Z_lt_le_dec x (Sfr fr + 320)) as [H1|H1]; [exact (Hout x Hx ltac:(lia))|].
        destruct (Z_lt_le_dec x (Sfr fr + 324)) as [H2|H2]; [|exact (Hout x Hx ltac:(lia))].
        exfalso. apply Hnsh. exists (fr + (x - Sfr fr) * 8).
        split; [apply HinFS; lia | symmetry; rewrite r18_shadow_off by lia; lia]. }
      exact (r18_law_fs_store (hb ++ g_H g) mem mem' md FSb HAH HwFSb HFSb0
               Hmc Hwrit Hfsok'). }
  destruct LAWS as (HAH' & HOWN' & HSTK' & HSHI').
  (* the new 392 metadata bytes of the frame *)
  assert (Hsh' : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
  { destruct Hsh as (sh0 & Hb0 & HL0).
    apply (r18_bytes_of_present (Z.to_nat FRAME_SHADOW) mem' (Sfr fr)); [lia | lia |].
    intros k Hk.
    pose proof (proj2 (proj2 Hb0) k ltac:(lia)) as Hb0k.
    destruct (nth_error sh0 k) as [b|] eqn:Ek; [|exfalso; apply nth_error_None in Ek; lia].
    destruct (Z_lt_le_dec (Sfr fr + Z.of_nat k) (Sfr fr + 320)) as [H1|H1].
    - exists b. unfold mrd, wa in Hb0k |- *. rewrite (Hout (Sfr fr + Z.of_nat k) ltac:(lia) ltac:(lia)). exact Hb0k.
    - destruct (Z_lt_le_dec (Sfr fr + Z.of_nat k) (Sfr fr + 324)) as [H2|H2].
      + exact (HPres (Sfr fr + Z.of_nat k) ltac:(lia)).
      + exists b. unfold mrd, wa in Hb0k |- *. rewrite (Hout (Sfr fr + Z.of_nat k) ltac:(lia) ltac:(lia)).
        exact Hb0k. }
  (* the written range is below the application memory of the window and the spills *)
  assert (HshiHi : Sfr fr + 324 <= HIGHMEM_BEG).
  { pose proof (Hinsh (Sfr fr + 323) ltac:(lia)) as IS.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  assert (HA9 : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 -> A0 = A).
  { intros A0 HA0r HA0b. unfold rg in Hr9.
    pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HA0r)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A (2 ^ 64)) in E0 by lia. rewrite (Z.mod_small A0 (2 ^ 64)) in E0 by lia.
    symmetry; exact E0. }
  (* the premises of the frame-and-metadata transport, in its own order *)
  assert (Hrokeep : ro_agree rsegs mem').
  { apply (r18_ro_keep mem mem' _ Hro MU). intros x Hx.
    pose proof (r18_ro_lt x Hx) as Hlt. cbn [outside]. split; [|exact I].
    unfold ASAN_K in HSfrlo. lia. }
  assert (HDJ : rt_disjoint [(Sfr fr + 320, Sfr fr + 324)]).
  { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
      RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
      RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [disjoint_from].
    unfold ASAN_K in HSfrlo. repeat split; (lia || exact I). }
  assert (HWkept : forall x, 0 <= x < 2 ^ 64 -> ~ (fr + 24 <= x < fr + FRAME_BYTES) ->
            ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) -> Frame.outside [(Sfr fr + 320, Sfr fr + 324)] x).
  { intros x Hx Hnb Hnsh. cbn [Frame.outside]. split; [|exact I]. lia. }
  assert (HWspill : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
            forall x, A0 + 304 <= x < A0 + 312 -> Frame.outside [(Sfr fr + 320, Sfr fr + 324)] x).
  { intros A0 HA0r HA0b x Hx. pose proof (HA9 A0 HA0r HA0b) as <-.
    cbn [Frame.outside]. split; [|exact I]. unfold HIGHMEM_BEG in *. lia. }
  assert (HWsaved : forall x, g_S g - 104 <= x < g_S g ->
            Frame.outside [(Sfr fr + 320, Sfr fr + 324)] x).
  { intros x Hx. cbn [Frame.outside]. split; [|exact I]. unfold HIGHMEM_BEG in *. lia. }
  assert (HWsel : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
            forall x, A0 + 16 <= x < A0 + 32 -> Frame.outside [(Sfr fr + 320, Sfr fr + 324)] x).
  { intros A0 HA0r HA0b x Hx. pose proof (HA9 A0 HA0r HA0b) as <-.
    cbn [Frame.outside]. split; [|exact I]. unfold HIGHMEM_BEG in *. lia. }
  assert (HWwin : forall x, g_S g - AFx.SLOT_STACK <= x < g_S g ->
            Frame.outside [(Sfr fr + 320, Sfr fr + 324)] x \/ exists b, mem' (wa x) = Some b).
  { intros x Hx. left. cbn [Frame.outside]. split; [|exact I].
    unfold AFx.SLOT_STACK, HIGHMEM_BEG in *. lia. }
  assert (HAG' : forall a, in_globals AFx.frame_AG a -> addressable mem' a 1).
  { intros a Hin.
    apply (addr1_munch [(Sfr fr + 320, Sfr fr + 324)] mem mem' a (r18_munch_f _ _ _ MU));
      [|exact (HAG a Hin)].
    cbn [Frame.outside]. split; [|exact I].
    destruct Hin as (lo & len & Hinl & Hr).
    pose proof (r18_AG_lt a lo len Hinl Hr) as Halt.
    pose proof (addr1_app mem a (HAG a (ex_intro _ lo (ex_intro _ len (conj Hinl Hr))))) as Happa.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happa.
    unfold Sfr, shadow_addr, ASAN_K in *.
    revert Happa Halt HGT. Z.div_mod_to_equations. lia. }
  split.
  - exact (sl_fr_meta B APIf ra empty FF g fr hb regs regs' mem mem'
             md [(Sfr fr + 320, Sfr fr + 324)] HFRA (r18_munch_f _ _ _ MU) (r18_wmono_f _ _ WM)
             Hrokeep HDJ HAH' HSTK' Happ HGT Hsh' HWkept HWspill HWsaved HWsel HWwin HAG'
             E2 E3 E4 E8 E9 E19 E26).
  - apply (ent_store B APIf ra g fr hb regs mem mem' md [(Sfr fr + 320, Sfr fr + 324)]
             HENT HFRA (r18_munch_f _ _ _ MU)); [| exact HSTK' | exact HSHI' |].
    + intros x Hx.
      destruct (Z_lt_le_dec x (Sfr fr + 320)) as [H1|H1];
        [left; cbn [Frame.outside]; split; [lia|exact I]|].
      destruct (Z_lt_le_dec x (Sfr fr + 324)) as [H2|H2];
        [|left; cbn [Frame.outside]; split; [lia|exact I]].
      right. right. right. unfold Sfr in *. lia.
    + intros a Himg Ho. exact (proj2 (HOWN' a) Ho).
Qed.

(* AH, the owned set, stklo and stkhi after the callee's store W = [sp - K, sp) + [fr + 2560, fr + 2592). *)
Lemma r18_ah : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  munch [(ACx.aspZ regs - DECLARATION_OF_K, ACx.aspZ regs); (fr + 2560, fr + 2560 + 32)] mem mem' ->
  wmono rsegs mem mem' -> rd_mono mem mem' ->
  ACx.aa_AH ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall a, ACx.aa_owned ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
             ACx.aa_owned ACx.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
  ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem' md
    = ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  ACx.aa_stkhi ACx.ASYMS AsanRTInv.RT (APIf rc) mem' md
    = ACx.aa_stkhi ACx.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md HFRA MU WM HRDM.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlowin & Hstkwin).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  rewrite Haspz in MU, Hlowin.
  assert (HSS : AFx.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : ACx.FS_SIZE = 11571200) by reflexivity.
  unfold FN_STACK in Hlowin.
  pose proof (ACx.a_laws_stack_high ACx.ASYMS _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH) as Hhigh.
  unfold stk in Hwin. destruct Hwin as (Hwlo & Hwhi & _).
  assert (HWR : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a).
  { intros a _ Ha. exact (WM (Z_to_bv 64 a) Ha). }
  destruct Hloc as [(H0 & Hspfr & Hreal)|(Hfr0 & HfsbS & Hfs & _)].
  - assert (Hunch : forall a, 0 <= a < 2 ^ 64 ->
      ~ ACx.a_store_ok (hb ++ g_H g) (ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
      split; [|split; [|exact I]]; intro Hin.
      - apply Hns. unfold ACx.a_store_ok. right; left.
        unfold DECLARATION_OF_K, APPMEM_END, AFx.SLOT_STACK in *. split; lia.
      - apply Hns. unfold ACx.a_store_ok. right; left. exact (Hreal a ltac:(lia)). }
    exact (r18_law_store
             (hb ++ g_H g) mem mem' md HAH Hunch HWR).
  - destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSb & HFSb0 & HwFSb & HFSbr).
    pose proof (HfsbS FSb HwFSb HFSb0) as HfrGE.
    pose proof (r18_law_fs_place
                  (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0) as (HGTfs & HFSstk & _ & _).
    assert (HFSz : FSb + ACx.FS_SIZE <= 2 ^ 64)
      by (unfold APPMEM_END, AFx.SLOT_STACK in *; lia).
    pose proof (r18_law_fs_ok
                  (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0) as Hfsok.
    assert (HPres : forall q0, 0 <= q0 < 2 ^ 64 -> (exists b, mbyte rsegs mem q0 = Some b) ->
                    (exists b, mbyte rsegs mem' q0 = Some b)).
    { intros q0 Hq0 Hp. apply (HRDM (wa q0)). exact Hp. }
    assert (Hfsok' : ACx.a_fs_ok mem' FSb).
    { apply (a_fs_ok_pres [(sp - DECLARATION_OF_K, sp); (fr + 2560, fr + 2560 + 32)] mem mem' FSb
               Hfsok (r18_munch_f _ _ _ MU) HWR HPres).
      - intros q0 Hmeta. pose proof (fs_meta_below FSb q0 Hmeta) as Hbelow.
        cbn [Frame.outside]. split; [|split; [|exact I]]; intro Hin;
          unfold DECLARATION_OF_K, ACx.FS_SIZE, APPMEM_END, AFx.SLOT_STACK in *; lia.
      - lia.
      - exact HFSz. }
    assert (Hunch : forall a, 0 <= a < 2 ^ 64 ->
      ~ ACx.a_store_ok (hb ++ g_H g) (ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FSb <= a < FSb + ACx.FS_SIZE) ->
      ~ (exists bb, FSb <= bb < FSb + ACx.FS_SIZE /\ a = shadow_addr bb) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns HnFS Hnsh. apply MU. rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
      split; [|split; [|exact I]]; intro Hin.
      - apply Hns. unfold ACx.a_store_ok. right; left.
        unfold DECLARATION_OF_K, APPMEM_END, AFx.SLOT_STACK in *. split; lia.
      - apply HnFS. unfold DECLARATION_OF_K, ACx.FS_SIZE in *. split; lia. }
    exact (r18_law_fs_store
             (hb ++ g_H g) mem mem' md FSb HAH HwFSb HFSb0 Hunch HWR Hfsok').
Qed.

Lemma seg_R18 : forall b, Hat B APIf ra (Inv_A818d0_at (fx:=fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A81858_at (fx:=fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hbody).
  destruct Hbody as ((Hgn & Hb6 & HHB & H23 & HOUR & HOUTA & HCUR & Hsp192) & Hb0 & HRFb & H27 & Ha0 &
    HU1 & HU2 & Hsp216 & Hsp16 & Hsp8 & Hsp112 & Hsp128 & HPRO & Hsp104 & Hsp96 & Hsp64 & H21 & Hsp144 &
    Hsp208 & HRWid & HRWjk & Hsp280 & Hsp240 & HRWjy & HRWsc & Hsp152 & HAid & HRXS).
  subst c. subst b.
  (* the layout constants as equations, so that lia reads them without unfolding *)
  assert (EHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (EAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (ELE : LOWMEM_END = 0x7fff8000) by reflexivity.
  assert (EAK : ASAN_K = 0x7fff8000) by reflexivity.
  assert (ECAT : CAT = 0x9e800) by reflexivity.
  assert (ECR : CAT_ROW = 296) by reflexivity.
  assert (EDK : DECLARATION_OF_K = 2304) by reflexivity.
  assert (ESS : AFx.SLOT_STACK = 1048576) by reflexivity.
  assert (EFN : FN_STACK = 1044480) by reflexivity.
  assert (EGT : ACx.GT = 6283264) by reflexivity.
  assert (EFS : ACx.FS_SIZE = 11571200) by reflexivity.
  assert (EDS : decl_slot fr = fr + 2560) by reflexivity.
  (* names from FRA *)
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hlowin & Hstkwin).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hfrpl & Hfr9 & Hfspl & Hfrwr).
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (HGTfr & Hframeapp).
  pose proof (sl_frame_apart_win B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as Hapart.
  rewrite Haspz in Hlowin, Hstkwin, Hapart.
  assert (HSS : AFx.SLOT_STACK = 1048576) by reflexivity.
  unfold FN_STACK in Hlowin, Hstkwin.
  pose proof (ACx.a_laws_stack_high ACx.ASYMS _ _ _ _ (ACx.aa_laws ACx.ASYMS AsanRTInv.RT (APIf rc))
                (hb1 phi (rnb g 0) ++ g_H g) mem md HAH) as Hhigh.
  unfold ACx.GT in HGTfr.
  assert (HSPstrong : HIGHMEM_BEG + 1044480 <= sp) by (unfold HIGHMEM_BEG in *; lia).
  (* RT facts *)
  destruct HRT as (HAC & HSW & HasO & HCF & HasR & HREAL & HasRest).
  (* round-trip bundle *)
  pose proof HRFb as ((Hb6' & HCUR' & HOUR' & H23' & HIDB & HFGB) & Hnz & H24 & HF).
  destruct (a_rtn (g_in g) (Z.of_nat 0) Hnz) as (_ & Hnb & HL).
  change (rt_n (g_in g) (Z.of_nat 0)) with (rnb g 0) in Hnb, HL.
  change (Z.of_nat 0) with 0 in HL, HF.
  (* phi placement *)
  pose proof (a_hb B APIf ra g fr phi (rnb g 0) regs mem md HFRA) as (Hphi0' & Hphi4096 & Hphistk & Hein & Hphibytes).
  (* A in range *)
  assert (HA0 : 0 <= A) by (unfold stk in Hwin; lia).
  assert (HSle : g_S g <= 2 ^ 64) by (unfold stk in Hwin; lia).
  assert (HA312 : A + 312 <= 2 ^ 64) by lia.
  assert (Hframe8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia).
  assert (HSfr324 : Sfr fr + 324 <= HIGHMEM_BEG).
  { assert (Hin : in_shadow (Sfr fr + 323)).
    { replace (Sfr fr + 323) with (shadow_addr (fr + 323 * 8)) by (rewrite r18_shadow_off by lia; lia).
      apply shadow_of_app. apply Hframeapp. lia. }
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin |- *. lia. }
  (* the catalogue row *)
  assert (Hrowr : CAT <= mrow (g_in g) /\ mrow (g_in g) + 296 <= CAT + 3256).
  { unfold mrow. pose proof (a_istar_range (g_in g)) as Hi. lia. }
  assert (Hmr8 : mrow (g_in g) mod 8 = 0).
  { unfold mrow, CAT, CAT_ROW. pose proof (a_istar_range (g_in g)) as Hi.
    replace (649216 + 296 * istar (g_in g)) with ((81152 + 37 * istar (g_in g)) * 8) by lia.
    apply Z_mod_mult. }
  assert (Hrowaddr1 : forall a, CAT <= a < CAT + 3256 -> addressable mem a 1)
    by exact (r18_cat_addr g fr (hb1 phi (rnb g 0)) regs mem md HFRA).
  assert (Hrow296 : addressable mem (mrow (g_in g)) 296).
  { apply r18_addr_join; [unfold CAT in Hrowr; lia | lia | unfold CAT, APPMEM_END in *; lia |].
    intros i Hi. apply Hrowaddr1. unfold CAT in *. lia. }
  assert (Hrowgran : addressable mem (mrow (g_in g) + 16) 8).
  { apply r18_addr_join; [unfold CAT in Hrowr; lia | lia | unfold CAT, APPMEM_END in *; lia |].
    intros i Hi. apply Hrowaddr1. unfold CAT in *. lia. }
  assert (Hrowb : bytes_at rsegs mem (mrow (g_in g)) (rt_mb (g_in g))).
  { pose proof (a_row_img (istar (g_in g)) (a_istar_range (g_in g))) as HIM.
    apply (r18_img_bytes mem (mrow (g_in g)) 296 (rt_mb (g_in g))).
    - intros k Hk. apply (r18_cat_img g fr (hb1 phi (rnb g 0)) regs mem md HFRA). unfold CAT in *. lia.
    - unfold rt_mb. exact HIM.
    - unfold CAT in Hrowr; lia.
    - unfold CAT, APPMEM_END in *; lia. }
  (* the two 4-byte compares: the row's words at + 16 / + 20 are ports_parse's two outputs *)
  assert (Hrow16 : bytes_at rsegs mem (mrow (g_in g) + 16)
                     (le4 (Z_to_bv 64 (4 * RcLeaf.n_in (rt_pbs (g_in g)))))).
  { rewrite <- (r18_row_ic (g_in g)).
    replace (mrow (g_in g) + 16) with (mrow (g_in g) + Z.of_nat 16) by lia.
    apply (r18_sub mem (mrow (g_in g)) (rt_mb (g_in g)) 16 4);
      [ exact Hrowb | rewrite (r18_row_len (g_in g)); lia ]. }
  assert (Hrow20 : bytes_at rsegs mem (mrow (g_in g) + 20)
                     (le4 (Z_to_bv 64 (4 * RcLeaf.n_out (rt_pbs (g_in g)))))).
  { rewrite <- (r18_row_oc (g_in g)).
    replace (mrow (g_in g) + 20) with (mrow (g_in g) + Z.of_nat 20) by lia.
    apply (r18_sub mem (mrow (g_in g)) (rt_mb (g_in g)) 20 4);
      [ exact Hrowb | rewrite (r18_row_len (g_in g)); lia ]. }
  (* the frame's metadata bytes of the declaration slot, and the four stores' window *)
  assert (HstkSH : stk rsegs mem (Sfr fr + 320) (Sfr fr + 324)).
  { split; [unfold ASAN_K in HSfrlo; lia|]. split; [unfold HIGHMEM_BEG in HSfr324; lia|].
    intros a Ha. apply HSW.
    replace a with (shadow_addr (fr + (a - Sfr fr) * 8)) by (rewrite r18_shadow_off by lia; lia).
    apply shadow_of_app. apply Hframeapp. lia. }
  (* geometry of the frame, the window and the block *)
  assert (Hspapp : forall x, sp - DECLARATION_OF_K <= x < sp -> app_mem x).
  { intros x Hx. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END, DECLARATION_OF_K in *. lia. }
  assert (Hblkfr : fr + FRAME_BYTES <= phi \/ phi + rnb g 0 <= fr).
  { destruct Hloc as [(H0' & Hspfr & Hreal)|(Hfr0' & HfsbS & Hfs & _)].
    - right. lia.
    - destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [Hle|Hgt]; [left; exact Hle|].
      destruct (Z_le_gt_dec (phi + rnb g 0) fr) as [Hle2|Hgt2]; [right; exact Hle2|].
      exfalso.
      pose proof (r18_law_blocks
                    (hb1 phi (rnb g 0) ++ g_H g) mem md phi (rnb g 0) HAH
                    ltac:(unfold hb1; apply in_or_app; left; apply in_eq)) as (_ & _ & _ & _ & Hbb).
      destruct (Hbb (Z.max phi fr) ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
      exact (Hnfs (Hfs (Z.max phi fr) ltac:(lia))). }
  assert (Hdeclsp : decl_slot fr + 32 <= sp - DECLARATION_OF_K \/ sp <= decl_slot fr).
  { destruct (Hfrpl DECLARATION_OF_K ltac:(unfold FN_STACK, DECLARATION_OF_K; lia)) as [Hc|Hc];
      rewrite Haspz in Hc; unfold decl_slot; [left; lia | right; lia]. }
  assert (Hrowsp : mrow (g_in g) + 296 <= sp - DECLARATION_OF_K \/ sp <= mrow (g_in g))
    by (left; unfold CAT, DECLARATION_OF_K, HIGHMEM_BEG in *; lia).
  assert (Hdeclrow : decl_slot fr + 32 <= mrow (g_in g) \/ mrow (g_in g) + 296 <= decl_slot fr)
    by (right; unfold decl_slot, CAT in *; lia).
  (* the metadata bytes of the declaration slot *)
  assert (HdeclD : decl_slot fr = fr + 2560) by reflexivity.
  (* run *)
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x81858) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x818d0 /\
       exists mem1,
       YKa.getr R 2 = YKa.getr regs 2 /\ YKa.getr R 3 = YKa.getr regs 3 /\
       YKa.getr R 4 = YKa.getr regs 4 /\ YKa.getr R 8 = YKa.getr regs 8 /\
       YKa.getr R 9 = YKa.getr regs 9 /\ YKa.getr R 19 = YKa.getr regs 19 /\
       YKa.getr R 21 = YKa.getr regs 21 /\ YKa.getr R 22 = YKa.getr regs 22 /\
       YKa.getr R 23 = YKa.getr regs 23 /\ YKa.getr R 24 = YKa.getr regs 24 /\
       YKa.getr R 25 = YKa.getr regs 25 /\ YKa.getr R 26 = YKa.getr regs 26 /\
       YKa.getr R 27 = YKa.getr regs 27 /\
       YKa.getr R 18 = Z_to_bv 64 (decl_slot fr) /\ YKa.getr R 10 = Z_to_bv 64 1 /\
       munch [(Sfr fr + 320, Sfr fr + 324)] mem mem1 /\ wmono rsegs mem mem1 /\
       stk rsegs mem1 (Sfr fr + 320) (Sfr fr + 324) /\
       munch [(sp - DECLARATION_OF_K, sp); (decl_slot fr, decl_slot fr + 32)] mem1 mem' /\
       wmono rsegs mem1 mem' /\
       stk rsegs mem' (sp - DECLARATION_OF_K) sp /\
       rw_cells rsegs mem' (decl_slot fr) [CB 32 (RcDecl.decl (rt_mb (g_in g)))] /\
       bytes_at rsegs mem' (mrow (g_in g)) (rt_mb (g_in g)) /\
       bytes_at rsegs mem' (Sfr fr + 320) [Z_to_bv 8 0] /\ bytes_at rsegs mem' (Sfr fr + 321) [Z_to_bv 8 0] /\
       bytes_at rsegs mem' (Sfr fr + 322) [Z_to_bv 8 0] /\ bytes_at rsegs mem' (Sfr fr + 323) [Z_to_bv 8 0])
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg in Ha0, H21, Hr19, Hr26, Hr9.
    eapply evt_mono.
    + apply (r18_evt DC) with (spv := sp) (A := A) (SHv := Sfr fr) (D := decl_slot fr)
        (mr := mrow (g_in g)) (q := fr + 2528)
        (v1 := 4 * RcLeaf.n_in (rt_pbs (g_in g))) (v2 := 4 * RcLeaf.n_out (rt_pbs (g_in g)))
        (row := rt_mb (g_in g)).
      * exact Hr2.
      * exact Hr9.
      * exact Hr19.
      * exact Hr26.
      * exact Ha0.
      * unfold DECLARATION_OF_K, HIGHMEM_BEG in *; lia.
      * unfold APPMEM_END in *; lia.
      * exact HA0.
      * exact HA312.
      * unfold CAT in Hrowr; lia.
      * unfold CAT in Hrowr; lia.
      * exact Hmr8.
      * unfold ASAN_K in HSfrlo; lia.
      * unfold HIGHMEM_BEG in HSfr324; lia.
      * lia.
      * lia.
      * unfold decl_slot; lia.
      * unfold decl_slot, APPMEM_END in *; lia.
      * exact Hdeclrow.
      * exact Hrowsp.
      * exact Hdeclsp.
      * left. unfold DECLARATION_OF_K, HIGHMEM_BEG in *. lia.
      * (* metadata bytes against the declaration slot: the frame is application memory, the four bytes are
           metadata, so the frame is either wholly above them or wholly below *)
        destruct (Hframeapp (decl_slot fr) ltac:(unfold decl_slot; lia)) as [Hlow | Hhiapp].
        -- right. unfold decl_slot, Sfr, shadow_addr, ASAN_K, LOWMEM_END in *.
           revert Hframe8 Hlow. Z.div_mod_to_equations. lia.
        -- left. unfold HIGHMEM_BEG in *. lia.
      * unfold RT_LO, RT_HI, decl_slot. right. unfold ACx.GT in *. lia.
      * unfold decl_slot. apply Hframeapp. lia.
      * exact (r18_row_len (g_in g)).
      * exact (a_rtm_declok (g_in g)).
      * exact (r18_spill_rd regs mem 200 (decl_slot fr) A Hsp192 Hr9 HA0 ltac:(lia) ltac:(lia)).
      * exact (r18_spill_rd regs mem 8 (mrow (g_in g) + 16) A Hsp16 Hr9 HA0 ltac:(lia) ltac:(lia)).
      * exact (r18_spill_rd regs mem 0 (mrow (g_in g) + 20) A Hsp8 Hr9 HA0 ltac:(lia) ltac:(lia)).
      * exact (r18_spill_rd regs mem 216 (fr + 2528) A Hsp216 Hr9 HA0 ltac:(lia) ltac:(lia)).
      * exact (r18_meta0 mem (mrow (g_in g) + 16) (mrow (g_in g) + 16) Hrowgran
                 ltac:(revert Hmr8; Z.div_mod_to_equations; lia) ltac:(lia)).
      * exact (r18_meta0 mem (mrow (g_in g) + 16) (mrow (g_in g) + 20) Hrowgran
                 ltac:(revert Hmr8; Z.div_mod_to_equations; lia) ltac:(lia)).
      * exact (r18_rdn mem (fr + 2528) _ 4%nat HU1 (length_le4 _)).
      * replace (fr + 2528 + 4) with (fr + 2532) by lia.
        exact (r18_rdn mem (fr + 2532) _ 4%nat HU2 (length_le4 _)).
      * exact (r18_rdn mem (mrow (g_in g) + 16) _ 4%nat Hrow16 (length_le4 _)).
      * exact (r18_rdn mem (mrow (g_in g) + 20) _ 4%nat Hrow20 (length_le4 _)).
      * exact HstkSH.
      * exact Hro.
      * (* the facts the load at 0x818c4 and the call need, after the four metadata stores *)
        intros mem1 MU1 WM1 ST1 MI1 HZ0 HZ1 HZ2 HZ3.
        assert (HRDM1 : rd_mono mem mem1).
        { apply (rd_mono_list [(Sfr fr + 320, Sfr fr + 324)] mem mem1 MU1).
          constructor; [|constructor].
          cbn [fst snd]. intros y Hy.
          destruct ST1 as (_ & _ & ST1v). exact (proj2 (ST1v y ltac:(lia))). }
        split.
        { apply (r18_spill_rd regs mem1 112 (mrow (g_in g)) A); try assumption; try lia.
          apply (r18_spill_keep regs regs mem mem1 112 (mrow (g_in g)) A
                   [(Sfr fr + 320, Sfr fr + 324)] Hsp112 Hr9 eq_refl HA0 ltac:(lia) ltac:(lia) MU1).
          intros x Hx. cbn [Frame.outside]. split; [|exact I].
          unfold HIGHMEM_BEG in *; lia. }
        split.
        { split; [unfold HIGHMEM_BEG, DECLARATION_OF_K in *; lia|]. split; [unfold APPMEM_END in *; lia|].
          intros a Ha. destruct Hstkwin as (_ & _ & Hwv).
          destruct (Hwv a ltac:(unfold DECLARATION_OF_K in *; lia)) as (Hw1 & Hw2).
          split.
          - exact (WM1 (wa a) Hw1).
          - exact (HRDM1 (wa a) Hw2). }
        split.
        { apply (a_keep [(Sfr fr + 320, Sfr fr + 324)] mem mem1 (mrow (g_in g)) (rt_mb (g_in g)) MU1);
            [|exact Hrowb].
          rewrite (r18_row_len (g_in g)). intros x Hx. cbn [Frame.outside]. split; [|exact I].
          unfold CAT in *. unfold HIGHMEM_BEG in *. lia. }
        split.
        { assert (HDpres : forall k, (k < 32)%nat ->
                    exists bb, mrd rsegs mem1 (wa (decl_slot fr + Z.of_nat k)) = Some bb).
          { intros k Hk.
            destruct (r18_frame_rd g fr (hb1 phi (rnb g 0)) regs mem md HFRA (decl_slot fr + Z.of_nat k)
                        ltac:(unfold decl_slot; lia)) as (bb & Hbb).
            unfold mbyte in Hbb. exact (HRDM1 (wa (decl_slot fr + Z.of_nat k)) (ex_intro _ bb Hbb)). }
          destruct (r18_bytes_of_present 32%nat mem1 (decl_slot fr)
                      ltac:(unfold decl_slot; lia) ltac:(unfold decl_slot, APPMEM_END in *; lia) HDpres)
            as (ob & HobB & HobL).
          exists ob. split; [split; [cbn; exact (conj HobL I) |
                                     cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HobB]|].
          split; [unfold decl_slot; lia|]. split; [cbn [cells_size csize]; unfold decl_slot in *; lia|].
          intros i Hi. cbn [cells_size csize] in Hi.
          apply (WM1 (wa (decl_slot fr + i))). apply Hfrwr. unfold decl_slot. lia. }
        split.
        { (* every runtime cell is an image byte, below GT; the four stores are metadata bytes above ASAN_K *)
          assert (HWlo1 : forall x, 0 <= x < 6283264 -> outside [(Sfr fr + 320, Sfr fr + 324)] x).
          { intros x Hx. cbn [outside]. split; [|exact I]. lia. }
          unfold asan_cells in HAC |- *.
          decompose [and] HAC.
          repeat split;
            (eapply r18_keep_low; [exact MU1 | eassumption | exact HWlo1 |
               rewrite ?length_le8, ?length_le4; cbn [length Z.of_nat];
               unfold CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND,
                 GOT_HIEND, MIDBEG, GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, REAL_MEMSET,
                 GOT_REAL_MEMSET; lia]). }
        split.
        { intros a Hin.
          destruct (Z_lt_le_dec a (Sfr fr + 320)) as [H1|H1].
          - destruct (HSW a Hin) as (Hw1 & Hw2). split.
            + assert (Hm : mem1 (wa a) = mem (wa a)).
              { apply MU1. rewrite Mem.wa_unsigned by (pose proof (in_shadow_range a Hin); lia).
                cbn [outside]. split; [lia | exact I]. }
              unfold wview in *. rewrite Hm. exact Hw1.
            + exact (HRDM1 (wa a) Hw2).
          - destruct (Z_lt_le_dec a (Sfr fr + 324)) as [H2|H2].
            + destruct ST1 as (_ & _ & ST1v). exact (ST1v a ltac:(lia)).
            + destruct (HSW a Hin) as (Hw1 & Hw2). split.
              * assert (Hm : mem1 (wa a) = mem (wa a)).
                { apply MU1. rewrite Mem.wa_unsigned by (pose proof (in_shadow_range a Hin); lia).
                  cbn [outside]. split; [lia | exact I]. }
                unfold wview in *. rewrite Hm. exact Hw1.
              * exact (HRDM1 (wa a) Hw2). }
        split.
        { apply (r18_addr_keep_rng mem mem1 _ (mrow (g_in g)) 296 Hrow296 MU1).
          intros i Hi. cbn [Frame.outside]. split; [|exact I].
          pose proof (Hrowaddr1 (mrow (g_in g) + i) ltac:(unfold CAT in *; lia)) as Hai.
          pose proof (addr1_app mem (mrow (g_in g) + i) Hai) as Happi.
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happi.
          unfold shadow_addr, Sfr, ASAN_K in *. unfold CAT in *.
          revert Happi HSfr324 HGTfr. unfold Sfr, shadow_addr, ASAN_K.
          Z.div_mod_to_equations. lia. }
        { (* the 32 bytes at the declaration slot are marked usable by the four stores *)
          split; [unfold decl_slot; lia|]. split; [lia|].
          split; [unfold decl_slot, APPMEM_END in *; lia|].
          intros i Hi. split.
          - apply Hframeapp. unfold decl_slot. lia.
          - destruct (r18_decl_meta fr i Hframe8 Hi) as (Esh & Hq4).
            replace (decl_slot fr + i) with (fr + 2560 + i) by (unfold decl_slot; lia).
            rewrite Esh. exists (Z_to_bv 8 0).
            split; [|unfold shadow_ok; left; reflexivity].
            assert (E4 : i / 8 = 0 \/ i / 8 = 1 \/ i / 8 = 2 \/ i / 8 = 3) by lia.
            destruct E4 as [->|[->|[->| ->]]].
            + replace (Sfr fr + 320 + 0) with (Sfr fr + 320) by lia. exact (r18_b1_rd mem1 _ _ HZ0).
            + replace (Sfr fr + 320 + 1) with (Sfr fr + 321) by lia. exact (r18_b1_rd mem1 _ _ HZ1).
            + replace (Sfr fr + 320 + 2) with (Sfr fr + 322) by lia. exact (r18_b1_rd mem1 _ _ HZ2).
            + replace (Sfr fr + 320 + 3) with (Sfr fr + 323) by lia. exact (r18_b1_rd mem1 _ _ HZ3). }
    + intros ms' (R & m1 & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P21 & P22 & P23 & P24 & P25 & P26 & P27 &
                  P18 & P10 & MU1 & WM1 & ST1 & MU2 & WM2 & ST2 & HRW & HROWq & HZ0 & HZ1 & HZ2 & HZ3).
      exists R, (Z_to_bv 64 0x818d0), m'. split; [exact Hms|].
      split; [reflexivity|]. exists m1.
      split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
      split; [exact P19|]. split; [exact P21|]. split; [exact P22|]. split; [exact P23|].
      split; [exact P24|]. split; [exact P25|]. split; [exact P26|]. split; [exact P27|].
      split; [exact P18|]. split; [exact P10|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact ST1|].
      split; [exact MU2|]. split; [exact WM2|]. split; [exact ST2|].
      split; [exact HRW|]. split; [exact HROWq|].
      split; [exact HZ0|]. split; [exact HZ1|]. split; [exact HZ2 | exact HZ3].
  - (* the continuation at 0x818d0: rebuild FRA, ENT and the exit cut *)
    intros R pc' mem' regs'' md'
      (Hpc & mem1 & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K27 & K18 & K10 &
       MU1 & WM1 & ST1 & MU2 & WM2 & ST2 & HRW & HROWq & HZ0 & HZ1 & HZ2 & HZ3) Hreg Hmat.
    subst pc'.
    (* phase 1: the four metadata stores *)
    assert (HPres1 : forall qq, Sfr fr + 320 <= qq < Sfr fr + 324 ->
              exists bb, mrd rsegs mem1 (wa qq) = Some bb).
    { intros qq Hq. destruct ST1 as (_ & _ & ST1v). exact (proj2 (ST1v qq Hq)). }
    destruct (r18_sh_move g fr (hb1 phi (rnb g 0)) regs regs mem mem1 md HFRA HENT MU1 WM1 HPres1
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as (HFRA1 & HENT1).
    assert (HRDM1 : rd_mono mem mem1).
    { apply (rd_mono_list [(Sfr fr + 320, Sfr fr + 324)] mem mem1 MU1).
      constructor; [|constructor].
      cbn [fst snd]. intros y Hy.
      destruct ST1 as (_ & _ & ST1v). exact (proj2 (ST1v y ltac:(lia))). }
    (* phase 2: the callee's write set *)
    set (W := [(sp - DECLARATION_OF_K, sp); (decl_slot fr, decl_slot fr + 32)]).
    assert (Hdapp : forall x, decl_slot fr <= x < decl_slot fr + 32 -> app_mem x).
    { intros x Hx. apply Hframeapp. unfold decl_slot in *. lia. }
    assert (HAW : all_app W).
    { unfold W. cbn [all_app app_ivl]. split; [|split; [|exact I]].
      - intros a Ha. exact (Hspapp a Ha).
      - intros a Ha. exact (Hdapp a Ha). }
    assert (HDJ : rt_disjoint W).
    { unfold W, rt_disjoint; cbn [disjoint_from].
      unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
        RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN in *.
      unfold decl_slot, DECLARATION_OF_K, HIGHMEM_BEG in *.
      repeat split; first [ left; lia | right; lia | exact I ]. }
    assert (HRDM2 : rd_mono mem1 mem').
    { apply (rd_mono_list W mem1 mem' MU2).
      unfold W. constructor; [|constructor; [|constructor]].
      - cbn [fst snd]. intros y Hy. destruct ST2 as (_ & _ & ST2v). exact (proj2 (ST2v y ltac:(lia))).
      - cbn [fst snd]. intros y Hy.
        destruct HRW as ((Hwf & HRWb) & _).
        cbn [cells_bytes cbytes] in HRWb. rewrite app_nil_r in HRWb.
        destruct HRWb as (_ & _ & HRWr).
        pose proof (HRWr (Z.to_nat (y - decl_slot fr))
                      ltac:(rewrite (r18_decl_len (g_in g)); lia)) as Hb.
        replace (decl_slot fr + Z.of_nat (Z.to_nat (y - decl_slot fr))) with y in Hb by lia.
        destruct (nth_error (RcDecl.decl (rt_mb (g_in g))) (Z.to_nat (y - decl_slot fr))) as [bb|] eqn:Eb;
          [exists bb; rewrite Hb; first [exact Eb | reflexivity]|].
        apply nth_error_None in Eb. rewrite (r18_decl_len (g_in g)) in Eb. lia. }
    assert (MUa : munch [(ACx.aspZ regs - DECLARATION_OF_K, ACx.aspZ regs); (fr + 2560, fr + 2560 + 32)]
                    mem1 mem').
    { rewrite Haspz. unfold W, decl_slot in MU2. exact MU2. }
    assert (HFRA1b : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs mem1 md) by exact HFRA1.
    pose proof (r18_ah g fr (hb1 phi (rnb g 0)) regs mem1 mem' md HFRA1b MUa WM2 HRDM2)
      as (HAH' & HOWN' & HSTK' & HSHI').
    assert (Hro1 : ro_agree rsegs mem1).
    { destruct HFRA1 as (A1 & sp1 & s51 & _ & _ & Hro1 & _). exact Hro1. }
    assert (Hrokeep : ro_agree rsegs mem').
    { apply (r18_ro_keep mem1 mem' W Hro1 MU2). intros a Hroa.
      pose proof (r18_ro_lt a Hroa) as Hlt. unfold W. cbn [Frame.outside].
      split; [|split; [|exact I]]; unfold decl_slot, DECLARATION_OF_K, HIGHMEM_BEG in *; lia. }
    assert (HWlo : forall x, 0 <= x < 6283264 -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]];
        unfold decl_slot, DECLARATION_OF_K, HIGHMEM_BEG in *; lia. }
    assert (HWhdr : forall x, fr <= x < fr + 24 -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - intro Hc. apply (Hapart x ltac:(lia)). unfold DECLARATION_OF_K in *. lia.
      - unfold decl_slot. lia. }
    assert (HWspill : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 ->
              forall x, A0 + 16 <= x < A0 + 312 -> Frame.outside W x).
    { intros A0 E _ x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - apply (r18_wrap_out A A0 (sp - DECLARATION_OF_K) sp x ltac:(rewrite <- Hr9; exact E));
          unfold DECLARATION_OF_K in *; lia.
      - apply (r18_wrap_out A A0 (decl_slot fr) (decl_slot fr + 32) x ltac:(rewrite <- Hr9; exact E));
          unfold decl_slot in *; lia. }
    assert (HWsaved : forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]];
        unfold decl_slot, DECLARATION_OF_K in *; lia. }
    assert (HWsh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x).
    { intros x Hx.
      assert (Hin : in_shadow x).
      { replace x with (shadow_addr (fr + (x - Sfr fr) * 8)) by (rewrite r18_shadow_off by lia; lia).
        apply shadow_of_app. apply Hframeapp. unfold Sfr in *. lia. }
      unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; intro Hc.
      - exact (AsanRTFacts.app_not_shadow x (Hspapp x Hc) Hin).
      - exact (AsanRTFacts.app_not_shadow x (Hdapp x Hc) Hin). }
    pose proof (eq_trans (Hreg _) K9) as K9'.
    (* the callee's window is above stklo, the FakeStack below it (a_laws_fs_place), and the declaration slot
       is inside the frame body: W meets no FakeStack byte outside the frame body *)
    assert (HWfs : forall FS x, word_mem rsegs mem1 (ACx.as_tp ACx.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
      FS <= x < FS + ACx.FS_SIZE -> ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x).
    { intros FS x Hwtp HFS Hx Hnbody.
      pose proof HFRA1 as HF1. destruct HF1 as (A1 & sp1 & s51 & _ & HAH1 & _).
      pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g 0)) regs mem1 md HFRA1) as (Hlo1 & _).
      pose proof (r18_law_fs_place
                    (hb1 phi (rnb g 0) ++ g_H g) mem1 md FS HAH1 Hwtp HFS) as (_ & HFSstk & _ & _).
      unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; unfold decl_slot in *; lia. }
    assert (HFRAmd : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs'' mem' md).
    { apply (B3FrCl.b3_fr_cl B APIf ra empty FF g fr (hb1 phi (rnb g 0)) regs regs'' mem1 mem' md W HFRA1
        (r18_munch_f _ _ _ MU2) (r18_wmono_f _ _ WM2) Hrokeep HAW HDJ HAH' HSTK' HWlo HWhdr
        (fun A0 E HA0b x Hx => HWspill A0 E HA0b x ltac:(lia))
        (fun A0 E HA0b x Hx => HWspill A0 E HA0b x ltac:(lia))
        HWsaved HWsh HWfs HRDM2);
        (rewrite Hreg; assumption). }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g 0)) regs'' regs'' mem' md md' HFRAmd);
        try reflexivity. exact Hmat. }
    assert (HENT2 : ENT (fx:=fx) APIf g (hb1 phi (rnb g 0)) mem' md).
    { apply (ent_store B APIf ra g fr (hb1 phi (rnb g 0)) regs mem1 mem' md W HENT1 HFRA1
               (r18_munch_f _ _ _ MU2));
        [| exact HSTK' | exact HSHI' |].
      - intros x Hx. unfold W.
        destruct (Z_lt_le_dec x (sp - DECLARATION_OF_K)) as [H1|H1].
        + destruct (Z_lt_le_dec x (decl_slot fr)) as [H3|H3].
          * left. cbn [Frame.outside]. split; [lia|]. split; [unfold decl_slot in *; lia | exact I].
          * destruct (Z_lt_le_dec x (decl_slot fr + 32)) as [H4|H4].
            -- right. right. left. unfold decl_slot in *. lia.
            -- left. cbn [Frame.outside]. split; [lia|]. split; [lia | exact I].
        + destruct (Z_lt_le_dec x sp) as [H2|H2].
          * right. left. unfold AFx.SLOT_STACK, DECLARATION_OF_K in *. lia.
          * destruct (Z_lt_le_dec x (decl_slot fr)) as [H3|H3].
            -- left. cbn [Frame.outside]. split; [lia|]. split; [unfold decl_slot in *; lia | exact I].
            -- destruct (Z_lt_le_dec x (decl_slot fr + 32)) as [H4|H4].
               ++ right. right. left. unfold decl_slot in *. lia.
               ++ left. cbn [Frame.outside]. split; [lia|]. split; [lia | exact I].
      - intros a Himg Ho. exact (proj2 (HOWN' a) Ho). }
    pose proof (ent_mat APIf g (hb1 phi (rnb g 0)) mem' md md' HENT2 Hmat) as HENT'.
    (* the frame slots and the block survive both write sets *)
    assert (HoutF1 : forall x, fr + 2176 <= x < fr + 2560 \/ fr + 2592 <= x < fr + FRAME_BYTES ->
              Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - intro Hc. apply (Hapart x ltac:(lia)). unfold DECLARATION_OF_K in *. lia.
      - unfold decl_slot. lia. }
    assert (HoutS1 : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside [(Sfr fr + 320, Sfr fr + 324)] x).
    { intros x Hx. cbn [Frame.outside]. split; [|exact I].
      pose proof (Hframeapp x Hx) as Happx.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happx.
      unfold Sfr, shadow_addr, ASAN_K in *. lia. }
    assert (Hkeep2 : forall a bs, bytes_at rsegs mem a bs ->
              (forall x, a <= x < a + Z.of_nat (length bs) -> fr + 2176 <= x < fr + 2560 \/
                 fr + 2592 <= x < fr + FRAME_BYTES) ->
              bytes_at rsegs mem' a bs).
    { intros a bs Hb Hr.
      apply (a_keep W mem1 mem' a bs MU2); [intros x Hx; apply HoutF1; exact (Hr x Hx)|].
      apply (a_keep [(Sfr fr + 320, Sfr fr + 324)] mem mem1 a bs MU1);
        [intros x Hx; apply HoutS1; pose proof (Hr x Hx); lia | exact Hb]. }
    assert (HOUR'' : OURb g fr mem').
    { unfold OURb in *. apply Hkeep2; [exact HOUR'|].
      rewrite OUR_length. intros x Hx. right. lia. }
    assert (HIDB'' : IDBr g fr (RID (g_in g) 0) mem').
    { unfold IDBr in *. apply Hkeep2; [exact HIDB|].
      assert (LI : length (RID (g_in g) 0) = 38%nat) by reflexivity.
      rewrite LI. intros x Hx. left. lia. }
    assert (HFGB'' : FGBr g fr (RFG (g_in g) 0) mem').
    { unfold FGBr in *. apply Hkeep2; [exact HFGB|].
      assert (LF : length (RFG (g_in g) 0) = 72%nat) by reflexivity.
      rewrite LF. intros x Hx. left. lia. }
    assert (HoutBlk1 : forall x, phi <= x < phi + rnb g 0 ->
              Frame.outside [(Sfr fr + 320, Sfr fr + 324)] x).
    { intros x Hx. cbn [Frame.outside]. split; [|exact I].
      destruct (Hphibytes x Hx) as (Happx & _).
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happx.
      unfold Sfr, shadow_addr, ASAN_K in *. lia. }
    assert (HoutBlk2 : forall x, phi <= x < phi + rnb g 0 -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - unfold DECLARATION_OF_K in *. lia.
      - unfold decl_slot in *. lia. }
    assert (HF'' : bytes_at rsegs mem' phi (rt_F (g_in g) 0)).
    { apply (a_keep W mem1 mem' phi (rt_F (g_in g) 0) MU2).
      - rewrite HL. intros x Hx. apply HoutBlk2. rewrite Z2Nat.id in Hx by lia. exact Hx.
      - apply (a_keep [(Sfr fr + 320, Sfr fr + 324)] mem mem1 phi (rt_F (g_in g) 0) MU1); [|exact HF].
        rewrite HL. intros x Hx. apply HoutBlk1. rewrite Z2Nat.id in Hx by lia. exact Hx. }
    assert (H23'' : rg regs'' 23 (Z.of_nat 0))
      by (unfold rg in *; exact (eq_trans (Hreg _) (eq_trans K23 H23'))).
    assert (HCUR'' : CUR g 7 regs'').
    { destruct HCUR' as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split.
      - exact (eq_trans (Hreg _) (eq_trans K22 Hc22)).
      - exact (eq_trans (Hreg _) (eq_trans K25 Hc25)). }
    assert (H24'' : rg regs'' 24 phi)
      by (unfold rg in *; exact (eq_trans (Hreg _) (eq_trans K24 H24))).
    assert (HRFb'' : RFb g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs'' mem').
    { split.
      { split; [exact Hb6'|]. split; [exact HCUR''|]. split; [exact HOUR''|]. split; [exact H23''|].
        split; [exact HIDB'' | exact HFGB'']. }
      split; [exact Hnz|]. split; [exact H24'' | exact HF'']. }
    (* the heap block stays addressable *)
    assert (Hsz : ACx.a_size (rnb g 0) = rnb g 0) by (unfold ACx.a_size; lia).
    destruct HHB as (Hphinz & HAphi). rewrite Hsz in HAphi.
    assert (HHB' : HB mem' phi (rnb g 0)).
    { split; [exact Hphinz|]. rewrite Hsz.
      apply (sl_addr_keep mem1 mem' W phi (rnb g 0));
        [| exact (r18_munch_f _ _ _ MU2) | exact HAW].
      apply (r18_addr_keep_rng mem mem1 _ phi (rnb g 0) HAphi MU1).
      intros i Hi. cbn [Frame.outside]. split; [|exact I].
      destruct (Hphibytes (phi + i) ltac:(lia)) as (Happx & _).
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happx.
      unfold Sfr, shadow_addr, ASAN_K in *. revert Happx. Z.div_mod_to_equations. lia. }
    (* the identity record stays addressable *)
    assert (HAid'' : addressable mem' (fr + 2176) 38).
    { apply (sl_addr_keep mem1 mem' W (fr + 2176) 38);
        [| exact (r18_munch_f _ _ _ MU2) | exact HAW].
      apply (r18_addr_keep_rng mem mem1 _ (fr + 2176) 38 HAid MU1).
      intros i Hi. cbn [Frame.outside]. split; [|exact I].
      replace (shadow_addr (fr + 2176 + i)) with (Sfr fr + 272 + i / 8)
        by (unfold Sfr, shadow_addr; revert Hframe8 Hi; Z.div_mod_to_equations; lia).
      assert (0 <= i / 8 < 5) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
    (* our[]'s 6 bytes stay addressable: their shadow byte S(fr) + 328 is not one of S(fr) + 320 .. + 323 *)
    assert (HA6k : addressable mem (fr + 2624) 6 -> addressable mem' (fr + 2624) 6).
    { intros HAour. apply (sl_addr_keep mem1 mem' W (fr + 2624) 6);
        [| exact (r18_munch_f _ _ _ MU2) | exact HAW].
      apply (r18_addr_keep_rng mem mem1 _ (fr + 2624) 6 HAour MU1).
      intros i Hi. cbn [Frame.outside]. split; [|exact I].
      replace (shadow_addr (fr + 2624 + i)) with (Sfr fr + 328 + i / 8)
        by (unfold Sfr, shadow_addr; revert Hframe8 Hi; Z.div_mod_to_equations; lia).
      assert (0 <= i / 8 < 1) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
    (* PRO's input block: a live block of the entry heap (a_laws_blocks), so application memory below stklo (so
       below the callee's window) and apart from the frame (on the real arm the frame is at or above stklo, on the
       side arm it is in the side stack, which no block byte is); so it misses both write sets, and its shadow
       bytes miss the four stores' S(fr) + 320 .. + 323 (the shadow bytes of frame bytes) *)
    assert (INB : In (g_p g, g_n g) (g_H g) -> forall x, g_p g <= x < g_p g + g_n g ->
              app_mem x /\ x < sp - DECLARATION_OF_K /\ ~ (fr <= x < fr + FRAME_BYTES)).
    { intros Hin x Hx.
      destruct (r18_law_blocks
                  (hb1 phi (rnb g 0) ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hpend & _ & Hpb).
      destruct (Hpb x Hx) as (Happx & _ & _ & _ & Hnfsx).
      assert (Hstkle : ACx.aa_stklo ACx.ASYMS AsanRTInv.RT (APIf rc) mem md <= g_S g - AFx.SLOT_STACK)
        by exact Hstklo.
      split; [exact Happx|]. split; [lia|].
      intros Hxf. destruct Hloc as [(H0' & Hspfr & Hreal)|(Hfr0' & HfsbS & Hfs & _)].
      - pose proof (Hreal x Hxf). lia.
      - exact (Hnfsx (Hfs x Hxf)). }
    assert (HINk : (0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
              bytes_at rsegs mem (g_p g) (g_in g) -> bytes_at rsegs mem' (g_p g) (g_in g)).
    { intros Hin HIN.
      apply (a_keep W mem1 mem' (g_p g) (g_in g) MU2).
      - intros x Hx. rewrite <- g_n_len in Hx.
        destruct (INB (Hin ltac:(lia)) x Hx) as (_ & Hxw & Hxfr).
        unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; unfold decl_slot in *; lia.
      - apply (a_keep [(Sfr fr + 320, Sfr fr + 324)] mem mem1 (g_p g) (g_in g) MU1); [|exact HIN].
        intros x Hx. rewrite <- g_n_len in Hx.
        destruct (INB (Hin ltac:(lia)) x Hx) as (Happx & _ & _).
        cbn [Frame.outside]. split; [|exact I].
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happx.
        unfold Sfr, shadow_addr, ASAN_K in *. lia. }
    assert (HINAk : In (g_p g, g_n g) (g_H g) ->
              addressable mem (g_p g) (g_n g) -> addressable mem' (g_p g) (g_n g)).
    { intros Hin HA.
      apply (sl_addr_keep mem1 mem' W (g_p g) (g_n g)); [| exact (r18_munch_f _ _ _ MU2) | exact HAW].
      apply (r18_addr_keep_rng mem mem1 _ (g_p g) (g_n g) HA MU1).
      intros i Hi. cbn [Frame.outside]. split; [|exact I].
      destruct (INB Hin (g_p g + i) ltac:(lia)) as (_ & _ & Hxfr).
      unfold Sfr, shadow_addr. revert Hframe8 Hxfr. Z.div_mod_to_equations. lia. }
    (* out[] stays addressable: its shadow bytes S(fr) + 68 .. + 254 are not the four stores' S(fr) + 320 ..
       + 323, and the callee's write set is app memory *)
    assert (HOUTA'' : OUTA fr mem').
    { unfold OUTA in *. apply (sl_addr_keep mem1 mem' W (fr + 544) 1492);
        [| exact (r18_munch_f _ _ _ MU2) | exact HAW].
      apply (r18_addr_keep_rng mem mem1 _ (fr + 544) 1492 HOUTA MU1).
      intros i Hi. cbn [Frame.outside]. split; [|exact I].
      replace (shadow_addr (fr + 544 + i)) with (Sfr fr + 68 + i / 8)
        by (unfold Sfr, shadow_addr; revert Hframe8 Hi; Z.div_mod_to_equations; lia).
      assert (0 <= i / 8 < 187) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
    (* the declaration slot is marked usable, and holds the declaration *)
    assert (HADecl : addressable mem' (decl_slot fr) 32).
    { split; [unfold decl_slot; lia|]. split; [lia|].
      split; [unfold decl_slot, APPMEM_END in *; lia|].
      intros i Hi. split.
      - apply Hframeapp. unfold decl_slot. lia.
      - destruct (r18_decl_meta fr i Hframe8 Hi) as (Esh & Hq4).
        replace (decl_slot fr + i) with (fr + 2560 + i) by (unfold decl_slot; lia).
        rewrite Esh. exists (Z_to_bv 8 0).
        split; [|unfold shadow_ok; left; reflexivity].
        assert (E4 : i / 8 = 0 \/ i / 8 = 1 \/ i / 8 = 2 \/ i / 8 = 3) by lia.
        destruct E4 as [->|[->|[->| ->]]].
        + replace (Sfr fr + 320 + 0) with (Sfr fr + 320) by lia. exact (r18_b1_rd mem' _ _ HZ0).
        + replace (Sfr fr + 320 + 1) with (Sfr fr + 321) by lia. exact (r18_b1_rd mem' _ _ HZ1).
        + replace (Sfr fr + 320 + 2) with (Sfr fr + 322) by lia. exact (r18_b1_rd mem' _ _ HZ2).
        + replace (Sfr fr + 320 + 3) with (Sfr fr + 323) by lia. exact (r18_b1_rd mem' _ _ HZ3). }
    assert (HDeclB : bytes_at rsegs mem' (decl_slot fr) (RcDecl.decl (rt_mb (g_in g)))).
    { destruct HRW as ((Hwf & HRWb) & _). cbn [cells_bytes cbytes] in HRWb.
      rewrite app_nil_r in HRWb. exact HRWb. }
    (* the spills the exit cut carries *)
    assert (Hspk : forall off v, 0 <= off -> off + 8 <= 312 -> spill regs mem off v ->
              spill regs'' mem' off v).
    { intros off v Ho1 Ho2 HS.
      assert (HS1 : spill regs mem1 off v).
      { apply (r18_spill_keep regs regs mem mem1 off v A [(Sfr fr + 320, Sfr fr + 324)] HS Hr9 eq_refl
                 HA0 ltac:(lia) ltac:(lia) MU1).
        intros x Hx. cbn [outside]. split; [|exact I]. unfold HIGHMEM_BEG in *. lia. }
      apply (r18_spill_keep regs regs'' mem1 mem' off v A W HS1 Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU2).
      intros x Hx. unfold W. cbn [outside]. split; [|split; [|exact I]];
        unfold decl_slot, DECLARATION_OF_K in *; lia. }
    (* the carried spills: no instruction of the segment and no byte the callee writes is in [A + 0, A + 312),
       so each passes through unchanged; the frame cells fr + 2688 (38 bytes), fr + 2768 (72), fr + 3040 (1) and
       fr + 3056 (32) are frame bytes above the declaration slot, off both write sets *)
    assert (Hrwk : forall a n bs, fr + 2592 <= a -> a + Z.of_nat n <= fr + FRAME_BYTES ->
              rw_cells rsegs mem a [CB n bs] -> rw_cells rsegs mem' a [CB n bs]).
    { intros a n bs Ha1 Ha2 HRWa.
      apply (r18_rwcb_keep W mem1 mem' a n bs MU2 WM2); [intros x Hx; apply HoutF1; lia|].
      apply (r18_rwcb_keep [(Sfr fr + 320, Sfr fr + 324)] mem mem1 a n bs MU1 WM1);
        [intros x Hx; apply HoutS1; lia | exact HRWa]. }
    (* rebuild the exit cut *)
    rewrite <- SEGS. apply Hexit. exists phi, 1, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split.
    { split; [exact Hgn|]. split; [exact HRFb''|]. split; [exact HOUTA''|].
      split; [unfold rg in *; exact (eq_trans (Hreg _) K10)|].
      split; [lia|].
      split; [unfold rg in *; exact (eq_trans (Hreg _) (eq_trans K27 H27))|].
      split; [unfold rg in *; exact (eq_trans (Hreg _) K18)|].
      exact HDeclB. }
    split; [reflexivity|].
    split; [exact HHB'|].
    split; [lia|].
    split; [exact (r18_decl_len (g_in g))|].
    split; [exact HADecl|].
    split; [exact (Hspk 128 (fr + 544) ltac:(lia) ltac:(lia) Hsp128)|].
    split.
    { apply (r18_pro_keep g fr regs regs'' mem mem'
               (fun xoff xv Ho H => Hspk xoff xv ltac:(lia) ltac:(lia) H));
        [exact HA6k | exact HINk | exact HINAk | exact HPRO]. }
    split; [exact (Hspk 104 0x21140 ltac:(lia) ltac:(lia) Hsp104)|].
    split; [exact (Hspk 96 0x1234 ltac:(lia) ltac:(lia) Hsp96)|].
    split; [exact (Hspk 64 0xe38f0000 ltac:(lia) ltac:(lia) Hsp64)|].
    split; [unfold rg in *; exact (eq_trans (Hreg _) (eq_trans K21 H21))|].
    split; [exact (Hspk 112 (mrow (g_in g)) ltac:(lia) ltac:(lia) Hsp112)|].
    split; [exact (Hspk 144 (fr + 2688) ltac:(lia) ltac:(lia) Hsp144)|].
    split; [exact (Hspk 192 (fr + 2768) ltac:(lia) ltac:(lia) Hsp208)|].
    split.
    { destruct HRWid as (idb & HRWi). exists idb.
      exact (Hrwk (fr + 2688) 38%nat idb ltac:(lia) ltac:(lia) HRWi). }
    split.
    { destruct HRWjk as (junk & HRWj). exists junk.
      exact (Hrwk (fr + 2768) 72%nat junk ltac:(lia) ltac:(lia) HRWj). }
    split; [exact (Hspk 280 (fr + 3040) ltac:(lia) ltac:(lia) Hsp280)|].
    split; [exact (Hspk 240 (fr + 3056) ltac:(lia) ltac:(lia) Hsp240)|].
    split.
    { destruct HRWjy as (jy & HRWy). exists jy.
      exact (Hrwk (fr + 3040) 1%nat jy ltac:(lia) ltac:(lia) HRWy). }
    split.
    { destruct HRWsc as (junk & HRWs). exists junk.
      exact (Hrwk (fr + 3056) 32%nat junk ltac:(lia) ltac:(lia) HRWs). }
    split; [exact (Hspk 152 (Sfr fr + 68) ltac:(lia) ltac:(lia) Hsp152)|].
    split; [exact HAid''|].
    (* RXS (push 10): the spills by Hspk; the fragment record's shadow bytes S(fr) + 282 .. + 290 are not the four
       stores' S(fr) + 320 .. + 323, and the callee's write set is application memory *)
    apply (r18_rxs_keep g fr regs regs'' mem mem' (fun xoff xv Ho H => Hspk xoff xv ltac:(lia) ltac:(lia) H));
      [|exact HRXS].
    intros HA72. apply (sl_addr_keep mem1 mem' W (fr + 2256) 72); [| exact (r18_munch_f _ _ _ MU2) | exact HAW].
    apply (r18_addr_keep_rng mem mem1 _ (fr + 2256) 72 HA72 MU1).
    intros i Hi. cbn [Frame.outside]. split; [|exact I].
    replace (shadow_addr (fr + 2256 + i)) with (Sfr fr + 282 + i / 8)
      by (unfold Sfr, shadow_addr; revert Hframe8 Hi; Z.div_mod_to_equations; lia).
    assert (0 <= i / 8 < 9) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

End R18W.
