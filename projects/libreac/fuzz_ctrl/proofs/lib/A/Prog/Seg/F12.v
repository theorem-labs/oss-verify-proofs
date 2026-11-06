(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths, module names and numbers changed; 1486 of its 1528 lines of code are new or changed and 354 lines of the source are left out. *)
(* Segment F12 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A), plan-asan 2 row F12: the block
   0x820f8-0x82134, which ends in the 72-byte copy `jal checked_memcpy@0x82134`.

   0x820f8 `bltz a0` (a0 = the result of the reac_identity_ingest call at 0x820f4) is NOT taken: the entry cut
   Inv_A820f8_at carries 0 <= a0 < 2^63, so the abort pair at 0x82bf4 is not reached.  0x820fc spills s9 to [s1+152].
   0x82100-0x82120 write the byte 0 to the nine metadata bytes s3+42 .. s3+50 (s3 = S(fr) = shadow_addr fr, FRA);
   they are the metadata bytes of the 72 frame bytes [fr+336, fr+408), so after them that range is a usable
   (addressable) range.  0x82124-0x82130 load a2 = 72, a0 = [s1+184] = fr+336 (the destination), s9 = a1 =
   [s1+192] = fr+2768 = fragb fr (the source), and 0x82134 calls checked_memcpy (__asan_memcpy, 0x52028), whose
   lib/A contract asan_memcpy_c.v is a Section Hypothesis here.  The segment ends at the return point 0x82138.

   Cuts.  The official texts of lib/A/Prog/SlotInv.v: the entries Inv_A820fc_at (F10's exit, both frame arms) and
   Inv_A820f8_at (F11's exit), the exit Inv_A82138_at (F13's entry).  f12_run is the run from 0x820fc under the
   part f12_P of the two entry bodies that the segment needs, on the official shell b5_CUT; f12_entry1 drops ir,
   f12_entry2 steps the bltz.  The run writes f12_W: the spill [A+152, A+160), the nine metadata bytes, the copy
   [fr+336, fr+408) and the memcpy window [sp-2224, sp).  The memcpy contract asks for mem_inv, which no cut
   carries: the call runs on MemNorm.normalize of the memory (evt_normalize from FRA's ro_agree; the premises and
   the post cross mem_rel by lib/A/RoAdapt.v).  FRA moves across f12_W by f12_fr_run (Seg/F4.v's f4_fr_run with the
   spill premise narrowed to [A+16, A+32) and [A+304, A+312) and the frame's new shadow list) and sl_fra_move, ENT
   by ent_store / ent_mat; the heap law by a_laws_store (real arm) or a_fs_ok_store_AH (side arm).  The exit's
   F17CARRY field `spill regs m 152 (b2z (t_tfill j))` is the segment's own store at 0x820fc (s9 is b5_K's);
   every other exit conjunct is carried from the entry (FLSI, LK, b5_C, b5_K, b5_RC, IDb1, b5_F17, b5_W240, b5_PF,
   across f12_W) or made by the segment (the copy at fr + 336, s9 = fragb fr); F17CARRY's rec_inv0 is assembled
   from b5_PF's long-frame group, b5_F17, b5_SPILL's [A+248], b5_K's [A+280] and b5_PH, its rec_parse is b5_PF's.
   On the s5 = 0 (real-stack) arm sp = fr; on the s5 = fr (side-stack) arm the frame is FakeStack slot jj of class
   6.  Every fact of the exit cut is proved for both arms. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue RoAdapt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcReply RcDeclLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib
  asan_memcpy_c bcmp_wrap_c memcmp_c reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
(* Tac_b5 states sl_run_lib with the UL copy of the machine-state constructor; the Lib step engine matches the
   Lib one.  They are convertible; f12_lib_ms turns the run's state into the form the step engine matches. *)
Module UM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.
Ltac f12_lib_ms :=
  match goal with
  | |- ?E ?sg ?Q (UM.MS ?a ?b ?c ?d ?e ?f ?g) => change (E sg Q (MS a b c d e f g))
  end.

(* The segment keeps the memory of the ten stores explicit (the write chain), so that munch / mem_inv / the byte
   facts are rebuilt by the write-frame lemmas at the end; the automatic cell bookkeeping is therefore switched
   off (the same override as lib/Prog/reac_ctrl_identity_fragment.v). *)
Local Ltac mem_after_store_opt ::= idtac.

(* ---- small arithmetic / memory helpers (all local, f12_-prefixed) ---- *)

Lemma f12_getr_reg : forall (R : bvmap 5 word) (r : bv 5), bv_eqb r 0 = false -> Sem.reg_get R r = getr R r.
Proof. intros R r H. unfold getr. rewrite H. reflexivity. Qed.

(* store_ok only reads wview, which a write never removes. *)
Lemma f12_sok_write : forall (m : word -> option byte) (c : word) (bs : list byte) (a : word) (n : nat),
  store_ok rsegs m a n = true -> store_ok rsegs (write_to_mem m c bs) a n = true.
Proof.
  intros m c bs a n. revert a. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [store_ok] in *. destruct (wview rsegs m a) eqn:E; [|discriminate].
  destruct (wview rsegs (write_to_mem m c bs) a) eqn:E2.
  - apply IH. exact H.
  - exfalso. apply (wview_write_mono rsegs m c bs a); [rewrite E; discriminate | exact E2].
Qed.

Lemma f12_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by lia. exact HH.
Qed.

(* Route (C) twin: the write reads no shadow byte, so no region premise; every region P present before is present after. *)
Lemma f12_shadow_rw_write_on : forall (m : word -> option byte) (a : Z) (bs : list byte),
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  forall P, SRO.shadow_rw_on P m -> SRO.shadow_rw_on P (write_to_mem m (wa a) bs).
Proof.
  intros m a bs Ha Hl P H x Hp Hx. destruct (H x Hp Hx) as (Hw & b & Hb).
  pose proof (in_shadow_range _ Hx) as (Hx1 & Hx2).
  split; [apply wview_write_mono; exact Hw|].
  unfold mrd in *. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb];
    try (eexists; exact Hb).
  destruct (nth_error bs (Z.to_nat (x - a))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

Lemma f12_shadow_rw_write : forall (m : word -> option byte) (a : Z) (bs : list byte),
  shadow_rw m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> shadow_rw (write_to_mem m (wa a) bs).
Proof.
  intros m a bs H Ha Hl. exact (SRO.shadow_rw_of_on_all _ (f12_shadow_rw_write_on m a bs Ha Hl _ (SRO.shadow_rw_on_of_shadow_rw _ m H))).
Qed.

(* A readable+writable interval yields a byte list of any length inside it. *)
Lemma f12_bytes_of_stk : forall (m : word -> option byte) (a : Z) (k : nat) (lo hi : Z),
  stk rsegs m lo hi -> lo <= a -> a + Z.of_nat k <= hi ->
  exists bs, length bs = k /\ bytes_at rsegs m a bs.
Proof.
  intros m a k. revert a. induction k as [|k IH]; intros a lo hi HS Hlo Hhi.
  - exists []. split; [reflexivity|]. pose proof HS as (Hl0 & Hh0 & _). split; [lia|]. split; [cbn; lia|].
    intros i Hi; cbn in Hi; lia.
  - pose proof HS as (Hl0 & Hh0 & Hb).
    destruct (Hb a ltac:(lia)) as (_ & b & Hbb).
    destruct (IH (a + 1) lo hi HS ltac:(lia) ltac:(lia)) as (bs & Hlen & Hbs).
    exists (b :: bs). split; [cbn; lia|].
    replace (b :: bs) with ([b] ++ bs) by reflexivity.
    apply bytes_at_app. split.
    + split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
      destruct i as [|i]; [|lia]. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Hbb.
    + cbn [length Z.of_nat]. exact Hbs.
Qed.

Lemma f12_wr_of_stk : forall (m : word -> option byte) (a n lo hi : Z),
  stk rsegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at rsegs m a n.
Proof.
  intros m a n lo hi (Hl0 & Hh0 & Hb) Hlo Hn Hhi. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Hb (a + i) ltac:(lia)) as (Hw & _). exact Hw.
Qed.

Lemma f12_wrsub : forall (m : word -> option byte) (a n k n' b : Z),
  wr_at rsegs m a n -> 0 <= k -> 0 <= n' -> k + n' <= n -> b = a + k -> wr_at rsegs m b n'.
Proof. intros m a n k n' b H Hk Hn Hkn ->. exact (wr_at_sub m a n k n' H Hk Hn Hkn). Qed.

Lemma f12_stk_rwb : forall (m : word -> option byte) (a : Z) (k : nat) (lo hi : Z),
  stk rsegs m lo hi -> lo <= a -> a + Z.of_nat k <= hi ->
  exists bs, length bs = k /\ rw_cells rsegs m a [CB k bs].
Proof.
  intros m a k lo hi HS Hlo Hhi.
  destruct (f12_bytes_of_stk m a k lo hi HS Hlo Hhi) as (bs & Hlen & Hbs).
  exists bs. split; [exact Hlen|]. split.
  - split; [cbn; split; [exact Hlen | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hbs.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
    apply (f12_wr_of_stk m a (Z.of_nat k) lo hi HS Hlo ltac:(lia) ltac:(lia)).
Qed.

Lemma f12_rw_of_bytes : forall (m : word -> option byte) (a : Z) (bs : list byte) (n : nat),
  bytes_at rsegs m a bs -> length bs = n -> wr_at rsegs m a (Z.of_nat n) -> rw_cells rsegs m a [CB n bs].
Proof.
  intros m a bs n Hb Hl Hw. split.
  - split; [cbn; split; [exact Hl | exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma f12_q64_rw : forall (m : word -> option byte) (a v : Z),
  q64 m a v -> wr_at rsegs m a 8 -> rw_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m a v Hq Hw. split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hq.
  - cbn [cells_size csize Nat.add]. exact Hw.
Qed.

Lemma f12_q64_rw3 : forall (m : word -> option byte) (a v1 v2 v3 : Z),
  q64 m a v1 -> q64 m (a + 8) v2 -> q64 m (a + 16) v3 -> wr_at rsegs m a 24 ->
  rw_cells rsegs m a [C8 (Z_to_bv 64 v1); C8 (Z_to_bv 64 v2); C8 (Z_to_bv 64 v3)].
Proof.
  intros m a v1 v2 v3 H1 H2 H3 Hw. split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_app. split; [exact H1|]. rewrite length_le8. change (Z.of_nat 8) with 8.
    apply bytes_at_app. split; [exact H2|]. rewrite length_le8. change (Z.of_nat 8) with 8.
    replace (a + 8 + 8) with (a + 16) by lia. exact H3.
  - cbn [cells_size csize Nat.add]. exact Hw.
Qed.

(* Route (C) twin: the shadow bytes read are [lo, hi). *)
Definition f12_shadow_stk_shadow_R (lo hi : Z) : Z -> Prop := fun a => lo <= a < hi.

Lemma f12_shadow_stk_on : forall (m : word -> option byte) (lo hi : Z),
  SRO.shadow_rw_on (f12_shadow_stk_shadow_R lo hi) m -> (forall a, lo <= a < hi -> in_shadow a) -> 0 <= lo ->
  hi <= 2 ^ 64 -> stk rsegs m lo hi.
Proof.
  intros m lo hi HS Hin Hlo Hhi. split; [lia|]. split; [lia|].
  intros a Ha. destruct (HS a Ha (Hin a Ha)) as (Hw & b & Hb). split; [exact Hw | exists b; exact Hb].
Qed.

(* The metadata interval of the frame is a readable+writable interval (RT's shadow_rw). *)
Lemma f12_shadow_stk : forall (m : word -> option byte) (lo hi : Z),
  shadow_rw m -> (forall a, lo <= a < hi -> in_shadow a) -> 0 <= lo -> hi <= 2 ^ 64 -> stk rsegs m lo hi.
Proof.
  intros m lo hi HS Hin Hlo Hhi. exact (f12_shadow_stk_on m lo hi (SRO.shadow_rw_on_of_shadow_rw _ m HS) Hin Hlo Hhi).
Qed.

(* The metadata byte of fr + j, for an 8-aligned frame base. *)
Lemma f12_sh_fr : forall fr j, fr mod 8 = 0 -> 0 <= j -> shadow_addr (fr + j) = Sfr fr + j / 8.
Proof.
  intros fr j H8 Hj. unfold shadow_addr, Sfr, AsanRT.shadow_addr.
  replace fr with (8 * (fr / 8)) at 1 by (Z.div_mod_to_equations; lia).
  rewrite Z.mul_comm, Z.div_add_l by lia. lia.
Qed.

Lemma f12_in_shadow_fr : forall fr a,
  (forall x, fr <= x < fr + FRAME_BYTES -> app_mem x) -> fr mod 8 = 0 -> Sfr fr <= a < Sfr fr + FRAME_SHADOW -> in_shadow a.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros fr a Happ H8 Ha.
  assert (Hx : fr <= fr + 8 * (a - Sfr fr) < fr + FRAME_BYTES) by lia.
  pose proof (shadow_of_app (fr + 8 * (a - Sfr fr)) (Happ _ Hx)) as His.
  rewrite (f12_sh_fr fr (8 * (a - Sfr fr)) H8 ltac:(lia)) in His.
  replace (8 * (a - Sfr fr) / 8) with (a - Sfr fr) in His
    by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  replace (Sfr fr + (a - Sfr fr)) with a in His by lia. exact His.
Qed.

(* A metadata byte outside the written frame range stays outside the written metadata range. *)
Lemma f12_sh_out_fr : forall fr x k1 k2, fr mod 8 = 0 -> 0 <= fr -> 0 <= x ->
  ~ (fr + 8 * k1 <= x < fr + 8 * k2) -> ~ (Sfr fr + k1 <= shadow_addr x < Sfr fr + k2).
Proof.
  intros fr x k1 k2 H8 Hfr Hx Hout Hin. apply Hout.
  unfold Sfr, shadow_addr, AsanRT.shadow_addr in Hin. Z.div_mod_to_equations. lia.
Qed.

(* addressable survives a run whose writes miss the metadata bytes of the range. *)
Lemma f12_addr_munch : forall (m m' : word -> option byte) (W : list ivl) (p n : Z),
  addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros m m' W p n (H1 & H2 & H3 & H) MU Hout. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Happ) as His.
  pose proof (in_shadow_range _ His) as (Hr1 & Hr2).
  unfold mrd. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. exact (Hout i Hi).
Qed.

(* The nine metadata bytes 0 at Sfr fr + 42 .. + 50 make the 72 frame bytes [fr+336, fr+408) a usable range. *)
Lemma f12_addr_of_zero9 : forall (m : word -> option byte) (fr : Z),
  fr mod 8 = 0 -> (forall x, fr <= x < fr + FRAME_BYTES -> app_mem x) -> 0 <= fr ->
  (forall k, 0 <= k < 9 -> exists b, mrd rsegs m (wa (Sfr fr + 42 + k)) = Some b /\ bv_signed b = 0) ->
  addressable m (fr + 336) 72.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros m fr H8 Happ Hfr0 Hz.
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in *. destruct Ha as [Ha|Ha]; lia. }
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Happ; lia|].
  assert (E : shadow_addr (fr + 336 + i) = Sfr fr + 42 + i / 8).
  { replace (fr + 336 + i) with (fr + (336 + i)) by lia.
    rewrite (f12_sh_fr fr (336 + i) H8 ltac:(lia)).
    replace (336 + i) with (i + 42 * 8) by lia. rewrite Z.div_add by lia. lia. }
  destruct (Hz (i / 8) ltac:(Z.div_mod_to_equations; lia)) as (b & Hb & Hs).
  exists b. rewrite E. split; [exact Hb|]. unfold shadow_ok. left. exact Hs.
Qed.

Lemma f12_mrd_of_bytes : forall (m : word -> option byte) (a : Z) (b : byte),
  bytes_at rsegs m a [b] -> mrd rsegs m (wa a) = Some b.
Proof.
  intros m a b (H1 & H2 & H). pose proof (H 0%nat ltac:(cbn; lia)) as HH.
  cbn [Z.of_nat nth_error] in HH. rewrite Z.add_0_r in HH. exact HH.
Qed.

(* An addressable block lies entirely in the low or entirely in the high app range. *)
Lemma f12_app_block : forall m p n, addressable m p n -> 0 < n -> p + n <= LOWMEM_END \/ HIGHMEM_BEG <= p.
Proof.
  intros m p n (H1 & H2 & H3 & H) Hn.
  destruct (H 0 ltac:(lia)) as (Hp & _). rewrite Z.add_0_r in Hp.
  destruct Hp as [Hlow|Hhigh]; [|right; lia]. left.
  destruct (Z_le_dec (p + n) LOWMEM_END) as [Hle|Hgt]; [exact Hle|exfalso].
  destruct (H (LOWMEM_END - p) ltac:(lia)) as (Hb & _).
  replace (p + (LOWMEM_END - p)) with LOWMEM_END in Hb by lia.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG in *. destruct Hb as [Hb|Hb]; lia.
Qed.

(* A metadata address lies between the end of the low app range and the start of the high app range. *)
Lemma f12_sh_lt : forall x, in_shadow x -> LOWMEM_END <= x /\ x < HIGHMEM_BEG.
Proof.
  intros x H. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
Qed.

(* Two intervals that share no point are ordered. *)
Lemma f12_ivl_dj : forall a1 b1 a2 b2, a1 < b1 -> a2 < b2 ->
  (forall x, a1 <= x < b1 -> a2 <= x < b2 -> False) -> b1 <= a2 \/ b2 <= a1.
Proof.
  intros a1 b1 a2 b2 H1 H2 H.
  destruct (Z_le_dec b1 a2) as [Hle|Hgt]; [left; exact Hle|].
  destruct (Z_le_dec b2 a1) as [Hle2|Hgt2]; [right; exact Hle2|].
  exfalso. apply (H (Z.max a1 a2)); lia.
Qed.

(* The two runtime function words and the two control bytes the exit cut carries, from RT. *)
Lemma f12_real_bcmp : forall m, asan_real_cells m -> bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
Proof.
  intros m H. exact (AsanRTInv.real_cell_of m REAL_BCMP BCMP H ltac:(vm_compute; reflexivity)).
Qed.

Lemma f12_real_memcmp : forall m, asan_real_cells m -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
Proof.
  intros m H. exact (AsanRTInv.real_cell_of m REAL_MEMCMP MEMCMP H ltac:(vm_compute; reflexivity)).
Qed.

Lemma f12_got_cf : forall m, asan_cf_cells m -> bytes_at rsegs m GOT_CF (le8 (wa CF)).
Proof. intros m (H & _). exact H. Qed.

Lemma f12_cf_254 : forall m, asan_cf_cells m -> bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
Proof.
  intros m (_ & _ & _ & _ & _ & _ & H & _).
  pose proof (rc_bytes_sub rsegs m (RT_CF + 240)
                (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0]) 14 1 H
                ltac:(cbn; lia)) as HS.
  cbn [cf_b map firstn skipn] in HS.
  replace (CF + 254) with (RT_CF + 240 + Z.of_nat 14) by (unfold CF, RT_CF; cbn; lia).
  exact HS.
Qed.

Lemma f12_cf_255 : forall m, asan_cf_cells m -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Proof.
  intros m (_ & _ & _ & _ & _ & _ & H & _).
  pose proof (rc_bytes_sub rsegs m (RT_CF + 240)
                (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0]) 15 1 H
                ltac:(cbn; lia)) as HS.
  cbn [cf_b map firstn skipn] in HS.
  replace (CF + 255) with (RT_CF + 240 + Z.of_nat 15) by (unfold CF, RT_CF; cbn; lia).
  exact HS.
Qed.

(* ---- tactics of the run: the store_ok of the current memory, a carried 8-byte read, write-frame chains ---- *)

(* mkR_of as the Lib register record the Lib step engine reduces (F10's copy builds the UL one). *)
Lemma f12_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a known register slot to its carried value (F10's f10_subst_slot is section-local there). *)
Ltac f12_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

Ltac f12_sok H :=
  let T := type of H in
  match T with
  | store_ok ?sg _ ?a ?n = true =>
    match goal with
    | |- context [MS _ _ _ _ _ ?mm (seg_rom _)] =>
        let N := fresh "SOKc" in
        assert (N : store_ok sg mm a n = true) by (repeat apply f12_sok_write; exact H)
    end
  end.

Lemma f12_signed : forall v, 0 <= v < 2 ^ 63 -> bv_signed (Z_to_bv 64 v) = v.
Proof.
  intros v Hv. unfold bv_signed, bv_swrap. rewrite MState.unsigned_lit by lia.
  change (bv_half_modulus 64) with (2 ^ 63). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia.
Qed.

(* ---- model lengths and list facts the exit's record bundles need ---- *)

(* The identity record of every turn has ID_SIZE = 38 bytes: ID0 has, and the two ingest steps of a turn (rp_id on
   the reply arm, fg_id on a closed fragment) keep the length (RcIdentModel.ING_length). *)
Lemma f12_rpid_len : forall idb len g, length idb = RcIdentModel.ID_SIZE ->
  length (rp_id idb len g) = RcIdentModel.ID_SIZE.
Proof.
  intros idb len g H. unfold rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end;
    [apply RcIdentModel.ING_length; exact H | exact H].
Qed.

Lemma f12_fgid_len : forall idb len st g, length idb = RcIdentModel.ID_SIZE ->
  length (fg_id idb len st g) = RcIdentModel.ID_SIZE.
Proof.
  intros idb len st g H. unfold fg_id.
  match goal with |- context [if ?c then _ else _] => destruct c end;
    [apply RcIdentModel.ING_length; exact H | exact H].
Qed.

Lemma f12_tID_len : forall inp j, length (t_ID inp j) = RcIdentModel.ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  cbn [fst_at]. unfold turn. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end; cbn [fs_id];
    apply f12_fgid_len, f12_rpid_len; exact IH.
Qed.

Lemma f12_ID1_len : forall g j, length (ID1 g j) = 38%nat.
Proof. intros g j. unfold ID1. rewrite f12_rpid_len; [reflexivity | apply f12_tID_len]. Qed.

(* The frame body at phi has at most t_len bytes; a bsl slice at most its width. *)
Lemma f12_phi_len : forall inp j, Z.of_nat (length (t_phi inp j)) <= Z.max 0 (t_len inp j).
Proof. intros inp j. unfold t_phi, t_len, f_phi. rewrite length_firstn. lia. Qed.

Lemma f12_bsl_len : forall bs k n, 0 <= n -> Z.of_nat (length (RcFrag.bsl bs k n)) <= n.
Proof. intros bs k n Hn. unfold RcFrag.bsl. rewrite length_firstn. lia. Qed.

Lemma f12_bytes_first : forall m a bs k, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof. intros m a bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. exact (proj1 H). Qed.

(* A memcmp of n bytes reads only the first n bytes of each side. *)
Lemma f12_mcmp_firstn : forall n l r,
  SFA.memcmp_model (firstn n l) (firstn n r) n = SFA.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r]; cbn; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

(* A byte of a carried list is present. *)
Lemma f12_bytes_mrd : forall m a bs q, bytes_at rsegs m a bs -> a <= q < a + Z.of_nat (length bs) ->
  exists b, mbyte rsegs m q = Some b.
Proof.
  intros m a bs q (_ & _ & H) Hq.
  pose proof (H (Z.to_nat (q - a)) ltac:(lia)) as Hn.
  rewrite Z2Nat.id in Hn by lia. replace (a + (q - a)) with q in Hn by lia.
  destruct (nth_error bs (Z.to_nat (q - a))) as [b|] eqn:E; [exists b; exact Hn|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* A readable+writable interval stays one across a run, when each of its bytes is outside the run's writes or
   present afterwards. *)
Lemma f12_stk_after : forall W m m' lo hi, stk rsegs m lo hi -> Frame.munch W m m' -> Frame.wmono rsegs m m' ->
  (forall x, lo <= x < hi -> Frame.outside W x \/ exists b, mbyte rsegs m' x = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HW. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb). split; [exact (WM _ Hv)|].
  destruct (HW a Ha) as [Ho|(b' & Hb')]; [|exists b'; exact Hb'].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* Every registered global lies in the image, below AC.GT (Seg/F4.v's f4_ag_lt). *)
Definition f12_ag_ok : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? AC.GT)) AF.frame_AG.

Lemma f12_ag_true : f12_ag_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f12_ag_lt : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & n & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) f12_ag_true (lo, n) Hin) as H.
  apply andb_prop in H as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2. cbn in H1, H2. lia.
Qed.

(* ---- transports of the carried facts across a run with write set W and a register change ---- *)

Lemma f12_q64_mv : forall W m m' a v, q64 m a v -> Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> Frame.outside W x) -> q64 m' a v.
Proof.
  intros W m m' a v H MU HW. unfold q64 in *. eapply fl_bytes; [exact H | exact MU |].
  rewrite length_le8. exact HW.
Qed.

Lemma f12_A_eq : forall regs A A', rg regs 9 A -> 0 <= A < 2 ^ 64 -> rg regs 9 A' -> 0 <= A' < 2 ^ 64 -> A' = A.
Proof.
  intros regs A A' H HA H' HA'. pose proof (rg_eq64 regs 9 A' A H' H) as Hm.
  rewrite !Z.mod_small in Hm by lia. exact Hm.
Qed.

(* A spill word (the exists-A form) at the canonical spill base A. *)
Lemma f12_spill_q64 : forall regs m A off v, rg regs 9 A -> 0 <= A < 2 ^ 64 -> 0 <= off <= 400 ->
  A + 416 <= 2 ^ 64 -> spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HA Hoff HA416 (A' & HA' & Hq).
  assert (E : A' = A).
  { pose proof Hq as Hb. unfold q64 in Hb. destruct Hb as (Hb0 & Hb1 & _).
    rewrite length_le8 in Hb1. change (Z.of_nat 8) with 8 in Hb1.
    pose proof (rg_eq64 regs 9 A' A HA' H9) as Hm.
    rewrite (Z.mod_small A) in Hm by lia.
    assert (HA'0 : 0 <= A').
    { destruct (Z_le_gt_dec 0 A') as [Hp|Hneg]; [exact Hp|exfalso].
      assert (HmA : A' mod 2 ^ 64 = A' + 2 ^ 64)
        by (rewrite <- (Z.mod_add A' 1 (2 ^ 64)) by lia; rewrite Z.mod_small; lia).
      rewrite HmA in Hm. lia. }
    rewrite (Z.mod_small A') in Hm by lia. exact Hm. }
  subst A'. exact Hq.
Qed.

(* The harness input block (f1_IN and PRO's input pair) across a run that misses its bytes and their shadow. *)
Lemma f12_inb_mv : forall g m m' W, Frame.munch W m m' ->
  (0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g ->
     Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  bytes_at rsegs m (g_p g) (g_in g) -> bytes_at rsegs m' (g_p g) (g_in g).
Proof.
  intros g m m' W MU HW Hb.
  destruct (Z_lt_le_dec 0 (g_n g)) as [Hn|Hn].
  - eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. rewrite <- g_n_len in Hx. exact (proj1 (HW Hn x Hx)).
  - assert (Hl : length (g_in g) = 0%nat) by (rewrite g_n_len in Hn; lia).
    destruct Hb as (H1 & H2 & _). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite Hl in Hi. lia.
Qed.

Lemma f12_inad_mv : forall g m m' W, Frame.munch W m m' ->
  (0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g ->
     Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  addressable m (g_p g) (g_n g) -> addressable m' (g_p g) (g_n g).
Proof.
  intros g m m' W MU HW Had.
  destruct (Z_lt_le_dec 0 (g_n g)) as [Hn|Hn].
  - apply (f12_addr_munch m m' W (g_p g) (g_n g) Had MU). intros i Hi.
    exact (proj2 (HW Hn (g_p g + i) ltac:(lia))).
  - destruct Had as (H1 & H2 & H3 & _). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
    intros i Hi. lia.
Qed.

Lemma f12_IN_mv : forall g m m' W, Frame.munch W m m' ->
  (0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g ->
     Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  f1_IN g m -> f1_IN g m'.
Proof.
  intros g m m' W MU HW (H1 & H2 & H3). split; [exact H1|].
  split; [exact (f12_inad_mv g m m' W MU HW H2) | exact (f12_inb_mv g m m' W MU HW H3)].
Qed.

(* v1.9: the first fragment's body (fs_body, the bytes FSb names at fr + 2880) is empty or a prefix of a 50-byte
   frame from byte 27 on, so it has at most 23 bytes. *)
Lemma f12_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  assert (Hg : length (t_g inp j) = 50%nat) by (unfold t_g; apply fr50_length).
  rewrite length_firstn, length_skipn, Hg. apply Nat.le_min_r.
Qed.

(* FLSI across a run that writes none of its spills (they are at A + 32 .. A + 280, apart from [A+152, A+160)),
   none of the metadata bytes of our[] (fr + 2624), of the 17 bytes at fr + 2691, of the fragment record
   (fragb fr) and of the identity record (fr + 2688), and neither the input block nor its metadata; the frame's stk
   fact is the caller's (fra_stk at the new state). *)
Lemma f12_FLSI_mv : forall g j fr regs regs' m m' W A,
  rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 -> Frame.munch W m m' ->
  (forall x, A + 32 <= x < A + 288 -> (x < A + 152 \/ A + 160 <= x) -> Frame.outside W x) ->
  (forall i, 0 <= i < 6 -> Frame.outside W (shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < 17 -> Frame.outside W (shadow_addr (fr + 2691 + i))) ->
  (forall i, 0 <= i < 72 -> Frame.outside W (shadow_addr (fragb fr + i))) ->
  (forall i, 0 <= i < 38 -> Frame.outside W (shadow_addr (fr + 2688 + i))) ->
  (0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g ->
     Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  stk rsegs m' fr (fr + FRAME_BYTES) ->
  FLSI g j fr regs m -> FLSI g j fr regs' m'.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g j fr regs regs' m m' W A H9 HA HA416 E9 MU HWsp HW6 HW17 HW72 HW38 HWin Hstk'
    (((H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248' & Had6 & Hin & Hblk & P184 & P256 & P264 & P272 &
       P32) &
      H128 & _ & H144 & Had17) &
     H216 & H224 & H248 & HIN &
     (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cad72 & Cad38 & C72 & C64 & C56 & C48)).
  assert (SP : forall off v, 32 <= off <= 280 -> (off + 8 <= 152 \/ 160 <= off) ->
            spill regs m off v -> spill regs' m' off v).
  { intros off v Hoff Hoff2 Hs. exists A. split; [unfold rg in *; rewrite E9; exact H9|].
    apply (f12_q64_mv W m m' (A + off) v (f12_spill_q64 regs m A off v H9 HA ltac:(lia) HA416 Hs) MU).
    intros x Hx. apply HWsp; lia. }
  split.
  { split.
    { split; [exact (SP 40 _ ltac:(lia) ltac:(lia) H40)|].
      split; [exact (SP 120 _ ltac:(lia) ltac:(lia) H120)|].
      split; [exact (SP 136 _ ltac:(lia) ltac:(lia) H136)|].
      split; [exact (SP 160 _ ltac:(lia) ltac:(lia) H160)|].
      split; [exact (SP 168 _ ltac:(lia) ltac:(lia) H168)|].
      split; [exact (SP 176 _ ltac:(lia) ltac:(lia) H176)|].
      split; [exact (SP 208 _ ltac:(lia) ltac:(lia) H208)|].
      split; [exact (SP 248 _ ltac:(lia) ltac:(lia) H248')|].
      split; [exact (f12_addr_munch m m' W (fr + 2624) 6 Had6 MU HW6)|].
      split; [exact (f12_inb_mv g m m' W MU HWin Hin)|].
      split.
      { intros Hn. destruct (Hblk Hn) as (Hi & Ha). split; [exact Hi | exact (f12_inad_mv g m m' W MU HWin Ha)]. }
      split; [exact (SP 184 _ ltac:(lia) ltac:(lia) P184)|].
      split; [exact (SP 256 _ ltac:(lia) ltac:(lia) P256)|].
      split; [exact (SP 264 _ ltac:(lia) ltac:(lia) P264)|].
      split; [exact (SP 272 _ ltac:(lia) ltac:(lia) P272) | exact (SP 32 _ ltac:(lia) ltac:(lia) P32)]. }
    split; [exact (SP 128 _ ltac:(lia) ltac:(lia) H128)|].
    split; [exact Hstk'|].
    split; [exact (SP 144 _ ltac:(lia) ltac:(lia) H144)|].
    exact (f12_addr_munch m m' W (fr + 2691) 17 Had17 MU HW17). }
  split; [exact (SP 216 _ ltac:(lia) ltac:(lia) H216)|].
  split; [exact (SP 224 _ ltac:(lia) ltac:(lia) H224)|].
  split; [exact (SP 248 _ ltac:(lia) ltac:(lia) H248)|].
  split; [exact (f12_IN_mv g m m' W MU HWin HIN)|].
  split; [exact (SP 256 _ ltac:(lia) ltac:(lia) C256)|].
  split; [exact (SP 184 _ ltac:(lia) ltac:(lia) C184)|].
  split; [exact (SP 192 _ ltac:(lia) ltac:(lia) C192)|].
  split; [exact (SP 80 _ ltac:(lia) ltac:(lia) C80)|].
  split; [exact (SP 88 _ ltac:(lia) ltac:(lia) C88)|].
  split; [exact (SP 96 _ ltac:(lia) ltac:(lia) C96)|].
  split; [exact (SP 272 _ ltac:(lia) ltac:(lia) C272)|].
  split; [exact (SP 264 _ ltac:(lia) ltac:(lia) C264)|].
  split; [exact (f12_addr_munch m m' W (fragb fr) 72 Cad72 MU HW72)|].
  split; [exact (f12_addr_munch m m' W (fr + 2688) 38 Cad38 MU HW38)|].
  split; [exact (SP 72 _ ltac:(lia) ltac:(lia) C72)|].
  split; [exact (SP 64 _ ltac:(lia) ltac:(lia) C64)|].
  split; [exact (SP 56 _ ltac:(lia) ltac:(lia) C56) | exact (SP 48 _ ltac:(lia) ltac:(lia) C48)].
Qed.

Lemma f12_LK_mv : forall g j fr regs regs' m m' W, getr regs' 21 = getr regs 21 -> Frame.munch W m m' ->
  (forall x, fr + 2624 <= x < fr + 2630 -> Frame.outside W x) -> LK g fr j regs m -> LK g fr j regs' m'.
Proof.
  intros g j fr regs regs' m m' W E21 MU HW (Hj & H21 & HOUR).
  split; [exact Hj|]. split; [unfold rg in *; rewrite E21; exact H21|].
  unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length. intros x Hx. apply HW. lia.
Qed.

(* A sub-slice of a carried byte list. *)
Lemma f12_bytes_bsl : forall m a bs k n, bytes_at rsegs m a bs -> 0 <= k -> 0 <= n ->
  k + n <= Z.of_nat (length bs) -> bytes_at rsegs m (a + k) (RcFrag.bsl bs k n).
Proof.
  intros m a bs k n H Hk Hn Hkn. unfold RcFrag.bsl.
  rewrite <- (firstn_skipn (Z.to_nat k) bs) in H. apply bytes_at_app in H. destruct H as (_ & H).
  rewrite length_firstn in H.
  replace (a + Z.of_nat (Nat.min (Z.to_nat k) (length bs))) with (a + k) in H by lia.
  exact (f12_bytes_first m (a + k) _ (Z.to_nat n) H).
Qed.

(* rec_parse (the parse-made part of rec_inv) across a run that misses the record's bytes 14 .. 17 and their
   metadata and the u16 at fr + 196. *)
Lemma f12_parse_mv : forall g j fr phi m m' W,
  Frame.munch W m m' ->
  (forall x, phi + 14 <= x < phi + 18 -> Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  (forall x, fr + 196 <= x < fr + 198 -> Frame.outside W x) ->
  rec_parse g j fr phi m -> rec_parse g j fr phi m'.
Proof.
  intros g j fr phi m m' W MU HWb HWu
    (f16 & v14 & v15 & v16 & v17 & Hu16 & Hb14 & Hb15 & Hb16 & Hb17 & R14 & R15 & R16 & R17 &
     S14 & S15 & S16 & S17 & Hf16 & Hk).
  assert (Hsh : forall k, 0 <= k -> Z.shiftr (phi + k) 3 + ASAN_K = shadow_addr (phi + k)).
  { intros k Hk0. unfold shadow_addr. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  assert (B1 : forall k v, 14 <= k <= 17 -> b8 m (phi + k) v -> b8 m' (phi + k) v).
  { intros k v Hk0 Hb. unfold b8 in *. eapply fl_bytes; [exact Hb | exact MU |]. cbn [length].
    intros x Hx. exact (proj1 (HWb x ltac:(lia))). }
  assert (BS : forall k, 14 <= k <= 17 -> b8 m (Z.shiftr (phi + k) 3 + ASAN_K) 0 ->
            b8 m' (Z.shiftr (phi + k) 3 + ASAN_K) 0).
  { intros k Hk0 Hb. rewrite (Hsh k) in Hb by lia. rewrite (Hsh k) by lia. unfold b8 in *.
    eapply fl_bytes; [exact Hb | exact MU |]. cbn [length]. intros x Hx.
    replace x with (shadow_addr (phi + k)) by lia. exact (proj2 (HWb (phi + k) ltac:(lia))). }
  exists f16, v14, v15, v16, v17.
  split.
  { unfold u16 in *. eapply fl_bytes; [exact Hu16 | exact MU |]. rewrite length_le2.
    intros x Hx. apply HWu. lia. }
  split; [apply B1; [lia | exact Hb14]|].
  split; [apply B1; [lia | exact Hb15]|].
  split; [apply B1; [lia | exact Hb16]|].
  split; [apply B1; [lia | exact Hb17]|].
  split; [exact R14|]. split; [exact R15|]. split; [exact R16|]. split; [exact R17|].
  split; [apply BS; [lia | exact S14]|].
  split; [apply BS; [lia | exact S15]|].
  split; [apply BS; [lia | exact S16]|].
  split; [apply BS; [lia | exact S17]|].
  split; [exact Hf16 | exact Hk].
Qed.

(* ---- the segment's write set and the part of the two entry bodies the run reads ---- *)

(* The spill [A+152, A+160) (0x820fc), the nine metadata bytes S(fr)+42 .. S(fr)+50 (0x82100-0x82120), the copy
   [fr+336, fr+408) and the memcpy window [sp - ASAN_MEMCPY_K, sp) (ASAN_MEMCPY_K = 2224). *)
Definition f12_W (A fr sp : Z) : list (Z * Z) :=
  [(A + 152, A + 160); (Sfr fr + 42, Sfr fr + 51); (fr + 336, fr + 408); (sp - 2224, sp)].

(* The conjuncts of the bodies of Inv_A820fc_at and Inv_A820f8_at that both share (the first drops ir = false,
   the second the length bound and a0). *)
Definition f12_P (g : ghost) (j : nat) (phi fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  b5_K g j phi fr regs m /\ b5_RC fr m /\ IDb1 g fr j m /\
  b5_F17 g j phi fr regs m /\ b5_W240 g j regs m /\ b5_PF g j phi fr regs m.

(* The b5_CUT body of f12_P moves across a register change that keeps the registers it reads. *)
Lemma f12_body_regs : forall g j phi fr regs regs' m,
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 ->
  getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 ->
  FLSI g j fr regs m -> LK g fr j regs m -> b5_C g j phi fr regs m -> f12_P g j phi fr regs m ->
  FLSI g j fr regs' m /\ LK g fr j regs' m /\ b5_C g j phi fr regs' m /\ f12_P g j phi fr regs' m.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g j phi fr regs regs' m E2 E9 E18 E20 E21 E22 E23 E24 E25 HF HL HC HP.
  assert (R9 : forall (P : Z -> Prop), (exists A, rg regs 9 A /\ P A) -> exists A, rg regs' 9 A /\ P A).
  { intros P (A & HA & HPA). exists A. split; [unfold rg in *; rewrite E9; exact HA | exact HPA]. }
  assert (Rr : forall r v, getr regs' r = getr regs r -> rg regs r v -> rg regs' r v).
  { intros r v E Hr. unfold rg in *. rewrite E. exact Hr. }
  assert (RS : forall off v, spill regs m off v -> spill regs' m off v) by (intros off v Hs; exact (R9 _ Hs)).
  assert (RFS : FSj g fr j regs m -> FSj g fr j regs' m).
  { intros (H1 & H2 & H3 & H4 & H5). split; [exact (RS _ _ H1)|]. split; [exact (RS _ _ H2)|].
    split; [exact H3|]. split; [exact H4 | exact H5]. }
  split.
  { destruct HF as ((HP0 & H128 & Hstk & H144 & Had) & H216 & H224 & H248 & HIN &
      (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cad72 & Cad38 & C72 & C64 & C56 & C48)).
    destruct HP0 as (H40 & H120 & H136 & H160 & H168 & H176 & H208 & H248' & Had6 & Hin & Hblk &
      P184 & P256 & P264 & P272 & P32).
    split.
    - split.
      + split; [exact (RS _ _ H40)|]. split; [exact (RS _ _ H120)|]. split; [exact (RS _ _ H136)|].
        split; [exact (RS _ _ H160)|]. split; [exact (RS _ _ H168)|]. split; [exact (RS _ _ H176)|].
        split; [exact (RS _ _ H208)|]. split; [exact (RS _ _ H248')|]. split; [exact Had6|].
        split; [exact Hin|]. split; [exact Hblk|].
        split; [exact (RS _ _ P184)|]. split; [exact (RS _ _ P256)|].
        split; [exact (RS _ _ P264)|]. split; [exact (RS _ _ P272) | exact (RS _ _ P32)].
      + split; [exact (RS _ _ H128)|]. split; [exact Hstk|]. split; [exact (RS _ _ H144) | exact Had].
    - split; [exact (RS _ _ H216)|]. split; [exact (RS _ _ H224)|]. split; [exact (RS _ _ H248)|].
      split; [exact HIN|].
      split; [exact (RS _ _ C256)|]. split; [exact (RS _ _ C184)|]. split; [exact (RS _ _ C192)|].
      split; [exact (RS _ _ C80)|]. split; [exact (RS _ _ C88)|]. split; [exact (RS _ _ C96)|].
      split; [exact (RS _ _ C272)|]. split; [exact (RS _ _ C264)|]. split; [exact Cad72|].
      split; [exact Cad38|]. split; [exact (RS _ _ C72)|]. split; [exact (RS _ _ C64)|].
      split; [exact (RS _ _ C56) | exact (RS _ _ C48)]. }
  split.
  { destruct HL as (Hj & H21 & HOUR). split; [exact Hj|]. split; [exact (Rr _ _ E21 H21) | exact HOUR]. }
  split.
  { destruct HC as (Hs7 & Hr18 & HCA & HPH & HFR & HFS & HKN & HFG & HFSj).
    split; [exact (Rr _ _ E23 Hs7)|]. split; [exact (Rr _ _ E18 Hr18)|].
    split; [exact (R9 _ HCA)|].
    split.
    { destruct HPH as (P1 & P2 & P3). split; [exact P1|]. split; [|exact P3].
      unfold AC.aspZ. rewrite E2. exact P2. }
    split; [exact HFR|]. split; [exact HFS|]. split; [exact HKN|]. split; [exact HFG | exact (RFS HFSj)]. }
  destruct HP as (HK & HRC & HID & H17 & H240 & HPF).
  split.
  { destruct HK as (K20 & K22 & K24 & K25 & K280 & K176 & Kargs).
    split; [exact (Rr _ _ E20 K20)|]. split; [exact (Rr _ _ E22 K22)|]. split; [exact (Rr _ _ E24 K24)|].
    split; [exact (Rr _ _ E25 K25)|]. split; [exact (R9 _ K280)|]. split; [exact K176 | exact Kargs]. }
  split; [exact HRC|]. split; [exact HID|].
  split; [exact (R9 _ H17)|]. split; [exact (R9 _ H240) | exact (R9 _ HPF)].
Qed.

(* ---- tactics of the run's write chain ---- *)

(* A disjointness side condition: linear, or by one of the carried placement disjunctions. *)
Ltac f12_dj :=
  (try unfold ASAN_MEMCPY_K); (try unfold AF.SLOT_STACK); (try unfold REAC_CTRL_IDENTITY_FRAGMENT_K);
  (try unfold BCMP_WRAP_K); (try unfold fragb);
  first [ left; lia | right; lia
        | multimatch goal with
          | H : _ \/ _ |- _ => destruct H as [Hq|Hq]; first [left; lia | right; lia]
          end
        | match goal with |- ?G => idtac "F12DJ-FAIL:" G end; fail ].
Ltac f12_nl :=
  try unfold fragb in *;
  rewrite ?length_le8, ?length_le1;
  repeat match goal with H : length ?l = _ |- context [length ?l] => rewrite H end;
  cbn [length Z.of_nat cells_size csize Nat.add].
Ltac f12_len := f12_nl; lia.
Ltac f12_djl := f12_nl; f12_dj.
(* A carried 8-byte word read through the write chain. *)
Ltac f12_rd H a v :=
  match goal with
  | |- context [MS _ _ _ _ _ ?mm (seg_rom _)] =>
      let N := fresh "RDc" in
      assert (N : ov_read_bytes rsegs mm (wa a) 8 = Some (le8 (Z_to_bv 64 v))) by
        (apply f12_rd8; [ repeat (apply bytes_at_write_other; [ | lia | f12_len | f12_djl ]);
                          exact H | apply length_le8 ])
  end.
(* A metadata byte 0 written by one of the nine stores. *)
Ltac f12_zb :=
  eexists; split;
  [ apply f12_mrd_of_bytes;
    repeat first [ apply bytes_at_write_same; cbn [length Z.of_nat]; lia
                 | apply bytes_at_write_other; [ | lia | f12_len | f12_djl ] ]
  | vm_compute; reflexivity ].

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The lib/A contract of checked_memcpy (A/Prog/asan_memcpy_c.v), a Section Hypothesis. *)
Hypothesis HMCPY : asan_memcpy_contract.

(* ---------------- the generated laws and frame_facts, each taken apart once ----------------
   a Theorem Labs lane's rule for its generated laws (append-only at every nesting level; generation N+1 brings named
   sub-projections): this file takes each law's /\ list apart in ONE lemma below (an f12_law_ lemma), which returns
   only the facts the file uses, and every site uses that lemma. No pattern names a binder of a law's list: the list
   is split by decompose, and f12_law_fact closes each returned fact by its type, directly or (a fact under a binder)
   from the split instance of the hypothesis under the same binder. A conjunct that a later generation appends, at
   any level, is left unused. *)
Ltac f12_law_fact :=
  first [ assumption
        | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          match goal with P : forall _, _ -> _ |- _ =>
            let Q := fresh "Q" in pose proof (P x Hx) as Q; decompose [and] Q;
            repeat match goal with |- _ /\ _ => apply conj end; assumption
          end ].
Ltac f12_law_close := repeat match goal with |- _ /\ _ => apply conj end; f12_law_fact.

Lemma f12_law_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a) /\ (forall a, p <= a < p + n -> ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH HIn.
  pose proof (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ _ _ HAH HIn) as L.
  decompose [and] L. f12_law_close.
Qed.

Lemma f12_law_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hagree Hwm.
  pose proof (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ _ HAH Hagree Hwm) as L.
  decompose [and] L. f12_law_close.
Qed.

Lemma f12_law_fs_place : forall H mem md b,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Htp Hb.
  pose proof (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ _ HAH Htp Hb) as L.
  decompose [and] L. f12_law_close.
Qed.

(* frame_facts (a Theorem Labs lane's, SlotInv.v), taken apart once: the image's segments and the three sink-cell addresses. *)
Lemma f12_ff : ms_segs B = rsegs /\ @sk_ofl_head SH = 0x5fbf08 /\ @sk_ofl_lock SK = 0x5fbf00 /\
  @sk_threaded SK = 0x5fbaa0 + 1.
Proof.
  destruct FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  exact (conj SEGS (conj Hhead (conj Hlock Hthr))).
Qed.

(* The FRA rebuild across a run that writes shadow bytes (the frame's own, given back as the new 392-byte list),
   the frame body, the spill band apart from [A+16, A+32) and [A+304, A+312), and a stack window: Seg/F4.v's
   f4_fr_run with those two premises changed. RT by RT_meta_write; AH / stklo, the S-anchored window, FSREC, the
   registered globals and the window's addressability from the caller; the rest kept by fl_bytes (their
   addresses are outside W) and wmono (errno). *)
Lemma f12_fr_run : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (forall x, 0 <= x < AC.GT -> Frame.outside W x) ->
  (forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 ->
     forall x, (A + 16 <= x < A + 32) \/ (A + 304 <= x < A + 312) -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  FRA B APIf ra g fr hb regs mem' md.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros g fr hb regs mem mem' md W HFRA MU WM HRO HD HSH HAH' HSTK HWhdr HWimg HWA9 HWsaved Hshnew HWwin
    HrecK HAG' HWA'.
  pose proof f12_ff as (SEGS & Hhead & Hlock & Hthr).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. apply HWimg. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HSH)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
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
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split; [|exact (HrecK Hrec)].
        intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact HWwin|].
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
  split; [exact Hhb | exact Hlive].
Qed.

(* ---- the run 0x820fc -> 0x82138: the ten stores, the two loads and the memcpy, to F13's entry cut ---- *)
Lemma f12_run : forall j, Hat B APIf ra (Inv_A82138_at B APIf ra) j ->
  Hat B APIf ra (fun g j c => b5_CUT B APIf ra g 0x820fc j (f12_P g j) c) j.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros j Hexit g c HInv.
  pose proof f12_ff as (SEGS & _).
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HC & HP).
  subst c. rewrite SEGS.
  destruct HP as (HbK & HbRC & HID & HF17 & HW240 & HPF).
  pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hapart & _ & _ & _).
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Hfrapp).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A0 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof HC as (Hs7 & Hr18 & (A & H9 & HA64 & HSPILL & Hq232) & HbPH & HbFR & HbFS & HbKN & HFGj & HFSj).
  pose proof HSPILL as (Hq248 & Hq256 & Hq144 & Hq184 & Hq192 & Hq80 & Hq88 & Hq96 & Hq272 & Hq264).
  pose proof HbFR as (HfgA & HidA & HFGb & HFGl).
  pose proof HbK as (Hs4 & Hs6 & Hs8 & Hs9 & Hsp280 & Hu176 & Hargs).
  pose proof HbRC as (HADpa & HADpp & HADpn).
  pose proof HHB as (Hphinz & HADphi).
  pose proof HFLSI as ((HPRO & _ & Hfrstk & _ & _) & _ & _ & _ & (HinH & _ & _) & _).
  pose proof HPRO as (_ & S120 & S136 & _ & _ & S176 & _ & _ & _ & _ & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhi.
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HFN : FN_STACK = 1044480) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HGTv : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HFSv : AC.FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HKm : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (Hsp0 : 0 <= sp < 2 ^ 64).
  { rewrite <- Haspz. unfold AC.aspZ.
    pose proof (bv_unsigned_in_range 64 (getr regs 2)) as HR. unfold bv_modulus in HR. cbn in HR. lia. }
  assert (HA0b : 0 <= A0 < 2 ^ 64) by lia.
  pose proof (f12_A_eq regs A A0 H9 HA64 Hr9 HA0b) as EA0. subst A0.
  rewrite Haspz in Hwlo, Hwstk.
  assert (Hfrw2 : fr + FRAME_BYTES <= sp - 2224 \/ sp <= fr).
  { destruct (Hapart 2224 ltac:(lia)) as [Hd|Hd]; rewrite Haspz in Hd; [left|right]; lia. }
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (HSPu : bv_unsigned (Z_to_bv 64 sp) = sp) by (apply MState.unsigned_lit; lia).
  assert (HspA : sp <= APPMEM_END) by lia.
  assert (HCk : 0 < LOWMEM_END /\ LOWMEM_END < LOWSHADOW_END /\ LOWSHADOW_END < HIGHSHADOW_BEG /\
               HIGHSHADOW_BEG < HIGHMEM_BEG /\ HIGHMEM_BEG < APPMEM_END /\ APPMEM_END <= 2 ^ 64 /\
               AC.GT + 1048576 < HIGHMEM_BEG /\ RT_HI < AC.GT /\ 0 < AC.GT /\
               RT_LO < RT_HI /\ RT_HI < LOWMEM_END /\ 0 < RT_LO /\
               0 < REAL_BCMP /\ REAL_BCMP + 8 < LOWMEM_END /\
               0 < REAL_MEMCMP /\ REAL_MEMCMP + 8 < LOWMEM_END /\
               0 < GOT_CF /\ GOT_CF + 8 < LOWMEM_END /\ 0 < CF /\ CF + 256 < LOWMEM_END /\
               REAL_BCMP + 8 < AC.GT /\ REAL_MEMCMP + 8 < AC.GT /\ GOT_CF + 8 < AC.GT /\ CF + 256 < AC.GT)
    by (unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END, AC.GT, RT_HI, RT_LO,
          REAL_BCMP, REAL_MEMCMP, GOT_CF, CF; lia).
  destruct HCk as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & HC7 & HC8 & HC9 & HC10 & HC11 & HC12 &
                   HC13 & HC14 & HC15 & HC16 & HC17 & HC18 & HC19 & HC20 &
                   HC21 & HC22 & HC23 & HC24).
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfrub : fr + FRAME_BYTES <= APPMEM_END) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (HshIS : forall a, Sfr fr <= a < Sfr fr + FRAME_SHADOW -> in_shadow a)
    by (intros a Ha; exact (f12_in_shadow_fr fr a Hfrapp Hfr8 Ha)).
  assert (HSHlo : LOWMEM_END <= Sfr fr)
    by (destruct (f12_sh_lt (Sfr fr) (HshIS (Sfr fr) ltac:(lia))) as (Hi1 & Hi2); lia).
  assert (HSHhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG)
    by (destruct (f12_sh_lt (Sfr fr + FRAME_SHADOW - 1) (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia))) as (Hi1 & Hi2); lia).
  (* the frame lies wholly above or wholly below its metadata range (it is app memory, low or high) *)
  assert (Harm : fr + FRAME_BYTES <= Sfr fr \/ Sfr fr + FRAME_SHADOW <= fr).
  { pose proof (Hfrapp fr ltac:(lia)) as Ha. pose proof (Hfrapp (fr + FRAME_BYTES - 1) ltac:(lia)) as Hb.
    clear - Ha Hb HFBval HFSval. unfold Sfr, shadow_addr, ASAN_K, app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
    destruct Ha as [Hlow|Hhigh]; [left|right]; destruct Hb as [Hb|Hb]; Z.div_mod_to_equations; lia. }
  pose proof (AsanRTInv.RT_cells sp mem md HRT) as HAC.
  pose proof (AsanRTInv.RT_shadow_rw sp mem md HRT) as HSW.
  pose proof HRT as (_ & _ & _ & HCF & _ & HREAL & _).
  assert (Hshstk : stk rsegs mem (Sfr fr) (Sfr fr + FRAME_SHADOW))
    by (apply (f12_shadow_stk mem (Sfr fr) (Sfr fr + FRAME_SHADOW) HSW HshIS); lia).
  (* the spill band [A + 64, A + 288) inside the S-anchored window *)
  assert (Hstksp : stk rsegs mem (A + 64) (A + 288)).
  { destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) (A + 64) (g_S g) Hwin ltac:(lia)) as (_ & HS1).
    destruct (stk_split rsegs mem (A + 64) (A + 288) (g_S g) HS1 ltac:(lia)) as (HS2 & _). exact HS2. }
  assert (Hwrsp : wr_at rsegs mem (A + 64) 224)
    by (apply (f12_wr_of_stk mem (A + 64) 224 (A + 64) (A + 288) Hstksp); lia).
  assert (Hwrsh : wr_at rsegs mem (Sfr fr) FRAME_SHADOW)
    by (apply (f12_wr_of_stk mem (Sfr fr) FRAME_SHADOW (Sfr fr) (Sfr fr + FRAME_SHADOW) Hshstk); lia).
  assert (Hwrfr : wr_at rsegs mem fr FRAME_BYTES)
    by (apply (f12_wr_of_stk mem fr FRAME_BYTES fr (fr + FRAME_BYTES) Hfrstk); lia).
  (* every live block (the record block, the input block) is app memory below stklo and apart from the frame *)
  assert (Hblk : forall q k x, In (q, k) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) -> q <= x < q + k ->
            app_mem x /\ x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\ ~ (fr <= x < fr + FRAME_BYTES)).
  { intros q k x Hin Hx.
    destruct (f12_law_blocks _ mem md q k HAH Hin) as (Hqs & Hqapp & Hqnfs).
    pose proof (Hqapp x Hx) as Hxa. pose proof (Hqnfs x Hx) as Hnfs.
    split; [exact Hxa|]. split; [lia|]. intros Hfx.
    destruct Hloc as [(_ & _ & Hreal)|(_ & _ & HinFS & _)].
    - destruct (Hreal x Hfx) as (Hlo & _). lia.
    - exact (Hnfs (HinFS x Hfx)). }
  assert (Hinphi : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (cbn [hb1 app In]; left; reflexivity).
  destruct Hsp280 as (A280 & H9280 & HA280 & Hq280).
  pose proof (f12_A_eq regs A A280 H9 HA64 H9280 HA280) as E280. subst A280.
  set (st := t_FG (g_in g) j) in *.
  destruct (f12_stk_rwb mem (fr + 336) 72 fr (fr + FRAME_BYTES) Hfrstk ltac:(lia) ltac:(cbn [Z.of_nat]; lia))
    as (junk & Hjl & Hjrw).
  assert (B152 : store_ok rsegs mem (wa (A + 152)) 8%nat = true).
  { replace (A + 152) with (A + 64 + 88) by lia.
    apply (wr_at_store_ok rsegs mem (A + 64) 224 88 8%nat Hwrsp ltac:(lia) ltac:(cbn; lia)). }
  assert (B42 : store_ok rsegs mem (wa (Sfr fr + 42)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 42 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B43 : store_ok rsegs mem (wa (Sfr fr + 43)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 43 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B44 : store_ok rsegs mem (wa (Sfr fr + 44)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 44 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B45 : store_ok rsegs mem (wa (Sfr fr + 45)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 45 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B46 : store_ok rsegs mem (wa (Sfr fr + 46)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 46 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B47 : store_ok rsegs mem (wa (Sfr fr + 47)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 47 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B48 : store_ok rsegs mem (wa (Sfr fr + 48)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 48 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B49 : store_ok rsegs mem (wa (Sfr fr + 49)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 49 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  assert (B50 : store_ok rsegs mem (wa (Sfr fr + 50)) 1%nat = true)
    by (apply (wr_at_store_ok rsegs mem (Sfr fr) FRAME_SHADOW 50 1%nat Hwrsh ltac:(lia) ltac:(cbn; lia))).
  apply (sl_run_lib regs (Z_to_bv 64 0x820fc) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x82138 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 25 = Z_to_bv 64 (fragb fr) /\ getr R 26 = getr regs 26 /\
       munch (f12_W A fr sp) mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (sp - FN_STACK) sp /\ q64 mem' (A + 152) (b2z (t_tfill (g_in g) j)) /\
       rw_cells rsegs mem' (fr + 336) [CB 72 st] /\ bytes_at rsegs mem' (fragb fr) st /\
       addressable mem' (fr + 336) 72 /\ asan_cells mem' /\ shadow_rw mem')
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f12_mkR_of_expand.
    f12_subst_slot H9. rewrite Hr2. f12_subst_slot Hr19.
    try f12_lib_ms.
    f12_sok B152. step.
    f12_sok B46. step.
    f12_sok B47. step.
    f12_sok B48. step.
    f12_sok B49. step.
    f12_sok B42. step.
    f12_sok B43. step.
    f12_sok B44. step.
    f12_sok B45. step.
    f12_sok B50. step.
    step.
    f12_rd Hq184 (A + 184) (fr + 336). step.
    f12_rd Hq192 (A + 192) (fr + 2768). step.
    step. step.
    (* ---- the ten stores are done: the memory facts over the write chain ---- *)
    match goal with
    | |- context [MS _ _ _ _ _ ?m0 (seg_rom _)] => remember m0 as mm eqn:Emm
    end.
    assert (MUst : munch [(A + 152, A + 160); (Sfr fr + 42, Sfr fr + 51)] mem mm).
    { rewrite Emm.
      repeat (apply munch_write; [ | lia | f12_len | cbn [inside]; rewrite ?length_le8, ?length_le1; cbn [Z.of_nat];
                                   first [left; lia | right; left; lia] ]).
      apply munch_refl. }
    assert (WMst : wmono rsegs mem mm) by (rewrite Emm; repeat apply wmono_write; apply wmono_refl).
    assert (STst : stk rsegs mm (sp - FN_STACK) sp)
      by (rewrite Emm; repeat (apply stk_write; [ | lia | f12_len ]); exact Hwstk).
    assert (SWst : shadow_rw mm)
      by (rewrite Emm; repeat (apply f12_shadow_rw_write; [ | lia | f12_len ]); exact HSW).
    assert (ROmm : ro_agree rsegs mm).
    { apply (sl_ro_keep [(A + 152, A + 160); (Sfr fr + 42, Sfr fr + 51)] mem mm Hro MUst). intros x Hx.
      cbn [Frame.outside outside].
      split; [lia|]. split; [lia | exact I]. }
    assert (ACst : asan_cells mm)
      by (apply (fl_asan_cells _ mem mm HAC MUst); intros x Hx; cbn [outside]; repeat split; try exact I; lia).
    assert (BAsrc : bytes_at rsegs mm (fragb fr) st)
      by (rewrite Emm; repeat (apply bytes_at_write_other; [ | lia | f12_len | f12_djl ]); exact HFGb).
    assert (RWdst : rw_cells rsegs mm (fr + 336) [CB 72 junk])
      by (rewrite Emm; repeat (apply rw_cells_frame; [ | lia | f12_len | f12_djl ]); exact Hjrw).
    assert (Q152m : bytes_at rsegs mm (A + 152) (le8 (getr regs 25))).
    { rewrite Emm.
      repeat first [ apply bytes_at_write_same; rewrite ?length_le8; cbn [Z.of_nat]; lia
                   | apply bytes_at_write_other; [ | lia | f12_len | f12_djl ] ]. }
    assert (ADsrc : addressable mm (fragb fr) 72).
    { apply (f12_addr_munch mem mm _ (fragb fr) 72 HfgA MUst). intros i Hi.
      assert (Hsh : in_shadow (shadow_addr (fragb fr + i)))
        by (apply shadow_of_app; apply Hfrapp; unfold fragb; lia).
      assert (Hne : ~ (Sfr fr + 42 <= shadow_addr (fragb fr + i) < Sfr fr + 51))
        by (apply (f12_sh_out_fr fr (fragb fr + i) 42 51 Hfr8 Hfr0 ltac:(unfold fragb; lia));
            unfold fragb; lia).
      destruct (f12_sh_lt _ Hsh) as (Hsl & Hsu).
      cbn [outside]; repeat split; try exact I;
      first [lia | match goal with |- ?G => idtac "ADFAIL:" G end; fail]. }
    assert (ADdst : addressable mm (fr + 336) 72).
    { apply (f12_addr_of_zero9 _ fr Hfr8 Hfrapp Hfr0). intros k Hk. rewrite Emm.
      destruct (Z.eq_dec k 0) as [->|?]; [replace (Sfr fr + 42 + 0) with (Sfr fr + 42) by lia; f12_zb|].
      destruct (Z.eq_dec k 1) as [->|?]; [replace (Sfr fr + 42 + 1) with (Sfr fr + 43) by lia; f12_zb|].
      destruct (Z.eq_dec k 2) as [->|?]; [replace (Sfr fr + 42 + 2) with (Sfr fr + 44) by lia; f12_zb|].
      destruct (Z.eq_dec k 3) as [->|?]; [replace (Sfr fr + 42 + 3) with (Sfr fr + 45) by lia; f12_zb|].
      destruct (Z.eq_dec k 4) as [->|?]; [replace (Sfr fr + 42 + 4) with (Sfr fr + 46) by lia; f12_zb|].
      destruct (Z.eq_dec k 5) as [->|?]; [replace (Sfr fr + 42 + 5) with (Sfr fr + 47) by lia; f12_zb|].
      destruct (Z.eq_dec k 6) as [->|?]; [replace (Sfr fr + 42 + 6) with (Sfr fr + 48) by lia; f12_zb|].
      destruct (Z.eq_dec k 7) as [->|?]; [replace (Sfr fr + 42 + 7) with (Sfr fr + 49) by lia; f12_zb|].
      replace k with 8 by lia. replace (Sfr fr + 42 + 8) with (Sfr fr + 50) by lia. f12_zb. }
    (* ---- the call of checked_memcpy, on the normalized memory ---- *)
    try unfold fragb in *.
    assert (E336 : bv_unsigned (Z_to_bv 64 (fr + 336)) = fr + 336) by (apply MState.unsigned_lit; lia).
    assert (E2768 : bv_unsigned (Z_to_bv 64 (fr + 2768)) = fr + 2768) by (apply MState.unsigned_lit; lia).
    assert (E72 : bv_unsigned (Z_to_bv 64 72) = 72) by (apply MState.unsigned_lit; lia).
    pose proof HMCPY as HM. unfold asan_memcpy_contract, ASAN_MEMCPY_K in HM. cbv zeta in HM.
    pose proof (mem_rel_normalize rsegs mm ROmm) as REL.
    eapply evt_cut.
    { eapply (evt_normalize rsegs); [vm_compute; reflexivity | exact ROmm |].
      eapply HM with (src := st) (junk := junk) (lo := sp - FN_STACK).
      all: rewrite ?E336, ?E2768, ?E72, ?HSPu.
      all: try change (Z.to_nat 72) with 72%nat.
      - exact (proj1 (bytes_at_rel rsegs mm _ _ _ REL) BAsrc).
      - exact HFGl.
      - apply (rel_rw_norm mm _ _ _ REL); [|exact RWdst].
        intros i Hi. apply ro_addr_false_hi. cbn [cells_size csize Nat.add] in Hi. lia.
      - right; right. lia.
      - lia.
      - exact (rel_addr_norm mm _ _ _ REL ADsrc).
      - exact (rel_addr_norm mm _ _ _ REL ADdst).
      - right. apply Hfrapp. lia.
      - right. apply Hfrapp. lia.
      - right. split; apply Hfrapp; lia.
      - right. lia.
      - destruct Hfrw2 as [Hd|Hd]; [left | right]; lia.
      - destruct Hfrw2 as [Hd|Hd]; [left | right]; lia.
      - apply (rel_stk_norm mm _ _ _ REL); [intros x Hx; apply ro_addr_false_hi; lia | exact STst].
      - lia.
      - lia.
      - exact HspA.
      - exact (rel_ac_norm mm _ REL ACst).
      - exact (rel_sw_norm mm _ REL SWst).
      - exact (mem_inv_normalize rsegs mm). }
    intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
      E0 & MU0 & WM0 & MI0 & ST0 & RW0 & BA0 & AC0 & SR0) & Hrel & Hro').
    subst s0'.
    destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
    destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes,
      EFc, ERom, HR', Hro'.
    subst r' f' p' sv' rv' fc' ro'.
    pose proof (munch_rel rsegs _ mm (normalize rsegs mm) m' m0' REL HR' Hro' MU0) as MUc.
    pose proof (wmono_rel rsegs mm (normalize rsegs mm) m' m0' REL HR' Hro' WM0) as WMc.
    pose proof (ro_agree_same rsegs mm m' ROmm Hro') as ROc.
    pose proof (rel_stk_back m' m0' _ _ HR' ST0) as STc.
    pose proof (rel_rw_back m' m0' _ _ HR' RW0) as RWc.
    pose proof (proj2 (bytes_at_rel rsegs m' m0' _ _ HR') BA0) as BAc.
    pose proof (rel_ac_back m' m0' HR' AC0) as ACc.
    pose proof (rel_sw_back m' m0' HR' SR0) as SRc.
    unfold ASAN_MEMCPY_K in MUc.
    rewrite ?E336 in MUc. rewrite ?E72 in MUc. rewrite ?HSPu in MUc.
    rewrite ?HSPu in STc.
    rewrite ?E336 in RWc. rewrite ?E72 in RWc.
    rewrite ?E2768 in BAc.
    replace (ret_pc (Z_to_bv 64 0x82138)) with (Z_to_bv 64 0x82138)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    apply evt_done.
    do 3 eexists. split; [reflexivity|].
    split; [reflexivity|].
    do 14 (split; [reflexivity|]).
    split.
    { unfold f12_W. eapply munch_trans.
      - eapply munch_weaken; [|exact MUst]. intros z Hz. cbn [outside] in *.
        repeat split; try exact I; lia.
      - eapply munch_weaken; [|exact MUc]. intros z Hz. cbn [outside] in *.
        repeat split; try exact I; lia. }
    split; [eapply wmono_trans; [exact WMst | exact WMc]|].
    split; [exact ROc|].
    split; [exact STc|].
    split.
    { unfold q64. unfold rg in Hs9. rewrite <- Hs9.
      eapply fl_bytes; [exact Q152m | exact MUc |]. rewrite length_le8. intros x Hx. cbn [outside].
      repeat split; try exact I; lia. }
    split; [change (Z.to_nat 72) with 72%nat in RWc; exact RWc|].
    split; [exact BAc|].
    split.
    { eapply (f12_addr_munch _ _ _ (fr + 336) 72 ADdst MUc). intros i Hi.
      assert (Hsh : in_shadow (shadow_addr (fr + 336 + i))) by (apply shadow_of_app; apply Hfrapp; lia).
      destruct (f12_sh_lt _ Hsh) as (Hsl & Hsu).
      cbn [outside]. repeat split; try exact I.
      all: first [ lia
                 | intros HCx; apply (fun H1 => app_not_shadow _ H1 Hsh); apply Hfrapp; lia
                 | match goal with |- ?G => idtac "ADDFAIL:" G end; fail ]. }
    split; [exact ACc | exact SRc].
  - (* ---- the exit cut at 0x82138 ---- *)
    intros R pc' mem' regs' md' (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 &
      E26 & MUt & WMt & ROt & STt & Q152 & RWd & BAs & ADd & ACt & SWt) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (Fr25 : getr regs' 25 = Z_to_bv 64 (fragb fr)) by (rewrite Hreg; exact E25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite Fr9; exact H9).
    assert (Trg : forall r v, getr regs' r = getr regs r -> rg regs r v -> rg regs' r v)
      by (intros r v E Hr; unfold rg in *; rewrite E; exact Hr).
    assert (TBL : bytes_at rsegs mem' (fr + 336) st)
      by (pose proof RWd as ((_ & Hb) & _); cbn [cells_bytes cbytes] in Hb; rewrite app_nil_r in Hb; exact Hb).
    pose proof Q152 as Q152b. unfold q64 in Q152b.
    (* ---- the write set f12_W, against every carried fact ---- *)
    assert (HWout : forall x, (x < A + 152 \/ A + 160 <= x) -> (x < Sfr fr + 42 \/ Sfr fr + 51 <= x) ->
              (x < fr + 336 \/ fr + 408 <= x) -> (x < sp - 2224 \/ sp <= x) -> Frame.outside (f12_W A fr sp) x).
    { intros x H1 H2 H3 H4. unfold f12_W. cbn [Frame.outside].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    assert (DISJ : forall q, (A + 152 <= q < A + 160) \/ (Sfr fr + 42 <= q < Sfr fr + 51) \/
               (fr + 336 <= q < fr + 408) \/ (sp - 2224 <= q < sp) \/ Frame.outside (f12_W A fr sp) q).
    { intros q. unfold f12_W. cbn [Frame.outside]. lia. }
    assert (HshW : forall x, app_mem x -> x < Sfr fr + 42 \/ Sfr fr + 51 <= x).
    { intros x Hx. destruct (Z_lt_le_dec x (Sfr fr + 42)) as [h|h]; [left; exact h|].
      destruct (Z_lt_le_dec x (Sfr fr + 51)) as [h2|h2]; [|right; exact h2].
      exfalso. exact (app_not_shadow x Hx (HshIS x ltac:(lia))). }
    assert (HfrS : forall s, in_shadow s -> s < fr + 336 \/ fr + 408 <= s).
    { intros s Hs. destruct (Z_lt_le_dec s (fr + 336)) as [h|h]; [left; exact h|].
      destruct (Z_lt_le_dec s (fr + 408)) as [h2|h2]; [|right; exact h2].
      exfalso. exact (app_not_shadow s (Hfrapp s ltac:(lia)) Hs). }
    assert (HWsh : forall a, app_mem a -> 0 <= a -> ~ (fr + 336 <= a < fr + 408) ->
              Frame.outside (f12_W A fr sp) (shadow_addr a)).
    { intros a Ha Ha0 Hna.
      pose proof (shadow_of_app a Ha) as Hs. destruct (f12_sh_lt _ Hs) as (Hs1 & Hs2).
      apply HWout; [lia | | exact (HfrS _ Hs) | lia].
      pose proof (f12_sh_out_fr fr a 42 51 Hfr8 Hfr0 Ha0 ltac:(lia)) as Hn. lia. }
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> (x < fr + 336 \/ fr + 408 <= x) ->
              Frame.outside (f12_W A fr sp) x).
    { intros x Hx Hc. apply HWout; [lia | exact (HshW x (Hfrapp x Hx)) | exact Hc |].
      destruct Hfrw2 as [Hd|Hd]; lia. }
    assert (HWA9 : forall x, A + 16 <= x < A + 416 -> (x < A + 152 \/ A + 160 <= x) ->
              Frame.outside (f12_W A fr sp) x).
    { intros x Hx Hc. apply HWout; [exact Hc | lia | lia | lia]. }
    assert (HWlo : forall x, 0 <= x < AC.GT -> Frame.outside (f12_W A fr sp) x).
    { intros x Hx. apply HWout; lia. }
    assert (HWsv : forall x, g_S g - 104 <= x < g_S g -> Frame.outside (f12_W A fr sp) x).
    { intros x Hx. apply HWout; lia. }
    assert (HWblk : forall q k x, In (q, k) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) -> q <= x < q + k ->
              Frame.outside (f12_W A fr sp) x /\ Frame.outside (f12_W A fr sp) (shadow_addr x)).
    { intros q k x Hin Hx. destruct (Hblk q k x Hin Hx) as (Hxa & Hxs & Hxf).
      assert (Hx0 : 0 <= x) by (unfold app_mem in Hxa; lia).
      split.
      - apply HWout; [lia | exact (HshW x Hxa) | lia | lia].
      - apply HWsh; [exact Hxa | exact Hx0 | lia]. }
    assert (HWin : 0 < g_n g -> forall x, g_p g <= x < g_p g + g_n g ->
              Frame.outside (f12_W A fr sp) x /\ Frame.outside (f12_W A fr sp) (shadow_addr x)).
    { intros Hn x Hx. apply (HWblk (g_p g) (g_n g) x); [apply in_or_app; right; exact (HinH Hn) | exact Hx]. }
    (* ---- AH, image ownership, stklo, stkhi across the run ---- *)
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WMt (Z_to_bv 64 a) Hw)).
    assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem' md /\
      (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem' md a
             <-> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md a) /\
      AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
        AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
      AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
        AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [(Hs50 & Hspfr & Hreal)|(Hs5f & HfsbS & HinFS & Hrec)].
      - (* real-stack arm: every written byte is at or above stklo, or the metadata of a frame byte *)
        assert (HstoreR : forall a, 0 <= a < 2 ^ 64 ->
          ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
              (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
          mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
        { intros a Ha Hns. apply MUt. rewrite MState.unsigned_lit by lia.
          destruct (DISJ a) as [D|[D|[D|[D|D]]]].
          - exfalso. apply Hns. unfold AC.a_store_ok. right; left. lia.
          - exfalso. apply Hns. unfold AC.a_store_ok. right; right; right.
            exists (fr + 8 * (a - Sfr fr)). split.
            + rewrite (f12_sh_fr fr (8 * (a - Sfr fr)) Hfr8 ltac:(lia)).
              replace (8 * (a - Sfr fr) / 8) with (a - Sfr fr)
                by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity). lia.
            + right; left. destruct (Hreal (fr + 8 * (a - Sfr fr)) ltac:(lia)) as (Hlo & Hhi). lia.
          - exfalso. apply Hns. unfold AC.a_store_ok. right; left.
            destruct (Hreal a ltac:(lia)) as (Hlo & Hhi). lia.
          - exfalso. apply Hns. unfold AC.a_store_ok. right; left. lia.
          - exact D. }
        exact (f12_law_store (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH HstoreR HwmL).
      - (* side arm: the frame is FakeStack slot jj of class 6 (FSREC); the metadata lies below FS + 36864 *)
        destruct Hrec as (FS & jj & HFSw & HFSr & Hjj & Hfre & _ & _).
        destruct (f12_law_fs_place (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md FS HAH HFSw HFSr)
          as (HFSgt & HFSst & HFSapp).
        assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
        rewrite HM6 in Hjj.
        assert (Hfrv : fr = FS + 6328320 + jj * 4096)
          by (rewrite Hfre; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  (exists b, mbyte rsegs mem' q = Some b)).
        { intros q Hq (b & Hb).
          destruct (DISJ q) as [D|[D|[D|[D|D]]]].
          - exact (f12_bytes_mrd mem' (A + 152) _ q Q152b ltac:(rewrite length_le8; lia)).
          - destruct (SWt q (HshIS q ltac:(lia))) as (_ & bb & Hbb). exists bb. exact Hbb.
          - exact (f12_bytes_mrd mem' (fr + 336) _ q TBL ltac:(rewrite HFGl; lia)).
          - destruct STt as (_ & _ & Hsk). destruct (Hsk q ltac:(lia)) as (_ & bb & Hbb). exists bb. exact Hbb.
          - exists b. rewrite (KindBGlue.mbyte_munch rsegs _ mem mem' q MUt Hq D). exact Hb. }
        assert (Hmeta : forall q, fs_meta FS q -> Frame.outside (f12_W A fr sp) q).
        { intros q Hq.
          assert (HqFS : FS <= q < FS + 36864).
          { pose proof (fs_meta_below FS q Hq) as Hlt. split; [|exact Hlt].
            destruct Hq as [Hc0|[Hc0|[(c & Hc & Hr)|(c & jj' & Hc & Hjj' & Heq)]]].
            - lia.
            - lia.
            - unfold AC.a_fs_hint in Hr. lia.
            - subst q. exact (proj1 (a_fs_flag_range FS c jj' Hc Hjj')). }
          assert (Happq : app_mem q) by (apply HFSapp; lia).
          apply HWout; [lia | exact (HshW q Happq) | lia | lia]. }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
          ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
              (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
          ~ (FS <= q < FS + AC.FS_SIZE) ->
          ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
          mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns Hnf Hnsh. apply MUt. rewrite MState.unsigned_lit by lia.
          destruct (DISJ q) as [D|[D|[D|[D|D]]]].
          - exfalso. apply Hns. unfold AC.a_store_ok. right; left. lia.
          - exfalso. apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia|].
            rewrite (f12_sh_fr fr (8 * (q - Sfr fr)) Hfr8 ltac:(lia)).
            replace (8 * (q - Sfr fr) / 8) with (q - Sfr fr)
              by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity). lia.
          - exfalso. apply Hnf. lia.
          - exfalso. apply Hns. unfold AC.a_store_ok. right; left. lia.
          - exact D. }
        destruct (a_fs_ok_store_AH AC.ASYMS (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
                    (f12_W A fr sp) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md FS LAWS HAH HFSw
                    ltac:(lia) ltac:(lia) MUt HwmL Hpres Hmeta Hagree)
          as (HA1 & HA2 & HA3 & HA4).
        split; [exact HA1|]. split; [exact HA2|]. split; [exact HA3 | exact HA4]. }
    destruct HAHS as (HAH' & Hown & HSTKlo & HSTKhi).
    (* ---- the frame's 392 metadata bytes, the S-anchored window and FSREC after the run ---- *)
    assert (HshStk : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW))
      by (apply (f12_shadow_stk mem' (Sfr fr) (Sfr fr + FRAME_SHADOW) SWt HshIS); lia).
    assert (Hshnew : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
    { destruct (f12_bytes_of_stk mem' (Sfr fr) (Z.to_nat FRAME_SHADOW) (Sfr fr) (Sfr fr + FRAME_SHADOW) HshStk ltac:(lia)
                  ltac:(cbn [Z.of_nat]; lia)) as (sh & Hl & Hb).
      exists sh. split; [exact Hb | exact Hl]. }
    assert (Hwin' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { apply (f12_stk_after (f12_W A fr sp) mem mem' _ _ Hwin MUt WMt). intros x Hx.
      destruct (DISJ x) as [D|[D|[D|[D|D]]]].
      - right. exact (f12_bytes_mrd mem' (A + 152) _ x Q152b ltac:(rewrite length_le8; lia)).
      - left. apply HWout; lia.
      - right. exact (f12_bytes_mrd mem' (fr + 336) _ x TBL ltac:(rewrite HFGl; lia)).
      - right. destruct STt as (_ & _ & Hsk). destruct (Hsk x ltac:(lia)) as (_ & bb & Hbb).
        exists bb. exact Hbb.
      - left. exact D. }
    assert (HrecK : FSREC fr mem -> FSREC fr mem').
    { intros Hrec. eapply fsrec_munch_lo with (W := f12_W A fr sp); [exact Hrec | exact HAH | exact MUt | |].
      - intros x Hx. apply HWlo. lia.
      - intros x Hxa Hxf Hxs. apply HWout; [lia | exact (HshW x Hxa) | lia | lia]. }
    (* ---- FRA and ENT at the exit ---- *)
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (sl_fra_move B APIf ra g fr _ regs regs' mem' md md');
        [| exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19 | exact Fr26 | exact Hmat].
      apply (f12_fr_run g fr _ regs mem mem' md (f12_W A fr sp) HFRA MUt WMt ROt).
      - unfold f12_W, rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
          RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
          RT_AGLOB, RT_AGLOB_LEN.
        unfold LOWMEM_END in HSHlo. unfold AC.GT in HGT.
        cbn [disjoint_from]. repeat split; try exact I;
        first [right; lia | left; lia | match goal with |- ?G => idtac "RTDJ:" G end; fail].
      - intros a Ha. destruct (SWt a Ha) as (_ & b & Hb). exists b. exact Hb.
      - exact HAH'.
      - exact HSTKlo.
      - intros x Hx. apply HWfr; lia.
      - exact HWlo.
      - intros A' HA' HA'r x Hx. rewrite (f12_A_eq regs A A' H9 HA64 HA' HA'r) in Hx. apply HWA9; lia.
      - exact HWsv.
      - exact Hshnew.
      - exact Hwin'.
      - exact HrecK.
      - intros a Ha. pose proof (f12_ag_lt a Ha) as Hab.
        apply (addr1_munch (f12_W A fr sp) mem mem' a MUt); [|exact (HAG a Ha)].
        apply HWsh; [exact (addr1_app mem a (HAG a Ha)) | lia | lia].
      - intros a Ha1 Ha2. pose proof (HWA a Ha1 Ha2) as HadA.
        apply (addr1_munch (f12_W A fr sp) mem mem' a MUt); [|exact HadA].
        apply HWsh; [exact (addr1_app mem a HadA) | lia | lia]. }
    assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { eapply ent_mat; [| exact Hmat].
      eapply ent_store with (W := f12_W A fr sp); [exact HENT | exact HFRA | exact MUt | | exact HSTKlo
                                                  | exact HSTKhi |].
      - intros x Hx. destruct (DISJ x) as [D|[D|[D|[D|D]]]].
        + right; left. lia.
        + right; right; right. lia.
        + right; right; left. lia.
        + right; left. lia.
        + left. exact D.
      - intros a _ Ho. exact (proj2 (Hown a) Ho). }
    (* ---- the carried facts at the exit ---- *)
    assert (Tq : forall off v, 24 <= off <= 400 -> (off + 8 <= 152 \/ 160 <= off) ->
              q64 mem (A + off) v -> q64 mem' (A + off) v).
    { intros off v Hoff Hoff2 Hqv. apply (f12_q64_mv (f12_W A fr sp) mem mem' (A + off) v Hqv MUt).
      intros x Hx. apply HWA9; lia. }
    assert (Tsp : forall off v, 24 <= off <= 400 -> (off + 8 <= 152 \/ 160 <= off) ->
              spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hoff2 Hs. exists A. split; [exact H9'|].
      apply Tq; [lia | lia | exact (f12_spill_q64 regs mem A off v H9 HA64 ltac:(lia) ltac:(lia) Hs)]. }
    assert (Tad : forall p n, addressable mem p n -> (forall i, 0 <= i < n -> ~ (fr + 336 <= p + i < fr + 408)) ->
              addressable mem' p n).
    { intros p n Had Hn. apply (f12_addr_munch mem mem' _ p n Had MUt). intros i Hi.
      pose proof Had as (Hp0 & _ & _ & Hall). destruct (Hall i Hi) as (Hai & _).
      apply HWsh; [exact Hai | lia | exact (Hn i Hi)]. }
    assert (Tfr : forall a bs, bytes_at rsegs mem a bs -> fr <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
              (a + Z.of_nat (length bs) <= fr + 336 \/ fr + 408 <= a) -> bytes_at rsegs mem' a bs).
    { intros a bs Hb H1 H2 H3. eapply fl_bytes; [exact Hb | exact MUt |]. intros x Hx. apply HWfr; lia. }
    assert (Tphi : forall a bs, bytes_at rsegs mem a bs -> phi <= a ->
              a + Z.of_nat (length bs) <= phi + AC.a_size (flen g j) -> bytes_at rsegs mem' a bs).
    { intros a bs Hb H1 H2. eapply fl_bytes; [exact Hb | exact MUt |]. intros x Hx.
      exact (proj1 (HWblk phi (AC.a_size (flen g j)) x Hinphi ltac:(lia))). }
    assert (TFS : FSj g fr j regs' mem').
    { destruct HFSj as (S104 & S112 & Sbody & Sad & HFI).
      split; [apply Tsp; [lia | lia | exact S104]|].
      split; [apply Tsp; [lia | lia | exact S112]|].
      pose proof (f12_fs_body_len (g_in g) j) as Hbl.
      split; [apply Tfr; [exact Sbody | lia | lia | lia]|].
      split; [apply Tad; [exact Sad | intros i Hi; lia] | exact HFI]. }
    assert (TID : IDb1 g fr j mem').
    { destruct HID as (HIDe & HIDok). split; [|exact HIDok].
      unfold IDBe in *. apply Tfr; [exact HIDe | lia | rewrite f12_ID1_len; lia | rewrite f12_ID1_len; lia]. }
    assert (TFG : FGj g fr j mem').
    { destruct HFGj as (HFGe & Hfok). split; [|exact Hfok].
      assert (LFG : length (t_FG (g_in g) j) = 72%nat) by exact HFGl.
      unfold FGBe in *. apply Tfr; [exact HFGe | lia | rewrite LFG; lia | rewrite LFG; lia]. }
    (* ---- the exit cut Inv_A82138_at ---- *)
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|].
    split; [exact HENT'|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { split; [exact Hphinz|]. apply Tad; [exact HADphi|].
      intros i Hi Hc. destruct (Hblk phi _ (phi + i) Hinphi ltac:(lia)) as (_ & _ & Hnf). apply Hnf. lia. }
    split.
    { apply (f12_FLSI_mv g j fr regs regs' mem mem' (f12_W A fr sp) A H9 HA64 ltac:(lia) Fr9 MUt).
      - intros x Hx Hc. apply HWA9; lia.
      - intros i Hi. apply HWsh; [apply Hfrapp; lia | lia | lia].
      - intros i Hi. apply HWsh; [apply Hfrapp; lia | lia | lia].
      - intros i Hi. unfold fragb. apply HWsh; [apply Hfrapp; lia | lia | lia].
      - intros i Hi. apply HWsh; [apply Hfrapp; lia | lia | lia].
      - exact HWin.
      - exact (fra_stk B APIf ra g fr _ regs' mem' md' HFRA').
      - exact HFLSI. }
    split.
    { apply (f12_LK_mv g j fr regs regs' mem mem' (f12_W A fr sp) Fr21 MUt); [|exact HLK].
      intros x Hx. apply HWfr; lia. }
    exists A, (b2z (t_sum_ok (g_in g) j)).
    split; [exact H9'|].
    split; [unfold rg; exact Fr25|].
    split; [exact HA64|].
    split; [unfold b2z; destruct (t_sum_ok (g_in g) j); lia|].
    split; [reflexivity|].
    split.
    { apply f12_q64_rw3.
      - apply Tq; [lia | lia | exact Hq256].
      - replace (A + 256 + 8) with (A + 264) by lia. apply Tq; [lia | lia | exact Hq264].
      - replace (A + 256 + 16) with (A + 272) by lia. apply Tq; [lia | lia | exact Hq272].
      - eapply wr_at_transport; [apply (f12_wrsub mem (A + 64) 224 192 24 (A + 256) Hwrsp); lia | exact WMt]. }
    split.
    { apply (f12_rw_of_bytes mem' (fragb fr) st 72); [ | exact HFGl | ].
      - apply Tfr; [exact HFGb | unfold fragb; lia | rewrite HFGl; unfold fragb; lia
                   | rewrite HFGl; unfold fragb; lia].
      - eapply wr_at_transport; [|exact WMt].
        apply (f12_wrsub mem fr FRAME_BYTES 2768 (Z.of_nat 72) (fragb fr) Hwrfr);
          [lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | unfold fragb; lia]. }
    split; [apply Tad; [exact HfgA | intros i Hi; unfold fragb; lia]|].
    split; [apply Tad; [exact HADpa | intros i Hi; lia]|].
    split; [apply Tad; [exact HADpp | intros i Hi; lia]|].
    split; [apply Tad; [exact HADpn | intros i Hi; lia]|].
    split; [exact ACt|]. split; [exact SWt|].
    split.
    { eapply fl_bytes; [apply f12_real_bcmp; exact HREAL | exact MUt |].
      rewrite length_le8. intros x Hx. apply HWlo. lia. }
    split.
    { eapply fl_bytes; [apply f12_real_memcmp; exact HREAL | exact MUt |].
      rewrite length_le8. intros x Hx. apply HWlo. lia. }
    split.
    { eapply fl_bytes; [apply f12_got_cf; exact HCF | exact MUt |].
      rewrite length_le8. intros x Hx. apply HWlo. lia. }
    split.
    { eapply fl_bytes; [apply f12_cf_254; exact HCF | exact MUt |].
      intros x Hx. apply HWlo. cbn [length] in Hx. lia. }
    split.
    { eapply fl_bytes; [apply f12_cf_255; exact HCF | exact MUt |].
      intros x Hx. apply HWlo. cbn [length] in Hx. lia. }
    split; [apply Tq; [lia | lia | exact Hq184]|].
    split; [apply Tq; [lia | lia | exact Hq192]|].
    split; [apply Tq; [lia | lia | exact Hq280]|].
    split; [exact TBL|].
    split; [exact ADd|].
    split; [apply Tq; [lia | lia | exact Hq80]|].
    split; [apply Tq; [lia | lia | exact Hq88]|].
    split; [apply Tq; [lia | lia | exact Hq96]|].
    split; [apply Tq; [lia | lia | exact Hq272]|].
    split; [apply Tq; [lia | lia | exact Hq264]|].
    split.
    { (* F16CARRY *)
      split; [exact (proj2 HFGj)|].
      split; [exact TFS|].
      split; [exists (ID1 g j); split; [exact (proj1 TID) | apply f12_ID1_len]|].
      split; [apply Tad; [exact HidA | intros i Hi; lia]|].
      split; [apply Tq; [lia | lia | exact Hq144]|].
      (* F17CARRY *)
      split; [exact (Trg _ _ Fr23 Hs7)|].
      split; [exact (Trg _ _ Fr22 Hs6)|].
      split; [exact (Trg _ _ Fr24 Hs8)|].
      split; [exact (Trg _ _ Fr18 Hr18)|].
      split; [exact (Trg _ _ Fr20 Hs4)|].
      split; [apply Tq; [lia | lia | exact Hq232]|].
      split.
      { destruct HF17 as (A17 & H917 & HA17 & Hq200).
        rewrite (f12_A_eq regs A A17 H9 HA64 H917 HA17) in Hq200. apply Tq; [lia | lia | exact Hq200]. }
      split; [apply Tq; [lia | lia | exact (f12_spill_q64 regs mem A 136 _ H9 HA64 ltac:(lia) ltac:(lia) S136)]|].
      split; [apply Tq; [lia | lia | exact (f12_spill_q64 regs mem A 120 _ H9 HA64 ltac:(lia) ltac:(lia) S120)]|].
      split; [apply Tq; [lia | lia | exact (f12_spill_q64 regs mem A 176 _ H9 HA64 ltac:(lia) ltac:(lia) S176)]|].
      split; [exists A; split; [exact H9' | exact Q152]|].
      split.
      { destruct HW240 as (A24 & H924 & HA24 & w240 & Hq240 & Hw0r & Hwt & Hwf).
        rewrite (f12_A_eq regs A A24 H9 HA64 H924 HA24) in Hq240.
        exists w240. split; [apply Tq; [lia | lia | exact Hq240]|].
        split; [exact Hw0r|]. split; [exact Hwt | exact Hwf]. }
      destruct HPF as (Ab & H9b & HAb & HL & H8).
      rewrite (f12_A_eq regs A Ab H9 HA64 H9b HAb) in H8.
      split.
      { intros H50.
        destruct (HL H50) as ((rb & Hrb & Hrbl) & Hphi).
        destruct HbPH as (HPHg & _ & _).
        assert (Hsz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
        assert (HGl : length (t_g (g_in g) j) = 50%nat) by (unfold t_g; apply fr50_length).
        assert (TG : bytes_at rsegs mem' phi (t_g (g_in g) j))
          by (apply Tphi; [exact (HPHg H50) | lia | rewrite HGl, Hsz; lia]).
        split.
        { exists (firstn 38 rb). split; [|rewrite length_firstn; lia].
          apply Tphi; [apply f12_bytes_first; exact Hrb | lia | rewrite length_firstn, Hsz; lia]. }
        split; [exact TG|].
        split.
        { apply Tphi; [exact Hphi | lia |]. pose proof (f12_phi_len (g_in g) j) as Hpl.
          rewrite Hsz. unfold flen in *. lia. }
        (* rec_inv0: b5_PH / HB / the block law, b5_F17, b5_SPILL's [A+248], b5_K's [A+280] *)
        pose proof HADphi as (Hp0 & _ & Hpe & _).
        split; [lia|].
        split; [unfold AC.a_size in Hpe; lia|].
        split; [exact H50|].
        split; [pose proof (RcParse.ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)); unfold t_k; lia|].
        split; [intros a Ha; exact (proj1 (Hblk phi _ a Hinphi ltac:(rewrite Hsz; lia)))|].
        split.
        { destruct HF17 as (A17 & H917 & HA17 & Hq200).
          rewrite (f12_A_eq regs A A17 H9 HA64 H917 HA17) in Hq200. apply Tq; [lia | lia | exact Hq200]. }
        split; [unfold t_blk; apply f12_bytes_bsl; [exact TG | lia | lia | rewrite HGl; lia]|].
        split; [apply f12_bytes_bsl; [exact TG | lia | lia | rewrite HGl; lia]|].
        split; [apply Tq; [lia | lia | exact Hq248] | apply Tq; [lia | lia | exact Hq280]]. }
      intros H8819.
      assert (Hbig : 50 <= flen g j).
      { unfold t_8819 in H8819. apply andb_prop in H8819 as (H1 & _). apply andb_prop in H1 as (H1 & _).
        unfold t_big in H1. apply Z.leb_le in H1. exact H1. }
      assert (Hsz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
      destruct (H8 H8819) as (HPG & (ls & rs & Hq56 & Hls & Hlsl & Hrs & Hrsl & Hmc & Had186) &
                              (ls2 & rs2 & Hq48 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hmc2 & Had180)).
      split.
      { apply (f12_parse_mv g j fr phi mem mem' (f12_W A fr sp) MUt); [ | | exact HPG].
        - intros x Hx. exact (HWblk phi _ x Hinphi ltac:(rewrite Hsz; lia)).
        - intros x Hx. apply HWfr; lia. }
      split.
      { exists (firstn 6 ls), (firstn 6 rs).
        split; [apply Tq; [lia | lia | exact Hq56]|].
        split; [apply Tfr; [apply f12_bytes_first; exact Hls | lia | rewrite length_firstn; lia
                           | rewrite length_firstn; lia]|].
        split; [rewrite length_firstn; lia|].
        split; [apply Tphi; [apply f12_bytes_first; exact Hrs | lia | rewrite length_firstn, Hsz; lia]|].
        split; [rewrite length_firstn; lia|].
        split; [rewrite f12_mcmp_firstn; exact Hmc|].
        apply Tad; [exact Had186 | intros i Hi; lia]. }
      exists (firstn 6 ls2), (firstn 6 rs2).
      split; [apply Tq; [lia | lia | exact Hq48]|].
      split; [apply Tfr; [apply f12_bytes_first; exact Hls2 | lia | rewrite length_firstn; lia
                         | rewrite length_firstn; lia]|].
      split; [rewrite length_firstn; lia|].
      split; [apply Tphi; [apply f12_bytes_first; exact Hrs2 | lia | rewrite length_firstn, Hsz; lia]|].
      split; [rewrite length_firstn; lia|].
      split; [rewrite f12_mcmp_firstn; exact Hmc2|].
      apply Tad; [exact Had180 | intros i Hi; lia]. }
    (* IFS1 *)
    split; [exact TID|]. split; [exact TFG | exact TFS].
Qed.

(* ENTRY 1 (0x820fc, F10's exit): f12_P is its body without ir = false. *)
Lemma f12_entry1 : forall j, Hat B APIf ra (fun g j c => b5_CUT B APIf ra g 0x820fc j (f12_P g j) c) j ->
  Hat B APIf ra (Inv_A820fc_at B APIf ra) j.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros j H g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HC &
    HK & HRC & _ & HID & H17 & H240 & H17b).
  apply H. exists phi, regs, mem, md, fr.
  split; [exact Ec|]. split; [exact HFRA|]. split; [exact HENT|].
  split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HFLSI|]. split; [exact HLK|].
  split; [exact HC|].
  split; [exact HK|]. split; [exact HRC|]. split; [exact HID|]. split; [exact H17|].
  split; [exact H240 | exact H17b].
Qed.

(* ENTRY 2 (0x820f8, the reac_identity_ingest return): `bltz a0` with 0 <= a0 < 2^63 is not taken; land at
   0x820fc with every register kept and f12_P moved to the new register file. *)
Lemma f12_entry2 : forall j, Hat B APIf ra (fun g j c => b5_CUT B APIf ra g 0x820fc j (f12_P g j) c) j ->
  Hat B APIf ra (Inv_A820f8_at B APIf ra) j.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros j H g c (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HLK & HC &
    HK & HRC & _ & (v & Ha0 & Hv) & HID & H17 & H240 & H17b).
  pose proof f12_ff as (SEGS & _). subst c. rewrite SEGS.
  pose proof HFRA as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _).
  apply (sl_run_lib regs (Z_to_bv 64 0x820f8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x820fc /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
       getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite f12_mkR_of_expand. try f12_lib_ms. f12_subst_slot Ha0.
    step.
    match goal with
    | |- context [if ?cnd then _ else _] =>
        replace cnd with false
          by (symmetry; unfold bv_lts; rewrite (f12_signed v Hv);
              change (bv_signed (Z_to_bv 64 0)) with 0; apply Z.ltb_ge; lia)
    end.
    cbv iota.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    repeat split; reflexivity.
  - intros R pc' mem' regs' md' (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 &
      E25 & E26) Hreg Hmat.
    subst pc' mem'. rewrite <- SEGS. apply H.
    assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    destruct (f12_body_regs g j phi fr regs regs' mem F2 F9
                ltac:(rewrite Hreg; exact E18) ltac:(rewrite Hreg; exact E20) ltac:(rewrite Hreg; exact E21)
                ltac:(rewrite Hreg; exact E22) ltac:(rewrite Hreg; exact E23) ltac:(rewrite Hreg; exact E24)
                ltac:(rewrite Hreg; exact E25) HFLSI HLK HC
                (conj HK (conj HRC (conj HID (conj H17 (conj H240 H17b))))))
      as (HF' & HL' & HC' & HP').
    exists phi, regs', mem, md', fr.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr _ regs regs' mem md md' HFRA);
        [ exact F2 | rewrite Hreg; exact E3 | rewrite Hreg; exact E4 | rewrite Hreg; exact E8 | exact F9
        | rewrite Hreg; exact E19 | rewrite Hreg; exact E26 | exact Hmat ]. }
    split; [eapply ent_mat; [exact HENT | exact Hmat]|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|]. split; [exact HF'|]. split; [exact HL'|].
    split; [exact HC' | exact HP'].
Qed.

(* The segment lemma: from F13's entry cut at 0x82138, both entry cuts hold. *)
Lemma seg_F12 : forall j, Hat B APIf ra (Inv_A82138_at B APIf ra) j ->
  Hat B APIf ra (Inv_A820fc_at B APIf ra) j /\ Hat B APIf ra (Inv_A820f8_at B APIf ra) j.
Proof. pose proof FRAME_BYTES_val as HFBval. pose proof FRAME_SHADOW_val as HFSval.
  intros j Hexit. pose proof (f12_run j Hexit) as Hrun.
  split; [exact (f12_entry1 j Hrun) | exact (f12_entry2 j Hrun)].
Qed.

End S.
