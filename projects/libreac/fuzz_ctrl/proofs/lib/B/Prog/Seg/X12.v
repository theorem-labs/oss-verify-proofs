(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 2169 of its 2293 lines of code are new or changed and 887 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F30.v, with its module paths and module names changed; 801 of its 920 lines of code are new or changed and 2174 lines of the source are left out. *)
(* Segments X1 (0x82eac-0x82ec8 / 0x82ecc) and X2 (0x82ecc-0x82f28) of the entry function
   LLVMFuzzerTestOneInput of fuzz_ctrl (asan-ubsan build of image B), libreac v1.9.0. The image-B port of
   lib/A/Prog/Seg/X12.v (seg_X1 / seg_X2).

   X1: `ld a0,176(s1); lbu a0,20(a0); beqz a0,0x82ed0`.  On the taken path (byte 20 of the identity record is 0)
   the segment falls into the shadow-fill block at 0x82ed0; on the other path it runs `ld a0,176(s1);
   addi a0,a0,3; li a2,17; li a1,0` and calls the memchr wrapper at 0x42ab0 on [fr+2691, fr+2708), and reaches
   0x82ecc with a0 <> 0 (the byte searched for is present, so the wrapper returns fr + 2691 + j, never 0).
   X2: `beqz a0,0x82fa4` is shown NOT taken (a0 <> 0; 0x82fa4 is the abort pair), then the same block.
   None of the X1 / X2 loads has an instrumented check: [s1+176] is a spill slot and byte 20 of the identity
   record is read without a shadow check in this build.

   The shared block 0x82ed0-0x82f2c: `li a0,-8`, twenty `sb a0,off(s3)` into the frame's shadow bytes
   (s3 = S(fr), offsets 352 353 354 360 361 362 363 364 348 349 350 351 339 340 346 347 328 336 337 338, all in
   [328, 365) of the frame's 392 shadow bytes), then `ld s8,48(s1); ld s9,40(s1)` to the release join 0x82f2c,
   which is Inv_Jrel (CUTST0 with register 24 = the selector and register 25 = fr).  v1.8 had fifteen stores
   (328..354) and `ld s8,64(s1); ld s7,56(s1)`: v1.9 moves the 352..354 stores (frag's last three granules; frag is
   fr + 2768, 72 bytes, shadow 346..354) to the head of the block and adds 360..364, the five shadow granules of the
   new local `first` (fr + 2880, 40 bytes; frame 3040 -> 3136 bytes).  Evidence (v1.9 listing): s3 is set once,
   0x810d4 `srli s3,s9,3` (s9 = fr) and 0x810fc `add s3,s3,s10` (s10 = ASAN_K), FRA's rg regs 19 (Sfr fr); P3
   unpoisons the same five bytes (0x81cdc / 0x81ce0 / 0x81cf4-0x81cfc `sb zero,360..364(s3)`) before its
   checked_memset 0x81d0c of [A+168] = fr + 2880, 40 bytes.  Each epilogue store writes 0xf8 (stack use-after-scope)
   into a shadow byte of the frame.  No exit cut of X1 / X2 names those bytes: FRAS (Inv_Jrel) carries the 392
   frame shadow bytes as an existential list and ENT names only the shadow of the image and of [S, APPMEM_END);
   Inv_B82ecc is reached before the stores.  (Inv_B82eac's `addressable m (fr + 2691) 17`, shadow 336..338, is
   X1's entry fact, used by the memchr wrapper before the stores; RAD's `addressable m (fr + 2880) 40` belongs to
   the frame-loop cuts.)  The frame facts cross the shadow stores with Tac_slot.sl_fr_meta and the wrapper's stack
   window with Tac_slot.sl_callee_keep; the entry relation ENT crosses both with Tac_slot.ent_store and the
   lazy-page step with ent_mat.

   Image A -> image B: the identity record pointer spill [A + 144] -> [A + 176] (v1.8 [A + 184]; the same record,
   fr + 2688: 0x81500 `sd a1,176(s1)` with a1 = a3 + 512, a3 = fr + 2176); the selector / frame reload s5 / s6
   (regs 21 / 22) -> s8 / s9 (regs 24 / 25) from [A + 48] / [A + 40]; the fr spill A + 336.

   Cuts.  The segments are stated on the official Inv_B82eac / Inv_B82ecc / Inv_Jrel of lib/B/Prog/SlotInv.v
   (v1.9 pcs 0x82eac / 0x82ecc / 0x82f2c; the names are still v1.8): Inv_B82eac carries the record pointer spill
   [A + 176] = fr + 2688, the 21 identity bytes there with a 0 in bytes 3 .. 19 and those 17 bytes addressable;
   Inv_B82ecc carries a0 <> 0 as `exists q, a0v regs q /\ 0 < q < 2 ^ 64`.  The spill is read at s1's A, the base
   FRA pins.

   The memchr wrapper's contract is the Section Hypothesis HMW (lib/B/Prog/memchr_wrap_c.v memchr_wrap_contract;
   lib/B/Prog/memchr_wrap.v memchr_wrap_holds discharges it).  It needs mem_inv, which no cut body carries (FRA
   keeps ro_agree only), so the call runs on the normalized memory (MemNorm.evt_normalize) and its post crosses
   back over mem_rel.  The 20 shadow stores need no mem_inv. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require memchr_c memchr_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module MW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memchr_wrap_c.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.memchr_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module TF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.Tac_fs.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module KBG := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.KindBGlue.

(* ---------------------------------------------------------------- generic helpers *)

(* bytes_at sub-range (local copy of lib.Prog.RcBoxLib.bytes_at_sub; importing it qualified would shadow the
   step engine). *)
Lemma x12_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

Lemma x12_rd_le8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H.
  pose proof (bytes_at_ov_read rsegs m a (le8 v) 0 8 H ltac:(rewrite length_le8; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH.
Qed.

Lemma x12_rd_b1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn [length]; lia)) as HH.
  cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH. cbn [firstn] in HH. exact HH.
Qed.

(* store_ok of one byte inside a present-and-writable window. *)
Lemma x12_stk_store_ok : forall m lo hi a, stk rsegs m lo hi -> lo <= a < hi -> store_ok rsegs m (wa a) 1 = true.
Proof.
  intros m lo hi a (H0 & H1 & H) Ha.
  assert (WR : wr_at rsegs m a 1).
  { split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with a by lia. exact (proj1 (H a Ha)). }
  pose proof (wr_at_store_ok rsegs m a 1 0 1 WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* S(fr) + i is the shadow byte of fr + 8 i. *)
Lemma x12_sh_of : forall fr x, shadow_addr (fr + 8 * (x - shadow_addr fr)) = x.
Proof.
  intros fr x. unfold shadow_addr.
  replace (fr + 8 * (x - (fr / 8 + ASAN_K))) with ((x - (fr / 8 + ASAN_K)) * 8 + fr) by lia.
  rewrite Z.div_add_l by lia. lia.
Qed.

(* Reading a byte list out of a present window. *)
Definition x12_rdb (m : word -> option byte) (a : Z) : byte :=
  match mrd rsegs m (wa a) with Some b => b | None => Z_to_bv 8 0 end.
Fixpoint x12_rds (m : word -> option byte) (a : Z) (n : nat) : list byte :=
  match n with O => [] | S k => x12_rdb m a :: x12_rds m (a + 1) k end.

Lemma x12_rds_length : forall n m a, length (x12_rds m a n) = n.
Proof. induction n as [|n IH]; intros m a; cbn [x12_rds length]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma x12_bytes_of_stk : forall (n : nat) m lo hi, stk rsegs m lo hi -> 0 <= lo -> lo + Z.of_nat n <= hi ->
  hi <= 2 ^ 64 -> bytes_at rsegs m lo (x12_rds m lo n).
Proof.
  induction n as [|n IH]; intros m lo hi HST H0 Hn Hhi.
  - split; [lia|]. split; [cbn [x12_rds length Z.of_nat]; lia|].
    intros i Hi; cbn [x12_rds length] in Hi; lia.
  - pose proof HST as HST2. destruct HST2 as (Hlo & Hhi2 & H).
    pose proof (proj2 (stk_split rsegs m lo (lo + 1) hi HST ltac:(lia))) as HST1.
    pose proof (IH m (lo + 1) hi HST1 ltac:(lia) ltac:(lia) ltac:(lia)) as IHa.
    destruct IHa as (Ha1 & Ha2 & Ha3).
    split; [lia|]. split; [rewrite x12_rds_length; lia|].
    intros i Hi. rewrite x12_rds_length in Hi.
    destruct i as [|i]; cbn [x12_rds nth_error].
    + rewrite Z.add_0_r. unfold x12_rdb.
      destruct (H lo ltac:(lia)) as (_ & b & Hb). rewrite Hb. reflexivity.
    + replace (lo + Z.of_nat (S i)) with (lo + 1 + Z.of_nat i) by lia.
      rewrite Ha3 by (rewrite x12_rds_length; lia). reflexivity.
Qed.

Lemma x12_mod64 : forall a a', Z_to_bv 64 a' = Z_to_bv 64 a -> a' mod 2 ^ 64 = a mod 2 ^ 64.
Proof.
  intros a a' H. apply (f_equal (bv_unsigned (n := 64))) in H.
  rewrite !LMS.unsigned_lit_wrap in H. exact H.
Qed.

Lemma x12_eq_of_bv : forall a a', Z_to_bv 64 a' = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 -> 0 <= a' < 2 ^ 64 -> a' = a.
Proof.
  intros a a' H Ha Ha'. pose proof (x12_mod64 a a' H) as E.
  rewrite (Z.mod_small a' (2 ^ 64)) in E by lia. rewrite (Z.mod_small a (2 ^ 64)) in E by lia. exact E.
Qed.

(* Two 64-bit values with the same byte image at one address agree. *)
Lemma x12_word_uniq : forall mem a v w, 0 <= a -> a + 8 <= 2 ^ 64 ->
  word_mem rsegs mem a v -> word_mem rsegs mem a w -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> v = w.
Proof.
  intros mem a v w Ha Ha8 Hv Hw Hvb Hwb.
  apply (x12_eq_of_bv w v); [|exact Hwb | exact Hvb].
  apply (fl_le8_eq [] mem mem a (Z_to_bv 64 v) (Z_to_bv 64 w)).
  - apply KBG.word_mem_le8; assumption.
  - apply KBG.word_mem_le8; assumption.
  - apply munch_refl.
  - intros x _. exact I.
Qed.

(* The registered globals all lie below GT (so below the frame). *)
Lemma x12_ag_lt : forall a, in_globals AF.frame_AG a -> a < AC.GT.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (H : forallb (fun p => Z.leb (fst p + snd p) AC.GT) AF.frame_AG = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. pose proof (H (lo, len) Hin) as Hb. cbn [fst snd] in Hb.
  apply Z.leb_le in Hb. lia.
Qed.

(* ---- transfers along MemNorm.mem_rel, for the memchr wrapper call: its contract needs mem_inv, which FRA
   does not carry, so the call runs on the normalized memory (MemNorm.evt_normalize) and each premise crosses
   mem_rel on the way in, each post clause on the way back.  Only the read-only image bytes differ between the
   two memories, and every segment of the image ends at or below GT (Tac_slot.img_tops_true). *)

(* A segment that holds [x, x + n) ends at or below top (local copy of lib/B/Prog/Seg/F18.v f18_seg_below). *)
Lemma x12_seg_below : forall (sg : list Segment) top x n s,
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sg = true ->
  find_segment sg x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction sg as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr]. apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma x12_ro_hi : forall a, AC.GT <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. assert (HGT : AC.GT = 0x5fe000) by reflexivity. unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. rewrite wa_unsigned in E by lia.
  destruct (x12_seg_below rsegs AC.GT a 1 s img_tops_true E ltac:(lia)) as [L|L]; lia.
Qed.

Lemma x12_shadow_not_ro : forall a, in_shadow a -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. apply x12_ro_hi. assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha. lia.
Qed.

(* One present-and-writable cell (the body of both stk and shadow_rw) crosses mem_rel at any address the image
   does not own. *)
Lemma x12_cell_rel : forall m m0 a, mem_rel rsegs m m0 -> ro_addr rsegs (wa a) = false ->
  (wview rsegs m (wa a) <> None /\ (exists b, mrd rsegs m (wa a) = Some b)) <->
  (wview rsegs m0 (wa a) <> None /\ (exists b, mrd rsegs m0 (wa a) = Some b)).
Proof.
  intros m m0 a HR Hro.
  rewrite (wview_rel_rw rsegs m m0 (wa a) HR Hro), (mrd_rel rsegs m m0 (wa a) HR). tauto.
Qed.

Lemma x12_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> HIGHMEM_BEG <= lo -> hi <= APPMEM_END ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  refine (proj1 (x12_cell_rel m m0 a HR (x12_ro_hi a _)) (H a Ha)).
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  unfold HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Lemma x12_stk_rel_back : forall m m0 lo hi, mem_rel rsegs m m0 -> HIGHMEM_BEG <= lo -> hi <= APPMEM_END ->
  stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR Hlo Hhi (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  refine (proj2 (x12_cell_rel m m0 a HR (x12_ro_hi a _)) (H a Ha)).
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  unfold HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Lemma x12_sw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha.
  exact (proj1 (x12_cell_rel m m0 a HR (x12_shadow_not_ro a Ha)) (H a Ha)).
Qed.

Lemma x12_sw_rel_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha.
  exact (proj2 (x12_cell_rel m m0 a HR (x12_shadow_not_ro a Ha)) (H a Ha)).
Qed.

Lemma x12_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma x12_ac_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 HR H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs =>
      exact (proj1 (bytes_at_rel rsegs m m0 a bs HR) ltac:(assumption)) end.
Qed.

Lemma x12_ac_rel_back : forall m m0, mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 HR H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs =>
      exact (proj2 (bytes_at_rel rsegs m m0 a bs HR) ltac:(assumption)) end.
Qed.

(* ---------------------------------------------------------------- instruction runs *)

(* Resolve the branch condition from H (if_true_by / if_false_by leave one goal too few here: replace closes
   its side goal with H by assumption when H is in context). *)
Ltac x12_br b H :=
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (symmetry; exact H); cbv iota
  end.

(* store_ok of the byte at Sh + off, out of the shadow window ST. *)
Ltac x12_st ST Sh off :=
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa (Sh + off)) 1 = true)
        by (apply (x12_stk_store_ok _ _ _ _ ST); lia)
  end.

(* 0x82ed0 - 0x82f2c: li a0,-8; twenty sb a0,off(s3) (offsets 352 353 354 360 361 362 363 364 348 349 350 351 339
   340 346 347 328 336 337 338); ld s8,48(s1) (the selector, vS); ld s9,40(s1) (the frame base, vF).
   Touched: the shadow bytes [Sh + 328, Sh + 365) (written), [A + 40, A + 56) (read). v1.8 (0x82e80 - 0x82ec8) had
   fifteen stores, 352..354 after 347 and no 360..364, then ld s8,64(s1); ld s7,56(s1). *)
Lemma x12_store_evt :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A Sh vS vF : Z),
    s1v = Z_to_bv 64 A -> s3v = Z_to_bv 64 Sh ->
    stk rsegs m Sh (Sh + 392) ->
    bytes_at rsegs m (A + 48) (le8 (Z_to_bv 64 vS)) ->
    bytes_at rsegs m (A + 40) (le8 (Z_to_bv 64 vF)) ->
    0 <= Sh -> Sh + 392 <= 2 ^ 64 -> Sh + 392 <= A -> A + 56 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists (m' : word -> option byte),
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (-8)) a1 a2 a3 a4 a5 a6 a7
                       s2 s3v s4 s5 s6 s7 (Z_to_bv 64 vS) (Z_to_bv 64 vF) s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 536364) fc None m' (seg_rom rsegs)
         /\ munch [(Sh + 328, Sh + 365)] m m'
         /\ wmono rsegs m m' /\ stk rsegs m' Sh (Sh + 392))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536272) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A Sh vS vF -> -> ST H48 H40 HSh0 HSh1 HShA HAb.
  pose proof (munch_refl [(Sh + 328, Sh + 365)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  x12_st ST Sh 352. step. store_done.
  x12_st ST Sh 353. step. store_done.
  x12_st ST Sh 354. step. store_done.
  x12_st ST Sh 360. step. store_done.
  x12_st ST Sh 361. step. store_done.
  x12_st ST Sh 362. step. store_done.
  x12_st ST Sh 363. step. store_done.
  x12_st ST Sh 364. step. store_done.
  x12_st ST Sh 348. step. store_done.
  x12_st ST Sh 349. step. store_done.
  x12_st ST Sh 350. step. store_done.
  x12_st ST Sh 351. step. store_done.
  x12_st ST Sh 339. step. store_done.
  x12_st ST Sh 340. step. store_done.
  x12_st ST Sh 346. step. store_done.
  x12_st ST Sh 347. step. store_done.
  x12_st ST Sh 328. step. store_done.
  x12_st ST Sh 336. step. store_done.
  x12_st ST Sh 337. step. store_done.
  x12_st ST Sh 338. step. store_done.
  pose proof (x12_rd_le8 _ _ _ H48) as HR48.
  step.
  clear HR48.
  pose proof (x12_rd_le8 _ _ _ H40) as HR40.
  step.
  clear HR40.
  apply evt_done. cbv beta. eexists _.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* 0x82eac - 0x82ed0, taken branch (byte 20 of the identity record is 0).
   Touched: [A + 176, A + 184) and the byte fr + 2708 (read). *)
Lemma x12_b_evt :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr : Z) (b20 : byte),
    s1v = Z_to_bv 64 A ->
    bytes_at rsegs m (A + 176) (le8 (Z_to_bv 64 (fr + 2688))) ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 = 0 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 0) a1
                               a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 536272) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536236) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr b20 -> H176 H20 Hb0.
  assert (HBz : zxb b20 = Z_to_bv 64 0).
  { apply bv_eq. rewrite kb_unsigned_zxb, Hb0. symmetry. apply LMS.unsigned_lit. lia. }
  assert (HB : bv_eqb (zxb b20) (Z_to_bv 64 0) = true) by (rewrite HBz; unfold bv_eqb; apply Z.eqb_refl).
  pose proof (x12_rd_le8 _ _ _ H176) as HR176.
  step.
  pose proof (x12_rd_b1 _ _ _ H20) as HR20.
  replace (fr + 2688 + 20) with (fr + 2708) in HR20 by lia.
  step.
  step.
  x12_br true HB.
  apply evt_done. cbv beta. rewrite HBz. reflexivity.
Qed.

(* 0x82eac - 0x82ecc: the memchr wrapper on [fr+2691, fr+2708), its contract given as HM.
   Touched: [A + 176, A + 184), the byte fr + 2708 and [fr + 2691, fr + 2708) (read); the wrapper's own stack
   window [sp - 2208, sp) (written). *)
Lemma x12_a_evt :
  MW.memchr_wrap_contract ->
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A fr lo spZ : Z) (buf : list byte) (b20 : byte) (j : nat),
    s1v = Z_to_bv 64 A -> bv_unsigned sp = spZ ->
    bytes_at rsegs m (A + 176) (le8 (Z_to_bv 64 (fr + 2688))) ->
    0 <= fr -> fr + FRAME_BYTES <= APPMEM_END ->
    bytes_at rsegs m (fr + 2708) [b20] -> bv_unsigned b20 <> 0 ->
    bytes_at rsegs m (fr + 2691) buf -> length buf = 17%nat -> SF.find_byte 0 buf = Some j ->
    ro_agree rsegs m -> addressable m (fr + 2691) 17 ->
    (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
    (fr + FRAME_BYTES <= spZ - 2208 \/ spZ <= fr) ->
    stk rsegs m lo spZ -> lo + 2208 <= spZ ->
    HIGHMEM_BEG <= lo -> spZ <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m MW.REAL_MEMCHR (le8 (wa MC.MEMCHR)) ->
    LE.evt rsegs
      (fun ms' => exists (x1 a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR x1 sp gp tp t0' t1' t2' s0 s1v (Z_to_bv 64 (fr + 2691 + Z.of_nat j))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 536268) fc None m' (seg_rom rsegs)
         /\ munch [(spZ - 2208, spZ)] m m'
         /\ wmono rsegs m m' /\ ro_same rsegs m m' /\ stk rsegs m' lo spZ
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536236) fc None m (seg_rom rsegs)).
Proof.
  intros HM ra0 gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m A fr lo spZ buf b20 j -> Esp H176 Hfr0 HfrA H20 Hb20 Hbuf HbufL HFB HRO Hadr Happ Hdisj
    HST Hlo1 Hlo2 Hspa HAC HSW HRM.
  subst spZ. pose proof FRAME_BYTES_val as HFBv.
  unfold APPMEM_END in HfrA.
  assert (HPb : 0 <= fr + 2691 < 2 ^ 64) by lia.
  pose proof (SF.find_byte_Some 0 buf j HFB) as (Hjl & _ & _).
  assert (HFF : SF.find_byte 0 (firstn (Z.to_nat 17) buf) = Some j).
  { rewrite firstn_all2 by (rewrite HbufL; cbn [Z.to_nat]; lia). exact HFB. }
  assert (HRES : SF.memchr_res (fr + 2691) 0 17 buf = fr + 2691 + Z.of_nat j)
    by (unfold SF.memchr_res; rewrite HFF; reflexivity).
  assert (HN : MW.memchr_n (fr + 2691) 0 17 buf = Z.of_nat j + 1).
  { unfold MW.memchr_n. rewrite HRES.
    replace (fr + 2691 + Z.of_nat j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia. }
  assert (HOK : SF.memchr_ok (fr + 2691) 0 17 buf).
  { unfold SF.memchr_ok. rewrite HFF. left. rewrite HbufL. cbn [Z.of_nat]. lia. }
  assert (HB : bv_eqb (zxb b20) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite kb_unsigned_zxb in E. rewrite LMS.unsigned_lit in E by lia. exact (Hb20 E). }
  pose proof (x12_rd_le8 _ _ _ H176) as HR176.
  step.
  pose proof (x12_rd_b1 _ _ _ H20) as HR20.
  replace (fr + 2688 + 20) with (fr + 2708) in HR20 by lia.
  step.
  step.
  x12_br false HB.
  step. step. step. step. step.
  unfold MW.memchr_wrap_contract, MW.MEMCHR_WRAP_K in HM. cbv zeta in HM.
  assert (EP : bv_unsigned (Z_to_bv 64 (fr + 2691)) = fr + 2691) by (apply LMS.unsigned_lit; lia).
  assert (E0 : bv_unsigned (Z_to_bv 64 0) = 0) by (vm_compute; reflexivity).
  assert (E17 : bv_unsigned (Z_to_bv 64 17) = 17) by (vm_compute; reflexivity).
  eapply evt_cut.
  { (* the contract needs mem_inv, which FRA does not give (it gives ro_agree): run the call on the normalized
       memory, where mem_inv_normalize supplies it, and carry the post back over mem_rel / ro_same. *)
    eapply (evt_normalize rsegs _ _ F _ fc None m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO).
    pose proof (mem_rel_normalize rsegs m HRO) as REL.
    eapply HM with (buf := buf) (lo := lo).
    all: rewrite ?EP, ?E0, ?E17, ?Zmod_0_l, ?HN.
    - exact (bytes_at_normalize rsegs m (fr + 2691) buf HRO Hbuf).
    - exact HOK.
    - apply mem_inv_normalize.
    - lia.
    - apply (x12_addr_rel m (normalize rsegs m) (fr + 2691) (Z.of_nat j + 1) REL).
      pose proof (addressable_sub m (fr + 2691) 17 0 (Z.of_nat j + 1) Hadr ltac:(lia) ltac:(lia) ltac:(lia)) as HA2.
      rewrite Z.add_0_r in HA2. exact HA2.
    - right. apply Happ. lia.
    - right. apply Happ. lia.
    - rewrite HbufL. cbn [Z.of_nat]. destruct Hdisj as [Hd|Hd]; lia.
    - exact (x12_stk_rel m (normalize rsegs m) lo (bv_unsigned sp) REL Hlo2 Hspa HST).
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact (x12_ac_rel m (normalize rsegs m) REL HAC).
    - exact (x12_sw_rel m (normalize rsegs m) REL HSW).
    - exact (bytes_at_normalize rsegs m MW.REAL_MEMCHR (le8 (wa MC.MEMCHR)) HRO HRM). }
  intros ms' (s0' & HP & HMS & HRS).
  destruct HP as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6''
              & m0' & E & MU0 & WM0 & MI0 & ST0 & AC0 & SW0 & HB0).
  subst s0'.
  destruct HMS as (HRg & HFg & HPc & HSvc & HRes & HFc & HRom & HMR).
  destruct ms' as [regs2 fregs2 pc2 svc2 resv2 fcsr2 mem2 rom2].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HRg, HFg, HPc, HSvc, HRes, HFc, HRom, HMR, HRS.
  subst regs2 fregs2 pc2 svc2 resv2 fcsr2 rom2.
  rewrite EP, E0, E17, Zmod_0_l, HRES.
  replace (ret_pc (Z_to_bv 64 536268)) with (Z_to_bv 64 536268)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done. cbv beta.
  exists (Z_to_bv 64 536268), a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'',
         mem2.
  split; [reflexivity|].
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) mem2 m0' REL HMR HRS MU0)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) mem2 m0' REL HMR HRS WM0)|].
  split; [exact HRS|].
  split; [exact (x12_stk_rel_back mem2 m0' lo (bv_unsigned sp) HMR Hlo2 Hspa ST0)|].
  split; [exact (x12_ac_rel_back mem2 m0' HMR AC0) | exact (x12_sw_rel_back mem2 m0' HMR SW0)].
Qed.

(* 0x82ecc - 0x82ed0: beqz a0,0x82fa4 (the abort pair) shown not taken, a0 <> 0. Touches no memory. *)
Lemma x12_x2_evt :
  forall (ra0 gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q : Z),
    a0w = Z_to_bv 64 q -> 0 < q < 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7
                               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (Z_to_bv 64 536272) fc None m (seg_rom rsegs))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7
               s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 536268) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 s1v a0w a1 a2 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    sp F fc m q -> Hq.
  assert (HB : bv_eqb (Z_to_bv 64 q) (Z_to_bv 64 0) = false).
  { apply bv_eqb_neq. intro E. apply (f_equal (bv_unsigned (n := 64))) in E.
    rewrite !LMS.unsigned_lit in E by lia. lia. }
  step.
  x12_br false HB.
  apply evt_done. cbv beta. reflexivity.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The memchr wrapper's contract (0x42ab0, lib/B/Prog/memchr_wrap_c.v); lib/B/Prog/memchr_wrap.v
   memchr_wrap_holds proves it. *)
Hypothesis HMW : MW.memchr_wrap_contract.

(* ---- frame geometry. *)

Lemma x12_shadow_in : forall fr, (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr Happ x Hx.
  assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by (unfold Sfr in *; lia).
  pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
  unfold Sfr in His. rewrite x12_sh_of in His. exact His.
Qed.

Lemma x12_shadow_stk : forall m fr, shadow_rw m -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  stk rsegs m (Sfr fr) (Sfr fr + FRAME_SHADOW).
Proof.
  pose proof FRAME_SHADOW_val as HFSv.
  intros m fr HSW Happ.
  pose proof (x12_shadow_in fr Happ) as HIS.
  pose proof (in_shadow_range (Sfr fr) (HIS (Sfr fr) ltac:(lia))) as R1.
  pose proof (in_shadow_range (Sfr fr + 391) (HIS (Sfr fr + 391) ltac:(lia))) as R2.
  split; [lia|]. split; [lia|]. intros a Ha. exact (HSW a (HIS a Ha)).
Qed.

(* The side stack's base, when the frame lives in it (a_in_fs pins it to one 64-bit word at tp). *)
Lemma x12_fs_base : forall mem fr,
  (forall a, fr <= a < fr + FRAME_BYTES -> AC.a_in_fs AC.ASYMS mem a) ->
  exists FS, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
    FS <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros mem fr Hfs.
  destruct (Hfs fr ltac:(lia)) as (b1 & Hb1r & Hw1 & Hr1).
  destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (b2 & Hb2r & Hw2 & Hr2).
  assert (E : b2 = b1).
  { apply (x12_word_uniq mem (AC.as_tp AC.ASYMS) b2 b1); try assumption;
      unfold AC.as_tp, AC.ASYMS; cbn; lia. }
  subst b2. exists b1. split; [exact Hw1|]. split; [exact Hb1r|]. split; [lia|].
  unfold AC.FS_SIZE in *. lia.
Qed.

(* FRA gives FRAS at a selector the caller names, once that selector is the one in [A + 48] (v1.8 [A + 64]). *)
Lemma x12_FRAS_of_FRA : forall g fr hb regs mem md A s5,
  FRA B APIf ra g fr hb regs mem md ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 -> q64 mem (A + 48) s5 -> 0 <= s5 < 2 ^ 64 ->
  FRAS B APIf ra g fr hb regs mem md s5.
Proof.
  intros g fr hb regs mem md A s5 HFRA Hr9a HAb Hsela Hs5b.
  destruct HFRA as (A0 & sp & s50 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (H1 & H2 & _); lia).
  assert (HA0b : 0 <= A0 < 2 ^ 64) by (unfold AF.SLOT_STACK in HSb; lia).
  assert (EA : A = A0)
    by (apply (x12_eq_of_bv A0 A); [unfold rg in *; rewrite <- Hr9a; exact Hr9 | exact HA0b | exact HAb]).
  subst A.
  assert (HfrB : 0 <= fr /\ fr + 8 <= 2 ^ 64)
    by (destruct Hhdr1 as (H1 & H2 & _); rewrite length_le8 in H2; lia).
  assert (Hs50b : 0 <= s50 < 2 ^ 64) by (destruct Hs5 as [E|E]; rewrite E; lia).
  assert (ES : s5 = s50).
  { assert (E : Z_to_bv 64 s5 = Z_to_bv 64 s50).
    { apply (fl_le8_eq [] mem mem (A0 + 48) (Z_to_bv 64 s5) (Z_to_bv 64 s50) Hsela Hsel (munch_refl [] mem)).
      intros x _. exact I. }
    apply (x12_eq_of_bv s50 s5 E); lia. }
  subst s5.
  unfold FRAS, FRAH. exists A0, sp. tauto.
Qed.

(* ---- the shared tail: 0x82ed0 to the release join. *)

Lemma x12_tail : forall g fr regs mem md,
  Hcut B APIf ra (Inv_Jrel B APIf ra) ->
  FRA B APIf ra g fr [] regs mem md ->
  ENT APIf g [] mem md ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 536272) mem (seg_rom rsegs)) md) (Post B APIf ra g).
Proof.
  intros g fr regs mem md Hjrel HFRA HENT.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (proj1 FF) as SEGS.
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS ([] ++ g_H g) mem md HAH) as Hhi.
  assert (HSb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (H1 & H2 & _); lia).
  assert (HAb : 0 <= A < 2 ^ 64) by (unfold AF.SLOT_STACK in HSb; lia).
  assert (HAhigh : HIGHMEM_BEG <= A) by (unfold AF.SLOT_STACK in *; lia).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (Hsphigh : HIGHMEM_BEG + 1044480 < sp) by lia.
  assert (HfrB : 0 <= fr /\ fr + 8 <= 2 ^ 64)
    by (destruct Hhdr1 as (H1 & H2 & _); rewrite length_le8 in H2; lia).
  assert (Hs5b : 0 <= s5 < 2 ^ 64) by (destruct Hs5 as [E|E]; rewrite E; lia).
  pose proof (AsanRTInv.RT_shadow_rw sp mem md HRT) as HSW.
  pose proof (x12_shadow_stk mem fr HSW Happ) as HSTK.
  assert (HSTK2 : stk rsegs mem (Sfr fr) (Sfr fr + 392)) by (rewrite <- HFSv; exact HSTK).
  pose proof (x12_shadow_in fr Happ) as HIS.
  assert (HShb : 0 <= Sfr fr /\ Sfr fr + 392 <= 2 ^ 64) by (destruct HSTK2 as (H1 & H2 & _); lia).
  assert (HShhigh : Sfr fr + 392 <= HIGHMEM_BEG).
  { pose proof (HIS (Sfr fr + 391) ltac:(lia)) as Hin.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin. unfold HIGHMEM_BEG. lia. }
  assert (HShA : Sfr fr + 392 <= A) by (unfold HIGHMEM_BEG in *; lia).
  set (W := [(Sfr fr + 328, Sfr fr + 365)]).
  (* lazy run 0x82ed0 -> 0x82f2c (x12_store_evt): writes [Sfr fr + 328, Sfr fr + 365) (the twenty shadow stores,
     v1.8 [Sfr fr + 328, Sfr fr + 355)), reads [A + 40, A + 56) (v1.8 [A + 56, A + 72)). *)
  apply (sl_run_lib regs (Z_to_bv 64 536272) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 536364 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 24 = Z_to_bv 64 s5 /\ getr R 25 = Z_to_bv 64 fr /\
       munch W mem mem' /\ wmono rsegs mem mem' /\ stk rsegs mem' (Sfr fr) (Sfr fr + 392))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold Regs6ss.mkR_of.
    eapply LE.evt_mono.
    { eapply x12_store_evt with (A := A) (Sh := Sfr fr) (vS := s5) (vF := fr).
      - unfold rg in Hr9; exact Hr9.
      - unfold rg in Hr19; exact Hr19.
      - exact HSTK2.
      - unfold q64 in Hsel; exact Hsel.
      - unfold q64 in Hfr40; exact Hfr40.
      - lia.
      - lia.
      - exact HShA.
      - lia. }
    { intros ms' (m' & E & MU & WM & ST').
      eexists _, (Z_to_bv 64 536364), m'. split; [exact E|].
      repeat (split; [reflexivity|]).
      split; [exact MU|]. split; [exact WM | exact ST']. }
  - intros R pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E24 & E25 & MU & WM & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (Fr24 : getr regs' 24 = Z_to_bv 64 s5) by (rewrite Hreg; exact E24).
    assert (Fr25 : getr regs' 25 = Z_to_bv 64 fr) by (rewrite Hreg; exact E25).
    assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    assert (HWsh : forall x, ~ LFr.outside W x -> Sfr fr + 328 <= x < Sfr fr + 365).
    { intros x Ho. unfold W in Ho. cbn [LFr.outside] in Ho.
      destruct (Z_le_gt_dec (Sfr fr + 328) x) as [H1|H1]; [|exfalso; apply Ho; split; [lia | exact I]].
      destruct (Z_lt_ge_dec x (Sfr fr + 365)) as [H2|H2]; [lia|exfalso; apply Ho; split; [lia | exact I]]. }
    assert (HWout : forall x, (x < Sfr fr + 328 \/ Sfr fr + 365 <= x) -> LFr.outside W x)
      by (intros x Hx; unfold W; cbn [LFr.outside]; split; [lia | exact I]).
    (* the 20 stores write shadow bytes only, all at or above GT: the read-only image bytes are kept. *)
    assert (HroM : ro_agree rsegs mem').
    { apply (sl_ro_keep W mem mem' Hro MU). intros x Hx. apply HWout. left.
      pose proof (HIS (Sfr fr) ltac:(lia)) as Hin0.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin0.
      assert (HGT0 : AC.GT = 0x5fe000) by reflexivity. lia. }
    (* AH, the runtime's ownership of an image byte, and the two stack bounds across the 20 shadow stores. *)
    assert (HAHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
                     (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a ->
                                AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a) /\
                     AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                     AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                     AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                     AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { destruct Hloc as [[Hs50 (Hspfr & Hreal)] | [Hs5fr (Hsep & Hfs & Hrec)]].
      - assert (HSOK : forall a, 0 <= a < 2 ^ 64 ->
          ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
          mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
        { intros a Ha Hns. apply MU. rewrite LMS.unsigned_lit by exact Ha.
          destruct (kb_outside_dec W a) as [Ho|Ho]; [exact Ho|].
          exfalso. apply Hns. pose proof (HWsh a Ho) as Hin.
          unfold AC.a_store_ok. right. right. right.
          exists (fr + 8 * (a - Sfr fr)). split.
          - unfold Sfr. rewrite x12_sh_of. reflexivity.
          - right. left. apply Hreal. unfold Sfr in *. lia. }
        destruct (AC.a_laws_store _ _ _ _ _ LAWS ([] ++ g_H g) mem mem' md HAH HSOK Hwm) as (H1 & H2 & H3 & H4).
        split; [exact H1|]. split; [intros a Ha; exact (proj2 (H2 a) Ha)|]. split; [exact H3 | exact H4].
      - destruct (x12_fs_base mem fr Hfs) as (FS & HwFS & HFSb & HFSlo & HFShi).
        destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS ([] ++ g_H g) mem md FS HAH HwFS HFSb)
          as (_ & _ & _ & HAPfs).
        assert (HFSsz : FS + AC.FS_SIZE <= 2 ^ 64).
        { pose proof (HAPfs (FS + AC.FS_SIZE - 1) ltac:(unfold AC.FS_SIZE; lia)) as Ha.
          unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. lia. }
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                          (exists b, mbyte rsegs mem' q = Some b)).
        { intros q Hq Hb. destruct (kb_outside_dec W q) as [Ho|Ho].
          - rewrite (KBG.mbyte_munch rsegs W mem mem' q MU Hq Ho). exact Hb.
          - pose proof (HWsh q Ho) as Hin. destruct ST' as (_ & _ & HST').
            destruct (HST' q ltac:(lia)) as (_ & b & Hbb). exists b. exact Hbb. }
        assert (Hmeta : forall q, TF.fs_meta FS q -> LFr.outside W q).
        { intros q Hm. destruct (kb_outside_dec W q) as [Ho|Ho]; [exact Ho|].
          exfalso. pose proof (TF.fs_meta_below FS q Hm) as Hb.
          assert (Hlo : FS <= q).
          { unfold TF.fs_meta, AC.a_fs_hint, AC.a_fs_flag, AC.a_fs_M in Hm.
            destruct Hm as [H|[H|[(c & Hc & Hr)|(c & j & Hc & Hj & Hq)]]]; [lia | lia | lia |].
            assert (P3 : 2 ^ (15 - Z.of_nat c) <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
            change (2 ^ 15) with 32768 in *. lia. }
          pose proof (HWsh q Ho) as Hin.
          assert (Happq : app_mem q) by (apply HAPfs; unfold AC.FS_SIZE in *; lia).
          exact (app_not_shadow q Happq (HIS q ltac:(lia))). }
        assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
          ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
          ~ (FS <= q < FS + AC.FS_SIZE) ->
          ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
          mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
        { intros q Hq Hns Hnfs Hnsh. apply MU. rewrite LMS.unsigned_lit by exact Hq.
          destruct (kb_outside_dec W q) as [Ho|Ho]; [exact Ho|].
          exfalso. pose proof (HWsh q Ho) as Hin. apply Hnsh.
          exists (fr + 8 * (q - Sfr fr)). split; [unfold Sfr in *; lia|].
          unfold Sfr. rewrite x12_sh_of. reflexivity. }
        destruct (TF.a_fs_ok_store_AH AC.ASYMS (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc))
                    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
                    W ([] ++ g_H g) mem mem' md FS LAWS HAH HwFS HFSb HFSsz MU Hwm Hpres Hmeta Hagree)
          as (H1 & H2 & H3 & H4).
        split; [exact H1|]. split; [intros a Ha; exact (proj2 (H2 a) Ha)|]. split; [exact H3 | exact H4]. }
    destruct HAHSTK as (HAH' & Howned & HSTKeq & HSTKhi).
    assert (Hshnew : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
    { exists (x12_rds mem' (Sfr fr) 392). split.
      - apply (x12_bytes_of_stk 392 mem' (Sfr fr) (Sfr fr + 392) ST'); cbn [Z.of_nat]; lia.
      - rewrite x12_rds_length, HFSv. reflexivity. }
    assert (Hrtdj : rt_disjoint W).
    { pose proof (HIS (Sfr fr) ltac:(lia)) as Hin0.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin0.
      unfold W, rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [left; lia | right; lia | exact I]. }
    assert (HFRA1 : FRA B APIf ra g fr [] regs' mem' md).
    { eapply (sl_fr_meta B APIf ra empty FF g fr [] regs regs' mem mem' md W HFRA MU WM HroM Hrtdj HAH' HSTKeq
                Happ HGT Hshnew).
      - intros x Hx Hnb Hnsh. apply HWout. unfold Sfr in *. lia.
      - intros A' HA' HA'b x Hx.
        assert (EA' : A' = A) by (apply (x12_eq_of_bv A A'); [rewrite <- HA'; exact Hr9 | exact HAb | exact HA'b]).
        subst A'. apply HWout. right. lia.
      - intros x Hx. apply HWout. right. lia.
      - intros A' HA' HA'b x Hx.
        assert (EA' : A' = A) by (apply (x12_eq_of_bv A A'); [rewrite <- HA'; exact Hr9 | exact HAb | exact HA'b]).
        subst A'. apply HWout. right. lia.
      - intros x Hx. left. apply HWout. right. unfold AF.SLOT_STACK in *. lia.
      - intros a Hin. apply (addr1_munch W mem mem' a MU); [|exact (HAG a Hin)].
        apply HWout. left.
        pose proof (x12_ag_lt a Hin) as Hlt.
        assert (Hle : a / 8 <= fr / 8) by (apply Z.div_le_mono; [lia | unfold AC.GT in *; lia]).
        unfold Sfr, shadow_addr in *. lia.
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26. }
    assert (HFRA2 : FRA B APIf ra g fr [] regs' mem' md').
    { eapply (sl_fra_move B APIf ra g fr [] regs' regs' mem' md md' HFRA1); try reflexivity; exact Hmat. }
    (* ENT across the same window: every byte W writes is one of the frame's 392 shadow bytes. *)
    assert (HENT1 : ENT APIf g [] mem' md).
    { eapply ent_store with (W := W);
        [ exact HENT | exact HFRA | exact MU
        | intros x Hx; destruct (kb_outside_dec W x) as [Ho|Ho]; [left; exact Ho|];
          right; right; right; pose proof (HWsh x Ho) as Hin; lia
        | exact HSTKeq | exact HSTKhi | intros a _ Hown; exact (Howned a Hown) ]. }
    assert (HENT2 : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
    assert (Hsel' : q64 mem' (A + 48) s5).
    { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
      rewrite length_le8. intros x Hx. apply HWout. right. lia. }
    assert (HJ : Inv_Jrel B APIf ra g (mkCfg (mkst regs' (Z_to_bv 64 536364) mem' (seg_rom rsegs)) md')).
    { exists regs', mem', md', fr, s5. rewrite SEGS.
      split; [reflexivity|].
      split.
      - apply (x12_FRAS_of_FRA g fr [] regs' mem' md' A s5 HFRA2); try assumption.
        unfold rg in *. rewrite Fr9. exact Hr9.
      - split; [exact HENT2|].
        split; [unfold rg; exact Fr24 | unfold rg; exact Fr25]. }
    pose proof (Hjrel g _ HJ) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

(* ---------------------------------------------------------------- the segments *)

(* S_X2 (forms-asan-ubsan-v190.md (a working note, not in this delivery); v1.9 cut names, Inv_B82ecc = v1.9 pc 0x82ecc,
   Inv_Jrel = v1.9 pc 0x82f2c). *)
Lemma seg_X2 : Hcut B APIf ra (Inv_Jrel B APIf ra) -> Hcut B APIf ra (Inv_B82ecc B APIf ra).
Proof.
  intros Hjrel g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & Hour & (q & Ha0 & Hq)).
  subst c.
  rewrite SEGS.
  assert (Hhalt : m_halted md = None)
    by (destruct HFRA as (A & sp & s5 & _ & _ & _ & _ & H & _); exact H).
  (* lazy run 0x82ecc -> 0x82ed0 (x12_x2_evt): no memory touched. *)
  apply (sl_run_lib regs (Z_to_bv 64 536268) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 536272 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26)
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold Regs6ss.mkR_of.
    eapply LE.evt_mono.
    { eapply x12_x2_evt with (q := q); [unfold a0v, rg in Ha0; exact Ha0 | exact Hq]. }
    { intros ms' E.
      eexists _, (Z_to_bv 64 536272), mem. split; [exact E|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. reflexivity. }
  - intros R pc' mem' regs' md' (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E19 & E26) Hreg Hmat.
    subst pc' mem'.
    assert (HFRA' : FRA B APIf ra g fr [] regs' mem md').
    { eapply (sl_fra_move B APIf ra g fr [] regs regs' mem md md' HFRA);
        [ rewrite Hreg; exact E2 | rewrite Hreg; exact E3 | rewrite Hreg; exact E4
        | rewrite Hreg; exact E8 | rewrite Hreg; exact E9 | rewrite Hreg; exact E19
        | rewrite Hreg; exact E26 | exact Hmat ]. }
    assert (HENT' : ENT APIf g [] mem md') by (eapply ent_mat; [exact HENT | exact Hmat]).
    exact (x12_tail g fr regs' mem md' Hjrel HFRA' HENT').
Qed.

(* S_X1 (forms-asan-ubsan-v190.md (a working note, not in this delivery); v1.9 cut names, Inv_B82eac = v1.9 pc 0x82eac). *)
Lemma seg_X1 : Hcut B APIf ra (Inv_B82ecc B APIf ra) -> Hcut B APIf ra (Inv_Jrel B APIf ra) ->
  Hcut B APIf ra (Inv_B82eac B APIf ra).
Proof.
  intros Hexit Hjrel g c HInv.
  pose proof FRAME_BYTES_val as HFBv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & Hour & H176 &
    (nm & Hnm & Hnml & Hfb) & Hadr).
  subst c.
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hapart & HfrA9 & Hfssep & Hfrw).
  pose proof (Hapart 2208 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as Hdisj.
  rewrite Haspz in Hdisj.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hwlo & Hwstk).
  rewrite Haspz in Hwlo, Hwstk.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS ([] ++ g_H g) mem md HAH) as Hhi.
  assert (HSb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (H1 & H2 & _); lia).
  assert (HAb : 0 <= A < 2 ^ 64) by (unfold AF.SLOT_STACK in HSb; lia).
  assert (HAhigh : HIGHMEM_BEG <= A) by (unfold AF.SLOT_STACK in *; lia).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (Hsphigh : HIGHMEM_BEG + 1044480 < sp) by lia.
  assert (HfrB : 0 <= fr) by (unfold AC.GT in HGT; lia).
  assert (HfrA : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. lia. }
  (* the record facts the official cut carries (adopt 8): the spill [A+176] (v1.8 [A+184]) read at the cut's own
     spill base A (the `spill` existential names the base only modulo 2^64; A is pinned by s1 and 0 <= A < 2^64) *)
  assert (H176q : q64 mem (A + 176) (fr + 2688)).
  { destruct H176 as (A' & HA' & Hq).
    assert (EA : A' = A).
    { pose proof (rg_eq64 _ _ _ _ HA' Hr9) as Hm.
      unfold q64, bytes_at in Hq. destruct Hq as (Hq0 & Hq1 & _).
      rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
      change (2 ^ 64) with 18446744073709551616 in *.
      Z.div_mod_to_equations. lia. }
    subst A'. exact Hq. }
  rewrite SEGS.
  assert (HL1 : length (firstn 1 (skipn 20 nm)) = 1%nat) by (rewrite length_firstn, length_skipn; lia).
  pose proof (x12_ba_sub mem (fr + 2688) nm 20 1 Hnm ltac:(lia)) as H20.
  destruct (firstn 1 (skipn 20 nm)) as [|b20 tl] eqn:E20; [cbn [length] in HL1; lia|].
  destruct tl as [|b21 tl2]; [|cbn [length] in HL1; lia].
  replace (fr + 2688 + Z.of_nat 20) with (fr + 2708) in H20 by lia.
  destruct (Z.eq_dec (bv_unsigned b20) 0) as [Hb0|Hbnz].
  - (* path B: byte 20 is 0; straight into the shadow fill *)
    (* lazy run 0x82eac -> 0x82ed0 (x12_b_evt): reads [A + 176, A + 184) and fr + 2708. *)
    apply (sl_run_lib regs (Z_to_bv 64 536236) mem md
      (fun R pc' mem' =>
         pc' = Z_to_bv 64 536272 /\ mem' = mem /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 26 = getr regs 26)
      (Post B APIf ra g)).
    + exact Hhalt.
    + unfold Regs6ss.mkR_of.
      eapply LE.evt_mono.
      { eapply x12_b_evt with (A := A) (fr := fr) (b20 := b20).
        - unfold rg in Hr9; exact Hr9.
        - unfold q64 in H176q; exact H176q.
        - exact H20.
        - exact Hb0. }
      { intros ms' E. eexists _, (Z_to_bv 64 536272), mem. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        repeat (split; [reflexivity|]). reflexivity. }
    + intros R pc' mem' regs' md' (Hpc & Hmem & E2 & E3 & E4 & E8 & E9 & E19 & E26) Hreg Hmat.
      subst pc' mem'.
      assert (HFRA' : FRA B APIf ra g fr [] regs' mem md').
      { eapply (sl_fra_move B APIf ra g fr [] regs regs' mem md md' HFRA);
          [ rewrite Hreg; exact E2 | rewrite Hreg; exact E3 | rewrite Hreg; exact E4
          | rewrite Hreg; exact E8 | rewrite Hreg; exact E9 | rewrite Hreg; exact E19
          | rewrite Hreg; exact E26 | exact Hmat ]. }
      assert (HENT' : ENT APIf g [] mem md') by (eapply ent_mat; [exact HENT | exact Hmat]).
      exact (x12_tail g fr regs' mem md' Hjrel HFRA' HENT').
  - (* path A: byte 20 is not 0; the memchr wrapper runs *)
    set (buf := firstn 17 (skipn 3 nm)).
    assert (HbufL : length buf = 17%nat) by (unfold buf; rewrite length_firstn, length_skipn; lia).
    pose proof (x12_ba_sub mem (fr + 2688) nm 3 17 Hnm ltac:(lia)) as Hbuf.
    replace (fr + 2688 + Z.of_nat 3) with (fr + 2691) in Hbuf by lia.
    fold buf in Hbuf. fold buf in Hfb.
    destruct (SF.find_byte 0 buf) as [j|] eqn:EF; [|exfalso; apply Hfb; first [reflexivity | exact EF]].
    pose proof (SF.find_byte_Some 0 buf j EF) as (Hjl & _ & _).
    pose proof (AsanRTInv.RT_shadow_rw sp mem md HRT) as HSW.
    pose proof (AsanRTInv.RT_cells sp mem md HRT) as HAC0.
    assert (HRM : bytes_at rsegs mem MW.REAL_MEMCHR (le8 (wa MC.MEMCHR))).
    { apply (real_cell_of mem MW.REAL_MEMCHR MC.MEMCHR (AsanRTInv.RT_real_cells sp mem md HRT));
        vm_compute; reflexivity. }
    (* lazy run 0x82eac -> 0x82ecc (x12_a_evt, through the memchr wrapper): reads [A + 176, A + 184), fr + 2708 and
       [fr + 2691, fr + 2708); writes the wrapper's window [sp - 2208, sp). *)
    apply (sl_run_lib regs (Z_to_bv 64 536236) mem md
      (fun R pc' mem' =>
         pc' = Z_to_bv 64 536268 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 26 = getr regs 26 /\ getr R 10 = Z_to_bv 64 (fr + 2691 + Z.of_nat j) /\
         munch [(sp - 2208, sp)] mem mem' /\ wmono rsegs mem mem' /\ ro_same rsegs mem mem' /\
         stk rsegs mem' (sp - FN_STACK) sp /\ asan_cells mem' /\ shadow_rw mem')
      (Post B APIf ra g)).
    + exact Hhalt.
    + unfold Regs6ss.mkR_of.
      eapply LE.evt_mono.
      { eapply (x12_a_evt HMW) with (A := A) (fr := fr) (b20 := b20) (buf := buf) (j := j)
          (lo := sp - FN_STACK) (spZ := sp).
        - unfold rg in Hr9; exact Hr9.
        - exact Haspz.
        - unfold q64 in H176q; exact H176q.
        - exact HfrB.
        - exact HfrA.
        - exact H20.
        - exact Hbnz.
        - exact Hbuf.
        - exact HbufL.
        - exact EF.
        - exact Hro.
        - exact Hadr.
        - exact Happ.
        - exact Hdisj.
        - exact Hwstk.
        - lia.
        - unfold HIGHMEM_BEG in *. lia.
        - unfold APPMEM_END in *. lia.
        - exact HAC0.
        - exact HSW.
        - exact HRM. }
      { intros ms' (x1 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m'
                    & E & MU & WM & RS & ST' & AC' & SW').
        eexists _, (Z_to_bv 64 536268), m'. split; [exact E|].
        repeat (split; [reflexivity|]).
        split; [exact MU|]. split; [exact WM|]. split; [exact RS|]. split; [exact ST'|].
        split; [exact AC' | exact SW']. }
    + intros R pc' mem' regs' md'
        (Hpc & E2 & E3 & E4 & E8 & E9 & E19 & E26 & E10 & MU & WM & RS & ST' & AC' & SW') Hreg Hmat.
      subst pc'.
      set (W := [(sp - 2208, sp)]) in MU.
      assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
      assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
      assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
      assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
      assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
      assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact E19).
      assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
      assert (Fr10 : getr regs' 10 = Z_to_bv 64 (fr + 2691 + Z.of_nat j)) by (rewrite Hreg; exact E10).
      assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
        by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
      assert (HWout : forall x, (x < sp - 2208 \/ sp <= x) -> LFr.outside W x)
        by (intros x Hx; unfold W; cbn [LFr.outside]; split; [lia | exact I]).
      assert (HWin : forall x, ~ LFr.outside W x -> sp - 2208 <= x < sp).
      { intros x Ho. unfold W in Ho. cbn [LFr.outside] in Ho.
        destruct (Z_le_gt_dec (sp - 2208) x) as [H1|H1]; [|exfalso; apply Ho; split; [lia | exact I]].
        destruct (Z_lt_ge_dec x sp) as [H2|H2]; [lia | exfalso; apply Ho; split; [lia | exact I]]. }
      assert (HSOK : forall a, 0 <= a < 2 ^ 64 ->
        ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
        mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { intros a Ha Hns. apply MU. rewrite LMS.unsigned_lit by exact Ha.
        destruct (kb_outside_dec W a) as [Ho|Ho]; [exact Ho|].
        exfalso. apply Hns. pose proof (HWin a Ho) as Hin.
        unfold AC.a_store_ok. right. left. unfold APPMEM_END in *. lia. }
      destruct (AC.a_laws_store _ _ _ _ _ LAWS ([] ++ g_H g) mem mem' md HAH HSOK Hwm)
        as (HAH' & Howned & HSTKeq & HSTKhi).
      (* FRA across the wrapper's own stack window: the canonical callee transport of Seg/Tac_slot. *)
      assert (HFRA2 : FRA B APIf ra g fr [] regs' mem' md').
      { eapply (sl_callee_keep B APIf ra empty FF g fr [] regs regs' mem mem' md md' 2208 HFRA).
        - rewrite Haspz. exact MU.
        - exact WM.
        - eapply sl_win_stk with (K := 2208);
            [ exact HFRA | unfold FN_STACK, AF.SLOT_STACK; lia | rewrite Haspz; exact MU | exact WM
            | rewrite Haspz; exact (proj2 (stk_split rsegs mem' (sp - FN_STACK) (sp - 2208) sp ST' ltac:(lia))) ].
        - unfold FN_STACK, AF.SLOT_STACK. lia.
        - rewrite Haspz. unfold APPMEM_END in *. lia.
        - rewrite Haspz. destruct Hdisj as [Hd|Hd]; lia.
        - exact HfrA.
        - exact Fr2.
        - exact Fr3.
        - exact Fr4.
        - exact Fr8.
        - exact Fr9.
        - exact Fr19.
        - exact Fr26.
        - exact Hmat. }
      assert (HENT1 : ENT APIf g [] mem' md).
      { eapply ent_store with (W := W);
          [ exact HENT | exact HFRA | exact MU
          | intros x Hx; destruct (kb_outside_dec W x) as [Ho|Ho]; [left; exact Ho|];
            right; left; pose proof (HWin x Ho) as Hin; unfold AF.SLOT_STACK in *; lia
          | exact HSTKeq | exact HSTKhi | intros a _ Hown; exact (proj2 (Howned a) Hown) ]. }
      assert (HENT2 : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
      assert (HIexit : Inv_B82ecc B APIf ra g (mkCfg (mkst regs' (Z_to_bv 64 536268) mem' (seg_rom rsegs)) md')).
      { exists regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
        split; [exact HFRA2|]. split; [exact HENT2|]. split; [exact Hn|].
        split.
        { unfold OURb in *. eapply fl_bytes; [exact Hour | exact MU |].
          rewrite OUR_length. intros x Hx. apply HWout. destruct Hdisj as [Hd|Hd]; lia. }
        exists (fr + 2691 + Z.of_nat j). split; [unfold a0v, rg; exact Fr10|].
        unfold APPMEM_END in HfrA. lia. }
      pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
