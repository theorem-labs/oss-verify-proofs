(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Tac.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Image.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Malloc.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require PropExec.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require MState.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Mem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Exec.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require ITree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Stdio.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require PState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MallocRep.

From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT}.
Definition CTX : Z := 0x1a188.
Definition MLOCK : Z := 0x1a0d0.
Definition LIBC : Z := 0x1a120.
Definition NEED_LOCKS : Z := 0x1a123.
Definition PAGE_SIZE_A : Z := 0x1a150.
Definition SIZE_CLASSES : Z := 0x18170.
Definition DEBRUIJN : Z := 0x18130.

Definition get_meta_entry : Z := 0x15970.
Definition malloc_entry : Z := 0x16c7c.
Definition free_entry : Z := 0x15e70.
Definition alloc_meta_entry : Z := 0x15fd4.
Definition alloc_slot_entry : Z := 0x162e0.
Definition nontrivial_free_entry : Z := 0x15a6c.
Definition mmap_entry : Z := 0x172d4.
Definition munmap_entry : Z := 0x173e4.
Definition mprotect_entry : Z := 0x1739c.
Definition unlock_entry : Z := 0x17b14.

Definition agent_reserved : list (Z * Z) := [(0x10000, 0x9000); (0x19000, 0x2000)].

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition b8 (z : Z) : byte := Z_to_bv 8 z.
Definition pw (st : mstate) (p : optr) : word := wz (oconc st p).

Definition meta_word (mr : meta) : Z :=
  m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr.

Definition meta_cells (st : mstate) (mr : meta) : list cell :=
  [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (pw st (m_mem mr));
   C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr))].

Definition brk_word (st : mstate) : Z :=
  match c_brk (ctx st) with
  | BrkUntried => 0
  | BrkDead => 2^64 - 1
  | BrkLive rid off => conc st (rid, off)
  end.

Definition ctx_head_cells (st : mstate) : list cell :=
  let c := ctx st in
  [C8 (wz (c_secret c)); C4 (wz (c_init_done c)); C4 (wz (c_mmap_counter c));
   C8 (pw st (c_free_meta_head c)); C8 (pw st (c_avail_meta c));
   C8 (wz (c_avail_meta_count c)); C8 (wz (c_avail_meta_area_count c)); C8 (wz (c_meta_alloc_shift c));
   C8 (pw st (c_meta_area_head c)); C8 (pw st (c_meta_area_tail c)); C8 (pw st (c_avail_meta_areas c))].

Definition actives (st : mstate) : list word := map (fun i => pw st (active st (Z.of_nat i))) (seq 0 48).
Definition usages (st : mstate) : list word := map (fun i => wz (usage st (Z.of_nat i))) (seq 0 48).
Definition unmap_seqs (st : mstate) : list byte := map (fun i => b8 (unmap_seq st (Z.of_nat i))) (seq 0 32).
Definition bouncess (st : mstate) : list byte := map (fun i => b8 (bounces st (Z.of_nat i))) (seq 0 32).
Definition zeros (n : nat) : list byte := repeat (b8 0) n.
Definition ctx_tail_cells (st : mstate) : list cell :=
  [C1 (b8 (c_seq (ctx st))); CB 7 (zeros 7); C8 (wz (brk_word st))].


Definition lr_lo (r : region) : Z :=
  match r_kind r with RKBrk => r_base r + 4096 | _ => r_base r end.

Lemma lr_lo_ge r : r_base r <= lr_lo r.
Proof. unfold lr_lo. destruct (r_kind r); lia. Qed.
Lemma lr_lo_group r : r_kind r = RKGroup -> lr_lo r = r_base r.
Proof. unfold lr_lo. intros ->. reflexivity. Qed.
Lemma lr_lo_nbrk r : r_kind r <> RKBrk -> lr_lo r = r_base r.
Proof. unfold lr_lo. destruct (r_kind r); congruence. Qed.

Section MREP.
Variable st : mstate.
Variable m : word -> option byte.

Definition regions_wf : Prop :=
  s_reserved st = agent_reserved
  /\ (forall rid r, (s_regions st) !! rid = Some r ->
        0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r
        /\ r_base r + round_up_pg (r_len r) <= ATOP
        /\ ranges_free agent_reserved (r_base r) (round_up_pg (r_len r)) = true)
  /\ (forall rid1 r1 rid2 r2, (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
        r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= lr_lo r1)
  /\ (forall a ar, (s_areas st) !! a = Some ar ->
        exists r, (s_regions st) !! (fst a) = Some r /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0
                  /\ r_kind r <> RKGroup /\ lr_lo r <= r_base r + snd a)
  /\ (forall b gh, (s_groups st) !! b = Some gh ->
        exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0).

End MREP.

Definition mrep_W (st : mstate) : list (Z * Z) :=
  (CTX, CTX + 928)
  :: map (fun kr : N * region => (r_base (snd kr), r_base (snd kr) + round_up_pg (r_len (snd kr)))) (map_to_list (s_regions st)).

Definition blocks_preserved (L : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall a, (exists bl, In bl L /\ fst bl <= a < fst bl + snd bl) -> m' (wa a) = m (wa a).


Lemma conc_aadd : forall st p d,
  is_Some ((s_regions st) !! (fst p)) -> conc st (aadd p d) = conc st p + d.
Proof.
  intros st [rid off] d [r Hr]. unfold conc, aadd, get_region. cbn. rewrite Hr. lia.
Qed.

Lemma conc_region : forall st rid off r,
  (s_regions st) !! rid = Some r -> conc st (rid, off) = r_base r + off.
Proof. intros. unfold conc, get_region. cbn. rewrite H. reflexivity. Qed.

Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros. unfold round_up_pg, PGSZ. assert (0 <= Z.land (-x) (4096 - 1)) by (apply Z.land_nonneg; right; lia). lia. Qed.

Lemma wz_unsigned x : 0 <= x < 2^64 -> bv_unsigned (wz x) = x.
Proof. intros. unfold wz. apply unsigned_lit. lia. Qed.
Lemma b8_unsigned x : 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof. intros. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.
Lemma zxb_b8 x : 0 <= x < 256 -> zxb (b8 x) = wz x.
Proof. intros. unfold zxb, wz. rewrite b8_unsigned by lia. reflexivity. Qed.
Lemma zx16_wz x : 0 <= x < 65536 -> zx16 (wz x) = wz x.
Proof. intros. unfold zx16, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx32_wz x : 0 <= x < 2^31 -> sx32 (wz x) = wz x.
Proof. intros. unfold sx32, wz. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

Lemma land_ldiff_distr x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_pgmask x : 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros Hx.
  assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12) with 4096. pose proof (Z.div_mod x 4096). lia.
Qed.

Lemma mod_mod_pow2 z a b : 0 <= a <= b -> (z mod 2^b) mod 2^a = z mod 2^a.
Proof. intros. apply Z.mod_mod_divide. exists (2^(b-a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma swrap32_mod32 z : (bv_swrap 32 z) mod 2^32 = z mod 2^32.
Proof.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  replace (z + 2^31 - 2^31) with z by lia. reflexivity.
Qed.

Lemma wrap32_sx32_wz a : 0 <= a < 2^32 -> bv_wrap 32 (bv_unsigned (sx32 (wz a))) = a.
Proof.
  intros Ha. unfold sx32, wz. rewrite (unsigned_lit a) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (2 ^ Z.of_N 32) with (2^32).
  rewrite (mod_mod_pow2 _ 32 64) by lia. rewrite swrap32_mod32. apply Z.mod_small. lia.
Qed.

Lemma bit_test_form a i : 0 <= a -> 0 <= i ->
  Z.land (bv_swrap 32 (Z.shiftr a i) mod 2^64) 1 = Z.b2z (Z.testbit a i).
Proof.
  intros Ha Hi. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia.
  rewrite Z.testbit_spec' by lia. rewrite <- Z.shiftr_div_pow2 by lia.
  rewrite (mod_mod_pow2 _ 1 64) by lia.
  rewrite <- (mod_mod_pow2 (bv_swrap 32 (a ≫ i)) 1 32) by lia. rewrite swrap32_mod32.
  rewrite (mod_mod_pow2 _ 1 32) by lia. reflexivity.
Qed.

Lemma signed_wz_small x : 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.

End CANSEC1.
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc end.


Section CANSEC2. Context {rc : runConstT}.
Lemma size_class_range sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros H. unfold size_class.
  assert (F : Forall (fun x => 1 <= x <= 8191) size_classes).
  { unfold size_classes. repeat (constructor; [lia|]). constructor. }
  apply (Forall_nth (fun x => 1 <= x <= 8191) size_classes); [exact F|]. cbn. lia.
Qed.


Lemma conc_region' : forall st (q : aptr) r,
  (s_regions st) !! (fst q) = Some r -> conc st q = r_base r + snd q.
Proof. intros st [rid off] r H. apply conc_region. exact H. Qed.

Definition meta_slot (st : mstate) (g : aptr) : Prop :=
  exists a ar k, (s_areas st) !! a = Some ar /\ 0 <= k < NSLOTS /\ g = aadd a (AREA_HDR + META_SIZE * k).

Lemma le2_lohi : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> le2 (wz (lo + 256 * hi)) = [b8 lo; b8 hi].
Proof.
  intros lo hi Hl Hh. unfold le2, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  f_equal; [apply Z_to_bv8_mod; rewrite <- Zplus_mod_idemp_r; replace (256 * hi) with (hi * 2^8) by lia; rewrite Z_mod_mult; rewrite Z.add_0_r; reflexivity|].
  f_equal. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace (lo + 256 * hi) with (lo + hi * 256) by lia. rewrite Z.div_add, Z.div_small by lia. reflexivity.
Qed.



Definition ticks_ok (st : mstate) : Prop :=
  (forall rid sh u hl ch, (s_shadow st) !! rid = Some sh -> (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= s_tick st)%N)
  /\ (forall rid sh pg t, (s_shadow st) !! rid = Some sh -> (r_havp sh) !! pg = Some t -> (t <= s_tick st)%N).


Lemma reserved_disjoint : forall b n, ranges_free agent_reserved b n = true ->
  (b + n <= 0x10000 \/ 0x19000 <= b) /\ (b + n <= 0x19000 \/ 0x1b000 <= b).
Proof.
  intros b n H. unfold ranges_free, agent_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

Definition wr_in (st : mstate) (rid : N) (a len : Z) : Prop :=
  exists r, (s_regions st) !! rid = Some r /\ lr_lo r <= a /\ a + len <= r_base r + round_up_pg (r_len r) /\ 0 <= len.

Lemma wr_in_image : forall st rid a len,
  regions_wf st -> wr_in st rid a len ->
  (a + len <= 0x19000 \/ 0x1b000 <= a) /\ 0 <= a /\ a + len <= 2^64.
Proof.
  intros st rid a len (_ & WR & _) (r & Hr & H1 & H2 & H3).
  destruct (WR rid r Hr) as (B0 & _ & L0 & BC & RF). atop_facts.
  destruct (reserved_disjoint _ _ RF) as [_ D2]. pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r). lia.
Qed.

Lemma wr_in_other : forall st rid a len rid' r',
  regions_wf st -> wr_in st rid a len -> (s_regions st) !! rid' = Some r' -> rid' <> rid ->
  a + len <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= a.
Proof.
  intros st rid a len rid' r' (_ & _ & DJ & _) (r & Hr & H1 & H2 & H3) Hr' Hne.
  destruct (DJ rid r rid' r' Hr Hr' ltac:(congruence)); lia.
Qed.

Lemma area_lr_lo : forall st a ar r, regions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
  lr_lo r <= r_base r + snd a.
Proof.
  intros st a ar r (_ & _ & _ & WA & _) Ha Hr. destruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO).
  rewrite Hr in Hr0. inversion Hr0; subst. exact LO.
Qed.

Lemma regions_disjoint_full : forall st rid1 r1 rid2 r2,
  regions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
  r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk ->
  r_base r1 + round_up_pg (r_len r1) <= r_base r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof.
  intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1 K2.
  pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_nbrk r1 K1), (lr_lo_nbrk r2 K2) in X. exact X.
Qed.

Lemma regions_disjoint_grp : forall st rid1 r1 rid2 r2,
  regions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
  r_kind r1 = RKGroup ->
  r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof.
  intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1.
  pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_group r1 K1) in X. exact X.
Qed.

Lemma area_conc : forall st a ar, regions_wf st -> (s_areas st) !! a = Some ar ->
  exists r, (s_regions st) !! (fst a) = Some r /\ conc st a = r_base r + snd a
            /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0 /\ r_kind r <> RKGroup
            /\ 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= ATOP.
Proof.
  intros st a ar (_ & WR & _ & WA & _) Ha. destruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _).
  destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _).
  exists r. rewrite (conc_region' st a r Hr). repeat split; auto.
Qed.

Lemma group_conc : forall st b gh, regions_wf st -> (s_groups st) !! b = Some gh ->
  exists r, (s_regions st) !! (fst b) = Some r /\ conc st b = r_base r + snd b
            /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0
            /\ 0 < r_base r /\ r_base r + round_up_pg (r_len r) <= ATOP.
Proof.
  intros st b gh (_ & WR & _ & _ & WG) Hb. destruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL).
  destruct (WR _ r Hr) as (R0 & _ & _ & RC & _).
  exists r. rewrite (conc_region' st b r Hr). repeat split; auto.
Qed.

Lemma s_shadow_wr8 : forall st p v,
  s_shadow (wr8 p v st) =
  <[fst p := mkShadow (<[snd p := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst p)))) (r_hav (get_shadow st (fst p))) (r_havp (get_shadow st (fst p)))]> (s_shadow st).
Proof. intros. reflexivity. Qed.

Lemma get_shadow_unfold : forall st rid, get_shadow st rid = default shadow0 ((s_shadow st) !! rid).
Proof. reflexivity. Qed.

Lemma get_shadow_wr8_same : forall st p v,
  get_shadow (wr8 p v st) (fst p) =
  mkShadow (<[snd p := (Z.land v 255, s_tick st)]> (r_cells (get_shadow st (fst p)))) (r_hav (get_shadow st (fst p))) (r_havp (get_shadow st (fst p))).
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_eq. reflexivity. Qed.

Lemma get_shadow_wr8_other : forall st p v rid, rid <> fst p ->
  get_shadow (wr8 p v st) rid = get_shadow st rid.
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cell_read_wr8_other : forall st p v o, o <> snd p ->
  cell_read (get_shadow (wr8 p v st) (fst p)) o = cell_read (get_shadow st (fst p)) o.
Proof. intros. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cell_read_wr8_same : forall st p v,
  ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 p v st) (fst p)) (snd p) = Known v.
Proof.
  intros st p v [T1 T2] Hv. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_eq.
  replace (Z.land v 255) with v by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  unfold get_shadow. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn.
  - assert (SP : stale_pg (r_havp sh !! (snd p `div` 4096)) (Some (s_tick st)) = false).
    { unfold stale_pg. destruct (r_havp sh !! (snd p `div` 4096)) eqn:E2; [|reflexivity].
      apply N.ltb_ge. eapply T2; eauto. }
    assert (SU : stale (default [] (r_hav sh !! (snd p `div` 16))) (snd p `mod` 16) (Some (s_tick st)) = false).
    { unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. intros ([cov t] & Hin & Hb).
      destruct (r_hav sh !! (snd p `div` 16)) eqn:E3; cbn in Hin; [|contradiction].
      apply Bool.andb_true_iff in Hb. destruct Hb as [_ Hb]. apply N.ltb_lt in Hb.
      pose proof (T1 _ _ _ _ _ E E3 Hin) as HT. cbn [snd] in HT. exfalso. apply (N.lt_irrefl t). eapply N.le_lt_trans; [exact HT | exact Hb]. }
    rewrite SP, SU. reflexivity.
  - rewrite lookup_empty. cbn. reflexivity.
Qed.

Lemma ticks_ok_wr8 : forall st p v, ticks_ok st -> ticks_ok (wr8 p v st).
Proof.
  intros st p v [T1 T2]. split.
  - intros rid sh u hl ch Hs Hu Hin. cbn [s_tick wr8 upd_shadow set_shadow] in *.
    rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
    + rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hu.
      unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hu.
      * eapply T1; eauto.
      * rewrite lookup_empty in Hu. discriminate.
    + rewrite lookup_insert_ne in Hs by congruence. eapply T1; eauto.
  - intros rid sh pg t Hs Hp. cbn [s_tick wr8 upd_shadow set_shadow] in *.
    rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
    + rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hp.
      unfold get_shadow in Hp. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hp.
      * eapply T2; eauto.
      * rewrite lookup_empty in Hp. discriminate.
    + rewrite lookup_insert_ne in Hs by congruence. eapply T2; eauto.
Qed.

Lemma wr8_mod : forall st p v, wr8 p v st = wr8 p (v mod 256) st.
Proof.
  intros. unfold wr8, upd_shadow. cbn beta.
  replace (Z.land (v mod 256) 255) with (Z.land v 255); [reflexivity|].
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le2_split : forall v, 0 <= v < 65536 -> le2 (wz v) = [b8 (v mod 256); b8 (v / 256)].
Proof.
  intros v Hv. replace v with (v mod 256 + 256 * (v / 256)) at 1 by (pose proof (Z.div_mod v 256); lia).
  rewrite le2_lohi; [reflexivity| |]; [pose proof (Z.mod_pos_bound v 256); lia | split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]].
Qed.


Lemma get_meta_rec_upd : forall st g f g',
  get_meta_rec (upd_meta g f st) g' = if aptr_eqb g' g then f (get_meta_rec st g) else get_meta_rec st g'.
Proof.
  intros. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn [s_metas set_metas].
  unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
  destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
    first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma aptr_eqb_refl : forall g, aptr_eqb g g = true.
Proof. intros [a b]. unfold aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

Lemma map_seq_upd : forall {X} (f g : nat -> X) (j : nat) (x : X) n s,
  (forall i, (s <= i < s + n)%nat -> g i = if Nat.eqb i j then x else f i) ->
  (s <= j)%nat ->
  map g (seq s n) = upd (map f (seq s n)) (j - s) x.
Proof.
  intros X f g j x n. induction n as [|n IH]; intros s Hg Hj; [reflexivity|].
  cbn [seq map]. destruct (Nat.eq_dec j s) as [->|NE].
  - rewrite Nat.sub_diag. cbn [upd]. rewrite Hg by lia. rewrite Nat.eqb_refl. f_equal.
    apply map_ext_in. intros i Hi. apply in_seq in Hi. rewrite Hg by lia.
    destruct (Nat.eqb_spec i s); [lia|reflexivity].
  - replace (j - s)%nat with (S (j - S s)) by lia. cbn [upd]. f_equal.
    + rewrite Hg by lia. destruct (Nat.eqb_spec s j); [lia|reflexivity].
    + apply IH; [intros; apply Hg; lia|lia].
Qed.

Lemma active_set_active : forall st sc v i,
  active (set_active sc v st) i = if Z.eqb i sc then v else active st i.
Proof.
  intros. unfold active, set_active, upd_ctx. cbn [ctx s_ctx c_active set_active_map].
  destruct v as [p|]; destruct (Z.eqb_spec i sc); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
  - rewrite lookup_delete_eq. reflexivity.
  - rewrite lookup_delete_ne by congruence. reflexivity.
Qed.

Lemma actives_set_active : forall st sc v, 0 <= sc < 48 ->
  actives (set_active sc v st) = upd (actives st) (Z.to_nat sc) (pw st v).
Proof.
  intros st sc v Hsc. unfold actives.
  replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
  apply (map_seq_upd (fun i => pw st (active st (Z.of_nat i))) (fun i => pw (set_active sc v st) (active (set_active sc v st) (Z.of_nat i)))); [|lia].
  intros i Hi. rewrite active_set_active.
  assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
  rewrite Hpw. destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

Definition sh_ticks (sh : shadow) (t : N) : Prop :=
  (forall u hl ch, (r_hav sh) !! u = Some hl -> In ch hl -> (snd ch <= t)%N)
  /\ (forall pg t', (r_havp sh) !! pg = Some t' -> (t' <= t)%N).

Definition shadow_le (sh sh' : shadow) : Prop :=
  r_cells sh' = r_cells sh /\ forall o v, cell_read sh' o = Known v -> cell_read sh o = Known v.

Lemma shadow_le_refl : forall sh, shadow_le sh sh. Proof. intros; split; auto. Qed.
Lemma shadow_le_trans : forall a b c, shadow_le a b -> shadow_le b c -> shadow_le a c.
Proof. intros a b c [E1 H1] [E2 H2]. split; [congruence|]. eauto. Qed.

Lemma In_filter_bool : forall {A} (f : A -> bool) (l : list A) x,
  In x (filter (fun y => f y) l) <-> In x l /\ f x = true.
Proof.
  intros A f l x. rewrite <- !list_elem_of_In. rewrite list_elem_of_filter.
  unfold Is_true. destruct (f x); intuition congruence.
Qed.

Lemma stale_hav_add : forall hl cov t b tc,
  (forall ch, In ch hl -> (snd ch <= t)%N) ->
  stale (hav_add cov t hl) b tc = false -> stale hl b tc = false.
Proof.
  intros hl cov t b tc Ht Hs. unfold stale in *.
  apply Bool.not_true_iff_false. apply Bool.not_true_iff_false in Hs. rewrite existsb_exists in *.
  intros ([c' h'] & Hin & Hb). apply Hs. cbn [fst snd] in Hb.
  apply Bool.andb_true_iff in Hb. destruct Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1.
  destruct (Z.ltb_spec cov c').
  - exists (c', h'). split; [|cbn [fst snd]; rewrite (proj2 (Z.ltb_lt _ _) Hb1), Hb2; reflexivity].
    unfold hav_add. right. apply In_filter_bool. split; [exact Hin|]. cbn. apply Z.ltb_lt. assumption.
  - exists (cov, t). split; [unfold hav_add; left; reflexivity|]. cbn [fst snd].
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
    destruct tc as [tc|]; [|reflexivity]. apply N.ltb_lt. apply N.ltb_lt in Hb2.
    pose proof (Ht _ Hin) as Hh. cbn [snd] in Hh. eapply N.lt_le_trans; [exact Hb2|exact Hh].
Qed.

Lemma hav_unit_step : forall cells hav havp u cov t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells (<[u := hav_add cov t (default [] (hav !! u))]> hav) havp)
  /\ sh_ticks (mkShadow cells (<[u := hav_add cov t (default [] (hav !! u))]> hav) havp) t.
Proof.
  intros cells hav havp u cov t [T1 T2]. cbn [r_hav r_havp] in T1, T2.
  assert (Hl : forall ch, In ch (default [] (hav !! u)) -> (snd ch <= t)%N).
  { intros ch Hin. destruct (hav !! u) eqn:E2; cbn in Hin; [eapply T1; eauto| contradiction]. }
  split.
  - split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
    destruct (Z.eq_dec (o / 16) u) as [E|NE].
    + rewrite E, lookup_insert_eq in Hc. cbn [default from_option id] in Hc. rewrite E.
      destruct (cells !! o) as [[v0 tc]|].
      * destruct (stale_pg (havp !! (o / 4096)) (Some tc)) eqn:SP; [cbn in Hc; discriminate|].
        destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) (Some tc)) eqn:SU; [cbn in Hc; discriminate|].
        rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
      * destruct (stale_pg (havp !! (o / 4096)) None) eqn:SP; [cbn in Hc; discriminate|].
        destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) None) eqn:SU; [cbn in Hc; discriminate|].
        rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
    + rewrite lookup_insert_ne in Hc by congruence. exact Hc.
  - split; cbn [r_hav r_havp]; [|exact T2].
    intros u' hl ch Hu Hin. destruct (Z.eq_dec u' u) as [->|NE].
    + rewrite lookup_insert_eq in Hu. inversion Hu; subst hl. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
      apply In_filter_bool in Hin. destruct Hin as [Hin _]. apply Hl. exact Hin.
    + rewrite lookup_insert_ne in Hu by congruence. eapply T1; eauto.
Qed.

Lemma hav_page_step : forall cells hav havp pg t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells hav (<[pg := t]> havp))
  /\ sh_ticks (mkShadow cells hav (<[pg := t]> havp)) t.
Proof.
  intros cells hav havp pg t [T1 T2]. cbn [r_hav r_havp] in T1, T2. split.
  - split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
    destruct (Z.eq_dec (o / 4096) pg) as [E|NE].
    + rewrite E, lookup_insert_eq in Hc. rewrite E.
      destruct (cells !! o) as [[v0 tc]|]; cbn [stale_pg orb] in Hc.
      * destruct (N.ltb_spec tc t); [discriminate|].
        destruct (havp !! pg) as [h|] eqn:E2; cbn [stale_pg].
        -- pose proof (T2 _ _ E2). replace (tc <? h)%N with false by (symmetry; apply N.ltb_ge; lia). exact Hc.
        -- exact Hc.
      * discriminate.
    + rewrite lookup_insert_ne in Hc by congruence. exact Hc.
  - split; cbn [r_hav r_havp]; [exact T1|].
    intros pg' t' Hp. destruct (Z.eq_dec pg' pg) as [->|NE].
    + rewrite lookup_insert_eq in Hp. inversion Hp; subst. lia.
    + rewrite lookup_insert_ne in Hp by congruence. eapply T2; eauto.
Qed.

Lemma Z_iter_invariant : forall {A} (f : A -> A) (Inv : A -> Prop) n x,
  (forall y, Inv y -> Inv (f y)) -> Inv x -> Inv (Z.iter n f x).
Proof.
  intros A f Inv n x Hf Hx. destruct n; cbn; auto. apply Pos.iter_invariant; auto.
Qed.

Lemma havoc_units_le : forall cells hav havp x y t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells (havoc_units x y t hav) havp)
  /\ sh_ticks (mkShadow cells (havoc_units x y t hav) havp) t.
Proof.
  intros cells hav havp x y t T. unfold havoc_units.
  set (f := fun acc : Z * gmap Z (list (Z * N)) => _).
  apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells (snd acc) havp)
                                         /\ sh_ticks (mkShadow cells (snd acc) havp) t)).
  - intros [u h] [HL HT]. unfold f. cbn [fst snd].
    destruct (hav_unit_step cells h havp u (if u =? (y - 1) / 16 then (let r := y mod 16 in if r =? 0 then 16 else r) else 16) t HT) as [HL2 HT2].
    split; [eapply shadow_le_trans; eauto| exact HT2].
  - cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

Lemma havoc_pages_le : forall cells hav havp p0 p1 t,
  sh_ticks (mkShadow cells hav havp) t ->
  shadow_le (mkShadow cells hav havp) (mkShadow cells hav (havoc_pages p0 p1 t havp))
  /\ sh_ticks (mkShadow cells hav (havoc_pages p0 p1 t havp)) t.
Proof.
  intros cells hav havp p0 p1 t T. unfold havoc_pages.
  set (f := fun acc : Z * gmap Z N => _).
  apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells hav (snd acc))
                                         /\ sh_ticks (mkShadow cells hav (snd acc)) t)).
  - intros [pg h] [HL HT]. unfold f. cbn [fst snd].
    destruct (hav_page_step cells hav h pg t HT) as [HL2 HT2].
    split; [eapply shadow_le_trans; eauto| exact HT2].
  - cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

Lemma sh_ticks_of_ticks_ok : forall st rid, ticks_ok st -> sh_ticks (get_shadow st rid) (s_tick st).
Proof.
  intros st rid [T1 T2]. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
  - split; [intros; eapply T1; eauto | intros; eapply T2; eauto].
  - split; cbn; intros; rewrite lookup_empty in *; discriminate.
Qed.

Definition W_high (W : list (Z * Z)) : Prop := forall lo hi, In (lo, hi) W -> ATOP <= lo.

Lemma W_high_disjoint : forall W a n, W_high W -> a + n <= ATOP -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Hn; cbn; [exact I|].
  split. { left. pose proof (HW lo hi ltac:(left; reflexivity)). lia. }
  apply IH; [| exact Hn]. intros lo' hi' Hin. apply (HW lo' hi'). right; exact Hin.
Qed.

Lemma ticks_ok_set_tick : forall st t, (s_tick st <= t)%N -> ticks_ok st -> ticks_ok (set_tick t st).
Proof.
  intros st t Ht [T1 T2]. split; cbn.
  - intros rid sh u hl ch H1 H2 H3. pose proof (T1 rid sh u hl ch H1 H2 H3). lia.
  - intros rid sh pg t' H1 H2. pose proof (T2 rid sh pg t' H1 H2). lia.
Qed.

Lemma malloc_impl_spec_statement : True. Proof. exact I. Qed.

Lemma free_trivial_spec_statement : True. Proof. exact I. Qed.

Lemma wrappers_spec_statement : True. Proof. exact I. Qed.


End CANSEC2.
End MallocRep.

Module F_malloc_free.

From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MallocRep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AGP : Z := 0x1a800.


Definition sxv (v : Z) : Z := (bv_swrap 32 v) mod 2^64.

Lemma sxv_range v : 0 <= sxv v < 2^64.
Proof. unfold sxv. apply Z.mod_pos_bound. lia. Qed.

Lemma swrap32_eq' z : bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.

End CANSEC1.
Ltac pow_lits :=
  change (2^64)%Z with 18446744073709551616%Z in *;
  change (2^63)%Z with 9223372036854775808%Z in *;
  change (2^33)%Z with 8589934592%Z in *;
  change (2^32)%Z with 4294967296%Z in *;
  change (2^31)%Z with 2147483648%Z in *.
Ltac mlia := pow_lits; Z.div_mod_to_equations; lia.

Section CANSEC2. Context {rc : runConstT}.
Lemma sxv_small v : 0 <= v < 2^31 -> sxv v = v.
Proof. intros. unfold sxv. rewrite swrap32_eq'. rewrite (Z.mod_small (v + 2^31)) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma mod64_mod32 z : (z mod 2^64) mod 2^32 = z mod 2^32.
Proof. apply mod_mod_pow2. lia. Qed.

Lemma sxv_mod32 v : (sxv v) mod 2^32 = v mod 2^32.
Proof. unfold sxv. rewrite mod64_mod32, swrap32_eq'. mlia. Qed.

Lemma sx32_wz_sxv v : 0 <= v < 2^64 -> sx32 (wz v) = wz (sxv v).
Proof. intros. unfold sx32, sxv. rewrite wz_unsigned by lia. unfold wz. rewrite Z_to_bv_mod64. reflexivity. Qed.

Lemma sextw_sxv v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)) + 0)) = wz (sxv v).
Proof.
  rewrite wz_unsigned by (apply sxv_range). rewrite Z.add_0_r. unfold wz, sxv.
  rewrite <- (Z_to_bv_mod64 (bv_swrap 32 (bv_swrap 32 v mod 2^64))). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.
Lemma sextw_sxv' v : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv v)))) = wz (sxv v).
Proof. rewrite <- (Z.add_0_r (bv_unsigned _)). apply sextw_sxv. Qed.

Lemma self_word b3 : 0 <= b3 < 256 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (zxb (b8 b3))) 31)) mod 32)))
  = wz (sxv (2 ^ (Z.land b3 31))).
Proof.
  intros. rewrite zxb_b8, (wz_unsigned b3) by lia.
  assert (0 <= Z.land b3 31 < 32).
  { split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma all_word mword : 0 <= mword ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (mword mod 32)))) + -1))
  = wz (sxv (2 ^ (mword mod 32 + 1) - 1)).
Proof.
  intros. rewrite unsigned_lit_wrap. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  replace (2 * 2 ^ (mword mod 32)) with (2 ^ (mword mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
  unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  set (y := 2 ^ (mword mod 32 + 1)). rewrite !swrap32_eq'. mlia.
Qed.

Lemma lor_range64 a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lor a b < 2^64.
Proof. intros. apply (zr_lor a b); unfold inr64; lia. Qed.

Lemma land_range64 a b : 0 <= a < 2^64 -> 0 <= b -> 0 <= Z.land a b < 2^64.
Proof. intros. apply (zr_land_l a b); unfold inr64; lia. Qed.

Lemma sxv_testbit_lo v i : 0 <= v < 2^32 -> 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
  intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

Lemma sxv_cases v : 0 <= v < 2^32 -> (v < 2^31 /\ sxv v = v) \/ (2^31 <= v /\ sxv v = v + 2^64 - 2^32).
Proof.
  intros. unfold sxv. rewrite swrap32_eq'.
  destruct (Z.lt_ge_cases v (2^31)); [left|right]; split; auto; pow_lits; Z.div_mod_to_equations; nia.
Qed.

Lemma free_assert_ok freed avail idx :
  0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= idx < 32 ->
  Z.testbit freed idx = false -> Z.testbit avail idx = false ->
  Z.land (sxv (2^idx)) (Z.lor (sxv freed) (sxv avail)) = 0.
Proof.
  intros HF HA HI TF TA.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64).
  2:{ rewrite (Z.bits_above_log2 (sxv (2^idx))); [reflexivity| apply sxv_range |].
      pose proof (sxv_range (2^idx)). destruct (Z.eq_dec (sxv (2^idx)) 0) as [->|]. cbn; lia.
      apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia]. }
  destruct (Z.lt_ge_cases idx 31).
  - rewrite (sxv_small (2^idx)) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    rewrite Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec idx n); [|reflexivity]. subst n. cbn.
    rewrite !sxv_testbit_lo by lia. rewrite TF, TA. reflexivity.
  - assert (idx = 31) by lia. subst idx.
    assert (Hlt : forall v, 0 <= v < 2^32 -> Z.testbit v 31 = false -> v < 2^31).
    { intros v Hv Hb. destruct (Z.lt_ge_cases v (2^31)); auto.
      exfalso. assert (Z.testbit v 31 = true); [|congruence].
      rewrite Z.testbit_true by lia. replace (v / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity. }
    pose proof (Hlt freed HF TF). pose proof (Hlt avail HA TA).
    rewrite (sxv_small freed), (sxv_small avail) by lia.
    destruct (Z.lt_ge_cases n 31).
    + replace (Z.testbit (sxv (2^31)) n) with false; [reflexivity|].
      symmetry. rewrite sxv_testbit_lo by lia. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
    + assert (Lg : forall v, 0 <= v < 2^31 -> Z.testbit v n = false).
      { intros v Hv. destruct (Z.eq_dec v 0) as [->|]. apply Z.bits_0.
        apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 31); [apply Z.log2_lt_pow2; lia| lia]. }
      rewrite (Lg freed), (Lg avail) by lia. apply andb_false_r.
Qed.

Lemma sxv_zero v : 0 <= v < 2^32 -> sxv v = 0 <-> v = 0.
Proof. intros. destruct (sxv_cases v H) as [[? ->]|[? ->]]; lia. Qed.

Lemma add_bit_nocarry v idx : 0 <= v < 2^32 -> 0 <= idx < 32 -> Z.testbit v idx = false ->
  v + 2^idx < 2^32.
Proof.
  intros Hv Hi Hb.
  assert (HL : Z.land v (2^idx) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec idx n); [subst; rewrite Hb; reflexivity | apply andb_false_r]. }
  rewrite (Z.add_nocarry_lxor _ _ HL).
  assert (0 <= 2^idx < 2^32) by (split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
  apply Z_bounded_by_bits; [lia | apply Z.lxor_nonneg; lia |].
  intros k Hk. rewrite Z.lxor_spec, (Z_testbit_high 32 v k), (Z_testbit_high 32 (2^idx) k) by lia. reflexivity.
Qed.

Lemma sxv_congr v w : v mod 2^32 = w mod 2^32 -> sxv v = sxv w.
Proof. intros E. unfold sxv. rewrite !swrap32_eq'. f_equal. f_equal. rewrite <- Zplus_mod_idemp_l, E, Zplus_mod_idemp_l. reflexivity. Qed.

Lemma lor_sxv_mod32 f a : 0 <= f < 2^32 -> 0 <= a < 2^32 ->
  (Z.lor (sxv f) (sxv a)) mod 2^32 = Z.lor f a.
Proof.
  intros. rewrite <- zb_land_mask, zb_land_lor_distr_l, !zb_land_mask, !sxv_mod32, !Z.mod_small by lia. reflexivity.
Qed.

Lemma addw_word x y : Z_to_bv 64 (bv_swrap 32 (x + y)) = wz (sxv (x + y)).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Lemma wz_inj a b : 0 <= a < 2^64 -> 0 <= b < 2^64 -> wz a = wz b -> a = b.
Proof. intros Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !wz_unsigned in E by lia. exact E. Qed.

Lemma sxv_eq_iff v w : sxv v = sxv w <-> v mod 2^32 = w mod 2^32.
Proof. split; [| apply sxv_congr]. intros E. rewrite <- (sxv_mod32 v), <- (sxv_mod32 w), E. reflexivity. Qed.

Lemma free_all_test freed avail idx li :
  0 <= freed < 2^32 -> 0 <= avail < 2^32 -> 0 <= idx <= li -> li < 32 ->
  (sxv (sxv (2^idx) + Z.lor (sxv freed) (sxv avail)) = sxv (2^(li + 1) - 1)
   <-> Z.lor freed avail + 2^idx = 2^(li+1) - 1).
Proof.
  intros HF HA HI HL. rewrite sxv_eq_iff.
  rewrite <- Zplus_mod_idemp_r, lor_sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32 by lia.
  assert (X1 : 0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
  assert (XY : 2^idx < 2^(li+1)) by (apply Z.pow_lt_mono_r; lia).
  assert (Y32 : 2^(li+1) <= 2^32) by (apply Z.pow_le_mono_r; lia).
  pose proof (Z_lor_range freed avail ltac:(lia) ltac:(lia)).
  assert (HLr : Z.lor freed avail < 2^32).
  { apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |]. intros k Hk.
    rewrite Z.lor_spec, (Z_testbit_high 32 freed k), (Z_testbit_high 32 avail k) by lia. reflexivity. }
  set (X := 2^idx) in *. set (Y := 2^(li+1)) in *. set (L := Z.lor freed avail) in *.
  clearbody X Y L. rewrite (Z.mod_small X) by lia. mlia.
Qed.

Lemma le4_congr (a b : word) : bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> le4 a = le4 b.
Proof. intros E. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia). rewrite E. reflexivity. Qed.

Lemma free_store_val freed idx : 0 <= freed < 2^32 -> 0 <= idx < 32 -> Z.testbit freed idx = false ->
  le4 (wz (sxv (sxv (2^idx) + sxv freed))) = le4 (wz (freed + 2^idx)).
Proof.
  intros. pose proof (add_bit_nocarry freed idx ltac:(lia) ltac:(lia) ltac:(assumption)).
  assert (0 < 2^idx) by (apply Z.pow_pos_nonneg; lia).
  apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
  rewrite sxv_mod32, <- Zplus_mod_idemp_r, sxv_mod32, <- Zplus_mod_idemp_l, sxv_mod32, !Z.mod_small by lia. lia.
Qed.

Lemma self_word' b3 : 0 <= b3 < 256 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 1 (bv_unsigned (Z_to_bv 64 (Z.land b3 31)) mod 32)))
  = wz (sxv (2 ^ (Z.land b3 31))).
Proof.
  intros.
  assert (0 <= Z.land b3 31 < 32).
  { split. apply Z.land_nonneg; lia. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  rewrite (wz_unsigned (Z.land b3 31)) by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_1_l.
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma sllw2_word e : 0 <= e ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftl 2 (e mod 32))) = wz (sxv (2 ^ (e mod 32 + 1))).
Proof.
  intros. rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
  replace (2 * 2 ^ (e mod 32)) with (2 ^ (e mod 32 + 1)) by (rewrite Z.pow_add_r by (try apply Z.mod_pos_bound; lia); lia).
  unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity.
Qed.

Lemma addiw_m1_word y : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv y)) + -1)) = wz (sxv (y - 1)).
Proof.
  rewrite wz_unsigned by (apply sxv_range). unfold wz, sxv. rewrite <- (Z_to_bv_mod64 (bv_swrap 32 _)). f_equal.
  rewrite !swrap32_eq'. mlia.
Qed.

Lemma rw_cells_congr segs m A cs cs' :
  cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' -> cells_wf cs' ->
  rw_cells segs m A cs -> rw_cells segs m A cs'.
Proof. intros EB ES WF [[_ B] W]. split; [split; [exact WF| rewrite <- EB; exact B] | rewrite <- ES; exact W]. Qed.

Lemma le1_neg1 : le1 (Z_to_bv 64 (-1)) = [b8 255].
Proof. cbn. f_equal. apply bv_eq. vm_compute. reflexivity. Qed.



End CANSEC2.
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          let E := fresh "EQ" m' in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
          clear HB; try rename H' into H
        end
    end
  end.

Section CANSEC3. Context {rc : runConstT}.
Definition frozen (P : Prop) : Prop := P.

Definition free_W (sp : word) (P G : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.

End CANSEC3.
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.


Section CANSEC4. Context {rc : runConstT}.
Lemma wr_at_sub : forall segs m A n A' n',
  wr_at segs m A n -> A <= A' -> A' + n' <= A + n -> wr_at segs m A' n'.
Proof.
  intros segs m A n A' n' (H0 & H1 & H) LA LB. split; [lia|]. split; [lia|].
  intros i Hi. replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
Qed.

Lemma rw_cells_prefix : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) -> rw_cells segs m A cs1.
Proof.
  intros segs m A cs1 cs2 [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [B1 _].
  split; [split; [exact WF1 | exact B1] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

Lemma bytes_at_at : forall segs m a a' bs, bytes_at segs m a bs -> a = a' -> bytes_at segs m a' bs.
Proof. intros; subst; assumption. Qed.

Lemma rw_cells_of_bytes : forall segs m A cs,
  cells_wf cs -> bytes_at segs m A (cells_bytes cs) -> wr_at segs m A (Z.of_nat (cells_size cs)) -> rw_cells segs m A cs.
Proof. intros. split; [split|]; assumption. Qed.

Lemma area_of_slot : forall (a : aptr) k, snd a mod 4096 = 0 -> 0 <= k < 101 ->
  area_of (aadd a (24 + 40 * k)) = a.
Proof.
  intros [ar ao] k Hm Hk. unfold area_of, aadd. cbn [fst snd] in *. f_equal.
  replace (ao + (24 + 40 * k)) with ((24 + 40 * k) + (ao / 4096) * 4096) by (Z.div_mod_to_equations; nia).
  rewrite Z.mod_add, Z.mod_small by lia. Z.div_mod_to_equations; nia.
Qed.

Lemma page_off_mod : forall b o x, b mod 4096 = 0 -> o mod 4096 = 0 -> 0 <= x < 4096 -> (b + o + x) mod 4096 = x.
Proof.
  intros b o x Hb Ho Hx.
  replace (b + o + x) with (x + (b / 4096 + o / 4096) * 4096) by (Z.div_mod_to_equations; nia).
  rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.

Lemma base16_mod : forall b po, b mod 4096 = 0 -> po mod 16 = 0 -> (b + po) mod 16 = 0.
Proof.
  intros b po Hb Hp. replace (b + po) with ((b / 4096) * 256 * 16 + (po / 16) * 16) by (Z.div_mod_to_equations; lia).
  rewrite <- Z.mul_add_distr_r, Z.mod_mul. reflexivity. lia.
Qed.

Definition freeW (sp : word) (P G : Z) : list (Z * Z) :=
  [(bv_unsigned sp - 48, bv_unsigned sp); (P - 4, P); (G, G + 40)]%Z.


Lemma rd8_known {R} st q v (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v -> rd8 st q k = k v.
Proof. intros H. unfold rd8. rewrite H. reflexivity. Qed.

Lemma rd16_known {R} st q v0 v1 (k : Z -> M R) :
  cell_read (get_shadow st (fst q)) (snd q) = Known v0 ->
  cell_read (get_shadow st (fst q)) (snd q + 1) = Known v1 ->
  rd16 st q k = k (v0 + 256 * v1).
Proof. intros H0 H1. unfold rd16, rd8. rewrite H0. cbn [fst snd aadd]. rewrite H1. reflexivity. Qed.

Lemma get_meta_rec_wr8 st q v g : get_meta_rec (wr8 q v st) g = get_meta_rec st g.
Proof. reflexivity. Qed.
Lemma get_meta_rec_wr16 st q v g : get_meta_rec (wr16 q v st) g = get_meta_rec st g.
Proof. reflexivity. Qed.

Lemma optr_eqb_refl : forall q : aptr, optr_eqb (Some q) (Some q) = true.
Proof. intros [qa qb]. unfold optr_eqb, aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

Lemma free_trivial_model : forall st (p : aptr) g gh ar (b3 lo hi : Z),
  let sh := get_shadow st (fst p) in
  let po := snd p in
  let off16 := lo + 256 * hi in
  let idx := Z.land b3 31 in
  let base := aadd p (- (UNIT * off16) - UNIT) in
  let mr := get_meta_rec st g in
  let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) (wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st)) in
  let reserved := Z.shiftr b3 5 in
  let e := aadd (slot_start' mr idx) (get_stride mr - IB) in
  po mod 16 = 0 ->
  cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
  cell_read sh (po - 2) = Known lo -> cell_read sh (po - 1) = Known hi ->
  (s_groups st) !! base = Some gh -> g_meta gh = Some g ->
  m_mem mr = Some base ->
  (s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
  0 <= m_avail mr -> 0 <= m_freed mr -> 0 <= b3 ->
  idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
  (m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
  (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  (m_maplen mr <> 0 -> off16 <= m_maplen mr * 4096 / UNIT - 1) ->
  reserved < 5 -> reserved <= snd e - po ->
  cell_read sh (snd e - reserved) = Known 0 -> cell_read sh (snd e) = Known 0 ->
  m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
  free st (Some p) = ret st'.
Proof.
  intros until hi. intros sh po off16 idx base mr st' reserved e AL C4 C3 C2 C1 Hgh Hg Hmem Har Hchk AV FR B3
         Hidx Hav Hfr Hsc Hsc63 Hml RES5 RESe E1 E0 Hfz Hall.
  unfold free, free_hdr, get_meta, guard. fold po. rewrite (proj2 (Z.eqb_eq _ _) AL).
  rewrite (rd16_known st (aadd p (-2)) lo hi) by (cbn [fst snd aadd]; fold po; first [replace (po + -2) with (po - 2) by lia; exact C2 | replace (po + -2 + 1) with (po - 1) by lia; exact C1]).
  cbv beta.
  rewrite (rd8_known st (aadd p (-3)) b3) by (cbn [fst snd aadd]; fold po; replace (po + -3) with (po - 3) by lia; exact C3).
  cbv beta.
  rewrite (rd8_known st (aadd p (-4)) 0) by (cbn [fst snd aadd]; fold po; replace (po + -4) with (po - 4) by lia; exact C4).
  cbv beta. cbn [Z.eqb negb].
  fold off16. fold base. unfold get_group. rewrite Hgh, Hg. fold mr. rewrite Hmem, optr_eqb_refl.
  fold idx. replace (idx <=? m_last_idx mr) with true by (symmetry; apply Z.leb_le; lia).
  unfold testbit. rewrite Hav, Hfr. cbn [negb].
  rewrite Har, Hchk, Z.eqb_refl.
  match goal with |- context [if (if ?c then ?x else ?y) then _ else SVis (EUndef (UAssert 16)) _] =>
    replace (if c then x else y) with true end.
  2:{ destruct (Z.ltb_spec (m_sizeclass mr) 48).
      - specialize (Hsc ltac:(lia)). symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
      - specialize (Hsc63 ltac:(lia)). symmetry. apply Z.eqb_eq. lia. }
  match goal with |- context [if (if ?c then ?x else ?y) then _ else SVis (EUndef (UAssert 17)) _] =>
    replace (if c then x else y) with true end.
  2:{ destruct (Z.eqb_spec (m_maplen mr) 0); cbn [negb]; [reflexivity|]. symmetry. apply Z.leb_le. apply Hml. assumption. }
  unfold slot_start. rewrite Hmem.
  assert (He : aadd (aadd base (UNIT + get_stride mr * idx)) (get_stride mr - IB) = e) by (unfold e, slot_start'; rewrite Hmem; reflexivity).
  rewrite He.
  assert (Fe : fst e = fst p) by (rewrite <- He; reflexivity).
  unfold get_nominal_size.
  rewrite (rd8_known st (aadd p (-3)) b3) by (cbn [fst snd aadd]; fold po; replace (po + -3) with (po - 3) by lia; exact C3).
  cbv beta. fold reserved.
  replace (5 <=? reserved) with false by (symmetry; apply Z.leb_gt; lia).
  fold po. replace (reserved <=? snd e - po) with true by (symmetry; apply Z.leb_le; lia).
  rewrite (rd8_known st (aadd e (- reserved)) 0) by (cbn [fst snd aadd]; rewrite Fe; fold sh; replace (snd e + - reserved) with (snd e - reserved) by lia; exact E1).
  cbv beta. cbn [Z.eqb].
  rewrite (rd8_known st e 0) by (rewrite Fe; exact E0).
  unfold guard. cbn [Z.eqb]. unfold Malloc.ret at 1. rewrite sbind_ret_l.
  unfold free_tail, guard. rewrite !get_meta_rec_wr16, !get_meta_rec_wr8. fold mr.
  unfold testbit. rewrite Z.lor_spec, Hfr, Hav. cbn [orb negb].
  replace (m_freed mr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hfz).
  replace (Z.lor (m_freed mr) (m_avail mr) + bit idx =? mask_upto (m_last_idx mr)) with false by (symmetry; apply Z.eqb_neq; exact Hall).
  cbn [orb negb]. reflexivity.
Qed.


End CANSEC4.
End F_malloc_free.

Module F_malloc_fast.

From Stdlib Require Import ZArith. From Stdlib Require Import NArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude. From LinuxProcessSemantics.Riscv Require Import Instr. From LinuxProcessSemantics.Riscv Require Import Decode. From LinuxProcessSemantics.Riscv Require Import DecodeC. From LinuxProcessSemantics.Riscv Require Import Sem. From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Walk.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import SFModel.
Import MallocRep. Import F_malloc_free.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Section CANSEC1. Context {rc : runConstT}.
Lemma swrap_word x : Z_to_bv 64 (bv_swrap 32 x) = wz (sxv x).
Proof. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Lemma sxv_testbit_lo' v i : 0 <= i < 32 -> Z.testbit (sxv v) i = Z.testbit v i.
Proof.
  intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. apply Z.mod_pow2_bits_low. lia.
Qed.

Lemma sxv_cases' v : let u := v mod 2^32 in
  (u < 2^31 /\ sxv v = u) \/ (2^31 <= u /\ sxv v = u + 2^64 - 2^32).
Proof.
  cbv zeta. pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
  rewrite <- (sxv_congr (v mod 2^32) v) by (apply Z.mod_mod; lia).
  destruct (sxv_cases (v mod 2^32) ltac:(lia)); tauto.
Qed.

Lemma testbit_31_mod32 v : Z.testbit v 31 = (2^31 <=? v mod 2^32).
Proof.
  rewrite <- (Z.mod_pow2_bits_low v 32 31) by lia. rewrite Z.testbit_eqb by lia.
  pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
  destruct (Z.leb_spec (2^31) (v mod 2^32)).
  - replace (v mod 2^32 / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma sxv_testbit_hi v i : 31 <= i < 64 -> Z.testbit (sxv v) i = Z.testbit v 31.
Proof.
  intros Hi. rewrite testbit_31_mod32. rewrite Z.testbit_eqb by lia.
  assert (P31 : 2^31 <= 2^i) by (apply Z.pow_le_mono_r; lia).
  assert (P63 : 2^i <= 2^63) by (apply Z.pow_le_mono_r; lia).
  assert (E64 : 2^64 = 2^(64-i) * 2^i) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (E2 : 2^(64-i) = 2 * 2^(64-i-1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (P1 : 1 <= 2^(64-i-1)) by (apply Z.pow_le_mono_r with (b:=0) in Hi || idtac; apply (Z.pow_le_mono_r 2 0); lia).
  destruct (sxv_cases' v) as [[Hu E]|[Hu E]]; rewrite E.
  - rewrite Z.div_small by lia. cbn. symmetry. apply Z.leb_gt. lia.
  - pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
    replace ((v mod 2^32 + 2^64 - 2^32) / 2^i) with (2^(64-i) - 1) by (Z.div_mod_to_equations; nia).
    rewrite E2. replace (2 * 2^(64-i-1) - 1) with (1 + (2^(64-i-1) - 1) * 2) by lia.
    rewrite Z.mod_add by lia. cbn. symmetry. apply Z.leb_le. lia.
Qed.

Lemma sxv_testbit_high v i : 64 <= i -> Z.testbit (sxv v) i = false.
Proof.
  intros. pose proof (sxv_range v). destruct (Z.eq_dec (sxv v) 0) as [->|]. apply Z.bits_0.
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.

Lemma sxv_land a b : Z.land (sxv a) (sxv b) = sxv (Z.land a b).
Proof.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 32); [| destruct (Z.lt_ge_cases i 64)].
  - rewrite !sxv_testbit_lo' by lia. symmetry. apply Z.land_spec.
  - rewrite !sxv_testbit_hi by lia. rewrite Z.land_spec. reflexivity.
  - rewrite !sxv_testbit_high by lia. reflexivity.
Qed.

Lemma sxv_idem v : sxv (sxv v) = sxv v.
Proof. apply sxv_congr. apply sxv_mod32. Qed.

Lemma land_opp_odd a : Z.land (2 * a + 1) (- (2 * a + 1)) = 1.
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma land_opp_even a : Z.land (2 * a) (- (2 * a)) = 2 * Z.land a (- a).
Proof.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

Lemma lowbit_pow2 : forall m, 0 < m -> exists k, 0 <= k /\ Z.land m (- m) = 2 ^ k /\ 2 ^ k <= m.
Proof.
  intros m Hm.
  pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
  cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
  intros x IH Hx0 Hx.
  destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
  - destruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
    exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
  - exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.

Lemma land_opp_pow2 k : 0 <= k -> Z.land (2 ^ k) (- 2 ^ k) = 2 ^ k.
Proof.
  intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
  subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

Lemma lowbit_nonzero m : 0 < m -> exists k, 0 <= k /\ lowbit m = 2 ^ k /\ 2 ^ k <= m.
Proof. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

Lemma lowbit_0 : lowbit 0 = 0.
Proof. reflexivity. Qed.

Lemma ctz32_pow2 k : 0 <= k -> ctz32 (2 ^ k) = k.
Proof. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

Lemma negw_and_lowbit v : 0 <= v < 2^32 ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz (sxv v)))))) (bv_unsigned (wz (sxv v))))
  = wz (sxv (lowbit v)).
Proof.
  intros Hv. rewrite swrap_word. rewrite !wz_unsigned by apply sxv_range.
  rewrite sxv_land. unfold lowbit, wz. f_equal.
  rewrite (Z.land_comm v (- v)).
  transitivity (sxv (Z.land (sxv (0 - sxv v)) (sxv v))); [rewrite sxv_land, sxv_idem; reflexivity|].
  transitivity (sxv (Z.land (sxv (- v)) (sxv v))); [| rewrite sxv_land, sxv_idem; reflexivity].
  f_equal. f_equal. apply sxv_congr.
  rewrite <- Zminus_mod_idemp_r, sxv_mod32, Zminus_mod_idemp_r. replace (0 - v) with (- v) by lia. reflexivity.
Qed.

Definition DB32 : Z := 124511785.
Definition dbi (k : Z) : Z := ((2 ^ k * DB32) mod 2^32) / 2^27.

Lemma lowbit_pow2_id k : 0 <= k -> lowbit (2 ^ k) = 2 ^ k.
Proof. intros. unfold lowbit. apply land_opp_pow2. assumption. Qed.

Lemma mulw_word a c : Z_to_bv 64 (bv_swrap 32 (bv_unsigned (wz (sxv a)) * c)) = wz (sxv (a * c)).
Proof.
  rewrite wz_unsigned by apply sxv_range. rewrite swrap_word. unfold wz. f_equal. apply sxv_congr.
  rewrite <- Z.mul_mod_idemp_l, sxv_mod32, Z.mul_mod_idemp_l by lia. reflexivity.
Qed.

Lemma srliw27_val a : bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (wz (sxv a)))) 27) = (a mod 2^32) / 2^27.
Proof.
  rewrite wz_unsigned by apply sxv_range.
  change (bv_wrap 32 (sxv a)) with ((sxv a) mod 2^32). rewrite sxv_mod32.
  rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound a (2^32) ltac:(lia)).
  apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Lemma dbi_range k : 0 <= dbi k < 32.
Proof. unfold dbi. pose proof (Z.mod_pos_bound (2^k * DB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

Lemma le4_avail_sub a b : 0 <= b <= a -> a < 2^32 ->
  le4 (wz (sxv (sxv a - sxv b))) = le4 (wz (a - b)).
Proof.
  intros. apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
  rewrite sxv_mod32, <- Zminus_mod_idemp_r, sxv_mod32, <- Zminus_mod_idemp_l, sxv_mod32, Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  reflexivity.
Qed.

Lemma srliw27_word a :
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (wz (sxv a)))) 27)) = wz ((a mod 2^32) / 2^27).
Proof. rewrite srliw27_val. reflexivity. Qed.


End CANSEC1.
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          let E := fresh "EQ" m' in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
          clear HB; try rename H' into H
        end
    end
  end.

Section CANSEC2. Context {rc : runConstT}.
Lemma rw_cells_CB_len segs m A n bs rest : rw_cells segs m A (CB n bs :: rest) -> length bs = n.
Proof. intros [[[H _] _] _]. exact H. Qed.

End CANSEC2.
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.
End F_malloc_fast.

Module InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Export InitMem.
End InitMem.

Module ProgDeps.
From Stdlib Require Import ZArith. From Stdlib Require Import List. From Stdlib Require Import Lia. From Stdlib Require Import Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase. From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics. From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType. From LinuxProcessSemantics.LinuxProcessSem Require Import State. From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import MState. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Mem. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Exec. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Nodes. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Decode. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Image.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.Prelim. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM01. Import SM01. Import SM01.Monad. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Stdio.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Export PState.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Notation MP := (Monad.M PState).


Section CANSEC1. Context {rc : runConstT}.
Definition neg_errno (e : Z) : Z := 2^64 - e.

Definition MAP_FIXED_Z : Z := 16.

Inductive fixed_ans : Type := FxKept (e : Z) | FxDone | FxLost (e : Z).
Definition dec_mmap_fixed (addr len : Z) (rsp : resp) : option fixed_ans :=
  match rsp with
  | mkEffectU r [] [] [] [] _ => match errno_of r with Some e => Some (FxKept e) | None => None end
  | mkEffectU r [] [] [(a, n)] [] _ =>
      if bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len)) then
        match errno_of r with
        | Some e => Some (FxLost e)
        | None => if bv_eqb r (Z_to_bv 64 addr) then Some FxDone else None
        end
      else None
  | _ => None
  end.

Definition dec_mprotect_rw (addr len : Z) (rsp : resp) : option range_ans :=
  match dec_mprotect addr len rsp with
  | Some (RgErr e) => if e =? ENOSYS then None else Some (RgErr e)
  | Some (RgDone true) => Some (RgDone true)
  | _ => None
  end.

Definition ev_step (atop : Z) (e : ev) : MP Z :=
  match e with
  | EBrk req =>
      if req =? 0 then
        (r <- msys (NBrk 0) dec_brk0 ;; mupd (set_brk_ps r) ;;; mret r)
      else
        (s <- mget ;;
         a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with
         | BrkGrown => mupd (set_brk_ps req) ;;; mret req
         | BrkSame => mret (ps_brk s)
         end)
  | EMmap addr len prot flags =>
      if negb (Z.land flags MAP_FIXED_Z =? 0) then
        (a <- msys (NMmap addr len prot flags) (dec_mmap_fixed addr len) ;;
         mret match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end)
      else if prot =? 0 then
        (a <- msys (NMmap addr len prot flags) (dec_mmap_none atop len []) ;;
         mret match a with MmErr e => neg_errno e | MmOk x => x end)
      else
        (a <- msys (NMmap addr len prot flags) (dec_mmap atop len []) ;;
         mret match a with MmErr e => neg_errno e | MmOk x => x end)
  | EMunmap addr len =>
      a <- msys (NMunmap addr len) (dec_munmap addr len) ;;
      mret match a with RgErr e => neg_errno e | RgDone _ => 0 end
  | EMprotect addr len prot =>
      a <- msys (NMprotect addr len prot) (dec_mprotect_rw addr len) ;;
      mret match a with RgErr e => neg_errno e | RgDone _ => 0 end
  | EPeek _ _ _ => munr
  | EUndef _ => munr
  end.

Fixpoint membed {R} (atop : Z) (t : stree ev Z R) : MP R :=
  match t with
  | SRet r => mret r
  | SVis e k => z <- ev_step atop e ;; membed atop (k z)
  end.

Definition bptr : Type := (cptr * Z)%type.

Definition fresh_off (cs : mstate) (slot : cptr) (n : Z) : Z :=
  match (s_slots cs) !! slot with
  | Some (g, idx) =>
      let mr := get_meta_rec cs g in
      fold_off (Z.land (c_mmap_counter (s_ctx cs)) 255) ((get_stride mr - IB - n) / UNIT)
  | None => 0
  end.

Definition raw_malloc (n : Z) : MP (option bptr) :=
  s <- mget ;;
  '(st', p) <- membed (s_atop (ps_m s)) (cmalloc (ps_m s) n) ;;
  mupd (set_m st') ;;;
  mret (match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end).
Definition raw_free (p : bptr) : MP unit :=
  s <- mget ;;
  st' <- membed (s_atop (ps_m s)) (cfree (ps_m s) (Some (fst p))) ;;
  mupd (set_m st').

Definition ptr_addr (s : PState) (p : bptr) : Z := conc (ps_m s) (fst p) + UNIT * snd p.
End CANSEC1.
End ProgDeps.
