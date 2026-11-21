(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocBlocks Malloc_iface MallocRep Malloc_fp F_malloc_free.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MallocP Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RMallocz_iface RCalloc_iface RF_allzerop RF_allzerop_live RF_malloc_spec RF_malloc_top.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import F_memset. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Printf_pieces. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Zh_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zeros_app : forall a b, zeros a ++ zeros b = zeros (a + b).
Proof. intros a b. unfold zeros. symmetry. apply repeat_app. Qed.

Lemma zeros_length : forall a, length (zeros a) = a.
Proof. intros a. unfold zeros. apply repeat_length. Qed.

(* [comment removed for export] *)
Definition zsuf (bs : list byte) (n k : Z) : Prop :=
  length bs = Z.to_nat n /\ skipn (Z.to_nat k) bs = zeros (Z.to_nat (n - k)).

Lemma zsuf_init : forall bs n, length bs = Z.to_nat n -> 0 <= n -> zsuf bs n n.
Proof. intros bs n L Hn. split; [exact L|]. rewrite Z.sub_diag. cbn. rewrite <- L. apply skipn_all. Qed.

Lemma zsuf_all : forall bs n, zsuf bs n 0 -> bs = zeros (Z.to_nat n).
Proof. intros bs n [L Z0]. cbn in Z0. rewrite Z.sub_0_r in Z0. exact Z0. Qed.

(* [comment removed for export] *)
Lemma zsuf_extend16 : forall bs n k, zsuf bs n k -> 16 <= k <= n ->
  firstn 8 (skipn (Z.to_nat (k - 16)) bs) = zeros 8 -> firstn 8 (skipn (Z.to_nat (k - 8)) bs) = zeros 8 ->
  zsuf bs n (k - 16).
Proof.
  intros bs n k [L Zs] Hk H1 H2. split; [exact L|].
  rewrite <- (firstn_skipn 8 (skipn (Z.to_nat (k - 16)) bs)). rewrite H1, skipn_skipn.
  replace (8 + Z.to_nat (k - 16))%nat with (Z.to_nat (k - 8)) by lia.
  rewrite <- (firstn_skipn 8 (skipn (Z.to_nat (k - 8)) bs)). rewrite H2, skipn_skipn.
  replace (8 + Z.to_nat (k - 8))%nat with (Z.to_nat k) by lia.
  rewrite Zs, !zeros_app. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma zsuf_set : forall bs n o i, zsuf bs n (o + i) -> 0 <= o -> 0 <= i -> o + i <= n ->
  zsuf (firstn (Z.to_nat o) bs ++ zeros (Z.to_nat i) ++ skipn (Z.to_nat (o + i)) bs) n o.
Proof.
  intros bs n o i [L Zs] Ho Hi Hn. split.
  - rewrite !length_app, length_firstn, zeros_length, length_skipn. lia.
  - rewrite skipn_app, length_firstn. rewrite (skipn_all2 (firstn (Z.to_nat o) bs)) by (rewrite length_firstn; lia).
    replace (Z.to_nat o - Nat.min (Z.to_nat o) (length bs))%nat with 0%nat by lia. rewrite skipn_O. cbn [app].
    rewrite Zs, zeros_app. f_equal. lia.
Qed.

Lemma le8_zero : le8 (Z_to_bv 64 0) = zeros 8.
Proof. vm_compute. reflexivity. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma shl52_shr52 : forall x, 0 <= x < 2^64 -> bv_unsigned (Z_to_bv 64 (x ≪ 52)) ≫ 52 = x mod 4096.
Proof.
  intros x Hx. rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^64) with (2^12 * 2^52). rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma land_page : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros x Hx. rewrite RF_allzerop.land_hi52 by lia.
  rewrite (Z.mod_small (x / 4096)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.div_mod x 4096 ltac:(lia)). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blk_bytes : forall (m : mem) A n bs, rw_cells psegs m A [CB (Z.to_nat n) bs] ->
  bytes_at psegs m A bs /\ length bs = Z.to_nat n /\ wr_at psegs m A (Z.of_nat (Z.to_nat n)).
Proof.
  intros m A n bs [[[L _] B] W]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  cbn [cells_size csize] in W. rewrite Nat.add_0_r in W. cbn [cell_wf] in L. auto.
Qed.

Lemma blk_sub : forall (m : mem) A n bs o N, rw_cells psegs m A [CB (Z.to_nat n) bs] -> 0 <= o -> 0 <= N -> o + N <= n ->
  rw_cells psegs m (A + o) [CB (Z.to_nat N) (firstn (Z.to_nat N) (skipn (Z.to_nat o) bs))].
Proof.
  intros m A n bs o N H Ho HN Hn. destruct (blk_bytes _ _ _ _ H) as (B & L & W).
  rewrite <- (firstn_skipn (Z.to_nat o) bs) in B. apply bytes_at_app in B. destruct B as [_ B].
  rewrite length_firstn in B. replace (Nat.min (Z.to_nat o) (length bs)) with (Z.to_nat o) in B by lia. rewrite Z2Nat.id in B by lia.
  rewrite <- (firstn_skipn (Z.to_nat N) (skipn (Z.to_nat o) bs)) in B. apply bytes_at_app in B. destruct B as [B _].
  apply rw_cells_of_bytes.
  - cbn. split; [|exact I]. rewrite length_firstn, length_skipn. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. eapply wr_at_sub; [exact W| lia| lia].
Qed.

Lemma blk_set : forall (m m' : mem) A n bs o N xs,
  rw_cells psegs m A [CB (Z.to_nat n) bs] -> 0 <= o -> 0 <= N -> o + N <= n ->
  munch [(A + o, A + o + N)] m m' -> wmono psegs m m' ->
  rw_cells psegs m' (A + o) [CB (Z.to_nat N) xs] ->
  rw_cells psegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat o) bs ++ xs ++ skipn (Z.to_nat (o + N)) bs)].
Proof.
  intros m m' A n bs o N xs H Ho HN Hn MU WM H'. destruct (blk_bytes _ _ _ _ H) as (B & L & W). destruct (blk_bytes _ _ _ _ H') as (B' & L' & W').
  pose proof (bytes_at_bound _ _ _ _ B) as BB.
  rewrite <- (firstn_skipn (Z.to_nat o) bs) in B. apply bytes_at_app in B. destruct B as [B1 B23].
  rewrite length_firstn in B23. replace (Nat.min (Z.to_nat o) (length bs)) with (Z.to_nat o) in B23 by lia. rewrite Z2Nat.id in B23 by lia.
  rewrite <- (firstn_skipn (Z.to_nat N) (skipn (Z.to_nat o) bs)) in B23. apply bytes_at_app in B23. destruct B23 as [_ B3].
  rewrite length_firstn, length_skipn, skipn_skipn in B3.
  replace (Nat.min (Z.to_nat N) (length bs - Z.to_nat o)) with (Z.to_nat N) in B3 by lia. rewrite Z2Nat.id in B3 by lia.
  replace (Z.to_nat N + Z.to_nat o)%nat with (Z.to_nat (o + N)) in B3 by lia.
  apply rw_cells_of_bytes.
  - cbn. split; [|exact I]. rewrite !length_app, length_firstn, length_skipn. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
    + eapply bytes_at_transport; [exact B1| exact MU|]. cbn. rewrite length_firstn. split; [left; lia| exact I].
    + rewrite length_firstn. replace (Nat.min (Z.to_nat o) (length bs)) with (Z.to_nat o) by lia. rewrite Z2Nat.id by lia.
      apply bytes_at_app. split; [exact B'|]. rewrite L', Z2Nat.id by lia.
      eapply bytes_at_transport; [exact B3| exact MU|]. cbn. split; [right; lia| exact I].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. eapply wr_at_transport; [exact W| exact WM].
Qed.

Lemma blk_read8 : forall (m : mem) A n bs o, rw_cells psegs m A [CB (Z.to_nat n) bs] -> 0 <= o -> o + 8 <= n ->
  exists z, 0 <= z < 2^64 /\ ov_read_bytes psegs m (wa (A + o)) 8 = Some (le8 (Z_to_bv 64 z))
            /\ (z = 0 -> firstn 8 (skipn (Z.to_nat o) bs) = zeros 8).
Proof.
  intros m A n bs o H Ho Hn. destruct (blk_bytes _ _ _ _ H) as (B & L & W).
  pose proof (bytes_at_read psegs m A bs o 8 B ltac:(lia) ltac:(lia)) as RD.
  destruct (le8_of_bytes (firstn 8 (skipn (Z.to_nat o) bs))) as (z & Hz & E). { rewrite length_firstn, length_skipn. lia. }
  exists z. split; [exact Hz|]. split; [rewrite E; exact RD|]. intros ->. rewrite <- E. apply le8_zero.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CLEAR.
Variables (gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v sp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (A n lo : Z) (fj : list byte).
Hypothesis A0 : 0 < A.
Hypothesis ALO : A + n <= lo.
Hypothesis LO : lo <= bv_unsigned sp + -32.
Hypothesis N32 : 0 < n < 2^32.

Definition clear_post : machine_state -> Prop := fun ms' =>
  exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom psegs)
    /\ munch [(A, A + n)] m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ rw_cells psegs m' A [CB (Z.to_nat n) (zeros (Z.to_nat n))] /\ stk psegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition CINV (m : mem) (bs : list byte) (k : Z) : Prop :=
  mem_inv psegs m /\ munch [(A, A + n)] m0 m /\ wmono psegs m0 m
  /\ rw_cells psegs m A [CB (Z.to_nat n) bs] /\ zsuf bs n k /\ 0 <= k <= n
  /\ rw_cells psegs m (bv_unsigned sp + -32) [CB 8 fj; C8 s1v; C8 s0v; C8 rav] /\ stk psegs m lo (bv_unsigned sp + -32).

Lemma cinv_memset : forall m m' bs o i, CINV m bs (o + i) -> 0 <= o -> 0 <= i ->
  munch [(A + o, A + o + i)] m m' -> wmono psegs m m' -> mem_inv psegs m' ->
  rw_cells psegs m' (A + o) [CB (Z.to_nat i) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat i))] ->
  CINV m' (firstn (Z.to_nat o) bs ++ zeros (Z.to_nat i) ++ skipn (Z.to_nat (o + i)) bs) o.
Proof.
  intros m m' bs o i (MI & MU & WM & BLK & ZS & K & FR & ST) Ho Hi MU' WM' MI' BLK'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  split; [exact MI'|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU']. intros x Hx. cbn in Hx |- *. split; [lia| exact I]. }
  split; [eapply wmono_trans; eassumption|].
  split. { eapply (blk_set m m' A n bs o i); try eassumption; lia. }
  split; [apply zsuf_set; [exact ZS| lia| lia| lia]|].
  split; [lia|].
  split. { eapply rw_cells_transport; [exact FR| exact MU'| exact WM'|]. cbn. split; [right; lia| exact I]. }
  eapply stk_transport_disjoint; [exact ST| exact MU'| exact WM'|]. cbn. split; [right; lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma calloc_tail : forall (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) bs k,
  CINV m bs k ->
  evt psegs clear_post
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 k) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x209a4) fc None m (seg_rom psegs)).
Proof.
  intros until k. intros INV. pose proof INV as (MI & MU & WM & BLK & ZS & K & FR & ST).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  do 7 step. release_frame FR ST (bv_unsigned sp). step.
  pose proof (blk_sub m A n bs 0 k BLK ltac:(lia) ltac:(lia) ltac:(lia)) as SUB. rewrite Z.add_0_r in SUB.
  eapply evt_cut.
  { eapply (memset_callZ) with (D := A) (C := 0) (N := k); [exact SUB| exact MI| lia| lia| lia| lia]. }
  intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m4 & -> & MU4 & WM4 & MI4 & BLK4).
  apply evt_done. unfold clear_post.
  exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m4. split; [reflexivity|].
  assert (SUBM : sub_fp [(A, A + k)] [(A, A + n)]) by (intros x Hx; cbn in Hx |- *; split; [lia| exact I]).
  split; [eapply munch_trans; [exact MU| eapply munch_weaken; [exact SUBM| exact MU4]]|].
  split; [eapply wmono_trans; eassumption|]. split; [exact MI4|].
  split.
  { pose proof (blk_set m m4 A n bs 0 k _ BLK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; exact MU4) WM4 ltac:(rewrite Z.add_0_r; exact BLK4)) as SET.
    pose proof (zsuf_set bs n 0 k ltac:(rewrite Z.add_0_l; exact ZS) ltac:(lia) ltac:(lia) ltac:(lia)) as ZS'.
    apply zsuf_all in ZS'. change (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat k)) with (zeros (Z.to_nat k)) in SET. rewrite ZS' in SET. exact SET. }
  eapply stk_transport_disjoint; [exact ST| exact MU4| exact WM4|]. cbn. split; [right; lia| exact I].
Qed.
(* [comment removed for export] *)
Definition KN (o : Z) : Prop :=
  forall (ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) bs', CINV m' bs' o -> 4096 <= o ->
    evt psegs clear_post
      (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 o) (Z_to_bv 64 (A + o)) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20964) fc None m' (seg_rom psegs)).

(* [comment removed for export] *)
Lemma mal0_after : forall pc, pc = 0x20958 \/ pc = 0x20998 \/ pc = 0x2093c ->
  forall (ra' t0 t1 t2 s1x a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) bs o,
  CINV m bs o -> KN o ->
  evt psegs clear_post
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1x (Z_to_bv 64 (A + o)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).
Proof.
  intros pc Hpc. intros until o. intros INV HKN. pose proof INV as (MI & MU & WM & BLK & ZS & K & FR & ST).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (AR : 0 <= A < 2^64) by lia.
  assert (TAILK : forall (ra'' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
            evt psegs clear_post
              (MS (mkR ra'' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp u0 u1 u2 (Z_to_bv 64 A) (Z_to_bv 64 o) b0 b1 b2 b3 b4 b5 b6 b7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (Z_to_bv 64 0x209a4) fc None m (seg_rom psegs)))
    by (intros; eapply calloc_tail; exact INV).
  destruct Hpc as [-> | [-> | ->]].
  - step. rewrite (unsigned_lit A) by lia. replace (A + o + - A) with o by lia.
    step. rewrite (unsigned_lit o) by lia. step. if_cases C; zify_cond C.
    + apply TAILK.
    + unfold KN in HKN. eapply HKN; [exact INV|].
      rewrite Z.shiftr_div_pow2 in C by lia. change (2^12) with 4096 in C.
      destruct (Z.lt_ge_cases o 4096) as [L|G]; [exfalso; apply C; apply Z.div_small; lia| exact G].
  - step. rewrite (unsigned_lit A) by lia. replace (A + o + - A) with o by lia.
    step. rewrite (unsigned_lit o) by lia. step. if_cases C; zify_cond C.
    + unfold KN in HKN. eapply HKN; [exact INV|].
      rewrite Z.shiftr_div_pow2 in C by lia. change (2^12) with 4096 in C.
      destruct (Z.lt_ge_cases o 4096) as [L|G]; [exfalso; apply C; apply Z.div_small; lia| exact G].
    + apply TAILK.
  - step. rewrite (unsigned_lit A) by lia. replace (A + o + - A) with o by lia.
    step. rewrite (unsigned_lit o) by lia. step. if_cases C; zify_cond C.
    + unfold KN in HKN. eapply HKN; [exact INV|].
      rewrite Z.shiftr_div_pow2 in C by lia. change (2^12) with 4096 in C.
      destruct (Z.lt_ge_cases o 4096) as [L|G]; [exfalso; apply C; apply Z.div_small; lia| exact G].
    + step. apply TAILK.
Qed.

(* [comment removed for export] *)
Lemma mal0_memset : forall pc, pc = 0x20954 \/ pc = 0x20994 ->
  forall (ra' t0 t1 t2 s1x a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) bs o i,
  CINV m bs (o + i) -> 0 <= o -> 0 <= i -> KN o ->
  evt psegs clear_post
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1x (Z_to_bv 64 (A + o)) (Z_to_bv 64 0) (Z_to_bv 64 i) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m (seg_rom psegs)).
Proof.
  intros pc Hpc. intros until i. intros INV Ho Hi HKN. pose proof INV as (MI & MU & WM & BLK & ZS & K & FR & ST).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (blk_sub m A n bs o i BLK Ho Hi ltac:(lia)) as SUB.
  destruct Hpc as [-> | ->].
  - step.
    eapply evt_cut.
    { eapply (memset_callZ) with (D := A + o) (C := 0) (N := i); [exact SUB| exact MI| lia| lia| lia| lia]. }
    intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m4 & -> & MU4 & WM4 & MI4 & BLK4).
    replace (ret_pc (Z_to_bv 64 0x20958)) with (Z_to_bv 64 0x20958) by (symmetry; rpc).
    eapply (mal0_after 0x20958); [left; reflexivity| | exact HKN].
    eapply cinv_memset; eassumption.
  - step.
    eapply evt_cut.
    { eapply (memset_callZ) with (D := A + o) (C := 0) (N := i); [exact SUB| exact MI| lia| lia| lia| lia]. }
    intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m4 & -> & MU4 & WM4 & MI4 & BLK4).
    replace (ret_pc (Z_to_bv 64 0x20998)) with (Z_to_bv 64 0x20998) by (symmetry; rpc).
    eapply (mal0_after 0x20998); [right; left; reflexivity| | exact HKN].
    eapply cinv_memset; eassumption.
Qed.
(* [comment removed for export] *)
Lemma mal0_scan : forall (j : nat) (ra' t0 t1 t2 s1x a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) bs o,
  CINV m bs (o + 16 * (Z.of_nat j + 1)) -> 0 <= o -> 16 * (Z.of_nat j + 1) <= 4096 -> KN o ->
  evt psegs clear_post
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) s1x
             (Z_to_bv 64 (A + o + 16 * (Z.of_nat j + 1))) (Z_to_bv 64 (A + o)) (Z_to_bv 64 (16 * (Z.of_nat j + 1))) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20970) fc None m (seg_rom psegs)).
Proof.
  induction j as [|j IH]; intros until o; intros INV Ho HI HKN.
  - (* [comment removed for export] *)
    pose proof INV as (MI & MU & WM & BLK & ZS & K & FR & ST).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    change (16 * (Z.of_nat 0 + 1)) with 16 in *.
    destruct (blk_read8 m A n bs (o + 16 - 16) BLK ltac:(lia) ltac:(lia)) as (z1 & Z1 & RD1 & ZZ1).
    destruct (blk_read8 m A n bs (o + 16 - 8) BLK ltac:(lia) ltac:(lia)) as (z2 & Z2 & RD2 & ZZ2).
    step. step. step. step. rewrite (unsigned_lit z1), (unsigned_lit z2) by lia.
    if_cases C; zify_cond C.
    + (* [comment removed for export] *)
      step. replace (A + o + 16 + - (16)) with (A + o) by lia. step.
      eapply (mal0_memset 0x20954); [left; reflexivity| exact INV| lia| lia| exact HKN].
    + (* [comment removed for export] *)
      apply Z.lor_eq_0_iff in C. destruct C as [-> ->].
      pose proof (zsuf_extend16 bs n (o + 16) ZS ltac:(lia) (ZZ1 eq_refl) (ZZ2 eq_refl)) as ZS'.
      replace (o + 16 - 16) with o in ZS' by lia.
      assert (INV' : CINV m bs (o + 0)).
      { rewrite Z.add_0_r. split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact BLK|]. split; [exact ZS'|]. split; [lia|]. split; assumption. }
      step. step. step. if_false. step. replace (A + o + - 0) with (A + o) by lia. step.
      eapply (mal0_memset 0x20994); [right; reflexivity| exact INV'| lia| lia| exact HKN].
  - (* [comment removed for export] *)
    pose proof INV as (MI & MU & WM & BLK & ZS & K & FR & ST).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    set (i := 16 * (Z.of_nat (S j) + 1)) in *.
    assert (Ei : i = 16 * (Z.of_nat j + 1) + 16) by (unfold i; lia).
    destruct (blk_read8 m A n bs (o + i - 16) BLK ltac:(lia) ltac:(lia)) as (z1 & Z1 & RD1 & ZZ1).
    destruct (blk_read8 m A n bs (o + i - 8) BLK ltac:(lia) ltac:(lia)) as (z2 & Z2 & RD2 & ZZ2).
    step. step. step. step. rewrite (unsigned_lit z1), (unsigned_lit z2) by lia.
    if_cases C; zify_cond C.
    + (* [comment removed for export] *)
      step. rewrite (unsigned_lit i) by lia. replace (A + o + i + - i) with (A + o) by lia. step.
      eapply (mal0_memset 0x20954); [left; reflexivity| exact INV| lia| lia| exact HKN].
    + apply Z.lor_eq_0_iff in C. destruct C as [-> ->].
      pose proof (zsuf_extend16 bs n (o + i) ZS ltac:(lia) (ZZ1 eq_refl) (ZZ2 eq_refl)) as ZS'.
      assert (INV' : CINV m bs (o + 16 * (Z.of_nat j + 1))).
      { replace (o + 16 * (Z.of_nat j + 1)) with (o + i - 16) by lia.
        split; [exact MI|]. split; [exact MU|]. split; [exact WM|]. split; [exact BLK|]. split; [exact ZS'|]. split; [lia|]. split; assumption. }
      step. step. step.
      replace (i + -16) with (16 * (Z.of_nat j + 1)) by lia. replace (A + o + i + -16) with (A + o + 16 * (Z.of_nat j + 1)) by lia.
      if_cases C; zify_cond C; [| exfalso; lia].
      eapply IH; [exact INV'| lia| lia| exact HKN].
Qed.

(* [comment removed for export] *)
Lemma mal0_loop : forall (np : nat) (ra' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) bs o,
  CINV m bs o -> 4096 <= o <= 4096 * Z.of_nat np ->
  evt psegs clear_post
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 o) (Z_to_bv 64 (A + o)) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20964) fc None m (seg_rom psegs)).
Proof.
  induction np as [|np IH]; intros until o; intros INV Ho; [exfalso; lia|].
  pose proof INV as (MI & MU & WM & BLK & ZS & K & FR & ST).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step.
  replace (A + o + -4096) with (A + (o - 4096)) by lia.
  replace (Z_to_bv 64 (A + o)) with (Z_to_bv 64 (A + (o - 4096) + 16 * (Z.of_nat 255 + 1))) by (f_equal; change (Z.of_nat 255) with 255; lia).
  change (Z_to_bv 64 4096) with (Z_to_bv 64 (16 * (Z.of_nat 255 + 1))).
  eapply (mal0_scan 255).
  - replace (o - 4096 + 16 * (Z.of_nat 255 + 1)) with o by (change (Z.of_nat 255) with 255; lia). exact INV.
  - lia.
  - change (Z.of_nat 255) with 255. lia.
  - unfold KN. intros. eapply IH; [eassumption|]. rewrite Nat2Z.inj_succ in Ho. lia.
Qed.

(* [comment removed for export] *)
Lemma calloc_clear : forall (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) bs,
  CINV m bs n ->
  evt psegs clear_post
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x20918) fc None m (seg_rom psegs)).
Proof.
  intros until bs. intros INV. pose proof INV as (MI & MU & WM & BLK & ZS & K & FR & ST).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. rewrite (unsigned_lit n) by lia. step. if_cases C; zify_cond C.
  - (* [comment removed for export] *) eapply calloc_tail. exact INV.
  - (* [comment removed for export] *)
    step. step. step. step. step. step.
    assert (N4 : 4096 <= n).
    { rewrite Z.shiftr_div_pow2 in C by lia. change (2^12) with 4096 in C.
      destruct (Z.lt_ge_cases n 4096) as [L|G]; [exfalso; apply C; apply Z.div_small; lia| exact G]. }
    assert (ANR : 0 <= A + n < 2^64) by lia.
    rewrite (unsigned_lit (A + n)) by lia.
    rewrite (shl52_shr52 (A + n) ANR), (land_page (A + n) ANR).
    set (pm := (A + n) mod 4096). assert (PM : 0 <= pm < 4096) by (apply Z.mod_pos_bound; lia).
    replace (A + n - pm) with (A + (n - pm)) by lia.
    pose proof (blk_sub m A n bs (n - pm) pm BLK ltac:(lia) ltac:(lia) ltac:(lia)) as SUB.
    step.
    eapply evt_cut.
    { eapply (memset_callZ) with (D := A + (n - pm)) (C := 0) (N := pm); [exact SUB| exact MI| lia| lia| lia| lia]. }
    intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m4 & -> & MU4 & WM4 & MI4 & BLK4).
    replace (ret_pc (Z_to_bv 64 0x2093c)) with (Z_to_bv 64 0x2093c) by (symmetry; rpc).
    eapply (mal0_after 0x2093c); [right; right; reflexivity| |].
    + eapply (cinv_memset m m4 bs (n - pm) pm); [| lia| lia| exact MU4| exact WM4| exact MI4| exact BLK4].
      replace (n - pm + pm) with n by lia. exact INV.
    + unfold KN. intros. eapply (mal0_loop (Z.to_nat n)); [eassumption|]. lia.
Qed.
End CLEAR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rheap_pres_of_munch : forall LB SP W (m m' : mem),
  munch W m m' -> wmono psegs m m' -> (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a) ->
  rheap_pres LB SP m m'.
Proof.
  intros LB SP W m m' MU WM HO a Ha Hc. split; [| apply WM].
  apply MU. rewrite wa_unsigned by lia. exact (HO a Ha Hc).
Qed.

Theorem rcalloc_proof : rcalloc_stmt.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv.
  intros HEAP AUXB SB ST CLO LO ERR REPL MI TP HA0 HA1 N. subst a0 a1.
  unfold RCALLOC_SYM, RCALLOC_STACK, RMALLOC_STACK, RMALLOC_REPLACED in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof alloc_ceiling_range as CEILR.
  assert (ERRA : errno_addr tp = 0x3a74c) by (rewrite TP; unfold errno_addr; rewrite unsigned_lit by (unfold RATP; lia); reflexivity).
  rewrite ERRA in ERR.
  assert (BLR : forall b, In b LB -> blk_addr b + blk_size b <= alloc_ceiling /\ 0 <= blk_size b /\ 0 < blk_addr b).
  { intros b Hb. destruct (RHEAP_block_range_proof _ _ _ _ HEAP Hb) as (X1 & _ & X3 & X4 & _). lia. }
  assert (CLI0 : forall a, 0 <= a < 2^64 -> rclient_addr LB (bv_unsigned sp) a -> outside [(bv_unsigned sp - 32, bv_unsigned sp)] a).
  { intros a Ha Hc. cbn. split; [|exact I]. destruct Hc as [Hc|[[Hc _]|(b' & Hb' & Hr)]]; [lia| lia|].
    destruct (BLR _ Hb'). unfold in_block in Hr. lia. }
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold implM. iprefix.
  carve_frame 32%nat ST. do 4 step.
  step. if_cases C0; zify_cond C0; [exfalso; rewrite ?unsigned_lit in C0 by lia; lia|]. clear C0.
  step. rewrite (unsigned_lit n) by lia.
  replace ((n * 1) ≫ 64) with 0 by (rewrite Z.mul_1_r, Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_cases C0; zify_cond C0; [| exfalso; apply C0; reflexivity]. clear C0.
  step. rewrite (unsigned_lit n) by lia. rewrite Z.mul_1_r. step. step.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : RHEAP s LB m1).
  { eapply RHEAP_frame_proof; [exact HEAP| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUXB| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
  assert (SP32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  ihere.
  lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
    lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
  eapply implM_post_evt.
  { eapply (rmallocz_spec) with (B := B) (lo := lo) (errv := errv);
      [exact HEAP1| exact AUX1| rewrite SP32; lia| rewrite SP32; exact ST| exact CLO| rewrite SP32; unfold RMALLOC_STACK; lia
      | rewrite ERRA; exact ERR| exact MI| exact TP| reflexivity| lia]. }
  cbv beta. intros r s1' ms1 PO. unfold rmallocz_post in PO.
  destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv2
                  & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & RES).
  rewrite SP32 in ST3, HP. rewrite ERRA in ERR3.
  replace (ret_pc (Z_to_bv 64 0x20904)) with (Z_to_bv 64 0x20904) by (symmetry; rpc).
  (* [comment removed for export] *)
  pose proof (rheap_pres_rw_cells _ _ _ _ _ _ HP FR ltac:(left; cbn; lia)) as FR3.
  pose proof (rheap_pres_rw_cells _ _ _ _ _ _ HP REPL ltac:(right; left; cbn; unfold RLIBC, RCTX, RERRNO, RATP, RSSP_GUARD, RGOT_SSP; lia)) as REPL3.
  assert (HP0 : rheap_pres LB (bv_unsigned sp) m m3).
  { eapply rheap_pres_trans; [eapply rheap_pres_of_munch; [exact MU| exact WM| exact CLI0]|]. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
  clear MU WM FR REPL ERR MI ST HEAP1 AUX1.
  destruct r as [p|].
  2:{ (* [comment removed for export] *)
    destruct RES as (-> & HEAP3).
    step. if_true.
    do 5 step. release_frame FR3 ST3 (bv_unsigned sp). step.
    apply evt_done. unfold rcalloc_post.
    do 15 eexists. exists m3, errv2. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [rewrite ERRA; exact ERR3|]. split; [exact AUX3|]. split; [exact HP0|].
    split; [exact FA|]. split; [exact SO|]. split; [reflexivity| exact HEAP3]. }
  destruct RES as (A & junkA & -> & BR & HEAP3 & BLK & _ & AZJ).
  pose proof BR as (A0 & A16 & N0 & AC & AIMG).
  step. if_cases C0; zify_cond C0; [exfalso; rewrite ?unsigned_lit in C0 by lia; lia|]. clear C0.
  do 3 step. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  step. if_true.
  step. step.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (rallzerop_heap) with (s := s1') (LB := (p, A, n) :: LB) (p := p) (A := A) (n := n);
      [exact HEAP3| left; reflexivity| exact MI3| reflexivity]. }
  intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & -> & VZ).
  replace (ret_pc (Z_to_bv 64 0x209e4)) with (Z_to_bv 64 0x209e4) by (symmetry; rpc).
  step. if_cases CV; zify_cond CV.
  - (* [comment removed for export] *)
    pose proof (AZJ (VZ CV)) as EJ. subst junkA.
    do 5 step. release_frame FR3 ST3 (bv_unsigned sp). step.
    apply evt_done. unfold rcalloc_post.
    do 15 eexists. exists m3, errv2. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [rewrite ERRA; exact ERR3|]. split; [exact AUX3|]. split; [exact HP0|].
    split; [exact FA|]. split; [exact SO|]. exists A. split; [reflexivity|]. split; [exact BR|]. split; [exact HEAP3| exact BLK].
  - (* [comment removed for export] *)
    step.
    pose proof (blk_bytes _ _ _ _ BLK) as (_ & LJ & _).
    eapply evt_mono.
    { eapply (calloc_clear gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 sp F fc m3 A n lo); [exact A0| lia| lia| lia|].
      split; [exact MI3|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact BLK|].
      split; [apply zsuf_init; [exact LJ| lia]|]. split; [lia|]. split; [exact FR3| exact ST3]. }
    intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m4 & -> & MU4 & WM4 & MI4 & BLK4 & ST4).
    assert (CLI4 : forall a, 0 <= a < 2^64 -> rclient_addr LB (bv_unsigned sp) a -> outside [(A, A + n)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. destruct Hc as [Hc|[[Hc _]|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (heap_sep s1' [(p, A, n)] LB m3 (p, A, n) b' RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof HEAP3 ltac:(left; reflexivity) Hb') as DJ.
      cbn [blk_addr blk_size fst snd] in DJ. unfold in_block in Hr. lia. }
    unfold rcalloc_post.
    do 15 eexists. exists m4, errv2. split; [reflexivity|].
    split; [exact MI4|]. split; [exact ST4|].
    split. { rewrite ERRA. eapply rw_cells_transport; [exact ERR3| exact MU4| exact WM4|]. cbn. lia. }
    split. { eapply rauxv_ok_frame; [exact AUX3| exact MU4| exact WM4|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    split. { eapply rheap_pres_trans; [exact HP0|]. eapply rheap_pres_of_munch; [exact MU4| exact WM4| exact CLI4]. }
    split; [exact FA|]. split; [exact SO|].
    exists A. split; [reflexivity|]. split; [exact BR|]. split; [| exact BLK4].
    eapply RHEAP_frame_proof; [exact HEAP3| exact MU4| exact WM4|].
    constructor; [| constructor]. right; right. exists (p, A, n). split; [left; reflexivity|]. cbn. lia.
Qed.
End WithCeiling0.
