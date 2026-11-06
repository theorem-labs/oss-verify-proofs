(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Export ADepotM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition aobj (p n : Z) : Prop :=
     (4096 <= p /\ 0 <= n /\ p + n <= kLowShadowMapBeg /\ (p + n <= 0x10000 \/ 0x60a000 <= p))
  \/ (kHighMemBeg <= p /\ 0 <= n /\ p + n <= alloc_ceiling).
Definition pz_in (addr size : Z) : Prop := (0 <= addr /\ addr + size <= kLowShadowMapBeg) \/ kHighMemBeg <= addr.
Definition pz0_in (addr size : Z) : Prop := (8 <= addr /\ addr + size <= kLowShadowMapBeg) \/ kHighMemBeg + 8 <= addr.
Definition fl_in (a size : Z) : Prop := (0 <= a /\ a + size <= kLowShadowMapBeg) \/ kHighMemBeg <= a.
Definition m2s_in (p : Z) : Prop := (0 <= p <= kLowMemEnd) \/ (kHighMemBeg <= p <= kHighMemEnd).
Lemma aobj_facts : forall p n, aobj p n ->
  4096 <= p /\ 0 <= n /\ p + n <= alloc_ceiling /\ (p + n <= 0x10000 \/ 0x60a000 <= p) /\ (p + n <= kLowShadowMapBeg \/ kHighMemBeg <= p).
Proof. unfold aobj, kLowShadowMapBeg, kHighMemBeg. intros p n H. pose proof alloc_ceiling_val. lia. Qed.
Lemma aobj_hi : forall p n, kHighMemBeg <= p -> 0 <= n -> p + n <= alloc_ceiling -> aobj p n.
Proof. unfold aobj. intros. right. lia. Qed.
Lemma aobj_sub : forall p n p' n', aobj p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n -> aobj p' n'.
Proof. unfold aobj. intros. lia. Qed.
Lemma aobj_pz_in : forall p n a s, aobj p n -> p <= a -> a + s <= p + n -> pz_in a s.
Proof. unfold aobj, pz_in. intros. lia. Qed.
Lemma aobj_pz0_in : forall p n a s, aobj p n -> p + 8 <= a -> a + s <= p + n -> pz0_in a s.
Proof. unfold aobj, pz0_in. intros. lia. Qed.
Lemma aobj_fl_in : forall p n a s, aobj p n -> p <= a -> a + s <= p + n -> fl_in a s.
Proof. unfold aobj, fl_in. intros. lia. Qed.
Lemma aobj_m2s_in : forall p n a, aobj p n -> p <= a -> a < p + n -> m2s_in a.
Proof. unfold aobj, m2s_in, kLowShadowMapBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd. intros p n a H L R. pose proof alloc_ceiling_val. lia. Qed.
Lemma pz_in_m2s : forall addr size, pz_in addr size -> 0 <= size -> addr < 2^47 -> m2s_in addr.
Proof. unfold pz_in, m2s_in, kLowShadowMapBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd. intros. lia. Qed.
(* [comment removed for export] *)
Lemma aobj_app_rangeA : forall p n, app_rangeA AL_pboth p n <-> aobj p n.
Proof. intros. unfold app_rangeA, aobj. cbn [al_image_lo al_image_hi AL_pboth]. tauto. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aobj_lin : forall p n, aobj p n -> exists ix sx : Z,
  0 <= ix <= 1 /\ 0 <= sx <= 1 /\ 4096 <= p /\ 0 <= n /\ p + n <= alloc_ceiling /\
  p + n <= 0x10000 + ix * 2^48 /\ ix * 0x60a000 <= p /\
  p + n <= 0x7fff7000 + sx * 2^48 /\ sx * 0x10007fff8000 <= p.
Proof.
  intros p n H. pose proof alloc_ceiling_val. unfold aobj, kLowShadowMapBeg, kHighMemBeg in H.
  destruct H as [(A & B & C & [D|D])|(A & B & C)].
  - exists 0, 0. lia. - exists 1, 0. lia. - exists 1, 1. lia.
Qed.
Definition aobjK (p n : Z) : Prop := aobj p n.     (* [comment removed for export] *)
Lemma aobjK_i : forall p n, aobj p n -> aobjK p n. Proof. exact (fun p n H => H). Qed.
Lemma aobjK_e : forall p n, aobjK p n -> aobj p n. Proof. exact (fun p n H => H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rzlog_entry : Z := 0x3c6c4.
Definition rzlog_stack : Z := 16.
Definition rzlog_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (l : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz l) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).
Definition rzlog_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l lo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
    0 <= l <= 7 -> a0 = wz (16 * 2 ^ l) -> bv_unsigned ra mod 2 = 0 ->
    evt rsegs (rzlog_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc l lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz rzlog_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition get_thread_entry : Z := 0x624e0.
Definition get_thread_stack : Z := 16.
Definition thread_cells (m : word -> option byte) (tp : word) (tsd ctx thr : Z) : Prop :=
     ro_cells rsegs m 0xb4420 [C1 (Z_to_bv 8 1)] /\ ro_cells rsegs m 0xb4424 [C4 (wz 0)]
  /\ ro_cells rsegs m (bv_unsigned tp - 88) [C8 (wz tsd)]
  /\ ro_cells rsegs m tsd [C8 (wz ctx)]
  /\ ro_cells rsegs m (ctx + 152) [C8 (wz thr)]
  /\ 0 <= tsd /\ tsd + 8 <= alloc_ceiling /\ 0 < ctx /\ ctx + 0x10000 <= alloc_ceiling
  /\ aobj thr 4096 /\ thr + 4096 <= alloc_ceiling /\ 88 <= bv_unsigned tp <= alloc_ceiling /\ aobj ctx 0x10000.
(* [comment removed for export] *)
Definition get_thread_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (thr : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz thr) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).
Definition get_thread_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tsd ctx thr lo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> alloc_ceiling <= lo ->
    thread_cells m tp tsd ctx thr -> bv_unsigned ra mod 2 = 0 ->
    evt rsegs (get_thread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc thr lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz get_thread_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition thread_stats_entry : Z := 0x616ac.
Definition thread_stats_stack : Z := 32.
Definition thread_stats_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tsd ctx thr lo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 32 -> alloc_ceiling <= lo ->
    thread_cells m tp tsd ctx thr -> bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (thr + off_th_stats)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz thread_stats_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unwind_entry : Z := 0x60a78.
Definition unwind_stack : Z := 224.
Definition unwind_depth2 (top bot bp : Z) : bool := (bot <? top) && (4096 <=? top) && (bot <? bp) && (bp <? top - 16).
Definition unwind_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (obj pc0 bp tsd ctx thr top bot lo : Z) (ra0 v : word) (junkbuf : list byte) (tag0 sz0 tfb0 : word),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 224 -> alloc_ceiling <= lo ->
    a0 = wz obj -> a1 = wz pc0 -> a2 = wz bp -> a3 = wz 0 -> a4 = wz 1 -> a5 = wz 30 ->
    4096 <= pc0 < 2^47 -> 4096 <= bv_unsigned ra0 -> bv_unsigned ra0 <> pc0 ->
    bp mod 16 = 0 -> bv_unsigned v <= bp -> 0 <= top < 2^64 -> 0 <= bot < 2^64 ->
    thread_cells m tp tsd ctx thr ->
    ro_cells rsegs m 0xb5898 [C1 (Z_to_bv 8 1)] ->                                   (* [comment removed for export] *)
    ro_cells rsegs m 0xa8b50 [C8 (wz 0x144660)] -> ro_cells rsegs m 0x144660 [C8 (wz 4096)] ->   (* [comment removed for export] *)
    rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)] -> ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m obj [C8 (wz (obj + 16)); C4 sz0; C4 tag0; CB 2040 junkbuf; C8 tfb0] ->   (* [comment removed for export] *)
    ro_cells rsegs m (bp - 16) [C8 v; C8 ra0] ->
    (* [comment removed for export] *)
    bv_unsigned sp <= obj -> obj + 2064 <= bp - 16 -> bp <= 2^47 -> thr + 4096 <= lo \/ bv_unsigned sp + 2^16 <= thr ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (jb1 : list byte) m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (obj + 8, obj + 12); (obj + 16, obj + 32); (obj + 2056, obj + 2064);
                           (thr + off_th_unwinding, thr + off_th_unwinding + 1)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)]
                 /\ rw_cells rsegs m' (obj + 2056) [C8 (wz bp)]
                 /\ (if unwind_depth2 top bot bp
                     then rw_cells rsegs m' (obj + 8) [C4 (wz 2)] /\ rw_cells rsegs m' (obj + 16) [C8 (wz pc0); C8 ra0]
                     else rw_cells rsegs m' (obj + 8) [C4 (wz 1)] /\ rw_cells rsegs m' (obj + 16) [C8 (wz pc0); CB 8 jb1]))
                    (* [comment removed for export] *)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz unwind_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_entry : Z := 0x59c74.
Definition poison_stack : Z := 64.
Definition poison_consts (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xb441c [C1 (Z_to_bv 8 1)]                                    (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa8b60 [C8 (wz 0x1466e8)] /\ ro_cells rsegs m (0x1466e8 + 120) [C8 (wz 18446744073709551615)]   (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa8b70 [C8 (wz 0xb4bb8)] /\ ro_cells rsegs m 0xb4bb8 [C8 (wz kShadowOffset)]
  /\ ro_cells rsegs m 0xa8b78 [C8 (wz 0xb58a8)] /\ ro_cells rsegs m 0xa8b80 [C8 (wz 0xb58b0)] /\ ro_cells rsegs m 0xa8b88 [C8 (wz 0xb58a0)]
  /\ ro_cells rsegs m 0xb58a0 [C8 (wz kHighMemEnd); C8 (wz 0); C8 (wz 0)]
  /\ ro_cells rsegs m 0xa8b90 [C8 (wz 0xaaa18)] /\ ro_cells rsegs m 0xaaa18 [C8 (wz 0xa1f90)]
  /\ ro_cells rsegs m 0xa8b50 [C8 (wz 0x144660)] /\ ro_cells rsegs m 0x144660 [C8 (wz 4096)].
Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr size value lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (sh addr, sh addr + size / 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (sh addr) (repeat (Z_to_bv 8 value) (Z.to_nat (size / 8))).
Definition poison_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (addr size value lo : Z) (old : list byte),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    a0 = wz addr -> a1 = wz size -> a2 = wz value ->
    addr mod 8 = 0 -> size mod 8 = 0 -> 8 <= size -> pz_in addr size -> addr + size <= 2^47 ->
    0 <= value < 256 -> (value = 0 -> size / 8 < 2^45) ->
    poison_consts m ->
    rw_cells rsegs m (sh addr) [CB (Z.to_nat (size / 8)) old] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size value lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz poison_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition classid_blk_entry : Z := 0x3b8b4.
Definition classid_blk_exit : Z := 0x3b990.
Definition classid_blk_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : Z) (Q : machine_state -> Prop),
    513 <= s <= 65536 -> s mod 8 = 0 ->
    (forall a2' a4' a5' a6' a7' t0' t1' : word,
        evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2 (wz (size_class s)) s1 a0 a1 a2' a3 a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz classid_blk_exit) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz s) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz classid_blk_entry) fc None m (seg_rom rsegs)).


(* [comment removed for export] *)
Definition classid_blk2_entry : Z := 0x37630.
Definition classid_blk2_exit : Z := 0x3770c.
Definition classid_blk2_stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : Z) (Q : machine_state -> Prop), 513 <= s <= 65536 -> s mod 8 = 0 -> (forall a2' a3' a4' a5' a6' : word, evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (size_class s)) a2' a3' a4' a5' a6' a7 s2 (Z_to_bv 64 s) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 classid_blk2_exit) fc None m (seg_rom rsegs))) -> evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 s) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 classid_blk2_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot_cellsC (L : alayout) (segs : list Segment) (D : list (list Z)) (n0 f0 : Z) (m : word -> option byte) : Prop :=
  let tab := al_theDepot L in let ss := al_stackStore L in
  (* [comment removed for export] *)
  (forall b, 0 <= b < 2^20 -> u32_at segs m (tab + 4 * b) (depot_headC D b 1 0)) /\
  u32_at segs m (al_depot_n_uniq_ids L) (Z.of_nat (length D)) /\
  u64_at segs m (al_depot_nodes_map1 L) n0 /\ (forall j, 1 <= j < kDepotNodesL1 -> u64_at segs m (al_depot_nodes_map1 L + 8 * j) 0) /\
  (* [comment removed for export] *)
  (forall i, (i < length D)%nat ->
     rw_cells segs m (n0 + 16 * (Z.of_nat i + 1))
       [C8 (wz (depot_hashC (nth i D []))); C4 (wz (depot_linkC D i)); C4 (wz (depot_off D i + 1))]) /\
  (* [comment removed for export] *)
  u64_at segs m ss (depot_total D) /\ u64_at segs m (ss + 16) f0 /\ u32_at segs m (ss + 24) (depot_total D) /\
  (forall i, (i < length D)%nat ->
     u64_at segs m (f0 + 8 * depot_off D i) (Z.of_nat (length (nth i D []))) /\
     (forall t w, nth_error (nth i D []) t = Some w -> u64_at segs m (f0 + 8 * (depot_off D i + 1 + Z.of_nat t)) w)) /\
  (* [comment removed for export] *)
  mapped m n0 kDepotNodesBlock /\ mapped m f0 kStackStoreBlockBytes /\
  al_stackStore L + 32 <= al_theDepot L /\ al_theDepot L + kDepotTabBytes = al_depot_n_uniq_ids L /\ al_depot_n_uniq_ids L + 16 = al_depot_nodes_map1 L.

Definition depot_put_entry : Z := 0x78cb8.
Definition depot_put_stack : Z := 512.
(* [comment removed for export] *)
Definition depot_put_stmt (depot_rep : alayout -> list Segment -> list (list Z) -> Z -> Z -> (word -> option byte) -> Prop) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D : list (list Z)) (k : list Z) (tr n0 f0 lo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 512 -> alloc_ceiling <= lo ->
    a0 = wz tr -> a1 = wz (Z.of_nat (length k)) (* [comment removed for export] *) ->
    (1 <= length k <= 255)%nat -> Forall (fun w => 0 <= w < 2^64) k ->
    bytes_at rsegs m tr (u64s (map (Z_to_bv 64) k)) -> bv_unsigned sp <= tr (* [comment removed for export] *) ->
    tr + 8 * Z.of_nat (length k) <= 2^47 ->
    depot_rep AL_pboth rsegs D n0 f0 m ->
    NoDup (map depot_hashC D) -> Z.of_nat (length D) + 1 < 65535 -> depot_total D + 1 + Z.of_nat (length k) < kStackStoreBlockFrames ->
    aobj n0 kDepotNodesBlock -> n0 + kDepotNodesBlock <= alloc_ceiling -> aobj f0 kStackStoreBlockBytes -> f0 + kStackStoreBlockBytes <= alloc_ceiling ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (snd (depot_putC D k))) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch ((bv_unsigned sp - 512, bv_unsigned sp) ::
                           (al_stackStore AL_pboth, al_depot_nodes_map1 AL_pboth + 8 * kDepotNodesL1) ::
                           (n0, n0 + kDepotNodesBlock) :: (f0, f0 + kStackStoreBlockBytes) :: nil) m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ depot_rep AL_pboth rsegs (fst (depot_putC D k)) n0 f0 m')
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz depot_put_entry) fc None m (seg_rom rsegs)).

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aobj_lin1 H :=
  lazymatch type of H with aobj ?p ?n =>
    let K := fresh "K" H in rename H into K;
    let ix := fresh "ix" in let sx := fresh "sx" in
    destruct (aobj_lin _ _ K) as (ix & sx & H); change (aobjK p n) in K
  end.
Ltac aobj_lin_all := repeat match goal with H : aobj _ _ |- _ => aobj_lin1 H end.
(* [comment removed for export] *)
Ltac aobj_lin1S H :=
  lazymatch type of H with aobj ?p ?n =>
    let ix := fresh "ix" in let sx := fresh "sx" in let L := fresh "L" H in
    destruct (aobj_lin _ _ H) as (ix & sx & L); change (aobjK p n) in H
  end.
Ltac aobj_lin_allS := repeat match goal with H : aobj _ _ |- _ => aobj_lin1S H end.
(* [comment removed for export] *)
Ltac plia1 :=
  lazymatch goal with
  | |- aobj _ _ => first [ assumption
                         | match goal with K : aobjK _ _ |- _ => apply (aobj_sub _ _ _ _ (aobjK_e _ _ K)); lia end
                         | match goal with K : aobj _ _ |- _ => apply (aobj_sub _ _ _ _ K); lia end
                         | apply aobj_hi; [ unfold kHighMemBeg in *; lia | lia | lia ] ]
  | |- aobjK _ _ => apply aobjK_i; plia1
  | |- pz_in _ _ => first [ assumption
                          | match goal with K : aobjK _ _ |- _ => apply (aobj_pz_in _ _ _ _ (aobjK_e _ _ K)); lia end
                          | match goal with K : aobj _ _ |- _ => apply (aobj_pz_in _ _ _ _ K); lia end
                          | unfold pz_in, kLowShadowMapBeg, kHighMemBeg in *; lia ]
  | |- pz0_in _ _ => first [ assumption
                           | match goal with K : aobjK _ _ |- _ => apply (aobj_pz0_in _ _ _ _ (aobjK_e _ _ K)); lia end
                           | match goal with K : aobj _ _ |- _ => apply (aobj_pz0_in _ _ _ _ K); lia end
                           | unfold pz0_in, kLowShadowMapBeg, kHighMemBeg in *; lia ]
  | |- fl_in _ _ => first [ assumption
                          | match goal with K : aobjK _ _ |- _ => apply (aobj_fl_in _ _ _ _ (aobjK_e _ _ K)); lia end
                          | match goal with K : aobj _ _ |- _ => apply (aobj_fl_in _ _ _ _ K); lia end
                          | unfold fl_in, kLowShadowMapBeg, kHighMemBeg in *; lia ]
  | |- m2s_in _ => first [ assumption
                         | match goal with K : aobjK _ _ |- _ => apply (aobj_m2s_in _ _ _ (aobjK_e _ _ K)); lia end
                         | match goal with K : aobj _ _ |- _ => apply (aobj_m2s_in _ _ _ K); lia end
                         | match goal with K : pz_in _ _ |- _ => apply (pz_in_m2s _ _ K); lia end
                         | unfold m2s_in, fl_in, pz_in, pz0_in, kLowShadowMapBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia ]
  | |- _ /\ _ => split; plia1
  | |- _ => lia
  end.
Ltac plia := plia1.
