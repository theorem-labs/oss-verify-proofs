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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARtStmts ARtSscs ARtSeg3 ARtSoqz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition recycle_entry : Z := 0x38f14.
Definition recycle_ret : Z := 0x39084.
Definition dorec_entry : Z := 0x3927c.
Definition dorec_head : Z := 0x392f4.
Definition dorec_callblk : Z := 0x39334.
Definition dorec_retpc : Z := 0x39340.
Definition dorec_batchblk : Z := 0x3934c.
Definition dorec_nextpc : Z := 0x39378.
Definition cbrec_entry : Z := 0x393b4.

(* [comment removed for export] *)
Definition baddr (bs : list (Z * Z)) (i : nat) : Z := nth i (map fst bs) 0.
Definition bsz (bs : list (Z * Z)) (i : nat) : Z := nth i (map snd bs) 0.
Fixpoint lsum (bs : list (Z * Z)) : Z := match bs with [] => 0 | (_, s) :: r => s + lsum r end.
(* [comment removed for export] *)
Fixpoint npop (qmin sz : Z) (bs : list (Z * Z)) : nat :=
  match bs with
  | [] => 0%nat
  | (_, s) :: r => if sz <=? qmin then 0%nat else S (npop qmin (sz - s) r)
  end.
Definition bivls (bs : list (Z * Z)) : list (Z * Z) := map (fun b => (fst b, fst b + 8)) bs.
(* [comment removed for export] *)
Definition bchain (m : word -> option byte) (bs : list (Z * Z)) : Prop :=
  forall i, (i < length bs)%nat -> rw_cells rsegs m (baddr bs i) [C8 (wz (baddr bs (S i))); C8 (wz (bsz bs i))].
(* [comment removed for export] *)
Definition bchain_cut (m : word -> option byte) (bs : list (Z * Z)) (k : nat) : Prop :=
  forall i, (i < length bs)%nat ->
    rw_cells rsegs m (baddr bs i) [C8 (wz (if (S i =? k)%nat then 0 else baddr bs (S i))); C8 (wz (bsz bs i))].
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition bwf (bs : list (Z * Z)) : Prop :=
  (forall i, (i < length bs)%nat -> kHighMemBeg <= baddr bs i /\ baddr bs i + 24 <= alloc_ceiling /\ baddr bs i mod 8 = 0 /\
                                   0 <= bsz bs i < 2^64) /\
  (forall i j, (i < length bs)%nat -> (j < length bs)%nat -> i <> j -> baddr bs i + 24 <= baddr bs j \/ baddr bs j + 24 <= baddr bs i).

(* [comment removed for export] *)
Definition recycle_frame (tn tf tl ts : Z) (s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition dorec_frame (scr : list byte) (cbc cbs : word) (s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 scr; C8 cbc; C8 cbs; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qdrainR0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (q c cache sto hi gf gl gqb qmax qmin nb fb lb qb lo : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    a0 = wz q -> a1 = wz c -> a2 = wz cache -> a3 = wz sto ->
    0x10000 <= q -> q + 192 <= 0x60a000 -> q mod 8 = 0 -> aobj c 32 -> c + 32 <= alloc_ceiling ->
    0 <= hi < 2^15 -> 0 <= gqb -> 0 <= qb -> qmax < gqb + qb < 2^64 -> 0 <= qmax -> 0 <= qmin < 2^64 ->
    nb <> 0 -> 0 <= nb < 2^64 -> 0 <= fb < 2^64 -> 0 <= lb < 2^64 ->
    rw_cells rsegs m (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz hi)] ->
    ro_cells rsegs m (q + 64) [C8 (wz qmax); C8 (wz qmin)] ->
    rw_cells rsegs m (q + 160) [C8 (wz 0); C8 (wz gf); C8 (wz gl); C8 (wz gqb)] ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (forall (t0' t1' a4' a5' a6' a7' : word) (m' : word -> option byte),
        munch [(bv_unsigned sp - 48, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192); (c, c + 32)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        rw_cells rsegs m' (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (wz hi)] ->
        rw_cells rsegs m' (q + 160) [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz (gqb + qb))] ->
        rw_cells rsegs m' c [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
        evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz q) (wz qmin) a2 a3 a4' a5' a6' a7'
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz recycle_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz qdrain_entry) fc None m (seg_rom rsegs)).

Definition qdrainRA_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (q c cache sto hi gn gf gl gqb qmax qmin nb fb lb qb lo : Z) (glnx : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    a0 = wz q -> a1 = wz c -> a2 = wz cache -> a3 = wz sto ->
    0x10000 <= q -> q + 192 <= 0x60a000 -> q mod 8 = 0 -> aobj c 32 -> c + 32 <= alloc_ceiling ->
    kHighMemBeg <= gl -> gl + 24 <= alloc_ceiling -> (c + 32 <= gl \/ gl + 8 <= c) ->
    0 <= hi < 2^15 -> 0 <= gqb -> 0 <= qb -> qmax < gqb + qb < 2^64 -> 0 <= qmax -> 0 <= qmin < 2^64 ->
    nb <> 0 -> 0 <= nb < 2^64 -> gn <> 0 -> 0 <= gn -> gn + nb < 2^64 -> 0 <= fb < 2^64 -> 0 <= lb < 2^64 ->
    rw_cells rsegs m (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz hi)] ->
    ro_cells rsegs m (q + 64) [C8 (wz qmax); C8 (wz qmin)] ->
    rw_cells rsegs m (q + 160) [C8 (wz gn); C8 (wz gf); C8 (wz gl); C8 (wz gqb)] ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m gl [C8 glnx] ->
    (forall (t0' t1' a4' a5' a6' a7' : word) (m' : word -> option byte),
        munch [(bv_unsigned sp - 48, bv_unsigned sp); (q + 152, q + 156); (q + 160, q + 192); (c, c + 32); (gl, gl + 8)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        rw_cells rsegs m' (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (wz hi)] ->
        rw_cells rsegs m' (q + 160) [C8 (wz (gn + nb)); C8 (wz gf); C8 (wz lb); C8 (wz (gqb + qb))] ->
        rw_cells rsegs m' c [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
        rw_cells rsegs m' gl [C8 (wz fb)] ->
        evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz q) (wz qmin) a2 a3 a4' a5' a6' a7'
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz recycle_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz qdrain_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition recycle_stack : Z := 80.
Definition recycle_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (q qmin hi gl gqb lo : Z) (bs : list (Z * Z)) (Q : machine_state -> Prop),
    let gn := Z.of_nat (length bs) in
    let k := npop qmin gqb bs in
    let kz := Z.of_nat k in
    let psum := lsum (firstn k bs) in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> alloc_ceiling <= lo ->
    a0 = wz q -> a1 = wz qmin ->
    0x10000 <= q -> q + 192 <= 0x60a000 -> q mod 8 = 0 ->
    0 <= hi < 2^15 -> 0 <= qmin < 2^64 -> 0 <= gqb -> gqb * 100 < 2^64 -> gn < 2^24 -> 0 <= gl < 2^64 ->
    gn * 8192 <= gqb -> (gn * 16384 <= gqb \/ gqb <= gn * 8192) ->          (* [comment removed for export] *)
    lsum bs <= gqb -> gqb - lsum bs <= qmin ->                              (* [comment removed for export] *)
    bwf bs -> bchain m bs ->
    rw_cells rsegs m (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (wz hi)] ->
    rw_cells rsegs m (q + 160) [C8 (wz gn); C8 (wz (baddr bs 0)); C8 (wz gl); C8 (wz gqb)] ->
    (forall (t0' t1' t2' a4' a5' a6' a7' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -80)
                 (recycle_frame kz (if (k =? 0)%nat then 0 else baddr bs 0) (if (k =? 0)%nat then 0 else baddr bs (k - 1)) psum
                                s4 s3 s2 s1 s0 ra) ->
        rw_cells rsegs m' (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz hi)] ->
        rw_cells rsegs m' (q + 160) [C8 (wz (gn - kz)); C8 (wz (baddr bs k));
                                     C8 (wz (if ((k =? length bs)%nat && (0 <? k)%nat)%bool then 0 else gl)); C8 (wz (gqb - psum))] ->
        bchain_cut m' bs k ->
        munch ((bv_unsigned sp - 80, bv_unsigned sp) :: (q + 152, q + 156) :: (q + 160, q + 192) :: bivls (firstn k bs)) m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp - 80) ->
        evt rsegs Q (MS (mkR (wz recycle_ret) (wz (bv_unsigned sp + -80)) gp tp t0' t1' t2' s0 s1
                            (wz q) (wz (bv_unsigned sp + -80)) a2 a3 a4' a5' a6' a7'
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz dorec_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz recycle_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition recycle_post_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (usp lo tn tf tl ts : Z) (s4v s3v s2v s1v s0v ra0 : word),
    mem_inv rsegs m -> stk rsegs m lo (usp - 80) -> lo <= usp - 80 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    rw_cells rsegs m (usp + -80) (recycle_frame tn tf tl ts s4v s3v s2v s1v s0v ra0) ->
    bv_unsigned ra0 mod 2 = 0 ->
    evt rsegs (fun ms' => exists m',
                 ms' = MS (mkR ra0 (wz usp) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7
                              s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom rsegs)
                 /\ munch [(usp - 80, usp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp)
        (MS (mkR (wz recycle_ret) (wz (usp + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz recycle_ret) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dorec_stack : Z := 112.
Definition dorec_entry0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (T lo tf tl ts : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> alloc_ceiling <= lo ->
    a1 = wz T -> alloc_ceiling <= T -> T + 32 <= 2^47 -> T mod 8 = 0 -> (T + 32 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= T) ->
    rw_cells rsegs m T [C8 (wz 0); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists a0' a1' m',
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ rw_cells rsegs m' T [C8 (wz 0); C8 (wz tf); C8 (wz tl); C8 (wz ts)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz dorec_entry) fc None m (seg_rom rsegs)).

Definition dorec_entryS_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (T lo tn tf tl ts : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 112 -> alloc_ceiling <= lo ->
    a1 = wz T -> alloc_ceiling <= T -> T + 32 <= 2^47 -> T mod 8 = 0 -> (T + 32 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= T) ->
    tn <> 0 -> 0 <= tn < 2^64 ->
    rw_cells rsegs m T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
    (forall (scr : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -112) (dorec_frame scr a2 a3 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
        rw_cells rsegs m' T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
        munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 112) ->
        evt rsegs Q (MS (mkR ra (wz (bv_unsigned sp + -112)) gp tp t0 t1 t2 (wz T) (wz 0xb1558) (wz tn) (wz 0xb12c0) a2 a3 a4 a5 a6 a7
                            (wz 0xb1598) (wz 0xb1808) s4 (wz (2^37)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (wz dorec_head) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz dorec_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition dorec_pop_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (T tn b tl ts nx bsize cnt : Z)
         (K0 K1 : (word -> option byte) -> Prop) (Q : machine_state -> Prop),
    mem_inv rsegs m ->
    alloc_ceiling <= T -> T + 32 <= 2^47 -> T mod 8 = 0 ->
    kHighMemBeg <= b -> b + 24 <= alloc_ceiling -> b mod 8 = 0 ->
    1 <= tn < 2^64 -> 0 <= nx < 2^64 -> 0 <= tl < 2^64 -> 0 <= bsize -> bsize <= ts < 2^64 -> 0 <= cnt < 2^64 ->
    rw_cells rsegs m T [C8 (wz tn); C8 (wz b); C8 (wz tl); C8 (wz ts)] ->
    rw_cells rsegs m b [C8 (wz nx); C8 (wz bsize); C8 (wz cnt)] ->
    (forall m', cnt = 0 ->
        rw_cells rsegs m' T [C8 (wz (tn - 1)); C8 (wz nx); C8 (wz (if nx =? 0 then 0 else tl)); C8 (wz (ts - bsize))] ->
        rw_cells rsegs m' b [C8 (wz nx); C8 (wz bsize); C8 (wz cnt)] ->
        munch [(T, T + 32)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> K0 m' ->
        evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (wz T) s1 (wz bsize) (wz (ts - bsize)) a2 a3 a4 a5 a6 a7
                            s2 s3 (wz b) s5 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz dorec_batchblk) fc None m' (seg_rom rsegs))) ->
    (forall m', cnt <> 0 ->
        rw_cells rsegs m' T [C8 (wz (tn - 1)); C8 (wz nx); C8 (wz (if nx =? 0 then 0 else tl)); C8 (wz (ts - bsize))] ->
        rw_cells rsegs m' b [C8 (wz nx); C8 (wz bsize); C8 (wz cnt)] ->
        munch [(T, T + 32)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> K1 m' ->
        evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (wz T) s1 (wz bsize) (wz (ts - bsize)) a2 a3 a4 a5 a6 a7
                            s2 s3 (wz b) s5 (wz cnt) (wz (b + 152)) (wz (cnt + 16)) (wz 16) s10 s11 t3 t4 t5 t6)
                        F (wz dorec_callblk) fc None m' (seg_rom rsegs))) ->
    (forall m', munch [(T, T + 32)] m m' -> K0 m') -> (forall m', munch [(T, T + 32)] m m' -> K1 m') ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 (wz T) s1 (wz tn) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz dorec_head) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition dorec_call_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i : Z) (p : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> kHighMemBeg <= b -> b + 24 + 8 * i + 8 <= alloc_ceiling -> b mod 8 = 0 -> 0 <= i ->
    bv_unsigned sp + 8 < 2^64 ->
    rw_cells rsegs m (b + 24 + 8 * i) [C8 p] ->
    evt rsegs Q (MS (mkR (wz dorec_retpc) sp gp tp t0 t1 t2 s0 s1 (wz (bv_unsigned sp + 8)) p a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 (wz (b + 152 + 8 * i)) s8 (wz (16 + i)) s10 s11 t3 t4 t5 t6) F (wz cbrec_entry) fc None m (seg_rom rsegs)) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz (b + 152 + 8 * i)) s8 (wz (16 + i)) s10 s11 t3 t4 t5 t6)
                    F (wz dorec_callblk) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition dorec_ret_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b i cnt : Z) (Q : machine_state -> Prop),
    0 <= i < cnt -> cnt < 2^60 -> kHighMemBeg <= b -> b + 8192 <= alloc_ceiling ->
    (i + 1 < cnt ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz (b + 152 + 8 * (i + 1))) (wz (cnt + 16))
                         (wz (16 + (i + 1))) s10 s11 t3 t4 t5 t6) F (wz dorec_callblk) fc None m (seg_rom rsegs))) ->
    (i + 1 = cnt ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz (b + 152 + 8 * (i + 1))) (wz (cnt + 16))
                         (wz (16 + (i + 1))) s10 s11 t3 t4 t5 t6) F (wz dorec_batchblk) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (wz (b + 152 + 8 * i)) (wz (cnt + 16))
                        (wz (16 + i)) s10 s11 t3 t4 t5 t6) F (wz dorec_retpc) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition dorec_batch_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sb kb : Z) (cbc : word) (Q : machine_state -> Prop),
    let b := sb + 24 * 2^32 + 16 * kb in
    mem_inv rsegs m -> alloc_ceiling <= bv_unsigned sp -> bv_unsigned sp + 112 <= 2^47 -> bv_unsigned sp mod 8 = 0 ->
    0 <= sb -> sb + 2^37 < 2^64 -> 0 <= kb < 2^28 ->
    ro_cells rsegs m 0xb1578 [C8 (wz sb)] ->
    rw_cells rsegs m (bv_unsigned sp + 8) [C8 cbc] ->
    evt rsegs Q (MS (mkR (wz dorec_nextpc) sp gp tp t0 t1 t2 s0 (wz 0xb1558) cbc (wz 0xb1558) (wz 24) (wz b) a4 a5 a6 a7
                        s2 s3 (wz b) (wz (2^37)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz lcdealloc_entry) fc None m (seg_rom rsegs)) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 (wz 0xb1558) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (wz b) (wz (2^37)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz dorec_batchblk) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition dorec_next_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (usp lo T tn tf tl ts : Z) (scr : list byte)
         (cbc cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (usp - 112) -> lo <= usp - 112 -> alloc_ceiling <= lo -> usp <= 2^47 -> usp mod 16 = 0 ->
    alloc_ceiling <= T -> T + 32 <= 2^47 -> T mod 8 = 0 -> (T + 32 <= usp - 112 \/ usp <= T) -> 0 <= tn < 2^64 ->
    rw_cells rsegs m T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
    rw_cells rsegs m (usp + -112) (dorec_frame scr cbc cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    bv_unsigned ra0 mod 2 = 0 ->
    (tn <> 0 ->
     evt rsegs Q (MS (mkR ra (wz (usp + -112)) gp tp t0 t1 t2 (wz T) s1 (wz tn) a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz dorec_head) fc None m (seg_rom rsegs))) ->
    (tn = 0 -> stk rsegs m lo usp ->
        evt rsegs Q (MS (mkR ra0 (wz usp) gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7
                            s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6) F (ret_pc ra0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (wz (usp + -112)) gp tp t0 t1 t2 (wz T) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz dorec_nextpc) fc None m (seg_rom rsegs)).

End CEIL.
