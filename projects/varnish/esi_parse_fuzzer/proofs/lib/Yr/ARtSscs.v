(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ACells ARtStmts.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Definition TP : Z := 0x5e83d8.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tls_consts (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)]                        (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaaf68 [C8 (wz 0xa2ea0)]                       (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa9e90 [C8 (wz 1); C8 (wz 0xfffffffffffff800)]  (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x5e83d0 [C8 (wz 0x5e83f8)]                       (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x5e8400 [C8 (wz 0x5e8bd8)]                       (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa9180 [C8 (wz 0x146ee8)] /\ ro_cells rsegs m (0x146ee8 + 137) [C1 (Z_to_bv 8 1)]  (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa91e0 [C8 (wz 0x144e58)] /\ ro_cells rsegs m 0x144e58 [C4 (wz 0)]                 (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa9ea0 [C8 (wz 8)].                              (* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition tls_dyn (m : word -> option byte) (dtls dtvbeg : Z) : Prop :=
     ro_cells rsegs m 0x5e83e0 [C8 (wz dtls)] (* [comment removed for export] *) /\ ro_cells rsegs m (dtls + 24) [C8 (wz dtvbeg)]
  /\ dtvbeg <> 0 /\ 0 <= dtvbeg < 2^64 /\ aobj dtls 32 /\ dtls + 32 <= alloc_ceiling.
Definition tlsfs_entry : Z := 0x47a58.
Definition tlsfs_stack : Z := 176.     (* [comment removed for export] *)
Definition tlsfs_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz TP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).
Definition tlsfs_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tsd ctx thr tlsb tlse dtls dtvbeg lo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 -> alloc_ceiling <= lo ->
    tp = wz TP -> a0 = wz 0xa9e90 ->
    tls_consts m -> tls_dyn m dtls dtvbeg -> thread_cells m tp tsd ctx thr ->
    ro_cells rsegs m (thr + 48) [C8 (wz tlsb); C8 (wz tlse)] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (tlsfs_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz tlsfs_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fs_hdr (m : word -> option byte) (fs : Z) : Prop :=
     ro_cells rsegs m 0x5e83d8 [C8 (wz fs)]                             (* [comment removed for export] *)
  /\ ro_cells rsegs m (fs + 88) [C8 (wz kFakeStackSizeLog)] /\ ro_cells rsegs m (fs + 96) [C1 (Z_to_bv 8 0)]
  /\ fs mod 4096 = 0 /\ aobj fs kFakeStackBytes /\ fs + kFakeStackBytes <= alloc_ceiling.
Definition smalloc_entry (k : Z) : Z := match k with 0 => 0x4280c | 1 => 0x42980 | _ => 0x42b10 end.
(* [comment removed for export] *)
Definition smalloc_stack : Z := 224.
Definition smalloc_post (k : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (fs h sz lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  let pos := h mod fslots k in
  let ff := fframe_addr fs k pos in
  let fl := fflag_addr fs k pos in
  let nsh := (if Z.leb k 6 then fsize k / 8 else sz / 8) in
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz ff) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (fs + 8 * k, fs + 8 * k + 8); (fl, fl + 1);
              (ff, ff + fsize k); (sh ff, sh ff + nsh)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (fs + 8 * k) (le8 (wz (h + 1)))                 (* [comment removed for export] *)
    /\ bytes_at rsegs m' fl [Z_to_bv 8 1]                                 (* [comment removed for export] *)
    /\ bytes_at rsegs m' (ff + 24) (le8 sp)                              (* [comment removed for export] *)
    /\ bytes_at rsegs m' (saved_flag_ptr ff k) (le8 (wz fl))             (* [comment removed for export] *)
    /\ bytes_at rsegs m' (sh ff) (repeat (Z_to_bv 8 0) (Z.to_nat nsh)).  (* [comment removed for export] *)
Definition smalloc_stmt (k : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (tsd ctx thr tlsb tlse dtls dtvbeg fs h sz lo : Z) (oldsh : list byte),
    let pos := h mod fslots k in
    let ff := fframe_addr fs k pos in
    let fl := fflag_addr fs k pos in
    let nsh := (if Z.leb k 6 then fsize k / 8 else sz / 8) in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 224 -> alloc_ceiling <= lo ->
    tp = wz TP -> a0 = wz sz -> (k = 7 -> sz mod 8 = 0 /\ 8 <= sz <= fsize 7) ->
    tls_consts m -> tls_dyn m dtls dtvbeg -> thread_cells m tp tsd ctx thr ->
    ro_cells rsegs m (thr + 48) [C8 (wz tlsb); C8 (wz tlse)] ->
    poison_consts m ->                                                    (* [comment removed for export] *)
    fs_hdr m fs ->
    0 <= h < 2^63 ->
    bytes_at rsegs m (fs + 8 * k) (le8 (wz h)) ->                         (* [comment removed for export] *)
    bytes_at rsegs m fl [Z_to_bv 8 0] ->                                  (* [comment removed for export] *)
    mapped m fs kFakeStackBytes ->                                        (* [comment removed for export] *)
    rw_cells rsegs m (sh ff) [CB (Z.to_nat nsh) oldsh] ->                 (* [comment removed for export] *)
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (smalloc_post k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs h sz lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz (smalloc_entry k)) fc None m (seg_rom rsegs)).
Definition smalloc0_stmt : Prop := smalloc_stmt 0.
Definition smalloc1_stmt : Prop := smalloc_stmt 1.
Definition smalloc7_stmt : Prop := smalloc_stmt 7.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sfree7_entry : Z := 0x42c8c.
Definition sfree7_stack : Z := 96.      (* [comment removed for export] *)
Definition sfree7_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ff fl sz lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (fl, fl + 1); (sh ff, sh ff + sz / 8)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' fl [Z_to_bv 8 0]                                             (* [comment removed for export] *)
    /\ bytes_at rsegs m' (sh ff) (repeat (Z_to_bv 8 0xf5) (Z.to_nat (sz / 8))).     (* [comment removed for export] *)
Definition sfree7_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ff fl sz lo : Z) (oldfl : byte) (oldsh : list byte),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> alloc_ceiling <= lo ->
    a0 = wz ff -> a1 = wz sz -> sz mod 8 = 0 -> 8 <= sz <= fsize 7 ->
    ff mod 8 = 0 -> aobj ff (fsize 7) -> ff + fsize 7 <= alloc_ceiling ->
    aobj fl 1 -> fl + 1 <= alloc_ceiling ->
    poison_consts m ->
    ro_cells rsegs m (saved_flag_ptr ff 7) [C8 (wz fl)] ->
    rw_cells rsegs m fl [C1 oldfl] ->
    rw_cells rsegs m (sh ff) [CB (Z.to_nat (sz / 8)) oldsh] ->
    (* [comment removed for export] *)
    (fl + 1 <= ff \/ ff + fsize 7 <= fl) -> (fl + 1 <= sh ff \/ sh ff + sz / 8 <= fl) ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (sfree7_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ff fl sz lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz sfree7_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dealloc_entry : Z := 0x36e88.
Definition qchunk_entry : Z := 0x3b410.
Definition dealloc_stack : Z := 96.     (* [comment removed for export] *)
Definition kInvalidTidShifted : Z := 0xFFFFFFFF00000000.
Definition dealloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (this p n b1 sto tsd ctx thr fr fd lo : Z) (old : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 -> alloc_ceiling <= lo ->
    tp = wz TP -> a0 = wz this -> a1 = wz p -> a4 = wz sto -> a5 = wz 1 ->
    0 <= this /\ this + 4096 <= alloc_ceiling ->
    p mod 16 = 0 -> aobj (p + -16) 24 -> p + 8 <= alloc_ceiling ->
    0 <= n < 2^32 -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= fr < 2^64 -> 0 <= fd < 2^64 ->
    rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m p [C8 old] ->
    ro_cells rsegs m 0x146e88 [C8 (wz 0)] ->                             (* [comment removed for export] *)
    thread_cells m tp tsd ctx thr ->
    rw_cells rsegs m (thr + 2824) [C8 (wz fr); C8 (wz fd)] ->            (* [comment removed for export] *)
    (* [comment removed for export] *)
    tsd + 8 <= p + -16 -> (p + 8 <= ctx \/ ctx + 0x10000 <= p + -16) -> (p + 8 <= thr \/ thr + 4096 <= p + -16) ->
    bv_unsigned ra mod 2 = 0 ->
    (forall (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        rw_cells rsegs m' p [C8 (wz kInvalidTidShifted)] ->
        rw_cells rsegs m' (thr + 2824) [C8 (wz (fr + 1)); C8 (wz (n + fd))] ->     (* [comment removed for export] *)
        munch [(bv_unsigned sp - 96, bv_unsigned sp); (p + -16, p + -12); (p, p + 8); (thr + 2824, thr + 2840)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz this) (wz (p + -16)) (wz p) (wz sto) a4' a5' a6' a7'
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz qchunk_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz dealloc_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition qput_entry : Z := 0x3b588.
Definition qchunk_stack : Z := 560.    (* [comment removed for export] *)
Definition qchunk_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (this p n b1 sto tsd ctx thr lo : Z) (D : list (list Z)) (k : list Z) (tr n0 f0 : Z) (fctx : word)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 560 -> alloc_ceiling <= lo ->
    tp = wz TP -> a0 = wz this -> a1 = wz (p + -16) -> a2 = wz p -> a3 = wz sto ->
    0 <= this /\ this + 4096 <= alloc_ceiling ->
    p mod 16 = 0 -> aobj (p + -16) 24 -> p + 8 <= alloc_ceiling -> 0 <= n < 2^32 -> 0 <= b1 < 256 ->
    rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m p [C8 fctx] ->
    thread_cells m tp tsd ctx thr -> ro_cells rsegs m thr [C8 (wz ctx)] -> ro_cells rsegs m (ctx + 8) [C4 (wz kMainTid)] ->
    (* [comment removed for export] *)
    ro_cells rsegs m sto [C8 (wz tr); C8 (wz (Z.of_nat (length k)))] -> bv_unsigned sp <= sto -> sto + 16 <= 2^47 ->
    (1 <= length k <= 255)%nat -> Forall (fun w => 0 <= w < 2^64) k ->
    bytes_at rsegs m tr (u64s (map (Z_to_bv 64) k)) -> bv_unsigned sp <= tr -> tr + 8 * Z.of_nat (length k) <= 2^47 ->
    (* [comment removed for export] *)
    ARt_u2d.depot_repL AL_pasan rsegs D n0 f0 m ->
    NoDup (map depot_hashC D) -> Z.of_nat (length D) + 1 < 65535 -> depot_total D + 1 + Z.of_nat (length k) < kStackStoreBlockFrames ->
    aobj n0 kDepotNodesBlock -> n0 + kDepotNodesBlock <= alloc_ceiling -> aobj f0 kStackStoreBlockBytes -> f0 + kStackStoreBlockBytes <= alloc_ceiling ->
    (* [comment removed for export] *)
    (p + 8 <= ctx \/ ctx + 0x10000 <= p + -16) -> (p + 8 <= thr \/ thr + 4096 <= p + -16) ->
    (p + 8 <= n0 \/ n0 + kDepotNodesBlock <= p + -16) -> (p + 8 <= f0 \/ f0 + kStackStoreBlockBytes <= p + -16) ->
    bv_unsigned ra mod 2 = 0 ->
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        rw_cells rsegs m' p [C8 (wz (snd (depot_putC D k)))] ->
        ARt_u2d.depot_repL AL_pasan rsegs (fst (depot_putC D k)) n0 f0 m' ->
        munch ((bv_unsigned sp - 560, bv_unsigned sp) :: (p, p + 8) ::
               (al_stackStore AL_pasan, al_depot_nodes_map1 AL_pasan + 8 * kDepotNodesL1) ::
               (n0, n0 + kDepotNodesBlock) :: (f0, f0 + kStackStoreBlockBytes) :: nil) m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz (this + 728)) (wz (thr + 80)) (wz (thr + 208)) (wz sto) (wz (p + -16)) (wz n) a6' a7'
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (wz qput_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz qchunk_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition enqueue_entry : Z := 0x3b738.
Definition enqueue_stack : Z := 64.
Definition enqueue_fast_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c cache sto mch size nb fb lb qb nx bsz cnt lo : Z) (junk : word),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    a0 = wz c -> a1 = wz cache -> a2 = wz sto -> a3 = wz mch -> a4 = wz size ->
    aobj c 32 -> c + 32 <= alloc_ceiling -> kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling ->
    (c + 32 <= lb \/ lb + 8192 <= c) ->
    nb <> 0 -> 0 <= nb < 2^64 -> 0 <= cnt < 1021 -> 0 <= size < 2^64 -> 0 <= mch < 2^64 ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz cnt)] ->
    rw_cells rsegs m (lb + 24 + 8 * cnt) [C8 junk] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (c, c + 32); (lb, lb + 24); (lb + 24 + 8 * cnt, lb + 32 + 8 * cnt)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ rw_cells rsegs m' c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz (qb + size))]
                 /\ rw_cells rsegs m' lb [C8 (wz nx); C8 (wz (bsz + size)); C8 (wz (cnt + 1))]
                 /\ rw_cells rsegs m' (lb + 24 + 8 * cnt) [C8 (wz mch)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz enqueue_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition qput_stack : Z := 144.      (* [comment removed for export] *)
Definition qput_fast_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (q c cache sto p n b1 qmax cmax r8 nb fb lb qb nx bsz cnt lo : Z) (fctx junk : word) (oldsh : list byte),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> alloc_ceiling <= lo ->
    a0 = wz q -> a1 = wz c -> a2 = wz cache -> a3 = wz sto -> a4 = wz (p + -16) -> a5 = wz n ->
    0x10000 <= q -> q + 88 <= 0x60a000 -> 0 <= cache < 2^64 -> 0 <= sto < 2^64 ->
    p mod 16 = 0 -> aobj (p + -16) (16 + 8 * r8) -> p + 8 * r8 <= alloc_ceiling -> 1 <= n < 2^32 -> 0 <= b1 < 256 ->
    8 * r8 - 8 < n <= 8 * r8 ->
    cmax <> 0 -> 0 <= cmax < 2^64 -> 0 <= qmax < 2^64 -> n <= qmax ->
    aobj c 32 -> c + 32 <= alloc_ceiling -> kHighMemBeg <= lb -> lb + 8192 <= alloc_ceiling ->
    (c + 32 <= lb \/ lb + 8192 <= c) -> (c + 32 <= p + -16 \/ p + 8 * r8 <= c) -> (lb + 8192 <= p + -16 \/ p + 8 * r8 <= lb) ->
    nb <> 0 -> 0 <= nb < 2^64 -> 0 <= cnt < 1021 -> 0 <= qb -> qb + n <= cmax ->
    ro_cells rsegs m (q + 64) [C8 (wz qmax)] -> ro_cells rsegs m (q + 80) [C8 (wz cmax)] ->
    ro_cells rsegs m 0xa9188 [C8 (wz 0xb2bb8)] -> ro_cells rsegs m (0xb2bb8 + 48) [C4 (wz 0)] ->   (* [comment removed for export] *)
    poison_consts m ->
    rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m (sh p) [CB (Z.to_nat r8) oldsh] ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m lb [C8 (wz nx); C8 (wz bsz); C8 (wz cnt)] ->
    rw_cells rsegs m (lb + 24 + 8 * cnt) [C8 junk] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (sh p, sh p + r8); (c, c + 32); (lb, lb + 24);
                           (lb + 24 + 8 * cnt, lb + 32 + 8 * cnt)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8))
                 /\ rw_cells rsegs m' c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz (qb + n))]
                 /\ rw_cells rsegs m' lb [C8 (wz nx); C8 (wz (bsz + n)); C8 (wz (cnt + 1))]
                 /\ rw_cells rsegs m' (lb + 24 + 8 * cnt) [C8 (wz (p + -16))])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz qput_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition free_mid_entry : Z := 0x589b0.
Definition free_mid_stmt : Prop :=
  forall (rax gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (fp p tsd ctx thr top bot lo : Z) (ra0 v s5v s4v s3v s2v s1v j0 j3 : word) (pad j12 jb : list byte)
         (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2128) -> lo <= fp - 2128 - 224 -> alloc_ceiling <= lo ->
    tp = wz TP -> fp mod 16 = 0 -> fp <= 2^47 ->
    0 < p -> aobj (p + -16) 16 -> p < alloc_ceiling ->
    4096 <= bv_unsigned ra0 -> bv_unsigned ra0 <> 0x58ab4 -> bv_unsigned v <= fp -> 0 <= top < 2^64 -> 0 <= bot < 2^64 ->
    thread_cells m tp tsd ctx thr ->
    ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)] ->                                              (* [comment removed for export] *)
    ro_cells rsegs m 0xa9170 [C8 (wz 0x144e60)] -> ro_cells rsegs m 0x144e60 [C8 (wz 4096)] ->   (* [comment removed for export] *)
    ro_cells rsegs m 0xb60bc [C4 (wz 30)] ->                                                     (* [comment removed for export] *)
    ro_cells rsegs m 0xa9180 [C8 (wz 0x146ee8)] -> ro_cells rsegs m (0x146ee8 + 34) [C1 (Z_to_bv 8 1)] ->  (* [comment removed for export] *)
    ro_cells rsegs m (0xb65c8 + 8 * Z.shiftr p 32) [C8 (wz 0)] ->                               (* [comment removed for export] *)
    rw_cells rsegs m (thr + 8) [C8 (wz top); C8 (wz bot)] -> ro_cells rsegs m (thr + 40) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
    (thr + 4096 <= lo \/ fp - 2128 + 2^16 <= thr) ->
    rw_cells rsegs m (fp + -2128) [C8 j0; CB 8 j12; CB 2040 jb; C8 j3] ->                         (* [comment removed for export] *)
    rw_cells rsegs m (fp + -64) [CB 8 pad; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 v; C8 ra0] ->   (* [comment removed for export] *)
    (forall (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (jb1 jrest : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (fp + -2128) [C8 (wz (fp + -2128 + 16))] ->
        rw_cells rsegs m' (fp + -2128 + 32) [CB 2024 jrest] ->                                 (* [comment removed for export] *)
        rw_cells rsegs m' (fp + -2128 + 2056) [C8 (wz fp)] ->
        (if unwind_depth2 top bot fp
         then rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz 2)] /\ rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58ab4); C8 ra0]
         else rw_cells rsegs m' (fp + -2128 + 8) [C4 (wz 1)] /\ rw_cells rsegs m' (fp + -2128 + 16) [C8 (wz 0x58ab4); CB 8 jb1]) ->
        rw_cells rsegs m' (fp + -2128 + 12) [C4 (wz 0)] ->
        rw_cells rsegs m' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)] ->
        rw_cells rsegs m' (fp + -64) [CB 8 pad; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 v; C8 ra0] ->
        munch [(fp - 2128 - 224, fp - 2128); (fp + -2128, fp + -2128 + 32); (fp + -2128 + 2056, fp + -2128 + 2064);
               (thr + off_th_unwinding, thr + off_th_unwinding + 1)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (fp - 2128) ->
        evt rsegs Q (MS (mkR (wz 0x58b24) (wz (fp + -2128)) gp tp t0' t1' t2' (wz fp) (wz p)
                         (wz 0xb1d58) (wz p) (wz 0) (wz 0) (wz (fp + -2128)) (wz 1) a6' a7'
                         (wz 0x58ab4) (wz 1) (wz (fp + -2128)) (wz (fp + -81)) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz dealloc_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR rax (wz (fp + -2128)) gp tp t0 t1 t2 (wz fp) (wz p) (wz 0xb65c0) a1 a2 a3 a4 a5 a6 a7
                     ra0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz free_mid_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition free_icpt_entry : Z := 0x5897c.
Definition ia_entry : Z := 0x6467c.
Definition free_pro_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 2128 ->
    (forall (junk pad : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -2128) [CB 2064 junk] ->
        rw_cells rsegs m' (bv_unsigned sp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        munch [(bv_unsigned sp - 2128, bv_unsigned sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (bv_unsigned sp - 2128) ->
        evt rsegs Q (MS (mkR (wz 0x589b0) (wz (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp a0 a0 a1 a2 a3 a4 a5 a6 a7
                            ra s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz ia_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz free_icpt_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition free_epi_entry : Z := 0x58b24.
Definition free_epi_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fp lo : Z) (s5v s4v s3v s2v s1v s0v ra0 : word)
         (junk pad : list byte) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (fp - 2128) -> lo <= fp - 2128 -> sp = wz (fp + -2128) -> 0 <= fp - 2128 -> fp <= 2^47 ->
    rw_cells rsegs m (fp + -2128) [CB 2064 junk] ->
    rw_cells rsegs m (fp + -64) [CB 8 pad; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    (stk rsegs m lo fp ->
        evt rsegs Q (MS (mkR ra0 (wz fp) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz free_epi_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition ia_fast_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    ro_cells rsegs m 0x144e48 [C1 (Z_to_bv 8 1)] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0xb65c0) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
                 /\ stk rsegs m' lo (bv_unsigned sp))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ia_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition IAB : Z := 0xb65c0.
Definition ia_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (hi lo : Z)
         (j0 : byte) (j1 j3 j4 : list byte) (ws : list word),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 48 -> alloc_ceiling <= lo ->
    0 <= hi < 2^15 ->
    rw_cells rsegs m 0x144e48 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz hi)] ->      (* [comment removed for export] *)
    ro_cells rsegs m 0xa9170 [C8 (wz 0x144e60)] -> ro_cells rsegs m 0x144e60 [C8 (wz 4096)] ->   (* [comment removed for export] *)
    rw_cells rsegs m IAB [C1 j0] ->
    rw_cells rsegs m (IAB + 8) [CB (Z.to_nat 262144) j1] ->
    u64arr rsegs m (IAB + 0x40040) ws -> length ws = 432%nat ->
    rw_cells rsegs m (IAB + 0x40dc0) [CB (Z.to_nat 262728) j3] ->
    rw_cells rsegs m (IAB + 0x81008) [CB 40 j4] ->
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz IAB) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x144e48, 0x144e4c); (IAB, IAB + 1); (IAB + 8, IAB + 8 + 262144);
                           (IAB + 0x40040, IAB + 0x40040 + 3456); (IAB + 0x40dc0, IAB + 0x40dc0 + 262728); (IAB + 0x81008, IAB + 0x81008 + 40)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ rw_cells rsegs m' 0x144e48 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (wz hi)]
                 /\ rw_cells rsegs m' IAB [C1 (Z_to_bv 8 0)]
                 /\ rw_cells rsegs m' (IAB + 8) [CB (Z.to_nat 262144) (repeat (Z_to_bv 8 0) (Z.to_nat 262144))]
                 /\ u64arr rsegs m' (IAB + 0x40040) (repeat (wz 0) 432)
                 /\ rw_cells rsegs m' (IAB + 0x40dc0) [C8 (wz 4096); C8 (wz (IAB + 0x40dd0)); CB (Z.to_nat 262712) (repeat (Z_to_bv 8 0) (Z.to_nat 262712))]
                 /\ rw_cells rsegs m' (IAB + 0x81008) [CB 40 (repeat (Z_to_bv 8 0) 40)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ia_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition enqueue_new0_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c C sto mch size fb lb qb cnt maxc sb lo : Z) (ks : list word) (kw statv : word) (bj0 bj1 bj2 bj3 : word),
    let b := sb + 24 * 2^32 + 16 * bv_unsigned kw in
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 64 -> alloc_ceiling <= lo ->
    a0 = wz c -> a1 = wz C -> a2 = wz sto -> a3 = wz mch -> a4 = wz size ->
    aobj c 32 -> c + 32 <= alloc_ceiling -> aobj C 3888 -> C + 3888 <= alloc_ceiling -> C mod 16 = 0 ->
    (c + 32 <= C + 1920 \/ C + 2584 <= c) ->
    0 <= sb -> sb + 2^37 <= 2^47 -> kHighMemBeg <= b -> b + 8192 <= alloc_ceiling ->
    (b + 32 <= c \/ c + 32 <= b) -> (b + 32 <= C + 1920 \/ C + 2584 <= b) ->
    1 <= cnt <= 16 -> length ks = 16%nat -> nth_error ks (Z.to_nat (cnt - 1)) = Some kw -> bv_unsigned kw < 2^32 ->
    0 <= size < 2^64 -> 0 <= mch < 2^64 ->
    ro_cells rsegs m 0xb1d78 [C8 (wz sb)] ->                                                         (* [comment removed for export] *)
    rw_cells rsegs m c [C8 (wz 0); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    rw_cells rsegs m (C + 1920) [C4 (wz cnt); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)] ->     (* [comment removed for export] *)
    rw_cells rsegs m (C + 2576) [C8 statv] ->                                                        (* [comment removed for export] *)
    rw_cells rsegs m b [C8 bj0; C8 bj1; C8 bj2; C8 bj3] ->                                          (* [comment removed for export] *)
    bv_unsigned ra mod 2 = 0 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' m',
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
                 /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (c, c + 32); (C + 1920, C + 1924); (C + 2576, C + 2584); (b, b + 32)] m m'
                 /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
                 /\ rw_cells rsegs m' c [C8 (wz 1); C8 (wz b); C8 (wz b); C8 (wz (qb + (size + 8192)))]
                 /\ rw_cells rsegs m' (C + 1920) [C4 (wz (cnt - 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)]
                 /\ rw_cells rsegs m' (C + 2576) [C8 statv']
                 /\ rw_cells rsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz enqueue_entry) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition qdrain_entry : Z := 0x38e90.
Definition qput_pre_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (q c cache sto p n b1 qmax cmax r8 lo : Z) (oldsh : list byte) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> alloc_ceiling <= lo ->
    a0 = wz q -> a1 = wz c -> a2 = wz cache -> a3 = wz sto -> a4 = wz (p + -16) -> a5 = wz n ->
    0x10000 <= q -> q + 88 <= 0x60a000 -> 0 <= cache < 2^64 -> 0 <= sto < 2^64 -> 0 <= c < 2^64 ->
    p mod 16 = 0 -> aobj (p + -16) (16 + 8 * r8) -> p + 8 * r8 <= alloc_ceiling -> 1 <= n < 2^32 -> 0 <= b1 < 256 ->
    8 * r8 - 8 < n <= 8 * r8 ->
    cmax <> 0 -> 0 <= cmax < 2^64 -> 0 <= qmax < 2^64 -> n <= qmax ->
    ro_cells rsegs m (q + 64) [C8 (wz qmax)] -> ro_cells rsegs m (q + 80) [C8 (wz cmax)] ->
    ro_cells rsegs m 0xa9188 [C8 (wz 0xb2bb8)] -> ro_cells rsegs m (0xb2bb8 + 48) [C4 (wz 0)] ->
    poison_consts m ->
    rw_cells rsegs m (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m (sh p) [CB (Z.to_nat r8) oldsh] ->
    (forall (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp + -80) [C8 (wz cache); C8 (wz sto); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        rw_cells rsegs m' (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        bytes_at rsegs m' (sh p) (repeat (Z_to_bv 8 0xfd) (Z.to_nat r8)) ->
        munch [(bv_unsigned sp - 144, bv_unsigned sp); (sh p, sh p + r8)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp - 80) ->
        evt rsegs Q (MS (mkR (wz 0x3b72c) (wz (bv_unsigned sp + -80)) gp tp t0' t1' t2' (wz q) (wz c)
                            (wz c) (wz cache) (wz sto) (wz (p + -16)) (wz n) a5' a6' a7'
                            (wz n) (wz sto) (wz cache) (wz (p + -16)) (wz cmax) s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (wz enqueue_entry) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz qput_entry) fc None m (seg_rom rsegs)).
Definition qput_tail_nodrain_stmt : Prop :=
  forall (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (s0v s1v s2v s3v s4v s5v s6v ra0 f0 f8 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv q c sz cmax nb fb lb qb lo : Z) (s2 s3 s4 s5 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (spv - 80) -> lo <= spv - 80 -> 0 <= spv - 80 -> spv <= 2^64 ->
    aobj c 32 -> c + 32 <= alloc_ceiling -> 0 <= cmax < 2^64 -> 0 <= qb <= cmax ->
    rw_cells rsegs m (spv + -80) [C8 f0; C8 f8; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    (stk rsegs m lo spv ->
        evt rsegs Q (MS (mkR ra0 (wz spv) gp tp t0 t1 t2 s0v s1v (wz qb) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz 0x3b72c) (wz (spv + -80)) gp tp t0 t1 t2 (wz q) (wz c) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz cmax) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x3b72c) fc None m (seg_rom rsegs)).
Definition qput_tail_drain_stmt : Prop :=
  forall (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (s0v s1v s2v s3v s4v s5v s6v ra0 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv q c cache sto cmax nb fb lb qb : Z) (s2 s3 s4 s5 : word) (Q : machine_state -> Prop),
    mem_inv rsegs m -> 0 <= spv - 80 -> spv <= 2^64 ->
    aobj c 32 -> c + 32 <= alloc_ceiling -> 0 <= cmax -> cmax < qb < 2^64 -> 0 <= cache < 2^64 -> 0 <= sto < 2^64 ->
    rw_cells rsegs m (spv + -80) [C8 (wz cache); C8 (wz sto); C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    rw_cells rsegs m c [C8 (wz nb); C8 (wz fb); C8 (wz lb); C8 (wz qb)] ->
    evt rsegs Q (MS (mkR (wz 0x3b664) (wz (spv + -80)) gp tp t0 t1 t2 (wz q) (wz c) (wz q) (wz c) (wz cache) (wz sto) a4 a5 a6 a7
                     s2 s3 s4 s5 (wz cmax) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz qdrain_entry) fc None m (seg_rom rsegs)) ->
    evt rsegs Q (MS (mkR (wz 0x3b72c) (wz (spv + -80)) gp tp t0 t1 t2 (wz q) (wz c) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz cmax) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x3b72c) fc None m (seg_rom rsegs)).

End CEIL.
Definition qput_epi_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (s0v s1v s2v s3v s4v s5v s6v ra0 f0 f8 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv lo : Z) (Q : machine_state -> Prop),
    mem_inv rsegs m -> stk rsegs m lo (spv - 80) -> lo <= spv - 80 -> 0 <= spv - 80 -> spv <= 2^64 ->
    rw_cells rsegs m (spv + -80) [C8 f0; C8 f8; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    (stk rsegs m lo spv ->
        evt rsegs Q (MS (mkR ra0 (wz spv) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra0) fc None m (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra (wz (spv + -80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz 0x3b664) fc None m (seg_rom rsegs)).
