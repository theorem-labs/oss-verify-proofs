From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay RcFin RcEmit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c RcAsanFP
  reac_box_model_block_c.
Import ListNotations.
Open Scope Z_scope.

Definition CTRL_EMIT_AS : Z := 0x849d8.
(* K = 128 + max(K_ms 2208, K_mc 2224, K_lay 4512, K_br 48, K_fin 16): contracts/libreac/ctrl_emit_as@reac_ctrlblk.md
   Names. *)
Definition CTRL_EMIT_AS_K : Z := 4640.

(* The thread cells that fp names are apart from the class-0 and class-1 side-stack bytes (struct.asan.runtime
   RT4.3) and from the shadow of the function's own window [lo, hi): ctrl_lay_block's class-1 frame and
   reac_box_model_block's class-0 frame and the callees' real-stack frames keep them (ctrl_lay_block_tls of
   lib/A/Prog/ctrl_lay_block_c.v). *)
Definition ctrl_emit_as_tls (m : word -> option byte) (TP FS lo hi : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    fp_dj (fp_tls TP DT TS C T DB k) (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]).

(* The plain contract (lib/Prog/ctrl_emit_as_c.v) with the premises of the asan build (S1.9, S1.10 of the English
   contract): the runtime's cells and shadow (asan_cells, shadow_rw), the addressable bytes, the window in AppMem,
   and the side-stack state for ctrl_lay_block's __asan_stack_malloc_1 and reac_box_model_block's
   __asan_stack_malloc_0 (fp [0%nat; 1%nat], ctrl_emit_as_tls). For ctrl_lay_block's premises also: the JOIN block
   that reac_box_model_block copies for k = 5, 6 addressable, and the ends g + al and g + 7 of the argument copy in
   AppMem (__asan_memcpy); for the two header copies (__asan_memcpy) the ends d + 6, d + 7, s + 6, s + 7 in AppMem.
   The run may also write the class-0 and class-1 side-stack bytes (fp_w [0%nat; 1%nat] FS) and the shadow of its
   window. *)
Definition ctrl_emit_as_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o f md d s g n ns FS : Z)
         (row tb mb nb gb db sb junk : list byte),
    let S := bv_unsigned sp in
    let Lo := S - CTRL_EMIT_AS_K in
    let k := ly_k row in
    let L := ubat row 21 in
    let A := ubat row 23 in
    let c := ubat row 20 in
    let E := em_E L (ubat row 22) n (em_hid mb) in
    let len := em_len L n in
    let R := if E then len else 0 in
    let blk := fin c (ubat row 18) (ubat row 19)
                 (ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb) in
    let nm := (3 <= k <= 9 /\ (ly_bb k = 5 \/ ly_bb k = 6)) /\ has mb <> 0 /\ rname mb <> 0 in
    let W := [(Lo, S); (o, o + R)] in
    a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 md -> a3 = Z_to_bv 64 d -> a4 = Z_to_bv 64 s ->
    a6 = Z_to_bv 64 n -> a7 = Z_to_bv 64 g -> t4 = Z_to_bv 64 ns ->
    -2^31 <= n < 2^31 -> -2^31 <= ns < 2^31 -> 0 <= g < 2^64 ->
    S mod 16 = 0 -> stk rsegs m Lo S ->
    ly_dj Lo S f (f + 24) -> (k = 2 -> ly_dj Lo S (ly_tm row) (ly_tm row + 32)) -> ly_dj Lo S md (md + 296) ->
    (nm -> ly_dj Lo S (rname mb) (rname mb + Z.of_nat (length nb))) ->
    ly_dj Lo S d (d + 6) -> ly_dj Lo S s (s + 6) ->
    (g <> 0 -> ly_al row <> 0 -> ly_dj Lo S g (g + ly_al row)) ->
    f <> 0 -> f mod 8 = 0 -> f + 24 <= 2^64 -> length row = 24%nat -> bytes_at rsegs m f row ->
    k <= 9 -> c <= 2 -> L <= 2 -> ubat row 22 <= 1 -> A <= 1 ->
    ly_ao row + ly_al row <= 32 ->
    (k = 2 -> ly_tm row + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm row) tb) ->
    (c = 2 -> 2 <= ubat row 19 /\ ubat row 18 + ubat row 19 <= 31) ->
    (L = 2 -> A = 0) ->
    md <> 0 -> md mod 8 = 0 -> md + 296 <= 2^64 -> length mb = 296%nat -> bytes_at rsegs m md mb ->
    (nm -> name_ok nb /\ bytes_at rsegs m (rname mb) nb) ->
    0 < o -> o + 1492 <= 2^64 ->
    (E = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\ ly_dj Lo S o (o + len) /\
       ly_dj o (o + len) f (f + 24) /\ (k = 2 -> ly_dj o (o + len) (ly_tm row) (ly_tm row + 32)) /\
       ly_dj o (o + len) md (md + 296) /\
       (nm -> ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) s (s + 6) /\
       (g <> 0 -> ly_al row <> 0 -> ly_dj o (o + len) g (g + ly_al row))) ->
    length db = 6%nat -> bytes_at rsegs m d db -> length sb = 6%nat -> bytes_at rsegs m s sb ->
    (g <> 0 -> ly_al row <> 0 -> Z.of_nat (length gb) = ly_al row /\ bytes_at rsegs m g gb) ->
    (A = 1 -> ns <= 0) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= Lo -> S <= APPMEM_END -> addressable m Lo CTRL_EMIT_AS_K ->
    addressable m f 24 -> addressable m md 296 -> addressable m d 6 -> addressable m s 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (s + 6) /\ app_mem (s + 7) ->
    (k = 2 -> addressable m (ly_tm row) 32) ->
    (nm -> addressable m (rname mb) (Z.of_nat (length nb))) ->
    (g <> 0 -> ly_al row <> 0 -> addressable m g (ly_al row)) ->
    (g <> 0 -> ly_al row <> 0 -> app_mem (g + ly_al row) /\ app_mem (g + 7)) ->
    (E = true -> addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (k = 5 -> addressable m JOIN_0014 32) -> (k = 6 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS Lo S W [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)] ->
    (k = 2 -> fp_dj [(ly_tm row, ly_tm row + 32)] (fp_w [0%nat; 1%nat] FS)) ->
    (nm -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    (g <> 0 -> ly_al row <> 0 -> fp_dj [(g, g + ly_al row)] (fp_w [0%nat; 1%nat] FS)) ->
    ctrl_emit_as_tls m (bv_unsigned tp) FS Lo S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 R)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (W ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr Lo, shadow_addr S)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S
         /\ asan_cells m' /\ shadow_rw m' /\ addressable m' Lo CTRL_EMIT_AS_K
         /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS Lo S W [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)]
         /\ (E = true ->
               bytes_at rsegs m' o
                 (em_fr db sb (bv_unsigned a5 mod 65536) (nth 0 row (Z_to_bv 8 0)) (nth 1 row (Z_to_bv 8 0))
                    blk len)
               /\ (L <> 2 -> em_wok n = true)
               /\ (c = 1 \/ c = 2 ->
                     closes c (ubat row 18) (ubat row 19) blk
                     /\ (closes c (ubat row 18) (ubat row 19)
                           (ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb) ->
                         blk = ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_EMIT_AS) fc None m (seg_rom rsegs)).

(* Footprint form (the re-walk form (D), RECIPE.md step 1 (a working note, not in this delivery)): the same run, from the same start state and
   with the same post, as an ExecF.evtF under a footprint RNG, with one rng premise per region the run and its
   callees touch, so the pages the run touches are known and no lazy first touch of this run is refused.
   The regions: the image [0x10000, 0x10000 + 0x5ee000) (every cell this run and its callees read by absolute
   address: the GOT cell 0x9fad0 and the runtime cell 0xa8878 that hold the shadow offset, [RT_LO, RT_HI) for the
   wrappers, BOX_CATALOGUE, JOIN_0013, JOIN_0014 and the thread cells of fp_tls that are image constants); this
   frame's stack window [Lo, S) = [S - 4640, S), which holds the frames of __asan_memset, __asan_memcpy,
   ctrl_lay_block, reac_braid_encode and ctrl_finish below it, and the shadow of that window (ctrl_lay_block's
   side-stack frames poison it); the side stack [FS, FS + FS_SIZE) and its shadow (the ranges of
   fp_w [0%nat; 1%nat] FS are inside both); the thread cells that fp_tls names, under the guard asan_tls_cells
   carries (ctrl_emit_as_tls names the same cells); and, under the guard its data premise carries, each buffer the
   run or a callee reads or writes with the cover of its shadow bytes.  A shadow cover is rounded out to whole
   8-byte WORDS at both ends, because the wrappers load shadow WORDS, not single shadow bytes (this function's own
   checks are single-byte lb loads at (x >> 3) + ASAN_K, inside those covers).
   ctrl_emit_as_contract_of_F gives the old statement back with RNG_all. *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes.

(* The thread cells that fp_tls names are in the footprint, under the guard asan_tls_cells carries: the shape of
   ctrl_emit_as_tls above, with rng in place of fp_dj. *)
Definition ctrl_emit_as_rtls (RNG : footprint) (m : word -> option byte) (TP : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    Forall (fun r => rng RNG (fst r) (snd r - fst r)) (fp_tls TP DT TS C T DB k).

(* RNG is the FIRST binder (a Theorem Labs lane's ruling, binding in RECIPE; relayed by a Theorem Labs lane 2026-10-27 22:35Z,
   which withdraws the earlier 16:28Z shape).  rng_bytes RNG comes first among the footprint premises:
   ctrl_lay_block_contract_F (lib/A/Prog/ctrl_lay_block_c.v) carries it, so this caller must too. *)
Definition ctrl_emit_as_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o f md d s g n ns FS : Z)
         (row tb mb nb gb db sb junk : list byte),
    let S := bv_unsigned sp in
    let Lo := S - CTRL_EMIT_AS_K in
    let k := ly_k row in
    let L := ubat row 21 in
    let A := ubat row 23 in
    let c := ubat row 20 in
    let E := em_E L (ubat row 22) n (em_hid mb) in
    let len := em_len L n in
    let R := if E then len else 0 in
    let blk := fin c (ubat row 18) (ubat row 19)
                 (ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb) in
    let nm := (3 <= k <= 9 /\ (ly_bb k = 5 \/ ly_bb k = 6)) /\ has mb <> 0 /\ rname mb <> 0 in
    let W := [(Lo, S); (o, o + R)] in
    a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 md -> a3 = Z_to_bv 64 d -> a4 = Z_to_bv 64 s ->
    a6 = Z_to_bv 64 n -> a7 = Z_to_bv 64 g -> t4 = Z_to_bv 64 ns ->
    -2^31 <= n < 2^31 -> -2^31 <= ns < 2^31 -> 0 <= g < 2^64 ->
    S mod 16 = 0 -> stk rsegs m Lo S ->
    ly_dj Lo S f (f + 24) -> (k = 2 -> ly_dj Lo S (ly_tm row) (ly_tm row + 32)) -> ly_dj Lo S md (md + 296) ->
    (nm -> ly_dj Lo S (rname mb) (rname mb + Z.of_nat (length nb))) ->
    ly_dj Lo S d (d + 6) -> ly_dj Lo S s (s + 6) ->
    (g <> 0 -> ly_al row <> 0 -> ly_dj Lo S g (g + ly_al row)) ->
    f <> 0 -> f mod 8 = 0 -> f + 24 <= 2^64 -> length row = 24%nat -> bytes_at rsegs m f row ->
    k <= 9 -> c <= 2 -> L <= 2 -> ubat row 22 <= 1 -> A <= 1 ->
    ly_ao row + ly_al row <= 32 ->
    (k = 2 -> ly_tm row + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm row) tb) ->
    (c = 2 -> 2 <= ubat row 19 /\ ubat row 18 + ubat row 19 <= 31) ->
    (L = 2 -> A = 0) ->
    md <> 0 -> md mod 8 = 0 -> md + 296 <= 2^64 -> length mb = 296%nat -> bytes_at rsegs m md mb ->
    (nm -> name_ok nb /\ bytes_at rsegs m (rname mb) nb) ->
    0 < o -> o + 1492 <= 2^64 ->
    (E = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\ ly_dj Lo S o (o + len) /\
       ly_dj o (o + len) f (f + 24) /\ (k = 2 -> ly_dj o (o + len) (ly_tm row) (ly_tm row + 32)) /\
       ly_dj o (o + len) md (md + 296) /\
       (nm -> ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) s (s + 6) /\
       (g <> 0 -> ly_al row <> 0 -> ly_dj o (o + len) g (g + ly_al row))) ->
    length db = 6%nat -> bytes_at rsegs m d db -> length sb = 6%nat -> bytes_at rsegs m s sb ->
    (g <> 0 -> ly_al row <> 0 -> Z.of_nat (length gb) = ly_al row /\ bytes_at rsegs m g gb) ->
    (A = 1 -> ns <= 0) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= Lo -> S <= APPMEM_END -> addressable m Lo CTRL_EMIT_AS_K ->
    addressable m f 24 -> addressable m md 296 -> addressable m d 6 -> addressable m s 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (s + 6) /\ app_mem (s + 7) ->
    (k = 2 -> addressable m (ly_tm row) 32) ->
    (nm -> addressable m (rname mb) (Z.of_nat (length nb))) ->
    (g <> 0 -> ly_al row <> 0 -> addressable m g (ly_al row)) ->
    (g <> 0 -> ly_al row <> 0 -> app_mem (g + ly_al row) /\ app_mem (g + 7)) ->
    (E = true -> addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (k = 5 -> addressable m JOIN_0014 32) -> (k = 6 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS Lo S W [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)] ->
    (k = 2 -> fp_dj [(ly_tm row, ly_tm row + 32)] (fp_w [0%nat; 1%nat] FS)) ->
    (nm -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    (g <> 0 -> ly_al row <> 0 -> fp_dj [(g, g + ly_al row)] (fp_w [0%nat; 1%nat] FS)) ->
    ctrl_emit_as_tls m (bv_unsigned tp) FS Lo S ->
    (* footprint: rng_bytes, then one rng premise per region the run and its callees touch *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG Lo CTRL_EMIT_AS_K ->
    rng RNG (shadow_addr Lo / 8 * 8) (shadow_addr (S - 1) / 8 * 8 + 8 - shadow_addr Lo / 8 * 8) ->
    rng RNG FS FS_SIZE ->
    rng RNG (shadow_addr FS / 8 * 8) (shadow_addr (FS + FS_SIZE - 1) / 8 * 8 + 8 - shadow_addr FS / 8 * 8) ->
    ctrl_emit_as_rtls RNG m (bv_unsigned tp) ->
    rng RNG f 24 ->
    rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 23) / 8 * 8 + 8 - shadow_addr f / 8 * 8) ->
    rng RNG md 296 ->
    rng RNG (shadow_addr md / 8 * 8) (shadow_addr (md + 295) / 8 * 8 + 8 - shadow_addr md / 8 * 8) ->
    rng RNG d 6 ->
    rng RNG (shadow_addr d / 8 * 8) (shadow_addr (d + 5) / 8 * 8 + 8 - shadow_addr d / 8 * 8) ->
    rng RNG s 6 ->
    rng RNG (shadow_addr s / 8 * 8) (shadow_addr (s + 5) / 8 * 8 + 8 - shadow_addr s / 8 * 8) ->
    (k = 2 -> rng RNG (ly_tm row) 32 /\
       rng RNG (shadow_addr (ly_tm row) / 8 * 8)
         (shadow_addr (ly_tm row + 31) / 8 * 8 + 8 - shadow_addr (ly_tm row) / 8 * 8)) ->
    (nm -> rng RNG (rname mb) (Z.of_nat (length nb)) /\
       rng RNG (shadow_addr (rname mb) / 8 * 8)
         (shadow_addr (rname mb + Z.of_nat (length nb) - 1) / 8 * 8 + 8 - shadow_addr (rname mb) / 8 * 8)) ->
    (g <> 0 -> ly_al row <> 0 -> rng RNG g (ly_al row) /\
       rng RNG (shadow_addr g / 8 * 8)
         (shadow_addr (g + ly_al row - 1) / 8 * 8 + 8 - shadow_addr g / 8 * 8)) ->
    (E = true -> rng RNG o len /\
       rng RNG (shadow_addr o / 8 * 8) (shadow_addr (o + len - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8)) ->
    (k = 5 -> rng RNG (shadow_addr JOIN_0014 / 8 * 8)
                (shadow_addr (JOIN_0014 + 31) / 8 * 8 + 8 - shadow_addr JOIN_0014 / 8 * 8)) ->
    (k = 6 -> rng RNG (shadow_addr JOIN_0013 / 8 * 8)
                (shadow_addr (JOIN_0013 + 31) / 8 * 8 + 8 - shadow_addr JOIN_0013 / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 R)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (W ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr Lo, shadow_addr S)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S
         /\ asan_cells m' /\ shadow_rw m' /\ addressable m' Lo CTRL_EMIT_AS_K
         /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS Lo S W [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)]
         /\ (E = true ->
               bytes_at rsegs m' o
                 (em_fr db sb (bv_unsigned a5 mod 65536) (nth 0 row (Z_to_bv 8 0)) (nth 1 row (Z_to_bv 8 0))
                    blk len)
               /\ (L <> 2 -> em_wok n = true)
               /\ (c = 1 \/ c = 2 ->
                     closes c (ubat row 18) (ubat row 19) blk
                     /\ (closes c (ubat row 18) (ubat row 19)
                           (ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb) ->
                         blk = ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_EMIT_AS) fc None m (seg_rom rsegs)).

(* The 8-aligned word cover of the shadow bytes of [p, q] of application memory is inside RNG_all. *)
Lemma rng_all_shcov : forall p q, 0 <= p -> q <= APPMEM_END ->
  rng RNG_all (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
Proof.
  intros p n Hp Hn. apply rng_all; unfold shadow_addr, ASAN_K, APPMEM_END in *;
    Z.div_mod_to_equations; lia.
Qed.

(* The old statement is the _F statement at the footprint that admits every access (rng_bytes and every rng premise
   by rng_all; the bounds come from the addressable and bytes_at premises the old statement already carries). *)
Lemma ctrl_emit_as_contract_of_F : ctrl_emit_as_contract_F -> ctrl_emit_as_contract.
Proof.
  intros HF. unfold ctrl_emit_as_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o f md d s g n ns FS row tb mb nb gb db sb junk.
  cbv zeta.
  intros Ea0 Ea1 Ea2 Ea3 Ea4 Ea6 Ea7 Et4 Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR
    Hk Hc HL HG HA Hao Htm Hc2 HLA Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0
    HAC HSW HHM HAE AWIN Af Amd Ad As APD APS Atm An Ag APg AO AJ14 AJ13 FP FPtm FPn FPg FPT.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof FP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & TLS0 & _ & FSP & _ & _ & _ & FSL & _ & _ & _).
  pose proof FSP as (FSpos & FSmod & FSgt & FSapp & _).
  pose proof Af as (Af0 & _ & Afe & _). pose proof Amd as (Amd0 & _ & Amde & _).
  pose proof Ad as (Ad0 & _ & Ade & _). pose proof As as (As0 & _ & Ase & _).
  apply (evtF_evt rsegs RNG_all).
  apply (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m o f md d s g n ns FS row tb mb nb gb db sb junk); try assumption.
  - unfold rng_bytes; intros; exact I.
  - apply rng_all; lia.
  - apply rng_all; unfold CTRL_EMIT_AS_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply rng_all_shcov; unfold CTRL_EMIT_AS_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply rng_all; unfold CTRL_EMIT_AS_K, HIGHMEM_BEG, APPMEM_END, FS_SIZE in *; lia.
  - apply rng_all_shcov; unfold CTRL_EMIT_AS_K, HIGHMEM_BEG, APPMEM_END, FS_SIZE in *; lia.
  - intros DT TS C T DB kk HT.
    unfold asan_tls_cells in HT.
    destruct HT as (B1 & B2 & B3 & B4 & B5 & Bk & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16
                    & B17 & B18).
    destruct B10 as (tb0 & te0 & B10).
    repeat match goal with
    | H : bytes_at rsegs m ?a ?l |- _ =>
        let N := fresh "N" in pose proof (bytes_at_bound rsegs m a l H) as N;
        rewrite ?length_app, ?length_le8, ?length_le4 in N; cbn [length] in N; clear H
    end.
    unfold fp_tls, TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY, VERBOSITY,
      DTLS_TPOFF.
    repeat (apply Forall_cons; [cbn [fst snd]; apply rng_all; lia|]). apply Forall_nil.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply rng_all_shcov; unfold APPMEM_END in *; lia.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply rng_all_shcov; unfold APPMEM_END in *; lia.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply rng_all_shcov; unfold APPMEM_END in *; lia.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply rng_all_shcov; unfold APPMEM_END in *; lia.
  - intros Hk2. pose proof (Atm Hk2) as (At0 & _ & Ate & _). split;
      [apply rng_all | apply rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros HNM. pose proof (An HNM) as (An0 & An1 & Ane & _). split;
      [apply rng_all | apply rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros Hg0 Hal. pose proof (Ag Hg0 Hal) as (Ag0 & Ag1 & Age & _). split;
      [apply rng_all | apply rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros HE. pose proof (AO HE) as ((AO0 & AO1 & AOe & _) & _ & _). split;
      [apply rng_all | apply rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros Hk5. pose proof (AJ14 Hk5) as (AJ0 & _ & AJe & _). apply rng_all_shcov; unfold APPMEM_END in *; lia.
  - intros Hk6. pose proof (AJ13 Hk6) as (AJ0 & _ & AJe & _). apply rng_all_shcov; unfold APPMEM_END in *; lia.
Qed.

(* ---- Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; form of a Theorem Labs lane 09:38Z): ctrl_emit_as_contract_on and
   ctrl_emit_as_contract_F_on, the two statements above with TWO changes each:
     - the premise `shadow_rw m` becomes `shadow_rw_on (ctrl_emit_as_shadow_R S FS o f md d s g n row mb nb) m`;
     - the post's `shadow_rw m'` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P m'`: every shadow region the
       caller holds before the call it holds after the call.
   ctrl_emit_as_shadow_R is the shadow part of the footprint the _F statement above names (its rng premises on shadow
   bytes, this file's ctrl_emit_as_contract_F): the 8-aligned shadow-word cover (sh_word_on, a Theorem Labs lane's
   lib/A/Prog/sh_word_on.v) of this frame's window [Lo, S), which holds every real-stack frame of the run and of its
   callees; the shadow of the class-0 and class-1 blocks of the side stack, [shadow_addr (fs_frame FS c 0),
   + 131072) for c = 0, 1, which holds every side-stack frame that reac_box_model_block's __asan_stack_malloc_0
   (class 0) and ctrl_lay_block's __asan_stack_malloc_1 (class 1) can choose and their stores (a Theorem Labs lane 10:57Z,
   side-stack-shadow.md (a working note, not in this delivery): the cut's AR gives the frames area only, not the side-stack header's shadow; the class-c
   block is asan_stack_malloc's R); and, under the guard of its data premise, of each
   buffer that the run or a callee reads or writes: the row f, the box model row md, the header sources d and s, the
   tm block (k = 2), the name (nm), the argument g, the output o (E = true) and the JOIN block (k = 5, 6).  Each
   callee's own region at its call is inside it (__asan_memcpy: asan_memcpy_shadow_R, the covers of its source and
   destination; ctrl_finish: no premise).  No other shadow byte is read or written by the run.
   These are STATEMENTS here.  ctrl_emit_as_contract_on is proved when ctrl_emit_as.v's run narrows (aepi, route (C)
   L2), which takes the callees' _on contracts; until then cite it only as a hypothesis, as the old contract is cited.
   The old statements follow (ctrl_emit_as_contract_of_on, ctrl_emit_as_contract_F_of_F_on);
   ctrl_emit_as_contract_on_of_F_on is ctrl_emit_as_contract_of_F for the new pair. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import sh_word_on asan_stack_malloc_c_on.

(* NOTE (premise-check-fuzz_ctrl.md (a working note, not in this delivery)): two
   shadow loads of the run lie OUTSIDE ctrl_emit_as_shadow_R: pc 0x84ac8 at shadow_addr (0x9e810 + 296 i) and pc 0x84adc
   at shadow_addr (0x9e920 + 296 i), i < 11 (BOX_CATALOGUE's shadow).  Both are dead code under this contract's premise
   `md <> 0` (both predecessors of block 0x84aa0 need s6 = md = 0).  That premise is load-bearing for R: whoever
   weakens `md <> 0` must widen R to cover those loads. *)
Definition ctrl_emit_as_shadow_R (S FS o f md d s g n : Z) (row mb nb : list byte) (a : Z) : Prop :=
  sh_word_on (S - CTRL_EMIT_AS_K) CTRL_EMIT_AS_K a \/
  asan_stack_malloc_shadow_R FS 0%nat a \/
  asan_stack_malloc_shadow_R FS 1%nat a \/
  sh_word_on f 24 a \/ sh_word_on md 296 a \/ sh_word_on d 6 a \/ sh_word_on s 6 a \/
  (ly_k row = 2 /\ sh_word_on (ly_tm row) 32 a) \/
  (((3 <= ly_k row <= 9 /\ (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6)) /\ has mb <> 0 /\ rname mb <> 0) /\
     sh_word_on (rname mb) (Z.of_nat (length nb)) a) \/
  (g <> 0 /\ ly_al row <> 0 /\ sh_word_on g (ly_al row) a) \/
  (em_E (ubat row 21) (ubat row 22) n (em_hid mb) = true /\ sh_word_on o (em_len (ubat row 21) n) a) \/
  (ly_k row = 5 /\ sh_word_on JOIN_0014 32 a) \/ (ly_k row = 6 /\ sh_word_on JOIN_0013 32 a).

Definition ctrl_emit_as_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o f md d s g n ns FS : Z)
         (row tb mb nb gb db sb junk : list byte),
    let S := bv_unsigned sp in
    let Lo := S - CTRL_EMIT_AS_K in
    let k := ly_k row in
    let L := ubat row 21 in
    let A := ubat row 23 in
    let c := ubat row 20 in
    let E := em_E L (ubat row 22) n (em_hid mb) in
    let len := em_len L n in
    let R := if E then len else 0 in
    let blk := fin c (ubat row 18) (ubat row 19)
                 (ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb) in
    let nm := (3 <= k <= 9 /\ (ly_bb k = 5 \/ ly_bb k = 6)) /\ has mb <> 0 /\ rname mb <> 0 in
    let W := [(Lo, S); (o, o + R)] in
    a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 md -> a3 = Z_to_bv 64 d -> a4 = Z_to_bv 64 s ->
    a6 = Z_to_bv 64 n -> a7 = Z_to_bv 64 g -> t4 = Z_to_bv 64 ns ->
    -2^31 <= n < 2^31 -> -2^31 <= ns < 2^31 -> 0 <= g < 2^64 ->
    S mod 16 = 0 -> stk rsegs m Lo S ->
    ly_dj Lo S f (f + 24) -> (k = 2 -> ly_dj Lo S (ly_tm row) (ly_tm row + 32)) -> ly_dj Lo S md (md + 296) ->
    (nm -> ly_dj Lo S (rname mb) (rname mb + Z.of_nat (length nb))) ->
    ly_dj Lo S d (d + 6) -> ly_dj Lo S s (s + 6) ->
    (g <> 0 -> ly_al row <> 0 -> ly_dj Lo S g (g + ly_al row)) ->
    f <> 0 -> f mod 8 = 0 -> f + 24 <= 2^64 -> length row = 24%nat -> bytes_at rsegs m f row ->
    k <= 9 -> c <= 2 -> L <= 2 -> ubat row 22 <= 1 -> A <= 1 ->
    ly_ao row + ly_al row <= 32 ->
    (k = 2 -> ly_tm row + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm row) tb) ->
    (c = 2 -> 2 <= ubat row 19 /\ ubat row 18 + ubat row 19 <= 31) ->
    (L = 2 -> A = 0) ->
    md <> 0 -> md mod 8 = 0 -> md + 296 <= 2^64 -> length mb = 296%nat -> bytes_at rsegs m md mb ->
    (nm -> name_ok nb /\ bytes_at rsegs m (rname mb) nb) ->
    0 < o -> o + 1492 <= 2^64 ->
    (E = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\ ly_dj Lo S o (o + len) /\
       ly_dj o (o + len) f (f + 24) /\ (k = 2 -> ly_dj o (o + len) (ly_tm row) (ly_tm row + 32)) /\
       ly_dj o (o + len) md (md + 296) /\
       (nm -> ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) s (s + 6) /\
       (g <> 0 -> ly_al row <> 0 -> ly_dj o (o + len) g (g + ly_al row))) ->
    length db = 6%nat -> bytes_at rsegs m d db -> length sb = 6%nat -> bytes_at rsegs m s sb ->
    (g <> 0 -> ly_al row <> 0 -> Z.of_nat (length gb) = ly_al row /\ bytes_at rsegs m g gb) ->
    (A = 1 -> ns <= 0) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw_on (ctrl_emit_as_shadow_R S FS o f md d s g n row mb nb) m ->
    HIGHMEM_BEG <= Lo -> S <= APPMEM_END -> addressable m Lo CTRL_EMIT_AS_K ->
    addressable m f 24 -> addressable m md 296 -> addressable m d 6 -> addressable m s 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (s + 6) /\ app_mem (s + 7) ->
    (k = 2 -> addressable m (ly_tm row) 32) ->
    (nm -> addressable m (rname mb) (Z.of_nat (length nb))) ->
    (g <> 0 -> ly_al row <> 0 -> addressable m g (ly_al row)) ->
    (g <> 0 -> ly_al row <> 0 -> app_mem (g + ly_al row) /\ app_mem (g + 7)) ->
    (E = true -> addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (k = 5 -> addressable m JOIN_0014 32) -> (k = 6 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS Lo S W [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)] ->
    (k = 2 -> fp_dj [(ly_tm row, ly_tm row + 32)] (fp_w [0%nat; 1%nat] FS)) ->
    (nm -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    (g <> 0 -> ly_al row <> 0 -> fp_dj [(g, g + ly_al row)] (fp_w [0%nat; 1%nat] FS)) ->
    ctrl_emit_as_tls m (bv_unsigned tp) FS Lo S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 R)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (W ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr Lo, shadow_addr S)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S
         /\ asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m')
         /\ addressable m' Lo CTRL_EMIT_AS_K
         /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS Lo S W [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)]
         /\ (E = true ->
               bytes_at rsegs m' o
                 (em_fr db sb (bv_unsigned a5 mod 65536) (nth 0 row (Z_to_bv 8 0)) (nth 1 row (Z_to_bv 8 0))
                    blk len)
               /\ (L <> 2 -> em_wok n = true)
               /\ (c = 1 \/ c = 2 ->
                     closes c (ubat row 18) (ubat row 19) blk
                     /\ (closes c (ubat row 18) (ubat row 19)
                           (ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb) ->
                         blk = ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_EMIT_AS) fc None m (seg_rom rsegs)).

(* The old statement: the universal shadow_rw gives the region (shadow_rw_on_of_shadow_rw), and the post's region
   transport at P := fun _ => True gives the universal post back (shadow_rw_of_on_all). *)
Lemma ctrl_emit_as_contract_of_on : ctrl_emit_as_contract_on -> ctrl_emit_as_contract.
Proof.
  intros H. unfold ctrl_emit_as_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o f md d s g n ns FS row tb mb nb gb db sb junk.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m o f md d s g n ns FS row tb mb nb gb db sb junk) as H'.
  cbv zeta in H' |- *.
  intros Ea0 Ea1 Ea2 Ea3 Ea4 Ea6 Ea7 Et4 Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR
    Hk Hc HL HG HA Hao Htm Hc2 HLA Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0
    HAC HSW HHM HAE AWIN Af Amd Ad As APD APS Atm An Ag APg AO AJ14 AJ13 FP FPtm FPn FPg FPT.
  eapply evt_mono.
  - exact (H' Ea0 Ea1 Ea2 Ea3 Ea4 Ea6 Ea7 Et4 Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR
             Hk Hc HL HG HA Hao Htm Hc2 HLA Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0
             HAC (shadow_rw_on_of_shadow_rw _ m HSW) HHM HAE AWIN Af Amd Ad As APD APS Atm An Ag APg AO AJ14 AJ13
             FP FPtm FPn FPg FPT).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                Ems & MU & WM & MI & ST & AC & SW & Rest).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj Ems (conj MU (conj WM (conj MI (conj ST (conj AC (conj _ Rest))))))).
    exact (shadow_rw_of_on_all m' (SW (fun _ => True) (shadow_rw_on_of_shadow_rw _ m HSW))).
Qed.

Definition ctrl_emit_as_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o f md d s g n ns FS : Z)
         (row tb mb nb gb db sb junk : list byte),
    let S := bv_unsigned sp in
    let Lo := S - CTRL_EMIT_AS_K in
    let k := ly_k row in
    let L := ubat row 21 in
    let A := ubat row 23 in
    let c := ubat row 20 in
    let E := em_E L (ubat row 22) n (em_hid mb) in
    let len := em_len L n in
    let R := if E then len else 0 in
    let blk := fin c (ubat row 18) (ubat row 19)
                 (ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb) in
    let nm := (3 <= k <= 9 /\ (ly_bb k = 5 \/ ly_bb k = 6)) /\ has mb <> 0 /\ rname mb <> 0 in
    let W := [(Lo, S); (o, o + R)] in
    a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 md -> a3 = Z_to_bv 64 d -> a4 = Z_to_bv 64 s ->
    a6 = Z_to_bv 64 n -> a7 = Z_to_bv 64 g -> t4 = Z_to_bv 64 ns ->
    -2^31 <= n < 2^31 -> -2^31 <= ns < 2^31 -> 0 <= g < 2^64 ->
    S mod 16 = 0 -> stk rsegs m Lo S ->
    ly_dj Lo S f (f + 24) -> (k = 2 -> ly_dj Lo S (ly_tm row) (ly_tm row + 32)) -> ly_dj Lo S md (md + 296) ->
    (nm -> ly_dj Lo S (rname mb) (rname mb + Z.of_nat (length nb))) ->
    ly_dj Lo S d (d + 6) -> ly_dj Lo S s (s + 6) ->
    (g <> 0 -> ly_al row <> 0 -> ly_dj Lo S g (g + ly_al row)) ->
    f <> 0 -> f mod 8 = 0 -> f + 24 <= 2^64 -> length row = 24%nat -> bytes_at rsegs m f row ->
    k <= 9 -> c <= 2 -> L <= 2 -> ubat row 22 <= 1 -> A <= 1 ->
    ly_ao row + ly_al row <= 32 ->
    (k = 2 -> ly_tm row + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm row) tb) ->
    (c = 2 -> 2 <= ubat row 19 /\ ubat row 18 + ubat row 19 <= 31) ->
    (L = 2 -> A = 0) ->
    md <> 0 -> md mod 8 = 0 -> md + 296 <= 2^64 -> length mb = 296%nat -> bytes_at rsegs m md mb ->
    (nm -> name_ok nb /\ bytes_at rsegs m (rname mb) nb) ->
    0 < o -> o + 1492 <= 2^64 ->
    (E = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\ ly_dj Lo S o (o + len) /\
       ly_dj o (o + len) f (f + 24) /\ (k = 2 -> ly_dj o (o + len) (ly_tm row) (ly_tm row + 32)) /\
       ly_dj o (o + len) md (md + 296) /\
       (nm -> ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) s (s + 6) /\
       (g <> 0 -> ly_al row <> 0 -> ly_dj o (o + len) g (g + ly_al row))) ->
    length db = 6%nat -> bytes_at rsegs m d db -> length sb = 6%nat -> bytes_at rsegs m s sb ->
    (g <> 0 -> ly_al row <> 0 -> Z.of_nat (length gb) = ly_al row /\ bytes_at rsegs m g gb) ->
    (A = 1 -> ns <= 0) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw_on (ctrl_emit_as_shadow_R S FS o f md d s g n row mb nb) m ->
    HIGHMEM_BEG <= Lo -> S <= APPMEM_END -> addressable m Lo CTRL_EMIT_AS_K ->
    addressable m f 24 -> addressable m md 296 -> addressable m d 6 -> addressable m s 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (s + 6) /\ app_mem (s + 7) ->
    (k = 2 -> addressable m (ly_tm row) 32) ->
    (nm -> addressable m (rname mb) (Z.of_nat (length nb))) ->
    (g <> 0 -> ly_al row <> 0 -> addressable m g (ly_al row)) ->
    (g <> 0 -> ly_al row <> 0 -> app_mem (g + ly_al row) /\ app_mem (g + 7)) ->
    (E = true -> addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (k = 5 -> addressable m JOIN_0014 32) -> (k = 6 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS Lo S W [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)] ->
    (k = 2 -> fp_dj [(ly_tm row, ly_tm row + 32)] (fp_w [0%nat; 1%nat] FS)) ->
    (nm -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    (g <> 0 -> ly_al row <> 0 -> fp_dj [(g, g + ly_al row)] (fp_w [0%nat; 1%nat] FS)) ->
    ctrl_emit_as_tls m (bv_unsigned tp) FS Lo S ->
    (* footprint: rng_bytes, then one rng premise per region the run and its callees touch *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG Lo CTRL_EMIT_AS_K ->
    rng RNG (shadow_addr Lo / 8 * 8) (shadow_addr (S - 1) / 8 * 8 + 8 - shadow_addr Lo / 8 * 8) ->
    rng RNG FS FS_SIZE ->
    rng RNG (shadow_addr FS / 8 * 8) (shadow_addr (FS + FS_SIZE - 1) / 8 * 8 + 8 - shadow_addr FS / 8 * 8) ->
    ctrl_emit_as_rtls RNG m (bv_unsigned tp) ->
    rng RNG f 24 ->
    rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 23) / 8 * 8 + 8 - shadow_addr f / 8 * 8) ->
    rng RNG md 296 ->
    rng RNG (shadow_addr md / 8 * 8) (shadow_addr (md + 295) / 8 * 8 + 8 - shadow_addr md / 8 * 8) ->
    rng RNG d 6 ->
    rng RNG (shadow_addr d / 8 * 8) (shadow_addr (d + 5) / 8 * 8 + 8 - shadow_addr d / 8 * 8) ->
    rng RNG s 6 ->
    rng RNG (shadow_addr s / 8 * 8) (shadow_addr (s + 5) / 8 * 8 + 8 - shadow_addr s / 8 * 8) ->
    (k = 2 -> rng RNG (ly_tm row) 32 /\
       rng RNG (shadow_addr (ly_tm row) / 8 * 8)
         (shadow_addr (ly_tm row + 31) / 8 * 8 + 8 - shadow_addr (ly_tm row) / 8 * 8)) ->
    (nm -> rng RNG (rname mb) (Z.of_nat (length nb)) /\
       rng RNG (shadow_addr (rname mb) / 8 * 8)
         (shadow_addr (rname mb + Z.of_nat (length nb) - 1) / 8 * 8 + 8 - shadow_addr (rname mb) / 8 * 8)) ->
    (g <> 0 -> ly_al row <> 0 -> rng RNG g (ly_al row) /\
       rng RNG (shadow_addr g / 8 * 8)
         (shadow_addr (g + ly_al row - 1) / 8 * 8 + 8 - shadow_addr g / 8 * 8)) ->
    (E = true -> rng RNG o len /\
       rng RNG (shadow_addr o / 8 * 8) (shadow_addr (o + len - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8)) ->
    (k = 5 -> rng RNG (shadow_addr JOIN_0014 / 8 * 8)
                (shadow_addr (JOIN_0014 + 31) / 8 * 8 + 8 - shadow_addr JOIN_0014 / 8 * 8)) ->
    (k = 6 -> rng RNG (shadow_addr JOIN_0013 / 8 * 8)
                (shadow_addr (JOIN_0013 + 31) / 8 * 8 + 8 - shadow_addr JOIN_0013 / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 R)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (W ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr Lo, shadow_addr S)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S
         /\ asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m')
         /\ addressable m' Lo CTRL_EMIT_AS_K
         /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS Lo S W [(f, f + 24); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)]
         /\ (E = true ->
               bytes_at rsegs m' o
                 (em_fr db sb (bv_unsigned a5 mod 65536) (nth 0 row (Z_to_bv 8 0)) (nth 1 row (Z_to_bv 8 0))
                    blk len)
               /\ (L <> 2 -> em_wok n = true)
               /\ (c = 1 \/ c = 2 ->
                     closes c (ubat row 18) (ubat row 19) blk
                     /\ (closes c (ubat row 18) (ubat row 19)
                           (ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb) ->
                         blk = ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_EMIT_AS) fc None m (seg_rom rsegs)).

Lemma ctrl_emit_as_contract_F_of_F_on : ctrl_emit_as_contract_F_on -> ctrl_emit_as_contract_F.
Proof.
  intros H. unfold ctrl_emit_as_contract_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o f md d s g n ns FS row tb mb nb gb db sb junk.
  pose proof (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m o f md d s g n ns FS row tb mb nb gb db sb junk) as H'.
  cbv zeta in H' |- *.
  intros Ea0 Ea1 Ea2 Ea3 Ea4 Ea6 Ea7 Et4 Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR
    Hk Hc HL HG HA Hao Htm Hc2 HLA Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0
    HAC HSW HHM HAE AWIN Af Amd Ad As APD APS Atm An Ag APg AO AJ14 AJ13 FP FPtm FPn FPg FPT
    RB RIMG RWIN RSWIN RFS RSFS RTLS Rf RSf Rmd RSmd Rd RSd Rs RSs Rtm Rnm Rg Ro RJ14 RJ13.
  eapply evtF_mono.
  - exact (H' Ea0 Ea1 Ea2 Ea3 Ea4 Ea6 Ea7 Et4 Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR
             Hk Hc HL HG HA Hao Htm Hc2 HLA Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0
             HAC (shadow_rw_on_of_shadow_rw _ m HSW) HHM HAE AWIN Af Amd Ad As APD APS Atm An Ag APg AO AJ14 AJ13
             FP FPtm FPn FPg FPT
             RB RIMG RWIN RSWIN RFS RSFS RTLS Rf RSf Rmd RSmd Rd RSd Rs RSs Rtm Rnm Rg Ro RJ14 RJ13).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                Ems & MU & WM & MI & ST & AC & SW & Rest).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj Ems (conj MU (conj WM (conj MI (conj ST (conj AC (conj _ Rest))))))).
    exact (shadow_rw_of_on_all m' (SW (fun _ => True) (shadow_rw_on_of_shadow_rw _ m HSW))).
Qed.


(* ctrl_emit_as_contract_of_F for the route (C) pair (its proof, unchanged: the region premise and the post pass
   through). *)
Lemma ctrl_emit_as_contract_on_of_F_on : ctrl_emit_as_contract_F_on -> ctrl_emit_as_contract_on.
Proof.
  intros HF. unfold ctrl_emit_as_contract_on.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o f md d s g n ns FS row tb mb nb gb db sb junk.
  cbv zeta.
  intros Ea0 Ea1 Ea2 Ea3 Ea4 Ea6 Ea7 Et4 Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR
    Hk Hc HL HG HA Hao Htm Hc2 HLA Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0
    HAC HSW HHM HAE AWIN Af Amd Ad As APD APS Atm An Ag APg AO AJ14 AJ13 FP FPtm FPn FPg FPT.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof FP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & TLS0 & _ & FSP & _ & _ & _ & FSL & _ & _ & _).
  pose proof FSP as (FSpos & FSmod & FSgt & FSapp & _).
  pose proof Af as (Af0 & _ & Afe & _). pose proof Amd as (Amd0 & _ & Amde & _).
  pose proof Ad as (Ad0 & _ & Ade & _). pose proof As as (As0 & _ & Ase & _).
  apply (evtF_evt rsegs RNG_all).
  apply (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m o f md d s g n ns FS row tb mb nb gb db sb junk); try assumption.
  - unfold rng_bytes; intros; exact I.
  - apply rng_all; lia.
  - apply rng_all; unfold CTRL_EMIT_AS_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply rng_all_shcov; unfold CTRL_EMIT_AS_K, HIGHMEM_BEG, APPMEM_END in *; lia.
  - apply rng_all; unfold CTRL_EMIT_AS_K, HIGHMEM_BEG, APPMEM_END, FS_SIZE in *; lia.
  - apply rng_all_shcov; unfold CTRL_EMIT_AS_K, HIGHMEM_BEG, APPMEM_END, FS_SIZE in *; lia.
  - intros DT TS C T DB kk HT.
    unfold asan_tls_cells in HT.
    destruct HT as (B1 & B2 & B3 & B4 & B5 & Bk & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16
                    & B17 & B18).
    destruct B10 as (tb0 & te0 & B10).
    repeat match goal with
    | H : bytes_at rsegs m ?a ?l |- _ =>
        let N := fresh "N" in pose proof (bytes_at_bound rsegs m a l H) as N;
        rewrite ?length_app, ?length_le8, ?length_le4 in N; cbn [length] in N; clear H
    end.
    unfold fp_tls, TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY, VERBOSITY,
      DTLS_TPOFF.
    repeat (apply Forall_cons; [cbn [fst snd]; apply rng_all; lia|]). apply Forall_nil.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply rng_all_shcov; unfold APPMEM_END in *; lia.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply rng_all_shcov; unfold APPMEM_END in *; lia.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply rng_all_shcov; unfold APPMEM_END in *; lia.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply rng_all_shcov; unfold APPMEM_END in *; lia.
  - intros Hk2. pose proof (Atm Hk2) as (At0 & _ & Ate & _). split;
      [apply rng_all | apply rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros HNM. pose proof (An HNM) as (An0 & An1 & Ane & _). split;
      [apply rng_all | apply rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros Hg0 Hal. pose proof (Ag Hg0 Hal) as (Ag0 & Ag1 & Age & _). split;
      [apply rng_all | apply rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros HE. pose proof (AO HE) as ((AO0 & AO1 & AOe & _) & _ & _). split;
      [apply rng_all | apply rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros Hk5. pose proof (AJ14 Hk5) as (AJ0 & _ & AJe & _). apply rng_all_shcov; unfold APPMEM_END in *; lia.
  - intros Hk6. pose proof (AJ13 Hk6) as (AJ0 & _ & AJe & _). apply rng_all_shcov; unfold APPMEM_END in *; lia.
Qed.

Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_emit_as_c.ctrl_emit_as_contract_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_emit_as_c.ctrl_emit_as_contract_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_emit_as_c.ctrl_emit_as_contract_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_emit_as_c.ctrl_emit_as_contract_F_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_emit_as_c.ctrl_emit_as_contract_of_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_emit_as_c.ctrl_emit_as_contract_of_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_emit_as_c.ctrl_emit_as_contract_F_of_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_emit_as_c.ctrl_emit_as_contract_F_of_F_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_emit_as_c.ctrl_emit_as_contract_on_of_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_emit_as_c.ctrl_emit_as_contract_on_of_F_on.
