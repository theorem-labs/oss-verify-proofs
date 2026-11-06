From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay RcFin RcEmit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c RcAsanFP
  reac_box_model_block_c.
Import ListNotations.
Open Scope Z_scope.

Definition CTRL_EMIT_AS : Z := 0x853c4.
(* K = 128 + max(K_ms 2208, K_mc 2224, K_lay 4512, K_br 128, K_fin 32): contracts/libreac/ctrl_emit_as@reac_ctrlblk.md
   Names. *)
Definition CTRL_EMIT_AS_K : Z := 4640.

(* The thread cells that fp names are apart from the class-0 and class-1 side-stack bytes (struct.asan.runtime
   RT4.3) and from the shadow of the function's own window [lo, hi): ctrl_lay_block's class-1 frame and
   reac_box_model_block's class-0 frame and the callees' real-stack frames keep them (ctrl_lay_block_tls of
   lib/B/Prog/ctrl_lay_block_c.v). *)
Definition ctrl_emit_as_tls (m : word -> option byte) (TP FS lo hi : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    fp_dj (fp_tls TP DT TS C T DB k) (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]).

(* The plain contract (lib/Prog/ctrl_emit_as_c.v) with the premises of the asan-ubsan build (S1.9, S1.10 of the
   English contract): the runtime's cells and shadow (asan_cells, shadow_rw), the addressable bytes, the window in
   AppMem, and the side-stack state for ctrl_lay_block's __asan_stack_malloc_1 and reac_box_model_block's
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
    (* asan-ubsan *)
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

(* ---------------------------------------------------------------------------------------------------------- *)
(* Footprint form (RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF under a footprint RNG, with one
   rng premise per region the run and its callees touch, each under the guard its data premise carries.
   ctrl_emit_as_contract_of_F gives the old statement back at the footprint that admits every access. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes.

(* The image: the loaded segments, from 0x10000 to the end of the writable data rounded up to a page (ASAN_GT).
   It holds the GOT cell and the cell of the shadow offset ([RT_LO, RT_HI)), the runtime's own data cells that
   __asan_stack_malloc reads, and the two JOIN blocks reac_box_model_block copies: one whole-image range
   [0x10000, 0x5fe000) = rng RNG 0x10000 0x5ee000 (a Theorem Labs lane's reac_ctrl_build_as text). *)

(* The 8-aligned shadow WORD cover of the bytes [p, p + n). An ASan runtime wrapper (__asan_memset,
   __asan_memcpy) loads the shadow in aligned 8-byte words, so the byte-exact span of a buffer a wrapper checks
   is one word short at each end; this cover is a Theorem Labs lane's wrapper _F text (lib/B/Prog/reac_identity_initF.v,
   declaration_ofF.v). Every buffer below reaches a wrapper, through this function (__asan_memset and the two
   __asan_memcpy copies of the output) or through ctrl_lay_block, so every shadow premise is this cover; it
   covers the byte-exact span of this function's own single-byte checks as well. *)
Definition rng_shcov (RNG : footprint) (p n : Z) : Prop :=
  rng RNG (shadow_addr p / 8 * 8) (shadow_addr (p + n - 1) / 8 * 8 + 8 - shadow_addr p / 8 * 8).

(* The thread cells that __asan_stack_malloc reads through tp (fp_tls of lib/B/Prog/RcAsanFP.v): ctrl_lay_block
   reaches them through __asan_stack_malloc_1 and through reac_box_model_block's __asan_stack_malloc_0. Their
   addresses are read out of memory, so the premise is stated over the witnesses asan_tls_cells fixes, as the
   ctrl_emit_as_tls premise above is. *)
Definition rng_tls (RNG : footprint) (m : word -> option byte) (TP : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    Forall (fun r : ivl => rng RNG (fst r) (snd r - fst r)) (fp_tls TP DT TS C T DB k).

(* ctrl_emit_as_contract with (RNG : footprint) bound FIRST (a Theorem Labs lane's ruling, binding in RECIPE; relayed
   by a Theorem Labs lane 22:35Z), the same premises in the same order, then rng_bytes RNG (ctrl_lay_block_contract_F of
   lib/B/Prog/ctrl_lay_block_c.v carries it, so this caller must too), then one rng premise per region the run
   touches: the window [Lo, S) of this frame and of the callees' frames and the shadow words of that window (the
   callees' ASan prologues poison and unpoison it); the side stack for frames and its shadow (fp_w [0; 1] FS of the
   post's munch window); the image; the thread cells; and each buffer the function or a callee reads or writes,
   with its shadow word cover, under the guard its data premise carries.
   The run reads no other image data: md <> 0, so the BOX_CATALOGUE search at 0x85494 is not entered. *)
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
    (* asan-ubsan *)
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
    (* footprint *)
    rng_bytes RNG ->
    rng RNG Lo CTRL_EMIT_AS_K -> rng_shcov RNG Lo CTRL_EMIT_AS_K ->
    rng RNG FS FS_SIZE -> rng_shcov RNG FS FS_SIZE ->
    rng RNG 0x10000 0x5ee000 ->
    rng_tls RNG m (bv_unsigned tp) ->
    rng RNG f 24 -> rng_shcov RNG f 24 ->
    rng RNG md 296 -> rng_shcov RNG md 296 ->
    rng RNG d 6 -> rng_shcov RNG d 6 ->
    rng RNG s 6 -> rng_shcov RNG s 6 ->
    (E = true -> rng RNG o len /\ rng_shcov RNG o len) ->
    (k = 2 -> rng RNG (ly_tm row) 32 /\ rng_shcov RNG (ly_tm row) 32) ->
    (nm -> rng RNG (rname mb) (Z.of_nat (length nb)) /\ rng_shcov RNG (rname mb) (Z.of_nat (length nb))) ->
    (g <> 0 -> ly_al row <> 0 -> rng RNG g (ly_al row) /\ rng_shcov RNG g (ly_al row)) ->
    (k = 5 -> rng_shcov RNG JOIN_0014 32) -> (k = 6 -> rng_shcov RNG JOIN_0013 32) ->
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

(* The shadow word cover of a range of application memory is free at the footprint that admits every access. *)
Lemma rng_all_shcov : forall p n, 0 <= p -> p + n <= APPMEM_END -> rng_shcov RNG_all p n.
Proof.
  intros p n Hp Hn. unfold rng_shcov. apply rng_all;
    unfold shadow_addr, ASAN_K, APPMEM_END in *; Z.div_mod_to_equations; lia.
Qed.

(* The thread cells are free at that footprint too: asan_tls_cells bounds every range of fp_tls. *)
Lemma rng_all_tls : forall m TP, (exists DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k) ->
  rng_tls RNG_all m TP.
Proof.
  intros m TP _ DT TS C T DB k HT.
  destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
    & T19).
  pose proof (bytes_at_bound rsegs m _ _ T3) as B3. rewrite length_le8 in B3.
  pose proof (bytes_at_bound rsegs m _ _ T4) as B4. rewrite length_le8 in B4.
  pose proof (bytes_at_bound rsegs m _ _ T8) as B8. rewrite length_le8 in B8.
  pose proof (bytes_at_bound rsegs m _ _ T9) as B9. rewrite length_le8 in B9.
  pose proof (bytes_at_bound rsegs m _ _ T10) as B10. rewrite length_le8 in B10.
  destruct T11 as (tb0 & te0 & T11). pose proof (bytes_at_bound rsegs m _ _ T11) as B11.
  rewrite length_app, !length_le8 in B11.
  pose proof (bytes_at_bound rsegs m _ _ T17) as B17. rewrite length_le8 in B17.
  pose proof (bytes_at_bound rsegs m _ _ T19) as B19. rewrite length_le8 in B19.
  unfold fp_tls, TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY, VERBOSITY,
    DTLS_TPOFF.
  repeat (apply Forall_cons; [cbn [fst snd]; apply rng_all; lia|]). apply Forall_nil.
Qed.

(* The old statement is the _F statement at the footprint that admits every access (rng_bytes and every rng
   premise by rng_all): the footprint form carries no premise the old contract lacks. *)
Lemma ctrl_emit_as_contract_of_F : ctrl_emit_as_contract_F -> ctrl_emit_as_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o f md d s g n ns FS row tb mb nb gb db sb junk.
  cbv zeta.
  intros Ea0 Ea1 Ea2 Ea3 Ea4 Ea6 Ea7 Et4.
  intros Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR Hk Hc HL HG HA Hao Htm Hc2 HLA
    Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0
    HAC HSW HHM HAE AWIN Af Amd Ad As APD APS Atm An Ag APg AO AJ14 AJ13 FP FPtm FPn FPg FPT.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof AWIN as (AW0 & AW1 & AW2 & _).
  pose proof Af as (Af0 & _ & Af2 & _). pose proof Amd as (Am0 & _ & Am2 & _).
  pose proof Ad as (Ad0 & _ & Ad2 & _). pose proof As as (As0 & _ & As2 & _).
  (* the side stack: 0 < FS and FS + FS_SIZE <= Lo, from the fp premise *)
  pose proof FP as FPd.
  destruct FPd as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & FSP & _ & _ & _ & FSL & _ & _ & _).
  destruct FSP as (FSpos & _ & _ & _ & _).
  assert (RRB : rng_bytes RNG_all) by (unfold rng_bytes; intros; exact I).
  assert (RWIN : rng RNG_all (bv_unsigned sp - CTRL_EMIT_AS_K) CTRL_EMIT_AS_K)
    by (apply rng_all; unfold CTRL_EMIT_AS_K, APPMEM_END in *; lia).
  assert (RWSH : rng_shcov RNG_all (bv_unsigned sp - CTRL_EMIT_AS_K) CTRL_EMIT_AS_K)
    by (apply rng_all_shcov; unfold CTRL_EMIT_AS_K, APPMEM_END in *; lia).
  assert (RFS : rng RNG_all FS FS_SIZE)
    by (apply rng_all; unfold CTRL_EMIT_AS_K, APPMEM_END in *; lia).
  assert (RFSH : rng_shcov RNG_all FS FS_SIZE)
    by (apply rng_all_shcov; unfold CTRL_EMIT_AS_K, APPMEM_END in *; lia).
  assert (RIMG : rng RNG_all 0x10000 0x5ee000)
    by (apply rng_all; lia).
  assert (RTLS : rng_tls RNG_all m (bv_unsigned tp))
    by (apply rng_all_tls; exists DT0, TS0, C0, T0, DB0, k0; exact HT0).
  assert (RROW : rng RNG_all f 24) by (apply rng_all; lia).
  assert (RROWS : rng_shcov RNG_all f 24) by (apply rng_all_shcov; lia).
  assert (RMD : rng RNG_all md 296) by (apply rng_all; lia).
  assert (RMDS : rng_shcov RNG_all md 296) by (apply rng_all_shcov; lia).
  assert (RD : rng RNG_all d 6) by (apply rng_all; unfold APPMEM_END in *; lia).
  assert (RDS : rng_shcov RNG_all d 6) by (apply rng_all_shcov; lia).
  assert (RS : rng RNG_all s 6) by (apply rng_all; unfold APPMEM_END in *; lia).
  assert (RSS : rng_shcov RNG_all s 6) by (apply rng_all_shcov; lia).
  assert (RO : em_E (ubat row 21) (ubat row 22) n (em_hid mb) = true ->
               rng RNG_all o (em_len (ubat row 21) n) /\
               rng_shcov RNG_all o (em_len (ubat row 21) n)).
  { intros HE. destruct (AO HE) as (AOa & _ & _). pose proof AOa as (AO0 & _ & AO2 & _).
    split; [apply rng_all; unfold APPMEM_END in *; lia | apply rng_all_shcov; lia]. }
  assert (RTM : ly_k row = 2 -> rng RNG_all (ly_tm row) 32 /\ rng_shcov RNG_all (ly_tm row) 32).
  { intros Hk2. pose proof (Atm Hk2) as (AT0 & _ & AT2 & _).
    split; [apply rng_all; unfold APPMEM_END in *; lia | apply rng_all_shcov; lia]. }
  assert (RNB : (3 <= ly_k row <= 9 /\ (ly_bb (ly_k row) = 5 \/ ly_bb (ly_k row) = 6)) /\
                has mb <> 0 /\ rname mb <> 0 ->
                rng RNG_all (rname mb) (Z.of_nat (length nb)) /\
                rng_shcov RNG_all (rname mb) (Z.of_nat (length nb))).
  { intros HNM. pose proof (An HNM) as (AN0 & _ & AN2 & _).
    split; [apply rng_all; unfold APPMEM_END in *; lia | apply rng_all_shcov; lia]. }
  assert (RG : g <> 0 -> ly_al row <> 0 -> rng RNG_all g (ly_al row) /\ rng_shcov RNG_all g (ly_al row)).
  { intros G0 A0. pose proof (Ag G0 A0) as (AG0 & _ & AG2 & _).
    split; [apply rng_all; unfold APPMEM_END in *; lia | apply rng_all_shcov; lia]. }
  assert (RJ14 : ly_k row = 5 -> rng_shcov RNG_all JOIN_0014 32).
  { intros Hk5. pose proof (AJ14 Hk5) as (AK0 & _ & AK2 & _). apply rng_all_shcov; lia. }
  assert (RJ13 : ly_k row = 6 -> rng_shcov RNG_all JOIN_0013 32).
  { intros Hk6. pose proof (AJ13 Hk6) as (AK0 & _ & AK2 & _). apply rng_all_shcov; lia. }
  exact (evtF_evt rsegs RNG_all _ _
           (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6 F fc m o f md d s g n ns FS row tb mb nb gb db sb junk
               Ea0 Ea1 Ea2 Ea3 Ea4 Ea6 Ea7 Et4
               Hn Hns Hg HS16 HST Dsf Dst Dsm Dsn Dsd Dss Dsg Hf0 Hf8 Hf24 Hrl HR Hk Hc HL HG HA Hao Htm Hc2 HLA
               Hmd0 Hmd8 Hmd296 Hml HM Hnm Ho Ho1492 HEo Hdb HD Hsb HSb Hgb Hns0 MI0
               HAC HSW HHM HAE AWIN Af Amd Ad As APD APS Atm An Ag APg AO AJ14 AJ13 FP FPtm FPn FPg FPT
               RRB RWIN RWSH RFS RFSH RIMG RTLS RROW RROWS RMD RMDS RD RDS RS RSS RO RTM RNB RG RJ14 RJ13)).
Qed.
