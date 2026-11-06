From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay RcFin RcEmit
  ctrl_lay_block_c.
Import ListNotations.
Open Scope Z_scope.

Definition CTRL_EMIT_AS : Z := 0x1479c.
Definition CTRL_EMIT_AS_K : Z := 352.

Definition ctrl_emit_as_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o f md d s g n ns : Z)
         (row tb mb nb gb db sb junk : list byte),
    let S := bv_unsigned sp in
    let Lo := S - CTRL_EMIT_AS_K in
    let k := ly_k row in
    let L := ubat row 21 in
    let A := ubat row 23 in
    let c := ubat row 20 in
    let E := em_E L (ubat row 22) n (em_hid mb) in
    let len := em_len L n in
    let blk := fin c (ubat row 18) (ubat row 19)
                 (ly_lay k tb (ly_Z md mb nb (ly_bb k)) g (ly_ao row) (ly_al row) gb) in
    let nm := (3 <= k <= 9 /\ (ly_bb k = 5 \/ ly_bb k = 6)) /\ has mb <> 0 /\ rname mb <> 0 in
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
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if E then len else 0))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch [(Lo, S); (o, o + (if E then len else 0))] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S
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
