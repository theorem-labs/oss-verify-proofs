From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcPorts RcBox RcSynth RcLay RcFin RcEmit
  reac_ctrl_build_as_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c RcAsanFP
  reac_box_model_block_c.
Import ListNotations.
Open Scope Z_scope.

(* The models ba_row, ba_fr, ba_tbl, ba_go, ba_E, ba_X are the plain contract's (lib/Prog/reac_ctrl_build_as_c.v);
   its addresses are not used here. *)
Definition REAC_CTRL_BUILD_AS : Z := 0x848ac.
(* The window of ctrl_emit_as (lib/A/Prog/ctrl_emit_as_c.v), which runs at the entry sp (tail jump); the own frame
   (80) and reac_box_model_upstream_width's (16) are inside it. *)
Definition REAC_CTRL_BUILD_AS_K : Z := 4640.
(* CTRL_FRAMES (.data.rel.ro); the code reads its rows 3 .. 9: the 168 bytes [BA_FR + 72, BA_FR + 240). *)
Definition BA_FR : Z := 0x9f7e0.
(* switch.table.reac_ctrl_build_as (.rodata): 7 words, word b = ba_row b. *)
Definition BA_SW : Z := 0x21980.

(* The thread cells that fp names are apart from the class-0 and class-1 side-stack bytes and from the shadow of the
   window [lo, hi) (ctrl_emit_as_tls of lib/A/Prog/ctrl_emit_as_c.v, which this run passes on at its tail jump). *)
Definition reac_ctrl_build_as_tls (m : word -> option byte) (TP FS lo hi : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    fp_dj (fp_tls TP DT TS C T DB k) (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]).

Definition reac_ctrl_build_as_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns FS : Z)
         (mb nb db sb junk : list byte),
    let S := bv_unsigned sp in
    let Lo := S - REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let len := 52 + 36 * n in
    let go := ba_go o md b in
    let E := ba_E n mb b in
    let R := if go && E then len else 0 in
    let nm := (b = 5 \/ b = 6) /\ has mb <> 0 /\ rname mb <> 0 in
    let W := [(Lo, S); (o, o + R)] in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns -> -2^31 <= ns <= 0 ->
    S mod 16 = 0 -> stk rsegs m Lo S ->
    bytes_at rsegs m (BA_FR + 72) ba_tbl -> ly_dj Lo S (BA_FR + 72) (BA_FR + 240) ->
    length db = 6%nat -> bytes_at rsegs m d db -> ly_dj Lo S d (d + 6) ->
    length sb = 6%nat -> bytes_at rsegs m s sb -> ly_dj Lo S s (s + 6) ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    (md <> 0 -> nm -> name_ok nb /\ bytes_at rsegs m (rname mb) nb /\
                      ly_dj Lo S (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (o <> 0 -> o + 1492 <= 2^64) ->
    (go && E = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\ ly_dj Lo S o (o + len) /\
       ly_dj o (o + len) (BA_FR + 72) (BA_FR + 240) /\ ly_dj o (o + len) md (md + 296) /\
       (nm -> ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) s (s + 6)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= Lo -> S <= APPMEM_END -> addressable m Lo REAC_CTRL_BUILD_AS_K ->
    addressable m BA_SW 56 -> addressable m (BA_FR + 72) 168 -> addressable m d 6 -> addressable m s 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (s + 6) /\ app_mem (s + 7) ->
    (md <> 0 -> addressable m md 296) ->
    (md <> 0 -> nm -> addressable m (rname mb) (Z.of_nat (length nb))) ->
    (go && E = true -> addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (b = 1 -> addressable m JOIN_0014 32) -> (b = 2 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS Lo S W
      [(BA_FR + 72, BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)] ->
    (md <> 0 -> nm -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    reac_ctrl_build_as_tls m (bv_unsigned tp) FS Lo S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 R)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (W ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr Lo, shadow_addr S)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S
         /\ asan_cells m' /\ shadow_rw m' /\ addressable m' Lo REAC_CTRL_BUILD_AS_K
         /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS Lo S W
              [(BA_FR + 72, BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)]
         /\ (go = false -> munch [(S - 80, S)] m m')
         /\ (go && E = true ->
               bytes_at rsegs m' o
                 (em_fr db sb (bv_unsigned a5 mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234) (ba_X md mb nb b) len)
               /\ em_wok n = true
               /\ (b <= 1 -> blocksum (ba_X md mb nb b) = 0)
               /\ (blocksum (ly_Z md mb nb b) = 0 -> ba_X md mb nb b = ly_Z md mb nb b)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_BUILD_AS) fc None m (seg_rom rsegs)).

(* ---- the footprint form (RECIPE.md step 1 (a working note, not in this delivery)) ----
   The same run as an ExecF.evtF under a footprint RNG that holds every region the run and its callees read or
   write. An instruction fetch is not an access of ExecF, so only data accesses are covered. RNG is the FIRST
   binder (the binding convention of RECIPE.md (a working note, not in this delivery)). The footprint premises start with rng_bytes RNG: the
   tail callee's ctrl_emit_as_contract_F carries it (a working branch 96c5aa3e60d,
   lib/A/Prog/ctrl_emit_as_c.v), so this caller must too. A shadow cover is rounded out to whole 8-byte WORDS at
   both ends, in the shape that ctrl_emit_as_c.v's own footprint form uses. The regions, in the order of the rng
   premises below:
   - the image [0x10000, 0x10000 + 0x5ee000): every cell this run and the run of the tail callee ctrl_emit_as
     read at an ABSOLUTE address (the switch table at BA_SW, the CTRL_FRAMES row at f, the JOIN templates of
     reac_box_model_block, GOT_CELL_K and CELL_K and the rest of [RT_LO, RT_HI), the image-resident thread
     cells of fp_tls), and [0x7fffa000, 0x7fffa000 + 0xbdc00), the shadow of that span, which holds the shadow
     bytes the instrumented check of the switch-table load reads (0x7fffa000 = shadow_addr 0x10000 and
     0xbdc00 = 0x5ee000 / 8; both ends are 8-aligned);
   - the window [Lo, S) and the cover of its shadow: this frame, reac_box_model_upstream_width's frame below
     it, and the whole window of ctrl_emit_as, which runs at the same sp (tail jump) and poisons and releases
     its frame;
   - GOT_CELL_K and CELL_K, the two 8-byte loads of the shadow offset, also kept as their own premises (the
     literal-address form the step tactic's access solver takes);
   - the side stack [FS, FS + FS_SIZE) and the cover of its shadow: the hint words, the flag bytes and the
     class-0 and class-1 frames that __asan_stack_malloc_0 / _1 hand out below ctrl_emit_as (every range of
     fp_w [0; 1] FS is inside the two);
   - the thread cells that fp_tls names, under the guard asan_tls_cells carries in THIS run's memory m (the
     per-memory shape of ctrl_emit_as_rtls; a Theorem Labs lane 2026-10-28: the earlier form quantified every memory,
     which only an everything-footprint satisfies). The run carries the premise to its later memory by
     ba_rtls_W (reac_ctrl_build_asF.v);
   - each buffer the run passes on with the cover of its shadow bytes, under exactly the guard its
     plain-contract premise carries: the 296-byte model at md, the two 6-byte headers at d and s, the name at
     rname mb, and the output [o, o + len) when the run writes one.
   reac_ctrl_build_as_contract_of_F gives the old statement back with RNG_all, so the footprint form asks for
   nothing the old contract lacks. *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes.

(* The 8-aligned word cover of the shadow bytes of [p, q] of application memory is inside RNG_all (the text of
   ctrl_emit_as_c.v's rng_all_shcov, a Theorem Labs lane 96c5aa3e60d). *)
Lemma ba_rng_all_shcov : forall p q, 0 <= p -> q <= APPMEM_END ->
  rng RNG_all (shadow_addr p / 8 * 8) (shadow_addr q / 8 * 8 + 8 - shadow_addr p / 8 * 8).
Proof.
  intros p q Hp Hq. apply rng_all; unfold shadow_addr, ASAN_K, APPMEM_END in *;
    Z.div_mod_to_equations; lia.
Qed.

Definition reac_ctrl_build_as_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns FS : Z)
         (mb nb db sb junk : list byte),
    let S := bv_unsigned sp in
    let Lo := S - REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let len := 52 + 36 * n in
    let go := ba_go o md b in
    let E := ba_E n mb b in
    let R := if go && E then len else 0 in
    let nm := (b = 5 \/ b = 6) /\ has mb <> 0 /\ rname mb <> 0 in
    let W := [(Lo, S); (o, o + R)] in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns -> -2^31 <= ns <= 0 ->
    S mod 16 = 0 -> stk rsegs m Lo S ->
    bytes_at rsegs m (BA_FR + 72) ba_tbl -> ly_dj Lo S (BA_FR + 72) (BA_FR + 240) ->
    length db = 6%nat -> bytes_at rsegs m d db -> ly_dj Lo S d (d + 6) ->
    length sb = 6%nat -> bytes_at rsegs m s sb -> ly_dj Lo S s (s + 6) ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    (md <> 0 -> nm -> name_ok nb /\ bytes_at rsegs m (rname mb) nb /\
                      ly_dj Lo S (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (o <> 0 -> o + 1492 <= 2^64) ->
    (go && E = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\ ly_dj Lo S o (o + len) /\
       ly_dj o (o + len) (BA_FR + 72) (BA_FR + 240) /\ ly_dj o (o + len) md (md + 296) /\
       (nm -> ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) s (s + 6)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= Lo -> S <= APPMEM_END -> addressable m Lo REAC_CTRL_BUILD_AS_K ->
    addressable m BA_SW 56 -> addressable m (BA_FR + 72) 168 -> addressable m d 6 -> addressable m s 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (s + 6) /\ app_mem (s + 7) ->
    (md <> 0 -> addressable m md 296) ->
    (md <> 0 -> nm -> addressable m (rname mb) (Z.of_nat (length nb))) ->
    (go && E = true -> addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (b = 1 -> addressable m JOIN_0014 32) -> (b = 2 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS Lo S W
      [(BA_FR + 72, BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)] ->
    (md <> 0 -> nm -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    reac_ctrl_build_as_tls m (bv_unsigned tp) FS Lo S ->
    (* the footprint: rng_bytes, then one rng premise per region the run and its callees read or write *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG 0x7fffa000 0xbdc00 ->
    rng RNG Lo REAC_CTRL_BUILD_AS_K ->
    rng RNG (shadow_addr Lo / 8 * 8) (shadow_addr (S - 1) / 8 * 8 + 8 - shadow_addr Lo / 8 * 8) ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG FS FS_SIZE ->
    rng RNG (shadow_addr FS / 8 * 8) (shadow_addr (FS + FS_SIZE - 1) / 8 * 8 + 8 - shadow_addr FS / 8 * 8) ->
    (* the thread cells of THIS run's memory m (per memory, as ctrl_emit_as_rtls; the earlier `forall mm` form
       quantified every memory, which only an everything-footprint satisfies: a Theorem Labs lane's signature #1) *)
    (forall (DT TS C T DB : word) (kk : Z),
       asan_tls_cells m (bv_unsigned tp) DT TS C T DB kk ->
       Forall (fun r => rng RNG (fst r) (snd r - fst r)) (fp_tls (bv_unsigned tp) DT TS C T DB kk)) ->
    (md <> 0 -> rng RNG md 296 /\
       rng RNG (shadow_addr md / 8 * 8) (shadow_addr (md + 295) / 8 * 8 + 8 - shadow_addr md / 8 * 8)) ->
    rng RNG d 6 ->
    rng RNG (shadow_addr d / 8 * 8) (shadow_addr (d + 5) / 8 * 8 + 8 - shadow_addr d / 8 * 8) ->
    rng RNG s 6 ->
    rng RNG (shadow_addr s / 8 * 8) (shadow_addr (s + 5) / 8 * 8 + 8 - shadow_addr s / 8 * 8) ->
    (md <> 0 -> nm -> rng RNG (rname mb) (Z.of_nat (length nb)) /\
       rng RNG (shadow_addr (rname mb) / 8 * 8)
         (shadow_addr (rname mb + Z.of_nat (length nb) - 1) / 8 * 8 + 8 - shadow_addr (rname mb) / 8 * 8)) ->
    (go && E = true -> rng RNG o len /\
       rng RNG (shadow_addr o / 8 * 8) (shadow_addr (o + len - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 R)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (W ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr Lo, shadow_addr S)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S
         /\ asan_cells m' /\ shadow_rw m' /\ addressable m' Lo REAC_CTRL_BUILD_AS_K
         /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS Lo S W
              [(BA_FR + 72, BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)]
         /\ (go = false -> munch [(S - 80, S)] m m')
         /\ (go && E = true ->
               bytes_at rsegs m' o
                 (em_fr db sb (bv_unsigned a5 mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234) (ba_X md mb nb b) len)
               /\ em_wok n = true
               /\ (b <= 1 -> blocksum (ba_X md mb nb b) = 0)
               /\ (blocksum (ly_Z md mb nb b) = 0 -> ba_X md mb nb b = ly_Z md mb nb b)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_BUILD_AS) fc None m (seg_rom rsegs)).

Lemma reac_ctrl_build_as_contract_of_F :
  reac_ctrl_build_as_contract_F -> reac_ctrl_build_as_contract.
Proof.
  unfold reac_ctrl_build_as_contract_F, reac_ctrl_build_as_contract. cbv zeta.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns FS mb nb db sb junk
    Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Hns HS16 HST HT DsT Hdb HD Dsd Hsb HSb Dss HM HN Ho1492 HEo MI0 HAC HSW HHM HAE
    AWIN ASW ATB AD AS APD APS AM AN AO AJ14 AJ13 FP FPN FPT.
  pose proof HST as (STlo & SThi & _).
  pose proof FP as FP'.
  destruct FP' as (DT0 & TS0 & C0 & T0 & DB0 & k0 & TLS0 & HTP & HFS & H88 & H96 & HCLS & HFSlo & HAPP & DJW & DJD).
  pose proof HFS as (FSpos & FS4096 & FSGT & FSAPP & FSSTK).
  pose proof AD as (AD0 & _ & AD2 & _).
  pose proof AS as (AS0 & _ & AS2 & _).
  eapply evtF_evt,
    (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
        F fc m o md b d s ns FS mb nb db sb junk); try assumption.
  - unfold rng_bytes; intros; exact I.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; unfold REAC_CTRL_BUILD_AS_K in *; lia.
  - apply ba_rng_all_shcov; unfold REAC_CTRL_BUILD_AS_K, APPMEM_END in *; lia.
  - apply rng_all; unfold GOT_CELL_K; lia.
  - apply rng_all; unfold CELL_K; lia.
  - apply rng_all; unfold REAC_CTRL_BUILD_AS_K, APPMEM_END, FS_SIZE in *; lia.
  - apply ba_rng_all_shcov; unfold REAC_CTRL_BUILD_AS_K, APPMEM_END, FS_SIZE in *; lia.
  - intros DT TS C T DB kk HC.
    unfold asan_tls_cells in HC.
    destruct HC as (C1 & C2 & C3 & C4 & C5 & Hkk & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 &
                    C17 & C18 & C19).
    destruct C11 as (tb0 & te0 & C11).
    destruct C3 as (B3 & B3' & _). destruct C4 as (B4 & B4' & _). destruct C8 as (B8 & B8' & _).
    destruct C9 as (B9 & B9' & _). destruct C10 as (B10 & B10' & _). destruct C17 as (B17 & B17' & _).
    destruct C19 as (B19 & B19' & _). destruct C11 as (B11 & B11' & _).
    rewrite length_le8 in B3', B4', B8', B9', B10', B17', B19'. rewrite !app_length, !length_le8 in B11'.
    unfold fp_tls, TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY,
      VERBOSITY, DTLS_TPOFF.
    repeat (apply Forall_cons; [cbn [fst snd]; apply rng_all; lia|]). apply Forall_nil.
  - intros Hmd. pose proof (AM Hmd) as (M0 & _ & M2 & _).
    split; [apply rng_all | apply ba_rng_all_shcov]; unfold APPMEM_END in *; lia.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply ba_rng_all_shcov; unfold APPMEM_END in *; lia.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply ba_rng_all_shcov; unfold APPMEM_END in *; lia.
  - intros Hmd Hnm. pose proof (AN Hmd Hnm) as (N0 & N1 & N2 & _).
    split; [apply rng_all | apply ba_rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros HE. pose proof (AO HE) as ((O0 & O1 & O2 & _) & _ & _).
    split; [apply rng_all | apply ba_rng_all_shcov]; unfold APPMEM_END in *; lia.
Qed.

(* ---- route (C) (a Theorem Labs lane 09:20Z; a Theorem Labs lane form 09:37Z / 09:38Z): the _on twins. The premise `shadow_rw m` becomes
   `shadow_rw_on (reac_ctrl_build_as_shadow_R ...) m` and the post's `shadow_rw m'` becomes
   `forall P, shadow_rw_on P m -> shadow_rw_on P m'`. The region is ctrl_emit_as's own region (a Theorem Labs lane,
   ctrl_emit_as_c.v blob 398ae3890b9) at this run's tail jump: S and FS unchanged (sp restored), f = BA_FR + 24 row(b),
   g = 0, n = upstream_width(md), row = ba_fr (ba_row b). reac_ctrl_build_as itself reads its shadow bytes (the
   switch-table entry; through reac_box_model_upstream_width the shadow of the box MODEL row's bytes [md + 16,
   md + 24)) through `addressable` premises, not through shadow_rw (a Theorem Labs lane batch 10: 1 + 2 shadow loads, 0
   stores); ctrl_emit_as's region relies on md <> 0, which the call has (go = true), and its 80-byte frame lies in ctrl_emit_as's window [S - 4640, S). The old statements follow. ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require ctrl_emit_as_c.

Definition reac_ctrl_build_as_shadow_R (S FS o md d s b : Z) (mb nb : list byte) : Z -> Prop :=
  ctrl_emit_as_c.ctrl_emit_as_shadow_R S FS o (BA_FR + 24 * ba_row b) md d s 0
    (bm_uw md (firstn 8 (skipn 16 mb))) (ba_fr (ba_row b)) mb nb.

Definition reac_ctrl_build_as_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns FS : Z)
         (mb nb db sb junk : list byte),
    let S := bv_unsigned sp in
    let Lo := S - REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let len := 52 + 36 * n in
    let go := ba_go o md b in
    let E := ba_E n mb b in
    let R := if go && E then len else 0 in
    let nm := (b = 5 \/ b = 6) /\ has mb <> 0 /\ rname mb <> 0 in
    let W := [(Lo, S); (o, o + R)] in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns -> -2^31 <= ns <= 0 ->
    S mod 16 = 0 -> stk rsegs m Lo S ->
    bytes_at rsegs m (BA_FR + 72) ba_tbl -> ly_dj Lo S (BA_FR + 72) (BA_FR + 240) ->
    length db = 6%nat -> bytes_at rsegs m d db -> ly_dj Lo S d (d + 6) ->
    length sb = 6%nat -> bytes_at rsegs m s sb -> ly_dj Lo S s (s + 6) ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    (md <> 0 -> nm -> name_ok nb /\ bytes_at rsegs m (rname mb) nb /\
                      ly_dj Lo S (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (o <> 0 -> o + 1492 <= 2^64) ->
    (go && E = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\ ly_dj Lo S o (o + len) /\
       ly_dj o (o + len) (BA_FR + 72) (BA_FR + 240) /\ ly_dj o (o + len) md (md + 296) /\
       (nm -> ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) s (s + 6)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_build_as_shadow_R S FS o md d s b mb nb) m ->
    HIGHMEM_BEG <= Lo -> S <= APPMEM_END -> addressable m Lo REAC_CTRL_BUILD_AS_K ->
    addressable m BA_SW 56 -> addressable m (BA_FR + 72) 168 -> addressable m d 6 -> addressable m s 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (s + 6) /\ app_mem (s + 7) ->
    (md <> 0 -> addressable m md 296) ->
    (md <> 0 -> nm -> addressable m (rname mb) (Z.of_nat (length nb))) ->
    (go && E = true -> addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (b = 1 -> addressable m JOIN_0014 32) -> (b = 2 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS Lo S W
      [(BA_FR + 72, BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)] ->
    (md <> 0 -> nm -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    reac_ctrl_build_as_tls m (bv_unsigned tp) FS Lo S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 R)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (W ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr Lo, shadow_addr S)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S
         /\ asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\ addressable m' Lo REAC_CTRL_BUILD_AS_K
         /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS Lo S W
              [(BA_FR + 72, BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)]
         /\ (go = false -> munch [(S - 80, S)] m m')
         /\ (go && E = true ->
               bytes_at rsegs m' o
                 (em_fr db sb (bv_unsigned a5 mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234) (ba_X md mb nb b) len)
               /\ em_wok n = true
               /\ (b <= 1 -> blocksum (ba_X md mb nb b) = 0)
               /\ (blocksum (ly_Z md mb nb b) = 0 -> ba_X md mb nb b = ly_Z md mb nb b)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_BUILD_AS) fc None m (seg_rom rsegs)).

Definition reac_ctrl_build_as_contract_F_on : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o md b d s ns FS : Z)
         (mb nb db sb junk : list byte),
    let S := bv_unsigned sp in
    let Lo := S - REAC_CTRL_BUILD_AS_K in
    let n := bm_uw md (firstn 8 (skipn 16 mb)) in
    let len := 52 + 36 * n in
    let go := ba_go o md b in
    let E := ba_E n mb b in
    let R := if go && E then len else 0 in
    let nm := (b = 5 \/ b = 6) /\ has mb <> 0 /\ rname mb <> 0 in
    let W := [(Lo, S); (o, o + R)] in
    bv_unsigned a0 = o -> bv_unsigned a1 = md -> bv_unsigned a2 = b -> bv_unsigned a3 = d -> bv_unsigned a4 = s ->
    a7 = Z_to_bv 64 ns -> -2^31 <= ns <= 0 ->
    S mod 16 = 0 -> stk rsegs m Lo S ->
    bytes_at rsegs m (BA_FR + 72) ba_tbl -> ly_dj Lo S (BA_FR + 72) (BA_FR + 240) ->
    length db = 6%nat -> bytes_at rsegs m d db -> ly_dj Lo S d (d + 6) ->
    length sb = 6%nat -> bytes_at rsegs m s sb -> ly_dj Lo S s (s + 6) ->
    (md <> 0 -> md mod 8 = 0 /\ md + 296 <= 2^64 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
                ly_dj Lo S md (md + 296)) ->
    (md <> 0 -> nm -> name_ok nb /\ bytes_at rsegs m (rname mb) nb /\
                      ly_dj Lo S (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (o <> 0 -> o + 1492 <= 2^64) ->
    (go && E = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\ ly_dj Lo S o (o + len) /\
       ly_dj o (o + len) (BA_FR + 72) (BA_FR + 240) /\ ly_dj o (o + len) md (md + 296) /\
       (nm -> ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) s (s + 6)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_build_as_shadow_R S FS o md d s b mb nb) m ->
    HIGHMEM_BEG <= Lo -> S <= APPMEM_END -> addressable m Lo REAC_CTRL_BUILD_AS_K ->
    addressable m BA_SW 56 -> addressable m (BA_FR + 72) 168 -> addressable m d 6 -> addressable m s 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (s + 6) /\ app_mem (s + 7) ->
    (md <> 0 -> addressable m md 296) ->
    (md <> 0 -> nm -> addressable m (rname mb) (Z.of_nat (length nb))) ->
    (go && E = true -> addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (b = 1 -> addressable m JOIN_0014 32) -> (b = 2 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS Lo S W
      [(BA_FR + 72, BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)] ->
    (md <> 0 -> nm -> fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    reac_ctrl_build_as_tls m (bv_unsigned tp) FS Lo S ->
    (* the footprint: rng_bytes, then one rng premise per region the run and its callees read or write *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG 0x7fffa000 0xbdc00 ->
    rng RNG Lo REAC_CTRL_BUILD_AS_K ->
    rng RNG (shadow_addr Lo / 8 * 8) (shadow_addr (S - 1) / 8 * 8 + 8 - shadow_addr Lo / 8 * 8) ->
    rng RNG GOT_CELL_K 8 -> rng RNG CELL_K 8 ->
    rng RNG FS FS_SIZE ->
    rng RNG (shadow_addr FS / 8 * 8) (shadow_addr (FS + FS_SIZE - 1) / 8 * 8 + 8 - shadow_addr FS / 8 * 8) ->
    (* the thread cells of THIS run's memory m (per memory, as ctrl_emit_as_rtls; the earlier `forall mm` form
       quantified every memory, which only an everything-footprint satisfies: a Theorem Labs lane's signature #1) *)
    (forall (DT TS C T DB : word) (kk : Z),
       asan_tls_cells m (bv_unsigned tp) DT TS C T DB kk ->
       Forall (fun r => rng RNG (fst r) (snd r - fst r)) (fp_tls (bv_unsigned tp) DT TS C T DB kk)) ->
    (md <> 0 -> rng RNG md 296 /\
       rng RNG (shadow_addr md / 8 * 8) (shadow_addr (md + 295) / 8 * 8 + 8 - shadow_addr md / 8 * 8)) ->
    rng RNG d 6 ->
    rng RNG (shadow_addr d / 8 * 8) (shadow_addr (d + 5) / 8 * 8 + 8 - shadow_addr d / 8 * 8) ->
    rng RNG s 6 ->
    rng RNG (shadow_addr s / 8 * 8) (shadow_addr (s + 5) / 8 * 8 + 8 - shadow_addr s / 8 * 8) ->
    (md <> 0 -> nm -> rng RNG (rname mb) (Z.of_nat (length nb)) /\
       rng RNG (shadow_addr (rname mb) / 8 * 8)
         (shadow_addr (rname mb + Z.of_nat (length nb) - 1) / 8 * 8 + 8 - shadow_addr (rname mb) / 8 * 8)) ->
    (go && E = true -> rng RNG o len /\
       rng RNG (shadow_addr o / 8 * 8) (shadow_addr (o + len - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 R)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs)
         /\ munch (W ++ fp_w [0%nat; 1%nat] FS ++ [(shadow_addr Lo, shadow_addr S)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' Lo S
         /\ asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m') /\ addressable m' Lo REAC_CTRL_BUILD_AS_K
         /\ fp [0%nat; 1%nat] m' (bv_unsigned tp) FS Lo S W
              [(BA_FR + 72, BA_FR + 240); (md, md + 296); (d, d + 6); (s, s + 6); (o, o + R)]
         /\ (go = false -> munch [(S - 80, S)] m m')
         /\ (go && E = true ->
               bytes_at rsegs m' o
                 (em_fr db sb (bv_unsigned a5 mod 65536) (Z_to_bv 8 205) (Z_to_bv 8 234) (ba_X md mb nb b) len)
               /\ em_wok n = true
               /\ (b <= 1 -> blocksum (ba_X md mb nb b) = 0)
               /\ (blocksum (ly_Z md mb nb b) = 0 -> ba_X md mb nb b = ly_Z md mb nb b)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_BUILD_AS) fc None m (seg_rom rsegs)).

(* The old statements: shadow_rw gives the region (shadow_rw_on_of_shadow_rw); the post's transport at
   P := fun _ => True gives shadow_rw back (shadow_rw_of_on_all). *)
Lemma reac_ctrl_build_as_contract_of_on : reac_ctrl_build_as_contract_on -> reac_ctrl_build_as_contract.
Proof.
  intros H. unfold reac_ctrl_build_as_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns FS mb nb db sb junk.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o md b d s ns FS mb nb db sb junk) as H'.
  unfold reac_ctrl_build_as_contract_on in H'. cbv zeta in H' |- *.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Hns HS16 HST HT DsT Hdb HD Dsd Hsb HSb Dss HM HN Ho1492 HEo MI0 HAC HSW HHM HAE
    AWIN ASW ATB AD AS APD APS AM AN AO AJ14 AJ13 FP FPN FPT.
  eapply evt_mono.
  - exact (H' Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Hns HS16 HST HT DsT Hdb HD Dsd Hsb HSb Dss HM HN Ho1492 HEo MI0 HAC (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) HHM HAE
    AWIN ASW ATB AD AS APD APS AM AN AO AJ14 AJ13 FP FPN FPT).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                Ems & MU & WM & MI & ST & AC & SW & Rest).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj Ems (conj MU (conj WM (conj MI (conj ST (conj AC (conj _ Rest))))))).
    exact (A.ShadowRwOn.shadow_rw_of_on_all m' (SW (fun _ => True) (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW))).
Qed.

Lemma reac_ctrl_build_as_contract_F_of_on : reac_ctrl_build_as_contract_F_on -> reac_ctrl_build_as_contract_F.
Proof.
  intros H. unfold reac_ctrl_build_as_contract_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns FS mb nb db sb junk.
  pose proof (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o md b d s ns FS mb nb db sb junk) as H'.
  unfold reac_ctrl_build_as_contract_F_on in H'. cbv zeta in H' |- *.
  intros Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Hns HS16 HST HT DsT Hdb HD Dsd Hsb HSb Dss HM HN Ho1492 HEo MI0 HAC HSW HHM HAE
    AWIN ASW ATB AD AS APD APS AM AN AO AJ14 AJ13 FP FPN FPT
    RRB RIMG RISH RWIN RWSH RGK RCK RFS RFSS RTLS RMD RDD RDS RSD RSS RNB ROO.
  eapply evtF_mono.
  - exact (H' Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Hns HS16 HST HT DsT Hdb HD Dsd Hsb HSb Dss HM HN Ho1492 HEo MI0 HAC (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW) HHM HAE
    AWIN ASW ATB AD AS APD APS AM AN AO AJ14 AJ13 FP FPN FPT
    RRB RIMG RISH RWIN RWSH RGK RCK RFS RFSS RTLS RMD RDD RDS RSD RSS RNB ROO).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                Ems & MU & WM & MI & ST & AC & SW & Rest).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj Ems (conj MU (conj WM (conj MI (conj ST (conj AC (conj _ Rest))))))).
    exact (A.ShadowRwOn.shadow_rw_of_on_all m' (SW (fun _ => True) (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m HSW))).
Qed.

(* The footprint _on twin gives the plain _on twin at ExecF.RNG_all, as reac_ctrl_build_as_contract_of_F does. *)
Lemma reac_ctrl_build_as_contract_on_of_F_on :
  reac_ctrl_build_as_contract_F_on -> reac_ctrl_build_as_contract_on.
Proof.
  unfold reac_ctrl_build_as_contract_F_on, reac_ctrl_build_as_contract_on. cbv zeta.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o md b d s ns FS mb nb db sb junk
    Ha0 Ha1 Ha2 Ha3 Ha4 Ha7 Hns HS16 HST HT DsT Hdb HD Dsd Hsb HSb Dss HM HN Ho1492 HEo MI0 HAC HSW HHM HAE
    AWIN ASW ATB AD AS APD APS AM AN AO AJ14 AJ13 FP FPN FPT.
  pose proof HST as (STlo & SThi & _).
  pose proof FP as FP'.
  destruct FP' as (DT0 & TS0 & C0 & T0 & DB0 & k0 & TLS0 & HTP & HFS & H88 & H96 & HCLS & HFSlo & HAPP & DJW & DJD).
  pose proof HFS as (FSpos & FS4096 & FSGT & FSAPP & FSSTK).
  pose proof AD as (AD0 & _ & AD2 & _).
  pose proof AS as (AS0 & _ & AS2 & _).
  eapply evtF_evt,
    (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
        F fc m o md b d s ns FS mb nb db sb junk); try assumption.
  - unfold rng_bytes; intros; exact I.
  - apply rng_all; lia.
  - apply rng_all; lia.
  - apply rng_all; unfold REAC_CTRL_BUILD_AS_K in *; lia.
  - apply ba_rng_all_shcov; unfold REAC_CTRL_BUILD_AS_K, APPMEM_END in *; lia.
  - apply rng_all; unfold GOT_CELL_K; lia.
  - apply rng_all; unfold CELL_K; lia.
  - apply rng_all; unfold REAC_CTRL_BUILD_AS_K, APPMEM_END, FS_SIZE in *; lia.
  - apply ba_rng_all_shcov; unfold REAC_CTRL_BUILD_AS_K, APPMEM_END, FS_SIZE in *; lia.
  - intros DT TS C T DB kk HC.
    unfold asan_tls_cells in HC.
    destruct HC as (C1 & C2 & C3 & C4 & C5 & Hkk & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 &
                    C17 & C18 & C19).
    destruct C11 as (tb0 & te0 & C11).
    destruct C3 as (B3 & B3' & _). destruct C4 as (B4 & B4' & _). destruct C8 as (B8 & B8' & _).
    destruct C9 as (B9 & B9' & _). destruct C10 as (B10 & B10' & _). destruct C17 as (B17 & B17' & _).
    destruct C19 as (B19 & B19' & _). destruct C11 as (B11 & B11' & _).
    rewrite length_le8 in B3', B4', B8', B9', B10', B17', B19'. rewrite !app_length, !length_le8 in B11'.
    unfold fp_tls, TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF, GOT_VERBOSITY,
      VERBOSITY, DTLS_TPOFF.
    repeat (apply Forall_cons; [cbn [fst snd]; apply rng_all; lia|]). apply Forall_nil.
  - intros Hmd. pose proof (AM Hmd) as (M0 & _ & M2 & _).
    split; [apply rng_all | apply ba_rng_all_shcov]; unfold APPMEM_END in *; lia.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply ba_rng_all_shcov; unfold APPMEM_END in *; lia.
  - apply rng_all; unfold APPMEM_END in *; lia.
  - apply ba_rng_all_shcov; unfold APPMEM_END in *; lia.
  - intros Hmd Hnm. pose proof (AN Hmd Hnm) as (N0 & N1 & N2 & _).
    split; [apply rng_all | apply ba_rng_all_shcov]; unfold APPMEM_END in *; lia.
  - intros HE. pose proof (AO HE) as ((O0 & O1 & O2 & _) & _ & _).
    split; [apply rng_all | apply ba_rng_all_shcov]; unfold APPMEM_END in *; lia.
Qed.
