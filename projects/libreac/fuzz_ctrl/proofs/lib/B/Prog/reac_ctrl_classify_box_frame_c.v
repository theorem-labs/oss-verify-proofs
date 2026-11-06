From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c RcAsanFP
  reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* The model reac_ctrl_classify_box_frame_ev is the ubsan contract's (lib/U/Prog/reac_ctrl_classify_box_frame_c.v);
   its addresses are not used here. *)
Definition REAC_CTRL_CLASSIFY_BOX_FRAME : Z := 0x837c4.
(* K = 64 + max(K of reac_ctrl_parse 8800, the bcmp wrapper 4560, reac_ctrl_checksum_verify 16): the frame is 64 bytes
   and the callees run at S - 64 (contracts/libreac/reac_ctrl_classify_box_frame.md Names). *)
Definition REAC_CTRL_CLASSIFY_BOX_FRAME_K : Z := 8864.

(* The writes outside the side stack (fp's W) and the data ranges (fp's D). *)
Definition reac_ctrl_classify_box_frame_W (o v S : Z) : list ivl :=
  [(S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S); (o, o + 36); (v, v + 4)].
Definition reac_ctrl_classify_box_frame_D (f n u o v : Z) : list ivl :=
  (if n <? 50 then [] else [(f, f + 50); (u, u + 6)]) ++ [(o, o + 36); (v, v + 4)].

(* The thread cells that fp names are apart from the class-1 side-stack bytes (struct.asan.runtime RT4.3) and from
   the shadow of the function's window [lo, hi): reac_ctrl_parse's frame on the side stack or on the real stack keeps
   them (reac_ctrl_parse_tls of lib/B/Prog/reac_ctrl_parse_c.v for the window [S - 8864, S - 64)). *)
Definition reac_ctrl_classify_box_frame_tls (m : word -> option byte) (TP FS lo hi : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    fp_dj (fp_tls TP DT TS C T DB k) (fp_w [1%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]).

(* The ubsan contract (lib/U/Prog/reac_ctrl_classify_box_frame_c.v, the plain form) with K = 8864 and the premises of
   the asan-ubsan build (S1.8, S1.9 of the English contract): the runtime's cells and shadow (asan_cells, shadow_rw),
   the window in AppMem and addressable; for reac_ctrl_parse the addressable bytes at f, o and BC, o's end in AppMem
   and o apart from the bcmp wrapper's cells, the cells the bcmp wrapper reads, and the side-stack state for its
   __asan_stack_malloc_1 (fp [1%nat], reac_ctrl_classify_box_frame_tls); for the two bcmp wrapper calls (o + 4, u, 6),
   (o + 10, u, 6) the addressable 6 bytes at u and the ends u + 6, u + 7 in AppMem; for the own shadow checks the
   addressable bytes at o and v; for asan_cells at the return v apart from [RT_LO, RT_HI). The run may also write the
   class-1 side-stack bytes (fp_w [1%nat] FS) and the shadow of its window. *)
Definition reac_ctrl_classify_box_frame_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 u -> a3 = Z_to_bv 64 o -> a4 = Z_to_bv 64 v ->
    sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S (reac_ctrl_classify_box_frame_W o v S)
      (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls m (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_CLASSIFY_BOX_FRAME) fc None m (seg_rom rsegs)).

(* Footprint form (re-walk (D), RECIPE.md step 1 (a working note, not in this delivery)): the same run as an ExecF.evtF under a footprint
   RNG, with one rng premise per region the run and its callees read or write, each under the guard its data
   premise carries: the image (every absolute cell the run and its callees load -- the shadow-offset cells
   GOT_CELL_K/CELL_K, the GOT entries and CF that the bcmp wrapper reads), this frame's 64-byte window and the
   callees' frames below it (reac_ctrl_parse at S - 64, the bcmp wrapper, reac_ctrl_checksum_verify), and each
   buffer with the shadow bytes the ASan checks read.  A buffer a CALLEE checks (f by reac_ctrl_parse and
   reac_ctrl_checksum_verify, u by the bcmp wrapper, BC by reac_ctrl_parse's bcmp, o also by reac_ctrl_parse and
   the bcmp wrapper) gets the 8-aligned shadow WORD cover (the wrappers load shadow words); v, which only this
   function checks with single-byte lb loads, gets the byte-exact cover; o, checked by this function AND by
   callees, takes the word cover (it is a superset of the byte-exact range).  rng_bytes RNG is carried for the
   bcmp wrapper's _F contract (route 1 one level down).  The run also enters reac_ctrl_parse, whose own footprint
   form (lib/B/Prog/reac_ctrl_parse_c.v reac_ctrl_parse_contract_F) names four more regions: the shadow WORD cover
   of parse's window, the side stack's header [FS, fs_frame FS 0 0), the class-1 side-stack bytes fp_w [1%nat] FS
   (the frame __asan_stack_malloc_1 may hand it, with its flag, hint and shadow) and the cells of asan_tls_cells
   that the runtime reads through tp.  They are carried here in this frame's own variables -- the shadow word
   cover of THIS window covers parse's, which lies inside it -- so the proof passes them down by rng_sub.
   RNG is bound FIRST, before the register binders (every _F contract binds it first). *)
Definition reac_ctrl_classify_box_frame_contract_F : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S FS : Z)
         (fr us junk vb : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 u -> a3 = Z_to_bv 64 o -> a4 = Z_to_bv 64 v ->
    sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> S < 2^64 ->
    S mod 16 = 0 ->
    REAC_CTRL_CLASSIFY_BOX_FRAME_K <= S -> stk rsegs m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\
                (f + 50 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= f)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> rw_cells rsegs m o [CB 36 junk] ->
    (o + 36 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    length us = 6%nat ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\
                (u + 6 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= u)) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> rw_cells rsegs m v [CB 4 vb] ->
    (v + 4 <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K \/ S <= v) ->
    (v + 4 <= o \/ o + 36 <= v) -> (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    mem_inv rsegs m ->
    (* asan-ubsan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_CLASSIFY_BOX_FRAME_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S (reac_ctrl_classify_box_frame_W o v S)
      (reac_ctrl_classify_box_frame_D f n u o v) ->
    reac_ctrl_classify_box_frame_tls m (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S ->
    (* footprint *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    rng RNG (shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) / 8 * 8)
      (shadow_addr (S - 1) / 8 * 8 + 8 - shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) / 8 * 8) ->
    (50 <= n -> rng RNG f 50 /\
       rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 50 - 1) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    rng RNG o 36 ->
    rng RNG (shadow_addr o / 8 * 8) (shadow_addr (o + 36 - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8) ->
    (50 <= n -> rng RNG u 6 /\
       rng RNG (shadow_addr u / 8 * 8) (shadow_addr (u + 6 - 1) / 8 * 8 + 8 - shadow_addr u / 8 * 8)) ->
    rng RNG v 4 ->
    rng RNG (shadow_addr v) (shadow_addr (v + 4 - 1) - shadow_addr v + 1) ->
    rng RNG REAC_CTRL_PARSE_BC 6 ->
    rng RNG (shadow_addr REAC_CTRL_PARSE_BC / 8 * 8)
      (shadow_addr (REAC_CTRL_PARSE_BC + 6 - 1) / 8 * 8 + 8 - shadow_addr REAC_CTRL_PARSE_BC / 8 * 8) ->
    rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(o, o + 36); (v, v + 4); (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K, S)] ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_CLASSIFY_BOX_FRAME) fc None m (seg_rom rsegs)).

(* The old contract as a corollary: evtF_evt of the footprint form at RNG_all, each rng premise by rng_all. *)
Lemma reac_ctrl_classify_box_frame_contract_of_F :
  reac_ctrl_classify_box_frame_contract_F -> reac_ctrl_classify_box_frame_contract.
Proof.
  unfold reac_ctrl_classify_box_frame_contract_F, reac_ctrl_classify_box_frame_contract. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n u o v S FS fr us junk vb E0 E1 E2 E3 E4 Esp Rf Rn Ru Ro Rv RS1 S16 RK Hstk Lfr HF50 Ho0 Ho4 Ho36 ROcell
    DOs DOf DOu Lus HU50 Hv0 Hv4 Hv36 RVcell DVs DVo DVf DVu MI AC SW HHM HAE AW AFU AO HOA HOC AV HVR HBC
    CL1 CL2 CL3 CL4 CL5 FP0 TL0.
  (* the side stack's bounds and the class-1 addresses, for the three side-stack premises *)
  pose proof (eq_refl : REAC_CTRL_CLASSIFY_BOX_FRAME_K = 8864) as HK.
  pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (EFR1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EFL : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EHT : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  apply (evtF_evt rsegs RNG_all).
  apply (HF RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            F fc m f n u o v S FS fr us junk vb); try assumption.
  - (* rng_bytes RNG_all: vacuous (every per-byte-decided footprint, RNG_all included) *)
    intros b j Hb Hj Hk. exact I.
  - apply rng_all; lia.
  - apply rng_all; unfold REAC_CTRL_CLASSIFY_BOX_FRAME_K in *; lia.
  - (* the shadow of the window *)
    apply rng_all; unfold shadow_addr, ASAN_K, REAC_CTRL_CLASSIFY_BOX_FRAME_K in *;
      Z.div_mod_to_equations; lia.
  - intros HN. destruct (HF50 HN) as (Hf0 & Hf50b & _ & _).
    split; [apply rng_all; lia|].
    apply rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - apply rng_all; lia.
  - apply rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - intros HN. destruct (HU50 HN) as (Hu6 & _ & _).
    split; [apply rng_all; lia|].
    apply rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - apply rng_all; lia.
  - apply rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - apply rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply rng_all; unfold shadow_addr, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* the side stack's header *) apply rng_all; rewrite ?EFR0; lia.
  - (* the class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply rng_all;
      rewrite ?EM, ?EFR1, ?EFL, ?EHT; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* the cells of asan_tls_cells: each is a cell the run reads, so bytes_at bounds it *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply rng_all; lia|]).
    destruct Hiv.
Qed.
