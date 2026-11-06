From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcClassify
  reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c RcAsanFP
  reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* The model reac_ctrl_classify_box_frame_ev is the plain contract's (lib/Prog/reac_ctrl_classify_box_frame_c.v); its
   addresses are not used here. *)
Definition REAC_CTRL_CLASSIFY_BOX_FRAME : Z := 0x831b8.
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
   them (reac_ctrl_parse_tls of lib/A/Prog/reac_ctrl_parse_c.v for the window [S - 8864, S - 64)). *)
Definition reac_ctrl_classify_box_frame_tls (m : word -> option byte) (TP FS lo hi : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    fp_dj (fp_tls TP DT TS C T DB k) (fp_w [1%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]).

(* The plain contract (lib/Prog/reac_ctrl_classify_box_frame_c.v) with K = 8864 and the premises of the asan build
   (S1.8, S1.9 of the English contract): the runtime's cells and shadow (asan_cells, shadow_rw), the window in AppMem
   and addressable; for reac_ctrl_parse the addressable bytes at f, o and BC, o's end in AppMem and o apart from the
   bcmp wrapper's cells, the cells the bcmp wrapper reads, and the side-stack state for its __asan_stack_malloc_1
   (fp [1%nat], reac_ctrl_classify_box_frame_tls); for the two bcmp wrapper calls (o + 4, u, 6), (o + 10, u, 6) the
   addressable 6 bytes at u and the ends u + 6, u + 7 in AppMem; for the own shadow checks the addressable bytes at o
   and v; for asan_cells at the return v apart from [RT_LO, RT_HI). The run may also write the class-1 side-stack
   bytes (fp_w [1%nat] FS) and the shadow of its window. *)
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
    (* asan *)
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

(* Footprint (_F) form of the contract above (re-walk (D), RECIPE step 1): the same run as an ExecF.evtF under a
   universally quantified footprint RNG, with one rng premise per region the run reads or writes.  Instruction
   fetch is not an access.  The regions, each as small as the run needs:
   - the image [0x10000, 0x5fe000), which holds the GOT cells and the memory-checking runtime words
     [RT_LO, RT_HI) that this run and its callees read, and the 6 bytes at REAC_CTRL_PARSE_BC;
   - the stack window [S - K, S), written, and the metadata bytes of that window (reac_ctrl_parse marks its own
     frame there);
   - the 36 bytes at o (read and written) and the 4 bytes at v (written);
   - when 50 <= n, the 50 bytes at f and the 6 bytes at u (read);
   - the metadata bytes of each instrumented check: of o, of v, of f, of u and of REAC_CTRL_PARSE_BC;
   - the side stack that __asan_stack_malloc_1 serves reac_ctrl_parse from: its header, the class-1 ranges
     fp_w [1%nat] FS (hint word, flag bytes, frames and their metadata bytes) and the thread cells it reads.
   The metadata bytes of [p, n) are given as the 8-ALIGNED word cover of the bytes the instrumented check loads
   (the check is a load of the shadow byte at (a >> 3) + 0x7fff8000 and a compare; the error path, a call of the
   report entry, is not reached).  Before the regions, rng_bytes RNG (lib/Lib/RngBytes.v): the published image-A
   footprint twins of the callees reac_ctrl_parse and the bcmp wrapper take it, so the caller carries it. *)

(* Every byte of every range of l is in RNG.  Bound free (no 0 <= lo and lo + len <= 2^64): the ranges of fp_tls
   are built from pointers the thread cells hold, whose bounds the caller need not carry. *)
Definition rng_ivls (RNG : ExecF.footprint) (l : list ivl) : Prop :=
  Forall (fun r => forall b (j : nat), fst r <= b -> b + Z.of_nat j <= snd r -> RNG b j) l.

(* The side-stack state of __asan_stack_malloc_1 (class 1, which reac_ctrl_parse's frame uses) in RNG: the header
   [FS, FS + 36864), the class-1 ranges, and the thread cells the allocation reads.  reac_ctrl_parse's own
   footprint contract takes the same premise. *)
Definition rng_fp_cls1 (RNG : ExecF.footprint) (m : word -> option byte) (TP FS : Z) : Prop :=
  ExecF.rng RNG FS 36864 /\ rng_ivls RNG (fp_w [1%nat] FS) /\
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k -> rng_ivls RNG (fp_tls TP DT TS C T DB k)).

Definition reac_ctrl_classify_box_frame_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
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
    (* asan *)
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
    (* the regions the run reads or writes *)
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) / 8 * 8)
      (shadow_addr (S - 1) / 8 * 8 + 8 - shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) / 8 * 8) ->
    ExecF.rng RNG o 36 ->
    ExecF.rng RNG (shadow_addr o / 8 * 8) (shadow_addr (o + 36 - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8) ->
    ExecF.rng RNG v 4 ->
    ExecF.rng RNG (shadow_addr v / 8 * 8) (shadow_addr (v + 4 - 1) / 8 * 8 + 8 - shadow_addr v / 8 * 8) ->
    (50 <= n -> ExecF.rng RNG f 50) ->
    (50 <= n -> ExecF.rng RNG (shadow_addr f / 8 * 8)
                  (shadow_addr (f + 50 - 1) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    (50 <= n -> ExecF.rng RNG u 6) ->
    (50 <= n -> ExecF.rng RNG (shadow_addr u / 8 * 8)
                  (shadow_addr (u + 6 - 1) / 8 * 8 + 8 - shadow_addr u / 8 * 8)) ->
    ExecF.rng RNG (shadow_addr REAC_CTRL_PARSE_BC / 8 * 8)
      (shadow_addr (REAC_CTRL_PARSE_BC + 6 - 1) / 8 * 8 + 8 - shadow_addr REAC_CTRL_PARSE_BC / 8 * 8) ->
    rng_fp_cls1 RNG m (bv_unsigned tp) FS ->
    ExecF.evtF rsegs RNG
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

(* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; form of a Theorem Labs lane 09:38Z): reac_ctrl_classify_box_frame_contract_on and
   reac_ctrl_classify_box_frame_contract_F_on, the two statements above with TWO changes each:
     - the premise `shadow_rw m` becomes `shadow_rw_on (reac_ctrl_classify_box_frame_shadow_R S FS f n u o v) m`;
     - the post's `shadow_rw m'` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P m'`: every shadow region the
       caller holds before the call it holds after the call.
   reac_ctrl_classify_box_frame_shadow_R is the shadow part of the footprint the _F statement above names, as 8-aligned
   shadow-word covers (sh_word_on, a Theorem Labs lane's lib/A/Prog/sh_word_on.v): the window [S - K, S), which holds
   reac_ctrl_parse's real-stack frame and its 16 shadow bytes; the shadow of the side stack's class-1 block
   [shadow_addr (fs_frame FS 1 0), + 131072), which holds reac_ctrl_parse's class-1 frame's 16 shadow bytes and
   __asan_stack_malloc_1's stores (a Theorem Labs lane 10:57Z, side-stack-shadow.md (a working note, not in this delivery): the class-c block is asan_stack_malloc's
   R; the side-stack header's shadow is not in R); the 36 bytes at o and the 4 bytes at v; when 50 <= n the 50 bytes
   at f and the 6 bytes at u;
   and the 6 bytes at REAC_CTRL_PARSE_BC.  The callees' regions at their calls are inside it: reac_ctrl_parse's
   reac_ctrl_parse_shadow_R f n o (S - 64) FS (a Theorem Labs lane, lib/A/Prog/reac_ctrl_parse_c.v: its frame's 16 shadow bytes
   in the window, __asan_stack_malloc_1's region, which under a Theorem Labs lane's 10:57Z decision is the class-1 block, and
   the covers of o, f and BC), the bcmp wrapper's bcmp_wrap_shadow_R (o + 4) u 6 and (o + 10) u 6 (the covers of o
   and u; the calls run only when 50 <= n); reac_ctrl_checksum_verify's _on contract (a Theorem Labs lane) has no shadow
   premise.  No other shadow byte is read or written by the run.
   These are STATEMENTS here: reac_ctrl_classify_box_frame_contract_on is proved when the classify run narrows (cal /
   pro, route (C) L2), which takes the callees' _on contracts; until then cite it only as a hypothesis, as the old
   contract is cited.  The old statements follow (reac_ctrl_classify_box_frame_contract_of_on,
   reac_ctrl_classify_box_frame_contract_F_of_F_on). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import sh_word_on asan_stack_malloc_c_on.

Definition reac_ctrl_classify_box_frame_shadow_R (S FS f n u o v : Z) (a : Z) : Prop :=
  sh_word_on (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K a \/
  asan_stack_malloc_shadow_R FS 1%nat a \/
  sh_word_on o 36 a \/ sh_word_on v 4 a \/
  (50 <= n /\ sh_word_on f 50 a) \/ (50 <= n /\ sh_word_on u 6 a) \/
  sh_word_on REAC_CTRL_PARSE_BC 6 a.

Definition reac_ctrl_classify_box_frame_contract_on : Prop :=
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
    (* asan *)
    asan_cells m -> shadow_rw_on (reac_ctrl_classify_box_frame_shadow_R S FS f n u o v) m ->
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
         asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_CLASSIFY_BOX_FRAME) fc None m (seg_rom rsegs)).

(* The old statement: the universal shadow_rw gives the region (shadow_rw_on_of_shadow_rw), and the post's region
   transport at P := fun _ => True gives the universal post back (shadow_rw_of_on_all). *)
Lemma reac_ctrl_classify_box_frame_contract_of_on :
  reac_ctrl_classify_box_frame_contract_on -> reac_ctrl_classify_box_frame_contract.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f
    n u o v S FS fr us junk vb H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22
    H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 SW H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49 H50
    H51 H52 H53.
  eapply evt_mono.
  - exact (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           f n u o v S FS fr us junk vb H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20
           H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 (shadow_rw_on_of_shadow_rw _ m SW) H37 H38
           H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49 H50 H51 H52 H53).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                Ems & MU & WM & MI' & ST' & RO & RV & AC' & SW' & Rest).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj Ems (conj MU (conj WM (conj MI' (conj ST' (conj RO (conj RV (conj AC' (conj _ Rest))))))))).
    exact (shadow_rw_of_on_all m' (SW' (fun _ => True) (shadow_rw_on_of_shadow_rw _ m SW))).
Qed.

Definition reac_ctrl_classify_box_frame_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
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
    (* asan *)
    asan_cells m -> shadow_rw_on (reac_ctrl_classify_box_frame_shadow_R S FS f n u o v) m ->
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
    (* the regions the run reads or writes *)
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) / 8 * 8)
      (shadow_addr (S - 1) / 8 * 8 + 8 - shadow_addr (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) / 8 * 8) ->
    ExecF.rng RNG o 36 ->
    ExecF.rng RNG (shadow_addr o / 8 * 8) (shadow_addr (o + 36 - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8) ->
    ExecF.rng RNG v 4 ->
    ExecF.rng RNG (shadow_addr v / 8 * 8) (shadow_addr (v + 4 - 1) / 8 * 8 + 8 - shadow_addr v / 8 * 8) ->
    (50 <= n -> ExecF.rng RNG f 50) ->
    (50 <= n -> ExecF.rng RNG (shadow_addr f / 8 * 8)
                  (shadow_addr (f + 50 - 1) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    (50 <= n -> ExecF.rng RNG u 6) ->
    (50 <= n -> ExecF.rng RNG (shadow_addr u / 8 * 8)
                  (shadow_addr (u + 6 - 1) / 8 * 8 + 8 - shadow_addr u / 8 * 8)) ->
    ExecF.rng RNG (shadow_addr REAC_CTRL_PARSE_BC / 8 * 8)
      (shadow_addr (REAC_CTRL_PARSE_BC + 6 - 1) / 8 * 8 + 8 - shadow_addr REAC_CTRL_PARSE_BC / 8 * 8) ->
    rng_fp_cls1 RNG m (bv_unsigned tp) FS ->
    ExecF.evtF rsegs RNG
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
         asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) REAC_CTRL_CLASSIFY_BOX_FRAME_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S
           (reac_ctrl_classify_box_frame_W o v S) (reac_ctrl_classify_box_frame_D f n u o v) /\
         reac_ctrl_classify_box_frame_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_CLASSIFY_BOX_FRAME_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_CLASSIFY_BOX_FRAME) fc None m (seg_rom rsegs)).

Lemma reac_ctrl_classify_box_frame_contract_F_of_F_on :
  reac_ctrl_classify_box_frame_contract_F_on -> reac_ctrl_classify_box_frame_contract_F.
Proof.
  intros H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
    m f n u o v S FS fr us junk vb H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21
    H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 SW H37 H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49
    H50 H51 H52 H53 R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13.
  eapply ExecF.evtF_mono.
  - exact (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F
           fc m f n u o v S FS fr us junk vb H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19
           H20 H21 H22 H23 H24 H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 (shadow_rw_on_of_shadow_rw _ m SW) H37
           H38 H39 H40 H41 H42 H43 H44 H45 H46 H47 H48 H49 H50 H51 H52 H53 R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11
           R12 R13).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                Ems & MU & WM & MI' & ST' & RO & RV & AC' & SW' & Rest).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj Ems (conj MU (conj WM (conj MI' (conj ST' (conj RO (conj RV (conj AC' (conj _ Rest))))))))).
    exact (shadow_rw_of_on_all m' (SW' (fun _ => True) (shadow_rw_on_of_shadow_rw _ m SW))).
Qed.

Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_contract_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_contract_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_contract_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_contract_F_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_contract_of_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_contract_of_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_contract_F_of_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_contract_F_of_F_on.
