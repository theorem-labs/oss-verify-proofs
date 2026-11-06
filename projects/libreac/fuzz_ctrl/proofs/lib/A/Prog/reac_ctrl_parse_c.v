From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c RcAsanFP.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_CTRL_PARSE : Z := 0x83578.
(* K = 4240 + max(K of __asan_stack_malloc_1 208, __asan_memset 2208, __asan_memcpy 2224, the bcmp wrapper 4560,
   kind_of_link1 0): contracts/libreac/reac_ctrl_parse.md Names. *)
Definition REAC_CTRL_PARSE_K : Z := 8800.
(* BC: the 6 bytes ff at .str.4 that the bcmp wrapper compares with. *)
Definition REAC_CTRL_PARSE_BC : Z := 0x21200.

Definition reac_ctrl_parse_fp (o S : Z) : list (Z * Z) :=
  (if o =? 0 then [] else [(o, o + 36)]) ++ [(S - REAC_CTRL_PARSE_K, S)].

(* The writes outside the side stack (fp's W) and the data ranges (fp's D). *)
Definition reac_ctrl_parse_W (o S : Z) : list ivl :=
  (S - REAC_CTRL_PARSE_K, S) :: (if o =? 0 then [] else [(o, o + 36)]).
Definition reac_ctrl_parse_D (f n o : Z) : list ivl :=
  (if n <? 50 then [] else [(f, f + 50)]) ++ (if o =? 0 then [] else [(o, o + 36)]).

(* The thread cells that fp names are apart from the class-1 side-stack bytes (struct.asan.runtime RT4.3) and from
   the shadow of the function's own window [lo, hi): the function's own frame on the side stack or on the real stack
   keeps them. *)
Definition reac_ctrl_parse_tls (m : word -> option byte) (TP FS lo hi : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    fp_dj (fp_tls TP DT TS C T DB k) (fp_w [1%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]).

(* The plain contract (lib/Prog/reac_ctrl_parse_c.v) with K = 8800 and the premises of the asan build (S1.6, S1.7
   of the English contract): the runtime's cells and shadow (asan_cells, shadow_rw), the window in AppMem and
   addressable, the addressable bytes at f, o and BC, o apart from the runtime's cells, the cells the bcmp wrapper
   reads, and the side-stack state for __asan_stack_malloc_1 (fp [1%nat], with reac_ctrl_parse_tls). The run may
   also write the class-1 side-stack bytes (fp_w [1%nat] FS) and the shadow of its window. *)
Definition reac_ctrl_parse_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 o -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> stk rsegs m (S - REAC_CTRL_PARSE_K) S ->
    mem_inv rsegs m ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i) ->
    (o <> 0 ->
       o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\
         (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
           (reac_ctrl_parse_D f n o) /\
         (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat -> bytes_at rsegs m (fs_flag FS 1%nat 0) fl ->
            bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
         reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).

(* The free-frame variant of the contract (P9): a list X of class-1 frames held in use at entry is excluded from
   the write footprint, so a caller learns that those frames' bytes and shadow survive the call. Versus
   reac_ctrl_parse_contract: X is the leading universal, X's frames are class-1 and flag-1 at entry, the side-stack
   precondition and the munch write set use the free-frame footprint (fpx / fp_wx [1%nat] FS X), and the post adds
   that X's flags are still 1 and that fpx holds at m'. *)
Definition reac_ctrl_parse_contract_x : Prop :=
  forall (X : list (nat * Z))
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte),
    Forall (fun ci => fst ci = 1%nat /\ 0 <= snd ci < fs_M 1 /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X ->
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 o -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> stk rsegs m (S - REAC_CTRL_PARSE_K) S ->
    mem_inv rsegs m ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i) ->
    (o <> 0 ->
       o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fpx [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
      (reac_ctrl_parse_D f n o) X ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\
         (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fpx [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
           (reac_ctrl_parse_D f n o) X /\
         Forall (fun ci => bytes_at rsegs m' (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X /\
         (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat -> bytes_at rsegs m (fs_flag FS 1%nat 0) fl ->
            bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
         reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).

(* The free-frame contract instantiated at X = [] is the plain contract (fp_wx [] = fp_w, fpx [] = fp, the added
   premise and post over [] are trivial). *)
Lemma reac_ctrl_parse_contract_x_nil : reac_ctrl_parse_contract_x -> reac_ctrl_parse_contract.
Proof.
  intros HX. unfold reac_ctrl_parse_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  eapply evt_mono.
  - apply (HX [] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5
      t6 F fc m f n o S FS fr junk);
      first [ assumption | apply Forall_nil | exact Hfp ].
  - intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      Heq & Hmunch & Hwm & Hmi' & Hstk' & Hrw & Hac' & Hsw' & Haddr' & Hfp' & Hflag' & Hkept & Htls').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact Heq|]. split; [exact Hmunch|]. split; [exact Hwm|]. split; [exact Hmi'|].
    split; [exact Hstk'|]. split; [exact Hrw|]. split; [exact Hac'|]. split; [exact Hsw'|].
    split; [exact Haddr'|]. split; [exact Hfp'|]. split; [exact Hkept|]. exact Htls'.
Qed.

(* ---- The footprint form of the free-frame contract (RECIPE.md step 1 (a working note, not in this delivery)): the same run, from the same
   start state and with the same post as reac_ctrl_parse_contract_x, as an ExecF.evtF under a footprint RNG (the first
   binder), with one rng premise per region the run touches, each guarded as the plain contract guards that region.
   The regions: the image [IMG_LO, IMG_LO + IMG_LEN) (every instruction fetch, every literal .rodata load, the
   runtime's cells, the GOT words, CF and the static thread cells); the window [S - K, S) and its shadow; the 50 bytes
   at f (50 <= n) and the 36 bytes at o (o <> 0), each with its shadow; the 6 bytes at BC and their shadow; the side
   stack's header [FS, fs_frame FS 0 0) and the class-1 bytes fp_w [1%nat] FS (hint, flags, frames, their shadow);
   the dynamic thread cells fp_tls of asan_tls_cells. rng_bytes (lib/Lib/RngBytes.v): RNG is decided byte by byte.
   reac_ctrl_parse_contract_x_of_F gives reac_ctrl_parse_contract_x back at ExecF.RNG_all. ---- *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF RngBytes.

(* The image: [IMG_LO, IMG_HI) of lib/A/Prog/ImgBounds.v, the page-rounded span of the PT_LOAD segments of rsegs
   (lib/A/Img0.v; lib/AZ/AsanW/AImg.v a_seg_flags: [0x10000, 0x30000) [0x30000, 0x9e000) [0x9e000, 0xa1000)
   [0xa1000, 0x5fe000)), and its length IMG_LEN as lib/A/Prog/rng_asan.v writes it. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Export ImgBounds.
Notation IMG_LEN := (IMG_HI - IMG_LO).

(* The shadow of [p, p + n) as whole aligned 8-byte shadow words (the instrumented checks and the runtime load
   aligned shadow words, never the exact shadow byte): [sh_lo p, sh_lo p + sh_len p n). *)
Definition sh_lo (p : Z) : Z := (p / 8 + ASAN_K) / 8 * 8.
Definition sh_len (p n : Z) : Z := ((p + n - 1) / 8 + ASAN_K) / 8 * 8 + 8 - sh_lo p.

Definition reac_ctrl_parse_contract_x_F : Prop :=
  forall (RNG : ExecF.footprint) (X : list (nat * Z))
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte),
    Forall (fun ci => fst ci = 1%nat /\ 0 <= snd ci < fs_M 1 /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X ->
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 o -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> stk rsegs m (S - REAC_CTRL_PARSE_K) S ->
    mem_inv rsegs m ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i) ->
    (o <> 0 ->
       o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fpx [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
      (reac_ctrl_parse_D f n o) X ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= n -> ExecF.rng RNG f 50) ->
    (50 <= n -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    (o <> 0 -> ExecF.rng RNG o 36) ->
    (o <> 0 -> ExecF.rng RNG (sh_lo o) (sh_len o 36)) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\
         (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fpx [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
           (reac_ctrl_parse_D f n o) X /\
         Forall (fun ci => bytes_at rsegs m' (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X /\
         (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat -> bytes_at rsegs m (fs_flag FS 1%nat 0) fl ->
            bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
         reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).

(* The _F statement at the footprint that admits every access is the old statement: each rng premise by rng_all
   from the bounds the old premises carry (the window, f, o and FS bounds; fs_place; the bytes_at bounds of the cells
   of asan_tls_cells), so the _F statement asks for nothing new. *)
Lemma reac_ctrl_parse_contract_x_of_F : reac_ctrl_parse_contract_x_F -> reac_ctrl_parse_contract_x.
Proof.
  unfold reac_ctrl_parse_contract_x_F, reac_ctrl_parse_contract_x. intros HF.
  intros X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros HX Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  pose proof (eq_refl : REAC_CTRL_PARSE_K = 8800) as HK.
  pose proof Hfp as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EF : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EH : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m f n o S FS fr junk); try assumption.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f *) intros H50. destruct (Hn50 H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hn50 H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* o *) intros Ho0. destruct (Ho36 Ho0) as (_ & Ho1 & _). apply ExecF.rng_all; lia.
  - intros Ho0. destruct (Ho36 Ho0) as (_ & Ho1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* BC *) apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0; lia.
  - (* class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* dynamic thread cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

(* ---- The footprint form of the PLAIN contract: the same run, from the same start state and with the same post as
   reac_ctrl_parse_contract, as an ExecF.evtF under a footprint RNG (the first binder). Its footprint premises are the
   X = [] instance of reac_ctrl_parse_contract_x_F's (none of them mentions X): rng_bytes, the image, the window and
   its shadow [shadow_addr (S - K), shadow_addr S), f and its shadow under 50 <= n, o and its shadow under o <> 0, BC
   and its shadow, the side-stack header, the class-1 side-stack bytes fp_w [1%nat] FS, and the cells of
   asan_tls_cells.
   reac_ctrl_parse_contract_F_of_x_F is the twin of reac_ctrl_parse_contract_x_nil (fpx [] = fp, fp_wx [] = fp_w, the
   X premise and the X-only post conjunct over [] are trivial); reac_ctrl_parse_contract_of_F gives
   reac_ctrl_parse_contract back at ExecF.RNG_all. ---- *)
Definition reac_ctrl_parse_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 o -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> stk rsegs m (S - REAC_CTRL_PARSE_K) S ->
    mem_inv rsegs m ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i) ->
    (o <> 0 ->
       o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= n -> ExecF.rng RNG f 50) ->
    (50 <= n -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    (o <> 0 -> ExecF.rng RNG o 36) ->
    (o <> 0 -> ExecF.rng RNG (sh_lo o) (sh_len o 36)) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\
         (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
         asan_cells m' /\ shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
           (reac_ctrl_parse_D f n o) /\
         (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat -> bytes_at rsegs m (fs_flag FS 1%nat 0) fl ->
            bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
         reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).

(* The free-frame footprint form at X = [] is the plain footprint form: the footprint premises are the same, the
   X premise is Forall_nil, fpx [1%nat] ... [] is fp [1%nat] ... and fp_wx [1%nat] FS [] is fp_w [1%nat] FS by
   the [] branch of fp_wx (lib/A/Prog/RcAsanFP.v, fpx_nil, fp_wx_nil), and the X-only post conjunct over [] is
   dropped. *)
Lemma reac_ctrl_parse_contract_F_of_x_F : reac_ctrl_parse_contract_x_F -> reac_ctrl_parse_contract_F.
Proof.
  intros HX. unfold reac_ctrl_parse_contract_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  intros Hrbt Himg Hwin Hwins Hfrng Hfrngs Horng Horngs Hbcr Hbcs Hhdr Hfw Htlsr.
  eapply ExecF.evtF_mono.
  - apply (HX RNG [] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5
      t6 F fc m f n o S FS fr junk);
      first [ assumption | apply Forall_nil | exact Hfp ].
  - intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      Heq & Hmunch & Hwm & Hmi' & Hstk' & Hrw & Hac' & Hsw' & Haddr' & Hfp' & Hflag' & Hkept & Htls').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact Heq|]. split; [exact Hmunch|]. split; [exact Hwm|]. split; [exact Hmi'|].
    split; [exact Hstk'|]. split; [exact Hrw|]. split; [exact Hac'|]. split; [exact Hsw'|].
    split; [exact Haddr'|]. split; [exact Hfp'|]. split; [exact Hkept|]. exact Htls'.
Qed.

(* The plain _F statement at the footprint that admits every access is the plain contract: each rng premise by
   rng_all from the bounds the plain premises carry (the window, f, o and FS bounds; fs_place; the bytes_at bounds
   of the cells of asan_tls_cells), so the _F statement asks for nothing new. *)
Lemma reac_ctrl_parse_contract_of_F : reac_ctrl_parse_contract_F -> reac_ctrl_parse_contract.
Proof.
  unfold reac_ctrl_parse_contract_F, reac_ctrl_parse_contract. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  pose proof (eq_refl : REAC_CTRL_PARSE_K = 8800) as HK.
  pose proof Hfp as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EF : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EH : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
           t5 t6 F fc m f n o S FS fr junk); try assumption.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f *) intros H50. destruct (Hn50 H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hn50 H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* o *) intros Ho0. destruct (Ho36 Ho0) as (_ & Ho1 & _). apply ExecF.rng_all; lia.
  - intros Ho0. destruct (Ho36 Ho0) as (_ & Ho1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* BC *) apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0; lia.
  - (* class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* dynamic thread cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

(* ==== Route (C) (a Theorem Labs lane 09:20Z; form of record lib/A/ShadowRwOn.v, a working branch ea8776b2302; wave lead
   a Theorem Labs lane, ASSIGN.md (a working note, not in this delivery)): the four contracts above with the universal premise `shadow_rw m` narrowed
   to `shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m` and the post's `shadow_rw m'` stated as
   `forall P, shadow_rw_on P m -> shadow_rw_on P m'`. The four Definitions above stay byte-identical; the run lemmas
   that take callee contracts (reac_ctrl_parse.v (not in this delivery), reac_ctrl_parseF.v) prove the `_on` forms from the callees' `_on`
   contracts (a Theorem Labs lane 09:58Z ruling). Each `_on` Definition below is its old Definition with exactly those two
   changes. rule 24: proof-index reac_ctrl_parse (2026-10-29 00:3xZ, exit 0): 12 named files + 8 lemma rows,
   plain / ubsan builds of fuzz_disco / fuzz_grant / fuzz_scene; checker a Theorem Labs lane:
   CONFIRM. At ossv/recipes c5e779efe8c (2026-10-31), released ASan proofs of reac_ctrl_parse exist in fuzz_grant, fuzz_disco and fuzz_scene. This restates ctrl's own image-A parse contracts; no function is proved in this file. ==== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import sh_word_on asan_stack_malloc_c_on.

(* The shadow bytes the run reaches through shadow_rw: every shadow byte it stores to, and every shadow byte a callee's
   `_on` contract names at its call (a callee's region through the callee's own predicate where that predicate is in
   this contract's binders: asan_stack_malloc_shadow_R FS 1). Read off the v1.9.0 image-A listing of reac_ctrl_parse
   (0x83578, 2464 bytes) and the run reac_ctrl_parse.v; fr is the frame (s8), s7 = (fr >> 3) + s9 = shadow_addr fr
   (s9 = ASAN_K, loaded from CELL_K at 0x835d8), A = (S - 128) / 32 * 32 (0x83578 addi sp,sp,-128; 0x835b4 andi
   sp,sp,-32).
   - the real-stack frame fr = A - 128 (0x83600 addi a0,sp,-128; 0x83604 andi s8,a0,-32; used when
     __asan_stack_malloc_1 is not called or returns 0): its 16 shadow bytes [shadow_addr fr, shadow_addr fr + 16),
     stored by the poisoning 0x83658 .. 0x83698 (sixteen sb to 0(s7) .. 15(s7)), the box redzone 0x83924 .. 0x83934
     (sb 0xf8 to 4(s7) .. 8(s7)) and the release 0x83998 .. 0x839d4 (sixteen sb zero); the run takes their wview
     from shadow_rw (reac_ctrl_parse.v fk_facts, shadow16_stk);
   - the class-1 block shadow [shadow_addr (fs_frame FS 1 0), + 131072) = asan_stack_malloc_shadow_R FS 1: the call
     0x835e8 jal __asan_stack_malloc_1(128) (its `_on` premise; it writes the shadow of the class-1 frame it chooses),
     and the side-stack frame fr = fs_frame FS 1 j (0 <= j < 8192) it returns: the same poisoning, the box redzone and
     the release 0x8394c .. 0x83988 (sixteen sb 0xf5) all store to [shadow_addr fr, shadow_addr fr + 16)
     = shadow_addr (fs_frame FS 1 0) + 16 j + [0, 16), inside it (no side-stack header shadow byte is touched);
   - o <> 0: the aligned shadow words of the 36 bytes at o, sh_word_on o 36: 0x836b4 jal __asan_memset(o, 0, 36)
     (the words of [o, o + 36)), 0x83718 jal __asan_memcpy(o + 10, f, 6) and 0x83728 jal __asan_memcpy(o + 4, f + 6, 6)
     (the destination words, asan_memcpy_shadow_R); with o = 0 the box is fr + 32 and these words lie in the frame's
     16 shadow bytes above (fr mod 32 = 0);
   - 50 <= n: the aligned shadow words of the 50 bytes at f, sh_word_on f 50: the memcpy sources at 0x83718 (f, 6) and
     0x83728 (f + 6, 6), and 0x8373c jal bcmp wrapper (f, BC, 6) (bcmp_wrap_shadow_R f BC 6, its left operand); the
     memcpy and bcmp calls sit after 0x836bc bltu s6,a0 (n < 50 skips them);
   - 50 <= n: the aligned shadow words of the 6 bytes at BC, sh_word_on REAC_CTRL_PARSE_BC 6: the bcmp wrapper's right
     operand (0x8372c auipc a0 / 0x83730 addi a1,a0,-0x52c: a1 = 0x21200 = BC).
   The shadow loads of the instrumented checks (the lb before each checked load and store, from 0x836cc on: shadow_addr
   of f + 12 .. f + 22 and f + 32 .. f + 38, and of the box's cells) lie inside these regions; their bytes come from the
   addressable premises and the frame's own shadow stores, not from shadow_rw.
   Reads and stores checked (listing 0x83578 .. 0x83f18): parse's only shadow stores are the sb to 0(s7) .. 15(s7) at
   0x83658 .. 0x83698, 0x83924 .. 0x83934, 0x8394c .. 0x83988 and 0x83998 .. 0x839d4, all in [shadow_addr fr,
   shadow_addr fr + 16); its other stores (the box, the frame words, the stack slots, the flag byte at 0x83990 in the
   side-stack header) are not shadow addresses. *)
Definition reac_ctrl_parse_shadow_R (f n o S FS : Z) (a : Z) : Prop :=
  (shadow_addr ((S - 128) / 32 * 32 - 128) <= a < shadow_addr ((S - 128) / 32 * 32 - 128) + 16) \/
  asan_stack_malloc_shadow_R FS 1%nat a \/
  (o <> 0 /\ sh_word_on o 36 a) \/
  (50 <= n /\ sh_word_on f 50 a) \/
  (50 <= n /\ sh_word_on REAC_CTRL_PARSE_BC 6 a).

(* reac_ctrl_parse_contract with the narrowed shadow premise and post. *)
Definition reac_ctrl_parse_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 o -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> stk rsegs m (S - REAC_CTRL_PARSE_K) S ->
    mem_inv rsegs m ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i) ->
    (o <> 0 ->
       o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    (* asan *)
    asan_cells m -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\
         (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
         asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
           (reac_ctrl_parse_D f n o) /\
         (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat -> bytes_at rsegs m (fs_flag FS 1%nat 0) fl ->
            bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
         reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).

(* reac_ctrl_parse_contract_x with the narrowed shadow premise and post (the same run, so the same R). *)
Definition reac_ctrl_parse_contract_x_on : Prop :=
  forall (X : list (nat * Z))
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte),
    Forall (fun ci => fst ci = 1%nat /\ 0 <= snd ci < fs_M 1 /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X ->
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 o -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> stk rsegs m (S - REAC_CTRL_PARSE_K) S ->
    mem_inv rsegs m ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i) ->
    (o <> 0 ->
       o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    (* asan *)
    asan_cells m -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fpx [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
      (reac_ctrl_parse_D f n o) X ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\
         (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
         asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fpx [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
           (reac_ctrl_parse_D f n o) X /\
         Forall (fun ci => bytes_at rsegs m' (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X /\
         (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat -> bytes_at rsegs m (fs_flag FS 1%nat 0) fl ->
            bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
         reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).

(* reac_ctrl_parse_contract_x_F with the narrowed shadow premise and post (the footprint premises unchanged). *)
Definition reac_ctrl_parse_contract_x_F_on : Prop :=
  forall (RNG : ExecF.footprint) (X : list (nat * Z))
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte),
    Forall (fun ci => fst ci = 1%nat /\ 0 <= snd ci < fs_M 1 /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X ->
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 o -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> stk rsegs m (S - REAC_CTRL_PARSE_K) S ->
    mem_inv rsegs m ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i) ->
    (o <> 0 ->
       o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    (* asan *)
    asan_cells m -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fpx [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
      (reac_ctrl_parse_D f n o) X ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= n -> ExecF.rng RNG f 50) ->
    (50 <= n -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    (o <> 0 -> ExecF.rng RNG o 36) ->
    (o <> 0 -> ExecF.rng RNG (sh_lo o) (sh_len o 36)) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\
         (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
         asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fpx [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
           (reac_ctrl_parse_D f n o) X /\
         Forall (fun ci => bytes_at rsegs m' (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X /\
         (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat -> bytes_at rsegs m (fs_flag FS 1%nat 0) fl ->
            bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
         reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).

(* reac_ctrl_parse_contract_F with the narrowed shadow premise and post (the footprint premises unchanged). *)
Definition reac_ctrl_parse_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 o -> sp = Z_to_bv 64 S ->
    0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> S < 2^64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> stk rsegs m (S - REAC_CTRL_PARSE_K) S ->
    mem_inv rsegs m ->
    length fr = 50%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i) ->
    (o <> 0 ->
       o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)) ->
    (* asan *)
    asan_cells m -> shadow_rw_on (reac_ctrl_parse_shadow_R f n o S FS) m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= n -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    (* footprint *)
    rng_bytes RNG ->
    ExecF.rng RNG IMG_LO IMG_LEN ->
    ExecF.rng RNG (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    ExecF.rng RNG (shadow_addr (S - REAC_CTRL_PARSE_K)) (shadow_addr S - shadow_addr (S - REAC_CTRL_PARSE_K)) ->
    (50 <= n -> ExecF.rng RNG f 50) ->
    (50 <= n -> ExecF.rng RNG (sh_lo f) (sh_len f 50)) ->
    (o <> 0 -> ExecF.rng RNG o 36) ->
    (o <> 0 -> ExecF.rng RNG (sh_lo o) (sh_len o 36)) ->
    ExecF.rng RNG REAC_CTRL_PARSE_BC 6 ->
    ExecF.rng RNG (sh_lo REAC_CTRL_PARSE_BC) (sh_len REAC_CTRL_PARSE_BC 6) ->
    ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
    Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
    (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
       Forall (fun iv => ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\
         (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
         asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\
         addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
           (reac_ctrl_parse_D f n o) /\
         (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat -> bytes_at rsegs m (fs_flag FS 1%nat 0) fl ->
            bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
         reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).

(* The `_on` twins of the four relations above, each the old proof with the `_on` names (the narrowed premise and
   post pass through unchanged). *)
Lemma reac_ctrl_parse_contract_x_on_nil : reac_ctrl_parse_contract_x_on -> reac_ctrl_parse_contract_on.
Proof.
  intros HX. unfold reac_ctrl_parse_contract_on.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  eapply evt_mono.
  - apply (HX [] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5
      t6 F fc m f n o S FS fr junk);
      first [ assumption | apply Forall_nil | exact Hfp ].
  - intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      Heq & Hmunch & Hwm & Hmi' & Hstk' & Hrw & Hac' & Hsw' & Haddr' & Hfp' & Hflag' & Hkept & Htls').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact Heq|]. split; [exact Hmunch|]. split; [exact Hwm|]. split; [exact Hmi'|].
    split; [exact Hstk'|]. split; [exact Hrw|]. split; [exact Hac'|]. split; [exact Hsw'|].
    split; [exact Haddr'|]. split; [exact Hfp'|]. split; [exact Hkept|]. exact Htls'.
Qed.

Lemma reac_ctrl_parse_contract_x_on_of_F_on : reac_ctrl_parse_contract_x_F_on -> reac_ctrl_parse_contract_x_on.
Proof.
  unfold reac_ctrl_parse_contract_x_F_on, reac_ctrl_parse_contract_x_on. intros HF.
  intros X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros HX Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  pose proof (eq_refl : REAC_CTRL_PARSE_K = 8800) as HK.
  pose proof Hfp as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EF : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EH : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m f n o S FS fr junk); try assumption.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f *) intros H50. destruct (Hn50 H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hn50 H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* o *) intros Ho0. destruct (Ho36 Ho0) as (_ & Ho1 & _). apply ExecF.rng_all; lia.
  - intros Ho0. destruct (Ho36 Ho0) as (_ & Ho1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* BC *) apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0; lia.
  - (* class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* dynamic thread cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

Lemma reac_ctrl_parse_contract_F_on_of_x_F_on : reac_ctrl_parse_contract_x_F_on -> reac_ctrl_parse_contract_F_on.
Proof.
  intros HX. unfold reac_ctrl_parse_contract_F_on.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  intros Hrbt Himg Hwin Hwins Hfrng Hfrngs Horng Horngs Hbcr Hbcs Hhdr Hfw Htlsr.
  eapply ExecF.evtF_mono.
  - apply (HX RNG [] ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5
      t6 F fc m f n o S FS fr junk);
      first [ assumption | apply Forall_nil | exact Hfp ].
  - intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      Heq & Hmunch & Hwm & Hmi' & Hstk' & Hrw & Hac' & Hsw' & Haddr' & Hfp' & Hflag' & Hkept & Htls').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact Heq|]. split; [exact Hmunch|]. split; [exact Hwm|]. split; [exact Hmi'|].
    split; [exact Hstk'|]. split; [exact Hrw|]. split; [exact Hac'|]. split; [exact Hsw'|].
    split; [exact Haddr'|]. split; [exact Hfp'|]. split; [exact Hkept|]. exact Htls'.
Qed.

Lemma reac_ctrl_parse_contract_on_of_F_on : reac_ctrl_parse_contract_F_on -> reac_ctrl_parse_contract_on.
Proof.
  unfold reac_ctrl_parse_contract_F_on, reac_ctrl_parse_contract_on. intros HF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  pose proof (eq_refl : REAC_CTRL_PARSE_K = 8800) as HK.
  pose proof Hfp as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & _ & (HFS0 & _) & _ & _ & _ & HFSl & _).
  unfold FS_SIZE in HFSl.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : forall j, fs_frame FS 1 j = FS + 1085440 + j * 128)
    by (intros j; unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  assert (EF : fs_flag FS 1 0 = FS + 20480)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 1)) with 16384; lia).
  assert (EH : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4
           t5 t6 F fc m f n o S FS fr junk); try assumption.
  - (* rng_bytes *) intros b j _ _ _. exact I.
  - (* image *) apply ExecF.rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* window *) apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* f *) intros H50. destruct (Hn50 H50) as (Hf0 & Hf1 & _). apply ExecF.rng_all; lia.
  - intros H50. destruct (Hn50 H50) as (Hf0 & Hf1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* o *) intros Ho0. destruct (Ho36 Ho0) as (_ & Ho1 & _). apply ExecF.rng_all; lia.
  - intros Ho0. destruct (Ho36 Ho0) as (_ & Ho1 & _).
    apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K; Z.div_mod_to_equations; lia.
  - (* BC *) apply ExecF.rng_all; unfold REAC_CTRL_PARSE_BC; lia.
  - apply ExecF.rng_all; unfold sh_len, sh_lo, ASAN_K, REAC_CTRL_PARSE_BC; Z.div_mod_to_equations; lia.
  - (* side-stack header *) apply ExecF.rng_all; rewrite ?E0; lia.
  - (* class-1 side-stack bytes *)
    apply Forall_forall. intros iv Hiv. unfold fp_w, fp_w1 in Hiv. cbn [flat_map app In] in Hiv.
    destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; apply ExecF.rng_all;
      rewrite ?EM, ?E1, ?EF, ?EH; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
  - (* dynamic thread cells *)
    intros DT TS C T DB k Hc. apply Forall_forall. intros iv Hiv.
    destruct Hc as ((Hc1 & Hc1' & _) & (Hc2 & Hc2' & _) & (Hc3 & Hc3' & _) & (Hc4 & Hc4' & _) & (Hc5 & Hc5' & _) &
      _ & (Hc6 & Hc6' & _) & (Hc7 & Hc7' & _) & (Hc8 & Hc8' & _) & (Hc9 & Hc9' & _) &
      (tb & te & Hc10 & Hc10' & _) & (Hc11 & Hc11' & _) & (Hc12 & Hc12' & _) & (Hc13 & Hc13' & _) &
      (Hc14 & Hc14' & _) & (Hc15 & Hc15' & _) & (Hc16 & Hc16' & _) & _ & (Hc17 & Hc17' & _)).
    rewrite ?length_app, ?length_le8, ?length_le4 in *. cbn [length] in Hc5', Hc12'.
    cbn [fp_tls In] in Hiv.
    repeat (destruct Hiv as [<-|Hiv]; [cbn [fst snd]; apply ExecF.rng_all; lia|]).
    destruct Hiv.
Qed.

(* Each old contract from its `_on` form: the narrowed premise by shadow_rw_on_of_shadow_rw, the old post's shadow_rw m'
   by the `_on` post at P := fun _ => True and shadow_rw_of_on_all. *)
Lemma reac_ctrl_parse_contract_of_on : reac_ctrl_parse_contract_on -> reac_ctrl_parse_contract.
Proof.
  intros HO. unfold reac_ctrl_parse_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  eapply evt_mono.
  - apply (HO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc m f n o S FS fr junk);
      first [ assumption | exact (shadow_rw_on_of_shadow_rw _ m Hsw) ].
  - intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      Heq & Hmunch & Hwm & Hmi' & Hstk' & Hrw & Hac' & Hsw' & Haddr' & Hfp' & Hkept & Htls').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact Heq|]. split; [exact Hmunch|]. split; [exact Hwm|]. split; [exact Hmi'|].
    split; [exact Hstk'|]. split; [exact Hrw|]. split; [exact Hac'|].
    split; [exact (shadow_rw_of_on_all m' (Hsw' (fun _ => True) (shadow_rw_on_of_shadow_rw _ m Hsw)))|].
    split; [exact Haddr'|]. split; [exact Hfp'|]. split; [exact Hkept|]. exact Htls'.
Qed.

Lemma reac_ctrl_parse_contract_x_of_on : reac_ctrl_parse_contract_x_on -> reac_ctrl_parse_contract_x.
Proof.
  intros HO. unfold reac_ctrl_parse_contract_x.
  intros X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros HX Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  eapply evt_mono.
  - apply (HO X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc m f n o S FS fr junk);
      first [ assumption | exact (shadow_rw_on_of_shadow_rw _ m Hsw) ].
  - intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      Heq & Hmunch & Hwm & Hmi' & Hstk' & Hrw & Hac' & Hsw' & Haddr' & Hfp' & Hflag' & Hkept & Htls').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact Heq|]. split; [exact Hmunch|]. split; [exact Hwm|]. split; [exact Hmi'|].
    split; [exact Hstk'|]. split; [exact Hrw|]. split; [exact Hac'|].
    split; [exact (shadow_rw_of_on_all m' (Hsw' (fun _ => True) (shadow_rw_on_of_shadow_rw _ m Hsw)))|].
    split; [exact Haddr'|]. split; [exact Hfp'|]. split; [exact Hflag'|]. split; [exact Hkept|]. exact Htls'.
Qed.

Lemma reac_ctrl_parse_contract_x_F_of_on : reac_ctrl_parse_contract_x_F_on -> reac_ctrl_parse_contract_x_F.
Proof.
  intros HO. unfold reac_ctrl_parse_contract_x_F.
  intros RNG X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros HX Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  intros Hrbt Himg Hwin Hwins Hfrng Hfrngs Horng Horngs Hbcr Hbcs Hhdr Hfw Htlsr.
  eapply ExecF.evtF_mono.
  - apply (HO RNG X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc m f n o S FS fr junk);
      first [ assumption | exact (shadow_rw_on_of_shadow_rw _ m Hsw) ].
  - intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      Heq & Hmunch & Hwm & Hmi' & Hstk' & Hrw & Hac' & Hsw' & Haddr' & Hfp' & Hflag' & Hkept & Htls').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact Heq|]. split; [exact Hmunch|]. split; [exact Hwm|]. split; [exact Hmi'|].
    split; [exact Hstk'|]. split; [exact Hrw|]. split; [exact Hac'|].
    split; [exact (shadow_rw_of_on_all m' (Hsw' (fun _ => True) (shadow_rw_on_of_shadow_rw _ m Hsw)))|].
    split; [exact Haddr'|]. split; [exact Hfp'|]. split; [exact Hflag'|]. split; [exact Hkept|]. exact Htls'.
Qed.

Lemma reac_ctrl_parse_contract_F_of_on : reac_ctrl_parse_contract_F_on -> reac_ctrl_parse_contract_F.
Proof.
  intros HO. unfold reac_ctrl_parse_contract_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk.
  intros Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae Haddr Hfa Hoa Hbc
    Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls.
  intros Hrbt Himg Hwin Hwins Hfrng Hfrngs Horng Horngs Hbcr Hbcs Hhdr Hfw Htlsr.
  eapply ExecF.evtF_mono.
  - apply (HO RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      t3 t4 t5 t6 F fc m f n o S FS fr junk);
      first [ assumption | exact (shadow_rw_on_of_shadow_rw _ m Hsw) ].
  - intros ms' Hpost.
    destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
      Heq & Hmunch & Hwm & Hmi' & Hstk' & Hrw & Hac' & Hsw' & Haddr' & Hfp' & Hkept & Htls').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact Heq|]. split; [exact Hmunch|]. split; [exact Hwm|]. split; [exact Hmi'|].
    split; [exact Hstk'|]. split; [exact Hrw|]. split; [exact Hac'|].
    split; [exact (shadow_rw_of_on_all m' (Hsw' (fun _ => True) (shadow_rw_on_of_shadow_rw _ m Hsw)))|].
    split; [exact Haddr'|]. split; [exact Hfp'|]. split; [exact Hkept|]. exact Htls'.
Qed.
