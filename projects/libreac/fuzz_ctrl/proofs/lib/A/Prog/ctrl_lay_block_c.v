From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcBox RcSynth RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c RcAsanFP
  reac_box_model_block_c.
Import ListNotations.
Open Scope Z_scope.

Definition CTRL_LAY_BLOCK : Z := 0x855f4.
(* K = max(4240, 144 + K(__asan_stack_malloc_1) 208, 240 + max(K(__asan_memset) 2208, K(__asan_memcpy) 2224,
   K(reac_box_model_block) 4272)): contracts/libreac/ctrl_lay_block@reac_ctrlblk.md Names. The frame is 128 bytes,
   sp2 = S - 128 rounded down to 32; __asan_stack_malloc_1 runs at sp2; the probe writes 8 bytes at sp2 - 4096 >=
   S - 4240; the callees run at fr = sp2 - 96 >= S - 240 (real-stack ASan frame) or at sp2 (side-stack frame). *)
Definition CTRL_LAY_BLOCK_K : Z := 4512.

(* The writes outside the side stack (fp's W) and the data ranges (fp's D). *)
Definition ctrl_lay_block_W (p S : Z) : list ivl := [(S - CTRL_LAY_BLOCK_K, S); (p + 18, p + 50)].
Definition ctrl_lay_block_D (p f : Z) : list ivl := [(f, f + 24); (p + 18, p + 50)].

(* The thread cells that fp names are apart from the class-0 and class-1 side-stack bytes (struct.asan.runtime
   RT4.3) and from the shadow of the function's own window [lo, hi): the function's own class-1 frame,
   reac_box_model_block's class-0 frame and the real-stack frames keep them. *)
Definition ctrl_lay_block_tls (m : word -> option byte) (TP FS lo hi : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    fp_dj (fp_tls TP DT TS C T DB k) (fp_w [0%nat; 1%nat] FS ++ [(shadow_addr lo, shadow_addr hi)]).

(* The plain contract (lib/Prog/ctrl_lay_block_c.v) with K = 4512 and the premises of the asan build (S1.2, S1.7,
   S1.8 of the English contract): the runtime's cells and shadow (asan_cells, shadow_rw), the window in AppMem and
   addressable, the addressable bytes of the row, the block [p + 18, p + 50), tm, g, m and its name, and the JOIN
   block that reac_box_model_block copies for k = 5, 6; the ends in AppMem that __asan_memset and __asan_memcpy need;
   the block apart from the runtime's cells; and the side-stack state for __asan_stack_malloc_1 and
   reac_box_model_block's __asan_stack_malloc_0 (fp [0%nat; 1%nat], tm, g, m and the name apart from
   fp_w [0%nat; 1%nat] FS, ctrl_lay_block_tls). The run may also write the class-0 and class-1 side-stack bytes
   (fp_w [0%nat; 1%nat] FS) and the shadow of its window. *)
Definition ctrl_lay_block_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f md g FS : Z)
         (fr ob tb mb nb gb : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 md -> a3 = Z_to_bv 64 g ->
    0 <= p < 2^64 -> 0 <= f < 2^64 -> 0 <= md < 2^64 -> 0 <= g < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) ->
    ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (p + 18) (p + 50) ->
    ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) f (f + 24) ->
    (ly_k fr = 2 -> ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (ly_tm fr) (ly_tm fr + 32)) ->
    (g <> 0 -> ly_al fr <> 0 ->
       ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) g (g + ly_al fr)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) md (md + 296) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
    f mod 8 = 0 -> f + 24 <= 2^64 -> length fr = 24%nat -> bytes_at rsegs m f fr ->
    ly_k fr <= 9 -> ly_ao fr + ly_al fr <= 32 ->
    (ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm fr) tb) ->
    p <> 0 -> p + 50 <= 2^64 -> rw_cells rsegs m (p + 18) [CB 32 ob] ->
    ly_dj (p + 18) (p + 50) f (f + 24) ->
    (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          name_ok nb /\ bytes_at rsegs m (rname mb) nb)) ->
    (g <> 0 -> ly_al fr <> 0 ->
       Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - CTRL_LAY_BLOCK_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K ->
    addressable m f 24 ->
    addressable m (p + 18) 32 -> app_mem (p + 50) -> (p + 50 <= RT_LO \/ RT_HI <= p + 18) ->
    (ly_k fr = 2 -> addressable m (ly_tm fr) 32) ->
    (g <> 0 -> ly_al fr <> 0 ->
       addressable m g (ly_al fr) /\ app_mem (g + ly_al fr) /\ app_mem (g + 7) /\ app_mem (p + 25 + ly_ao fr)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       addressable m md 296 /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          addressable m (rname mb) (Z.of_nat (length nb)))) ->
    (ly_k fr = 5 -> addressable m JOIN_0014 32) ->
    (ly_k fr = 6 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp)
      (ctrl_lay_block_W p (bv_unsigned sp)) (ctrl_lay_block_D p f) ->
    (ly_k fr = 2 -> fp_dj [(ly_tm fr, ly_tm fr + 32)] (fp_w [0%nat; 1%nat] FS)) ->
    (g <> 0 -> ly_al fr <> 0 -> fp_dj [(g, g + ly_al fr)] (fp_w [0%nat; 1%nat] FS)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       fp_dj [(md, md + 296)] (fp_w [0%nat; 1%nat] FS) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS))) ->
    ctrl_lay_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(p + 18, p + 50); (bv_unsigned sp - CTRL_LAY_BLOCK_K, bv_unsigned sp)] ++
                fp_w [0%nat; 1%nat] FS ++
                [(shadow_addr (bv_unsigned sp - CTRL_LAY_BLOCK_K), shadow_addr (bv_unsigned sp))]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) /\
         rw_cells rsegs m' (p + 18)
           [CB 32 (ly_lay (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))) g (ly_ao fr) (ly_al fr) gb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K /\
         fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp)
           (ctrl_lay_block_W p (bv_unsigned sp)) (ctrl_lay_block_D p f) /\
         ctrl_lay_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m (seg_rom rsegs)).

(* --------------------------------------------------------------------------------------------------------- *)
(* Footprint form (RECIPE.md step 1 (a working note, not in this delivery), a Theorem Labs lane's rewalk-F-policy.md (a working note, not in this delivery) canonical shape): the same run as
   an ExecF.evtF under a universally quantified footprint RNG, with the premises of ctrl_lay_block_contract
   unchanged and one rng premise per region the run reads or writes (instruction fetch is not an access).  The
   regions come from the steps of the run (lib/A/Prog/ctrl_lay_block.v) and from the contracts of the callees
   __asan_stack_malloc_1, __asan_memset, __asan_memcpy and reac_box_model_block:

     image (code, GOT, runtime words)            [0x10000, 0x5fe000)                 read
     memory-checking runtime words               [RT_LO, RT_HI)                      read/write
     own window (frame, spills, probe, callees)  [S - K, S)                          read/write
     window shadow (frame words, memset/memcpy)  8-aligned cover of its shadow       read/write, checked
     thread pointer words                        [TP - 88, TP - 80), [TP - 8, TP+16) read
     the thread cells asan_tls_cells names       ctrl_lay_block_tls_rng              read
     side stack (hints, flags, class-0/1 frames) [FS, FS + FS_SIZE)                  read/write
     class-0 frame shadow (reac_box_model_block) shadow of the class-0 frames        write
     class-1 frame shadow (this function)        shadow of the class-1 frames        write
     the output block                            [p + 18, p + 50)                    read/write, checked
     the f record                                [f, f + 24)                         read, checked
     the template (ly_k fr = 2)                  [ly_tm fr, + 32)                    read, checked
     the g block (g <> 0, ly_al fr <> 0)         [g, g + ly_al fr)                   read, checked
     the md record (3 <= ly_k fr <= 9, md <> 0)  [md, md + 296)                      read, checked
     the name (ly_bb = 5, 6, has mb, rname mb)   [rname mb, + length nb)             read, checked
     JOIN_0014 (ly_k fr = 5) / JOIN_0013 (= 6)   [JOIN, JOIN + 32)                   read, checked

   The frame [frb, frb + 96) the setup writes and its 12 shadow bytes lie in the window and in the window's
   shadow cover (the real-stack frame) or in the side stack and in the shadow of the class-1 frames (the class-1
   frame): ctrl_lay_blockF.v's fk_rng_F derives them from the two cases of FK.  Each checked region also carries
   the 8-ALIGNED shadow word cover (sh_cover) its instrumented checks load: the check of a field is a load of the
   shadow byte at (a >> 3) + ASAN_K and a compare, and __asan_memcpy's and __asan_memset's quick check loads
   aligned shadow words.  ctrl_lay_block_contract_of_F gives the old statement back at ExecF.RNG_all. *)
From Stdlib Require Import Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.

(* The 8-aligned shadow word cover of [a, a + n) with n > 0 (a Theorem Labs lane's canonical form). *)
Definition sh_lo (a : Z) : Z := shadow_addr a / 8 * 8.
Definition sh_len (a n : Z) : Z := shadow_addr (a + n - 1) / 8 * 8 + 8 - sh_lo a.
Definition sh_cover (RNG : ExecF.footprint) (a n : Z) : Prop := ExecF.rng RNG (sh_lo a) (sh_len a n).

(* The thread cells that __asan_stack_malloc_1 reads through the thread pointer.  asan_tls_cells pins each of
   DT, TS, C, T, DB and k from the bytes of m, so the premise at every witness is the premise at the witnesses of
   the run. *)
Definition ctrl_lay_block_tls_rng (RNG : ExecF.footprint) (m : word -> option byte) (TP : Z) : Prop :=
  forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
    ExecF.rng RNG (bv_unsigned DT + 8) 8 /\ ExecF.rng RNG (bv_unsigned TS + 8 * k) 8 /\
    ExecF.rng RNG (bv_unsigned C + 152) 8 /\ ExecF.rng RNG (bv_unsigned T + 48) 16 /\
    ExecF.rng RNG (bv_unsigned DB + 24) 8.

Definition ctrl_lay_block_contract_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f md g FS : Z)
         (fr ob tb mb nb gb : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 md -> a3 = Z_to_bv 64 g ->
    0 <= p < 2^64 -> 0 <= f < 2^64 -> 0 <= md < 2^64 -> 0 <= g < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) ->
    ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (p + 18) (p + 50) ->
    ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) f (f + 24) ->
    (ly_k fr = 2 -> ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (ly_tm fr) (ly_tm fr + 32)) ->
    (g <> 0 -> ly_al fr <> 0 ->
       ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) g (g + ly_al fr)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) md (md + 296) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
    f mod 8 = 0 -> f + 24 <= 2^64 -> length fr = 24%nat -> bytes_at rsegs m f fr ->
    ly_k fr <= 9 -> ly_ao fr + ly_al fr <= 32 ->
    (ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm fr) tb) ->
    p <> 0 -> p + 50 <= 2^64 -> rw_cells rsegs m (p + 18) [CB 32 ob] ->
    ly_dj (p + 18) (p + 50) f (f + 24) ->
    (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          name_ok nb /\ bytes_at rsegs m (rname mb) nb)) ->
    (g <> 0 -> ly_al fr <> 0 ->
       Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= bv_unsigned sp - CTRL_LAY_BLOCK_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K ->
    addressable m f 24 ->
    addressable m (p + 18) 32 -> app_mem (p + 50) -> (p + 50 <= RT_LO \/ RT_HI <= p + 18) ->
    (ly_k fr = 2 -> addressable m (ly_tm fr) 32) ->
    (g <> 0 -> ly_al fr <> 0 ->
       addressable m g (ly_al fr) /\ app_mem (g + ly_al fr) /\ app_mem (g + 7) /\ app_mem (p + 25 + ly_ao fr)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       addressable m md 296 /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          addressable m (rname mb) (Z.of_nat (length nb)))) ->
    (ly_k fr = 5 -> addressable m JOIN_0014 32) ->
    (ly_k fr = 6 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp)
      (ctrl_lay_block_W p (bv_unsigned sp)) (ctrl_lay_block_D p f) ->
    (ly_k fr = 2 -> fp_dj [(ly_tm fr, ly_tm fr + 32)] (fp_w [0%nat; 1%nat] FS)) ->
    (g <> 0 -> ly_al fr <> 0 -> fp_dj [(g, g + ly_al fr)] (fp_w [0%nat; 1%nat] FS)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       fp_dj [(md, md + 296)] (fp_w [0%nat; 1%nat] FS) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS))) ->
    ctrl_lay_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) ->
    (* the regions the run reads or writes *)
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG RT_LO (RT_HI - RT_LO) ->
    ExecF.rng RNG (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K ->
    sh_cover RNG (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K ->
    ExecF.rng RNG (bv_unsigned tp - 88) 8 -> ExecF.rng RNG (bv_unsigned tp - 8) 24 ->
    ctrl_lay_block_tls_rng RNG m (bv_unsigned tp) ->
    ExecF.rng RNG FS FS_SIZE ->
    ExecF.rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8) ->
    ExecF.rng RNG (shadow_addr (fs_frame FS 1%nat 0)) (fs_M 1%nat * fs_B 1%nat / 8) ->
    ExecF.rng RNG (p + 18) 32 -> sh_cover RNG (p + 18) 32 ->
    ExecF.rng RNG f 24 -> sh_cover RNG f 24 ->
    (ly_k fr <> 2 \/ ExecF.rng RNG (ly_tm fr) 32 /\ sh_cover RNG (ly_tm fr) 32) ->
    (g = 0 \/ ly_al fr = 0 \/ ExecF.rng RNG g (ly_al fr) /\ sh_cover RNG g (ly_al fr)) ->
    (~ (3 <= ly_k fr <= 9) \/ md = 0 \/ ExecF.rng RNG md 296 /\ sh_cover RNG md 296) ->
    (~ (3 <= ly_k fr <= 9) \/ md = 0 \/ ~ (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) \/
       has mb = 0 \/ rname mb = 0 \/
       ExecF.rng RNG (rname mb) (Z.of_nat (length nb)) /\ sh_cover RNG (rname mb) (Z.of_nat (length nb))) ->
    (ly_k fr <> 5 \/ ExecF.rng RNG JOIN_0014 32 /\ sh_cover RNG JOIN_0014 32) ->
    (ly_k fr <> 6 \/ ExecF.rng RNG JOIN_0013 32 /\ sh_cover RNG JOIN_0013 32) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(p + 18, p + 50); (bv_unsigned sp - CTRL_LAY_BLOCK_K, bv_unsigned sp)] ++
                fp_w [0%nat; 1%nat] FS ++
                [(shadow_addr (bv_unsigned sp - CTRL_LAY_BLOCK_K), shadow_addr (bv_unsigned sp))]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) /\
         rw_cells rsegs m' (p + 18)
           [CB 32 (ly_lay (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))) g (ly_ao fr) (ly_al fr) gb)] /\
         asan_cells m' /\ shadow_rw m' /\
         addressable m' (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K /\
         fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp)
           (ctrl_lay_block_W p (bv_unsigned sp)) (ctrl_lay_block_D p f) /\
         ctrl_lay_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m (seg_rom rsegs)).

(* RECIPE step 1: the old statement as a corollary of the footprint form at ExecF.RNG_all, every rng premise by
   ExecF.rng_all and rng_bytes by its RNG_all instance.  Every region of the run lies in [0, 2^64): the image and
   the runtime words are literals, the window, the output block, the f record and the checked data blocks are
   below APPMEM_END by stk / addressable, the thread cells by the bytes of asan_tls_cells, the side stack by
   fs_place, and a shadow address is below APPMEM_END / 8 + ASAN_K.  ctrl_lay_blockF.v proves
   ctrl_lay_block_contract_F; the old ctrl_lay_block_contract follows from it by this lemma. *)
Lemma ctrl_lay_block_contract_of_F : ctrl_lay_block_contract_F -> ctrl_lay_block_contract.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p f md g FS fr ob tb mb nb gb E0 E1 E2 E3 Rp Rf Rmd Rg SP16 ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FL FB
    K9 AOL TM P0 P50 BLK DB1 DB2 DB3 DBN MDP GP MI0 AC0 SR0 HHM HAE AW0 AF AR AP50 ARDJ ATM AG AMD AJ5 AJ6
    FP0 FPT FPG FPM TLS0.
  pose proof (eq_refl : CTRL_LAY_BLOCK_K = 4512) as EK.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 tp) as Rtp. change (bv_modulus 64) with (2^64) in Rtp.
  pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold HIGHMEM_BEG, APPMEM_END, CTRL_LAY_BLOCK_K in HHM', HAE'.
  pose proof AW0 as (AW00 & AW01 & AW02 & _). unfold APPMEM_END, CTRL_LAY_BLOCK_K in AW02.
  pose proof AR as (AR0 & AR1 & AR2 & _). unfold APPMEM_END in AR2.
  pose proof AF as (AF0 & AF1 & AF2 & _). unfold APPMEM_END in AF2.
  (* the side stack and the thread cells are inside the application memory *)
  pose proof FP0 as (DT & TS & C & T & DB & k & HTC & HTP & HPL & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
  pose proof HPL as (PL0 & PL1 & PL2 & PL3 & PL4).
  assert (FSlo : 0 <= FS) by lia.
  assert (FShi : FS + FS_SIZE <= 2^64).
  { pose proof (PL3 FS ltac:(unfold FS_SIZE; lia)) as A1.
    pose proof (PL3 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as A2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2. unfold FS_SIZE in *. lia. }
  unfold FS_SIZE in FShi.
  (* the bytes of each cell the run reads lie in [0, 2^64) (bytes_at carries both bounds) *)
  pose proof HTC as (_ & _ & HDT & HDT8 & _ & _ & _ & HTS & HTSk & HC152 & (tb' & te' & HT48) & _ & _ & _ & _ & _
                     & HTPDB & _ & HDB24).
  pose proof HDT as (PDT0 & PDT1 & _). pose proof HTS as (PTS0 & PTS1 & _).
  pose proof HTPDB as (PDB0 & PDB1 & _).
  rewrite length_le8 in PDT1, PTS1, PDB1. cbn [Z.of_nat] in PDT1, PTS1, PDB1.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            t3 t4 t5 t6 F fc m p f md g FS fr ob tb mb nb gb); try assumption;
    unfold sh_cover, sh_len, sh_lo, shadow_addr, ASAN_K.
  - unfold rng_bytes; intros; exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold RT_LO, RT_HI; lia.
  - apply ExecF.rng_all; unfold CTRL_LAY_BLOCK_K; lia.
  - apply ExecF.rng_all; unfold CTRL_LAY_BLOCK_K; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - intros DT' TS' C' T' DB' k' HT'.
    pose proof HT' as (_ & _ & _ & HDT8' & _ & (Hk0 & Hk1) & _ & _ & HTSk' & HC152' & (tb2 & te2 & HT48') & _ & _
                       & _ & _ & _ & _ & _ & HDB24').
    pose proof HDT8' as (QDT0' & QDT1' & _). pose proof HTSk' as (QTS0' & QTS1' & _).
    pose proof HC152' as (QC0' & QC1' & _). pose proof HT48' as (QT0' & QT1' & _).
    pose proof HDB24' as (QDB0' & QDB1' & _).
    rewrite length_le8 in QDT1', QTS1', QC1', QDB1'. rewrite length_app, !length_le8 in QT1'.
    cbn [Z.of_nat] in QDT1', QTS1', QC1', QDB1', QT1'.
    split; [apply ExecF.rng_all; lia|]. split; [apply ExecF.rng_all; lia|].
    split; [apply ExecF.rng_all; lia|]. split; apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - assert (EFR : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (ESH : fs_M 0%nat * fs_B 0%nat / 8 = 131072) by reflexivity.
    rewrite EFR, ESH. unfold shadow_addr, ASAN_K. apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - assert (EFR : fs_frame FS 1%nat 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (ESH : fs_M 1%nat * fs_B 1%nat / 8 = 131072) by reflexivity.
    rewrite EFR, ESH. unfold shadow_addr, ASAN_K. apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - destruct (Z.eq_dec (ly_k fr) 2) as [E2'|E2']; [right | left; exact E2'].
    pose proof (ATM E2') as (AT0 & AT1 & AT2 & _). unfold APPMEM_END in AT2.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
  - destruct (Z.eq_dec g 0) as [->|Hg0]; [left; reflexivity | right].
    destruct (Z.eq_dec (ly_al fr) 0) as [Ha0|Ha0]; [left; exact Ha0 | right].
    pose proof (proj1 (AG Hg0 Ha0)) as (AG0 & AG1 & AG2 & _). unfold APPMEM_END in AG2.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
  - destruct (Z_le_dec 3 (ly_k fr)) as [L3|L3]; [|left; lia].
    destruct (Z_le_dec (ly_k fr) 9) as [L9|L9]; [|left; lia].
    destruct (Z.eq_dec md 0) as [->|Hm0]; [right; left; reflexivity | right; right].
    pose proof (proj1 (AMD ltac:(lia) Hm0)) as (AM0 & AM1 & AM2 & _). unfold APPMEM_END in AM2.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
  - destruct (Z_le_dec 3 (ly_k fr)) as [L3|L3]; [|left; lia].
    destruct (Z_le_dec (ly_k fr) 9) as [L9|L9]; [|left; lia].
    destruct (Z.eq_dec md 0) as [->|Hm0]; [right; left; reflexivity|].
    destruct (Z.eq_dec (ly_bb (ly_k fr)) 5) as [B5|B5];
      [|destruct (Z.eq_dec (ly_bb (ly_k fr)) 6) as [B6|B6]].
    3: { right; right; left. intros [Hc|Hc]; [exact (B5 Hc) | exact (B6 Hc)]. }
    all: destruct (Z.eq_dec (has mb) 0) as [Hh|Hh]; [right; right; right; left; exact Hh|].
    all: destruct (Z.eq_dec (rname mb) 0) as [Hr|Hr]; [right; right; right; right; left; exact Hr|].
    all: right; right; right; right; right.
    all: match goal with |- _ /\ _ =>
           let AN := fresh "AN" in
           first [ pose proof (proj2 (AMD ltac:(lia) Hm0) (or_introl B5) Hh Hr) as AN
                 | pose proof (proj2 (AMD ltac:(lia) Hm0) (or_intror B6) Hh Hr) as AN ];
           destruct AN as (AN0 & AN1 & AN2 & _); unfold APPMEM_END in AN2 end.
    all: split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
  - destruct (Z.eq_dec (ly_k fr) 5) as [E5|E5]; [right | left; exact E5].
    pose proof (AJ5 E5) as (AJ0 & AJ1 & AJ2 & _). unfold APPMEM_END in AJ2.
    split; apply ExecF.rng_all; unfold JOIN_0014 in *; try Z.div_mod_to_equations; lia.
  - destruct (Z.eq_dec (ly_k fr) 6) as [E6|E6]; [right | left; exact E6].
    pose proof (AJ6 E6) as (AJ0 & AJ1 & AJ2 & _). unfold APPMEM_END in AJ2.
    split; apply ExecF.rng_all; unfold JOIN_0013 in *; try Z.div_mod_to_equations; lia.
Qed.

(* --------------------------------------------------------------------------------------------------------- *)
(* Route (C) (a Theorem Labs lane 2026-10-29 09:20Z; form of a Theorem Labs lane 09:38Z): ctrl_lay_block_contract_on and
   ctrl_lay_block_contract_F_on, the two statements above with TWO changes each:
     - the premise `shadow_rw m` becomes `shadow_rw_on (ctrl_lay_block_shadow_R S FS p f md g fr mb nb) m`
       (S = bv_unsigned sp);
     - the post's `shadow_rw m'` becomes `forall P, shadow_rw_on P m -> shadow_rw_on P m'`: every shadow region the
       caller holds before the call it holds after the call.
   ctrl_lay_block_shadow_R is the shadow part of the footprint the _F statement above names (its table and its rng
   premises on shadow bytes), as 8-aligned shadow-word covers (sh_word_on, a Theorem Labs lane's lib/A/Prog/sh_word_on.v):
   the window [S - K, S), which holds the real-stack frame [frb, frb + 96) and its 12 shadow bytes
   (frame_shadow_rwcells_shadow_R frb, ctrl_lay_block.v) and every callee's real-stack frame; the shadow of the
   class-0 and class-1 blocks of the side stack, [shadow_addr (fs_frame FS c 0), + 131072) for c = 0, 1: the class-1
   frame's 16 shadow bytes [shadow_addr frb, + 16) (frb = fs_frame FS 1 j, j < fs_M 1), reac_box_model_block's
   class-0 frame's 8, and __asan_stack_malloc_1's / _0's stores (a Theorem Labs lane 10:57Z, side-stack-shadow.md (a working note, not in this delivery): the class-c
   block is asan_stack_malloc's R; the side-stack header's shadow is not in R); and, under the guard of its data
   premise, of each block the run or a callee reads or writes:
   the output block [p + 18, p + 50), the row f, the template tm (k = 2), g (g, al <> 0), md and the name
   (3 <= k <= 9, md <> 0, and for the name ly_bb k = 5, 6 with has mb, rname mb <> 0), and the JOIN block (k = 5, 6).
   reac_box_model_block's region at its call (reac_box_model_block_shadow_R, reac_box_model_block_c.v) and
   __asan_memcpy's (asan_memcpy_shadow_R) are inside it.  No other shadow byte is read or written by the run.
   These are STATEMENTS here: ctrl_lay_block_contract_on is proved when ctrl_lay_block.v's run narrows (lay_tail,
   route (C) L2), which takes the callees' _on contracts; until then cite it only as a hypothesis, as the old
   contract is cited.  The old statements follow (ctrl_lay_block_contract_of_on, ctrl_lay_block_contract_F_of_F_on);
   ctrl_lay_block_contract_on_of_F_on is ctrl_lay_block_contract_of_F for the new pair. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import sh_word_on asan_stack_malloc_c_on.

Definition ctrl_lay_block_shadow_R (S FS p f md g : Z) (fr mb nb : list byte) (a : Z) : Prop :=
  sh_word_on (S - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K a \/
  asan_stack_malloc_shadow_R FS 0%nat a \/
  asan_stack_malloc_shadow_R FS 1%nat a \/
  sh_word_on (p + 18) 32 a \/ sh_word_on f 24 a \/
  (ly_k fr = 2 /\ sh_word_on (ly_tm fr) 32 a) \/
  (g <> 0 /\ ly_al fr <> 0 /\ sh_word_on g (ly_al fr) a) \/
  (3 <= ly_k fr <= 9 /\ md <> 0 /\ sh_word_on md 296 a) \/
  (3 <= ly_k fr <= 9 /\ md <> 0 /\ (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) /\ has mb <> 0 /\ rname mb <> 0 /\
     sh_word_on (rname mb) (Z.of_nat (length nb)) a) \/
  (ly_k fr = 5 /\ sh_word_on JOIN_0014 32 a) \/ (ly_k fr = 6 /\ sh_word_on JOIN_0013 32 a).

Definition ctrl_lay_block_contract_on : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f md g FS : Z)
         (fr ob tb mb nb gb : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 md -> a3 = Z_to_bv 64 g ->
    0 <= p < 2^64 -> 0 <= f < 2^64 -> 0 <= md < 2^64 -> 0 <= g < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) ->
    ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (p + 18) (p + 50) ->
    ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) f (f + 24) ->
    (ly_k fr = 2 -> ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (ly_tm fr) (ly_tm fr + 32)) ->
    (g <> 0 -> ly_al fr <> 0 ->
       ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) g (g + ly_al fr)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) md (md + 296) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
    f mod 8 = 0 -> f + 24 <= 2^64 -> length fr = 24%nat -> bytes_at rsegs m f fr ->
    ly_k fr <= 9 -> ly_ao fr + ly_al fr <= 32 ->
    (ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm fr) tb) ->
    p <> 0 -> p + 50 <= 2^64 -> rw_cells rsegs m (p + 18) [CB 32 ob] ->
    ly_dj (p + 18) (p + 50) f (f + 24) ->
    (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          name_ok nb /\ bytes_at rsegs m (rname mb) nb)) ->
    (g <> 0 -> ly_al fr <> 0 ->
       Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw_on (ctrl_lay_block_shadow_R (bv_unsigned sp) FS p f md g fr mb nb) m ->
    HIGHMEM_BEG <= bv_unsigned sp - CTRL_LAY_BLOCK_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K ->
    addressable m f 24 ->
    addressable m (p + 18) 32 -> app_mem (p + 50) -> (p + 50 <= RT_LO \/ RT_HI <= p + 18) ->
    (ly_k fr = 2 -> addressable m (ly_tm fr) 32) ->
    (g <> 0 -> ly_al fr <> 0 ->
       addressable m g (ly_al fr) /\ app_mem (g + ly_al fr) /\ app_mem (g + 7) /\ app_mem (p + 25 + ly_ao fr)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       addressable m md 296 /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          addressable m (rname mb) (Z.of_nat (length nb)))) ->
    (ly_k fr = 5 -> addressable m JOIN_0014 32) ->
    (ly_k fr = 6 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp)
      (ctrl_lay_block_W p (bv_unsigned sp)) (ctrl_lay_block_D p f) ->
    (ly_k fr = 2 -> fp_dj [(ly_tm fr, ly_tm fr + 32)] (fp_w [0%nat; 1%nat] FS)) ->
    (g <> 0 -> ly_al fr <> 0 -> fp_dj [(g, g + ly_al fr)] (fp_w [0%nat; 1%nat] FS)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       fp_dj [(md, md + 296)] (fp_w [0%nat; 1%nat] FS) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS))) ->
    ctrl_lay_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(p + 18, p + 50); (bv_unsigned sp - CTRL_LAY_BLOCK_K, bv_unsigned sp)] ++
                fp_w [0%nat; 1%nat] FS ++
                [(shadow_addr (bv_unsigned sp - CTRL_LAY_BLOCK_K), shadow_addr (bv_unsigned sp))]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) /\
         rw_cells rsegs m' (p + 18)
           [CB 32 (ly_lay (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))) g (ly_ao fr) (ly_al fr) gb)] /\
         asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m') /\
         addressable m' (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K /\
         fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp)
           (ctrl_lay_block_W p (bv_unsigned sp)) (ctrl_lay_block_D p f) /\
         ctrl_lay_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m (seg_rom rsegs)).

(* The old statement: the universal shadow_rw gives the region (shadow_rw_on_of_shadow_rw), and the post's region
   transport at P := fun _ => True gives the universal post back (shadow_rw_of_on_all). *)
Lemma ctrl_lay_block_contract_of_on : ctrl_lay_block_contract_on -> ctrl_lay_block_contract.
Proof.
  intros H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p f md g FS fr ob tb mb nb gb E0 E1 E2 E3 Rp Rf Rmd Rg SP16 ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FL FB
    K9 AOL TM P0 P50 BLK DB1 DB2 DB3 DBN MDP GP MI0 AC0 SR0 HHM HAE AW0 AF AR AP50 ARDJ ATM AG AMD AJ5 AJ6
    FP0 FPT FPG FPM TLS0.
  eapply evt_mono.
  - exact (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m p f md g FS fr ob tb mb nb gb E0 E1 E2 E3 Rp Rf Rmd Rg SP16 ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FL FB
           K9 AOL TM P0 P50 BLK DB1 DB2 DB3 DBN MDP GP MI0 AC0 (shadow_rw_on_of_shadow_rw _ m SR0) HHM HAE AW0 AF AR
           AP50 ARDJ ATM AG AMD AJ5 AJ6 FP0 FPT FPG FPM TLS0).
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                Ems & MU & WM & MI & ST & BLK' & AC & SW & Rest).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj Ems (conj MU (conj WM (conj MI (conj ST (conj BLK' (conj AC (conj _ Rest)))))))).
    exact (shadow_rw_of_on_all m' (SW (fun _ => True) (shadow_rw_on_of_shadow_rw _ m SR0))).
Qed.

Definition ctrl_lay_block_contract_F_on : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p f md g FS : Z)
         (fr ob tb mb nb gb : list byte),
    a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 f -> a2 = Z_to_bv 64 md -> a3 = Z_to_bv 64 g ->
    0 <= p < 2^64 -> 0 <= f < 2^64 -> 0 <= md < 2^64 -> 0 <= g < 2^64 ->
    bv_unsigned sp mod 16 = 0 ->
    stk rsegs m (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) ->
    ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (p + 18) (p + 50) ->
    ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) f (f + 24) ->
    (ly_k fr = 2 -> ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (ly_tm fr) (ly_tm fr + 32)) ->
    (g <> 0 -> ly_al fr <> 0 ->
       ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) g (g + ly_al fr)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) md (md + 296) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          ly_dj (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) (rname mb) (rname mb + Z.of_nat (length nb)))) ->
    f mod 8 = 0 -> f + 24 <= 2^64 -> length fr = 24%nat -> bytes_at rsegs m f fr ->
    ly_k fr <= 9 -> ly_ao fr + ly_al fr <= 32 ->
    (ly_k fr = 2 -> ly_tm fr + 32 <= 2^64 /\ length tb = 32%nat /\ ro_bytes rsegs (ly_tm fr) tb) ->
    p <> 0 -> p + 50 <= 2^64 -> rw_cells rsegs m (p + 18) [CB 32 ob] ->
    ly_dj (p + 18) (p + 50) f (f + 24) ->
    (ly_k fr = 2 -> ly_dj (p + 18) (p + 50) (ly_tm fr) (ly_tm fr + 32)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 -> ly_dj (p + 18) (p + 50) md (md + 296)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 -> (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
       ly_dj (p + 18) (p + 50) (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       md mod 8 = 0 /\ length mb = 296%nat /\ bytes_at rsegs m md mb /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          name_ok nb /\ bytes_at rsegs m (rname mb) nb)) ->
    (g <> 0 -> ly_al fr <> 0 ->
       Z.of_nat (length gb) = ly_al fr /\ bytes_at rsegs m g gb /\ ly_dj (p + 18) (p + 50) g (g + ly_al fr)) ->
    mem_inv rsegs m ->
    (* asan *)
    asan_cells m -> shadow_rw_on (ctrl_lay_block_shadow_R (bv_unsigned sp) FS p f md g fr mb nb) m ->
    HIGHMEM_BEG <= bv_unsigned sp - CTRL_LAY_BLOCK_K -> bv_unsigned sp <= APPMEM_END ->
    addressable m (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K ->
    addressable m f 24 ->
    addressable m (p + 18) 32 -> app_mem (p + 50) -> (p + 50 <= RT_LO \/ RT_HI <= p + 18) ->
    (ly_k fr = 2 -> addressable m (ly_tm fr) 32) ->
    (g <> 0 -> ly_al fr <> 0 ->
       addressable m g (ly_al fr) /\ app_mem (g + ly_al fr) /\ app_mem (g + 7) /\ app_mem (p + 25 + ly_ao fr)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       addressable m md 296 /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          addressable m (rname mb) (Z.of_nat (length nb)))) ->
    (ly_k fr = 5 -> addressable m JOIN_0014 32) ->
    (ly_k fr = 6 -> addressable m JOIN_0013 32) ->
    fp [0%nat; 1%nat] m (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp)
      (ctrl_lay_block_W p (bv_unsigned sp)) (ctrl_lay_block_D p f) ->
    (ly_k fr = 2 -> fp_dj [(ly_tm fr, ly_tm fr + 32)] (fp_w [0%nat; 1%nat] FS)) ->
    (g <> 0 -> ly_al fr <> 0 -> fp_dj [(g, g + ly_al fr)] (fp_w [0%nat; 1%nat] FS)) ->
    (3 <= ly_k fr <= 9 -> md <> 0 ->
       fp_dj [(md, md + 296)] (fp_w [0%nat; 1%nat] FS) /\
       ((ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) -> has mb <> 0 -> rname mb <> 0 ->
          fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS))) ->
    ctrl_lay_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) ->
    (* the regions the run reads or writes *)
    rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG RT_LO (RT_HI - RT_LO) ->
    ExecF.rng RNG (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K ->
    sh_cover RNG (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K ->
    ExecF.rng RNG (bv_unsigned tp - 88) 8 -> ExecF.rng RNG (bv_unsigned tp - 8) 24 ->
    ctrl_lay_block_tls_rng RNG m (bv_unsigned tp) ->
    ExecF.rng RNG FS FS_SIZE ->
    ExecF.rng RNG (shadow_addr (fs_frame FS 0%nat 0)) (fs_M 0%nat * fs_B 0%nat / 8) ->
    ExecF.rng RNG (shadow_addr (fs_frame FS 1%nat 0)) (fs_M 1%nat * fs_B 1%nat / 8) ->
    ExecF.rng RNG (p + 18) 32 -> sh_cover RNG (p + 18) 32 ->
    ExecF.rng RNG f 24 -> sh_cover RNG f 24 ->
    (ly_k fr <> 2 \/ ExecF.rng RNG (ly_tm fr) 32 /\ sh_cover RNG (ly_tm fr) 32) ->
    (g = 0 \/ ly_al fr = 0 \/ ExecF.rng RNG g (ly_al fr) /\ sh_cover RNG g (ly_al fr)) ->
    (~ (3 <= ly_k fr <= 9) \/ md = 0 \/ ExecF.rng RNG md 296 /\ sh_cover RNG md 296) ->
    (~ (3 <= ly_k fr <= 9) \/ md = 0 \/ ~ (ly_bb (ly_k fr) = 5 \/ ly_bb (ly_k fr) = 6) \/
       has mb = 0 \/ rname mb = 0 \/
       ExecF.rng RNG (rname mb) (Z.of_nat (length nb)) /\ sh_cover RNG (rname mb) (Z.of_nat (length nb))) ->
    (ly_k fr <> 5 \/ ExecF.rng RNG JOIN_0014 32 /\ sh_cover RNG JOIN_0014 32) ->
    (ly_k fr <> 6 \/ ExecF.rng RNG JOIN_0013 32 /\ sh_cover RNG JOIN_0013 32) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch ([(p + 18, p + 50); (bv_unsigned sp - CTRL_LAY_BLOCK_K, bv_unsigned sp)] ++
                fp_w [0%nat; 1%nat] FS ++
                [(shadow_addr (bv_unsigned sp - CTRL_LAY_BLOCK_K), shadow_addr (bv_unsigned sp))]) m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp) /\
         rw_cells rsegs m' (p + 18)
           [CB 32 (ly_lay (ly_k fr) tb (ly_Z md mb nb (ly_bb (ly_k fr))) g (ly_ao fr) (ly_al fr) gb)] /\
         asan_cells m' /\ (forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P m') /\
         addressable m' (bv_unsigned sp - CTRL_LAY_BLOCK_K) CTRL_LAY_BLOCK_K /\
         fp [0%nat; 1%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp)
           (ctrl_lay_block_W p (bv_unsigned sp)) (ctrl_lay_block_D p f) /\
         ctrl_lay_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - CTRL_LAY_BLOCK_K) (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CTRL_LAY_BLOCK) fc None m (seg_rom rsegs)).

Lemma ctrl_lay_block_contract_F_of_F_on : ctrl_lay_block_contract_F_on -> ctrl_lay_block_contract_F.
Proof.
  intros H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p f md g FS fr ob tb mb nb gb E0 E1 E2 E3 Rp Rf Rmd Rg SP16 ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FL FB
    K9 AOL TM P0 P50 BLK DB1 DB2 DB3 DBN MDP GP MI0 AC0 SR0 HHM HAE AW0 AF AR AP50 ARDJ ATM AG AMD AJ5 AJ6
    FP0 FPT FPG FPM TLS0
    RB RIMG RRT RWIN RSWIN RTP1 RTP2 RTLS RFS RF0 RF1 RP RSP RF RSF RTM RG RMD RNM RJ5 RJ6.
  eapply ExecF.evtF_mono.
  - exact (H RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m p f md g FS fr ob tb mb nb gb E0 E1 E2 E3 Rp Rf Rmd Rg SP16 ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FL FB
           K9 AOL TM P0 P50 BLK DB1 DB2 DB3 DBN MDP GP MI0 AC0 (shadow_rw_on_of_shadow_rw _ m SR0) HHM HAE AW0 AF AR
           AP50 ARDJ ATM AG AMD AJ5 AJ6 FP0 FPT FPG FPM TLS0
           RB RIMG RRT RWIN RSWIN RTP1 RTP2 RTLS RFS RF0 RF1 RP RSP RF RSF RTM RG RMD RNM RJ5 RJ6).
  - intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                Ems & MU & WM & MI & ST & BLK' & AC & SW & Rest).
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    refine (conj Ems (conj MU (conj WM (conj MI (conj ST (conj BLK' (conj AC (conj _ Rest)))))))).
    exact (shadow_rw_of_on_all m' (SW (fun _ => True) (shadow_rw_on_of_shadow_rw _ m SR0))).
Qed.

(* ctrl_lay_block_contract_of_F for the route (C) pair (its proof, unchanged: the region premise and the post pass
   through).  ctrl_lay_blockF.v proves ctrl_lay_block_contract_F; ctrl_lay_block_contract_F_on is proved with the run. *)
Lemma ctrl_lay_block_contract_on_of_F_on : ctrl_lay_block_contract_F_on -> ctrl_lay_block_contract_on.
Proof.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p f md g FS fr ob tb mb nb gb E0 E1 E2 E3 Rp Rf Rmd Rg SP16 ST0 DJ1 DJ2 DJ3 DJ3g DJ3m F8 F24 FL FB
    K9 AOL TM P0 P50 BLK DB1 DB2 DB3 DBN MDP GP MI0 AC0 SR0 HHM HAE AW0 AF AR AP50 ARDJ ATM AG AMD AJ5 AJ6
    FP0 FPT FPG FPM TLS0.
  pose proof (eq_refl : CTRL_LAY_BLOCK_K = 4512) as EK.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (bv_unsigned_in_range 64 tp) as Rtp. change (bv_modulus 64) with (2^64) in Rtp.
  pose proof HHM as HHM'. pose proof HAE as HAE'.
  unfold HIGHMEM_BEG, APPMEM_END, CTRL_LAY_BLOCK_K in HHM', HAE'.
  pose proof AW0 as (AW00 & AW01 & AW02 & _). unfold APPMEM_END, CTRL_LAY_BLOCK_K in AW02.
  pose proof AR as (AR0 & AR1 & AR2 & _). unfold APPMEM_END in AR2.
  pose proof AF as (AF0 & AF1 & AF2 & _). unfold APPMEM_END in AF2.
  (* the side stack and the thread cells are inside the application memory *)
  pose proof FP0 as (DT & TS & C & T & DB & k & HTC & HTP & HPL & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
  pose proof HPL as (PL0 & PL1 & PL2 & PL3 & PL4).
  assert (FSlo : 0 <= FS) by lia.
  assert (FShi : FS + FS_SIZE <= 2^64).
  { pose proof (PL3 FS ltac:(unfold FS_SIZE; lia)) as A1.
    pose proof (PL3 (FS + FS_SIZE - 1) ltac:(unfold FS_SIZE; lia)) as A2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A1, A2. unfold FS_SIZE in *. lia. }
  unfold FS_SIZE in FShi.
  (* the bytes of each cell the run reads lie in [0, 2^64) (bytes_at carries both bounds) *)
  pose proof HTC as (_ & _ & HDT & HDT8 & _ & _ & _ & HTS & HTSk & HC152 & (tb' & te' & HT48) & _ & _ & _ & _ & _
                     & HTPDB & _ & HDB24).
  pose proof HDT as (PDT0 & PDT1 & _). pose proof HTS as (PTS0 & PTS1 & _).
  pose proof HTPDB as (PDB0 & PDB1 & _).
  rewrite length_le8 in PDT1, PTS1, PDB1. cbn [Z.of_nat] in PDT1, PTS1, PDB1.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply (HF ExecF.RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
            t3 t4 t5 t6 F fc m p f md g FS fr ob tb mb nb gb); try assumption;
    unfold sh_cover, sh_len, sh_lo, shadow_addr, ASAN_K.
  - unfold rng_bytes; intros; exact I.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; unfold RT_LO, RT_HI; lia.
  - apply ExecF.rng_all; unfold CTRL_LAY_BLOCK_K; lia.
  - apply ExecF.rng_all; unfold CTRL_LAY_BLOCK_K; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - intros DT' TS' C' T' DB' k' HT'.
    pose proof HT' as (_ & _ & _ & HDT8' & _ & (Hk0 & Hk1) & _ & _ & HTSk' & HC152' & (tb2 & te2 & HT48') & _ & _
                       & _ & _ & _ & _ & _ & HDB24').
    pose proof HDT8' as (QDT0' & QDT1' & _). pose proof HTSk' as (QTS0' & QTS1' & _).
    pose proof HC152' as (QC0' & QC1' & _). pose proof HT48' as (QT0' & QT1' & _).
    pose proof HDB24' as (QDB0' & QDB1' & _).
    rewrite length_le8 in QDT1', QTS1', QC1', QDB1'. rewrite length_app, !length_le8 in QT1'.
    cbn [Z.of_nat] in QDT1', QTS1', QC1', QDB1', QT1'.
    split; [apply ExecF.rng_all; lia|]. split; [apply ExecF.rng_all; lia|].
    split; [apply ExecF.rng_all; lia|]. split; apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; lia.
  - assert (EFR : fs_frame FS 0%nat 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (ESH : fs_M 0%nat * fs_B 0%nat / 8 = 131072) by reflexivity.
    rewrite EFR, ESH. unfold shadow_addr, ASAN_K. apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - assert (EFR : fs_frame FS 1%nat 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (ESH : fs_M 1%nat * fs_B 1%nat / 8 = 131072) by reflexivity.
    rewrite EFR, ESH. unfold shadow_addr, ASAN_K. apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - apply ExecF.rng_all; lia.
  - apply ExecF.rng_all; Z.div_mod_to_equations; lia.
  - destruct (Z.eq_dec (ly_k fr) 2) as [E2'|E2']; [right | left; exact E2'].
    pose proof (ATM E2') as (AT0 & AT1 & AT2 & _). unfold APPMEM_END in AT2.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
  - destruct (Z.eq_dec g 0) as [->|Hg0]; [left; reflexivity | right].
    destruct (Z.eq_dec (ly_al fr) 0) as [Ha0|Ha0]; [left; exact Ha0 | right].
    pose proof (proj1 (AG Hg0 Ha0)) as (AG0 & AG1 & AG2 & _). unfold APPMEM_END in AG2.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
  - destruct (Z_le_dec 3 (ly_k fr)) as [L3|L3]; [|left; lia].
    destruct (Z_le_dec (ly_k fr) 9) as [L9|L9]; [|left; lia].
    destruct (Z.eq_dec md 0) as [->|Hm0]; [right; left; reflexivity | right; right].
    pose proof (proj1 (AMD ltac:(lia) Hm0)) as (AM0 & AM1 & AM2 & _). unfold APPMEM_END in AM2.
    split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
  - destruct (Z_le_dec 3 (ly_k fr)) as [L3|L3]; [|left; lia].
    destruct (Z_le_dec (ly_k fr) 9) as [L9|L9]; [|left; lia].
    destruct (Z.eq_dec md 0) as [->|Hm0]; [right; left; reflexivity|].
    destruct (Z.eq_dec (ly_bb (ly_k fr)) 5) as [B5|B5];
      [|destruct (Z.eq_dec (ly_bb (ly_k fr)) 6) as [B6|B6]].
    3: { right; right; left. intros [Hc|Hc]; [exact (B5 Hc) | exact (B6 Hc)]. }
    all: destruct (Z.eq_dec (has mb) 0) as [Hh|Hh]; [right; right; right; left; exact Hh|].
    all: destruct (Z.eq_dec (rname mb) 0) as [Hr|Hr]; [right; right; right; right; left; exact Hr|].
    all: right; right; right; right; right.
    all: match goal with |- _ /\ _ =>
           let AN := fresh "AN" in
           first [ pose proof (proj2 (AMD ltac:(lia) Hm0) (or_introl B5) Hh Hr) as AN
                 | pose proof (proj2 (AMD ltac:(lia) Hm0) (or_intror B6) Hh Hr) as AN ];
           destruct AN as (AN0 & AN1 & AN2 & _); unfold APPMEM_END in AN2 end.
    all: split; apply ExecF.rng_all; try Z.div_mod_to_equations; lia.
  - destruct (Z.eq_dec (ly_k fr) 5) as [E5|E5]; [right | left; exact E5].
    pose proof (AJ5 E5) as (AJ0 & AJ1 & AJ2 & _). unfold APPMEM_END in AJ2.
    split; apply ExecF.rng_all; unfold JOIN_0014 in *; try Z.div_mod_to_equations; lia.
  - destruct (Z.eq_dec (ly_k fr) 6) as [E6|E6]; [right | left; exact E6].
    pose proof (AJ6 E6) as (AJ0 & AJ1 & AJ2 & _). unfold APPMEM_END in AJ2.
    split; apply ExecF.rng_all; unfold JOIN_0013 in *; try Z.div_mod_to_equations; lia.
Qed.

Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_lay_block_c.ctrl_lay_block_contract_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_lay_block_c.ctrl_lay_block_contract_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_lay_block_c.ctrl_lay_block_contract_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_lay_block_c.ctrl_lay_block_contract_F_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_lay_block_c.ctrl_lay_block_contract_of_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_lay_block_c.ctrl_lay_block_contract_of_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_lay_block_c.ctrl_lay_block_contract_F_of_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_lay_block_c.ctrl_lay_block_contract_F_of_F_on.
Locate OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_lay_block_c.ctrl_lay_block_contract_on_of_F_on.
Print Assumptions OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.ctrl_lay_block_c.ctrl_lay_block_contract_on_of_F_on.
