From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
Import ListNotations.
Open Scope Z_scope.

Definition ASAN_STACK_MALLOC_0 : Z := 0x3d6f4.
Definition ASAN_STACK_MALLOC_1 : Z := 0x3d868.
Definition ASAN_STACK_MALLOC_2 : Z := 0x3d9f8.
Definition ASAN_STACK_MALLOC_6 : Z := 0x3db94.
Definition ASAN_STACK_MALLOC_K : Z := 208.

Definition ASAN_GT : Z := 0x5fe000.
Definition TLS_INDEX : Z := 0xa15d0.
Definition DTLS_TPOFF : Z := 0xa15e0.
Definition REAL_TLS_GET_ADDR : Z := 0xa2690.
Definition MUSL_TLS_GET_ADDR : Z := 0x99624.
Definition TSD_KEY_INITED : Z := 0xa8f20.
Definition TSD_KEY : Z := 0xa8f24.
Definition GOT_CF : Z := 0xa08e0.
Definition CF : Z := 0x13b1e8.
Definition GOT_VERBOSITY : Z := 0xa0940.
Definition VERBOSITY : Z := 0x139158.

Definition FS_SIZE : Z := 11571200.
Definition fs_B (c : nat) : Z := 64 * 2 ^ Z.of_nat c.
Definition fs_M (c : nat) : Z := 2 ^ (14 - Z.of_nat c).
Definition fs_frame (FS : Z) (c : nat) (j : Z) : Z := FS + 36864 + Z.of_nat c * 2 ^ 20 + j * fs_B c.
Definition fs_flag (FS : Z) (c : nat) (j : Z) : Z := FS + 4096 + 2 ^ 15 - 2 ^ (15 - Z.of_nat c) + j.
Definition fs_hint (FS : Z) (c : nat) : Z := FS + 8 * Z.of_nat c.
Definition fs_shadow_n (c : nat) (L : Z) : Z := (if Nat.leb c 6 then fs_B c else L) / 8.

Definition fs_place (m : word -> option byte) (FS : Z) : Prop :=
  0 < FS /\ FS mod 4096 = 0 /\ ASAN_GT <= FS /\ (forall a, FS <= a < FS + FS_SIZE -> app_mem a)
  /\ stk rsegs m FS (FS + FS_SIZE).

Definition asan_tls_cells (m : word -> option byte) (TP : Z) (DT TS C T DB : word) (k : Z) : Prop :=
  bytes_at rsegs m TLS_INDEX (le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 (-2048)))
  /\ bytes_at rsegs m REAL_TLS_GET_ADDR (le8 (Z_to_bv 64 MUSL_TLS_GET_ADDR))
  /\ bytes_at rsegs m (TP - 8) (le8 DT) /\ bytes_at rsegs m (bv_unsigned DT + 8) (le8 (Z_to_bv 64 (TP + 2048)))
  /\ bytes_at rsegs m TSD_KEY_INITED [Z_to_bv 8 1]
  /\ 0 <= k < 2 ^ 32 /\ bytes_at rsegs m TSD_KEY (le4 (Z_to_bv 64 k))
  /\ bytes_at rsegs m (TP - 88) (le8 TS) /\ bytes_at rsegs m (bv_unsigned TS + 8 * k) (le8 C)
  /\ bytes_at rsegs m (bv_unsigned C + 152) (le8 T)
  /\ (exists tb te : word, bytes_at rsegs m (bv_unsigned T + 48) (le8 tb ++ le8 te))
  /\ bytes_at rsegs m GOT_CF (le8 (Z_to_bv 64 CF)) /\ bytes_at rsegs m (CF + 137) [Z_to_bv 8 1]
  /\ bytes_at rsegs m GOT_VERBOSITY (le8 (Z_to_bv 64 VERBOSITY)) /\ bytes_at rsegs m VERBOSITY (le4 (Z_to_bv 64 0))
  /\ bytes_at rsegs m DTLS_TPOFF (le8 (Z_to_bv 64 8))
  /\ bytes_at rsegs m (TP + 8) (le8 DB) /\ bv_unsigned DB <> 0
  /\ bytes_at rsegs m (bv_unsigned DB + 24) (le8 (Z_to_bv 64 TP)).

Definition asan_stack_malloc_frame (c : nat) (K : Z) (sp : word) (L FS j : Z) (a0 : word)
    (m m' : word -> option byte) : Prop :=
  let fr := fs_frame FS c j in let B := fs_B c in let n := fs_shadow_n c L in
  a0 = Z_to_bv 64 fr /\ fr mod 64 = 0 /\ ((6 <= c)%nat -> fr mod 4096 = 0)
  /\ bytes_at rsegs m' (fs_flag FS c j) [Z_to_bv 8 1]
  /\ bytes_at rsegs m' (fr + 24) (le8 sp)
  /\ bytes_at rsegs m' (fr + B - 8) (le8 (Z_to_bv 64 (fs_flag FS c j)))
  /\ bytes_at rsegs m' (shadow_addr fr) (repeat (Z_to_bv 8 0) (Z.to_nat n)) /\ addressable m' fr L
  /\ stk rsegs m' fr (fr + B) /\ (forall a, fr <= a < fr + B -> app_mem a)
  /\ FS <= fr /\ fr + B <= FS + FS_SIZE /\ ASAN_GT <= fr /\ fr + B <= bv_unsigned sp - K
  /\ (forall (c' : nat) (j' : Z), (c' <= 10)%nat -> 0 <= j' < fs_M c' -> (c' <> c \/ j' <> j) ->
        fs_frame FS c' j' + fs_B c' <= fr \/ fr + B <= fs_frame FS c' j')
  /\ munch [(fs_hint FS c, fs_hint FS c + 8); (fs_flag FS c j, fs_flag FS c j + 1); (fr + 24, fr + 32);
            (fr + B - 8, fr + B); (shadow_addr fr, shadow_addr fr + n); (bv_unsigned sp - K, bv_unsigned sp)] m m'.

Definition asan_stack_malloc_post (c : nat) (K : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (L FS : Z) (h : word) (flags : list byte) (lo : Z) (m : word -> option byte)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ fs_place m' FS /\ (exists h', bytes_at rsegs m' (fs_hint FS c) (le8 h'))
    /\ ((Forall (fun b => b = Z_to_bv 8 1) flags /\ a0 = Z_to_bv 64 0
         /\ munch [(fs_hint FS c, fs_hint FS c + 8); (bv_unsigned sp - K, bv_unsigned sp)] m m')
        \/ (exists i, 0 <= i < fs_M c
            /\ (forall i', 0 <= i' < i ->
                  nth_error flags (Z.to_nat ((bv_unsigned h + i') mod fs_M c)) = Some (Z_to_bv 8 1))
            /\ nth_error flags (Z.to_nat ((bv_unsigned h + i) mod fs_M c)) = Some (Z_to_bv 8 0)
            /\ asan_stack_malloc_frame c K sp L FS ((bv_unsigned h + i) mod fs_M c) a0 m m')).

Definition asan_stack_malloc_contract (c : nat) (entry K : Z) : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS : Z) (h DT TS C T DB : word) (k : Z) (flags : list byte),
  let L := bv_unsigned a0 in let TP := bv_unsigned tp in let S0 := bv_unsigned sp in
  1 <= L <= fs_B c -> L mod 8 = 0 ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  asan_tls_cells m TP DT TS C T DB k ->
  ((7 <= c)%nat -> bytes_at rsegs m (CF + 120) (le8 (Z_to_bv 64 (2 ^ 64 - 1)))) ->
  bytes_at rsegs m TP (le8 (Z_to_bv 64 FS)) -> fs_place m FS ->
  bytes_at rsegs m (FS + 88) (le8 (Z_to_bv 64 20)) -> bytes_at rsegs m (FS + 96) [Z_to_bv 8 0] ->
  bytes_at rsegs m (fs_hint FS c) (le8 h) ->
  bytes_at rsegs m (fs_flag FS c 0) flags -> Z.of_nat (length flags) = fs_M c ->
  Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  stk rsegs m lo S0 -> lo + K <= S0 -> FS + FS_SIZE <= S0 - K -> (forall a, S0 - K <= a < S0 -> app_mem a) ->
  disjoint_from [(TP - 88, TP - 80); (TP - 8, TP + 16); (bv_unsigned DT + 8, bv_unsigned DT + 16);
                 (bv_unsigned TS + 8 * k, bv_unsigned TS + 8 * k + 8); (bv_unsigned C + 152, bv_unsigned C + 160);
                 (bv_unsigned T + 48, bv_unsigned T + 64); (bv_unsigned DB + 24, bv_unsigned DB + 32)] (S0 - K) K ->
  evt rsegs (asan_stack_malloc_post c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS h flags lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition asan_stack_malloc_0_contract : Prop :=
  asan_stack_malloc_contract 0 ASAN_STACK_MALLOC_0 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_1_contract : Prop :=
  asan_stack_malloc_contract 1 ASAN_STACK_MALLOC_1 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_2_contract : Prop :=
  asan_stack_malloc_contract 2 ASAN_STACK_MALLOC_2 ASAN_STACK_MALLOC_K.
Definition asan_stack_malloc_6_contract : Prop :=
  asan_stack_malloc_contract 6 ASAN_STACK_MALLOC_6 ASAN_STACK_MALLOC_K.
