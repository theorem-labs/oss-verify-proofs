(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Prelim ScanInt.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals.
Import ListNotations.
Open Scope Z_scope.

Definition A0_strlen : Z := 0x44120.
Definition A0_strncmp : Z := 0x4412c.
Definition A0_strncasecmp : Z := 0x44130.
Definition A0_strstr : Z := 0x44134.
Definition A0_memchr : Z := 0x44140.
Definition A0_sscanf : Z := 0x44160.
Definition A0_inet_pton : Z := 0x4417c.
Definition A0_strncpy : Z := 0x441c8.
Definition A0_strtoll : Z := 0x441cc.
Definition A0_strtol : Z := 0x441d0.
Definition A0_atoi : Z := 0x441d4.
Definition A0_memcpy_i : Z := 0x56aa8.
Definition A0_memset_i : Z := 0x56aa0.

Definition A0_tolower : Z := 0x94050.
Definition A0_isalnum : Z := 0x94018.
Definition A0_isxdigit : Z := 0x94034.
Definition A0_htons : Z := 0x999b4.
Definition A0_errno_location : Z := 0x94778.

Notation A0_RT_STACK2 := 8192%Z.

Section I.
Context {HC : HasCeiling}.

Definition icpt_win (A n : Z) : Prop :=
  0 <= n /\ ((4096 <= A /\ A + n <= 0x7fff7000) \/ (0x10007fff8000 <= A /\ A + n <= 2^47)).
Definition icpt_rng (A n : Z) : Prop := icpt_win A n /\ A + n < 2^47 /\ n <= 2^43.
#[using="Type"] Lemma icpt_rng_intro : forall A n, icpt_win A n -> A + n <= alloc_ceiling -> n <= 2^43 -> icpt_rng A n.
Proof. intros A n W H1 H2. pose proof alloc_ceiling_bounds. split; [exact W|]. lia. Qed.

Definition strlen_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).
Definition strlen_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (S : Z) (str slack : list byte) (lo : Z),
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) -> icpt_rng S (Z.of_nat (length str) + 1) ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
  (S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling \/ q <= S)%Z ->
  mem_inv asegs m -> a0 = wz S ->
  evt asegs (strlen_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str slack lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strlen) fc None m (seg_rom asegs)).

Definition zsign (v : Z) : Z := if v <? 0 then -1 else if 0 <? v then 1 else 0.
Definition strncmp_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A B : Z) (ls rs : list byte) (res : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz res) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ bytes_at asegs m' A ls /\ bytes_at asegs m' B rs.

Definition strncmp_stmt_A (entry : Z) (nocase : bool) : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A B n : Z) (ls rs : list byte) (v : Z) (lo : Z),
  bytes_at asegs m A ls -> bytes_at asegs m B rs ->
  (if nocase then strncasecmp_model ls rs n else strncmp_model ls rs n) = Some v ->
  accessible m A (Z.min n (Z.of_nat (length ls))) -> sh_readable m A (Z.min n (Z.of_nat (length ls))) ->
  accessible m B (Z.min n (Z.of_nat (length rs))) -> sh_readable m B (Z.min n (Z.of_nat (length rs))) ->
  icpt_rng A (Z.min n (Z.of_nat (length ls))) -> icpt_rng B (Z.min n (Z.of_nat (length rs))) ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
  (A + Z.of_nat (length ls) <= alloc_ceiling \/ q <= A)%Z -> (B + Z.of_nat (length rs) <= alloc_ceiling \/ q <= B)%Z ->
  mem_inv asegs m -> a0 = wz A -> a1 = wz B -> a2 = wz n -> 0 <= n < 2^63 ->
  evt asegs (strncmp_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A B ls rs (if nocase then v else zsign v) lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz entry) fc None m (seg_rom asegs)).

Definition memchr_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A c n : Z) (buf : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz (memchr_res A c n buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ bytes_at asegs m' A buf.
Definition memchr_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (A c n : Z) (buf : list byte) (lo : Z),
  bytes_at asegs m A buf -> memchr_ok A c n buf ->

  accessible m A (let r := memchr_res A c n buf in if r =? 0 then n else r - A + 1) ->
  sh_readable m A (let r := memchr_res A c n buf in if r =? 0 then n else r - A + 1) ->
  icpt_rng A (let r := memchr_res A c n buf in if r =? 0 then n else r - A + 1) ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
  (A + Z.of_nat (length buf) <= alloc_ceiling \/ q <= A)%Z ->
  mem_inv asegs m -> a0 = wz A -> a1 = wz c -> a2 = wz n -> 0 <= c < 256 -> 0 <= n < 2^63 ->
  evt asegs (memchr_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c n buf lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_memchr) fc None m (seg_rom asegs)).

Definition asan_memcpy_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S n lo : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + n); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' D [CB (Z.to_nat n) src] /\ bytes_at asegs m' S src.
Definition asan_memcpy_stmt (entry : Z) : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n lo : Z) (src junk : list byte),
  rw_cells asegs m D [CB (Z.to_nat n) junk] -> bytes_at asegs m S src -> Z.of_nat (length src) = n ->
  (S + n <= D \/ D + n <= S) ->
  accessible m D n -> sh_readable m D n -> accessible m S n -> sh_readable m S n -> icpt_rng D n -> icpt_rng S n ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
  (D + n <= alloc_ceiling \/ q <= D) -> env_safe [(D, D + n)] -> (S + n <= alloc_ceiling \/ q <= S) ->
  mem_inv asegs m -> a0 = wz D -> a1 = wz S -> a2 = wz n -> 0 <= n ->
  evt asegs (asan_memcpy_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n lo src m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz entry) fc None m (seg_rom asegs)).

Definition asan_memmove_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S n U lo : Z) (us : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(D, D + n); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ u8arr asegs m' U (upd_bytes us (Z.to_nat (D - U)) (firstn (Z.to_nat n) (skipn (Z.to_nat (S - U)) us))).
Definition asan_memmove_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n U lo : Z) (us : list byte),
  u8arr asegs m U us -> (U <= S /\ S + n <= U + Z.of_nat (length us)) -> (U <= D /\ D + n <= U + Z.of_nat (length us)) ->
  accessible m D n -> sh_readable m D n -> accessible m S n -> sh_readable m S n -> icpt_rng D n -> icpt_rng S n ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
  0x609000 <= U -> U + Z.of_nat (length us) <= alloc_ceiling ->
  mem_inv asegs m -> a0 = wz D -> a1 = wz S -> a2 = wz n -> 0 <= n < 2^40 ->
  evt asegs (asan_memmove_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n U lo us m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_asan_memmove) fc None m (seg_rom asegs)).

Definition asan_memset_post2 (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P c n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(P, P + n); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' P [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].
Definition asan_memset_stmt2 (entry : Z) : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (P c n lo : Z) (junk : list byte),
  rw_cells asegs m P [CB (Z.to_nat n) junk] -> accessible m P n -> sh_readable m P n -> icpt_rng P n ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
  (P + n <= alloc_ceiling \/ q <= P) -> env_safe [(P, P + n)] ->
  mem_inv asegs m -> a0 = wz P -> a1 = wz c -> a2 = wz n -> 0 <= n -> 0 <= c < 256 ->
  evt asegs (asan_memset_post2 ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P c n lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz entry) fc None m (seg_rom asegs)).

Definition leaf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (res : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs)
    /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m.
Definition tolower_stmt_A : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc m (c : Z),
  0 <= c < 256 -> a0 = wz c -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (to_lower c) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A0_tolower) fc None m (seg_rom asegs)).
Definition htons_stmt_A : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc m,
  (bv_unsigned a0 < 65536)%Z -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (htons_z (bv_unsigned a0)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A0_htons) fc None m (seg_rom asegs)).
Definition errno_location_stmt_A : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc m,
  (164 <= bv_unsigned tp)%Z -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned tp - 164) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz A0_errno_location) fc None m (seg_rom asegs)).

Definition A0_read : Z := 0x44148.
Definition A0_fwrite : Z := 0x4414c.
Notation REAL_read := 690820%Z.
Notation REAL_fwrite := 635068%Z.
Notation READ_RESUME := 290504%Z.
Notation FWRITE_RESUME := 291140%Z.

Definition read_front_post (q : Z) (gp tp : word) (fd buf cnt : Z) (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk : list byte),
    ms' = MS (mkR (wz READ_RESUME) (wz (q - 2128)) gp tp t0 t1 t2 (wz q) (wz buf) (wz fd) (wz buf) (wz cnt) a3 a4 a5 a6 a7
                 (wz cnt) (wz fd) (wz 1) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz REAL_read) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q - 2128) /\ asan_env asegs m'
    /\ rw_cells asegs m' (q - 2128) [CB 2080 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0].
Definition read_front_stmt : Prop :=
  forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (fd buf cnt lo : Z),
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 2128 - 64 -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz fd -> a1 = wz buf -> a2 = wz cnt ->
  evt asegs (read_front_post q gp tp fd buf cnt ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_read) fc None m (seg_rom asegs)).

Definition icpt_back_post (ra0 : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (res lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 (wz res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'.
Definition read_back_stmt : Prop :=
  forall (ra0 s0 s1 s2 s3 s4 : word) (q : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (fd buf cnt res lo : Z) (junk : list byte),
  rw_cells asegs m (q - 2128) [CB 2080 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
  asan_env asegs m -> stk asegs m lo (q - 2128) -> alloc_ceiling <= lo -> lo <= q - 2128 - A0_RT_STACK -> q < 2^64 ->
  (0 < res -> res <= cnt /\ accessible m buf res /\ sh_readable m buf res /\ icpt_rng buf res) -> - 2^63 <= res < 2^63 -> 0 <= cnt < 2^63 ->
  (buf + cnt <= alloc_ceiling \/ q <= buf) -> 0 <= buf ->
  mem_inv asegs m ->
  evt asegs (icpt_back_post ra0 q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m)
    (MS (mkR (wz READ_RESUME) (wz (q - 2128)) gp tp t0 t1 t2 (wz q) (wz buf) (wz res) a1 a2 a3 a4 a5 a6 a7
             (wz cnt) (wz fd) (wz 1) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz READ_RESUME) fc None m (seg_rom asegs)).

Definition fwrite_front_post (q : Z) (gp tp : word) (p sz nm f : Z) (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk : list byte),
    ms' = MS (mkR (wz FWRITE_RESUME) (wz (q - 2128)) gp tp t0 t1 t2 (wz q) (wz sz) (wz p) (wz sz) (wz nm) (wz f) a4 a5 a6 a7
                 (wz p) (wz f) (wz nm) (wz 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz REAL_fwrite) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q - 2128) /\ asan_env asegs m'
    /\ rw_cells asegs m' (q - 2128) [CB 2072 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0].
Definition fwrite_front_stmt : Prop :=
  forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (p sz nm f lo : Z),
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 2128 - 64 -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz p -> a1 = wz sz -> a2 = wz nm -> a3 = wz f ->
  evt asegs (fwrite_front_post q gp tp p sz nm f ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_fwrite) fc None m (seg_rom asegs)).
Definition fwrite_back_stmt : Prop :=
  forall (ra0 s0 s1 s2 s3 s4 s5 : word) (q : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (p sz nm f r lo : Z) (junk : list byte),
  rw_cells asegs m (q - 2128) [CB 2072 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
  asan_env asegs m -> stk asegs m lo (q - 2128) -> alloc_ceiling <= lo -> lo <= q - 2128 - A0_RT_STACK -> q < 2^64 ->
  0 <= r <= nm -> 0 <= sz -> r * sz < 2^40 -> (0 < r * sz -> accessible m p (r * sz) /\ sh_readable m p (r * sz) /\ icpt_rng p (r * sz)) ->
  (p + nm * sz <= alloc_ceiling \/ q <= p) -> 0 <= p < 2^64 ->
  mem_inv asegs m ->
  evt asegs (icpt_back_post ra0 q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r lo m)
    (MS (mkR (wz FWRITE_RESUME) (wz (q - 2128)) gp tp t0 t1 t2 (wz q) (wz sz) (wz r) a1 a2 a3 a4 a5 a6 a7
             (wz p) (wz f) (wz nm) (wz 1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FWRITE_RESUME) fc None m (seg_rom asegs)).

Definition A0_vprintf : Z := 0x44164.
Definition A0_vfprintf : Z := 0x44168.
Definition A0_fprintf : Z := 0x44170.
Notation REAL_vprintf := 661032%Z.
Notation REAL_vfprintf := 635716%Z.
Notation VPRINTF_RESUME := 297444%Z.
Notation VFPRINTF_RESUME := 300372%Z.
Notation FPRINTF_RESUME := 301424%Z.
Notation A0_FMT_E := 84283%Z.
Notation A0_FMT_F1 := 88516%Z.
Notation A0_FMT_F2 := 121501%Z.
Notation A0_FMT_F3 := 121522%Z.
Notation A0_FMT_F4 := 104842%Z.

Definition fmt_pct_s (fmt flen : Z) : Prop := (fmt = A0_FMT_F1 /\ flen = 17) \/ (fmt = A0_FMT_F2 /\ flen = 21) \/ (fmt = A0_FMT_F3 /\ flen = 23).

Definition vprintf_front_post (q : Z) (gp tp : word) (ap : Z) (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk : list byte),
    ms' = MS (mkR (wz VPRINTF_RESUME) (wz (q - 48)) gp tp t0 t1 t2 (wz A0_FMT_E) (wz ap) (wz A0_FMT_E) (wz ap) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz REAL_vprintf) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q - 48) /\ asan_env asegs m'
    /\ rw_cells asegs m' (q - 48) [CB 8 junk; C8 (wz ap); C8 (wz ap); C8 s1; C8 s0; C8 ra0].
Definition vprintf_front_stmt : Prop :=
  forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (ap lo : Z) (argw : word),
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 48 - A0_RT_STACK -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz A0_FMT_E -> a1 = wz ap ->
  rw_cells asegs m ap [C8 argw] -> (ap + 8 <= alloc_ceiling \/ q <= ap) -> 0 <= ap -> ap mod 8 = 0 ->
  accessible m A0_FMT_E 4 -> sh_readable m A0_FMT_E 4 ->
  evt asegs (vprintf_front_post q gp tp ap ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_vprintf) fc None m (seg_rom asegs)).
Definition vprintf_back_stmt : Prop :=
  forall (ra0 s0 s1 : word) (q : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x8 x9 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (ap res lo : Z) (junk : list byte),
  rw_cells asegs m (q - 48) [CB 8 junk; C8 (wz ap); C8 (wz ap); C8 s1; C8 s0; C8 ra0] ->
  stk asegs m lo (q - 48) -> alloc_ceiling <= lo -> q < 2^64 -> asan_env asegs m -> mem_inv asegs m ->
  evt asegs (icpt_back_post ra0 q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m)
    (MS (mkR (wz VPRINTF_RESUME) (wz (q - 48)) gp tp t0 t1 t2 x8 x9 (wz res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz VPRINTF_RESUME) fc None m (seg_rom asegs)).

Definition vfprintf_front_post (q : Z) (gp tp : word) (stream ap : Z) (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (wz VFPRINTF_RESUME) (wz (q - 48)) gp tp t0 t1 t2 (wz A0_FMT_E) (wz stream) (wz stream) (wz A0_FMT_E) (wz ap) a3 a4 a5 a6 a7
                 (wz ap) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz REAL_vfprintf) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q - 48) /\ asan_env asegs m'
    /\ rw_cells asegs m' (q - 48) [C8 (wz ap); C8 (wz ap); C8 s2; C8 s1; C8 s0; C8 ra0].
Definition vfprintf_front_stmt : Prop :=
  forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (stream ap lo : Z) (argw : word),
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 48 - A0_RT_STACK -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz stream -> a1 = wz A0_FMT_E -> a2 = wz ap -> 0 <= stream < 2^64 ->
  rw_cells asegs m ap [C8 argw] -> (ap + 8 <= alloc_ceiling \/ q <= ap) -> 0 <= ap -> ap mod 8 = 0 ->
  accessible m A0_FMT_E 4 -> sh_readable m A0_FMT_E 4 ->
  evt asegs (vfprintf_front_post q gp tp stream ap ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_vfprintf) fc None m (seg_rom asegs)).
Definition vfprintf_back_stmt : Prop :=
  forall (ra0 s0 s1 s2 : word) (q : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x8 x9 x18 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (ap res lo : Z),
  rw_cells asegs m (q - 48) [C8 (wz ap); C8 (wz ap); C8 s2; C8 s1; C8 s0; C8 ra0] ->
  stk asegs m lo (q - 48) -> alloc_ceiling <= lo -> q < 2^64 -> asan_env asegs m -> mem_inv asegs m ->
  evt asegs (icpt_back_post ra0 q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m)
    (MS (mkR (wz VFPRINTF_RESUME) (wz (q - 48)) gp tp t0 t1 t2 x8 x9 (wz res) a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz VFPRINTF_RESUME) fc None m (seg_rom asegs)).

Definition fprintf_front_post (q : Z) (gp tp : word) (stream fmt : Z) (a2 a3 a4 a5 a6 a7 : word) (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' (junk : list byte) (aq : word),
    ms' = MS (mkR (wz FPRINTF_RESUME) (wz (q - 112)) gp tp t0 t1 t2 (wz fmt) (wz stream) (wz stream) (wz fmt) (wz (q - 48)) x13 x14 x15 x16 x17
                 (wz (q - 48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz REAL_vfprintf) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (q - 112) /\ asan_env asegs m'
    /\ rw_cells asegs m' (q - 112) [CB 8 junk; C8 (wz (q - 48)); C8 aq; C8 (wz (q - 48)); C8 s2; C8 s1; C8 s0; C8 ra0;
                                  C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].
Definition fprintf_s_front_stmt (fmt flen : Z) : Prop :=
  forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (stream S lo : Z) (sbuf : list byte),
  fmt_pct_s fmt flen ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 112 - A0_RT_STACK -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz stream -> a1 = wz fmt -> a2 = wz S -> 0 <= stream < 2^64 ->
  accessible m fmt flen -> sh_readable m fmt flen ->
  bytes_at asegs m S (sbuf ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sbuf -> 0 < S ->
  (S + Z.of_nat (length sbuf) + 1 <= alloc_ceiling \/ q <= S) ->
  accessible m S (Z.of_nat (length sbuf) + 1) -> sh_readable m S (Z.of_nat (length sbuf) + 1) -> icpt_rng S (Z.of_nat (length sbuf) + 1) ->
  evt asegs (fprintf_front_post q gp tp stream fmt a2 a3 a4 a5 a6 a7 ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_fprintf) fc None m (seg_rom asegs)).
Definition fprintf_u_front_stmt : Prop :=
  forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (stream lo : Z),
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 112 - A0_RT_STACK -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz stream -> a1 = wz A0_FMT_F4 -> 0 <= stream < 2^64 ->
  accessible m A0_FMT_F4 33 -> sh_readable m A0_FMT_F4 33 ->
  evt asegs (fprintf_front_post q gp tp stream A0_FMT_F4 a2 a3 a4 a5 a6 a7 ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_fprintf) fc None m (seg_rom asegs)).
Definition fprintf_back_stmt : Prop :=
  forall (ra0 s0 s1 s2 : word) (q : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x8 x9 x18 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (res lo : Z) (cells : list cell),
  rw_cells asegs m (q - 112) cells -> cells_size cells = 112%nat ->
  nth_error cells 4 = Some (C8 s2) -> nth_error cells 5 = Some (C8 s1) -> nth_error cells 6 = Some (C8 s0) -> nth_error cells 7 = Some (C8 ra0) ->
  firstn 4 (map csize cells) = [8; 8; 8; 8]%nat ->
  stk asegs m lo (q - 112) -> alloc_ceiling <= lo -> q < 2^64 -> asan_env asegs m -> mem_inv asegs m ->
  evt asegs (icpt_back_post ra0 q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m)
    (MS (mkR (wz FPRINTF_RESUME) (wz (q - 112)) gp tp t0 t1 t2 x8 x9 (wz res) a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FPRINTF_RESUME) fc None m (seg_rom asegs)).

Definition A0_asan_dtor : Z := 0x8b360.
Definition dtor_W : list ivl :=
  map (fun g => match g with (b, srz, _) => (sh b, sh (b + srz)) end) A0_GLOBALS
  ++ flat_map (fun g => match g with (_, _, odr) => if odr =? 0 then [] else [(odr, odr + 1)] end) A0_GLOBALS
  ++ [(A0_GLOBALS_FLAG, A0_GLOBALS_FLAG + 8)]
  ++ [(0xb11b0, 0xb11b8); (sh 0xaedc0, sh 0xb0240)].
Definition asan_dtor_post (ra0 : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch ((lo, q) :: dtor_W) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'.
Definition asan_dtor_stmt : Prop :=
  forall (ra0 : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 -> mem_inv asegs m ->

  Forall (fun g => match g with (b, srz, _) => exists bs, rw_cells asegs m (sh b) [CB (Z.to_nat (srz / 8)) bs] end) A0_GLOBALS ->
  (exists bs, rw_cells asegs m (sh 0xaedc0) [CB 656 bs]) ->
  evt asegs (asan_dtor_post ra0 q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra0 (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_asan_dtor) fc None m (seg_rom asegs)).

Definition A0_got_ssp : Z := 0xaad68.
Definition A0_ssp_guard : Z := 0x6069b0.

Definition A0_STRTOL_DEPTH : Z := 4096.
Definition strtol_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (E : Z) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (k : Z),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (E, E + 8); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' A0_got_ssp [C8 (wz A0_ssp_guard)] /\ rw_cells asegs m' A0_ssp_guard [C8 canary]
    /\ rw_cells asegs m' (bv_unsigned tp - 164) [C4 errv']
    /\ 0 <= k <= Z.of_nat (length str)
    /\ rw_cells asegs m' E [C8 (wz (S + k))].
Definition strtol_stmt_A : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (S : Z) (str : list byte) (E base : Z) (ejunk : list byte) (errv canary : word) (lo q : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) ->
  rw_cells asegs m E [CB 8 ejunk] ->
  rw_cells asegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
  asan_env asegs m ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) -> icpt_win S (Z.of_nat (length str) + 1) ->
  Z.of_nat (length str) + 1 <= 2^40 ->
  accessible m E 8 -> sh_readable m E 8 -> icpt_win E 8 ->
  (base = 10 \/ base = 16) ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_STRTOL_DEPTH -> q < 2^63 ->
  4096 + 164 <= bv_unsigned tp -> bv_unsigned tp - 160 <= 0x609000 ->
  bv_unsigned tp = 0x5e6970 ->
  0x609000 <= S -> S + Z.of_nat (length str) + 1 <= alloc_ceiling ->
  0x609000 <= E -> E + 8 <= alloc_ceiling -> E mod 8 = 0 ->
  (E + 8 <= S \/ S + Z.of_nat (length str) + 1 <= E) ->
  mem_inv asegs m -> a0 = wz S -> a1 = wz E -> a2 = wz base ->
  evt asegs (strtol_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str E canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strtol) fc None m (seg_rom asegs)).

Definition A0_FMT_SSCANF : Z := 0x218a0.
Definition A0_SSCANF_DEPTH : Z := 16384.
Definition zbytes_A (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition rtext_A (T : Z) (txt pre post : list Z) : Prop :=
  txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
  ((- (T + Prelim.zlength pre + 1)) mod 8 <= Prelim.zlength post)%Z /\ (Prelim.zlength txt <= 2^40)%Z.
Definition A0_ERRNO : Z := 0x5e68cc.
Definition sscanf3_post_A (rax : word) (qx : Z) (gpx tpx x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (Fx : bvmap 5 word) (fcx : bv 32)
    (txt pre : list Z) (P1 P2 P3 lox : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ev' v1 v2 v3 : word) (r : Z),
    ms' = MS (mkR rax (wz qx) gpx tpx t0 t1 t2 x8 x9 (wz r) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             Fx (ret_pc rax) fcx None m' (seg_rom asegs)
    /\ munch [(lox, qx); (P1, P1 + 4); (P2, P2 + 4); (P3, P3 + 4); (A0_ERRNO, A0_ERRNO + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lox qx /\ asan_env asegs m'
    /\ accessible m' lox (qx - lox) /\ sh_readable m' lox (qx - lox)
    /\ ScanInt.sscanf_model ScanInt.FMT_STATUSLINE txt (Prelim.zlength pre) = Some r /\ (r = -1 \/ 0 <= r <= 3)
    /\ rw_cells asegs m' A0_got_ssp [C8 (wz A0_ssp_guard)] /\ rw_cells asegs m' A0_ssp_guard [C8 canary]
    /\ rw_cells asegs m' A0_ERRNO [C4 ev']
    /\ rw_cells asegs m' P1 [C4 v1] /\ rw_cells asegs m' P2 [C4 v2] /\ rw_cells asegs m' P3 [C4 v3].

Definition sscanf_status_stmt_A : Prop :=
  forall (rax : word) (qx : Z) (gpx tpx t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
         (Fx : bvmap 5 word) (fcx : bv 32) (m : mem) (T : Z) (txt pre post : list Z) (P1 P2 P3 : Z) (v1 v2 v3 ev canary : word) (lox : Z),
  rtext_A T txt pre post -> bytes_at asegs m T (zbytes_A txt) ->
  accessible m T (Prelim.zlength pre + 1) -> sh_readable m T (Prelim.zlength pre + 1) -> icpt_win T (Prelim.zlength pre + 1) -> Prelim.zlength pre + 1 <= 2^43 ->
  accessible m A0_FMT_SSCANF 11 -> sh_readable m A0_FMT_SSCANF 11 ->
  accessible m P1 4 -> sh_readable m P1 4 -> icpt_win P1 4 ->
  accessible m P2 4 -> sh_readable m P2 4 -> icpt_win P2 4 ->
  accessible m P3 4 -> sh_readable m P3 4 -> icpt_win P3 4 ->
  stk asegs m lox qx -> mem_inv asegs m -> asan_env asegs m ->
  alloc_ceiling <= lox -> lox <= qx - A0_SSCANF_DEPTH -> qx mod 16 = 0 -> qx < 2^64 ->

  qx <= 2^47 -> accessible m lox (qx - lox) -> sh_readable m lox (qx - lox) ->
  tpx = wz 6187376 ->
  0x609000 <= T -> T + Prelim.zlength txt <= alloc_ceiling ->
  (0x609000 <= P1 /\ P1 + 4 <= alloc_ceiling) -> (0x609000 <= P2 /\ P2 + 4 <= alloc_ceiling) -> (0x609000 <= P3 /\ P3 + 4 <= alloc_ceiling) ->
  (P1 + 4 <= T \/ T + Prelim.zlength txt <= P1) -> (P2 + 4 <= T \/ T + Prelim.zlength txt <= P2) -> (P3 + 4 <= T \/ T + Prelim.zlength txt <= P3) ->
  (P1 + 4 <= P2 \/ P2 + 4 <= P1) -> (P1 + 4 <= P3 \/ P3 + 4 <= P1) -> (P2 + 4 <= P3 \/ P3 + 4 <= P2) ->
  rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
  rw_cells asegs m A0_ERRNO [C4 ev] ->
  rw_cells asegs m P1 [C4 v1] -> rw_cells asegs m P2 [C4 v2] -> rw_cells asegs m P3 [C4 v3] ->
  a0 = wz T -> a1 = wz A0_FMT_SSCANF -> a2 = wz P1 -> a3 = wz P2 -> a4 = wz P3 ->
  evt asegs (sscanf3_post_A rax qx gpx tpx x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Fx fcx txt pre P1 P2 P3 lox canary m)
      (MS (mkR rax (wz qx) gpx tpx t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          Fx (wz A0_sscanf) fcx None m (seg_rom asegs)).

Definition A0_FMT_SSCANF_VER : Z := 0x21ae0.
Definition sscanf2_post_A (rax : word) (qx : Z) (gpx tpx x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) (Fx : bvmap 5 word) (fcx : bv 32)
    (txt pre : list Z) (P1 P2 lox : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (ev' v1 v2 : word) (r : Z),
    ms' = MS (mkR rax (wz qx) gpx tpx t0 t1 t2 x8 x9 (wz r) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
             Fx (ret_pc rax) fcx None m' (seg_rom asegs)
    /\ munch [(lox, qx); (P1, P1 + 4); (P2, P2 + 4); (A0_ERRNO, A0_ERRNO + 4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lox qx /\ asan_env asegs m'
    /\ accessible m' lox (qx - lox) /\ sh_readable m' lox (qx - lox)
    /\ ScanInt.sscanf_model ScanInt.FMT_VERSION txt (Prelim.zlength pre) = Some r /\ (r = -1 \/ 0 <= r <= 2)
    /\ rw_cells asegs m' A0_got_ssp [C8 (wz A0_ssp_guard)] /\ rw_cells asegs m' A0_ssp_guard [C8 canary]
    /\ rw_cells asegs m' A0_ERRNO [C4 ev']
    /\ rw_cells asegs m' P1 [C4 v1] /\ rw_cells asegs m' P2 [C4 v2].

Definition sscanf_version_stmt_A : Prop :=
  forall (rax : word) (qx : Z) (gpx tpx t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
         (Fx : bvmap 5 word) (fcx : bv 32) (m : mem) (T : Z) (txt pre post : list Z) (P1 P2 : Z) (v1 v2 ev canary : word) (lox : Z),
  rtext_A T txt pre post -> bytes_at asegs m T (zbytes_A txt) ->
  accessible m T (Prelim.zlength pre + 1) -> sh_readable m T (Prelim.zlength pre + 1) -> icpt_win T (Prelim.zlength pre + 1) -> Prelim.zlength pre + 1 <= 2^43 ->
  accessible m A0_FMT_SSCANF_VER 8 -> sh_readable m A0_FMT_SSCANF_VER 8 ->
  accessible m P1 4 -> sh_readable m P1 4 -> icpt_win P1 4 ->
  accessible m P2 4 -> sh_readable m P2 4 -> icpt_win P2 4 ->
  stk asegs m lox qx -> mem_inv asegs m -> asan_env asegs m ->
  alloc_ceiling <= lox -> lox <= qx - A0_SSCANF_DEPTH -> qx mod 16 = 0 -> qx < 2^64 ->

  qx <= 2^47 -> accessible m lox (qx - lox) -> sh_readable m lox (qx - lox) ->
  tpx = wz 6187376 ->
  0x609000 <= T -> T + Prelim.zlength txt <= alloc_ceiling ->
  (0x609000 <= P1 /\ P1 + 4 <= alloc_ceiling) -> (0x609000 <= P2 /\ P2 + 4 <= alloc_ceiling) ->
  (P1 + 4 <= T \/ T + Prelim.zlength txt <= P1) -> (P2 + 4 <= T \/ T + Prelim.zlength txt <= P2) ->
  (P1 + 4 <= P2 \/ P2 + 4 <= P1) ->
  rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
  rw_cells asegs m A0_ERRNO [C4 ev] ->
  rw_cells asegs m P1 [C4 v1] -> rw_cells asegs m P2 [C4 v2] ->
  a0 = wz T -> a1 = wz A0_FMT_SSCANF_VER -> a2 = wz P1 -> a3 = wz P2 ->
  evt asegs (sscanf2_post_A rax qx gpx tpx x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 Fx fcx txt pre P1 P2 lox canary m)
      (MS (mkR rax (wz qx) gpx tpx t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          Fx (wz A0_sscanf) fcx None m (seg_rom asegs)).

Definition stpn_k_A (str : list byte) (n : nat) : nat := Nat.min (length str) n.
Definition stpn_result_A (str : list byte) (n : nat) : list byte :=
  firstn (stpn_k_A str n) str ++ repeat (Z_to_bv 8 0) (n - stpn_k_A str n).

Definition strncpy_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S n : Z) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (D, D + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ rw_cells asegs m' D [CB (Z.to_nat n) (stpn_result_A str (Z.to_nat n))]
    /\ bytes_at asegs m' S (str ++ Z_to_bv 8 0 :: slack).
Definition strncpy_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (D S n : Z) (str slack djunk : list byte) (lo : Z),
  rw_cells asegs m D [CB (Z.to_nat n) djunk] -> 0 <= n < 2^31 ->
  bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  accessible m S (Z.min n (Z.of_nat (length str) + 1)) -> sh_readable m S (Z.min n (Z.of_nat (length str) + 1)) -> icpt_win S (Z.min n (Z.of_nat (length str) + 1)) ->
  accessible m D n -> sh_readable m D n -> icpt_win D n ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 2 * A0_RT_STACK
   -> q < 2^64 ->
  0x609000 <= D -> D + n <= alloc_ceiling -> 4096 <= S -> S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
  (D + n <= S \/ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= D) ->
  mem_inv asegs m -> a0 = wz D -> a1 = wz S -> a2 = wz n ->
  evt asegs (strncpy_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S n str slack lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strncpy) fc None m (seg_rom asegs)).

Definition inet_pton_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (A : Z) (N : nat) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (outs : list byte),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (A, A + Z.of_nat N)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ accessible m' lo (q - lo) /\ sh_readable m' lo (q - lo)
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' A0_got_ssp [C8 (wz A0_ssp_guard)] /\ rw_cells asegs m' A0_ssp_guard [C8 canary]
    /\ rw_cells asegs m' A [CB N outs]
    /\ (r = 0 \/ r = 1).
Definition inet_pton_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (af S A : Z) (str ojunk : list byte) (N : nat) (canary : word) (lo : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str ->
  rw_cells asegs m A [CB N ojunk] ->
  ((af = 2 /\ 4 <= Z.of_nat N) \/ (af = 10 /\ N = 16%nat)) ->
  rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) -> icpt_win S (Z.of_nat (length str) + 1) ->
  Z.of_nat (length str) + 1 <= 2^43 ->
  accessible m A (Z.of_nat N) -> sh_readable m A (Z.of_nat N) -> icpt_win A (Z.of_nat N) ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 2 * A0_RT_STACK -> q < 2^64 ->

  q <= 2^47 -> accessible m lo (q - lo) -> sh_readable m lo (q - lo) ->
  0x609000 <= S -> S + Z.of_nat (length str) + 1 <= alloc_ceiling -> 0x609000 <= A -> A + Z.of_nat N <= alloc_ceiling ->
  (A + Z.of_nat N <= S \/ S + Z.of_nat (length str) + 1 <= A) ->
  mem_inv asegs m -> a0 = wz af -> a1 = wz S -> a2 = wz A ->
  evt asegs (inet_pton_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str A N canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_inet_pton) fc None m (seg_rom asegs)).

Definition strtol0_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (S : Z) (str : list byte) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ bytes_at asegs m' S (str ++ [Z_to_bv 8 0])
    /\ rw_cells asegs m' A0_got_ssp [C8 (wz A0_ssp_guard)] /\ rw_cells asegs m' A0_ssp_guard [C8 canary]
    /\ rw_cells asegs m' (bv_unsigned tp - 164) [C4 errv'].
Definition strtol0_stmt_A : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (S : Z) (str : list byte) (errv canary : word) (lo q : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) ->
  rw_cells asegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
  asan_env asegs m ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) -> icpt_win S (Z.of_nat (length str) + 1) ->
  Z.of_nat (length str) + 1 <= 2^40 ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_STRTOL_DEPTH -> q < 2^63 ->
  4096 + 164 <= bv_unsigned tp -> bv_unsigned tp - 160 <= 0x609000 ->
  bv_unsigned tp = 0x5e6970 ->
  0x609000 <= S -> S + Z.of_nat (length str) + 1 <= alloc_ceiling ->
  mem_inv asegs m -> a0 = wz S -> a1 = wz 0 -> a2 = wz 10 ->
  evt asegs (strtol0_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strtol) fc None m (seg_rom asegs)).

Definition atoi_stmt_A : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (S : Z) (str : list byte) (errv canary : word) (lo q : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str ->
  rw_cells asegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
  asan_env asegs m ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) -> icpt_win S (Z.of_nat (length str) + 1) ->
  Z.of_nat (length str) + 1 <= 2^40 ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^63 ->
  4096 + 164 <= bv_unsigned tp -> bv_unsigned tp - 160 <= 0x609000 ->
  bv_unsigned tp = 0x5e6970 ->
  0x609000 <= S -> S + Z.of_nat (length str) + 1 <= alloc_ceiling ->
  mem_inv asegs m -> a0 = wz S ->
  evt asegs (strtol0_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_atoi) fc None m (seg_rom asegs)).

Definition A0_CHUNKED : Z := 0x21900.
Definition A0_STRSTR_DEPTH : Z := 8192.

Definition strstr_chunked_post_A (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (H : Z) (hay slack : list byte) (canary : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ asan_env asegs m'
    /\ bytes_at asegs m' H (hay ++ Z_to_bv 8 0 :: slack)
    /\ rw_cells asegs m' A0_got_ssp [C8 (wz A0_ssp_guard)] /\ rw_cells asegs m' A0_ssp_guard [C8 canary]
    /\ (r = 0 \/ H <= r <= H + Z.of_nat (length hay)).
Definition strstr_chunked_stmt_A : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (H : Z) (hay slack : list byte) (canary : word) (lo : Z),
  bytes_at asegs m H (hay ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) hay ->
  (- (H + Z.of_nat (length hay) + 1)) mod 8 <= Z.of_nat (length slack) ->
  rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
  accessible m H (Z.of_nat (length hay) + 1) -> sh_readable m H (Z.of_nat (length hay) + 1) -> icpt_win H (Z.of_nat (length hay) + 1) -> Z.of_nat (length hay) + 1 <= 2^43 ->
  accessible m A0_CHUNKED 8 -> sh_readable m A0_CHUNKED 8 ->
  asan_env asegs m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_STRSTR_DEPTH -> q < 2^64 ->
  0x609000 <= H -> H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= alloc_ceiling ->
  mem_inv asegs m -> a0 = wz H -> a1 = wz A0_CHUNKED ->
  evt asegs (strstr_chunked_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H hay slack canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strstr) fc None m (seg_rom asegs)).

Definition strtoll_stmt_A : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (S : Z) (str : list byte) (E : Z) (ejunk : list byte) (errv canary : word) (lo q : Z),
  bytes_at asegs m S (str ++ [Z_to_bv 8 0]) ->
  rw_cells asegs m E [CB 8 ejunk] ->
  rw_cells asegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells asegs m A0_got_ssp [C8 (wz A0_ssp_guard)] -> rw_cells asegs m A0_ssp_guard [C8 canary] ->
  asan_env asegs m ->
  accessible m S (Z.of_nat (length str) + 1) -> sh_readable m S (Z.of_nat (length str) + 1) -> icpt_win S (Z.of_nat (length str) + 1) ->
  Z.of_nat (length str) + 1 <= 2^40 ->
  accessible m E 8 -> sh_readable m E 8 -> icpt_win E 8 ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_STRTOL_DEPTH -> q < 2^63 ->
  4096 + 164 <= bv_unsigned tp -> bv_unsigned tp - 160 <= 0x609000 ->
  bv_unsigned tp = 0x5e6970 ->
  0x609000 <= S -> S + Z.of_nat (length str) + 1 <= alloc_ceiling ->
  0x609000 <= E -> E + 8 <= alloc_ceiling -> E mod 8 = 0 ->
  (E + 8 <= S \/ S + Z.of_nat (length str) + 1 <= E) ->
  mem_inv asegs m -> a0 = wz S -> a1 = wz E -> a2 = wz 10 ->
  evt asegs (strtol_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc S str E canary lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_strtoll) fc None m (seg_rom asegs)).

Record icpt_contracts := mkIC {
  ic_strlen : strlen_stmt_A;
  ic_strncmp : strncmp_stmt_A A0_strncmp false;
  ic_strncasecmp : strncmp_stmt_A A0_strncasecmp true;
  ic_memchr : memchr_stmt_A;
  ic_memcpy : asan_memcpy_stmt A0_asan_memcpy;
  ic_memcpy_i : asan_memcpy_stmt A0_memcpy_i;
  ic_memmove : asan_memmove_stmt;
  ic_memset : asan_memset_stmt2 A0_asan_memset;
  ic_memset_i : asan_memset_stmt2 A0_memset_i;
  ic_tolower : tolower_stmt_A;
  ic_htons : htons_stmt_A;
  ic_errno_location : errno_location_stmt_A;
  ic_read_front : read_front_stmt; ic_read_back : read_back_stmt;
  ic_fwrite_front : fwrite_front_stmt; ic_fwrite_back : fwrite_back_stmt;
  ic_vprintf_front : vprintf_front_stmt; ic_vprintf_back : vprintf_back_stmt;
  ic_vfprintf_front : vfprintf_front_stmt; ic_vfprintf_back : vfprintf_back_stmt;
  ic_fprintf_F1 : fprintf_s_front_stmt A0_FMT_F1 17; ic_fprintf_F2 : fprintf_s_front_stmt A0_FMT_F2 21; ic_fprintf_F3 : fprintf_s_front_stmt A0_FMT_F3 23;
  ic_fprintf_F4 : fprintf_u_front_stmt; ic_fprintf_back : fprintf_back_stmt;
  ic_asan_dtor : asan_dtor_stmt;
  ic_strtol : strtol_stmt_A;
  ic_sscanf_status : sscanf_status_stmt_A;
  ic_strncpy : strncpy_stmt_A; ic_atoi : atoi_stmt_A; ic_inet_pton : inet_pton_stmt_A; ic_strtol0 : strtol0_stmt_A;
  ic_strstr_chunked : strstr_chunked_stmt_A; ic_strtoll : strtoll_stmt_A;
  ic_sscanf_version : sscanf_version_stmt_A

}.
End I.
