(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AxSymExec3 AsanPlanCore DigitFam.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import BigModel BigFactsRun BigFactsDigits.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition u8_at (M : word -> option byte) (a : Z) (b : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 b].
Definition u64_at (M : word -> option byte) (a : Z) (v : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
(* [comment removed for export] *)
Definition defined (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.
Definition writable (M : word -> option byte) (a n : Z) : Prop :=
  forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok RSEGS M (Z_to_bv 64 (a + d)) k = true.
Definition limbs_at (M : word -> option byte) (q : Z) (ws : list Z) : Prop :=
  forall i, (i < length ws)%nat -> u64_at M (q + 8 * Z.of_nat i) (nth i ws 0).
Definition bytes_at (M : word -> option byte) (p : Z) (bs : list Z) : Prop :=
  forall i, (i < length bs)%nat -> u8_at M (p + Z.of_nat i) (nth i bs 0).

(* [comment removed for export] *)
Definition DL_HEAD : Z := 0x20c98.      (* [comment removed for export] *)
Definition DL_EXIT : Z := 0x20cc8.      (* [comment removed for export] *)
Definition DL_SCRATCH : Z := 216.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition dl_kept_reg (r : reg) : Prop :=
  r <> 0%bv /\ ~ In (ridx r) APC.caller_saved /\ ridx r <> 18%nat /\ ridx r <> 20%nat /\ ridx r <> 22%nat.

(* [comment removed for export] *)
Definition digit_loop_dyn_src0 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (s q p C : Z) (ds : list Z),
    let m := length ds in
    (* [comment removed for export] *)
    getr R (2%bv : reg) = Z_to_bv 64 s ->
    getr R (3%bv : reg) = Z_to_bv 64 67584 -> getr R (4%bv : reg) = Z_to_bv 64 459832 ->      (* [comment removed for export] *)
    getr R (18%bv : reg) = Z_to_bv 64 p ->                 (* [comment removed for export] *)
    getr R (20%bv : reg) = Z_to_bv 64 (Z.of_nat m) ->      (* [comment removed for export] *)
    getr R (21%bv : reg) = Z_to_bv 64 9 ->                 (* [comment removed for export] *)
    (forall i, 65536 <= i < 131072 -> M (Z_to_bv 64 i) = None) ->   (* [comment removed for export] *)
    (39 <= m <= 4999)%nat ->
    (* [comment removed for export] *)
    u8_at M s 1 -> u64_at M (s + 8) 0 -> u64_at M (s + 16) C -> u64_at M (s + 24) q ->
    C = Z.of_nat (round_up (num_words_est m)) ->
    (* [comment removed for export] *)
    bytes_at M p ds -> Forall (fun c => 48 <= c <= 57) ds ->
    (* [comment removed for export] *)
    s mod 16 = 0 -> q mod 8 = 0 ->
    2 ^ 20 <= s - DL_SCRATCH -> s + 32 <= 2 ^ 47 -> 4096 <= q -> q + 8 * C <= 2 ^ 47 -> 4096 <= p -> p + Z.of_nat m <= 2 ^ 47 ->
    writable M (s - DL_SCRATCH) (DL_SCRATCH + 32) ->
    defined M q (8 * C) -> writable M q (8 * C) ->
    (q + 8 * C <= s - DL_SCRATCH \/ s + 32 <= q) ->
    (p + Z.of_nat m <= s - DL_SCRATCH \/ s + 32 <= p) ->
    (p + Z.of_nat m <= q \/ q + 8 * C <= p) ->
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
      msteps RSEGS (@mkst fx R (Z_to_bv 64 DL_HEAD) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 DL_EXIT) M' (seg_rom RSEGS))
      (* [comment removed for export] *)
      /\ (forall r : reg, dl_kept_reg r -> getr R' r = getr R r)
      /\ getr R' (18%bv : reg) = Z_to_bv 64 (p + Z.of_nat m)          (* [comment removed for export] *)
      /\ getr R' (20%bv : reg) = Z_to_bv 64 0                         (* [comment removed for export] *)
      /\ getr R' (22%bv : reg) = Z_to_bv 64 (nth (m - 1) ds 0)         (* [comment removed for export] *)
      (* [comment removed for export] *)
      /\ (let V := dec ds in let n := nwords V in
          u8_at M' s 1 /\ u64_at M' (s + 8) (Z.of_nat n) /\ u64_at M' (s + 16) C /\ u64_at M' (s + 24) q
          /\ (n <= num_words_est m)%nat /\ limbs_at M' q (wlist V n))
      (* [comment removed for export] *)
      /\ (forall x : word, let a := bv_unsigned x in
            ~ (s - DL_SCRATCH <= a < s + 16) -> ~ (q <= a < q + 8 * C) -> M' x = M x)
      /\ mem_grows M M'.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DQ_ENTRY : Z := 0x22578.
Definition DQ_RET : Z := 0x22670.
Definition dq_clob : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.   (* [comment removed for export] *)

Definition ddquotient_src0 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (d : Z),
    getr R (13%bv : reg) = Z_to_bv 64 d -> 2 ^ 63 <= d < 2 ^ 64 ->
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
      msteps RSEGS (@mkst fx R (Z_to_bv 64 DQ_ENTRY) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 DQ_RET) M' (seg_rom RSEGS))
      /\ (forall r : reg, ~ In (ridx r) dq_clob -> getr R' r = getr R r)
      /\ M' = M.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DL_ERR : Z := 0x20d38.

Definition digit_loop_dyn_bad_src0 : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (s q p C : Z) (m : nat) (ds : list Z) (c : Z),
    let K := length ds in
    getr R (2%bv : reg) = Z_to_bv 64 s ->
    getr R (3%bv : reg) = Z_to_bv 64 67584 -> getr R (4%bv : reg) = Z_to_bv 64 459832 ->      (* [comment removed for export] *)
    getr R (18%bv : reg) = Z_to_bv 64 p ->
    getr R (20%bv : reg) = Z_to_bv 64 (Z.of_nat m) ->
    getr R (21%bv : reg) = Z_to_bv 64 9 ->
    (forall i, 65536 <= i < 131072 -> M (Z_to_bv 64 i) = None) ->
    (K < m)%nat -> (39 <= m <= 4999)%nat ->
    u8_at M s 1 -> u64_at M (s + 8) 0 -> u64_at M (s + 16) C -> u64_at M (s + 24) q ->
    C = Z.of_nat (round_up (num_words_est m)) ->
    bytes_at M p ds -> Forall (fun d => 48 <= d <= 57) ds ->
    u8_at M (p + Z.of_nat K) c -> (0 <= c < 48 \/ 57 < c < 256) ->
    s mod 16 = 0 -> q mod 8 = 0 ->
    2 ^ 20 <= s - DL_SCRATCH -> s + 32 <= 2 ^ 47 -> 4096 <= q -> q + 8 * C <= 2 ^ 47 -> 4096 <= p -> p + Z.of_nat m <= 2 ^ 47 ->
    writable M (s - DL_SCRATCH) (DL_SCRATCH + 32) ->
    defined M q (8 * C) -> writable M q (8 * C) ->
    (q + 8 * C <= s - DL_SCRATCH \/ s + 32 <= q) ->
    (p + Z.of_nat m <= s - DL_SCRATCH \/ s + 32 <= p) ->
    (p + Z.of_nat m <= q \/ q + 8 * C <= p) ->
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte),
      msteps RSEGS (@mkst fx R (Z_to_bv 64 DL_HEAD) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 DL_ERR) M' (seg_rom RSEGS))
      /\ (forall r : reg, dl_kept_reg r -> getr R' r = getr R r)
      /\ getr R' (18%bv : reg) = Z_to_bv 64 (p + Z.of_nat K)
      /\ getr R' (20%bv : reg) = Z_to_bv 64 (Z.of_nat m - Z.of_nat K)
      /\ getr R' (22%bv : reg) = Z_to_bv 64 c
      /\ (let V := dec ds in let n := nwords V in
          u8_at M' s 1 /\ u64_at M' (s + 8) (Z.of_nat n) /\ u64_at M' (s + 16) C /\ u64_at M' (s + 24) q
          /\ (n <= num_words_est m)%nat /\ limbs_at M' q (wlist V n))
      /\ (forall x : word, let a := bv_unsigned x in
            ~ (s - DL_SCRATCH <= a < s + 16) -> ~ (q <= a < q + 8 * C) -> M' x = M x)
      /\ mem_grows M M'.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DLI_AFTMUL : Z := 0x20cb0.   (* [comment removed for export] *)
Definition DLI_SCRATCH : Z := 400.      (* [comment removed for export] *)

Definition digit_loop_inl_src0 (f : nat) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (s p : Z) (b0 w0 w1 : Z) (ds : list Z),
    let m := length ds in
    getr R (2%bv : reg) = Z_to_bv 64 s ->
    getr R (3%bv : reg) = Z_to_bv 64 67584 -> getr R (4%bv : reg) = Z_to_bv 64 459832 ->      (* [comment removed for export] *)
    getr R (18%bv : reg) = Z_to_bv 64 p ->
    getr R (20%bv : reg) = Z_to_bv 64 (Z.of_nat m) ->
    getr R (21%bv : reg) = Z_to_bv 64 9 ->
    (1 <= m <= 38)%nat ->
    (* [comment removed for export] *)
    (forall i, 65536 <= i < 131072 -> M (Z_to_bv 64 i) = None) ->
    (* [comment removed for export] *)
    u8_at M s b0 -> 0 <= b0 < 256 -> Z.land b0 3 = 0 -> u64_at M (s + 8) 0 -> u64_at M (s + 16) w0 -> u64_at M (s + 24) w1 ->
    (* [comment removed for export] *)
    bytes_at M p ds -> Forall (fun c => 48 <= c <= 57) ds -> (1 <= DF.nsig ds)%nat -> DF.pfam_cond f ds ->
    (* [comment removed for export] *)
    s mod 16 = 0 -> 140735340000000 <= s -> s + 32 <= 2 ^ 47 -> 4096 <= p -> p + Z.of_nat m <= 2 ^ 47 ->
    writable M (s - DLI_SCRATCH) (DLI_SCRATCH + 32) ->
    (p + Z.of_nat m <= s - DLI_SCRATCH \/ s + 32 <= p) ->
    let z := DF.leading_zeros ds in
    exists (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (pc' : Z) (k : nat) (size v0 v1 : Z),
      msteps RSEGS (@mkst fx R (Z_to_bv 64 DL_HEAD) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS))
      /\ match f with
         | 0%nat => pc' = DL_EXIT /\ k = m /\ size = 1 /\ v0 = DF.dval ds /\ 1 <= v0 < 2 ^ 64
         | 4%nat => pc' = DL_EXIT /\ k = m /\ size = 2 /\ v0 = DF.dval ds mod 2 ^ 64 /\ v1 = 1 /\ 0 <= v0 <= 3   (* [comment removed for export] *)
         | 1%nat => pc' = DLI_AFTMUL /\ k = (z + 19)%nat /\ size = 2 /\ v0 = (10 * DF.P19 ds) mod 2 ^ 64 /\ v1 = (10 * DF.P19 ds) / 2 ^ 64 /\ 1 <= v1 <= 5
         | 3%nat => pc' = DLI_AFTMUL /\ k = (z + 20)%nat /\ size = 2 /\ v0 = (10 * DF.P20 ds) mod 2 ^ 64 /\ v1 = (10 * DF.P20 ds) / 2 ^ 64 /\ 5 <= v1 <= 9
         | 2%nat => pc' = DL_HEAD /\ k = (z + 20)%nat /\ size = 2 /\ v0 = DF.P20 ds mod 2 ^ 64 /\ v1 = DF.P20 ds / 2 ^ 64 /\ 0 <= v0 <= 3 /\ v1 = 1
         | _ => False
         end
      (* [comment removed for export] *)
      /\ (forall r : reg, dl_kept_reg r -> getr R' r = getr R r)
      /\ getr R' (18%bv : reg) = Z_to_bv 64 (p + Z.of_nat k)                       (* [comment removed for export] *)
      /\ getr R' (20%bv : reg) = Z_to_bv 64 (Z.of_nat m - Z.of_nat k)               (* [comment removed for export] *)
      /\ getr R' (21%bv : reg) = Z_to_bv 64 9
      /\ (pc' <> DL_HEAD -> getr R' (22%bv : reg) = Z_to_bv 64 (nth (if Z.eqb pc' DL_EXIT then (m - 1)%nat else k) ds 0))   (* [comment removed for export] *)
      (* [comment removed for export] *)
      /\ u8_at M' s b0 /\ u64_at M' (s + 8) size /\ u64_at M' (s + 16) v0 /\ (size = 2 -> u64_at M' (s + 24) v1)
      (* [comment removed for export] *)
      /\ (forall x : word, let a := bv_unsigned x in ~ (s - DLI_SCRATCH <= a < s + 32) -> M' x = M x)
      /\ mem_grows M M'.
