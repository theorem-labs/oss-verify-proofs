(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Spec Require Import Prelim StrFun Canon Stdio.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Spec Require PrintfFormats.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow IcptSpec.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SEGTOP_A : Z := 0x73a000.
(* [comment removed for export] *)
Definition USTACK_TOP : Z := 0x800000000000.
Definition STACK_WIN : Z := 0x800000.
(* [comment removed for export] *)
Definition RT_STACK : Z := 0x10000.
(* [comment removed for export] *)
Definition LIVE_MAX : Z := 256.
Definition FRAMES_MAX : nat := 16.
(* [comment removed for export] *)
Definition mcost (n : Z) : Z := if n <=? 64512 then 0 else 2 * n + 16384.

(* [comment removed for export] *)
Definition e_malloc : Z := 0xb87f8.        (* [comment removed for export] *)
Definition e_free : Z := 0xb87f4.          (* [comment removed for export] *)
Definition e_strdup : Z := 0x97600.        (* [comment removed for export] *)
Definition e_strndup : Z := 0x97578.       (* [comment removed for export] *)
Definition e_strlen : Z := 0xa25c8.        (* [comment removed for export] *)
Definition e_strnlen : Z := 0xa25cc.       (* [comment removed for export] *)
Definition e_strncmp : Z := 0x97580.       (* [comment removed for export] *)
Definition e_memchr : Z := 0xa25e4.        (* [comment removed for export] *)
Definition e_memset : Z := 0xb6c68.        (* [comment removed for export] *)
Definition e_memcpy : Z := 0xb6c70.        (* [comment removed for export] *)
Definition e_asan_memcpy : Z := 0xb6c74.   (* [comment removed for export] *)
Definition e_asan_memset : Z := 0xb7110.   (* [comment removed for export] *)
Definition e_read : Z := 0xa25ec.          (* [comment removed for export] *)
Definition e_fwrite : Z := 0xa25f8.        (* [comment removed for export] *)
Definition e_vprintf : Z := 0xa2618.       (* [comment removed for export] *)
Definition e_vfprintf : Z := 0xa261c.      (* [comment removed for export] *)
Definition e_vsnprintf : Z := 0xa2620.     (* [comment removed for export] *)
Definition e_fprintf : Z := 0xa2624.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stack_malloc (k : nat) : Z :=
  match k with 0%nat => 0x9cce0 | 1%nat => 0x9ce54 | 4%nat => 0x9d32c | _ => 0x9d4f8 end.
(* [comment removed for export] *)
Definition set_shadow_vals : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 0xf1; 0xf2; 0xf3; 0xf5; 0xf8].
Definition e_set_shadow (v : Z) : Z :=
  match v with
  | 0 => 0xbaa20 | 1 => 0xbaa38 | 2 => 0xbaa50 | 3 => 0xbaa68 | 4 => 0xbaa80 | 5 => 0xbaa98 | 6 => 0xbaab0
  | 7 => 0xbaac8 | 241 => 0xbaae0 | 242 => 0xbaaf8 | 243 => 0xbab10 | 245 => 0xbab28 | _ => 0xbab40
  end.

(* [comment removed for export] *)
Definition fs_size (k : nat) : Z := Z.shiftl 64 (Z.of_nat k).

(* [comment removed for export] *)
Definition ALLOC_RAS : list Z :=
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  [0xe6e58; 0xe6eac; 0xe6ed0; 0xe7000; 0xe7138; 0xe71cc; 0xe9598; 0xe95c0; 0xe963c; 0xef7c8; 0xef7d8; 0xef8c4; 0xef8cc; 0xefa70; 0xefa78; 0xf34e8; 0xfb054; 0xfb05c; 0xfd2d8; 0xfd328].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record rt_sig : Type := mkRTS {
  rts : Type;
  ART : rts -> mem -> Prop;               (* [comment removed for export] *)
  ARTM : rts -> Model -> Prop;            (* [comment removed for export] *)
  rt_live : rts -> list (Z * Z);          (* [comment removed for export] *)
  rt_frames : rts -> list (Z * nat);      (* [comment removed for export] *)
  rt_allow : rts -> list (Z * Z);         (* [comment removed for export] *)
  rt_sp0 : rts -> Z;                      (* [comment removed for export] *)
  rt_credit : rts -> Z                    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition fdfs_only (PMc : Model -> Prop) : Prop :=
  forall mo mo', m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> PMc mo -> PMc mo'.

(* [comment removed for export] *)
Definition ASTA (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop) (Pm : machine_state -> Prop) : config -> Prop :=
  AST SEGTOP_A (rt_allow RT Σ) Pm (fun mo => ARTM RT Σ mo /\ PMc mo).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CLIENT_STATIC : list (Z * Z) := [ (0x1d3a10, 0x1e14d8) (* [comment removed for export] *) ;
                                              (0x707190, 0x717190) (* [comment removed for export] *) ;
                                              (0x717190, 0x739798) (* [comment removed for export] *) ].
(* [comment removed for export] *)
Definition RT_STATIC : list (Z * Z) :=
  [(* [comment removed for export] *)
   (0x1d3c44, 0x1d3c60); (0x1d3c68, 0x1d3c80); (0x1d3c84, 0x1d3ca0); (0x1d3ca8, 0x1d3cc0); (0x1d3cc8, 0x1d3ce0); (0x1d3ce8, 0x1d3d00); (0x1d3d04, 0x1d3d20); (0x1d3d24, 0x1d3d40);
   (0x717e60, 0x717e68); (0x717eb0, 0x717ee0); (0x717ee8, 0x717ef8); (0x739260, 0x739268);
   (* [comment removed for export] *)
   (0x738178, 0x738180)].

Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists lo hi, In (lo, hi) l /\ lo <= a < hi.
Definition client_static (a : Z) : Prop := in_ranges CLIENT_STATIC a /\ ~ in_ranges RT_STATIC a.

Definition in_live (live : list (Z * Z)) (a : Z) : Prop := exists p n, In (p, n) live /\ p <= a < p + n.
(* [comment removed for export] *)
Definition in_fframe (frames : list (Z * nat)) (a : Z) : Prop :=
  exists f k, In (f, k) frames /\ f <= a < f + fs_size k - 8.
(* [comment removed for export] *)
Definition in_fframe_shadow (frames : list (Z * nat)) (a : Z) : Prop :=
  exists f k, In (f, k) frames /\ shad f <= a < shad (f + fs_size k).

Definition aclient (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (a : Z) : Prop :=
  (sp <= a < USTACK_TOP) \/ client_static a \/ in_live live a \/ in_fframe frames a \/ in_fframe_shadow frames a.

(* [comment removed for export] *)
Definition rt_pres (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (m m' : mem) : Prop :=
  forall a : word, aclient live frames sp (bv_unsigned a) -> m' a = m a.
(* [comment removed for export] *)
Definition rt_pres_ex (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (d n : Z) (m m' : mem) : Prop :=
  forall a : word, aclient live frames sp (bv_unsigned a) -> ~ (d <= bv_unsigned a < d + n) -> m' a = m a.

(* [comment removed for export] *)
Definition rng_class (RT : rt_sig) (Σ : rts RT) (s n : Z) : Prop :=
  (exists p k, In (p, k) (rt_live RT Σ) /\ p <= s /\ s + n <= p + k)
  \/ (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= s /\ s + n <= f + fs_size k - 8)
  \/ (rt_sp0 RT Σ - STACK_WIN + 64 <= s /\ s + n <= USTACK_TOP - 16)
  \/ (0x10000 <= s /\ s + n <= SEGTOP_A).

(* [comment removed for export] *)
Definition call_ok (RT : rt_sig) (Σ : rts RT) (m : mem) (sp : word) (lo : Z) : Prop :=
  stk asegs m lo (bv_unsigned sp) /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + RT_STACK <= bv_unsigned sp
  /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0.

(* [comment removed for export] *)
Definition unwind_ok (ra s0 sp : word) : Prop :=
  In (bv_unsigned ra) ALLOC_RAS
  /\ (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition frm_clear (fc : bv 32) : bv 32 := Z_to_bv 32 (Z.land (bv_unsigned fc) 31).
Lemma land31_range : forall x, 0 <= x -> 0 <= Z.land x 31 <= 31.
Proof.
  intros x Hx. assert (E : Z.land x 31 = x mod 32). { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
  rewrite E. assert (B : 0 < 32) by lia. pose proof (Z.mod_pos_bound x 32 B). lia.
Qed.
Lemma frm_clear_unsigned : forall fc, bv_unsigned (frm_clear fc) = Z.land (bv_unsigned fc) 31.
Proof.
  intros fc. unfold frm_clear. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 32 fc) as HR. pose proof (land31_range (bv_unsigned fc) ltac:(lia)).
  rewrite bv_wrap_small by (unfold bv_modulus; lia). reflexivity.
Qed.
Lemma frm_clear_idem : forall fc, frm_clear (frm_clear fc) = frm_clear fc.
Proof. intros fc. unfold frm_clear at 1. rewrite frm_clear_unsigned. rewrite <- Z.land_assoc. reflexivity. Qed.
Lemma frm_clear_small : forall fc, bv_unsigned fc < 32 -> frm_clear fc = fc.
Proof.
  intros fc H. apply bv_eq. rewrite frm_clear_unsigned. pose proof (bv_unsigned_in_range 32 fc).
  change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Lemma frm_clear_zero : frm_clear (Z_to_bv 32 0) = Z_to_bv 32 0.
Proof. apply frm_clear_small. rewrite Z_to_bv_unsigned. cbv. reflexivity. Qed.

(* [comment removed for export] *)
Definition entry_st (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (pc : Z) (m : mem) : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) (frm_clear fc) None m (seg_rom asegs).

(* [comment removed for export] *)
Definition ret_st (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (ret_pc ra) (frm_clear fc') None m' (seg_rom asegs).

(* [comment removed for export] *)
Definition rt_after (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
  ART RT Σ' m' /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo sp.

(* [comment removed for export] *)
Definition rt_after_f (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
  ART RT Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo sp.

Lemma rt_after_f_of : forall RT Σ' sp lo m m', rt_after RT Σ' sp lo m m' -> rt_after_f RT Σ' sp lo m m'.
Proof. intros RT Σ' sp lo m m' (H1 & H2 & _ & H4). exact (conj H1 (conj H2 H4)). Qed.

(* [comment removed for export] *)
Definition icpt_post (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (lo d n : Z) (m : mem) (Q : mem -> Prop) : config -> Prop :=
  ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
                    /\ rt_after RT Σ (bv_unsigned sp) lo m m'
                    /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m' /\ Q m').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Contracts.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition malloc_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (n lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (p : Z),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' p n /\ acc asegs m' p n) c
    /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

Definition malloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x717eb8 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_malloc m)))
            (malloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

(* [comment removed for export] *)
Definition live_remove (p : Z) (live : list (Z * Z)) : list (Z * Z) := filter (fun e => negb (fst e =? p)) live.

(* [comment removed for export] *)
Definition free_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (p lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (v : word),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m') c
    /\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ.

Definition free_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x717eb8 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

(* [comment removed for export] *)
Definition free_null_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x717eb8 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (fun c => exists v, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

(* [comment removed for export] *)
Definition strdup_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s : Z) (str : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> tp = Z_to_bv 64 0x717eb8 ->
  bytes_at asegs m s (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 < 2^27 ->
  rng_class RT Σ s (Z.of_nat (length str) + 1) -> acc asegs m s (Z.of_nat (length str) + 1) ->
  ((forall i, 0 <= i < Z.of_nat (length str) + 1 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (s + i))
   \/ (0x10000 <= s /\ s + Z.of_nat (length str) + 1 <= 0x1c8000) (* [comment removed for export] *)) ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (Z.of_nat (length str) + 1) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strdup m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ bytes_at asegs m' p (str ++ [Z_to_bv 8 0]) /\ wr_at asegs m' p (Z.of_nat (length str) + 1)
         /\ acc asegs m' p (Z.of_nat (length str) + 1)) c
       /\ rt_live RT Σ' = (p, Z.of_nat (length str) + 1) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (Z.of_nat (length str) + 1)
       /\ 0 < p /\ p + Z.of_nat (length str) + 1 < USTACK_TOP).

(* [comment removed for export] *)
Definition strndup_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s k : Z) (buf : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 k -> tp = Z_to_bv 64 0x717eb8 ->
  0 <= k < 2^27 -> bytes_at asegs m s buf -> strnlen_known k buf ->
  (exists p0 n0, In (p0, n0) (rt_live RT Σ) /\ p0 <= s /\ s + Z.of_nat (length buf) <= p0 + n0) ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (k + 1) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  let cl := strnlen_res k buf in
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strndup m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ bytes_at asegs m' p (firstn (Z.to_nat cl) buf ++ [Z_to_bv 8 0]) /\ wr_at asegs m' p (cl + 1)
         /\ acc asegs m' p (cl + 1)) c
       /\ rt_live RT Σ' = (p, cl + 1) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (cl + 1)
       /\ 0 < p /\ p + cl + 1 < USTACK_TOP).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition checked_src (Σ : rts RT) (m : mem) (sp : word) (lo s n : Z) : Prop :=
  (0 < n -> acc asegs m s n /\ rng_class RT Σ s n) /\ (s + n <= lo \/ bv_unsigned sp <= s).
(* [comment removed for export] *)
Definition checked_dst (Σ : rts RT) (m : mem) (sp : word) (d n : Z) : Prop :=
  (0 < n -> acc asegs m d n /\ rng_class RT Σ d n)
  /\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (d + i)) /\ wr_at asegs m d n.

(* [comment removed for export] *)
Definition memcpy_icontract (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at asegs m s bs ->
  checked_src Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst Σ m sp d (Z.of_nat (length bs)) ->
  (d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
               (fun m' => bytes_at asegs m' d bs)).

(* [comment removed for export] *)
Definition memset_icontract (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d n : Z) (c : byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (bv_unsigned c) -> a2 = Z_to_bv 64 n ->
  0 <= d <= 2^47 -> 0 <= n < 2^40 -> checked_dst Σ m sp d n ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d n m
               (fun m' => bytes_at asegs m' d (repeat c (Z.to_nat n)))).

(* [comment removed for export] *)
Definition memchr_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s cz n : Z) (buf : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 cz -> a2 = Z_to_bv 64 n ->
  0 < s <= 2^47 -> 0 <= cz < 256 -> 0 <= n < 2^40 -> bytes_at asegs m s buf -> memchr_ok s cz n buf ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) (* [comment removed for export] *) ->
  checked_src Σ m sp lo s (memchr_chk cz n buf) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_memchr m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (memchr_res s cz n buf)) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strlen_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s : Z) (str slack : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < s <= 2^47 -> (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  checked_src Σ m sp lo s (Z.of_nat (length str) + 1) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strlen m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length str))) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strnlen_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s n : Z) (buf : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
  0 < s <= 2^47 -> 0 <= n < 2^40 -> bytes_at asegs m s buf -> strnlen_ok s n buf ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) (* [comment removed for export] *) ->
  checked_src Σ m sp lo s (strnlen_chk n buf) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strnlen m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strnlen_res n buf)) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strncmp_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p1 p2 n : Z) (b1 b2 : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 n ->
  0 < n < 2^31 -> bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> strncmp_ok n b1 b2 ->
  checked_src Σ m sp lo p1 (strncmp_sz n b1 b2) -> checked_src Σ m sp lo p2 (strncmp_sz n b1 b2) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strncmp m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strncmp_res n b1 b2)) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_malloc_contract (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> (k <= 10)%nat -> tp = Z_to_bv 64 0x717eb8 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8)) c
       /\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP).

(* [comment removed for export] *)
Definition set_shadow_contract (v : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d n : Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> In v set_shadow_vals -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n ->
  0 <= n < 2^20 -> (forall i, 0 <= i < n -> in_fframe_shadow (rt_frames RT Σ) (d + i)) -> wr_at asegs m d n ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_set_shadow v) m)))
    (fun c => exists v0, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 lo d n m
               (fun m' => bytes_at asegs m' d (repeat (Z_to_bv 8 v) (Z.to_nat n))) c).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition client_consts (m : mem) : Prop :=
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
  /\ ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
  /\ ro_cells asegs m g_GOT_detect_uar [C8 (Z_to_bv 64 g_detect_stack_use_after_return)]
  /\ ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)].

(* [comment removed for export] *)
Definition ACC_LITS : list (Z * Z) :=
  [(0x30ce0, 14); (0x30d00, 10); (0x30d20, 16); (0x30d40, 29); (0x30e40, 39); (0x30ea0, 16); (0x30ec0, 18); (0x30f00, 19); (0x30fa0, 12); (0x30fc0, 24); (0x311a0, 11); (0x31340, 16); (0x31360, 12); (0x313e0, 13); (0x31440, 12); (0x314a0, 17); (0x31560, 10); (0x316c0, 15); (0x316e0, 22); (0x31760, 11); (0x31960, 16); (0x31b40, 14); (0x322a0, 15); (0x322c0, 19); (0x32300, 15); (0x32320, 17); (0x32360, 23); (0x326c0, 22); (0x32700, 15); (0x32ac0, 17); (0x32c40, 15); (0x32c60, 29); (0x32ca0, 11); (0x32cc0, 14); (0x32da0, 17); (0x32ea0, 22); (0x32ee0, 20); (0x32f20, 37); (0x33a80, 19); (0x33ac0, 8); (0x33ae0, 16); (0x36ba0, 13); (0x36bc0, 17); (0x36de0, 25); (0x36e80, 18); (0x36ec0, 14); (0x36ee0, 15); (0x36f00, 15); (0x36f20, 16); (0x36f40, 22); (0x37000, 14); (0x37020, 18); (0x37060, 25); (0x2dca0, 17); (0x30f40, 47); (0x31000, 48); (0x31060, 52); (0x310c0, 53); (0x31140, 37); (0x32240, 37); (0x31b60, 27); (0x323a0, 37); (0x32400, 47); (0x32460, 46); (0x324c0, 31); (0x32500, 51); (0x32560, 56); (0x325c0, 58); (0x32620, 77); (0x36e20, 35); (0x36f80, 84); (0x31ba0, 132); (0x2dce0, 31); (0x2dd20, 18); (0x2dd60, 22); (0x2dda0, 19); (0x2dde0, 20); (0x2de20, 18); (0x2de60, 13); (0x2de80, 14); (0x2dea0, 19); (0x2dee0, 13); (0x2df00, 13); (0x2df60, 32); (0x2dfa0, 10); (0x2dfc0, 14); (0x2dfe0, 17); (0x2e020, 11); (0x2e040, 18); (0x2e080, 14); (0x2e0a0, 20); (0x2e0e0, 13); (0x2e100, 46); (0x2e160, 10); (0x2e180, 24); (0x2e1c0, 26); (0x2e200, 17); (0x2e240, 11); (0x2e260, 21); (0x2e2a0, 15); (0x2e2c0, 33); (0x2e320, 18); (0x2e360, 31); (0x2e3a0, 23); (0x2e3e0, 11); (0x2e400, 17); (0x2e440, 20); (0x2e480, 13); (0x2e4a0, 21); (0x2e4e0, 23); (0x2e520, 20); (0x2e560, 19); (0x2e5a0, 15); (0x2e5c0, 35); (0x2e620, 19); (0x2e660, 25); (0x2e6a0, 19); (0x2e6e0, 46); (0x2e740, 21); (0x2e780, 49); (0x2e7e0, 18); (0x2e820, 16); (0x2e840, 14); (0x2e860, 26); (0x2e8a0, 14); (0x2e8c0, 18); (0x2e900, 13); (0x2e920, 16); (0x2e940, 18); (0x2e980, 3); (0x2e9a0, 65); (0x2ea20, 15); (0x2ea40, 17); (0x2ea80, 34); (0x2eae0, 2); (0x2eb00, 5); (0x2eb20, 28); (0x2eb60, 12); (0x2eb80, 28); (0x2ebc0, 21); (0x2ec00, 21); (0x2ec40, 1); (0x2ec60, 21); (0x2eca0, 9); (0x2ecc0, 23); (0x2ed00, 17); (0x2ed40, 22); (0x2ed80, 9); (0x2eda0, 12); (0x2edc0, 21); (0x2ee00, 17); (0x2ee40, 17); (0x2ee80, 19); (0x2eec0, 16); (0x2eee0, 46); (0x2ef40, 23); (0x2ef80, 19); (0x2efc0, 13); (0x2efe0, 15); (0x2f040, 22); (0x2f080, 12); (0x2f0a0, 36); (0x2f100, 13); (0x2f120, 15); (0x2f140, 15); (0x2f160, 17); (0x2f1a0, 14); (0x2f1c0, 27); (0x2f200, 17); (0x2f240, 15); (0x2f260, 16); (0x2f280, 18); (0x2f2c0, 15); (0x2f2e0, 15); (0x2f300, 15); (0x2f320, 17); (0x2f360, 33); (0x2f400, 20); (0x2f440, 14); (0x2f460, 36); (0x2f4c0, 15); (0x2f4e0, 26); (0x2f520, 32); (0x2f560, 41); (0x2f5c0, 15); (0x2f5e0, 12); (0x2f600, 16); (0x2f620, 17); (0x2f660, 17); (0x2f6a0, 19); (0x2f6e0, 27); (0x2f720, 13); (0x2f740, 17); (0x2f780, 28); (0x2f7c0, 18); (0x2f840, 19); (0x2f880, 13); (0x2f8a0, 37); (0x2f900, 14); (0x2f920, 15); (0x2f940, 16); (0x2f960, 19); (0x2f9a0, 17); (0x2f9e0, 17); (0x2fa20, 15); (0x2fa40, 16); (0x2fa60, 16); (0x2fa80, 15); (0x2faa0, 20); (0x2fae0, 18); (0x2fb20, 1); (0x2fb40, 2); (0x2fb60, 2); (0x2fb80, 2); (0x2fba0, 16); (0x2fbc0, 14); (0x2fbe0, 14); (0x2fc00, 18); (0x2fc40, 16); (0x2fc60, 23); (0x2fca0, 18); (0x2fce0, 37); (0x2fd40, 27); (0x2fdc0, 16); (0x2fde0, 16); (0x2fe00, 10); (0x2fe60, 22); (0x2fea0, 11); (0x2fec0, 36); (0x2ff20, 12); (0x2ff40, 15); (0x2ff60, 14); (0x2ff80, 17); (0x2ffc0, 13); (0x2ffe0, 27); (0x30020, 17); (0x30060, 14); (0x30080, 16); (0x300a0, 18); (0x300e0, 14); (0x30100, 16); (0x30120, 21); (0x30160, 28); (0x30220, 16); (0x30240, 9); (0x30260, 18); (0x302a0, 4); (0x302c0, 18); (0x30300, 26); (0x30340, 19); (0x30380, 15); (0x303a0, 15); (0x30400, 22); (0x30440, 10); (0x30460, 24); (0x304a0, 24); (0x304e0, 16); (0x30500, 37); (0x30560, 11); (0x30580, 15); (0x305a0, 15); (0x30600, 36); (0x30660, 11); (0x30680, 19); (0x306c0, 36); (0x30720, 12); (0x30740, 58); (0x307a0, 15); (0x307c0, 8); (0x307e0, 17); (0x30820, 18); (0x30860, 11); (0x30880, 26); (0x308c0, 17); (0x30900, 30); (0x30940, 16); (0x30960, 27); (0x309e0, 29); (0x30a20, 10); (0x30a40, 37); (0x30aa0, 11); (0x30ac0, 16); (0x30ae0, 9); (0x30b00, 17); (0x30b40, 9); (0x30b60, 14); (0x30b80, 9); (0x30ba0, 16); (0x30bc0, 34); (0x30c20, 25); (0x30c60, 25); (0x30d80, 17); (0x30dc0, 18); (0x30e00, 24); (0x31120, 9); (0x311c0, 8); (0x311e0, 28); (0x31220, 19); (0x31260, 17); (0x312a0, 16); (0x312c0, 31); (0x31300, 15); (0x31320, 15); (0x31380, 12); (0x313a0, 19); (0x31400, 13); (0x31420, 15); (0x31460, 12); (0x31480, 15); (0x314e0, 10); (0x31500, 10); (0x31520, 17); (0x31580, 11); (0x315a0, 11); (0x315c0, 18); (0x31600, 18); (0x31640, 19); (0x31680, 11); (0x316a0, 15); (0x31720, 19); (0x31900, 17); (0x31940, 12); (0x31980, 37); (0x319e0, 12); (0x31a00, 17); (0x31a40, 19); (0x31a80, 56); (0x31ae0, 64); (0x31c60, 14); (0x31c80, 19); (0x31cc0, 16); (0x31ce0, 13); (0x31d00, 23); (0x31d40, 17); (0x31d80, 29); (0x31dc0, 17); (0x31e00, 19); (0x31e40, 16); (0x31e60, 17); (0x31ea0, 21); (0x31ee0, 18); (0x31f20, 24); (0x31f60, 35); (0x31fc0, 17); (0x32000, 29); (0x32040, 19); (0x320c0, 23); (0x32100, 14); (0x32120, 22); (0x32160, 20); (0x321a0, 16); (0x321c0, 18); (0x32200, 12); (0x32220, 13); (0x326a0, 16); (0x32720, 16); (0x32740, 36); (0x327a0, 16); (0x327c0, 20); (0x32800, 43); (0x32860, 15); (0x32880, 19); (0x328c0, 16); (0x328e0, 25); (0x32920, 20); (0x32960, 16); (0x32980, 27); (0x329c0, 24); (0x32a00, 23); (0x32a40, 18); (0x32a80, 21); (0x32b00, 18); (0x32b40, 36); (0x32ba0, 16); (0x32bc0, 25); (0x32c00, 21); (0x32ce0, 20); (0x32d20, 10); (0x32d40, 5); (0x32de0, 21); (0x32e20, 24); (0x32e60, 31); (0x33160, 17); (0x331a0, 15); (0x331c0, 14); (0x331e0, 18); (0x33220, 54); (0x33280, 27); (0x332c0, 32); (0x33300, 25); (0x33340, 55); (0x333a0, 28); (0x333e0, 42); (0x33440, 30); (0x33480, 20); (0x334c0, 13); (0x334e0, 23); (0x33520, 20); (0x33560, 16); (0x33580, 59); (0x335e0, 16); (0x33600, 16); (0x33620, 15); (0x33640, 18); (0x33680, 16); (0x336a0, 16); (0x336c0, 19); (0x33700, 15); (0x33720, 15); (0x33740, 15); (0x33760, 15); (0x33780, 15); (0x337a0, 15); (0x337c0, 29); (0x33800, 14); (0x33820, 15); (0x33840, 33); (0x338a0, 16); (0x338c0, 17); (0x33900, 16); (0x33920, 20); (0x33960, 34); (0x33a00, 17); (0x33a40, 10); (0x33a60, 14); (0x33b40, 17); (0x33b80, 12); (0x33ba0, 17); (0x33be0, 31); (0x33e80, 34); (0x33ee0, 22); (0x33f20, 22); (0x33fa0, 18); (0x33fe0, 18); (0x34020, 17); (0x34060, 21); (0x340a0, 24); (0x340e0, 15); (0x34100, 25); (0x34140, 29); (0x34180, 16); (0x341a0, 21); (0x341e0, 50); (0x34280, 21); (0x342c0, 20); (0x34300, 15); (0x34320, 15); (0x34340, 14); (0x343e0, 19); (0x34420, 13); (0x34440, 37); (0x344a0, 6); (0x344c0, 33); (0x34560, 19); (0x345a0, 20); (0x345e0, 21); (0x34620, 15); (0x34640, 38); (0x346a0, 21); (0x346e0, 24); (0x34760, 17); (0x34860, 21); (0x348a0, 19); (0x348e0, 2); (0x34900, 15); (0x34920, 16); (0x34940, 2); (0x34960, 21); (0x349a0, 43); (0x34a00, 72); (0x34a80, 16); (0x34aa0, 18); (0x34ae0, 3); (0x34b00, 22); (0x34b40, 13); (0x34b60, 15); (0x34b80, 45); (0x34be0, 33); (0x34c40, 18); (0x34c80, 22); (0x34cc0, 20); (0x34d00, 18); (0x34d40, 22); (0x34d80, 20); (0x34dc0, 25); (0x34e00, 26); (0x34e40, 16); (0x34e60, 17); (0x34ea0, 28); (0x34ee0, 34); (0x34f40, 41); (0x34fa0, 19); (0x34fe0, 21); (0x35020, 55); (0x35080, 61); (0x350e0, 53); (0x35140, 37); (0x351a0, 24); (0x351e0, 20); (0x35220, 23); (0x35260, 25); (0x352a0, 25); (0x352e0, 6); (0x35300, 9); (0x35320, 57); (0x35380, 12); (0x353a0, 9); (0x353c0, 3); (0x353e0, 23); (0x35420, 26); (0x35460, 9); (0x35480, 8); (0x354a0, 3); (0x354c0, 10); (0x354e0, 4); (0x35500, 18); (0x35540, 6); (0x35560, 17); (0x355a0, 33); (0x35600, 24); (0x35640, 38); (0x356a0, 10); (0x356c0, 23); (0x35700, 11); (0x35720, 9); (0x357e0, 21); (0x35820, 18); (0x358a0, 21); (0x358e0, 13); (0x35900, 19); (0x35980, 21); (0x359c0, 21); (0x35a00, 20); (0x35a40, 15); (0x35a60, 21); (0x35aa0, 19); (0x35ae0, 16); (0x35b00, 26); (0x35b40, 33); (0x35ba0, 19); (0x35be0, 18); (0x35c20, 16); (0x35c40, 13); (0x35c60, 4); (0x35c80, 26); (0x35cc0, 16); (0x35ce0, 19); (0x35d20, 17); (0x35d60, 50); (0x35dc0, 69); (0x35e40, 41); (0x35ea0, 13); (0x35ec0, 53); (0x35f20, 26); (0x35fa0, 21); (0x35fe0, 19); (0x36060, 19); (0x360a0, 18); (0x360e0, 16); (0x36100, 51); (0x36160, 12); (0x36180, 19); (0x361c0, 15); (0x361e0, 19); (0x36220, 17); (0x36260, 22); (0x362a0, 35); (0x36300, 63); (0x36360, 24); (0x363e0, 7); (0x36400, 17); (0x36440, 18); (0x36480, 19); (0x364c0, 22); (0x36500, 16); (0x36520, 16); (0x36540, 18); (0x36580, 14); (0x36660, 15); (0x36680, 18); (0x366c0, 16); (0x366e0, 28); (0x36720, 66); (0x367a0, 69); (0x36820, 70); (0x368a0, 17); (0x368e0, 18); (0x36920, 66); (0x369a0, 10); (0x369c0, 11); (0x369e0, 10); (0x36a00, 11); (0x36a20, 24); (0x36a60, 20); (0x36aa0, 14); (0x36ac0, 20); (0x36b00, 8); (0x36b60, 19); (0x36c00, 19); (0x36c40, 16); (0x36c60, 31); (0x36ca0, 35); (0x36d00, 21); (0x36d40, 17); (0x36d80, 19); (0x36dc0, 14); (0x370e0, 21); (0x37120, 15); (0x37140, 21); (0x37180, 16); (0x371a0, 13); (0x371c0, 17); (0x37200, 18); (0x37240, 10); (0x37260, 13); (0x37280, 5); (0x372a0, 27); (0x372e0, 25); (0x37320, 25); (0x37360, 28); (0x373a0, 25); (0x373e0, 20); (0x37420, 18); (0x37460, 19); (0x374a0, 33); (0x37500, 22); (0x37540, 43); (0x375a0, 60); (0x37600, 48); (0x37660, 46); (0x37780, 18); (0x377c0, 18); (0x37800, 25); (0x37840, 16); (0x37860, 23); (0x378a0, 18); (0x378e0, 18); (0x37920, 35); (0x37980, 15); (0x379e0, 18); (0x37a20, 20); (0x37a60, 20); (0x37aa0, 16); (0x37ac0, 16); (0x37ae0, 13); (0x37b00, 20); (0x37b40, 17); (0x37b80, 14); (0x37ba0, 18); (0x37be0, 16); (0x37c00, 52); (0x37c60, 55); (0x37cc0, 55); (0x37d20, 19); (0x37d60, 19); (0x37da0, 17); (0x37de0, 20); (0x37e20, 18); (0x37e60, 18); (0x37ea0, 19); (0x37ee0, 19); (0x37f20, 18); (0x37f60, 19); (0x37fa0, 16); (0x37fc0, 17); (0x38000, 63); (0x38060, 23); (0x380a0, 18); (0x380e0, 17); (0x38120, 15); (0x38140, 18); (0x38180, 49); (0x381e0, 37); (0x38240, 16); (0x38260, 19); (0x382a0, 18); (0x382e0, 21); (0x38320, 18); (0x38360, 18); (0x383a0, 20); (0x383e0, 18); (0x38420, 25); (0x38460, 43); (0x384c0, 20); (0x38500, 21); (0x38540, 18); (0x38580, 15); (0x385a0, 14); (0x385c0, 16); (0x385e0, 10); (0x38600, 50); (0x38660, 12); (0x38680, 22); (0x386c0, 27); (0x38700, 23); (0x38740, 11); (0x38760, 40); (0x387c0, 24); (0x38800, 11); (0x38820, 53); (0x38880, 19); (0x388c0, 6); (0x388e0, 5); (0x38900, 2); (0x38920, 20); (0x38960, 22); (0x389a0, 16); (0x389c0, 14); (0x38aa0, 25); (0x38ae0, 47); (0x38b40, 14); (0x38b60, 52); (0x38bc0, 14); (0x38be0, 23); (0x38c20, 40); (0x38c80, 24); (0x38cc0, 38); (0x38d20, 5); (0x38d40, 6); (0x38d60, 74); (0x38de0, 23); (0x38e20, 24); (0x38e60, 40); (0x38ec0, 20); (0x38f00, 19); (0x38f40, 44); (0x38fa0, 19); (0x38fe0, 19); (0x39020, 38); (0x39080, 43); (0x390e0, 21); (0x39120, 21); (0x39160, 86); (0x391e0, 1); (0x39200, 83); (0x39280, 14); (0x392a0, 20); (0x392e0, 27); (0x39320, 47); (0x39380, 22); (0x393c0, 21); (0x39400, 18); (0x39440, 21); (0x39480, 31); (0x394c0, 16); (0x394e0, 69); (0x395a0, 18); (0x395e0, 14); (0x39600, 37); (0x39660, 15); (0x39680, 15); (0x396a0, 18); (0x396e0, 16); (0x39700, 17); (0x39740, 20); (0x39780, 16); (0x397a0, 25); (0x397e0, 21); (0x39820, 23); (0x39860, 42); (0x398c0, 23); (0x39940, 16); (0x39960, 15); (0x39980, 16); (0x399a0, 20); (0x399e0, 15); (0x39a00, 17); (0x39a40, 20); (0x39a80, 22); (0x39ac0, 14); (0x39b20, 68); (0x39ba0, 13); (0x39bc0, 50); (0x39c20, 17); (0x39c60, 37); (0x39cc0, 14); (0x39ce0, 17); (0x39d20, 13); (0x39d40, 11); (0x39d60, 13); (0x39d80, 27); (0x39e00, 17); (0x39e40, 21); (0x39e80, 13); (0x39ea0, 23); (0x39ee0, 60); (0x39f80, 20); (0x39fc0, 25); (0x3a000, 30); (0x3a040, 13); (0x3a060, 30); (0x3a0a0, 34); (0x3a100, 22); (0x3a140, 28); (0x3a180, 18); (0x3a1c0, 17); (0x3a200, 24); (0x3a240, 23); (0x3a2c0, 16); (0x3a2e0, 17); (0x3a320, 16); (0x3a340, 14); (0x3a360, 16); (0x3a380, 17); (0x3a3c0, 17); (0x3a400, 13); (0x3a420, 17); (0x3a460, 20); (0x3a4a0, 23); (0x3a4e0, 11); (0x3a500, 41); (0x3a560, 6); (0x3a580, 43); (0x3a5e0, 45); (0x3a640, 56); (0x3a6a0, 54); (0x3a700, 54); (0x3a760, 57); (0x3a7c0, 42); (0x3a820, 55); (0x3a880, 47); (0x3a8e0, 60); (0x3a940, 10); (0x3a960, 10); (0x3a980, 30); (0x3a9c0, 68); (0x3aa40, 22); (0x3aa80, 37); (0x3aae0, 38); (0x3ab40, 39); (0x3aba0, 37); (0x33d00, 132); (0x33dc0, 132); (0x34360, 20); (0x34720, 4); (0x34740, 12); (0x347a0, 56); (0x35740, 56); (0x389e0, 160)].

Record art_facts : Prop := mkAF {
  af_client_consts : forall Σ m, ART RT Σ m -> client_consts m;
  (* [comment removed for export] *)
  af_frame : forall Σ (m m' : mem) (sp : Z), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= sp ->
    (forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> m' a = m a) ->
    wmono asegs m m' -> ART RT Σ m';
  (* [comment removed for export] *)
  af_with_fds : forall Σ mo fds, ARTM RT Σ mo -> ARTM RT Σ (with_fds fds mo);
  af_mat_stable : forall Σ, mat_stable (ARTM RT Σ);
  (* [comment removed for export] *)
  af_acc_live : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> wr_at asegs m p n /\ acc asegs m p n;
  (* [comment removed for export] *)
  af_live_slack : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
    exists slack, bytes_at asegs m (p + n) slack /\ (- (p + n)) mod 8 <= Z.of_nat (length slack)
      /\ p + n + Z.of_nat (length slack) <= rt_sp0 RT Σ - STACK_WIN;
  (* [comment removed for export] *)
  af_acc_stack : forall Σ m a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= a -> a + n <= USTACK_TOP -> acc asegs m a n;
  (* [comment removed for export] *)
  af_acc_static : forall Σ m a n, ART RT Σ m -> 0 <= a ->
    (forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x1d4090 <= a + i < 0x1e1450)) -> acc asegs m a n;
  (* [comment removed for export] *)
  af_live_range : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
    0 < p /\ p + n <= rt_sp0 RT Σ - STACK_WIN /\ (p + n <= 0x10000 \/ SEGTOP_A <= p);
  af_live_disj : forall Σ m p1 n1 p2 n2 l1 l2, ART RT Σ m -> rt_live RT Σ = l1 ++ (p1, n1) :: l2 -> In (p2, n2) (l1 ++ l2) ->
    p1 + n1 <= p2 \/ p2 + n2 <= p1;
  af_frames_range : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
    0 < f /\ f + fs_size k <= rt_sp0 RT Σ - STACK_WIN /\ (f + fs_size k <= 0x10000 \/ SEGTOP_A <= f)
    /\ forall p n, In (p, n) (rt_live RT Σ) -> f + fs_size k <= p \/ p + n <= f;
  af_sp0_range : forall Σ m, ART RT Σ m -> SEGTOP_A + STACK_WIN <= rt_sp0 RT Σ <= USTACK_TOP;
  (* [comment removed for export] *)
  af_sp0_win : forall Σ m, ART RT Σ m -> 0x7fff80000000 <= rt_sp0 RT Σ;
  (* [comment removed for export] *)
  af_frame_release : forall Σ (m : mem) f k fr, ART RT Σ m -> rt_frames RT Σ = (f, k) :: fr ->
    exists (Σ' : rts RT) (fl : Z), rw_cells asegs m fl [C1 (Z_to_bv 8 1)]
      /\ ~ aclient (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP fl
      (* [comment removed for export] *)
      /\ 0 < fl /\ fl + 1 <= rt_sp0 RT Σ - STACK_WIN
      (* [comment removed for export] *)
      /\ ro_cells asegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 fl)]
      /\ forall m', munch [(fl, fl + 1)] m m' -> wmono asegs m m' -> rw_cells asegs m' fl [C1 (Z_to_bv 8 0)] ->
           ART RT Σ' m' /\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
           /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_allow RT Σ' = rt_allow RT Σ /\ (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo);
  (* [comment removed for export] *)
  af_frames_align : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f mod 64 = 0 /\ SEGTOP_A <= f;
  af_frames_disj : forall Σ m f1 k1 f2 k2 l1 l2, ART RT Σ m -> rt_frames RT Σ = l1 ++ (f1, k1) :: l2 -> In (f2, k2) (l1 ++ l2) ->
    f1 + fs_size k1 <= f2 \/ f2 + fs_size k2 <= f1;
  af_fshadow_apart : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
    (forall p n, In (p, n) (rt_live RT Σ) -> p + n <= shad f \/ shad (f + fs_size k) <= p)
    /\ (forall f' k', In (f', k') (rt_frames RT Σ) -> f' + fs_size k' <= shad f \/ shad (f + fs_size k) <= f');
  (* [comment removed for export] *)
  af_got_lib : forall Σ m, ART RT Σ m ->
    ro_cells asegs m 0x1d0088 [C8 (Z_to_bv 64 0x1d3c40)] /\ ro_cells asegs m 0x1d0238 [C8 (Z_to_bv 64 0x737ef8)];
  (* [comment removed for export] *)
  af_acc_lits : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) ACC_LITS;
  (* [comment removed for export] *)
  af_frames_hi : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f;
  (* [comment removed for export] *)
  af_live_align : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p mod 16 = 0
}.

Record rt_contracts : Prop := mkRTC {
  rc_malloc : malloc_contract;
  rc_free : free_contract;
  rc_free_null : free_null_contract;
  rc_memcpy : memcpy_icontract e_memcpy;
  rc_asan_memcpy : memcpy_icontract e_asan_memcpy;
  rc_memset : memset_icontract e_memset;
  rc_asan_memset : memset_icontract e_asan_memset;
  rc_memchr : memchr_icontract;
  rc_strlen : strlen_icontract;
  rc_strnlen : strnlen_icontract;
  rc_stack_malloc_0 : stack_malloc_contract 0;
  rc_stack_malloc_1 : stack_malloc_contract 1;
  rc_stack_malloc_4 : stack_malloc_contract 4;
  rc_stack_malloc_6 : stack_malloc_contract 6;
  rc_set_shadow : forall v, In v set_shadow_vals -> set_shadow_contract v;
  rc_facts : art_facts
}.

End Contracts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PMfd (F0 : list (word * FdEntry)) (fs0 : Fs) : Model -> Prop := fun mo => m_fds mo = F0 /\ m_fs mo = fs0.

Lemma PMfd_fdfs_only : forall F0 fs0, fdfs_only (PMfd F0 fs0).
Proof. intros F0 fs0 mo mo' E1 E2 [H1 H2]. split; congruence. Qed.

(* [comment removed for export] *)
Definition rt_pres_fp (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (W : list (Z * Z)) (m m' : mem) : Prop :=
  forall a : word, aclient live frames sp (bv_unsigned a) -> outside W (bv_unsigned a) -> m' a = m a.

(* [comment removed for export] *)
Definition errno_cell (tp : word) : Z := bv_unsigned tp - 164.

(* [comment removed for export] *)
Definition FMT_usage : Z := 0x1939f.          (* [comment removed for export] *)
Definition FMT_cannot_open : Z := 0x27a98.    (* [comment removed for export] *)
Definition FMT_read_error : Z := 0x27aad.     (* [comment removed for export] *)
Definition FMT_too_big : Z := 0x203bc.        (* [comment removed for export] *)
Definition FMT_emit : Z := 0x177bb.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STDERR_FILE : Z := 0x1d3d98.

(* [comment removed for export] *)
Inductive fp_case : Type :=
| FPusage (argv0 : Z) (s : list byte)       (* [comment removed for export] *)
| FPcannot_open (path : Z) (s : list byte)  (* [comment removed for export] *)
| FPread_error (path : Z) (s : list byte)   (* [comment removed for export] *)
| FPtoo_big.                                (* [comment removed for export] *)

Definition fp_fmt (c : fp_case) : Z :=
  match c with FPusage _ _ => FMT_usage | FPcannot_open _ _ => FMT_cannot_open
             | FPread_error _ _ => FMT_read_error | FPtoo_big => FMT_too_big end.
Definition fp_arg (c : fp_case) : Z :=
  match c with FPusage a _ | FPcannot_open a _ | FPread_error a _ => a | FPtoo_big => 67108864 end.
(* [comment removed for export] *)
Definition fp_str (c : fp_case) : option (Z * list byte) :=
  match c with FPusage a s | FPcannot_open a s | FPread_error a s => Some (a, s) | FPtoo_big => None end.
(* [comment removed for export] *)
Definition fp_msg (c : fp_case) : list Z :=
  match c with
  | FPusage _ s => msg_usage (map bv_unsigned s)
  | FPcannot_open _ s => msg_cannot_open (map bv_unsigned s)
  | FPread_error _ s => msg_read_error (map bv_unsigned s)
  | FPtoo_big => msg_too_big
  end.

(* [comment removed for export] *)
Definition so_lines (k : nat) : stdout_st := mkStdout true (zeros_out k) false false.

(* [comment removed for export] *)
Definition io_ssp (m : mem) : Prop :=
  exists g : word, ro_cells asegs m 0x1d0238 [C8 (Z_to_bv 64 0x737ef8)] /\ ro_cells asegs m 0x737ef8 [C8 g].

Section IO.
Variable RT : rt_sig.
(* [comment removed for export] *)
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
(* [comment removed for export] *)
Variable IO_FP : list (Z * Z).

(* [comment removed for export] *)
Definition read_icontract_file : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (fd buf count : Z) p off data (lo : Z),
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
  buf = g_read_stage (* [comment removed for export] *) ->
  3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
  fd_lookup F0 (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup fs0 p = Some data ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  let bs := file_read data off (Z_to_bv 64 count) in
  cps asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                    s10 s11 t3 t4 t5 t6 F fc e_read m)))
    (ASTA RT Σ (PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0)
       (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (len_word bs) m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(buf, buf + Z.of_nat (length bs))] m m'
          /\ bytes_at asegs m' buf bs)).

(* [comment removed for export] *)
Definition read_icontract_dir : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (fd buf count : Z) (lo : Z),
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
  buf = g_read_stage (* [comment removed for export] *) ->
  3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
  fd_lookup F0 (Z_to_bv 64 fd) = Some FdDir ->
  (forall i, 0 <= i < 4 -> client_static (errno_cell tp + i)) ->
  tp = Z_to_bv 64 0x717eb8 -> (exists v, rw_cells asegs m (errno_cell tp) [C4 v]) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                    s10 s11 t3 t4 t5 t6 F fc e_read m)))
    (ASTA RT Σ (PMfd F0 fs0)
       (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(errno_cell tp, errno_cell tp + 4)] m m')).

(* [comment removed for export] *)
Definition fprintf_stderr_icontract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (c : fp_case) (errp : Z) (lo : Z),
  a0 = Z_to_bv 64 errp -> a1 = Z_to_bv 64 (fp_fmt c) -> a2 = Z_to_bv 64 (fp_arg c) ->
  errp = STDERR_FILE ->
  (forall a s, fp_str c = Some (a, s) -> bytes_at asegs m a (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
       /\ Z.of_nat (length s) < 131072 /\ checked_src RT Σ m sp lo a (Z.of_nat (length s) + 1)
       (* [comment removed for export] *)
       /\ bv_unsigned sp <= a
       /\ exists slack, bytes_at asegs m (a + Z.of_nat (length s) + 1) slack
            /\ (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
            /\ a + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16) ->
  fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  ERR_rep m -> io_ssp m ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_fprintf m)))
    (evw 2 (fp_msg c))
    (ASTA RT Σ (PMfd F0 fs0)
       (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
          /\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m'))).

(* [comment removed for export] *)
Definition fwrite_stderr_icontract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (sa : Z) (s : list byte) (errp : Z) (lo : Z),
  a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 (Z.of_nat (length s)) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 errp ->
  errp = STDERR_FILE -> 0 < Z.of_nat (length s) <= 64 ->
  (sa = 0x2b544 \/ sa = 0x193b0) (* [comment removed for export] *) ->
  bytes_at asegs m sa s -> checked_src RT Σ m sp lo sa (Z.of_nat (length s)) ->
  fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  ERR_rep m -> io_ssp m ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_fwrite m)))
    (evw 2 (map bv_unsigned s))
    (ASTA RT Σ (PMfd F0 fs0)
       (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
          /\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m'))).

(* [comment removed for export] *)
Definition emit0_out (so : stdout_st) : list Z := if so_first so then [48; 10] else [].
Definition emit0_next (so : stdout_st) : stdout_st :=
  if so_first so then so_lines 0 else mkStdout true (so_buf so ++ [48; 10]) false false.

Definition vprintf_emit0_icontract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (so : stdout_st) (ap : Z) (lo : Z),
  a0 = Z_to_bv 64 FMT_emit -> a1 = Z_to_bv 64 ap ->
  rw_cells asegs m ap [C8 (Z_to_bv 64 0)] (* [comment removed for export] *) ->
  ap = bv_unsigned sp + 24 (* [comment removed for export] *) ->
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  OUT_rep so m -> io_ssp m ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_vprintf m)))
    (evw 1 (emit0_out so))
    (ASTA RT Σ (PMfd F0 fs0)
       (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
          /\ OUT_rep (emit0_next so) m' /\ (ERR_rep m -> ERR_rep m'))).

(* [comment removed for export] *)
Definition FMT_msg_A : Z := 0x2bb70.
(* [comment removed for export] *)
Definition msg_text (str1 : list byte) (line : Z) (str2 : list byte) : list Z :=
  concat (PrintfFormats.pieces_msg (map bv_unsigned str1) line (map bv_unsigned str2)).

(* [comment removed for export] *)
Definition vsn_str (Σ : rts RT) (m : mem) (sp : word) (lo D dn S : Z) (str : list byte) : Prop :=
  exists slack : list byte,
    bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str
    /\ (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ 0 < S /\ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo
    /\ checked_src RT Σ m sp lo S (Z.of_nat (length str) + 1)
    /\ (D + dn <= S \/ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= D).

(* [comment removed for export] *)
Definition vsnprintf_msg_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (D n ap S1 S2 line : Z) (str1 str2 junk : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMT_msg_A -> a3 = Z_to_bv 64 ap ->
  rw_cells asegs m ap [C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 line); C8 (Z_to_bv 64 S2)] (* [comment removed for export] *) ->
  bv_unsigned sp <= ap -> ap + 24 <= USTACK_TOP ->
  let o := msg_text str1 line str2 in
  vsn_str Σ m sp lo D (zlength o + 1) S1 str1 -> vsn_str Σ m sp lo D (zlength o + 1) S2 str2 -> 0 <= line < 2^64 ->
  zlength o <= 80 -> zlength o < n -> n < 2^31 ->
  rw_cells asegs m D [CB (Z.to_nat (zlength o + 1)) junk] -> checked_dst RT Σ m sp D (zlength o + 1) ->
  (D + zlength o + 1 <= lo \/ bv_unsigned sp <= D) -> SEGTOP_A <= D -> (D + zlength o + 1 <= ap \/ ap + 24 <= D) ->
  io_ssp m -> ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_vsnprintf m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (zlength o)) lo D (zlength o + 1) m
               (fun m' => bytes_at asegs m' D (map (Z_to_bv 8) o ++ [Z_to_bv 8 0]))).

Record io_contracts : Prop := mkIOC {
  ioc_read_file : read_icontract_file;
  ioc_read_dir : read_icontract_dir;
  ioc_fprintf : fprintf_stderr_icontract;
  ioc_fwrite : fwrite_stderr_icontract;
  ioc_vprintf : vprintf_emit0_icontract
}.

End IO.
