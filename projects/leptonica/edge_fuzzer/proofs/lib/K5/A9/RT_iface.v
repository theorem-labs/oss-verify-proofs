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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Spec Require Import Prelim StrFun Canon Stdio.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Spec Require PrintfFormats.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow IcptSpec.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SEGTOP_A : Z := 0x72e000.
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
Definition e_malloc : Z := 0xb85e4.        (* [comment removed for export] *)
Definition e_free : Z := 0xb85e0.          (* [comment removed for export] *)
Definition e_strdup : Z := 0x973ec.        (* [comment removed for export] *)
Definition e_strndup : Z := 0x97364.       (* [comment removed for export] *)
Definition e_strlen : Z := 0xa23b4.        (* [comment removed for export] *)
Definition e_strnlen : Z := 0xa23b8.       (* [comment removed for export] *)
Definition e_strncmp : Z := 0x9736c.       (* [comment removed for export] *)
Definition e_memchr : Z := 0xa23d0.        (* [comment removed for export] *)
Definition e_memset : Z := 0xb6a54.        (* [comment removed for export] *)
Definition e_memcpy : Z := 0xb6a5c.        (* [comment removed for export] *)
Definition e_asan_memcpy : Z := 0xb6a60.   (* [comment removed for export] *)
Definition e_asan_memset : Z := 0xb6efc.   (* [comment removed for export] *)
Definition e_read : Z := 0xa23d8.          (* [comment removed for export] *)
Definition e_fwrite : Z := 0xa23e4.        (* [comment removed for export] *)
Definition e_vprintf : Z := 0xa2404.       (* [comment removed for export] *)
Definition e_vfprintf : Z := 0xa2408.      (* [comment removed for export] *)
Definition e_vsnprintf : Z := 0xa240c.     (* [comment removed for export] *)
Definition e_fprintf : Z := 0xa2410.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stack_malloc (k : nat) : Z :=
  match k with 0%nat => 0x9cacc | 1%nat => 0x9cc40 | 4%nat => 0x9d118 | _ => 0x9d2e4 end.
(* [comment removed for export] *)
Definition set_shadow_vals : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 0xf1; 0xf2; 0xf3; 0xf5; 0xf8].
Definition e_set_shadow (v : Z) : Z :=
  match v with
  | 0 => 0xba80c | 1 => 0xba824 | 2 => 0xba83c | 3 => 0xba854 | 4 => 0xba86c | 5 => 0xba884 | 6 => 0xba89c
  | 7 => 0xba8b4 | 241 => 0xba8cc | 242 => 0xba8e4 | 243 => 0xba8fc | 245 => 0xba914 | _ => 0xba92c
  end.

(* [comment removed for export] *)
Definition fs_size (k : nat) : Z := Z.shiftl 64 (Z.of_nat k).

(* [comment removed for export] *)
Definition ALLOC_RAS : list Z :=
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  [0xe6c30; 0xe6c84; 0xe6ca8; 0xe6dd8; 0xe6f10; 0xe6fa4; 0xe90c0; 0xe90e8; 0xe9164; 0xeebec; 0xeecc8; 0xeecd0; 0xeee50; 0xeee58; 0xf2560; 0xf9550; 0xf9558; 0xfb578; 0xfb5bc].

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
Definition CLIENT_STATIC : list (Z * Z) := [ (0x1c81f0, 0x1d5a58) (* [comment removed for export] *) ;
                                              (0x6fb710, 0x70b710) (* [comment removed for export] *) ;
                                              (0x70b710, 0x72dd18) (* [comment removed for export] *) ].
(* [comment removed for export] *)
Definition RT_STATIC : list (Z * Z) :=
  [(* [comment removed for export] *)
   (0x1c8424, 0x1c8440); (0x1c8448, 0x1c8460); (0x1c8464, 0x1c8480); (0x1c8488, 0x1c84a0); (0x1c84a8, 0x1c84c0); (0x1c84c8, 0x1c84e0); (0x1c84e4, 0x1c8500); (0x1c8504, 0x1c8520);
   (0x70c3e0, 0x70c3e8); (0x70c430, 0x70c460); (0x70c468, 0x70c478); (0x72d7e0, 0x72d7e8);
   (* [comment removed for export] *)
   (0x72c6f8, 0x72c700)].

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
  1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x70c438 ->
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
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x70c438 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

(* [comment removed for export] *)
Definition free_null_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x70c438 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (fun c => exists v, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

(* [comment removed for export] *)
Definition strdup_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s : Z) (str : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> tp = Z_to_bv 64 0x70c438 ->
  bytes_at asegs m s (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 < 2^27 ->
  rng_class RT Σ s (Z.of_nat (length str) + 1) -> acc asegs m s (Z.of_nat (length str) + 1) ->
  ((forall i, 0 <= i < Z.of_nat (length str) + 1 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (s + i))
   \/ (0x10000 <= s /\ s + Z.of_nat (length str) + 1 <= 0x1bd000) (* [comment removed for export] *)) ->
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
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 k -> tp = Z_to_bv 64 0x70c438 ->
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
  fdfs_only PMc -> mat_stable PMc -> (k <= 10)%nat -> tp = Z_to_bv 64 0x70c438 ->
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
  [(0x30e00, 14); (0x30e20, 10); (0x30e40, 16); (0x30e60, 29); (0x30f60, 39); (0x30fc0, 16); (0x30fe0, 18); (0x31020, 19); (0x310c0, 12); (0x310e0, 24); (0x312c0, 11); (0x31460, 16); (0x31480, 12); (0x31500, 13); (0x31560, 12); (0x315c0, 17); (0x31680, 10); (0x317e0, 15); (0x31800, 22); (0x31880, 11); (0x31a80, 16); (0x31c60, 14); (0x323c0, 15); (0x323e0, 19); (0x32420, 15); (0x32440, 17); (0x32480, 23); (0x327e0, 22); (0x32820, 15); (0x32b40, 17); (0x32cc0, 15); (0x32ce0, 29); (0x32d20, 11); (0x32d40, 14); (0x32e20, 17); (0x32f20, 22); (0x32f60, 20); (0x32fa0, 37); (0x33b00, 19); (0x33b40, 8); (0x33b60, 16); (0x36c20, 13); (0x36c40, 17); (0x36e60, 25); (0x36f00, 18); (0x36f40, 14); (0x36f60, 15); (0x36f80, 15); (0x36fa0, 16); (0x36fc0, 22); (0x37080, 14); (0x370a0, 18); (0x370e0, 25); (0x2dec0, 17); (0x31060, 47); (0x31120, 48); (0x31180, 52); (0x311e0, 53); (0x31260, 37); (0x32360, 37); (0x31c80, 27); (0x324c0, 37); (0x32520, 47); (0x32580, 46); (0x325e0, 31); (0x32620, 51); (0x32680, 56); (0x326e0, 58); (0x32740, 77); (0x36ea0, 35); (0x37000, 84); (0x31cc0, 132); (0x2df00, 31); (0x2df40, 18); (0x2df80, 22); (0x2dfc0, 19); (0x2e000, 20); (0x2e040, 18); (0x2e080, 19); (0x2e0c0, 13); (0x2e0e0, 13); (0x2e140, 32); (0x2e180, 10); (0x2e1a0, 14); (0x2e1c0, 17); (0x2e200, 11); (0x2e220, 18); (0x2e260, 14); (0x2e280, 20); (0x2e2c0, 13); (0x2e2e0, 46); (0x2e340, 10); (0x2e360, 24); (0x2e3a0, 26); (0x2e3e0, 17); (0x2e420, 11); (0x2e440, 21); (0x2e480, 15); (0x2e4a0, 33); (0x2e500, 18); (0x2e540, 31); (0x2e580, 23); (0x2e5c0, 11); (0x2e5e0, 17); (0x2e620, 20); (0x2e660, 13); (0x2e680, 21); (0x2e6c0, 23); (0x2e700, 20); (0x2e740, 19); (0x2e780, 15); (0x2e7a0, 35); (0x2e800, 19); (0x2e840, 25); (0x2e880, 19); (0x2e8c0, 46); (0x2e920, 21); (0x2e960, 49); (0x2e9c0, 18); (0x2ea00, 16); (0x2ea20, 14); (0x2ea40, 26); (0x2ea80, 14); (0x2eaa0, 18); (0x2eae0, 13); (0x2eb00, 16); (0x2eb20, 18); (0x2eb60, 3); (0x2eb80, 65); (0x2ec00, 15); (0x2ec20, 17); (0x2ec60, 34); (0x2ecc0, 2); (0x2ece0, 5); (0x2ed00, 28); (0x2ed40, 12); (0x2ed60, 1); (0x2ed80, 21); (0x2edc0, 9); (0x2ede0, 23); (0x2ee20, 17); (0x2ee60, 22); (0x2eea0, 9); (0x2eec0, 12); (0x2eee0, 21); (0x2ef20, 17); (0x2ef60, 17); (0x2efa0, 19); (0x2efe0, 16); (0x2f000, 46); (0x2f060, 23); (0x2f0a0, 19); (0x2f0e0, 13); (0x2f100, 15); (0x2f160, 22); (0x2f1a0, 12); (0x2f1c0, 36); (0x2f220, 13); (0x2f240, 15); (0x2f260, 15); (0x2f280, 17); (0x2f2c0, 14); (0x2f2e0, 27); (0x2f320, 17); (0x2f360, 15); (0x2f380, 16); (0x2f3a0, 18); (0x2f3e0, 15); (0x2f400, 15); (0x2f420, 15); (0x2f440, 17); (0x2f480, 33); (0x2f520, 20); (0x2f560, 14); (0x2f580, 36); (0x2f5e0, 15); (0x2f600, 26); (0x2f640, 32); (0x2f680, 41); (0x2f6e0, 15); (0x2f700, 12); (0x2f720, 16); (0x2f740, 17); (0x2f780, 17); (0x2f7c0, 19); (0x2f800, 27); (0x2f840, 13); (0x2f860, 17); (0x2f8a0, 28); (0x2f8e0, 18); (0x2f960, 19); (0x2f9a0, 13); (0x2f9c0, 37); (0x2fa20, 14); (0x2fa40, 15); (0x2fa60, 16); (0x2fa80, 19); (0x2fac0, 17); (0x2fb00, 17); (0x2fb40, 15); (0x2fb60, 16); (0x2fb80, 16); (0x2fba0, 15); (0x2fbc0, 20); (0x2fc00, 18); (0x2fc40, 1); (0x2fc60, 2); (0x2fc80, 2); (0x2fca0, 2); (0x2fcc0, 16); (0x2fce0, 14); (0x2fd00, 14); (0x2fd20, 18); (0x2fd60, 16); (0x2fd80, 23); (0x2fdc0, 18); (0x2fe00, 37); (0x2fe60, 27); (0x2fee0, 16); (0x2ff00, 16); (0x2ff20, 10); (0x2ff80, 22); (0x2ffc0, 11); (0x2ffe0, 36); (0x30040, 12); (0x30060, 15); (0x30080, 14); (0x300a0, 17); (0x300e0, 13); (0x30100, 27); (0x30140, 17); (0x30180, 14); (0x301a0, 16); (0x301c0, 18); (0x30200, 14); (0x30220, 16); (0x30240, 21); (0x30280, 28); (0x30340, 16); (0x30360, 9); (0x30380, 18); (0x303c0, 4); (0x303e0, 18); (0x30420, 26); (0x30460, 19); (0x304a0, 15); (0x304c0, 15); (0x30520, 22); (0x30560, 10); (0x30580, 24); (0x305c0, 24); (0x30600, 16); (0x30620, 37); (0x30680, 11); (0x306a0, 15); (0x306c0, 15); (0x30720, 36); (0x30780, 11); (0x307a0, 19); (0x307e0, 36); (0x30840, 12); (0x30860, 58); (0x308c0, 15); (0x308e0, 8); (0x30900, 17); (0x30940, 18); (0x30980, 11); (0x309a0, 26); (0x309e0, 17); (0x30a20, 30); (0x30a60, 16); (0x30a80, 27); (0x30b00, 29); (0x30b40, 10); (0x30b60, 37); (0x30bc0, 11); (0x30be0, 16); (0x30c00, 9); (0x30c20, 17); (0x30c60, 9); (0x30c80, 14); (0x30ca0, 9); (0x30cc0, 16); (0x30ce0, 34); (0x30d40, 25); (0x30d80, 25); (0x30ea0, 17); (0x30ee0, 18); (0x30f20, 24); (0x31240, 9); (0x312e0, 8); (0x31300, 28); (0x31340, 19); (0x31380, 17); (0x313c0, 16); (0x313e0, 31); (0x31420, 15); (0x31440, 15); (0x314a0, 12); (0x314c0, 19); (0x31520, 13); (0x31540, 15); (0x31580, 12); (0x315a0, 15); (0x31600, 10); (0x31620, 10); (0x31640, 17); (0x316a0, 11); (0x316c0, 11); (0x316e0, 18); (0x31720, 18); (0x31760, 19); (0x317a0, 11); (0x317c0, 15); (0x31840, 19); (0x31a20, 17); (0x31a60, 12); (0x31aa0, 37); (0x31b00, 12); (0x31b20, 17); (0x31b60, 19); (0x31ba0, 56); (0x31c00, 64); (0x31d80, 14); (0x31da0, 19); (0x31de0, 16); (0x31e00, 13); (0x31e20, 23); (0x31e60, 17); (0x31ea0, 29); (0x31ee0, 17); (0x31f20, 19); (0x31f60, 16); (0x31f80, 17); (0x31fc0, 21); (0x32000, 18); (0x32040, 24); (0x32080, 35); (0x320e0, 17); (0x32120, 29); (0x32160, 19); (0x321e0, 23); (0x32220, 14); (0x32240, 22); (0x32280, 20); (0x322c0, 16); (0x322e0, 18); (0x32320, 12); (0x32340, 13); (0x327c0, 16); (0x32840, 16); (0x32860, 36); (0x328c0, 16); (0x328e0, 20); (0x32920, 15); (0x32940, 19); (0x32980, 16); (0x329a0, 20); (0x329e0, 16); (0x32a00, 27); (0x32a40, 24); (0x32a80, 23); (0x32ac0, 18); (0x32b00, 21); (0x32b80, 18); (0x32bc0, 36); (0x32c20, 16); (0x32c40, 25); (0x32c80, 21); (0x32d60, 20); (0x32da0, 10); (0x32dc0, 5); (0x32e60, 21); (0x32ea0, 24); (0x32ee0, 31); (0x331e0, 17); (0x33220, 15); (0x33240, 14); (0x33260, 18); (0x332a0, 54); (0x33300, 27); (0x33340, 32); (0x33380, 25); (0x333c0, 55); (0x33420, 28); (0x33460, 42); (0x334c0, 30); (0x33500, 20); (0x33540, 13); (0x33560, 23); (0x335a0, 20); (0x335e0, 16); (0x33600, 59); (0x33660, 16); (0x33680, 16); (0x336a0, 15); (0x336c0, 18); (0x33700, 16); (0x33720, 16); (0x33740, 19); (0x33780, 15); (0x337a0, 15); (0x337c0, 15); (0x337e0, 15); (0x33800, 15); (0x33820, 15); (0x33840, 29); (0x33880, 14); (0x338a0, 15); (0x338c0, 33); (0x33920, 16); (0x33940, 17); (0x33980, 16); (0x339a0, 20); (0x339e0, 34); (0x33a80, 17); (0x33ac0, 10); (0x33ae0, 14); (0x33bc0, 17); (0x33c00, 12); (0x33c20, 17); (0x33c60, 31); (0x33f00, 34); (0x33f60, 22); (0x33fa0, 22); (0x34020, 18); (0x34060, 18); (0x340a0, 17); (0x340e0, 21); (0x34120, 24); (0x34160, 15); (0x34180, 25); (0x341c0, 29); (0x34200, 16); (0x34220, 21); (0x34260, 50); (0x34300, 21); (0x34340, 20); (0x34380, 15); (0x343a0, 15); (0x343c0, 14); (0x34460, 19); (0x344a0, 13); (0x344c0, 37); (0x34520, 6); (0x34540, 33); (0x345e0, 19); (0x34620, 20); (0x34660, 21); (0x346a0, 15); (0x346c0, 38); (0x34720, 21); (0x34760, 24); (0x347e0, 17); (0x348e0, 21); (0x34920, 19); (0x34960, 2); (0x34980, 15); (0x349a0, 16); (0x349c0, 2); (0x349e0, 21); (0x34a20, 43); (0x34a80, 72); (0x34b00, 16); (0x34b20, 18); (0x34b60, 3); (0x34b80, 22); (0x34bc0, 13); (0x34be0, 15); (0x34c00, 45); (0x34c60, 33); (0x34cc0, 18); (0x34d00, 22); (0x34d40, 20); (0x34d80, 18); (0x34dc0, 22); (0x34e00, 20); (0x34e40, 25); (0x34e80, 26); (0x34ec0, 16); (0x34ee0, 17); (0x34f20, 28); (0x34f60, 34); (0x34fc0, 41); (0x35020, 19); (0x35060, 21); (0x350a0, 55); (0x35100, 61); (0x35160, 53); (0x351c0, 37); (0x35220, 24); (0x35260, 20); (0x352a0, 23); (0x352e0, 25); (0x35320, 25); (0x35360, 6); (0x35380, 9); (0x353a0, 57); (0x35400, 12); (0x35420, 9); (0x35440, 3); (0x35460, 23); (0x354a0, 26); (0x354e0, 9); (0x35500, 8); (0x35520, 3); (0x35540, 10); (0x35560, 4); (0x35580, 18); (0x355c0, 6); (0x355e0, 17); (0x35620, 33); (0x35680, 24); (0x356c0, 38); (0x35720, 10); (0x35740, 23); (0x35780, 11); (0x357a0, 9); (0x35860, 21); (0x358a0, 18); (0x35920, 21); (0x35960, 13); (0x35980, 19); (0x35a00, 21); (0x35a40, 21); (0x35a80, 20); (0x35ac0, 15); (0x35ae0, 21); (0x35b20, 19); (0x35b60, 16); (0x35b80, 26); (0x35bc0, 33); (0x35c20, 19); (0x35c60, 18); (0x35ca0, 16); (0x35cc0, 13); (0x35ce0, 4); (0x35d00, 26); (0x35d40, 16); (0x35d60, 19); (0x35da0, 17); (0x35de0, 50); (0x35e40, 69); (0x35ec0, 41); (0x35f20, 13); (0x35f40, 53); (0x35fa0, 26); (0x36020, 21); (0x36060, 19); (0x360e0, 19); (0x36120, 18); (0x36160, 16); (0x36180, 51); (0x361e0, 12); (0x36200, 19); (0x36240, 15); (0x36260, 19); (0x362a0, 17); (0x362e0, 22); (0x36320, 35); (0x36380, 63); (0x363e0, 24); (0x36460, 7); (0x36480, 17); (0x364c0, 18); (0x36500, 19); (0x36540, 22); (0x36580, 16); (0x365a0, 16); (0x365c0, 18); (0x36600, 14); (0x366e0, 15); (0x36700, 18); (0x36740, 16); (0x36760, 28); (0x367a0, 66); (0x36820, 69); (0x368a0, 70); (0x36920, 17); (0x36960, 18); (0x369a0, 66); (0x36a20, 10); (0x36a40, 11); (0x36a60, 10); (0x36a80, 11); (0x36aa0, 24); (0x36ae0, 20); (0x36b20, 14); (0x36b40, 20); (0x36b80, 8); (0x36be0, 19); (0x36c80, 19); (0x36cc0, 16); (0x36ce0, 31); (0x36d20, 35); (0x36d80, 21); (0x36dc0, 17); (0x36e00, 19); (0x36e40, 14); (0x37160, 21); (0x371a0, 15); (0x371c0, 21); (0x37200, 16); (0x37220, 13); (0x37240, 17); (0x37280, 18); (0x372c0, 10); (0x372e0, 13); (0x37300, 5); (0x37320, 27); (0x37360, 25); (0x373a0, 25); (0x373e0, 28); (0x37420, 25); (0x37460, 20); (0x374a0, 18); (0x374e0, 19); (0x37520, 33); (0x37580, 22); (0x375c0, 43); (0x37620, 60); (0x37680, 48); (0x376e0, 46); (0x37800, 18); (0x37840, 18); (0x37880, 25); (0x378c0, 16); (0x378e0, 23); (0x37920, 18); (0x37960, 18); (0x379a0, 35); (0x37a00, 15); (0x37a60, 18); (0x37aa0, 20); (0x37ae0, 20); (0x37b20, 16); (0x37b40, 16); (0x37b60, 13); (0x37b80, 13); (0x37ba0, 20); (0x37be0, 17); (0x37c20, 14); (0x37c40, 18); (0x37c80, 16); (0x37ca0, 52); (0x37d00, 55); (0x37d60, 55); (0x37dc0, 19); (0x37e00, 19); (0x37e40, 17); (0x37e80, 20); (0x37ec0, 18); (0x37f00, 18); (0x37f40, 19); (0x37f80, 19); (0x37fc0, 18); (0x38000, 19); (0x38040, 16); (0x38060, 17); (0x380a0, 63); (0x38100, 23); (0x38140, 18); (0x38180, 17); (0x381c0, 15); (0x381e0, 18); (0x38220, 49); (0x38280, 19); (0x382c0, 18); (0x38300, 21); (0x38340, 18); (0x38380, 18); (0x383c0, 20); (0x38400, 18); (0x38440, 25); (0x38480, 43); (0x384e0, 20); (0x38520, 21); (0x38560, 18); (0x385a0, 15); (0x385c0, 14); (0x385e0, 16); (0x38600, 10); (0x38620, 50); (0x38680, 12); (0x386a0, 22); (0x386e0, 27); (0x38720, 23); (0x38760, 11); (0x38780, 40); (0x387e0, 24); (0x38820, 11); (0x38840, 53); (0x388a0, 19); (0x388e0, 6); (0x38900, 5); (0x38920, 2); (0x38940, 20); (0x38980, 22); (0x389c0, 16); (0x389e0, 14); (0x38ac0, 25); (0x38b00, 47); (0x38b60, 14); (0x38b80, 52); (0x38be0, 14); (0x38c00, 23); (0x38c40, 40); (0x38ca0, 24); (0x38ce0, 38); (0x38d40, 5); (0x38d60, 6); (0x38d80, 74); (0x38e00, 23); (0x38e40, 24); (0x38e80, 40); (0x38ee0, 20); (0x38f20, 19); (0x38f60, 44); (0x38fc0, 19); (0x39000, 19); (0x39040, 38); (0x390a0, 43); (0x39100, 21); (0x39140, 21); (0x39180, 86); (0x39200, 1); (0x39220, 83); (0x392a0, 14); (0x392c0, 20); (0x39300, 27); (0x39340, 47); (0x393a0, 22); (0x393e0, 21); (0x39420, 18); (0x39460, 21); (0x394a0, 31); (0x394e0, 16); (0x39500, 69); (0x395c0, 18); (0x39600, 14); (0x39620, 37); (0x39680, 15); (0x396a0, 15); (0x396c0, 18); (0x39700, 16); (0x39720, 17); (0x39760, 20); (0x397a0, 16); (0x397c0, 25); (0x39800, 21); (0x39840, 23); (0x39880, 42); (0x398e0, 23); (0x39960, 16); (0x39980, 15); (0x399a0, 16); (0x399c0, 20); (0x39a00, 15); (0x39a20, 17); (0x39a60, 20); (0x39aa0, 22); (0x39ae0, 14); (0x39b40, 68); (0x39bc0, 13); (0x39be0, 50); (0x39c40, 17); (0x39c80, 37); (0x39ce0, 14); (0x39d00, 17); (0x39d40, 13); (0x39d60, 11); (0x39d80, 13); (0x39da0, 27); (0x39e20, 17); (0x39e60, 21); (0x39ea0, 13); (0x39ec0, 23); (0x39f00, 60); (0x39fa0, 20); (0x39fe0, 25); (0x3a020, 30); (0x3a060, 13); (0x3a080, 30); (0x3a0c0, 34); (0x3a120, 22); (0x3a160, 28); (0x3a1a0, 18); (0x3a1e0, 24); (0x3a220, 23); (0x3a2a0, 16); (0x3a2c0, 17); (0x3a300, 16); (0x3a320, 14); (0x3a340, 16); (0x3a360, 17); (0x3a3a0, 17); (0x3a3e0, 13); (0x3a400, 17); (0x3a440, 20); (0x3a480, 23); (0x3a4c0, 11); (0x3a4e0, 41); (0x3a540, 6); (0x3a560, 43); (0x3a5c0, 45); (0x3a620, 56); (0x3a680, 54); (0x3a6e0, 54); (0x3a740, 57); (0x3a7a0, 42); (0x3a800, 55); (0x3a860, 47); (0x3a8c0, 60); (0x3a920, 10); (0x3a940, 10); (0x3a960, 30); (0x3a9a0, 68); (0x3aa20, 22); (0x3aa60, 37); (0x3aac0, 38); (0x3ab20, 39); (0x3ab80, 37); (0x33d80, 132); (0x33e40, 132); (0x343e0, 20); (0x347a0, 4); (0x347c0, 12); (0x34820, 56); (0x357c0, 56); (0x38a00, 160)].

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
    (forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x1c8870 <= a + i < 0x1d59f0)) -> acc asegs m a n;
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
    ro_cells asegs m 0x1c4868 [C8 (Z_to_bv 64 0x1c8420)] /\ ro_cells asegs m 0x1c4a18 [C8 (Z_to_bv 64 0x72c478)];
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
Definition FMT_usage : Z := 0x1930d.          (* [comment removed for export] *)
Definition FMT_cannot_open : Z := 0x27cb9.    (* [comment removed for export] *)
Definition FMT_read_error : Z := 0x27cce.     (* [comment removed for export] *)
Definition FMT_too_big : Z := 0x20360.        (* [comment removed for export] *)
Definition FMT_emit : Z := 0x17742.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STDERR_FILE : Z := 0x1c8578.

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
  exists g : word, ro_cells asegs m 0x1c4a18 [C8 (Z_to_bv 64 0x72c478)] /\ ro_cells asegs m 0x72c478 [C8 g].

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
  tp = Z_to_bv 64 0x70c438 -> (exists v, rw_cells asegs m (errno_cell tp) [C4 v]) ->
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
  (sa = 0x2b765 \/ sa = 0x1931e) (* [comment removed for export] *) ->
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
Definition FMT_msg_A : Z := 0x2bd91.
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
