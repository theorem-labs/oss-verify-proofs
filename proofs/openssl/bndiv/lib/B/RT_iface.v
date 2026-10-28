(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim StrFun Canon Stdio.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require PrintfFormats.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow IcptSpec. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Export GDesc SiteData.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SEGTOP_A : Z := 0xbfd000.
(* [comment removed for export] *)
Definition USTACK_TOP : Z := 0x800000000000.
Definition STACK_WIN : Z := 0x800000.
(* [comment removed for export] *)
Definition RT_STACK : Z := 0x10000.
(* [comment removed for export] *)
Definition LIVE_MAX : Z := 2048.   (* [comment removed for export] *)
Definition FRAMES_MAX : nat := 16.
(* [comment removed for export] *)
Definition mcost (n : Z) : Z := if n <=? 64512 then 0 else 2 * n + 16384.

(* [comment removed for export] *)
Definition e_malloc : Z := 0x1be300.        (* [comment removed for export] *)
Definition e_free : Z := 0x1be2fc.          (* [comment removed for export] *)
Definition e_calloc : Z := 0x1be304.        (* [comment removed for export] *)
Definition e_realloc : Z := 0x1be308.       (* [comment removed for export] *)
Definition e_strlen : Z := 0x1a7524.        (* [comment removed for export] *)
Definition e_strnlen : Z := 0x1a7528.       (* [comment removed for export] *)
Definition e_strncmp : Z := 0x1a7530.       (* [comment removed for export] *)
Definition e_memchr : Z := 0x1a754c.        (* [comment removed for export] *)
Definition e_memset : Z := 0x1bcc34.        (* [comment removed for export] *)
Definition e_memcpy : Z := 0x1bcc38.        (* [comment removed for export] *)
Definition e_asan_memcpy : Z := 0x1bcc3c.   (* [comment removed for export] *)
Definition e_asan_memset : Z := 0x1bd0d8.   (* [comment removed for export] *)
Definition e_read : Z := 0x1a7554.          (* [comment removed for export] *)
Definition e_fwrite : Z := 0x1a755c.        (* [comment removed for export] *)
Definition e_vprintf : Z := 0x1a7574.       (* [comment removed for export] *)
Definition e_vfprintf : Z := 0x1a7578.      (* [comment removed for export] *)
Definition e_fprintf : Z := 0x1a7584.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stack_malloc (k : nat) : Z :=
  match k with 0%nat => 0x1a1378 | 2%nat => 0x1a167c | _ => 0x1a19c4 end.
(* [comment removed for export] *)
Definition set_shadow_vals : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 0xf1; 0xf2; 0xf3; 0xf5; 0xf8].
Definition e_set_shadow (v : Z) : Z :=
  match v with
  | 0 => 0x1c0538 | 1 => 0x1c0550 | 2 => 0x1c0568 | 3 => 0x1c0580 | 4 => 0x1c0598 | 5 => 0x1c05b0 | 6 => 0x1c05c8
  | 7 => 0x1c05e0 | 241 => 0x1c05f8 | 242 => 0x1c0610 | 243 => 0x1c0628 | 245 => 0x1c0640 | _ => 0x1c0658
  end.

(* [comment removed for export] *)
Definition fs_size (k : nat) : Z := Z.shiftl 64 (Z.of_nat k).

(* [comment removed for export] *)

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
Definition CLIENT_STATIC : list (Z * Z) :=   (* [comment removed for export] *)
  [(0x5e6630, 0x6a0398); (0xbc6050, 0xbd6050); (0xbd6050, 0xbfc730)].
(* [comment removed for export] *)
Definition RT_STATIC : list (Z * Z) :=   (* [comment removed for export] *)
  [(0xbdadf8, 0xbdae00); (0xbdae48, 0xbdae90); (0xbfb110, 0xbfb118); (0xbfc1f8, 0xbfc200)].

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
  stk bsegs m lo (bv_unsigned sp) /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + RT_STACK <= bv_unsigned sp
  /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0.

(* [comment removed for export] *)
Definition unwind_ok (ra s0 sp : word) : Prop :=
  In (bv_unsigned ra) ALLOC_RAS
  /\ (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0).

(* [comment removed for export] *)
Definition unwind_ch (m : mem) (ra s0 sp : word) : Prop :=
  exists ras, In (bv_unsigned ra :: ras) SITE_TRACES /\ uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.

Lemma unwind_ok_ch : forall (m : mem) ra s0 sp, unwind_ok ra s0 sp -> unwind_ch m ra s0 sp.
Proof.
  intros m ra s0 sp (H1 & H2). exists []. split.
  - exact (alloc_ras_sites _ H1).
  - cbn [uw_chain]. unfold fp_stop. destruct H2 as [H2|[H2|H2]]; [left; lia | right; left; exact H2 | right; right; exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entry_st (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (pc : Z) (m : mem) : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

(* [comment removed for export] *)
Definition ret_st (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (ret_pc ra) fc' None m' (seg_rom bsegs).

(* [comment removed for export] *)
Definition rt_after (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
  ART RT Σ' m' /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo sp.

(* [comment removed for export] *)
Definition rt_after_f (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
  ART RT Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' lo sp.

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
         /\ wr_at bsegs m' p n /\ acc bsegs m' p n) c
    /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

Definition malloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n <= 0x8000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xbdae50 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_malloc m)))
            (malloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

(* [comment removed for export] *)
Definition malloc_contract_ok : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n <= 0x8000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xbdae50 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_malloc m)))
            (malloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

Lemma malloc_contract_ok_of : malloc_contract -> malloc_contract_ok.
Proof. intros H. unfold malloc_contract_ok. intros. eapply H; try eassumption. apply unwind_ok_ch. assumption. Qed.

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
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0xbdae50 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

(* [comment removed for export] *)
Definition free_contract_ok : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0xbdae50 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

Lemma free_contract_ok_of : free_contract -> free_contract_ok.
Proof. intros H. unfold free_contract_ok. intros. eapply H; try eassumption. apply unwind_ok_ch. assumption. Qed.

(* [comment removed for export] *)
Definition free_null_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0xbdae50 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (fun c => exists v, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

(* [comment removed for export] *)
Definition free_null_contract_ok : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0xbdae50 ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (fun c => exists v, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Lemma free_null_contract_ok_of : free_null_contract -> free_null_contract_ok.
Proof. intros H. unfold free_null_contract_ok. intros. eapply H; try eassumption. apply unwind_ok_ch. assumption. Qed.

(* [comment removed for export] *)
Definition calloc_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (n lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (p : Z),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at bsegs m' p n /\ acc bsegs m' p n /\ bytes_at bsegs m' p (repeat (Z_to_bv 8 0) (Z.to_nat n))) c
    /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

Definition calloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (k sz lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  0 <= k < 2^64 -> 0 <= sz < 2^64 -> 1 <= k * sz <= 64512 ->
  a0 = Z_to_bv 64 k -> a1 = Z_to_bv 64 sz -> tp = Z_to_bv 64 0xbdae50 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (k * sz) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_calloc m)))
            (calloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (k * sz) lo m).

(* [comment removed for export] *)
Definition realloc_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (p n0 n lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (q : Z),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at bsegs m' q n /\ acc bsegs m' q n
         /\ (forall old, bytes_at bsegs m p old -> Z.of_nat (length old) = Z.min n0 n -> bytes_at bsegs m' q old)) c
    /\ rt_live RT Σ' = (q, n) :: live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q + n < USTACK_TOP.

Definition realloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n0 n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n0) (rt_live RT Σ) -> 1 <= n0 <= 64512 -> 1 <= n <= 64512 ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xbdae50 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_realloc m)))
            (realloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p n0 n lo m).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition checked_src (Σ : rts RT) (m : mem) (sp : word) (lo s n : Z) : Prop :=
  (0 < n -> acc bsegs m s n /\ rng_class RT Σ s n) /\ (s + n <= lo \/ bv_unsigned sp <= s).
(* [comment removed for export] *)
Definition checked_dst (Σ : rts RT) (m : mem) (sp : word) (d n : Z) : Prop :=
  (0 < n -> acc bsegs m d n /\ rng_class RT Σ d n)
  /\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (d + i)) /\ wr_at bsegs m d n.

(* [comment removed for export] *)
Definition memcpy_icontract (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
  checked_src Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst Σ m sp d (Z.of_nat (length bs)) ->
  (d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
               (fun m' => bytes_at bsegs m' d bs)).

(* [comment removed for export] *)
Definition memset_icontract (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d n : Z) (c : byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (bv_unsigned c) -> a2 = Z_to_bv 64 n ->
  0 <= d <= 2^47 -> 0 <= n < 2^40 -> checked_dst Σ m sp d n ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d n m
               (fun m' => bytes_at bsegs m' d (repeat c (Z.to_nat n)))).

(* [comment removed for export] *)
Definition memchr_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s cz n : Z) (buf : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 cz -> a2 = Z_to_bv 64 n ->
  0 < s <= 2^47 -> 0 <= cz < 256 -> 0 <= n < 2^40 -> bytes_at bsegs m s buf -> memchr_ok s cz n buf ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) (* [comment removed for export] *) ->
  checked_src Σ m sp lo s (memchr_chk cz n buf) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_memchr m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (memchr_res s cz n buf)) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strlen_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s : Z) (str slack : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s ->
  bytes_at bsegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < s <= 2^47 -> (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  checked_src Σ m sp lo s (Z.of_nat (length str) + 1) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strlen m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length str))) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strnlen_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s n : Z) (buf : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
  0 < s <= 2^47 -> 0 <= n < 2^40 -> bytes_at bsegs m s buf -> strnlen_ok s n buf ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) (* [comment removed for export] *) ->
  checked_src Σ m sp lo s (strnlen_chk n buf) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strnlen m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strnlen_res n buf)) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strncmp_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p1 p2 n : Z) (b1 b2 : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 n ->
  0 < n < 2^31 -> bytes_at bsegs m p1 b1 -> bytes_at bsegs m p2 b2 -> strncmp_ok n b1 b2 ->
  checked_src Σ m sp lo p1 (strncmp_sz n b1 b2) -> checked_src Σ m sp lo p2 (strncmp_sz n b1 b2) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
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
  fdfs_only PMc -> mat_stable PMc -> (k = 0 \/ k = 2 \/ k = 4)%nat -> tp = Z_to_bv 64 0xbdae50 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at bsegs m' f (fs_size k - 8) /\ wr_at bsegs m' (shad f) (fs_size k / 8)) c
       /\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP).

(* [comment removed for export] *)
Definition set_shadow_contract (v : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d n : Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> In v set_shadow_vals -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n ->
  0 <= n < 2^20 -> (forall i, 0 <= i < n -> in_fframe_shadow (rt_frames RT Σ) (d + i)) -> wr_at bsegs m d n ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_set_shadow v) m)))
    (fun c => exists v0, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 lo d n m
               (fun m' => bytes_at bsegs m' d (repeat (Z_to_bv 8 v) (Z.to_nat n))) c).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RELRO_LO : Z := 0x56b000.
Definition RELRO_HI : Z := 0x5e3000.
Definition relro_pristine (m : mem) : Prop := forall a : word, RELRO_LO <= bv_unsigned a < RELRO_HI -> mrd bsegs m a = seg_rom bsegs a.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition client_consts (m : mem) : Prop :=
  ro_cells bsegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
  /\ ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
  /\ ro_cells bsegs m g_GOT_detect_uar [C8 (Z_to_bv 64 g_detect_stack_use_after_return)]
  /\ ro_cells bsegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)]
  /\ relro_pristine m.

(* [comment removed for export] *)
Definition ACC_LITS : list (Z * Z) := [].

Record art_facts : Prop := mkAF {
  af_client_consts : forall Σ m, ART RT Σ m -> client_consts m;
  (* [comment removed for export] *)
  af_frame : forall Σ (m m' : mem) (sp : Z), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= sp ->
    (forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> m' a = m a) ->
    wmono bsegs m m' -> ART RT Σ m';
  (* [comment removed for export] *)
  af_with_fds : forall Σ mo fds, ARTM RT Σ mo -> ARTM RT Σ (with_fds fds mo);
  af_mat_stable : forall Σ, mat_stable (ARTM RT Σ);
  (* [comment removed for export] *)
  af_acc_live : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> wr_at bsegs m p n /\ acc bsegs m p n;
  (* [comment removed for export] *)
  af_live_slack : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
    exists slack, bytes_at bsegs m (p + n) slack /\ (- (p + n)) mod 8 <= Z.of_nat (length slack)
      /\ p + n + Z.of_nat (length slack) <= rt_sp0 RT Σ - STACK_WIN;
  (* [comment removed for export] *)
  af_acc_stack : forall Σ m a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= a -> a + n <= USTACK_TOP -> acc bsegs m a n;
  (* [comment removed for export] *)
  af_acc_static : forall Σ m a n, ART RT Σ m -> 0 <= a ->
    (forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x5e7460 <= a + i < 0x6a0320)
                             /\ ~ (0x5e6660 <= a + i < 0x5e7140) /\ ~ (0xbd6080 <= a + i < 0xbda540)) -> acc bsegs m a n;
  (* [comment removed for export] *)
  af_lib_sh : forall Σ m g, ART RT Σ m -> In g GDESC -> bytes_at bsegs m (shad (gd_beg g)) (ushadow (gd_size g));
  (* [comment removed for export] *)
  af_img_shadow : forall Σ m, ART RT Σ m -> stk bsegs m (shad 0x10000) (shad SEGTOP_A);
  (* [comment removed for export] *)
  af_sh_live : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> bytes_at bsegs m (shad p) (ushadow n);
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
    exists (Σ' : rts RT) (fl : Z), rw_cells bsegs m fl [C1 (Z_to_bv 8 1)]
      /\ ~ aclient (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP fl
      (* [comment removed for export] *)
      /\ 0 < fl /\ fl + 1 <= rt_sp0 RT Σ - STACK_WIN
      (* [comment removed for export] *)
      /\ (fl + 1 <= f \/ f + fs_size k <= fl) /\ (fl + 1 <= 0x10000 \/ SEGTOP_A <= fl) /\ (fl + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= fl)
      (* [comment removed for export] *)
      /\ ro_cells bsegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 fl)]
      /\ forall m', munch [(fl, fl + 1)] m m' -> wmono bsegs m m' -> rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)] ->
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
    ro_cells bsegs m 0x5e2c40 [C8 (Z_to_bv 64 0xbfae90)] /\ ro_cells bsegs m 0x5e2c40 [C8 (Z_to_bv 64 0xbfae90)];
  (* [comment removed for export] *)
  af_acc_lits : forall Σ m, ART RT Σ m -> Forall (fun r => acc bsegs m (fst r) (snd r)) ACC_LITS;
  (* [comment removed for export] *)
  af_frames_hi : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f;
  (* [comment removed for export] *)
  af_live_offshadow : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p;
  (* [comment removed for export] *)
  af_credit_nonneg : forall Σ m, ART RT Σ m -> 0 <= rt_credit RT Σ;
  (* [comment removed for export] *)
  af_tsd : forall Σ m, ART RT Σ m -> rw_cells bsegs m 0xbdadf8 [C8 (Z_to_bv 64 0xbfc1f8)]
}.

Record rt_contracts : Prop := mkRTC {
  rc_malloc : malloc_contract;
  rc_free : free_contract;
  rc_free_null : free_null_contract;
  rc_calloc : calloc_contract;
  rc_realloc : realloc_contract;
  rc_memcpy : memcpy_icontract e_memcpy;
  rc_asan_memcpy : memcpy_icontract e_asan_memcpy;
  rc_memset : memset_icontract e_memset;
  rc_asan_memset : memset_icontract e_asan_memset;
  rc_memchr : memchr_icontract;
  rc_strlen : strlen_icontract;
  rc_strnlen : strnlen_icontract;
  rc_strncmp : strncmp_icontract;
  rc_stack_malloc_0 : stack_malloc_contract 0;
  rc_stack_malloc_2 : stack_malloc_contract 2;
  rc_stack_malloc_4 : stack_malloc_contract 4;
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
Definition FMT_usage : Z := 0x210ec.          (* [comment removed for export] *)
Definition FMT_cannot_open : Z := 0x3d197.    (* [comment removed for export] *)
Definition FMT_read_error : Z := 0x3d1ac.     (* [comment removed for export] *)
Definition FMT_too_big : Z := 0x2ef35.        (* [comment removed for export] *)
Definition FMT_emit : Z := 0x1d8ea.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STDERR_FILE : Z := 0x5e7168.

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
  exists g : word, ro_cells bsegs m 0x5e2c40 [C8 (Z_to_bv 64 0xbfae90)] /\ ro_cells bsegs m 0xbfae90 [C8 g].

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
  tp = Z_to_bv 64 0xbdae50 -> rw_cells bsegs m (0xbdae50 + -156) [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0)] ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  let bs := file_read data off (Z_to_bv 64 count) in
  cps bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                    s10 s11 t3 t4 t5 t6 F fc e_read m)))
    (ASTA RT Σ (PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0)
       (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (len_word bs) m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(buf, buf + Z.of_nat (length bs))] m m'
          /\ bytes_at bsegs m' buf bs)).

(* [comment removed for export] *)
Definition read_icontract_dir : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (fd buf count : Z) (lo : Z),
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
  buf = g_read_stage (* [comment removed for export] *) ->
  3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
  fd_lookup F0 (Z_to_bv 64 fd) = Some FdDir ->
  (forall i, 0 <= i < 4 -> client_static (errno_cell tp + i)) ->
  tp = Z_to_bv 64 0xbdae50 -> (exists v, rw_cells bsegs m (errno_cell tp) [C4 v]) ->
  rw_cells bsegs m (0xbdae50 + -156) [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0)] ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cps bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
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
  (forall a s, fp_str c = Some (a, s) -> bytes_at bsegs m a (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
       /\ Z.of_nat (length s) < 131072 /\ checked_src RT Σ m sp lo a (Z.of_nat (length s) + 1)
       (* [comment removed for export] *)
       /\ bv_unsigned sp <= a
       /\ exists slack, bytes_at bsegs m (a + Z.of_nat (length s) + 1) slack
            /\ (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
            /\ a + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16) ->
  fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  ERR_rep m -> io_ssp m ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
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
  (sa = 0x44570 \/ sa = 0x210fd) (* [comment removed for export] *) ->
  bytes_at bsegs m sa s -> checked_src RT Σ m sp lo sa (Z.of_nat (length s)) ->
  fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  ERR_rep m -> io_ssp m ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
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
  rw_cells bsegs m ap [C8 (Z_to_bv 64 0)] (* [comment removed for export] *) ->
  ap = bv_unsigned sp + 24 (* [comment removed for export] *) ->
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  OUT_rep so m -> io_ssp m ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_vprintf m)))
    (evw 1 (emit0_out so))
    (ASTA RT Σ (PMfd F0 fs0)
       (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
          /\ OUT_rep (emit0_next so) m' /\ (ERR_rep m -> ERR_rep m'))).

Record io_contracts : Prop := mkIOC {
  ioc_read_file : read_icontract_file;
  ioc_read_dir : read_icontract_dir;
  ioc_fprintf : fprintf_stderr_icontract;
  ioc_fwrite : fwrite_stderr_icontract;
  ioc_vprintf : vprintf_emit0_icontract
}.

End IO.
