(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim StrFun Canon Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require PrintfFormats.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Export GDesc SiteData.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SEGTOP_A : Z := 0xbcb000.
(* [comment removed for export] *)
Definition USTACK_TOP : Z := 0x800000000000.
Definition STACK_WIN : Z := 0x800000.
(* [comment removed for export] *)
Definition RT_STACK : Z := 0x10000.
(* [comment removed for export] *)
Definition LIVE_MAX : Z := 65536.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition PBYTES_MAX : Z := 0x20000000.   (* [comment removed for export] *)
Definition NSEC_LIVE : Z := 8000.
Definition lw (n : Z) : Z := if n <=? 64512 then 4 * Z.max 0 n + 32 else 0.
Definition isbig (e : Z * Z) : bool := 64512 <? snd e.
Fixpoint psum (l : list (Z * Z)) : Z := match l with nil => 0 | e :: l' => lw (snd e) + psum l' end.
Definition nbig (l : list (Z * Z)) : Z := Z.of_nat (length (List.filter isbig l)).
(* [comment removed for export] *)
Definition live_room (l : list (Z * Z)) (n : Z) : Prop :=
  Z.of_nat (length l) < LIVE_MAX /\ psum l + lw n <= PBYTES_MAX /\ nbig l + (if n <=? 64512 then 0 else 1) <= NSEC_LIVE.
(* [comment removed for export] *)
Definition live_caps (l : list (Z * Z)) : Prop := Z.of_nat (length l) <= LIVE_MAX /\ psum l <= PBYTES_MAX /\ nbig l <= NSEC_LIVE.
Lemma lw_nonneg : forall n, 0 <= lw n.
Proof. intros n. unfold lw. destruct (n <=? 64512); lia. Qed.
Lemma psum_app : forall l1 l2, psum (l1 ++ l2) = psum l1 + psum l2.
Proof. induction l1 as [|e l1 IH]; intros l2; cbn [psum app]; [lia|]. rewrite IH. lia. Qed.
Lemma nbig_cons : forall e l, nbig (e :: l) = (if isbig e then 1 else 0) + nbig l.
Proof. intros e l. unfold nbig. cbn [List.filter]. destruct (isbig e); [cbn [length]; rewrite Nat2Z.inj_succ|]; lia. Qed.
Lemma live_room_count : forall l n, live_room l n -> Z.of_nat (length l) < LIVE_MAX.
Proof. intros l n (H & _). exact H. Qed.
Lemma live_caps_nil : live_caps nil.
Proof. unfold live_caps, nbig, LIVE_MAX, PBYTES_MAX, NSEC_LIVE. cbn. lia. Qed.
(* [comment removed for export] *)
Definition LW_MAX : Z := 258080.   (* [comment removed for export] *)
Definition lroom3 (l : list (Z * Z)) (c p b : Z) : Prop :=
  Z.of_nat (length l) + c <= LIVE_MAX /\ psum l + p <= PBYTES_MAX /\ nbig l + b <= NSEC_LIVE.
Lemma lw_le_max : forall n, lw n <= LW_MAX.
Proof. intros n. unfold lw, LW_MAX. destruct (Z.leb_spec n 64512); lia. Qed.
Lemma psum_nonneg : forall l, 0 <= psum l.
Proof. induction l as [|e l IH]; cbn [psum]; [lia|]. pose proof (lw_nonneg (snd e)). lia. Qed.
Lemma nbig_nonneg : forall l, 0 <= nbig l.
Proof. intros l. unfold nbig. lia. Qed.
Lemma lroom3_live_room : forall l c p b n, lroom3 l c p b -> 1 <= c -> LW_MAX <= p -> 1 <= b -> live_room l n.
Proof.
  intros l c p b n (H1 & H2 & H3) Hc Hp Hb. pose proof (lw_le_max n). unfold live_room.
  split; [lia|]. split; [lia|]. destruct (n <=? 64512); lia.
Qed.
Lemma lroom3_mono : forall l c p b c' p' b', lroom3 l c p b -> c' <= c -> p' <= p -> b' <= b -> lroom3 l c' p' b'.
Proof. intros l c p b c' p' b' (H1 & H2 & H3) X Y W. unfold lroom3. lia. Qed.
Lemma lroom3_cons : forall l c p b q n, lroom3 l c p b -> lroom3 ((q, n) :: l) (c - 1) (p - LW_MAX) (b - 1).
Proof.
  intros l c p b q n (H1 & H2 & H3). pose proof (lw_le_max n). unfold lroom3. cbn [length psum snd]. rewrite nbig_cons.
  split; [lia|]. split; [lia|]. destruct (isbig (q, n)); lia.
Qed.
Lemma lroom3_app : forall l1 l2 c p b, lroom3 l2 c p b -> lroom3 (l1 ++ l2) (c - Z.of_nat (length l1)) (p - psum l1) (b - nbig l1).
Proof.
  intros l1 l2 c p b (H1 & H2 & H3). unfold lroom3. rewrite length_app, Nat2Z.inj_add, psum_app.
  assert (E : nbig (l1 ++ l2) = nbig l1 + nbig l2) by (unfold nbig; rewrite List.filter_app, length_app; lia).
  rewrite E. lia.
Qed.
Lemma lroom3_le : forall l l' c p b dc dp db, lroom3 l c p b ->
  Z.of_nat (length l') <= Z.of_nat (length l) + dc -> psum l' <= psum l + dp -> nbig l' <= nbig l + db ->
  lroom3 l' (c - dc) (p - dp) (b - db).
Proof. intros l l' c p b dc dp db (H1 & H2 & H3) X Y W. unfold lroom3. lia. Qed.
Lemma nbig_app : forall l1 l2, nbig (l1 ++ l2) = nbig l1 + nbig l2.
Proof. intros l1 l2. unfold nbig. rewrite List.filter_app, length_app. lia. Qed.
Lemma psum_le_len : forall l, psum l <= Z.of_nat (length l) * LW_MAX.
Proof. induction l as [|e l IH]; cbn [psum length]; [lia|]. pose proof (lw_le_max (snd e)). rewrite Nat2Z.inj_succ. lia. Qed.
Lemma nbig_le_len : forall l, nbig l <= Z.of_nat (length l).
Proof. intros l. unfold nbig. induction l as [|e l IH]; cbn [List.filter]; [lia|]. destruct (isbig e); cbn [length]; lia. Qed.
(* [comment removed for export] *)
Lemma lroom3_of_len : forall l c p b, Z.of_nat (length l) + c <= LIVE_MAX -> Z.of_nat (length l) * LW_MAX + p <= PBYTES_MAX ->
  Z.of_nat (length l) + b <= NSEC_LIVE -> lroom3 l c p b.
Proof. intros l c p b A B C. pose proof (psum_le_len l). pose proof (nbig_le_len l). unfold lroom3. lia. Qed.
Lemma live_room_of_len : forall l n, Z.of_nat (length l) <= 2000 -> live_room l n.
Proof.
  intros l n H. apply (lroom3_live_room l 1 LW_MAX 1 n); [|lia|lia|lia].
  apply lroom3_of_len; unfold LIVE_MAX, PBYTES_MAX, NSEC_LIVE, LW_MAX; lia.
Qed.
Lemma lroom3_app_intro : forall l1 l2 c p b, lroom3 l2 (c + Z.of_nat (length l1)) (p + psum l1) (b + nbig l1) -> lroom3 (l1 ++ l2) c p b.
Proof. intros l1 l2 c p b (H1 & H2 & H3). unfold lroom3. rewrite length_app, Nat2Z.inj_add, psum_app, nbig_app. lia. Qed.
Lemma live_caps_cons : forall l p n, live_room l n -> live_caps ((p, n) :: l).
Proof.
  intros l p n (H1 & H2 & H3). unfold live_caps. cbn [length psum snd]. rewrite nbig_cons. unfold isbig. cbn [snd].
  split; [lia|]. split; [lia|]. destruct (Z.leb_spec n 64512); destruct (Z.ltb_spec 64512 n); lia.
Qed.
Definition FRAMES_MAX : nat := 512.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition mcost (n : Z) : Z := if n <=? 64512 then 0 else 2 * n + 16384.

(* [comment removed for export] *)
Definition e_malloc : Z := 0x1c4094.        (* [comment removed for export] *)
Definition e_free : Z := 0x1c4090.          (* [comment removed for export] *)
Definition e_calloc : Z := 0x1c4098.        (* [comment removed for export] *)
Definition e_realloc : Z := 0x1c409c.       (* [comment removed for export] *)
Definition e_strlen : Z := 0x1ad618.        (* [comment removed for export] *)
Definition e_strnlen : Z := 0x1ad61c.       (* [comment removed for export] *)
Definition e_strncmp : Z := 0x1ad624.       (* [comment removed for export] *)
Definition e_memchr : Z := 0x1ad640.        (* [comment removed for export] *)
Definition e_memset : Z := 0x1c29c8.        (* [comment removed for export] *)
Definition e_memcpy : Z := 0x1c29cc.        (* [comment removed for export] *)
Definition e_asan_memcpy : Z := 0x1c29d0.   (* [comment removed for export] *)
Definition e_asan_memset : Z := 0x1c2e6c.   (* [comment removed for export] *)
Definition e_read : Z := 0x1ad648.          (* [comment removed for export] *)
Definition e_fwrite : Z := 0x1ad650.        (* [comment removed for export] *)
Definition e_vprintf : Z := 0x1ad664.       (* [comment removed for export] *)
Definition e_vfprintf : Z := 0x1ad668.      (* [comment removed for export] *)
Definition e_fprintf : Z := 0x1ad670.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stack_malloc (k : nat) : Z :=
  match k with 0%nat => 0x1a746c | 1%nat => 0x1a75e0 | 2%nat => 0x1a7770 | 3%nat => 0x1a790c | _ => 0x1a7ab8 end.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition set_shadow_vals : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 0xf1; 0xf2; 0xf3; 0xf5; 0xf8].
Definition e_set_shadow (v : Z) : Z :=
  match v with
  | 0 => 0x1c62cc | 1 => 0x1c62e4 | 2 => 0x1c62fc | 3 => 0x1c6314 | 4 => 0x1c632c | 5 => 0x1c6344 | 6 => 0x1c635c
  | 7 => 0x1c6374 | 241 => 0x1c638c | 242 => 0x1c63a4 | 243 => 0x1c63bc | 245 => 0x1c63d4 | _ => 0x1c63ec
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
  [(0x5aebc8, 0x66e9d8); (0xb94690, 0xba4690); (0xba4690, 0xbcacd0)].
(* [comment removed for export] *)
Definition RT_STATIC : list (Z * Z) :=   (* [comment removed for export] *)
  [(0xba9398, 0xba93a0); (0xba93e8, 0xba9430); (0xbc96b0, 0xbc96b8); (0xbca798, 0xbca7a0)].

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
  stk ctasegs m lo (bv_unsigned sp) /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + RT_STACK <= bv_unsigned sp
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
     F (Z_to_bv 64 pc) fc None m (seg_rom ctasegs).

(* [comment removed for export] *)
Definition ret_st (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (ret_pc ra) fc' None m' (seg_rom ctasegs).

(* [comment removed for export] *)
Definition rt_after (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
  ART RT Σ' m' /\ mem_inv ctasegs m' /\ wmono ctasegs m m' /\ stk ctasegs m' lo sp.

(* [comment removed for export] *)
Definition rt_after_f (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
  ART RT Σ' m' /\ mem_inv ctasegs m' /\ stk ctasegs m' lo sp.

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
         /\ wr_at ctasegs m' p n /\ acc ctasegs m' p n) c
    /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

Definition malloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n <= 0x8000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba93f0 ->
  live_room (rt_live RT Σ) n -> mcost n <= rt_credit RT Σ ->      (* [comment removed for export] *)
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_malloc m)))
            (malloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

(* [comment removed for export] *)
Definition malloc_contract_ok : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n <= 0x8000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba93f0 ->
  live_room (rt_live RT Σ) n -> mcost n <= rt_credit RT Σ ->      (* [comment removed for export] *)
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_malloc m)))
            (malloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

Lemma malloc_contract_ok_of : malloc_contract -> malloc_contract_ok.
Proof. intros H. unfold malloc_contract_ok. intros. eapply H; try eassumption. apply unwind_ok_ch. assumption. Qed.

(* [comment removed for export] *)
Definition live_remove (p : Z) (live : list (Z * Z)) : list (Z * Z) := filter (fun e => negb (fst e =? p)) live.
(* [comment removed for export] *)
Lemma psum_filter_le : forall f l, Forall (fun e => 0 <= snd e) l -> psum (List.filter f l) <= psum l.
Proof.
  intros f l HF. induction l as [|e l IH]; cbn [List.filter psum]; [lia|]. apply Forall_cons_iff in HF as [He HF]. specialize (IH HF).
  pose proof (lw_nonneg (snd e)). destruct (f e); cbn [psum]; lia.
Qed.
Lemma nbig_filter_le : forall f l, nbig (List.filter f l) <= nbig l.
Proof.
  intros f l. unfold nbig. induction l as [|e l IH]; cbn [List.filter]; [lia|]. destruct (f e); cbn [List.filter]; destruct (isbig e); cbn [length]; rewrite ?Nat2Z.inj_succ; lia.
Qed.
Lemma length_filter_le : forall (f : Z * Z -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof. intros f l. induction l as [|e l IH]; cbn [List.filter]; [lia|]. destruct (f e); cbn [length]; lia. Qed.
Lemma live_remove_eq : forall p l, live_remove p l = List.filter (fun e => negb (fst e =? p)) l.
Proof.
  intros p l. unfold live_remove. induction l as [|e l IH]; [reflexivity|].
  cbn in *. rewrite <- IH. destruct (fst e =? p); reflexivity.
Qed.
Lemma lroom3_remove : forall l q c p b, lroom3 l c p b -> lroom3 (live_remove q l) c p b.
Proof.
  intros l q c p b (H1 & H2 & H3). unfold lroom3. rewrite live_remove_eq.
  assert (HF : Forall (fun e : Z * Z => 0 <= lw (snd e)) l) by (apply Forall_forall; intros e _; apply lw_nonneg).
  assert (P : psum (List.filter (fun e => negb (fst e =? q)) l) <= psum l).
  { clear - HF. induction l as [|e l IH]; cbn [List.filter psum]; [lia|]. apply Forall_cons_iff in HF as [He HF]. specialize (IH HF). destruct (negb (fst e =? q)); cbn [psum]; lia. }
  pose proof (nbig_filter_le (fun e => negb (fst e =? q)) l). pose proof (length_filter_le (fun e => negb (fst e =? q)) l). lia.
Qed.
Lemma live_caps_remove : forall l p, Forall (fun e => 0 <= snd e) l -> live_caps l -> live_caps (live_remove p l).
Proof.
  intros l p HF (H1 & H2 & H3). unfold live_caps. rewrite live_remove_eq.
  pose proof (psum_filter_le (fun e => negb (fst e =? p)) l HF). pose proof (nbig_filter_le (fun e => negb (fst e =? p)) l).
  pose proof (length_filter_le (fun e => negb (fst e =? p)) l) as L.
  lia.
Qed.

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
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0xba93f0 ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

(* [comment removed for export] *)
Definition free_contract_ok : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0xba93f0 ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

Lemma free_contract_ok_of : free_contract -> free_contract_ok.
Proof. intros H. unfold free_contract_ok. intros. eapply H; try eassumption. apply unwind_ok_ch. assumption. Qed.

(* [comment removed for export] *)
Definition free_null_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0xba93f0 ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (fun c => exists v, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

(* [comment removed for export] *)
Definition free_null_contract_ok : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0xba93f0 ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
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
         /\ wr_at ctasegs m' p n /\ acc ctasegs m' p n /\ bytes_at ctasegs m' p (repeat (Z_to_bv 8 0) (Z.to_nat n))) c
    /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

Definition calloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (k sz lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  0 <= k < 2^64 -> 0 <= sz < 2^64 -> 1 <= k * sz <= 64512 ->
  a0 = Z_to_bv 64 k -> a1 = Z_to_bv 64 sz -> tp = Z_to_bv 64 0xba93f0 ->
  live_room (rt_live RT Σ) (k * sz) -> mcost (k * sz) <= rt_credit RT Σ ->      (* [comment removed for export] *)
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_calloc m)))
            (calloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (k * sz) lo m).

(* [comment removed for export] *)
Definition realloc_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (p n0 n lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (q : Z),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at ctasegs m' q n /\ acc ctasegs m' q n
         /\ (forall old, bytes_at ctasegs m p old -> Z.of_nat (length old) = Z.min n0 n -> bytes_at ctasegs m' q old)) c
    /\ rt_live RT Σ' = (q, n) :: live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q + n < USTACK_TOP.

Definition realloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n0 n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n0) (rt_live RT Σ) -> 1 <= n0 <= 64512 -> 1 <= n <= 64512 ->
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> tp = Z_to_bv 64 0xba93f0 ->
  live_room (rt_live RT Σ) n -> mcost n <= rt_credit RT Σ ->      (* [comment removed for export] *)
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_realloc m)))
            (realloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p n0 n lo m).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_posix_memalign : Z := 0x1c40a0.   (* [comment removed for export] *)
Definition PMA_ALIGN : Z := 64.
Definition PMA_SIZE : Z := 32768.

Definition posix_memalign_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (mp lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (p : Z),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) mp 8 m m'
         /\ rw_cells ctasegs m' mp [C8 (Z_to_bv 64 p)]
         /\ wr_at ctasegs m' p PMA_SIZE /\ acc ctasegs m' p PMA_SIZE) c
    /\ rt_live RT Σ' = (p, PMA_SIZE) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost PMA_SIZE /\ 0 < p /\ p mod PMA_ALIGN = 0 /\ p + PMA_SIZE < USTACK_TOP.

Definition posix_memalign_init_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (mp lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 mp -> a1 = Z_to_bv 64 PMA_ALIGN -> a2 = Z_to_bv 64 PMA_SIZE -> tp = Z_to_bv 64 0xba93f0 ->
  live_room (rt_live RT Σ) PMA_SIZE -> mcost PMA_SIZE <= rt_credit RT Σ ->      (* [comment removed for export] *)
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->      (* [comment removed for export] *)
  mp mod 8 = 0 -> (forall i, 0 <= i < 8 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (mp + i)) -> wr_at ctasegs m mp 8 ->
  (mp + 8 <= lo \/ bv_unsigned sp <= mp) ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_posix_memalign m)))
            (posix_memalign_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mp lo m).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition checked_src (Σ : rts RT) (m : mem) (sp : word) (lo s n : Z) : Prop :=
  (0 < n -> acc ctasegs m s n /\ rng_class RT Σ s n) /\ (s + n <= lo \/ bv_unsigned sp <= s).
(* [comment removed for export] *)
Definition checked_dst (Σ : rts RT) (m : mem) (sp : word) (d n : Z) : Prop :=
  (0 < n -> acc ctasegs m d n /\ rng_class RT Σ d n)
  /\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (d + i)) /\ wr_at ctasegs m d n.

(* [comment removed for export] *)
Definition memcpy_icontract (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at ctasegs m s bs ->
  checked_src Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst Σ m sp d (Z.of_nat (length bs)) ->
  (d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
               (fun m' => bytes_at ctasegs m' d bs)).

(* [comment removed for export] *)
Definition memset_icontract (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d n : Z) (c : byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (bv_unsigned c) -> a2 = Z_to_bv 64 n ->
  0 <= d <= 2^47 -> 0 <= n < 2^40 -> checked_dst Σ m sp d n ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d n m
               (fun m' => bytes_at ctasegs m' d (repeat c (Z.to_nat n)))).

(* [comment removed for export] *)
Definition memchr_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s cz n : Z) (buf : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 cz -> a2 = Z_to_bv 64 n ->
  0 < s <= 2^47 -> 0 <= cz < 256 -> 0 <= n < 2^40 -> bytes_at ctasegs m s buf -> memchr_ok s cz n buf ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) (* [comment removed for export] *) ->
  checked_src Σ m sp lo s (memchr_chk cz n buf) ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_memchr m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (memchr_res s cz n buf)) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strlen_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s : Z) (str slack : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s ->
  bytes_at ctasegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < s <= 2^47 -> (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  checked_src Σ m sp lo s (Z.of_nat (length str) + 1) ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strlen m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length str))) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strnlen_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s n : Z) (buf : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
  0 < s <= 2^47 -> 0 <= n < 2^40 -> bytes_at ctasegs m s buf -> strnlen_ok s n buf ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) (* [comment removed for export] *) ->
  checked_src Σ m sp lo s (strnlen_chk n buf) ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strnlen m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strnlen_res n buf)) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strncmp_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p1 p2 n : Z) (b1 b2 : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 n ->
  0 < n < 2^31 -> bytes_at ctasegs m p1 b1 -> bytes_at ctasegs m p2 b2 -> strncmp_ok n b1 b2 ->
  checked_src Σ m sp lo p1 (strncmp_sz n b1 b2) -> checked_src Σ m sp lo p2 (strncmp_sz n b1 b2) ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
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
  fdfs_only PMc -> mat_stable PMc -> (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4)%nat -> tp = Z_to_bv 64 0xba93f0 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at ctasegs m' f (fs_size k - 8) /\ wr_at ctasegs m' (shad f) (fs_size k / 8)) c
       /\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP).

(* [comment removed for export] *)
Definition set_shadow_contract (v : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d n : Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> In v set_shadow_vals -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n ->
  0 <= n < 2^20 -> (forall i, 0 <= i < n -> in_fframe_shadow (rt_frames RT Σ) (d + i)) -> wr_at ctasegs m d n ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_set_shadow v) m)))
    (fun c => exists v0, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 lo d n m
               (fun m' => bytes_at ctasegs m' d (repeat (Z_to_bv 8 v) (Z.to_nat n))) c).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RELRO_LO : Z := 0x533000.
Definition RELRO_HI : Z := 0x5ac000.
Definition relro_pristine (m : mem) : Prop := forall a : word, RELRO_LO <= bv_unsigned a < RELRO_HI -> mrd ctasegs m a = seg_rom ctasegs a.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition client_consts (m : mem) : Prop :=
  ro_cells ctasegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
  /\ ro_cells ctasegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
  /\ ro_cells ctasegs m g_GOT_detect_uar [C8 (Z_to_bv 64 g_detect_stack_use_after_return)]
  /\ ro_cells ctasegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)]
  /\ relro_pristine m.

(* [comment removed for export] *)
Definition ACC_LITS : list (Z * Z) := [].

Record art_facts : Prop := mkAF {
  af_client_consts : forall Σ m, ART RT Σ m -> client_consts m;
  (* [comment removed for export] *)
  af_frame : forall Σ (m m' : mem) (sp : Z), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= sp ->
    (forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> m' a = m a) ->
    wmono ctasegs m m' -> ART RT Σ m';
  (* [comment removed for export] *)
  af_with_fds : forall Σ mo fds, ARTM RT Σ mo -> ARTM RT Σ (with_fds fds mo);
  af_mat_stable : forall Σ, mat_stable (ARTM RT Σ);
  (* [comment removed for export] *)
  af_acc_live : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> wr_at ctasegs m p n /\ acc ctasegs m p n;
  (* [comment removed for export] *)
  af_live_slack : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
    exists slack, bytes_at ctasegs m (p + n) slack /\ (- (p + n)) mod 8 <= Z.of_nat (length slack)
      /\ p + n + Z.of_nat (length slack) <= rt_sp0 RT Σ - STACK_WIN;
  (* [comment removed for export] *)
  af_acc_stack : forall Σ m a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= a -> a + n <= USTACK_TOP -> acc ctasegs m a n;
  (* [comment removed for export] *)
  af_acc_static : forall Σ m a n, ART RT Σ m -> 0 <= a ->
    (forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x5af720 <= a + i < 0x66e960)
                             /\ ~ (0x5aebe0 <= a + i < 0x5af400) /\ ~ (0xba46c0 <= a + i < 0xba8ae0)) -> acc ctasegs m a n;
  (* [comment removed for export] *)
  af_lib_sh : forall Σ m g, ART RT Σ m -> In g GDESC -> bytes_at ctasegs m (shad (gd_beg g)) (ushadow (gd_size g));
  (* [comment removed for export] *)
  af_img_shadow : forall Σ m, ART RT Σ m -> stk ctasegs m (shad 0x10000) (shad SEGTOP_A);
  (* [comment removed for export] *)
  af_sh_live : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> bytes_at ctasegs m (shad p) (ushadow n);
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
    exists (Σ' : rts RT) (fl : Z), rw_cells ctasegs m fl [C1 (Z_to_bv 8 1)]
      /\ ~ aclient (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP fl
      (* [comment removed for export] *)
      /\ 0 < fl /\ fl + 1 <= rt_sp0 RT Σ - STACK_WIN
      (* [comment removed for export] *)
      /\ (fl + 1 <= f \/ f + fs_size k <= fl) /\ (fl + 1 <= 0x10000 \/ SEGTOP_A <= fl) /\ (fl + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= fl)
      (* [comment removed for export] *)
      /\ ro_cells ctasegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 fl)]
      /\ forall m', munch [(fl, fl + 1)] m m' -> wmono ctasegs m m' -> rw_cells ctasegs m' fl [C1 (Z_to_bv 8 0)] ->
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
    ro_cells ctasegs m 0x5ab1e0 [C8 (Z_to_bv 64 0xbc9430)] /\ ro_cells ctasegs m 0x5ab1e0 [C8 (Z_to_bv 64 0xbc9430)];
  (* [comment removed for export] *)
  af_acc_lits : forall Σ m, ART RT Σ m -> Forall (fun r => acc ctasegs m (fst r) (snd r)) ACC_LITS;
  (* [comment removed for export] *)
  af_frames_hi : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f;
  (* [comment removed for export] *)
  af_live_offshadow : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p;
  (* [comment removed for export] *)
  af_credit_nonneg : forall Σ m, ART RT Σ m -> 0 <= rt_credit RT Σ;
  (* [comment removed for export] *)
  af_tsd : forall Σ m, ART RT Σ m -> rw_cells ctasegs m 0xba9398 [C8 (Z_to_bv 64 0xbca798)]
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
  rc_stack_malloc_1 : stack_malloc_contract 1;   (* [comment removed for export] *)
  rc_stack_malloc_2 : stack_malloc_contract 2;
  rc_stack_malloc_3 : stack_malloc_contract 3;
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
Definition FMT_usage : Z := 0x212eb.          (* [comment removed for export] *)
Definition FMT_cannot_open : Z := 0x3cd30.    (* [comment removed for export] *)
Definition FMT_read_error : Z := 0x3cd45.     (* [comment removed for export] *)
Definition FMT_too_big : Z := 0x2efb9.        (* [comment removed for export] *)
Definition FMT_emit : Z := 0x1db09.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STDERR_FILE : Z := 0x5af428.

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
  exists g : word, ro_cells ctasegs m 0x5ab1e0 [C8 (Z_to_bv 64 0xbc9430)] /\ ro_cells ctasegs m 0xbc9430 [C8 g].

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
  tp = Z_to_bv 64 0xba93f0 -> rw_cells ctasegs m (0xba93f0 + -156) [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0)] ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  let bs := file_read data off (Z_to_bv 64 count) in
  cps ctasegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                    s10 s11 t3 t4 t5 t6 F fc e_read m)))
    (ASTA RT Σ (PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0)
       (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (len_word bs) m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(buf, buf + Z.of_nat (length bs))] m m'
          /\ bytes_at ctasegs m' buf bs)).

(* [comment removed for export] *)
Definition read_icontract_dir : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (fd buf count : Z) (lo : Z),
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
  buf = g_read_stage (* [comment removed for export] *) ->
  3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
  fd_lookup F0 (Z_to_bv 64 fd) = Some FdDir ->
  (forall i, 0 <= i < 4 -> client_static (errno_cell tp + i)) ->
  tp = Z_to_bv 64 0xba93f0 -> (exists v, rw_cells ctasegs m (errno_cell tp) [C4 v]) ->
  rw_cells ctasegs m (0xba93f0 + -156) [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0)] ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cps ctasegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
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
  (forall a s, fp_str c = Some (a, s) -> bytes_at ctasegs m a (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
       /\ Z.of_nat (length s) < 131072 /\ checked_src RT Σ m sp lo a (Z.of_nat (length s) + 1)
       (* [comment removed for export] *)
       /\ bv_unsigned sp <= a
       /\ exists slack, bytes_at ctasegs m (a + Z.of_nat (length s) + 1) slack
            /\ (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
            /\ a + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16) ->
  fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  ERR_rep m -> io_ssp m ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cpsE ctasegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
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
  (sa = 0x44179 \/ sa = 0x212fc) (* [comment removed for export] *) ->
  bytes_at ctasegs m sa s -> checked_src RT Σ m sp lo sa (Z.of_nat (length s)) ->
  fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  ERR_rep m -> io_ssp m ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cpsE ctasegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
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
  rw_cells ctasegs m ap [C8 (Z_to_bv 64 0)] (* [comment removed for export] *) ->
  ap = bv_unsigned sp + 24 (* [comment removed for export] *) ->
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  OUT_rep so m -> io_ssp m ->
  ART RT Σ m -> mem_inv ctasegs m -> call_ok RT Σ m sp lo ->
  cpsE ctasegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
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
