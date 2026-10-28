(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition RMALLOC_SYM : Z := 0x2b33a8.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0x2b3268.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ralloc_static (a : Z) : Prop :=
  (RLIBC <= a < RCTX + 936) \/ (RERRNO <= a < RERRNO + 4)     (* [comment removed for export] *)
  \/ (RSSP_GUARD <= a < RSSP_GUARD + 8) \/ (RGOT_SSP <= a < RGOT_SSP + 8).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop :=
  exists st LB0, Permutation.Permutation LB0 LB /\ strip st = ps_m s /\ rmrep st m
                 /\ HINV_from ref_reserved st (ps_brk s) LB0.

Lemma RHEAP_ext : forall s s' LB m, RHEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> RHEAP s' LB m.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros s s' LB m (st & LB0 & HP & H1 & H2 & H3) E1 E2. exists st, LB0. rewrite E1, E2. auto 6. Qed.

Lemma RHEAP_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros s LB LB' m (st & LB0 & HP & H1 & H2 & H3) P. exists st, LB0. split; [|auto].
  eapply Permutation.Permutation_trans; [exact HP| exact P].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x2c2000 <= a < 0x355000 /\ ~ ralloc_static a) \/ in_block LB a.

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview ctusegs m (wa a) <> None -> wview ctusegs m' (wa a) <> None).

Lemma rheap_pres_refl : forall LB SP m, rheap_pres LB SP m m.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros LB SP m a _ _. auto. Qed.

Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
  rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
  split; [congruence| auto].
Qed.

Lemma rheap_pres_weaken : forall LB LB' SP SP' m m',
  rheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> rheap_pres LB' SP' m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0x2c2000 <= A /\ A + n <= 0x355000 /\ (A + n <= RLIBC \/ RCTX + 936 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)
      /\ (A + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= A) /\ (A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

Lemma rclient_range_addr : forall LB SP A n a,
  rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LB SP A n a HR Ha. unfold rclient_range, rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *.
  destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

Lemma rheap_pres_bytes_at : forall LB SP m m' A bs,
  rheap_pres LB SP m m' -> bytes_at ctusegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at ctusegs m' A bs.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

Lemma rheap_pres_wr_at : forall LB SP m m' A n,
  rheap_pres LB SP m m' -> wr_at ctusegs m A n -> rclient_range LB SP A n -> wr_at ctusegs m' A n.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

Lemma rheap_pres_rw_cells : forall LB SP m m' A cs,
  rheap_pres LB SP m m' -> rw_cells ctusegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells ctusegs m' A cs.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rheap_pres_wr_at; eauto.
Qed.

Lemma rheap_pres_u8arr : forall LB SP m m' A xs,
  rheap_pres LB SP m m' -> u8arr ctusegs m A xs -> rclient_range LB SP A (Z.of_nat (length xs)) ->
  u8arr ctusegs m' A xs.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells ctusegs m' A (length xs)).
  eapply rheap_pres_rw_cells; [exact HP| apply rw_cells_of_u8arr; exact H|].
  cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
Qed.

Lemma rheap_pres_stk : forall LB SP m m' lo hi,
  rheap_pres LB SP m m' -> stk ctusegs m lo hi -> SP <= lo -> stk ctusegs m' lo hi.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rblock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0x355000 <= A).

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (0x2c2000 <= fst iv /\ snd iv <= 0x355000 /\ (snd iv <= RLIBC \/ RCTX + 936 <= fst iv)
      /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv)
      /\ (snd iv <= 0x354990 \/ 0x354990 + 4 <= fst iv))     (* [comment removed for export] *)
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition raddr_exposed (s : PState) (n : Z) : Prop :=
  MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init (reservedZ ctusegs)).

Lemma raddr_exposed_big : forall s n, MMAP_THRESHOLD <= n -> raddr_exposed s n.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros; left; assumption. Qed.
Lemma raddr_exposed_init : forall s n, ps_m s = ps_m (ps_init (reservedZ ctusegs)) -> raddr_exposed s n.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros; right; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells ctusegs m' A [CB (Z.to_nat n) junk]
           /\ (raddr_exposed s n -> A = ptr_addr s' p)
           /\ (exists off g i, 0 <= off <= 255 /\ A = conc (ps_m s') (fst p) + UNIT * off      (* [comment removed for export] *)
                              /\ s_slots (ps_m s') !! (fst p) = Some (g, i)                    (* [comment removed for export] *)
                              /\ get_stride (get_meta_rec (ps_m s') g) - IB - n < 2^30)        (* [comment removed for export] *)
       end.

Definition rmalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] ->
  mem_inv ctusegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM ctusegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom ctusegs)).

Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' (errno_addr tp) [C4 errv]          (* [comment removed for export] *)
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (lb_remove p LB) m'.

Definition rfree_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] ->
  mem_inv ctusegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM ctusegs (raw_free p) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition rfree_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  a0 = Z_to_bv 64 0 ->
  evt ctusegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom ctusegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom ctusegs)).

Lemma rfree_null_spec : rfree_null_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until m. intros ->. unfold RFREE_SYM.
  step. step. if_true. step. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End WithCeiling0.
