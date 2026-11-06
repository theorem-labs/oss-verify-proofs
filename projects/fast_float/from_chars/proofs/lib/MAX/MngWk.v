(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition w64 (z : Z) : word := Z_to_bv 64 z.

Definition set_reg_addr (L : layout) (r : nat) (a : Z) : layout :=
  Layout (ly_ctx L) (fun k => if Nat.eqb k r then a else ly_reg L k) (ly_brk0 L) (ly_sec L).

(* [comment removed for export] *)
Definition brk_cur (L : layout) (s : astate) : Z :=
  match st_brk s with
  | BrkNever => ly_brk0 L
  | BrkCur r pages => ly_reg L r + PGSZ * pages
  | BrkDead => 0
  end.
Definition brk_base (L : layout) (s : astate) : Z :=
  match st_brk s with
  | BrkNever => ly_brk0 L
  | BrkCur r _ => ly_reg L r
  | BrkDead => 0
  end.

Definition SYS_brk : Z := 214.
Definition SYS_munmap : Z := 215.
Definition SYS_mmap : Z := 222.
Definition SYS_mprotect : Z := 226.

(* [comment removed for export] *)
Definition req_regs (L : layout) (s : astate) (q : kreq) : option (Z * list Z) :=
  match q with
  | KBrkQuery => Some (SYS_brk, [0])
  | KBrkGrow n => Some (SYS_brk, [brk_cur L s + PGSZ * n])
  | KGuard => Some (SYS_mmap, [brk_base L s; PGSZ; 0; 50; 2 ^ 64 - 1; 0])
  | KMmapRW len => Some (SYS_mmap, [0; len; 3; 34; 2 ^ 64 - 1; 0])
  | KMmapNone len => Some (SYS_mmap, [0; len; 0; 34; 2 ^ 64 - 1; 0])
  | KMprotect p => Some (SYS_mprotect, [loc_addr L (LMem p); PGSZ; 3])
  | KMunmap r len => Some (SYS_munmap, [ly_reg L r; len])
  | KJunk _ => None
  end.

Fixpoint args_match (regs : bvmap 5 word) (i : Z) (args : list Z) : Prop :=
  match args with
  | [] => True
  | a :: rest => bv_unsigned (getr regs (Z_to_bv 5 (10 + i))) = a mod 2 ^ 64 /\ args_match regs (i + 1) rest
  end.

(* [comment removed for export] *)
Definition mem_after (m : word -> option byte) (eff : SyscallEffect) : word -> option byte :=
  apply_writes (apply_copies m (apply_zeros (apply_unmaps m (eff_unmaps eff)) (eff_zeros eff)) (eff_copies eff))
               (eff_writes eff).

Section WK.
Variable segs : list Segment.
(* [comment removed for export] *)
Variable FORB : list (Z * Z).
Variable HTOP : Z.

(* [comment removed for export] *)
Definition at_ecall (L : layout) (s : astate) (q : kreq) (regs : bvmap 5 word) (pc : word) : Prop :=
  (exists w, fetch_word segs pc = Some w /\ is_ecall w = true) /\
  exists no args, req_regs L s q = Some (no, args) /\ bv_unsigned (getr regs 17) = no /\ args_match regs 0 args.

(* [comment removed for export] *)
Definition fresh_range (L : layout) (s : astate) (lo n : Z) : Prop :=
  PGSZ <= lo /\ lo mod PGSZ = 0 /\ 0 <= n /\ lo + n <= HTOP /\
  Forall (fun r => ranges_disjoint (lo, n) r) FORB /\
  (forall rg, In rg (footprint s) -> ranges_disjoint (lo, n) (crange L rg)) /\
  (forall r rg, region_of s r = Some rg -> rg_live rg = true -> ranges_disjoint (lo, n) (ly_reg L r, rg_len rg)).

Inductive koutcome (L : layout) (s : astate) : kreq -> SyscallEffect -> Z -> layout -> Prop :=
(* [comment removed for export] *)
| o_brk_query :
    koutcome L s KBrkQuery (mkEffect (w64 (ly_brk0 L)) [] []) 1 L
(* [comment removed for export] *)
| o_brk_refuse n :
    koutcome L s (KBrkGrow n) (mkEffect (w64 (brk_cur L s)) [] []) 0 L
(* [comment removed for export] *)
| o_brk_grant n :
    fresh_range L s (brk_cur L s) (PGSZ * n) ->
    koutcome L s (KBrkGrow n) (mkEffect (w64 (brk_cur L s + PGSZ * n)) [] [(w64 (brk_cur L s), w64 (PGSZ * n))]) 1
             (match st_brk s with
              | BrkNever => set_reg_addr L (length (st_regions s)) (ly_brk0 L)
              | _ => L
              end)
(* [comment removed for export] *)
| o_guard :
    koutcome L s KGuard (mkEffectU (w64 (brk_base L s)) [] [] [(w64 (brk_base L s), w64 PGSZ)] [] []) 1 L
(* [comment removed for export] *)
| o_mmap_rw len a :
    fresh_range L s a (page_round len) ->
    koutcome L s (KMmapRW len) (mkEffect (w64 a) [] [(w64 a, w64 (page_round len))]) 1
             (set_reg_addr L (length (st_regions s)) a)
(* [comment removed for export] *)
| o_mmap_na len a :
    fresh_range L s a len ->
    koutcome L s (KMmapNone len) (mkEffectU (w64 a) [] [] [(w64 a, w64 len)] [] []) 1
             (set_reg_addr L (length (st_regions s)) a)
(* [comment removed for export] *)
| o_mprotect p :
    koutcome L s (KMprotect p) (mkEffect (w64 0) [] [(w64 (loc_addr L (LMem p)), w64 PGSZ)]) 1 L
(* [comment removed for export] *)
| o_munmap r len :
    koutcome L s (KMunmap r len) (mkEffectU (w64 0) [] [] [(w64 (ly_reg L r), w64 (page_round len))] [] []) 1 L.

Section Walk.
Context {fx : FPState}.
Variable rom : word -> option byte.
Context {R : Type}.

Definition wpost : Type := layout -> R -> bvmap 5 word -> word -> (word -> option byte) -> Prop.

Fixpoint wk (L : layout) (regs : bvmap 5 word) (pc : word) (m : word -> option byte) (t : itree astate R) (Q : wpost)
    {struct t} : Prop :=
  match t with
  | IRet r => exists regs' pc' m', msteps segs (mkst regs pc m rom) (mkst regs' pc' m' rom) /\ Q L r regs' pc' m'
  | IFail _ => True
  | IAsk (KJunk _) _ k => exists z, 0 <= z < 256 /\ wk L regs pc m (k z) Q
  | IAsk q s k =>
      exists regs1 pc1 m1, msteps segs (mkst regs pc m rom) (mkst regs1 pc1 m1 rom) /\ at_ecall L s q regs1 pc1 /\
        forall eff ans L', koutcome L s q eff ans L' ->
          wk L' (regupd regs1 10 (eff_ret eff)) (bv_add pc1 (w64 4)) (mem_after m1 eff) (k ans) Q
  end.

#[using="Type"] Lemma wk_mono : forall t L regs pc m (Q Q' : wpost),
  (forall L' r regs' pc' m', Q L' r regs' pc' m' -> Q' L' r regs' pc' m') -> wk L regs pc m t Q -> wk L regs pc m t Q'.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction t as [r | q s k IH | f]; intros L regs pc m Q Q' HQ H; cbn in *.
  - destruct H as (regs' & pc' & m' & Hm & Hq). exists regs', pc', m'. split; [exact Hm | apply HQ, Hq].
  - destruct q;
      try (destruct H as (regs1 & pc1 & m1 & Hm & He & Hk); exists regs1, pc1, m1; split; [exact Hm|]; split; [exact He|];
           intros eff ans L' Ho; eapply IH; [exact HQ | apply Hk; exact Ho]).
    destruct H as (z & Hz & Hr). exists z. split; [exact Hz|]. eapply IH; [exact HQ | exact Hr].
  - exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wk_msteps : forall t L regs pc m regs0 pc0 m0 Q,
  msteps segs (mkst regs0 pc0 m0 rom) (mkst regs pc m rom) -> wk L regs pc m t Q -> wk L regs0 pc0 m0 t Q.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction t as [r | q s k IH | f]; intros L regs pc m regs0 pc0 m0 Q Hrun H; cbn in *.
  - destruct H as (regs' & pc' & m' & Hm & Hq). exists regs', pc', m'. split; [eapply msteps_trans; eassumption | exact Hq].
  - destruct q;
      try (destruct H as (regs1 & pc1 & m1 & Hm & He & Hk); exists regs1, pc1, m1;
           split; [eapply msteps_trans; eassumption|]; split; [exact He | exact Hk]).
    destruct H as (z & Hz & Hr). exists z. split; [exact Hz|]. eapply IH; eassumption.
  - exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wk_ret : forall L regs pc m r (Q : wpost), Q L r regs pc m -> wk L regs pc m (IRet r) Q.
Proof. LiaFast.lf_pins LiaFast.u0. intros L regs pc m r Q H. exists regs, pc, m. split; [apply mst_refl | exact H]. Qed.
End Walk.

(* [comment removed for export] *)
#[using="Type"] Lemma wk_ibind : forall {fx : FPState} rom {A B : Type} (t : itree astate A) (k : A -> itree astate B) L regs pc m
    (Q : @wpost B),
  wk (R := A) rom L regs pc m t (fun L' a regs' pc' m' => wk rom L' regs' pc' m' (k a) Q) ->
  wk rom L regs pc m (ibind t k) Q.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fx rom A B t k. induction t as [r | q s kt IH | f]; intros L regs pc m Q H; cbn in *.
  - destruct H as (regs' & pc' & m' & Hm & Hq). eapply wk_msteps; [exact Hm | exact Hq].
  - destruct q;
      try (destruct H as (regs1 & pc1 & m1 & Hm & He & Hk); exists regs1, pc1, m1; split; [exact Hm|]; split; [exact He|];
           intros eff ans L' Ho; apply IH; apply Hk; exact Ho).
    destruct H as (z & Hz & Hr). exists z. split; [exact Hz|]. apply IH. exact Hr.
  - exact I.
Qed.
End WK.
