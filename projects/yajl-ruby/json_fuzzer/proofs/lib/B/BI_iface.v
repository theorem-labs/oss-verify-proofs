(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages LazyModel.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass AsanLayout.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BI_shadow BI_region_is_poisoned B_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition C_SB : Z := 0x7fff8000.

(* [comment removed for export] *)
Definition pg_lo (a : Z) : Z := a - a mod 4096.
Definition pg_hi (a : Z) : Z := a - a mod 4096 + 4096.   (* [comment removed for export] *)

Section Stmts.
Variable segs : list Segment.
Variable APS : Type.
Variable AHK : APS -> list ablock -> list fblock -> mem -> Model -> Prop.
(* [comment removed for export] *)
Variable aS : APS -> word -> Prop.

(* [comment removed for export] *)
Definition AHK_icp_globals_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo -> icp_globals segs m C_SB.

(* [comment removed for export] *)
Definition AHK_icp_block_shadow_stmt : Prop :=
  forall s LB LF m mo b A n, AHK s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window segs m C_SB A n ws /\ range_clean C_SB A n ws /\ app_mem (ab_addr b) (ab_size b).

(* [comment removed for export] *)
Definition AHK_icp_regions_stmt : Prop :=
  forall s LB LF m mo, AHK s LB LF m mo ->
       lazy_disjoint mo alloc_ceiling (2^47)                       (* [comment removed for export] *)
    /\ lazy_disjoint mo 0x10000 0x603000                           (* [comment removed for export] *)
    /\ (forall b, In b LB -> lazy_disjoint mo (ab_addr b) (ab_addr b + ab_size b))
    /\ (forall b A n, In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
          pages_budgeted (aS s) (shw_lo C_SB A) (shw_hi C_SB A n)).

(* [comment removed for export] *)
Definition AHK_icp_stack_shadow_stmt : Prop :=
  forall s LB LF m mo A n, AHK s LB LF m mo -> alloc_ceiling <= A -> 1 <= n -> A + n <= 2^47 ->
    exists ws, shadow_window segs m C_SB A n ws /\ range_clean C_SB A n ws
               /\ pages_budgeted (aS s) (shw_lo C_SB A) (shw_hi C_SB A n).

Definition AHK_icp_musl_statics_shadow_stmt : Prop :=
  forall s LB LF m mo A n, AHK s LB LF m mo -> 0x5d0810 <= A -> 1 <= n -> A + n <= 0x603000 ->
    exists ws, shadow_window segs m C_SB A n ws /\ range_clean C_SB A n ws
               /\ pages_budgeted (aS s) (shw_lo C_SB A) (shw_hi C_SB A n).

(* [comment removed for export] *)
Lemma app_mem_shadow_facts : forall X L A n, app_mem X L -> X <= A -> 1 <= n -> A + n <= X + L ->
     range_in_mem C_SB A n
  /\ C_SB <= shw_lo C_SB A /\ shw_hi C_SB A n <= C_SB + 0x100000000000
  /\ (shw_hi C_SB A n <= 0x8fff7008 \/ C_SB + 0x2000000000 <= shw_lo C_SB A)
  /\ (forall Y M, app_mem Y M -> 0 <= M -> shw_hi C_SB A n <= Y \/ Y + M <= shw_lo C_SB A)
  /\ A + n < 2^47 /\ 0 < A.
Proof.
  intros X L A n AM HXA Hn HAL. aceil.
  unfold app_mem in AM. rewrite kLowAppEnd_val, kHighMemBeg_val in AM.
  assert (CASE : (0 < A /\ A + n <= 0x7fff7000) \/ (0x10007fff8000 <= A /\ A + n <= alloc_ceiling)) by lia. clear AM HXA HAL.
  pose proof (shw_geom C_SB A n ltac:(unfold C_SB; lia) ltac:(lia) Hn) as G; cbv zeta in G.
  rewrite !Z.shiftr_div_pow2 in G by lia. change (2^3) with 8 in G.
  unfold range_in_mem, A_HIGHEND_VAL, C_SB in *.
  split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  split; [| split; [| lia]].
  - Z.div_mod_to_equations; lia.
  - intros Y M AY HM. unfold app_mem in AY. rewrite kLowAppEnd_val, kHighMemBeg_val in AY. Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
End Stmts.
End RC__1.
