(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_A2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import F_mm_syscalls MallocRep F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocModel_B.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocModel_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocModel_B.F_ntf_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.

Module F_am_K2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocKit_A2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocModel_B.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocModel_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocModel_B.F_ntf_B.
Import ListNotations.
Local Open Scope Z_scope.

Module A2 := MallocKit_A2.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling}.
Definition clear_range (st : mstate) (lo n : Z) : Prop :=
  forall rid r x, (s_regions st) !! rid = Some r -> lr_lo r <= x < r_base r + round_up_pg (r_len r) -> ~ (lo <= x < lo + n).

Lemma clear_range_of_ranges_free st lo n : ranges_free (live_ranges st) lo n = true -> clear_range st lo n.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros RF rid r x Hr Hx Hin. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo in Hx. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma round_up_pg_aligned x : x mod 4096 = 0 -> round_up_pg x = x.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= alloc_ceiling.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.
End GROW.
End WithCeiling0.
End F_am_K2.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.

Module F_am_H.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import F_mm_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require KStepLite.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_B MallocModel_B MallocKit_B3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocModel_B.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocModel_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B3 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocModel_B.F_ntf_B.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_K OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_C OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_F OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_G.
Import ListNotations.
Local Open Scope bv_scope.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling}.
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition brk_res (cur req : Z) (a : brk_ans) : Z := match a with BrkGrown => req | BrkSame => cur end.
Definition brk_mem (cur req : Z) (a : brk_ans) : word -> option byte :=
  match a with
  | BrkGrown => match brk_new_pages cur req with Some (lo, n) => apply_zeros m [(wa lo, Z_to_bv 64 n)] | None => m end
  | BrkSame => m
  end.
End BRKNODES.

Lemma land_neg_aligned cur : 0 < cur < 2^64 -> cur mod 4096 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 (0 + - cur))) 4095 = 0.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros H AL. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  replace ((0 + - cur) mod 2^64) with ((2^52 - cur / 4096) * 4096) by (Z.div_mod_to_equations; lia).
  change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. apply Z.mod_mul. lia.
Qed.

Lemma brk_new_pages_aligned cur n : 0 <= cur -> 0 < n -> cur mod 4096 = 0 -> n mod 4096 = 0 ->
  brk_new_pages cur (cur + n) = Some (cur, n).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros C0 N0 CA NA. unfold brk_new_pages. rewrite <- !KStepLite.round_up_pg_eq.
  rewrite !KStepLite.round_up_pg_aligned by (auto; rewrite Z.add_mod, CA, NA by lia; reflexivity).
  replace (cur <? cur + n) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. f_equal. lia.
Qed.

Definition fx_rel (A : Z) (a : fixed_ans) (r : word) (u : bool) : Prop :=
  match a with
  | FxKept e => errno_of r = Some e /\ u = false
  | FxDone => r = Z_to_bv 64 A /\ u = true
  | FxLost e => errno_of r = Some e /\ u = true
  end.
Lemma dec_mmap_fixed_shape A L rsp a : dec_mmap_fixed A L rsp = Some a -> exists r u, fx_rel A a r u /\ rsp = fixed_shape A L r u.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  unfold dec_mmap_fixed, fixed_shape. destruct rsp as [r ws zs us cp ci].
  destruct ws; [| discriminate]. destruct zs; [| discriminate]. destruct us as [|[ua un] us].
  - destruct cp; [| discriminate]. destruct ci; [| discriminate].
    destruct (errno_of r) eqn:E; [| discriminate]. intros H; inversion H; subst. exists r, false. cbn. rewrite E. auto.
  - destruct us; [| destruct cp; destruct ci; discriminate]. destruct cp; [| discriminate]. destruct ci; [| discriminate].
    destruct (bv_eqb ua (Z_to_bv 64 A) && bv_eqb un (Z_to_bv 64 (mmap_len L))) eqn:E; [| discriminate].
    apply andb_prop in E. destruct E as [E1 E2]. apply Fs.bv_eqb_eq in E1. apply Fs.bv_eqb_eq in E2. subst ua un.
    destruct (errno_of r) eqn:E.
    + intros H; inversion H; subst. exists r, true. cbn. rewrite E. auto.
    + destruct (bv_eqb r (Z_to_bv 64 A)) eqn:E3; [| discriminate]. apply Fs.bv_eqb_eq in E3. intros H; inversion H; subst. exists (Z_to_bv 64 A), true. cbn. auto.
Qed.
End WithCeiling0.
End F_am_H.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_am_P.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_A OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_K OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_alloc_meta.F_am_K2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_C OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_D OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_E OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_F OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.F_am_G OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_alloc_meta.F_am_H OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_am_P.
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.


From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Section WithCeiling0. Context {CE__ : Ceiling}.
Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).
Lemma magree_trans (C1 C2 C3 : Z -> Prop) m1 m2 m3 :
  magree C1 m1 m2 -> magree C2 m2 m3 -> (forall a, C1 a -> C3 a) -> (forall a, C2 a -> C3 a) -> magree C3 m1 m3.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__). intros A B I1 I2 a Ha Hc. rewrite (B a Ha) by (intros X; apply Hc, I2, X). apply A; [exact Ha|]. intros X; apply Hc, I1, X. Qed.
Lemma magree_of_munch C W m m' : munch W m m' -> ivs_covered C W -> magree C m m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros MU COV a Ha Hc. apply MU. rewrite wa_unsigned by lia.
  revert COV Hc. clear. induction W as [|[lo hi] W IH]; cbn; intros COV Hc; [exact I|].
  destruct COV as [C1 COV]. split; [| apply IH; assumption]. intros Hin. apply Hc. apply C1. exact Hin.
Qed.

Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.
End ASM.
End WithCeiling0.
