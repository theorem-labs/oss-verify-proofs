(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac ITree Nodes SysStep Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_syscalls.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (match a with RgDone true => True | _ => wmono usegs m m' end)
    /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ match a with RgErr e => (1 <= e <= 4095)%Z | _ => True end.

Lemma rmunmap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L ->
  (0 < A)%Z -> (A + mmap_len L <= 2^64)%Z -> (0 < L < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (enode (NMunmap A L) (dec_munmap A L))
       (epost (rmunmap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST ERR MI -> -> A0 AL L0 LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  unfold rmunmap_entry. apply impl_enode.
  carve_frame 32%nat ST.
  do 6 step. (* [comment removed for export] *)
  step. step. (* [comment removed for export] *)
  do 3 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_munmap_Some _ _ _ _ Hdec) as [ci D]. clear Hdec.
  destruct ans as [e|[|]].
  - destruct D as [-> He]. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
  - rewrite D. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
Qed.

Lemma rmprotect_args : forall A L, (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 <= A)%Z -> (0 <= L)%Z -> (A + L + 4096 <= 2^64)%Z ->
  Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))) = Z_to_bv 64 A
  /\ Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + L + 4095))) 18446744073709547520))
                 - bv_unsigned (Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))))) = Z_to_bv 64 L.
Proof.
  intros A L HA HL A0 L0 B. rewrite (Z.land_comm 18446744073709547520).
  rewrite (unsigned_lit A), (unsigned_lit (A + L + 4095)) by lia. rewrite !land_m4096 by lia.
  assert (E1 : (A - A mod 4096 = A)%Z) by lia.
  assert (E2 : ((A + L + 4095) - (A + L + 4095) mod 4096 = A + L)%Z) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2. rewrite !unsigned_lit by lia. split; [reflexivity|]. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ rw_cells usegs m' RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
    /\ match a with
       | RgErr e => (1 <= e <= 4095)%Z
       | RgDone true => rw_cells usegs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
       | RgDone false => True
       end.

Lemma rmprotect_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  rw_cells usegs m RPAGE_SIZE [C8 (Z_to_bv 64 4096)] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P ->
  (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 < A)%Z -> (0 < L)%Z -> (A + L + 4096 <= 2^64)%Z -> (0 <= P < 2^64)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (A + L <= 0x10000 \/ 0x69000 <= A)%Z ->
  (0x69000 <= lo)%Z -> (errno_addr tp + 4 <= RPAGE_SIZE \/ RPAGE_SIZE + 8 <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (enode (NMprotect A L P) (dec_mprotect A L))
       (epost (rmprotect_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST ERR PG MI -> -> -> AA LA A0 L0 AL PR LO SEP1 SEP2 SEP3 SEP4 SLO SEP5 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold rmprotect_entry, RPAGE_SIZE in *. apply impl_enode.
  carve_frame 16%nat ST.
  step. step. step. step.
  do 7 step.
  destruct (rmprotect_args A L AA LA ltac:(lia) ltac:(lia) AL) as [E1 E2]. rewrite E2, E1.
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_mprotect_Some _ _ _ _ Hdec) as [ci D]. clear Hdec.
  rewrite (mmap_len_aligned L LA) in D.
  destruct ans as [e|[|]].
  - destruct D as [-> He]. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D.
    assert (ROF : forall x : word, (A <= bv_unsigned x < A + L)%Z -> ro_addr usegs x = false) by (intros x Hx; apply ref_ro_addr_false; lia).
    sys_nret. lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish.
  - rewrite D. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; exact I.
Qed.

Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom usegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ stk usegs m' lo (bv_unsigned sp)
        /\ rw_cells usegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
        /\ (1 <= e <= 4095)%Z
    | MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom usegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
        /\ wmono usegs m m2 /\ mem_inv usegs m2
        /\ stk usegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
        /\ rw_cells usegs m2 (errno_addr tp) [C4 errv]
        /\ mmap_addr_ok ATOP len avoid x = true
    end.

Lemma rmmap_anon_spec : forall (isnone : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
  let prot := (if isnone then 0 else 3)%Z in
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 prot -> a3 = Z_to_bv 64 34 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < len <= 2^62)%Z ->
  (lo <= bv_unsigned sp - 80)%Z -> (ATOP <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (enode (NMmap 0 len prot 34) (if isnone then dec_mmap_none ATOP len avoid else dec_mmap ATOP len avoid))
       (epost (rmmap_anon_post isnone ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc len avoid errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros prot ST ERR MI -> -> -> -> -> -> LEN LO CEIL SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl usegs m) as WM.
  atop_facts.
  assert (PR : (0 <= prot < 4)%Z) by (destruct isnone; subst prot; lia). clearbody prot.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  step. step.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec.
  assert (D : exists ci, match ans with
              | MmErr e => rsp = efferr_ci ci e /\ (1 <= e <= 4095)%Z
              | MmOk a => rsp = (if isnone then mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] ci
                                 else mkEffectU (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))] [] [] ci)
                          /\ mmap_addr_ok ATOP len avoid a = true
              end).
  { destruct isnone; [pose proof (dec_mmap_none_Some _ _ _ _ _ Hdec) as [ci D] | pose proof (dec_mmap_Some _ _ _ _ _ Hdec) as [ci D]];
      exists ci; destruct ans; exact D. }
  clear Hdec. destruct D as [ci D]. destruct ans as [e|x].
  - clear MU1. destruct D as [-> He]. sys_nret.
    step. step. step.
    rewrite unsigned_errno_ret, zb_lxor_ones, Z.lor_0_l by lia.
    if_cases K; zify_cond K.
    + (* [comment removed for export] *)
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      finish; lia.
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by lia.
      step. step. step. step.
      replace (Z_to_bv 64 18446744073709551604) with (errno_ret 12) by (apply bv_eq; reflexivity).
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia).
      finish; lia.
  - clear MU. destruct D as [-> Hok]. pose proof (mmap_addr_ok_true _ _ _ _ Hok) as ((XA & X0 & XC) & XAV).
    pose proof (mmap_len_ge len) as ML.
    lazymatch goal with |- context [nret (MSsvc _ _ _ _ _ _ ?mc _) _] => rename mc into m2 end || idtac.
    destruct isnone; sys_nret_raw.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           set (m' := mm);
           assert (Hza : (0 <= x < 2^64)%Z) by lia; assert (Hzn : (0 <= mmap_len len < 2^64)%Z) by lia;
           assert (Hzan : (x + mmap_len len <= 2^64)%Z) by lia
         end.
    1: pose proof (rw_cells_unmaps_other usegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_unmaps_other usegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
    2: pose proof (rw_cells_zeros_other usegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_zeros usegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST) as ST'.
    all: fold m' in FR', ST'; clear FR; rename ST into ST0.
    all: step; step; step.
    all: rewrite zb_lxor_ones, Z.lor_0_l by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia.
    all: if_cases K; zify_cond K; rewrite ?land_ones64 in K by lia; [| exfalso; lia].
    (* [comment removed for export] *)
    all: step; step; step; step; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]; step.
    (* [comment removed for export] *)
    all: do 9 step; release_frame FR' ST' (bv_unsigned sp); step.
    all: apply evt_done; unfold rmmap_anon_post, mmap_raw; cbv iota.
    all: do 14 eexists; eexists; split; [subst m'; reflexivity|].
    all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST'|]; split; [exact ERR| exact Hok].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    R a r u /\
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (u = false -> wmono usegs m m')
    /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

Lemma rmmap_fixed_spec : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  (forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rstrip rsp = fixed_shape A L r u) ->
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 50 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < A)%Z -> (0 < L <= 2^62)%Z -> (A + mmap_len L < 2^64)%Z -> (0 <= P < 4)%Z ->
  (lo <= bv_unsigned sp - 80)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (enode (NMmap A L P 50) dec)
       (epost (rmmap_fixed_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros DEC ST ERR MI -> -> -> -> -> -> A0 LEN AL PR LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  (* [comment removed for export] *)
  set (z0 := Z_to_bv 64 0). set (zm1 := Z_to_bv 64 (-1)). set (z50 := Z_to_bv 64 50).
  set (zA := Z_to_bv 64 A). set (zL := Z_to_bv 64 L). set (zP := Z_to_bv 64 P).
  do 6 step. step. step. do 6 step. step.
  subst z0 zm1 z50 zA zL zP.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & E). clear Hdec. rewrite <- nret_rstrip, E. clear E.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  destruct u; unfold fixed_shape; cbv iota.
  all: sys_nret.
  all: step; step; step.
  all: if_cases K; zify_cond K; [| exfalso; apply Z.lor_eq_0_iff in K; lia ].
  all: step; call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia |]; rename PC into ST; rename POST into ERR.
  all: do 10 step; release_frame FR ST (bv_unsigned sp).
  all: unfold rmmap_fixed_post; apply evt_done; exists r; eexists; do 15 eexists; split; [exact HR|]; split; [reflexivity|].
  all: split; [ eapply munch_weaken; [|exact MU]; intros y; cbn; lia |].
  all: split; [ first [intros; discriminate | intros _; assumption] |].
  all: split; [lazymatch goal with H : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact H end|].
  all: split; [lazymatch goal with H : stk usegs ?mm ?a ?b |- stk usegs ?mm _ _ => exact H end|].
  all: lazymatch goal with H : rw_cells usegs ?mm ?a ?c |- rw_cells usegs ?mm _ _ => exact H end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition rbrk_regs (a0 : word) : _ :=
  mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma ram_brk0_node :
  impl usegs (at_node usegs) (enode (NBrk 0) dec_brk0)
       (epost (fun r ms' => ms' = MS (rbrk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 0x2ec30) fc None m (seg_rom usegs) /\ (0 <= r < 2^64)%Z))
       (MS (rbrk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 0x2ec2c) fc None m (seg_rom usegs)).
Proof.
  unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
  intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as (ci & -> & Hr). sys_nret.
  apply evt_done. split; [reflexivity| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma ram_brk_node_at (pc : Z) :
  (pc = 0x2ec14 \/ pc = 0x2ec50)%Z -> forall cur req, req <> 0%Z ->
  impl usegs (at_node usegs) (enode (NBrk req) (dec_brk cur req))
       (epost (fun a ms' => ms' = MS (rbrk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem m cur req a) (seg_rom usegs)))
       (MS (rbrk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).
Proof.
  intros Hpc cur req NZ. unfold rbrk_regs.
  destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
    intros rsp a Hdec; apply dec_brk_Some in Hdec; destruct Hdec as [ci Hdec];
    (destruct a; rewrite Hdec; unfold eff0_ci, brk_res, brk_mem, zeros_of;
      [ destruct (brk_new_pages cur req) as [[lo n]|]; [sys_nret_raw | sys_nret]
      | sys_nret ];
      apply evt_done; reflexivity).
Qed.
End BRKNODES.
End CANSEC1.
