(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ITree Ceiling Nodes SysStep Decode SysMm.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts F_syscalls.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Definition vm_wait_entry : Z := 0x25f30.
Definition p0munmap_entry : Z := 0x19fa8.
Definition p0mprotect_entry : Z := 0x19e8c.
Definition p0mmap_entry : Z := 0x19da0.
Definition p0mremap_entry : Z := 0x19ed4.

Definition vm_wait_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma vm_wait_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m P0_VMLOCK [C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 32)%Z -> (P0_IMG_HI <= lo)%Z ->
  evt rsegs (vm_wait_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x25f30) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST VL MI LO ILO.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  do 7 step. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by reflexivity. step. try if_true. do 5 step.
  release_frame FR ST (bv_unsigned sp).
  unfold vm_wait_post. finish.
Qed.

Definition p0munmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (match a with RgDone true => True | _ => wmono rsegs m m' end)
    /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ rw_cells rsegs m' P0_VMLOCK [C4 (Z_to_bv 64 0)]
    /\ match a with RgErr e => (1 <= e <= 4095)%Z | _ => True end.

Lemma p0munmap_spec {HCEIL : HasCeiling} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m P0_VMLOCK [C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L ->
  (0 < A)%Z -> (A mod 4096 = 0)%Z -> (A + mmap_len L <= alloc_ceiling)%Z -> (0 < L < 2^63)%Z ->
  (lo <= bv_unsigned sp - 64)%Z -> (P0_IMG_HI <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (errno_addr tp + 4 <= P0_VMLOCK \/ P0_VMLOCK + 4 <= errno_addr tp)%Z ->
  ((A + mmap_len L <= P0_IMG_LO \/ P0_RO_HI <= A) /\ (A + mmap_len L <= 0x2a000 \/ P0_IMG_HI <= A))%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMunmap A L) (dec_munmap A L))
       (epost (p0munmap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x19fa8) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR VL MI -> -> A0 AA AL L0 LO ILO SEP1 SEP2 SEP3 SEPE [SEPA1 SEPA2] TP.
  pose proof alloc_ceiling_bounds.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  apply impl_enode.
  carve_frame 32%nat ST.
  do 6 step.
  step. call_sp vm_wait_spec; [exact ST | exact VL | exact MI | lia | lia | ]. rename POST into ST.
  lazymatch goal with H : mem_inv rsegs _ |- _ => rename H into MI end.
  do 3 step.
  step_ecall.
  split. { at_node_solve. all: rewrite ?unsigned_lit by lia; try lia.
           - unfold page_size. exact AA.
           - rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
           - unfold two_pow_64. fold (mmap_len L). lia. }
  intros rsp ans Hdec. pose proof (dec_munmap_Some _ _ _ _ Hdec) as D. clear Hdec.
  destruct ans as [e|[|]].
  - destruct D as [Hs He]. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold p0munmap_post, munmap_ret, rg_errno. finish; lia.
  - rename D into Hs. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold p0munmap_post, munmap_ret, rg_errno. finish; exact I.
  - rename D into Hs. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold p0munmap_post, munmap_ret, rg_errno. finish; exact I.
Qed.

Definition p0mprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ rw_cells rsegs m' P0_PAGE_SIZE [C8 (Z_to_bv 64 4096)]
    /\ match a with
       | RgErr e => (1 <= e <= 4095)%Z
       | RgDone true => rw_cells rsegs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
       | RgDone false => True
       end.

Lemma p0mprotect_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (errv : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m P0_PAGE_SIZE [C8 (Z_to_bv 64 4096)] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 (PROT_READ + PROT_WRITE) ->
  (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 < A)%Z -> (0 < L)%Z -> (A + L + 4096 <= 2^63)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  ((A + L <= P0_IMG_LO \/ P0_RO_HI <= A) /\ (A + L <= 0x2a000 \/ P0_IMG_HI <= A))%Z ->
  (P0_IMG_HI <= lo)%Z -> (errno_addr tp + 4 <= P0_PAGE_SIZE \/ P0_PAGE_SIZE + 8 <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMprotect A L (PROT_READ + PROT_WRITE)) (dec_mprotect A L))
       (epost (p0mprotect_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x19e8c) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR PG MI -> -> -> AA LA A0 L0 AL LO SEP1 SEP2 SEP3 [SEP4 SEP4'] SLO SEP5 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply impl_enode.
  carve_frame 16%nat ST.
  step. step. step. step.
  do 7 step.
  destruct (rmprotect_args A L AA LA ltac:(lia) ltac:(lia) ltac:(lia)) as [E1 E2]. rewrite E2, E1.
  step. step_ecall.
  split. { at_node_solve. all: rewrite ?unsigned_lit by lia; try lia.
           - unfold page_size. exact AA.
           - rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
           - unfold two_pow_64. fold (mmap_len L). rewrite (mmap_len_aligned L LA). lia. }
  intros rsp ans Hdec. pose proof (dec_mprotect_Some _ _ _ _ Hdec) as D. clear Hdec.
  rewrite (mmap_len_aligned L LA) in D.
  destruct ans as [e|[|]].
  - destruct D as [Hs He]. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold p0mprotect_post, munmap_ret, rg_errno. finish; lia.
  - rename D into Hs.
    assert (ROF : forall x : word, (A <= bv_unsigned x < A + L)%Z -> ro_addr rsegs x = false) by (intros x Hx; apply p0_ro_addr_false; lia).
    sys_nret. lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold p0mprotect_post, munmap_ret, rg_errno. finish.
  - rename D into Hs. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold p0mprotect_post, munmap_ret, rg_errno. finish; exact I.
Qed.

Definition p0mmap_anon_post {HCEIL : HasCeiling} (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp)
        /\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
        /\ (1 <= e <= 4095)%Z
    | MmOk x =>

        mmap_addr_ok len avoid x = true /\
        ((alloc_ceiling < x + mmap_len len)%Z \/
         exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
         /\ wmono rsegs m m2 /\ mem_inv rsegs m2
         /\ stk rsegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
         /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv])
    end.

Lemma p0mmap_anon_spec {HCEIL : HasCeiling} : forall (isnone : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
  let prot := (if isnone then 0 else 3)%Z in
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 prot -> a3 = Z_to_bv 64 34 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < len <= 2^62)%Z ->
  (lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMmap 0 len prot 34) (if isnone then dec_mmap_none len avoid else dec_mmap len avoid))
       (epost (p0mmap_anon_post isnone ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc len avoid errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x19da0) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros prot ST ERR MI -> -> -> -> -> -> LEN LO CEIL SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_bounds.

  assert (SH1 : w_is0 (Z_to_bv 64 len) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  assert (SH3 : let P := Z_to_bv 64 prot in let FL := Z_to_bv 64 34 in
      (mmap_modeled_b P FL (Z_to_bv 64 0) = true
       \/ (mmap_modeled_b P FL (Z_to_bv 64 0) = false /\
           mmap_noaccess_b P FL (Z_to_bv 64 0) = true)
       \/ (mmap_modeled_b P FL (Z_to_bv 64 0) = false /\
           mmap_noaccess_b P FL (Z_to_bv 64 0) = false /\
           mmap_fixed_noaccess_b P FL (Z_to_bv 64 0) = true))).
  { destruct isnone; subst prot; [right; left; split; reflexivity | left; reflexivity]. }
  assert (PR : (0 <= prot < 4)%Z) by (destruct isnone; subst prot; lia). clearbody prot.
  apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  step. step.
  step. step. step_ecall.
  split. { at_node_solve. all: first [exact SH1 | exact SH3 | reflexivity]. }
  intros rsp ans Hdec.
  assert (D : match ans with
              | MmErr e => strip rsp = efferr e /\ (1 <= e <= 4095)%Z
              | MmOk a => strip rsp = (if isnone then mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] []
                                 else mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))])
                          /\ mmap_addr_ok len avoid a = true
              end).
  { destruct isnone; [pose proof (dec_mmap_none_Some _ _ _ _ Hdec) as D | pose proof (dec_mmap_Some _ _ _ _ Hdec) as D];
      destruct ans; exact D. }
  clear Hdec. destruct ans as [e|x].
  - clear MU1. destruct D as [Hs He]. sys_nret.
    step. step. step.
    rewrite unsigned_errno_ret, zb_lxor_ones, Z.lor_0_l by lia.
    if_cases K; zify_cond K.
    +
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold p0mmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      finish; lia.
    +
      rewrite ?unsigned_lit in K by lia.
      step. step. step. step.
      replace (Z_to_bv 64 18446744073709551604) with (errno_ret 12) by (apply bv_eq; reflexivity).
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold p0mmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia).
      finish; lia.
  - clear MU. destruct D as [Hs Hok]. pose proof (mmap_addr_ok_true _ _ _ Hok) as ((XA & X0 & XCmax) & XAV).

    destruct (Z.lt_ge_cases alloc_ceiling (x + mmap_len len)) as [BAD|XC].
    { apply evt_done. unfold p0mmap_anon_post. split; [exact Hok| left; exact BAD]. }
    pose proof alloc_ceiling_bounds. pose proof (mmap_len_ge len) as ML.
    lazymatch goal with |- context [nret (MSsvc _ _ _ _ _ _ ?mc _) _] => rename mc into m2 end || idtac.
    destruct isnone; sys_nret_raw.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           set (m' := mm);
           assert (Hza : (0 <= x < 2^64)%Z) by lia; assert (Hzn : (0 <= mmap_len len < 2^64)%Z) by lia;
           assert (Hzan : (x + mmap_len len <= 2^64)%Z) by lia
         end.
    1: pose proof (rw_cells_unmaps_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_unmaps_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
    2: pose proof (rw_cells_zeros_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_zeros rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST) as ST'.
    all: fold m' in FR', ST'; clear FR; rename ST into ST0.
    all: step; step; step.
    all: rewrite zb_lxor_ones, Z.lor_0_l by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia.
    all: if_cases K; zify_cond K; rewrite ?land_ones64 in K by lia; [| exfalso; lia].

    all: step; step; step; step; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]; step.

    all: do 9 step; release_frame FR' ST' (bv_unsigned sp); step.
    all: apply evt_done; unfold p0mmap_anon_post, mmap_raw; cbv iota; split; [exact Hok|]; right.
    all: do 14 eexists; eexists; split; [subst m'; reflexivity|].
    all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST'|]; exact ERR.
Qed.

Definition p0mmap_fixed_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    R a r u /\
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (u = false -> wmono rsegs m m')
    /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (sysret_errno r errv)]
    /\ rw_cells rsegs m' P0_VMLOCK [C4 (Z_to_bv 64 0)].

Lemma p0mmap_fixed_spec : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (errv : word) (lo : Z),
  (forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ strip rsp = fixed_shape A L r u) ->
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m P0_VMLOCK [C4 (Z_to_bv 64 0)] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 PROT_NONE -> a3 = Z_to_bv 64 50 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < A)%Z -> (0 < L <= 2^62)%Z -> (A + mmap_len L < 2^64)%Z ->
  (lo <= bv_unsigned sp - 96)%Z -> (P0_IMG_HI <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (errno_addr tp + 4 <= P0_VMLOCK \/ P0_VMLOCK + 4 <= errno_addr tp)%Z ->
  ((A + mmap_len L <= P0_IMG_LO \/ P0_RO_HI <= A) /\ (A + mmap_len L <= 0x2a000 \/ P0_IMG_HI <= A))%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMmap A L PROT_NONE 50) dec)
       (epost (p0mmap_fixed_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x19da0) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros DEC ST ERR VL MI -> -> -> -> -> -> A0 LEN AL LO ILO SEP1 SEP2 SEP3 SEPE [SEPA1 SEPA2] TP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  assert (SH1 : w_is0 (Z_to_bv 64 L) = false) by (rewrite w_is0_lit by lia; apply Z.eqb_neq; lia).
  apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.

  set (z0 := Z_to_bv 64 0). set (zm1 := Z_to_bv 64 (-1)). set (z50 := Z_to_bv 64 50).
  set (zA := Z_to_bv 64 A). set (zL := Z_to_bv 64 L). set (zP := Z_to_bv 64 PROT_NONE).
  do 6 step. step.
  call_sp vm_wait_spec; [exact ST | exact VL | exact MI | lia | lia | ]. rename POST into ST.
  lazymatch goal with H : mem_inv rsegs _ |- _ => rename H into MI end.
  do 6 step. step.
  subst z0 zm1 z50 zA zL zP.
  step. step. step_ecall.
  split. { at_node_solve. all: first [exact SH1 | reflexivity | right; right; repeat split; reflexivity]. }
  intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & Hs). clear Hdec.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  destruct u; unfold fixed_shape in Hs; cbv iota in Hs.
  all: sys_nret.
  all: step; step; step.
  all: if_cases K; zify_cond K; [| exfalso; apply Z.lor_eq_0_iff in K; lia ].
  all: step; call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia |]; rename PC into ST; rename POST into ERR.
  all: do 10 step; release_frame FR ST (bv_unsigned sp).
  all: unfold p0mmap_fixed_post; apply evt_done; exists r; eexists; do 15 eexists; split; [exact HR|]; split; [reflexivity|].
  all: split; [ eapply munch_weaken; [|exact MU]; intros y; cbn; lia |].
  all: split; [ first [intros; discriminate | intros _; assumption] |].
  all: split; [lazymatch goal with H : mem_inv rsegs ?mm |- mem_inv rsegs ?mm => exact H end|].
  all: split; [lazymatch goal with H : stk rsegs ?mm ?a ?b |- stk rsegs ?mm _ _ => exact H end|].
  all: split; [lazymatch goal with H : rw_cells rsegs ?mm ?a [C4 (sysret_errno _ _)] |- _ => exact H end|].
  all: lazymatch goal with H : rw_cells rsegs ?mm 377592%Z ?c |- _ => exact H end.
Qed.

Definition mremap_same_raw (old on nn : Z) (m2 : word -> option byte) : word -> option byte :=
  if (nn <? on)%Z then apply_unmaps m2 [(wa (old + nn), Z_to_bv 64 (on - nn))]
  else if (on <? nn)%Z then apply_zeros m2 [(wa (old + on), Z_to_bv 64 (nn - on))] else m2.

Definition mremap_move_raw (old on dst nn : Z) (m2 : word -> option byte) : word -> option byte :=
  apply_copy m2 (apply_zeros (apply_unmaps m2 [(wa old, Z_to_bv 64 on)]) [(wa (dst + on), Z_to_bv 64 (nn - on))])
             (mkCopy (wa old) (wa dst) (Z_to_bv 64 on)).

Definition p0mremap_post {HCEIL : HasCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (old old_len new_len : Z) (avoid : list (Z * Z)) (errv canary : word) (lo : Z) (m : word -> option byte) (a : mremap_ans)
    : machine_state -> Prop :=
  let on := mmap_len old_len in let nn := mmap_len new_len in
  fun ms' =>
    match a with
    | MrErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp)
        /\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)]
        /\ rw_cells rsegs m' P0_GOT_SSP [C8 (Z_to_bv 64 P0_SSP_GUARD)]
        /\ rw_cells rsegs m' P0_SSP_GUARD [C8 canary]
        /\ (1 <= e <= 4095)%Z
    | MrSame =>

        (on < nn /\ alloc_ceiling < old + nn)%Z \/
        exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 old) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mremap_same_raw old on nn m2) (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2
        /\ wmono rsegs m m2 /\ mem_inv rsegs m2
        /\ stk rsegs (mremap_same_raw old on nn m2) lo (bv_unsigned sp)
        /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
        /\ rw_cells rsegs m2 P0_GOT_SSP [C8 (Z_to_bv 64 P0_SSP_GUARD)]
        /\ rw_cells rsegs m2 P0_SSP_GUARD [C8 canary]
        /\ (nn <= on \/ (old + nn <= alloc_ceiling /\ avoids old nn avoid = true))%Z
    | MrMoved dst =>

        (alloc_ceiling < dst + nn)%Z \/
        exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mremap_move_raw old on dst nn m2) (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m2
        /\ wmono rsegs m m2 /\ mem_inv rsegs m2
        /\ stk rsegs (mremap_move_raw old on dst nn m2) lo (bv_unsigned sp)
        /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
        /\ rw_cells rsegs m2 P0_GOT_SSP [C8 (Z_to_bv 64 P0_SSP_GUARD)]
        /\ rw_cells rsegs m2 P0_SSP_GUARD [C8 canary]
        /\ (dst mod page_size = 0 /\ 0 < dst /\ dst + nn <= alloc_ceiling /\ on < nn)%Z /\ avoids dst nn avoid = true
    end.

Lemma p0mremap_spec {HCEIL : HasCeiling} : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (old old_len new_len : Z) (avoid : list (Z * Z)) (errv canary : word) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  rw_cells rsegs m P0_GOT_SSP [C8 (Z_to_bv 64 P0_SSP_GUARD)] ->
  rw_cells rsegs m P0_SSP_GUARD [C8 canary] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 old -> a1 = Z_to_bv 64 old_len -> a2 = Z_to_bv 64 new_len -> a3 = Z_to_bv 64 MREMAP_MAYMOVE ->
  (0 < old)%Z -> (old mod 4096 = 0)%Z -> (0 < old_len <= 2^62)%Z -> (0 < new_len <= 2^62)%Z ->
  (old + mmap_len old_len <= alloc_ceiling)%Z ->
  ((old + mmap_len old_len <= P0_IMG_LO \/ P0_RO_HI <= old) /\ (old + mmap_len old_len <= 0x2a000 \/ P0_IMG_HI <= old))%Z ->
  (forall a k, avoids a k avoid = true -> ((a + k <= P0_IMG_LO \/ P0_RO_HI <= a) /\ (a + k <= 0x2a000 \/ P0_IMG_HI <= a))%Z) ->
  (lo <= bv_unsigned sp - 112)%Z -> (alloc_ceiling <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  ((errno_addr tp + 4 <= P0_GOT_SSP \/ P0_GOT_SSP + 8 <= errno_addr tp) /\ (errno_addr tp + 4 <= P0_SSP_GUARD \/ P0_SSP_GUARD + 8 <= errno_addr tp))%Z ->
  (old + mmap_len old_len <= errno_addr tp \/ errno_addr tp + 4 <= old)%Z ->
  (forall a k, avoids a k avoid = true -> (a + k <= errno_addr tp \/ errno_addr tp + 4 <= a)%Z) ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMremap old old_len new_len) (dec_mremap old old_len new_len avoid))
       (epost (p0mremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old old_len new_len avoid errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x19ed4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST ERR GOT SSP MI -> -> -> -> O0 OA OL NL OCEIL [OIMG OIMG'] AVI LO CEIL SEP1 [EIMG EIMG'] SEPO AVE TP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_bounds.
  pose proof (mmap_len_ge old_len) as MLO. pose proof (mmap_len_ge new_len) as MLN.
  pose proof (mmap_len_lt old_len) as MLO2. pose proof (mmap_len_lt new_len) as MLN2.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
  apply impl_enode.
  carve_frame 96%nat ST.
  do 7 step.
  step. step.
  do 4 step.
  step.
  step. step.
  step.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. } clear K1.
  step. step_ecall.
  split. { at_node_solve. all: rewrite ?unsigned_lit by lia; try lia.
           - unfold page_size. exact OA.
           - unfold page_align_is0_b. rewrite w_is0_lit by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
             rewrite unsigned_lit by lia. apply Z.leb_gt. unfold two_pow_64. fold (mmap_len new_len). lia.
           - unfold page_align_is0_b. rewrite w_is0_lit by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
             rewrite unsigned_lit by lia. apply Z.leb_gt. unfold two_pow_64. fold (mmap_len old_len). lia. }
  intros rsp ans Hdec. pose proof (dec_mremap_Some _ _ _ _ _ _ Hdec) as D. clear Hdec. cbv zeta in D.
  destruct ans as [e| |dst].
  -
    clear MU1. destruct D as [Hs He]. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 4 step. if_false. do 9 step. release_frame FR ST (bv_unsigned sp).
    unfold p0mremap_post. cbv zeta iota. finish; lia.
  -
    clear MU. destruct D as [Hs Hsz].
    apply evt_nret_strip. rewrite Hs. unfold mremap_inplace_effect, mremap_tail. rewrite !lit_add_lit.
    set (on := mmap_len old_len) in *. set (nn := mmap_len new_len) in *.

    assert (REST : forall (xt0 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 : word) (m' : word -> option byte),
      (nn <= on \/ (old + nn <= alloc_ceiling /\ avoids old nn avoid = true))%Z ->
      m' = mremap_same_raw old on nn m0 ->
      rw_cells rsegs m' (bv_unsigned sp + -96)
        [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk)))))));
         C8 canary; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra; C8 a4; C8 a5; C8 a6; C8 a7] ->
      stk rsegs m' lo (bv_unsigned sp + -96) ->
      rw_cells rsegs m' 375432 [C8 canary] ->
      evt rsegs
        (p0mremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old old_len new_len avoid errv canary lo m MrSame)
        (MS (mkR (Z_to_bv 64 0x19f70) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp xt0 t1 t2
                 xs0 (Z_to_bv 64 375432) (Z_to_bv 64 old) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x17f70) fc None m' (seg_rom rsegs))).
    { intros xt0 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 m' Hsz' Em' FR' ST' SSP'.

      step. step. step. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia]. step.
      do 4 step. if_false. do 9 step. release_frame FR' ST' (bv_unsigned sp).
      apply evt_done. unfold p0mremap_post. cbv zeta iota. fold on nn. right.
      do 14 eexists. exists m0. split; [rewrite Em'; reflexivity|].
      split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [rewrite <- Em'; exact ST'|].
      split; [exact ERR|]. split; [exact GOT|]. split; [exact SSP|]. exact Hsz'. }
    destruct (Z.ltb_spec nn on) as [LT|GE].
    +
      rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs.
      replace (Z_to_bv 64 106344 + Z_to_bv 64 4 : word) with (Z_to_bv 64 106348 : word) by (rewrite lit_add_lit; reflexivity).
      rewrite apply_mem_unmaps. change (Z_to_bv 64 (old + nn)) with (wa (old + nn)).
      assert (Hza : (0 <= old + nn < 2^64)%Z) by lia. assert (Hzn : (0 <= on - nn < 2^64)%Z) by lia.
      assert (Hzan : (old + nn + (on - nn) <= 2^64)%Z) by lia.
      step. apply (REST _ _ _ _ _ _ _ _ _ (apply_unmaps m0 [(wa (old + nn), Z_to_bv 64 (on - nn))])).
      * left. lia.
      * unfold mremap_same_raw. rewrite (proj2 (Z.ltb_lt _ _) LT). reflexivity.
      * apply (rw_cells_unmaps_other rsegs _ _ _ Hza Hzn Hzan _ _ FR). cbn; lia.
      * apply (stk_unmaps_other rsegs _ _ _ Hza Hzn Hzan _ _ ST). lia.
      * apply (rw_cells_unmaps_other rsegs _ _ _ Hza Hzn Hzan _ _ SSP). cbn; lia.
    + destruct (Z.ltb_spec on nn) as [LT2|GE2].
      *
        rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs.
        replace (Z_to_bv 64 106344 + Z_to_bv 64 4 : word) with (Z_to_bv 64 106348 : word) by (rewrite lit_add_lit; reflexivity).
        rewrite apply_mem_zeros. change (Z_to_bv 64 (old + on)) with (wa (old + on)).
        destruct Hsz as [?|[Hcemax Hav]]; [lia|]. pose proof alloc_ceiling_bounds. pose proof (AVI _ _ Hav) as [Himg Himg'].

        destruct (Z.lt_ge_cases alloc_ceiling (old + nn)) as [BAD|Hce].
        { apply evt_done. unfold p0mremap_post. cbv zeta iota. fold on nn. left. split; [exact LT2| exact BAD]. }
        assert (Hza : (0 <= old + on < 2^64)%Z) by lia. assert (Hzn : (0 <= nn - on < 2^64)%Z) by lia.
        assert (Hzan : (old + on + (nn - on) <= 2^64)%Z) by lia.
        step. apply (REST _ _ _ _ _ _ _ _ _ (apply_zeros m0 [(wa (old + on), Z_to_bv 64 (nn - on))])).
        -- right. split; [exact Hce | exact Hav].
        -- unfold mremap_same_raw. rewrite (proj2 (Z.ltb_ge _ _) GE), (proj2 (Z.ltb_lt _ _) LT2). reflexivity.
        -- apply (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan _ _ FR). cbn; lia.
        -- apply (stk_zeros rsegs _ _ _ Hza Hzn Hzan _ _ ST).
        -- apply (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan _ _ SSP). cbn; lia.
      *
        rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs.
        replace (Z_to_bv 64 106344 + Z_to_bv 64 4 : word) with (Z_to_bv 64 106348 : word) by (rewrite lit_add_lit; reflexivity).
        rewrite apply_mem_none.
        step. apply (REST _ _ _ _ _ _ _ _ _ m0); [left; lia| |exact FR|exact ST|exact SSP].
        unfold mremap_same_raw. rewrite (proj2 (Z.ltb_ge _ _) GE), (proj2 (Z.ltb_ge _ _) GE2). reflexivity.
  -
    clear MU. destruct D as (Hs & (DA & D0 & DCmax & LT) & DAV). pose proof alloc_ceiling_bounds.
    set (nn0 := mmap_len new_len) in DCmax.

    destruct (Z.lt_ge_cases alloc_ceiling (dst + mmap_len new_len)) as [BAD|DC].
    { apply evt_done. unfold p0mremap_post. cbv zeta iota. left. exact BAD. }
    subst nn0.
    pose proof (AVI _ _ DAV) as [Dimg Dimg']. pose proof (AVE _ _ DAV) as Derr.
    set (on := mmap_len old_len) in *. set (nn := mmap_len new_len) in *.
    apply evt_nret_strip. rewrite Hs. unfold mremap_move_effect, mremap_tail. rewrite (proj2 (Z.ltb_lt _ _) LT), !lit_add_lit.
    rewrite nret_MSsvc_copies; rewrite ?mkR_set_a0; simp_regs.
    replace (Z_to_bv 64 106344 + Z_to_bv 64 4 : word) with (Z_to_bv 64 106348 : word) by (rewrite lit_add_lit; reflexivity).
    cbn [apply_writes apply_copies].
    set (m1 := apply_unmaps m0 [(Z_to_bv 64 old, Z_to_bv 64 on)]).
    set (m2' := apply_zeros m1 [(Z_to_bv 64 (dst + on), Z_to_bv 64 (nn - on))]).
    set (m3 := apply_copy m0 m2' (mkCopy (Z_to_bv 64 old) (Z_to_bv 64 dst) (Z_to_bv 64 on))).
    assert (U1 : (0 <= old < 2^64)%Z) by lia. assert (U2 : (0 <= on < 2^64)%Z) by lia. assert (U3 : (old + on <= 2^64)%Z) by lia.
    assert (Z1 : (0 <= dst + on < 2^64)%Z) by lia. assert (Z2 : (0 <= nn - on < 2^64)%Z) by lia. assert (Z3 : (dst + on + (nn - on) <= 2^64)%Z) by lia.
    assert (C1 : (0 <= dst < 2^64)%Z) by lia. assert (C3 : (dst + on <= 2^64)%Z) by lia.
    assert (FR1 := rw_cells_unmaps_other rsegs _ _ _ U1 U2 U3 _ _ FR ltac:(cbn; lia)).
    assert (ST1 := stk_unmaps_other rsegs _ _ _ U1 U2 U3 _ _ ST ltac:(lia)).
    assert (SSP1 := rw_cells_unmaps_other rsegs _ _ _ U1 U2 U3 _ _ SSP ltac:(cbn; lia)).
    assert (MI1 := mem_inv_unmaps rsegs _ _ _ U1 U2 U3 MI).
    fold m1 in FR1, ST1, SSP1, MI1.
    assert (FR2 := rw_cells_zeros_other rsegs _ _ _ Z1 Z2 Z3 _ _ FR1 ltac:(cbn; lia)).
    assert (ST2 := stk_zeros rsegs _ _ _ Z1 Z2 Z3 _ _ ST1).
    assert (SSP2 := rw_cells_zeros_other rsegs _ _ _ Z1 Z2 Z3 _ _ SSP1 ltac:(cbn; lia)).
    assert (MI2 := mem_inv_zeros rsegs _ _ _ Z1 Z2 Z3 MI1 ltac:(intros x Hx; apply p0_ro_addr_false; lia)).
    fold m2' in FR2, ST2, SSP2, MI2.
    assert (FR3 := rw_cells_copy_other rsegs m0 m2' old dst on C1 U2 _ _ FR2 ltac:(cbn; lia)).
    assert (ST3 := stk_copy_other rsegs m0 m2' old dst on C1 U2 _ _ ST2 ltac:(lia)).
    assert (SSP3 := rw_cells_copy_other rsegs m0 m2' old dst on C1 U2 _ _ SSP2 ltac:(cbn; lia)).
    assert (MI3 := mem_inv_copy rsegs m0 m2' old dst on C1 U2 MI2 ltac:(intros x Hx; apply p0_ro_addr_false; lia)).
    fold m3 in FR3, ST3, SSP3, MI3.
    clear FR2 ST2 SSP2 MI2 FR1 ST1 SSP1 MI1.

    step. step. step. step. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia]. step.
    do 4 step. if_false. do 9 step. release_frame FR3 ST3 (bv_unsigned sp).
    apply evt_done. unfold p0mremap_post. cbv zeta iota. fold on nn. right.
    do 14 eexists. exists m0. split; [subst m3 m2' m1; unfold mremap_move_raw; reflexivity|].
    split; [exact MU1|]. split; [exact WM|]. split; [exact MI|]. split; [subst m3 m2' m1; unfold mremap_move_raw; exact ST3|].
    split; [exact ERR|]. split; [exact GOT|]. split; [exact SSP|]. pose proof alloc_ceiling_bounds. repeat split; try assumption; lia.
Qed.
