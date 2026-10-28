(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import Tac ITree Nodes SysStep Decode.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.Agent Require Import F_syscalls_u5.
Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac transport_zeros segs m a n Ha Hn Han ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_zeros m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "zero-filled range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
  | H : mem_inv segs m |- _ =>
      let H' := fresh "MI" in
      assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
        by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
      clear H
  end.

Ltac transport_unmaps segs m a n Ha Hn Han ::=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : stk segs m ?lo ?hi |- _ =>
      first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi) in H; [|slia]
            | idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
  | H : munch ?W ?m0 m |- _ =>
      first [ apply (munch_unmaps m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
            | fail 100 "unmapped range not inside the declared footprint" ]
  | H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
  | H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
  end.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Lemma mmap_len_ge : forall len, (len <= mmap_len len)%Z.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.
Lemma mmap_len_nonneg : forall len, (0 <= len)%Z -> (0 <= mmap_len len)%Z.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition munmap_ret (a : range_ans) : word :=
  match a with RgErr _ => Z_to_bv 64 (-1) | RgDone _ => Z_to_bv 64 0 end.
Definition rg_errno (a : range_ans) (errv : word) : word :=
  match a with RgErr e => Z_to_bv 64 e | RgDone _ => errv end.

(* [comment removed for export] *)
Definition munmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (match a with RgDone true => True | _ => wmono asegs m m' end)
    /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ match a with RgErr e => (1 <= e <= 4095)%Z | _ => True end.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_len_aligned : forall len, (len mod 4096 = 0)%Z -> mmap_len len = len.
Proof. intros. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. Qed.

Lemma land_ldiff_distr' x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_m4096 x : (0 <= x < 2^64)%Z -> Z.land x 18446744073709547520 = (x - x mod 4096)%Z.
Proof.
  intros Hx.
  assert (E : 18446744073709547520%Z = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr'. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12)%Z with 4096%Z. pose proof (Z.div_mod x 4096). lia.
Qed.

(* [comment removed for export] *)
Lemma mprotect_args : forall A L, (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 <= A)%Z -> (0 <= L)%Z -> (A + L + 4096 <= 2^64)%Z ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 A)) 18446744073709547520) = Z_to_bv 64 A
  /\ Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + (4095 + L)))) 18446744073709547520))
                 - bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 A)) 18446744073709547520))) = Z_to_bv 64 L.
Proof.
  intros A L HA HL A0 L0 B.
  rewrite (unsigned_lit A), (unsigned_lit (A + (4095 + L))) by lia. rewrite !land_m4096 by lia.
  assert (E1 : (A - A mod 4096 = A)%Z) by lia.
  assert (E2 : ((A + (4095 + L)) - (A + (4095 + L)) mod 4096 = A + L)%Z) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2. rewrite !unsigned_lit by lia. split; [reflexivity|]. f_equal. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_fix_errno (e : Z) : Z := if (e =? 1)%Z then 12%Z else e.

(* [comment removed for export] *)
Definition mmap_raw (isnone : bool) (x len : Z) (m : word -> option byte) : word -> option byte :=
  if isnone then apply_unmaps m [(wa x, Z_to_bv 64 (mmap_len len))]
  else apply_zeros m [(wa x, Z_to_bv 64 (mmap_len len))].

(* [comment removed for export] *)
Definition mmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp)
        /\ rw_cells asegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
        /\ (1 <= e <= 4095)%Z
    | MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom asegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m2
        /\ wmono asegs m m2 /\ mem_inv asegs m2
        /\ stk asegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
        /\ rw_cells asegs m2 (errno_addr tp) [C4 errv]
        /\ mmap_addr_ok len avoid x = true
    end.

(* [comment removed for export] *)
End CEIL_WRAP_1.


Ltac mmap_err_finish MU WM :=
  intros ms' PO; cbv beta in PO; unfold sysret_post, sysret_val, sysret_errno in PO; rewrite errno_of_errno_ret in PO by lia;
  destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU' & WM' & MI' & ST' & ERR');
  unfold mmap_anon_post, mmap_fix_errno;
  first [ replace (_ =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia)
        | replace (_ =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia) ]; cbv iota;
  do 15 eexists; split; [reflexivity|];
  split; [ eapply munch_trans; [exact MU|]; eapply munch_weaken; [|exact MU']; intros y; cbn; lia |];
  split; [ eapply wmono_trans; [exact WM | exact WM'] |];
  split; [exact MI'|]; split; [exact ST'|]; split; [exact ERR'|]; lia.

(* [comment removed for export] *)
Ltac sys_nret_raw :=
  rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
       let p' := eval vm_compute in (p + 4)%Z in
       replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
   | _ => idtac
   end);
  first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps ].
Section CEIL_WRAP_2.
Context {RUNp : RunP}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fixed_shape (A L : Z) (r : word) (u : bool) : resp :=
  if u then mkEffectU r [] [] [(wa A, Z_to_bv 64 (mmap_len L))] [] [] else mkEffectU r [] [] [] [] [].

Definition mmap_fixed_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    R a r u /\
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (u = false -> wmono asegs m m')
    /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 (sysret_errno r errv)].
End CEIL_WRAP_2.

(* [comment removed for export] *)
