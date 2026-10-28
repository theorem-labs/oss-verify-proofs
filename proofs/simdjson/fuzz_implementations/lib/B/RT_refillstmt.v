(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_refill RT_state RT_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Definition populate (r : regst) (S k : Z) : regst :=
  let auser := S * Z.of_nat (length (r_st r)) in
  let msz := if r_muser r <? auser + k * S then round_fa (auser + k * S - r_muser r) else 0 in
  let muser' := r_muser r + msz in
  let newc := (muser' - auser) / S in
  let nf' := Z.of_nat (length (r_fl r)) + newc in
  let mfa' := if r_mfa r <? 4 * nf' then round_fa (4 * nf') else r_mfa r in
  mkReg muser' mfa' (r_st r ++ repeat CkIdle (Z.to_nat newc))
        (r_fl r ++ rev (map (fun j => Z.of_nat (length (r_st r)) + Z.of_nat j) (seq 0 (Z.to_nat newc)))).

Definition refill_reg (r : regst) (c : Z) : regst :=
  let n := MaxCount c / 2 in
  let r1 := if Z.of_nat (length (r_fl r)) <? n then populate r (ClassSize c) (n - Z.of_nat (length (r_fl r))) else r in
  mkReg (r_muser r1) (r_mfa r1) (r_st r1) (firstn (length (r_fl r1) - Z.to_nat n) (r_fl r1)).

Definition refill_ca (r : regst) (c : Z) : list Z :=
  let n := MaxCount c / 2 in
  let r1 := if Z.of_nat (length (r_fl r)) <? n then populate r (ClassSize c) (n - Z.of_nat (length (r_fl r))) else r in
  skipn (length (r_fl r1) - Z.to_nat n) (r_fl r1).

Definition refillΣ (Σ : rtsA) (c : Z) : rtsA :=
  mkRtsA (lay Σ) (fun c' => if c' =? c then refill_reg (pr Σ c) c else pr Σ c')
    (fun c' => if c' =? c then refill_ca (pr Σ c) c else ca Σ c') true (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ)
    (fs0 Σ) (fsc0 Σ) (fs4 Σ) (fs1 Σ) (fs3 Σ) (fs2 Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ) (ann Σ).

Definition refill_entry_st (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (T c : Z) (m : mem) : machine_state :=
  entry_st ra sp gp (Z_to_bv 64 tpA) t0 t1 t2 s0 s1 (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 (pc_addr T c)) (Z_to_bv 64 INST)
           (Z_to_bv 64 c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc refill_entry m.

Definition refill_stmt : Prop :=
  forall (Σ : rtsA) PMc (ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (c lo : Z),
  fdfs_only PMc -> mat_stable PMc -> 1 <= c <= 30 -> ca Σ c = [] ->
  ART_A Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> l_ACEIL (lay Σ) <= lo -> lo + 0x400 <= bv_unsigned sp -> bv_unsigned sp <= 2 ^ 47 ->
  cps bsegs (ASTA RTA Σ PMc (eq (refill_entry_st ra sp gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                                    F fc (l_T (lay Σ)) c m)))
    (ASTA RTA (refillΣ Σ c) PMc
       (fun ms => exists m', ret_stF fc ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) m' ms
          /\ ART_A (refillΣ Σ c) m' /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo (bv_unsigned sp)
          /\ rt_pres (live Σ) (frames Σ) (bv_unsigned sp) m m')).

Lemma refillΣ_facts : forall Σ c,
  lay (refillΣ Σ c) = lay Σ /\ live (refillΣ Σ c) = live Σ /\ frames (refillΣ Σ c) = frames Σ /\ credit (refillΣ Σ c) = credit Σ
  /\ dep (refillΣ Σ c) = dep Σ /\ sec (refillΣ Σ c) = sec Σ /\ sec_nres (refillΣ Σ c) = sec_nres Σ /\ aw (refillΣ Σ c) = aw Σ
  /\ ql (refillΣ Σ c) = ql Σ /\ qg (refillΣ Σ c) = qg Σ /\ fs0 (refillΣ Σ c) = fs0 Σ /\ fsc0 (refillΣ Σ c) = fsc0 Σ
  /\ fs4 (refillΣ Σ c) = fs4 Σ /\ ia_init (refillΣ Σ c) = ia_init Σ /\ ca_init (refillΣ Σ c) = true
  /\ (forall c', c' <> c -> pr (refillΣ Σ c) c' = pr Σ c' /\ ca (refillΣ Σ c) c' = ca Σ c')
  /\ ca (refillΣ Σ c) c = refill_ca (pr Σ c) c /\ pr (refillΣ Σ c) c = refill_reg (pr Σ c) c.
Proof.
  intros Σ c. unfold refillΣ. cbn [lay live frames ann credit dep sec sec_nres aw ql qg fs0 fsc0 fs4 fs1 fs3 fs2 ia_init ca_init pr ca].
  repeat (split; [reflexivity|]). split; [intros c' Hne; rewrite (proj2 (Z.eqb_neq c' c) Hne); split; reflexivity|].
  rewrite Z.eqb_refl. split; reflexivity.
Qed.

Lemma populate_fl_len : forall r S k, 1 <= S -> 1 <= k -> S * Z.of_nat (length (r_st r)) <= r_muser r ->
  Z.of_nat (length (r_fl (populate r S k))) = Z.of_nat (length (r_fl r)) + (r_muser (populate r S k) - S * Z.of_nat (length (r_st r))) / S
  /\ k <= (r_muser (populate r S k) - S * Z.of_nat (length (r_st r))) / S.
Proof.
  intros r S k HS Hk Hau. unfold populate. cbn [r_fl r_muser].
  set (auser := S * Z.of_nat (length (r_st r))) in *.
  assert (Hm : auser + k * S <= r_muser r + (if r_muser r <? auser + k * S then round_fa (auser + k * S - r_muser r) else 0)).
  { destruct (Z.ltb_spec (r_muser r) (auser + k * S)) as [X|X]; [pose proof (round_fa_ge (auser + k * S - r_muser r) ltac:(lia)); lia | lia]. }
  assert (Hk' : k <= (r_muser r + (if r_muser r <? auser + k * S then round_fa (auser + k * S - r_muser r) else 0) - auser) / S).
  { apply Z.div_le_lower_bound; lia. }
  split; [|exact Hk'].
  rewrite length_app, length_rev, length_map, length_seq, Nat2Z.inj_add, Z2Nat.id; [reflexivity|].
  pose proof (Z.div_pos (r_muser r + (if r_muser r <? auser + k * S then round_fa (auser + k * S - r_muser r) else 0) - auser) S ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma refill_ca_len : forall r c, 1 <= c <= 30 -> reg_wf c r -> Z.of_nat (length (refill_ca r c)) = MaxCount c / 2.
Proof.
  intros r c Hc HW. pose proof (MaxCount_range c ltac:(lia)) as (Hm1 & Hm2). pose proof (ClassSize_range c ltac:(lia)) as (Hs & _).
  destruct HW as (_ & _ & W3 & _).
  assert (Hn : 1 <= MaxCount c / 2 <= 8) by (split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia).
  unfold refill_ca. destruct (Z.ltb_spec (Z.of_nat (length (r_fl r))) (MaxCount c / 2)) as [X|X].
  - destruct (populate_fl_len r (ClassSize c) (MaxCount c / 2 - Z.of_nat (length (r_fl r))) ltac:(lia) ltac:(lia) W3) as (E1 & E2).
    rewrite length_skipn. lia.
  - rewrite length_skipn. lia.
Qed.

End GWIN.
