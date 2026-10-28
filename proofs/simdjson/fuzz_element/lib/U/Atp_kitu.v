(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_memchr F_memcmp F_strlen F_memcpy F_memmove_t2 Atp_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Lemma land7_mod8 : forall A, (0 <= A)%Z -> (A mod 8 = 0)%Z -> Z.land A 7 = 0%Z.
Proof. intros A H0 H8. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact H8. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma tix_shr61 : forall i, 0 <= i < 2^60 -> Z.shiftr (i + 1152921504606846976) 61 = 0.
Proof. intros i Hi. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Lemma tix_land7 : forall T i, T mod 8 = 0 -> 0 <= T -> 0 <= i -> Z.land (T + 8 * i) 7 = 0.
Proof.
  intros T i HT T0 I0. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  rewrite Z.add_mod, HT, Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

Lemma tix_cps : forall Q (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (D TAPE i RA : Z) (rest : list cell),
  rw_cells usegs m D (C8 (Z_to_bv 64 TAPE) :: rest) -> 0 < TAPE -> 0 <= i -> TAPE + 8 * i < 2^63 -> i < 2^60 -> TAPE mod 8 = 0 ->
  0 <= D -> D + 8 < 2^64 -> ra = Z_to_bv 64 RA -> 0 <= RA < 2^64 -> RA mod 2 = 0 ->
  (forall (xa1 xa2 xa3 xa4 : word),
     evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (TAPE + 8 * i)) xa1 xa2 xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 RA) fc None m (seg_rom usegs))) ->
  evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 ATP_TIX) fc None m (seg_rom usegs)).
Proof.
  intros until rest. intros DC T0 I0 TI I60 T8 D0 D64 -> RA0 RA2 HK.
  unfold ATP_TIX.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. astep. astep. astep. astep.
  replace (0 <? TAPE) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (TAPE + 8 * i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  step. if_false.

  astep. astep. astep. astep. rewrite tix_shr61 by lia.
  step. if_lia.

  step. if_lia. step. if_lia. astep. rewrite tix_land7 by lia. step. if_lia.
  step.
  replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| exact RA2]).
  eapply evt_eq; [| eapply HK]. atp_st_eq.
Qed.

Lemma svf_or_found : forall y x, 0 < y -> Z.lor (Z.land (Z.b2z (0 <? y) + -1) 18446744073709551615) x = x.
Proof.
  intros y x Hy. replace (0 <? y) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. change (1 + -1) with 0.
  rewrite Z.land_0_l. apply Z.lor_0_l.
Qed.
Lemma svf_or_npos : forall x, 0 <= x < 2^64 -> Z.lor (Z.land (Z.b2z (0 <? 0) + -1) 18446744073709551615) x = 18446744073709551615.
Proof.
  intros x Hx. cbn [Z.ltb Z.compare Z.b2z]. change (Z.land (0 + -1) 18446744073709551615) with 18446744073709551615.
  pose proof (Z.add_lor_land 18446744073709551615 x) as E.
  rewrite (Z.land_comm 18446744073709551615 x) in E. rewrite land64_mod, Z.mod_small in E by lia. lia.
Qed.

Definition svfind_res (n c : Z) (buf : list byte) : Z :=
  match find_byte c (firstn (Z.to_nat n) buf) with Some i => Z.of_nat i | None => -1 end.

Lemma svfind_res_range : forall n c buf, 0 <= n -> svfind_res n c buf = -1 \/ 0 <= svfind_res n c buf < n.
Proof.
  intros n c buf Hn. unfold svfind_res. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [i|] eqn:FB; [| left; reflexivity].
  right. pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

Definition svfind_post (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo SV A n c : Z) (buf : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (svfind_res n c buf)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 16, q)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ rw_cells usegs m' SV [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 n)].

Lemma svfind_spec : forall (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo SV A n c : Z) (buf : list byte),
  rw_cells usegs m SV [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 n)] -> q <= SV -> SV + 16 < 2^63 ->
  bytes_at usegs m A buf -> Z.of_nat (length buf) = n -> 0 < A -> A + n <= lo -> 0 <= c < 256 ->
  stk usegs m lo q -> lo <= q - 16 -> mem_inv usegs m ->
  evt usegs (svfind_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo SV A n c buf m)
    (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 SV) (Z_to_bv 64 c) (Z_to_bv 64 0) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ATP_SVFIND) fc None m (seg_rom usegs)).
Proof.
  intros until buf. intros SVC QS S63 BUF LEN A0 ALO C8R ST LO MI.
  unfold ATP_SVFIND.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (N0 : 0 <= n) by lia.
  pose proof (munch_refl [(q - 16, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. carve_frame 16%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
  step. step. step.
  step. if_cases K0; zify_cond K0.
  -
    astep. step. step. step. release_frame FR ST q. step.
    apply evt_done. unfold svfind_post. do 15 eexists. split.
    { unfold svfind_res. replace (Z.to_nat n) with 0%nat by lia. cbn [firstn find_byte]. atp_st_eq_goal. }
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact SVC.
  -
    step. astep. rewrite (Z.add_0_l A). step. if_lia. astep. astep.
    replace (0 <? A) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (A <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Pos.lxor].
    astep. step. if_false. astep. try replace (n + - 0) with n by lia. step.
    call memchr_spec.
    1:{ rewrite unsigned_lit by lia. exact BUF. }
    1:{ rewrite !unsigned_lit by lia. unfold memchr_ok. rewrite (Z.mod_small c 256) by lia.
        match goal with |- context [find_byte ?cc ?l] => destruct (find_byte cc l) end; [left|]; lia. }
    1:{ assumption. }
    rewrite !unsigned_lit by lia. rewrite (Z.mod_small c 256) by lia. unfold memchr_res. name_mem m2.
    lazymatch goal with H : mem_inv usegs m2 |- _ => rename H into MI2 end.

    match goal with |- context [find_byte ?cc ?l] => destruct (find_byte cc l) as [ix|] eqn:FB end.
    + pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn in Hl.
      astep. astep. astep. astep. step. step. step. step. release_frame FR ST q. step.
      rewrite svf_or_found by lia.
      apply evt_done. unfold svfind_post. do 15 eexists. split.
      { unfold svfind_res. rewrite FB. atp_st_eq_goal. }
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST|]. exact SVC.
    + astep. astep. astep. astep. step. step. step. step. release_frame FR ST q. step.
      rewrite svf_or_npos by (rewrite land64_mod; lia).
      apply evt_done. unfold svfind_post. do 15 eexists. split.
      { unfold svfind_res. rewrite FB. atp_st_eq_goal. }
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ST|]. exact SVC.
Qed.

End WithCeiling0.
