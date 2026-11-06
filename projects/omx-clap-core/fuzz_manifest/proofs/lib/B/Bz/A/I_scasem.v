(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/bndiv/lib/A/I_strncmpw.v, with its module paths, addresses and numbers changed; 111 of its 201 lines of code are new or changed and 225 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Bz/A/I_scasem.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Bz/A/I_scasem.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Bz/A/I_scasem.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A Require Import Shadow R_small I_qck D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition zlw (c : Z) : Z := if ((65 <=? c) && (c <=? 90))%bool then c + 32 else c.

Lemma zlw_range : forall c, 0 <= c < 256 -> 0 <= zlw c < 256.
Proof. intros c H. unfold zlw. destruct ((65 <=? c) && (c <=? 90))%bool eqn:E; [apply andb_prop in E as [E1 E2]|]; lia. Qed.

Lemma zlw_zero : forall c, 0 <= c -> (zlw c = 0 <-> c = 0).
Proof. intros c H. unfold zlw. destruct ((65 <=? c) && (c <=? 90))%bool eqn:E; [apply andb_prop in E as [E1 E2]|]; lia. Qed.

Fixpoint scase_idx_aux (b1 b2 : list byte) (k : nat) {struct k} : nat :=
  match k with
  | O => O
  | S k' => match b1, b2 with
            | x :: b1', y :: b2' => if negb (zlw (bv_unsigned x) =? zlw (bv_unsigned y)) || (bv_unsigned x =? 0) then O
                                    else S (scase_idx_aux b1' b2' k')
            | _, _ => O
            end
  end.
Definition scase_idx (n : Z) (b1 b2 : list byte) : Z := Z.of_nat (scase_idx_aux b1 b2 (Z.to_nat n)).
Definition scase_sz (n : Z) (b1 b2 : list byte) : Z := Z.min (scase_idx n b1 b2 + 1) n.
Definition scase_ok (n : Z) (b1 b2 : list byte) : Prop :=
  scase_sz n b1 b2 <= Z.of_nat (length b1) /\ scase_sz n b1 b2 <= Z.of_nat (length b2).
Definition scase_res (n : Z) (b1 b2 : list byte) : Z :=
  let i := Z.to_nat (scase_idx n b1 b2) in
  if scase_idx n b1 b2 =? n then 0
  else match nth_error b1 i, nth_error b2 i with
       | Some x, Some y => zlw (bv_unsigned x) - zlw (bv_unsigned y)
       | _, _ => 0
       end.

Definition cc_pre (b1 b2 : list byte) (k : nat) : Prop :=
  forall j, (j < k)%nat -> exists x y, nth_error b1 j = Some x /\ nth_error b2 j = Some y
    /\ zlw (bv_unsigned x) = zlw (bv_unsigned y) /\ bv_unsigned x <> 0.

Lemma cc_pre_S : forall b1 b2 k x y, cc_pre b1 b2 k -> nth_error b1 k = Some x -> nth_error b2 k = Some y ->
  zlw (bv_unsigned x) = zlw (bv_unsigned y) -> bv_unsigned x <> 0 -> cc_pre b1 b2 (S k).
Proof.
  intros b1 b2 k x y HP H1 H2 HL HX j Hj. destruct (Nat.eq_dec j k) as [->|NE]; [exists x, y; auto|]. apply HP. lia.
Qed.

Lemma cc_pre_tl : forall x1 x2 b1 b2 k, cc_pre (x1 :: b1) (x2 :: b2) (S k) -> cc_pre b1 b2 k.
Proof.
  intros x1 x2 b1 b2 k HP j Hj. destruct (HP (S j) ltac:(lia)) as (x & y & E1 & E2 & L & NZ). exists x, y. cbn in E1, E2. auto.
Qed.

Lemma cc_idx_step : forall x y b1 b2 K, zlw (bv_unsigned x) = zlw (bv_unsigned y) -> bv_unsigned x <> 0 ->
  scase_idx_aux (x :: b1) (y :: b2) (S K) = S (scase_idx_aux b1 b2 K).
Proof.
  intros x y b1 b2 K HL NZ. cbn [scase_idx_aux]. rewrite HL, Z.eqb_refl. cbn [negb orb].
  rewrite (proj2 (Z.eqb_neq _ _) NZ). reflexivity.
Qed.

Lemma cc_idx_break : forall k K b1 b2 x y,
  (k < K)%nat -> cc_pre b1 b2 k -> nth_error b1 k = Some x -> nth_error b2 k = Some y ->
  (zlw (bv_unsigned x) <> zlw (bv_unsigned y) \/ bv_unsigned x = 0) ->
  scase_idx_aux b1 b2 K = k.
Proof.
  induction k as [|k IH]; intros K b1 b2 x y HK HP H1 H2 HB.
  - destruct K as [|K']; [lia|]. destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
    cbn in H1, H2. injection H1 as ->. injection H2 as ->. cbn [scase_idx_aux].
    destruct HB as [HB|HB].
    + rewrite (proj2 (Z.eqb_neq _ _) HB). reflexivity.
    + rewrite HB. cbn. rewrite orb_true_r. reflexivity.
  - destruct K as [|K']; [lia|].
    destruct (HP 0%nat ltac:(lia)) as (x0 & y0 & Hz1 & Hz2 & HL & Hnz).
    destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
    cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
    rewrite cc_idx_step by assumption. f_equal.
    apply (IH K' b1' b2' x y); [lia| exact (cc_pre_tl _ _ _ _ _ HP)| exact H1| exact H2| exact HB].
Qed.

Lemma cc_idx_full : forall K b1 b2, cc_pre b1 b2 K -> scase_idx_aux b1 b2 K = K.
Proof.
  induction K as [|K IH]; intros b1 b2 HP; [reflexivity|].
  destruct (HP 0%nat ltac:(lia)) as (x0 & y0 & Hz1 & Hz2 & HL & Hnz).
  destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
  cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
  rewrite cc_idx_step by assumption. f_equal. apply IH. exact (cc_pre_tl _ _ _ _ _ HP).
Qed.

Lemma cc_idx_ge : forall k K b1 b2, (k <= K)%nat -> cc_pre b1 b2 k -> (k <= scase_idx_aux b1 b2 K)%nat.
Proof.
  induction k as [|k IH]; intros K b1 b2 HK HP; [lia|].
  destruct K as [|K']; [lia|].
  destruct (HP 0%nat ltac:(lia)) as (x0 & y0 & Hz1 & Hz2 & HL & Hnz).
  destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
  cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
  rewrite cc_idx_step by assumption. specialize (IH K' b1' b2' ltac:(lia) (cc_pre_tl _ _ _ _ _ HP)). lia.
Qed.

Lemma cc_idx_le : forall K b1 b2, (scase_idx_aux b1 b2 K <= K)%nat.
Proof.
  induction K as [|K IH]; intros b1 b2; [cbn; lia|].
  destruct b1 as [|x1 b1']; [cbn; lia|]. destruct b2 as [|y1 b2']; [cbn; lia|].
  cbn [scase_idx_aux]. destruct (_ || _); [lia|]. specialize (IH b1' b2'). lia.
Qed.

Lemma cc_res_break : forall n b1 b2 k x y, 0 <= n -> (k < Z.to_nat n)%nat -> cc_pre b1 b2 k ->
  nth_error b1 k = Some x -> nth_error b2 k = Some y ->
  (zlw (bv_unsigned x) <> zlw (bv_unsigned y) \/ bv_unsigned x = 0) ->
  scase_idx n b1 b2 = Z.of_nat k /\ scase_res n b1 b2 = zlw (bv_unsigned x) - zlw (bv_unsigned y).
Proof.
  intros n b1 b2 k x y N0 HK HP H1 H2 HB.
  assert (E : scase_idx n b1 b2 = Z.of_nat k) by (unfold scase_idx; rewrite (cc_idx_break k _ b1 b2 x y HK HP H1 H2 HB); reflexivity).
  split; [exact E|]. unfold scase_res. rewrite E. rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite Nat2Z.id, H1, H2. reflexivity.
Qed.

Lemma cc_res_full : forall n b1 b2, 0 <= n -> cc_pre b1 b2 (Z.to_nat n) ->
  scase_idx n b1 b2 = n /\ scase_res n b1 b2 = 0.
Proof.
  intros n b1 b2 N0 HP.
  assert (E : scase_idx n b1 b2 = n) by (unfold scase_idx; rewrite (cc_idx_full _ b1 b2 HP); lia).
  split; [exact E|]. unfold scase_res. rewrite E, Z.eqb_refl. reflexivity.
Qed.

Lemma cc_idx_firstn : forall K b1 b2 j, (scase_idx_aux b1 b2 K < j \/ K <= j)%nat ->
  scase_idx_aux (firstn j b1) (firstn j b2) K = scase_idx_aux b1 b2 K.
Proof.
  induction K as [|K IH]; intros b1 b2 j HJ; [reflexivity|].
  destruct j as [|j']; [cbn in HJ; lia|].
  destruct b1 as [|x1 b1']; [reflexivity|]. destruct b2 as [|y1 b2']; [rewrite firstn_nil; reflexivity|].
  cbn [firstn scase_idx_aux]. cbn [scase_idx_aux] in HJ.
  destruct (_ || _); [reflexivity|]. f_equal. apply IH. lia.
Qed.

Lemma zbrute256 : forall (f g : Z -> Z),
  forallb (fun k => Z.eqb (f (Z.of_nat k)) (g (Z.of_nat k))) (seq 0 256) = true -> forall c, 0 <= c < 256 -> f c = g c.
Proof.
  intros f g H c Hc. rewrite forallb_forall in H.
  specialize (H (Z.to_nat c) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.

Lemma lw_expr : forall c, 0 <= c < 256 -> c + Z.b2z ((c + -65) mod 18446744073709551616 <? 26) ≪ 5 = zlw c.
Proof.
  apply (zbrute256 (fun c => c + Z.b2z ((c + -65) mod 18446744073709551616 <? 26) ≪ 5) zlw). vm_compute. reflexivity.
Qed.

Lemma iscc_cmp_loop : forall (r k : nat) (n p1 p2 : Z) (b1 b2 : list byte)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem),
  n = Z.of_nat (k + S r) -> n < 2^64 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> scase_ok n b1 b2 -> cc_pre b1 b2 k -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a0' a1' : word) (x1 x2 : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0' a1' a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 p2) (Z_to_bv 64 p1) s4 s5 s6 s7 (Z_to_bv 64 x2) (Z_to_bv 64 x1) s10
                    (Z_to_bv 64 (scase_idx n b1 b2)) t3 t4 t5 t6)
               F (Z_to_bv 64 0x424a4) fc None m (seg_rom asegs)
      /\ 0 <= x1 < 256 /\ 0 <= x2 < 256 /\ zlw x1 - zlw x2 = scase_res n b1 b2)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p2) (Z_to_bv 64 p1) s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (Z.of_nat k)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x42460) fc None m (seg_rom asegs)).
Proof.
  induction r as [|r IH]; intros k n p1 p2 b1 b2 ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m
    Hn HN B1 B2 OK HP MI;
  ( pose proof (cc_idx_ge k (Z.to_nat n) b1 b2 ltac:(lia) HP) as GE;
    pose proof OK as (L1 & L2); unfold scase_sz, scase_idx in L1, L2;
    destruct (nth_error b1 k) as [x|] eqn:E1; [| apply nth_error_None in E1; lia];
    destruct (nth_error b2 k) as [y|] eqn:E2; [| apply nth_error_None in E2; lia];
    pose proof (bytes_at_nth1 asegs m p1 b1 k x B1 E1) as BX; pose proof (ro_C1_of_bytes m _ _ BX) as CX;
    pose proof (bytes_at_nth1 asegs m p2 b2 k y B2 E2) as BY; pose proof (ro_C1_of_bytes m _ _ BY) as CY;
    pose proof (bytes_at_bound _ _ _ _ B1) as BB1; pose proof (bytes_at_bound _ _ _ _ B2) as BB2;
    pose proof (bv_unsigned_in_range 8 x) as XR; pose proof (bv_unsigned_in_range 8 y) as YR; unfold bv_modulus in XR, YR;
    change (2 ^ Z.of_N 8) with 256 in XR, YR;
    pose proof (zlw_range (bv_unsigned x) XR) as LXR; pose proof (zlw_range (bv_unsigned y) YR) as LYR;
    pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
    assert (EUk : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia);
    assert (EUk1 : bv_unsigned (Z_to_bv 64 (Z.of_nat k + 1)) = Z.of_nat k + 1) by (apply unsigned_lit; lia);
    assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia);
    assert (EU1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia);
    assert (EU2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia);
    assert (EUx : bv_unsigned (Z_to_bv 64 (bv_unsigned x)) = bv_unsigned x) by (apply unsigned_lit; lia);
    assert (EUy : bv_unsigned (Z_to_bv 64 (bv_unsigned y)) = bv_unsigned y) by (apply unsigned_lit; lia);
    assert (EULx : bv_unsigned (Z_to_bv 64 (zlw (bv_unsigned x))) = zlw (bv_unsigned x)) by (apply unsigned_lit; lia);
    assert (EULy : bv_unsigned (Z_to_bv 64 (zlw (bv_unsigned y))) = zlw (bv_unsigned y)) by (apply unsigned_lit; lia);
    lstep; set (q1 := p1 + Z.of_nat k) in *; lstep;
    lstep; set (q2 := p2 + Z.of_nat k) in *; lstep;
    cbv beta in *;
    lstep; if_cases K; zify_cond K; rewrite ?EUx, ?EUy in K; try change (bv_unsigned (Z_to_bv 64 0)) with 0 in K).
  - destruct (cc_res_break n b1 b2 k x y ltac:(lia) ltac:(lia) HP E1 E2 (or_intror K)) as (RI & RR).
    apply evt_done. do 2 eexists. exists (bv_unsigned x), (bv_unsigned y). rewrite RI.
    split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
  - do 8 lstep. rewrite (lw_expr (bv_unsigned x) XR), (lw_expr (bv_unsigned y) YR).
    lstep. if_cases K2; zify_cond K2; rewrite ?EULx, ?EULy in K2.
    + destruct (cc_res_break n b1 b2 k x y ltac:(lia) ltac:(lia) HP E1 E2 (or_introl K2)) as (RI & RR).
      apply evt_done. do 2 eexists. exists (bv_unsigned x), (bv_unsigned y). rewrite RI.
      split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
    + pose proof (cc_pre_S b1 b2 k x y HP E1 E2 K2 K) as HP1.
      lstep. lstep. if_false. lstep.
      destruct (cc_res_full n b1 b2 ltac:(lia) ltac:(replace (Z.to_nat n) with (S k) by lia; exact HP1)) as (RI & RR).
      apply evt_done. do 2 eexists. exists (bv_unsigned x), (bv_unsigned y). rewrite RI.
      split; [reflexivity|]. split; [lia| split; [lia|]]. rewrite RR, K2. lia.
  - destruct (cc_res_break n b1 b2 k x y ltac:(lia) ltac:(lia) HP E1 E2 (or_intror K)) as (RI & RR).
    apply evt_done. do 2 eexists. exists (bv_unsigned x), (bv_unsigned y). rewrite RI.
    split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
  - do 8 lstep. rewrite (lw_expr (bv_unsigned x) XR), (lw_expr (bv_unsigned y) YR).
    lstep. if_cases K2; zify_cond K2; rewrite ?EULx, ?EULy in K2.
    + destruct (cc_res_break n b1 b2 k x y ltac:(lia) ltac:(lia) HP E1 E2 (or_introl K2)) as (RI & RR).
      apply evt_done. do 2 eexists. exists (bv_unsigned x), (bv_unsigned y). rewrite RI.
      split; [reflexivity|]. split; [lia| split; [lia| symmetry; exact RR]].
    + pose proof (cc_pre_S b1 b2 k x y HP E1 E2 K2 K) as HP1.
      lstep. lstep. if_true.
      replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
      apply (IH (S k) n p1 p2 b1 b2); [lia| lia| exact B1| exact B2| exact OK| exact HP1| exact MI].
Qed.
