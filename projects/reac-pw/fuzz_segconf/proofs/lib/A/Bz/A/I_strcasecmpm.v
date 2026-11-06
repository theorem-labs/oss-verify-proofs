(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/leptonica/fhmtgen_fuzzer/lib/K5/A10/I_strcmpw.v, with its module paths, module names and addresses changed; 133 of its 171 lines of code are new or changed and 61 lines of the source are left out. *)
(* reac-pw/fuzz_segconf image A (fuzz_segconf.asan, sha256 48c5355bdacb...): the comparison loop of the strcasecmp
   wrapper ___interceptor_strcasecmp (0x44af8, 0x500 bytes; the loop is 0x44b58-0x44b94) and the model of what it
   computes. Written for this unit; the shape follows fuzz_manifest's strncasecmp walk (lib/A/Bz/A/I_scasem.v at
   origin/ossv/recipes 501c0d516c69), without the length bound: the loop stops at the first index where the
   ASCII-lowered bytes differ or the first string's byte is 0.

   The loop body, per index k (s2 = first string, s1 = second string, s4 = k):
     0x44b58 add a0,s2,s4; add a1,s1,s4; lbu a0,0(a0); lbu a1,0(a1)
     0x44b68 a2 / a1 := the ASCII-lowered bytes (addi -65; sltiu 26; slli 5; add)
     0x44b88 sub s5,a2,a1; addi s4,s4,1; beqz a0,0x44b98; beqz s5,0x44b58
   so at 0x44b98 s4 holds the stop index + 1 and s5 the difference of the lowered bytes there. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import Shadow R_small I_qck D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* ---- the model ---- *)

(* the wrapper's ASCII lowering of one byte value (0x44b68-0x44b84) *)
Definition zlc (c : Z) : Z := if ((65 <=? c) && (c <=? 90))%bool then c + 32 else c.

Lemma zlc_range : forall c, 0 <= c < 256 -> 0 <= zlc c < 256.
Proof. intros c H. unfold zlc. destruct ((65 <=? c) && (c <=? 90))%bool eqn:E; [apply andb_prop in E as [E1 E2]|]; lia. Qed.

Lemma zlc_zero : forall c, 0 <= c -> (zlc c = 0 <-> c = 0).
Proof. intros c H. unfold zlc. destruct ((65 <=? c) && (c <=? 90))%bool eqn:E; [apply andb_prop in E as [E1 E2]|]; lia. Qed.

(* the index where the loop stops: the first k with lowered bytes that differ or a 0 byte in the first string *)
Fixpoint scc_idx (b1 b2 : list byte) {struct b1} : nat :=
  match b1, b2 with
  | x :: b1', y :: b2' =>
      if negb (zlc (bv_unsigned x) =? zlc (bv_unsigned y)) || (bv_unsigned x =? 0) then O
      else S (scc_idx b1' b2')
  | _, _ => O
  end.

(* the loop stops inside both byte lists *)
Definition scc_ok (b1 b2 : list byte) : Prop :=
  (scc_idx b1 b2 < length b1)%nat /\ (scc_idx b1 b2 < length b2)%nat.

(* the number of bytes the wrapper then checks in each string *)
Definition scc_sz (b1 b2 : list byte) : Z := Z.of_nat (scc_idx b1 b2) + 1.

(* the answer: the difference of the lowered bytes at the stop index *)
Definition scc_res (b1 b2 : list byte) : Z :=
  match nth_error b1 (scc_idx b1 b2), nth_error b2 (scc_idx b1 b2) with
  | Some x, Some y => zlc (bv_unsigned x) - zlc (bv_unsigned y)
  | _, _ => 0
  end.

(* the first k indices: both bytes present, the lowered bytes agree, the first is not 0 *)
Definition ccp (b1 b2 : list byte) (k : nat) : Prop :=
  forall j, (j < k)%nat -> exists x y, nth_error b1 j = Some x /\ nth_error b2 j = Some y
    /\ zlc (bv_unsigned x) = zlc (bv_unsigned y) /\ bv_unsigned x <> 0.

Lemma ccp_0 : forall b1 b2, ccp b1 b2 0.
Proof. intros b1 b2 j Hj. lia. Qed.

Lemma ccp_S : forall b1 b2 k x y, ccp b1 b2 k -> nth_error b1 k = Some x -> nth_error b2 k = Some y ->
  zlc (bv_unsigned x) = zlc (bv_unsigned y) -> bv_unsigned x <> 0 -> ccp b1 b2 (S k).
Proof.
  intros b1 b2 k x y HP H1 H2 HL HX j Hj. destruct (Nat.eq_dec j k) as [->|NE]; [exists x, y; auto|]. apply HP. lia.
Qed.

Lemma ccp_tl : forall x1 x2 b1 b2 k, ccp (x1 :: b1) (x2 :: b2) (S k) -> ccp b1 b2 k.
Proof.
  intros x1 x2 b1 b2 k HP j Hj. destruct (HP (S j) ltac:(lia)) as (x & y & E1 & E2 & L & NZ). exists x, y. cbn in E1, E2. auto.
Qed.

Lemma scc_idx_step : forall x y b1 b2, zlc (bv_unsigned x) = zlc (bv_unsigned y) -> bv_unsigned x <> 0 ->
  scc_idx (x :: b1) (y :: b2) = S (scc_idx b1 b2).
Proof.
  intros x y b1 b2 HL NZ. cbn [scc_idx]. rewrite HL, Z.eqb_refl. cbn [negb orb].
  rewrite (proj2 (Z.eqb_neq _ _) NZ). reflexivity.
Qed.

Lemma scc_idx_break : forall k b1 b2 x y,
  ccp b1 b2 k -> nth_error b1 k = Some x -> nth_error b2 k = Some y ->
  (zlc (bv_unsigned x) <> zlc (bv_unsigned y) \/ bv_unsigned x = 0) ->
  scc_idx b1 b2 = k.
Proof.
  induction k as [|k IH]; intros b1 b2 x y HP H1 H2 HB.
  - destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
    cbn in H1, H2. injection H1 as ->. injection H2 as ->. cbn [scc_idx].
    destruct HB as [HB|HB].
    + rewrite (proj2 (Z.eqb_neq _ _) HB). reflexivity.
    + rewrite HB. cbn. rewrite orb_true_r. reflexivity.
  - destruct (HP 0%nat ltac:(lia)) as (x0 & y0 & Hz1 & Hz2 & HL & Hnz).
    destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
    cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
    rewrite scc_idx_step by assumption. f_equal.
    apply (IH b1' b2' x y); [exact (ccp_tl _ _ _ _ _ HP)| exact H1| exact H2| exact HB].
Qed.

Lemma scc_idx_ge : forall k b1 b2, ccp b1 b2 k -> (k <= scc_idx b1 b2)%nat.
Proof.
  induction k as [|k IH]; intros b1 b2 HP; [lia|].
  destruct (HP 0%nat ltac:(lia)) as (x0 & y0 & Hz1 & Hz2 & HL & Hnz).
  destruct b1 as [|x1 b1']; [discriminate|]. destruct b2 as [|y1 b2']; [discriminate|].
  cbn in Hz1, Hz2. injection Hz1 as ->. injection Hz2 as ->.
  rewrite scc_idx_step by assumption. specialize (IH b1' b2' (ccp_tl _ _ _ _ _ HP)). lia.
Qed.

Lemma scc_break : forall k b1 b2 x y,
  ccp b1 b2 k -> nth_error b1 k = Some x -> nth_error b2 k = Some y ->
  (zlc (bv_unsigned x) <> zlc (bv_unsigned y) \/ bv_unsigned x = 0) ->
  scc_idx b1 b2 = k /\ scc_sz b1 b2 = Z.of_nat k + 1 /\ scc_res b1 b2 = zlc (bv_unsigned x) - zlc (bv_unsigned y).
Proof.
  intros k b1 b2 x y HP H1 H2 HB.
  pose proof (scc_idx_break k b1 b2 x y HP H1 H2 HB) as E.
  split; [exact E|]. split; [unfold scc_sz; rewrite E; reflexivity|].
  unfold scc_res. rewrite E, H1, H2. reflexivity.
Qed.

(* ---- the lowering, as the code computes it ---- *)

Lemma zbrute256 : forall (f g : Z -> Z),
  forallb (fun k => Z.eqb (f (Z.of_nat k)) (g (Z.of_nat k))) (seq 0 256) = true -> forall c, 0 <= c < 256 -> f c = g c.
Proof.
  intros f g H c Hc. rewrite forallb_forall in H.
  specialize (H (Z.to_nat c) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.

Lemma lc_expr : forall c, 0 <= c < 256 -> c + Z.b2z ((c + -65) mod 18446744073709551616 <? 26) ≪ 5 = zlc c.
Proof.
  apply (zbrute256 (fun c => c + Z.b2z ((c + -65) mod 18446744073709551616 <? 26) ≪ 5) zlc). vm_compute. reflexivity.
Qed.

(* ---- the loop ---- *)

Lemma sub_zero_iff : forall a b, 0 <= a < 256 -> 0 <= b < 256 ->
  (bv_unsigned (Z_to_bv 64 (a - b)) = 0 <-> a = b).
Proof.
  intros a b Ha Hb. rewrite unsigned_lit_wrap.
  split; intros H; [| subst b; rewrite Z.sub_diag; reflexivity].
  Z.div_mod_to_equations. lia.
Qed.

Lemma icase_cmp_loop : forall (r k : nat) (p1 p2 : Z) (b1 b2 : list byte)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  scc_idx b1 b2 = (k + r)%nat -> scc_ok b1 b2 ->
  bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 ->
  p1 + Z.of_nat (length b1) <= 2^47 -> p2 + Z.of_nat (length b2) <= 2^47 -> ccp b1 b2 k -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a0' a1' a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p2) a0' a1' a2' a3' a4 a5 a6 a7
                    (Z_to_bv 64 p1) s3 (Z_to_bv 64 (scc_sz b1 b2)) (Z_to_bv 64 (scc_res b1 b2)) s6 s7 s8 s9 s10 s11
                    t3 t4 t5 t6)
               F (Z_to_bv 64 0x44b98) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 p2) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p1) s3 (Z_to_bv 64 (Z.of_nat k)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x44b58) fc None m (seg_rom asegs)).
Proof.
  induction r as [|r IH]; intros k p1 p2 b1 b2 ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m Hr OK B1 B2 R1 R2 HP MI;
  ( pose proof (scc_idx_ge k b1 b2 HP) as GE;
    pose proof OK as (L1 & L2);
    destruct (nth_error b1 k) as [x|] eqn:E1; [| apply nth_error_None in E1; lia];
    destruct (nth_error b2 k) as [y|] eqn:E2; [| apply nth_error_None in E2; lia];
    pose proof (bytes_at_nth1 asegs m p1 b1 k x B1 E1) as BX; pose proof (ro_C1_of_bytes m _ _ BX) as CX;
    pose proof (bytes_at_nth1 asegs m p2 b2 k y B2 E2) as BY; pose proof (ro_C1_of_bytes m _ _ BY) as CY;
    pose proof (bytes_at_bound _ _ _ _ B1) as BB1; pose proof (bytes_at_bound _ _ _ _ B2) as BB2;
    pose proof (bv_unsigned_in_range 8 x) as XR; pose proof (bv_unsigned_in_range 8 y) as YR; unfold bv_modulus in XR, YR;
    change (2 ^ Z.of_N 8) with 256 in XR, YR;
    pose proof (zlc_range (bv_unsigned x) XR) as LXR; pose proof (zlc_range (bv_unsigned y) YR) as LYR;
    pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
    assert (EUk : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia);
    assert (EUk1 : bv_unsigned (Z_to_bv 64 (Z.of_nat k + 1)) = Z.of_nat k + 1) by (apply unsigned_lit; lia);
    assert (EU1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia);
    assert (EU2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia);
    assert (EUx : bv_unsigned (Z_to_bv 64 (bv_unsigned x)) = bv_unsigned x) by (apply unsigned_lit; lia);
    assert (EUy : bv_unsigned (Z_to_bv 64 (bv_unsigned y)) = bv_unsigned y) by (apply unsigned_lit; lia);
    assert (EULx : bv_unsigned (Z_to_bv 64 (zlc (bv_unsigned x))) = zlc (bv_unsigned x)) by (apply unsigned_lit; lia);
    assert (EULy : bv_unsigned (Z_to_bv 64 (zlc (bv_unsigned y))) = zlc (bv_unsigned y)) by (apply unsigned_lit; lia);
    lstep; lstep; set (q1 := p1 + Z.of_nat k) in *; set (q2 := p2 + Z.of_nat k) in *;
    lstep; lstep; cbv beta in *;
    do 8 lstep; rewrite (lc_expr (bv_unsigned x) XR), (lc_expr (bv_unsigned y) YR);
    lstep; lstep;
    lstep; if_cases K; zify_cond K; rewrite ?EUx in K).
  - (* r = 0, first byte 0: the loop stops at k *)
    destruct (scc_break k b1 b2 x y HP E1 E2 (or_intror K)) as (EI & ES & ER).
    apply evt_done. do 4 eexists. rewrite ES, ER. reflexivity.
  - lstep. if_cases K2; zify_cond K2.
    + (* the lowered bytes agree: the loop would go on past k, against Hr *)
      exfalso. apply (sub_zero_iff _ _ LXR LYR) in K2.
      pose proof (scc_idx_ge (S k) b1 b2 (ccp_S b1 b2 k x y HP E1 E2 K2 K)). lia.
    + assert (NEQ : zlc (bv_unsigned x) <> zlc (bv_unsigned y))
        by (intros E; apply K2; apply (sub_zero_iff _ _ LXR LYR); exact E).
      destruct (scc_break k b1 b2 x y HP E1 E2 (or_introl NEQ)) as (EI & ES & ER).
      apply evt_done. do 4 eexists. rewrite ES, ER. reflexivity.
  - (* r > 0, first byte 0: the loop would stop at k, against Hr *)
    exfalso. pose proof (scc_idx_break k b1 b2 x y HP E1 E2 (or_intror K)). lia.
  - lstep. if_cases K2; zify_cond K2.
    + apply (sub_zero_iff _ _ LXR LYR) in K2.
      pose proof (ccp_S b1 b2 k x y HP E1 E2 K2 K) as HP1.
      replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
      apply (IH (S k) p1 p2 b1 b2); [lia| exact OK| exact B1| exact B2| exact R1| exact R2| exact HP1| exact MI].
    + exfalso.
      assert (NEQ : zlc (bv_unsigned x) <> zlc (bv_unsigned y))
        by (intros E; apply K2; apply (sub_zero_iff _ _ LXR LYR); exact E).
      pose proof (scc_idx_break k b1 b2 x y HP E1 E2 (or_introl NEQ)). lia.
Qed.
