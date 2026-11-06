From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcRec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import dt1_head_c.
Import ListNotations.
Open Scope Z_scope.

Definition dinv (m0 m : word -> option byte) (o : Z) (P : list byte) : Prop :=
  wr_at rsegs m o 20 /\ munch [(o, o + 20)] m0 m /\ wmono rsegs m0 m /\ (mem_inv rsegs m0 -> mem_inv rsegs m)
  /\ bytes_at rsegs m o P.

Lemma dinv_init : forall m o, wr_at rsegs m o 20 -> dinv m m o [].
Proof.
  intros m o W. pose proof W as (Ho & Hl & _).
  split; [exact W|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [tauto|].
  apply bytes_at_nil. lia.
Qed.

Lemma dinv_ok : forall m0 m o P k, dinv m0 m o P -> k = Z.of_nat (length P) -> (length P < 20)%nat ->
  store_ok rsegs m (wa (o + k)) 1 = true.
Proof.
  intros m0 m o P k (W & _) Hk Hl. apply (wr_at_store_ok rsegs m o 20 k 1 W); lia.
Qed.

Lemma dinv_ok0 : forall m0 m (x : word), dinv m0 m (bv_unsigned x) [] -> store_ok rsegs m x 1 = true.
Proof.
  intros m0 m x D. pose proof (dinv_ok m0 m (bv_unsigned x) [] 0 D eq_refl ltac:(cbn; lia)) as H.
  rewrite Z.add_0_r in H. rewrite (wa_of_var x (bv_unsigned x) eq_refl) in H. exact H.
Qed.

Lemma wa_add0 : forall x : word, x = wa (bv_unsigned x + Z.of_nat 0).
Proof. intros x. unfold wa. cbn [Z.of_nat]. rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self. Qed.

Lemma dinv_store : forall m0 m o P (A v : word), dinv m0 m o P -> (length P < 20)%nat ->
  A = wa (o + Z.of_nat (length P)) ->
  dinv m0 (write_to_mem m A (le1 v)) o (P ++ [Z_to_bv 8 (bv_unsigned v)]).
Proof.
  intros m0 m o P A v (W & MU & WM & MI & BA) Hl ->.
  pose proof W as (Ho & Hol & _).
  pose proof (wr_at_store_ok rsegs m o 20 (Z.of_nat (length P)) 1 W ltac:(lia) ltac:(lia)) as HS.
  change (le1 v) with [Z_to_bv 8 (bv_unsigned v)].
  split; [apply wr_at_write; exact W|].
  split; [apply munch_write; [exact MU | lia | cbn [length]; lia | cbn [inside]; left; cbn [length]; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [intros HI; apply mem_inv_store; [apply MI; exact HI | exact HS]|].
  apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact BA | lia | cbn [length]; lia | left; lia].
  - apply bytes_at_write_same; cbn [length]; lia.
Qed.

Lemma rc_cons_eq : forall (x y : byte) xs ys, x = y -> xs = ys -> x :: xs = y :: ys.
Proof. intros; subst; reflexivity. Qed.

Ltac dst k :=
  lazymatch goal with
  | D : dinv ?m0 ?mc ?o ?P |- _ =>
      let HS := fresh "HS" in
      first [ pose proof (dinv_ok0 m0 mc _ D) as HS
            | pose proof (dinv_ok m0 mc o P k D eq_refl ltac:(apply Nat.ltb_lt; reflexivity)) as HS ];
      step;
      clear HS;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
          let D' := fresh "D" in
          pose proof (dinv_store m0 mc o P A v D ltac:(apply Nat.ltb_lt; reflexivity)
                        ltac:(first [reflexivity | apply wa_add0])) as D';
          clear D;
          let mc' := fresh "mc" in
          set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
      end
  end.

Ltac bstep := step; if_false.

Theorem dt1_head_holds : dt1_head_contract.
Proof.
  unfold dt1_head_contract, DT1_HEAD.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Ho W.
  pose proof (dinv_init m (bv_unsigned a0) W) as D.
  step. step.
  dst 0. bstep.
  step. dst 1. bstep.
  step. dst 2. bstep.
  step. step. dst 3. bstep.
  step. dst 4. bstep.
  step. step. dst 5. bstep.
  step. dst 6. bstep.
  step. step. dst 7. bstep.
  step. dst 8. bstep.
  step. step. dst 9. bstep.
  step. step. dst 10. bstep.
  step. step. dst 11. bstep.
  step. dst 12. bstep.
  step. dst 13. bstep.
  step. step. dst 14. bstep.
  step. dst 15. bstep.
  step. step. dst 16. bstep.
  step. dst 17. bstep.
  step. step. dst 18. bstep.
  dst 19.
  step.
  apply evt_done.
  match goal with D : dinv _ ?mf _ _ |- _ => destruct D as (W' & MU & WM & MI & BA); do 4 eexists; exists mf end.
  split; [reflexivity|].
  split; [|split; [exact MU|split; [exact WM|exact MI]]].
  eapply bytes_at_ext; [exact BA|].
  unfold dt1_bytes. cbn [map app].
  repeat apply rc_cons_eq;
    first [ reflexivity
          | apply Z_to_bv8_mod; rewrite unsigned_lit_wrap; rewrite mod_mod8_of_modw by lia; reflexivity ].
Qed.
