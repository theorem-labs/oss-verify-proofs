From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes check_reject_clean_starved_c fuzz_pick_c.
Import ListNotations.
Open Scope Z_scope.

(* The walk of the out-of-line ubsan fuzz_pick 0x152d0 (fuzz_pick_c.v).  Its djb2 loop is the instruction pattern of the
   two loops check_reject_clean_starved keeps inline (0x13c94, 0x13d64), with a0 the base, a1 the count, a3 the hash,
   a4 the flag (a0 <> 0), a5 / a6 the checked / loaded pointers and a7 / t0 the scratch.  The pure facts and the loop
   tactic are those of the inline loops (CrsHash.v, CrsSegA.v, CrsSegB.v), stated here on their own so that this file
   needs only the frozen check_reject_clean_starved_c.v and the contract.
   Provenance: the same walk of the same code in the ubsan CF tree, origin/cold/h-rw-ide-17-p102-S-cf e7104a983098,
   lib/U/Prog/CF/CrsHash.v (blob 89cd88f73658): crsu_iter :114-137 = fp_iter, crsu_lp :177-193 = fp_loop, crsu_pick
   :196-241 = fuzz_pick_holds (restated for fuzz_pick_contract's equality premises).  Copied, not Required: that file
   is another lane's, is not on this base (base blob c1e614aab40b is the old walk), and would put the CF contract and
   SRCF into the closure of lib/U/Prog. *)

Lemma fp_djb2_cons : forall h (c : byte) r,
  djb2 h (zb (c :: r)) = djb2 ((33 * h + bv_unsigned c) mod 2 ^ 64) (zb r).
Proof. reflexivity. Qed.

Lemma fp_djb2_range : forall l h, 0 <= h < 2 ^ 64 -> 0 <= djb2 h l < 2 ^ 64.
Proof.
  induction l as [|c r IH]; intros h Hh; cbn [djb2]; [exact Hh|].
  apply IH. apply Z.mod_pos_bound. lia.
Qed.

Lemma fp_pick0 : forall x, pick x 0 = 0.
Proof. reflexivity. Qed.

Lemma fp_pick : forall x n, 0 < n -> pick x n = djb2 5381 x mod n.
Proof. intros x n Hn. unfold pick. rewrite (proj2 (Z.eqb_neq n 0)) by lia. reflexivity. Qed.

Lemma fp_read1 : forall m p (c : byte) r,
  bytes_at rsegs m p (c :: r) -> ov_read_bytes rsegs m (wa p) 1 = Some [c].
Proof.
  intros m p c r HB. rewrite <- (Z.add_0_r p) at 1.
  rewrite (bytes_at_read rsegs m p _ 0 1 HB) by (cbn; lia). reflexivity.
Qed.

Lemma fp_tail : forall m p (c : byte) r,
  bytes_at rsegs m p (c :: r) -> bytes_at rsegs m (p + 1) r.
Proof.
  intros m p c r HB. apply (proj1 (bytes_at_app rsegs m p [c] r)) in HB. destruct HB as [_ HB]. exact HB.
Qed.

Lemma fp_hash_val : forall h (c : byte), 0 <= h < 2 ^ 64 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 h)) 5 + h + bv_unsigned (zxb c)) =
  Z_to_bv 64 ((33 * h + bv_unsigned c) mod 2 ^ 64).
Proof.
  intros h c Hh.
  assert (Hc : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  unfold zxb. rewrite (unsigned_lit h) by lia. rewrite (unsigned_lit (bv_unsigned c)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  apply bv_eq. rewrite !unsigned_lit_wrap. rewrite Zmod_mod. f_equal. change (2 ^ 5) with 32. lia.
Qed.

Lemma fp_sltiu : forall p, 1 <= p < 2 ^ 64 -> v_sltiu (Z_to_bv 64 p) 1 = Z_to_bv 64 0.
Proof.
  intros p Hp. unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec p 1); [lia | reflexivity].
Qed.

Lemma fp_snez : forall d, 0 < d < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 d) = Z_to_bv 64 1.
Proof.
  intros d Hd. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
  destruct (Z.ltb_spec 0 d); [reflexivity | lia].
Qed.

Lemma fp_remu : forall x y, 0 <= x < 2 ^ 64 -> 0 < y < 2 ^ 64 ->
  Sem.mul_div Instr.M_REMU (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x mod y).
Proof.
  intros x y Hx Hy. unfold Sem.mul_div.
  rewrite (unsigned_lit y) by lia.
  replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_modu_unsigned.
  rewrite (unsigned_lit x), (unsigned_lit y), (unsigned_lit (x mod y))
    by (pose proof (Z.mod_pos_bound x y ltac:(lia)); lia).
  reflexivity.
Qed.

Ltac fp_has_cmp x := idtac; match x with context [Z.eqb _ _] => idtac | context [Z.ltb _ _] => idtac
  | context [Z.leb _ _] => idtac end.

Ltac fp_is_binop f :=
  lazymatch f with
  | Z.add => idtac | Z.sub => idtac | Z.mul => idtac | Z.modulo => idtac | Z.div => idtac | Z.pow => idtac
  | Z.lxor => idtac | Z.lor => idtac | Z.land => idtac | Z.shiftr => idtac | Z.shiftl => idtac
  | Z.eqb => idtac | Z.ltb => idtac | Z.leb => idtac
  end.

Ltac fp_fold_lits :=
  repeat match goal with
  | |- context [?f ?a ?b] => fp_is_binop f; is_Zlit_zb a; is_Zlit_zb b;
                             let v := eval vm_compute in (f a b) in change (f a b) with v
  end.

Ltac fp_solve_c :=
  unfold bv_eqb, bv_ltu, bv_leu;
  rewrite ?unsigned_lit_wrap;
  repeat (cbn [Z.b2z]; fp_fold_lits;
          match goal with
          | |- context [Z.eqb ?a ?b] => assert_fails (fp_has_cmp a); assert_fails (fp_has_cmp b);
                                         destruct (Z.eqb_spec a b)
          | |- context [Z.ltb ?a ?b] => assert_fails (fp_has_cmp a); assert_fails (fp_has_cmp b);
                                         destruct (Z.ltb_spec a b)
          | |- context [Z.leb ?a ?b] => assert_fails (fp_has_cmp a); assert_fails (fp_has_cmp b);
                                         destruct (Z.leb_spec a b)
          end);
  cbn [Z.b2z]; fp_fold_lits;
  first [reflexivity | exfalso; Z.div_mod_to_equations; lia].

Ltac fp_br b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b by (symmetry; fp_solve_c); cbv beta iota
  end.

(* One pass of the loop at 0x152e8: the overflow check (bltu a5, a0; seqz a7, a5; xor a7, a4, a7; beqz a7; beqz a0,
   none taken), the hash step a3 := 33 * a3 + byte mod 2 ^ 64, a1 -= 1, a5 += 1, a6 += 1, and bnez a1. *)
Local Ltac fp_iter IH :=
  lazymatch goal with
  | HB : bytes_at rsegs ?m ?p (?c :: ?r), HE : _ + Z.of_nat (length (_ :: _)) = ?E, Hh : 0 <= ?h < 2 ^ 64 |- _ =>
      pose proof (fp_read1 m p c r HB) as RD;
      pose proof (bytes_at_bound rsegs m p (c :: r) HB) as BB;
      pose proof (fp_tail m p c r HB) as HB';
      cbn [length] in HE, BB;
      rewrite fp_djb2_cons;
      step; fp_br false;
      step; rewrite (fp_sltiu p ltac:(lia));
      step; step; fp_br false;
      step; fp_br false;
      do 8 step;
      rewrite (fp_hash_val h c Hh);
      replace (Z.of_nat (length (c :: r)) + -1) with (Z.of_nat (length r)) by (cbn [length]; lia);
      destruct r as [|c' r];
      [ assert (HE1 : E = p + 1) by (cbn in HE; lia); clear HE; subst E;
        change (Z.of_nat (length (@nil byte))) with 0;
        fp_br false;
        apply evt_done; cbv beta; eexists _, _; reflexivity
      | assert (Hl : 1 <= Z.of_nat (length (c' :: r)) < 2 ^ 64) by (cbn [length] in *; lia);
        fp_br true;
        eapply IH; [exact HB' | congruence | lia | cbn [length] in *; lia | assumption | apply Z.mod_pos_bound; lia] ]
  end.

Lemma fp_loop : forall (ra sp gp tp t1 t2 s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (D E : Z) (tl : list byte) (p h : Z) (a7 t0 : word),
  bytes_at rsegs m p tl -> tl <> [] -> 0 < D <= p -> p + Z.of_nat (length tl) = E -> E < 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
  evt rsegs
    (fun ms' => exists a7' t0' : word,
       ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 0) a2 (Z_to_bv 64 (djb2 h (zb tl)))
                     (Z_to_bv 64 1) (Z_to_bv 64 E) (Z_to_bv 64 E) a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1531c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (Z.of_nat (length tl))) a2 (Z_to_bv 64 h)
             (Z_to_bv 64 1) (Z_to_bv 64 p) (Z_to_bv 64 p) a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x152e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t1 t2 s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D E tl.
  induction tl as [|c r IH]; intros p h a7 t0 HB HNE HD HE HEb Hh; [congruence|].
  fp_iter IH.
Qed.

Theorem fuzz_pick_holds : fuzz_pick_contract.
Proof.
  unfold fuzz_pick_contract, FUZZ_PICK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n k x
    E0 E1 E2 Hk Hn Hd Hdn Hlen HB.
  subst a0 a1 a2 n.
  assert (Uk : bv_unsigned (Z_to_bv 64 k) = k) by (apply unsigned_lit; lia).
  pose proof (fp_djb2_range (zb x) 5381 ltac:(lia)) as DR.
  step. step. step.
  assert (TB : x = [] \/ x <> []) by (destruct x; [left; reflexivity | right; discriminate]).
  destruct TB as [-> | NE].
  - cbn [length Z.of_nat] in *. if_true.
    destruct (Z.eqb_spec k 0) as [-> | Hk0].
    + step. if_true. step. step. rewrite fp_pick0. finish.
    + step. if_false. step. rewrite fp_remu by lia. step.
      rewrite fp_pick by lia. change (djb2 5381 (zb [])) with 5381. finish.
  - assert (LP : (0 < length x)%nat) by (destruct x; [congruence | cbn; lia]).
    assert (Ulen : bv_unsigned (Z_to_bv 64 (Z.of_nat (length x))) = Z.of_nat (length x)) by (apply unsigned_lit; lia).
    if_false. do 3 step.
    rewrite (fp_snez d) by lia.
    eapply evt_cut.
    { eapply fp_loop with (D := d) (E := d + Z.of_nat (length x)) (tl := x) (p := d) (h := 5381);
        [exact HB | exact NE | lia | reflexivity | lia | lia]. }
    intros ms' (a7' & t0' & ->).
    destruct (Z.eqb_spec k 0) as [-> | Hk0].
    + step. if_true. step. step. rewrite fp_pick0. finish.
    + step. if_false. step. rewrite fp_remu by lia. step.
      rewrite fp_pick by lia. finish.
Qed.
