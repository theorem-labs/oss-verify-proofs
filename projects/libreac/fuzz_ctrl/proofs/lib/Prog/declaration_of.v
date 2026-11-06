From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcDecl RcDeclLib memset_c memcpy_c declaration_of_c.
Import ListNotations.
Open Scope Z_scope.

Section Plain.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mw ow : word) (F : bvmap 5 word) (fc : bv 32)
  (m0 : word -> option byte) (lo : Z) (row ob : list byte).
Hypothesis MSET : memset_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis LO : lo + 64 <= bv_unsigned sp.
Hypothesis HLEN : length row = 296%nat.
Hypothesis DMO : bv_unsigned ow + 32 <= bv_unsigned mw \/ bv_unsigned mw + 296 <= bv_unsigned ow.
Hypothesis DMS : bv_unsigned mw + 296 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned mw.
Hypothesis DOS : bv_unsigned ow + 32 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= bv_unsigned ow.

Definition FCELLS : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition Qd : machine_state -> Prop :=
  declaration_of_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mw ow F fc m0 lo row ob.
Definition D (mc : word -> option byte) (P : list byte) : Prop :=
  oinv rsegs (bv_unsigned sp + -64) FCELLS lo (bv_unsigned sp - 64) (bv_unsigned sp) m0 mc (bv_unsigned mw) row
    (bv_unsigned ow) P.

Lemma DF0 : bv_unsigned sp + -64 + Z.of_nat (cells_size FCELLS) <= bv_unsigned ow \/
            bv_unsigned ow + 32 <= bv_unsigned sp + -64.
Proof. unfold FCELLS. cbn [cells_size csize Nat.add]. lia. Qed.

Lemma DR0 : bv_unsigned mw + Z.of_nat (length row) <= bv_unsigned ow \/ bv_unsigned ow + 32 <= bv_unsigned mw.
Proof. rewrite HLEN. lia. Qed.

Lemma Rw : forall x : word, 0 <= bv_unsigned x < 2^64.
Proof. intros x. exact (zr_word x). Qed.

Lemma epi : forall mc res ob' rac t0c t1c t2c s0c s1c s2c s3c s4c s5c s6c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c,
  rw_cells rsegs mc (bv_unsigned sp + -64) FCELLS ->
  stk rsegs mc lo (bv_unsigned sp + -64) ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned ow, bv_unsigned ow + 32)] m0 mc ->
  wmono rsegs m0 mc -> mem_inv rsegs mc -> bytes_at rsegs mc (bv_unsigned mw) row ->
  rw_cells rsegs mc (bv_unsigned ow) [CB 32 ob'] ->
  res = (if decl_ok row then 1 else 0) -> ob' = (if decl_ok row then decl row else ob) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0c t1c t2c s0c s1c (Z_to_bv 64 res)
                     a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                 F (Z_to_bv 64 0x13ea8) fc None mc (seg_rom rsegs)).
Proof.
  intros mc res ob' rac t0c t1c t2c s0c s1c s2c s3c s4c s5c s6c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c
    FR ST MU WM MI HR HO -> ->.
  pose proof (Rw sp) as Rsp.
  unfold FCELLS in FR.
  do 9 step.
  release_frame FR ST (bv_unsigned sp).
  step.
  apply evt_done. unfold Qd, declaration_of_post, DECLARATION_OF_FRAME.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact HO|]. exact HR.
Qed.

Lemma o_memset : forall mc P (n : Z) v (x y z : word) retpc spc s0c s1c s2c s3c s4c s5c s6c t0c t1c t2c
    a3c a4c a5c a6c a7c t3c t4c t5c t6c,
  D mc P -> 0 < n -> (length P + Z.to_nat n <= 32)%nat -> 0 <= v < 256 -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
  bv_unsigned x = bv_unsigned ow + Z.of_nat (length P) -> bv_unsigned y = v -> bv_unsigned z = n ->
  (forall m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     D m' (P ++ repeat (Z_to_bv 8 v) (Z.to_nat n)) ->
     evt rsegs Qd (MS (mkR (Z_to_bv 64 retpc) spc gp tp t0' t1' t2' s0c s1c x a1' a2' a3' a4' a5' a6' a7'
                         s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 retpc) fc None m' (seg_rom rsegs))) ->
  evt rsegs Qd (MS (mkR (Z_to_bv 64 retpc) spc gp tp t0c t1c t2c s0c s1c x y z
                      a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 MEMSET) fc None mc (seg_rom rsegs)).
Proof.
  intros mc P n v x y z retpc spc s0c s1c s2c s3c s4c s5c s6c t0c t1c t2c a3c a4c a5c a6c a7c t3c t4c t5c t6c
    DD Hn0 Hn Hv Hr He Ex Ey Ez K.
  pose proof (Rw ow) as Row. pose proof (oinv_bound rsegs _ _ _ _ _ _ _ _ _ _ _ DD) as OB.
  destruct (oinv_target rsegs _ _ _ _ _ _ _ _ _ _ _ (Z.to_nat n) DD Hn) as [junk RW].
  eapply evt_cut.
  { apply (MSET (Z_to_bv 64 retpc) spc gp tp t0c t1c t2c s0c s1c x y z a3c a4c a5c a6c a7c
             s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c F fc mc junk).
    - rewrite Ex, Ez. exact RW.
    - exact (oinv_mem_inv rsegs _ _ _ _ _ _ _ _ _ _ _ DD). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              -> & MUc & WMc & MIc & RWc).
  rewrite Ex, Ez in MUc. rewrite Ex, Ey, Ez in RWc. rewrite (Z.mod_small v 256) in RWc by lia.
  rewrite (ret_pc_even retpc) by lia.
  destruct (rc_cb_rw rsegs m' _ _ _ RWc) as (HB & HL & _).
  apply K. eapply oinv_call; [exact DD | rewrite repeat_length; exact Hn | exact DF0 | exact DR0 | | exact WMc | exact MIc | exact HB].
  rewrite repeat_length, Z2Nat.id by lia. exact MUc.
Qed.

Lemma o_memcpy : forall mc P (k n : nat) (x y z : word) retpc spc s0c s1c s2c s3c s4c s5c s6c t0c t1c t2c
    a3c a4c a5c a6c a7c t3c t4c t5c t6c,
  D mc P -> (0 < n)%nat -> (length P + n <= 32)%nat -> (k + n <= 296)%nat -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
  bv_unsigned x = bv_unsigned ow + Z.of_nat (length P) -> bv_unsigned y = bv_unsigned mw + Z.of_nat k ->
  bv_unsigned z = Z.of_nat n ->
  (forall m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
     D m' (P ++ firstn n (skipn k row)) ->
     evt rsegs Qd (MS (mkR (Z_to_bv 64 retpc) spc gp tp t0' t1' t2' s0c s1c x a1' a2' a3' a4' a5' a6' a7'
                         s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 retpc) fc None m' (seg_rom rsegs))) ->
  evt rsegs Qd (MS (mkR (Z_to_bv 64 retpc) spc gp tp t0c t1c t2c s0c s1c x y z
                      a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x1d3d8) fc None mc (seg_rom rsegs)).
Proof.
  intros mc P k n x y z retpc spc s0c s1c s2c s3c s4c s5c s6c t0c t1c t2c a3c a4c a5c a6c a7c t3c t4c t5c t6c
    DD Hn0 Hn Hk Hr He Ex Ey Ez K.
  pose proof (Rw ow) as Row. pose proof (Rw mw) as Rmw. pose proof (oinv_bound rsegs _ _ _ _ _ _ _ _ _ _ _ DD) as OB.
  pose proof (oinv_row rsegs _ _ _ _ _ _ _ _ _ _ _ DD) as HR.
  pose proof (bytes_at_bound rsegs mc _ _ HR) as HRb. rewrite HLEN in HRb. change (Z.of_nat 296) with 296 in HRb.
  pose proof (rc_bytes_sub rsegs mc (bv_unsigned mw) row k n HR ltac:(lia)) as HS.
  destruct (oinv_target rsegs _ _ _ _ _ _ _ _ _ _ _ n DD Hn) as [junk RW].
  assert (LS : length (firstn n (skipn k row)) = n)
    by (rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia]).
  eapply evt_cut.
  { apply (MCPY (Z_to_bv 64 retpc) spc gp tp t0c t1c t2c s0c s1c x y z a3c a4c a5c a6c a7c
             s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c F fc mc (firstn n (skipn k row)) junk).
    - rewrite Ey. exact HS.
    - rewrite Ez, Nat2Z.id. exact LS.
    - rewrite Ex, Ez, Nat2Z.id. exact RW.
    - rewrite Ex, Ey, Ez. lia.
    - exact (oinv_mem_inv rsegs _ _ _ _ _ _ _ _ _ _ _ DD). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              -> & MUc & WMc & MIc & RWc & _).
  rewrite Ex, Ez in MUc. rewrite Ex, Ez, Nat2Z.id in RWc.
  rewrite (ret_pc_even retpc) by lia.
  destruct (rc_cb_rw rsegs m' _ _ _ RWc) as (HB & HL & _).
  apply K. eapply oinv_call; [exact DD | rewrite LS; exact Hn | exact DF0 | exact DR0 | | exact WMc | exact MIc | exact HB].
  rewrite LS. exact MUc.
Qed.

Ltac byte_of v :=
  lazymatch v with
  | Z_to_bv 64 ?z => constr:(Z_to_bv 8 z)
  | zxb ?b => b
  end.

Ltac ost k :=
  lazymatch goal with
  | DD : D ?mc ?P |- _ =>
      let HS := fresh "HS" in
      lazymatch k with
      | 0 => pose proof (oinv_okw rsegs _ _ _ _ _ _ mc _ _ _ P ow DD ltac:(cbn [length Z.of_nat]; lia)
                           ltac:(cbn [length]; lia)) as HS
      | _ => pose proof (oinv_ok rsegs _ _ _ _ _ _ mc _ _ _ P k DD ltac:(reflexivity) ltac:(cbn [length]; lia)) as HS
      end;
      step; clear HS;
      lazymatch goal with
      | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
          let b := byte_of v in
          let D' := fresh "D" in
          assert (D' : D (write_to_mem mc A (le1 v)) (P ++ [b]))
            by (apply (oinv_store rsegs _ _ _ _ _ _ mc _ _ _ P A v b DD);
                [cbn [length]; lia | exact DF0 | exact DR0
                | first [reflexivity | unfold wa; cbn [length Z.of_nat]; rewrite Z.add_0_r; symmetry;
                                       apply Z_to_bv_lit_self]
                | first [apply rc_le1_lit; lia | apply le1_zxb]]);
          cbn [app] in D'; clear DD;
          let mc' := fresh "mc" in
          set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
      end
  end.

Ltac rrow k :=
  lazymatch goal with
  | DD : D ?mc _ |- _ =>
      let HR := fresh "HR" in
      pose proof (rd_byte rsegs mc (bv_unsigned mw) row k (oinv_row rsegs _ _ _ _ _ _ _ _ _ _ _ DD)
                    ltac:(rewrite HLEN; lia)) as HR;
      let z := eval cbv in (Z.of_nat k) in change (Z.of_nat k) with z in HR
  end.

Lemma cdA : forall (j : nat) mc rac spc t0c t1c t2c s0c s1c s2c s4c s5c s6c a0c a1c a2c a3c a4c a5c a6c a7c
    t3c t4c t5c t6c,
  (0 < j <= 12)%nat ->
  evt rsegs Qd (MS (mkR rac spc gp tp t0c t1c t2c s0c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c (Z_to_bv 64 0)
                      s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x13f7c) fc None mc (seg_rom rsegs)) ->
  evt rsegs Qd (MS (mkR rac spc gp tp t0c t1c t2c s0c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c (Z_to_bv 64 (Z.of_nat j))
                      s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x13f74) fc None mc (seg_rom rsegs)).
Proof.
  induction j as [|j IH]; intros mc rac spc t0c t1c t2c s0c s1c s2c s4c s5c s6c a0c a1c a2c a3c a4c a5c a6c a7c
    t3c t4c t5c t6c Hj K; [lia|].
  step. rewrite rc_addiw_dec by lia. replace (Z.of_nat (S j) - 1) with (Z.of_nat j) by lia.
  step. rewrite rc_eqbz by lia.
  destruct (Z.eqb_spec (Z.of_nat j) 0) as [E|E]; cbn [negb].
  - replace (Z.of_nat j) with 0 by lia. exact K.
  - apply IH; [lia | exact K].
Qed.

Lemma cdB : forall (j : nat) mc rac spc t0c t1c t2c s0c s1c s2c s4c s5c s6c a0c a1c a2c a3c a4c a5c a6c a7c
    t3c t4c t5c t6c,
  (0 < j <= 12)%nat ->
  evt rsegs Qd (MS (mkR rac spc gp tp t0c t1c t2c s0c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c (Z_to_bv 64 0)
                      s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x13fb4) fc None mc (seg_rom rsegs)) ->
  evt rsegs Qd (MS (mkR rac spc gp tp t0c t1c t2c s0c s1c a0c a1c a2c a3c a4c a5c a6c a7c s2c (Z_to_bv 64 (Z.of_nat j))
                      s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x13fac) fc None mc (seg_rom rsegs)).
Proof.
  induction j as [|j IH]; intros mc rac spc t0c t1c t2c s0c s1c s2c s4c s5c s6c a0c a1c a2c a3c a4c a5c a6c a7c
    t3c t4c t5c t6c Hj K; [lia|].
  step. rewrite rc_addiw_dec by lia. replace (Z.of_nat (S j) - 1) with (Z.of_nat j) by lia.
  step. rewrite rc_eqbz by lia.
  destruct (Z.eqb_spec (Z.of_nat j) 0) as [E|E]; cbn [negb].
  - replace (Z.of_nat j) with 0 by lia. exact K.
  - apply IH; [lia | exact K].
Qed.

Lemma sumloop : forall n i mc ic oc rac t0c t1c t2c s1c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c t3c t4c t5c t6c,
  (i + n = 31)%nat -> (0 < n)%nat -> gfacts row ic oc -> D mc (gram_pre row) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0c t1c t2c ow s1c
                      (Z_to_bv 64 (psum (gram_pre row) i)) (Z_to_bv 64 (bv_unsigned ow + 31))
                      (Z_to_bv 64 (bv_unsigned ow + Z.of_nat i)) a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c
                      s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x13ffc) fc None mc (seg_rom rsegs)).
Proof.
  induction n as [|n IH]; intros i mc ic oc rac t0c t1c t2c s1c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c
    t3c t4c t5c t6c Hin Hn G DD; [lia|].
  destruct (gfacts_ok row ic oc HLEN G) as (OK & DE & LP & _).
  pose proof (Rw ow) as Row. pose proof (Rw sp) as Rsp. pose proof (oinv_bound rsegs _ _ _ _ _ _ _ _ _ _ _ DD) as OB.
  pose proof (oinv_rd rsegs _ _ _ _ _ _ _ _ _ _ _ i DD ltac:(lia)) as HR.
  step. step. step. rewrite psum_S_zxb.
  step.
  rewrite (eqb_le64 (bv_unsigned ow + Z.of_nat i + 1) (bv_unsigned ow + 31)) by lia.
  destruct n as [|n].
  - replace (bv_unsigned ow + Z.of_nat i + 1 =? bv_unsigned ow + 31) with true by (symmetry; apply Z.eqb_eq; lia).
    cbn [negb]. replace i with 30%nat in * by lia.
    step.
    pose proof (oinv_ok rsegs _ _ _ _ _ _ mc _ _ _ (gram_pre row) 31 DD ltac:(rewrite LP; reflexivity) ltac:(lia)) as HS.
    step. clear HS.
    match goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem mc ?A (le1 ?v)) _) =>
        assert (D' : D (write_to_mem mc A (le1 v)) (gram_pre row ++ [check_byte (gram_pre row)]))
          by (apply (oinv_store rsegs _ _ _ _ _ _ mc _ _ _ (gram_pre row) A v _ DD);
              [lia | exact DF0 | exact DR0 | unfold wa; rewrite LP; reflexivity | apply rc_le1_neg]);
        set (mc' := write_to_mem mc A (le1 v)) in *; clearbody mc'
    end.
    step. step.
    destruct (oinv_final rsegs _ _ _ _ _ _ _ _ _ _ _ D' ltac:(rewrite length_app, LP; reflexivity))
      as (FR & ST & MU & WM & MI & HRw & HO).
    eapply epi; [exact FR | exact ST | exact MU | exact WM | exact MI | exact HRw | exact HO
                | rewrite OK; reflexivity | rewrite OK, DE; reflexivity].
  - replace (bv_unsigned ow + Z.of_nat i + 1 =? bv_unsigned ow + 31) with false
      by (symmetry; apply Z.eqb_neq; lia).
    cbn [negb].
    replace (bv_unsigned ow + Z.of_nat i + 1) with (bv_unsigned ow + Z.of_nat (S i)) by lia.
    apply (IH (S i) mc ic oc); [lia | lia | exact G | exact DD].
Qed.

Lemma tailcp : forall mc ic oc rac t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c t3c t4c t5c t6c,
  gfacts row ic oc -> D mc (gram_head row ++ slot_bytes (box_lay row) (ic / 4) (oc / 4)) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0c t1c t2c ow mw a0c a1c a2c a3c a4c a5c a6c
                      a7c s2c s3c s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x13fe0) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c s2c s3c s4c s5c s6c t3c t4c t5c t6c G DD.
  destruct (gfacts_ok row ic oc HLEN G) as (OK & DE & LP & EP).
  pose proof (Rw ow) as Row. pose proof (Rw mw) as Rmw. pose proof (Rw sp) as Rsp.
  pose proof (oinv_bound rsegs _ _ _ _ _ _ _ _ _ _ _ DD) as OB.
  assert (LH : length (gram_head row ++ slot_bytes (box_lay row) (ic / 4) (oc / 4)) = 20%nat).
  { pose proof LP as L. rewrite EP, length_app in L. rewrite firstn_length_le in L by (rewrite length_skipn, HLEN; lia).
    lia. }
  pose proof (oinv_row rsegs _ _ _ _ _ _ _ _ _ _ _ DD) as HRw.
  pose proof (bytes_at_bound rsegs mc _ _ HRw) as HRb. rewrite HLEN in HRb. change (Z.of_nat 296) with 296 in HRb.
  step. step. step. step.
  eapply (o_memcpy mc _ 254 11); [exact DD | lia | lia | lia | lia | reflexivity
         | rewrite unsigned_lit by lia; rewrite LH; reflexivity
         | rewrite unsigned_lit by lia; reflexivity | reflexivity |].
  intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' D'.
  rewrite <- EP in D'.
  pose proof (oinv_rd rsegs _ _ _ _ _ _ _ _ _ _ _ 0 D' ltac:(lia)) as HR0.
  rewrite (wa_of_var ow (bv_unsigned ow + Z.of_nat 0)) in HR0 by (cbn [Z.of_nat]; lia).
  pose proof (psum_range (gram_pre row) 1) as PR.
  step. step. step.
  change (Z_to_bv 64 0) with (Z_to_bv 64 (psum (gram_pre row) 0)).
  step. step. step. rewrite psum_S_zxb.
  step.
  rewrite (eqb_le64 (bv_unsigned ow + 1) (bv_unsigned ow + 31)) by lia.
  replace (bv_unsigned ow + 1 =? bv_unsigned ow + 31) with false by (symmetry; apply Z.eqb_neq; lia).
  cbn [negb].
  apply (sumloop 30 1 m' ic oc); [lia | lia | exact G | exact D'].
Qed.

Lemma threes : forall mc ic oc rac t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c s3c s4c s5c s6c t3c t4c t5c t6c,
  gfacts row ic oc -> D mc (gram_head row ++ runs (box_lay row) (ic / 4) (oc / 4)) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0c t1c t2c ow mw a0c a1c a2c a3c a4c a5c a6c
                      a7c (Z_to_bv 64 (ic / 4 + oc / 4)) s3c s4c s5c s6c s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x13fb4) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c s3c s4c s5c s6c t3c t4c t5c t6c G DD.
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & _).
  pose proof (Rw ow) as Row. pose proof (Rw sp) as Rsp.
  pose proof (oinv_bound rsegs _ _ _ _ _ _ _ _ _ _ _ DD) as OB.
  step. rewrite rc_sextw by lia. step. step. rewrite rc_lts_lit by lia.
  destruct (Z.ltb_spec 11 (ic / 4 + oc / 4)) as [E12|E12].
  - apply (tailcp _ ic oc); [exact G|]. rewrite slot_runs. replace (Z.to_nat (12 - ic / 4 - oc / 4)) with 0%nat by lia.
    cbn [repeat]. rewrite app_nil_r. exact DD.
  - do 8 step.
    eapply (o_memset mc _ (12 - (ic / 4 + oc / 4)) 3);
      [exact DD | lia | rewrite length_app, head_len, runs_len by lia; lia | lia | lia | reflexivity
      | rewrite unsigned_lit by lia; rewrite length_app, head_len, runs_len by lia; lia
      | reflexivity | apply rc_zext_sub; lia |].
    intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' D'.
    apply (tailcp _ ic oc); [exact G|].
    rewrite slot_runs. replace (Z.to_nat (12 - ic / 4 - oc / 4)) with (Z.to_nat (12 - (ic / 4 + oc / 4)))
      by (f_equal; lia).
    rewrite app_assoc. exact D'.
Qed.

Lemma ef4 : forall mc ic oc rac t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c s5c s6c t3c t4c t5c t6c,
  gfacts row ic oc -> box_lay row = 1 -> D mc (gram_head row ++ repeat (Z_to_bv 8 1) (Z.to_nat (oc / 4))) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0c t1c t2c ow mw a0c a1c a2c a3c a4c a5c a6c
                      a7c (Z_to_bv 64 (oc / 4)) (Z_to_bv 64 ic) (Z_to_bv 64 (ic / 4)) s5c s6c
                      s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x13f4c) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c s5c s6c t3c t4c t5c t6c G HL DD.
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof G as (HO & HI & HOC & Ric & Roc & Mic & Moc & Hab).
  pose proof (Rw ow) as Row. pose proof (Rw sp) as Rsp.
  pose proof (oinv_bound rsegs _ _ _ _ _ _ _ _ _ _ _ DD) as OB.
  step. rewrite rc_eqbz by lia. destruct (Z.eqb_spec ic 0) as [E0|E0]; cbv iota.
  - assert (Ea : ic / 4 = 0) by (rewrite E0; reflexivity).
    replace (Z_to_bv 64 (oc / 4)) with (Z_to_bv 64 (ic / 4 + oc / 4)) by (rewrite Ea; reflexivity).
    apply (threes _ ic oc); [exact G|]. unfold runs. rewrite HL, Z.eqb_refl, Ea. cbn [Z.to_nat repeat].
    rewrite app_nil_r. exact DD.
  - do 7 step. rewrite rc_sextw by lia. rewrite rc_seqz_add by lia. step.
    eapply (o_memset mc _ (ic / 4) 0); [exact DD | lia | rewrite length_app, head_len, repeat_length; lia | lia | lia
           | reflexivity | rewrite unsigned_lit by lia; rewrite length_app, head_len, repeat_length; lia
           | reflexivity | rewrite unsigned_lit by lia; reflexivity |].
    intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' D'.
    step.
    replace (Z_to_bv 64 (ic / 4)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (ic / 4)))) by (rewrite Z2Nat.id by lia; reflexivity).
    apply cdA; [lia|].
    step.
    replace (Z_to_bv 64 (oc / 4 + ic / 4)) with (Z_to_bv 64 (ic / 4 + oc / 4)) by (f_equal; lia).
    apply (threes _ ic oc); [exact G|]. unfold runs. rewrite HL, Z.eqb_refl. rewrite <- app_assoc in D'. exact D'.
Qed.

Lemma f2c : forall mc ic oc rac t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c s3c s4c t3c t4c t5c t6c,
  gfacts row ic oc -> box_lay row <> 1 -> D mc (gram_head row ++ repeat (Z_to_bv 8 2) (Z.to_nat (ic / 4))) ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0c t1c t2c ow mw a0c a1c a2c a3c a4c a5c a6c
                      a7c (Z_to_bv 64 (ic / 4)) s3c s4c (Z_to_bv 64 (oc / 4)) (Z_to_bv 64 oc)
                      s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x13f84) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c s3c s4c t3c t4c t5c t6c G HL DD.
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof G as (HO & HI & HOC & Ric & Roc & Mic & Moc & Hab).
  pose proof (Rw ow) as Row. pose proof (Rw sp) as Rsp.
  pose proof (oinv_bound rsegs _ _ _ _ _ _ _ _ _ _ _ DD) as OB.
  assert (HL' : (box_lay row =? 1) = false) by (apply Z.eqb_neq; exact HL).
  step. rewrite rc_eqbz by lia. destruct (Z.eqb_spec oc 0) as [E0|E0]; cbv iota.
  - assert (Eb : oc / 4 = 0) by (rewrite E0; reflexivity).
    replace (Z_to_bv 64 (ic / 4)) with (Z_to_bv 64 (ic / 4 + oc / 4)) by (rewrite Eb, Z.add_0_r; reflexivity).
    apply (threes _ ic oc); [exact G|]. unfold runs. rewrite HL', Eb. cbn [Z.to_nat repeat].
    rewrite app_nil_r. exact DD.
  - do 7 step. rewrite rc_sextw by lia. rewrite rc_seqz_add by lia. step.
    eapply (o_memset mc _ (oc / 4) 1); [exact DD | lia | rewrite length_app, head_len, repeat_length; lia | lia | lia
           | reflexivity | rewrite unsigned_lit by lia; rewrite length_app, head_len, repeat_length; lia
           | reflexivity | rewrite unsigned_lit by lia; reflexivity |].
    intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' D'.
    step.
    replace (Z_to_bv 64 (oc / 4)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (oc / 4)))) by (rewrite Z2Nat.id by lia; reflexivity).
    apply cdB; [lia|].
    apply (threes _ ic oc); [exact G|]. unfold runs. rewrite HL'. rewrite <- app_assoc in D'. exact D'.
Qed.

Lemma succ : forall mc ic oc rac t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c s2c t3c t4c t5c t6c,
  gfacts row ic oc -> D mc [] ->
  evt rsegs Qd (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0c t1c t2c ow mw a0c a1c a2c a3c a4c a5c a6c
                      a7c s2c (Z_to_bv 64 ic) (Z_to_bv 64 (ic / 4)) (Z_to_bv 64 (oc / 4)) (Z_to_bv 64 oc)
                      s7 s8 s9 s10 s11 t3c t4c t5c t6c)
                  F (Z_to_bv 64 0x13ed0) fc None mc (seg_rom rsegs)).
Proof.
  intros mc ic oc rac t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c s2c t3c t4c t5c t6c G DD.
  pose proof (gfacts_bounds row ic oc G) as (B1 & B2 & B3 & B4 & B5).
  pose proof G as (HO & HI & HOC & Ric & Roc & Mic & Moc & Hab).
  pose proof (Rw ow) as Row. pose proof (Rw mw) as Rmw. pose proof (Rw sp) as Rsp.
  pose proof (oinv_bound rsegs _ _ _ _ _ _ _ _ _ _ _ DD) as OB.
  do 3 step.
  ost 0. ost 1. ost 2. ost 3.
  rrow 252%nat. step. ost 4. ost 5. ost 6.
  rrow 253%nat. step. ost 7.
  rrow 290%nat. step. step. step.
  match goal with D1 : D ?mc1 _ |- _ => change (D mc1 (gram_head row)) in D1 end.
  rewrite rc_zxb_eqb by lia.
  destruct (Z.eqb_spec (bv_unsigned (nth 290 row (Z_to_bv 8 0))) 1) as [EL|EL]; cbn [negb]; cbv iota.
  - assert (HL : box_lay row = 1) by exact EL.
    step. rewrite rc_eqbz by lia. destruct (Z.eqb_spec oc 0) as [E0|E0]; cbv iota.
    + step.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (oc / 4)) by (rewrite E0; reflexivity).
      apply (ef4 _ ic oc); [exact G | exact HL |]. replace (Z.to_nat (oc / 4)) with 0%nat by (rewrite E0; reflexivity).
      cbn [repeat]. rewrite app_nil_r. assumption.
    + do 4 step. rewrite rc_seqz_add by lia. step.
      eapply (o_memset _ (gram_head row) (oc / 4) 1); [eassumption | lia | rewrite head_len; lia | lia | lia
             | reflexivity | rewrite unsigned_lit by lia; reflexivity | reflexivity
             | rewrite unsigned_lit by lia; reflexivity |].
      intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' D'.
      step. apply (ef4 _ ic oc); [exact G | exact HL | exact D'].
  - assert (HL : box_lay row <> 1) by exact EL.
    step. rewrite rc_eqbz by lia. destruct (Z.eqb_spec ic 0) as [E0|E0]; cbv iota.
    + step.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (ic / 4)) by (rewrite E0; reflexivity).
      apply (f2c _ ic oc); [exact G | exact HL |]. replace (Z.to_nat (ic / 4)) with 0%nat by (rewrite E0; reflexivity).
      cbn [repeat]. rewrite app_nil_r. assumption.
    + do 4 step. rewrite rc_seqz_add by lia. step.
      eapply (o_memset _ (gram_head row) (ic / 4) 2); [eassumption | lia | rewrite head_len; lia | lia | lia
             | reflexivity | rewrite unsigned_lit by lia; reflexivity | reflexivity
             | rewrite unsigned_lit by lia; reflexivity |].
      intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' D'.
      step. apply (f2c _ ic oc); [exact G | exact HL | exact D'].
Qed.

Ltac fail_exit HN :=
  step; step;
  match goal with
  | FR : rw_cells _ _ (bv_unsigned sp + -64) _, ST : stk _ _ _ _, MU : munch _ _ _, WM : wmono _ _ _,
    MI : mem_inv _ _, HROW : bytes_at _ _ (bv_unsigned mw) _, HO : rw_cells _ _ (bv_unsigned ow) _ |- _ =>
      eapply epi; [exact FR | exact ST | exact MU | exact WM | exact MI | exact HROW | exact HO
                  | rewrite (dok_false row ltac:(assumption) HN); reflexivity
                  | rewrite (dok_false row ltac:(assumption) HN); reflexivity]
  end.

Lemma run : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  stk rsegs m0 lo (bv_unsigned sp) -> bytes_at rsegs m0 (bv_unsigned mw) row ->
  rw_cells rsegs m0 (bv_unsigned ow) [CB 32 ob] -> mem_inv rsegs m0 ->
  evt rsegs Qd (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 mw ow a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                      t3 t4 t5 t6)
                  F (Z_to_bv 64 DECLARATION_OF) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST HROW HO MI.
  unfold DECLARATION_OF.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (bv_unsigned ow, bv_unsigned ow + 32)] m0) as MU.
  pose proof (wmono_refl rsegs m0) as WM.
  pose proof (Rw sp) as Rsp. pose proof (Rw mw) as Ra0. pose proof (Rw ow) as Ra1.
  pose proof (bytes_at_bound rsegs m0 _ _ HROW) as HRb. rewrite HLEN in HRb. change (Z.of_nat 296) with 296 in HRb.
  pose proof (rw_cells_bound rsegs m0 _ _ HO) as HOb. cbn [cells_size csize Nat.add] in HOb.
  change (Z.of_nat 32) with 32 in HOb.
  carve_frame 64%nat ST.
  do 10 step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (D0 : D mm []) by (eapply oinv_init; [exact FR | exact ST | exact MU | exact WM | exact MI | exact HROW
                                                 | exact HO]);
    pose proof (rd_byte rsegs mm (bv_unsigned mw) row 288 HROW ltac:(lia)) as R288;
    pose proof (rc_rd4 rsegs mm (bv_unsigned mw) row 16 HROW ltac:(lia)) as R16;
    pose proof (rc_rd4 rsegs mm (bv_unsigned mw) row 20 HROW ltac:(lia)) as R20
  end.
  change (Z.of_nat 288) with 288 in R288. change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 20) with 20 in R20.
  pose proof (rc_u32le_range row 16) as U16. pose proof (rc_u32le_range row 20) as U20.
  pose proof (rc_s32_range _ U16) as S16.
  step. step. step.
  rewrite rc_zxb_eqb by lia.
  destruct (Z.eqb_spec (bv_unsigned (nth 288 row (Z_to_bv 8 0))) 0) as [EO|EO]; cbv iota.
  - step. step. step. step.
    eapply (o_memcpy _ [] 24 32); [exact D0 | lia | cbn [length]; lia | lia | lia | reflexivity
      | cbn [length Z.of_nat]; lia | rewrite unsigned_lit by lia; reflexivity | reflexivity |].
    intros m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' D'.
    step.
    destruct (oinv_final rsegs _ _ _ _ _ _ _ _ _ _ _ D'
                ltac:(cbn [app]; rewrite firstn_length_le; [reflexivity | rewrite length_skipn, HLEN; lia]))
      as (FR' & ST' & MU' & WM' & MI' & HR' & HO').
    eapply epi; [exact FR' | exact ST' | exact MU' | exact WM' | exact MI' | exact HR' | exact HO' | |].
    + unfold decl_ok, box_org, rval, rbyte. rewrite EO. reflexivity.
    + unfold decl_ok, decl, box_org, rval, rbyte, box_cfg. rewrite EO. reflexivity.
  - step. rewrite (rc_sx32 (u32le row 16) U16).
    step. rewrite rc_lts0 by lia.
    destruct (Z.ltb_spec (s32 (u32le row 16)) 0) as [EI|EI]; cbv iota.
    + assert (HN : ~ (0 <= box_ic row /\ 0 <= box_oc row /\ box_ic row mod 4 = 0 /\ box_oc row mod 4 = 0 /\
                      box_ic row / 4 + box_oc row / 4 <= 12)) by (intros (H1 & _); unfold box_ic in H1; lia).
      fail_exit HN.
    + step. rewrite (rc_zx32 (u32le row 20) U20). do 6 step. step.
      rewrite rc_okmask by lia.
      destruct ((Z.land (u32le row 20) 18446744071562067971 =? 0) && (s32 (u32le row 16) mod 4 =? 0)) eqn:EM;
        cbn [negb]; cbv iota.
      * apply andb_prop in EM as [EM1 EM2]. apply Z.eqb_eq in EM1, EM2.
        apply rc_mask_zero in EM1 as [Hu Hm].
        assert (S32o : s32 (u32le row 20) = u32le row 20)
          by (unfold s32; rewrite (proj2 (Z.ltb_lt _ _) Hu); reflexivity).
        do 5 step. rewrite (rc_srli2 (u32le row 20)) by lia. rewrite (rc_srliw2 (s32 (u32le row 16))) by lia.
        assert (B4 : 0 <= u32le row 20 / 4 < 2^30) by (Z.div_mod_to_equations; lia).
        assert (B5 : 0 <= s32 (u32le row 16) / 4 < 2^30) by (Z.div_mod_to_equations; lia).
        rewrite rc_ltu_lit by lia.
        destruct (Z.ltb_spec 12 (u32le row 20 / 4 + s32 (u32le row 16) / 4)) as [E12|E12]; cbn [negb]; cbv iota.
        -- assert (HN : ~ (0 <= box_ic row /\ 0 <= box_oc row /\ box_ic row mod 4 = 0 /\ box_oc row mod 4 = 0 /\
                           box_ic row / 4 + box_oc row / 4 <= 12))
             by (intros (H1 & H2 & H3 & H4 & H5); unfold box_ic, box_oc in *; rewrite S32o in H5; lia).
           fail_exit HN.
        -- eapply (succ _ (s32 (u32le row 16)) (u32le row 20)); [|exact D0].
           split; [exact EO|]. split; [reflexivity|]. split; [unfold box_oc; exact S32o|].
           split; [lia|]. split; [lia|]. split; [exact EM2|]. split; [exact Hm|]. lia.
      * assert (HN : ~ (0 <= box_ic row /\ 0 <= box_oc row /\ box_ic row mod 4 = 0 /\ box_oc row mod 4 = 0 /\
                        box_ic row / 4 + box_oc row / 4 <= 12)).
        { intros (H1 & H2 & H3 & H4 & H5).
          assert (Hu : u32le row 20 < 2^31)
            by (revert H2; unfold box_oc, s32; destruct (Z.ltb_spec (u32le row 20) (2^31)); intros; lia).
          assert (S32o : s32 (u32le row 20) = u32le row 20)
            by (unfold s32; rewrite (proj2 (Z.ltb_lt _ _) Hu); reflexivity).
          unfold box_oc in H4. rewrite S32o in H4.
          pose proof (proj2 (rc_mask_zero row 20) (conj Hu H4)) as L.
          unfold box_ic in H3. rewrite L, H3 in EM. cbn in EM. discriminate EM. }
        fail_exit HN.
Qed.

End Plain.

Theorem declaration_of_holds : memset_contract -> memcpy_contract -> declaration_of_contract.
Proof.
  intros MSET MCPY. unfold declaration_of_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo row ob
    ST LO HM8 HLEN HROW HO DMO DMS DOS MI.
  unfold DECLARATION_OF_FRAME in *.
  eapply run; eassumption.
Qed.

Ltac rowtac :=
  lazymatch goal with
  | |- exists row, image_bytes ?segs ?A ?n = Some row /\ _ =>
      let r := eval vm_compute in (image_bytes segs A n) in
      lazymatch r with
      | Some ?l => exists l; split; [vm_compute; reflexivity | split; vm_compute; reflexivity]
      end
  end.

Theorem declaration_of_rows_holds : declaration_of_rows.
Proof.
  unfold declaration_of_rows, BOX_CATALOGUE. intros i Hi.
  do 11 (destruct i as [|i]; [rowtac|]). lia.
Qed.
