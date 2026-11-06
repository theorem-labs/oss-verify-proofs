From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import put_utf8_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma lor_add : forall x c k, 0 <= k -> 0 <= x < 2^k -> Z.land c (2^k - 1) = 0 -> Z.lor x c = x + c.
Proof.
  intros x c k Hk Hx Hc.
  assert (Hm : Z.land x (2^k - 1) = x) by (rewrite zb_land_mask by lia; apply Z.mod_small; lia).
  assert (H0 : Z.land x c = 0).
  { rewrite <- Hm, <- Z.land_assoc, (Z.land_comm (2^k - 1) c), Hc, Z.land_0_r. reflexivity. }
  rewrite <- Z.lxor_lor by exact H0. rewrite <- Z.add_nocarry_lxor by exact H0. reflexivity.
Qed.

Lemma lor192 : forall x, 0 <= x < 64 -> Z.lor x 192 = x + 192.
Proof. intros x H. apply (lor_add x 192 6); [lia | exact H | reflexivity]. Qed.
Lemma lor224 : forall x, 0 <= x < 32 -> Z.lor x 224 = x + 224.
Proof. intros x H. apply (lor_add x 224 5); [lia | exact H | reflexivity]. Qed.
Lemma lor240 : forall x, 0 <= x < 16 -> Z.lor x 240 = x + 240.
Proof. intros x H. apply (lor_add x 240 4); [lia | exact H | reflexivity]. Qed.
Lemma land63 : forall x, Z.land x 63 = x mod 64.
Proof. intros x. apply (zb_land_mask x 6). lia. Qed.

Lemma srliw16 : forall cp, 0 <= cp < 2^21 ->
  bv_eqb (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 cp))) 16))) (Z_to_bv 64 0)
  = (cp <? 0x10000).
Proof.
  intros cp H.
  rewrite unsigned_lit by lia.
  rewrite bv_wrap_small by (change (bv_modulus 32) with (2^32); lia).
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); Z.div_mod_to_equations; lia).
  unfold bv_eqb. rewrite !unsigned_lit by (Z.div_mod_to_equations; lia).
  destruct (Z.ltb_spec cp 0x10000); [apply Z.eqb_eq | apply Z.eqb_neq]; Z.div_mod_to_equations; lia.
Qed.

Lemma wtm_app : forall bs bs2 m o k, k = Z.of_nat (length bs) ->
  write_to_mem (write_to_mem m (wa o) bs) (wa (o + k)) bs2 = write_to_mem m (wa o) (bs ++ bs2).
Proof.
  induction bs as [|x bs IH]; intros bs2 m o k ->.
  - cbn [length Z.of_nat app write_to_mem]. rewrite Z.add_0_r. reflexivity.
  - cbn [length app write_to_mem]. rewrite !wa_succ.
    rewrite <- (IH bs2 _ (o + 1) (Z.of_nat (length bs)) eq_refl). do 2 f_equal. lia.
Qed.

Lemma fin : forall m o bs, 0 <= o -> o + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs (write_to_mem m (wa o) bs) o bs /\
  munch [(o, o + Z.of_nat (length bs))] m (write_to_mem m (wa o) bs) /\
  wmono rsegs m (write_to_mem m (wa o) bs).
Proof.
  intros m o bs H1 H2. split; [apply bytes_at_write_same; lia|]. split.
  - apply munch_write; [apply munch_refl | lia | lia | cbn; left; lia].
  - apply wmono_write, wmono_refl.
Qed.

Lemma utf8_1 : forall cp, cp < 0x80 -> utf8 cp = [Z_to_bv 8 cp].
Proof. intros cp H. unfold utf8. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma utf8_2 : forall cp, 0x80 <= cp -> cp < 0x800 ->
  utf8 cp = [Z_to_bv 8 (0xC0 + cp / 64); Z_to_bv 8 (0x80 + cp mod 64)].
Proof.
  intros cp H1 H2. unfold utf8. rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H2). reflexivity.
Qed.
Lemma utf8_3 : forall cp, 0x800 <= cp -> cp < 0x10000 ->
  utf8 cp = [Z_to_bv 8 (0xE0 + cp / 4096); Z_to_bv 8 (0x80 + (cp / 64) mod 64); Z_to_bv 8 (0x80 + cp mod 64)].
Proof.
  intros cp H1 H2. unfold utf8.
  rewrite (proj2 (Z.ltb_ge cp 0x80) ltac:(lia)), (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H2).
  reflexivity.
Qed.
Lemma utf8_4 : forall cp, 0x10000 <= cp ->
  utf8 cp = [Z_to_bv 8 (0xF0 + cp / 262144); Z_to_bv 8 (0x80 + (cp / 4096) mod 64);
             Z_to_bv 8 (0x80 + (cp / 64) mod 64); Z_to_bv 8 (0x80 + cp mod 64)].
Proof.
  intros cp H. unfold utf8.
  rewrite (proj2 (Z.ltb_ge cp 0x80) ltac:(lia)), (proj2 (Z.ltb_ge cp 0x800) ltac:(lia)), (proj2 (Z.ltb_ge _ _) H).
  reflexivity.
Qed.

Ltac hs o W k :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?M _) =>
    let H := fresh "HS" in
    assert (H : store_ok rsegs M (wa (o + k)) 1 = true)
      by (eapply wr_at_store_ok; [repeat apply wr_at_write; exact W | lia | cbn [length]; lia])
  end.

Ltac byte_arith :=
  apply Z_to_bv8_mod;
  repeat first
    [ rewrite unsigned_lit_wrap
    | rewrite Z.shiftr_div_pow2 by lia
    | rewrite Z.shiftl_mul_pow2 by lia
    | rewrite land63 ];
  repeat first
    [ rewrite lor192 by (Z.div_mod_to_equations; lia)
    | rewrite lor224 by (Z.div_mod_to_equations; lia)
    | rewrite lor240 by (Z.div_mod_to_equations; lia) ];
  Z.div_mod_to_equations; lia.

Ltac bytes_eq :=
  lazymatch goal with
  | |- [] = [] => reflexivity
  | |- _ :: _ = _ :: _ => apply (f_equal2 (@cons byte)); [byte_arith | bytes_eq]
  end.

Ltac finish L :=
  lazymatch goal with |- context [wa (?o + 0)] => replace (wa (o + 0)) with (wa o) by (f_equal; lia) end;
  rewrite ?wtm_app by reflexivity;
  lazymatch type of L with
  | _ = ?B =>
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
      replace bs with B by (unfold le1; cbn [Z_to_le_bytes app]; bytes_eq)
    end
  end;
  apply evt_done; do 14 eexists; eexists; split; [reflexivity|];
  apply fin; cbn [length]; lia.

Theorem put_utf8_holds : put_utf8_contract.
Proof.
  unfold put_utf8_contract, PUT_UTF8.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m o cp
    E0 E1 Ho W Hcp.
  subst a0 a1.
  assert (U1 : bv_unsigned (Z_to_bv 64 cp) = cp) by (apply unsigned_lit; lia).
  step. step.
  destruct (Z.ltb_spec cp 0x80) as [C1|C1].
  - pose proof (utf8_1 cp C1) as L. rewrite L in W |- *. cbn [length] in W |- *.
    pose proof W as (Wo & Wn & _).
    if_false.
    hs o W 0. step. step. step.
    finish L.
  - if_true. step. step.
    destruct (Z.ltb_spec cp 0x800) as [C2|C2].
    + pose proof (utf8_2 cp C1 C2) as L. rewrite L in W |- *. cbn [length] in W |- *.
      pose proof W as (Wo & Wn & _).
      if_false.
      do 4 step.
      hs o W 0. step. hs o W 1. step. step. step.
      finish L.
    + if_true. step. step.
      rewrite srliw16 by lia.
      destruct (Z.ltb_spec cp 0x10000) as [C3|C3].
      * pose proof (utf8_3 cp C2 C3) as L. rewrite L in W |- *. cbn [length] in W |- *.
        pose proof W as (Wo & Wn & _).
        if_false.
        do 7 step.
        hs o W 0. step. hs o W 1. step. hs o W 2. step. step. step.
        finish L.
      * pose proof (utf8_4 cp C3) as L. rewrite L in W |- *. cbn [length] in W |- *.
        pose proof W as (Wo & Wn & _).
        if_true.
        do 10 step.
        hs o W 0. step. hs o W 1. step. hs o W 2. step. hs o W 3. step. step. step.
        finish L.
Qed.
