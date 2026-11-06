From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import ReacDecodeLib
  reac_upstream_channels_c reac_upstream_decode.
Import ListNotations.
Open Scope Z_scope.

Lemma magic_bytes : forall m, mem_inv rsegs m ->
  bytes_at rsegs m 0x103a0 (le8 (Z_to_bv 64 0xe38e38e38e38e38f)).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | rewrite length_le8; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma geomv : forall x q, 0 <= x < 2^64 -> 0 <= q < 2^21 -> 0 <= x - q * 36 < 36 ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) - q * 36)))
    + -1))) (bv_unsigned (Z_to_bv 64 q)) = if x - q * 36 =? 0 then q else 0.
Proof.
  intros x q Hx Hq Hr. rewrite (unsigned_lit x) by lia. rewrite (unsigned_lit q) by lia.
  unfold v_sltu, c_ltu. rewrite ltu_lit by lia.
  destruct (Z.eqb_spec (x - q * 36) 0) as [E|E].
  - rewrite E. cbn [Z.ltb Z.compare]. change (bv_unsigned (Z_to_bv 64 0) + -1) with (-1).
    rewrite unsigned_lit_wrap. change (-1 mod 2^64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    apply Z.mod_small. lia.
  - rewrite (proj2 (Z.ltb_lt 0 (x - q * 36))) by lia. change (bv_unsigned (Z_to_bv 64 1) + -1) with 0.
    rewrite (unsigned_lit 0) by lia. apply Z.land_0_l.
Qed.

Lemma up_expect : forall q, 0 <= q < 2^21 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned
    (v_sltiu (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 q) + -2))) 39)) (bv_unsigned (v_sltiu (Z_to_bv 64
    (Z.land (bv_unsigned (Z_to_bv 64 q)) 1)) 1)) + -1))) (bv_unsigned (Z_to_bv 64 q)))) + 0))
  = Z_to_bv 64 (if (2 <=? q) && (q <=? 40) && (q mod 2 =? 0) then q else -1).
Proof.
  intros q Hq. rewrite (unsigned_lit q) by lia. rewrite (swrap32_id (q + -2)) by lia. rewrite land1.
  pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as Hm.
  unfold v_sltiu. change (bv_wrap 64 39) with 39. change (bv_wrap 64 1) with 1.
  rewrite (unsigned_lit (q mod 2)) by lia. rewrite (unsigned_lit_wrap (q + -2)).
  assert (A : ((q + -2) mod 2^64 <? 39) = (2 <=? q) && (q <=? 40)).
  { destruct (Z_lt_le_dec q 2).
    - rewrite <- (Z.mod_add (q + -2) 1) by lia. rewrite Z.mod_small by lia.
      destruct (Z.ltb_spec (q + -2 + 1 * 2^64) 39); destruct (Z.leb_spec 2 q); cbn; lia.
    - rewrite Z.mod_small by lia.
      destruct (Z.ltb_spec (q + -2) 39); destruct (Z.leb_spec 2 q); destruct (Z.leb_spec q 40); cbn; lia. }
  assert (B : (q mod 2 <? 1) = (q mod 2 =? 0)).
  { destruct (Z.ltb_spec (q mod 2) 1); destruct (Z.eqb_spec (q mod 2) 0); lia. }
  rewrite A, B.
  destruct ((2 <=? q) && (q <=? 40)); destruct (q mod 2 =? 0); cbn [andb].
  - change (bv_unsigned (Z_to_bv 64 1)) with 1. change (Z.land 1 1 + -1) with 0.
    change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.lor_0_l. rewrite (unsigned_lit q) by lia.
    rewrite Z.add_0_r, (swrap32_id q) by lia. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    change (Z.land 1 0 + -1) with (-1). change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64).
    rewrite Z.lor_comm, Z.lor_ones_low by (first [ lia | destruct (Z.eq_dec q 0) as [Z0|Z0]; [rewrite Z0; cbn; lia | apply Z.log2_lt_pow2; lia] ]).
    vm_compute. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    change (Z.land 0 1 + -1) with (-1). change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64).
    rewrite Z.lor_comm, Z.lor_ones_low by (first [ lia | destruct (Z.eq_dec q 0) as [Z0|Z0]; [rewrite Z0; cbn; lia | apply Z.log2_lt_pow2; lia] ]).
    vm_compute. reflexivity.
  - change (bv_unsigned (Z_to_bv 64 0)) with 0.
    change (Z.land 0 0 + -1) with (-1). change (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64).
    rewrite Z.lor_comm, Z.lor_ones_low by (first [ lia | destruct (Z.eq_dec q 0) as [Z0|Z0]; [rewrite Z0; cbn; lia | apply Z.log2_lt_pow2; lia] ]).
    vm_compute. reflexivity.
Qed.

Lemma upstream_result_q : forall len, 52 <= len < 2^26 -> (len - 52) mod 36 = 0 ->
  upstream_result len = (if (2 <=? (len - 52) / 36) && ((len - 52) / 36 <=? 40) && (((len - 52) / 36) mod 2 =? 0)
    then (len - 52) / 36 else -1).
Proof.
  intros len H1 H2. unfold upstream_result, upstream_ok, upstream_width.
  assert (Q : 0 <= (len - 52) / 36 < 2^21) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (Z.mod_small ((len - 52) / 36)) by lia.
  rewrite (proj2 (Z.leb_le 52 len)) by lia. rewrite (proj2 (Z.eqb_eq _ _) H2). cbn [andb].
  assert (EV : Z.even ((len - 52) / 36) = (((len - 52) / 36) mod 2 =? 0)).
  { destruct (Z.Even_or_Odd ((len - 52) / 36)) as [[k E]|[k E]].
    - rewrite (proj2 (Z.even_spec _)) by (exists k; exact E). symmetry. apply Z.eqb_eq. rewrite E.
      Z.div_mod_to_equations. lia.
    - assert (Z.even ((len - 52) / 36) = false)
        by (rewrite <- Z.negb_odd; rewrite (proj2 (Z.odd_spec _)) by (exists k; exact E); reflexivity).
      rewrite H. symmetry. apply Z.eqb_neq. rewrite E. Z.div_mod_to_equations. lia. }
  rewrite EV.
  destruct (2 <=? (len - 52) / 36), ((len - 52) / 36 <=? 40), (((len - 52) / 36) mod 2 =? 0); reflexivity.
Qed.

Lemma upstream_result_bad : forall len, ~ (52 <= len /\ (len - 52) mod 36 = 0) -> upstream_result len = -1.
Proof.
  intros len H. unfold upstream_result, upstream_ok.
  destruct (Z.leb_spec 52 len); destruct (Z.eqb_spec ((len - 52) mod 36) 0); cbn [andb]; try reflexivity; tauto.
Qed.

Definition up_olen (len : Z) : Z := if 0 <? upstream_result len then 36 * upstream_result len else 1.

Lemma upstream_result_range : forall len, 0 <= len < 2^26 -> -1 <= upstream_result len <= 40.
Proof.
  intros len H. unfold upstream_result, upstream_ok.
  destruct ((52 <=? len) && ((len - 52) mod 36 =? 0) && Z.even (upstream_width len) && (2 <=? upstream_width len)
    && (upstream_width len <=? 40)) eqn:E; [|lia].
  rewrite !andb_true_iff, !Z.leb_le in E. lia.
Qed.

Section UA.
Context (IUC : reac_upstream_channels_contract).
Variables (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
  x30 x31 sp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (len : Z).
Hypothesis HLB : 0 <= len < 2^26.
Hypothesis MI : mem_inv rsegs m.

Ltac closed_cond :=
  lazymatch goal with |- context [negb (bv_eqb ?a ?b)] =>
    let c := eval vm_compute in (negb (bv_eqb a b)) in change (negb (bv_eqb a b)) with c end.

Lemma seg_UA :
  (forall (y11 y12 y13 : word),
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x13328) sp x3 x4 x5 x6 x7 (Z_to_bv 64 len) x9 (Z_to_bv 64 (up_olen len)) y11
       y12 y13 x14 x15 x16 x17 x18 (Z_to_bv 64 (upstream_result len)) x20 (Z_to_bv 64 (up_olen len)) x22 x23 x24
       x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x14df4) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 sp x3 x4 x5 x6 x7 (Z_to_bv 64 len) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
     x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13298) fc None m (seg_rom rsegs)).
Proof.
  intros CONT.
  pose proof (magic_bytes m MI) as HMG.
  pose proof (rd_all _ _ _ HMG) as HRM. rewrite length_le8 in HRM.
  pose proof (upstream_result_range len HLB) as UR.
  step. step.
  eapply evt_cut; [eapply (IUC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m) |].
  { exact HMG. }
  intros ms' (a1' & a2' & a3' & ->).
  replace (ret_pc (Z_to_bv 64 0x132a0)) with (Z_to_bv 64 0x132a0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit len) by lia.
  step. step. step.
  rewrite ltu_lit by lia.
  assert (TAIL : forall y10 y11 y12 : word, evt rsegs Q (MS (mkR (Z_to_bv 64 0x132a0) sp x3 x4 x5 x6 x7
       (Z_to_bv 64 len) x9 y10 y11 y12 a3' x14 x15 x16 x17 x18 (Z_to_bv 64 (upstream_result len)) x20 x21
       x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13304) fc None m (seg_rom rsegs))).
  { intros y10 y11 y12. step. rewrite lts0_lit by lia. unfold up_olen in CONT.
    destruct (Z.ltb_spec 0 (upstream_result len)) as [P|P]; cbn [negb].
    - step. step. step. step. rewrite (unsigned_lit (upstream_result len)) by lia.
      rewrite (unsigned_lit (upstream_result len * 36)) by lia.
      step. step.
      replace (Z.lor (upstream_result len * 36) (bv_unsigned (v_sltiu (Z_to_bv 64 (upstream_result len * 36)) 1)))
        with (36 * upstream_result len).
      2:{ unfold v_sltiu. rewrite unsigned_lit by lia. change (bv_wrap 64 1) with 1.
          rewrite (proj2 (Z.ltb_ge _ 1)) by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.lor_0_r. lia. }
      apply CONT.
    - step. step. step. step. apply CONT. }
  destruct (Z.ltb_spec len 52) as [L52|L52].
  - step. do 9 step.
    replace (upstream_result len) with (-1) in * by (symmetry; apply upstream_result_bad; lia).
    closed_cond. apply TAIL.
  - do 4 step.
    rewrite (unsigned_lit (len + -52)) by lia.
    step.
    rewrite (unsigned_lit (Z.shiftr _ 64)) by (rewrite Z.shiftr_div_pow2 by lia; split;
      [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia]).
    rewrite div36 by lia.
    assert (QB : 0 <= (len + -52) / 36 < 2^21) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    set (q := (len + -52) / 36) in *.
    step. step. step.
    rewrite (unsigned_lit q) by lia. rewrite (unsigned_lit (q * 36)) by lia.
    step. step. step.
    rewrite geomv by (subst q; Z.div_mod_to_equations; lia).
    destruct (Z.eqb_spec (len + -52 - q * 36) 0) as [R0|R0].
    + do 10 step.
      rewrite up_expect by lia.
      replace (if (2 <=? q) && (q <=? 40) && (q mod 2 =? 0) then q else -1) with (upstream_result len).
      2:{ subst q. replace (len + -52) with (len - 52) by lia. apply upstream_result_q; [lia|].
          replace (len - 52) with (len + -52) by lia. Z.div_mod_to_equations; lia. }
      rewrite bv_eqb_refl. cbn [negb]. apply TAIL.
    + do 10 step.
      replace (upstream_result len) with (-1) in * by (symmetry; apply upstream_result_bad;
        intros (_ & RM); apply R0; subst q; replace (len + -52) with (len - 52) by lia; Z.div_mod_to_equations; lia).
      closed_cond. apply TAIL.
Qed.

End UA.
