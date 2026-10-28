(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BZBridge BacX BSFModel BSysStep BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsWalk BakeStackRep B5_tls B5_smkit RtB_Iface.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section MTS2.
  Context {HCEIL : HeapCeil}.
  Lemma mts2_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (p : Z),
    mem_inv asegs m -> a0 = Z_to_bv 64 p ->
    ((0 <= p /\ p + 8 <= ALOWSH_LO) \/ (AHI_LO <= p /\ p + 8 <= AAPP_HI)) ->
    rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
    rw_cells asegs m AGOT_MIDBEG [C8 (wz AMIDBEG_CELL)] -> rw_cells asegs m AGOT_MIDEND [C8 (wz AMIDEND_CELL)] ->
    rw_cells asegs m AGOT_HIEND [C8 (wz AHIEND_CELL)] ->
    rw_cells asegs m AHIEND_CELL [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)] ->
    evt asegs (mts_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xbb924) fc None m (seg_rom asegs)).
  Proof.
    intros until p. intros MI Ha0 PP G1 C1 G2 G3 G4 C4. subst a0.
    unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_MIDBEG, AMIDBEG_CELL, AGOT_MIDEND, AMIDEND_CELL, AGOT_HIEND, AHIEND_CELL, AHI_LO, AAPP_HI, ALOWSH_LO, wz in *.
    rewrite ASHADOW_BASE_val in *.
    do 7 zstep.
    replace (Z.land (Z.land (Z.b2z (2147450880 <? 2147450879) + -1) 18446744073709551615) 2147450879)
      with 2147450879 by reflexivity.
    zstep. if_cases K1; zify_cond K1.
    { zstep. zstep. rewrite Z.add_comm, sh_shiftr by lia. zstep. unfold mts_post. finish. }
    destruct PP as [PP|PP]; [exfalso; lia|]. destruct PP as [P0 P1].
    do 7 zstep.
    replace (0 + -1) with (-1) by reflexivity.
    zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
    do 5 zstep.
    change (Z.shiftr (2^47 - 1) 3 + 2147450880) with 17594333495295.
    zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
    zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
    zstep. zstep. rewrite Z.add_comm, sh_shiftr by lia. zstep. unfold mts_post. finish.
  Qed.
End MTS2.

Lemma pb_app : forall a b v, poison_bytes (a + b) v = poison_bytes a v ++ poison_bytes b v.
Proof. intros. unfold poison_bytes. apply repeat_app. Qed.
Lemma pb_length : forall a v, length (poison_bytes a v) = a.
Proof. intros. unfold poison_bytes. apply repeat_length. Qed.

Definition ccp (x : Z) : list byte := if Z.eqb (x mod 8) 0 then [] else [b8 (x mod 8)].
Lemma ccp_length : forall x, Z.of_nat (length (ccp x)) = nsh x - x / 8.
Proof. intros x. unfold ccp, nsh. destruct (Z.eqb_spec (x mod 8) 0) as [E|E]; cbn [length]; Z.div_mod_to_equations; lia. Qed.

Lemma cc_gen_eq : forall len x, cc_gen len x = poison_bytes (Z.to_nat (x / 8)) 0 ++ ccp x ++ poison_bytes (Z.to_nat (nsh len - nsh x)) 0xfc.
Proof. intros. unfold cc_gen, shadow_of, ccp, poison_bytes. rewrite app_assoc. reflexivity. Qed.

Lemma firstn_repeat_ : forall (A : Type) (x : A) k a, firstn k (repeat x a) = repeat x (Nat.min k a).
Proof. induction k as [|k IH]; intros [|a]; cbn; try reflexivity. f_equal. apply IH. Qed.
Lemma skipn_repeat_ : forall (A : Type) (x : A) k a, skipn k (repeat x a) = repeat x (a - k).
Proof. induction k as [|k IH]; intros [|a]; cbn; try reflexivity. apply IH. Qed.

Lemma firstn_pb_app : forall k a v (l : list byte), (k <= a)%nat -> firstn k (poison_bytes a v ++ l) = poison_bytes k v.
Proof.
  intros k a v l H. rewrite firstn_app. rewrite pb_length.
  replace (k - a)%nat with O by lia. rewrite firstn_O, app_nil_r.
  unfold poison_bytes. rewrite firstn_repeat_. f_equal. lia.
Qed.

Lemma cc_gen_firstn : forall len x k, 0 <= x -> (k <= Z.to_nat (x / 8))%nat -> firstn k (cc_gen len x) = poison_bytes k 0.
Proof. intros len x k Hx Hk. rewrite cc_gen_eq. apply firstn_pb_app. exact Hk. Qed.

Lemma nsh_nonneg : forall x, 0 <= x -> 0 <= nsh x.
Proof. intros x H. unfold nsh. apply Z.div_pos; lia. Qed.
Lemma nsh_mono : forall x y, x <= y -> nsh x <= nsh y.
Proof. intros x y H. unfold nsh. apply Z.div_le_mono; lia. Qed.
Lemma nsh_bounds : forall x, x / 8 <= nsh x <= x / 8 + 1 /\ (x mod 8 = 0 -> nsh x = x / 8) /\ (x mod 8 <> 0 -> nsh x = x / 8 + 1).
Proof. intros x. unfold nsh. Z.div_mod_to_equations. split; [lia|]. split; intros; lia. Qed.

Lemma cc_gen_skipn : forall len x k, 0 <= x <= len -> nsh x <= Z.of_nat k <= nsh len ->
  skipn k (cc_gen len x) = poison_bytes (Z.to_nat (nsh len) - k) 0xfc.
Proof.
  intros len x k Hx Hk. rewrite cc_gen_eq, app_assoc.
  assert (LP : length (poison_bytes (Z.to_nat (x / 8)) 0 ++ ccp x) = Z.to_nat (nsh x)).
  { rewrite length_app, pb_length. pose proof (ccp_length x) as C. assert (0 <= x / 8) by (apply Z.div_pos; lia). lia. }
  rewrite skipn_app, (skipn_all2 (poison_bytes (Z.to_nat (x / 8)) 0 ++ ccp x)) by lia. rewrite LP. cbn [app].
  unfold poison_bytes. rewrite skipn_repeat_. f_equal.
  pose proof (nsh_nonneg x (proj1 Hx)). pose proof (nsh_mono x len (proj2 Hx)). lia.
Qed.

Lemma cc_gen_len : forall len x, 0 <= x <= len -> length (cc_gen len x) = Z.to_nat (nsh len).
Proof. intros len x H. pose proof (cc_gen_length len x H). lia. Qed.

Lemma cc_gen_last : forall len x, 0 <= x <= len -> len mod 8 <> 0 ->
  skipn (Z.to_nat (len / 8)) (cc_gen len x) = [if 8 * (len / 8) <? x then b8 (x mod 8) else b8 0xfc].
Proof.
  intros len x Hx L8. pose proof (nsh_bounds len) as (NB1 & _ & NB3). specialize (NB3 L8).
  destruct (Z.ltb_spec (8 * (len / 8)) x) as [LT|GE].
  -
    assert (XD : x / 8 = len / 8) by (Z.div_mod_to_equations; lia).
    assert (XM : x mod 8 <> 0) by (Z.div_mod_to_equations; lia).
    rewrite cc_gen_eq. unfold ccp. destruct (Z.eqb_spec (x mod 8) 0) as [E|_]; [contradiction|].
    rewrite skipn_app, pb_length, XD, skipn_all2 by (rewrite pb_length; lia). cbn [app].
    replace (Z.to_nat (len / 8) - Z.to_nat (len / 8))%nat with O by lia. cbn [skipn].
    pose proof (nsh_bounds x) as (_ & _ & NX). rewrite (NX XM), XD, NB3. replace (len / 8 + 1 - (len / 8 + 1)) with 0 by lia.
    reflexivity.
  - rewrite cc_gen_skipn.
    + rewrite NB3. replace (Z.to_nat (len / 8 + 1) - Z.to_nat (len / 8))%nat with 1%nat by (assert (0 <= len / 8) by (apply Z.div_pos; lia); lia).
      reflexivity.
    + exact Hx.
    + pose proof (nsh_bounds x) as (NXB & NX0 & NX1). assert (0 <= len / 8) by (apply Z.div_pos; lia).
      split; [| lia]. destruct (Z.eq_dec (x mod 8) 0) as [E|E]; [rewrite (NX0 E) | rewrite (NX1 E)]; Z.div_mod_to_equations; lia.
Qed.

Lemma cb_split3 : forall m a N (l : list byte) k1 k2,
  rw_cells asegs m a [CB N l] -> (k1 + k2 <= N)%nat ->
  rw_cells asegs m a [CB k1 (firstn k1 l)] /\ rw_cells asegs m (a + Z.of_nat k1) [CB k2 (firstn k2 (skipn k1 l))]
  /\ rw_cells asegs m (a + Z.of_nat k1 + Z.of_nat k2) [CB (N - k1 - k2) (skipn (k1 + k2) l)].
Proof.
  intros m a N l k1 k2 H K.
  destruct (rw_cells_CB_split asegs m a N k1 l H ltac:(lia)) as [H1 H2].
  destruct (rw_cells_CB_split asegs m _ (N - k1) k2 (skipn k1 l) H2 ltac:(lia)) as [H3 H4].
  rewrite skipn_skipn in H4. replace (k2 + k1)%nat with (k1 + k2)%nat in H4 by lia.
  replace (N - k1 - k2)%nat with (N - k1 - k2)%nat by lia.
  split; [exact H1|]. split; [exact H3| exact H4].
Qed.

Lemma cb_join3 : forall m a n1 n2 n3 (l1 l2 l3 : list byte),
  rw_cells asegs m a [CB n1 l1] -> rw_cells asegs m (a + Z.of_nat n1) [CB n2 l2] ->
  rw_cells asegs m (a + Z.of_nat n1 + Z.of_nat n2) [CB n3 l3] ->
  rw_cells asegs m a [CB (n1 + n2 + n3) (l1 ++ l2 ++ l3)].
Proof.
  intros m a n1 n2 n3 l1 l2 l3 H1 H2 H3.
  pose proof (rw_cells_CB_join asegs m _ _ _ _ _ H2 H3) as H23.
  pose proof (rw_cells_CB_join asegs m _ _ _ _ _ H1 ltac:(replace (Z.of_nat (n2 + n3)) with (Z.of_nat n2 + Z.of_nat n3) by lia; exact H23)) as H.
  replace (n1 + n2 + n3)%nat with (n1 + (n2 + n3))%nat by lia. exact H.
Qed.

Lemma cb1_c1 : forall m a x, rw_cells asegs m a [CB 1 [x]] -> rw_cells asegs m a [C1 x].
Proof. intros m a x [[W B] R]. split; [split|]; cbn in *; tauto. Qed.
Lemma c1_cb1 : forall m a x, rw_cells asegs m a [C1 x] -> rw_cells asegs m a [CB 1 [x]].
Proof. intros m a x [[W B] R]. split; [split|]; cbn in *; try tauto. Qed.
Lemma cb1_elem : forall m a (l : list byte), rw_cells asegs m a [CB 1 l] -> exists x, l = [x].
Proof.
  intros m a l [[W _] _]. cbn in W. destruct W as [L _].
  destruct l as [|x [|y l]]; cbn in L; try discriminate. exists x. reflexivity.
Qed.

Definition cc_x (len o n : Z) : list byte := firstn (Z.to_nat (nsh n - n / 8)) (skipn (Z.to_nat (n / 8)) (cc_gen len o)).
Lemma cc_gen_rest : forall len o n, 0 <= o <= len -> 0 <= n <= len -> nsh o <= nsh n ->
  skipn (Z.to_nat (n / 8)) (cc_gen len o) = cc_x len o n ++ poison_bytes (Z.to_nat (nsh len - nsh n)) 0xfc.
Proof.
  intros len o n Ho Hn Hon. unfold cc_x.
  pose proof (nsh_bounds n) as (NB & _ & _). pose proof (nsh_mono n len (proj2 Hn)) as NM.
  assert (D0 : 0 <= n / 8) by (apply Z.div_pos; lia).
  rewrite <- (firstn_skipn (Z.to_nat (nsh n - n / 8)) (skipn (Z.to_nat (n / 8)) (cc_gen len o))) at 1. f_equal.
  rewrite skipn_skipn. rewrite cc_gen_skipn by (try lia; rewrite Nat2Z.inj_add, !Z2Nat.id by lia; lia). f_equal. lia.
Qed.
Lemma cc_x_length : forall len o n, 0 <= o <= len -> 0 <= n <= len -> length (cc_x len o n) = Z.to_nat (nsh n - n / 8).
Proof.
  intros len o n Ho Hn. unfold cc_x. pose proof (nsh_bounds n) as (NB & _ & _). pose proof (nsh_mono n len (proj2 Hn)) as NM.
  assert (D0 : 0 <= n / 8) by (apply Z.div_pos; lia).
  rewrite length_firstn, length_skipn, (cc_gen_len len o Ho). lia.
Qed.
