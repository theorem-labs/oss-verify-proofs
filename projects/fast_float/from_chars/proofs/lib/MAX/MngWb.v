(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound.
Import AX2S.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr.
Import ListNotations.

Module AxZ2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition m64 (a : Z) : Z := if (0 <=? a) && (a <? 18446744073709551616) then a else a mod 18446744073709551616.
Definition m32 (a : Z) : Z := if (0 <=? a) && (a <? 4294967296) then a else a mod 4294967296.
Definition s32 (a : Z) : Z := m32 (a + 2147483648) - 2147483648.

Lemma m64_ok : forall a, m64 a = a mod 2^64.
Proof.
  intros a. unfold m64. destruct ((0 <=? a) && (a <? 18446744073709551616)) eqn:E.
  - apply andb_true_iff in E as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. rewrite Z.mod_small by (cbn; lia). reflexivity.
  - reflexivity.
Qed.

Lemma m32_ok : forall a, m32 a = a mod 2^32.
Proof.
  intros a. unfold m32. destruct ((0 <=? a) && (a <? 4294967296)) eqn:E.
  - apply andb_true_iff in E as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. rewrite Z.mod_small by (cbn; lia). reflexivity.
  - reflexivity.
Qed.

Lemma s32_ok : forall a, s32 a = bv_swrap 32 a.
Proof.
  intros a. unfold s32, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. rewrite m32_ok. cbn [Z.of_N]. reflexivity.
Qed.

Section ZEval2.
Variable E : env.

Fixpoint zeval2 (e : expr) : Z :=
  match e with
  | ELit z => z
  | EAlu ALU_ADD a b => zeval2 a + zeval2 b
  | EAlu ALU_SUB a b => zeval2 a - zeval2 b
  | EAlu ALU_AND a b => Z.land (m64 (zeval2 a)) (m64 (zeval2 b))
  | EAlu ALU_OR a b => Z.lor (m64 (zeval2 a)) (m64 (zeval2 b))
  | EAlu ALU_SRL a b => Z.shiftr (m64 (zeval2 a)) (zeval2 b mod 64)
  | EAlu ALU_SLL a b => Z.shiftl (m64 (zeval2 a)) (zeval2 b mod 64)
  | EMd M_MUL a b => zeval2 a * zeval2 b
  | EAluw ALU_ADD a b => s32 (zeval2 a + zeval2 b)
  | EAluw ALU_SLL a b => s32 (Z.shiftl (m64 (zeval2 a)) (zeval2 b mod 32))
  | EAluw ALU_SRL a b => s32 (Z.shiftr (m32 (zeval2 a)) (zeval2 b mod 32))
  | EExt sx lo n a => ext_Z sx lo n (m64 (zeval2 a))
  | _ => bv_unsigned (edenot E e)
  end.

#[using="Type"] Lemma zeval2_sound : forall e, edenot E e = wa (zeval2 e).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction e as [z|n|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n];
    try (cbn [zeval2]; rewrite wa_u; reflexivity).
  - reflexivity.
  - destruct op; cbn [zeval2 edenot]; try (rewrite wa_u; reflexivity); rewrite IHa, IHb; rewrite ?m64_ok.
    + rewrite alu_add. unfold v_add. apply wa_eqm. rewrite !u_wa. rewrite ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Z.mod_mod by lia. reflexivity.
    + rewrite alu_sub. unfold v_sub. apply wa_eqm. rewrite !u_wa. rewrite ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r, ?Z.mod_mod by lia. reflexivity.
    + rewrite alu_sll. unfold v_sll. rewrite !u_wa. rewrite mod64_64s. reflexivity.
    + rewrite alu_srl. unfold v_srl. rewrite !u_wa. rewrite mod64_64s. reflexivity.
    + rewrite alu_or. unfold v_or. rewrite !u_wa. reflexivity.
    + rewrite alu_and. unfold v_and. rewrite !u_wa. reflexivity.
  - destruct op; cbn [zeval2 edenot]; try (rewrite wa_u; reflexivity); rewrite IHa, IHb; rewrite ?s32_ok, ?m64_ok, ?m32_ok.
    + rewrite w_addw. unfold v_addw. rewrite !u_wa. unfold wa. f_equal. apply swrap32_eqm.
      rewrite Zplus_mod. rewrite !mod64_32. rewrite <- Zplus_mod. reflexivity.
    + rewrite w_sllw. unfold v_sllw. rewrite !u_wa. rewrite mod64_32s. reflexivity.
    + rewrite w_srlw. unfold v_srlw. rewrite !u_wa. unfold bv_wrap. change (bv_modulus 32) with (2^32).
      rewrite mod64_32, mod64_32s. reflexivity.
  - destruct op; cbn [zeval2 edenot]; try (rewrite wa_u; reflexivity); rewrite IHa, IHb.
    rewrite m_mul. unfold v_mul. apply wa_eqm. rewrite !u_wa. rewrite ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r, ?Z.mod_mod by lia. reflexivity.
  - cbn [zeval2 edenot]. rewrite IHa. rewrite m64_ok. unfold ext_val. rewrite u_wa. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zeval2_u : forall e, bv_unsigned (edenot E e) = zeval2 e mod 2^64.
Proof. LiaFast.lf_pins LiaFast.u0. intros e. rewrite zeval2_sound. apply u_wa. Qed.

End ZEval2.
End AxZ2.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section WB.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma bview_ext : forall m m' x, m' (wa x) = m (wa x) -> bview segs m' x = bview segs m x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m m' x E. unfold bview. destruct ((0 <=? x) && (x <? 2^64)); [|reflexivity].
  unfold wview. rewrite E. cbn [ov_read_bytes]. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma bview_some_byte : forall m x b, 0 <= x < 2^64 -> m (wa x) = Some b -> bview segs m x = Some (bv_unsigned b).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m x b Hx E. unfold bview. replace ((0 <=? x) && (x <? 2^64)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  unfold wview. rewrite E. cbn [ov_read_bytes]. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma wbytes_out : forall bs m (a : word) x,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 -> 0 <= x < 2^64 ->
  (x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= x) ->
  wbytes m a bs (wa x) = m (wa x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs m a x Hnw Hx [H|H].
  - apply wbytes_below; [exact Hnw|]. rewrite u_wa_small by lia. exact H.
  - apply wbytes_above. rewrite u_wa_small by lia. exact H.
Qed.

#[using="Type"] Lemma wbytes_at : forall bs m (a : word) k,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 -> (k < length bs)%nat ->
  wbytes m a bs (wa (bv_unsigned a + Z.of_nat k)) = Some (nth k bs (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins LiaFast.u0.
  induction bs as [|b t IH]; intros m a k Hnw Hk; [cbn in Hk; lia|].
  cbn [wbytes length] in *. destruct k as [|k].
  - rewrite Z.add_0_r, wa_u. cbn [nth]. pose proof (u64_range a) as Ra.
    destruct t as [|b2 t'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + assert (Ha1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (rewrite w_add_1; apply u_small; cbn [length] in Hnw; lia).
      rewrite (wbytes_below (b2 :: t')); [| rewrite Ha1; lia | rewrite Ha1; lia].
      rewrite bv_eqb_refl. reflexivity.
  - cbn [nth]. pose proof (u64_range a) as Ra.
    replace (bv_unsigned a + Z.of_nat (S k)) with (bv_unsigned (a + 1) + Z.of_nat k).
    + apply IH; [|lia]. rewrite w_add_1, u_small by lia. lia.
    + rewrite w_add_1, u_small by lia. lia.
Qed.

End WB.

Lemma wbytes_at_wa : forall bs m a k, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> (k < length bs)%nat ->
  wbytes m (wa a) bs (wa (a + Z.of_nat k)) = Some (nth k bs (Z_to_bv 8 0)).
Proof.
  intros bs m a k H0 H1 Hk. destruct bs as [|b t]; [cbn in Hk; lia|].
  assert (Ha : bv_unsigned (wa a) = a) by (apply u_wa_small; cbn [length] in H1; lia).
  rewrite <- Ha at 2. apply wbytes_at; [rewrite Ha; exact H1 | exact Hk].
Qed.

Lemma wbytes_at_wa0 : forall bs m a, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> (0 < length bs)%nat ->
  wbytes m (wa a) bs (wa a) = Some (nth 0 bs (Z_to_bv 8 0)).
Proof. intros bs m a H0 H1 Hk. rewrite <- (wbytes_at_wa bs m a 0 H0 H1 Hk). rewrite Z.add_0_r. reflexivity. Qed.
