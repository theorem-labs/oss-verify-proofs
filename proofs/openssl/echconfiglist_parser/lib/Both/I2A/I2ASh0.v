(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Uint63.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxState FxMem FxImage I2Run I2RunA.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.I2A Require Import I2AInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition row_hit (g : Z) (r : Z * Z * Z) : bool :=
  let '(beg, sz, _) := r in (beg <=? g) && (g <? beg + 8 * nsh sz) && (beg mod 8 =? 0) && (0 <=? sz).
Definition row_byte (rows : list (Z * Z * Z)) (g : Z) : option Z :=
  match find (row_hit g) rows with
  | Some (beg, sz, _) => if (g - beg) / 8 <? sz / 8 then Some 0 else Some (sz mod 8)
  | None => None
  end.
(* [comment removed for export] *)
Definition byte_okb (rows : list (Z * Z * Z)) (a j b : Z) : bool :=
  match row_byte rows ((a + j - ASHADOW_BASE) * 8) with Some e => (e =? b) | None => false end
  || ((ASHW_ERRNO <=? a + j) && (a + j <? ASHW_ERRNO + 8) && (b =? 0)).
Definition i8 : list int := [0; 1; 2; 3; 4; 5; 6; 7]%uint63.
Definition sh0_cell_chk (rows : list (Z * Z * Z)) (ac : int * cell) : bool :=
  let a := to_Z (fst ac) in
  (ASHADOW_BASE + 0x2000 <=? a) && (a + 8 <=? 2 ^ 62) &&
  match snd ac with
  | CV (FV _ w) =>
      ((a =? ASHW_ERRNO) && (wZ w =? 0))
      || forallb (fun j : int => byte_okb rows a (to_Z j) ((wZ w / 2 ^ (8 * to_Z j)) mod 256)) i8
  | CB sl =>
      forallb (fun j : int => match sget j sl with
                              | SK b => byte_okb rows a (to_Z j) (to_Z b)
                              | SU => true
                              | SV _ _ => false
                              end) i8
  | CU => false
  end.
Definition sh0_chk (A : i2aconsts) : bool := forallb (sh0_cell_chk aglobals) (ka_sh0 A).

(* [comment removed for export] *)
Lemma find_some_In {T} (f : T -> bool) (l : list T) x : find f l = Some x -> In x l /\ f x = true.
Proof.
  induction l as [|y l IH]; cbn; intros H; [discriminate|].
  destruct (f y) eqn:E; [injection H as <-; auto|]. destruct (IH H) as [H1 H2]. auto.
Qed.

Lemma In_i8 (j : int) : In j i8 <-> 0 <= to_Z j < 8.
Proof.
  unfold i8. split.
  - intros H. cbn [In] in H.
    repeat match type of H with _ \/ _ => destruct H as [<-|H] | False => destruct H end.
    all: match goal with |- 0 <= to_Z ?x < 8 => let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end; lia.
  - intros H.
    assert (K : to_Z j = 0 \/ to_Z j = 1 \/ to_Z j = 2 \/ to_Z j = 3 \/ to_Z j = 4 \/ to_Z j = 5 \/ to_Z j = 6 \/ to_Z j = 7) by lia.
    destruct K as [K|[K|[K|[K|[K|[K|[K|K]]]]]]];
      [apply (f_equal of_Z) in K; rewrite of_to_Z in K; subst j; cbn; tauto ..].
Qed.

(* [comment removed for export] *)
Lemma global_body_byte : forall m beg sz szrz k,
  AGLOBAL_SH m (beg, sz, szrz) -> 0 <= sz -> 0 <= k < nsh sz ->
  mrd asegs m (wa (sh beg + k)) = Some (b8 (if k <? sz / 8 then 0 else sz mod 8)).
Proof.
  intros m beg sz szrz k HG Hsz Hk. unfold AGLOBAL_SH, SHAD in HG. destruct HG as (_ & _ & [[_ [_ HB]] _]).
  unfold global_shadow in HB. rewrite length_app in HB.
  pose proof (shadow_of_length sz Hsz) as HL.
  specialize (HB (Z.to_nat k) ltac:(lia)). rewrite Z2Nat.id in HB by lia. rewrite HB.
  rewrite nth_error_app1 by lia.
  destruct (Z.ltb_spec k (sz / 8)) as [Hlt|Hge].
  - rewrite shadow_of_nth_full; [reflexivity | lia | lia].
  - assert (Hm : sz mod 8 <> 0) by (unfold nsh in Hk; Z.div_mod_to_equations; lia).
    assert (Ek : k = sz / 8) by (unfold nsh in Hk; Z.div_mod_to_equations; lia).
    subst k. rewrite shadow_of_nth_last; [reflexivity | lia | exact Hm].
Qed.

Lemma row_byte_sound : forall m a j b,
  Forall (AGLOBAL_SH m) aglobals -> ACONST m ->
  byte_okb aglobals a j b = true -> ASHADOW_BASE <= a + j ->
  mrd asegs m (wa (a + j)) = Some (b8 b).
Proof.
  intros m a j b HG HAC Hb Ha. unfold byte_okb, row_byte in Hb. apply orb_true_iff in Hb. destruct Hb as [Hb|Hb].
  2:{ rewrite !andb_true_iff in Hb. destruct Hb as [[H1 H2] H3]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. subst b.
      pose proof (ACONST_errno_shw m HAC) as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
      assert (HB' : bytes_at asegs m ASHW_ERRNO (Z_to_le_bytes 8 0)) by exact HB. destruct HB' as (_ & _ & HB'').
      replace (a + j) with (ASHW_ERRNO + Z.of_nat (Z.to_nat (a + j - ASHW_ERRNO))) by lia.
      rewrite HB'' by (rewrite length_Z_to_le_bytes; lia). rewrite Z_to_le_bytes_nth by lia. reflexivity. }
  set (g := (a + j - ASHADOW_BASE) * 8) in Hb.
  destruct (find (row_hit g) aglobals) as [[[beg sz] szrz]|] eqn:E; [|discriminate].
  destruct (find_some_In _ _ _ E) as [Hin Hhit]. unfold row_hit in Hhit. rewrite !andb_true_iff in Hhit.
  destruct Hhit as [[[H1 H2] H3] H4]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. apply Z.leb_le in H4.
  pose proof (proj1 (Forall_forall _ _) HG _ Hin) as HGr.
  assert (Eaj : a + j = sh beg + (g - beg) / 8).
  { unfold sh. subst g. Z.div_mod_to_equations. lia. }
  rewrite Eaj. rewrite (global_body_byte m beg sz szrz ((g - beg) / 8) HGr H4) by (unfold nsh in *; Z.div_mod_to_equations; nia).
  f_equal. f_equal. destruct ((g - beg) / 8 <? sz / 8); apply Z.eqb_eq in Hb; exact Hb.
Qed.

Section S.
  Context {HCEIL : HeapCeil}.
  Variable A : i2aconsts.
  Hypothesis HCHK : sh0_chk A = true.

  Theorem sh0_of_aconst : forall m, ACONST m -> mem_inv asegs m -> sh0_facts A m.
  Proof.
    intros m HAC _. pose proof (proj1 (proj2 HAC)) as HG.
    unfold sh0_facts. apply Forall_forall. intros [a c] Hin.
    pose proof (proj1 (forallb_forall _ _) HCHK (a, c) Hin) as Hc. cbn [fst snd] in Hc |- *.
    unfold sh0_cell_chk in Hc. cbn [fst snd] in Hc. rewrite !andb_true_iff in Hc. destruct Hc as [[Hlo Hhi] Hc].
    apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. pose proof ASHADOW_BASE_val as EB.
    destruct c as [[t w]| |sl]; cbn [sh0_cell]; [| discriminate Hc |].
    - (* [comment removed for export] *)
      apply orb_true_iff in Hc. destruct Hc as [Hz | Hr].
      + apply andb_true_iff in Hz as [Ea Ew]. apply Z.eqb_eq in Ea. apply Z.eqb_eq in Ew. rewrite Ew, Ea.
        pose proof (ACONST_errno_shw m HAC) as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
        exact HB.
      + split; [lia|]. split; [rewrite length_Z_to_le_bytes; change (Z.of_nat 8) with 8; lia|]. intros i Hi. rewrite length_Z_to_le_bytes in Hi.
        rewrite Z_to_le_bytes_nth by exact Hi.
        pose proof (proj1 (forallb_forall _ _) Hr (of_Z (Z.of_nat i)) ltac:(apply In_i8; rewrite toZ_of_Z_small; lia)) as Hb.
        cbn beta in Hb. rewrite toZ_of_Z_small in Hb by lia.
        rewrite (row_byte_sound m (to_Z a) (Z.of_nat i) _ HG HAC Hb) by lia. unfold b8. f_equal. apply bv_eq.
        rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
    - (* [comment removed for export] *)
      intros j Hj. pose proof (proj1 (forallb_forall _ _) Hc j ltac:(apply In_i8; exact Hj)) as Hb. cbn beta in Hb.
      destruct (sget j sl) as [b|v k|]; [| discriminate Hb | exact I].
      rewrite (row_byte_sound m (to_Z a) (to_Z j) _ HG HAC Hb) by lia. reflexivity.
  Qed.
End S.
