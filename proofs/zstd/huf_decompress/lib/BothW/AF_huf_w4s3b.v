(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree HufWalkKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac w4ez :=
  repeat lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite ?(ez_ok zv E (kE_atoms zv xs));
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
      end
  end.

Lemma w4_br_nz : forall E P B,
  bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_NE
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P (EAluw ALU_SRL B (ELit 3))) (ELit 1))))
    (edenot E (ELit 0)) = true.
Proof.
  intros E P B HB HP.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
  rewrite (u_srlw_small (edenot E B) (Z_to_bv 64 3) 3) by
    (first [reflexivity | lia | change (2 ^ (3 mod 32)) with 8; Z.div_mod_to_equations; lia]).
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  change (2 ^ (3 mod 32)) with 8.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
    { apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8) <> 0).
    { assert (HB8 : bv_unsigned (edenot E B) / 8 <= 8) by (apply Z.div_le_upper_bound; lia).
      intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)) 1); [lia|].
  reflexivity.
Qed.

Ltac w4uz :=
  w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia.

Lemma w4_br_tix : forall E D X Y,
  2^64 - 2^48 <= bv_unsigned (edenot E D) -> 52 <= bv_unsigned (edenot E Y) mod 64 <= 63 ->
  branch_taken BC_GEU (edenot E D) (edenot E (EMd M_MUL (ELit 2) (EAlu ALU_SRL X Y))) = true.
Proof.
  intros E D X Y HD HY.
  assert (RX : bv_unsigned (edenot E X) < 2^64)
    by (pose proof (bv_unsigned_in_range _ (edenot E X)); unfold bv_modulus in *; lia).
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  cbn [edenot branch_taken].
  rewrite bv_ltu_Z, u_mul64, u_srl64.
  set (s := bv_unsigned (edenot E Y) mod 64) in *.
  change (bv_unsigned (Z_to_bv 64 2)) with 2.
  assert (HI : bv_unsigned (edenot E X) / 2 ^ s < 2 ^ (64 - s)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (s + (64 - s)) with 64 by lia. exact RX. }
  assert (H12 : 2 ^ (64 - s) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  assert (HP : 0 <= bv_unsigned (edenot E X) / 2 ^ s) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  change (2 ^ 12) with 4096 in H12.
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (bv_unsigned (edenot E D)) (2 * (bv_unsigned (edenot E X) / 2 ^ s))); [lia | reflexivity].
Qed.

Lemma w4_br_tixf : forall E D X Y,
  2^64 - 2^48 <= bv_unsigned (edenot E D) -> 52 <= bv_unsigned (edenot E Y) mod 64 <= 63 ->
  branch_taken BC_LTU (edenot E D) (edenot E (EMd M_MUL (ELit 2) (EAlu ALU_SRL X Y))) = false.
Proof.
  intros E D X Y HD HY.
  assert (RX : bv_unsigned (edenot E X) < 2^64)
    by (pose proof (bv_unsigned_in_range _ (edenot E X)); unfold bv_modulus in *; lia).
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  cbn [edenot branch_taken].
  rewrite bv_ltu_Z, u_mul64, u_srl64.
  set (s := bv_unsigned (edenot E Y) mod 64) in *.
  change (bv_unsigned (Z_to_bv 64 2)) with 2.
  assert (HI : bv_unsigned (edenot E X) / 2 ^ s < 2 ^ (64 - s)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (s + (64 - s)) with 64 by lia. exact RX. }
  assert (H12 : 2 ^ (64 - s) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  assert (HP : 0 <= bv_unsigned (edenot E X) / 2 ^ s) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  change (2 ^ 12) with 4096 in H12.
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (bv_unsigned (edenot E D)) (2 * (bv_unsigned (edenot E X) / 2 ^ s))); [lia | reflexivity].
Qed.

Lemma w4_br_nzf : forall E P B,
  bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_EQ
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P (EAlu ALU_SRL B (ELit 3))) (ELit 1))))
    (edenot E (ELit 0)) = false.
Proof.
  intros E P B HB HP.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64, u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (3 mod 64) with 3. change (2 ^ 3) with 8.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)).
    { apply Z.lxor_nonneg; split; intros; Z.div_mod_to_equations; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8) <> 0).
    { assert (HB8 : bv_unsigned (edenot E B) / 8 <= 8) by (apply Z.div_le_upper_bound; lia).
      intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B) / 8)) 1); [lia|].
  reflexivity.
Qed.

Ltac w4uzm :=
  first [ w4uz | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; Z.div_mod_to_equations; lia ].

Ltac w4br :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
         (EAlu ALU_XOR ?P (EAluw ALU_SRL ?B (ELit 3))) (ELit 1)))) (edenot ?E (ELit 0)) = true =>
      apply (w4_br_nz E P B); w4uz
  | |- branch_taken BC_GEU (edenot ?E ?D) (edenot ?E (EMd M_MUL (ELit 2) (EAlu ALU_SRL ?X ?Y))) = true =>
      apply (w4_br_tix E D X Y); w4uzm
  | |- branch_taken BC_EQ (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
         (EAlu ALU_XOR ?P (EAlu ALU_SRL ?B (ELit 3))) (ELit 1)))) (edenot ?E (ELit 0)) = false =>
      apply (w4_br_nzf E P B); w4uz
  | |- branch_taken BC_LTU (edenot ?E ?D) (edenot ?E (EMd M_MUL (ELit 2) (EAlu ALU_SRL ?X ?Y))) = false =>
      apply (w4_br_tixf E D X Y); w4uzm
  | |- branch_taken _ _ _ = _ =>
      w4ez; unfold branch_taken; try unfold bv_lts;
      rewrite ?bv_ltu_Z, ?bv_eqb_Z, ?zb_signed, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      rewrite ?Z.mod_small by lia;
      repeat match goal with |- context [(?x <? ?y)%Z] => destruct (Z.ltb_spec x y) end;
      repeat match goal with |- context [(?x =? ?y)%Z] => destruct (Z.eqb_spec x y) end;
      cbn [negb]; first [reflexivity | exfalso; lia]
  end.

Lemma w4_zk_word4_ok : forall segs zv xs m a v b c A cs k V,
  zatoms_lt (length zv) a = true -> zatoms_lt (length zv) v = true -> zsa a = SA b c ->
  0 <= zden zv a - c < 2^64 -> 0 <= zden zv a < 2^64 -> 0 <= zden zv v < 2^64 -> zden zv a + 4 <= 2^64 ->
  rw_cells segs m A cs -> cell_at cs k = Some (C4 V) -> zden zv a = A + Z.of_nat k -> V = Z_to_bv 64 (zden zv v) ->
  kentry_ok segs (kE zv xs) m (zk_ent (ZKWord a 4 v)).
Proof.
  intros segs zv xs m a v b c A cs k V HA HV HS R1 R2 R3 R4 [CA WR] HC HE HVe.
  cbn [kentry_ok zk_ent].
  assert (ES : estart (kE zv xs) (zsa a) = zden zv a) by (eapply estart_zsa_split; eauto).
  split; [lia|]. split.
  - unfold flat. rewrite ES. lia.
  - rewrite adenot_wa, ES, HE, (zle_ok zv xs v HV), <- HVe.
    destruct CA as [WF BA].
    destruct (cell_at_split cs k (C4 V) (C4 V) HC) as (pre & post & -> & HK & _).
    apply cells_wf_app in WF as [WFp WFr].
    assert (LEN : (k + 4 <= length (cells_bytes (pre ++ C4 V :: post)))%nat).
    { rewrite cells_bytes_app, length_app. cbn [cells_bytes]. rewrite length_app.
      pose proof (cbytes_length (C4 V) I) as L4. cbn [csize] in L4.
      rewrite L4, (cells_bytes_length pre WFp). lia. }
    pose proof (bytes_at_rdn segs m A _ k 4 BA LEN) as RD.
    unfold wa in *. etransitivity; [exact RD|]. f_equal.
    rewrite cells_bytes_app. cbn [cells_bytes cbytes].
    rewrite <- HK, <- (cells_bytes_length pre WFp), skipn_app_exact.
    unfold le4. reflexivity.
Qed.

Fixpoint w4_c4_offsets (off : nat) (cs : list cell) : list nat :=
  match cs with
  | [] => []
  | C4 _ :: r => off :: w4_c4_offsets (off + 4) r
  | c :: r => w4_c4_offsets (off + csize c) r
  end.

Ltac w4_word4_try segs zv xs m a v b c A cs H ks :=
  lazymatch ks with
  | nil => fail
  | cons ?k ?rest =>
      first [ eapply (w4_zk_word4_ok segs zv xs m a v b c A cs k _);
              [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
              | kx_arith | kx_arith | kx_arith | kx_arith | exact H | reflexivity
              | cbv [zden nth]; lia | cbv [zden nth]; f_equal; first [reflexivity | lia] ]
            | w4_word4_try segs zv xs m a v b c A cs H rest ]
  end.

Ltac w4word4_core segs zv xs m a v :=
  let s1 := eval vm_compute in (zsa a) in
  lazymatch s1 with SA ?b ?c =>
    match goal with H : rw_cells segs m ?A ?cs |- _ =>
      let ks := eval vm_compute in (w4_c4_offsets 0 cs) in
      w4_word4_try segs zv xs m a v b c A cs H ks end
  end.

Ltac w4word4 :=
  lazymatch goal with
  | |- kentry_ok ?segs (kE ?zv ?xs) ?m (zk_ent (ZKWord ?a 4 ?v)) => w4word4_core segs zv xs m a v
  | |- kentry_ok ?segs ?E ?m (zk_ent (ZKWord ?a 4 ?v)) =>
      let e := eval unfold E in E in
      lazymatch e with kx_env (map (Z_to_bv 64) ?zv) ?xs => w4word4_core segs zv xs m a v end
  end.

Lemma w4_srl_lt : forall E x s, 52 <= bv_unsigned (edenot E s) mod 64 <= 63 ->
  0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 4096.
Proof.
  intros E x s HS.
  assert (RX : bv_unsigned (edenot E x) < 2^64)
    by (pose proof (bv_unsigned_in_range _ (edenot E x)); unfold bv_modulus in *; lia).
  pose proof (bv_unsigned_in_range _ (edenot E x)) as [RX0 _].
  cbn [edenot]. rewrite u_srl64.
  set (t := bv_unsigned (edenot E s) mod 64) in *.
  assert (HI : bv_unsigned (edenot E x) / 2 ^ t < 2 ^ (64 - t)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (t + (64 - t)) with 64 by lia. exact RX. }
  assert (H12 : 2 ^ (64 - t) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  assert (HP : 0 <= bv_unsigned (edenot E x) / 2 ^ t) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  change (2 ^ 12) with 4096 in H12. lia.
Qed.

Lemma w4_shd_ap : forall E X B O k,
  bv_unsigned (edenot E X) < 2^47 -> 0 <= O -> O + 2^44 <= 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + 1 <= 2^64 ->
  bv_unsigned (edenot E B) + k + 1 <= O \/ O + 2^44 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit 1)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit 1) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k HX HO1 HO2 HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (2 ^ (3 mod 64)) with 8.
  assert (HD : bv_unsigned (edenot E X) / 8 < 2^44)
    by (apply Z.div_lt_upper_bound; [lia | change (8 * 2^44) with (2^47); lia]).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Ltac w4xb :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E ?X) < _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite (ez_ok zv E (kE_atoms zv xs) X);
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [bv_unsigned (edenot E (EAlu ALU_SRL ?x ?s))] =>
            let HV := fresh "HV" in
            assert (HV : 0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 4096) by (apply w4_srl_lt; w4uzm);
            let v := fresh "v" in set (v := bv_unsigned (edenot E (EAlu ALU_SRL x s))) in *; clearbody v
        end;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
        first [lia | Z.div_mod_to_equations; lia]
      end
  end.

Ltac w4apz :=
  w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
  match goal with H : KXGoM.apart _ _ _ _ |- _ =>
    let H' := fresh "AP" in pose proof H as H'; unfold KXGoM.apart in H'; lia end.

Ltac w4shd :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) _ /\ _ =>
      apply (w4_shd_ap E X B O k); [ w4xb | lia | lia | w4uz | w4uz | w4apz ]
  end.

Lemma w4_shd4 : forall E X B O k,
  bv_unsigned (edenot E X) < 2^47 -> 0 <= O -> O + 2^44 <= 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + 4 <= 2^64 ->
  bv_unsigned (edenot E B) + k + 4 <= O \/ O + 2^44 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit 4)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit 4) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k HX HO1 HO2 HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (bv_unsigned (Z_to_bv 64 4)) with 4. change (2 ^ (3 mod 64)) with 8.
  assert (HD : bv_unsigned (edenot E X) / 8 < 2^44)
    by (apply Z.div_lt_upper_bound; [lia | change (8 * 2^44) with (2^47); lia]).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Lemma w4_shd8 : forall E X B O k,
  bv_unsigned (edenot E X) < 2^47 -> 0 <= O -> O + 2^44 <= 2^64 ->
  0 <= bv_unsigned (edenot E B) + k -> bv_unsigned (edenot E B) + k + 8 <= 2^64 ->
  bv_unsigned (edenot E B) + k + 8 <= O \/ O + 2^44 <= bv_unsigned (edenot E B) + k ->
  flat E (SA (EAlu ALU_SRL X (ELit 3)) O) (elenZ E (ELit 1)) /\ flat E (SA B k) (elenZ E (ELit 8)) /\
  (estart E (SA (EAlu ALU_SRL X (ELit 3)) O) + elenZ E (ELit 1) <= estart E (SA B k) \/
   estart E (SA B k) + elenZ E (ELit 8) <= estart E (SA (EAlu ALU_SRL X (ELit 3)) O)).
Proof.
  intros E X B O k HX HO1 HO2 HB1 HB2 HAP.
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot].
  rewrite u_srl64.
  change (bv_unsigned (Z_to_bv 64 3)) with 3. change (bv_unsigned (Z_to_bv 64 1)) with 1.
  change (bv_unsigned (Z_to_bv 64 8)) with 8. change (2 ^ (3 mod 64)) with 8.
  assert (HD : bv_unsigned (edenot E X) / 8 < 2^44)
    by (apply Z.div_lt_upper_bound; [lia | change (8 * 2^44) with (2^47); lia]).
  assert (HD0 : 0 <= bv_unsigned (edenot E X) / 8) by (apply Z.div_pos; lia).
  repeat split; lia.
Qed.

Lemma w4_srlw8 : forall E B, bv_unsigned (edenot E B) <= 64 ->
  0 <= bv_unsigned (edenot E (EAluw ALU_SRL B (ELit 3))) <= 8.
Proof.
  intros E B HB.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot].
  rewrite (u_srlw_small (edenot E B) (Z_to_bv 64 3) 3) by
    (first [reflexivity | lia | change (2 ^ (3 mod 32)) with 8; Z.div_mod_to_equations; lia]).
  change (2 ^ (3 mod 32)) with 8. split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia.
Qed.

Ltac w4xbw :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E ?X) < _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite (ez_ok zv E (kE_atoms zv xs) X);
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [bv_unsigned (edenot E (EAluw ALU_SRL ?x (ELit 3)))] =>
            let HV := fresh "HV" in
            assert (HV : 0 <= bv_unsigned (edenot E (EAluw ALU_SRL x (ELit 3))) <= 8) by (apply w4_srlw8; w4uz);
            let v := fresh "v" in set (v := bv_unsigned (edenot E (EAluw ALU_SRL x (ELit 3)))) in *; clearbody v
        end;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia
      end
  end.

Lemma w4_srltl : forall E x s k, bv_unsigned (edenot E s) mod 64 = 64 - k -> 1 <= k <= 63 ->
  0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 2^k.
Proof.
  intros E x s k HS HK.
  assert (R1 : bv_unsigned (edenot E x) < 2^64)
    by (pose proof (bv_unsigned_in_range _ (edenot E x)); unfold bv_modulus in *; lia).
  pose proof (bv_unsigned_in_range _ (edenot E x)) as [R0 _].
  cbn [edenot]. rewrite u_srl64, HS.
  split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] |].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
  rewrite <- Z.pow_add_r by lia. replace (64 - k + k) with 64 by lia. exact R1.
Qed.

Ltac w4xbt k :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E ?X) < _ =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite (ez_ok zv E (kE_atoms zv xs) X);
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb];
        repeat match goal with
        | |- context [bv_unsigned (edenot E (EAlu ALU_SRL ?x ?s))] =>
            let HV := fresh "HV" in
            assert (HV : 0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 2^k) by (apply w4_srltl; [w4uzm | lia]);
            let v := fresh "v" in set (v := bv_unsigned (edenot E (EAlu ALU_SRL x s))) in *; clearbody v
        end;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia
      end
  end.

Lemma w4_br_nzy : forall E P Y,
  bv_unsigned (edenot E Y) < bv_unsigned (edenot E P) ->
  branch_taken BC_NE
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P Y) (ELit 1))))
    (edenot E (ELit 0)) = true.
Proof.
  intros E P Y H.
  pose proof (bv_unsigned_in_range _ (edenot E P)) as [RP _].
  pose proof (bv_unsigned_in_range _ (edenot E Y)) as [RY _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E Y))).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E Y))).
    { apply Z.lxor_nonneg; split; intros; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E Y)) <> 0).
    { intros HZ. pose proof (Z.lxor_eq _ _ HZ). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E Y))) 1); [lia|].
  reflexivity.
Qed.

Ltac w4bry :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU
         (EAlu ALU_XOR ?P (ELit ?k)) (ELit 1)))) (edenot ?E (ELit 0)) = true =>
      apply (w4_br_nzy E P (ELit k)); w4uz
  end.

Lemma w4_srlw3 : forall E e x, edenot E e = Z_to_bv 64 x -> 0 <= x < 2^31 ->
  bv_unsigned (edenot E (EAluw ALU_SRL e (ELit 3))) = x / 8.
Proof.
  intros E e x He Hx. cbn [edenot]. rewrite He.
  assert (H3 : bv_unsigned (Z_to_bv 64 3) = 3) by (rewrite Z_to_bv_unsigned; reflexivity).
  assert (HX : bv_unsigned (Z_to_bv 64 x) = x)
    by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); apply Z.mod_small; lia).
  rewrite (u_srlw_small (Z_to_bv 64 x) (Z_to_bv 64 3) 3); rewrite ?H3, ?HX.
  - change (3 mod 32) with 3. change (2 ^ 3) with 8. reflexivity.
  - reflexivity.
  - lia.
  - change (3 mod 32) with 3. change (2 ^ 3) with 8. apply Z.div_lt_upper_bound; lia.
Qed.

Ltac w4b8 :=
  lazymatch goal with |- context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?e (ELit 3)))] =>
    lazymatch goal with |- 0 <= ?b + _ <= _ =>
      rewrite (w4_srlw3 E e b); [Z.div_mod_to_equations; lia | w4ez; first [reflexivity | f_equal; lia] | lia] end end.

Tactic Notation "kx_runFLd" uconstr(STOPS) uconstr(FUEL) uconstr(DIRS) uconstr(KZS) uconstr(RRS) uconstr(WWS) uconstr(UWS) :=
  let S := constr:(STOPS : list Z) in let Fu := constr:(FUEL : nat) in let D := constr:(DIRS : list bool) in
  let K := constr:(KZS : list kz) in let R := constr:(RRS : list (Z * Z)) in let W := constr:(WWS : list (Z * Z)) in
  let U := constr:(UWS : list (Z * Z)) in
  kx_prepFm S Fu K R W U; kx_goFL D.

Lemma w4_ztab_munch : forall (m m' : word -> option byte) W A N st fs,
  ztab_fact bsegs m A N st fs -> munch W m m' -> disjoint_from W A N -> 0 <= A -> A + N <= 2^64 ->
  ztab_fact bsegs m' A N st fs.
Proof.
  intros m m' W A N st fs HZ HM HD H0 H1 z Hz lo hi Hf.
  destruct (HZ z Hz lo hi Hf) as [b [Hr Hb]]. exists b. split; [|exact Hb].
  rewrite <- Hr. apply rdn_ext.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. lia.
  - intros x Hx. apply HM. rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap, bv_modulus in Hx.
    rewrite Z.mod_small in Hx by lia.
    apply (disjoint_outside W A N); [exact HD | lia].
Qed.

Ltac w4_ptr_fix S off b :=
  match goal with
  | H : rw_cells _ _ _ [C8 (Z_to_bv 64 ?e)] |- _ =>
    lazymatch e with context [bv_unsigned (edenot ?E (EAluw ALU_SRL ?X (ELit 3)))] =>
      let Q := fresh "Q" in
      assert (Q : bv_unsigned (edenot E (EAluw ALU_SRL X (ELit 3))) = bv_unsigned (edenot E X) / 8);
      [ change (edenot E (EAluw ALU_SRL X (ELit 3))) with (sext 64 (alu32 ALU_SRL (low32 (edenot E X)) (low32 (edenot E (ELit 3)))));
        rewrite (u_srlw_small (edenot E X) (edenot E (ELit 3)) 3);
        [ reflexivity | vm_compute; reflexivity
        | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia
        | w4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
          replace (2 ^ (3 mod 32)) with 8 by reflexivity; lia ]
      | rewrite Q in H; clear Q;
        let b0 := eval unfold E in E in
        lazymatch b0 with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
          let na := eval vm_compute in (length zv) in
          rewrite (ez_ok zv E (kE_atoms zv xs) X) in H; cbv [ez] in H; change (length zv) with na in H;
          cbv [nth Nat.ltb Nat.leb] in H
        end;
        lazymatch type of H with rw_cells _ _ _ [C8 (Z_to_bv 64 ?e')] =>
          replace e' with (S + off - b / 8) in H
            by (rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia)
        end ]
    end
  end.

Ltac w4_rng_all :=
  repeat match goal with
  | |- context [bv_unsigned (ev ?E ?j)] =>
      lazymatch goal with _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail | _ => let R := fresh "R" in kx_range (EVar j) R end
  | |- context [bv_unsigned (edenot ?E ?e)] =>
      lazymatch goal with _ : _ <= bv_unsigned (edenot E e) <= _ |- _ => fail | _ => let R := fresh "R" in kx_range e R end
  end.

Lemma w4s32_negsh : forall E v tl rsv, 1 <= tl <= 12 -> 0 <= rsv <= 255 -> bv_unsigned (edenot E v) = tl + 256 * rsv ->
  edenot E (EAlu ALU_AND (EAluw ALU_SUB (ELit 0) v) (ELit 63)) = Z_to_bv 64 (64 - tl).
Proof.
  intros E v tl rsv HT HR HV.
  pose proof (neg_desc_shift tl rsv HT HR) as N.
  apply bv_eq. cbn [edenot]. rewrite u_and64. unfold sext. rewrite bv_sign_extend_unsigned.
  cbn [alu32 alu]. unfold bv_signed. rewrite bv_sub_unsigned. unfold low32. rewrite !bv_extract_unsigned.
  cbn [Z.of_N]. rewrite !Z.shiftr_0_r, HV, !Z_to_bv_unsigned, bv_swrap_wrap.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64. change (Z.of_N 32) with 32.
  rewrite ?Zmod_0_l. rewrite (Z.mod_small (tl + 256 * rsv)) by lia.
  rewrite (Z.mod_small 63) by lia. rewrite (Z.mod_small (64 - tl)) by lia.
  rewrite <- N. reflexivity.
Qed.

Lemma w4_ez_add : forall zv E a b ta tb, ez zv E a = ta -> ez zv E b = tb -> ez zv E (EAlu ALU_ADD a b) = ta + tb.
Proof. intros zv E a b ta tb <- <-. reflexivity. Qed.
Lemma w4_ez_sub : forall zv E a b ta tb, ez zv E a = ta -> ez zv E b = tb -> ez zv E (EAlu ALU_SUB a b) = ta - tb.
Proof. intros zv E a b ta tb <- <-. reflexivity. Qed.
Lemma w4_ez_mul : forall zv E a b ta tb, ez zv E a = ta -> ez zv E b = tb -> ez zv E (EMd M_MUL a b) = ta * tb.
Proof. intros zv E a b ta tb <- <-. reflexivity. Qed.
Lemma w4_ez_srl : forall zv E a sh ta, ez zv E a = ta -> ez zv E (EAlu ALU_SRL a (ELit sh)) = (ta mod 2^64) / 2^(sh mod 64).
Proof. intros zv E a sh ta <-. reflexivity. Qed.
Lemma w4_ez_lit : forall zv E z, ez zv E (ELit z) = z.
Proof. reflexivity. Qed.
Lemma w4_ez_hi : forall zv E j, Nat.ltb j (length zv) = false -> ez zv E (EVar j) = bv_unsigned (ev E j).
Proof. intros zv E j H. cbn [ez]. rewrite H. reflexivity. Qed.
Lemma w4_ez_lo : forall zv E j x, Nat.ltb j (length zv) = true -> nth j zv 0 = x -> ez zv E (EVar j) = x.
Proof. intros zv E j x H <-. cbn [ez]. rewrite H. reflexivity. Qed.

Ltac w4_ez_pf zv E e :=
  lazymatch e with
  | EAlu ALU_ADD ?a ?b => let pa := w4_ez_pf zv E a in let pb := w4_ez_pf zv E b in constr:(w4_ez_add zv E a b _ _ pa pb)
  | EAlu ALU_SUB ?a ?b => let pa := w4_ez_pf zv E a in let pb := w4_ez_pf zv E b in constr:(w4_ez_sub zv E a b _ _ pa pb)
  | EMd M_MUL ?a ?b => let pa := w4_ez_pf zv E a in let pb := w4_ez_pf zv E b in constr:(w4_ez_mul zv E a b _ _ pa pb)
  | EAlu ALU_SRL ?a (ELit ?sh) => let pa := w4_ez_pf zv E a in constr:(w4_ez_srl zv E a sh _ pa)
  | ELit ?z => constr:(w4_ez_lit zv E z)
  | EVar ?j =>
      lazymatch eval vm_compute in (Nat.ltb j (length zv)) with
      | false => constr:(w4_ez_hi zv E j eq_refl)
      | true => let x := eval cbv [nth] in (nth j zv 0) in constr:(w4_ez_lo zv E j x eq_refl eq_refl)
      end
  | _ => constr:(@eq_refl Z (bv_unsigned (edenot E e)) : ez zv E e = bv_unsigned (edenot E e))
  end.

Ltac w4_cell_gen H W :=
  lazymatch goal with
  | HLF : log_flat ?E ?log |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | rw_cells ?segs m ?A [?c0] =>
          let rec go pre l :=
            lazymatch l with
            | SE ?a W ?v :: ?rest =>
                first [ let Hn := fresh "HC" in
                        assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a W v :: rest)) A
                                       [ltac:(lazymatch W with 8%nat => exact (C8 (edenot E v)) | _ => exact (C4 (edenot E v)) end)])
                          by (first [ eapply (kx_cell_store8 segs E m pre a v rest A)
                                    | eapply (kx_cell_store4 segs E m pre a v rest A) ];
                              [ change (pre ++ SE a W v :: rest) with log; exact HLF
                              | exact H
                              | change E with (kE zv xs); kx_estart_z zv
                              | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]);
                        change (pre ++ SE a W v :: rest) with log in Hn;
                        rewrite (ez_ok zv E (kE_atoms zv xs) v) in Hn;
                        let EQ := fresh "HCe" in let pf := w4_ez_pf zv E v in pose proof pf as EQ; rewrite EQ in Hn; clear EQ;
                        rewrite ?Z_to_bv_bv_unsigned in Hn;
                        clear H; rename Hn into H
                      | let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest ]
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "w4_cell: no store found for" A
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.
Ltac w4_cell H := w4_cell_gen H 8%nat.
Ltac w4_cell4 H := w4_cell_gen H 4%nat.

Ltac w4_cells_post :=
  repeat match goal with
  | HLF : log_flat ?E ?log, H : rw_cells ?segs ?m ?A [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      let l := eval hnf in log in
      lazymatch A with
      | _ + ?off => tryif kx_log_has_off l off then first [ w4_cell H | w4_cell4 H | kx_frame H ] else kx_frame H
      | _ => first [ w4_cell H | w4_cell4 H | kx_frame H ]
      end
  end;
  try (cbn [cells_size csize]; lia).



Lemma w4_low3 : forall x : word, bv_unsigned x < 2^32 ->
  bv_unsigned (ext_val false 0 4 (alu64 ALU_ADD x (mul_div M_MUL (Z_to_bv 64 (-8))
     (sext 64 (alu32 ALU_SRL (low32 x) (low32 (Z_to_bv 64 3))))))) = bv_unsigned x mod 8.
Proof.
  intros x HX.
  pose proof (bv_unsigned_in_range _ x) as [X0 _].
  pose proof (Z.div_mod (bv_unsigned x) 8 ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound (bv_unsigned x) 8 ltac:(lia)) as MB.
  rewrite (proj1 (u_ext_zx 0 4 _)).
  replace (2 ^ (8 * Z.of_nat 0)) with 1 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity.
  rewrite Z.div_1_r, u_add64, u_mul64.
  rewrite (u_srlw_small x (Z_to_bv 64 3) 3) by
    (first [reflexivity | lia | change (2 ^ (3 mod 32)) with 8; Z.div_mod_to_equations; lia]).
  change (2 ^ (3 mod 32)) with 8.
  rewrite (u_lit64a (-8)).
  rewrite Zplus_mod_idemp_r.
  change ((-8) mod 2 ^ 64) with (2 ^ 64 - 8).
  replace (bv_unsigned x + (2 ^ 64 - 8) * (bv_unsigned x / 8))
    with (bv_unsigned x mod 8 + (bv_unsigned x / 8) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full.
  rewrite (Z.mod_small (bv_unsigned x mod 8) (2 ^ 64)) by lia.
  apply Z.mod_small. lia.
Qed.

Lemma w4_addv : forall (a b : word) A B, bv_unsigned a = A -> bv_unsigned b = B -> A + B < 2^64 ->
  bv_unsigned (alu64 ALU_ADD a b) = A + B.
Proof.
  intros a b A B HA HB HL.
  pose proof (bv_unsigned_in_range _ a) as [A0 _]. pose proof (bv_unsigned_in_range _ b) as [B0 _].
  rewrite u_add64, HA, HB. apply Z.mod_small. lia.
Qed.

Lemma w4_zxv : forall (a : word) A, bv_unsigned a = A -> A < 2^32 -> bv_unsigned (ext_val false 0 4 a) = A.
Proof.
  intros a A HA HL. rewrite u_ext_zx0_small; [exact HA |].
  replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity. lia.
Qed.

Lemma w4_extZ_sx4 : forall z, 0 <= z < 2^31 -> ext_Z true 0 4 z = z.
Proof.
  intros z HZ. unfold ext_Z.
  replace (2 ^ (8 * Z.of_nat 0)) with 1 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) by reflexivity.
  change (8 * N.of_nat 4)%N with 32%N.
  rewrite Z.div_1_r, Z.mod_small by lia. apply swrap32_small. lia.
Qed.

Lemma w4_bsum4a : forall (v1 v2 v3 v4 x : word),
  bv_unsigned v1 <= 12 -> bv_unsigned v2 <= 12 -> bv_unsigned v3 <= 12 -> bv_unsigned v4 <= 12 -> bv_unsigned x < 2^32 ->
  bv_unsigned (alu64 ALU_ADD v1 (ext_val false 0 4 (alu64 ALU_ADD v2 (ext_val false 0 4
      (alu64 ALU_ADD v3 (alu64 ALU_ADD v4 (ext_val false 0 4 (alu64 ALU_ADD x (mul_div M_MUL (Z_to_bv 64 (-8))
        (sext 64 (alu32 ALU_SRL (low32 x) (low32 (Z_to_bv 64 3)))))))))))))
  = bv_unsigned v1 + (bv_unsigned v2 + (bv_unsigned v3 + (bv_unsigned v4 + bv_unsigned x mod 8))).
Proof.
  intros v1 v2 v3 v4 x H1 H2 H3 H4 HX.
  pose proof (bv_unsigned_in_range _ v1) as [P1 _]. pose proof (bv_unsigned_in_range _ v2) as [P2 _].
  pose proof (bv_unsigned_in_range _ v3) as [P3 _]. pose proof (bv_unsigned_in_range _ v4) as [P4 _].
  pose proof (Z.mod_pos_bound (bv_unsigned x) 8 ltac:(lia)) as MB.
  eapply w4_addv; [reflexivity | | lia].
  eapply w4_zxv; [| lia]. eapply w4_addv; [reflexivity | | lia].
  eapply w4_zxv; [| lia]. eapply w4_addv; [reflexivity | | lia].
  eapply w4_addv; [reflexivity | | lia].
  exact (w4_low3 x HX).
Qed.

Lemma w4_bsum4 : forall (v1 v2 v3 v4 x : word),
  bv_unsigned v1 <= 12 -> bv_unsigned v2 <= 12 -> bv_unsigned v3 <= 12 -> bv_unsigned v4 <= 12 -> bv_unsigned x < 2^32 ->
  bv_unsigned (ext_val true 0 4 (alu64 ALU_ADD v1 (ext_val false 0 4 (alu64 ALU_ADD v2 (ext_val false 0 4
      (alu64 ALU_ADD v3 (alu64 ALU_ADD v4 (ext_val false 0 4 (alu64 ALU_ADD x (mul_div M_MUL (Z_to_bv 64 (-8))
        (sext 64 (alu32 ALU_SRL (low32 x) (low32 (Z_to_bv 64 3))))))))))))))
  = bv_unsigned v1 + (bv_unsigned v2 + (bv_unsigned v3 + (bv_unsigned v4 + bv_unsigned x mod 8))).
Proof.
  intros v1 v2 v3 v4 x H1 H2 H3 H4 HX.
  pose proof (bv_unsigned_in_range _ v1) as [P1 _]. pose proof (bv_unsigned_in_range _ v2) as [P2 _].
  pose proof (bv_unsigned_in_range _ v3) as [P3 _]. pose proof (bv_unsigned_in_range _ v4) as [P4 _].
  pose proof (Z.mod_pos_bound (bv_unsigned x) 8 ltac:(lia)) as MB.
  unfold ext_val at 1. rewrite (w4_bsum4a v1 v2 v3 v4 x H1 H2 H3 H4 HX).
  rewrite w4_extZ_sx4 by lia. apply u_small. lia.
Qed.

Lemma w4_bsum4z : forall (v1 v2 v3 v4 x : word),
  bv_unsigned v1 <= 12 -> bv_unsigned v2 <= 12 -> bv_unsigned v3 <= 12 -> bv_unsigned v4 <= 12 -> bv_unsigned x < 2^32 ->
  ext_Z true 0 4 (bv_unsigned (alu64 ALU_ADD v1 (ext_val false 0 4 (alu64 ALU_ADD v2 (ext_val false 0 4
      (alu64 ALU_ADD v3 (alu64 ALU_ADD v4 (ext_val false 0 4 (alu64 ALU_ADD x (mul_div M_MUL (Z_to_bv 64 (-8))
        (sext 64 (alu32 ALU_SRL (low32 x) (low32 (Z_to_bv 64 3))))))))))))))
  = bv_unsigned v1 + (bv_unsigned v2 + (bv_unsigned v3 + (bv_unsigned v4 + bv_unsigned x mod 8))).
Proof.
  intros v1 v2 v3 v4 x H1 H2 H3 H4 HX.
  pose proof (bv_unsigned_in_range _ v1) as [P1 _]. pose proof (bv_unsigned_in_range _ v2) as [P2 _].
  pose proof (bv_unsigned_in_range _ v3) as [P3 _]. pose proof (bv_unsigned_in_range _ v4) as [P4 _].
  pose proof (Z.mod_pos_bound (bv_unsigned x) 8 ltac:(lia)) as MB.
  rewrite (w4_bsum4a v1 v2 v3 v4 x H1 H2 H3 H4 HX). apply w4_extZ_sx4. lia.
Qed.

Lemma w4_br_geul : forall E z e, 0 <= z < 2^64 -> bv_unsigned (edenot E e) <= z ->
  branch_taken BC_GEU (edenot E (ELit z)) (edenot E e) = true.
Proof.
  intros E z e Hz He. cbn [edenot branch_taken]. rewrite bv_ltu_Z, (u_small z Hz).
  destruct (Z.ltb_spec z (bv_unsigned (edenot E e))); [lia | reflexivity].
Qed.

Ltac w4_rng_ev :=
  repeat match goal with
  | |- context [ev ?E ?j] =>
      lazymatch goal with _ : _ <= bv_unsigned (ev E j) <= _ |- _ => fail | _ => let R := fresh "R" in kx_range (EVar j) R end
  end.

Ltac w4br_bsum :=
  lazymatch goal with
  | |- branch_taken BC_GEU (edenot ?E (ELit 64)) (edenot ?E (EExt true 0 4 _)) = true =>
      apply w4_br_geul; [lia |]; cbn [edenot]; w4_rng_ev;
      rewrite w4_bsum4 by lia; lia
  end.

Ltac w4_bsum_rng :=
  lazymatch goal with
  | |- 0 <= ext_Z true 0 4 _ <= 64 => w4_rng_ev; rewrite w4_bsum4z by lia; lia
  end.

Lemma w4_bsum4w : forall (v1 v2 v3 v4 x : word),
  bv_unsigned v1 <= 12 -> bv_unsigned v2 <= 12 -> bv_unsigned v3 <= 12 -> bv_unsigned v4 <= 12 -> bv_unsigned x < 2^32 ->
  ext_Z true 0 4 (bv_unsigned (alu64 ALU_ADD v1 (ext_val false 0 4 (alu64 ALU_ADD v2 (ext_val false 0 4
      (alu64 ALU_ADD v3 (alu64 ALU_ADD v4 (ext_val false 0 4 (alu64 ALU_ADD x (mul_div M_MUL (Z_to_bv 64 (-8))
        (sext 64 (alu32 ALU_SRL (low32 x) (low32 (Z_to_bv 64 3))))))))))))))
  = bv_unsigned v1 + bv_unsigned (ext_val false 0 4 (alu64 ALU_ADD v2 (ext_val false 0 4
      (alu64 ALU_ADD v3 (alu64 ALU_ADD v4 (ext_val false 0 4 (alu64 ALU_ADD x (mul_div M_MUL (Z_to_bv 64 (-8))
        (sext 64 (alu32 ALU_SRL (low32 x) (low32 (Z_to_bv 64 3)))))))))))).
Proof.
  intros v1 v2 v3 v4 x H1 H2 H3 H4 HX.
  pose proof (bv_unsigned_in_range _ v2) as [P2 _].
  pose proof (bv_unsigned_in_range _ v3) as [P3 _]. pose proof (bv_unsigned_in_range _ v4) as [P4 _].
  pose proof (Z.mod_pos_bound (bv_unsigned x) 8 ltac:(lia)) as MB.
  rewrite (w4_bsum4z v1 v2 v3 v4 x H1 H2 H3 H4 HX). f_equal. symmetry.
  eapply w4_zxv; [| lia]. eapply w4_addv; [reflexivity | | lia].
  eapply w4_zxv; [| lia]. eapply w4_addv; [reflexivity | | lia].
  eapply w4_addv; [reflexivity | | lia].
  exact (w4_low3 x HX).
Qed.

Ltac w4_c4_bsum :=
  match goal with |- context [ext_Z true 0 4 (bv_unsigned (alu64 ALU_ADD ?v1 (ext_val false 0 4 (alu64 ALU_ADD ?v2
      (ext_val false 0 4 (alu64 ALU_ADD ?v3 (alu64 ALU_ADD ?v4 (ext_val false 0 4 (alu64 ALU_ADD ?x _)))))))))] =>
    w4_rng_ev; rewrite (w4_bsum4w v1 v2 v3 v4 x) by lia
  end;
  match goal with H : rw_cells _ _ _ [C4 (Z_to_bv 64 ?e)] |- _ =>
    lazymatch e with context [edenot _ (EExt _ _ _ _)] => cbn [edenot] in H end end.
