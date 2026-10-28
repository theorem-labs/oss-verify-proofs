(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.

From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseWalkKit HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface AF_huf_z4s_iface AF_huf_z4s3_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_reloadi.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Ltac z4ez :=
  do 30 (try (progress (lazymatch goal with
  | |- context [edenot ?E _] =>
      let b := eval unfold E in E in
      lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        rewrite ?(ez_ok zv E (kE_atoms zv xs));
        let na := eval vm_compute in (length zv) in
        cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]
      end
  end))).

Ltac z4br :=
  lazymatch goal with
  | |- branch_taken _ _ _ = _ =>
      z4ez; unfold branch_taken; rewrite ?bv_ltu_Z, ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      rewrite ?Z.mod_small by lia;
      first [ apply Bool.negb_true_iff, Z.ltb_ge; lia | apply Z.ltb_lt; lia
            | apply Bool.negb_false_iff, Z.ltb_lt; lia | apply Z.ltb_ge; lia ]
  end.

Lemma z4_zk_word4_ok : forall (segs : list Segment) (zv : list Z) (xs : list word) (m : word -> option byte)
    (a v : zexp) (b : expr) (c A : Z) (cs : list cell) (k : nat) (V : word),
  zatoms_lt (length zv) a = true -> zatoms_lt (length zv) v = true -> zsa a = SA b c ->
  0 <= zden zv a - c < 2^64 -> 0 <= zden zv a < 2^64 -> 0 <= zden zv v < 2^64 -> zden zv a + 4 <= 2^64 ->
  rw_cells segs m A cs -> cell_at cs k = Some (C4 V) -> zden zv a = A + Z.of_nat k -> V = Z_to_bv 64 (zden zv v) ->
  kentry_ok segs (kE zv xs) m (zk_ent (ZKWord a 4 v)).
Proof.
  intros segs zv xs m a v b c A cs k V HA HV HS H1 H2 H3 H4 RW CA EA EV.
  cbn [zk_ent kentry_ok].
  assert (ES : estart (kE zv xs) (zsa a) = zden zv a) by (eapply estart_zsa_split; eauto).
  assert (FL : flat (kE zv xs) (zsa a) 4) by (unfold flat; rewrite ES; lia).
  split; [lia|]. split; [exact FL|].
  rewrite <- ov_rdn.
  pose proof (rw_cells_read segs m A cs k (C4 V) RW CA) as R. cbn [csize cbytes] in R.
  replace (adenot (kE zv xs) (zsa a)) with (wa (A + Z.of_nat k)).
  - rewrite R. f_equal. rewrite (zle_ok zv xs v HV), <- EV. reflexivity.
  - apply bv_eq. rewrite (flat_u _ _ _ FL), ES. unfold wa. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    rewrite Z.mod_small; lia.
Qed.

Fixpoint z4_c4_offsets (off : nat) (cs : list cell) : list nat :=
  match cs with
  | [] => []
  | C4 _ :: r => off :: z4_c4_offsets (off + 4) r
  | c :: r => z4_c4_offsets (off + csize c) r
  end.

Ltac z4word4_try segs zv xs m a v b c A cs H ks :=
  lazymatch ks with
  | nil => fail
  | cons ?k ?rest =>
      first [ eapply (z4_zk_word4_ok segs zv xs m a v b c A cs k _);
              [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
              | kx_arith | kx_arith | kx_arith | kx_arith | exact H | reflexivity
              | cbv [zden nth]; lia | cbv [zden nth]; f_equal; first [reflexivity | lia] ]
            | z4word4_try segs zv xs m a v b c A cs H rest ]
  end.

Ltac z4word4 :=
  lazymatch goal with
  | |- kentry_ok ?segs ?E ?m (zk_ent (ZKWord ?a 4 ?v)) =>
      let e := eval unfold E in E in
      lazymatch e with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
        change E with (kE zv xs);
        let s1 := eval vm_compute in (zsa a) in
        lazymatch s1 with SA ?b ?c =>
          match goal with H : rw_cells segs m ?A ?cs |- _ =>
            let ks := eval vm_compute in (z4_c4_offsets 0 cs) in
            z4word4_try segs zv xs m a v b c A cs H ks end
        end
      end
  end.

Lemma z4_dl_b0 : forall tl mtl, 0 <= tl < 256 -> 0 <= mtl < 256 ->
  ext_val false 0 1 (Z_to_bv 64 (tl + 256 * mtl)) = Z_to_bv 64 tl.
Proof.
  intros tl mtl H1 H2. unfold ext_val, ext_Z. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.div_1_r.
  rewrite (Z.mod_small (tl + 256 * mtl)) by lia. rewrite (Z.mul_comm 256 mtl), Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma z4_eext : forall E sx lo n a, edenot E (EExt sx lo n a) = ext_val sx lo n (edenot E a).
Proof. reflexivity. Qed.

Ltac z4brdl := lazymatch goal with |- branch_taken _ _ _ = _ =>
  rewrite ?z4_eext; z4ez; rewrite ?z4_dl_b0 by lia; z4br end.

Lemma z4_bvm : forall x y, x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. exact H.
Qed.

Ltac z4_m64 := match goal with |- context [Z_to_bv 64 (- ?t + ?N)] =>
  let EQ := fresh "EQ" in
  assert (EQ : Z_to_bv 64 (- t + N) = Z_to_bv 64 (64 - t));
  [ apply z4_bvm; rewrite <- (Z.mod_add (64 - t) (-1) (2^64)) by lia; f_equal; lia
  | rewrite EQ; clear EQ ] end.

Lemma z4_br_nz : forall E P B,
  bv_unsigned (edenot E B) <= 64 -> 64 < bv_unsigned (edenot E P) ->
  branch_taken BC_NE
    (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR P B) (ELit 1))))
    (edenot E (ELit 0)) = true.
Proof.
  intros E P B HB HP.
  pose proof (bv_unsigned_in_range _ (edenot E B)) as [RB _].
  cbn [edenot branch_taken].
  rewrite bv_eqb_Z, u_xor64, u_sltu64, u_xor64.
  change (bv_unsigned (Z_to_bv 64 1)) with 1. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  assert (HL : 0 < Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B))).
  { assert (0 <= Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B))).
    { apply Z.lxor_nonneg; split; intros; lia. }
    assert (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B)) <> 0).
    { intros H0. pose proof (Z.lxor_eq _ _ H0). lia. }
    lia. }
  destruct (Z.ltb_spec (Z.lxor (bv_unsigned (edenot E P)) (bv_unsigned (edenot E B))) 1); [lia|].
  reflexivity.
Qed.

Lemma z4_srlw3 : forall E e b, edenot E e = Z_to_bv 64 b -> 0 <= b < 2^31 ->
  edenot E (EAluw ALU_SRL e (ELit 3)) = Z_to_bv 64 (b / 8).
Proof.
  intros E e b He Hb. assert (H8 : 0 <= b / 8 <= b) by (Z.div_mod_to_equations; lia).
  apply bv_eq. cbn [edenot]. rewrite He.
  rewrite (u_srlw_small (Z_to_bv 64 b) (Z_to_bv 64 3) 3) by
    (first [reflexivity | rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite Z.mod_small by lia;
            first [lia | change (2 ^ (3 mod 32)) with 8; Z.div_mod_to_equations; lia]]).
  change (2 ^ (3 mod 32)) with 8. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Ltac z4brx :=
  lazymatch goal with
  | |- branch_taken BC_NE (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR ?P ?B) (ELit 1))))
         (edenot ?E (ELit 0)) = true =>
      apply (z4_br_nz E P B); z4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia
  end.

Ltac z4post_ez :=
  rewrite ?z4_eext in *;
  do 30 (try (lazymatch goal with |- context [edenot ?E ?e] =>
    let b := eval unfold E in E in lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
    rewrite ?(ez_ok zv E (kE_atoms zv xs) e); let na := eval vm_compute in (length zv) in
    cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb] end end));
  rewrite ?Z_to_bv_bv_unsigned in *.

Notation Z4SPL w0 w1 w4 w5 w7 w8 w10 w11 tl mtl DST dcap Qe DT :=
  [C8 w0; C8 w1; C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (DST + dcap - 7)); C8 w4; C8 w5;
   C8 (Z_to_bv 64 (DST + dcap)); C8 w7; C8 w8; C8 (Z_to_bv 64 (DST + Qe)); C8 w10; C8 w11; C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 dcap)] (only parsing).

Lemma z4_srl_lt : forall E x s, 52 <= bv_unsigned (edenot E s) mod 64 <= 63 ->
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

Ltac z4uz :=
  z4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia; lia.

Ltac z4uzm :=
  first [ z4uz | z4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; Z.div_mod_to_equations; lia ].

Lemma z4_br_tix : forall E D X Y,
  2^64 - 2^47 <= bv_unsigned (edenot E D) -> 52 <= bv_unsigned (edenot E Y) mod 64 <= 63 ->
  branch_taken BC_GEU (edenot E D) (edenot E (EMd M_MUL (ELit 4) (EAlu ALU_SRL X Y))) = true.
Proof.
  intros E D X Y HD HY.
  assert (RX : bv_unsigned (edenot E X) < 2^64)
    by (pose proof (bv_unsigned_in_range _ (edenot E X)); unfold bv_modulus in *; lia).
  pose proof (bv_unsigned_in_range _ (edenot E X)) as [RX0 _].
  cbn [edenot branch_taken].
  rewrite bv_ltu_Z, u_mul64, u_srl64.
  set (s := bv_unsigned (edenot E Y) mod 64) in *.
  change (bv_unsigned (Z_to_bv 64 4)) with 4.
  assert (HI : bv_unsigned (edenot E X) / 2 ^ s < 2 ^ (64 - s)).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (s + (64 - s)) with 64 by lia. exact RX. }
  assert (H12 : 2 ^ (64 - s) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
  assert (HP : 0 <= bv_unsigned (edenot E X) / 2 ^ s) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  change (2 ^ 12) with 4096 in H12.
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec (bv_unsigned (edenot E D)) (4 * (bv_unsigned (edenot E X) / 2 ^ s))); [lia | reflexivity].
Qed.

Lemma z4_br_sh : forall E K X Y,
  bv_unsigned (edenot E K) = 2^61 -> 52 <= bv_unsigned (edenot E Y) mod 64 <= 63 ->
  branch_taken BC_EQ (edenot E (EAlu ALU_SRL (EAlu ALU_ADD K (EAlu ALU_SRL X Y)) (ELit 62))) (edenot E (ELit 0)) = true.
Proof.
  intros E K X Y HK HY.
  pose proof (z4_srl_lt E X Y HY) as HI.
  cbn [edenot branch_taken] in *.
  rewrite bv_eqb_Z, u_srl64, u_add64, HK.
  change (bv_unsigned (Z_to_bv 64 62)) with 62. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  change (62 mod 64) with 62.
  rewrite Z.mod_small by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma z4_shd_ap : forall E X B O k,
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

Ltac z4xb :=
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
            assert (HV : 0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 4096) by (apply z4_srl_lt; z4uzm);
            let v := fresh "v" in set (v := bv_unsigned (edenot E (EAlu ALU_SRL x s))) in *; clearbody v
        end;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
        first [lia | Z.div_mod_to_equations; lia]
      end
  end.

Lemma z4_srl_ltt : forall E x s t, 1 <= t <= 12 -> bv_unsigned (edenot E s) mod 64 = 64 - t ->
  0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 2^t.
Proof.
  intros E x s t HT HS.
  assert (RX : bv_unsigned (edenot E x) < 2^64)
    by (pose proof (bv_unsigned_in_range _ (edenot E x)); unfold bv_modulus in *; lia).
  pose proof (bv_unsigned_in_range _ (edenot E x)) as [RX0 _].
  cbn [edenot]. rewrite u_srl64. rewrite HS.
  split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  rewrite <- Z.pow_add_r by lia. replace (64 - t + t) with 64 by lia. exact RX.
Qed.

Ltac z4xbt :=
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
            match goal with HT : 1 <= ?t <= ?h |- _ =>
              assert (HV : 0 <= bv_unsigned (edenot E (EAlu ALU_SRL x s)) < 2^t)
                by (apply (z4_srl_ltt E x s t); [lia | z4uzm]) end;
            let v := fresh "v" in set (v := bv_unsigned (edenot E (EAlu ALU_SRL x s))) in *; clearbody v
        end;
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
        first [lia | Z.div_mod_to_equations; lia]
      end
  end.

Ltac z4apz :=
  z4ez; rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?Z.mod_small by lia;
  match goal with H : KXGoM.apart _ _ _ _ |- _ =>
    let H' := fresh "AP" in pose proof H as H'; unfold KXGoM.apart in H'; lia end.

Ltac z4shd :=
  lazymatch goal with
  | |- flat ?E (SA (EAlu ALU_SRL ?X (ELit 3)) ?O) _ /\ flat ?E (SA ?B ?k) _ /\ _ =>
      apply (z4_shd_ap E X B O k); [ first [z4xb | z4xbt] | lia | lia | z4uz | z4uz | z4apz ]
  end.

Ltac z4brt :=
  lazymatch goal with
  | |- branch_taken BC_GEU (edenot ?E ?D) (edenot ?E (EMd M_MUL (ELit 4) (EAlu ALU_SRL ?X ?Y))) = true =>
      apply (z4_br_tix E D X Y); z4uzm
  | |- branch_taken BC_EQ (edenot ?E (EAlu ALU_SRL (EAlu ALU_ADD ?K (EAlu ALU_SRL ?X ?Y)) (ELit 62))) (edenot ?E (ELit 0)) = true =>
      apply (z4_br_sh E K X Y); z4uzm
  end.

Lemma z4_nth_firstn : forall {X} (l : list X) (N k : nat), (k < N)%nat -> nth_error (firstn N l) k = nth_error l k.
Proof.
  intros X l. induction l as [|x l IH]; intros N k H; destruct N as [|N]; try lia; destruct k as [|k]; simpl; try reflexivity.
  all: apply IH; lia.
Qed.

Lemma z4_x2tab_pure : forall cells tl hb, x2_table_ok cells tl -> tl <= hb < 256 ->
  forall i lo hi, 0 <= i < 4 * 2^tl -> find_field (i mod 4) [(2, 0, hb); (3, 1, 2)] = Some (lo, hi) ->
  exists b, nth_error (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells)) (Z.to_nat i) = Some b /\ lo <= bv_unsigned b <= hi.
Proof.
  intros cells tl hb (TL & LEN & OK) HB i lo hi Hi HF.
  unfold FseNCount.Zlength in LEN.
  assert (KD : exists v j, i = 4 * v + j /\ 0 <= j < 4 /\ 0 <= v < 2^tl).
  { exists (i / 4), (i mod 4).
    split; [apply Z.div_mod; lia|]. split; [apply Z.mod_pos_bound; lia|].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  destruct KD as (v & j & Ek & Hj & Hv).
  assert (HM : i mod 4 = j).
  { rewrite Ek, Z.add_comm, Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia. }
  rewrite HM in HF.
  assert (LC : (Z.to_nat v < length cells)%nat) by lia.
  assert (NB : nth_error (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells)) (Z.to_nat i)
             = nth_error (x2_cellbytes (nth (Z.to_nat v) cells x2_default)) (Z.to_nat j)).
  { rewrite z4_nth_firstn by lia.
    replace (Z.to_nat i) with (4 * Z.to_nat v + Z.to_nat j)%nat by lia.
    apply x2_bytes'_nth; lia. }
  pose proof (OK v ltac:(lia)) as CO. unfold x2_cell_ok in CO. destruct CO as (_ & CNB & CLN).
  assert (JC : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct JC as [-> | [-> | [-> | ->]]]; cbn in HF; try discriminate HF; injection HF as E1 E2; subst lo hi.
  - assert (B2 : nth_error (x2_cellbytes (nth (Z.to_nat v) cells x2_default)) (Z.to_nat 2)
                 = Some (Z_to_bv 8 (x2_nbBits (nth (Z.to_nat v) cells x2_default)))) by reflexivity.
    rewrite B2 in NB. rewrite NB.
    eexists; split; [reflexivity|].
    rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - assert (B3 : nth_error (x2_cellbytes (nth (Z.to_nat v) cells x2_default)) (Z.to_nat 3)
                 = Some (Z_to_bv 8 (x2_len (nth (Z.to_nat v) cells x2_default)))) by reflexivity.
    rewrite B3 in NB. rewrite NB.
    eexists; split; [reflexivity|].
    rewrite Z_to_bv_unsigned, bv_wrap_small; [lia|]. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma z4_x2tab_fact_gen : forall mm A cells tl, x2_table_ok cells tl ->
  bytes_at bsegs mm A (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells)) ->
  ztab_fact bsegs mm A (4 * 2^tl) 4 [(2, 0, 12); (3, 1, 2)].
Proof.
  intros mm A cells tl TOK HB.
  pose proof TOK as (TL & LEN & _). unfold FseNCount.Zlength in LEN.
  assert (TL12 : 1 <= tl <= 12) by exact TL.
  eapply ztab_fact_bytes_at; [exact HB | |].
  - rewrite length_firstn, x2_bytes'_length. lia.
  - intros i lo hi Hi HF. exact (z4_x2tab_pure cells tl 12 TOK ltac:(lia) i lo hi Hi HF).
Qed.

Section CANSEC1. Context {rc : runConstT}.

Lemma z4ctx_facts : forall AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk,
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk -> 1 <= dcap ->
  AIMG_HI <= DST /\ DST + dcap + 8 <= 2^47 /\ dcap < 2^32 /\ AIMG_HI <= DT /\ DT + 12 <= 2^47 /\
  (0 < zlen src -> AIMG_HI <= SS /\ SS + zlen src + 8 <= 2^47) /\
  ATOP + 8192 <= bv_unsigned sp /\ bv_unsigned sp < 2^64 /\ rng RNG (bv_unsigned sp - 400) 400.
Proof.
  intros AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk C D1.
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof (bv_unsigned_in_range _ sp) as SPR. unfold bv_modulus in SPR.
  assert (BD : AIMG_HI <= DST /\ DST + dcap + 8 <= 2^47).
  { destruct DSTF as [(_ & E)|(pb & HB1)]; [lia|].
    pose proof (ablk_lin _ _ (ABL _ HB1)) as A. cbn [ab_addr ab_size] in A. lia. }
  assert (BT : AIMG_HI <= DT /\ DT + 12 <= 2^47).
  { pose proof (ablk_lin _ _ (ABL _ HDT)) as A. cbn [ab_addr ab_size] in A.
    unfold DTABLE_BYTES, HufHarness.DT_BYTES in A. pose proof (Z.pow_nonneg 2 mtl ltac:(lia)). lia. }
  assert (BS : 0 < zlen src -> AIMG_HI <= SS /\ SS + zlen src + 8 <= 2^47).
  { intros HN. destruct (SRCB HN) as (p & HS & L1 & L2).
    pose proof (ablk_lin _ _ (ABL _ HS)) as A. cbn [ab_addr ab_size] in A. lia. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BS|].
  split; [lia|]. split; [lia|].
  eapply rng_sub; [exact WSK | lia | lia].
Qed.

Lemma z4ctx_dt_top : forall AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk,
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk -> 0 <= tl ->
  DT + 4 + 4 * 2^tl + 8 <= 2^47.
Proof.
  intros AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk C HT0.
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & _).
  pose proof (ablk_lin _ _ (ABL _ HDT)) as A. cbn [ab_addr ab_size] in A.
  unfold DTABLE_BYTES, HufHarness.DT_BYTES in A.
  pose proof (Z.pow_le_mono_r 2 tl mtl ltac:(lia) TLM). lia.
Qed.

Lemma z4ctx_dst_sb : forall AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk,
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk -> 1 <= dcap ->
  KXGoM.apart DST dcap AZ4_SB (2^44).
Proof.
  intros AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk C D1.
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & _).
  destruct DSTF as [(_ & E)|(pb & HB1)]; [lia|].
  pose proof (ABL _ HB1) as A. cbn [ab_addr ab_size] in A.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  unfold ablk, AIMG_HI, KLS, KXGoM.apart, AZ4_SB in *. lia.
Qed.


Lemma z4_bytes_sub : forall m A (src : list Z) O Lk,
  bytes_at bsegs m A (map (Z_to_bv 8) src) -> 0 <= O -> 0 <= Lk -> O + Lk <= zlen src ->
  bytes_at bsegs m (A + O) (map (Z_to_bv 8) (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))).
Proof.
  intros m A src O Lk H O0 L0 OL.
  rewrite <- (firstn_skipn (Z.to_nat O) src), map_app in H.
  apply bytes_at_app in H as [_ H].
  rewrite <- (firstn_skipn (Z.to_nat Lk) (skipn (Z.to_nat O) src)), map_app in H.
  apply bytes_at_app in H as [H _].
  rewrite length_map, length_firstn in H.
  replace (A + O) with (A + Z.of_nat (Nat.min (Z.to_nat O) (length src))) by lia.
  exact H.
Qed.

Lemma z4_len_sub : forall (src : list Z) O Lk, 0 <= O -> 0 <= Lk -> O + Lk <= zlen src ->
  zlen (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src)) = Lk.
Proof. intros src O Lk O0 L0 OL. rewrite length_firstn, length_skipn. lia. Qed.

Lemma z4_src_pre : forall AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk (mm : amem) O Lk,
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  1 <= dcap -> 0 <= O -> 1 <= Lk -> O + Lk <= zlen src ->
  bytes_at bsegs mm SS (map (Z_to_bv 8) src) -> munch [(lo, bv_unsigned sp); (DST, DST + dcap)] m0 mm ->
  bytes_at bsegs mm (SS + O) (map (Z_to_bv 8) (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))) /\
  zlen (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src)) = Lk /\
  unpoisoned mm (SS + O) (SS + O + Lk) /\ rng RNG (SS + O) Lk /\
  SBL mod 8 = 0 /\ 0 <= SBL /\ SBL <= SS + O /\ SS + O + Lk <= SBL + (SBH - SBL) /\
  rng RNG (shad SBL) (shlen (SBH - SBL + 7)) /\
  4096 <= SS /\ SS + O + Lk <= 2^47 /\ SS + O + Lk + 400 <= bv_unsigned sp.
Proof.
  intros AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm O Lk C D1 O0 L1 OL BSS MU.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  set (SP := bv_unsigned sp) in *.
  assert (NZ : 0 < zlen src) by lia.
  destruct (SRCB NZ) as (psb & HSB & SB1 & SB2).
  destruct (hb_unpoisoned AI L RNG st LB m0 psb SBL (SBH - SBL) AH HSB) as (SU & SA16 & SN1 & SAB & SAT & SRG & SSH & SWR).
  destruct (FSS NZ) as (FS1 & FS2).
  pose proof (ablk_lin _ _ SAB) as SAL.
  destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
  pose proof (ablk_lin _ _ (ABL _ HDB)) as HDL. cbn [ab_addr ab_size] in HDL.
  pose proof (ablk_lin _ _ (ABL _ HDT)) as HTL. cbn [ab_addr ab_size] in HTL.
  pose proof (ablk_disj_band _ _ (ABL _ HDB)) as HDB2. cbn [ab_addr ab_size] in HDB2.
  destruct RCL as (SHC & RLT).
  pose proof (shclean_hull _ _ _ _ _ SHC) as (H1 & H2 & H3 & H4 & H5 & H6).
  assert (SPK : SP <= KEND) by lia.
  pose proof (z4_len_sub src O Lk O0 ltac:(lia) OL) as LBS.
  split; [apply z4_bytes_sub; [exact BSS | lia | lia | lia]|].
  split; [exact LBS|].
  split.
  { eapply unpoisoned_munch; [| exact MU |].
    - eapply unpoisoned_sub; [exact SU | lia | lia].
    - cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, KEND in *. atop_facts.
      pose proof (ablk_disj_band _ _ SAB) as SDB2. unfold KLS in *. Z.div_mod_to_equations; lia. }
  split; [eapply rng_sub; [exact SRG | lia | lia]|].
  split; [clear -SA16; Z.div_mod_to_equations; lia|].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact SSH|].
  unfold AIMG_HI in FS1. lia.
Qed.

Lemma z4_body_pre : forall AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk (mm : amem),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  1 <= dcap -> munch [(lo, bv_unsigned sp); (DST, DST + dcap)] m0 mm ->
  zlen cbs = 4 * 2^tl /\ unpoisoned mm (DT + 4) (DT + 4 + 4 * 2^tl) /\ rng RNG (DT + 4) (4 * 2^tl) /\
  unpoisoned mm DST (DST + dcap) /\ rng RNG DST dcap /\
  DT mod 8 = 0 /\ 0 <= DT /\ DT + 4 + 4 * 2^tl <= DT + DTABLE_BYTES mtl /\ rng RNG (shad DT) (shlen (DTABLE_BYTES mtl + 7)) /\
  DST mod 8 = 0 /\ 0 <= DST /\ rng RNG (shad DST) (shlen (dcap + 7)) /\
  KXGoM.apart DST dcap (bv_unsigned sp + -400) 400 /\ KXGoM.apart (DT + 4) (4 * 2^tl) (bv_unsigned sp + -400) 400 /\
  KXGoM.apart DST dcap (DT + 4) (4 * 2^tl) /\ KXGoM.apart DST dcap AZ4_SB (2^44) /\
  (forall hb i fl fh, tl <= hb < 256 -> 0 <= i < 4 * 2^tl -> find_field (i mod 4) [(2, 0, hb); (3, 1, 2)] = Some (fl, fh) ->
     exists b, nth_error cbs (Z.to_nat i) = Some b /\ fl <= bv_unsigned b <= fh) /\
  4096 <= DST /\ DST + dcap <= 2^47 /\ dcap < 2^32 /\ 4096 <= DT <= 2^47 /\ DT + 4 + 4 * 2^tl + 8 <= 2^47 /\
  2^46 <= bv_unsigned sp <= 2^47 /\ 1 <= tl <= 12 /\ 2 <= 2^tl <= 4096.
Proof.
  intros AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm C D1 MU.
  pose proof C as C0.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  pose proof (z4ctx_dst_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1) as ASB.
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  pose proof TOK as (TL & TLEN & _). assert (TL12 : 1 <= tl <= 12) by exact TL.
  pose proof (z4ctx_dt_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C0 ltac:(lia)) as DTT.
  set (SP := bv_unsigned sp) in *.
  destruct (hb_unpoisoned AI L RNG st LB m0 pdt DT (DTABLE_BYTES mtl) AH HDT) as (TU & TA16 & TN1 & TAB & TAT & TRG & TSH & TWR).
  destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
  destruct (hb_unpoisoned AI L RNG st LB m0 pb DST dcap AH HDB) as (DU & DA16 & DN1 & DAB & DAT & DRG & DSH & DWR).
  assert (P1 : 2^1 <= 2^tl) by (apply Z.pow_le_mono_r; lia).
  assert (P12 : 2^tl <= 2^12) by (apply Z.pow_le_mono_r; lia).
  assert (PM : 2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia).
  change (2^1) with 2 in P1. change (2^12) with 4096 in P12.
  destruct RCL as (SHC & RLT).
  pose proof (shclean_hull _ _ _ _ _ SHC) as (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (ablk_disj_band _ _ DAB) as DDB2.
  pose proof (ablk_disj_band _ _ TAB) as TDB2.
  assert (SPK : SP <= KEND) by lia.
  assert (DTB : DTABLE_BYTES mtl = 4 * (1 + 2^mtl)) by reflexivity.
  split; [exact LCB|].
  split.
  { eapply unpoisoned_munch; [| exact MU |].
    - eapply unpoisoned_sub; [exact TU | lia | lia].
    - cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, KEND in *. atop_facts.
      unfold KLS in *. Z.div_mod_to_equations; lia. }
  split; [eapply rng_sub; [exact TRG | lia | lia]|].
  split.
  { eapply unpoisoned_munch; [exact DU | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, KEND in *. atop_facts.
    unfold KLS in *. Z.div_mod_to_equations; lia. }
  split; [exact DRG|].
  split; [clear -TA16; Z.div_mod_to_equations; lia|].
  unfold AIMG_HI in FD1, FD4.
  split; [lia|]. split; [lia|].
  split; [exact TSH|].
  split; [clear -DA16; Z.div_mod_to_equations; lia|].
  split; [lia|].
  split; [exact DSH|].
  split; [unfold KXGoM.apart; lia|].
  split; [unfold KXGoM.apart; lia|].
  split; [unfold KXGoM.apart; lia|].
  split; [exact ASB|].
  split; [intros hb i fl fh HB Hi HF; rewrite ECB; exact (z4_x2tab_pure cells tl hb TOK HB i fl fh Hi HF)|].
  unfold AIMG_HI, KEND in *. lia.
Qed.

Section Z4RL.
Hypothesis HRL : reload_int_stmtA AHUF_RELOADI.

Lemma z4_rl_pre : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (sp tp : word) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region)
    (mm : amem) (BDo O Lk pt b : Z) (c : word) (jp : list byte) (F : bvmap 5 word) (fc : bv 32) (gp : word)
    (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  1 <= dcap -> 0 <= O -> O + Lk <= zlen src -> -264 <= BDo <= -144 -> BDo mod 8 = 0 ->
  bytes_at bsegs mm SS (map (Z_to_bv 8) src) -> stk bsegs mm lo (bv_unsigned sp + -384) -> mem_inv bsegs mm ->
  munch [(lo, bv_unsigned sp); (DST, DST + dcap)] m0 mm -> wmono bsegs m0 mm ->
  rw_cells bsegs mm (bv_unsigned sp + BDo) (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
  0 <= b <= 64 -> 8 <= pt -> pt + 8 <= Lk ->
  (forall (m' : amem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word),
     munch [(bv_unsigned sp + BDo, bv_unsigned sp + BDo + 40); (bv_unsigned sp + -384 - 16, bv_unsigned sp + -384)] mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp + -384) ->
     rw_cells bsegs m' (bv_unsigned sp + BDo) (BD4A (Z_to_bv 64 (le64v (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src)) (pt - b / 8))) (Z_to_bv 64 (b mod 8)) jp
             (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp t0 t1 t2 y8 y9 (Z_to_bv 64 (bv_unsigned sp + BDo))
                              a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (ret_pc y1) fc None m' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (bv_unsigned sp + BDo))
                              y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm BDo O Lk pt b c jp F fc gp
    y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 C D1 O0 OL BO1 BO2 BSS STK MI MU WM B1 B0 PT PL K.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  set (SP := bv_unsigned sp) in *.
  assert (NZ : 0 < zlen src) by lia.
  destruct (SRCB NZ) as (psb & HSB & SB1 & SB2).
  destruct (hb_unpoisoned AI L RNG st LB m0 psb SBL (SBH - SBL) AH HSB) as (SU & SA16 & SN1 & SAB & SAT & SRG & SSH & SWR).
  destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
  pose proof (ablk_lin _ _ (ABL _ HDB)) as HDL. cbn [ab_addr ab_size] in HDL.
  pose proof (ablk_lin _ _ (ABL _ HDT)) as HTL. cbn [ab_addr ab_size] in HTL.
  destruct RCL as (SHC & RLT).
  pose proof (shclean_hull _ _ _ _ _ SHC) as (H1 & H2 & H3 & H4 & H5 & H6).
  pose proof (z4_len_sub src O Lk O0 ltac:(lia) OL) as LBS.
  pose proof (ablk_disj_band _ _ (ABL _ HDB)) as HDB2. cbn [ab_addr ab_size] in HDB2.
  assert (SPK : SP <= KEND) by lia.
  assert (ART : artcells mm).
  { pose proof (AI_rtcells AI L RNG st LB m0 AH) as A0. unfold artcells in *.
    repeat match type of A0 with _ /\ _ => let H := fresh "A" in destruct A0 as [H A0] end.
    repeat (split; [eapply rw_cells_transport; [eassumption | exact MU | exact WM |];
                    cbn [disjoint_from cells_size csize]; unfold AIMG_HI in *; atop_facts; lia |]).
    eapply rw_cells_transport; [eassumption | exact MU | exact WM |];
      cbn [disjoint_from cells_size csize]; unfold AIMG_HI in *; atop_facts; lia. }
  assert (UBD : unpoisoned mm (SP + BDo) (SP + BDo + 40)).
  { eapply unpoisoned_munch; [| exact MU |].
    - eapply unpoisoned_sub; [eapply shclean_unpoisoned; exact SHC | lia | lia].
    - cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, KEND, KLS in *. atop_facts.
      Z.div_mod_to_equations; lia. }
  assert (USS : unpoisoned mm (SS + O) (SS + O + Lk)).
  { eapply unpoisoned_munch; [| exact MU |].
    - eapply unpoisoned_sub; [exact SU | lia | lia].
    - cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, AIMG_HI, KEND in *. atop_facts.
      pose proof (ablk_disj_band _ _ SAB) as SDB2. unfold KLS in *. Z.div_mod_to_equations; lia. }
  eapply (evtF_cut bsegs RNG _ Q).
  - apply (HRL RNG y1 gp tp y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
             F fc mm (SP + -384) lo (SP + BDo) (SS + O) b pt c jp (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src))).
    + exact B1.
    + apply z4_bytes_sub; [exact BSS | lia | lia | lia].
    + pose proof BYS as BY2. rewrite <- (firstn_skipn (Z.to_nat O) src) in BY2. apply Forall_app in BY2 as [_ BY2].
      rewrite <- (firstn_skipn (Z.to_nat Lk) (skipn (Z.to_nat O) src)) in BY2. apply Forall_app in BY2 as [BY2 _]. exact BY2.
    + lia.
    + lia.
    + unfold KEND in SPK. lia.
    + rewrite LBS. eapply ablk_sub; [exact SAB | lia | lia].
    + exact B0.
    + exact PT.
    + rewrite LBS. lia.
    + exact STK.
    + exact LOA.
    + unfold RELOADI_STACK. lia.
    + exact MI.
    + exact ART.
    + exact UBD.
    + rewrite LBS. exact USS.
    + eapply rng_sub; [exact FRS | lia | lia].
    + unfold rrng in RRS. eapply rng_sub; [exact RRS | |]; rewrite !shad_div; Z.div_mod_to_equations; lia.
    + rewrite LBS. eapply rng_sub; [exact SRG | lia | lia].
    + rewrite LBS. eapply rng_sub; [exact SSH | |]; unfold nshad, shlen; rewrite !shad_div, ?Z.shiftr_div_pow2 by lia;
        Z.div_mod_to_equations; lia.
    + unfold RELOADI_STACK. eapply rng_sub; [exact FRS | lia | lia].
    + exact WIM.
    + exact WIS.
  - intros ms' (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & m' & EQ & MU' & WM' & MI' & STK' & RW').
    subst ms'. unfold RELOADI_STACK in MU'. exact (K m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 MU' WM' MI' STK' RW').
Qed.

Lemma z4sf_rebuild : forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region)
    (mm m' : amem) (BDo : Z) (spl bd4 bd3 bd2 bd1 bd4' bd3' bd2' bd1' : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  1 <= dcap -> 0 < zlen src -> -264 <= BDo <= -144 ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm spl bd4 bd3 bd2 bd1 ->
  munch [(bv_unsigned sp + BDo, bv_unsigned sp + BDo + 40); (bv_unsigned sp + -384 - 16, bv_unsigned sp + -384)] mm m' -> wmono bsegs mm m' -> mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp + -384) ->
  rw_cells bsegs m' (bv_unsigned sp + -264) bd4' -> cells_size bd4' = 40%nat ->
  rw_cells bsegs m' (bv_unsigned sp + -224) bd3' -> cells_size bd3' = 40%nat ->
  rw_cells bsegs m' (bv_unsigned sp + -184) bd2' -> cells_size bd2' = 40%nat ->
  rw_cells bsegs m' (bv_unsigned sp + -144) bd1' -> cells_size bd1' = 40%nat ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs m' spl bd4' bd3' bd2' bd1'.
Proof.
  intros AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells cbs pdt
    SBL SBH rstk mm m' BDo spl bd4 bd3 bd2 bd1 bd4' bd3' bd2' bd1' C D1 NZ0 BO1 FR MU' WM' MI' STK' N4 N4S N3 N3S N2 N2S N1 N1S.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  destruct FR as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  set (SP := bv_unsigned sp) in *.
  assert (NZ : 0 < zlen src -> SS + zlen src <= ATOP).
  { intros NZ. destruct (SRCB NZ) as (psb & HSB & SB1 & SB2).
    pose proof (ablk_lin _ _ (ABL _ HSB)) as A. cbn [ab_addr ab_size] in A. lia. }
  destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
  pose proof (ablk_lin _ _ (ABL _ HDB)) as HDL. cbn [ab_addr ab_size] in HDL.
  pose proof (ablk_lin _ _ (ABL _ HDT)) as HTL. cbn [ab_addr ab_size] in HTL.
  assert (DTB : DT + 4 + zlen cbs <= ATOP).
  { rewrite LCB. unfold DTABLE_BYTES, HufHarness.DT_BYTES in HTL.
    pose proof (Z.pow_le_mono_r 2 tl mtl ltac:(lia) ltac:(lia)). lia. }
  destruct BUF as (buf & BU & BL).
  split; [exists buf; split; [eapply u8arr_transport; [exact BU | exact MU' | exact WM' |] | exact BL] |].
  { rewrite length_map, BL. cbn [disjoint_from]. lia. }
  split; [eapply bytes_at_transport; [exact BSS | exact MU' |]; rewrite length_map; cbn [disjoint_from];
          specialize (NZ NZ0); lia |].
  split; [eapply bytes_at_transport; [exact BDT4 | exact MU' |]; cbn [disjoint_from]; lia |].
  split; [eapply bytes_at_transport; [exact BDT | exact MU' |]; cbn [disjoint_from length]; lia |].
  split; [exact STK' |].
  split; [eapply rw_cells_transport; [exact SPL | exact MU' | exact WM' |]; rewrite SPLS; cbn [disjoint_from]; lia |].
  split; [exact SPLS |].
  split; [exact N4 |]. split; [exact N4S |]. split; [exact N3 |]. split; [exact N3S |].
  split; [exact N2 |]. split; [exact N2S |]. split; [exact N1 |]. split; [exact N1S |].
  split; [eapply rw_cells_transport; [exact FRM | exact MU' | exact WM' |]; cbn [disjoint_from cells_size csize]; lia |].
  split; [exact MI' |].
  split.
  - eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']].
    intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia.
  - eapply wmono_trans; [exact WM | exact WM'].
Qed.

Lemma z4sf_rebuild3 : forall (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region)
    (mm m' : amem) (BDo : Z) (spl bd4 bd3 bd2 bd1 spl' bd4' bd3' bd2' bd1' : list cell),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  1 <= dcap -> 0 < zlen src -> -264 <= BDo <= -144 ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm spl bd4 bd3 bd2 bd1 ->
  munch [(bv_unsigned sp + -384, bv_unsigned sp + -264); (bv_unsigned sp + BDo, bv_unsigned sp + BDo + 40); (DST, DST + dcap)] mm m' ->
  wmono bsegs mm m' -> mem_inv bsegs m' ->
  (exists buf, u8arr bsegs m' DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap) ->
  rw_cells bsegs m' (bv_unsigned sp + -384) spl' -> cells_size spl' = 120%nat ->
  rw_cells bsegs m' (bv_unsigned sp + -264) bd4' -> cells_size bd4' = 40%nat ->
  rw_cells bsegs m' (bv_unsigned sp + -224) bd3' -> cells_size bd3' = 40%nat ->
  rw_cells bsegs m' (bv_unsigned sp + -184) bd2' -> cells_size bd2' = 40%nat ->
  rw_cells bsegs m' (bv_unsigned sp + -144) bd1' -> cells_size bd1' = 40%nat ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs m' spl' bd4' bd3' bd2' bd1'.
Proof.
  intros AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells cbs pdt
    SBL SBH rstk mm m' BDo spl bd4 bd3 bd2 bd1 spl' bd4' bd3' bd2' bd1' C D1 NZ0 BO1 FR MU' WM' MI' BUF' SP' SPS'
    N4 N4S N3 N3S N2 N2S N1 N1S.
  pose proof (z4ctx_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C D1)
    as (FD1 & FD2 & FD3 & FD4 & FD5 & FSS & FSP1 & FSP2 & FRS).
  destruct C as (AH & NFK & ABL & MTL & TLM & HDT & TOK & ECB & LCB & DSTF & DC & BYS & NSM & S16 & SRCB & DJ1 & DJ2 & DJ3
                 & LOA & LOS & SPT & SP16 & TPA & HINV & RCL & RLO & RHI & RRL & RRS & WSK & WIM & WIS & WFS).
  destruct FR as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  set (SP := bv_unsigned sp) in *.
  assert (NZ : 0 < zlen src -> SS + zlen src <= ATOP).
  { intros NZ. destruct (SRCB NZ) as (psb & HSB & SB1 & SB2).
    pose proof (ablk_lin _ _ (ABL _ HSB)) as A. cbn [ab_addr ab_size] in A. lia. }
  destruct DSTF as [(E1 & E2)|(pb & HDB)]; [lia|].
  pose proof (ablk_lin _ _ (ABL _ HDB)) as HDL. cbn [ab_addr ab_size] in HDL.
  pose proof (ablk_lin _ _ (ABL _ HDT)) as HTL. cbn [ab_addr ab_size] in HTL.
  assert (DTB : DT + 4 + zlen cbs <= ATOP).
  { rewrite LCB. unfold DTABLE_BYTES, HufHarness.DT_BYTES in HTL.
    pose proof (Z.pow_le_mono_r 2 tl mtl ltac:(lia) ltac:(lia)). lia. }
  assert (DTB2 : 4 + zlen cbs <= DTABLE_BYTES mtl).
  { rewrite LCB. unfold DTABLE_BYTES, HufHarness.DT_BYTES.
    pose proof (Z.pow_le_mono_r 2 tl mtl ltac:(lia) ltac:(lia)). lia. }
  split; [exact BUF' |].
  split; [eapply bytes_at_transport; [exact BSS | exact MU' |]; rewrite length_map; cbn [disjoint_from];
          specialize (NZ NZ0); lia |].
  split; [eapply bytes_at_transport; [exact BDT4 | exact MU' |]; cbn [disjoint_from]; lia |].
  split; [eapply bytes_at_transport; [exact BDT | exact MU' |]; cbn [disjoint_from length]; lia |].
  split; [eapply stk_transport_disjoint; [exact STK | exact MU' | exact WM' |]; cbn [disjoint_from]; lia |].
  split; [exact SP' |].
  split; [exact SPS' |].
  split; [exact N4 |]. split; [exact N4S |]. split; [exact N3 |]. split; [exact N3S |].
  split; [exact N2 |]. split; [exact N2S |]. split; [exact N1 |]. split; [exact N1S |].
  split; [eapply rw_cells_transport; [exact FRM | exact MU' | exact WM' |]; cbn [disjoint_from cells_size csize]; lia |].
  split; [exact MI' |].
  split.
  - eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU']].
    intros x HX. cbn [outside] in *. repeat split; try exact I; intros ?; lia.
  - eapply wmono_trans; [exact WM | exact WM'].
Qed.

Lemma z4_rl_call1 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region)
    (mm : amem) (spl bd4 bd3 bd2 : list cell) (O Lk pt b : Z) (c : word) (jp : list byte)
    (F : bvmap 5 word) (fc : bv 32) (gp : word)
    (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  1 <= dcap -> 0 <= O -> O + Lk <= zlen src ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm spl
       bd4 bd3 bd2 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
  0 <= b <= 64 -> 8 <= pt -> pt + 8 <= Lk ->
  (forall (mm' : amem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word),
     Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm' spl
       bd4 bd3 bd2 (BD4A (Z_to_bv 64 (le64v (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src)) (pt - b / 8))) (Z_to_bv 64 (b mod 8)) jp
             (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp t0 t1 t2 y8 y9 (Z_to_bv 64 (bv_unsigned sp + -144))
                              a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (ret_pc y1) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (bv_unsigned sp + -144))
                              y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells cbs pdt
    SBL SBH rstk mm spl X1 X2 X3 O Lk pt b c jp F fc gp
    y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 C D1 O0 OL FR B0 PT PL K.
  pose proof FR as FR0.
  destruct FR0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  eapply (z4_rl_pre Q AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm (-144));
    [exact C | exact D1 | exact O0 | exact OL | lia | reflexivity | exact BSS | exact STK | exact MI | exact MU | exact WM
    | exact B1 | exact B0 | exact PT | exact PL |].
  intros m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 MU' WM' MI' STK' RW'.
  apply (K m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7).
  eapply (z4sf_rebuild AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells
            cbs pdt SBL SBH rstk mm m' (-144)); [exact C | exact D1 | lia | lia | exact FR | exact MU' | exact WM' | exact MI' | exact STK' | ..].
  - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]; rewrite B4S; cbn [disjoint_from]; lia.
  - exact B4S.
  - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]; rewrite B3S; cbn [disjoint_from]; lia.
  - exact B3S.
  - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]; rewrite B2S; cbn [disjoint_from]; lia.
  - exact B2S.
  - exact RW'.
  - reflexivity.
Qed.

Lemma z4_rl_call2 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region)
    (mm : amem) (spl bd4 bd3 bd1 : list cell) (O Lk pt b : Z) (c : word) (jp : list byte)
    (F : bvmap 5 word) (fc : bv 32) (gp : word)
    (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  1 <= dcap -> 0 <= O -> O + Lk <= zlen src ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm spl
       bd4 bd3 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
  0 <= b <= 64 -> 8 <= pt -> pt + 8 <= Lk ->
  (forall (mm' : amem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word),
     Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm' spl
       bd4 bd3 (BD4A (Z_to_bv 64 (le64v (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src)) (pt - b / 8))) (Z_to_bv 64 (b mod 8)) jp
             (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd1 ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp t0 t1 t2 y8 y9 (Z_to_bv 64 (bv_unsigned sp + -184))
                              a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (ret_pc y1) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (bv_unsigned sp + -184))
                              y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells cbs pdt
    SBL SBH rstk mm spl X1 X2 X3 O Lk pt b c jp F fc gp
    y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 C D1 O0 OL FR B0 PT PL K.
  pose proof FR as FR0.
  destruct FR0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  eapply (z4_rl_pre Q AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm (-184));
    [exact C | exact D1 | exact O0 | exact OL | lia | reflexivity | exact BSS | exact STK | exact MI | exact MU | exact WM
    | exact B2 | exact B0 | exact PT | exact PL |].
  intros m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 MU' WM' MI' STK' RW'.
  apply (K m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7).
  eapply (z4sf_rebuild AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells
            cbs pdt SBL SBH rstk mm m' (-184)); [exact C | exact D1 | lia | lia | exact FR | exact MU' | exact WM' | exact MI' | exact STK' | ..].
  - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]; rewrite B4S; cbn [disjoint_from]; lia.
  - exact B4S.
  - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]; rewrite B3S; cbn [disjoint_from]; lia.
  - exact B3S.
  - exact RW'.
  - reflexivity.
  - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]; rewrite B1S; cbn [disjoint_from]; lia.
  - exact B1S.
Qed.

Lemma z4_rl_call3 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region)
    (mm : amem) (spl bd4 bd2 bd1 : list cell) (O Lk pt b : Z) (c : word) (jp : list byte)
    (F : bvmap 5 word) (fc : bv 32) (gp : word)
    (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  1 <= dcap -> 0 <= O -> O + Lk <= zlen src ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm spl
       bd4 (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd2 bd1 ->
  0 <= b <= 64 -> 8 <= pt -> pt + 8 <= Lk ->
  (forall (mm' : amem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word),
     Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm' spl
       bd4 (BD4A (Z_to_bv 64 (le64v (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src)) (pt - b / 8))) (Z_to_bv 64 (b mod 8)) jp
             (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd2 bd1 ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp t0 t1 t2 y8 y9 (Z_to_bv 64 (bv_unsigned sp + -224))
                              a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (ret_pc y1) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (bv_unsigned sp + -224))
                              y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells cbs pdt
    SBL SBH rstk mm spl X1 X2 X3 O Lk pt b c jp F fc gp
    y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 C D1 O0 OL FR B0 PT PL K.
  pose proof FR as FR0.
  destruct FR0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  eapply (z4_rl_pre Q AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm (-224));
    [exact C | exact D1 | exact O0 | exact OL | lia | reflexivity | exact BSS | exact STK | exact MI | exact MU | exact WM
    | exact B3 | exact B0 | exact PT | exact PL |].
  intros m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 MU' WM' MI' STK' RW'.
  apply (K m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7).
  eapply (z4sf_rebuild AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells
            cbs pdt SBL SBH rstk mm m' (-224)); [exact C | exact D1 | lia | lia | exact FR | exact MU' | exact WM' | exact MI' | exact STK' | ..].
  - eapply rw_cells_transport; [exact B4 | exact MU' | exact WM' |]; rewrite B4S; cbn [disjoint_from]; lia.
  - exact B4S.
  - exact RW'.
  - reflexivity.
  - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]; rewrite B2S; cbn [disjoint_from]; lia.
  - exact B2S.
  - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]; rewrite B1S; cbn [disjoint_from]; lia.
  - exact B1S.
Qed.

Lemma z4_rl_call4 : forall (Q : machine_state -> Prop) (AI : AMallocIface) (L : alayout) (RNG : footprint) (st : astate)
    (LB : list ablock) (rng_fs : alayout -> footprint -> Prop)
    (ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : amem)
    (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte) (pdt : aptr)
    (SBL SBH : Z) (rstk : region)
    (mm : amem) (spl bd3 bd2 bd1 : list cell) (O Lk pt b : Z) (c : word) (jp : list byte)
    (F : bvmap 5 word) (fc : bv 32) (gp : word)
    (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
  z4ctx AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk ->
  1 <= dcap -> 0 <= O -> O + Lk <= zlen src ->
  Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm spl
       (BD4A c (Z_to_bv 64 b) jp (Z_to_bv 64 (SS + O + pt)) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd3 bd2 bd1 ->
  0 <= b <= 64 -> 8 <= pt -> pt + 8 <= Lk ->
  (forall (mm' : amem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 : word),
     Z4SF ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm' spl
       (BD4A (Z_to_bv 64 (le64v (firstn (Z.to_nat Lk) (skipn (Z.to_nat O) src)) (pt - b / 8))) (Z_to_bv 64 (b mod 8)) jp
             (Z_to_bv 64 (SS + O + (pt - b / 8))) (Z_to_bv 64 (SS + O)) (Z_to_bv 64 (SS + O + 8))) bd3 bd2 bd1 ->
     evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp t0 t1 t2 y8 y9 (Z_to_bv 64 (bv_unsigned sp + -264))
                              a1 a2 a3 a4 a5 a6 a7 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (ret_pc y1) fc None mm' (seg_rom bsegs))) ->
  evtF bsegs RNG Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -384)) gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 (bv_unsigned sp + -264))
                              y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 AHUF_RELOADI) fc None mm (seg_rom bsegs)).
Proof.
  intros Q AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells cbs pdt
    SBL SBH rstk mm spl X1 X2 X3 O Lk pt b c jp F fc gp
    y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 C D1 O0 OL FR B0 PT PL K.
  pose proof FR as FR0.
  destruct FR0 as (BUF & BSS & BDT4 & BDT & STK & SPL & SPLS & B4 & B4S & B3 & B3S & B2 & B2S & B1 & B1S & FRM & MI & MU & WM).
  eapply (z4_rl_pre Q AI L RNG st LB rng_fs sp tp m0 DST dcap SS DT mtl tl lo src cells cbs pdt SBL SBH rstk mm (-264));
    [exact C | exact D1 | exact O0 | exact OL | lia | reflexivity | exact BSS | exact STK | exact MI | exact MU | exact WM
    | exact B4 | exact B0 | exact PT | exact PL |].
  intros m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 MU' WM' MI' STK' RW'.
  apply (K m' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7).
  eapply (z4sf_rebuild AI L RNG st LB rng_fs ra sp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cells
            cbs pdt SBL SBH rstk mm m' (-264)); [exact C | exact D1 | lia | lia | exact FR | exact MU' | exact WM' | exact MI' | exact STK' | ..].
  - exact RW'.
  - reflexivity.
  - eapply rw_cells_transport; [exact B3 | exact MU' | exact WM' |]; rewrite B3S; cbn [disjoint_from]; lia.
  - exact B3S.
  - eapply rw_cells_transport; [exact B2 | exact MU' | exact WM' |]; rewrite B2S; cbn [disjoint_from]; lia.
  - exact B2S.
  - eapply rw_cells_transport; [exact B1 | exact MU' | exact WM' |]; rewrite B1S; cbn [disjoint_from]; lia.
  - exact B1S.
Qed.

End Z4RL.

End CANSEC1.











