(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_stage2_numkit Sj_stage2_numkit2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition crs (t : list Z) : list Z := t ++ repeat 32%Z 64.

Lemma crs_blen : forall t, Z.of_nat (length (zbytes (crs t))) = (blen t + 64)%Z.
Proof. intros t. rewrite zbytes_length. unfold crs, blen. rewrite length_app, repeat_length. lia. Qed.

Lemma crs_bytes_ok : forall t, bytes_ok t -> bytes_ok (crs t).
Proof.
  intros t H. unfold bytes_ok, crs in *. apply Forall_app. split; [exact H|].
  apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. lia.
Qed.

Lemma Bc_lt : forall t q, (B (crs t) q <> 0)%Z -> (B (crs t) q <> 32)%Z -> (0 <= q)%Z -> (q < blen t)%Z.
Proof.
  intros t q H0 H32 Hq. destruct (Z_lt_dec q (blen t)) as [L|L]; [exact L|]. exfalso.
  unfold B, crs, blen in *.
  destruct (Nat.lt_ge_cases (Z.to_nat q) (length t + 64)) as [L2|L2].
  - rewrite app_nth2 in H32 by lia. apply H32. apply nth_repeat_lt. lia.
  - apply H0. apply nth_overflow. rewrite length_app, repeat_length. exact L2.
Qed.

Definition rtxt (E : s2env) : list Z := skipn (Z.to_nat (e_off E 0)) (e_bs E).
Lemma rtxt_blen : forall E, (0 <= e_off E 0 <= e_len E)%Z -> blen (rtxt E) = (e_len E - e_off E 0)%Z.
Proof. intros E H. unfold rtxt, blen in *. rewrite length_skipn. lia. Qed.
Lemma rtxt_ok : forall E, env_ok E -> bytes_ok (crs (rtxt E)).
Proof.
  intros E OK. apply crs_bytes_ok. pose proof (ok_bytes _ OK) as H. unfold bytes_ok, rtxt in *.
  rewrite <- (firstn_skipn (Z.to_nat (e_off E 0)) (e_bs E)) in H. apply Forall_app in H. exact (proj2 H).
Qed.

Lemma cp_read_at : forall (m : mem) A l i a,
  bytes_at asegs m A (zbytes l) -> (0 <= i < Z.of_nat (length (zbytes l)))%Z -> a = wa (A + i) ->
  ov_read_bytes asegs m a 1 = Some [Z_to_bv 8 (B l i)].
Proof.
  intros m A l i a H Hi ->. pose proof (zbytes_length l) as ZL.
  eapply (u8ro_read asegs m A (zbytes l) i); [exact H | | lia | reflexivity].
  unfold B. apply nth_error_zbytes. lia.
Qed.
Ltac s2_load_cp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 1] =>
      lazymatch goal with
      | H : bytes_at segs m ?A (zbytes ?l) |- _ =>
          let Ea := addr_expr a in
          let idx := strip_base Ea A in
          rewrite (cp_read_at m A l idx a H ltac:(lia) ltac:(unfold wa; f_equal; lia))
      end
  end;
  load_post.

Definition MEMIR (E : s2env) (CP : Z) (nxt : word) (sl : list cell) (sc : list (bool * Z)) (fc : bv 32) (m1 : mem) : Prop :=
  MEMI E nxt sl sc fc m1 /\ bytes_at asegs m1 CP (zbytes (crs (rtxt E))).
Definition cp_ok (E : s2env) (CP : Z) : Prop :=
  (0 < CP)%Z /\ (CP + blen (rtxt E) + 64 <= e_lo E)%Z /\ (CP + blen (rtxt E) + 64 <= e_TAPE E \/ e_TAPE E + 8 * e_tcap E <= CP)%Z.
Definition cp_shz (E : s2env) (CP : Z) : Prop :=
  forall m', munch (s2_W E) (e_m0 E) m' -> wmono asegs (e_m0 E) m' -> shz m' CP (blen (rtxt E) + 56).

Lemma shzr_cp : forall (m1 : mem) CP n x a, shz m1 CP n -> (CP <= x < CP + n)%Z -> a = wa (SHA x) ->
  ov_read_bytes asegs m1 a 1 = Some [Z_to_bv 8 0].
Proof. intros m1 CP n x a S Hx ->. rewrite shr3_div. apply S. exact Hx. Qed.
Ltac s2_load_shadow_cp :=
  match goal with
  | |- context [ov_read_bytes asegs ?m ?a 1] =>
      let Ea := addr_expr a in
      let x := lazymatch Ea with (Z.shiftr ?x 3 + 2147450880)%Z => x end in
      lazymatch goal with
      | SHZCh : cp_shz ?E ?CP, MUh : munch _ (e_m0 ?E) m, WMh : wmono asegs (e_m0 ?E) m |- _ =>
          lazymatch x with context [CP] => idtac end;
          rewrite (shzr_cp m CP _ x a (SHZCh m MUh WMh) ltac:(lia) ltac:(unfold wa; f_equal; lia))
      end
  end;
  load_post.

Ltac nz_lt_by tac ::= apply Bc_lt; [tac | tac | lia].
Ltac nopen H ::=
  let CPB := fresh "CPB" in
  destruct H as [H CPB]; s2_open_mem H;
  lazymatch type of CPB with bytes_at _ _ _ (zbytes (crs ?t)) =>
    let CBL := fresh "CBL" in pose proof (crs_blen t) as CBL;
    let CB0 := fresh "CB0" in assert (CB0 : (0 <= blen t)%Z) by (unfold blen; lia) end;

  match goal with OKh : env_ok ?E |- _ => let TC := fresh "HTC3" in assert (TC : (3 <= e_tcap E)%Z) by (pose proof (ok_tcap _ OKh); unfold blen in *; lia) end;

  match goal with HC : cp_ok _ _ |- _ => let C0 := fresh "HCP0" in let C1 := fresh "HCP1" in pose proof (proj1 HC) as C0; pose proof (proj1 (proj2 HC)) as C1 end.
Ltac nclose ::= split; [ ntape_norm; s2_close_mem0 | eassumption ].

Ltac r_tlia :=
  first [ tlia0 | (s2_pose_sep; tlia0)
        | (match goal with H : cp_ok _ _ |- _ => pose proof (proj2 (proj2 H)) end; first [ tlia0 | (s2_pose_sep; tlia0) ]) ].

Definition rdelA_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall err xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    (1 <= err < 64)%Z -> MEMX E fc m1 ->
    evt asegs Q (S2R E 0xbd5a4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) xs5 xs6 (Z_to_bv 64 (err)) (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
Ltac nexit0 KX ::=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ (Z_to_bv 64 0xbd5a4%Z) _ _ _ _) =>
      let v := greg_val R 23%Z in
      lazymatch v with Z_to_bv 64 ?e => eapply (KX e); [lia | s2_close_memx] end
  end.
Ltac nexit KX ::= ngrun_to 0xbd5a4%Z; nexit0 KX.
