(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac SFModel.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout Fz_kit Fz_chk Fz_fkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma sxb_small : forall k, 0 <= k < 128 -> sxb (Z_to_bv 8 k) = Z_to_bv 64 k.
Proof.
  intros k Hk. unfold sxb. f_equal. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128.
  rewrite (Z.mod_small k) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma land7_mod : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma acc_check_byte : forall (m : word -> option byte) p n X sz, acc asegs m p n -> 0 <= p -> p <= X -> X + sz <= p + n -> 1 <= sz -> X mod 8 + sz <= 8 ->
  exists k, ro_cells asegs m (X / 8 + 2147450880) [C1 (Z_to_bv 8 k)] /\ 0 <= k < 8 /\ (k = 0 \/ X mod 8 + sz - 1 < k).
Proof.
  intros m p n X sz HA P0 PX XN SZ AL.
  destruct (HA (X + sz - 1 - p) ltac:(lia)) as (b & HB & OK). replace (p + (X + sz - 1 - p)) with (X + sz - 1) in HB, OK by lia.
  pose proof (bv_unsigned_in_range 8 b) as RB. unfold bv_modulus in RB. change (2 ^ Z.of_N 8) with 256 in RB.
  pose proof (Z.div_mod X 8 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound X 8 ltac:(lia)) as MX.
  assert (ED : (X + sz - 1) / 8 = X / 8).
  { replace (X + sz - 1) with (X mod 8 + sz - 1 + X / 8 * 8) by lia. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (EM : (X + sz - 1) mod 8 = X mod 8 + sz - 1).
  { replace (X + sz - 1) with (X mod 8 + sz - 1 + X / 8 * 8) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  exists (bv_unsigned b). split.
  - unfold shad, SHB in HB. rewrite ED in HB.
    assert (E8 : Z_to_bv 8 (bv_unsigned b) = b) by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range). rewrite E8.
    unfold ro_cells, cells_at. cbn [cells_wf cells_bytes cbytes]. rewrite app_nil_r. split; [split; [reflexivity | exact I] | exact HB].
  - unfold sh_ok in OK. rewrite EM in OK. lia.
Qed.

(* [comment removed for export] *)
Ltac acc_now A :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      lazymatch type of A with
      | acc asegs m _ _ => constr:(A)
      | acc asegs ?m0 ?p ?n =>
          lazymatch goal with
          | MU : munch ?W m0 m, HW : sh_fp ?W |- _ => constr:(acc_munch_sh W m0 m p n A MU HW ltac:(sh_side) ltac:(sh_side))
          end
      end
  end.

(* [comment removed for export] *)
Ltac chk_cond :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  rewrite ?unsigned_lit by lia; rewrite ?signed_of_Z by lia;
  first [ reflexivity
        | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.leb_le; lia | apply Z.leb_gt; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
        | apply (proj2 (Bool.negb_true_iff _)); first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia | apply Z.leb_gt; lia]
        | apply (proj2 (Bool.negb_false_iff _)); first [apply Z.eqb_eq; lia | apply Z.ltb_lt; lia | apply Z.leb_le; lia] ].
Ltac chk_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true by (symmetry; chk_cond); cbv iota
            | replace c with false by (symmetry; chk_cond); cbv iota ]
  end.

Ltac chk_at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => constr_eq pc p end.

(* [comment removed for export] *)
Ltac chk_byte A X sz :=
  let A' := acc_now A in
  let k := fresh "k" in let RO := fresh "ROk" in let Hk := fresh "Hk" in let OK := fresh "OKk" in
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      destruct (acc_check_byte m _ _ X sz A') as (k & RO & Hk & OK); [sh_side | sh_side | sh_side | sh_side | sh_side |];
      rewrite <- (shadow_spell1 X) in RO by sh_side
  end.

(* [comment removed for export] *)
Ltac chk_meet := first [ apply evt_done; do 2 eexists; reflexivity | fail 100 "chk_join: the state at FAST is not the join state (scratch registers?)" ].
Ltac chk_arm fast :=
  repeat (first
    [ chk_at_pc fast; chk_meet
    | lazymatch goal with
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => chk_if
      | |- context [Z.land ?Y 7] => rewrite (land7_mod Y)
      | |- _ => zstep
      end ]).

(* [comment removed for export] *)
Ltac chk_join fast r1 r2 :=
  lazymatch goal with
  | OK : (?k = 0 \/ _ < ?k), Hk : (0 <= ?k < 8), RO : ro_cells _ _ _ [C1 (Z_to_bv 8 ?k)] |- evt ?segs ?Q (MS ?R ?F (if _ then _ else _) ?fc ?rv ?m ?rom) =>
      rewrite (sxb_small k) by lia;
      (* [comment removed for export] *)
      let p1 := eval vm_compute in (bv_key (Z_to_bv 5 r1)) in
      let p2 := eval vm_compute in (bv_key (Z_to_bv 5 r2)) in
      let f := eval cbv beta iota delta [tset] in (fun v1 v2 : word => tset p2 v2 (tset p1 v1 R)) in
      apply (evt_cut segs (fun ms => exists v1 v2 : word, ms = MS (f v1 v2) F (Z_to_bv 64 fast) fc rv m rom));
      [ cbv beta; destruct OK as [-> | OK]; [chk_if; chk_at_pc fast; chk_meet | chk_arm fast]
      | clear RO Hk OK; try clear k;
        let ms' := fresh "ms" in let v1 := fresh "v" in let v2 := fresh "v" in
        intros ms' (v1 & v2 & ->); cbv beta ]
  end.

(* [comment removed for export] *)
Ltac chk_pass A X sz fast r1 r2 := chk_byte A X sz; do 4 zstep; chk_join fast r1 r2.
