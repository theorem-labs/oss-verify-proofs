(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_agree I_ut Fz_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sh_fp (W : list (Z * Z)) : Prop := forall x, 0x7fff8000 <= x < 0x10007fff8000 -> outside W x.

Lemma sh_fp_nil : sh_fp [].
Proof. intros x _. exact I. Qed.
Lemma sh_fp_cons : forall lo hi W, (hi <= 0x7fff8000 \/ 0x10007fff8000 <= lo) -> sh_fp W -> sh_fp ((lo, hi) :: W).
Proof. intros lo hi W H HW x Hx. cbn [outside]. split; [lia| exact (HW x Hx)]. Qed.
Lemma sh_fp_app : forall W1 W2, sh_fp W1 -> sh_fp W2 -> sh_fp (W1 ++ W2).
Proof.
  intros W1 W2 H1 H2 x Hx. specialize (H1 x Hx). specialize (H2 x Hx). clear Hx.
  induction W1 as [|[lo hi] W1 IH]; [exact H2|]. cbn [app outside] in *. destruct H1 as [A B]. split; [exact A| exact (IH B)].
Qed.
Ltac sh_fp_lia := repeat first [ apply sh_fp_nil | apply sh_fp_app | apply sh_fp_cons; [lia|] ].

(* [comment removed for export] *)
Lemma acc_munch_sh : forall W (m0 m : mem) p n, acc asegs m0 p n -> munch W m0 m -> sh_fp W -> 0 <= p -> p + n <= 2^47 -> acc asegs m p n.
Proof.
  intros W m0 m p n HA MU HW P0 PN i Hi. destruct (HA i Hi) as (b & HB & OK). exists b. split; [| exact OK].
  apply (bytes_at_agree asegs m0 m _ _ HB). intros a Ha. apply MU. apply HW. cbn [length] in Ha. unfold shad, SHB in Ha. cbv beta in Ha.
  assert (0 <= (p + i) / 8 < 2^44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

(* [comment removed for export] *)
Lemma acc_shadow0 : forall (m : mem) p n X, acc asegs m p n -> p mod 8 = 0 -> 0 <= p -> p <= X -> 8 * ((X - p) / 8) + 8 <= n ->
  ro_cells asegs m (X / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
  intros m p n X HA PAL P0 PX HN. change (Z_to_bv 8 0) with z8.
  pose proof (Z.div_mod p 8 ltac:(lia)) as DP. rewrite PAL in DP.
  pose proof (Z.div_mod (X - p) 8 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound (X - p) 8 ltac:(lia)) as RX.
  set (g := p + 8 * ((X - p) / 8)).
  assert (EG : X / 8 = g / 8).
  { unfold g. replace X with ((X - p) mod 8 + (p / 8 + (X - p) / 8) * 8) at 1 by lia.
    rewrite Z.div_add by lia. rewrite (Z.div_small ((X - p) mod 8) 8) by lia.
    replace (p + 8 * ((X - p) / 8)) with (0 + (p / 8 + (X - p) / 8) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite EG. change (g / 8 + 2147450880) with (shad g).
  assert (G8 : g mod 8 = 0) by (unfold g; replace (p + 8 * ((X - p) / 8)) with (0 + (p / 8 + (X - p) / 8) * 8) by lia; rewrite Z.mod_add by lia; reflexivity).
  assert (GP : p <= g) by (unfold g; pose proof (Z.div_pos (X - p) 8 ltac:(lia) ltac:(lia)); lia).
  pose proof (acc_granule0 m p n g HA GP ltac:(unfold g; lia) G8 ltac:(lia)) as HB.
  unfold ro_cells, cells_at. cbn [cells_wf cells_bytes cbytes]. rewrite app_nil_r. split; [split; [reflexivity | exact I] | exact HB].
Qed.

(* [comment removed for export] *)
Lemma shadow_spell1 : forall X, 0 <= X -> X ≫ 3 + 2147450880 = X / 8 + 2147450880.
Proof. intros X HX. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma shadow_spell2 : forall X, 0 <= X -> 2147450880 + X ≫ 3 = X / 8 + 2147450880.
Proof. intros X HX. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

(* [comment removed for export] *)
Ltac sh_arg E :=
  lazymatch E with
  | (?X ≫ 3 + 2147450880)%Z => X
  | (2147450880 + ?X ≫ 3)%Z => X
  end.

(* [comment removed for export] *)
Ltac sh_side := first [ lia | Z.div_mod_to_equations; lia ].

Ltac solve_load_shadow0 :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a 1%nat] =>
      let E := addr_expr a in
      let X := sh_arg E in
      match goal with
      | A : acc asegs ?m0 ?p ?n, PAL : (?p mod 8 = 0)%Z |- _ =>
          let RO := fresh "ROsh" in
          assert (RO : ro_cells segs m E [C1 (Z_to_bv 8 0)])
            by (first [ rewrite (shadow_spell1 X) by sh_side | rewrite (shadow_spell2 X) by sh_side ];
                first [ apply (acc_shadow0 m p n X A PAL); sh_side
                      | lazymatch goal with MU : munch ?W m0 m, HW : sh_fp ?W |- _ =>
                          apply (acc_shadow0 m p n X (acc_munch_sh W m0 m p n A MU HW ltac:(sh_side) ltac:(sh_side)) PAL); sh_side end ]);
          rewrite (ro_cells_read_at segs m E [C1 (Z_to_bv 8 0)] 0%nat (C1 (Z_to_bv 8 0)) 1%nat a RO)
            by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          clear RO; load_post
      end
  end.
Ltac solve_load ::= first [ solve_load_base | solve_load_image | solve_load_ut | solve_load_shadow0 ].
