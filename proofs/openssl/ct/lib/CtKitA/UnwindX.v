(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_unwind_chain RT_iface D_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnIfaceA UnwindA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma uw_chain_agree16 : forall (m m' : mem) ras f fp,
  uw_chain USTACK_TOP m f fp ras -> agree_on (fun a => fp - 16 <= a < USTACK_TOP) m m' -> uw_chain USTACK_TOP m' f fp ras.
Proof.
  intros m m' ras f fp HU AG. destruct ras as [|r ras]; cbn [uw_chain] in *; [exact HU|].
  destruct HU as (H1 & H2 & H3 & fp' & Hfp' & HC & HU). split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  exists fp'. split; [exact Hfp'|]. split.
  - eapply rw_cells_agree; [exact AG | exact HC |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia.
  - eapply uw_chain_agree; [exact HU|]. eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_prefix : forall (m : mem) a cs1 cs2, rw_cells ctasegs m a (cs1 ++ cs2) -> rw_cells ctasegs m a cs1.
Proof.
  intros m a cs1 cs2 ((Hwf & Hb) & Hw). apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [Hb1 _].
  split; [split; [exact W1 | exact Hb1]|].
  destruct Hw as (X1 & X2 & X3). rewrite cells_size_app, Nat2Z.inj_add in X2, X3.
  split; [exact X1|]. split; [lia|]. intros i Hi. apply X3. lia.
Qed.

(* [comment removed for export] *)
Lemma uw_chain_lower : forall (m : mem) ras f f' fp,
  uw_chain USTACK_TOP m f fp ras -> ras <> nil -> f' <= f -> uw_chain USTACK_TOP m f' fp ras.
Proof.
  intros m ras f f' fp HU NE LE. destruct ras as [|r ras]; [exfalso; apply NE; reflexivity|].
  cbn [uw_chain] in *. destruct HU as (H1 & H2 & H3 & REST). split; [lia|]. split; [exact H2|]. split; [exact H3| exact REST].
Qed.

Lemma cons_ne : forall (r : Z) (ras : list Z), r :: ras <> nil.
Proof. intros r ras H. discriminate H. Qed.

(* [comment removed for export] *)
Lemma uw_chain_agreeP : forall (P : Z -> Prop) (m m' : mem) ras f fp,
  agree_on P m m' -> uw_chain USTACK_TOP m f fp ras -> (forall a, f + 16 <= fp -> fp - 16 <= a < USTACK_TOP -> P a) -> uw_chain USTACK_TOP m' f fp ras.
Proof.
  intros P m m' ras f fp AG HU HP. destruct ras as [|r ras]; [exact HU|].
  pose proof HU as HU0. cbn [uw_chain] in HU0. destruct HU0 as (H1 & _).
  eapply uw_chain_agree16; [exact HU|]. eapply agree_on_mono; [exact AG|]. intros a Ha. apply HP; [exact H1 | exact Ha].
Qed.

(* [comment removed for export] *)
Lemma uw_chain_munchP : forall W (m m' : mem) ras f fp,
  munch W m m' -> uw_chain USTACK_TOP m f fp ras -> (forall a, f + 16 <= fp -> fp - 16 <= a < USTACK_TOP -> outside W a) -> uw_chain USTACK_TOP m' f fp ras.
Proof.
  intros W m m' ras f fp MU HU HP. eapply uw_chain_agreeP; [apply (agree_on_of_munch_nw _ _ _ MU) | exact HU | exact HP].
Qed.

Section WithAR.
Context {AR : ARun}.

(* [comment removed for export] *)
Lemma aclient_stack : forall LB SP a, SP <= a < USTACK_TOP -> aclient_addr LB SP a.
Proof. intros LB SP a Ha. left. exact Ha. Qed.

Lemma libw_below : forall a, rin_ivs LIBW_A a -> a < SEGTOP_A.
Proof. intros a Ha. unfold LIBW_A in Ha. unfold SEGTOP_A. cbn in Ha. lia. Qed.

(* [comment removed for export] *)
Lemma uw_call : forall (m0 mX : mem) f' fp N pre ra_e s0_e ras,
  uw_chain USTACK_TOP m0 fp s0_e ras ->
  agree_on (fun a => fp <= a < USTACK_TOP) m0 mX ->
  Z.of_nat (cells_size pre) = N - 16 -> f' + 16 <= fp -> fp mod 8 = 0 -> fp <= USTACK_TOP -> 0 <= s0_e < 2 ^ 64 ->
  rw_cells ctasegs mX (fp + - N) (pre ++ [C8 (Z_to_bv 64 s0_e); C8 (Z_to_bv 64 ra_e)]) ->
  uw_chain USTACK_TOP mX f' fp (ra_e :: ras).
Proof.
  intros m0 mX f' fp N pre ra_e s0_e ras UW AG HN H1 H2 H3 H4 FR.
  apply (uw_push_frame mX f' fp N pre ra_e s0_e ras HN H1 H2 H3 H4 FR).
  destruct ras as [|r ras]; cbn [uw_chain] in *; [exact UW|].
  destruct UW as (U1 & U2 & U3 & fp' & Hfp' & HC & HU). split; [exact U1|]. split; [exact U2|]. split; [exact U3|].
  exists fp'. split; [exact Hfp'|]. split.
  - eapply rw_cells_agree; [exact AG | exact HC |]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. lia.
  - eapply uw_chain_agree; [exact HU|]. eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta in *. lia.
Qed.

(* [comment removed for export] *)
Lemma uw_call_mu : forall W (m0 mX : mem) f' fp N pre ra_e s0_e ras,
  uw_chain USTACK_TOP m0 fp s0_e ras -> munch W m0 mX -> (forall a, fp <= a < USTACK_TOP -> outside W a) ->
  Z.of_nat (cells_size pre) = N - 16 -> f' + 16 <= fp -> fp mod 8 = 0 -> fp <= USTACK_TOP -> 0 <= s0_e < 2 ^ 64 ->
  rw_cells ctasegs mX (fp + - N) (pre ++ [C8 (Z_to_bv 64 s0_e); C8 (Z_to_bv 64 ra_e)]) ->
  uw_chain USTACK_TOP mX f' fp (ra_e :: ras).
Proof.
  intros W m0 mX f' fp N pre ra_e s0_e ras UW MU OUT HN H1 H2 H3 H4 FR.
  eapply (uw_call m0 mX f' fp N pre ra_e s0_e ras UW); [| exact HN | exact H1 | exact H2 | exact H3 | exact H4 | exact FR].
  eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. exact (OUT a Ha).
Qed.

(* [comment removed for export] *)
Lemma uw_call_lower : forall (m0 mX : mem) f0 f' fp N pre ra_e s0_e ras,
  uw_chain USTACK_TOP m0 f0 s0_e ras -> ras <> nil -> fp <= f0 ->
  agree_on (fun a => f0 <= a < USTACK_TOP) m0 mX ->
  Z.of_nat (cells_size pre) = N - 16 -> f' + 16 <= fp -> fp mod 8 = 0 -> fp <= USTACK_TOP -> 0 <= s0_e < 2 ^ 64 ->
  rw_cells ctasegs mX (fp + - N) (pre ++ [C8 (Z_to_bv 64 s0_e); C8 (Z_to_bv 64 ra_e)]) ->
  uw_chain USTACK_TOP mX f' fp (ra_e :: ras).
Proof.
  intros m0 mX f0 f' fp N pre ra_e s0_e ras UW NE LE AG HN H1 H2 H3 H4 FR.
  assert (U1 : uw_chain USTACK_TOP mX f0 s0_e ras).
  { eapply uw_chain_agree16; [exact UW|]. destruct ras as [|r ras]; [exfalso; apply NE; reflexivity|].
    cbn [uw_chain] in UW. destruct UW as (A1 & _). eapply agree_on_mono; [exact AG|]. intros a Ha. cbv beta in *. lia. }
  apply (uw_push_frame mX f' fp N pre ra_e s0_e ras HN H1 H2 H3 H4 FR). eapply uw_chain_lower; [exact U1 | exact NE | exact LE].
Qed.

(* [comment removed for export] *)
Lemma ax_pres_stack : forall LB SP X (m m' : mem) f,
  ax_pres LB SP X m m' -> SP <= f -> (forall a, rin_ivs X a -> a < f) -> agree_on (fun a => f <= a < USTACK_TOP) m m'.
Proof.
  intros LB SP X m m' f AX LE BX. eapply agree_on_mono; [exact AX|]. intros a Ha. cbv beta in Ha.
  split; [intros Hr; pose proof (BX a Hr); lia | left; lia].
Qed.

(* [comment removed for export] *)
Lemma uw_chain_axpres : forall LB SP (m m' : mem) ras f fp,
  ax_pres LB SP LIBW_A m m' -> uw_chain USTACK_TOP m f fp ras -> SP <= fp - 16 -> SEGTOP_A <= fp - 16 -> uw_chain USTACK_TOP m' f fp ras.
Proof.
  intros LB SP m m' ras f fp AX HU LE SG. eapply uw_chain_agree16; [exact HU|].
  eapply agree_on_mono; [exact AX|]. intros a Ha. cbv beta in Ha.
  split; [intros Hr; pose proof (libw_below a Hr); lia | left; lia].
Qed.

Lemma rin_ivs_app : forall X Y a, rin_ivs (X ++ Y) a -> rin_ivs X a \/ rin_ivs Y a.
Proof. intros X Y a. induction X as [|iv X IH]; cbn [rin_ivs app]; [tauto|]. intros [H|H]; [tauto|]. destruct (IH H); tauto. Qed.

(* [comment removed for export] *)
Lemma uw_call_axX : forall (m0 mX : mem) LB SP X f' fp N pre ra_e s0_e ras,
  uw_chain USTACK_TOP m0 fp s0_e ras -> ax_pres LB SP X m0 mX -> SP <= fp -> (forall a, rin_ivs X a -> a < fp) ->
  Z.of_nat (cells_size pre) = N - 16 -> f' + 16 <= fp -> fp mod 8 = 0 -> fp <= USTACK_TOP -> 0 <= s0_e < 2 ^ 64 ->
  rw_cells ctasegs mX (fp + - N) (pre ++ [C8 (Z_to_bv 64 s0_e); C8 (Z_to_bv 64 ra_e)]) ->
  uw_chain USTACK_TOP mX f' fp (ra_e :: ras).
Proof.
  intros m0 mX LB SP X f' fp N pre ra_e s0_e ras UW AX LE BX HN H1 H2 H3 H4 FR.
  eapply (uw_call m0 mX f' fp N pre ra_e s0_e ras UW); [| exact HN | exact H1 | exact H2 | exact H3 | exact H4 | exact FR].
  eapply ax_pres_stack; [exact AX | exact LE | exact BX].
Qed.

(* [comment removed for export] *)
Lemma uw_call_ax : forall (m0 mX : mem) LB SP f' fp N pre ra_e s0_e ras,
  uw_chain USTACK_TOP m0 fp s0_e ras -> ax_pres LB SP LIBW_A m0 mX -> SP <= fp -> SEGTOP_A <= fp ->
  Z.of_nat (cells_size pre) = N - 16 -> f' + 16 <= fp -> fp mod 8 = 0 -> fp <= USTACK_TOP -> 0 <= s0_e < 2 ^ 64 ->
  rw_cells ctasegs mX (fp + - N) (pre ++ [C8 (Z_to_bv 64 s0_e); C8 (Z_to_bv 64 ra_e)]) ->
  uw_chain USTACK_TOP mX f' fp (ra_e :: ras).
Proof.
  intros m0 mX LB SP f' fp N pre ra_e s0_e ras UW AX LE SG HN H1 H2 H3 H4 FR.
  eapply (uw_call_axX m0 mX LB SP LIBW_A f' fp N pre ra_e s0_e ras UW AX LE); [| exact HN | exact H1 | exact H2 | exact H3 | exact H4 | exact FR].
  intros a Ha. pose proof (libw_below a Ha). lia.
Qed.
End WithAR.

(* [comment removed for export] *)
Ltac uw_call_ax_tac m0 N UW AX FR :=
  lazymatch type of FR with
  | rw_cells _ ?mX _ ?cs =>
      let pre := eval cbn [List.removelast] in (List.removelast (List.removelast cs)) in
      lazymatch goal with
      | |- uw_chain _ _ ?f1 ?fp1 _ =>
          eapply (uw_call_ax m0 mX _ _ f1 fp1 N pre);
            [exact UW | exact AX | | | reflexivity | | | | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; exact FR]
      end
  end.
Ltac uw_call_mu_tac m0 N UW MU FR :=
  lazymatch type of FR with
  | rw_cells _ ?mX _ ?cs =>
      let pre := eval cbn [List.removelast] in (List.removelast (List.removelast cs)) in
      lazymatch goal with
      | |- uw_chain _ _ ?f1 ?fp1 _ =>
          eapply (uw_call_mu _ m0 mX f1 fp1 N pre);
            [exact UW | exact MU | | reflexivity | | | | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; exact FR]
      end
  end.
Ltac uw_call_axX_tac m0 N UW AX FR :=
  lazymatch type of FR with
  | rw_cells _ ?mX _ ?cs =>
      let pre := eval cbn [List.removelast] in (List.removelast (List.removelast cs)) in
      lazymatch goal with
      | |- uw_chain _ _ ?f1 ?fp1 _ =>
          eapply (uw_call_axX m0 mX _ _ _ f1 fp1 N pre);
            [exact UW | exact AX | | | reflexivity | | | | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; exact FR]
      end
  end.
