(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec StepTac StoreOk StreamSim.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Export RelocSpan CanonSpans.      (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition dwin_bounds_ok (img_lo rw_lo data_lo img_hi dD1 dD1b dD2 dB dBend : Z) : bool :=
  (0 <=? img_lo) && (img_lo <=? rw_lo) && (rw_lo <=? data_lo)
  && (data_lo <=? 0x1f3f8 + dD1) && (0x1f440 + dD1b <=? 0x1f440 + dD2)      (* [comment removed for export] *)
  && (data_lo <=? 0x1f440 + dD2) && (0x1f624 + dD2 <=? 0x1f630 + dB)
  && (0x300b0 + dBend <=? img_hi) && (img_hi <=? 2 ^ 32)
  && (dD1 mod 8 =? 0) && (dD2 mod 8 =? 0) && (dB mod 8 =? 0).

Definition dwin_bounds_chk {RL : Reloc} {RD : RelocData RL} : bool :=
  dwin_bounds_ok rl_img_lo rl_rw_lo rl_data_lo rl_img_hi dA_1f3f8 dA_1f430 dA_1f440 dA_1f630 dA_2fcb0.

Class RelocRW (RL : Reloc) (RD : RelocData RL) := {
  rl_dwin_bounds : dwin_bounds_chk = true;
  rl_rw_hull : hull_okb = true;
  rl_rw_spans : spans_check canon_spans = true;
  rl_rw_orders : orders_check canon_spans canon_order = true
}.

#[export] Instance RelocSpans_of_RW {RL : Reloc} {RD : RelocData RL} {RW : RelocRW RL RD} : RelocSpans RL RD :=
  {| rl_hull_ok := rl_rw_hull; rl_spans_ok := rl_rw_spans; rl_orders_ok := rl_rw_orders |}.

Section RW.
  Context {RL : Reloc} {RD : RelocData RL} {RW : RelocRW RL RD}.

  Lemma rl_dwin_facts :
    0 <= rl_img_lo /\ rl_img_lo <= rl_rw_lo /\ rl_rw_lo <= rl_data_lo
    /\ rl_data_lo <= 0x1f3f8 + dA_1f3f8 /\ 0x1f440 + dA_1f430 <= 0x1f440 + dA_1f440
    /\ rl_data_lo <= 0x1f440 + dA_1f440 /\ 0x1f624 + dA_1f440 <= 0x1f630 + dA_1f630
    /\ 0x300b0 + dA_2fcb0 <= rl_img_hi /\ rl_img_hi <= 2 ^ 32.
  Proof.
    pose proof rl_dwin_bounds as H. unfold dwin_bounds_chk, dwin_bounds_ok in H.
    apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
    repeat (apply andb_prop in H; destruct H as [H ?]).
    repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X end.
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rl_dDATA1_mod8 : dA_1f3f8 mod 8 = 0.
  Proof.
    pose proof rl_dwin_bounds as H. unfold dwin_bounds_chk, dwin_bounds_ok in H.
    apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. apply Z.eqb_eq in H. exact H.
  Qed.
  Lemma rl_dDATA_mod8 : dA_1f440 mod 8 = 0.
  Proof.
    pose proof rl_dwin_bounds as H. unfold dwin_bounds_chk, dwin_bounds_ok in H.
    apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. apply Z.eqb_eq in H. exact H.
  Qed.
  Lemma rl_dBSS_mod8 : dA_1f630 mod 8 = 0.
  Proof.
    pose proof rl_dwin_bounds as H. unfold dwin_bounds_chk, dwin_bounds_ok in H.
    apply andb_prop in H as [_ H]. apply Z.eqb_eq in H. exact H.
  Qed.
End RW.

Lemma mod4_add8 : forall c d, c mod 4 = 0 -> d mod 8 = 0 -> (c + d) mod 4 = 0.
Proof.
  intros c d Hc Hd. apply Z.mod_divide in Hd; [|lia]. destruct Hd as [q ->].
  replace (c + q * 8) with (c + (2 * q) * 4) by lia. rewrite Z.mod_add by lia. exact Hc.
Qed.
Lemma mod8_add8 : forall c d, c mod 8 = 0 -> d mod 8 = 0 -> (c + d) mod 8 = 0.
Proof.
  intros c d Hc Hd. apply Z.mod_divide in Hd; [|lia]. destruct Hd as [q ->].
  rewrite Z.mod_add by lia. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma modk_add_al : forall k al c d, 0 < k -> al mod k = 0 -> c mod k = 0 -> d mod al = 0 -> (c + d) mod k = 0.
Proof.
  intros k al c d Hk Hal Hc Hd.
  destruct (Z.eq_dec al 0) as [->|Hne]; [rewrite Zmod_0_r in Hd; subst d; rewrite Z.add_0_r; exact Hc|].
  apply Z.mod_divide in Hal; [|lia]. destruct Hal as [q ->].
  apply Z.mod_divide in Hd; [|exact Hne]. destruct Hd as [r ->].
  replace (c + r * (q * k)) with (c + (r * q) * k) by lia. rewrite Z.mod_add by lia. exact Hc.
Qed.
Ltac rl_align_span :=
  lazymatch goal with
  | |- (?c + @rl_delta ?RL ?b) mod ?k = 0 =>
      let r := eval vm_compute in (span_find canon_spans b) in
      lazymatch r with
      | Some ?s =>
          let al := eval vm_compute in (sp_al s) in
          apply (modk_add_al k al c (@rl_delta RL b)); [ lia | reflexivity | reflexivity | exact (proj2 (rl_span b s (@eq_refl _ (Some s)))) ]
      end
  end.

(* [comment removed for export] *)
Ltac rl_dmod8 :=
  first [ exact rl_dBSS_mod8 | exact rl_dDATA_mod8 | exact rl_dDATA1_mod8
        | lazymatch goal with
          | |- (@rl_delta ?RL ?b) mod 8 = 0 =>
              let r := eval vm_compute in (span_find canon_spans b) in
              lazymatch r with Some ?s => exact (proj2 (rl_span b s (@eq_refl _ (Some s)))) end
          end ].

(* [comment removed for export] *)
Ltac rl_align :=
  first [ reflexivity
        | apply mod4_add8; [ reflexivity | rl_dmod8 ]
        | apply mod8_add8; [ reflexivity | rl_dmod8 ]
        | rl_align_span ].

(* [comment removed for export] *)
Ltac rl_dwin_bounds :=
  lazymatch goal with
  | _ : rl_img_hi <= 2 ^ 32 |- _ => idtac
  | _ => let F := fresh "RWF" in
         let a := fresh "RWa" in let b := fresh "RWb" in let c := fresh "RWc" in let d := fresh "RWd" in
         let e := fresh "RWe" in let f := fresh "RWf" in let g := fresh "RWg" in let h := fresh "RWh" in let i := fresh "RWi" in
         let x := fresh "RWx" in let y := fresh "RWy" in let z := fresh "RWz" in
         pose proof rl_dwin_facts as F; destruct F as (a & b & c & d & e & f & g & h & i);
         pose proof (rl_delta_bd B_A_1f3f8) as x; pose proof (rl_delta_bd B_A_1f440) as y; pose proof (rl_delta_bd B_A_1f630) as z;
         rl_spans_data;     (* [comment removed for export] *)
         rl_data_chain      (* [comment removed for export] *)
  end.
