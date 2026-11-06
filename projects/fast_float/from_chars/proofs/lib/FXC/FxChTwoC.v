(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition P47c : Z := 0x800000000000.
(* [comment removed for export] *)
Definition twoc1 (all : list fact) (b : lin) (zhi : Z) (f : fact) : bool :=
  match f with
  | FRange w lo whi =>
      if Z.eqb lo 0 then
        let n := two64 + SH_LO - SH_HI - whi in
        if Z.ltb 0 n then
          if Z.leb n P47c then
            (* [comment removed for export] *)
            let g := laddc w SH_HI in
            let '(dlo, dhi) := irange all (lsub b g) in
            if Z.leb 0 dlo then if Z.leb (dhi + zhi) n then Z.ltb (snd (irange all g) + n) two64 else false else false
          else false
        else false
      else false
  | _ => false
  end.
Definition twoc_ns (fs : list fact) (b : lin) (zhi : Z) : bool := existsb_lz (twoc1 fs b zhi) fs.

Lemma u_laddc_mod : forall E l c, uE E (laddc l c) = (uE E l + c) mod two64.
Proof.
  intros E l c. unfold uE. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem twoc_ns_sound : forall E fs b zhi, Forall (fact_ok E) fs -> twoc_ns fs b zhi = true -> 0 <= zhi ->
  uE E b + zhi <= SH_LO \/ (SH_HI <= uE E b /\ uE E b + zhi <= two64).
Proof.
  intros E fs b zhi HF H Hz. unfold twoc_ns in H. rewrite existsb_lz_eq in H. apply existsb_exists in H as (f & Hin & H1).
  rewrite Forall_forall in HF. pose proof (HF f Hin) as Hf. assert (HF' : Forall (fact_ok E) fs) by (apply Forall_forall; exact HF).
  unfold twoc1 in H1. destruct f as [c a0 b0 tk|w lo whi|l' k' r'|l' m' v'|x' v' j'|xb bsb]; try discriminate.
  destruct (Z.eqb lo 0) eqn:El; [|discriminate]. apply Z.eqb_eq in El. subst lo. cbv zeta in H1.
  set (n := two64 + SH_LO - SH_HI - whi) in *.
  destruct (Z.ltb 0 n) eqn:Hn0; [|discriminate]. apply Z.ltb_lt in Hn0.
  destruct (Z.leb n P47c) eqn:Hn1; [|discriminate]. apply Z.leb_le in Hn1.
  set (g := laddc w SH_HI) in *.
  destruct (irange fs (lsub b g)) as [dlo dhi] eqn:Hdr.
  destruct (Z.leb 0 dlo) eqn:C1; [|discriminate]. destruct (Z.leb (dhi + zhi) n) eqn:C2; [|discriminate].
  apply Z.leb_le in C1, C2. apply Z.ltb_lt in H1.
  pose proof (irange_sound E fs (lsub b g) HF') as Rd. rewrite Hdr in Rd. cbn [fst snd] in Rd. fold (uE E (lsub b g)) in Rd.
  pose proof (irange_sound E fs g HF') as Rg. fold (uE E g) in Rg.
  cbn [fact_ok] in Hf. fold (uE E w) in Hf.
  pose proof (uE_range E b) as RB. pose proof (uE_range E g) as RG. pose proof (uE_range E w) as RW.
  (* [comment removed for export] *)
  assert (HG : uE E g = (uE E w + SH_HI) mod two64) by (unfold g; apply u_laddc_mod).
  (* [comment removed for export] *)
  assert (HB : uE E b = uE E g + uE E (lsub b g)).
  { destruct (small_diff E b g dlo dhi Rd) as [[Hl He]|[Hl He]]; [lia | exfalso; lia]. }
  destruct (Z_lt_le_dec (uE E w + SH_HI) two64) as [Hs|Hs].
  - (* [comment removed for export] *)
    rewrite Z.mod_small in HG by (unfold SH_HI in *; lia). right. split; [lia|]. lia.
  - (* [comment removed for export] *)
    assert (HG2 : uE E g = uE E w + SH_HI - two64).
    { rewrite HG. symmetry. apply (Z.mod_unique _ _ 1); unfold SH_HI, two64 in *; lia. }
    left. unfold n in *. lia.
Qed.
(* [comment removed for export] *)
Corollary twoc_ns_noshadow : forall E fs b zhi, Forall (fact_ok E) fs -> twoc_ns fs b zhi = true -> 0 <= zhi ->
  forall x, uE E b <= x < uE E b + zhi -> in_shadow x = false.
Proof.
  intros E fs b zhi HF H Hz x Hx. unfold in_shadow. apply andb_false_iff.
  destruct (twoc_ns_sound E fs b zhi HF H Hz) as [Hlo|[Hhi _]]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
Qed.
