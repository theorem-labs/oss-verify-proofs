(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import LedgerCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxDrive.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition covers (t : int) (o n : Z) (e : fent) : bool :=
  let '(t', o', l') := e in (t' =? t)%uint63 && (to_Z o' <=? o) && (o + n <=? to_Z o' + to_Z l').

Definition apart (t : int) (o n : Z) (e : fent) : bool :=
  let '(t', o', l') := e in
  if (t' =? t)%uint63 then (to_Z o' + to_Z l' <=? o) || (o + n <=? to_Z o') else true.

Definition in_entry_b (L : fledger) (t : int) (o n : Z) : bool :=
  (0 <=? n) && existsb (covers t o n) (fl_maps L).

Definition ledger_vis_b (L : fledger) (t : int) (o n : Z) : bool :=
  in_entry_b L t o n && forallb (apart t o n) (fl_na L).

(* [comment removed for export] *)
Fixpoint ledger_bnd (TOP : Z) (es : list fent) (t : int) (lo hi : Z) : Z * Z :=
  match es with
  | [] => (lo, hi)
  | (t', o', l') :: r =>
      if (t' =? t)%uint63
      then ledger_bnd TOP r t (Z.max lo (4096 - to_Z o')) (Z.min hi (TOP - to_Z o' - to_Z l'))
      else ledger_bnd TOP r t lo hi
  end.

(* [comment removed for export] *)
Lemma ledger_vis_b_mono L t o n o' n' :
  ledger_vis_b L t o n = true -> o <= o' -> o' + n' <= o + n -> 0 <= n' -> ledger_vis_b L t o' n' = true.
Proof.
  unfold ledger_vis_b, in_entry_b. intros H Ho Hn Hn'.
  apply andb_prop in H as [H Hap]. apply andb_prop in H as [_ Hex].
  apply andb_true_intro. split; [apply andb_true_intro; split; [apply Z.leb_le; exact Hn'|]|].
  - apply existsb_exists in Hex as (e & He & Hc). apply existsb_exists. exists e. split; [exact He|].
    destruct e as [[t0 o0] l0]. unfold covers in *. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H2, H3. rewrite H1. cbn [andb].
    apply andb_true_intro. split; apply Z.leb_le; lia.
  - rewrite forallb_forall in *. intros e He. specialize (Hap e He). destruct e as [[t0 o0] l0]. unfold apart in *.
    destruct (t0 =? t)%uint63; [|reflexivity].
    apply orb_prop in Hap as [Hap|Hap]; apply Z.leb_le in Hap; apply orb_true_iff; [left | right]; apply Z.leb_le; lia.
Qed.

Section Ledger.
Variable rho : int -> word.
Variable M : itrie region.
Variable L : fledger.
Variable V : VmMaps.
Variable R0 : list (word * word).
Variable Lim c S : Z.
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.
Hypothesis Hsep : regions_sep rho M.
Hypothesis Hinv : ledger_inv R0 Lim c S V.
Hypothesis Hmaps : vm_maps V = map (den rho) (fl_maps L).
Hypothesis Hna : vm_noaccess V = map (den rho) (fl_na L).
Hypothesis Hin_maps : Forall (ent_in M) (fl_maps L).
Hypothesis Hin_na : Forall (ent_in M) (fl_na L).

(* [comment removed for export] *)
Lemma den_interval t off len :
  ent_in M (t, off, len) ->
  e_lo (den rho (t, off, len)) = bv_unsigned (rho t) + to_Z off
  /\ e_sz (den rho (t, off, len)) = to_Z len
  /\ exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= to_Z off
                /\ to_Z off + to_Z len <= to_Z (rg_len rg).
Proof.
  intros (rg & Hg & Hlo & Hhi). unfold e_lo, e_sz, den. cbn [fst snd].
  destruct (HM t rg Hg) as (_ & _ & Hb & _).
  pose proof (i63_range off). pose proof (i63_range len). pose proof (i63_range (rg_len rg)).
  pose proof (bv_unsigned_in_range _ (rho t)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  split; [|split].
  - apply (adr_unsigned rho t (to_Z off)); lia.
  - rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
  - exists rg. repeat split; assumption.
Qed.

Lemma covers_spec t o n e :
  covers t o n e = true -> exists off len, e = (t, off, len) /\ to_Z off <= o /\ o + n <= to_Z off + to_Z len.
Proof.
  destruct e as [[t' o'] l']. unfold covers. intros Hc.
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Uint63.eqb_spec in H1. subst t'. apply Z.leb_le in H2, H3. exists o', l'. repeat split; assumption.
Qed.

Theorem in_entry_sound t o n :
  in_entry_b L t o n = true ->
  exists e, bv_unsigned (rho t) + o + n <= e /\ e <= alloc_top V /\ e mod 4096 = 0
    /\ exists p, In p (vm_maps V) /\ e_lo p <= bv_unsigned (rho t) + o /\ e = e_hi p
    /\ exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o /\ o + n <= to_Z (rg_len rg).
Proof.
  unfold in_entry_b. intros Hb. apply andb_prop in Hb as [Hn Hb]. apply Z.leb_le in Hn.
  apply existsb_exists in Hb as (e & Hin & Hc).
  destruct (covers_spec t o n e Hc) as (off & len & -> & Ho1 & Ho2).
  pose proof (proj1 (Forall_forall _ _) Hin_maps _ Hin) as Hent.
  destruct (den_interval t off len Hent) as (Elo & Esz & rg & Hg & Hrlo & Hrhi).
  set (p := den rho (t, off, len)) in *.
  assert (Hp : In p (vm_maps V)) by (rewrite Hmaps; apply in_map; exact Hin).
  destruct Hinv as [_ _ _ _ _ Hal Htop _ _ _ _ _ _ _ _ _].
  pose proof (proj1 (Forall_forall _ _) Hal p Hp) as [Hal1 Hal2].
  pose proof (proj1 (Forall_forall _ _) Htop p Hp) as [_ Ht2].
  exists (e_hi p). unfold e_hi in *. rewrite Elo, Esz in *. split; [lia|]. split; [exact Ht2|]. split.
  - unfold page_size in Hal1, Hal2. rewrite Z.add_mod by lia. rewrite Hal1, Hal2. reflexivity.
  - exists p. split; [exact Hp|]. split; [lia|]. split; [rewrite Elo, Esz; reflexivity|].
    exists rg. split; [exact Hg|]. split; lia.
Qed.

Theorem ledger_vis_sound t o n :
  ledger_vis_b L t o n = true ->
  forall z, bv_unsigned (rho t) + o <= z < bv_unsigned (rho t) + o + n ->
    (exists p, In p (vm_maps V) /\ e_lo p <= z < e_hi p)
    /\ (forall q, In q (vm_noaccess V) -> ~ (e_lo q <= z < e_hi q))
    /\ z < alloc_top V.
Proof.
  unfold ledger_vis_b. intros Hb z Hz. apply andb_prop in Hb as [He Hap].
  destruct (in_entry_sound t o n He) as (e & He1 & He2 & _ & p & Hp & Hplo & -> & rg & Hg & Hrlo & Hrhi).
  split; [exists p; split; [exact Hp | lia]|]. split; [|lia].
  intros q Hq Hzq. rewrite Hna in Hq. apply in_map_iff in Hq as (eq & <- & Hinq).
  destruct eq as [[t' o'] l'].
  pose proof (proj1 (Forall_forall _ _) Hin_na _ Hinq) as Hent.
  destruct (den_interval t' o' l' Hent) as (Elo & Esz & rg' & Hg' & Hrlo' & Hrhi').
  unfold e_hi in Hzq. rewrite Elo, Esz in Hzq.
  rewrite forallb_forall in Hap. specialize (Hap _ Hinq). unfold apart in Hap.
  destruct (t' =? t)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t'. apply orb_prop in Hap as [Hap|Hap]; apply Z.leb_le in Hap; lia.
  - assert (Hne : t' <> t) by (intros ->; rewrite Uint63.eqb_refl in Et; discriminate).
    destruct (Hsep t' t rg' rg Hne Hg' Hg) as [Hd|Hd]; lia.
Qed.

Theorem ledger_bnd_sound TOP : alloc_top V <= TOP ->
  forall es t lo hi, (forall e, In e es -> In e (fl_maps L)) ->
    lo <= bv_unsigned (rho t) <= hi ->
    fst (ledger_bnd TOP es t lo hi) <= bv_unsigned (rho t) <= snd (ledger_bnd TOP es t lo hi).
Proof.
  intros HTOP. induction es as [|[[t' o'] l'] r IH]; intros t lo hi Hsub Hb; [exact Hb|].
  cbn [ledger_bnd]. destruct (t' =? t)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. subst t'. apply IH; [intros e He; apply Hsub; right; exact He|].
    assert (Hin : In (t, o', l') (fl_maps L)) by (apply Hsub; left; reflexivity).
    pose proof (proj1 (Forall_forall _ _) Hin_maps _ Hin) as Hent.
    destruct (den_interval t o' l' Hent) as (Elo & Esz & _).
    set (p := den rho (t, o', l')) in *.
    assert (Hp : In p (vm_maps V)) by (rewrite Hmaps; apply in_map; exact Hin).
    destruct Hinv as [_ _ _ _ _ Hal Htop _ _ _ _ _ _ _ _ _].
    pose proof (proj1 (Forall_forall _ _) Hal p Hp) as [Hal1 _].
    pose proof (proj1 (Forall_forall _ _) Htop p Hp) as [Ht1 Ht2].
    unfold e_hi in Ht2. rewrite Elo, Esz in *. unfold page_size in Hal1.
    assert (4096 <= bv_unsigned (rho t) + to_Z o').
    { destruct (Z_lt_le_dec (bv_unsigned (rho t) + to_Z o') 4096) as [Hlt|]; [|lia].
      rewrite Z.mod_small in Hal1 by lia. lia. }
    lia.
  - apply IH; [intros e He; apply Hsub; right; exact He | exact Hb].
Qed.

End Ledger.
