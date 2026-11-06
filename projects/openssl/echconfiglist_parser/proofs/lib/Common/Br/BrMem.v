(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrEnv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rview_mrestrict segs (H : word -> bool) mem x :
  H x = false -> rview segs (mrestrict H mem) x = rview segs mem x.
Proof. intros Hx. unfold rview, mrestrict. rewrite Hx. reflexivity. Qed.

Lemma wview_mrestrict segs (H : word -> bool) mem x :
  H x = false -> wview segs (mrestrict H mem) x = wview segs mem x.
Proof. intros Hx. unfold wview, mrestrict. rewrite Hx. reflexivity. Qed.

Lemma region_ok_nowrap' rho t rg :
  region_ok rho t rg -> bv_unsigned (rho t) + to_Z (rg_len rg) < 2 ^ 63.
Proof. intros (_ & _ & Hb & _). exact Hb. Qed.

(* [comment removed for export] *)
Lemma rdn_intro segs mem a n bs :
  length bs = n ->
  (forall j, (j < n)%nat -> rview segs mem (aoff a j) = nth_error bs j) ->
  rdn segs mem a n = Some bs.
Proof. intros Hl Hb. rewrite <- ov_rdn. apply ov_read_bytes_intro; assumption. Qed.

(* [comment removed for export] *)
Section Mem.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.
Variable xv : nat -> word.
Variable xb : nat -> list byte.
Variable VT : vtab.
Variable M : itrie region.
Variable TL : ttab.
Variable XT : list (int * AX2.lin).
Variable TEQ : list teq.
Variable mem : word -> option byte.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Hypothesis HMem : mem_ok segs IM rho M mem.
Hypothesis HTL : tl_ok VT M TL = true.
Hypothesis HXT : xt_ok rho xv xb VT XT.
Hypothesis HTEQ : teq_ok rho TEQ.

Local Notation E := (env_of rho xv xb VT).

Lemma HM_regions : forall t rg, iget t M = Some rg -> region_ok rho t rg.
Proof. intros t rg Hg. exact (proj1 (proj1 HMem t rg Hg)). Qed.

(* [comment removed for export] *)
Variable H : word -> bool.
Variable visb : int -> Z -> Z -> bool.
Hypothesis visb_sound : forall t o n, visb t o n = true ->
  forall j, 0 <= j < n -> H (adr rho t (o + j)) = false.
Variable nosegb : int -> Z -> Z -> bool.
(* [comment removed for export] *)
Hypothesis nosegb_sound : forall t o n, nosegb t o n = true ->
  forall j, 0 <= j < n -> mem (adr rho t (o + j)) <> None
                          \/ find_segment segs (bv_unsigned (adr rho t (o + j))) 1 = None.
(* [comment removed for export] *)
Variable xslots : int -> Z -> option slots.
Hypothesis xslots_sound : forall t o sls, xslots t o = Some sls ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o / 8 * 8 /\ o / 8 * 8 + 8 <= to_Z (rg_len rg) /\ 0 <= o
    /\ slots_val rho sls (fun j => rview segs mem (adr rho t (o / 8 * 8 + Z.of_nat j))).
Variable xwrb : int -> Z -> Z -> bool.
Hypothesis xwrb_sound : forall t o n, xwrb t o n = true ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o /\ o + n <= to_Z (rg_len rg)
    /\ forall x, o <= x < o + n -> wview segs mem (adr rho t x) <> None.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition b62z : Z := 2 ^ 62.

(* [comment removed for export] *)
Definition page_atw (rg : region) (t pn : int) : option page :=
  if (to_Z pn * 4096 + 4096 <=? to_Z (rg_len rg)) then page_at IM rg t pn else None.

Lemma page_atw_ok rg t pn p :
  iget t M = Some rg -> to_Z pn < 2 ^ 50 -> page_atw rg t pn = Some p ->
  page_at IM rg t pn = Some p
  /\ page_ok segs IM rho mem t pn 512 p
  /\ to_Z (rg_lo rg) <= to_Z pn * 4096 /\ to_Z pn * 4096 + 4096 <= to_Z (rg_len rg).
Proof.
  intros Hg Hpn Hp. unfold page_atw in Hp.
  destruct (to_Z pn * 4096 + 4096 <=? to_Z (rg_len rg)) eqn:Ew; [|discriminate]. apply Z.leb_le in Ew.
  destruct (proj1 HMem t rg Hg) as [_ Hpages]. destruct (Hpages pn p Hpn Hp) as (Hok & Hlo & _ & _).
  rewrite (clim_full rg pn Ew) in Hok. split; [exact Hp|]. split; [exact Hok|]. split; [exact Hlo | exact Ew].
Qed.

Definition cell_lookup (t : int) (o : Z) : option fval :=
  if (0 <=? o) && (o <? b62z) && (o mod 8 =? 0) then
    let oi := of_Z o in
    match iget t M with
    | Some rg =>
        let pn := (oi >> 12)%uint63 in
        match page_atw rg t pn with
        | Some p => cell_at IM p pn ((oi land 4095) >> 3)%uint63
        | None => None
        end
    | None => None
    end
  else None.

Lemma of_Z_small o : 0 <= o < 2 ^ 62 -> to_Z (of_Z o) = o.
Proof. intros Ho. rewrite of_Z_spec. apply Z.mod_small. rewrite i63_wB. lia. Qed.

Lemma cell_lookup_sound t o fv :
  cell_lookup t o = Some fv ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o /\ o + 8 <= to_Z (rg_len rg)
    /\ forall j, (j < 8)%nat ->
         rview segs mem (adr rho t (o + Z.of_nat j)) = nth_error (wbytes8 (dv rho fv)) j.
Proof.
  unfold cell_lookup. intros Hc.
  destruct ((0 <=? o) && (o <? b62z) && (o mod 8 =? 0)) eqn:Eo; [|discriminate].
  apply andb_prop in Eo as [Eo E8]. apply andb_prop in Eo as [E0 E62].
  apply Z.leb_le in E0. apply Z.ltb_lt in E62. apply Z.eqb_eq in E8. unfold b62z in E62.
  destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
  set (oi := of_Z o) in *.
  assert (Hoi : to_Z oi = o) by (apply of_Z_small; lia).
  destruct (page_atw rg t (oi >> 12)%uint63) as [p|] eqn:Hp; [|discriminate].
  assert (Hpn : to_Z (oi >> 12)%uint63 = o / 4096) by (rewrite to_Z_lsr12, Hoi; reflexivity).
  assert (Hpn50 : to_Z (oi >> 12)%uint63 < 2 ^ 50).
  { rewrite Hpn. apply Z.div_lt_upper_bound; lia. }
  destruct (page_atw_ok rg t _ p Hg Hpn50 Hp) as (_ & Hpok & Hlo & Hhi).
  assert (Hci : to_Z ((oi land 4095) >> 3)%uint63 = (o mod 4096) / 8).
  { rewrite to_Z_lsr3, to_Z_land4095, Hoi. reflexivity. }
  exists rg. split; [reflexivity|]. rewrite Hpn in Hlo, Hhi.
  pose proof (off_decomp o E0) as Hdec. pose proof (cell_index_range o E0) as Hcr.
  assert (Hm8 : o mod 8 = 0) by exact E8.
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros j Hj. destruct Hpok as (_ & Hcells & _).
  specialize (Hcells _ fv ltac:(rewrite Hci; exact Hcr) Hc j Hj).
  rewrite Hpn, Hci in Hcells.
  replace (o + Z.of_nat j) with (o / 4096 * 4096 + o mod 4096 / 8 * 8 + Z.of_nat j) by lia.
  exact Hcells.
Qed.

(* [comment removed for export] *)
Lemma region_flat a t o n rg :
  aview VT M TL XT a = Some (t, o) -> iget t M = Some rg ->
  0 <= o -> 0 <= n -> o + n <= to_Z (rg_len rg) ->
  AX2S.flat E a n /\ AX2.adenot E a = adr rho t o
  /\ AX2S.estart E a = bv_unsigned (rho t) + o.
Proof.
  intros Hav Hg Ho Hn Hlen.
  pose proof (aview_sound rho xv xb VT M TL XT HM_regions Hrho0 HTL HXT a t o Hav) as Hs.
  pose proof (region_ok_nowrap' rho t rg (HM_regions t rg Hg)) as Hnw.
  pose proof (br_u64 (rho t)) as Hr.
  assert (Hf : AX2S.flat E a n) by (unfold AX2S.flat; rewrite Hs; lia).
  split; [exact Hf|]. split; [|exact Hs].
  apply bv_eq. rewrite (AX2S.flat_u _ _ _ Hf), Hs.
  rewrite (adr_unsigned rho t o Ho) by lia. reflexivity.
Qed.

Definition kword_ok (a : AX2.saddr) (w : nat) (v : AX2.expr) : bool :=
  Nat.eqb w 8
  && match aview VT M TL XT a with
     | Some (t, o) =>
         match cell_lookup t o with
         | Some fv => val_match VT TL XT TEQ v fv && visb t o 8
         | None => false
         end
     | None => false
     end.

Theorem kword_sound a w v :
  kword_ok a w v = true -> AX2S.kentry_ok segs E (mrestrict H mem) (AX2.KWord a w v).
Proof.
  unfold kword_ok. intros Hk. apply andb_prop in Hk as [Hw Hk]. apply Nat.eqb_eq in Hw. subst w.
  destruct (aview VT M TL XT a) as [[t o]|] eqn:Hav; [|discriminate].
  destruct (cell_lookup t o) as [fv|] eqn:Hc; [|discriminate].
  apply andb_prop in Hk as [Hvm Hvis].
  destruct (cell_lookup_sound t o fv Hc) as (rg & Hg & Hlo & Hhi & Hbytes).
  pose proof (i63_range (rg_lo rg)) as Hl0.
  destruct (region_flat a t o 8 rg Hav Hg ltac:(lia) ltac:(lia) Hhi) as (Hflat & Hadr & _).
  cbn [AX2S.kentry_ok]. split; [lia|]. split; [exact Hflat|].
  apply rdn_intro; [apply length_Z_to_le_bytes|].
  intros j Hj. rewrite Hadr, aoff_adr.
  rewrite rview_mrestrict by (apply (visb_sound t o 8 Hvis); lia).
  rewrite (Hbytes j Hj).
  rewrite (val_match_sound rho xv xb VT M TL XT TEQ HM_regions Hrho0 HTL HXT HTEQ v fv Hvm). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slots_lookup (t : int) (o : Z) : option slots :=
  if (0 <=? o) && (o <? b62z) then
    let oi := of_Z o in
    match iget t M with
    | Some rg =>
        let pn := (oi >> 12)%uint63 in
        match page_atw rg t pn with
        | Some p => Some (slots_at IM p pn ((oi land 4095) >> 3)%uint63)
        | None => None
        end
    | None => None
    end
  else None.

(* [comment removed for export] *)
Definition byte_match (e : AX2.expr) (j : Z) (sl : slot) : bool :=
  match sl with
  | SK b => match e with
            | AX2.ELit z => (to_Z b mod 256 =? (z / 2 ^ (8 * j)) mod 256)
            | _ => false
            end
  | SV v j' =>
      (to_Z j' =? j)
      && (val_match VT TL XT TEQ e v
          (* [comment removed for export] *)
          || ((j <? 4) && (vkind (vtag v) =? 2)%uint63
              && val_match VT TL XT TEQ e (FV (vbase (vtag v)) (vw v))))
  | SU => false
  end.

Fixpoint bytes_match (e : AX2.expr) (sls : slots) (bi j : Z) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => byte_match e j (sget (of_Z (bi + j)) sls) && bytes_match e sls bi (j + 1) k'
  end.

Definition slots_any (t : int) (o : Z) : option slots :=
  match slots_lookup t o with Some sls => Some sls | None => xslots t o end.

Definition kword_slots_ok (a : AX2.saddr) (w : nat) (v : AX2.expr) : bool :=
  (w <=? 8)%nat
  && match aview VT M TL XT a with
     | Some (t, o) =>
         (o mod 8 + Z.of_nat w <=? 8)
         && match slots_any t o with
            | Some sls => bytes_match v sls (o mod 8) 0 w && visb t o (Z.of_nat w)
            | None => false
            end
     | None => false
     end.

Lemma slots_lookup_sound t o sls :
  slots_lookup t o = Some sls ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o / 4096 * 4096 /\ o / 4096 * 4096 + 4096 <= to_Z (rg_len rg)
    /\ 0 <= o
    /\ slots_val rho sls (fun j => rview segs mem (adr rho t (o / 8 * 8 + Z.of_nat j))).
Proof.
  unfold slots_lookup. intros Hc.
  destruct ((0 <=? o) && (o <? b62z)) eqn:Eo; [|discriminate].
  apply andb_prop in Eo as [E0 E62]. apply Z.leb_le in E0. apply Z.ltb_lt in E62. unfold b62z in E62.
  destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
  set (oi := of_Z o) in *.
  assert (Hoi : to_Z oi = o) by (apply of_Z_small; lia).
  destruct (page_atw rg t (oi >> 12)%uint63) as [p|] eqn:Hp; [|discriminate].
  injection Hc as <-.
  assert (Hpn : to_Z (oi >> 12)%uint63 = o / 4096) by (rewrite to_Z_lsr12, Hoi; reflexivity).
  assert (Hpn50 : to_Z (oi >> 12)%uint63 < 2 ^ 50).
  { rewrite Hpn. apply Z.div_lt_upper_bound; lia. }
  destruct (page_atw_ok rg t _ p Hg Hpn50 Hp) as (_ & Hpok & Hlo & Hhi).
  assert (Hci : to_Z ((oi land 4095) >> 3)%uint63 = (o mod 4096) / 8).
  { rewrite to_Z_lsr3, to_Z_land4095, Hoi. reflexivity. }
  pose proof (cell_index_range o E0) as Hcr.
  exists rg. split; [reflexivity|]. rewrite Hpn in Hlo, Hhi. split; [exact Hlo|]. split; [exact Hhi|].
  split; [exact E0|].
  pose proof (slots_at_sound segs IM rho Hrho0 mem t _ 512 p _ Hpok ltac:(rewrite Hci; exact Hcr)) as Hs.
  eapply slots_val_ext; [|exact Hs]. intros j Hj. unfold cell_view. rewrite Hpn, Hci.
  f_equal. f_equal. Z.div_mod_to_equations. lia.
Qed.

Lemma slots_any_sound t o sls :
  slots_any t o = Some sls ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o / 8 * 8 /\ o / 8 * 8 + 8 <= to_Z (rg_len rg) /\ 0 <= o
    /\ slots_val rho sls (fun j => rview segs mem (adr rho t (o / 8 * 8 + Z.of_nat j))).
Proof.
  unfold slots_any. destruct (slots_lookup t o) as [s0|] eqn:Hl.
  - intros H0. injection H0 as <-.
    destruct (slots_lookup_sound t o s0 Hl) as (rg & Hg & Hlo & Hhi & Ho & Hsv).
    exists rg. split; [exact Hg|]. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    split; [exact Ho | exact Hsv].
  - apply xslots_sound.
Qed.

Lemma byte_mod64 z j : 0 <= j < 8 -> ((z mod 2 ^ 64) / 2 ^ (8 * j)) mod 256 = (z / 2 ^ (8 * j)) mod 256.
Proof.
  intros Hj.
  assert (Hp : 0 < 2 ^ (8 * j)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : 0 < 2 ^ (56 - 8 * j)) by (apply Z.pow_pos_nonneg; lia).
  assert (E64 : 2 ^ 64 = 2 ^ (8 * j) * (256 * 2 ^ (56 - 8 * j))).
  { rewrite Z.mul_assoc. change 256 with (2 ^ 8). rewrite <- !Z.pow_add_r by lia. f_equal. lia. }
  rewrite E64. rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm (2 ^ (8 * j)) ((z / 2 ^ (8 * j)) mod _)). rewrite Z.div_add by lia.
  rewrite (Z.div_small (z mod 2 ^ (8 * j))) by (apply Z.mod_pos_bound; lia). rewrite Z.add_0_l.
  apply Z.mod_mod_divide. exists (2 ^ (56 - 8 * j)). lia.
Qed.

Lemma lit_byte z j : 0 <= j < 8 ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z) / 2 ^ (8 * j)) = Z_to_bv 8 ((z / 2 ^ (8 * j)) mod 256).
Proof.
  intros Hj. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite <- (Z_to_bv8_mod (z mod 2 ^ 64 / 2 ^ (8 * j))). rewrite byte_mod64 by exact Hj. reflexivity.
Qed.

Lemma byte_match_sound e j sl ob :
  0 <= j < 8 -> byte_match e j sl = true -> slot_val rho sl ob ->
  ob = Some (Z_to_bv 8 (bv_unsigned (AX2.edenot E e) / 2 ^ (8 * j))).
Proof.
  intros Hj Hb Hs. destruct sl as [b | v j' |]; cbn [byte_match slot_val] in *; [| |discriminate].
  - destruct e as [z| | | | | | |]; try discriminate. apply Z.eqb_eq in Hb.
    cbn [AX2.edenot]. rewrite lit_byte by exact Hj. rewrite <- Hb, Z_to_bv8_mod. exact Hs.
  - apply andb_prop in Hb as [Hj' Hvm]. apply Z.eqb_eq in Hj'. apply orb_prop in Hvm as [Hvm|Hlo].
    + rewrite (val_match_sound rho xv xb VT M TL XT TEQ HM_regions Hrho0 HTL HXT HTEQ e v Hvm).
      rewrite Hs, Hj'. rewrite fk_wbytes8_nth by lia. rewrite Z2Nat.id by lia. reflexivity.
    + apply andb_prop in Hlo as [Hlo Hvm]. apply andb_prop in Hlo as [Hj4 Hk]. apply Z.ltb_lt in Hj4.
      apply Uint63.eqb_spec in Hk.
      rewrite (val_match_sound rho xv xb VT M TL XT TEQ HM_regions Hrho0 HTL HXT HTEQ e _ Hvm).
      rewrite (fk_dv_plain rho (FV (vbase (vtag v)) (vw v))) by (cbn [vtag]; apply fk_vbase_lt7). cbn [vtag vw].
      rewrite Hs, Hj'. unfold dv. rewrite Hk. change (dvk 2 ?x ?w) with (sx32 (bv_add x w)).
      rewrite (fk_bytes_sx32 _ (Z.to_nat j)) by lia.
      rewrite fk_wbytes8_nth by lia. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma bytes_match_sound e sls g bi : forall k j,
  0 <= bi -> 0 <= j -> bi + j + Z.of_nat k <= 8 ->
  bytes_match e sls bi j k = true -> slots_val rho sls g ->
  forall i, j <= i < j + Z.of_nat k ->
    g (Z.to_nat (bi + i)) = Some (Z_to_bv 8 (bv_unsigned (AX2.edenot E e) / 2 ^ (8 * i))).
Proof.
  induction k as [|k IH]; intros j Hbi Hj Hle Hm Hs i Hi; [lia|].
  cbn [bytes_match] in Hm. apply andb_prop in Hm as [Hm1 Hm2].
  destruct (Z.eq_dec i j) as [->|Hne].
  - assert (Hof : to_Z (of_Z (bi + j)) = bi + j) by (apply of_Z_small; lia).
    pose proof (slots_val_sget rho sls g (of_Z (bi + j)) Hs ltac:(rewrite Hof; lia)) as Hsv.
    rewrite Hof in Hsv. exact (byte_match_sound e j _ _ ltac:(lia) Hm1 Hsv).
  - apply (IH (j + 1)); try lia; assumption.
Qed.

Theorem kword_slots_sound a w v :
  kword_slots_ok a w v = true -> AX2S.kentry_ok segs E (mrestrict H mem) (AX2.KWord a w v).
Proof.
  unfold kword_slots_ok. intros Hk. apply andb_prop in Hk as [Hw Hk]. apply Nat.leb_le in Hw.
  destruct (aview VT M TL XT a) as [[t o]|] eqn:Hav; [|discriminate].
  apply andb_prop in Hk as [Hbi Hk]. apply Z.leb_le in Hbi.
  destruct (slots_any t o) as [sls|] eqn:Hc; [|discriminate].
  apply andb_prop in Hk as [Hbm Hvis].
  destruct (slots_any_sound t o sls Hc) as (rg & Hg & Hlo & Hhi & Ho & Hsv).
  pose proof (i63_range (rg_lo rg)) as Hl0.
  assert (Hin : o + Z.of_nat w <= to_Z (rg_len rg)) by (Z.div_mod_to_equations; lia).
  destruct (region_flat a t o (Z.of_nat w) rg Hav Hg Ho ltac:(lia) Hin) as (Hflat & Hadr & _).
  cbn [AX2S.kentry_ok]. split; [exact Hw|]. split; [exact Hflat|].
  apply rdn_intro; [apply length_Z_to_le_bytes|].
  intros j Hj. rewrite Hadr, aoff_adr.
  rewrite rview_mrestrict by (apply (visb_sound t o (Z.of_nat w) Hvis); lia).
  unfold word_to_le_bytes. rewrite Z_to_le_bytes_nth by exact Hj.
  pose proof (bytes_match_sound v sls _ (o mod 8) w 0 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)
                Hbm Hsv (Z.of_nat j) ltac:(lia)) as Hb.
  cbn beta in Hb. rewrite <- Hb. f_equal. f_equal.
  rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint pages_wr (rg : region) (t pn : int) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => match page_atw rg t pn with Some p => pg_wr p | None => false end
            && pages_wr rg t (pn + 1)%uint63 k'
  end.

Lemma pages_wr_spec rg t : forall k pn,
  to_Z pn + Z.of_nat k <= 2 ^ 50 ->
  pages_wr rg t pn k = true ->
  forall q, to_Z pn <= q < to_Z pn + Z.of_nat k ->
    exists p, page_atw rg t (of_Z q) = Some p /\ pg_wr p = true.
Proof.
  induction k as [|k IH]; intros pn Hb Hw q Hq; [lia|].
  cbn [pages_wr] in Hw. apply andb_prop in Hw as [Hp Hrest].
  pose proof (i63_range pn) as Hpn.
  destruct (Z.eq_dec q (to_Z pn)) as [->|Hne].
  - rewrite of_to_Z. destruct (page_atw rg t pn) as [p|]; [|discriminate]. exists p. split; [reflexivity | exact Hp].
  - assert (E1 : to_Z (pn + 1)%uint63 = to_Z pn + 1).
    { rewrite add_spec. change (to_Z 1) with 1. apply Z.mod_small. rewrite i63_wB. lia. }
    apply (IH (pn + 1)%uint63); [lia | exact Hrest | lia].
Qed.

(* [comment removed for export] *)
Definition range_wr (t : int) (o n : Z) : bool :=
  (0 <=? o) && (0 <? n) && (o + n <? b62z)
  && match iget t M with
     | Some rg =>
         (* [comment removed for export] *)
         if ((o + n - 1) / 4096 - o / 4096 + 1 <=? 4194304)
         then pages_wr rg t (of_Z (o / 4096)) (Z.to_nat ((o + n - 1) / 4096 - o / 4096 + 1)) else false
     | None => false
     end.

Lemma range_wr_sound t o n :
  range_wr t o n = true ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o /\ o + n <= to_Z (rg_len rg)
    /\ forall x, o <= x < o + n -> wview segs mem (adr rho t x) <> None.
Proof.
  unfold range_wr. intros Hr. apply andb_prop in Hr as [Hr Hp]. apply andb_prop in Hr as [Hr E62].
  apply andb_prop in Hr as [E0 En]. apply Z.leb_le in E0. apply Z.ltb_lt in En, E62. unfold b62z in E62.
  destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
  destruct ((o + n - 1) / 4096 - o / 4096 + 1 <=? 4194304); [|discriminate].
  exists rg. split; [reflexivity|].
  set (p0 := o / 4096) in *. set (p1 := (o + n - 1) / 4096) in *.
  assert (Hp01 : 0 <= p0 <= p1) by (unfold p0, p1; Z.div_mod_to_equations; lia).
  assert (Hp1 : p1 < 2 ^ 50) by (unfold p1; apply Z.div_lt_upper_bound; lia).
  assert (Hof : to_Z (of_Z p0) = p0) by (apply of_Z_small; lia).
  assert (Hkb : to_Z (of_Z p0) + Z.of_nat (Z.to_nat (p1 - p0 + 1)) <= 2 ^ 50) by (rewrite Hof; lia).
  pose proof (pages_wr_spec rg t _ (of_Z p0) Hkb Hp) as Hpages.
  rewrite Hof in Hpages.
  assert (Hpage : forall q, p0 <= q <= p1 ->
            to_Z (rg_lo rg) <= q * 4096 /\ q * 4096 + 4096 <= to_Z (rg_len rg)
            /\ forall j, 0 <= j < 4096 -> wview segs mem (adr rho t (q * 4096 + j)) <> None).
  { intros q Hq. destruct (Hpages q ltac:(lia)) as (p & Hpa & Hwr).
    assert (Hq' : to_Z (of_Z q) = q) by (apply of_Z_small; lia).
    destruct (page_atw_ok rg t (of_Z q) p Hg ltac:(rewrite Hq'; lia) Hpa) as (_ & (Hw & _) & Hlo & Hhi).
    rewrite Hq' in *. split; [exact Hlo|]. split; [exact Hhi|]. exact (Hw Hwr). }
  split; [|split].
  - destruct (Hpage p0 ltac:(lia)) as (Hlo & _). unfold p0 in Hlo. Z.div_mod_to_equations. lia.
  - destruct (Hpage p1 ltac:(lia)) as (_ & Hhi & _). unfold p1 in Hhi. Z.div_mod_to_equations. lia.
  - intros x Hx. destruct (Hpage (x / 4096)) as (_ & _ & Hw).
    { unfold p0, p1. split; apply Z.div_le_mono; lia. }
    specialize (Hw (x mod 4096) (Z.mod_pos_bound x 4096 ltac:(lia))).
    replace (x / 4096 * 4096 + x mod 4096) with x in Hw by (Z.div_mod_to_equations; lia).
    exact Hw.
Qed.

Definition wr_any (t : int) (o n : Z) : bool := range_wr t o n || xwrb t o n.

Lemma wr_any_sound t o n :
  wr_any t o n = true ->
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= o /\ o + n <= to_Z (rg_len rg)
    /\ forall x, o <= x < o + n -> wview segs mem (adr rho t x) <> None.
Proof. unfold wr_any. intros H0. apply orb_prop in H0 as [H0|H0]; [exact (range_wr_sound t o n H0) | exact (xwrb_sound t o n H0)]. Qed.

Definition kwr_ok (a : AX2.saddr) (n : AX2.expr) : bool :=
  match n, aview VT M TL XT a with
  | AX2.ELit len, Some (t, o) =>
      (0 <? len) && (len <? b62z) && wr_any t o len && visb t o len
  | _, _ => false
  end.

Lemma elen_lit len : 0 <= len < 2 ^ 64 -> AX2S.elenZ E (AX2.ELit len) = len.
Proof. intros Hl. unfold AX2S.elenZ. cbn [AX2.edenot]. apply br_lit_small. exact Hl. Qed.

Theorem kwr_sound a n :
  kwr_ok a n = true -> AX2S.kentry_ok segs E (mrestrict H mem) (AX2.KWr a n).
Proof.
  unfold kwr_ok. intros Hk. destruct n as [len| | | | | | |]; try discriminate.
  destruct (aview VT M TL XT a) as [[t o]|] eqn:Hav; [|discriminate].
  apply andb_prop in Hk as [Hk Hvis]. apply andb_prop in Hk as [Hk Hrw].
  apply andb_prop in Hk as [Hl0 Hl1]. apply Z.ltb_lt in Hl0, Hl1. unfold b62z in Hl1.
  destruct (wr_any_sound t o len Hrw) as (rg & Hg & Hlo & Hhi & Hw).
  pose proof (i63_range (rg_lo rg)) as Hrl.
  destruct (region_flat a t o len rg Hav Hg ltac:(lia) ltac:(lia) Hhi) as (Hflat & Hadr & Hst).
  cbn [AX2S.kentry_ok]. rewrite (elen_lit len) by lia. split; [exact Hflat|].
  intros d m Hd Hm. apply store_ok_intro. intros j Hj.
  pose proof (region_ok_nowrap' rho t rg (HM_regions t rg Hg)) as Hnw. pose proof (br_u64 (rho t)) as Hr.
  assert (Ea : aoff (Z_to_bv 64 (AX2S.estart E a + d)) j = adr rho t (o + (d + Z.of_nat j))).
  { rewrite Hst. unfold aoff, adr. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia. }
  rewrite Ea. rewrite wview_mrestrict by (apply (visb_sound t o len Hvis); lia).
  apply Hw. lia.
Qed.

Definition kunk_ok (a : AX2.saddr) (n : AX2.expr) : bool :=
  match n, aview VT M TL XT a with
  | AX2.ELit len, Some (t, o) =>
      (0 <? len) && (len <? b62z) && wr_any t o len && visb t o len && nosegb t o len
  | _, _ => false
  end.

Theorem kunk_sound a n :
  kunk_ok a n = true -> AX2S.kentry_ok segs E (mrestrict H mem) (AX2.KUnk a n).
Proof.
  unfold kunk_ok. intros Hk. destruct n as [len| | | | | | |]; try discriminate.
  destruct (aview VT M TL XT a) as [[t o]|] eqn:Hav; [|discriminate].
  apply andb_prop in Hk as [Hk Hns]. apply andb_prop in Hk as [Hk Hvis]. apply andb_prop in Hk as [Hk Hrw].
  apply andb_prop in Hk as [Hl0 Hl1]. apply Z.ltb_lt in Hl0, Hl1. unfold b62z in Hl1.
  destruct (wr_any_sound t o len Hrw) as (rg & Hg & Hlo & Hhi & Hw).
  pose proof (i63_range (rg_lo rg)) as Hrl.
  destruct (region_flat a t o len rg Hav Hg ltac:(lia) ltac:(lia) Hhi) as (Hflat & Hadr & Hst).
  cbn [AX2S.kentry_ok]. rewrite (elen_lit len) by lia. split; [exact Hflat|].
  intros i Hi.
  pose proof (region_ok_nowrap' rho t rg (HM_regions t rg Hg)) as Hnw. pose proof (br_u64 (rho t)) as Hr.
  assert (Ea : Z_to_bv 64 (AX2S.estart E a + i) = adr rho t (o + i)).
  { rewrite Hst. unfold adr. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia. }
  rewrite Ea. unfold mrestrict. rewrite (visb_sound t o len Hvis i Hi).
  destruct (nosegb_sound t o len Hns i Hi) as [Hdef|Hnsg]; [exact Hdef|].
  specialize (Hw (o + i) ltac:(lia)). unfold wview in Hw.
  destruct (mem (adr rho t (o + i))) as [b|]; [discriminate|].
  rewrite Hnsg in Hw. congruence.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fv_zero (v : fval) : bool := (vtag v =? 0)%uint63 && (wZ (vw v) =? 0).

Fixpoint cells_zero (p : page) (pn ci : int) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => match cell_at IM p pn ci with Some v => fv_zero v | None => false end
            && cells_zero p pn (ci + 1)%uint63 k'
  end.

Definition page_blank (p : page) : bool :=
  match pg_kind p, pg_cells p with
  | PKZero, IEmpty => true
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition page_zero (rg : region) (t pn : int) (c0 : int) (k : nat) : bool :=
  match page_atw rg t pn with
  | Some p => if page_blank p then true else cells_zero p pn c0 k     (* [comment removed for export] *)
  | None => false
  end.

(* [comment removed for export] *)
Fixpoint zero_pages_b (rg : region) (t : int) (lo hi : Z) (fuel : nat) : bool :=
  match fuel with
  | O => lo >=? hi
  | S f =>
      if lo >=? hi then true
      else
        let pn := lo / 512 in
        let top := Z.min hi ((pn + 1) * 512) in
        page_zero rg t (of_Z pn) (of_Z (lo - pn * 512)) (Z.to_nat (top - lo))
        && zero_pages_b rg t top hi f
  end.

Definition range_zero (t : int) (o n : Z) : bool :=
  (0 <=? o) && (0 <? n) && (o + n <? b62z) && (o mod 8 =? 0) && (n mod 8 =? 0)
  && match iget t M with
     | Some rg => if ((o + n) / 4096 - o / 4096 + 2 <=? 4194304)
                  then zero_pages_b rg t (o / 8) ((o + n) / 8) (Z.to_nat ((o + n) / 4096 - o / 4096 + 2)) else false
     | None => false
     end.

Lemma fv_zero_bytes v j : fv_zero v = true -> (j < 8)%nat ->
  nth_error (wbytes8 (dv rho v)) j = Some (Z_to_bv 8 0).
Proof.
  intros Hz Hj. destruct v as [t w]. unfold fv_zero in Hz. cbn [vtag vw] in Hz.
  apply andb_prop in Hz as [Ht Hw]. apply Uint63.eqb_spec in Ht. apply Z.eqb_eq in Hw. subst t.
  rewrite (fk_dv_conc rho w Hrho0). rewrite fk_wbytes8_nth by exact Hj. rewrite wbv_unsigned, Hw.
  rewrite Z.div_0_l; [reflexivity|]. apply Z.pow_nonzero; lia.
Qed.

Lemma cells_zero_spec p pn : forall k ci,
  to_Z ci + Z.of_nat k <= 512 ->
  cells_zero p pn ci k = true ->
  forall c, to_Z ci <= c < to_Z ci + Z.of_nat k ->
    exists v, cell_at IM p pn (of_Z c) = Some v /\ fv_zero v = true.
Proof.
  induction k as [|k IH]; intros ci Hb Hz c Hc; [lia|].
  cbn [cells_zero] in Hz. apply andb_prop in Hz as [Hh Hr]. pose proof (i63_range ci) as Hci.
  destruct (Z.eq_dec c (to_Z ci)) as [->|Hne].
  - rewrite of_to_Z. destruct (cell_at IM p pn ci) as [v|]; [|discriminate]. exists v. split; [reflexivity | exact Hh].
  - assert (E1 : to_Z (ci + 1)%uint63 = to_Z ci + 1).
    { rewrite add_spec. change (to_Z 1) with 1. apply Z.mod_small. rewrite i63_wB. lia. }
    apply (IH (ci + 1)%uint63); [lia | exact Hr | lia].
Qed.

Lemma page_blank_cell p pn ci : page_blank p = true -> cell_at IM p pn ci = Some fv0.
Proof.
  unfold page_blank, cell_at. destruct (pg_kind p); try discriminate.
  destruct (pg_cells p); try discriminate. intros _. reflexivity.
Qed.

Lemma page_zero_spec rg t pn c0 k :
  iget t M = Some rg -> 0 <= pn < 2 ^ 50 -> 0 <= c0 -> c0 + Z.of_nat k <= 512 ->
  page_zero rg t (of_Z pn) (of_Z c0) k = true ->
  to_Z (rg_lo rg) <= pn * 4096 /\ pn * 4096 + 4096 <= to_Z (rg_len rg)
  /\ forall c, c0 <= c < c0 + Z.of_nat k -> forall j, (j < 8)%nat ->
       rview segs mem (adr rho t (pn * 4096 + c * 8 + Z.of_nat j)) = Some (Z_to_bv 8 0).
Proof.
  intros Hg Hpn Hc0 Hck Hz. unfold page_zero in Hz.
  assert (Hpn' : to_Z (of_Z pn) = pn) by (apply of_Z_small; lia).
  assert (Hc0' : to_Z (of_Z c0) = c0) by (apply of_Z_small; lia).
  destruct (page_atw rg t (of_Z pn)) as [p|] eqn:Hp; [|discriminate].
  destruct (page_atw_ok rg t _ p Hg ltac:(rewrite Hpn'; lia) Hp) as (_ & (_ & Hcells & _) & Hlo & Hhi).
  rewrite Hpn' in *. split; [exact Hlo|]. split; [exact Hhi|].
  intros c Hc j Hj.
  assert (Hc' : to_Z (of_Z c) = c) by (apply of_Z_small; lia).
  assert (Hv : exists v, cell_at IM p (of_Z pn) (of_Z c) = Some v /\ fv_zero v = true).
  { apply orb_prop in Hz as [Hz|Hz].
    - exists fv0. split; [apply page_blank_cell; exact Hz | reflexivity].
    - apply (cells_zero_spec p (of_Z pn) k (of_Z c0)); [rewrite Hc0'; lia | exact Hz | rewrite Hc0'; lia]. }
  destruct Hv as (v & Hv1 & Hv2).
  specialize (Hcells (of_Z c) v ltac:(rewrite Hc'; lia) Hv1 j Hj). rewrite Hc' in Hcells.
  rewrite Hcells. apply fv_zero_bytes; assumption.
Qed.

Lemma zero_pages_spec rg t : iget t M = Some rg -> forall fuel lo hi,
  0 <= lo -> hi <= 2 ^ 59 ->
  zero_pages_b rg t lo hi fuel = true ->
  forall c, lo <= c < hi ->
    to_Z (rg_lo rg) <= c * 8 /\ c * 8 + 8 <= to_Z (rg_len rg)
    /\ forall j, (j < 8)%nat -> rview segs mem (adr rho t (c * 8 + Z.of_nat j)) = Some (Z_to_bv 8 0).
Proof.
  intros Hg. induction fuel as [|f IH]; intros lo hi Hlo Hhi Hz c Hc; cbn [zero_pages_b] in Hz.
  - apply Z.geb_le in Hz. lia.
  - destruct (lo >=? hi) eqn:Ege; [apply Z.geb_le in Ege; lia|].
    apply andb_prop in Hz as [Hpz Hrest].
    set (pn := lo / 512) in *. set (top := Z.min hi ((pn + 1) * 512)) in *.
    assert (Hpn : 0 <= pn < 2 ^ 50).
    { unfold pn. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
    assert (Hlop : pn * 512 <= lo < (pn + 1) * 512) by (unfold pn; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec c top) as [Hct|Hct].
    + destruct (page_zero_spec rg t pn (lo - pn * 512) (Z.to_nat (top - lo)) Hg Hpn ltac:(lia)
                  ltac:(unfold top; lia) Hpz) as (Hrlo & Hrhi & Hcells).
      specialize (Hcells (c - pn * 512) ltac:(unfold top in *; lia)).
      split; [lia|]. split; [unfold top in *; lia|].
      intros j Hj. specialize (Hcells j Hj).
      replace (pn * 4096 + (c - pn * 512) * 8 + Z.of_nat j) with (c * 8 + Z.of_nat j) in Hcells by lia.
      exact Hcells.
    + apply (IH top hi); [unfold top; lia | exact Hhi | exact Hrest | lia].
Qed.

(* [comment removed for export] *)
Definition slot_zero (sl : slot) : bool :=
  match sl with SK b => (to_Z b mod 256 =? 0) | _ => false end.

Lemma slot_zero_sound sl ob : slot_zero sl = true -> slot_val rho sl ob -> ob = Some (Z_to_bv 8 0).
Proof.
  destruct sl as [b | v j |]; cbn [slot_zero slot_val]; try discriminate.
  intros Hz ->. apply Z.eqb_eq in Hz. rewrite <- (Z_to_bv8_mod (to_Z b)), Hz. reflexivity.
Qed.

Fixpoint zero_bytes_b (t : int) (o : Z) (k : nat) : bool :=
  match k with
  | O => true
  | S k' =>
      match slots_any t o with
      | Some sls => slot_zero (sget (of_Z (o mod 8)) sls)
      | None => false
      end && zero_bytes_b t (o + 1) k'
  end.

Definition kzero_ok (a : AX2.saddr) (n : AX2.expr) : bool :=
  match n, aview VT M TL XT a with
  | AX2.ELit len, Some (t, o) =>
      (* [comment removed for export] *)
      (if range_zero t o len then true
       else (if (0 <? len) && (len <=? 65536) then zero_bytes_b t o (Z.to_nat len) else false))
      && visb t o len && nosegb t o len
  | _, _ => false
  end.

Lemma zero_bytes_spec t : forall k o, 0 <= o ->
  zero_bytes_b t o k = true ->
  forall i, 0 <= i < Z.of_nat k ->
    rview segs mem (adr rho t (o + i)) = Some (Z_to_bv 8 0)
    /\ exists rg, iget t M = Some rg /\ o + i + 1 <= to_Z (rg_len rg).
Proof.
  induction k as [|k IH]; intros o Ho Hz i Hi; [lia|].
  cbn [zero_bytes_b] in Hz. apply andb_prop in Hz as [Hh Hr].
  destruct (Z.eq_dec i 0) as [->|Hne].
  - destruct (slots_any t o) as [sls|] eqn:Hs; [|discriminate].
    destruct (slots_any_sound t o sls Hs) as (rg & Hg & Hlo & Hhi & _ & Hsv).
    assert (Hof : to_Z (of_Z (o mod 8)) = o mod 8) by (apply of_Z_small; Z.div_mod_to_equations; lia).
    pose proof (slots_val_sget rho sls _ (of_Z (o mod 8)) Hsv ltac:(rewrite Hof; Z.div_mod_to_equations; lia)) as Hsl.
    rewrite Hof in Hsl. cbn beta in Hsl.
    pose proof (slot_zero_sound _ _ Hh Hsl) as Hb.
    rewrite Z2Nat.id in Hb by (Z.div_mod_to_equations; lia).
    replace (o / 8 * 8 + o mod 8) with o in Hb by (Z.div_mod_to_equations; lia).
    rewrite Z.add_0_r. split.
    + exact Hb.
    + exists rg. split; [exact Hg|]. Z.div_mod_to_equations. lia.
  - destruct (IH (o + 1) ltac:(lia) Hr (i - 1) ltac:(lia)) as [Hb Hrg].
    replace (o + 1 + (i - 1)) with (o + i) in * by lia. split; [exact Hb|].
    destruct Hrg as (rg & Hg & Hle). exists rg. split; [exact Hg | lia].
Qed.

Lemma rview_noseg x b : rview segs mem x = Some b -> find_segment segs (bv_unsigned x) 1 = None -> mem x = Some b.
Proof.
  unfold rview. destruct (mem x) as [b'|]; [tauto|]. intros Hr Hn.
  unfold memory_read in Hr. change (Z.of_N 1) with 1 in Hr. rewrite Hn in Hr. discriminate.
Qed.

Lemma rview_ov x b : rview segs mem x = Some b ->
  mem x <> None \/ find_segment segs (bv_unsigned x) 1 = None -> mem x = Some b.
Proof.
  intros Hr [Hd|Hn]; [|exact (rview_noseg x b Hr Hn)].
  unfold rview in Hr. destruct (mem x) as [b'|]; [exact Hr | contradiction].
Qed.

Theorem kzero_sound a n :
  kzero_ok a n = true -> AX2S.kentry_ok segs E (mrestrict H mem) (AX2.KZero a n).
Proof.
  unfold kzero_ok. intros Hk. destruct n as [len| | | | | | |]; try discriminate.
  destruct (aview VT M TL XT a) as [[t o]|] eqn:Hav; [|discriminate].
  apply andb_prop in Hk as [Hk Hns]. apply andb_prop in Hk as [Hrz Hvis].
  apply orb_prop in Hrz as [Hrz|Hzb].
  2:{ (* [comment removed for export] *)
    destruct ((0 <? len) && (len <=? 65536)) eqn:Hzb0; [|discriminate]. rename Hzb into Hz.
    apply andb_prop in Hzb0 as [Hl0 Hl1]. apply Z.ltb_lt in Hl0. apply Z.leb_le in Hl1.
    assert (Ho0 : 0 <= o).
    { destruct (Z.to_nat len) as [|k0] eqn:Ek; [lia|]. cbn [zero_bytes_b] in Hz. apply andb_prop in Hz as [Hh _].
      destruct (slots_any t o) as [sls|] eqn:Hs; [|discriminate].
      destruct (slots_any_sound t o sls Hs) as (_ & _ & _ & _ & Ho & _). exact Ho. }
    pose proof (zero_bytes_spec t _ o Ho0 Hz) as Hsp. rewrite Z2Nat.id in Hsp by lia.
    destruct (Hsp (len - 1) ltac:(lia)) as (_ & rg & Hg & Hlen).
    destruct (region_flat a t o len rg Hav Hg Ho0 ltac:(lia) ltac:(lia)) as (Hflat & Hadr & Hst).
    cbn [AX2S.kentry_ok]. rewrite (elen_lit len) by lia. split; [exact Hflat|].
    intros i Hi.
    pose proof (region_ok_nowrap' rho t rg (HM_regions t rg Hg)) as Hnw. pose proof (br_u64 (rho t)) as Hr.
    assert (Ea : Z_to_bv 64 (AX2S.estart E a + i) = adr rho t (o + i)).
    { rewrite Hst. unfold adr. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia. }
    rewrite Ea. unfold mrestrict. rewrite (visb_sound t o len Hvis i Hi).
    apply rview_ov; [|exact (nosegb_sound t o len Hns i Hi)].
    exact (proj1 (Hsp i Hi)). }
  unfold range_zero in Hrz. apply andb_prop in Hrz as [Hrz Hzp]. apply andb_prop in Hrz as [Hrz Hn8].
  apply andb_prop in Hrz as [Hrz Ho8]. apply andb_prop in Hrz as [Hrz H62]. apply andb_prop in Hrz as [Ho0 Hn0].
  apply Z.leb_le in Ho0. apply Z.ltb_lt in Hn0, H62. apply Z.eqb_eq in Ho8, Hn8. unfold b62z in H62.
  destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
  destruct ((o + len) / 4096 - o / 4096 + 2 <=? 4194304); [|discriminate].
  pose proof (zero_pages_spec rg t Hg _ (o / 8) ((o + len) / 8) ltac:(apply Z.div_pos; lia)
                ltac:(apply Z.div_le_upper_bound; lia) Hzp) as Hcells.
  assert (Hlen : o + len <= to_Z (rg_len rg)).
  { destruct (Hcells ((o + len) / 8 - 1)) as (_ & Hhi & _); Z.div_mod_to_equations; lia. }
  destruct (region_flat a t o len rg Hav Hg Ho0 ltac:(lia) Hlen) as (Hflat & Hadr & Hst).
  cbn [AX2S.kentry_ok]. rewrite (elen_lit len) by lia. split; [exact Hflat|].
  intros i Hi.
  pose proof (region_ok_nowrap' rho t rg (HM_regions t rg Hg)) as Hnw. pose proof (br_u64 (rho t)) as Hr.
  assert (Ea : Z_to_bv 64 (AX2S.estart E a + i) = adr rho t (o + i)).
  { rewrite Hst. unfold adr. apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). Z.div_mod_to_equations. lia. }
  rewrite Ea. unfold mrestrict. rewrite (visb_sound t o len Hvis i Hi).
  apply rview_ov; [|exact (nosegb_sound t o len Hns i Hi)].
  destruct (Hcells ((o + i) / 8) ltac:(Z.div_mod_to_equations; lia)) as (_ & _ & Hb).
  specialize (Hb (Z.to_nat ((o + i) mod 8)) ltac:(Z.div_mod_to_equations; lia)).
  rewrite Z2Nat.id in Hb by (Z.div_mod_to_equations; lia).
  replace ((o + i) / 8 * 8 + (o + i) mod 8) with (o + i) in Hb by (Z.div_mod_to_equations; lia).
  exact Hb.
Qed.

End Mem.
