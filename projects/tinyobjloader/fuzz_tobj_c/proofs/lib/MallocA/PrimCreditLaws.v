(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "div"; "sub"; "to_nat"; "mul"; "max"; "lt"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "class_state"; "cs_empty"; "aa_cls"; "cs_mapped_free_array"; "cs_mapped_user"; "AA"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "prim_credit"; "FACAP"; "MUCAP"; "sumZ"; "credit_c"; "CLS30"; "PRIM0"; "qmax"; "@Stdlib.Lists.List"; "In"; "NoDup"; "@Corelib.Init.Datatypes"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "kFreeArrayMapSize"; "kFreeArraySize"; "kUserSpaceSize"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model PrimCredit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma In_CLS30 : ltac2:(tb__ "0|0|
S0SdS1dS0R1S1aA3SbS1Z1R1A2S1R1Z1eA2A2A2Fc;").
Proof.
  intros c. unfold CLS30. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hc. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma NoDup_CLS30 : NoDup CLS30.
Proof. apply (NoDup_map_inv (fun z => Z.to_nat z)). unfold CLS30. rewrite map_map. rewrite (map_ext _ (fun k => k)) by (intros k; lia). rewrite map_id. apply seq_NoDup. Qed.

Lemma sumZ_ext : ltac2:(tb__ "0|1|
S0S0Fx;M0G0S1fS0A1S0S1dS0R1R2A3SaS0R4R2A1R5R2A1A3F_;Fx;SaS0S18R3R2A2S18R4R2A2A3F_;Fl;Fg;Ff;").
Proof.
  intros f g. induction l as [|x l IH]; intros H; [reflexivity|].
  change (g x + sumZ g l = f x + sumZ f l). rewrite (H x (or_introl eq_refl)), (IH (fun y Hy => H y (or_intror Hy))). reflexivity.
Qed.
Lemma sumZ_upd : ltac2:(tb__ "0|1|
S0S0Fx;M0G0S1fS0A1S0S1eS0R2A2S1dS0R2R3A3S0S1dS0R1R5A3ScSaS0R2R5A3A1SaS0R8R3A1R9R3A1A3F_;F_;Fx;SaS0S18R6R5A2S2S5S18R7R5A2R7R4A1A2R6R4A1A2A3F_;F_;F_;Fc;Fl;Fg;Ff;").
Proof.
  intros f g. induction l as [|x l IH]; intros c ND Hin H; [destruct Hin|].
  change (g x + sumZ g l = f x + sumZ f l - f c + g c). inversion ND as [|? ? Hx ND']; subst.
  destruct Hin as [->|Hin].
  - rewrite (sumZ_ext f g l); [lia|]. intros y Hy. apply H; [right; exact Hy|]. intros ->. exact (Hx Hy).
  - rewrite (IH c ND' Hin (fun y Hy Hne => H y (or_intror Hy) Hne)). rewrite (H x (or_introl eq_refl)); [lia|]. intros ->. exact (Hx Hin).
Qed.

Lemma cap_facts : ltac2:(tb__ "0|5|
S0SbS1Z1R1A2S1R1Z1eA2A2SbSbS1Z20S20R2A1M0A2S1G0Z10000A2A2SbSaS0S3G0Z10A2Z0M1A3SbS1S17R2A1M2S23A2SbSaS0S3G2Z8M3A2G1A3SbS1S16R2A1M4S22A2SbSaS0S3G4G3A2G1A3SbS1S2S7Z4S4G2G0A2A2S21A2G4A2S1G1S1cR2A1A2A2A2A2A2A2A2A2F_;Fc;").
Proof.
  intros c Hc. pose proof (proj1 (forallb_forall _ _) cap_okb_all c (proj2 (In_CLS30 c) Hc)) as H. unfold cap_okb in H.
  repeat (apply andb_prop in H as [H ?]).
  repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X | X : (_ =? _) = true |- _ => apply Z.eqb_eq in X end.
  repeat split; assumption.
Qed.

Lemma prim_credit_maps : ltac2:(tb__ "0|3|
S13S13S0SbS1Z1R1A2S1R1Z1eA2A2SbSaS0S12S14SeS6R2A1M0S10R3A1SfA4M1A1S12S14SeG0S10R4A1SfA4M2A1A3SaS0S11G1A1S11G2A1A3A2F_;Fc;SaS0S15R2A1S15R3A1A3F_;FA';FA;").
Proof.
  intros A A' H. unfold prim_credit. apply sumZ_ext. intros c Hc. apply In_CLS30 in Hc. destruct (H c Hc) as [E1 E2].
  unfold credit_c, creditU, creditF. cbn zeta. rewrite E1, E2. reflexivity.
Qed.

Lemma prim_credit_upd1 : ltac2:(tb__ "0|2|
S13S13S0SbS1Z1R1A2S1R1Z1eA2A2M0S0G0ScSaS0R2R4A3A1SaSeS14SeS6R3A1M1S10R6A1SfA4S14SeG1S10R7A1SfA4A3F_;F_;Fc';SaS0S15R4A1S2S5S15R5A1S19R5R3A2A2S19R4R3A2A2A3F_;F_;Fc;FA';FA;").
Proof.
  intros A A' c Hc Ho. unfold prim_credit. apply sumZ_upd; [exact NoDup_CLS30 | apply In_CLS30; exact Hc |].
  intros x Hx Hne. apply In_CLS30 in Hx. unfold credit_c. cbn zeta. rewrite (Ho x Hx Hne). reflexivity.
Qed.

Lemma credit_grow : ltac2:(tb__ "0|5|
S0S0S0SaS0S3R2Z8M0A2Z0M1A3M2G2SaS0S3R5G0A2G1A3SbS1R5R4A2S1R4R6A2A2SaS0S2S8G1S4S7Z9M3S5R7R5A2A2G0A2A2S2S5R5R6A2M4S4G4G0A2A2A2S8G1S4S7G3S5R7R6A2A2G0A2A2A3F_;F_;F_;F_;Fm';Fm;Fcap;").
Proof. intros cap m m' H1 H2 H3 H4. Z.div_mod_to_equations. lia. Qed.

Lemma prim_credit_populate : ltac2:(tb__ "0|9|
S13S13S0SbS1Z1R1A2S1R1Z1eA2A2M0S0G0ScSaS0R2R4A3A1SaSeS14SeS6R3A1M1S10R6A1SfA4S14SeG1S10R7A1SfA4A3F_;F_;Fc';S14SeG1S10R5A1M2SfA4SeS14SeS6R4A1G2SfA4SeSaS0S3S12R2A1Z8M3A2Z0M4A3M5G5SbS1S12R4A1S12R3A1M6A2S1G6S17R7A1A2A2SaS0S3S11R5A1G3A2G4A3M7G7SbS1S11R7A1S11R6A1M8A2S1G8S16RaA1A2A2S5S12R7A1S12R8A1A2S0S5S11R8A1S11R9A1A2S0SaS0S2S2S15ReA1S2R2S4R2G3A2A2A2S2R1S4R1G3A2A2A2S15RfA1A3Tdf;Tdu;F_;F_;F_;F_;F_;F_;Tcs';Tcs;F_;F_;Fc;FA';FA;").
Proof.
  intros A A' c Hc Ho cs cs' U1 U2 U3 F1 F2 F3 du df.
  rewrite (prim_credit_upd1 A A' c Hc Ho). unfold credit_c, creditU, creditF. cbn zeta. fold cs cs'.
  destruct (cap_facts c Hc) as (_ & _ & _ & MC8 & _ & FC8 & _).
  pose proof (credit_grow (MUCAP c) (cs_mapped_user cs) (cs_mapped_user cs') U1 U2 MC8 U3) as EU.
  pose proof (credit_grow (FACAP c) (cs_mapped_free_array cs) (cs_mapped_free_array cs') F1 F2 FC8 F3) as EF.
  fold du in EU. fold df in EF.
  set (u := Z.max 0 (9 * (MUCAP c - cs_mapped_user cs) / 8)) in *. set (u' := Z.max 0 (9 * (MUCAP c - cs_mapped_user cs') / 8)) in *.
  set (f := Z.max 0 (9 * (FACAP c - cs_mapped_free_array cs) / 8)) in *. set (f' := Z.max 0 (9 * (FACAP c - cs_mapped_free_array cs') / 8)) in *.
  set (pc := prim_credit A). set (x := du + du / 8) in *. set (y := df + df / 8) in *. clearbody u u' f f' pc x y. clear -EU EF. lia.
Qed.

Lemma prim_credit_famap : ltac2:(tb__ "0|8|
S13S13S0SbS1Z1R1A2S1R1Z1eA2A2M0S0G0ScSaS0R2R4A3A1SaSeS14SeS6R3A1M1S10R6A1SfA4S14SeG1S10R7A1SfA4A3F_;F_;Fc';S14SeG1S10R5A1M2SfA4SeS14SeS6R4A1G2SfA4SeSaS0S12R1A1S12R2A1A3SaS0S3S12R3A1Z8M3A2Z0M4A3S1S12R4A1S17R7A1A2SaS0S3S11R5A1G3A2G4A3M5G5SbS1S11R7A1M6S11R6A1M7A2S1G7S16RaA1A2A2S5G6S11R8A1A2S0SaS0S2S15RdA1S2R1S4R1G3A2A2A2S15ReA1A3Tdf;F_;F_;F_;F_;F_;F_;Tcs';Tcs;F_;F_;Fc;FA';FA;").
Proof.
  intros A A' c Hc Ho cs cs' EU U1 U3 F1 F2 F3 df.
  pose proof (prim_credit_populate A A' c Hc Ho U1 ltac:(fold cs'; rewrite EU; exact U1) ltac:(fold cs cs'; rewrite EU; lia) F1 F2 F3) as P.
  cbn zeta in P. fold cs cs' in P. rewrite EU in P. replace (cs_mapped_user cs - cs_mapped_user cs) with 0 in P by lia. change (0 / 8) with 0 in P. fold df in P. lia.
Qed.

Lemma facap_of_mucap : ltac2:(tb__ "0|1|
S0S0S0S0S0SbS1Z1R5A2S1R5Z1eA2A2SbS1Z0M0R5A2S1R5R4A2A2S1R5S17R7A1A2S1G0R4A2S1R5S4R8S20R9A1A2A2S9R7S2S7Z4R6A2S21A2A2S1R8S16RbA1A2F_;F_;F_;F_;F_;F_;Ftotal;Fmfa';Fmu;Fau;Fc;").
Proof.
  intros c au mu mfa' total Hc Hau Hmu Ht0 Ht Hm. destruct (cap_facts c Hc) as (HS & _ & _ & _ & _ & _ & HF & _).
  assert (au / Size c <= MUCAP c / Size c) by (apply Z.div_le_mono; [clear -HS; lia | clear -Hau Hmu; lia]).
  set (x := au / Size c) in *. set (y := MUCAP c / Size c) in *. set (k := kFreeArrayMapSize) in *. clearbody x y k. clear -Ht H Hm HF. lia.
Qed.

Lemma prim_credit_init : ltac2:(tb__ "0|0|
S13S0SbS1Z1R1A2S1R1Z1eA2A2SaSeS14SeS6R2A1S10R3A1SfA4SfA3F_;Fc;SaS0S15R2A1S1bA3F_;FA;").
Proof.
  intros A Hc. unfold prim_credit, PRIM0. apply sumZ_ext. intros c Hin. apply In_CLS30 in Hin.
  unfold credit_c, creditU, creditF. cbn zeta. rewrite (Hc c Hin). cbn [cs_mapped_user cs_mapped_free_array cs_empty]. rewrite !Z.sub_0_r.
  destruct (cap_facts c Hin) as (HS & _ & _ & _ & _ & _ & HF & HQ).
  assert (0 <= MUCAP c). { unfold MUCAP, PRIM_LIVE_MAX, kUserMapSize. set (s := Size c) in *. set (q := qmax c) in *. clearbody s q. clear -HS HQ. nia. }
  assert (0 <= FACAP c). { assert (0 <= MUCAP c / Size c) by (apply Z.div_pos; [assumption | clear -HS; lia]). unfold kFreeArrayMapSize in HF. set (y := MUCAP c / Size c) in *. clearbody y. clear -HF H0. lia. }
  rewrite !Z.max_r by (apply Z.div_pos; lia). reflexivity.
Qed.
