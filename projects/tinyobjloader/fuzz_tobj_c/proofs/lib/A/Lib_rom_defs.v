(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "of_nat"; "lt"; "sub"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "@Corelib.Init.Datatypes"; "fst"; "option"; "prod"; "Some"; "list"; "nat"; "snd"; "length"; "nil"; "S"; "app"; "cons"; "None"; "@Stdlib.Lists.List"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_rom_defs"; "lines_ok"; "decodes"; "dec_ent"; "tail_sum"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Lists.ListDef"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "rd64"; "@Stdlib.Arith.PeanoNat.Nat"; "pred"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjArena.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition dec_ent (m : word -> option byte) (a : Z) (p : Z * Z) : Prop := ltac2:(tb__ "0|1|
S8S7SbS0A1M0S1fVm;Va;A2SdS0SaS0S0Vp;A3A2A3S7G0S1fVm;S1Va;Z8A2A2SdS0S10S0S0Vp;A3A2A3A2").

Fixpoint decodes (m : word -> option byte) (d : Z) (T : list (Z * Z)) : Prop :=
  match T with
  | [] => True
  | p :: r => dec_ent m d p /\ decodes m (d + 16) r
  end.

Definition lines_ok (T : list (Z * Z)) (L : Z) : Prop := ltac2:(tb__ "0|6|
S8SfScS0S0A2M0S7SbG0A1M1S17G0VT;R2A3SdG0R1A2A3S8S2Z0M2SaS0S0R2A3M3A2S8S2G2S10S0S0R2A3M4A2S2S1G3G4A2VL;A2A2A2F_;Fp;Fk;SfG0G0S7G1S17G0VT;R3A3SdG0R2A2M5A3S7G1S17G0VT;S13R4A1A3G5A3S2S1S1SaS0S0R4A3S10S0S0R4A3A2Z1A2SaS0S0R3A3A2F_;F_;Fq;Fp;Fk;A2").

Lemma decodes_nth : ltac2:(tb__ "0|1|
S1cQ40A1SbS1cQ8A1A1F_;SeScS0S0A2M0A1S0SfG0S19R5R3R4A3S7SbG0A1S17G0R5R3A3SdG0R2A2A3S1aR7S1R5S3Z10S4R4A1A2A2R3A3F_;F_;Fp;Fk;Fd;FT;Fm;").
Proof.
  intros m T. induction T as [|q r IH]; intros d [|k] p HD Hk; cbn in Hk; try discriminate.
  - injection Hk as ->. rewrite Z.mul_0_r, Z.add_0_r. exact (proj1 HD).
  - replace (d + 16 * Z.of_nat (S k)) with (d + 16 + 16 * Z.of_nat k) by lia. apply IH; [exact (proj2 HD) | exact Hk].
Qed.

Lemma decodes_ext : ltac2:(tb__ "0|5|
S1cQ40M0A1SbS1cQ8A1A1M1Fx;M2G2SeScS0S0A2M3A1S0S0S8S2R2R1A2S5R1S1R2S3Z10S4S11G3R3A2A1A2A2A2A2S7G1R5S1dG0R2A2M4A1R6G4A1A3F_;Fz;S19R5R2R3A3S19R5R3R4A3F_;F_;Fd;FT;Fm';Fm;").
Proof.
  intros m m' T. induction T as [|p r IH]; intros d HE HD; [exact I|]. cbn [length] in HE. destruct HD as [[H1 H2] HR]. split.
  - split; [rewrite (rd64_ext m m' d) | rewrite (rd64_ext m m' (d + 8))]; try assumption; intros z Hz; apply HE; lia.
  - apply IH; [|exact HR]. intros z Hz. apply HE. lia.
Qed.

Lemma decodes_app : ltac2:(tb__ "0|1|
S1cQ40A1SbS1cQ8A1A1F_;SeScS0S0A2M0A1S0G0S19R4R2R3A3S1aR5S1R3S3Z10S4S11G0R4A2A1A2A2R2A3S19R6R4S14G0R5S15G0R3S12G0A1A3A3A3F_;F_;Fp;Fd;FT;Fm;").
Proof.
  intros m T. induction T as [|q r IH]; intros d p HD HE; cbn [length app] in *.
  - rewrite Z.mul_0_r, Z.add_0_r in HE. split; [exact HE | exact I].
  - split; [exact (proj1 HD)|]. apply IH; [exact (proj2 HD)|]. replace (d + 16 + 16 * Z.of_nat (length r)) with (d + 16 * Z.of_nat (S (length r))) by lia. exact HE.
Qed.

Lemma decodes_defined : ltac2:(tb__ "0|4|
S1cQ40M0A1SbS1cQ8A1M1A1M2F_;SeScS0S0A2M3A1S0S0S19R4R2R3A3S8S2R3R2A2S5R2S1R3S3Z10S4S11G3R4A2A1A2A2A2A2S9S7G2R6S1dG0R3A2A1S16G1A1A3A1F_;F_;Fz;Fd;FT;Fm;").
Proof.
  intros m T. induction T as [|p r IH]; intros d z HD Hz; cbn [length] in Hz; [lia|].
  destruct HD as [[H1 H2] HR].
  destruct (Z_lt_dec z (d + 16)) as [L|L]; [|apply (IH (d + 16)); [exact HR | lia]].
  unfold rd64 in H1, H2.
  destruct (bytes_at m d 8) as [l1|] eqn:E1; [|discriminate]. destruct (bytes_at m (d + 8) 8) as [l2|] eqn:E2; [|discriminate].
  destruct (Z_lt_dec z (d + 8)) as [L8|L8].
  - exact (bytes_at_defined m d 8 l1 E1 z ltac:(lia)).
  - exact (bytes_at_defined m (d + 8) 8 l2 E2 z ltac:(lia)).
Qed.

Lemma lines_ok_nil : ltac2:(tb__ "0|0|
S0S18S12ScS0S0A2A1R1A2FL;").
Proof. intros L. split; intros [|k]; intros; discriminate. Qed.

Lemma lines_ok_app : ltac2:(tb__ "0|5|
SeScS0S0A2M0A1M1S0G0S18R3R2A2S2Z0M2SaS0S0R2A3A2S2G2S10S0S0R3A3M3A2S2S1SaS0S0R4A3S10S0S0R4A3A2R5A2G0S7SbG0A1S17G0R8S20S11G0R8A2A1A3SdG0R1A2A3S9S7G1R9S12G0A1M4A3A1S2S1S1SaS0S0R3A3G3A2Z1A2SaS0S0R8A3A2F_;F_;Fq;S18S14G0R8S15G0R6G4A3A3R7A2F_;F_;F_;F_;F_;Fp;FL;FT;").
Proof.
  intros T L p [H1 H2] Hp0 Hp1 HpL Hlast. split.
  - intros k q Hk. destruct (Nat.lt_ge_cases k (length T)) as [Hlt|Hge].
    + rewrite nth_error_app1 in Hk by exact Hlt. exact (H1 k q Hk).
    + rewrite nth_error_app2 in Hk by exact Hge. destruct (k - length T)%nat as [|j] eqn:Ej; cbn in Hk; [|destruct j; discriminate].
      injection Hk as <-. lia.
  - intros k q q' Hk Hk'. destruct (Nat.lt_ge_cases (S k) (length T)) as [Hlt|Hge].
    + rewrite nth_error_app1 in Hk by lia. rewrite nth_error_app1 in Hk' by exact Hlt. exact (H2 k q q' Hk Hk').
    + rewrite nth_error_app2 in Hk' by exact Hge.
      destruct (S k - length T)%nat as [|j] eqn:Ej; cbn in Hk'; [|destruct j; discriminate]. injection Hk' as <-.
      assert (Ek : k = Nat.pred (length T)) by lia. subst k.
      rewrite nth_error_app1 in Hk by lia. apply (Hlast q Hk). intros ->. cbn in Hk. discriminate.
Qed.

Fixpoint tail_sum (T : list (Z * Z)) : Z := match T with [] => 0 | p :: r => snd p + 1 + tail_sum r end.

Lemma lines_tail_sum : ltac2:(tb__ "0|1|
SeScS0S0A2M0A1S0G0S18R3R2A2S7SbG0A1S17G0R4U0A3SdG0R2A2A3S2S1bR5A1S6S1R4Z1A2SaS0S0R3A3A2A2F_;F_;Fp;FL;FT;").
Proof.
  induction T as [|q r IH]; intros L p HT H0; cbn in H0; [discriminate|]. injection H0 as ->. cbn [tail_sum].
  destruct HT as [H1 H2]. destruct (H1 0%nat p eq_refl) as (P0 & P1 & PL).
  destruct r as [|q r'].
  - cbn. lia.
  - assert (HT' : lines_ok (q :: r') L).
    { split; [intros k x Hk; exact (H1 (S k) x Hk) | intros k x y Hk Hk'; exact (H2 (S k) x y Hk Hk')]. }
    pose proof (IH L q HT' eq_refl) as IHq. pose proof (H2 0%nat p q eq_refl eq_refl) as G. cbn [tail_sum] in IHq |- *. lia.
Qed.

Lemma lines_ok_skip : ltac2:(tb__ "0|1|
SeScS0S0A2M0A1S0SfS18R3R2A2S18S1eG0R2R4A3R3A2F_;Fn;FL;FT;").
Proof.
  intros T L n [H1 H2]. split.
  - intros k p Hk. rewrite nth_error_skipn in Hk. exact (H1 _ p Hk).
  - intros k p q Hk Hk'. rewrite nth_error_skipn in Hk, Hk'. replace (n + S k)%nat with (S (n + k)) in Hk' by lia. exact (H2 _ p q Hk Hk').
Qed.

Lemma lines_tail_sum_at : ltac2:(tb__ "0|1|
SeScS0S0A2M0A1S0SfG0S18R4R3A2S7SbG0A1S17G0R5R3A3SdG0R2A2A3S2S1bS1eG0R4R6A3A1S6S1R5Z1A2SaS0S0R3A3A2A2F_;F_;Fp;Fi;FL;FT;").
Proof.
  intros T L i p HT Hi. apply (lines_tail_sum (skipn i T) L p (lines_ok_skip T L i HT)). rewrite nth_error_skipn, Nat.add_0_r. exact Hi.
Qed.

Lemma lines_entry_bounds : ltac2:(tb__ "0|4|
SeScS0S0A2M0A1S0SfG0S18R4R3A2S7SbG0A1S17G0R5R3A3SdG0R2A2A3S8S2Z0M1SaS0S0R3A3M2A2S8S2G1S10S0S0R3A3M3A2S2S1G2G3A2R5A2A2A2F_;F_;Fp;Fi;FL;FT;").
Proof. intros T L i p [H1 _] Hi. exact (H1 i p Hi). Qed.

Lemma lines_next_pos : ltac2:(tb__ "0|3|
SeScS0S0A2M0A1S0SfG0G0S18R5R4A2S7SbG0A1M1S17G0R6R4A3SdG0R3A2M2A3S7G1S17G0R7S13R5A1A3G2A3S2S1S1SaS0S0R5A3S10S0S0R5A3A2Z1A2SaS0S0R4A3A2F_;F_;F_;Fq;Fp;Fi;FL;FT;").
Proof. intros T L i p q [_ H2] Hi Hj. exact (H2 i p q Hi Hj). Qed.
