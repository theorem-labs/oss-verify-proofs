(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "obj_range"; "ranges_disjoint"; "pairwise_disjoint"; "@Corelib.Init.Datatypes"; "nat"; "prod"; "bool"; "list"; "orb"; "true"; "fst"; "negb"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones"; "zdesc"; "zdisjb"; "zcheck"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "leb"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "not"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones.Zones"; "in_zone"; "@Stdlib.Lists.List"; "Forall2"; "In"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Open Scope Z_scope.

Definition zdesc : Type := (nat * Z * Z)%type.

Definition zdisjb (d d' : zdesc) : bool := ltac2:(tb__ "0|3|
S6S6S5S0A2M0S0A2M1S7Ld;Vd;G0S0G0S7Lp;M2R2S5S0G1S7Ld';Vd';G0S0G2R2S5S0S9S9S9S9ScS1dR6R2A2A1S13R7R1A2A2S13R3R5A2A2S13R7R5A2A2S13R3R1A2A2Llo';Lz';X6x1Lhi';Lp;X6x1Llo;Lz;X6x1Lhi;Lp;X6x1").
Fixpoint zcheck (ds : list zdesc) : bool :=
  match ds with
  | [] => true
  | d :: t => forallb (zdisjb d) t && zcheck t
  end.

Section Zones.
Variable rho : valuation.
Variable zb : nat -> Z.
Variable zlo zhi : nat -> Z.
Variable zused : list nat.
Hypothesis Hsep : ltac2:(tb__ "0|3|
S5S5S1aS5R2Vzused;A3M0G0S17S15S5R4R3A3A1S16S11S12Vzb;R5A1M1Vzhi;R5A1A2S12Vzb;R4A1M2Vzlo;R4A1A2A2S11S12G2Vzhi;R4A1A2S12G1Vzlo;R5A1A2A2A2F_;F_;F_;Fz';Fz;").

Definition in_zone (o : sobj) (d : zdesc) : Prop := ltac2:(tb__ "0|5|
S6S6S5S0A2M0S0A2OLd;Vd;G0S0G0OLp;R2S5S0S14S1aS5R2Vzused;A3S14S11Vzlo;R2A1R1A2S14S11R3Vzhi;R2A1A2S16S11SdS0S0S2Vrho;Vo;A2M1A3M2SbS0S0G1A3M3A2S14S11S12Vzb;R2A1M4R1A2G3A2S11G2S12G4R3A2A2A2A2A2A2A2Llo;Lz;X6x1Lhi;Lp;X6x1").

Lemma zdisj_sound : ltac2:(tb__ "0|1|
S1S1SeSeS18R4R2A2M0G0S15S7SfR4R3A2SaA3S3S2Vrho;R7A2S2Vrho;R6A2A2F_;F_;F_;Fd';Fd;Fo';Fo;").
Proof.
  intros o o' [[z lo] hi] [[z' lo'] hi'] (U & L1 & L2 & R) (U' & L1' & L2' & R') Hb.
  unfold zdisjb in Hb. unfold ranges_disjoint.
  destruct (obj_range rho o) as [a b]. destruct (obj_range rho o') as [a' b']. cbn [fst snd] in *.
  destruct R as [R|[R1 R2]]; [lia|]. destruct R' as [R'|[R1' R2']]; [lia|].
  destruct (Nat.eqb_spec z z') as [<-|NE]; cbn [negb orb] in Hb.
  - repeat (apply Bool.orb_prop in Hb as [Hb|Hb]); try (apply Z.leb_le in Hb; lia).
  - destruct (Hsep z z' U U' NE); lia.
Qed.

Theorem zones_pd : ltac2:(tb__ "0|0|
S8S1A1S8SeA1S19S1SeS18R2R1A5S15S7S10R2A1SaA3S4Vrho;R4A2F_;F_;Fds;Fobjs;").
Proof.
  intros objs ds HF. induction HF as [|o d objs' ds' Ho HF IH]; intros Hc; [exact I|].
  cbn [zcheck] in Hc. apply andb_prop in Hc as [Hd Hc]. cbn [pairwise_disjoint]. split; [|exact (IH Hc)].
  clear IH Hc. induction HF as [|o' d' objs'' ds'' Ho' HF' IH']; [constructor|].
  cbn [forallb] in Hd. apply andb_prop in Hd as [H1 H2]. constructor; [exact (zdisj_sound o o' d d' Ho Ho' H1) | exact (IH' H2)].
Qed.

Theorem zones_cross : ltac2:(tb__ "0|2|
S8S1A1M0S8SeA1M1G0G1S19S1SeS18R4R3A5S19S1SeS18R3R2A5S15S7S1bSeSeS1bSeSfR1A1R4A3Ld;R5A3SaA3S1cS1S1S1cS1S1S3S2Vrho;R1A2S2Vrho;R2A2A2Lo';R6A3Lo;R7A3F_;F_;F_;Fds';Fobjs';Fds;Fobjs;").
Proof.
  intros objs ds objs' ds' HF HF' Hc. induction HF as [|o d objs1 ds1 Ho HF IH]; [constructor|].
  cbn [forallb] in Hc. apply andb_prop in Hc as [H1 H2]. constructor; [|exact (IH H2)].
  clear IH H2 HF. induction HF' as [|o' d' objs2 ds2 Ho' HF' IH']; [constructor|].
  cbn [forallb] in H1. apply andb_prop in H1 as [Ha Hb]. constructor; [|exact (IH' Hb)].
  pose proof (zdisj_sound o o' d d' Ho Ho' Ha) as D. unfold ranges_disjoint in D |- *. lia.
Qed.
End Zones.
