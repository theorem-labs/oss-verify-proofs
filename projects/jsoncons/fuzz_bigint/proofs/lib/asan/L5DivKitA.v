(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceA LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsA
     L5CoreA L5CoreSpecsA L5StepA L5CoreB L5ADetailH L5AFrameK.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5DKA.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5CB. Import L5ADH. Import L5AFK.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Section CTX.
Variables (M : word -> option byte) (model : Model) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z))
          (sp SCR : Z) (spc olo ohi : Z) (ocell : Z -> Prop) (own : (word -> option byte) -> Prop)
          (F fl : Z) (k : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model) (cr2 : credit).
Local Notation B := (ff_bytes k).
Local Notation FF' := ((F, k, spc + 32) :: FF).
Local Notation gctx := (L5AFK.gctx L ar HI LB FF LK A sp SCR spc olo ohi ocell own F fl k LK2 M2 model2 cr2).
Local Notation binv := (L5AFK.binv L ar HI M model LB FF LK A sp SCR spc own F k).

Ltac open_gctx G :=
  destruct G as [Hk SPT SLO SHI SPC OCR OWNAG FS1 FS2 FCEIL LKI2 FLP FLNC HH2 FLC FR F8 FBIG F32 FLA FLR FLBIG NCF NCS].

(* [comment removed for export] *)
Definition wp_ok (W : list L5.range) (BX : list (Z * Z)) (a : Z) : Prop :=
  ~ ocell a /\ (aclientw L ar (BX ++ LB) FF' 0 0 a /\ ~ (0x10000 <= a < 0x633000)) /\ (aclient L ar LB FF sp SCR a -> ~ L5.outside W a).

Lemma bstage (G : gctx) W BX Mc modelc LKc crc Ac (fx fx1 : FPState) Rc (pc : Z) R1 (pc1 : Z) M1v (Wp : Z -> Prop) (K : TSet) :
  binv W BX Mc modelc LKc crc Ac ->
  msteps RSEGS (st fx Rc pc (mrestrict (ahid Ac modelc) Mc)) (st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid Ac modelc) Mc) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1v (Z_to_bv 64 a) = mrestrict (ahid Ac modelc) Mc (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> Wp a -> wp_ok W BX a) ->
  (forall M1 model1, binv W BX M1 model1 LKc crc Ac -> ahid Ac model1 = ahid Ac modelc -> mrestrict (ahid Ac modelc) M1 = M1v -> mem_grows Mc M1 ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M1 (Z_to_bv 64 a) = Mc (Z_to_bv 64 a)) ->
      srealizes RSEGS SCFG (cfg (fx:=fx1) R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx) Rc pc Mc modelc) K.
Proof.
  intros BI MS MG FZ WP KONT. pose proof BI as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10).
  apply (apiece L ar C HI LY HIok (BX ++ LB) FF' LKc crc Ac Mc modelc fx fx1 Rc pc R1 pc1 M1v Wp K B1 B2 MS MG FZ).
  { intros a Ha Wa. exact (proj1 (proj2 (WP a Ha Wa))). }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  apply (KONT M1 model1). 2: exact AH1. 2: exact VIS1. 2: exact MGM1. 2: exact FRM1.
  open_gctx G. unfold L5AFK.binv. split. exact HH1. split. exact AM1. split. eapply L5LZ.model_rt_trans. exact B3. exact RT1. split. exact B4. split. exact B5.
  split. eapply astk_grows. exact B6. exact MGM1.
  split. { eapply ek_trans. exact B7. apply (ek_piece L ar LB FF sp SCR W Mc M1 Wp FRM1). intros a Ha Hc Ho X. exact (proj2 (proj2 (WP a Ha X)) Hc Ho). }
  split. { eapply dk_trans. exact B8. apply dk_grows. exact MGM1. }
  split. { apply (OWNAG Mc M1 B9). intros a Ha. pose proof (OCR a Ha) as RG. assert (Ra : 0 <= a < 2 ^ 64) by (clear - RG SPC; lia).
           apply FRM1. exact Ra. intros X. exact (proj1 (WP a Ra X) Ha). }
  eapply L5.defined_grows. exact MGM1. exact B10.
Qed.

(* [comment removed for export] *)
Lemma wp_frame (G : gctx) W BX a : spc <= a < sp -> ~ ocell a -> wp_ok W BX a.
Proof.
  open_gctx G. intros Ra NO. split. exact NO. split.
  - split. apply stack_client. clear - Ra SPC SLO SHI SPT; lia. clear; lia. clear - Ra SPC SLO SPT; lia.
  - intros Hc _. exact (NCS a Ra Hc).
Qed.
Lemma wp_fake (G : gctx) W BX a : F <= a < F + B - 8 -> ~ (F + 24 <= a < F + 32) -> wp_ok W BX a.
Proof.
  open_gctx G. intros Ra N24. split. { intros X. pose proof (OCR a X). clear - H Ra SPC SLO FCEIL. lia. } split.
  - split. apply (fframe_client L ar (BX ++ LB) FF' 0 0 F k (spc + 32)). left; reflexivity. split. exact Ra. exact N24. clear - Ra FR; lia.
  - intros Hc _. apply (NCF a). left. clear - Ra; lia. exact Hc.
Qed.
Lemma wp_shadow (G : gctx) W BX a : F / 8 + SB <= a < F / 8 + SB + B / 8 -> wp_ok W BX a.
Proof.
  open_gctx G. intros Ra.
  assert (RS : S F <= a <= S (F + B - 1)). { unfold S. rewrite (proj1 (proj2 F8)). clear - Ra. unfold SB in *. lia. }
  split. { intros X. pose proof (OCR a X). clear - H Ra SPC SLO SPT FR F8. unfold SB in Ra. pose proof (Z.div_le_mono F (2 ^ 47) 8 ltac:(lia) ltac:(lia)). change (2 ^ 47 / 8) with 17592186044416 in H0. lia. }
  split.
  - split. apply (fframe_shadow_client L ar (BX ++ LB) FF' 0 0 F k (spc + 32)). left; reflexivity. exact RS.
    clear - Ra FR F8. unfold SB in Ra. pose proof (Z.div_le_mono 4096 F 8 ltac:(lia) ltac:(lia)). change (4096 / 8) with 512 in H. lia.
  - intros Hc _. apply (NCF a). right. exact RS. exact Hc.
Qed.

End CTX.
End WithIface.
End SCFG_1.
End L5DKA.
