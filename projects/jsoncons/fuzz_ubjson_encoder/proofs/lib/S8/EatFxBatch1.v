(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac EatLeaf EatAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_enq_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
     (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21)).

Definition art_enq_new_mem (M : word -> option byte) (c ca L B bytes b m n cnt sv : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 M (ca + 1920) (cnt - 1)) (ca + 2576) (sv + 8192)) b 0) (b + 8) (n + 8192)) (b + 16) 1) (b + 24) m)
     (if L =? 0 then c + 8 else B) b) c (L + 1)) (c + 16) b) (c + 24) (bytes + (n + 8192)).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_enq_new_tail_fn : forall regs (M rom : word -> option byte) (raw : word) (sp c ca spb L B bytes w m n cnt sv x8 x9 x18 x19 x20 x21 : Z),
  let b := spb + 24 * 2 ^ 32 + 16 * w in
  getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 ca -> getr regs 13 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 n ->
  getr regs 15 = Z_to_bv 64 cnt -> ret_ok raw ->
  64 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= ca -> ca + 2600 < 2 ^ 64 -> (ca + 2576) mod 8 = 0 -> (ca + 2600 <= 0x10000 \/ 0x698000 <= ca) -> 0x698000 <= spb -> b + 8192 < 2 ^ 64 -> 0 <= w < 2 ^ 32 ->
  0 <= L < 2 ^ 63 -> 0 <= B -> B + 8 < 2 ^ 64 -> 0 <= bytes -> bytes + n + 8192 < 2 ^ 64 -> 0 <= n -> 0 <= m < 2 ^ 64 -> 1 <= cnt <= 16 -> 0 <= sv < 2 ^ 64 ->
  0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= x19 < 2 ^ 64 -> 0 <= x20 < 2 ^ 64 -> 0 <= x21 < 2 ^ 64 ->

  apart (sp - 64) 64 c 32 -> apart (sp - 64) 64 (ca + 1920) 664 -> apart (sp - 64) 64 b 32 -> (L <> 0 -> apart (sp - 64) 64 B 8) ->
  apart c 32 (ca + 1920) 664 -> apart c 32 b 32 -> (L <> 0 -> apart c 32 B 8) -> apart (ca + 1920) 664 b 32 -> (L <> 0 -> apart (ca + 1920) 664 B 8) -> (L <> 0 -> apart b 32 B 8) ->
  wrA M c 32 -> wrA M (ca + 1920) 4 -> wrA M (ca + 2576) 8 -> wrA M b 32 -> (L <> 0 -> wrA M B 8) ->
  cellA M (ca + 1936 + 4 * (cnt - 1)) 4 w -> cellA M (ca + 1928) 8 8192 -> cellA M (ca + 2576) 8 sv -> cellA M 0x13e3b8 8 spb ->
  cellA M c 8 L -> (L <> 0 -> cellA M (c + 16) 8 B) -> cellA M (c + 24) 8 bytes ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 -> cellA M (sp - 40) 8 x19 -> cellA M (sp - 48) 8 x20 -> cellA M (sp - 56) 8 x21 ->
  msteps ASEGS (mkst regs (0x57380 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 11 (Z_to_bv 64 (bytes + (n + 8192)))) 12 (Z_to_bv 64 (L + 1))) 14 (Z_to_bv 64 (n + 8192))) 15 (Z_to_bv 64 L)) 16 (Z_to_bv 64 103079215104)) 18 (Z_to_bv 64 x18)) 19 (Z_to_bv 64 x19)) 20 (Z_to_bv 64 x20)) 21 (Z_to_bv 64 x21))
          raw (art_enq_new_mem M c ca L B bytes b m n cnt sv) rom).
Proof.
  intros regs M rom raw sp c ca spb L B bytes w m n cnt sv x8 x9 x18 x19 x20 x21 b H2 H10 H11 H13 H14 H15 Hret
         Hsp Hsp' Hc Hc' Hca Hca' Hca8 Hcai Hspb Hb Hw HL HB HB' Hby Hby' Hn Hm Hcnt Hsv Hx8 Hx9 Hx18 Hx19 Hx20 Hx21
         A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 Wc Wcnt Wst Wb WB Cw Ccs Csv Cspb CL CB Cby F1 F8 F9 F18 F19 F20 F21.
  assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * w) by reflexivity. clearbody b.
  zstep F_57330 D_57330.
  stepn F_57334 D_57334. rwH. rewrite art_zb_slli by lia.
  zsw F_57338 D_57338 (ca + 1920) (cnt - 1) ltac:(zwok').
  stepn F_5733c D_5733c. rwH. rewrite art_zb_srli by lia. replace ((cnt + -1) * 2 ^ 32 / 2 ^ 30) with (4 * (cnt - 1)) by (replace ((cnt + -1) * 2 ^ 32) with (4 * (cnt - 1) * 2 ^ 30) by lia; rewrite Z_div_mult by lia; reflexivity).
  zstep F_57340 D_57340.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ccs' : cellA X (ca + 1928) 8 8192) by zcell;
    assert (Cw' : cellA X (ca + 4 * (cnt - 1) + 1936) 4 w) by (replace (ca + 4 * (cnt - 1) + 1936) with (ca + 1936 + 4 * (cnt - 1)) by lia; zcell);
    assert (Csv' : cellA X (ca + 2576) 8 sv) by zcell; assert (Wst' : wokA X (ca + 2576) 8) by zwok end.
  zld F_57344 D_57344 (ca + 1928) Ccs'.
  zstep F_57348 D_57348. zstep F_5734c D_5734c.
  zlwu F_57350 D_57350 (ca + 4 * (cnt - 1) + 1936) Cw'.
  zamoadd_d F_57354 D_57354 (ca + 2576) sv 8192 Csv' ltac:(exact Wst').
  zstep F_57358 D_57358.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X 0x13e3b8 8 spb) by zcell end.
  zld F_5735c D_5735c 0x13e3b8 Cspb'.
  zstep F_57360 D_57360. zstep F_57364 D_57364. zstep F_57368 D_57368. zstep F_5736c D_5736c. zstep F_57370 D_57370.
  zbft F_57374 D_57374.
  zstep F_57378 D_57378. zstep F_5737c D_5737c. zstep F_57380 D_57380.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell end.
  zld F_57384 D_57384 c CL'.
  zsd F_57388 D_57388 b 0 ltac:(zwok').
  zsd F_5738c D_5738c (b + 8) (n + 8192) ltac:(zwok').
  zsd F_57390 D_57390 (b + 16) 1 ltac:(zwok').
  zsd F_57394 D_57394 (b + 24) m ltac:(zwok').
  destruct (Z.eq_dec L 0) as [EL|NL].
  - zbtk F_57398 D_57398.
    zsd F_573d4 D_573d4 (c + 8) b ltac:(zwok').
    zsd F_573d8 D_573d8 c (L + 1) ltac:(zwok').
    zsd F_573dc D_573dc (c + 16) b ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell end.
    zld F_573e0 D_573e0 (c + 24) Cby'.
    zstep F_573e4 D_573e4.
    zsd F_573e8 D_573e8 (c + 24) (bytes + (n + 8192)) ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell; assert (F9' : cellA X (sp - 24) 8 x9) by zcell;
      assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell; assert (F20' : cellA X (sp - 48) 8 x20) by zcell;
      assert (F21' : cellA X (sp - 56) 8 x21) by zcell end.
    zld F_573ec D_573ec (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
    zld F_573f0 D_573f0 (sp - 16) F8'. zld F_573f4 D_573f4 (sp - 24) F9'. zld F_573f8 D_573f8 (sp - 32) F18'.
    zld F_573fc D_573fc (sp - 40) F19'. zld F_57400 D_57400 (sp - 48) F20'. zld F_57404 D_57404 (sp - 56) F21'.
    zstep F_57408 D_57408.
    stepret F_5740c D_5740c raw ltac:(gres; reflexivity).
    unfold art_enq_new_mem. rewrite (proj2 (Z.eqb_eq L 0) EL). zret.
  - zbft F_57398 D_57398.
    specialize (A4 NL). specialize (A7 NL). specialize (A9 NL). specialize (A10 NL). specialize (WB NL). specialize (CB NL).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CB' : cellA X (c + 16) 8 B) by zcell end.
    zld F_5739c D_5739c (c + 16) CB'.
    zsd F_573a0 D_573a0 B b ltac:(zwok').
    zstep F_573a4 D_573a4.
    stepn F_573a8 D_573a8.
    zsd F_573d8 D_573d8 c (L + 1) ltac:(zwok').
    zsd F_573dc D_573dc (c + 16) b ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell end.
    zld F_573e0 D_573e0 (c + 24) Cby'.
    zstep F_573e4 D_573e4.
    zsd F_573e8 D_573e8 (c + 24) (bytes + (n + 8192)) ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell; assert (F9' : cellA X (sp - 24) 8 x9) by zcell;
      assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell; assert (F20' : cellA X (sp - 48) 8 x20) by zcell;
      assert (F21' : cellA X (sp - 56) 8 x21) by zcell end.
    zld F_573ec D_573ec (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
    zld F_573f0 D_573f0 (sp - 16) F8'. zld F_573f4 D_573f4 (sp - 24) F9'. zld F_573f8 D_573f8 (sp - 32) F18'.
    zld F_573fc D_573fc (sp - 40) F19'. zld F_57400 D_57400 (sp - 48) F20'. zld F_57404 D_57404 (sp - 56) F21'.
    zstep F_57408 D_57408.
    stepret F_5740c D_5740c raw ltac:(gres; reflexivity).
    unfold art_enq_new_mem. rewrite (proj2 (Z.eqb_neq L 0) NL). zret.
Qed.

#[using="Type"] Lemma art_enq_new_head : forall regs (M rom : word -> option byte) (raw : word) (sp c L B : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 c ->
  64 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= L < 2 ^ 63 -> 0 <= B -> B + 32 < 2 ^ 64 ->
  apart (sp - 64) 64 c 32 -> (L <> 0 -> apart (sp - 64) 64 B 32) ->
  wrA M (sp - 64) 64 -> cellA M c 8 L -> (L <> 0 -> cellA M (c + 16) 8 B /\ cellA M (B + 16) 8 1021) ->
  exists regs', msteps ASEGS (mkst regs (0x57340 : word) M rom) (mkst regs' (0x57378 : word) (art_enq_frame M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 64)
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp c L B H1 H2 H10 Hsp Hsp' Hc Hc' HL HB HB' A1 A2 W CL CB.
  assert (PRE : msteps ASEGS (mkst regs (0x57340 : word) M rom)
                  (mkst (regupd (regupd regs 2 (Z_to_bv 64 (sp - 64))) 15 (Z_to_bv 64 L)) (0x57364 : word) (art_enq_frame M sp raw regs) rom)).
  { zstep F_572f0 D_572f0.
    zsd F_572f4 D_572f4 (sp - 8) (U raw) ltac:(rewok W). zsd F_572f8 D_572f8 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_572fc D_572fc (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_57300 D_57300 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_57304 D_57304 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_57308 D_57308 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_5730c D_5730c (sp - 56) (U (getr regs 21)) ltac:(rewok W).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell end.
    zld F_57310 D_57310 c CL'.
    unfold art_enq_frame. zret. }
  destruct (Z.eq_dec L 0) as [EL|NL].
  - eexists. split.
    { eapply msteps_trans; [exact PRE|]. zbtk F_57314 D_57314. apply mst_refl. }
    split; [gres; reflexivity|]. intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - destruct (CB NL) as (CB1 & CB2). specialize (A2 NL).
    eexists. split.
    { eapply msteps_trans; [exact PRE|]. zbft F_57314 D_57314.
      assert (CB1' : cellA (art_enq_frame M sp raw regs) (c + 16) 8 B) by (unfold art_enq_frame; zcell).
      assert (CB2' : cellA (art_enq_frame M sp raw regs) (B + 16) 8 1021) by (unfold art_enq_frame; zcell).
      zld F_57318 D_57318 (c + 16) CB1'.
      zld F_5731c D_5731c (B + 16) CB2'.
      zstep F_57320 D_57320.
      zbft F_57324 D_57324.
      apply mst_refl. }
    split; [gres; reflexivity|]. intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_enq_new_pop_fn : forall regs (M rom : word -> option byte) (ca cnt : Z),
  getr regs 11 = Z_to_bv 64 ca -> 0 <= ca -> ca + 2600 < 2 ^ 64 -> 1 <= cnt <= 16 -> cellA M (ca + 1920) 4 cnt ->
  msteps ASEGS (mkst regs (0x57378 : word) M rom) (mkst (regupd regs 15 (Z_to_bv 64 cnt)) (0x57380 : word) M rom).
Proof.
  intros regs M rom ca cnt H11 Hca Hca' Hcnt Ccnt.
  zlw F_57328 D_57328 (ca + 1920) Ccnt.
  zbft F_5732c D_5732c.
  zret.
Qed.

#[using="Type"] Lemma art_enq_new_ra_fn : forall regs (M rom : word -> option byte) (c ca st m n : Z),
  getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 ca -> getr regs 12 = Z_to_bv 64 st -> getr regs 13 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 n ->
  0 <= ca -> ca + 2600 < 2 ^ 64 -> cellA M (ca + 1920) 4 0 ->
  msteps ASEGS (mkst regs (0x57378 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x57494)) 8 (Z_to_bv 64 (ca + 1920))) 9 (Z_to_bv 64 ca)) 10 (Z_to_bv 64 ca)) 11 (Z_to_bv 64 (ca + 1920))) 12 (Z_to_bv 64 1303448)) 13 (Z_to_bv 64 24)) 15 (Z_to_bv 64 1303448)) 18 (Z_to_bv 64 m)) 19 (Z_to_bv 64 c)) 20 (Z_to_bv 64 st)) 21 (Z_to_bv 64 n))
          (0x57c74 : word) M rom).
Proof.
  intros regs M rom c ca st m n H10 H11 H12 H13 H14 Hca Hca' Ccnt.
  zlw F_57328 D_57328 (ca + 1920) Ccnt.
  zbtk F_5732c D_5732c.
  zstep F_57410 D_57410. zstep F_57414 D_57414. zstep F_57418 D_57418. zstep F_5741c D_5741c. zstep F_57420 D_57420. zstep F_57424 D_57424.
  zstep F_57428 D_57428. zstep F_5742c D_5742c. zstep F_57430 D_57430. zstep F_57434 D_57434. zstep F_57438 D_57438. zstep F_5743c D_5743c.
  stepn F_57440 D_57440.
  zret.
Qed.

#[using="Type"] Lemma art_enq_new_rb_fn : forall regs (M rom : word -> option byte) (c ca st m n cnt : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 (ca + 1920) -> getr regs 9 = Z_to_bv 64 ca -> getr regs 18 = Z_to_bv 64 m -> getr regs 19 = Z_to_bv 64 c ->
  getr regs 20 = Z_to_bv 64 st -> getr regs 21 = Z_to_bv 64 n ->
  0 <= ca -> ca + 2600 < 2 ^ 64 -> 1 <= cnt <= 16 -> cellA M (ca + 1920) 4 cnt ->
  msteps ASEGS (mkst regs (0x57494 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 c)) 11 (Z_to_bv 64 ca)) 12 (Z_to_bv 64 st)) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 n)) 15 (Z_to_bv 64 cnt))
          (0x57380 : word) M rom).
Proof.
  intros regs M rom c ca st m n cnt H10 H8 H9 H18 H19 H20 H21 Hca Hca' Hcnt Ccnt.
  zstep F_57444 D_57444.
  zbft F_57448 D_57448.
  zstep F_5744c D_5744c. zstep F_57450 D_57450. zstep F_57454 D_57454.
  zlw F_57458 D_57458 (ca + 1920) Ccnt.
  zstep F_5745c D_5745c.
  stepn F_57460 D_57460.
  zret.
Qed.
End FPX.
