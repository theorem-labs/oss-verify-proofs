(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac Pm9ArtLeaf Pm9ArtAllocG.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_5d000_5e000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_enq_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
     (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21)).

Definition art_enq_new_mem (M : word -> option byte) (c ca L B bytes b m n cnt sv : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 M (ca + 1920) (cnt - 1)) (ca + 2576) (sv + 8192)) b 0) (b + 8) (n + 8192)) (b + 16) 1) (b + 24) m)
     (if L =? 0 then c + 8 else B) b) c (L + 1)) (c + 16) b) (c + 24) (bytes + (n + 8192)).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_enq_new_tail_fn : forall regs (M rom : word -> option byte) (raw : word) (sp c ca spb L B bytes w m n cnt sv x8 x9 x18 x19 x20 x21 : Z),
  let b := spb + 24 * 2 ^ 32 + 16 * w in
  getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 ca -> getr regs 13 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 n ->
  getr regs 15 = Z_to_bv 64 cnt -> ret_ok raw ->
  64 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= ca -> ca + 2600 < 2 ^ 64 -> (ca + 2576) mod 8 = 0 -> (ca + 2600 <= 0x10000 \/ 0x6b4000 <= ca) -> 0x6b4000 <= spb -> b + 8192 < 2 ^ 64 -> 0 <= w < 2 ^ 32 ->
  0 <= L < 2 ^ 63 -> 0 <= B -> B + 8 < 2 ^ 64 -> 0 <= bytes -> bytes + n + 8192 < 2 ^ 64 -> 0 <= n -> 0 <= m < 2 ^ 64 -> 1 <= cnt <= 16 -> 0 <= sv < 2 ^ 64 ->
  0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= x19 < 2 ^ 64 -> 0 <= x20 < 2 ^ 64 -> 0 <= x21 < 2 ^ 64 ->

  apart (sp - 64) 64 c 32 -> apart (sp - 64) 64 (ca + 1920) 664 -> apart (sp - 64) 64 b 32 -> (L <> 0 -> apart (sp - 64) 64 B 8) ->
  apart c 32 (ca + 1920) 664 -> apart c 32 b 32 -> (L <> 0 -> apart c 32 B 8) -> apart (ca + 1920) 664 b 32 -> (L <> 0 -> apart (ca + 1920) 664 B 8) -> (L <> 0 -> apart b 32 B 8) ->
  wrA M c 32 -> wrA M (ca + 1920) 4 -> wrA M (ca + 2576) 8 -> wrA M b 32 -> (L <> 0 -> wrA M B 8) ->
  cellA M (ca + 1936 + 4 * (cnt - 1)) 4 w -> cellA M (ca + 1928) 8 8192 -> cellA M (ca + 2576) 8 sv -> cellA M 0x15a6b8 8 spb ->
  cellA M c 8 L -> (L <> 0 -> cellA M (c + 16) 8 B) -> cellA M (c + 24) 8 bytes ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 -> cellA M (sp - 40) 8 x19 -> cellA M (sp - 48) 8 x20 -> cellA M (sp - 56) 8 x21 ->
  msteps ASEGS (mkst regs (0x5ddd0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 11 (Z_to_bv 64 (bytes + (n + 8192)))) 12 (Z_to_bv 64 (L + 1))) 14 (Z_to_bv 64 (n + 8192))) 15 (Z_to_bv 64 L)) 16 (Z_to_bv 64 103079215104)) 18 (Z_to_bv 64 x18)) 19 (Z_to_bv 64 x19)) 20 (Z_to_bv 64 x20)) 21 (Z_to_bv 64 x21))
          raw (art_enq_new_mem M c ca L B bytes b m n cnt sv) rom).
Proof.
  intros regs M rom raw sp c ca spb L B bytes w m n cnt sv x8 x9 x18 x19 x20 x21 b H2 H10 H11 H13 H14 H15 Hret
         Hsp Hsp' Hc Hc' Hca Hca' Hca8 Hcai Hspb Hb Hw HL HB HB' Hby Hby' Hn Hm Hcnt Hsv Hx8 Hx9 Hx18 Hx19 Hx20 Hx21
         A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 Wc Wcnt Wst Wb WB Cw Ccs Csv Cspb CL CB Cby F1 F8 F9 F18 F19 F20 F21.
  assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * w) by reflexivity. clearbody b.
  zstep F_5dd88 D_5dd88.
  stepn F_5dd8c D_5dd8c. rwH. rewrite art_zb_slli by lia.
  zsw F_5dd90 D_5dd90 (ca + 1920) (cnt - 1) ltac:(zwok').
  stepn F_5dd94 D_5dd94. rwH. rewrite art_zb_srli by lia. replace ((cnt + -1) * 2 ^ 32 / 2 ^ 30) with (4 * (cnt - 1)) by (replace ((cnt + -1) * 2 ^ 32) with (4 * (cnt - 1) * 2 ^ 30) by lia; rewrite Z_div_mult by lia; reflexivity).
  zstep F_5dd98 D_5dd98.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ccs' : cellA X (ca + 1928) 8 8192) by zcell;
    assert (Cw' : cellA X (ca + 4 * (cnt - 1) + 1936) 4 w) by (replace (ca + 4 * (cnt - 1) + 1936) with (ca + 1936 + 4 * (cnt - 1)) by lia; zcell);
    assert (Csv' : cellA X (ca + 2576) 8 sv) by zcell; assert (Wst' : wokA X (ca + 2576) 8) by zwok end.
  zld F_5dd9c D_5dd9c (ca + 1928) Ccs'.
  zstep F_5dda0 D_5dda0. zstep F_5dda4 D_5dda4.
  zlwu F_5dda8 D_5dda8 (ca + 4 * (cnt - 1) + 1936) Cw'.
  zamoadd_d F_5ddac D_5ddac (ca + 2576) sv 8192 Csv' ltac:(exact Wst').
  zstep F_5ddb0 D_5ddb0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X 0x15a6b8 8 spb) by zcell end.
  zld F_5ddb4 D_5ddb4 0x15a6b8 Cspb'.
  zstep F_5ddb8 D_5ddb8. zstep F_5ddbc D_5ddbc. zstep F_5ddc0 D_5ddc0. zstep F_5ddc4 D_5ddc4. zstep F_5ddc8 D_5ddc8.
  zbft F_5ddcc D_5ddcc.
  zstep F_5ddd0 D_5ddd0. zstep F_5ddd4 D_5ddd4. zstep F_5ddd8 D_5ddd8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell end.
  zld F_5dddc D_5dddc c CL'.
  zsd F_5dde0 D_5dde0 b 0 ltac:(zwok').
  zsd F_5dde4 D_5dde4 (b + 8) (n + 8192) ltac:(zwok').
  zsd F_5dde8 D_5dde8 (b + 16) 1 ltac:(zwok').
  zsd F_5ddec D_5ddec (b + 24) m ltac:(zwok').
  destruct (Z.eq_dec L 0) as [EL|NL].
  - zbtk F_5ddf0 D_5ddf0.
    zsd F_5de2c D_5de2c (c + 8) b ltac:(zwok').
    zsd F_5de30 D_5de30 c (L + 1) ltac:(zwok').
    zsd F_5de34 D_5de34 (c + 16) b ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell end.
    zld F_5de38 D_5de38 (c + 24) Cby'.
    zstep F_5de3c D_5de3c.
    zsd F_5de40 D_5de40 (c + 24) (bytes + (n + 8192)) ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell; assert (F9' : cellA X (sp - 24) 8 x9) by zcell;
      assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell; assert (F20' : cellA X (sp - 48) 8 x20) by zcell;
      assert (F21' : cellA X (sp - 56) 8 x21) by zcell end.
    zld F_5de44 D_5de44 (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
    zld F_5de48 D_5de48 (sp - 16) F8'. zld F_5de4c D_5de4c (sp - 24) F9'. zld F_5de50 D_5de50 (sp - 32) F18'.
    zld F_5de54 D_5de54 (sp - 40) F19'. zld F_5de58 D_5de58 (sp - 48) F20'. zld F_5de5c D_5de5c (sp - 56) F21'.
    zstep F_5de60 D_5de60.
    stepret F_5de64 D_5de64 raw ltac:(gres; reflexivity).
    unfold art_enq_new_mem. rewrite (proj2 (Z.eqb_eq L 0) EL). zret.
  - zbft F_5ddf0 D_5ddf0.
    specialize (A4 NL). specialize (A7 NL). specialize (A9 NL). specialize (A10 NL). specialize (WB NL). specialize (CB NL).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CB' : cellA X (c + 16) 8 B) by zcell end.
    zld F_5ddf4 D_5ddf4 (c + 16) CB'.
    zsd F_5ddf8 D_5ddf8 B b ltac:(zwok').
    zstep F_5ddfc D_5ddfc.
    stepn F_5de00 D_5de00.
    zsd F_5de30 D_5de30 c (L + 1) ltac:(zwok').
    zsd F_5de34 D_5de34 (c + 16) b ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell end.
    zld F_5de38 D_5de38 (c + 24) Cby'.
    zstep F_5de3c D_5de3c.
    zsd F_5de40 D_5de40 (c + 24) (bytes + (n + 8192)) ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell; assert (F9' : cellA X (sp - 24) 8 x9) by zcell;
      assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell; assert (F20' : cellA X (sp - 48) 8 x20) by zcell;
      assert (F21' : cellA X (sp - 56) 8 x21) by zcell end.
    zld F_5de44 D_5de44 (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
    zld F_5de48 D_5de48 (sp - 16) F8'. zld F_5de4c D_5de4c (sp - 24) F9'. zld F_5de50 D_5de50 (sp - 32) F18'.
    zld F_5de54 D_5de54 (sp - 40) F19'. zld F_5de58 D_5de58 (sp - 48) F20'. zld F_5de5c D_5de5c (sp - 56) F21'.
    zstep F_5de60 D_5de60.
    stepret F_5de64 D_5de64 raw ltac:(gres; reflexivity).
    unfold art_enq_new_mem. rewrite (proj2 (Z.eqb_neq L 0) NL). zret.
Qed.

Lemma art_enq_new_head : forall regs (M rom : word -> option byte) (raw : word) (sp c L B : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 c ->
  64 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= L < 2 ^ 63 -> 0 <= B -> B + 32 < 2 ^ 64 ->
  apart (sp - 64) 64 c 32 -> (L <> 0 -> apart (sp - 64) 64 B 32) ->
  wrA M (sp - 64) 64 -> cellA M c 8 L -> (L <> 0 -> cellA M (c + 16) 8 B /\ cellA M (B + 16) 8 1021) ->
  exists regs', msteps ASEGS (mkst regs (0x5dd90 : word) M rom) (mkst regs' (0x5ddc8 : word) (art_enq_frame M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 64)
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp c L B H1 H2 H10 Hsp Hsp' Hc Hc' HL HB HB' A1 A2 W CL CB.
  assert (PRE : msteps ASEGS (mkst regs (0x5dd90 : word) M rom)
                  (mkst (regupd (regupd regs 2 (Z_to_bv 64 (sp - 64))) 15 (Z_to_bv 64 L)) (0x5ddb4 : word) (art_enq_frame M sp raw regs) rom)).
  { zstep F_5dd48 D_5dd48.
    zsd F_5dd4c D_5dd4c (sp - 8) (U raw) ltac:(rewok W). zsd F_5dd50 D_5dd50 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5dd54 D_5dd54 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5dd58 D_5dd58 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_5dd5c D_5dd5c (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5dd60 D_5dd60 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_5dd64 D_5dd64 (sp - 56) (U (getr regs 21)) ltac:(rewok W).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell end.
    zld F_5dd68 D_5dd68 c CL'.
    unfold art_enq_frame. zret. }
  destruct (Z.eq_dec L 0) as [EL|NL].
  - eexists. split.
    { eapply msteps_trans; [exact PRE|]. zbtk F_5dd6c D_5dd6c. apply mst_refl. }
    split; [gres; reflexivity|]. intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - destruct (CB NL) as (CB1 & CB2). specialize (A2 NL).
    eexists. split.
    { eapply msteps_trans; [exact PRE|]. zbft F_5dd6c D_5dd6c.
      assert (CB1' : cellA (art_enq_frame M sp raw regs) (c + 16) 8 B) by (unfold art_enq_frame; zcell).
      assert (CB2' : cellA (art_enq_frame M sp raw regs) (B + 16) 8 1021) by (unfold art_enq_frame; zcell).
      zld F_5dd70 D_5dd70 (c + 16) CB1'.
      zld F_5dd74 D_5dd74 (B + 16) CB2'.
      zstep F_5dd78 D_5dd78.
      zbft F_5dd7c D_5dd7c.
      apply mst_refl. }
    split; [gres; reflexivity|]. intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_enq_new_pop_fn : forall regs (M rom : word -> option byte) (ca cnt : Z),
  getr regs 11 = Z_to_bv 64 ca -> 0 <= ca -> ca + 2600 < 2 ^ 64 -> 1 <= cnt <= 16 -> cellA M (ca + 1920) 4 cnt ->
  msteps ASEGS (mkst regs (0x5ddc8 : word) M rom) (mkst (regupd regs 15 (Z_to_bv 64 cnt)) (0x5ddd0 : word) M rom).
Proof.
  intros regs M rom ca cnt H11 Hca Hca' Hcnt Ccnt.
  zlw F_5dd80 D_5dd80 (ca + 1920) Ccnt.
  zbft F_5dd84 D_5dd84.
  zret.
Qed.

Lemma art_enq_new_ra_fn : forall regs (M rom : word -> option byte) (c ca st m n : Z),
  getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 ca -> getr regs 12 = Z_to_bv 64 st -> getr regs 13 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 n ->
  0 <= ca -> ca + 2600 < 2 ^ 64 -> cellA M (ca + 1920) 4 0 ->
  msteps ASEGS (mkst regs (0x5ddc8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x5dee4)) 8 (Z_to_bv 64 (ca + 1920))) 9 (Z_to_bv 64 ca)) 10 (Z_to_bv 64 ca)) 11 (Z_to_bv 64 (ca + 1920))) 12 (Z_to_bv 64 1418904)) 13 (Z_to_bv 64 24)) 15 (Z_to_bv 64 1418904)) 18 (Z_to_bv 64 m)) 19 (Z_to_bv 64 c)) 20 (Z_to_bv 64 st)) 21 (Z_to_bv 64 n))
          (0x5e6c4 : word) M rom).
Proof.
  intros regs M rom c ca st m n H10 H11 H12 H13 H14 Hca Hca' Ccnt.
  zlw F_5dd80 D_5dd80 (ca + 1920) Ccnt.
  zbtk F_5dd84 D_5dd84.
  zstep F_5de68 D_5de68. zstep F_5de6c D_5de6c. zstep F_5de70 D_5de70. zstep F_5de74 D_5de74. zstep F_5de78 D_5de78. zstep F_5de7c D_5de7c.
  zstep F_5de80 D_5de80. zstep F_5de84 D_5de84. zstep F_5de88 D_5de88. zstep F_5de8c D_5de8c. zstep F_5de90 D_5de90. zstep F_5de94 D_5de94.
  stepn F_5de98 D_5de98.
  zret.
Qed.

Lemma art_enq_new_rb_fn : forall regs (M rom : word -> option byte) (c ca st m n cnt : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 (ca + 1920) -> getr regs 9 = Z_to_bv 64 ca -> getr regs 18 = Z_to_bv 64 m -> getr regs 19 = Z_to_bv 64 c ->
  getr regs 20 = Z_to_bv 64 st -> getr regs 21 = Z_to_bv 64 n ->
  0 <= ca -> ca + 2600 < 2 ^ 64 -> 1 <= cnt <= 16 -> cellA M (ca + 1920) 4 cnt ->
  msteps ASEGS (mkst regs (0x5dee4 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 c)) 11 (Z_to_bv 64 ca)) 12 (Z_to_bv 64 st)) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 n)) 15 (Z_to_bv 64 cnt))
          (0x5ddd0 : word) M rom).
Proof.
  intros regs M rom c ca st m n cnt H10 H8 H9 H18 H19 H20 H21 Hca Hca' Hcnt Ccnt.
  zstep F_5de9c D_5de9c.
  zbft F_5dea0 D_5dea0.
  zstep F_5dea4 D_5dea4. zstep F_5dea8 D_5dea8. zstep F_5deac D_5deac.
  zlw F_5deb0 D_5deb0 (ca + 1920) Ccnt.
  zstep F_5deb4 D_5deb4.
  stepn F_5deb8 D_5deb8.
  zret.
Qed.
End FPX.
