(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r41498_42984_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_enq_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
     (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21)).

(* [comment removed for export] *)
Definition art_enq_new_mem (M : word -> option byte) (c ca L B bytes b m n cnt sv : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 M (ca + 1920) (cnt - 1)) (ca + 2576) (sv + 8192)) b 0) (b + 8) (n + 8192)) (b + 16) 1) (b + 24) m)
     (if L =? 0 then c + 8 else B) b) c (L + 1)) (c + 16) b) (c + 24) (bytes + (n + 8192)).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_enq_new_tail_fn : forall regs (M rom : word -> option byte) (raw : word) (sp c ca spb L B bytes w m n cnt sv x8 x9 x18 x19 x20 x21 : Z),
  let b := spb + 24 * 2 ^ 32 + 16 * w in
  getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 ca -> getr regs 13 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 n ->
  getr regs 15 = Z_to_bv 64 cnt -> ret_ok raw ->
  64 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= ca -> ca + 2600 < 2 ^ 64 -> (ca + 2576) mod 8 = 0 -> (ca + 2600 <= 0x10000 \/ 0x696000 <= ca) -> 0x696000 <= spb -> b + 8192 < 2 ^ 64 -> 0 <= w < 2 ^ 32 ->
  0 <= L < 2 ^ 63 -> 0 <= B -> B + 8 < 2 ^ 64 -> 0 <= bytes -> bytes + n + 8192 < 2 ^ 64 -> 0 <= n -> 0 <= m < 2 ^ 64 -> 1 <= cnt <= 16 -> 0 <= sv < 2 ^ 64 ->
  0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= x19 < 2 ^ 64 -> 0 <= x20 < 2 ^ 64 -> 0 <= x21 < 2 ^ 64 ->
  (* [comment removed for export] *)
  apart (sp - 64) 64 c 32 -> apart (sp - 64) 64 (ca + 1920) 664 -> apart (sp - 64) 64 b 32 -> (L <> 0 -> apart (sp - 64) 64 B 8) ->
  apart c 32 (ca + 1920) 664 -> apart c 32 b 32 -> (L <> 0 -> apart c 32 B 8) -> apart (ca + 1920) 664 b 32 -> (L <> 0 -> apart (ca + 1920) 664 B 8) -> (L <> 0 -> apart b 32 B 8) ->
  wrA M c 32 -> wrA M (ca + 1920) 4 -> wrA M (ca + 2576) 8 -> wrA M b 32 -> (L <> 0 -> wrA M B 8) ->
  cellA M (ca + 1936 + 4 * (cnt - 1)) 4 w -> cellA M (ca + 1928) 8 8192 -> cellA M (ca + 2576) 8 sv -> cellA M 0x13c5f8 8 spb ->
  cellA M c 8 L -> (L <> 0 -> cellA M (c + 16) 8 B) -> cellA M (c + 24) 8 bytes ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 -> cellA M (sp - 40) 8 x19 -> cellA M (sp - 48) 8 x20 -> cellA M (sp - 56) 8 x21 ->
  msteps ASEGS (mkst regs (0x56b98 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 11 (Z_to_bv 64 (bytes + (n + 8192)))) 12 (Z_to_bv 64 (L + 1))) 14 (Z_to_bv 64 (n + 8192))) 15 (Z_to_bv 64 L)) 16 (Z_to_bv 64 103079215104)) 18 (Z_to_bv 64 x18)) 19 (Z_to_bv 64 x19)) 20 (Z_to_bv 64 x20)) 21 (Z_to_bv 64 x21))
          raw (art_enq_new_mem M c ca L B bytes b m n cnt sv) rom).
Proof.
  intros regs M rom raw sp c ca spb L B bytes w m n cnt sv x8 x9 x18 x19 x20 x21 b H2 H10 H11 H13 H14 H15 Hret
         Hsp Hsp' Hc Hc' Hca Hca' Hca8 Hcai Hspb Hb Hw HL HB HB' Hby Hby' Hn Hm Hcnt Hsv Hx8 Hx9 Hx18 Hx19 Hx20 Hx21
         A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 Wc Wcnt Wst Wb WB Cw Ccs Csv Cspb CL CB Cby F1 F8 F9 F18 F19 F20 F21.
  assert (Eb : b = spb + 24 * 2 ^ 32 + 16 * w) by reflexivity. clearbody b.
  zstep F_56780 D_56780.
  stepn F_56784 D_56784. rwH. rewrite art_zb_slli by lia.
  zsw F_56788 D_56788 (ca + 1920) (cnt - 1) ltac:(zwok').
  stepn F_5678c D_5678c. rwH. rewrite art_zb_srli by lia. replace ((cnt + -1) * 2 ^ 32 / 2 ^ 30) with (4 * (cnt - 1)) by (replace ((cnt + -1) * 2 ^ 32) with (4 * (cnt - 1) * 2 ^ 30) by lia; rewrite Z_div_mult by lia; reflexivity).
  zstep F_56790 D_56790.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ccs' : cellA X (ca + 1928) 8 8192) by zcell;
    assert (Cw' : cellA X (ca + 4 * (cnt - 1) + 1936) 4 w) by (replace (ca + 4 * (cnt - 1) + 1936) with (ca + 1936 + 4 * (cnt - 1)) by lia; zcell);
    assert (Csv' : cellA X (ca + 2576) 8 sv) by zcell; assert (Wst' : wokA X (ca + 2576) 8) by zwok end.
  zld F_56794 D_56794 (ca + 1928) Ccs'.
  zstep F_56798 D_56798. zstep F_5679c D_5679c.
  zlwu F_567a0 D_567a0 (ca + 4 * (cnt - 1) + 1936) Cw'.
  zamoadd_d F_567a4 D_567a4 (ca + 2576) sv 8192 Csv' ltac:(exact Wst').
  zstep F_567a8 D_567a8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X 0x13c5f8 8 spb) by zcell end.
  zld F_567ac D_567ac 0x13c5f8 Cspb'.
  zstep F_567b0 D_567b0. zstep F_567b4 D_567b4. zstep F_567b8 D_567b8. zstep F_567bc D_567bc. zstep F_567c0 D_567c0.
  zbft F_567c4 D_567c4.
  zstep F_567c8 D_567c8. zstep F_567cc D_567cc. zstep F_567d0 D_567d0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell end.
  zld F_567d4 D_567d4 c CL'.
  zsd F_567d8 D_567d8 b 0 ltac:(zwok').
  zsd F_567dc D_567dc (b + 8) (n + 8192) ltac:(zwok').
  zsd F_567e0 D_567e0 (b + 16) 1 ltac:(zwok').
  zsd F_567e4 D_567e4 (b + 24) m ltac:(zwok').
  destruct (Z.eq_dec L 0) as [EL|NL].
  - zbtk F_567e8 D_567e8.
    zsd F_56824 D_56824 (c + 8) b ltac:(zwok').
    zsd F_56828 D_56828 c (L + 1) ltac:(zwok').
    zsd F_5682c D_5682c (c + 16) b ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell end.
    zld F_56830 D_56830 (c + 24) Cby'.
    zstep F_56834 D_56834.
    zsd F_56838 D_56838 (c + 24) (bytes + (n + 8192)) ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell; assert (F9' : cellA X (sp - 24) 8 x9) by zcell;
      assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell; assert (F20' : cellA X (sp - 48) 8 x20) by zcell;
      assert (F21' : cellA X (sp - 56) 8 x21) by zcell end.
    zld F_5683c D_5683c (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
    zld F_56840 D_56840 (sp - 16) F8'. zld F_56844 D_56844 (sp - 24) F9'. zld F_56848 D_56848 (sp - 32) F18'.
    zld F_5684c D_5684c (sp - 40) F19'. zld F_56850 D_56850 (sp - 48) F20'. zld F_56854 D_56854 (sp - 56) F21'.
    zstep F_56858 D_56858.
    stepret F_5685c D_5685c raw ltac:(gres; reflexivity).
    unfold art_enq_new_mem. rewrite (proj2 (Z.eqb_eq L 0) EL). zret.
  - zbft F_567e8 D_567e8.
    specialize (A4 NL). specialize (A7 NL). specialize (A9 NL). specialize (A10 NL). specialize (WB NL). specialize (CB NL).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CB' : cellA X (c + 16) 8 B) by zcell end.
    zld F_567ec D_567ec (c + 16) CB'.
    zsd F_567f0 D_567f0 B b ltac:(zwok').
    zstep F_567f4 D_567f4.
    stepn F_567f8 D_567f8.
    zsd F_56828 D_56828 c (L + 1) ltac:(zwok').
    zsd F_5682c D_5682c (c + 16) b ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell end.
    zld F_56830 D_56830 (c + 24) Cby'.
    zstep F_56834 D_56834.
    zsd F_56838 D_56838 (c + 24) (bytes + (n + 8192)) ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell; assert (F9' : cellA X (sp - 24) 8 x9) by zcell;
      assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell; assert (F20' : cellA X (sp - 48) 8 x20) by zcell;
      assert (F21' : cellA X (sp - 56) 8 x21) by zcell end.
    zld F_5683c D_5683c (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
    zld F_56840 D_56840 (sp - 16) F8'. zld F_56844 D_56844 (sp - 24) F9'. zld F_56848 D_56848 (sp - 32) F18'.
    zld F_5684c D_5684c (sp - 40) F19'. zld F_56850 D_56850 (sp - 48) F20'. zld F_56854 D_56854 (sp - 56) F21'.
    zstep F_56858 D_56858.
    stepret F_5685c D_5685c raw ltac:(gres; reflexivity).
    unfold art_enq_new_mem. rewrite (proj2 (Z.eqb_neq L 0) NL). zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_enq_new_head : forall regs (M rom : word -> option byte) (raw : word) (sp c L B : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 c ->
  64 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= L < 2 ^ 63 -> 0 <= B -> B + 32 < 2 ^ 64 ->
  apart (sp - 64) 64 c 32 -> (L <> 0 -> apart (sp - 64) 64 B 32) ->
  wrA M (sp - 64) 64 -> cellA M c 8 L -> (L <> 0 -> cellA M (c + 16) 8 B /\ cellA M (B + 16) 8 1021) ->
  exists regs', msteps ASEGS (mkst regs (0x56b58 : word) M rom) (mkst regs' (0x56b90 : word) (art_enq_frame M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 64)
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp c L B H1 H2 H10 Hsp Hsp' Hc Hc' HL HB HB' A1 A2 W CL CB.
  assert (PRE : msteps ASEGS (mkst regs (0x56b58 : word) M rom)
                  (mkst (regupd (regupd regs 2 (Z_to_bv 64 (sp - 64))) 15 (Z_to_bv 64 L)) (0x56b7c : word) (art_enq_frame M sp raw regs) rom)).
  { zstep F_56740 D_56740.
    zsd F_56744 D_56744 (sp - 8) (U raw) ltac:(rewok W). zsd F_56748 D_56748 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5674c D_5674c (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_56750 D_56750 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_56754 D_56754 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_56758 D_56758 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
    zsd F_5675c D_5675c (sp - 56) (U (getr regs 21)) ltac:(rewok W).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell end.
    zld F_56760 D_56760 c CL'.
    unfold art_enq_frame. zret. }
  destruct (Z.eq_dec L 0) as [EL|NL].
  - eexists. split.
    { eapply msteps_trans; [exact PRE|]. zbtk F_56764 D_56764. apply mst_refl. }
    split; [gres; reflexivity|]. intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - destruct (CB NL) as (CB1 & CB2). specialize (A2 NL).
    eexists. split.
    { eapply msteps_trans; [exact PRE|]. zbft F_56764 D_56764.
      assert (CB1' : cellA (art_enq_frame M sp raw regs) (c + 16) 8 B) by (unfold art_enq_frame; zcell).
      assert (CB2' : cellA (art_enq_frame M sp raw regs) (B + 16) 8 1021) by (unfold art_enq_frame; zcell).
      zld F_56768 D_56768 (c + 16) CB1'.
      zld F_5676c D_5676c (B + 16) CB2'.
      zstep F_56770 D_56770.
      zbft F_56774 D_56774.
      apply mst_refl. }
    split; [gres; reflexivity|]. intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_enq_new_pop_fn : forall regs (M rom : word -> option byte) (ca cnt : Z),
  getr regs 11 = Z_to_bv 64 ca -> 0 <= ca -> ca + 2600 < 2 ^ 64 -> 1 <= cnt <= 16 -> cellA M (ca + 1920) 4 cnt ->
  msteps ASEGS (mkst regs (0x56b90 : word) M rom) (mkst (regupd regs 15 (Z_to_bv 64 cnt)) (0x56b98 : word) M rom).
Proof.
  intros regs M rom ca cnt H11 Hca Hca' Hcnt Ccnt.
  zlw F_56778 D_56778 (ca + 1920) Ccnt.
  zbft F_5677c D_5677c.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_enq_new_ra_fn : forall regs (M rom : word -> option byte) (c ca st m n : Z),
  getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 ca -> getr regs 12 = Z_to_bv 64 st -> getr regs 13 = Z_to_bv 64 m -> getr regs 14 = Z_to_bv 64 n ->
  0 <= ca -> ca + 2600 < 2 ^ 64 -> cellA M (ca + 1920) 4 0 ->
  msteps ASEGS (mkst regs (0x56b90 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x56cac)) 8 (Z_to_bv 64 (ca + 1920))) 9 (Z_to_bv 64 ca)) 10 (Z_to_bv 64 ca)) 11 (Z_to_bv 64 (ca + 1920))) 12 (Z_to_bv 64 1295832)) 13 (Z_to_bv 64 24)) 15 (Z_to_bv 64 1295832)) 18 (Z_to_bv 64 m)) 19 (Z_to_bv 64 c)) 20 (Z_to_bv 64 st)) 21 (Z_to_bv 64 n))
          (0x5748c : word) M rom).
Proof.
  intros regs M rom c ca st m n H10 H11 H12 H13 H14 Hca Hca' Ccnt.
  zlw F_56778 D_56778 (ca + 1920) Ccnt.
  zbtk F_5677c D_5677c.
  zstep F_56860 D_56860. zstep F_56864 D_56864. zstep F_56868 D_56868. zstep F_5686c D_5686c. zstep F_56870 D_56870. zstep F_56874 D_56874.
  zstep F_56878 D_56878. zstep F_5687c D_5687c. zstep F_56880 D_56880. zstep F_56884 D_56884. zstep F_56888 D_56888. zstep F_5688c D_5688c.
  stepn F_56890 D_56890.
  zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_enq_new_rb_fn : forall regs (M rom : word -> option byte) (c ca st m n cnt : Z),
  getr regs 10 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 (ca + 1920) -> getr regs 9 = Z_to_bv 64 ca -> getr regs 18 = Z_to_bv 64 m -> getr regs 19 = Z_to_bv 64 c ->
  getr regs 20 = Z_to_bv 64 st -> getr regs 21 = Z_to_bv 64 n ->
  0 <= ca -> ca + 2600 < 2 ^ 64 -> 1 <= cnt <= 16 -> cellA M (ca + 1920) 4 cnt ->
  msteps ASEGS (mkst regs (0x56cac : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 c)) 11 (Z_to_bv 64 ca)) 12 (Z_to_bv 64 st)) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 n)) 15 (Z_to_bv 64 cnt))
          (0x56b98 : word) M rom).
Proof.
  intros regs M rom c ca st m n cnt H10 H8 H9 H18 H19 H20 H21 Hca Hca' Hcnt Ccnt.
  zstep F_56894 D_56894.
  zbft F_56898 D_56898.
  zstep F_5689c D_5689c. zstep F_568a0 D_568a0. zstep F_568a4 D_568a4.
  zlw F_568a8 D_568a8 (ca + 1920) Ccnt.
  zstep F_568ac D_568ac.
  stepn F_568b0 D_568b0.
  zret.
Qed.
End FPX.
