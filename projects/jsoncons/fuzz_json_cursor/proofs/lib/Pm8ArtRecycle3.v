(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac Pm8ArtLeaf Pm8ArtAllocG Pm8ArtPoison ArtRuns ArtRunsMem Pm8ArtFp Pm8ArtPopulate1 Pm8ArtCellEx.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_5b000_5c000 Pm8_code_5c000_5d000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Ltac zamoadd_da F D a old v CELL oktac altac :=
  chain_step; [reflexivity
  | eapply (art_step_amoadd_d_x0 _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word) (Z_to_bv 64 old : word));
    [ exact F | reflexivity | exact D
    | gres; rwH; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | rewrite art_u_lit by lia; altac
    | exact CELL | apply bytes_le_to_Z_8
    | gres; rwH; first [reflexivity | f_equal; lia]
    | oktac ]
  | step_simpl ];
  rewrite ?art_zb_add;
  change (wbytes ?M0 (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 (old + v)))) with (Wn 8 M0 a (old + v)).

Definition art_f48 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20)).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_lcd_push_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ca ia c p spb w mc cnt csz sv : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 p ->
  0x6b3000 + 48 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 48) 48 ->
  1 <= c <= 31 -> 4096 <= ca -> ca + 2592 <= sp - 48 -> ca mod 8 = 0 -> (ca + 2592 <= 0x10000 \/ 0x6b3000 <= ca) -> 0x10000 <= ia -> ia + 64 <= 0x6b3000 ->
  0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> p = spb + c * 2 ^ 32 + 16 * w -> 0 <= w < 2 ^ 28 -> 0 <= cnt < mc -> mc <= 16 -> 0 <= csz < 2 ^ 63 -> 0 <= sv < 2 ^ 64 ->
  wrA M ca 2592 ->
  cellA M (ca + 80 * c) 4 cnt -> cellA M (ca + 80 * c + 4) 4 mc -> cellA M (ca + 80 * c + 8) 8 csz -> cellA M (ia + 32) 8 spb -> cellA M (ca + 2576) 8 sv ->
  msteps ASEGS (mkst regs (0x5bb70 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (ca + 2576))) 11 (Z_to_bv 64 (0 - csz))) 12 (Z_to_bv 64 (ca + c * 80 + cnt * 4))) 13 (Z_to_bv 64 w)) 14 (Z_to_bv 64 (cnt + 1))) 15 (Z_to_bv 64 mc)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20))
       raw (Wn 8 (Wn 4 (Wn 4 (art_f48 M sp raw regs) (ca + 80 * c) (cnt + 1)) (ca + 80 * c + 16 + 4 * cnt) w) (ca + 2576) (sv + (0 - csz))) rom).
Proof.
  intros regs M rom raw sp ca ia c p spb w mc cnt csz sv H1 Hret H2 H10 H11 H12 H13 Hsp Hsp' W Hc Hca Hca' Hca8 Hcai Hia Hia' Hspb Hspb' Ep Hw Hcnt Hmc Hcsz Hsv Wca Ccnt Cmc Ccsz Cspb Csv.
  zstep F_5bb20 D_5bb20.
  zsd F_5bb24 D_5bb24 (sp - 8) (U raw) ltac:(rewok W). zsd F_5bb28 D_5bb28 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_5bb2c D_5bb2c (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5bb30 D_5bb30 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_5bb34 D_5bb34 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5bb38 D_5bb38 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zbft F_5bb3c D_5bb3c.
  zstep F_5bb40 D_5bb40.
  zbft F_5bb44 D_5bb44.
  zstep F_5bb48 D_5bb48. zstep F_5bb4c D_5bb4c. zstep F_5bb50 D_5bb50.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 mc) by zcell; assert (Ccnt' : cellA X (ca + 80 * c) 4 cnt) by zcell;
    assert (Cspb' : cellA X (ia + 32) 8 spb) by zcell; assert (Ccsz' : cellA X (ca + 80 * c + 8) 8 csz) by zcell; assert (Csv' : cellA X (ca + 2576) 8 sv) by zcell;
    assert (Wca' : wrA X ca 2592) by zwr end.
  zlw F_5bb54 D_5bb54 (ca + 80 * c + 4) Cmc'.
  zbft F_5bb58 D_5bb58.
  zlw F_5bb5c D_5bb5c (ca + 80 * c) Ccnt'.
  zbft F_5bb60 D_5bb60.
  zld F_5bb64 D_5bb64 (ia + 32) Cspb'.
  zstep F_5bb68 D_5bb68. zstep F_5bb6c D_5bb6c. zstep F_5bb70 D_5bb70. zstep F_5bb74 D_5bb74. zstep F_5bb78 D_5bb78.
  zld F_5bb7c D_5bb7c (ca + 80 * c + 8) Ccsz'.
  zstep F_5bb80 D_5bb80.
  stepn F_5bb84 D_5bb84. rwH. rewrite (art_zb_srli_exact _ 30 (cnt * 4)) by lia.
  zstep F_5bb88 D_5bb88. zstep F_5bb8c D_5bb8c.
  stepn F_5bb90 D_5bb90. rwH. rewrite (art_zb_srli_exact _ 4 w) by lia.
  zsw F_5bb94 D_5bb94 (ca + 80 * c) (cnt + 1) ltac:(zwok').
  zsw F_5bb98 D_5bb98 (ca + 80 * c + 16 + 4 * cnt) w ltac:(zwok').
  zstep F_5bb9c D_5bb9c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csv2 : cellA X (ca + 2576) 8 sv) by zcell; assert (Wsv2 : wokA X (ca + 2576) 8) by zwok end.
  zamoadd_da F_5bba0 D_5bba0 (ca + 2576) sv (0 - csz) Csv2 ltac:(exact Wsv2) ltac:(rewrite Z.add_mod, Hca8 by lia; reflexivity).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
     assert (G9 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (G18 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell;
     assert (G19 : cellA X (sp - 40) 8 (U (getr regs 19))) by zcell; assert (G20 : cellA X (sp - 48) 8 (U (getr regs 20))) by zcell end.
  zld F_5bba4 D_5bba4 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_5bba8 D_5bba8 (sp - 16) G8. rewrite Z_to_bv_bv_unsigned.
  zld F_5bbac D_5bbac (sp - 24) G9. rewrite Z_to_bv_bv_unsigned.
  zld F_5bbb0 D_5bbb0 (sp - 32) G18. rewrite Z_to_bv_bv_unsigned.
  zld F_5bbb4 D_5bbb4 (sp - 40) G19. rewrite Z_to_bv_bv_unsigned.
  zld F_5bbb8 D_5bbb8 (sp - 48) G20. rewrite Z_to_bv_bv_unsigned.
  zstep F_5bbbc D_5bbbc.
  stepret F_5bbc0 D_5bbc0 raw ltac:(reflexivity).
  unfold art_f48. zret.
Qed.

Definition art_f80 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
    (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (sp - 72) (U (getr regs 23)).

Lemma art_mrtos_a : forall regs (M rom : word -> option byte) (raw : word) (sp ia c ris : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 0 ->
  0x6b3000 + 80 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 80) 80 -> 1 <= c <= 30 -> 0x10000 <= ia -> ia + 64 <= 0x6b3000 -> 0 <= ris < 2 ^ 63 ->
  cellA M (ia + 48) 8 ris ->
  exists regs', msteps ASEGS (mkst regs (0x5c550 : word) M rom) (mkst regs' (0x5c5cc : word) (art_f80 M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 18 = Z_to_bv 64 (AsanTab.class_size c) /\ getr regs' 19 = Z_to_bv 64 ia /\ getr regs' 21 = Z_to_bv 64 0
    /\ getr regs' 22 = Z_to_bv 64 ris /\ getr regs' 11 = Z_to_bv 64 (c * 2 ^ 7)
    /\ (forall r : reg, In r [3; 4; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp ia c ris H1 H2 H10 H12 H13 Hsp Hsp' W Hc Hia Hia' Hris Cris.
  destruct (Z_le_gt_dec c 16) as [Lc|Gc].
  - eexists. split.
    { zstep F_5c500 D_5c500.
      zsd F_5c504 D_5c504 (sp - 8) (U raw) ltac:(rewok W). zsd F_5c508 D_5c508 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_5c50c D_5c50c (sp - 24) (U (getr regs 9)) ltac:(rewok W).
      zsd F_5c510 D_5c510 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_5c514 D_5c514 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5c518 D_5c518 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zsd F_5c51c D_5c51c (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_5c520 D_5c520 (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd F_5c524 D_5c524 (sp - 72) (U (getr regs 23)) ltac:(rewok W).
      zstep F_5c528 D_5c528. zstep F_5c52c D_5c52c. zstep F_5c530 D_5c530. zstep F_5c534 D_5c534.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
      zld F_5c538 D_5c538 (ia + 48) Cris'.
      zstep F_5c53c D_5c53c. zstep F_5c540 D_5c540.
      zbft F_5c544 D_5c544.
      zstep F_5c548 D_5c548.
      zbft F_5c54c D_5c54c.
      zstep F_5c550 D_5c550.
      stepn F_5c554 D_5c554.
      unfold art_f80. apply mst_refl. }
    rewrite (art_class_size_small c ltac:(lia)).
    split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    { zstep F_5c500 D_5c500.
      zsd F_5c504 D_5c504 (sp - 8) (U raw) ltac:(rewok W). zsd F_5c508 D_5c508 (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_5c50c D_5c50c (sp - 24) (U (getr regs 9)) ltac:(rewok W).
      zsd F_5c510 D_5c510 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_5c514 D_5c514 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_5c518 D_5c518 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zsd F_5c51c D_5c51c (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_5c520 D_5c520 (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd F_5c524 D_5c524 (sp - 72) (U (getr regs 23)) ltac:(rewok W).
      zstep F_5c528 D_5c528. zstep F_5c52c D_5c52c. zstep F_5c530 D_5c530. zstep F_5c534 D_5c534.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
      zld F_5c538 D_5c538 (ia + 48) Cris'.
      zstep F_5c53c D_5c53c. zstep F_5c540 D_5c540.
      zbft F_5c544 D_5c544.
      zstep F_5c548 D_5c548.
      zbtk F_5c54c D_5c54c.
      zstep F_5c558 D_5c558. zstep F_5c55c D_5c55c. zstep F_5c560 D_5c560. zstep F_5c564 D_5c564. zstep F_5c568 D_5c568. zstep F_5c56c D_5c56c.
      zstep F_5c570 D_5c570. zstep F_5c574 D_5c574. zstep F_5c578 D_5c578.
      fold (art_pop_szw c). rewrite (art_pop_szw_ok c ltac:(lia)).
      unfold art_f80. apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_mrtos_b : forall regs (M rom : word -> option byte) (raw : word) (sp ia c ris sz nfree nfr j g8 g9 g18 g19 g20 g21 g22 g23 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 80) -> getr regs 18 = Z_to_bv 64 sz -> getr regs 19 = Z_to_bv 64 ia -> getr regs 21 = Z_to_bv 64 0 ->
  getr regs 22 = Z_to_bv 64 ris -> getr regs 11 = Z_to_bv 64 (c * 2 ^ 7) -> ret_ok raw ->
  80 <= sp -> sp < 2 ^ 64 -> 1 <= c <= 30 -> 0x10000 <= ia -> ia + 64 <= 0x6b3000 -> 0 <= ris -> ris + 128 * 64 < 2 ^ 47 -> 32 <= sz <= 65536 ->
  0 <= nfree < 2 ^ 40 -> 0 <= nfr < 2 ^ 64 -> 0 <= j < 2 ^ 64 ->
  0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> 0 <= g18 < 2 ^ 64 -> 0 <= g19 < 2 ^ 64 -> 0 <= g20 < 2 ^ 64 -> 0 <= g21 < 2 ^ 64 -> 0 <= g22 < 2 ^ 64 -> 0 <= g23 < 2 ^ 64 ->
  cellA M 0x153118 8 0x1ec460 -> cellA M 0x1ec460 8 4096 -> cellA M (ia + 40) 4 0xffffffff ->
  cellA M (ris + 128 * c + 16) 8 nfree -> cellA M (ris + 128 * c + 80) 8 nfr -> cellA M (ris + 128 * c + 88) 8 j ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  cellA M (sp - 56) 8 g21 -> cellA M (sp - 64) 8 g22 -> cellA M (sp - 72) 8 g23 ->
  exists regs', msteps ASEGS (mkst regs (0x5c5cc : word) M rom) (mkst regs' raw M rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18 /\ getr regs' 19 = Z_to_bv 64 g19
    /\ getr regs' 20 = Z_to_bv 64 g20 /\ getr regs' 21 = Z_to_bv 64 g21 /\ getr regs' 22 = Z_to_bv 64 g22 /\ getr regs' 23 = Z_to_bv 64 g23
    /\ (forall r : reg, In r [3; 4; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp ia c ris sz nfree nfr j g8 g9 g18 g19 g20 g21 g22 g23 H2 H18 H19 H21 H22 H11 Hret Hsp Hsp' Hc Hia Hia' Hris Hris' Hsz Hnfree Hnfr Hj
    Hg8 Hg9 Hg18 Hg19 Hg20 Hg21 Hg22 Hg23 Cpc Cpg Crel Cnfree Cnfr Cj F1 F8 F9 F18 F19 F20 F21 F22 F23.
  assert (HP : 0 <= nfree * sz < 2 ^ 64) by nia.
  set (P := nfree * sz) in *.
  set (Y := ((nfr - j) * sz) mod 2 ^ 64).
  assert (HY : 0 <= Y < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (EPI : forall rg, getr rg 2 = Z_to_bv 64 (sp - 80) ->
            exists regs', msteps ASEGS (mkst rg (0x5c6f8 : word) M rom) (mkst regs' raw M rom)
              /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18 /\ getr regs' 19 = Z_to_bv 64 g19
              /\ getr regs' 20 = Z_to_bv 64 g20 /\ getr regs' 21 = Z_to_bv 64 g21 /\ getr regs' 22 = Z_to_bv 64 g22 /\ getr regs' 23 = Z_to_bv 64 g23
              /\ (forall r : reg, In r [3; 4; 24; 25; 26; 27]%bv -> getr regs' r = getr rg r)).
  { intros rg G2. eexists. split.
    { zld F_5c6a8 D_5c6a8 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
      zld F_5c6ac D_5c6ac (sp - 16) F8. zld F_5c6b0 D_5c6b0 (sp - 24) F9. zld F_5c6b4 D_5c6b4 (sp - 32) F18. zld F_5c6b8 D_5c6b8 (sp - 40) F19.
      zld F_5c6bc D_5c6bc (sp - 48) F20. zld F_5c6c0 D_5c6c0 (sp - 56) F21. zld F_5c6c4 D_5c6c4 (sp - 64) F22. zld F_5c6c8 D_5c6c8 (sp - 72) F23.
      zstep F_5c6cc D_5c6cc.
      stepret F_5c6d0 D_5c6d0 raw ltac:(reflexivity).
      apply mst_refl. }
    split; [gres; f_equal; lia|]. do 8 (split; [gres; reflexivity|]).
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
  eassert (RUN0 : msteps ASEGS (mkst regs (0x5c5cc : word) M rom) _).
  { stepn F_5c57c D_5c57c.
    zld F_5c580 D_5c580 0x153118 Cpc.
    zld F_5c584 D_5c584 0x1ec460 Cpg.
    zstep F_5c588 D_5c588.
    zbft F_5c58c D_5c58c.
    zld F_5c590 D_5c590 (ris + 128 * c + 16) Cnfree.
    zstep F_5c594 D_5c594. fold P.
    apply mst_refl. }
  destruct (Z_lt_le_dec P 4096) as [LP|GP].
  -
    eassert (RUN1 : msteps ASEGS _ _).
    { eapply msteps_trans; [exact RUN0|]. zbft F_5c598 D_5c598. stepn F_5c59c D_5c59c. apply mst_refl. }
    match type of RUN1 with msteps _ _ (mkst ?R _ _ _) => destruct (EPI R ltac:(gres; exact H2)) as (r' & RUN2 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & EK) end.
    exists r'. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
    do 9 (split; [assumption|]). intros r Hr. rewrite (EK r Hr). cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eassert (RUN1 : msteps ASEGS _ _).
    { eapply msteps_trans; [exact RUN0|]. zbtk F_5c598 D_5c598.
      zld F_5c5b4 D_5c5b4 (ris + 128 * c + 80) Cnfr.
      zld F_5c5b8 D_5c5b8 (ris + 128 * c + 88) Cj.
      zstep F_5c5bc D_5c5bc. zstep F_5c5c0 D_5c5c0.
      rewrite <- (art_zb_mod64 ((nfr - j) * sz)). fold Y.
      apply mst_refl. }
    destruct (Z_lt_le_dec Y 4096) as [LY|GY].
    +
      eassert (RUN1b : msteps ASEGS _ _).
      { eapply msteps_trans; [exact RUN1|]. zbtk F_5c5c4 D_5c5c4. apply mst_refl. }
      match type of RUN1b with msteps _ _ (mkst ?R _ _ _) => destruct (EPI R ltac:(gres; exact H2)) as (r' & RUN2 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & EK) end.
      exists r'. split; [eapply msteps_trans; [exact RUN1b|exact RUN2]|].
      do 9 (split; [assumption|]). intros r Hr. rewrite (EK r Hr). cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
    +
      eassert (RUN1b : msteps ASEGS _ _).
      { eapply msteps_trans; [exact RUN1|]. zbft F_5c5c4 D_5c5c4. zbft F_5c5c8 D_5c5c8.
        zlw F_5c5cc D_5c5cc (ia + 40) Crel.
        stepb_tk F_5c5d0 D_5c5d0 ltac:(rwH; reflexivity).
        apply mst_refl. }
      match type of RUN1b with msteps _ _ (mkst ?R _ _ _) => destruct (EPI R ltac:(gres; exact H2)) as (r' & RUN2 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & EK) end.
      exists r'. split; [eapply msteps_trans; [exact RUN1b|exact RUN2]|].
      do 9 (split; [assumption|]). intros r Hr. rewrite (EK r Hr). cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Lemma art_mrtos_ret : forall regs (M rom : word -> option byte) (raw : word) (sp ia c ris nfree nfr : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 0 ->
  0x6b3000 + 80 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 80) 80 -> 1 <= c <= 30 -> 0x10000 <= ia -> ia + 64 <= 0x6b3000 -> 0x6b3000 <= ris -> ris + 128 * 64 < 2 ^ 47 ->
  apart (sp - 80) 80 (ris + 128 * c) 128 -> 0 <= nfree < 2 ^ 40 -> 0 <= nfr < 2 ^ 64 -> wrA M (ris + 128 * c) 128 ->
  cellA M (ia + 48) 8 ris -> cellA M 0x153118 8 0x1ec460 -> cellA M 0x1ec460 8 4096 -> cellA M (ia + 40) 4 0xffffffff ->
  cellA M (ris + 128 * c + 16) 8 nfree -> cellA M (ris + 128 * c + 80) 8 nfr ->
  exists regs', msteps ASEGS (mkst regs (0x5c550 : word) M rom) (mkst regs' raw (art_f80 M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp ia c ris nfree nfr H1 Hret H2 H10 H12 H13 Hsp Hsp' W Hc Hia Hia' Hris Hris' Ar Hnfree Hnfr Wr Cris Cpc Cpg Crel Cnfree Cnfr.
  destruct (art_cell_exists M (ris + 128 * c + 88) 8 ltac:(lia) ltac:(right; lia) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wr|lia|cbn; lia])) as (j & Hj & Cj).
  destruct (art_mrtos_a regs M rom raw sp ia c ris H1 H2 H10 H12 H13 Hsp Hsp' W Hc Hia Hia' ltac:(lia) Cris) as (r1 & RUN1 & A2 & A18 & A19 & A21 & A22 & A11 & AK).
  destruct (art_class_size_facts c Hc) as [Hsz _].
  pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as R18.
  pose proof (bv_unsigned_in_range 64 (getr regs 19)) as R19. pose proof (bv_unsigned_in_range 64 (getr regs 20)) as R20. pose proof (bv_unsigned_in_range 64 (getr regs 21)) as R21.
  pose proof (bv_unsigned_in_range 64 (getr regs 22)) as R22. pose proof (bv_unsigned_in_range 64 (getr regs 23)) as R23. change (bv_modulus 64) with (2 ^ 64) in *.
  unfold apart in Ar.
  assert (CELLS : let X := art_f80 M sp raw regs in
            cellA X 0x153118 8 0x1ec460 /\ cellA X 0x1ec460 8 4096 /\ cellA X (ia + 40) 4 0xffffffff
            /\ cellA X (ris + 128 * c + 16) 8 nfree /\ cellA X (ris + 128 * c + 80) 8 nfr /\ cellA X (ris + 128 * c + 88) 8 j
            /\ cellA X (sp - 8) 8 (U raw) /\ cellA X (sp - 16) 8 (U (getr regs 8)) /\ cellA X (sp - 24) 8 (U (getr regs 9)) /\ cellA X (sp - 32) 8 (U (getr regs 18))
            /\ cellA X (sp - 40) 8 (U (getr regs 19)) /\ cellA X (sp - 48) 8 (U (getr regs 20)) /\ cellA X (sp - 56) 8 (U (getr regs 21)) /\ cellA X (sp - 64) 8 (U (getr regs 22))
            /\ cellA X (sp - 72) 8 (U (getr regs 23))).
  { cbv zeta. unfold art_f80. repeat split; zcell. }
  cbv zeta in CELLS. destruct CELLS as (X1 & X2 & X3 & X4 & X5 & X6 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23).
  destruct (art_mrtos_b r1 (art_f80 M sp raw regs) rom raw sp ia c ris (AsanTab.class_size c) nfree nfr j _ _ _ _ _ _ _ _ A2 A18 A19 A21 A22 A11 Hret ltac:(lia) Hsp' Hc Hia Hia' ltac:(lia) Hris' Hsz
              Hnfree Hnfr Hj R8 R9 R18 R19 R20 R21 R22 R23 X1 X2 X3 X4 X5 X6 G1 G8 G9 G18 G19 G20 G21 G22 G23) as (r2 & RUN2 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & BK).
  exists r2. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|]. split; [exact B2|].
  intros r Hr. cbn [In] in Hr.
  destruct Hr as [<-|Hr]; [rewrite BK by (cbn; tauto); apply AK; cbn; tauto|]. destruct Hr as [<-|Hr]; [rewrite BK by (cbn; tauto); apply AK; cbn; tauto|].
  destruct Hr as [<-|Hr]; [rewrite B8; apply Z_to_bv_bv_unsigned|]. destruct Hr as [<-|Hr]; [rewrite B9; apply Z_to_bv_bv_unsigned|].
  destruct Hr as [<-|Hr]; [rewrite B18; apply Z_to_bv_bv_unsigned|]. destruct Hr as [<-|Hr]; [rewrite B19; apply Z_to_bv_bv_unsigned|].
  destruct Hr as [<-|Hr]; [rewrite B20; apply Z_to_bv_bv_unsigned|]. destruct Hr as [<-|Hr]; [rewrite B21; apply Z_to_bv_bv_unsigned|].
  destruct Hr as [<-|Hr]; [rewrite B22; apply Z_to_bv_bv_unsigned|]. destruct Hr as [<-|Hr]; [rewrite B23; apply Z_to_bv_bv_unsigned|].
  repeat (destruct Hr as [<-|Hr]; [rewrite BK by (cbn; tauto); apply AK; cbn; tauto|]). destruct Hr.
Qed.

Lemma art_f80_facts : forall M sp raw regs, 80 <= sp -> sp < 2 ^ 64 ->
  mem_grows M (art_f80 M sp raw regs) /\ art_agree [(sp - 80, 80)] M (art_f80 M sp raw regs).
Proof. intros M sp raw regs Hsp Hsp'. unfold art_f80. split; [zgrows|]. eapply art_agree_sub; [zagree|]. zsub. Qed.
Lemma art_f48_facts : forall M sp raw regs, 48 <= sp -> sp < 2 ^ 64 ->
  mem_grows M (art_f48 M sp raw regs) /\ art_agree [(sp - 48, 48)] M (art_f48 M sp raw regs).
Proof. intros M sp raw regs Hsp Hsp'. unfold art_f48. split; [zgrows|]. eapply art_agree_sub; [zagree|]. zsub. Qed.
Lemma art_f48_cells : forall M sp raw regs, 48 <= sp -> sp < 2 ^ 64 ->
  cellA (art_f48 M sp raw regs) (sp - 8) 8 (U raw) /\ cellA (art_f48 M sp raw regs) (sp - 16) 8 (U (getr regs 8)) /\ cellA (art_f48 M sp raw regs) (sp - 24) 8 (U (getr regs 9))
  /\ cellA (art_f48 M sp raw regs) (sp - 32) 8 (U (getr regs 18)) /\ cellA (art_f48 M sp raw regs) (sp - 40) 8 (U (getr regs 19)) /\ cellA (art_f48 M sp raw regs) (sp - 48) 8 (U (getr regs 20)).
Proof. intros M sp raw regs H1 H2. unfold art_f48. repeat split; zcell. Qed.
End FPX.
