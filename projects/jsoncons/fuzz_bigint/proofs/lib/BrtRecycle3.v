(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac BrtLeaf BrtAllocG BrtPoison ArtRuns ArtRunsMem BrtFp BrtPopulate1 BrtCellEx.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_3f2bc_408d0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition art_f48 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20)).

Section FPX. Context {fx : PropExec.FPState}.

Lemma art_lcd_push_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ca ia c p spb w mc cnt csz sv : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 p ->
  0x634000 + 48 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 48) 48 ->
  1 <= c <= 31 -> 4096 <= ca -> ca + 2592 <= sp - 48 -> ca mod 8 = 0 -> (ca + 2592 <= 0x10000 \/ 0x634000 <= ca) -> 0x10000 <= ia -> ia + 64 <= 0x634000 ->
  0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> p = spb + c * 2 ^ 32 + 16 * w -> 0 <= w < 2 ^ 28 -> 0 <= cnt < mc -> mc <= 16 -> 0 <= csz < 2 ^ 63 -> 0 <= sv < 2 ^ 64 ->
  wrA M ca 2592 ->
  cellA M (ca + 80 * c) 4 cnt -> cellA M (ca + 80 * c + 4) 4 mc -> cellA M (ca + 80 * c + 8) 8 csz -> cellA M (ia + 32) 8 spb -> cellA M (ca + 2576) 8 sv ->
  msteps ASEGS (mkst regs (0x3fd04 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 10 (Z_to_bv 64 (ca + 2576))) 11 (Z_to_bv 64 (0 - csz))) 12 (Z_to_bv 64 (ca + c * 80 + cnt * 4))) 13 (Z_to_bv 64 w)) 14 (Z_to_bv 64 (cnt + 1))) 15 (Z_to_bv 64 mc)) 18 (getr regs 18)) 19 (getr regs 19)) 20 (getr regs 20))
       raw (Wn 8 (Wn 4 (Wn 4 (art_f48 M sp raw regs) (ca + 80 * c) (cnt + 1)) (ca + 80 * c + 16 + 4 * cnt) w) (ca + 2576) (sv + (0 - csz))) rom).
Proof.
  intros regs M rom raw sp ca ia c p spb w mc cnt csz sv H1 Hret H2 H10 H11 H12 H13 Hsp Hsp' W Hc Hca Hca' Hca8 Hcai Hia Hia' Hspb Hspb' Ep Hw Hcnt Hmc Hcsz Hsv Wca Ccnt Cmc Ccsz Cspb Csv.
  zstep F_3fd04 D_3fd04.
  zsd F_3fd08 D_3fd08 (sp - 8) (U raw) ltac:(rewok W). zsd F_3fd0c D_3fd0c (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_3fd10 D_3fd10 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_3fd14 D_3fd14 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_3fd18 D_3fd18 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_3fd1c D_3fd1c (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zbft F_3fd20 D_3fd20.
  zstep F_3fd24 D_3fd24.
  zbft F_3fd28 D_3fd28.
  zstep F_3fd2c D_3fd2c. zstep F_3fd30 D_3fd30. zstep F_3fd34 D_3fd34.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 mc) by zcell; assert (Ccnt' : cellA X (ca + 80 * c) 4 cnt) by zcell;
    assert (Cspb' : cellA X (ia + 32) 8 spb) by zcell; assert (Ccsz' : cellA X (ca + 80 * c + 8) 8 csz) by zcell; assert (Csv' : cellA X (ca + 2576) 8 sv) by zcell;
    assert (Wca' : wrA X ca 2592) by zwr end.
  zlw F_3fd38 D_3fd38 (ca + 80 * c + 4) Cmc'.
  zbft F_3fd3c D_3fd3c.
  zlw F_3fd40 D_3fd40 (ca + 80 * c) Ccnt'.
  zbft F_3fd44 D_3fd44.
  zld F_3fd48 D_3fd48 (ia + 32) Cspb'.
  zstep F_3fd4c D_3fd4c. zstep F_3fd50 D_3fd50. zstep F_3fd54 D_3fd54. zstep F_3fd58 D_3fd58. zstep F_3fd5c D_3fd5c.
  zld F_3fd60 D_3fd60 (ca + 80 * c + 8) Ccsz'.
  zstep F_3fd64 D_3fd64.
  stepn F_3fd68 D_3fd68. rwH. rewrite (art_zb_srli_exact _ 30 (cnt * 4)) by lia.
  zstep F_3fd6c D_3fd6c. zstep F_3fd70 D_3fd70.
  stepn F_3fd74 D_3fd74. rwH. rewrite (art_zb_srli_exact _ 4 w) by lia.
  zsw F_3fd78 D_3fd78 (ca + 80 * c) (cnt + 1) ltac:(zwok').
  zsw F_3fd7c D_3fd7c (ca + 80 * c + 16 + 4 * cnt) w ltac:(zwok').
  zstep F_3fd80 D_3fd80.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csv2 : cellA X (ca + 2576) 8 sv) by zcell; assert (Wsv2 : wokA X (ca + 2576) 8) by zwok end.
  zamoadd_da F_3fd84 D_3fd84 (ca + 2576) sv (0 - csz) Csv2 ltac:(exact Wsv2) ltac:(rewrite Z.add_mod, Hca8 by lia; reflexivity).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
     assert (G9 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (G18 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell;
     assert (G19 : cellA X (sp - 40) 8 (U (getr regs 19))) by zcell; assert (G20 : cellA X (sp - 48) 8 (U (getr regs 20))) by zcell end.
  zld F_3fd88 D_3fd88 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_3fd8c D_3fd8c (sp - 16) G8. rewrite Z_to_bv_bv_unsigned.
  zld F_3fd90 D_3fd90 (sp - 24) G9. rewrite Z_to_bv_bv_unsigned.
  zld F_3fd94 D_3fd94 (sp - 32) G18. rewrite Z_to_bv_bv_unsigned.
  zld F_3fd98 D_3fd98 (sp - 40) G19. rewrite Z_to_bv_bv_unsigned.
  zld F_3fd9c D_3fd9c (sp - 48) G20. rewrite Z_to_bv_bv_unsigned.
  zstep F_3fda0 D_3fda0.
  stepret F_3fda4 D_3fda4 raw ltac:(reflexivity).
  unfold art_f48. zret.
Qed.

(* [comment removed for export] *)
Definition art_f80 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)))
    (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (sp - 72) (U (getr regs 23)).

(* [comment removed for export] *)
Lemma art_mrtos_a : forall regs (M rom : word -> option byte) (raw : word) (sp ia c ris : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 0 ->
  0x634000 + 80 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 80) 80 -> 1 <= c <= 30 -> 0x10000 <= ia -> ia + 64 <= 0x634000 -> 0 <= ris < 2 ^ 63 ->
  cellA M (ia + 48) 8 ris ->
  exists regs', msteps ASEGS (mkst regs (0x406e4 : word) M rom) (mkst regs' (0x40760 : word) (art_f80 M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 18 = Z_to_bv 64 (AsanTab.class_size c) /\ getr regs' 19 = Z_to_bv 64 ia /\ getr regs' 21 = Z_to_bv 64 0
    /\ getr regs' 22 = Z_to_bv 64 ris /\ getr regs' 11 = Z_to_bv 64 (c * 2 ^ 7)
    /\ (forall r : reg, In r [3; 4; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp ia c ris H1 H2 H10 H12 H13 Hsp Hsp' W Hc Hia Hia' Hris Cris.
  destruct (Z_le_gt_dec c 16) as [Lc|Gc].
  - eexists. split.
    { zstep F_406e4 D_406e4.
      zsd F_406e8 D_406e8 (sp - 8) (U raw) ltac:(rewok W). zsd F_406ec D_406ec (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_406f0 D_406f0 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
      zsd F_406f4 D_406f4 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_406f8 D_406f8 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_406fc D_406fc (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zsd F_40700 D_40700 (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_40704 D_40704 (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd F_40708 D_40708 (sp - 72) (U (getr regs 23)) ltac:(rewok W).
      zstep F_4070c D_4070c. zstep F_40710 D_40710. zstep F_40714 D_40714. zstep F_40718 D_40718.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
      zld F_4071c D_4071c (ia + 48) Cris'.
      zstep F_40720 D_40720. zstep F_40724 D_40724.
      zbft F_40728 D_40728.
      zstep F_4072c D_4072c.
      zbft F_40730 D_40730.
      zstep F_40734 D_40734.
      stepn F_40738 D_40738.
      unfold art_f80. apply mst_refl. }
    rewrite (art_class_size_small c ltac:(lia)).
    split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    { zstep F_406e4 D_406e4.
      zsd F_406e8 D_406e8 (sp - 8) (U raw) ltac:(rewok W). zsd F_406ec D_406ec (sp - 16) (U (getr regs 8)) ltac:(rewok W). zsd F_406f0 D_406f0 (sp - 24) (U (getr regs 9)) ltac:(rewok W).
      zsd F_406f4 D_406f4 (sp - 32) (U (getr regs 18)) ltac:(rewok W). zsd F_406f8 D_406f8 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_406fc D_406fc (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zsd F_40700 D_40700 (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_40704 D_40704 (sp - 64) (U (getr regs 22)) ltac:(rewok W). zsd F_40708 D_40708 (sp - 72) (U (getr regs 23)) ltac:(rewok W).
      zstep F_4070c D_4070c. zstep F_40710 D_40710. zstep F_40714 D_40714. zstep F_40718 D_40718.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cris' : cellA X (ia + 48) 8 ris) by zcell end.
      zld F_4071c D_4071c (ia + 48) Cris'.
      zstep F_40720 D_40720. zstep F_40724 D_40724.
      zbft F_40728 D_40728.
      zstep F_4072c D_4072c.
      zbtk F_40730 D_40730.
      zstep F_4073c D_4073c. zstep F_40740 D_40740. zstep F_40744 D_40744. zstep F_40748 D_40748. zstep F_4074c D_4074c. zstep F_40750 D_40750.
      zstep F_40754 D_40754. zstep F_40758 D_40758. zstep F_4075c D_4075c.
      fold (art_pop_szw c). rewrite (art_pop_szw_ok c ltac:(lia)).
      unfold art_f80. apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma art_mrtos_b : forall regs (M rom : word -> option byte) (raw : word) (sp ia c ris sz nfree nfr j g8 g9 g18 g19 g20 g21 g22 g23 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 80) -> getr regs 18 = Z_to_bv 64 sz -> getr regs 19 = Z_to_bv 64 ia -> getr regs 21 = Z_to_bv 64 0 ->
  getr regs 22 = Z_to_bv 64 ris -> getr regs 11 = Z_to_bv 64 (c * 2 ^ 7) -> ret_ok raw ->
  80 <= sp -> sp < 2 ^ 64 -> 1 <= c <= 30 -> 0x10000 <= ia -> ia + 64 <= 0x634000 -> 0 <= ris -> ris + 128 * 64 < 2 ^ 47 -> 32 <= sz <= 65536 ->
  0 <= nfree < 2 ^ 40 -> 0 <= nfr < 2 ^ 64 -> 0 <= j < 2 ^ 64 ->
  0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> 0 <= g18 < 2 ^ 64 -> 0 <= g19 < 2 ^ 64 -> 0 <= g20 < 2 ^ 64 -> 0 <= g21 < 2 ^ 64 -> 0 <= g22 < 2 ^ 64 -> 0 <= g23 < 2 ^ 64 ->
  cellA M 0xd64a8 8 0x16e1e0 -> cellA M 0x16e1e0 8 4096 -> cellA M (ia + 40) 4 0xffffffff ->
  cellA M (ris + 128 * c + 16) 8 nfree -> cellA M (ris + 128 * c + 80) 8 nfr -> cellA M (ris + 128 * c + 88) 8 j ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  cellA M (sp - 56) 8 g21 -> cellA M (sp - 64) 8 g22 -> cellA M (sp - 72) 8 g23 ->
  exists regs', msteps ASEGS (mkst regs (0x40760 : word) M rom) (mkst regs' raw M rom)
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
            exists regs', msteps ASEGS (mkst rg (0x4088c : word) M rom) (mkst regs' raw M rom)
              /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18 /\ getr regs' 19 = Z_to_bv 64 g19
              /\ getr regs' 20 = Z_to_bv 64 g20 /\ getr regs' 21 = Z_to_bv 64 g21 /\ getr regs' 22 = Z_to_bv 64 g22 /\ getr regs' 23 = Z_to_bv 64 g23
              /\ (forall r : reg, In r [3; 4; 24; 25; 26; 27]%bv -> getr regs' r = getr rg r)).
  { intros rg G2. eexists. split.
    { zld F_4088c D_4088c (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
      zld F_40890 D_40890 (sp - 16) F8. zld F_40894 D_40894 (sp - 24) F9. zld F_40898 D_40898 (sp - 32) F18. zld F_4089c D_4089c (sp - 40) F19.
      zld F_408a0 D_408a0 (sp - 48) F20. zld F_408a4 D_408a4 (sp - 56) F21. zld F_408a8 D_408a8 (sp - 64) F22. zld F_408ac D_408ac (sp - 72) F23.
      zstep F_408b0 D_408b0.
      stepret F_408b4 D_408b4 raw ltac:(reflexivity).
      apply mst_refl. }
    split; [gres; f_equal; lia|]. do 8 (split; [gres; reflexivity|]).
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
  eassert (RUN0 : msteps ASEGS (mkst regs (0x40760 : word) M rom) _).
  { stepn F_40760 D_40760.
    zld F_40764 D_40764 0xd64a8 Cpc.
    zld F_40768 D_40768 0x16e1e0 Cpg.
    zstep F_4076c D_4076c.
    zbft F_40770 D_40770.
    zld F_40774 D_40774 (ris + 128 * c + 16) Cnfree.
    zstep F_40778 D_40778. fold P.
    apply mst_refl. }
  destruct (Z_lt_le_dec P 4096) as [LP|GP].
  - (* [comment removed for export] *)
    eassert (RUN1 : msteps ASEGS _ _).
    { eapply msteps_trans; [exact RUN0|]. zbft F_4077c D_4077c. stepn F_40780 D_40780. apply mst_refl. }
    match type of RUN1 with msteps _ _ (mkst ?R _ _ _) => destruct (EPI R ltac:(gres; exact H2)) as (r' & RUN2 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & EK) end.
    exists r'. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
    do 9 (split; [assumption|]). intros r Hr. rewrite (EK r Hr). cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eassert (RUN1 : msteps ASEGS _ _).
    { eapply msteps_trans; [exact RUN0|]. zbtk F_4077c D_4077c.
      zld F_40798 D_40798 (ris + 128 * c + 80) Cnfr.
      zld F_4079c D_4079c (ris + 128 * c + 88) Cj.
      zstep F_407a0 D_407a0. zstep F_407a4 D_407a4.
      rewrite <- (art_zb_mod64 ((nfr - j) * sz)). fold Y.
      apply mst_refl. }
    destruct (Z_lt_le_dec Y 4096) as [LY|GY].
    + (* [comment removed for export] *)
      eassert (RUN1b : msteps ASEGS _ _).
      { eapply msteps_trans; [exact RUN1|]. zbtk F_407a8 D_407a8. apply mst_refl. }
      match type of RUN1b with msteps _ _ (mkst ?R _ _ _) => destruct (EPI R ltac:(gres; exact H2)) as (r' & RUN2 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & EK) end.
      exists r'. split; [eapply msteps_trans; [exact RUN1b|exact RUN2]|].
      do 9 (split; [assumption|]). intros r Hr. rewrite (EK r Hr). cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
    + (* [comment removed for export] *)
      eassert (RUN1b : msteps ASEGS _ _).
      { eapply msteps_trans; [exact RUN1|]. zbft F_407a8 D_407a8. zbft F_407ac D_407ac.
        zlw F_407b0 D_407b0 (ia + 40) Crel.
        stepb_tk F_407b4 D_407b4 ltac:(rwH; reflexivity).
        apply mst_refl. }
      match type of RUN1b with msteps _ _ (mkst ?R _ _ _) => destruct (EPI R ltac:(gres; exact H2)) as (r' & RUN2 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & EK) end.
      exists r'. split; [eapply msteps_trans; [exact RUN1b|exact RUN2]|].
      do 9 (split; [assumption|]). intros r Hr. rewrite (EK r Hr). cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

(* [comment removed for export] *)
Lemma art_mrtos_ret : forall regs (M rom : word -> option byte) (raw : word) (sp ia c ris nfree nfr : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 0 ->
  0x634000 + 80 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 80) 80 -> 1 <= c <= 30 -> 0x10000 <= ia -> ia + 64 <= 0x634000 -> 0x634000 <= ris -> ris + 128 * 64 < 2 ^ 47 ->
  apart (sp - 80) 80 (ris + 128 * c) 128 -> 0 <= nfree < 2 ^ 40 -> 0 <= nfr < 2 ^ 64 -> wrA M (ris + 128 * c) 128 ->
  cellA M (ia + 48) 8 ris -> cellA M 0xd64a8 8 0x16e1e0 -> cellA M 0x16e1e0 8 4096 -> cellA M (ia + 40) 4 0xffffffff ->
  cellA M (ris + 128 * c + 16) 8 nfree -> cellA M (ris + 128 * c + 80) 8 nfr ->
  exists regs', msteps ASEGS (mkst regs (0x406e4 : word) M rom) (mkst regs' raw (art_f80 M sp raw regs) rom)
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
            cellA X 0xd64a8 8 0x16e1e0 /\ cellA X 0x16e1e0 8 4096 /\ cellA X (ia + 40) 4 0xffffffff
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
