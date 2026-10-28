(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatInitCache_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatRefill1_b BatPopulate1_b BatCellEx_b BatCls_b BatClsRep_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatRecycle3_b BatRecycle3D_b BatRecycle3R_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3ef18_4052c_b.
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

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_lcd_full_a_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ca ia c p mc : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 ia -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 p ->
  0x696000 + 48 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 48) 48 ->
  1 <= c <= 31 -> 4096 <= ca -> ca + 2592 <= sp - 48 -> 0 <= ia < 2 ^ 64 -> 0 <= p < 2 ^ 64 -> 1 <= mc <= 16 ->
  cellA M (ca + 80 * c) 4 mc -> cellA M (ca + 80 * c + 4) 4 mc ->
  msteps ASEGS (mkst regs (0x54cf8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x54ea8)) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 (ca + 80 * c))) 9 (Z_to_bv 64 ca)) 11 (Z_to_bv 64 (ca + 80 * c))) 12 (Z_to_bv 64 ia)) 13 (Z_to_bv 64 c)) 14 (Z_to_bv 64 mc)) 15 (Z_to_bv 64 mc)) 18 (Z_to_bv 64 ia)) 19 (Z_to_bv 64 c)) 20 (Z_to_bv 64 p))
       (0x5508c : word) (art_f48 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp ca ia c p mc H1 H2 H10 H11 H12 H13 Hsp Hsp' W Hc Hca Hca' Hia Hp Hmc Ccnt Cmc.
  zstep F_548e0 D_548e0.
  zsd F_548e4 D_548e4 (sp - 8) (U raw) ltac:(rewok W). zsd F_548e8 D_548e8 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_548ec D_548ec (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_548f0 D_548f0 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zsd F_548f4 D_548f4 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_548f8 D_548f8 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
  zbft F_548fc D_548fc.
  zstep F_54900 D_54900.
  zbft F_54904 D_54904.
  zstep F_54908 D_54908. zstep F_5490c D_5490c. zstep F_54910 D_54910.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cmc' : cellA X (ca + 80 * c + 4) 4 mc) by zcell; assert (Ccnt' : cellA X (ca + 80 * c) 4 mc) by zcell end.
  zlw F_54914 D_54914 (ca + 80 * c + 4) Cmc'.
  zbft F_54918 D_54918.
  zlw F_5491c D_5491c (ca + 80 * c) Ccnt'.
  zbtk F_54920 D_54920.
  zstep F_54a70 D_54a70. zstep F_54a74 D_54a74. zstep F_54a78 D_54a78. zstep F_54a7c D_54a7c. zstep F_54a80 D_54a80. zstep F_54a84 D_54a84. zstep F_54a88 D_54a88.
  stepn F_54a8c D_54a8c.
  unfold art_f48. zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_lcd_full_b_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ca ia c p spb w cnt csz sv g8 g9 g18 g19 g20 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 (ca + 80 * c) -> getr regs 9 = Z_to_bv 64 ca -> getr regs 18 = Z_to_bv 64 ia -> getr regs 19 = Z_to_bv 64 c -> getr regs 20 = Z_to_bv 64 p ->
  ret_ok raw -> 48 <= sp -> sp < 2 ^ 64 ->
  1 <= c <= 31 -> 4096 <= ca -> ca + 2592 <= sp - 48 -> ca mod 8 = 0 -> (ca + 2592 <= 0x10000 \/ 0x696000 <= ca) -> 0x10000 <= ia -> ia + 64 <= 0x696000 ->
  0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> p = spb + c * 2 ^ 32 + 16 * w -> 0 <= w < 2 ^ 28 -> 0 <= cnt < 16 -> 0 <= csz < 2 ^ 63 -> 0 <= sv < 2 ^ 64 ->
  0 <= g8 < 2 ^ 64 -> 0 <= g9 < 2 ^ 64 -> 0 <= g18 < 2 ^ 64 -> 0 <= g19 < 2 ^ 64 -> 0 <= g20 < 2 ^ 64 ->
  wrA M ca 2592 ->
  cellA M (ca + 80 * c) 4 cnt -> cellA M (ca + 80 * c + 8) 8 csz -> cellA M (ia + 32) 8 spb -> cellA M (ca + 2576) 8 sv ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  msteps ASEGS (mkst regs (0x54ea8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 g8)) 9 (Z_to_bv 64 g9)) 10 (Z_to_bv 64 (ca + 2576))) 11 (Z_to_bv 64 (0 - csz))) 12 (Z_to_bv 64 (ca + 80 * c + cnt * 4))) 13 (Z_to_bv 64 w)) 14 (Z_to_bv 64 (cnt + 1))) 18 (Z_to_bv 64 g18)) 19 (Z_to_bv 64 g19)) 20 (Z_to_bv 64 g20))
       raw (Wn 8 (Wn 4 (Wn 4 M (ca + 80 * c) (cnt + 1)) (ca + 80 * c + 16 + 4 * cnt) w) (ca + 2576) (sv + (0 - csz))) rom).
Proof.
  intros regs M rom raw sp ca ia c p spb w cnt csz sv g8 g9 g18 g19 g20 H2 H8 H9 H18 H19 H20 Hret Hsp Hsp' Hc Hca Hca' Hca8 Hcai Hia Hia' Hspb Hspb' Ep Hw Hcnt Hcsz Hsv
    Hg8 Hg9 Hg18 Hg19 Hg20 Wca Ccnt Ccsz Cspb Csv F1 F8 F9 F18 F19 F20.
  zstep F_54a90 D_54a90. zstep F_54a94 D_54a94. zstep F_54a98 D_54a98. zstep F_54a9c D_54a9c.
  zlw F_54aa0 D_54aa0 (ca + 80 * c) Ccnt.
  stepn F_54aa4 D_54aa4.
  zld F_54924 D_54924 (ia + 32) Cspb.
  zstep F_54928 D_54928. zstep F_5492c D_5492c. zstep F_54930 D_54930. zstep F_54934 D_54934. zstep F_54938 D_54938.
  zld F_5493c D_5493c (ca + 80 * c + 8) Ccsz.
  zstep F_54940 D_54940.
  stepn F_54944 D_54944. rwH. rewrite (art_zb_srli_exact _ 30 (cnt * 4)) by lia.
  zstep F_54948 D_54948. zstep F_5494c D_5494c.
  stepn F_54950 D_54950. rwH. rewrite (art_zb_srli_exact _ 4 w) by lia.
  zsw F_54954 D_54954 (ca + 80 * c) (cnt + 1) ltac:(rewok Wca).
  zsw F_54958 D_54958 (ca + 80 * c + 16 + 4 * cnt) w ltac:(zwok').
  zstep F_5495c D_5495c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Csv2 : cellA X (ca + 2576) 8 sv) by zcell; assert (Wsv2 : wokA X (ca + 2576) 8) by zwok end.
  zamoadd_da F_54960 D_54960 (ca + 2576) sv (0 - csz) Csv2 ltac:(exact Wsv2) ltac:(rewrite Z.add_mod, Hca8 by lia; reflexivity).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 g8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 g9) by zcell; assert (G18 : cellA X (sp - 32) 8 g18) by zcell;
     assert (G19 : cellA X (sp - 40) 8 g19) by zcell; assert (G20 : cellA X (sp - 48) 8 g20) by zcell end.
  zld F_54964 D_54964 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_54968 D_54968 (sp - 16) G8. zld F_5496c D_5496c (sp - 24) G9. zld F_54970 D_54970 (sp - 32) G18. zld F_54974 D_54974 (sp - 40) G19. zld F_54978 D_54978 (sp - 48) G20.
  zstep F_5497c D_5497c.
  stepret F_54980 D_54980 raw ltac:(reflexivity).
  zret.
Qed.
End FPX.

(* [comment removed for export] *)
Definition art_cls_push (w : Z) (cl : art_cls) : art_cls :=
  CLS (cl_cache cl ++ [w]) (cl_free cl) (cl_au cl) (cl_mu cl) (cl_mfa cl) (cl_na cl) (cl_nfr cl).
Definition art_cls_return (h : nat) (cl : art_cls) : art_cls :=
  let k := (length (cl_cache cl) - h)%nat in
  CLS (firstn k (cl_cache cl)) (cl_free cl ++ skipn k (cl_cache cl)) (cl_au cl) (cl_mu cl) (cl_mfa cl) (cl_na cl) (cl_nfr cl + Z.of_nat h).
Definition art_cls_full (c : Z) (cl : art_cls) : bool := Z.of_nat (length (cl_cache cl)) =? art_ic_mc c.
Definition art_cls_dealloc (c w : Z) (cl : art_cls) : art_cls :=
  if art_cls_full c cl then art_cls_push w (art_cls_return (Z.to_nat (art_ic_mc c / 2)) cl) else art_cls_push w cl.

Lemma art_ic_mc_half : forall c, 1 <= c <= 31 -> art_ic_mc c = 2 * (art_ic_mc c / 2) /\ 1 <= art_ic_mc c / 2 <= 8.
Proof.
  intros c Hc. unfold art_ic_mc. set (m := Z.max 1 (Z.min 8 (1024 / art_ic_size c))).
  assert (Hm : 1 <= m <= 8) by (unfold m; lia).
  replace (2 * m / 2) with m by (symmetry; rewrite Z.mul_comm; apply Z.div_mul; lia). lia.
Qed.

(* [comment removed for export] *)
Definition art_lcd_fp (sp ca spb ris c nf : Z) : list (Z * Z) :=
  [ (sp - 320, 320); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8); (ris + 128 * c, 128); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 32) ].

(* [comment removed for export] *)
Lemma art_cls_dealloc_ok : forall c w cl, 1 <= c <= 30 -> art_cls_ok c cl -> Z.of_nat (length (cl_cache cl)) <= art_ic_mc c ->
  art_cptr_ok (AsanTab.class_size c) (cl_au cl) w -> ~ In w (cl_cache cl ++ cl_free cl) ->
  (art_cls_full c cl = true -> 4 * (Z.of_nat (length (cl_free cl)) + art_ic_mc c / 2) <= cl_mfa cl) ->
  art_cls_ok c (art_cls_dealloc c w cl).
Proof.
  intros c w cl Hc OK Hlen Hw Hnin Hroom.
  destruct OK as (L16 & Hau & Hcarve & Hmu & Hauk & Hmu' & Hmfa & Hmfa' & Hfree & Hall & Hnd).
  apply NoDup_ListNoDup in Hnd.
  destruct (art_ic_mc_half c ltac:(lia)) as (Emc & Hh). pose proof (art_ic_mc_range c ltac:(lia)) as Rmc.
  unfold art_cls_dealloc. destruct (art_cls_full c cl) eqn:EF.
  - (* [comment removed for export] *)
    unfold art_cls_full in EF. apply Z.eqb_eq in EF. specialize (Hroom eq_refl).
    set (h := Z.to_nat (art_ic_mc c / 2)). set (k := (length (cl_cache cl) - h)%nat).
    assert (Hk : (k + h = length (cl_cache cl))%nat) by (unfold k, h; lia).
    assert (PERM : Permutation (w :: cl_cache cl ++ cl_free cl) ((firstn k (cl_cache cl) ++ [w]) ++ (cl_free cl ++ skipn k (cl_cache cl)))).
    { rewrite <- (firstn_skipn k (cl_cache cl)) at 1. rewrite <- !app_assoc. cbn [app].
      eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head. apply perm_skip. apply Permutation_app_comm. }
    unfold art_cls_ok, art_cls_push, art_cls_return. cbn [cl_cache cl_free cl_au cl_mu cl_mfa]. fold h k.
    split. { rewrite length_app, length_firstn. cbn [length]. lia. }
    split; [exact Hau|]. split; [exact Hcarve|]. split; [exact Hmu|]. split; [exact Hauk|]. split; [exact Hmu'|]. split; [exact Hmfa|]. split; [exact Hmfa'|].
    split. { rewrite length_app, length_skipn. unfold h in *. lia. }
    split.
    + eapply Permutation_Forall; [exact PERM|]. constructor; assumption.
    + apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact PERM|]. constructor; assumption.
  - unfold art_cls_full in EF. apply Z.eqb_neq in EF.
    assert (PERM : Permutation (w :: cl_cache cl ++ cl_free cl) ((cl_cache cl ++ [w]) ++ cl_free cl)).
    { rewrite <- app_assoc. cbn [app]. apply Permutation_middle. }
    unfold art_cls_ok, art_cls_push. cbn [cl_cache cl_free cl_au cl_mu cl_mfa].
    split. { rewrite length_app. cbn [length]. pose proof (art_ic_mc_range c ltac:(lia)). lia. }
    split; [exact Hau|]. split; [exact Hcarve|]. split; [exact Hmu|]. split; [exact Hauk|]. split; [exact Hmu'|]. split; [exact Hmfa|]. split; [exact Hmfa'|].
    split; [exact Hfree|].
    split.
    + eapply Permutation_Forall; [exact PERM|]. constructor; assumption.
    + apply NoDup_ListNoDup. eapply Permutation_NoDup; [exact PERM|]. constructor; assumption.
Qed.

(* [comment removed for export] *)
Lemma art_region_rep_ret : forall spb ris c mx mx' (cl cl' : art_cls) (M M' : word -> option byte) (W : list (Z * Z)) (ws : list Z),
  let fa := spb + c * 2 ^ 32 + 3758096384 in
  let r := ris + 128 * c in
  let nf := Z.of_nat (length (cl_free cl)) in
  0 <= r -> r + 128 < 2 ^ 64 -> 0 <= fa -> fa + 2 ^ 29 < 2 ^ 64 -> 4 * nf <= 2 ^ 29 ->
  cl_free cl' = cl_free cl ++ ws -> cl_mfa cl' = cl_mfa cl -> cl_au cl' = cl_au cl -> cl_mu cl' = cl_mu cl -> cl_na cl' = cl_na cl ->
  art_region_rep spb ris c mx cl M -> mem_grows M M' -> art_agree W M M' ->
  art_gap W (r + 24) 56 -> art_gap W fa (4 * nf) ->
  cellA M' r 8 mx' -> cellA M' (r + 16) 8 (nf + Z.of_nat (length ws)) -> cellA M' (r + 80) 8 (cl_nfr cl') ->
  (forall j, (j < length ws)%nat -> cellA M' (fa + 4 * (nf + Z.of_nat j)) 4 (nth j ws 0)) ->
  art_region_rep spb ris c mx' cl' M'.
Proof.
  intros spb ris c mx mx' cl cl' M M' W ws fa r nf Hr Hr' Hfa Hfa' Hnf Efree Emfa Eau Emu Ena RR G A G24 GFA Cmx Cnf Cnfr Cws.
  destruct RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
  fold r in Rmx, Rnf, Rmfa, Rau, Ram, Rmu, Rmm, Rna, Rnfr, Wr. fold fa in Rfa, Wfa. fold nf in Rnf.
  assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
  unfold art_region_rep. fold r fa. rewrite Emfa, Eau, Emu, Ena, Efree.
  assert (T : forall a (n : nat) v, r + 24 <= a -> a + Z.of_nat n <= r + 80 -> cellA M a n v -> cellA M' a n v).
  { intros a n v Ha Hn C. apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G24|lia|lia]|lia|lia|exact C]. }
  split; [exact Cmx|].
  split. { rewrite length_app, Nat2Z.inj_add. exact Cnf. }
  split; [apply T; [lia|cbn; lia|exact Rmfa]|]. split; [apply T; [lia|cbn; lia|exact Rau]|]. split; [apply T; [lia|cbn; lia|exact Ram]|].
  split; [apply T; [lia|cbn; lia|exact Rmu]|]. split; [apply T; [lia|cbn; lia|exact Rmm]|]. split; [apply T; [lia|cbn; lia|exact Rna]|].
  split; [exact Cnfr|].
  split. { intros j Hj. rewrite length_app in Hj. destruct (Nat.lt_ge_cases j (length (cl_free cl))) as [Lt|Ge].
           - rewrite app_nth1 by exact Lt. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'. fold nf in Hj'.
             apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact GFA|lia|cbn; lia]|lia|cbn; lia|apply Rfa; exact Lt].
           - rewrite app_nth2 by exact Ge. replace (Z.of_nat j) with (nf + Z.of_nat (j - length (cl_free cl))) by (unfold nf; lia). apply Cws. lia. }
  split; [eapply wr_grows; [exact G|exact Wr]|]. split; [eapply wr_grows; [exact G|exact Wfa]|eapply wr_grows; [exact G|exact Wu]].
Qed.

Section FPY. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_lcd_run : forall regs (M rom : word -> option byte) (raw : word) (sp HI ca c p spb ris qris w sv : Z) (cl : art_cls),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 1295832 -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 p ->
  0x696000 <= HI -> HI <= sp - 320 -> sp < 2 ^ 64 -> HI + 8388608 <= 2 ^ 47 -> 1 <= c <= 30 ->
  0x696000 <= spb -> ris = spb + 2 ^ 37 -> ris = 128 * qris -> ris + 4096 <= HI ->
  4096 <= ca -> ca + 2592 <= HI -> ca mod 8 = 0 -> (ca + 2592 <= 0x10000 \/ 0x696000 <= ca) -> apart ca 2592 spb (2 ^ 37 + 4096) ->
  wrA M (sp - 320) 320 -> wrA M ca 2592 ->
  art_prim_consts spb ris M -> art_pc_hdr ca true M -> art_cls_rep ca spb ris c cl M -> art_cls_ok c cl ->
  Z.of_nat (length (cl_cache cl)) <= art_ic_mc c ->
  p = spb + c * 2 ^ 32 + 16 * w -> 0 <= w < 2 ^ 28 ->
  cellA M (ca + 2576) 8 sv ->
  (art_cls_full c cl = true -> 4 * (Z.of_nat (length (cl_free cl)) + art_ic_mc c / 2) <= cl_mfa cl) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x54cf8 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M'
    /\ art_agree (art_lcd_fp sp ca spb ris c (Z.of_nat (length (cl_free cl)))) M M'
    /\ art_cls_rep ca spb ris c (art_cls_dealloc c w cl) M'
    /\ cellA M' (ca + 2576) 8 (sv - art_ic_size c).
Proof.
  intros regs M rom raw sp HI ca c p spb ris qris w sv cl H1 Hret H2 H10 H11 H12 H13 HHI Hsp Hsp' HHI' Hc Hspb Eris Eq Hris' Hca Hca' Hca8 Hcai Aca
    W Wca PC PH [CR RR] OK Hlen Ep Hw Csv Hroom.
  destruct PC as (Cspb & Cris & Crel & _ & Crd & Cpc & Cpg & _ & _).
  destruct (PH c ltac:(lia)) as [Cmc Ccsz].
  destruct CR as [Ccnt Cch].
  pose proof RR as (Rmx & Rnf & Rmfa & Rau & Ram & Rmu & Rmm & Rna & Rnfr & Rfa & Wr & Wfa & Wu).
  pose proof OK as (L16 & Hau & Hcarve & Hmu & Hauk & Hmu' & Hmfa & Hmfa' & Hfree & Hall & Hnd).
  destruct (art_ic_mc_half c ltac:(lia)) as (Emc & Hh). pose proof (art_ic_mc_range c ltac:(lia)) as Rmc. pose proof (art_ic_size_pos c ltac:(lia)) as Rsz.
  pose proof (art_cell_norm _ _ _ _ Csv) as Csvn. pose proof (art_mod64_range sv) as Hsvn.
  pose proof (art_cell_norm _ _ _ _ Rnfr) as Rnfrn. pose proof (art_mod64_range (cl_nfr cl)) as Hnfrn.
  set (cnt := Z.of_nat (length (cl_cache cl))) in *. set (nf := Z.of_nat (length (cl_free cl))) in *.
  set (r := ris + 128 * c) in *. set (fa := spb + c * 2 ^ 32 + 3758096384) in *.
  assert (Er : r = ris + 128 * c) by reflexivity. assert (Efa : fa = spb + c * 2 ^ 32 + 3758096384) by reflexivity.
  assert (Hcnt0 : 0 <= cnt) by (unfold cnt; lia). assert (Hnf0 : 0 <= nf) by (unfold nf; lia).
  unfold apart in Aca.
  unfold art_cls_dealloc. destruct (art_cls_full c cl) eqn:EF; unfold art_cls_full in EF; fold cnt in EF.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in EF. specialize (Hroom eq_refl).
    set (h := art_ic_mc c / 2) in *. set (hn := Z.to_nat h). set (k := (length (cl_cache cl) - hn)%nat).
    assert (Ehn : Z.of_nat hn = h) by (unfold hn; lia).
    assert (Ek : Z.of_nat k = cnt - h) by (unfold k, cnt in *; lia).
    set (ws := skipn k (cl_cache cl)).
    assert (Lws : length ws = hn) by (unfold ws; rewrite length_skipn; unfold k; unfold cnt in *; lia).
    assert (Nws : forall j, nth j ws 0 = nth (k + j) (cl_cache cl) 0) by (intros j; unfold ws; apply nth_skipn).
    rewrite EF in Ccnt.
    pose proof (art_lcd_full_a_fn regs M rom raw sp ca 1295832 c p (art_ic_mc c) H1 H2 H10 H11 H12 H13 ltac:(lia) Hsp' ltac:(eapply wr_sub; [exact W|lia|lia])
                  ltac:(lia) Hca ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ccnt Cmc) as RUN1.
    destruct (art_f48_facts M sp raw regs ltac:(lia) Hsp') as (G1 & AG1).
    destruct (art_f48_cells M sp raw regs ltac:(lia) Hsp') as (E1 & E8 & E9 & E18 & E19 & E20).
    match type of RUN1 with msteps _ _ (mkst ?R1 _ _ _) => set (Ra := R1) in * end.
    set (Xa := art_f48 M sp raw regs) in *.
    assert (W1a : wrA Xa (sp - 48 - 272) 272) by (eapply wr_grows; [exact G1|]; eapply wr_sub; [exact W|lia|lia]).
    assert (W1c : wrA Xa ca 2592) by (eapply wr_grows; [exact G1|exact Wca]).
    assert (W1r : wrA Xa r 128) by (eapply wr_grows; [exact G1|exact Wr]).
    assert (W1f : wrA Xa fa (cl_mfa cl)) by (eapply wr_grows; [exact G1|exact Wfa]).
    assert (T1 : forall a (n : nat) v, apart a (Z.of_nat n) (sp - 48) 48 -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> cellA M a n v -> cellA Xa a n v).
    { intros a n v Ap Ha Hn C. apply (art_cell_tr _ M Xa a n v AG1); [cbn [art_gap fst snd]; split; [exact Ap|exact I]|exact Ha|exact Hn|exact C]. }
    assert (Cspb1 : cellA Xa (1295832 + 32) 8 spb) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cspb]).
    assert (Cris1 : cellA Xa (1295832 + 48) 8 ris) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cris]).
    assert (Crel1 : cellA Xa (1295832 + 40) 4 0xffffffff) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Crel]).
    assert (Cpc1 : cellA Xa 0x1374a0 8 0x1cf6e0) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cpc]).
    assert (Cpg1 : cellA Xa 0x1cf6e0 8 4096) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cpg]).
    assert (Crd1 : cellA Xa 0x10420 8 0xafffff00000fffff) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Crd]).
    assert (Cmx1 : cellA Xa r 8 0) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rmx]).
    assert (Cnf1 : cellA Xa (r + 16) 8 nf) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rnf]).
    assert (Cmfa1 : cellA Xa (r + 24) 8 (cl_mfa cl)) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rmfa]).
    assert (Cnfr1 : cellA Xa (r + 80) 8 (cl_nfr cl mod 2 ^ 64)) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Rnfrn]).
    assert (Ccnt1 : cellA Xa (ca + 80 * c) 4 (art_ic_mc c)) by (apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Ccnt]).
    assert (Cmc1 : cellA Xa (ca + 80 * c + 4) 4 (2 * h)) by (rewrite <- Emc; apply T1; [unfold apart; cbn; lia|lia|cbn; lia|exact Cmc]).
    clearbody Xa.
    assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA Xa (ca + 80 * c + 16 + 4 * (art_ic_mc c - h) + 4 * Z.of_nat j) 4 (nth j ws 0)).
    { intros j Hj. rewrite Lws in Hj. rewrite (Nws j).
      assert (Lt : (k + j < length (cl_cache cl))%nat) by (unfold k; unfold cnt in *; lia).
      split.
      - assert (X : art_cptr_ok (AsanTab.class_size c) (cl_au cl) (nth (k + j) (cl_cache cl) 0)).
        { apply (proj1 (Forall_forall _ _) Hall). apply in_or_app. left. apply nth_In. exact Lt. }
        pose proof (art_class_size_facts c Hc) as (Hsz & _).
        pose proof (art_cptr_lt (AsanTab.class_size c) (cl_au cl) _ ltac:(lia) ltac:(lia) X). lia.
      - pose proof (Cch (k + j)%nat Lt) as Cj. rewrite <- EF.
        replace (ca + 80 * c + 16 + 4 * (cnt - h) + 4 * Z.of_nat j) with (ca + 80 * c + 16 + 4 * Z.of_nat (k + j)) by lia.
        pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'. fold cnt in Hj'.
        apply (art_cell_tr _ M Xa _ _ _ AG1); [zgap|lia|cbn; lia|exact Cj]. }
    destruct (art_lcdrain_run ws Ra Xa rom (0x54ea8 : bv 64)%bv (sp - 48) HI ca 1295832 c (art_ic_mc c) h spb ris qris nf (cl_mfa cl) (cl_nfr cl mod 2 ^ 64)
                ltac:(unfold Ra; gres; bveq) ltac:(unfold ret_ok; bveq) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; exact H10) ltac:(unfold Ra; gres; reflexivity)
                ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity)
                HHI ltac:(lia) ltac:(lia) HHI' ltac:(lia) ltac:(lia) Hc Hspb Eris Eq Hris' Hca Hca' Hcai ltac:(unfold apart; lia)
                ltac:(rewrite Lws; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hnfrn
                W1a W1c W1r W1f Ccnt1 Cmc1 Cspb1 Cris1 Crel1 Cpc1 Cpg1 Crd1 Cmx1 Cnf1 Cmfa1 Cnfr1 Cws1)
      as (r2 & M2 & RUN2 & B2 & BK & G2 & AG2 & Ccnt2 & Cmx2 & Cnf2 & Cnfr2 & Cfa2).
    fold r fa in AG2, Cmx2, Cnf2, Cnfr2, Cfa2.
    replace (sp - 48 - 272) with (sp - 320) in AG2 by lia.
    pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Q8. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Q9. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as Q18.
    pose proof (bv_unsigned_in_range 64 (getr regs 19)) as Q19. pose proof (bv_unsigned_in_range 64 (getr regs 20)) as Q20.
    change (bv_modulus 64) with (2 ^ 64) in Q8, Q9, Q18, Q19, Q20.
    assert (Csz2 : cellA M2 (ca + 80 * c + 8) 8 (art_ic_size c)) by ztr.
    assert (Cspb2 : cellA M2 (1295832 + 32) 8 spb) by ztr.
    assert (Csv2 : cellA M2 (ca + 2576) 8 (sv mod 2 ^ 64)) by ztr.
    assert (D1 : cellA M2 (sp - 8) 8 (U raw)) by ztr. assert (D8 : cellA M2 (sp - 16) 8 (U (getr regs 8))) by ztr. assert (D9 : cellA M2 (sp - 24) 8 (U (getr regs 9))) by ztr.
    assert (D18 : cellA M2 (sp - 32) 8 (U (getr regs 18))) by ztr. assert (D19 : cellA M2 (sp - 40) 8 (U (getr regs 19))) by ztr. assert (D20 : cellA M2 (sp - 48) 8 (U (getr regs 20))) by ztr.
    pose proof (art_lcd_full_b_fn r2 M2 rom raw sp ca 1295832 c p spb w (art_ic_mc c - h) (art_ic_size c) (sv mod 2 ^ 64)
                  (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))
                  B2 ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity) ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity) ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity)
                  ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity) ltac:(rewrite BK by inl; unfold Ra; gres; reflexivity)
                  Hret ltac:(lia) Hsp' ltac:(lia) Hca ltac:(lia) Hca8 Hcai ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ep Hw ltac:(lia) ltac:(lia) Hsvn Q8 Q9 Q18 Q19 Q20
                  ltac:(eapply wr_grows; [exact G2|exact W1c]) Ccnt2 Csz2 Cspb2 Csv2 D1 D8 D9 D18 D19 D20) as RUN3.
    match type of RUN3 with msteps _ _ (mkst ?R3 _ ?X3 _) => set (Rf := R3) in *; set (Mf := X3) in * end.
    assert (G3 : mem_grows M2 Mf) by (unfold Mf; zgrows).
    assert (AG3 : art_agree [(ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)] M2 Mf).
    { unfold Mf. eapply art_agree_sub; [zagree|]. zsub. }
    assert (Gf : mem_grows M Mf) by (eapply mem_grows_trans; [exact G1|]; eapply mem_grows_trans; [exact G2|exact G3]).
    assert (Af : art_agree [(sp - 320, 320); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8); (fa + 4 * nf, 4 * h); (r, 8); (r + 16, 8); (r + 80, 8)] M Mf).
    { eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|exact AG3]|]. zsub. }
    exists Rf, Mf.
    split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|exact RUN3]|].
    split; [unfold Rf; gres; reflexivity|].
    split. { intros x Hx. cbn [In] in Hx.
      repeat (destruct Hx as [<-|Hx]; [unfold Rf; gres; first [reflexivity | apply Z_to_bv_bv_unsigned | rewrite BK by inl; unfold Ra; gres; reflexivity]|]). destruct Hx. }
    split; [exact Gf|].
    split. { eapply art_agree_sub; [exact Af|]. unfold art_lcd_fp. fold r fa. zsub. }
    split.
    + split.
      * (* [comment removed for export] *)
        unfold art_cls_push, art_cls_return. cbn [cl_cache]. fold hn k. split.
        -- rewrite length_app, length_firstn. cbn [length].
           replace (Z.of_nat (Nat.min k (length (cl_cache cl)) + 1)) with (art_ic_mc c - h + 1) by (unfold cnt in *; lia). unfold Mf. zcell.
        -- intros j Hj. rewrite length_app, length_firstn in Hj. cbn [length] in Hj.
           destruct (Nat.lt_ge_cases j k) as [Lt|Ge].
           ++ rewrite app_nth1 by (rewrite length_firstn; unfold cnt in *; lia). rewrite nth_firstn. replace (j <? k)%nat with true by (symmetry; apply Nat.ltb_lt; exact Lt).
              assert (Ltc : (j < length (cl_cache cl))%nat) by (unfold k in Lt; lia).
              pose proof (Cch j Ltc) as Cj. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'.
              assert (Cj2 : cellA M2 (ca + 80 * c + 16 + 4 * Z.of_nat j) 4 (nth j (cl_cache cl) 0)) by ztr.
              unfold Mf. zcell.
           ++ assert (Ej : j = k) by (unfold cnt in *; lia). subst j. rewrite app_nth2 by (rewrite length_firstn; unfold cnt in *; lia).
              rewrite length_firstn. replace (k - Nat.min k (length (cl_cache cl)))%nat with O by (unfold cnt in *; lia). cbn [nth].
              replace (Z.of_nat k) with (art_ic_mc c - h) by lia. unfold Mf. zcell.
      * (* [comment removed for export] *)
        apply (art_region_rep_ret spb ris c 0 0 cl (art_cls_push w (art_cls_return hn cl)) M Mf
                 [(sp - 320, 320); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8); (fa + 4 * nf, 4 * h); (r, 8); (r + 16, 8); (r + 80, 8)] ws);
          try reflexivity; fold r fa nf; first [ lia | exact RR | exact Gf | exact Af | idtac ].
        -- zgap.
        -- zgap.
        -- unfold Mf. zcell.
        -- rewrite Lws, Ehn. unfold Mf. zcell.
        -- cbn [art_cls_push art_cls_return cl_nfr]. rewrite Ehn. apply art_cell_mod_add. unfold Mf. zcell.
        -- intros j Hj. pose proof (Cfa2 j Hj) as Cj. rewrite Lws in Hj. unfold Mf. zcell.
    + replace (sv - art_ic_size c) with (sv + (0 - art_ic_size c)) by lia. apply art_cell_mod_add. unfold Mf. zcell.
  - (* [comment removed for export] *)
    apply Z.eqb_neq in EF. clear Hroom.
    pose proof (art_lcd_push_fn regs M rom raw sp ca 1295832 c p spb w (art_ic_mc c) cnt (art_ic_size c) (sv mod 2 ^ 64) H1 Hret H2 H10 H11 H12 H13
                  ltac:(lia) Hsp' ltac:(eapply wr_sub; [exact W|lia|lia]) ltac:(lia) Hca ltac:(lia) Hca8 Hcai ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ep Hw
                  ltac:(lia) ltac:(lia) ltac:(lia) Hsvn Wca Ccnt Cmc Ccsz Cspb Csvn) as RUN.
    match type of RUN with msteps _ _ (mkst ?R _ ?X _) => set (Rf := R) in *; set (Mf := X) in * end.
    assert (G : mem_grows M Mf) by (unfold Mf, art_f48; zgrows).
    assert (A : art_agree [(sp - 48, 48); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)] M Mf).
    { unfold Mf, art_f48. eapply art_agree_sub; [zagree|]. zsub. }
    exists Rf, Mf.
    split; [exact RUN|].
    split; [unfold Rf; gres; reflexivity|].
    split. { intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [unfold Rf; gres; reflexivity|]). destruct Hx. }
    split; [exact G|].
    split. { eapply art_agree_sub; [exact A|]. unfold art_lcd_fp. zsub. }
    split.
    + split.
      * (* [comment removed for export] *)
        unfold art_cls_push. cbn [cl_cache]. split.
        -- rewrite length_app. cbn [length]. replace (Z.of_nat (length (cl_cache cl) + 1)) with (cnt + 1) by (unfold cnt; lia). unfold Mf. zcell.
        -- intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
           destruct (Nat.lt_ge_cases j (length (cl_cache cl))) as [Lt|Ge].
           ++ rewrite app_nth1 by exact Lt. pose proof (Cch j Lt) as Cj. pose proof (proj1 (Nat2Z.inj_lt _ _) Lt) as Hj'. fold cnt in Hj'.
              unfold Mf, art_f48. zcell.
           ++ assert (Ej : j = length (cl_cache cl)) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. fold cnt.
              unfold Mf. zcell.
      * (* [comment removed for export] *)
        apply (art_region_rep_ret spb ris c 0 0 cl (art_cls_push w cl) M Mf [(sp - 48, 48); (ca + 80 * c, 4); (ca + 80 * c + 16, 64); (ca + 2576, 8)] []);
          try reflexivity; fold r fa nf; first [ lia | exact RR | exact G | exact A | idtac ].
        -- cbn [art_cls_push cl_free]. symmetry. apply app_nil_r.
        -- zgap.
        -- zgap.
        -- ztr.
        -- cbn [length]. replace (nf + Z.of_nat 0) with nf by lia. ztr.
        -- cbn [art_cls_push cl_nfr]. ztr.
        -- intros j Hj. cbn [length] in Hj. lia.
    + replace (sv - art_ic_size c) with (sv + (0 - art_ic_size c)) by lia. apply art_cell_mod_add. unfold Mf. zcell.
Qed.
End FPY.
