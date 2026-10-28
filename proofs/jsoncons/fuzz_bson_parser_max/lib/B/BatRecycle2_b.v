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
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatSecAlloc_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatCellEx_b BatImgCell_b BatSecRSpec_b BatPoison3_b BatRecycle1_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3ef18_4052c_b Ba0_code_r731ac_733ac_b Ba0_code_r719b0_719e8_b Ba0_code_r6d8b4_6d91c_b.
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
Definition art_secd_a_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ms parr idx n last nf ca s16 s24 : Z) : word -> option byte :=
  Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 8 (Wn 4 (art_flush_frame M sp raw regs)
     (0x13c618 + 616) 1) (0x13c618 + 56) (n - 1)) (0x13c618 + 64) 0) (0x13c618 + 80) (nf + 1)) (0x13c618 + 88) (ca - ms)) (parr + 8 * idx) last) (last + 24) idx)
     (0x13c888 + 16) (s16 + (0 - ms))) (0x13c888 + 24) (s24 + (0 - ms))) (0x13c618 + 616) 0.

(* [comment removed for export] *)
Ltac zamoadd_dc F D a old v CELL oktac :=
  chain_step; [reflexivity
  | eapply (art_step_amoadd_d_x0 _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word) (Z_to_bv 64 old : word));
    [ exact F | reflexivity | exact D
    | gres; rwH; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | rewrite art_u_lit by lia; reflexivity
    | exact CELL | apply bytes_le_to_Z_8
    | gres; rwH; first [reflexivity | f_equal; lia]
    | oktac ]
  | step_simpl ];
  rewrite ?art_zb_add;
  change (wbytes ?M0 (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 (old + v)))) with (Wn 8 M0 a (old + v)).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_secd_a_fn : forall regs (M rom : word -> option byte) (raw : word) (sp HI h ms parr idx n last nf ca s16 s24 : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x13c618 -> getr regs 11 = Z_to_bv 64 0x13c888 -> getr regs 12 = Z_to_bv 64 (h + 4096) ->
  0x696000 <= HI -> HI <= sp - 32 -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0x696000 <= h -> h + 4096 <= HI -> h mod 4096 = 0 -> 0x696000 <= last -> last + 32 <= HI -> apart (last + 24) 8 h 16 ->
  0x696000 <= parr -> parr + 8 * n <= HI -> apart parr (8 * n) h 4096 -> apart parr (8 * n) last 32 -> 0 <= idx < n -> n < 2 ^ 20 -> 0 <= ms < 2 ^ 64 ->
  0 <= nf < 2 ^ 64 -> 0 <= ca < 2 ^ 64 -> 0 <= s16 < 2 ^ 64 -> 0 <= s24 < 2 ^ 64 ->
  cellA M 0x13c618 8 4096 -> cellA M (0x13c618 + 616) 4 0 -> cellA M (0x13c618 + 8) 8 parr -> cellA M (0x13c618 + 56) 8 n ->
  cellA M (0x13c618 + 80) 8 nf -> cellA M (0x13c618 + 88) 8 ca -> cellA M (0x13c888 + 16) 8 s16 -> cellA M (0x13c888 + 24) 8 s24 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (h + 24) 8 idx -> cellA M (parr + 8 * idx) 8 h -> cellA M (parr + 8 * (n - 1)) 8 last ->
  wokA M (parr + 8 * idx) 8 -> wokA M (last + 24) 8 ->
  msteps ASEGS (mkst regs (0x54ec0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x54fb4)) 2 (Z_to_bv 64 (sp - 32))) 5 (Z_to_bv 64 (ca - ms))) 6 (Z_to_bv 64 0)) 8 (Z_to_bv 64 h)) 9 (Z_to_bv 64 h)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 idx)) 14 (Z_to_bv 64 1296536)) 15 (Z_to_bv 64 last)) 16 (Z_to_bv 64 (0 - ms))) 17 (Z_to_bv 64 ms)) 18 (Z_to_bv 64 ms))
       (0x7ab38 : word) (art_secd_a_mem M sp raw regs ms parr idx n last nf ca s16 s24) rom).
Proof.
  intros regs M rom raw sp HI h ms parr idx n last nf ca s16 s24 H1 H2 H10 H11 H12 HHI Hsp Hsp' W Hh Hh' Hh4 Hl Hl' Alh Hparr Hparr' Aph Apl Hidx Hn Hms Hnf Hca Hs16 Hs24
    Cpg Clk Cparr Cn Cnf Cca C16 C24 Chh Chms Chidx Cslot Clast Wslot Wlast.
  pose proof (art_img_wr M 0x13c618 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as Wimg.
  zstep F_54aa8 D_54aa8.
  zsd F_54aac D_54aac (sp - 8) (U raw) ltac:(rewok W). zsd F_54ab0 D_54ab0 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_54ab4 D_54ab4 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_54ab8 D_54ab8 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg' : cellA X 0x13c618 8 4096) by zcell end.
  zld F_54abc D_54abc 0x13c618 Cpg'.
  zstep F_54ac0 D_54ac0.
  stepn F_54ac4 D_54ac4. rwH. rewrite art_zb_and by lia.
  replace (Z.land 4095 (h + 4096)) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; rewrite Z.add_mod, Hh4 by lia; reflexivity).
  zbft F_54ac8 D_54ac8.
  zstep F_54acc D_54acc. zstep F_54ad0 D_54ad0.
  stepn F_54ad4 D_54ad4. rwH. zclosed (0x13c618 + 616).
  zstep F_54ad8 D_54ad8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x13c618 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0x13c618 + 616) 4) by zwok end.
  zcas6 F_54adc D_54adc F_54ae0 D_54ae0 F_54ae4 D_54ae4 F_54ae8 D_54ae8 F_54aec D_54aec F_54af0 D_54af0 (0x13c618 + 616) 0 1 1 1 Clk' Wlk'.
  zbft F_54af4 D_54af4.
  stepn F_54af8 D_54af8. rwH. zclosed 0.
  zstep F_54afc D_54afc. replace (h + 4096 - 4096) with h by lia.
  zbft F_54b00 D_54b00.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chidx' : cellA X (h + 24) 8 idx) by zcell; assert (Cparr' : cellA X (0x13c618 + 8) 8 parr) by zcell;
    assert (Cslot' : cellA X (parr + 8 * idx) 8 h) by zcell; assert (Cn' : cellA X (0x13c618 + 56) 8 n) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell;
    assert (Cnf' : cellA X (0x13c618 + 80) 8 nf) by zcell; assert (Cca' : cellA X (0x13c618 + 88) 8 ca) by zcell; assert (Clast' : cellA X (parr + 8 * (n - 1)) 8 last) by zcell end.
  zld F_54b04 D_54b04 (h + 24) Chidx'.
  zld F_54b08 D_54b08 (0x13c618 + 8) Cparr'.
  zstep F_54b0c D_54b0c. zstep F_54b10 D_54b10.
  zld F_54b14 D_54b14 (parr + 8 * idx) Cslot'.
  zbft F_54b18 D_54b18.
  zld F_54b1c D_54b1c (0x13c618 + 56) Cn'.
  zbft F_54b20 D_54b20.
  zstep F_54b24 D_54b24.
  zld F_54b28 D_54b28 (h + 8) Chms'.
  zstep F_54b2c D_54b2c.
  zld F_54b30 D_54b30 (0x13c618 + 80) Cnf'.
  zld F_54b34 D_54b34 (0x13c618 + 88) Cca'.
  zstep F_54b38 D_54b38.
  zld F_54b3c D_54b3c (parr + 8 * (n - 1)) Clast'.
  zstep F_54b40 D_54b40. zstep F_54b44 D_54b44.
  zsd F_54b48 D_54b48 (0x13c618 + 56) (n - 1) ltac:(zwok').
  zsb F_54b4c D_54b4c (0x13c618 + 64) 0 ltac:(zwok').
  zsd F_54b50 D_54b50 (0x13c618 + 80) (nf + 1) ltac:(zwok').
  zsd F_54b54 D_54b54 (0x13c618 + 88) (ca - ms) ltac:(zwok').
  zstep F_54b58 D_54b58. zstep F_54b5c D_54b5c.
  zsd F_54b60 D_54b60 (parr + 8 * idx) last ltac:(zwok').
  zsd F_54b64 D_54b64 (last + 24) idx ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (0x13c888 + 16) 8 s16) by zcell; assert (W16' : wokA X (0x13c888 + 16) 8) by zwok end.
  zamoadd_dc F_54b68 D_54b68 (0x13c888 + 16) s16 (0 - ms) C16' ltac:(exact W16').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chms2 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_54b6c D_54b6c (h + 8) Chms2.
  zstep F_54b70 D_54b70. zstep F_54b74 D_54b74.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C24' : cellA X (0x13c888 + 24) 8 s24) by zcell; assert (W24' : wokA X (0x13c888 + 24) 8) by zwok end.
  zamoadd_dc F_54b78 D_54b78 (0x13c888 + 24) s24 (0 - ms) C24' ltac:(exact W24').
  stepfence F_54b7c D_54b7c.
  zsb F_54b80 D_54b80 (0x13c618 + 616) 0 ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chh3 : cellA X h 8 h) by zcell; assert (Chms3 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_54b84 D_54b84 h Chh3.
  zld F_54b88 D_54b88 (h + 8) Chms3.
  zstep F_54b8c D_54b8c. zstep F_54b90 D_54b90. zstep F_54b94 D_54b94.
  stepn F_54b98 D_54b98.
  unfold art_secd_a_mem, art_flush_frame. zret.
Qed.

Definition art_secd_d_mem (M : word -> option byte) (sp : Z) (raw : word) (t ms x8 x9 x18 c88 c96 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 40) 0x54fc4) (sp - 56) 0x82abc) (t + 2800 + 88) (c88 + 1)) (t + 2800 + 96) (c96 + ms)) (sp - 8) (U raw)) (sp - 16) x8) (sp - 24) x9) (sp - 32) x18.

(* [comment removed for export] *)
#[using="Type"] Lemma art_secd_d_fn : forall regs (M rom : word -> option byte) (raw : word) (sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 h -> getr regs 18 = Z_to_bv 64 ms ->
  0x696000 <= HI -> HI <= sp - 96 -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 ->
  0x696000 <= h -> h + 4096 <= HI -> 0 < ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= c88 < 2 ^ 64 -> 0 <= c96 < 2 ^ 64 ->
  art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> tp + 8 <= HI -> tsd + 8 * key + 8 <= HI -> ctx + 160 <= HI -> apart t 4096 h 4096 -> wrA M t 4096 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (t + 2800 + 88) 8 c88 -> cellA M (t + 2800 + 96) 8 c96 ->
  msteps ASEGS (mkst regs (0x54fc0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x8d4fc)) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 ms)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (c96 + ms))) 14 (Z_to_bv 64 (c88 + 1))) 17 (Z_to_bv 64 215)) 18 (Z_to_bv 64 h))
       (0x8bc8c : word) (art_secd_d_mem M sp raw t ms x8 x9 x18 c88 c96) rom).
Proof.
  intros regs M rom raw sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 H2 H4 H8 H18 HHI Hsp Hsp' W Hh Hh' Hms Hx8 Hx9 Hx18 Hc88 Hc96 TSD Ht Ht' Htp Htsd Hctx Ath Wt F1 F8 F9 F18 Chh Chms C88 C96.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_54ba8 D_54ba8.
  zcall (art_thread_stats_fn _ _ _ (0x54fc4 : word) (sp - 32) tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C96' : cellA X (t + 2800 + 96) 8 c96) by zcell; assert (C88' : cellA X (t + 2800 + 88) 8 c88) by zcell;
    assert (Chh' : cellA X h 8 h) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
  zld F_54bac D_54bac (t + 2800 + 96) C96'.
  zld F_54bb0 D_54bb0 (t + 2800 + 88) C88'.
  zld F_54bb4 D_54bb4 h Chh'.
  zld F_54bb8 D_54bb8 (h + 8) Chms'.
  zstep F_54bbc D_54bbc. zstep F_54bc0 D_54bc0.
  zsd F_54bc4 D_54bc4 (t + 2800 + 88) (c88 + 1) ltac:(zwok').
  zsd F_54bc8 D_54bc8 (t + 2800 + 96) (c96 + ms) ltac:(zwok').
  zstep F_54bcc D_54bcc. zstep F_54bd0 D_54bd0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell; assert (W' : wrA X (sp - 64) 64) by zwr end.
  zld F_54bd4 D_54bd4 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_54bd8 D_54bd8 (sp - 16) G8.
  zld F_54bdc D_54bdc (sp - 24) G9.
  zld F_54be0 D_54be0 (sp - 32) G18.
  zstep F_54be4 D_54be4.
  stepn F_54be8 D_54be8.
  zstep F_8d0b4 D_8d0b4.
  zsd F_8d0b8 D_8d0b8 (sp - 8) (U raw) ltac:(zwok'). zsd F_8d0bc D_8d0bc (sp - 16) x8 ltac:(zwok').
  zsd F_8d0c0 D_8d0c0 (sp - 24) x9 ltac:(zwok'). zsd F_8d0c4 D_8d0c4 (sp - 32) x18 ltac:(zwok').
  zbft F_8d0c8 D_8d0c8.
  zstep F_8d0cc D_8d0cc.
  zbft F_8d0d0 D_8d0d0.
  zstep F_8d0d4 D_8d0d4. zstep F_8d0d8 D_8d0d8. zstep F_8d0dc D_8d0dc.
  stepn F_8d0e0 D_8d0e0.
  zstep F_8b870 D_8b870.
  unfold art_secd_d_mem. zret.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_secd_e_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ms x8 x9 x18 : Z),
  getr regs 1 = Z_to_bv 64 0x8d4fc -> getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 ms -> getr regs 10 = Z_to_bv 64 0 -> ret_ok raw ->
  0x696000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  wokA M (sp - 36) 4 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M 0x1374b0 8 0x1d1768 -> cellA M (0x1d1768 + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x8bc90 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 10 (Z_to_bv 64 ms)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521)) 18 (Z_to_bv 64 x18))
       raw (Wn 4 M (sp - 36) 18446744072277895850) rom).
Proof.
  intros regs M rom raw sp ms x8 x9 x18 H1 H2 H8 H10 Hret Hsp Hsp' Hms Hx8 Hx9 Hx18 Wk F1 F8 F9 F18 CF C144.
  stepret F_8b878 D_8b878 (Z_to_bv 64 0x8d4fc : word) ltac:(rwH; reflexivity).
  zstep F_8d0e4 D_8d0e4. zstep F_8d0e8 D_8d0e8.
  zsw F_8d0ec D_8d0ec (sp - 36) 18446744072277895850 ltac:(exact Wk).
  zstep F_8d0f0 D_8d0f0.
  stepn F_8d0f4 D_8d0f4.
  zstep F_8b844 D_8b844. zstep F_8b848 D_8b848.
  zbtk F_8b84c D_8b84c.
  zstep F_8b85c D_8b85c.
  stepret F_8b860 D_8b860 (Z_to_bv 64 0x8d510 : word) ltac:(rwH; reflexivity).
  zbft F_8d0f8 D_8d0f8.
  zstep F_8d0fc D_8d0fc.
  stepn F_8d100 D_8d100.
  zstep F_87770 D_87770.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF' : cellA X 0x1374b0 8 0x1d1768) by zcell; assert (C144' : cellA X (0x1d1768 + 144) 8 0) by zcell;
     assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell end.
  zld F_87774 D_87774 0x1374b0 CF'.
  zld F_87778 D_87778 (0x1d1768 + 144) C144'.
  zbtk F_8777c D_8777c.
  stepret F_87790 D_87790 (Z_to_bv 64 0x8d51c : word) ltac:(rwH; reflexivity).
  zld F_8d104 D_8d104 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_8d108 D_8d108 (sp - 16) G8.
  zld F_8d10c D_8d10c (sp - 24) G9.
  zld F_8d110 D_8d110 (sp - 32) G18.
  zstep F_8d114 D_8d114.
  stepret F_8d118 D_8d118 raw ltac:(reflexivity).
  zret.
Qed.
End FPX.
