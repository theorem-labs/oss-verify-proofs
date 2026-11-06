(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EbtLeaf EbtAllocG EbtPoison EbtSecAlloc ArtRuns ArtRunsMem EbtFp EbtCellEx EbtImgCell EbtSecRSpec EbtPoison3 EbtRecycle1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3ef18_4052c Eb0_code_r731ac_733ac Eb0_code_r719b0_719e8 Eb0_code_r6d8b4_6d91c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_secd_a_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ms parr idx n last nf ca s16 s24 : Z) : word -> option byte :=
  Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 8 (Wn 4 (art_flush_frame M sp raw regs)
     (0x142ad8 + 616) 1) (0x142ad8 + 56) (n - 1)) (0x142ad8 + 64) 0) (0x142ad8 + 80) (nf + 1)) (0x142ad8 + 88) (ca - ms)) (parr + 8 * idx) last) (last + 24) idx)
     (0x142d48 + 16) (s16 + (0 - ms))) (0x142d48 + 24) (s24 + (0 - ms))) (0x142ad8 + 616) 0.

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
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x142ad8 -> getr regs 11 = Z_to_bv 64 0x142d48 -> getr regs 12 = Z_to_bv 64 (h + 4096) ->
  0x69c000 <= HI -> HI <= sp - 32 -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0x69c000 <= h -> h + 4096 <= HI -> h mod 4096 = 0 -> 0x69c000 <= last -> last + 32 <= HI -> apart (last + 24) 8 h 16 ->
  0x69c000 <= parr -> parr + 8 * n <= HI -> apart parr (8 * n) h 4096 -> apart parr (8 * n) last 32 -> 0 <= idx < n -> n < 2 ^ 20 -> 0 <= ms < 2 ^ 64 ->
  0 <= nf < 2 ^ 64 -> 0 <= ca < 2 ^ 64 -> 0 <= s16 < 2 ^ 64 -> 0 <= s24 < 2 ^ 64 ->
  cellA M 0x142ad8 8 4096 -> cellA M (0x142ad8 + 616) 4 0 -> cellA M (0x142ad8 + 8) 8 parr -> cellA M (0x142ad8 + 56) 8 n ->
  cellA M (0x142ad8 + 80) 8 nf -> cellA M (0x142ad8 + 88) 8 ca -> cellA M (0x142d48 + 16) 8 s16 -> cellA M (0x142d48 + 24) 8 s24 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (h + 24) 8 idx -> cellA M (parr + 8 * idx) 8 h -> cellA M (parr + 8 * (n - 1)) 8 last ->
  wokA M (parr + 8 * idx) 8 -> wokA M (last + 24) 8 ->
  msteps ASEGS (mkst regs (0x55ed0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x55fc4)) 2 (Z_to_bv 64 (sp - 32))) 5 (Z_to_bv 64 (ca - ms))) 6 (Z_to_bv 64 0)) 8 (Z_to_bv 64 h)) 9 (Z_to_bv 64 h)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 idx)) 14 (Z_to_bv 64 1322328)) 15 (Z_to_bv 64 last)) 16 (Z_to_bv 64 (0 - ms))) 17 (Z_to_bv 64 ms)) 18 (Z_to_bv 64 ms))
       (0x7bce4 : word) (art_secd_a_mem M sp raw regs ms parr idx n last nf ca s16 s24) rom).
Proof.
  intros regs M rom raw sp HI h ms parr idx n last nf ca s16 s24 H1 H2 H10 H11 H12 HHI Hsp Hsp' W Hh Hh' Hh4 Hl Hl' Alh Hparr Hparr' Aph Apl Hidx Hn Hms Hnf Hca Hs16 Hs24
    Cpg Clk Cparr Cn Cnf Cca C16 C24 Chh Chms Chidx Cslot Clast Wslot Wlast.
  pose proof (art_img_wr M 0x142ad8 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as Wimg.
  zstep F_55e80 D_55e80.
  zsd F_55e84 D_55e84 (sp - 8) (U raw) ltac:(rewok W). zsd F_55e88 D_55e88 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_55e8c D_55e8c (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_55e90 D_55e90 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg' : cellA X 0x142ad8 8 4096) by zcell end.
  zld F_55e94 D_55e94 0x142ad8 Cpg'.
  zstep F_55e98 D_55e98.
  stepn F_55e9c D_55e9c. rwH. rewrite art_zb_and by lia.
  replace (Z.land 4095 (h + 4096)) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; rewrite Z.add_mod, Hh4 by lia; reflexivity).
  zbft F_55ea0 D_55ea0.
  zstep F_55ea4 D_55ea4. zstep F_55ea8 D_55ea8.
  stepn F_55eac D_55eac. rwH. zclosed (0x142ad8 + 616).
  zstep F_55eb0 D_55eb0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x142ad8 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0x142ad8 + 616) 4) by zwok end.
  zcas6 F_55eb4 D_55eb4 F_55eb8 D_55eb8 F_55ebc D_55ebc F_55ec0 D_55ec0 F_55ec4 D_55ec4 F_55ec8 D_55ec8 (0x142ad8 + 616) 0 1 1 1 Clk' Wlk'.
  zbft F_55ecc D_55ecc.
  stepn F_55ed0 D_55ed0. rwH. zclosed 0.
  zstep F_55ed4 D_55ed4. replace (h + 4096 - 4096) with h by lia.
  zbft F_55ed8 D_55ed8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chidx' : cellA X (h + 24) 8 idx) by zcell; assert (Cparr' : cellA X (0x142ad8 + 8) 8 parr) by zcell;
    assert (Cslot' : cellA X (parr + 8 * idx) 8 h) by zcell; assert (Cn' : cellA X (0x142ad8 + 56) 8 n) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell;
    assert (Cnf' : cellA X (0x142ad8 + 80) 8 nf) by zcell; assert (Cca' : cellA X (0x142ad8 + 88) 8 ca) by zcell; assert (Clast' : cellA X (parr + 8 * (n - 1)) 8 last) by zcell end.
  zld F_55edc D_55edc (h + 24) Chidx'.
  zld F_55ee0 D_55ee0 (0x142ad8 + 8) Cparr'.
  zstep F_55ee4 D_55ee4. zstep F_55ee8 D_55ee8.
  zld F_55eec D_55eec (parr + 8 * idx) Cslot'.
  zbft F_55ef0 D_55ef0.
  zld F_55ef4 D_55ef4 (0x142ad8 + 56) Cn'.
  zbft F_55ef8 D_55ef8.
  zstep F_55efc D_55efc.
  zld F_55f00 D_55f00 (h + 8) Chms'.
  zstep F_55f04 D_55f04.
  zld F_55f08 D_55f08 (0x142ad8 + 80) Cnf'.
  zld F_55f0c D_55f0c (0x142ad8 + 88) Cca'.
  zstep F_55f10 D_55f10.
  zld F_55f14 D_55f14 (parr + 8 * (n - 1)) Clast'.
  zstep F_55f18 D_55f18. zstep F_55f1c D_55f1c.
  zsd F_55f20 D_55f20 (0x142ad8 + 56) (n - 1) ltac:(zwok').
  zsb F_55f24 D_55f24 (0x142ad8 + 64) 0 ltac:(zwok').
  zsd F_55f28 D_55f28 (0x142ad8 + 80) (nf + 1) ltac:(zwok').
  zsd F_55f2c D_55f2c (0x142ad8 + 88) (ca - ms) ltac:(zwok').
  zstep F_55f30 D_55f30. zstep F_55f34 D_55f34.
  zsd F_55f38 D_55f38 (parr + 8 * idx) last ltac:(zwok').
  zsd F_55f3c D_55f3c (last + 24) idx ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (0x142d48 + 16) 8 s16) by zcell; assert (W16' : wokA X (0x142d48 + 16) 8) by zwok end.
  zamoadd_dc F_55f40 D_55f40 (0x142d48 + 16) s16 (0 - ms) C16' ltac:(exact W16').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chms2 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_55f44 D_55f44 (h + 8) Chms2.
  zstep F_55f48 D_55f48. zstep F_55f4c D_55f4c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C24' : cellA X (0x142d48 + 24) 8 s24) by zcell; assert (W24' : wokA X (0x142d48 + 24) 8) by zwok end.
  zamoadd_dc F_55f50 D_55f50 (0x142d48 + 24) s24 (0 - ms) C24' ltac:(exact W24').
  stepfence F_55f54 D_55f54.
  zsb F_55f58 D_55f58 (0x142ad8 + 616) 0 ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chh3 : cellA X h 8 h) by zcell; assert (Chms3 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_55f5c D_55f5c h Chh3.
  zld F_55f60 D_55f60 (h + 8) Chms3.
  zstep F_55f64 D_55f64. zstep F_55f68 D_55f68. zstep F_55f6c D_55f6c.
  stepn F_55f70 D_55f70.
  unfold art_secd_a_mem, art_flush_frame. zret.
Qed.

Definition art_secd_d_mem (M : word -> option byte) (sp : Z) (raw : word) (t ms x8 x9 x18 c88 c96 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 40) 0x55fd4) (sp - 56) 0x83c68) (t + 2800 + 88) (c88 + 1)) (t + 2800 + 96) (c96 + ms)) (sp - 8) (U raw)) (sp - 16) x8) (sp - 24) x9) (sp - 32) x18.

#[using="Type"] Lemma art_secd_d_fn : forall regs (M rom : word -> option byte) (raw : word) (sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 h -> getr regs 18 = Z_to_bv 64 ms ->
  0x69c000 <= HI -> HI <= sp - 96 -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 ->
  0x69c000 <= h -> h + 4096 <= HI -> 0 < ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= c88 < 2 ^ 64 -> 0 <= c96 < 2 ^ 64 ->
  art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> tp + 8 <= HI -> tsd + 8 * key + 8 <= HI -> ctx + 160 <= HI -> apart t 4096 h 4096 -> wrA M t 4096 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (t + 2800 + 88) 8 c88 -> cellA M (t + 2800 + 96) 8 c96 ->
  msteps ASEGS (mkst regs (0x55fd0 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x8e6a8)) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 ms)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (c96 + ms))) 14 (Z_to_bv 64 (c88 + 1))) 17 (Z_to_bv 64 215)) 18 (Z_to_bv 64 h))
       (0x8ce38 : word) (art_secd_d_mem M sp raw t ms x8 x9 x18 c88 c96) rom).
Proof.
  intros regs M rom raw sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 H2 H4 H8 H18 HHI Hsp Hsp' W Hh Hh' Hms Hx8 Hx9 Hx18 Hc88 Hc96 TSD Ht Ht' Htp Htsd Hctx Ath Wt F1 F8 F9 F18 Chh Chms C88 C96.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_55f80 D_55f80.
  zcall (art_thread_stats_fn _ _ _ (0x55fd4 : word) (sp - 32) tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C96' : cellA X (t + 2800 + 96) 8 c96) by zcell; assert (C88' : cellA X (t + 2800 + 88) 8 c88) by zcell;
    assert (Chh' : cellA X h 8 h) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
  zld F_55f84 D_55f84 (t + 2800 + 96) C96'.
  zld F_55f88 D_55f88 (t + 2800 + 88) C88'.
  zld F_55f8c D_55f8c h Chh'.
  zld F_55f90 D_55f90 (h + 8) Chms'.
  zstep F_55f94 D_55f94. zstep F_55f98 D_55f98.
  zsd F_55f9c D_55f9c (t + 2800 + 88) (c88 + 1) ltac:(zwok').
  zsd F_55fa0 D_55fa0 (t + 2800 + 96) (c96 + ms) ltac:(zwok').
  zstep F_55fa4 D_55fa4. zstep F_55fa8 D_55fa8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell; assert (W' : wrA X (sp - 64) 64) by zwr end.
  zld F_55fac D_55fac (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_55fb0 D_55fb0 (sp - 16) G8.
  zld F_55fb4 D_55fb4 (sp - 24) G9.
  zld F_55fb8 D_55fb8 (sp - 32) G18.
  zstep F_55fbc D_55fbc.
  stepn F_55fc0 D_55fc0.
  zstep F_8e628 D_8e628.
  zsd F_8e62c D_8e62c (sp - 8) (U raw) ltac:(zwok'). zsd F_8e630 D_8e630 (sp - 16) x8 ltac:(zwok').
  zsd F_8e634 D_8e634 (sp - 24) x9 ltac:(zwok'). zsd F_8e638 D_8e638 (sp - 32) x18 ltac:(zwok').
  zbft F_8e63c D_8e63c.
  zstep F_8e640 D_8e640.
  zbft F_8e644 D_8e644.
  zstep F_8e648 D_8e648. zstep F_8e64c D_8e64c. zstep F_8e650 D_8e650.
  stepn F_8e654 D_8e654.
  zstep F_8cde4 D_8cde4.
  unfold art_secd_d_mem. zret.
Qed.

#[using="Type"] Lemma art_secd_e_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ms x8 x9 x18 : Z),
  getr regs 1 = Z_to_bv 64 0x8e6a8 -> getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 ms -> getr regs 10 = Z_to_bv 64 0 -> ret_ok raw ->
  0x69c000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  wokA M (sp - 36) 4 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M 0x13d8b8 8 0x1d7c28 -> cellA M (0x1d7c28 + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x8ce3c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 10 (Z_to_bv 64 ms)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521)) 18 (Z_to_bv 64 x18))
       raw (Wn 4 M (sp - 36) 18446744072277895850) rom).
Proof.
  intros regs M rom raw sp ms x8 x9 x18 H1 H2 H8 H10 Hret Hsp Hsp' Hms Hx8 Hx9 Hx18 Wk F1 F8 F9 F18 CF C144.
  stepret F_8cdec D_8cdec (Z_to_bv 64 0x8e6a8 : word) ltac:(rwH; reflexivity).
  zstep F_8e658 D_8e658. zstep F_8e65c D_8e65c.
  zsw F_8e660 D_8e660 (sp - 36) 18446744072277895850 ltac:(exact Wk).
  zstep F_8e664 D_8e664.
  stepn F_8e668 D_8e668.
  zstep F_8cdb8 D_8cdb8. zstep F_8cdbc D_8cdbc.
  zbtk F_8cdc0 D_8cdc0.
  zstep F_8cdd0 D_8cdd0.
  stepret F_8cdd4 D_8cdd4 (Z_to_bv 64 0x8e6bc : word) ltac:(rwH; reflexivity).
  zbft F_8e66c D_8e66c.
  zstep F_8e670 D_8e670.
  stepn F_8e674 D_8e674.
  zstep F_88ce4 D_88ce4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF' : cellA X 0x13d8b8 8 0x1d7c28) by zcell; assert (C144' : cellA X (0x1d7c28 + 144) 8 0) by zcell;
     assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell end.
  zld F_88ce8 D_88ce8 0x13d8b8 CF'.
  zld F_88cec D_88cec (0x1d7c28 + 144) C144'.
  zbtk F_88cf0 D_88cf0.
  stepret F_88d04 D_88d04 (Z_to_bv 64 0x8e6c8 : word) ltac:(rwH; reflexivity).
  zld F_8e678 D_8e678 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_8e67c D_8e67c (sp - 16) G8.
  zld F_8e680 D_8e680 (sp - 24) G9.
  zld F_8e684 D_8e684 (sp - 32) G18.
  zstep F_8e688 D_8e688.
  stepret F_8e68c D_8e68c raw ltac:(reflexivity).
  zret.
Qed.
End FPX.
