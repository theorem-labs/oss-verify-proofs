(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac Pm8ArtLeaf Pm8ArtAllocG Pm8ArtPoison Pm8ArtSecAlloc ArtRuns ArtRunsMem Pm8ArtFp Pm8ArtCellEx Pm8ArtImgCell Pm8ArtSecRSpec Pm8ArtPoison3 Pm8ArtRecycle1.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_5b000_5c000 Pm8_code_8e000_8f000 Pm8_code_92000_93000 Pm8_code_94000_95000      .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_secd_a_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ms parr idx n last nf ca s16 s24 : Z) : word -> option byte :=
  Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 8 (Wn 4 (art_flush_frame M sp raw regs)
     (0x159398 + 616) 1) (0x159398 + 56) (n - 1)) (0x159398 + 64) 0) (0x159398 + 80) (nf + 1)) (0x159398 + 88) (ca - ms)) (parr + 8 * idx) last) (last + 24) idx)
     (0x159608 + 16) (s16 + (0 - ms))) (0x159608 + 24) (s24 + (0 - ms))) (0x159398 + 616) 0.

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

Lemma art_secd_a_fn : forall regs (M rom : word -> option byte) (raw : word) (sp HI h ms parr idx n last nf ca s16 s24 : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x159398 -> getr regs 11 = Z_to_bv 64 0x159608 -> getr regs 12 = Z_to_bv 64 (h + 4096) ->
  0x6b3000 <= HI -> HI <= sp - 32 -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0x6b3000 <= h -> h + 4096 <= HI -> h mod 4096 = 0 -> 0x6b3000 <= last -> last + 32 <= HI -> apart (last + 24) 8 h 16 ->
  0x6b3000 <= parr -> parr + 8 * n <= HI -> apart parr (8 * n) h 4096 -> apart parr (8 * n) last 32 -> 0 <= idx < n -> n < 2 ^ 20 -> 0 <= ms < 2 ^ 64 ->
  0 <= nf < 2 ^ 64 -> 0 <= ca < 2 ^ 64 -> 0 <= s16 < 2 ^ 64 -> 0 <= s24 < 2 ^ 64 ->
  cellA M 0x159398 8 4096 -> cellA M (0x159398 + 616) 4 0 -> cellA M (0x159398 + 8) 8 parr -> cellA M (0x159398 + 56) 8 n ->
  cellA M (0x159398 + 80) 8 nf -> cellA M (0x159398 + 88) 8 ca -> cellA M (0x159608 + 16) 8 s16 -> cellA M (0x159608 + 24) 8 s24 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (h + 24) 8 idx -> cellA M (parr + 8 * idx) 8 h -> cellA M (parr + 8 * (n - 1)) 8 last ->
  wokA M (parr + 8 * idx) 8 -> wokA M (last + 24) 8 ->
  msteps ASEGS (mkst regs (0x5bd38 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x5be2c)) 2 (Z_to_bv 64 (sp - 32))) 5 (Z_to_bv 64 (ca - ms))) 6 (Z_to_bv 64 0)) 8 (Z_to_bv 64 h)) 9 (Z_to_bv 64 h)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 idx)) 14 (Z_to_bv 64 1414680)) 15 (Z_to_bv 64 last)) 16 (Z_to_bv 64 (0 - ms))) 17 (Z_to_bv 64 ms)) 18 (Z_to_bv 64 ms))
       (0x81d18 : word) (art_secd_a_mem M sp raw regs ms parr idx n last nf ca s16 s24) rom).
Proof.
  intros regs M rom raw sp HI h ms parr idx n last nf ca s16 s24 H1 H2 H10 H11 H12 HHI Hsp Hsp' W Hh Hh' Hh4 Hl Hl' Alh Hparr Hparr' Aph Apl Hidx Hn Hms Hnf Hca Hs16 Hs24
    Cpg Clk Cparr Cn Cnf Cca C16 C24 Chh Chms Chidx Cslot Clast Wslot Wlast.
  pose proof (art_img_wr M 0x159398 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as Wimg.
  zstep F_5bce8 D_5bce8.
  zsd F_5bcec D_5bcec (sp - 8) (U raw) ltac:(rewok W). zsd F_5bcf0 D_5bcf0 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_5bcf4 D_5bcf4 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5bcf8 D_5bcf8 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg' : cellA X 0x159398 8 4096) by zcell end.
  zld F_5bcfc D_5bcfc 0x159398 Cpg'.
  zstep F_5bd00 D_5bd00.
  stepn F_5bd04 D_5bd04. rwH. rewrite art_zb_and by lia.
  replace (Z.land 4095 (h + 4096)) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; rewrite Z.add_mod, Hh4 by lia; reflexivity).
  zbft F_5bd08 D_5bd08.
  zstep F_5bd0c D_5bd0c. zstep F_5bd10 D_5bd10.
  stepn F_5bd14 D_5bd14. rwH. zclosed (0x159398 + 616).
  zstep F_5bd18 D_5bd18.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x159398 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0x159398 + 616) 4) by zwok end.
  zcas6 F_5bd1c D_5bd1c F_5bd20 D_5bd20 F_5bd24 D_5bd24 F_5bd28 D_5bd28 F_5bd2c D_5bd2c F_5bd30 D_5bd30 (0x159398 + 616) 0 1 1 1 Clk' Wlk'.
  zbft F_5bd34 D_5bd34.
  stepn F_5bd38 D_5bd38. rwH. zclosed 0.
  zstep F_5bd3c D_5bd3c. replace (h + 4096 - 4096) with h by lia.
  zbft F_5bd40 D_5bd40.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chidx' : cellA X (h + 24) 8 idx) by zcell; assert (Cparr' : cellA X (0x159398 + 8) 8 parr) by zcell;
    assert (Cslot' : cellA X (parr + 8 * idx) 8 h) by zcell; assert (Cn' : cellA X (0x159398 + 56) 8 n) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell;
    assert (Cnf' : cellA X (0x159398 + 80) 8 nf) by zcell; assert (Cca' : cellA X (0x159398 + 88) 8 ca) by zcell; assert (Clast' : cellA X (parr + 8 * (n - 1)) 8 last) by zcell end.
  zld F_5bd44 D_5bd44 (h + 24) Chidx'.
  zld F_5bd48 D_5bd48 (0x159398 + 8) Cparr'.
  zstep F_5bd4c D_5bd4c. zstep F_5bd50 D_5bd50.
  zld F_5bd54 D_5bd54 (parr + 8 * idx) Cslot'.
  zbft F_5bd58 D_5bd58.
  zld F_5bd5c D_5bd5c (0x159398 + 56) Cn'.
  zbft F_5bd60 D_5bd60.
  zstep F_5bd64 D_5bd64.
  zld F_5bd68 D_5bd68 (h + 8) Chms'.
  zstep F_5bd6c D_5bd6c.
  zld F_5bd70 D_5bd70 (0x159398 + 80) Cnf'.
  zld F_5bd74 D_5bd74 (0x159398 + 88) Cca'.
  zstep F_5bd78 D_5bd78.
  zld F_5bd7c D_5bd7c (parr + 8 * (n - 1)) Clast'.
  zstep F_5bd80 D_5bd80. zstep F_5bd84 D_5bd84.
  zsd F_5bd88 D_5bd88 (0x159398 + 56) (n - 1) ltac:(zwok').
  zsb F_5bd8c D_5bd8c (0x159398 + 64) 0 ltac:(zwok').
  zsd F_5bd90 D_5bd90 (0x159398 + 80) (nf + 1) ltac:(zwok').
  zsd F_5bd94 D_5bd94 (0x159398 + 88) (ca - ms) ltac:(zwok').
  zstep F_5bd98 D_5bd98. zstep F_5bd9c D_5bd9c.
  zsd F_5bda0 D_5bda0 (parr + 8 * idx) last ltac:(zwok').
  zsd F_5bda4 D_5bda4 (last + 24) idx ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (0x159608 + 16) 8 s16) by zcell; assert (W16' : wokA X (0x159608 + 16) 8) by zwok end.
  zamoadd_dc F_5bda8 D_5bda8 (0x159608 + 16) s16 (0 - ms) C16' ltac:(exact W16').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chms2 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_5bdac D_5bdac (h + 8) Chms2.
  zstep F_5bdb0 D_5bdb0. zstep F_5bdb4 D_5bdb4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C24' : cellA X (0x159608 + 24) 8 s24) by zcell; assert (W24' : wokA X (0x159608 + 24) 8) by zwok end.
  zamoadd_dc F_5bdb8 D_5bdb8 (0x159608 + 24) s24 (0 - ms) C24' ltac:(exact W24').
  stepfence F_5bdbc D_5bdbc.
  zsb F_5bdc0 D_5bdc0 (0x159398 + 616) 0 ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chh3 : cellA X h 8 h) by zcell; assert (Chms3 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_5bdc4 D_5bdc4 h Chh3.
  zld F_5bdc8 D_5bdc8 (h + 8) Chms3.
  zstep F_5bdcc D_5bdcc. zstep F_5bdd0 D_5bdd0. zstep F_5bdd4 D_5bdd4.
  stepn F_5bdd8 D_5bdd8.
  unfold art_secd_a_mem, art_flush_frame. zret.
Qed.

Definition art_secd_d_mem (M : word -> option byte) (sp : Z) (raw : word) (t ms x8 x9 x18 c88 c96 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 40) 0x5be3c) (sp - 56) 0x89c9c) (t + 2800 + 88) (c88 + 1)) (t + 2800 + 96) (c96 + ms)) (sp - 8) (U raw)) (sp - 16) x8) (sp - 24) x9) (sp - 32) x18.

Lemma art_secd_d_fn : forall regs (M rom : word -> option byte) (raw : word) (sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 h -> getr regs 18 = Z_to_bv 64 ms ->
  0x6b3000 <= HI -> HI <= sp - 96 -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 ->
  0x6b3000 <= h -> h + 4096 <= HI -> 0 < ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= c88 < 2 ^ 64 -> 0 <= c96 < 2 ^ 64 ->
  art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> tp + 8 <= HI -> tsd + 8 * key + 8 <= HI -> ctx + 160 <= HI -> apart t 4096 h 4096 -> wrA M t 4096 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (t + 2800 + 88) 8 c88 -> cellA M (t + 2800 + 96) 8 c96 ->
  msteps ASEGS (mkst regs (0x5be38 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x946dc)) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 ms)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (c96 + ms))) 14 (Z_to_bv 64 (c88 + 1))) 17 (Z_to_bv 64 215)) 18 (Z_to_bv 64 h))
       (0x92e6c : word) (art_secd_d_mem M sp raw t ms x8 x9 x18 c88 c96) rom).
Proof.
  intros regs M rom raw sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 H2 H4 H8 H18 HHI Hsp Hsp' W Hh Hh' Hms Hx8 Hx9 Hx18 Hc88 Hc96 TSD Ht Ht' Htp Htsd Hctx Ath Wt F1 F8 F9 F18 Chh Chms C88 C96.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_5bde8 D_5bde8.
  zcall (art_thread_stats_fn _ _ _ (0x5be3c : word) (sp - 32) tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C96' : cellA X (t + 2800 + 96) 8 c96) by zcell; assert (C88' : cellA X (t + 2800 + 88) 8 c88) by zcell;
    assert (Chh' : cellA X h 8 h) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
  zld F_5bdec D_5bdec (t + 2800 + 96) C96'.
  zld F_5bdf0 D_5bdf0 (t + 2800 + 88) C88'.
  zld F_5bdf4 D_5bdf4 h Chh'.
  zld F_5bdf8 D_5bdf8 (h + 8) Chms'.
  zstep F_5bdfc D_5bdfc. zstep F_5be00 D_5be00.
  zsd F_5be04 D_5be04 (t + 2800 + 88) (c88 + 1) ltac:(zwok').
  zsd F_5be08 D_5be08 (t + 2800 + 96) (c96 + ms) ltac:(zwok').
  zstep F_5be0c D_5be0c. zstep F_5be10 D_5be10.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell; assert (W' : wrA X (sp - 64) 64) by zwr end.
  zld F_5be14 D_5be14 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_5be18 D_5be18 (sp - 16) G8.
  zld F_5be1c D_5be1c (sp - 24) G9.
  zld F_5be20 D_5be20 (sp - 32) G18.
  zstep F_5be24 D_5be24.
  stepn F_5be28 D_5be28.
  zstep F_9465c D_9465c.
  zsd F_94660 D_94660 (sp - 8) (U raw) ltac:(zwok'). zsd F_94664 D_94664 (sp - 16) x8 ltac:(zwok').
  zsd F_94668 D_94668 (sp - 24) x9 ltac:(zwok'). zsd F_9466c D_9466c (sp - 32) x18 ltac:(zwok').
  zbft F_94670 D_94670.
  zstep F_94674 D_94674.
  zbft F_94678 D_94678.
  zstep F_9467c D_9467c. zstep F_94680 D_94680. zstep F_94684 D_94684.
  stepn F_94688 D_94688.
  zstep F_92e18 D_92e18.
  unfold art_secd_d_mem. zret.
Qed.

Lemma art_secd_e_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ms x8 x9 x18 : Z),
  getr regs 1 = Z_to_bv 64 0x946dc -> getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 ms -> getr regs 10 = Z_to_bv 64 0 -> ret_ok raw ->
  0x6b3000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  wokA M (sp - 36) 4 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M 0x153128 8 0x1ee4e8 -> cellA M (0x1ee4e8 + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x92e70 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 10 (Z_to_bv 64 ms)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521)) 18 (Z_to_bv 64 x18))
       raw (Wn 4 M (sp - 36) 18446744072277895850) rom).
Proof.
  intros regs M rom raw sp ms x8 x9 x18 H1 H2 H8 H10 Hret Hsp Hsp' Hms Hx8 Hx9 Hx18 Wk F1 F8 F9 F18 CF C144.
  stepret F_92e20 D_92e20 (Z_to_bv 64 0x946dc : word) ltac:(rwH; reflexivity).
  zstep F_9468c D_9468c. zstep F_94690 D_94690.
  zsw F_94694 D_94694 (sp - 36) 18446744072277895850 ltac:(exact Wk).
  zstep F_94698 D_94698.
  stepn F_9469c D_9469c.
  zstep F_92dec D_92dec. zstep F_92df0 D_92df0.
  zbtk F_92df4 D_92df4.
  zstep F_92e04 D_92e04.
  stepret F_92e08 D_92e08 (Z_to_bv 64 0x946f0 : word) ltac:(rwH; reflexivity).
  zbft F_946a0 D_946a0.
  zstep F_946a4 D_946a4.
  stepn F_946a8 D_946a8.
  zstep F_8ed18 D_8ed18.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF' : cellA X 0x153128 8 0x1ee4e8) by zcell; assert (C144' : cellA X (0x1ee4e8 + 144) 8 0) by zcell;
     assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell end.
  zld F_8ed1c D_8ed1c 0x153128 CF'.
  zld F_8ed20 D_8ed20 (0x1ee4e8 + 144) C144'.
  zbtk F_8ed24 D_8ed24.
  stepret F_8ed38 D_8ed38 (Z_to_bv 64 0x946fc : word) ltac:(rwH; reflexivity).
  zld F_946ac D_946ac (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_946b0 D_946b0 (sp - 16) G8.
  zld F_946b4 D_946b4 (sp - 24) G9.
  zld F_946b8 D_946b8 (sp - 32) G18.
  zstep F_946bc D_946bc.
  stepret F_946c0 D_946c0 raw ltac:(reflexivity).
  zret.
Qed.
End FPX.
