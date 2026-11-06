(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac ArtLeaf ArtAllocG ArtPoison ArtSecAlloc ArtRuns ArtRunsMem ArtFp ArtCellEx ArtImgCell ArtSecRSpec ArtPoison3 ArtRecycle1.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0_code_3f03c_40650 As0_code_7333c_7353c As0_code_71b40_71b78 As0_code_6da44_6daac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_secd_a_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ms parr idx n last nf ca s16 s24 : Z) : word -> option byte :=
  Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 8 (Wn 4 (art_flush_frame M sp raw regs)
     (0xda518 + 616) 1) (0xda518 + 56) (n - 1)) (0xda518 + 64) 0) (0xda518 + 80) (nf + 1)) (0xda518 + 88) (ca - ms)) (parr + 8 * idx) last) (last + 24) idx)
     (0xda788 + 16) (s16 + (0 - ms))) (0xda788 + 24) (s24 + (0 - ms))) (0xda518 + 616) 0.

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

Lemma art_secd_a_fn : forall regs (M rom : word -> option byte) (raw : word) (sp HI h ms parr idx n last nf ca s16 s24 : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0xda518 -> getr regs 11 = Z_to_bv 64 0xda788 -> getr regs 12 = Z_to_bv 64 (h + 4096) ->
  0x633000 <= HI -> HI <= sp - 32 -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0x633000 <= h -> h + 4096 <= HI -> h mod 4096 = 0 -> 0x633000 <= last -> last + 32 <= HI -> apart (last + 24) 8 h 16 ->
  0x633000 <= parr -> parr + 8 * n <= HI -> apart parr (8 * n) h 4096 -> apart parr (8 * n) last 32 -> 0 <= idx < n -> n < 2 ^ 20 -> 0 <= ms < 2 ^ 64 ->
  0 <= nf < 2 ^ 64 -> 0 <= ca < 2 ^ 64 -> 0 <= s16 < 2 ^ 64 -> 0 <= s24 < 2 ^ 64 ->
  cellA M 0xda518 8 4096 -> cellA M (0xda518 + 616) 4 0 -> cellA M (0xda518 + 8) 8 parr -> cellA M (0xda518 + 56) 8 n ->
  cellA M (0xda518 + 80) 8 nf -> cellA M (0xda518 + 88) 8 ca -> cellA M (0xda788 + 16) 8 s16 -> cellA M (0xda788 + 24) 8 s24 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (h + 24) 8 idx -> cellA M (parr + 8 * idx) 8 h -> cellA M (parr + 8 * (n - 1)) 8 last ->
  wokA M (parr + 8 * idx) 8 -> wokA M (last + 24) 8 ->
  msteps ASEGS (mkst regs (0x3fc4c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x3fd40)) 2 (Z_to_bv 64 (sp - 32))) 5 (Z_to_bv 64 (ca - ms))) 6 (Z_to_bv 64 0)) 8 (Z_to_bv 64 h)) 9 (Z_to_bv 64 h)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 idx)) 14 (Z_to_bv 64 894872)) 15 (Z_to_bv 64 last)) 16 (Z_to_bv 64 (0 - ms))) 17 (Z_to_bv 64 ms)) 18 (Z_to_bv 64 ms))
       (0x60f78 : word) (art_secd_a_mem M sp raw regs ms parr idx n last nf ca s16 s24) rom).
Proof.
  intros regs M rom raw sp HI h ms parr idx n last nf ca s16 s24 H1 H2 H10 H11 H12 HHI Hsp Hsp' W Hh Hh' Hh4 Hl Hl' Alh Hparr Hparr' Aph Apl Hidx Hn Hms Hnf Hca Hs16 Hs24
    Cpg Clk Cparr Cn Cnf Cca C16 C24 Chh Chms Chidx Cslot Clast Wslot Wlast.
  pose proof (art_img_wr M 0xda518 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as Wimg.
  zstep F_3fc4c D_3fc4c.
  zsd F_3fc50 D_3fc50 (sp - 8) (U raw) ltac:(rewok W). zsd F_3fc54 D_3fc54 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_3fc58 D_3fc58 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_3fc5c D_3fc5c (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg' : cellA X 0xda518 8 4096) by zcell end.
  zld F_3fc60 D_3fc60 0xda518 Cpg'.
  zstep F_3fc64 D_3fc64.
  stepn F_3fc68 D_3fc68. rwH. rewrite art_zb_and by lia.
  replace (Z.land 4095 (h + 4096)) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; rewrite Z.add_mod, Hh4 by lia; reflexivity).
  zbft F_3fc6c D_3fc6c.
  zstep F_3fc70 D_3fc70. zstep F_3fc74 D_3fc74.
  stepn F_3fc78 D_3fc78. rwH. zclosed (0xda518 + 616).
  zstep F_3fc7c D_3fc7c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0xda518 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0xda518 + 616) 4) by zwok end.
  zcas6 F_3fc80 D_3fc80 F_3fc84 D_3fc84 F_3fc88 D_3fc88 F_3fc8c D_3fc8c F_3fc90 D_3fc90 F_3fc94 D_3fc94 (0xda518 + 616) 0 1 1 1 Clk' Wlk'.
  zbft F_3fc98 D_3fc98.
  stepn F_3fc9c D_3fc9c. rwH. zclosed 0.
  zstep F_3fca0 D_3fca0. replace (h + 4096 - 4096) with h by lia.
  zbft F_3fca4 D_3fca4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chidx' : cellA X (h + 24) 8 idx) by zcell; assert (Cparr' : cellA X (0xda518 + 8) 8 parr) by zcell;
    assert (Cslot' : cellA X (parr + 8 * idx) 8 h) by zcell; assert (Cn' : cellA X (0xda518 + 56) 8 n) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell;
    assert (Cnf' : cellA X (0xda518 + 80) 8 nf) by zcell; assert (Cca' : cellA X (0xda518 + 88) 8 ca) by zcell; assert (Clast' : cellA X (parr + 8 * (n - 1)) 8 last) by zcell end.
  zld F_3fca8 D_3fca8 (h + 24) Chidx'.
  zld F_3fcac D_3fcac (0xda518 + 8) Cparr'.
  zstep F_3fcb0 D_3fcb0. zstep F_3fcb4 D_3fcb4.
  zld F_3fcb8 D_3fcb8 (parr + 8 * idx) Cslot'.
  zbft F_3fcbc D_3fcbc.
  zld F_3fcc0 D_3fcc0 (0xda518 + 56) Cn'.
  zbft F_3fcc4 D_3fcc4.
  zstep F_3fcc8 D_3fcc8.
  zld F_3fccc D_3fccc (h + 8) Chms'.
  zstep F_3fcd0 D_3fcd0.
  zld F_3fcd4 D_3fcd4 (0xda518 + 80) Cnf'.
  zld F_3fcd8 D_3fcd8 (0xda518 + 88) Cca'.
  zstep F_3fcdc D_3fcdc.
  zld F_3fce0 D_3fce0 (parr + 8 * (n - 1)) Clast'.
  zstep F_3fce4 D_3fce4. zstep F_3fce8 D_3fce8.
  zsd F_3fcec D_3fcec (0xda518 + 56) (n - 1) ltac:(zwok').
  zsb F_3fcf0 D_3fcf0 (0xda518 + 64) 0 ltac:(zwok').
  zsd F_3fcf4 D_3fcf4 (0xda518 + 80) (nf + 1) ltac:(zwok').
  zsd F_3fcf8 D_3fcf8 (0xda518 + 88) (ca - ms) ltac:(zwok').
  zstep F_3fcfc D_3fcfc. zstep F_3fd00 D_3fd00.
  zsd F_3fd04 D_3fd04 (parr + 8 * idx) last ltac:(zwok').
  zsd F_3fd08 D_3fd08 (last + 24) idx ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (0xda788 + 16) 8 s16) by zcell; assert (W16' : wokA X (0xda788 + 16) 8) by zwok end.
  zamoadd_dc F_3fd0c D_3fd0c (0xda788 + 16) s16 (0 - ms) C16' ltac:(exact W16').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chms2 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_3fd10 D_3fd10 (h + 8) Chms2.
  zstep F_3fd14 D_3fd14. zstep F_3fd18 D_3fd18.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C24' : cellA X (0xda788 + 24) 8 s24) by zcell; assert (W24' : wokA X (0xda788 + 24) 8) by zwok end.
  zamoadd_dc F_3fd1c D_3fd1c (0xda788 + 24) s24 (0 - ms) C24' ltac:(exact W24').
  stepfence F_3fd20 D_3fd20.
  zsb F_3fd24 D_3fd24 (0xda518 + 616) 0 ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chh3 : cellA X h 8 h) by zcell; assert (Chms3 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_3fd28 D_3fd28 h Chh3.
  zld F_3fd2c D_3fd2c (h + 8) Chms3.
  zstep F_3fd30 D_3fd30. zstep F_3fd34 D_3fd34. zstep F_3fd38 D_3fd38.
  stepn F_3fd3c D_3fd3c.
  unfold art_secd_a_mem, art_flush_frame. zret.
Qed.

Definition art_secd_d_mem (M : word -> option byte) (sp : Z) (raw : word) (t ms x8 x9 x18 c88 c96 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 40) 0x3fd50) (sp - 56) 0x689bc) (t + 2800 + 88) (c88 + 1)) (t + 2800 + 96) (c96 + ms)) (sp - 8) (U raw)) (sp - 16) x8) (sp - 24) x9) (sp - 32) x18.

(* [comment removed for export] *)
Lemma art_secd_d_fn : forall regs (M rom : word -> option byte) (raw : word) (sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 h -> getr regs 18 = Z_to_bv 64 ms ->
  0x633000 <= HI -> HI <= sp - 96 -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 ->
  0x633000 <= h -> h + 4096 <= HI -> 0 < ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= c88 < 2 ^ 64 -> 0 <= c96 < 2 ^ 64 ->
  art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> tp + 8 <= HI -> tsd + 8 * key + 8 <= HI -> ctx + 160 <= HI -> apart t 4096 h 4096 -> wrA M t 4096 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (t + 2800 + 88) 8 c88 -> cellA M (t + 2800 + 96) 8 c96 ->
  msteps ASEGS (mkst regs (0x3fd4c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x733e0)) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 ms)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (c96 + ms))) 14 (Z_to_bv 64 (c88 + 1))) 17 (Z_to_bv 64 215)) 18 (Z_to_bv 64 h))
       (0x71b70 : word) (art_secd_d_mem M sp raw t ms x8 x9 x18 c88 c96) rom).
Proof.
  intros regs M rom raw sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 H2 H4 H8 H18 HHI Hsp Hsp' W Hh Hh' Hms Hx8 Hx9 Hx18 Hc88 Hc96 TSD Ht Ht' Htp Htsd Hctx Ath Wt F1 F8 F9 F18 Chh Chms C88 C96.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_3fd4c D_3fd4c.
  zcall (art_thread_stats_fn _ _ _ (0x3fd50 : word) (sp - 32) tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C96' : cellA X (t + 2800 + 96) 8 c96) by zcell; assert (C88' : cellA X (t + 2800 + 88) 8 c88) by zcell;
    assert (Chh' : cellA X h 8 h) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
  zld F_3fd50 D_3fd50 (t + 2800 + 96) C96'.
  zld F_3fd54 D_3fd54 (t + 2800 + 88) C88'.
  zld F_3fd58 D_3fd58 h Chh'.
  zld F_3fd5c D_3fd5c (h + 8) Chms'.
  zstep F_3fd60 D_3fd60. zstep F_3fd64 D_3fd64.
  zsd F_3fd68 D_3fd68 (t + 2800 + 88) (c88 + 1) ltac:(zwok').
  zsd F_3fd6c D_3fd6c (t + 2800 + 96) (c96 + ms) ltac:(zwok').
  zstep F_3fd70 D_3fd70. zstep F_3fd74 D_3fd74.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell; assert (W' : wrA X (sp - 64) 64) by zwr end.
  zld F_3fd78 D_3fd78 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_3fd7c D_3fd7c (sp - 16) G8.
  zld F_3fd80 D_3fd80 (sp - 24) G9.
  zld F_3fd84 D_3fd84 (sp - 32) G18.
  zstep F_3fd88 D_3fd88.
  stepn F_3fd8c D_3fd8c.
  zstep F_733b0 D_733b0.
  zsd F_733b4 D_733b4 (sp - 8) (U raw) ltac:(zwok'). zsd F_733b8 D_733b8 (sp - 16) x8 ltac:(zwok').
  zsd F_733bc D_733bc (sp - 24) x9 ltac:(zwok'). zsd F_733c0 D_733c0 (sp - 32) x18 ltac:(zwok').
  zbft F_733c4 D_733c4.
  zstep F_733c8 D_733c8.
  zbft F_733cc D_733cc.
  zstep F_733d0 D_733d0. zstep F_733d4 D_733d4. zstep F_733d8 D_733d8.
  stepn F_733dc D_733dc.
  zstep F_71b6c D_71b6c.
  unfold art_secd_d_mem. zret.
Qed.

(* [comment removed for export] *)
Lemma art_secd_e_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ms x8 x9 x18 : Z),
  getr regs 1 = Z_to_bv 64 0x733e0 -> getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 ms -> getr regs 10 = Z_to_bv 64 0 -> ret_ok raw ->
  0x633000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  wokA M (sp - 36) 4 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M 0xd58a8 8 0x16f668 -> cellA M (0x16f668 + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x71b74 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 10 (Z_to_bv 64 ms)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521)) 18 (Z_to_bv 64 x18))
       raw (Wn 4 M (sp - 36) 18446744072277895850) rom).
Proof.
  intros regs M rom raw sp ms x8 x9 x18 H1 H2 H8 H10 Hret Hsp Hsp' Hms Hx8 Hx9 Hx18 Wk F1 F8 F9 F18 CF C144.
  stepret F_71b74 D_71b74 (Z_to_bv 64 0x733e0 : word) ltac:(rwH; reflexivity).
  zstep F_733e0 D_733e0. zstep F_733e4 D_733e4.
  zsw F_733e8 D_733e8 (sp - 36) 18446744072277895850 ltac:(exact Wk).
  zstep F_733ec D_733ec.
  stepn F_733f0 D_733f0.
  zstep F_71b40 D_71b40. zstep F_71b44 D_71b44.
  zbtk F_71b48 D_71b48.
  zstep F_71b58 D_71b58.
  stepret F_71b5c D_71b5c (Z_to_bv 64 0x733f4 : word) ltac:(rwH; reflexivity).
  zbft F_733f4 D_733f4.
  zstep F_733f8 D_733f8.
  stepn F_733fc D_733fc.
  zstep F_6da88 D_6da88.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF' : cellA X 0xd58a8 8 0x16f668) by zcell; assert (C144' : cellA X (0x16f668 + 144) 8 0) by zcell;
     assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell end.
  zld F_6da8c D_6da8c 0xd58a8 CF'.
  zld F_6da90 D_6da90 (0x16f668 + 144) C144'.
  zbtk F_6da94 D_6da94.
  stepret F_6daa8 D_6daa8 (Z_to_bv 64 0x73400 : word) ltac:(rwH; reflexivity).
  zld F_73400 D_73400 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_73404 D_73404 (sp - 16) G8.
  zld F_73408 D_73408 (sp - 24) G9.
  zld F_7340c D_7340c (sp - 32) G18.
  zstep F_73410 D_73410.
  stepret F_73414 D_73414 raw ltac:(reflexivity).
  zret.
Qed.
End FPX.
