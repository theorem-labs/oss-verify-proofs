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
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac BrtLeaf BrtAllocG BrtPoison BrtSecAlloc ArtRuns ArtRunsMem BrtFp BrtCellEx BrtImgCell BrtSecRSpec BrtPoison3 BrtRecycle1.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_3f2bc_408d0 Bo0_code_735bc_737bc Bo0_code_71dc0_71df8 Bo0_code_6dcc4_6dd2c.
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
Definition art_secd_a_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ms parr idx n last nf ca s16 s24 : Z) : word -> option byte :=
  Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 8 (Wn 4 (art_flush_frame M sp raw regs)
     (0xdb118 + 616) 1) (0xdb118 + 56) (n - 1)) (0xdb118 + 64) 0) (0xdb118 + 80) (nf + 1)) (0xdb118 + 88) (ca - ms)) (parr + 8 * idx) last) (last + 24) idx)
     (0xdb388 + 16) (s16 + (0 - ms))) (0xdb388 + 24) (s24 + (0 - ms))) (0xdb118 + 616) 0.

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
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0xdb118 -> getr regs 11 = Z_to_bv 64 0xdb388 -> getr regs 12 = Z_to_bv 64 (h + 4096) ->
  0x634000 <= HI -> HI <= sp - 32 -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0x634000 <= h -> h + 4096 <= HI -> h mod 4096 = 0 -> 0x634000 <= last -> last + 32 <= HI -> apart (last + 24) 8 h 16 ->
  0x634000 <= parr -> parr + 8 * n <= HI -> apart parr (8 * n) h 4096 -> apart parr (8 * n) last 32 -> 0 <= idx < n -> n < 2 ^ 20 -> 0 <= ms < 2 ^ 64 ->
  0 <= nf < 2 ^ 64 -> 0 <= ca < 2 ^ 64 -> 0 <= s16 < 2 ^ 64 -> 0 <= s24 < 2 ^ 64 ->
  cellA M 0xdb118 8 4096 -> cellA M (0xdb118 + 616) 4 0 -> cellA M (0xdb118 + 8) 8 parr -> cellA M (0xdb118 + 56) 8 n ->
  cellA M (0xdb118 + 80) 8 nf -> cellA M (0xdb118 + 88) 8 ca -> cellA M (0xdb388 + 16) 8 s16 -> cellA M (0xdb388 + 24) 8 s24 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (h + 24) 8 idx -> cellA M (parr + 8 * idx) 8 h -> cellA M (parr + 8 * (n - 1)) 8 last ->
  wokA M (parr + 8 * idx) 8 -> wokA M (last + 24) 8 ->
  msteps ASEGS (mkst regs (0x3fecc : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x3ffc0)) 2 (Z_to_bv 64 (sp - 32))) 5 (Z_to_bv 64 (ca - ms))) 6 (Z_to_bv 64 0)) 8 (Z_to_bv 64 h)) 9 (Z_to_bv 64 h)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 idx)) 14 (Z_to_bv 64 897944)) 15 (Z_to_bv 64 last)) 16 (Z_to_bv 64 (0 - ms))) 17 (Z_to_bv 64 ms)) 18 (Z_to_bv 64 ms))
       (0x611f8 : word) (art_secd_a_mem M sp raw regs ms parr idx n last nf ca s16 s24) rom).
Proof.
  intros regs M rom raw sp HI h ms parr idx n last nf ca s16 s24 H1 H2 H10 H11 H12 HHI Hsp Hsp' W Hh Hh' Hh4 Hl Hl' Alh Hparr Hparr' Aph Apl Hidx Hn Hms Hnf Hca Hs16 Hs24
    Cpg Clk Cparr Cn Cnf Cca C16 C24 Chh Chms Chidx Cslot Clast Wslot Wlast.
  pose proof (art_img_wr M 0xdb118 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as Wimg.
  zstep F_3fecc D_3fecc.
  zsd F_3fed0 D_3fed0 (sp - 8) (U raw) ltac:(rewok W). zsd F_3fed4 D_3fed4 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_3fed8 D_3fed8 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_3fedc D_3fedc (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg' : cellA X 0xdb118 8 4096) by zcell end.
  zld F_3fee0 D_3fee0 0xdb118 Cpg'.
  zstep F_3fee4 D_3fee4.
  stepn F_3fee8 D_3fee8. rwH. rewrite art_zb_and by lia.
  replace (Z.land 4095 (h + 4096)) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; rewrite Z.add_mod, Hh4 by lia; reflexivity).
  zbft F_3feec D_3feec.
  zstep F_3fef0 D_3fef0. zstep F_3fef4 D_3fef4.
  stepn F_3fef8 D_3fef8. rwH. zclosed (0xdb118 + 616).
  zstep F_3fefc D_3fefc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0xdb118 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0xdb118 + 616) 4) by zwok end.
  zcas6 F_3ff00 D_3ff00 F_3ff04 D_3ff04 F_3ff08 D_3ff08 F_3ff0c D_3ff0c F_3ff10 D_3ff10 F_3ff14 D_3ff14 (0xdb118 + 616) 0 1 1 1 Clk' Wlk'.
  zbft F_3ff18 D_3ff18.
  stepn F_3ff1c D_3ff1c. rwH. zclosed 0.
  zstep F_3ff20 D_3ff20. replace (h + 4096 - 4096) with h by lia.
  zbft F_3ff24 D_3ff24.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chidx' : cellA X (h + 24) 8 idx) by zcell; assert (Cparr' : cellA X (0xdb118 + 8) 8 parr) by zcell;
    assert (Cslot' : cellA X (parr + 8 * idx) 8 h) by zcell; assert (Cn' : cellA X (0xdb118 + 56) 8 n) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell;
    assert (Cnf' : cellA X (0xdb118 + 80) 8 nf) by zcell; assert (Cca' : cellA X (0xdb118 + 88) 8 ca) by zcell; assert (Clast' : cellA X (parr + 8 * (n - 1)) 8 last) by zcell end.
  zld F_3ff28 D_3ff28 (h + 24) Chidx'.
  zld F_3ff2c D_3ff2c (0xdb118 + 8) Cparr'.
  zstep F_3ff30 D_3ff30. zstep F_3ff34 D_3ff34.
  zld F_3ff38 D_3ff38 (parr + 8 * idx) Cslot'.
  zbft F_3ff3c D_3ff3c.
  zld F_3ff40 D_3ff40 (0xdb118 + 56) Cn'.
  zbft F_3ff44 D_3ff44.
  zstep F_3ff48 D_3ff48.
  zld F_3ff4c D_3ff4c (h + 8) Chms'.
  zstep F_3ff50 D_3ff50.
  zld F_3ff54 D_3ff54 (0xdb118 + 80) Cnf'.
  zld F_3ff58 D_3ff58 (0xdb118 + 88) Cca'.
  zstep F_3ff5c D_3ff5c.
  zld F_3ff60 D_3ff60 (parr + 8 * (n - 1)) Clast'.
  zstep F_3ff64 D_3ff64. zstep F_3ff68 D_3ff68.
  zsd F_3ff6c D_3ff6c (0xdb118 + 56) (n - 1) ltac:(zwok').
  zsb F_3ff70 D_3ff70 (0xdb118 + 64) 0 ltac:(zwok').
  zsd F_3ff74 D_3ff74 (0xdb118 + 80) (nf + 1) ltac:(zwok').
  zsd F_3ff78 D_3ff78 (0xdb118 + 88) (ca - ms) ltac:(zwok').
  zstep F_3ff7c D_3ff7c. zstep F_3ff80 D_3ff80.
  zsd F_3ff84 D_3ff84 (parr + 8 * idx) last ltac:(zwok').
  zsd F_3ff88 D_3ff88 (last + 24) idx ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (0xdb388 + 16) 8 s16) by zcell; assert (W16' : wokA X (0xdb388 + 16) 8) by zwok end.
  zamoadd_dc F_3ff8c D_3ff8c (0xdb388 + 16) s16 (0 - ms) C16' ltac:(exact W16').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chms2 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_3ff90 D_3ff90 (h + 8) Chms2.
  zstep F_3ff94 D_3ff94. zstep F_3ff98 D_3ff98.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C24' : cellA X (0xdb388 + 24) 8 s24) by zcell; assert (W24' : wokA X (0xdb388 + 24) 8) by zwok end.
  zamoadd_dc F_3ff9c D_3ff9c (0xdb388 + 24) s24 (0 - ms) C24' ltac:(exact W24').
  stepfence F_3ffa0 D_3ffa0.
  zsb F_3ffa4 D_3ffa4 (0xdb118 + 616) 0 ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chh3 : cellA X h 8 h) by zcell; assert (Chms3 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_3ffa8 D_3ffa8 h Chh3.
  zld F_3ffac D_3ffac (h + 8) Chms3.
  zstep F_3ffb0 D_3ffb0. zstep F_3ffb4 D_3ffb4. zstep F_3ffb8 D_3ffb8.
  stepn F_3ffbc D_3ffbc.
  unfold art_secd_a_mem, art_flush_frame. zret.
Qed.

Definition art_secd_d_mem (M : word -> option byte) (sp : Z) (raw : word) (t ms x8 x9 x18 c88 c96 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 40) 0x3ffd0) (sp - 56) 0x68c3c) (t + 2800 + 88) (c88 + 1)) (t + 2800 + 96) (c96 + ms)) (sp - 8) (U raw)) (sp - 16) x8) (sp - 24) x9) (sp - 32) x18.

(* [comment removed for export] *)
Lemma art_secd_d_fn : forall regs (M rom : word -> option byte) (raw : word) (sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 h -> getr regs 18 = Z_to_bv 64 ms ->
  0x634000 <= HI -> HI <= sp - 96 -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 ->
  0x634000 <= h -> h + 4096 <= HI -> 0 < ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= c88 < 2 ^ 64 -> 0 <= c96 < 2 ^ 64 ->
  art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> tp + 8 <= HI -> tsd + 8 * key + 8 <= HI -> ctx + 160 <= HI -> apart t 4096 h 4096 -> wrA M t 4096 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (t + 2800 + 88) 8 c88 -> cellA M (t + 2800 + 96) 8 c96 ->
  msteps ASEGS (mkst regs (0x3ffcc : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x73660)) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 ms)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (c96 + ms))) 14 (Z_to_bv 64 (c88 + 1))) 17 (Z_to_bv 64 215)) 18 (Z_to_bv 64 h))
       (0x71df0 : word) (art_secd_d_mem M sp raw t ms x8 x9 x18 c88 c96) rom).
Proof.
  intros regs M rom raw sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 H2 H4 H8 H18 HHI Hsp Hsp' W Hh Hh' Hms Hx8 Hx9 Hx18 Hc88 Hc96 TSD Ht Ht' Htp Htsd Hctx Ath Wt F1 F8 F9 F18 Chh Chms C88 C96.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_3ffcc D_3ffcc.
  zcall (art_thread_stats_fn _ _ _ (0x3ffd0 : word) (sp - 32) tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C96' : cellA X (t + 2800 + 96) 8 c96) by zcell; assert (C88' : cellA X (t + 2800 + 88) 8 c88) by zcell;
    assert (Chh' : cellA X h 8 h) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
  zld F_3ffd0 D_3ffd0 (t + 2800 + 96) C96'.
  zld F_3ffd4 D_3ffd4 (t + 2800 + 88) C88'.
  zld F_3ffd8 D_3ffd8 h Chh'.
  zld F_3ffdc D_3ffdc (h + 8) Chms'.
  zstep F_3ffe0 D_3ffe0. zstep F_3ffe4 D_3ffe4.
  zsd F_3ffe8 D_3ffe8 (t + 2800 + 88) (c88 + 1) ltac:(zwok').
  zsd F_3ffec D_3ffec (t + 2800 + 96) (c96 + ms) ltac:(zwok').
  zstep F_3fff0 D_3fff0. zstep F_3fff4 D_3fff4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell; assert (W' : wrA X (sp - 64) 64) by zwr end.
  zld F_3fff8 D_3fff8 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_3fffc D_3fffc (sp - 16) G8.
  zld F_40000 D_40000 (sp - 24) G9.
  zld F_40004 D_40004 (sp - 32) G18.
  zstep F_40008 D_40008.
  stepn F_4000c D_4000c.
  zstep F_73630 D_73630.
  zsd F_73634 D_73634 (sp - 8) (U raw) ltac:(zwok'). zsd F_73638 D_73638 (sp - 16) x8 ltac:(zwok').
  zsd F_7363c D_7363c (sp - 24) x9 ltac:(zwok'). zsd F_73640 D_73640 (sp - 32) x18 ltac:(zwok').
  zbft F_73644 D_73644.
  zstep F_73648 D_73648.
  zbft F_7364c D_7364c.
  zstep F_73650 D_73650. zstep F_73654 D_73654. zstep F_73658 D_73658.
  stepn F_7365c D_7365c.
  zstep F_71dec D_71dec.
  unfold art_secd_d_mem. zret.
Qed.

(* [comment removed for export] *)
Lemma art_secd_e_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ms x8 x9 x18 : Z),
  getr regs 1 = Z_to_bv 64 0x73660 -> getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 ms -> getr regs 10 = Z_to_bv 64 0 -> ret_ok raw ->
  0x634000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  wokA M (sp - 36) 4 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M 0xd64b8 8 0x170268 -> cellA M (0x170268 + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x71df4 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 10 (Z_to_bv 64 ms)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521)) 18 (Z_to_bv 64 x18))
       raw (Wn 4 M (sp - 36) 18446744072277895850) rom).
Proof.
  intros regs M rom raw sp ms x8 x9 x18 H1 H2 H8 H10 Hret Hsp Hsp' Hms Hx8 Hx9 Hx18 Wk F1 F8 F9 F18 CF C144.
  stepret F_71df4 D_71df4 (Z_to_bv 64 0x73660 : word) ltac:(rwH; reflexivity).
  zstep F_73660 D_73660. zstep F_73664 D_73664.
  zsw F_73668 D_73668 (sp - 36) 18446744072277895850 ltac:(exact Wk).
  zstep F_7366c D_7366c.
  stepn F_73670 D_73670.
  zstep F_71dc0 D_71dc0. zstep F_71dc4 D_71dc4.
  zbtk F_71dc8 D_71dc8.
  zstep F_71dd8 D_71dd8.
  stepret F_71ddc D_71ddc (Z_to_bv 64 0x73674 : word) ltac:(rwH; reflexivity).
  zbft F_73674 D_73674.
  zstep F_73678 D_73678.
  stepn F_7367c D_7367c.
  zstep F_6dd08 D_6dd08.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF' : cellA X 0xd64b8 8 0x170268) by zcell; assert (C144' : cellA X (0x170268 + 144) 8 0) by zcell;
     assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell end.
  zld F_6dd0c D_6dd0c 0xd64b8 CF'.
  zld F_6dd10 D_6dd10 (0x170268 + 144) C144'.
  zbtk F_6dd14 D_6dd14.
  stepret F_6dd28 D_6dd28 (Z_to_bv 64 0x73680 : word) ltac:(rwH; reflexivity).
  zld F_73680 D_73680 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_73684 D_73684 (sp - 16) G8.
  zld F_73688 D_73688 (sp - 24) G9.
  zld F_7368c D_7368c (sp - 32) G18.
  zstep F_73690 D_73690.
  stepret F_73694 D_73694 raw ltac:(reflexivity).
  zret.
Qed.
End FPX.
