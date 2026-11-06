(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac Pm9ArtLeaf Pm9ArtAllocG Pm9ArtPoison Pm9ArtSecAlloc ArtRuns ArtRunsMem Pm9ArtFp Pm9ArtCellEx Pm9ArtImgCell Pm9ArtSecRSpec Pm9ArtPoison3 Pm9ArtRecycle1.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_5c000_5d000 Pm9_code_8f000_90000 Pm9_code_93000_94000 Pm9_code_94000_95000         .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_secd_a_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ms parr idx n last nf ca s16 s24 : Z) : word -> option byte :=
  Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 8 (Wn 4 (art_flush_frame M sp raw regs)
     (0x15a6d8 + 616) 1) (0x15a6d8 + 56) (n - 1)) (0x15a6d8 + 64) 0) (0x15a6d8 + 80) (nf + 1)) (0x15a6d8 + 88) (ca - ms)) (parr + 8 * idx) last) (last + 24) idx)
     (0x15a948 + 16) (s16 + (0 - ms))) (0x15a948 + 24) (s24 + (0 - ms))) (0x15a6d8 + 616) 0.

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
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x15a6d8 -> getr regs 11 = Z_to_bv 64 0x15a948 -> getr regs 12 = Z_to_bv 64 (h + 4096) ->
  0x6b4000 <= HI -> HI <= sp - 32 -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0x6b4000 <= h -> h + 4096 <= HI -> h mod 4096 = 0 -> 0x6b4000 <= last -> last + 32 <= HI -> apart (last + 24) 8 h 16 ->
  0x6b4000 <= parr -> parr + 8 * n <= HI -> apart parr (8 * n) h 4096 -> apart parr (8 * n) last 32 -> 0 <= idx < n -> n < 2 ^ 20 -> 0 <= ms < 2 ^ 64 ->
  0 <= nf < 2 ^ 64 -> 0 <= ca < 2 ^ 64 -> 0 <= s16 < 2 ^ 64 -> 0 <= s24 < 2 ^ 64 ->
  cellA M 0x15a6d8 8 4096 -> cellA M (0x15a6d8 + 616) 4 0 -> cellA M (0x15a6d8 + 8) 8 parr -> cellA M (0x15a6d8 + 56) 8 n ->
  cellA M (0x15a6d8 + 80) 8 nf -> cellA M (0x15a6d8 + 88) 8 ca -> cellA M (0x15a948 + 16) 8 s16 -> cellA M (0x15a948 + 24) 8 s24 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (h + 24) 8 idx -> cellA M (parr + 8 * idx) 8 h -> cellA M (parr + 8 * (n - 1)) 8 last ->
  wokA M (parr + 8 * idx) 8 -> wokA M (last + 24) 8 ->
  msteps ASEGS (mkst regs (0x5c0f8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x5c1ec)) 2 (Z_to_bv 64 (sp - 32))) 5 (Z_to_bv 64 (ca - ms))) 6 (Z_to_bv 64 0)) 8 (Z_to_bv 64 h)) 9 (Z_to_bv 64 h)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 idx)) 14 (Z_to_bv 64 1419608)) 15 (Z_to_bv 64 last)) 16 (Z_to_bv 64 (0 - ms))) 17 (Z_to_bv 64 ms)) 18 (Z_to_bv 64 ms))
       (0x820d8 : word) (art_secd_a_mem M sp raw regs ms parr idx n last nf ca s16 s24) rom).
Proof.
  intros regs M rom raw sp HI h ms parr idx n last nf ca s16 s24 H1 H2 H10 H11 H12 HHI Hsp Hsp' W Hh Hh' Hh4 Hl Hl' Alh Hparr Hparr' Aph Apl Hidx Hn Hms Hnf Hca Hs16 Hs24
    Cpg Clk Cparr Cn Cnf Cca C16 C24 Chh Chms Chidx Cslot Clast Wslot Wlast.
  pose proof (art_img_wr M 0x15a6d8 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as Wimg.
  zstep F_5c0b0 D_5c0b0.
  zsd F_5c0b4 D_5c0b4 (sp - 8) (U raw) ltac:(rewok W). zsd F_5c0b8 D_5c0b8 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_5c0bc D_5c0bc (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_5c0c0 D_5c0c0 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg' : cellA X 0x15a6d8 8 4096) by zcell end.
  zld F_5c0c4 D_5c0c4 0x15a6d8 Cpg'.
  zstep F_5c0c8 D_5c0c8.
  stepn F_5c0cc D_5c0cc. rwH. rewrite art_zb_and by lia.
  replace (Z.land 4095 (h + 4096)) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; rewrite Z.add_mod, Hh4 by lia; reflexivity).
  zbft F_5c0d0 D_5c0d0.
  zstep F_5c0d4 D_5c0d4. zstep F_5c0d8 D_5c0d8.
  stepn F_5c0dc D_5c0dc. rwH. zclosed (0x15a6d8 + 616).
  zstep F_5c0e0 D_5c0e0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x15a6d8 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0x15a6d8 + 616) 4) by zwok end.
  zcas6 F_5c0e4 D_5c0e4 F_5c0e8 D_5c0e8 F_5c0ec D_5c0ec F_5c0f0 D_5c0f0 F_5c0f4 D_5c0f4 F_5c0f8 D_5c0f8 (0x15a6d8 + 616) 0 1 1 1 Clk' Wlk'.
  zbft F_5c0fc D_5c0fc.
  stepn F_5c100 D_5c100. rwH. zclosed 0.
  zstep F_5c104 D_5c104. replace (h + 4096 - 4096) with h by lia.
  zbft F_5c108 D_5c108.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chidx' : cellA X (h + 24) 8 idx) by zcell; assert (Cparr' : cellA X (0x15a6d8 + 8) 8 parr) by zcell;
    assert (Cslot' : cellA X (parr + 8 * idx) 8 h) by zcell; assert (Cn' : cellA X (0x15a6d8 + 56) 8 n) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell;
    assert (Cnf' : cellA X (0x15a6d8 + 80) 8 nf) by zcell; assert (Cca' : cellA X (0x15a6d8 + 88) 8 ca) by zcell; assert (Clast' : cellA X (parr + 8 * (n - 1)) 8 last) by zcell end.
  zld F_5c10c D_5c10c (h + 24) Chidx'.
  zld F_5c110 D_5c110 (0x15a6d8 + 8) Cparr'.
  zstep F_5c114 D_5c114. zstep F_5c118 D_5c118.
  zld F_5c11c D_5c11c (parr + 8 * idx) Cslot'.
  zbft F_5c120 D_5c120.
  zld F_5c124 D_5c124 (0x15a6d8 + 56) Cn'.
  zbft F_5c128 D_5c128.
  zstep F_5c12c D_5c12c.
  zld F_5c130 D_5c130 (h + 8) Chms'.
  zstep F_5c134 D_5c134.
  zld F_5c138 D_5c138 (0x15a6d8 + 80) Cnf'.
  zld F_5c13c D_5c13c (0x15a6d8 + 88) Cca'.
  zstep F_5c140 D_5c140.
  zld F_5c144 D_5c144 (parr + 8 * (n - 1)) Clast'.
  zstep F_5c148 D_5c148. zstep F_5c14c D_5c14c.
  zsd F_5c150 D_5c150 (0x15a6d8 + 56) (n - 1) ltac:(zwok').
  zsb F_5c154 D_5c154 (0x15a6d8 + 64) 0 ltac:(zwok').
  zsd F_5c158 D_5c158 (0x15a6d8 + 80) (nf + 1) ltac:(zwok').
  zsd F_5c15c D_5c15c (0x15a6d8 + 88) (ca - ms) ltac:(zwok').
  zstep F_5c160 D_5c160. zstep F_5c164 D_5c164.
  zsd F_5c168 D_5c168 (parr + 8 * idx) last ltac:(zwok').
  zsd F_5c16c D_5c16c (last + 24) idx ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (0x15a948 + 16) 8 s16) by zcell; assert (W16' : wokA X (0x15a948 + 16) 8) by zwok end.
  zamoadd_dc F_5c170 D_5c170 (0x15a948 + 16) s16 (0 - ms) C16' ltac:(exact W16').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chms2 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_5c174 D_5c174 (h + 8) Chms2.
  zstep F_5c178 D_5c178. zstep F_5c17c D_5c17c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C24' : cellA X (0x15a948 + 24) 8 s24) by zcell; assert (W24' : wokA X (0x15a948 + 24) 8) by zwok end.
  zamoadd_dc F_5c180 D_5c180 (0x15a948 + 24) s24 (0 - ms) C24' ltac:(exact W24').
  stepfence F_5c184 D_5c184.
  zsb F_5c188 D_5c188 (0x15a6d8 + 616) 0 ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chh3 : cellA X h 8 h) by zcell; assert (Chms3 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_5c18c D_5c18c h Chh3.
  zld F_5c190 D_5c190 (h + 8) Chms3.
  zstep F_5c194 D_5c194. zstep F_5c198 D_5c198. zstep F_5c19c D_5c19c.
  stepn F_5c1a0 D_5c1a0.
  unfold art_secd_a_mem, art_flush_frame. zret.
Qed.

Definition art_secd_d_mem (M : word -> option byte) (sp : Z) (raw : word) (t ms x8 x9 x18 c88 c96 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 40) 0x5c1fc) (sp - 56) 0x8a05c) (t + 2800 + 88) (c88 + 1)) (t + 2800 + 96) (c96 + ms)) (sp - 8) (U raw)) (sp - 16) x8) (sp - 24) x9) (sp - 32) x18.

Lemma art_secd_d_fn : forall regs (M rom : word -> option byte) (raw : word) (sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 h -> getr regs 18 = Z_to_bv 64 ms ->
  0x6b4000 <= HI -> HI <= sp - 96 -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 ->
  0x6b4000 <= h -> h + 4096 <= HI -> 0 < ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= c88 < 2 ^ 64 -> 0 <= c96 < 2 ^ 64 ->
  art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> tp + 8 <= HI -> tsd + 8 * key + 8 <= HI -> ctx + 160 <= HI -> apart t 4096 h 4096 -> wrA M t 4096 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (t + 2800 + 88) 8 c88 -> cellA M (t + 2800 + 96) 8 c96 ->
  msteps ASEGS (mkst regs (0x5c1f8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x94a9c)) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 ms)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (c96 + ms))) 14 (Z_to_bv 64 (c88 + 1))) 17 (Z_to_bv 64 215)) 18 (Z_to_bv 64 h))
       (0x9322c : word) (art_secd_d_mem M sp raw t ms x8 x9 x18 c88 c96) rom).
Proof.
  intros regs M rom raw sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 H2 H4 H8 H18 HHI Hsp Hsp' W Hh Hh' Hms Hx8 Hx9 Hx18 Hc88 Hc96 TSD Ht Ht' Htp Htsd Hctx Ath Wt F1 F8 F9 F18 Chh Chms C88 C96.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_5c1b0 D_5c1b0.
  zcall (art_thread_stats_fn _ _ _ (0x5c1fc : word) (sp - 32) tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C96' : cellA X (t + 2800 + 96) 8 c96) by zcell; assert (C88' : cellA X (t + 2800 + 88) 8 c88) by zcell;
    assert (Chh' : cellA X h 8 h) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
  zld F_5c1b4 D_5c1b4 (t + 2800 + 96) C96'.
  zld F_5c1b8 D_5c1b8 (t + 2800 + 88) C88'.
  zld F_5c1bc D_5c1bc h Chh'.
  zld F_5c1c0 D_5c1c0 (h + 8) Chms'.
  zstep F_5c1c4 D_5c1c4. zstep F_5c1c8 D_5c1c8.
  zsd F_5c1cc D_5c1cc (t + 2800 + 88) (c88 + 1) ltac:(zwok').
  zsd F_5c1d0 D_5c1d0 (t + 2800 + 96) (c96 + ms) ltac:(zwok').
  zstep F_5c1d4 D_5c1d4. zstep F_5c1d8 D_5c1d8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell; assert (W' : wrA X (sp - 64) 64) by zwr end.
  zld F_5c1dc D_5c1dc (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_5c1e0 D_5c1e0 (sp - 16) G8.
  zld F_5c1e4 D_5c1e4 (sp - 24) G9.
  zld F_5c1e8 D_5c1e8 (sp - 32) G18.
  zstep F_5c1ec D_5c1ec.
  stepn F_5c1f0 D_5c1f0.
  zstep F_94a24 D_94a24.
  zsd F_94a28 D_94a28 (sp - 8) (U raw) ltac:(zwok'). zsd F_94a2c D_94a2c (sp - 16) x8 ltac:(zwok').
  zsd F_94a30 D_94a30 (sp - 24) x9 ltac:(zwok'). zsd F_94a34 D_94a34 (sp - 32) x18 ltac:(zwok').
  zbft F_94a38 D_94a38.
  zstep F_94a3c D_94a3c.
  zbft F_94a40 D_94a40.
  zstep F_94a44 D_94a44. zstep F_94a48 D_94a48. zstep F_94a4c D_94a4c.
  stepn F_94a50 D_94a50.
  zstep F_931e0 D_931e0.
  unfold art_secd_d_mem. zret.
Qed.

Lemma art_secd_e_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ms x8 x9 x18 : Z),
  getr regs 1 = Z_to_bv 64 0x94a9c -> getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 ms -> getr regs 10 = Z_to_bv 64 0 -> ret_ok raw ->
  0x6b4000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  wokA M (sp - 36) 4 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M 0x1544f0 8 0x1ef828 -> cellA M (0x1ef828 + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x93230 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 10 (Z_to_bv 64 ms)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521)) 18 (Z_to_bv 64 x18))
       raw (Wn 4 M (sp - 36) 18446744072277895850) rom).
Proof.
  intros regs M rom raw sp ms x8 x9 x18 H1 H2 H8 H10 Hret Hsp Hsp' Hms Hx8 Hx9 Hx18 Wk F1 F8 F9 F18 CF C144.
  stepret F_931e8 D_931e8 (Z_to_bv 64 0x94a9c : word) ltac:(rwH; reflexivity).
  zstep F_94a54 D_94a54. zstep F_94a58 D_94a58.
  zsw F_94a5c D_94a5c (sp - 36) 18446744072277895850 ltac:(exact Wk).
  zstep F_94a60 D_94a60.
  stepn F_94a64 D_94a64.
  zstep F_931b4 D_931b4. zstep F_931b8 D_931b8.
  zbtk F_931bc D_931bc.
  zstep F_931cc D_931cc.
  stepret F_931d0 D_931d0 (Z_to_bv 64 0x94ab0 : word) ltac:(rwH; reflexivity).
  zbft F_94a68 D_94a68.
  zstep F_94a6c D_94a6c.
  stepn F_94a70 D_94a70.
  zstep F_8f0e0 D_8f0e0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF' : cellA X 0x1544f0 8 0x1ef828) by zcell; assert (C144' : cellA X (0x1ef828 + 144) 8 0) by zcell;
     assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell end.
  zld F_8f0e4 D_8f0e4 0x1544f0 CF'.
  zld F_8f0e8 D_8f0e8 (0x1ef828 + 144) C144'.
  zbtk F_8f0ec D_8f0ec.
  stepret F_8f100 D_8f100 (Z_to_bv 64 0x94abc : word) ltac:(rwH; reflexivity).
  zld F_94a74 D_94a74 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_94a78 D_94a78 (sp - 16) G8.
  zld F_94a7c D_94a7c (sp - 24) G9.
  zld F_94a80 D_94a80 (sp - 32) G18.
  zstep F_94a84 D_94a84.
  stepret F_94a88 D_94a88 raw ltac:(reflexivity).
  zret.
Qed.
End FPX.
