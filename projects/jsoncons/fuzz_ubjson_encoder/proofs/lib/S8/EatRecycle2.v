(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EatLeaf EatAllocG EatPoison EatSecAlloc ArtRuns ArtRunsMem EatFp EatCellEx EatImgCell EatSecRSpec EatPoison3 EatRecycle1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3ef18_4052c Ea0_code_r731ac_733ac Ea0_code_r719b0_719e8 Ea0_code_r6d8b4_6d91c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_secd_a_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (ms parr idx n last nf ca s16 s24 : Z) : word -> option byte :=
  Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 8 (Wn 4 (art_flush_frame M sp raw regs)
     (0x13e3d8 + 616) 1) (0x13e3d8 + 56) (n - 1)) (0x13e3d8 + 64) 0) (0x13e3d8 + 80) (nf + 1)) (0x13e3d8 + 88) (ca - ms)) (parr + 8 * idx) last) (last + 24) idx)
     (0x13e648 + 16) (s16 + (0 - ms))) (0x13e648 + 24) (s24 + (0 - ms))) (0x13e3d8 + 616) 0.

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
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x13e3d8 -> getr regs 11 = Z_to_bv 64 0x13e648 -> getr regs 12 = Z_to_bv 64 (h + 4096) ->
  0x698000 <= HI -> HI <= sp - 32 -> sp < 2 ^ 64 -> wrA M (sp - 32) 32 ->
  0x698000 <= h -> h + 4096 <= HI -> h mod 4096 = 0 -> 0x698000 <= last -> last + 32 <= HI -> apart (last + 24) 8 h 16 ->
  0x698000 <= parr -> parr + 8 * n <= HI -> apart parr (8 * n) h 4096 -> apart parr (8 * n) last 32 -> 0 <= idx < n -> n < 2 ^ 20 -> 0 <= ms < 2 ^ 64 ->
  0 <= nf < 2 ^ 64 -> 0 <= ca < 2 ^ 64 -> 0 <= s16 < 2 ^ 64 -> 0 <= s24 < 2 ^ 64 ->
  cellA M 0x13e3d8 8 4096 -> cellA M (0x13e3d8 + 616) 4 0 -> cellA M (0x13e3d8 + 8) 8 parr -> cellA M (0x13e3d8 + 56) 8 n ->
  cellA M (0x13e3d8 + 80) 8 nf -> cellA M (0x13e3d8 + 88) 8 ca -> cellA M (0x13e648 + 16) 8 s16 -> cellA M (0x13e648 + 24) 8 s24 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (h + 24) 8 idx -> cellA M (parr + 8 * idx) 8 h -> cellA M (parr + 8 * (n - 1)) 8 last ->
  wokA M (parr + 8 * idx) 8 -> wokA M (last + 24) 8 ->
  msteps ASEGS (mkst regs (0x556a8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x5579c)) 2 (Z_to_bv 64 (sp - 32))) 5 (Z_to_bv 64 (ca - ms))) 6 (Z_to_bv 64 0)) 8 (Z_to_bv 64 h)) 9 (Z_to_bv 64 h)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 idx)) 14 (Z_to_bv 64 1304152)) 15 (Z_to_bv 64 last)) 16 (Z_to_bv 64 (0 - ms))) 17 (Z_to_bv 64 ms)) 18 (Z_to_bv 64 ms))
       (0x7b4bc : word) (art_secd_a_mem M sp raw regs ms parr idx n last nf ca s16 s24) rom).
Proof.
  intros regs M rom raw sp HI h ms parr idx n last nf ca s16 s24 H1 H2 H10 H11 H12 HHI Hsp Hsp' W Hh Hh' Hh4 Hl Hl' Alh Hparr Hparr' Aph Apl Hidx Hn Hms Hnf Hca Hs16 Hs24
    Cpg Clk Cparr Cn Cnf Cca C16 C24 Chh Chms Chidx Cslot Clast Wslot Wlast.
  pose proof (art_img_wr M 0x13e3d8 1024 ltac:(lia) ltac:(lia) ltac:(lia)) as Wimg.
  zstep F_55658 D_55658.
  zsd F_5565c D_5565c (sp - 8) (U raw) ltac:(rewok W). zsd F_55660 D_55660 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_55664 D_55664 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_55668 D_55668 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg' : cellA X 0x13e3d8 8 4096) by zcell end.
  zld F_5566c D_5566c 0x13e3d8 Cpg'.
  zstep F_55670 D_55670.
  stepn F_55674 D_55674. rwH. rewrite art_zb_and by lia.
  replace (Z.land 4095 (h + 4096)) with 0 by (change 4095 with (Z.ones 12); rewrite Z.land_comm, Z.land_ones by lia; change (2 ^ 12) with 4096; rewrite Z.add_mod, Hh4 by lia; reflexivity).
  zbft F_55678 D_55678.
  zstep F_5567c D_5567c. zstep F_55680 D_55680.
  stepn F_55684 D_55684. rwH. zclosed (0x13e3d8 + 616).
  zstep F_55688 D_55688.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x13e3d8 + 616) 4 0) by zcell; assert (Wlk' : wokA X (0x13e3d8 + 616) 4) by zwok end.
  zcas6 F_5568c D_5568c F_55690 D_55690 F_55694 D_55694 F_55698 D_55698 F_5569c D_5569c F_556a0 D_556a0 (0x13e3d8 + 616) 0 1 1 1 Clk' Wlk'.
  zbft F_556a4 D_556a4.
  stepn F_556a8 D_556a8. rwH. zclosed 0.
  zstep F_556ac D_556ac. replace (h + 4096 - 4096) with h by lia.
  zbft F_556b0 D_556b0.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chidx' : cellA X (h + 24) 8 idx) by zcell; assert (Cparr' : cellA X (0x13e3d8 + 8) 8 parr) by zcell;
    assert (Cslot' : cellA X (parr + 8 * idx) 8 h) by zcell; assert (Cn' : cellA X (0x13e3d8 + 56) 8 n) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell;
    assert (Cnf' : cellA X (0x13e3d8 + 80) 8 nf) by zcell; assert (Cca' : cellA X (0x13e3d8 + 88) 8 ca) by zcell; assert (Clast' : cellA X (parr + 8 * (n - 1)) 8 last) by zcell end.
  zld F_556b4 D_556b4 (h + 24) Chidx'.
  zld F_556b8 D_556b8 (0x13e3d8 + 8) Cparr'.
  zstep F_556bc D_556bc. zstep F_556c0 D_556c0.
  zld F_556c4 D_556c4 (parr + 8 * idx) Cslot'.
  zbft F_556c8 D_556c8.
  zld F_556cc D_556cc (0x13e3d8 + 56) Cn'.
  zbft F_556d0 D_556d0.
  zstep F_556d4 D_556d4.
  zld F_556d8 D_556d8 (h + 8) Chms'.
  zstep F_556dc D_556dc.
  zld F_556e0 D_556e0 (0x13e3d8 + 80) Cnf'.
  zld F_556e4 D_556e4 (0x13e3d8 + 88) Cca'.
  zstep F_556e8 D_556e8.
  zld F_556ec D_556ec (parr + 8 * (n - 1)) Clast'.
  zstep F_556f0 D_556f0. zstep F_556f4 D_556f4.
  zsd F_556f8 D_556f8 (0x13e3d8 + 56) (n - 1) ltac:(zwok').
  zsb F_556fc D_556fc (0x13e3d8 + 64) 0 ltac:(zwok').
  zsd F_55700 D_55700 (0x13e3d8 + 80) (nf + 1) ltac:(zwok').
  zsd F_55704 D_55704 (0x13e3d8 + 88) (ca - ms) ltac:(zwok').
  zstep F_55708 D_55708. zstep F_5570c D_5570c.
  zsd F_55710 D_55710 (parr + 8 * idx) last ltac:(zwok').
  zsd F_55714 D_55714 (last + 24) idx ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (0x13e648 + 16) 8 s16) by zcell; assert (W16' : wokA X (0x13e648 + 16) 8) by zwok end.
  zamoadd_dc F_55718 D_55718 (0x13e648 + 16) s16 (0 - ms) C16' ltac:(exact W16').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chms2 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_5571c D_5571c (h + 8) Chms2.
  zstep F_55720 D_55720. zstep F_55724 D_55724.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C24' : cellA X (0x13e648 + 24) 8 s24) by zcell; assert (W24' : wokA X (0x13e648 + 24) 8) by zwok end.
  zamoadd_dc F_55728 D_55728 (0x13e648 + 24) s24 (0 - ms) C24' ltac:(exact W24').
  stepfence F_5572c D_5572c.
  zsb F_55730 D_55730 (0x13e3d8 + 616) 0 ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chh3 : cellA X h 8 h) by zcell; assert (Chms3 : cellA X (h + 8) 8 ms) by zcell end.
  zld F_55734 D_55734 h Chh3.
  zld F_55738 D_55738 (h + 8) Chms3.
  zstep F_5573c D_5573c. zstep F_55740 D_55740. zstep F_55744 D_55744.
  stepn F_55748 D_55748.
  unfold art_secd_a_mem, art_flush_frame. zret.
Qed.

Definition art_secd_d_mem (M : word -> option byte) (sp : Z) (raw : word) (t ms x8 x9 x18 c88 c96 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 40) 0x557ac) (sp - 56) 0x83440) (t + 2800 + 88) (c88 + 1)) (t + 2800 + 96) (c96 + ms)) (sp - 8) (U raw)) (sp - 16) x8) (sp - 24) x9) (sp - 32) x18.

#[using="Type"] Lemma art_secd_d_fn : forall regs (M rom : word -> option byte) (raw : word) (sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 h -> getr regs 18 = Z_to_bv 64 ms ->
  0x698000 <= HI -> HI <= sp - 96 -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 ->
  0x698000 <= h -> h + 4096 <= HI -> 0 < ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= c88 < 2 ^ 64 -> 0 <= c96 < 2 ^ 64 ->
  art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> tp + 8 <= HI -> tsd + 8 * key + 8 <= HI -> ctx + 160 <= HI -> apart t 4096 h 4096 -> wrA M t 4096 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M h 8 h -> cellA M (h + 8) 8 ms -> cellA M (t + 2800 + 88) 8 c88 -> cellA M (t + 2800 + 96) 8 c96 ->
  msteps ASEGS (mkst regs (0x557a8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x8de80)) 2 (Z_to_bv 64 (sp - 48))) 8 (Z_to_bv 64 ms)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 h)) 11 (Z_to_bv 64 ms)) 12 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (c96 + ms))) 14 (Z_to_bv 64 (c88 + 1))) 17 (Z_to_bv 64 215)) 18 (Z_to_bv 64 h))
       (0x8c610 : word) (art_secd_d_mem M sp raw t ms x8 x9 x18 c88 c96) rom).
Proof.
  intros regs M rom raw sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 H2 H4 H8 H18 HHI Hsp Hsp' W Hh Hh' Hms Hx8 Hx9 Hx18 Hc88 Hc96 TSD Ht Ht' Htp Htsd Hctx Ath Wt F1 F8 F9 F18 Chh Chms C88 C96.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  stepn F_55758 D_55758.
  zcall (art_thread_stats_fn _ _ _ (0x557ac : word) (sp - 32) tp key tsd ctx t).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C96' : cellA X (t + 2800 + 96) 8 c96) by zcell; assert (C88' : cellA X (t + 2800 + 88) 8 c88) by zcell;
    assert (Chh' : cellA X h 8 h) by zcell; assert (Chms' : cellA X (h + 8) 8 ms) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
  zld F_5575c D_5575c (t + 2800 + 96) C96'.
  zld F_55760 D_55760 (t + 2800 + 88) C88'.
  zld F_55764 D_55764 h Chh'.
  zld F_55768 D_55768 (h + 8) Chms'.
  zstep F_5576c D_5576c. zstep F_55770 D_55770.
  zsd F_55774 D_55774 (t + 2800 + 88) (c88 + 1) ltac:(zwok').
  zsd F_55778 D_55778 (t + 2800 + 96) (c96 + ms) ltac:(zwok').
  zstep F_5577c D_5577c. zstep F_55780 D_55780.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell; assert (W' : wrA X (sp - 64) 64) by zwr end.
  zld F_55784 D_55784 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_55788 D_55788 (sp - 16) G8.
  zld F_5578c D_5578c (sp - 24) G9.
  zld F_55790 D_55790 (sp - 32) G18.
  zstep F_55794 D_55794.
  stepn F_55798 D_55798.
  zstep F_8de00 D_8de00.
  zsd F_8de04 D_8de04 (sp - 8) (U raw) ltac:(zwok'). zsd F_8de08 D_8de08 (sp - 16) x8 ltac:(zwok').
  zsd F_8de0c D_8de0c (sp - 24) x9 ltac:(zwok'). zsd F_8de10 D_8de10 (sp - 32) x18 ltac:(zwok').
  zbft F_8de14 D_8de14.
  zstep F_8de18 D_8de18.
  zbft F_8de1c D_8de1c.
  zstep F_8de20 D_8de20. zstep F_8de24 D_8de24. zstep F_8de28 D_8de28.
  stepn F_8de2c D_8de2c.
  zstep F_8c5bc D_8c5bc.
  unfold art_secd_d_mem. zret.
Qed.

#[using="Type"] Lemma art_secd_e_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ms x8 x9 x18 : Z),
  getr regs 1 = Z_to_bv 64 0x8de80 -> getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 ms -> getr regs 10 = Z_to_bv 64 0 -> ret_ok raw ->
  0x698000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= ms < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  wokA M (sp - 36) 4 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 ->
  cellA M 0x1391a8 8 0x1d3528 -> cellA M (0x1d3528 + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x8c614 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 10 (Z_to_bv 64 ms)) 11 (Z_to_bv 64 0)) 12 (Z_to_bv 64 18446744073709547520)) 13 (Z_to_bv 64 18446744073709547521)) 18 (Z_to_bv 64 x18))
       raw (Wn 4 M (sp - 36) 18446744072277895850) rom).
Proof.
  intros regs M rom raw sp ms x8 x9 x18 H1 H2 H8 H10 Hret Hsp Hsp' Hms Hx8 Hx9 Hx18 Wk F1 F8 F9 F18 CF C144.
  stepret F_8c5c4 D_8c5c4 (Z_to_bv 64 0x8de80 : word) ltac:(rwH; reflexivity).
  zstep F_8de30 D_8de30. zstep F_8de34 D_8de34.
  zsw F_8de38 D_8de38 (sp - 36) 18446744072277895850 ltac:(exact Wk).
  zstep F_8de3c D_8de3c.
  stepn F_8de40 D_8de40.
  zstep F_8c590 D_8c590. zstep F_8c594 D_8c594.
  zbtk F_8c598 D_8c598.
  zstep F_8c5a8 D_8c5a8.
  stepret F_8c5ac D_8c5ac (Z_to_bv 64 0x8de94 : word) ltac:(rwH; reflexivity).
  zbft F_8de44 D_8de44.
  zstep F_8de48 D_8de48.
  stepn F_8de4c D_8de4c.
  zstep F_884bc D_884bc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF' : cellA X 0x1391a8 8 0x1d3528) by zcell; assert (C144' : cellA X (0x1d3528 + 144) 8 0) by zcell;
     assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 x8) by zcell;
     assert (G9 : cellA X (sp - 24) 8 x9) by zcell; assert (G18 : cellA X (sp - 32) 8 x18) by zcell end.
  zld F_884c0 D_884c0 0x1391a8 CF'.
  zld F_884c4 D_884c4 (0x1d3528 + 144) C144'.
  zbtk F_884c8 D_884c8.
  stepret F_884dc D_884dc (Z_to_bv 64 0x8dea0 : word) ltac:(rwH; reflexivity).
  zld F_8de50 D_8de50 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_8de54 D_8de54 (sp - 16) G8.
  zld F_8de58 D_8de58 (sp - 24) G9.
  zld F_8de5c D_8de5c (sp - 32) G18.
  zstep F_8de60 D_8de60.
  stepret F_8de64 D_8de64 raw ltac:(reflexivity).
  zret.
Qed.
End FPX.
