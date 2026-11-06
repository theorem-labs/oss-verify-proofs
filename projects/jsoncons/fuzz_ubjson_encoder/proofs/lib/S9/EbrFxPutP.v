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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac ArtFxTac EbtLeaf EbtPoison EbtAllocG EbtUnwind EbtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtHdrW.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtFxPut.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r5c3b4_5c44c Eb0_code_r5fac4_60344 Eb0_code_r67bcc_67d3c Eb0_code_r3cf10_3de98 Eb0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000080. Set Printing Width 10000.

Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Section FPX. Context {fx : PropExec.FPState}.

Definition art_fx_fq1p_mem (M : word -> option byte) (S p t id f22 : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (p - 16 + 16) id) (S - 2136) 502648) (S - 2144) S) (S - 2152) p) (S - 2160) 502536) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2208) (t + 208)) (S - 2208 + 8) (S - 2128)).
Lemma art_fx_fq1p_mem_eq : forall M S p t id f22, art_fx_fq1p_mem M S p t id f22 = art_fx_fq1_mem M S p t id f22.
Proof. intros. unfold art_fx_fq1p_mem, art_fx_fq1_mem. replace (p - 16 + 16) with p by lia. replace (S - 2208 + 8) with (S - 2200) by lia. reflexivity. Qed.

#[using="Type"] Lemma art_fx_fq1p_fn : forall regs (M rom : word -> option byte) (S p b1 n t id f22 spb : Z),
  getr regs 2 = Z_to_bv 64 (S - 2176) -> getr regs 8 = Z_to_bv 64 (p - 16) -> getr regs 9 = Z_to_bv 64 (S - 2128) -> getr regs 10 = Z_to_bv 64 id ->
  getr regs 18 = Z_to_bv 64 0x142a98 -> getr regs 19 = Z_to_bv 64 0 -> getr regs 20 = Z_to_bv 64 t -> getr regs 21 = Z_to_bv 64 (S - 81) -> getr regs 22 = Z_to_bv 64 f22 ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x69c000 + 16 <= p -> p + 8 < 2 ^ 47 -> 0 <= b1 < 2 ^ 24 -> 2 ^ 28 < n < 2 ^ 40 -> b1 / 256 = n / 2 ^ 32 -> 0 <= id < 2 ^ 32 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart (p - 16) 24 (S - 4096) 8192 -> 0 <= f22 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M (p - 16) 24 -> art_layout M ->
  cellA M (S - 2136) 8 (U (0x7ab78 : bv 64)%bv) -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x7ab08 : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) ->
  cellA M (p - 16) 4 (3 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M (0x142d70 + 80) 8 (2 ^ 20) -> cellA M (0x142d70 + 64) 8 (2 ^ 28) -> cellA M (0x1438f8 + 48) 4 0 ->
  cellA M 0x142ab8 8 spb -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> (p - 16 < spb \/ spb + 2 ^ 37 <= p - 16) ->
  exists regs',
    msteps ASEGS (mkst regs (0x57898 : word) M rom) (mkst regs' (0x55904 : word) (art_fx_fq1_mem M S p t id f22) rom)
    /\ getr regs' 1 = (0x57a78 : bv 64)%bv /\ getr regs' 2 = Z_to_bv 64 (S - 2208) /\ getr regs' 10 = Z_to_bv 64 (S - 2208) /\ getr regs' 11 = Z_to_bv 64 (p - 16)
    /\ getr regs' 9 = Z_to_bv 64 (t + 80) /\ getr regs' 22 = Z_to_bv 64 (2 ^ 20)
    /\ (forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom S p b1 n t id f22 spb H2 H8 H9 H10 H18 H19 H20 H21 H22 HS HS' Hp Hp' Hb1 Hn Hlink Hid Ht Ht' Apsp Hf22 W Wp L C36 C44 C52 C60 C68 C76 Chw Cn Cqc Cqm Cff Cspb Hspb0 Hspb Hsec.
  rewrite <- art_fx_fq1p_mem_eq. unfold art_fx_fq1p_mem.
  assert (Hb1w := Hb1). clear Hb1. assert (Hb1 : 0 <= b1 < 2 ^ 16) by (apply (art_b1_bound b1 n (proj1 Hb1w) Hlink); clear - Hn; lia). clear Hb1w.
  assert (Hhi : 0 <= b1 / 256 < 2 ^ 15) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  assert (Hlo : 0 <= n mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
  assert (Hhi32 : 0 <= b1 / 256 * 2 ^ 32 < 2 ^ 47) by lia.
  destruct Hsec as [Hsec|Hsec].
  - eexists. split.
    {
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_57848 D_57848. rwH. try rewrite art_zb_slli by lia.
  stepn F_5784c D_5784c. rwH. try rewrite art_zb_slli by lia.
  stepn F_57850 D_57850. rwH. try rewrite art_zb_srli by lia. try rewrite Z.div_mul by lia.
  stepn F_57854 D_57854. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zsd F_57858 D_57858 (p - 16 + 16) id ltac:(rewok Wp).
  zstep F_5785c D_5785c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (_ & _ & Chi);
    rewrite (art_hdrw_hi 3 b1) in Chi by lia;
    assert (Cn' : cellA X (p - 16 + 4) 4 (n mod 2 ^ 32)) by (replace (p - 16 + 4) with (p - 12) by lia; apply cell4_mod; zcell) end.
  zlhu F_57860 D_57860 (p - 16 + 2) Chi.
  zlwu F_57864 D_57864 (p - 16 + 4) Cn'.
  zstep F_57868 D_57868. zstep F_5786c D_5786c.
  stepn F_57870 D_57870. rwH. try rewrite art_zb_slli by lia.
  stepn F_57874 D_57874. rwH. rewrite art_fx_zb_or2 by lia. rewrite (art_or_b1lo b1 n) by lia.
  zstep F_57878 D_57878. zstep F_5787c D_5787c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x7ab78 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x7ab08 : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell end.
  zld F_57880 D_57880 (S - 2136) E36. zld F_57884 D_57884 (S - 2144) E44. zld F_57888 D_57888 (S - 2152) E52.
  zld F_5788c D_5788c (S - 2160) E60. zld F_57890 D_57890 (S - 2168) E68. zld F_57894 D_57894 (S - 2176) E76.
  zstep F_57898 D_57898.
  stepn F_5789c D_5789c.

  zstep F_57968 D_57968.
  zsd F_5796c D_5796c (S - 2136) (U (0x7ab78 : bv 64)%bv) ltac:(rewok W). zsd F_57970 D_57970 (S - 2144) S ltac:(rewok W). zsd F_57974 D_57974 (S - 2152) p ltac:(rewok W).
  zsd F_57978 D_57978 (S - 2160) (U (0x7ab08 : bv 64)%bv) ltac:(rewok W). zsd F_5797c D_5797c (S - 2168) 1 ltac:(rewok W). zsd F_57980 D_57980 (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_57984 D_57984 (S - 2184) (S - 81) ltac:(rewok W). zsd F_57988 D_57988 (S - 2192) f22 ltac:(rewok W).
  zstep F_5798c D_5798c.
  zsd F_57990 D_57990 (S - 2208) (t + 208) ltac:(rewok W). zsd F_57994 D_57994 (S - 2208 + 8) (S - 2128) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cqc' : cellA X (0x142d70 + 80) 8 (2 ^ 20)) by zcell; assert (Cqm' : cellA X (0x142d70 + 64) 8 (2 ^ 28)) by zcell end.
  zld F_57998 D_57998 (0x142d70 + 80) Cqc'.
  zstep F_5799c D_5799c.
  zbft F_579a0 D_579a0.
  zld F_579a4 D_579a4 (0x142d70 + 64) Cqm'.
  zbft F_579a8 D_579a8.
  zstep F_579ac D_579ac.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X 0x142ab8 8 spb) by zcell end.
  zld F_579b0 D_579b0 0x142ab8 Cspb'.
  zbtk F_579b4 D_579b4.
  zstep F_57a1c D_57a1c. zstep F_57a20 D_57a20.
  stepn F_57a24 D_57a24.
  apply mst_refl.
    }
  split; [gres; apply bv_eq; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    {
  pose proof L as (G48 & Csb & G50 & Cmb & G58 & Cme & G60 & Che & G40 & Cpg & G68 & Crm & G38 & Cth & Ccp).
  stepn F_57848 D_57848. rwH. try rewrite art_zb_slli by lia.
  stepn F_5784c D_5784c. rwH. try rewrite art_zb_slli by lia.
  stepn F_57850 D_57850. rwH. try rewrite art_zb_srli by lia. try rewrite Z.div_mul by lia.
  stepn F_57854 D_57854. rwH. rewrite ?Z.mul_0_l. rewrite art_fx_zb_or2 by lia. rewrite Z.lor_0_l.
  zsd F_57858 D_57858 (p - 16 + 16) id ltac:(rewok Wp).
  zstep F_5785c D_5785c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (_ & _ & Chi);
    rewrite (art_hdrw_hi 3 b1) in Chi by lia;
    assert (Cn' : cellA X (p - 16 + 4) 4 (n mod 2 ^ 32)) by (replace (p - 16 + 4) with (p - 12) by lia; apply cell4_mod; zcell) end.
  zlhu F_57860 D_57860 (p - 16 + 2) Chi.
  zlwu F_57864 D_57864 (p - 16 + 4) Cn'.
  zstep F_57868 D_57868. zstep F_5786c D_5786c.
  stepn F_57870 D_57870. rwH. try rewrite art_zb_slli by lia.
  stepn F_57874 D_57874. rwH. rewrite art_fx_zb_or2 by lia. rewrite (art_or_b1lo b1 n) by lia.
  zstep F_57878 D_57878. zstep F_5787c D_5787c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x7ab78 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x7ab08 : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell end.
  zld F_57880 D_57880 (S - 2136) E36. zld F_57884 D_57884 (S - 2144) E44. zld F_57888 D_57888 (S - 2152) E52.
  zld F_5788c D_5788c (S - 2160) E60. zld F_57890 D_57890 (S - 2168) E68. zld F_57894 D_57894 (S - 2176) E76.
  zstep F_57898 D_57898.
  stepn F_5789c D_5789c.

  zstep F_57968 D_57968.
  zsd F_5796c D_5796c (S - 2136) (U (0x7ab78 : bv 64)%bv) ltac:(rewok W). zsd F_57970 D_57970 (S - 2144) S ltac:(rewok W). zsd F_57974 D_57974 (S - 2152) p ltac:(rewok W).
  zsd F_57978 D_57978 (S - 2160) (U (0x7ab08 : bv 64)%bv) ltac:(rewok W). zsd F_5797c D_5797c (S - 2168) 1 ltac:(rewok W). zsd F_57980 D_57980 (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_57984 D_57984 (S - 2184) (S - 81) ltac:(rewok W). zsd F_57988 D_57988 (S - 2192) f22 ltac:(rewok W).
  zstep F_5798c D_5798c.
  zsd F_57990 D_57990 (S - 2208) (t + 208) ltac:(rewok W). zsd F_57994 D_57994 (S - 2208 + 8) (S - 2128) ltac:(rewok W).
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cqc' : cellA X (0x142d70 + 80) 8 (2 ^ 20)) by zcell; assert (Cqm' : cellA X (0x142d70 + 64) 8 (2 ^ 28)) by zcell end.
  zld F_57998 D_57998 (0x142d70 + 80) Cqc'.
  zstep F_5799c D_5799c.
  zbft F_579a0 D_579a0.
  zld F_579a4 D_579a4 (0x142d70 + 64) Cqm'.
  zbft F_579a8 D_579a8.
  zstep F_579ac D_579ac.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X 0x142ab8 8 spb) by zcell end.
  zld F_579b0 D_579b0 0x142ab8 Cspb'.
  zbft F_579b4 D_579b4.
  zstep F_579b8 D_579b8.
  stepn F_579bc D_579bc. rwH. try rewrite art_zb_slli by lia.
  zstep F_579c0 D_579c0.
  zbtk F_579c4 D_579c4.
  zstep F_57a1c D_57a1c. zstep F_57a20 D_57a20.
  stepn F_57a24 D_57a24.
  apply mst_refl.
    }
  split; [gres; apply bv_eq; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_fx_fq2p_fn : forall regs (M rom : word -> option byte) (raw0 : word) (S p c csz f22 g16 g24 g32 g40 g48 g56 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 9 = Z_to_bv 64 c -> getr regs 22 = Z_to_bv 64 (2 ^ 20) ->
  ret_ok raw0 -> 0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0 <= p < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> 0 <= csz <= 2 ^ 20 ->
  0 <= g16 < 2 ^ 64 -> 0 <= g24 < 2 ^ 64 -> 0 <= g32 < 2 ^ 64 -> 0 <= g40 < 2 ^ 64 -> 0 <= g48 < 2 ^ 64 -> 0 <= g56 < 2 ^ 64 ->
  cellA M (c + 24) 8 csz ->
  cellA M (S - 2136) 8 0x7ab78 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 0x7ab08 -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 ->
  cellA M (S - 8) 8 (U raw0) -> cellA M (S - 16) 8 g16 -> cellA M (S - 24) 8 g24 -> cellA M (S - 32) 8 g32 -> cellA M (S - 40) 8 g40 -> cellA M (S - 48) 8 g48 -> cellA M (S - 56) 8 g56 ->
  msteps ASEGS (mkst regs (0x57a78 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw0) 2 (Z_to_bv 64 S)) 8 (Z_to_bv 64 g16)) 9 (Z_to_bv 64 g24)) 10 (Z_to_bv 64 csz)) 18 (Z_to_bv 64 g32)) 19 (Z_to_bv 64 g40)) 20 (Z_to_bv 64 g48)) 21 (Z_to_bv 64 g56)) 22 (Z_to_bv 64 f22))
          raw0 M rom).
Proof.
  intros regs M rom raw0 S p c csz f22 g16 g24 g32 g40 g48 g56 H2 H9 H22 Hret HS HS' Hp Hf22 Hc Hc' Hcsz Hg16 Hg24 Hg32 Hg40 Hg48 Hg56 Ccsz E36 E44 E52 E60 E68 E76 E84 E92 F8 F16 F24 F32 F40 F48 F56.
  zld F_57a28 D_57a28 (c + 24) Ccsz.
  zbtk F_57a2c D_57a2c.
  zcall (art_fx_fq2e_fn _ _ _ raw0 S p f22 g16 g24 g32 g40 g48 g56).
  zret.
Qed.

End FPX.
