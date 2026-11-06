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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EatLeaf EatAllocG EatPoison ArtRuns ArtRunsMem EatFp EatFree1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3ef18_4052c.
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

Definition art_drain_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)).

Definition art_drain_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (c L F B bytes GL GB gbytes : Z) : word -> option byte :=
  let M2 := Wn 4 (art_drain_frame M sp raw regs) (0x13e670 + 152) 1 in
  let M3 := if GL =? 0 then Wn 8 (Wn 8 (Wn 8 M2 (0x13e670 + 176) B) (0x13e670 + 168) F) (0x13e670 + 160) L
            else Wn 8 (Wn 8 (Wn 8 M2 GB F) (0x13e670 + 160) (GL + L)) (0x13e670 + 176) B in
  Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M3 c 0) (c + 8) 0) (c + 16) 0) (0x13e670 + 184) (gbytes + bytes)) (c + 24) 0) (0x13e670 + 152) 0.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_drain_pre : forall regs (M rom : word -> option byte) (raw : word) (sp c L F B bytes GL GB gbytes : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x13e670 -> getr regs 11 = Z_to_bv 64 c ->
  0x698000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> (c + 32 <= 0x10000 \/ 0x698000 <= c) -> apart (sp - 48) 48 c 32 ->
  1 <= L < 2 ^ 63 -> 0 <= F < 2 ^ 64 -> 0 <= B < 2 ^ 64 -> 0 <= bytes -> 0 <= gbytes -> gbytes + bytes < 2 ^ 64 -> 0 <= GL -> GL + L < 2 ^ 63 ->
  (GL <> 0 -> 0x698000 <= GB /\ GB + 8 < 2 ^ 64 /\ apart (sp - 48) 48 GB 8 /\ apart c 32 GB 8 /\ wrA M GB 8) ->
  wrA M (sp - 48) 48 -> wrA M c 32 -> wrA M (0x13e670 + 152) 40 ->
  cellA M (0x13e670 + 152) 4 0 ->
  cellA M c 8 L -> cellA M (c + 8) 8 F -> cellA M (c + 16) 8 B -> cellA M (c + 24) 8 bytes ->
  cellA M (0x13e670 + 160) 8 GL -> (GL <> 0 -> cellA M (0x13e670 + 176) 8 GB) -> cellA M (0x13e670 + 184) 8 gbytes ->
  exists regs', msteps ASEGS (mkst regs (0x54a98 : word) M rom) (mkst regs' (0x54b5c : word) (art_drain_mem M sp raw regs c L F B bytes GL GB gbytes) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 10 = Z_to_bv 64 0x13e670
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp c L F B bytes GL GB gbytes H1 H2 H10 H11 IMG Hsp' Hc Hc' Hci Ac HL HF HB Hby Hgb Hgb' HGL HGL' HGB W Wc Wq Clk CL CF CB Cby CGL CGB Cgb.
  destruct (Z.eq_dec GL 0) as [EG|NG].
  -
    eexists. split.
    {
    zstep F_54a48 D_54a48.
    zsd F_54a4c D_54a4c (sp - 8) (U raw) ltac:(rewok W). zsd F_54a50 D_54a50 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_54a54 D_54a54 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_54a58 D_54a58 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_54a5c D_54a5c (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zstep F_54a60 D_54a60. zstep F_54a64 D_54a64.
    stepn F_54a68 D_54a68. rwH. zclosed (0x13e670 + 152).
    zstep F_54a6c D_54a6c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x13e670 + 152) 4 0) by zcell; assert (Wlk' : wokA X (0x13e670 + 152) 4) by zwok end.
    zcas6 F_54a70 D_54a70 F_54a74 D_54a74 F_54a78 D_54a78 F_54a7c D_54a7c F_54a80 D_54a80 F_54a84 D_54a84 (0x13e670 + 152) 0 1 1 1 Clk' Wlk'.
    zbft F_54a88 D_54a88.
    stepn F_54a8c D_54a8c. rwH. zclosed 0.
    zbft F_54a90 D_54a90.
    zstep F_54a94 D_54a94.
    zbft F_54a98 D_54a98.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell; assert (CGL' : cellA X (0x13e670 + 160) 8 GL) by zcell end.
    zld F_54a9c D_54a9c c CL'.
    zbft F_54aa0 D_54aa0.
    zld F_54aa4 D_54aa4 (0x13e670 + 160) CGL'.
    zbtk F_54aa8 D_54aa8.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CB' : cellA X (c + 16) 8 B) by zcell; assert (CF' : cellA X (c + 8) 8 F) by zcell; assert (CL2 : cellA X c 8 L) by zcell end.
    zld F_54acc D_54acc (c + 16) CB'.
    zsd F_54ad0 D_54ad0 (0x13e670 + 176) B ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF2 : cellA X (c + 8) 8 F) by zcell end.
    zld F_54ad4 D_54ad4 (c + 8) CF2.
    zsd F_54ad8 D_54ad8 (0x13e670 + 168) F ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL3 : cellA X c 8 L) by zcell end.
    zld F_54adc D_54adc c CL3.
    zsd F_54ae0 D_54ae0 (0x13e670 + 160) L ltac:(zwok').
    zsd F_54ae4 D_54ae4 c 0 ltac:(zwok'). zsd F_54ae8 D_54ae8 (c + 8) 0 ltac:(zwok'). zsd F_54aec D_54aec (c + 16) 0 ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell; assert (Cgb' : cellA X (0x13e670 + 184) 8 gbytes) by zcell end.
    zld F_54af0 D_54af0 (c + 24) Cby'.
    zld F_54af4 D_54af4 (0x13e670 + 184) Cgb'.
    zstep F_54af8 D_54af8.
    zsd F_54afc D_54afc (0x13e670 + 184) (gbytes + bytes) ltac:(zwok').
    zsd F_54b00 D_54b00 (c + 24) 0 ltac:(zwok').
    stepfence F_54b04 D_54b04.
    zsb F_54b08 D_54b08 (0x13e670 + 152) 0 ltac:(zwok').
    unfold art_drain_mem, art_drain_frame. rewrite (proj2 (Z.eqb_eq GL 0) EG). apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity|reflexivity|zmem_eq]. }
    split; [gres; f_equal; lia|]. split; [gres; exact H10|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  -
    destruct (HGB NG) as (GB0 & GB1 & AGs & AGc & WGB). specialize (CGB NG).
    eexists. split.
    {
    zstep F_54a48 D_54a48.
    zsd F_54a4c D_54a4c (sp - 8) (U raw) ltac:(rewok W). zsd F_54a50 D_54a50 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_54a54 D_54a54 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_54a58 D_54a58 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_54a5c D_54a5c (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zstep F_54a60 D_54a60. zstep F_54a64 D_54a64.
    stepn F_54a68 D_54a68. rwH. zclosed (0x13e670 + 152).
    zstep F_54a6c D_54a6c.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x13e670 + 152) 4 0) by zcell; assert (Wlk' : wokA X (0x13e670 + 152) 4) by zwok end.
    zcas6 F_54a70 D_54a70 F_54a74 D_54a74 F_54a78 D_54a78 F_54a7c D_54a7c F_54a80 D_54a80 F_54a84 D_54a84 (0x13e670 + 152) 0 1 1 1 Clk' Wlk'.
    zbft F_54a88 D_54a88.
    stepn F_54a8c D_54a8c. rwH. zclosed 0.
    zbft F_54a90 D_54a90.
    zstep F_54a94 D_54a94.
    zbft F_54a98 D_54a98.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell; assert (CGL' : cellA X (0x13e670 + 160) 8 GL) by zcell end.
    zld F_54a9c D_54a9c c CL'.
    zbft F_54aa0 D_54aa0.
    zld F_54aa4 D_54aa4 (0x13e670 + 160) CGL'.
    zbft F_54aa8 D_54aa8.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CGB' : cellA X (0x13e670 + 176) 8 GB) by zcell; assert (CB' : cellA X (c + 16) 8 B) by zcell; assert (CF' : cellA X (c + 8) 8 F) by zcell end.
    zld F_54aac D_54aac (0x13e670 + 176) CGB'.
    zld F_54ab0 D_54ab0 (c + 8) CF'.
    zld F_54ab4 D_54ab4 (c + 16) CB'.
    zstep F_54ab8 D_54ab8.
    zsd F_54abc D_54abc GB F ltac:(zwok').
    zsd F_54ac0 D_54ac0 (0x13e670 + 160) (GL + L) ltac:(zwok').
    zsd F_54ac4 D_54ac4 (0x13e670 + 176) B ltac:(zwok').
    stepn F_54ac8 D_54ac8.
    zsd F_54ae4 D_54ae4 c 0 ltac:(zwok'). zsd F_54ae8 D_54ae8 (c + 8) 0 ltac:(zwok'). zsd F_54aec D_54aec (c + 16) 0 ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell; assert (Cgb' : cellA X (0x13e670 + 184) 8 gbytes) by zcell end.
    zld F_54af0 D_54af0 (c + 24) Cby'.
    zld F_54af4 D_54af4 (0x13e670 + 184) Cgb'.
    zstep F_54af8 D_54af8.
    zsd F_54afc D_54afc (0x13e670 + 184) (gbytes + bytes) ltac:(zwok').
    zsd F_54b00 D_54b00 (c + 24) 0 ltac:(zwok').
    stepfence F_54b04 D_54b04.
    zsb F_54b08 D_54b08 (0x13e670 + 152) 0 ltac:(zwok').
    unfold art_drain_mem, art_drain_frame. rewrite (proj2 (Z.eqb_neq GL 0) NG). apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity|reflexivity|zmem_eq]. }
    split; [gres; f_equal; lia|]. split; [gres; exact H10|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_drain_ret_fn : forall regs (M rom : word -> option byte) (raw : word) (sp gb x8 x9 x18 x19 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 10 = Z_to_bv 64 0x13e670 -> ret_ok raw ->
  48 <= sp -> sp < 2 ^ 64 -> 0 <= gb <= 2 ^ 28 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= x19 < 2 ^ 64 ->
  cellA M (0x13e670 + 184) 8 gb -> cellA M (0x13e670 + 64) 8 (2 ^ 28) ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 -> cellA M (sp - 40) 8 x19 ->
  msteps ASEGS (mkst regs (0x54b5c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 11 (Z_to_bv 64 gb)) 14 (Z_to_bv 64 (2 ^ 28))) 18 (Z_to_bv 64 x18)) 19 (Z_to_bv 64 x19))
          raw M rom).
Proof.
  intros regs M rom raw sp gb x8 x9 x18 x19 H2 H10 Hret Hsp Hsp' Hgb Hx8 Hx9 Hx18 Hx19 Cgb Cmax F1 F8 F9 F18 F19.
  zld F_54b0c D_54b0c (0x13e670 + 184) Cgb.
  zld F_54b10 D_54b10 (0x13e670 + 64) Cmax.
  zbtk F_54b14 D_54b14.
  zld F_54b60 D_54b60 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
  zld F_54b64 D_54b64 (sp - 16) F8. zld F_54b68 D_54b68 (sp - 24) F9. zld F_54b6c D_54b6c (sp - 32) F18. zld F_54b70 D_54b70 (sp - 40) F19.
  zstep F_54b74 D_54b74.
  stepret F_54b78 D_54b78 raw ltac:(gres; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_drain_rcy_fn : forall regs (M rom : word -> option byte) (raw : word) (sp gb msz x8 x9 x18 x19 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 10 = Z_to_bv 64 0x13e670 ->
  48 <= sp -> sp < 2 ^ 64 -> 2 ^ 28 < gb < 2 ^ 64 -> 0 <= msz < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= x19 < 2 ^ 64 ->
  0x698000 + 48 <= sp ->
  cellA M (0x13e670 + 184) 8 gb -> cellA M (0x13e670 + 64) 8 (2 ^ 28) -> cellA M (0x13e670 + 72) 8 msz -> cellA M (0x13e670 + 152) 4 0 -> wrA M (0x13e670 + 152) 4 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 -> cellA M (sp - 40) 8 x19 ->
  msteps ASEGS (mkst regs (0x54b5c : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 0)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 11 (Z_to_bv 64 msz)) 14 (Z_to_bv 64 65280)) 15 (Z_to_bv 64 256)) 16 (Z_to_bv 64 1304328)) 17 (Z_to_bv 64 0)) 18 (Z_to_bv 64 x18)) 19 (Z_to_bv 64 x19))
          (0x54c3c : word) (Wn 4 M (0x13e670 + 152) 256) rom).
Proof.
  intros regs M rom raw sp gb msz x8 x9 x18 x19 H2 H10 Hsp Hsp' Hgb Hmsz Hx8 Hx9 Hx18 Hx19 IMG Cgb Cmax Cmin Clk Wlk F1 F8 F9 F18 F19.
  zld F_54b0c D_54b0c (0x13e670 + 184) Cgb.
  zld F_54b10 D_54b10 (0x13e670 + 64) Cmax.
  zbft F_54b14 D_54b14.
  zstep F_54b18 D_54b18. zstep F_54b1c D_54b1c. zstep F_54b20 D_54b20.
  stepn F_54b24 D_54b24. rwH. zclosed (0x13e670 + 152).
  stepn F_54b28 D_54b28. rwH. zclosed 1.
  stepn F_54b2c D_54b2c. rwH. zclosed 8.
  stepn F_54b30 D_54b30. rwH. zclosed 65280.
  stepn F_54b34 D_54b34. rwH. zclosed 256.
  assert (Wlk' : wokA M (0x13e670 + 152) 4) by (apply (wr_wok _ _ _ _ Wlk); cbn; lia).
  zcas6 F_54b38 D_54b38 F_54b3c D_54b3c F_54b40 D_54b40 F_54b44 D_54b44 F_54b48 D_54b48 F_54b4c D_54b4c (0x13e670 + 152) 0 256 256 256 Clk Wlk'.
  zbft F_54b50 D_54b50.
  stepn F_54b54 D_54b54. rwH. zclosed 0.
  stepn F_54b58 D_54b58. rwH. zclosed 0.
  zbtk F_54b5c D_54b5c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cmin' : cellA X (0x13e670 + 72) 8 msz) by zcell; assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell;
    assert (F9' : cellA X (sp - 24) 8 x9) by zcell; assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell end.
  zld F_54b7c D_54b7c (0x13e670 + 72) Cmin'.
  zld F_54b80 D_54b80 (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
  zld F_54b84 D_54b84 (sp - 16) F8'. zld F_54b88 D_54b88 (sp - 24) F9'. zld F_54b8c D_54b8c (sp - 32) F18'. zld F_54b90 D_54b90 (sp - 40) F19'.
  zstep F_54b94 D_54b94.
  stepn F_54b98 D_54b98.
  zret.
Qed.

#[using="Type"] Lemma art_drain_mem_lock : forall (M : word -> option byte) sp raw regs c L F B bytes GL GB gbytes,
  0x698000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> (c + 32 <= 0x10000 \/ 0x698000 <= c) ->
  (GL <> 0 -> 0x698000 <= GB /\ GB + 8 < 2 ^ 64) ->
  cellA (art_drain_mem M sp raw regs c L F B bytes GL GB gbytes) (0x13e670 + 152) 4 0.
Proof.
  intros M sp raw regs c L F B bytes GL GB gbytes IMG Hsp' Hc Hc' Hci HGB.
  change (cellA (art_drain_mem M sp raw regs c L F B bytes GL GB gbytes) (0x13e670 + 152) 4 (0 + 256 * 0 + 65536 * 0)).
  apply cell4_join; [lia|lia|lia|lia|lia| | | ].
  - unfold art_drain_mem. apply cell_Wn_hit; [lia|cbn; lia].
  - unfold art_drain_mem. destruct (Z.eqb_spec GL 0) as [EG|NG].
    + do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x13e670 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
        destruct (cell4_split X (0x13e670 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & Cb1 & _) end. exact Cb1.
    + destruct (HGB NG) as (GB0 & GB1).
      do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x13e670 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
        destruct (cell4_split X (0x13e670 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & Cb1 & _) end. exact Cb1.
  - unfold art_drain_mem. destruct (Z.eqb_spec GL 0) as [EG|NG].
    + do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x13e670 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
        destruct (cell4_split X (0x13e670 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & _ & Cb2) end. exact Cb2.
    + destruct (HGB NG) as (GB0 & GB1).
      do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x13e670 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
        destruct (cell4_split X (0x13e670 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & _ & Cb2) end. exact Cb2.
Qed.

#[using="Type"] Lemma art_drain_nr_run : forall regs (M rom : word -> option byte) (raw : word) (sp c L F B bytes GL GB gbytes : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x13e670 -> getr regs 11 = Z_to_bv 64 c ->
  0x698000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> (c + 32 <= 0x10000 \/ 0x698000 <= c) -> apart (sp - 48) 48 c 32 ->
  1 <= L < 2 ^ 63 -> 0 <= F < 2 ^ 64 -> 0 <= B < 2 ^ 64 -> 0 <= bytes -> 0 <= gbytes -> gbytes + bytes <= 2 ^ 28 -> 0 <= GL -> GL + L < 2 ^ 63 ->
  (GL <> 0 -> 0x698000 <= GB /\ GB + 8 < 2 ^ 64 /\ apart (sp - 48) 48 GB 8 /\ apart c 32 GB 8 /\ wrA M GB 8) ->
  wrA M (sp - 48) 48 -> wrA M c 32 -> wrA M (0x13e670 + 152) 40 ->
  cellA M (0x13e670 + 152) 4 0 -> cellA M (0x13e670 + 64) 8 (2 ^ 28) ->
  cellA M c 8 L -> cellA M (c + 8) 8 F -> cellA M (c + 16) 8 B -> cellA M (c + 24) 8 bytes ->
  cellA M (0x13e670 + 160) 8 GL -> (GL <> 0 -> cellA M (0x13e670 + 176) 8 GB) -> cellA M (0x13e670 + 184) 8 gbytes ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x54a98 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(sp - 48, 48); (0x13e670 + 152, 16); (0x13e670 + 176, 16); (c, 32); ((if GL =? 0 then 0x13e670 + 168 else GB), 8)] M M'
    /\ cellA M' c 8 0 /\ cellA M' (c + 8) 8 0 /\ cellA M' (c + 16) 8 0 /\ cellA M' (c + 24) 8 0
    /\ cellA M' (0x13e670 + 160) 8 (GL + L) /\ cellA M' (0x13e670 + 176) 8 B /\ cellA M' (0x13e670 + 184) 8 (gbytes + bytes) /\ cellA M' (0x13e670 + 152) 4 0
    /\ (GL = 0 -> cellA M' (0x13e670 + 168) 8 F) /\ (GL <> 0 -> cellA M' GB 8 F).
Proof.
  intros regs M rom raw sp c L F B bytes GL GB gbytes H1 Hret H2 H10 H11 IMG Hsp' Hc Hc' Hci Ac HL HF HB Hby Hgb Hgb' HGL HGL' HGB W Wc Wq Clk Cmax CL CF CB Cby CGL CGB Cgb.
  destruct (art_drain_pre regs M rom raw sp c L F B bytes GL GB gbytes H1 H2 H10 H11 IMG Hsp' Hc Hc' Hci Ac HL HF HB Hby Hgb ltac:(lia) HGL HGL' HGB W Wc Wq Clk CL CF CB Cby CGL CGB Cgb)
    as (r1 & RUN1 & R2 & R10 & RK).
  set (M1 := art_drain_mem M sp raw regs c L F B bytes GL GB gbytes) in *.
  pose proof Ac as Xc. unfold apart in Xc.
  assert (FACTS : mem_grows M M1 /\ art_agree [(sp - 48, 48); (0x13e670 + 152, 16); (0x13e670 + 176, 16); (c, 32); ((if GL =? 0 then 0x13e670 + 168 else GB), 8)] M M1
            /\ cellA M1 c 8 0 /\ cellA M1 (c + 8) 8 0 /\ cellA M1 (c + 16) 8 0 /\ cellA M1 (c + 24) 8 0
            /\ cellA M1 (0x13e670 + 160) 8 (GL + L) /\ cellA M1 (0x13e670 + 176) 8 B /\ cellA M1 (0x13e670 + 184) 8 (gbytes + bytes)
            /\ (GL = 0 -> cellA M1 (0x13e670 + 168) 8 F) /\ (GL <> 0 -> cellA M1 GB 8 F)
            /\ cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
            /\ cellA M1 (sp - 40) 8 (U (getr regs 19)) /\ cellA M1 (0x13e670 + 64) 8 (2 ^ 28)).
  { unfold M1, art_drain_mem, art_drain_frame. destruct (Z.eqb_spec GL 0) as [EG|NG].
    - split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia|].
      repeat split; try (intros E; try contradiction); try zcell. rewrite EG. zcell.
    - destruct (HGB NG) as (GB0 & GB1 & AGs & AGc & WGB). unfold apart in AGs, AGc.
      split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia|].
      repeat split; try (intros E; try contradiction); try zcell. }
  destruct FACTS as (G1 & A1 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & F1 & F8 & F9 & F18 & F19 & Cmax').
  pose proof (art_drain_ret_fn r1 M1 rom raw sp (gbytes + bytes) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) R2 R10 Hret ltac:(lia) ltac:(lia) ltac:(lia)
                (u64_range _) (u64_range _) (u64_range _) (u64_range _) C7 Cmax' F1 F8 F9 F18 F19) as RUN2.
  eexists. exists M1. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split. { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres; first [apply Z_to_bv_bv_unsigned | apply RK; inl]. }
  split; [exact G1|]. split; [exact A1|].
  repeat (split; [assumption|]). split; [|split; assumption].
  unfold M1. apply art_drain_mem_lock; try assumption. intros NG. destruct (HGB NG) as (GB0 & GB1 & _). split; assumption.
Qed.
End FPX.
