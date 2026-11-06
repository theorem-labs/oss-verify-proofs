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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EbtLeaf EbtAllocG EbtPoison ArtRuns ArtRunsMem EbtFp EbtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3ef18_4052c.
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

Definition art_drain_frame (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18))) (sp - 40) (U (getr regs 19)).

Definition art_drain_mem (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) (c L F B bytes GL GB gbytes : Z) : word -> option byte :=
  let M2 := Wn 4 (art_drain_frame M sp raw regs) (0x142d70 + 152) 1 in
  let M3 := if GL =? 0 then Wn 8 (Wn 8 (Wn 8 M2 (0x142d70 + 176) B) (0x142d70 + 168) F) (0x142d70 + 160) L
            else Wn 8 (Wn 8 (Wn 8 M2 GB F) (0x142d70 + 160) (GL + L)) (0x142d70 + 176) B in
  Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M3 c 0) (c + 8) 0) (c + 16) 0) (0x142d70 + 184) (gbytes + bytes)) (c + 24) 0) (0x142d70 + 152) 0.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_drain_pre : forall regs (M rom : word -> option byte) (raw : word) (sp c L F B bytes GL GB gbytes : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x142d70 -> getr regs 11 = Z_to_bv 64 c ->
  0x69c000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> (c + 32 <= 0x10000 \/ 0x69c000 <= c) -> apart (sp - 48) 48 c 32 ->
  1 <= L < 2 ^ 63 -> 0 <= F < 2 ^ 64 -> 0 <= B < 2 ^ 64 -> 0 <= bytes -> 0 <= gbytes -> gbytes + bytes < 2 ^ 64 -> 0 <= GL -> GL + L < 2 ^ 63 ->
  (GL <> 0 -> 0x69c000 <= GB /\ GB + 8 < 2 ^ 64 /\ apart (sp - 48) 48 GB 8 /\ apart c 32 GB 8 /\ wrA M GB 8) ->
  wrA M (sp - 48) 48 -> wrA M c 32 -> wrA M (0x142d70 + 152) 40 ->
  cellA M (0x142d70 + 152) 4 0 ->
  cellA M c 8 L -> cellA M (c + 8) 8 F -> cellA M (c + 16) 8 B -> cellA M (c + 24) 8 bytes ->
  cellA M (0x142d70 + 160) 8 GL -> (GL <> 0 -> cellA M (0x142d70 + 176) 8 GB) -> cellA M (0x142d70 + 184) 8 gbytes ->
  exists regs', msteps ASEGS (mkst regs (0x552c0 : word) M rom) (mkst regs' (0x55384 : word) (art_drain_mem M sp raw regs c L F B bytes GL GB gbytes) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 10 = Z_to_bv 64 0x142d70
    /\ (forall r : reg, In r [1; 3; 4; 8; 9; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp c L F B bytes GL GB gbytes H1 H2 H10 H11 IMG Hsp' Hc Hc' Hci Ac HL HF HB Hby Hgb Hgb' HGL HGL' HGB W Wc Wq Clk CL CF CB Cby CGL CGB Cgb.
  destruct (Z.eq_dec GL 0) as [EG|NG].
  -
    eexists. split.
    {
    zstep F_55270 D_55270.
    zsd F_55274 D_55274 (sp - 8) (U raw) ltac:(rewok W). zsd F_55278 D_55278 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5527c D_5527c (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_55280 D_55280 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_55284 D_55284 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zstep F_55288 D_55288. zstep F_5528c D_5528c.
    stepn F_55290 D_55290. rwH. zclosed (0x142d70 + 152).
    zstep F_55294 D_55294.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x142d70 + 152) 4 0) by zcell; assert (Wlk' : wokA X (0x142d70 + 152) 4) by zwok end.
    zcas6 F_55298 D_55298 F_5529c D_5529c F_552a0 D_552a0 F_552a4 D_552a4 F_552a8 D_552a8 F_552ac D_552ac (0x142d70 + 152) 0 1 1 1 Clk' Wlk'.
    zbft F_552b0 D_552b0.
    stepn F_552b4 D_552b4. rwH. zclosed 0.
    zbft F_552b8 D_552b8.
    zstep F_552bc D_552bc.
    zbft F_552c0 D_552c0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell; assert (CGL' : cellA X (0x142d70 + 160) 8 GL) by zcell end.
    zld F_552c4 D_552c4 c CL'.
    zbft F_552c8 D_552c8.
    zld F_552cc D_552cc (0x142d70 + 160) CGL'.
    zbtk F_552d0 D_552d0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CB' : cellA X (c + 16) 8 B) by zcell; assert (CF' : cellA X (c + 8) 8 F) by zcell; assert (CL2 : cellA X c 8 L) by zcell end.
    zld F_552f4 D_552f4 (c + 16) CB'.
    zsd F_552f8 D_552f8 (0x142d70 + 176) B ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CF2 : cellA X (c + 8) 8 F) by zcell end.
    zld F_552fc D_552fc (c + 8) CF2.
    zsd F_55300 D_55300 (0x142d70 + 168) F ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL3 : cellA X c 8 L) by zcell end.
    zld F_55304 D_55304 c CL3.
    zsd F_55308 D_55308 (0x142d70 + 160) L ltac:(zwok').
    zsd F_5530c D_5530c c 0 ltac:(zwok'). zsd F_55310 D_55310 (c + 8) 0 ltac:(zwok'). zsd F_55314 D_55314 (c + 16) 0 ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell; assert (Cgb' : cellA X (0x142d70 + 184) 8 gbytes) by zcell end.
    zld F_55318 D_55318 (c + 24) Cby'.
    zld F_5531c D_5531c (0x142d70 + 184) Cgb'.
    zstep F_55320 D_55320.
    zsd F_55324 D_55324 (0x142d70 + 184) (gbytes + bytes) ltac:(zwok').
    zsd F_55328 D_55328 (c + 24) 0 ltac:(zwok').
    stepfence F_5532c D_5532c.
    zsb F_55330 D_55330 (0x142d70 + 152) 0 ltac:(zwok').
    unfold art_drain_mem, art_drain_frame. rewrite (proj2 (Z.eqb_eq GL 0) EG). apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity|reflexivity|zmem_eq]. }
    split; [gres; f_equal; lia|]. split; [gres; exact H10|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  -
    destruct (HGB NG) as (GB0 & GB1 & AGs & AGc & WGB). specialize (CGB NG).
    eexists. split.
    {
    zstep F_55270 D_55270.
    zsd F_55274 D_55274 (sp - 8) (U raw) ltac:(rewok W). zsd F_55278 D_55278 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
    zsd F_5527c D_5527c (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_55280 D_55280 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
    zsd F_55284 D_55284 (sp - 40) (U (getr regs 19)) ltac:(rewok W).
    zstep F_55288 D_55288. zstep F_5528c D_5528c.
    stepn F_55290 D_55290. rwH. zclosed (0x142d70 + 152).
    zstep F_55294 D_55294.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (0x142d70 + 152) 4 0) by zcell; assert (Wlk' : wokA X (0x142d70 + 152) 4) by zwok end.
    zcas6 F_55298 D_55298 F_5529c D_5529c F_552a0 D_552a0 F_552a4 D_552a4 F_552a8 D_552a8 F_552ac D_552ac (0x142d70 + 152) 0 1 1 1 Clk' Wlk'.
    zbft F_552b0 D_552b0.
    stepn F_552b4 D_552b4. rwH. zclosed 0.
    zbft F_552b8 D_552b8.
    zstep F_552bc D_552bc.
    zbft F_552c0 D_552c0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CL' : cellA X c 8 L) by zcell; assert (CGL' : cellA X (0x142d70 + 160) 8 GL) by zcell end.
    zld F_552c4 D_552c4 c CL'.
    zbft F_552c8 D_552c8.
    zld F_552cc D_552cc (0x142d70 + 160) CGL'.
    zbft F_552d0 D_552d0.
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (CGB' : cellA X (0x142d70 + 176) 8 GB) by zcell; assert (CB' : cellA X (c + 16) 8 B) by zcell; assert (CF' : cellA X (c + 8) 8 F) by zcell end.
    zld F_552d4 D_552d4 (0x142d70 + 176) CGB'.
    zld F_552d8 D_552d8 (c + 8) CF'.
    zld F_552dc D_552dc (c + 16) CB'.
    zstep F_552e0 D_552e0.
    zsd F_552e4 D_552e4 GB F ltac:(zwok').
    zsd F_552e8 D_552e8 (0x142d70 + 160) (GL + L) ltac:(zwok').
    zsd F_552ec D_552ec (0x142d70 + 176) B ltac:(zwok').
    stepn F_552f0 D_552f0.
    zsd F_5530c D_5530c c 0 ltac:(zwok'). zsd F_55310 D_55310 (c + 8) 0 ltac:(zwok'). zsd F_55314 D_55314 (c + 16) 0 ltac:(zwok').
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cby' : cellA X (c + 24) 8 bytes) by zcell; assert (Cgb' : cellA X (0x142d70 + 184) 8 gbytes) by zcell end.
    zld F_55318 D_55318 (c + 24) Cby'.
    zld F_5531c D_5531c (0x142d70 + 184) Cgb'.
    zstep F_55320 D_55320.
    zsd F_55324 D_55324 (0x142d70 + 184) (gbytes + bytes) ltac:(zwok').
    zsd F_55328 D_55328 (c + 24) 0 ltac:(zwok').
    stepfence F_5532c D_5532c.
    zsb F_55330 D_55330 (0x142d70 + 152) 0 ltac:(zwok').
    unfold art_drain_mem, art_drain_frame. rewrite (proj2 (Z.eqb_neq GL 0) NG). apply art_msteps_of_eq. apply art_mkst_eq; [reflexivity|reflexivity|zmem_eq]. }
    split; [gres; f_equal; lia|]. split; [gres; exact H10|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_drain_ret_fn : forall regs (M rom : word -> option byte) (raw : word) (sp gb x8 x9 x18 x19 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 10 = Z_to_bv 64 0x142d70 -> ret_ok raw ->
  48 <= sp -> sp < 2 ^ 64 -> 0 <= gb <= 2 ^ 28 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= x19 < 2 ^ 64 ->
  cellA M (0x142d70 + 184) 8 gb -> cellA M (0x142d70 + 64) 8 (2 ^ 28) ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 -> cellA M (sp - 40) 8 x19 ->
  msteps ASEGS (mkst regs (0x55384 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 11 (Z_to_bv 64 gb)) 14 (Z_to_bv 64 (2 ^ 28))) 18 (Z_to_bv 64 x18)) 19 (Z_to_bv 64 x19))
          raw M rom).
Proof.
  intros regs M rom raw sp gb x8 x9 x18 x19 H2 H10 Hret Hsp Hsp' Hgb Hx8 Hx9 Hx18 Hx19 Cgb Cmax F1 F8 F9 F18 F19.
  zld F_55334 D_55334 (0x142d70 + 184) Cgb.
  zld F_55338 D_55338 (0x142d70 + 64) Cmax.
  zbtk F_5533c D_5533c.
  zld F_55388 D_55388 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
  zld F_5538c D_5538c (sp - 16) F8. zld F_55390 D_55390 (sp - 24) F9. zld F_55394 D_55394 (sp - 32) F18. zld F_55398 D_55398 (sp - 40) F19.
  zstep F_5539c D_5539c.
  stepret F_553a0 D_553a0 raw ltac:(gres; reflexivity).
  zret.
Qed.

#[using="Type"] Lemma art_drain_rcy_fn : forall regs (M rom : word -> option byte) (raw : word) (sp gb msz x8 x9 x18 x19 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 10 = Z_to_bv 64 0x142d70 ->
  48 <= sp -> sp < 2 ^ 64 -> 2 ^ 28 < gb < 2 ^ 64 -> 0 <= msz < 2 ^ 64 -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 -> 0 <= x19 < 2 ^ 64 ->
  0x69c000 + 48 <= sp ->
  cellA M (0x142d70 + 184) 8 gb -> cellA M (0x142d70 + 64) 8 (2 ^ 28) -> cellA M (0x142d70 + 72) 8 msz -> cellA M (0x142d70 + 152) 4 0 -> wrA M (0x142d70 + 152) 4 ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 x8 -> cellA M (sp - 24) 8 x9 -> cellA M (sp - 32) 8 x18 -> cellA M (sp - 40) 8 x19 ->
  msteps ASEGS (mkst regs (0x55384 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 5 (Z_to_bv 64 0)) 8 (Z_to_bv 64 x8)) 9 (Z_to_bv 64 x9)) 11 (Z_to_bv 64 msz)) 14 (Z_to_bv 64 65280)) 15 (Z_to_bv 64 256)) 16 (Z_to_bv 64 1322504)) 17 (Z_to_bv 64 0)) 18 (Z_to_bv 64 x18)) 19 (Z_to_bv 64 x19))
          (0x55464 : word) (Wn 4 M (0x142d70 + 152) 256) rom).
Proof.
  intros regs M rom raw sp gb msz x8 x9 x18 x19 H2 H10 Hsp Hsp' Hgb Hmsz Hx8 Hx9 Hx18 Hx19 IMG Cgb Cmax Cmin Clk Wlk F1 F8 F9 F18 F19.
  zld F_55334 D_55334 (0x142d70 + 184) Cgb.
  zld F_55338 D_55338 (0x142d70 + 64) Cmax.
  zbft F_5533c D_5533c.
  zstep F_55340 D_55340. zstep F_55344 D_55344. zstep F_55348 D_55348.
  stepn F_5534c D_5534c. rwH. zclosed (0x142d70 + 152).
  stepn F_55350 D_55350. rwH. zclosed 1.
  stepn F_55354 D_55354. rwH. zclosed 8.
  stepn F_55358 D_55358. rwH. zclosed 65280.
  stepn F_5535c D_5535c. rwH. zclosed 256.
  assert (Wlk' : wokA M (0x142d70 + 152) 4) by (apply (wr_wok _ _ _ _ Wlk); cbn; lia).
  zcas6 F_55360 D_55360 F_55364 D_55364 F_55368 D_55368 F_5536c D_5536c F_55370 D_55370 F_55374 D_55374 (0x142d70 + 152) 0 256 256 256 Clk Wlk'.
  zbft F_55378 D_55378.
  stepn F_5537c D_5537c. rwH. zclosed 0.
  stepn F_55380 D_55380. rwH. zclosed 0.
  zbtk F_55384 D_55384.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Cmin' : cellA X (0x142d70 + 72) 8 msz) by zcell; assert (F1' : cellA X (sp - 8) 8 (U raw)) by zcell; assert (F8' : cellA X (sp - 16) 8 x8) by zcell;
    assert (F9' : cellA X (sp - 24) 8 x9) by zcell; assert (F18' : cellA X (sp - 32) 8 x18) by zcell; assert (F19' : cellA X (sp - 40) 8 x19) by zcell end.
  zld F_553a4 D_553a4 (0x142d70 + 72) Cmin'.
  zld F_553a8 D_553a8 (sp - 8) F1'. rewrite Z_to_bv_bv_unsigned.
  zld F_553ac D_553ac (sp - 16) F8'. zld F_553b0 D_553b0 (sp - 24) F9'. zld F_553b4 D_553b4 (sp - 32) F18'. zld F_553b8 D_553b8 (sp - 40) F19'.
  zstep F_553bc D_553bc.
  stepn F_553c0 D_553c0.
  zret.
Qed.

#[using="Type"] Lemma art_drain_mem_lock : forall (M : word -> option byte) sp raw regs c L F B bytes GL GB gbytes,
  0x69c000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> (c + 32 <= 0x10000 \/ 0x69c000 <= c) ->
  (GL <> 0 -> 0x69c000 <= GB /\ GB + 8 < 2 ^ 64) ->
  cellA (art_drain_mem M sp raw regs c L F B bytes GL GB gbytes) (0x142d70 + 152) 4 0.
Proof.
  intros M sp raw regs c L F B bytes GL GB gbytes IMG Hsp' Hc Hc' Hci HGB.
  change (cellA (art_drain_mem M sp raw regs c L F B bytes GL GB gbytes) (0x142d70 + 152) 4 (0 + 256 * 0 + 65536 * 0)).
  apply cell4_join; [lia|lia|lia|lia|lia| | | ].
  - unfold art_drain_mem. apply cell_Wn_hit; [lia|cbn; lia].
  - unfold art_drain_mem. destruct (Z.eqb_spec GL 0) as [EG|NG].
    + do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x142d70 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
        destruct (cell4_split X (0x142d70 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & Cb1 & _) end. exact Cb1.
    + destruct (HGB NG) as (GB0 & GB1).
      do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x142d70 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
        destruct (cell4_split X (0x142d70 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & Cb1 & _) end. exact Cb1.
  - unfold art_drain_mem. destruct (Z.eqb_spec GL 0) as [EG|NG].
    + do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x142d70 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
        destruct (cell4_split X (0x142d70 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & _ & Cb2) end. exact Cb2.
    + destruct (HGB NG) as (GB0 & GB1).
      do 9 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]).
      match goal with |- cellA ?X _ _ _ => assert (C1 : cellA X (0x142d70 + 152) 4 1) by (apply cell_Wn_hit; [lia|cbn; lia]);
        destruct (cell4_split X (0x142d70 + 152) 1 ltac:(lia) ltac:(lia) ltac:(lia) C1) as (_ & _ & Cb2) end. exact Cb2.
Qed.

#[using="Type"] Lemma art_drain_nr_run : forall regs (M rom : word -> option byte) (raw : word) (sp c L F B bytes GL GB gbytes : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0x142d70 -> getr regs 11 = Z_to_bv 64 c ->
  0x69c000 + 48 <= sp -> sp < 2 ^ 64 -> 0 <= c -> c + 32 < 2 ^ 64 -> (c + 32 <= 0x10000 \/ 0x69c000 <= c) -> apart (sp - 48) 48 c 32 ->
  1 <= L < 2 ^ 63 -> 0 <= F < 2 ^ 64 -> 0 <= B < 2 ^ 64 -> 0 <= bytes -> 0 <= gbytes -> gbytes + bytes <= 2 ^ 28 -> 0 <= GL -> GL + L < 2 ^ 63 ->
  (GL <> 0 -> 0x69c000 <= GB /\ GB + 8 < 2 ^ 64 /\ apart (sp - 48) 48 GB 8 /\ apart c 32 GB 8 /\ wrA M GB 8) ->
  wrA M (sp - 48) 48 -> wrA M c 32 -> wrA M (0x142d70 + 152) 40 ->
  cellA M (0x142d70 + 152) 4 0 -> cellA M (0x142d70 + 64) 8 (2 ^ 28) ->
  cellA M c 8 L -> cellA M (c + 8) 8 F -> cellA M (c + 16) 8 B -> cellA M (c + 24) 8 bytes ->
  cellA M (0x142d70 + 160) 8 GL -> (GL <> 0 -> cellA M (0x142d70 + 176) 8 GB) -> cellA M (0x142d70 + 184) 8 gbytes ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x552c0 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M' /\ art_agree [(sp - 48, 48); (0x142d70 + 152, 16); (0x142d70 + 176, 16); (c, 32); ((if GL =? 0 then 0x142d70 + 168 else GB), 8)] M M'
    /\ cellA M' c 8 0 /\ cellA M' (c + 8) 8 0 /\ cellA M' (c + 16) 8 0 /\ cellA M' (c + 24) 8 0
    /\ cellA M' (0x142d70 + 160) 8 (GL + L) /\ cellA M' (0x142d70 + 176) 8 B /\ cellA M' (0x142d70 + 184) 8 (gbytes + bytes) /\ cellA M' (0x142d70 + 152) 4 0
    /\ (GL = 0 -> cellA M' (0x142d70 + 168) 8 F) /\ (GL <> 0 -> cellA M' GB 8 F).
Proof.
  intros regs M rom raw sp c L F B bytes GL GB gbytes H1 Hret H2 H10 H11 IMG Hsp' Hc Hc' Hci Ac HL HF HB Hby Hgb Hgb' HGL HGL' HGB W Wc Wq Clk Cmax CL CF CB Cby CGL CGB Cgb.
  destruct (art_drain_pre regs M rom raw sp c L F B bytes GL GB gbytes H1 H2 H10 H11 IMG Hsp' Hc Hc' Hci Ac HL HF HB Hby Hgb ltac:(lia) HGL HGL' HGB W Wc Wq Clk CL CF CB Cby CGL CGB Cgb)
    as (r1 & RUN1 & R2 & R10 & RK).
  set (M1 := art_drain_mem M sp raw regs c L F B bytes GL GB gbytes) in *.
  pose proof Ac as Xc. unfold apart in Xc.
  assert (FACTS : mem_grows M M1 /\ art_agree [(sp - 48, 48); (0x142d70 + 152, 16); (0x142d70 + 176, 16); (c, 32); ((if GL =? 0 then 0x142d70 + 168 else GB), 8)] M M1
            /\ cellA M1 c 8 0 /\ cellA M1 (c + 8) 8 0 /\ cellA M1 (c + 16) 8 0 /\ cellA M1 (c + 24) 8 0
            /\ cellA M1 (0x142d70 + 160) 8 (GL + L) /\ cellA M1 (0x142d70 + 176) 8 B /\ cellA M1 (0x142d70 + 184) 8 (gbytes + bytes)
            /\ (GL = 0 -> cellA M1 (0x142d70 + 168) 8 F) /\ (GL <> 0 -> cellA M1 GB 8 F)
            /\ cellA M1 (sp - 8) 8 (U raw) /\ cellA M1 (sp - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 24) 8 (U (getr regs 9)) /\ cellA M1 (sp - 32) 8 (U (getr regs 18))
            /\ cellA M1 (sp - 40) 8 (U (getr regs 19)) /\ cellA M1 (0x142d70 + 64) 8 (2 ^ 28)).
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
