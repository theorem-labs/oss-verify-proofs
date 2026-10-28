(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRop GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptBordSegs O23LeptRbord.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptErr V23LeptUb V23_code_port_rbord.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
(* [comment removed for export] *)
Ltac ldcell F D a z :=
  stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z)
    ltac:(rdn_addr a; rdn_chain) ltac:(apply bytes_le_to_Z_4; unorm; lia);
  rewrite ?(v_lw_small z) by lia.
Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM, u_Z2bv by lia; rewrite EQ; reflexivity).
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac condG := first [ condR | condZ ].

Section Rbord.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section SegsSpp.
Variable rom : word -> option byte.
  Lemma pixCopySpp_run : forall regs m (pixd pixs : Z) (vs vd : pixv) (ret : word),
    (1 <= pixs)%Z -> (1 <= pixd)%Z -> pixs <> pixd -> (pixs mod 8 = 0)%Z -> (pixd mod 8 = 0)%Z ->
    PIXat m pixs vs -> PIXat m pixd vd -> (1 <= p_spp vs)%Z ->
    store_ok SEGS m (Z_to_bv 64 pixd) 64 = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x6e360 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 (pixd + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (p_spp vs)))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixd pixs vs vd ret Hps Hpd NE ALs ALd PXs PXd Hspp SOKd Hret H1 H10 H11.
    pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _). pose proof (wf_spp _ WFs) as Rspp.
    pose proof (PIX_rd_spp SEGS _ _ _ PXs) as Cspp.
    eexists. split.
    - stepb_ft F_6e360 D_6e360 ltac:(condZ).
      stepb_ft F_6e364 D_6e364 ltac:(condZ).
      stepb_ft F_6e368 D_6e368 ltac:(condZ).
      guard8 F_6e36c D_6e36c ALs. stepb_ft F_6e370 D_6e370 ltac:(condZ).
      stepLD F_6e374 D_6e374 (Z_to_le_bytes 4 (p_spp vs)) (Z_to_bv 64 (p_spp vs)) ltac:(addr_norm; exact Cspp) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_spp vs)) by lia.
      stepb_ft F_6e378 D_6e378 ltac:(condZ).
      guard8 F_6e37c D_6e37c ALd. stepb_ft F_6e380 D_6e380 ltac:(condZ).
      stepST F_6e384 D_6e384 (Z_to_bv 64 (pixd + 12)) (Z_to_bv 64 (p_spp vs)) ltac:(sok_in SOKd).
      sn F_6e388 D_6e388. sn F_6e430 D_6e430.
      stepret F_6e434 D_6e434 ret ltac:(exact H1).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsSpp.

Section SegsR.
Variable rom : word -> option byte.

  Ltac rb_prologue s ret regs SOK :=
    zv F_71224 D_71224 (Z_to_bv 64 (s - 96));
    stepST F_71228 D_71228 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
    stepST F_7122c D_7122c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
    stepST F_71230 D_71230 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
    stepST F_71234 D_71234 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
    stepST F_71238 D_71238 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK);
    stepST F_7123c D_7123c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK);
    stepST F_71240 D_71240 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK);
    stepST F_71244 D_71244 (Z_to_bv 64 (s - 64)) (getr regs 23) ltac:(sok_in SOK).

  (* [comment removed for export] *)
  Lemma rb_A : forall regs m (s pixs left right top bot : Z) (vs : pixv) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 96 \/ s <= pixs)%Z ->
    (0 <= left <= 64)%Z -> (0 <= right <= 64)%Z -> (0 <= top <= 64)%Z -> (0 <= bot <= 64)%Z ->
    (1 <= p_w vs <= 20000)%Z -> (1 <= p_h vs <= 20000)%Z -> (1 <= p_w vs - left - right)%Z -> (1 <= p_h vs - top - bot)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot ->
    exists regs',
      msteps SEGS (mkst regs (0x71224 : word) m rom)
                  (mkst regs' (0x6da3c : word) (DIMS (FRR m s ret regs) (s - 68) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x712d8
      /\ getr regs' 10 = Z_to_bv 64 (p_w vs - left - right) /\ getr regs' 11 = Z_to_bv 64 (p_h vs - top - bot) /\ getr regs' 12 = Z_to_bv 64 (p_d vs)
      /\ getr regs' 8 = Z_to_bv 64 top /\ getr regs' 9 = Z_to_bv 64 left /\ getr regs' 18 = Z_to_bv 64 pixs
      /\ getr regs' 19 = Z_to_bv 64 (p_w vs - left - right) /\ getr regs' 20 = Z_to_bv 64 (p_h vs - top - bot)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s pixs left right top bot vs ret Hs Hs64 Hs16 Hp ALp PX DJ Hl Hr Ht Hb Hw Hh Hwd Hhd SOK H2 H1 H10 H11 H12 H13 H14.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof (lor_small right left 31 ltac:(lia) ltac:(lia) ltac:(lia)) as O1.
    pose proof (lor_small top bot 31 ltac:(lia) ltac:(lia) ltac:(lia)) as O2.
    pose proof (lor_small _ _ 31 ltac:(lia) O1 O2) as O3.
    assert (SL68 : ((s - 68) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
    assert (SL72 : ((s - 72) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
    assert (SL76 : ((s - 76) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
    assert (PXk : forall M a bs, PIXat M pixs vs -> (s - 96 <= a)%Z -> (a + Z.of_nat (length bs) <= s)%Z -> PIXat (wbytes M (Z_to_bv 64 a) bs) pixs vs).
    { intros M a bs P Ha Hb'. apply PIXat_out; [exact P | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia]. }
    unfold DIMS, FRR in *. eexists. split.
    - rb_prologue s ret regs SOK.
      stepb_ft F_71248 D_71248 ltac:(condZ).
      sn F_7124c D_7124c. sn F_71250 D_71250. sn F_71254 D_71254. sn F_71258 D_71258.
      stepat F_7125c D_7125c (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_71260 D_71260 (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_71264 D_71264 (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_71268 D_71268 ltac:(condZ).
      zv F_7126c D_7126c (Z_to_bv 64 (s - 68)). zv F_71270 D_71270 (Z_to_bv 64 (s - 72)). zv F_71274 D_71274 (Z_to_bv 64 (s - 76)).
      sn F_71278 D_71278. sn F_7127c D_7127c.
      zand F_6e2a4 D_6e2a4 andi_3 SL68. stepb_ft F_6e2a8 D_6e2a8 ltac:(condZ). stepb_ft F_6e2ac D_6e2ac ltac:(condR).
      stepST F_6e2b0 D_6e2b0 (Z_to_bv 64 (s - 68)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_6e2b4 D_6e2b4 andi_3 SL72. stepb_ft F_6e2b8 D_6e2b8 ltac:(condZ). stepb_ft F_6e2bc D_6e2bc ltac:(condR).
      stepST F_6e2c0 D_6e2c0 (Z_to_bv 64 (s - 68 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_6e2c4 D_6e2c4 andi_3 SL76. stepb_ft F_6e2c8 D_6e2c8 ltac:(condZ). stepb_ft F_6e2cc D_6e2cc ltac:(condR).
      stepST F_6e2d0 D_6e2d0 (Z_to_bv 64 (s - 68 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_6e2d4 D_6e2d4 ltac:(condZ).
      zand F_6e2d8 D_6e2d8 andi_7 ALp.
      stepb_ft F_6e2dc D_6e2dc ltac:(condZ). sn F_6e2e0 D_6e2e0. stepb_ft F_6e2e4 D_6e2e4 ltac:(condR).
      stepLD F_6e2e8 D_6e2e8 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_6e2ec D_6e2ec (Z_to_bv 64 (s - 68)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_6e2f0 D_6e2f0 ltac:(condZ). sn F_6e2f4 D_6e2f4. stepb_ft F_6e2f8 D_6e2f8 ltac:(condR).
      stepLD F_6e2fc D_6e2fc (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_6e300 D_6e300 (Z_to_bv 64 (s - 68 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      stepb_ft F_6e304 D_6e304 ltac:(condZ). sn F_6e308 D_6e308. stepb_ft F_6e30c D_6e30c ltac:(condR).
      stepLD F_6e310 D_6e310 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_6e314 D_6e314 (Z_to_bv 64 (s - 68 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_6e318 D_6e318.
      stepret F_6e31c D_6e31c (0x71280 : word) ltac:(bveq).
      ldcell F_71280 D_71280 (s - 68)%Z (p_w vs).
      sn F_71284 D_71284. fixv (Z_to_bv 64 (p_w vs - left)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_71288 D_71288. fixv (Z_to_bv 64 (p_w vs - left)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_7128c D_7128c ltac:(condG).
      sn F_71290 D_71290. fixv (Z_to_bv 64 (p_w vs - left)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_71294 D_71294. fixv (Z_to_bv 64 (p_w vs - left - right)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      sn F_71298 D_71298. fixv (Z_to_bv 64 (p_w vs - left - right)) ltac:(rewrite zbv_sub; reflexivity).
      stepb_ft F_7129c D_7129c ltac:(condG).
      ldcell F_712a0 D_712a0 (s - 68 - 4)%Z (p_h vs).
      sn F_712a4 D_712a4. fixv (Z_to_bv 64 (p_h vs - top)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_712a8 D_712a8. fixv (Z_to_bv 64 (p_h vs - top)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_712ac D_712ac ltac:(condG).
      sn F_712b0 D_712b0. fixv (Z_to_bv 64 (p_h vs - top)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_712b4 D_712b4. fixv (Z_to_bv 64 (p_h vs - top - bot)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      sn F_712b8 D_712b8. fixv (Z_to_bv 64 (p_h vs - top - bot)) ltac:(rewrite zbv_sub; reflexivity).
      stepb_ft F_712bc D_712bc ltac:(condG).
      stepb_ft F_712c0 D_712c0 ltac:(condZ).
      stepb_ft F_712c4 D_712c4 ltac:(condZ).
      ldcell F_712c8 D_712c8 (s - 68 - 8)%Z (p_d vs).
      sn F_712cc D_712cc. sn F_712d0 D_712d0. sn F_712d4 D_712d4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_N1 : forall regs m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x71224 : word) m rom) (mkst regs' (0x71370 : word) (FRR m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96)
      /\ regs_agree (fun r => In r [2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10. unfold FRR. eexists. split.
    - rb_prologue s ret regs SOK.
      stepb_tk F_71248 D_71248 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_N2 : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameR s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x71370 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10355 /\ getr regs' 11 = Z_to_bv 64 0x183fc
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Rg Rs CE H2. unfold frameR in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    eexists. split.
    - sn F_71370 D_71370.
      stepLD F_71374 D_71374 (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_71378 D_71378 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_7137c D_7137c. stepb_ft F_71380 D_71380 ltac:(condZ).
      sn F_71384 D_71384. sn F_71388 D_71388. sn F_7138c D_7138c. sn F_71390 D_71390. sn F_71394 D_71394.
      sn F_713bc D_713bc.
      stepLD8 F_713c0 D_713c0 ret. stepLD8 F_713c4 D_713c4 (getr r0 8). stepLD8 F_713c8 D_713c8 (getr r0 9).
      stepLD8 F_713cc D_713cc (getr r0 18). stepLD8 F_713d0 D_713d0 (getr r0 19). stepLD8 F_713d4 D_713d4 (getr r0 20).
      stepLD8 F_713d8 D_713d8 (getr r0 21). stepLD8 F_713dc D_713dc (getr r0 23).
      zv F_713e0 D_713e0 (Z_to_bv 64 s). sn F_713e4 D_713e4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x712d8 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x71464 /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x183fc /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_712d8 D_712d8 ltac:(condZ).
      sn F_71438 D_71438.
      stepLD F_7143c D_7143c (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_71440 D_71440 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_71444 D_71444. stepb_ft F_71448 D_71448 ltac:(condZ).
      sn F_7144c D_7144c. sn F_71450 D_71450. sn F_71454 D_71454. sn F_71458 D_71458. sn F_7145c D_7145c. sn F_71460 D_71460.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_E : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameR s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x7146c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Hret CE H2. unfold frameR in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    eexists. split.
    - stepLD8 F_7146c D_7146c ret. stepLD8 F_71470 D_71470 (getr r0 8). stepLD8 F_71474 D_71474 (getr r0 9).
      stepLD8 F_71478 D_71478 (getr r0 18). stepLD8 F_7147c D_7147c (getr r0 19). stepLD8 F_71480 D_71480 (getr r0 20).
      stepLD8 F_71484 D_71484 (getr r0 21). stepLD8 F_71488 D_71488 (getr r0 23).
      zv F_7148c D_7148c (Z_to_bv 64 s). stepret F_71490 D_71490 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  Lemma rb_F2 : forall regs m, exists regs',
      msteps SEGS (mkst regs (0x71464 : word) m rom) (mkst regs' (0x7146c : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_71464 D_71464; apply mst_refl | solve_regs_agree]. Qed.

  (* [comment removed for export] *)
  Lemma rb_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x712d8 : word) m rom) (mkst regs' (0x6e43c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x712e8 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 21 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 21]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H18. eexists. split.
    - stepb_ft F_712d8 D_712d8 ltac:(condZ).
      sn F_712dc D_712dc. sn F_712e0 D_712e0. sn F_712e4 D_712e4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma rb_B2 : forall regs m (pixd pixs : Z),
    getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x712e8 : word) m rom) (mkst regs' (0x6e360 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x712f4 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H21 H18. eexists. split.
    - sn F_712e8 D_712e8. sn F_712ec D_712ec. sn F_712f0 D_712f0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma rb_B3 : forall regs m (pixd pixs : Z),
    getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x712f4 : word) m rom) (mkst regs' (0x6e4cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x71300 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H21 H18. eexists. split.
    - sn F_712f4 D_712f4. sn F_712f8 D_712f8. sn F_712fc D_712fc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_R : forall regs m (s pixd pixs left top wd hd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs -> getr regs 9 = Z_to_bv 64 left ->
    getr regs 8 = Z_to_bv 64 top -> getr regs 19 = Z_to_bv 64 wd -> getr regs 20 = Z_to_bv 64 hd ->
    exists regs',
      msteps SEGS (mkst regs (0x71300 : word) m rom)
                  (mkst regs' (0x7f13c : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 top))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x7132c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 left /\ getr regs' 23 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 23]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top wd hd Hs Hs64 SOK H2 H21 H18 H9 H8 H19 H20. eexists. split.
    - sn F_71300 D_71300.
      stepST F_71304 D_71304 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 top) ltac:(sok_in SOK).
      sn F_71308 D_71308. sn F_7130c D_7130c. sn F_71310 D_71310. sn F_71314 D_71314. sn F_71318 D_71318. sn F_7131c D_7131c.
      sn F_71320 D_71320. sn F_71324 D_71324. sn F_71328 D_71328. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_D : forall regs m (pixs pixd : Z) (vs : pixv),
    (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> (p_d vs = 1 \/ p_d vs = 8)%Z ->
    getr regs 18 = Z_to_bv 64 pixs -> getr regs 23 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x7132c : word) m rom) (mkst regs' (0x7146c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixs pixd vs Hp ALp PX Hd H18 H23. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd.
    eexists. split.
    - sn F_7132c D_7132c. sn F_71330 D_71330.
      stepb_ft F_6f114 D_6f114 ltac:(condZ).
      zand F_6f118 D_6f118 andi_7 ALp. stepb_ft F_6f11c D_6f11c ltac:(condR).
      stepLD F_6f120 D_6f120 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepret F_6f124 D_6f124 (0x71334 : word) ltac:(bveq).
      sn F_71334 D_71334.
      stepb_tk F_71338 D_71338 ltac:(condZ).
      sn F_71368 D_71368. sn F_7136c D_7136c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsR.

(* [comment removed for export] *)
Definition rbfr (m : word -> option byte) (s : Z) (ret : word) (r0 : bvmap 5 word) (w h d : Z) : Prop :=
  cellsZ m (frameR s ret r0) /\
  rdn SEGS m (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  rdn SEGS m (Z_to_bv 64 (s - 72)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) /\
  rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)).

Lemma cells_FRR : forall m s ret regs, (96 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FRR m s ret regs) (frameR s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold frameR, FRR. cbn [cellsZ]. repeat split; rdn_solve. Qed.

Lemma rbfr_init : forall m s ret regs w h d, (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rbfr (DIMS (FRR m s ret regs) (s - 68) w h d) s ret regs w h d.
Proof.
  intros m s ret regs w h d Hs Hs64. unfold rbfr. split.
  - apply (cellsZ_out (FRR m s ret regs) _ (s - 76) (s - 64)).
    + intros x Hx. apply DIMS_out; lia.
    + eapply Forall_impl; [|exact (frameR_bounds s ret regs Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
    + apply cells_FRR; lia.
  - unfold DIMS. replace (s - 72)%Z with (s - 68 - 4)%Z by lia. replace (s - 76)%Z with (s - 68 - 8)%Z by lia.
    repeat split; rdn_chain.
Qed.

Lemma rbfr_frm : forall C s' m m' s ret r0 w h d, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 76)%Z -> (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rbfr m s ret r0 w h d -> rbfr m' s ret r0 w h d.
Proof.
  intros C s' m m' s ret r0 w h d CK F H1 H2 Hs Hs64 (CE & Rw & Rh & Rd). unfold rbfr.
  rewrite !(FRM_rdn16 C s' m m' _ 4 CK F) by (cbn; lia). split; [| repeat split; assumption].
  apply (cellsZ_frm C s' m m' _ CK F H1); [|exact CE].
  eapply Forall_impl; [|exact (frameR_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.

Lemma rbfr_out : forall m m' (lo hi : Z) s ret r0 w h d, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 76 \/ s <= lo)%Z -> (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  rbfr m s ret r0 w h d -> rbfr m' s ret r0 w h d.
Proof.
  intros m m' lo hi s ret r0 w h d OUT Hd Hs Hs64 (CE & Rw & Rh & Rd). unfold rbfr.
  split; [| repeat split; (eapply (rdn_after m m' lo hi); [exact OUT | lia | cbn; lia | cbn; lia | assumption])].
  apply (cellsZ_out m m' lo hi _ OUT); [|exact CE].
  eapply Forall_impl; [|exact (frameR_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.

Lemma str_pixRemoveBorderGeneral : str16 0x183fc 22.
Proof. str16_tac. Qed.
Lemma str_msg_pixs_undef : str16 0x10355 16.
Proof. str16_tac. Qed.

(* [comment removed for export] *)
Section SegsW.
Variable rom : word -> option byte.
  Lemma rbw_A : forall regs m (pixs npix : Z),
    (1 <= pixs < 2 ^ 64)%Z -> (1 <= npix < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 npix ->
    exists regs',
      msteps SEGS (mkst regs (0x711d4 : word) m rom) (mkst regs' (0x71224 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 npix /\ getr regs' 13 = Z_to_bv 64 npix /\ getr regs' 14 = Z_to_bv 64 npix
      /\ regs_agree (fun r => In r [12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m pixs npix Hp Hn H10 H11. eexists. split.
    - stepb_ft F_711d4 D_711d4 ltac:(condZ).
      stepb_ft F_711d8 D_711d8 ltac:(condZ).
      sn F_711dc D_711dc. sn F_711e0 D_711e0. sn F_711e4 D_711e4. sn F_711e8 D_711e8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsW.

End Rbord.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
