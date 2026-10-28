(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib LeptRop.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptPixHdr V2LeptPixCreate V2LeptRop_iface V2LeptGrayA V2LeptUb V2_code_pixAddBorderGeneral V2_code_pixGetDimensions.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require LiaFast.
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

Section GrayBorder.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition FRA (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)).
(* [comment removed for export] *)
Definition DIMS (m : word -> option byte) (a : Z) (w h d : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 a) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (a - 4)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (a - 8)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 a) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (a - 4)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
    (Z_to_bv 64 (a - 8)) (word_to_le_bytes 4 (Z_to_bv 64 d)).

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma ab_A : forall regs m (s pixs left right top bot val : Z) (vs : pixv) (ret : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 112 \/ s <= pixs)%Z ->
    (0 <= left <= 64)%Z -> (0 <= right <= 64)%Z -> (0 <= top <= 64)%Z -> (0 <= bot <= 64)%Z ->
    (1 <= p_w vs <= 20000)%Z -> (1 <= p_h vs <= 20000)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot ->
    getr regs 15 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x1c144 : word) m rom)
                  (mkst regs' (0x192d0 : word) (DIMS (FRA m s ret regs) (s - 84) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x1c200
      /\ getr regs' 10 = Z_to_bv 64 (p_w vs + left + right) /\ getr regs' 11 = Z_to_bv 64 (p_h vs + top + bot) /\ getr regs' 12 = Z_to_bv 64 (p_d vs)
      /\ getr regs' 8 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 left /\ getr regs' 22 = Z_to_bv 64 right
      /\ getr regs' 9 = Z_to_bv 64 top /\ getr regs' 19 = Z_to_bv 64 bot /\ getr regs' 24 = Z_to_bv 64 val
      /\ getr regs' 21 = Z_to_bv 64 (p_w vs + left + right) /\ getr regs' 23 = Z_to_bv 64 (p_h vs + top + bot)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs m s pixs left right top bot val vs ret Hs Hs64 Hs16 Hp ALp PX DJ Hl Hr Ht Hb Hw Hh SOK H2 H1 H10 H11 H12 H13 H14 H15.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof (lor_small right left 31 ltac:(lia) ltac:(lia) ltac:(lia)) as O1.
    pose proof (lor_small top bot 31 ltac:(lia) ltac:(lia) ltac:(lia)) as O2.
    pose proof (lor_small _ _ 31 ltac:(lia) O1 O2) as O3.
    assert (SL84 : ((s - 84) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
    assert (SL88 : ((s - 88) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
    assert (SL92 : ((s - 92) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
    assert (PX1 : PIXat (FRA m s ret regs) pixs vs).
    { unfold FRA. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    assert (PXk : forall M a bs, PIXat M pixs vs -> (s - 112 <= a)%Z -> (a + Z.of_nat (length bs) <= s)%Z -> PIXat (wbytes M (Z_to_bv 64 a) bs) pixs vs).
    { intros M a bs P Ha Hb'. apply PIXat_out; [exact P | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia]. }
    unfold DIMS, FRA in *. eexists. split.
    - zv F_1c144 D_1c144 (Z_to_bv 64 (s - 112)).
      stepST F_1c148 D_1c148 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_1c14c D_1c14c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1c150 D_1c150 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_1c154 D_1c154 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_1c158 D_1c158 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_1c15c D_1c15c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_1c160 D_1c160 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_1c164 D_1c164 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_1c168 D_1c168 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_1c16c D_1c16c (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepb_ft F_1c170 D_1c170 ltac:(condZ).
      sn F_1c174 D_1c174. sn F_1c178 D_1c178. sn F_1c17c D_1c17c. sn F_1c180 D_1c180. sn F_1c184 D_1c184.
      stepat F_1c188 D_1c188 (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_1c18c D_1c18c (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_1c190 D_1c190 (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_1c194 D_1c194 ltac:(condZ).
      sn F_1c198 D_1c198.
      zv F_1c19c D_1c19c (Z_to_bv 64 (s - 84)). zv F_1c1a0 D_1c1a0 (Z_to_bv 64 (s - 88)). zv F_1c1a4 D_1c1a4 (Z_to_bv 64 (s - 92)).
      sn F_1c1a8 D_1c1a8. sn F_1c1ac D_1c1ac.
      zand F_19b38 D_19b38 andi_3 SL84. stepb_ft F_19b3c D_19b3c ltac:(condZ). stepb_ft F_19b40 D_19b40 ltac:(condR).
      stepST F_19b44 D_19b44 (Z_to_bv 64 (s - 84)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_19b48 D_19b48 andi_3 SL88. stepb_ft F_19b4c D_19b4c ltac:(condZ). stepb_ft F_19b50 D_19b50 ltac:(condR).
      stepST F_19b54 D_19b54 (Z_to_bv 64 (s - 84 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_19b58 D_19b58 andi_3 SL92. stepb_ft F_19b5c D_19b5c ltac:(condZ). stepb_ft F_19b60 D_19b60 ltac:(condR).
      stepST F_19b64 D_19b64 (Z_to_bv 64 (s - 84 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_19b68 D_19b68 ltac:(condZ).
      zand F_19b6c D_19b6c andi_7 ALp.
      stepb_ft F_19b70 D_19b70 ltac:(condZ). sn F_19b74 D_19b74. stepb_ft F_19b78 D_19b78 ltac:(condR).
      stepLD F_19b7c D_19b7c (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_19b80 D_19b80 (Z_to_bv 64 (s - 84)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_19b84 D_19b84 ltac:(condZ). sn F_19b88 D_19b88. stepb_ft F_19b8c D_19b8c ltac:(condR).
      stepLD F_19b90 D_19b90 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_19b94 D_19b94 (Z_to_bv 64 (s - 84 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      stepb_ft F_19b98 D_19b98 ltac:(condZ). sn F_19b9c D_19b9c. stepb_ft F_19ba0 D_19ba0 ltac:(condR).
      stepLD F_19ba4 D_19ba4 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_19ba8 D_19ba8 (Z_to_bv 64 (s - 84 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_19bac D_19bac.
      stepret F_19bb0 D_19bb0 (0x1c1b0 : word) ltac:(bveq).
      ldcell F_1c1b0 D_1c1b0 (s - 84)%Z (p_w vs).
      sn F_1c1b4 D_1c1b4. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite zbv_add; reflexivity).
      sn F_1c1b8 D_1c1b8. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_1c1bc D_1c1bc ltac:(condG).
      sn F_1c1c0 D_1c1c0. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_1c1c4 D_1c1c4. fixv (Z_to_bv 64 (p_w vs + left + right)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_1c1c8 D_1c1c8. fixv (Z_to_bv 64 (p_w vs + left + right)) ltac:(rewrite zbv_add; reflexivity).
      stepb_ft F_1c1cc D_1c1cc ltac:(condG).
      ldcell F_1c1d0 D_1c1d0 (s - 84 - 4)%Z (p_h vs).
      sn F_1c1d4 D_1c1d4. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite zbv_add; reflexivity).
      sn F_1c1d8 D_1c1d8. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_1c1dc D_1c1dc ltac:(condG).
      sn F_1c1e0 D_1c1e0. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_1c1e4 D_1c1e4. fixv (Z_to_bv 64 (p_h vs + top + bot)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_1c1e8 D_1c1e8. fixv (Z_to_bv 64 (p_h vs + top + bot)) ltac:(rewrite zbv_add; reflexivity).
      stepb_ft F_1c1ec D_1c1ec ltac:(condG).
      ldcell F_1c1f0 D_1c1f0 (s - 84 - 8)%Z (p_d vs).
      sn F_1c1f4 D_1c1f4. sn F_1c1f8 D_1c1f8. sn F_1c1fc D_1c1fc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08) -> rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x1c200 : word) m rom) (mkst regs' (0x17ec4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1c2f0 /\ getr regs' 10 = Z_to_bv 64 0x10765 /\ getr regs' 11 = Z_to_bv 64 0x11378 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_1c200 D_1c200 ltac:(condZ).
      sn F_1c2c4 D_1c2c4.
      stepLD F_1c2c8 D_1c2c8 (Z_to_le_bytes 8 0x45f08) (Z_to_bv 64 0x45f08) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_1c2cc D_1c2cc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_1c2d0 D_1c2d0. stepb_ft F_1c2d4 D_1c2d4 ltac:(condZ).
      sn F_1c2d8 D_1c2d8. sn F_1c2dc D_1c2dc. sn F_1c2e0 D_1c2e0. sn F_1c2e4 D_1c2e4. sn F_1c2e8 D_1c2e8. sn F_1c2ec D_1c2ec.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F2 : forall regs m (res : Z),
    getr regs 10 = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (0x1c2f0 : word) m rom) (mkst regs' (0x1c408 : word) m rom)
      /\ getr regs' 20 = Z_to_bv 64 res /\ regs_agree (fun r => In r [20]%list) regs regs'.
  Proof.
    intros regs m res H10. eexists. split.
    - sn F_1c2f0 D_1c2f0. sn F_1c2f4 D_1c2f4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition frameA (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
    [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, getr r0 19); ((s - 48)%Z, getr r0 20);
     ((s - 56)%Z, getr r0 21); ((s - 64)%Z, getr r0 22); ((s - 72)%Z, getr r0 23); ((s - 80)%Z, getr r0 24)].

  (* [comment removed for export] *)
  Lemma ab_E : forall regs r0 m (s res : Z) (ret : word),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameA s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (0x1c408 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 res
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs r0 m s res ret Hs Hs64 Hret CE H2 H20. unfold frameA in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & _).
    eexists. split.
    - sn F_1c408 D_1c408.
      stepLD8 F_1c40c D_1c40c ret. stepLD8 F_1c410 D_1c410 (getr r0 8). stepLD8 F_1c414 D_1c414 (getr r0 9).
      stepLD8 F_1c418 D_1c418 (getr r0 18). stepLD8 F_1c41c D_1c41c (getr r0 19). stepLD8 F_1c420 D_1c420 (getr r0 20).
      stepLD8 F_1c424 D_1c424 (getr r0 21). stepLD8 F_1c428 D_1c428 (getr r0 22). stepLD8 F_1c42c D_1c42c (getr r0 23).
      stepLD8 F_1c430 D_1c430 (getr r0 24).
      zv F_1c434 D_1c434 (Z_to_bv 64 s). stepret F_1c438 D_1c438 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x1c200 : word) m rom) (mkst regs' (0x19bf4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1c210 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 20 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 20]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H8. eexists. split.
    - stepb_ft F_1c200 D_1c200 ltac:(condZ).
      sn F_1c204 D_1c204. sn F_1c208 D_1c208. sn F_1c20c D_1c20c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B2 : forall regs m (pixd pixs : Z),
    getr regs 20 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x1c210 : word) m rom) (mkst regs' (0x19c84 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1c21c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H20 H8. eexists. split.
    - sn F_1c210 D_1c210. sn F_1c214 D_1c214. sn F_1c218 D_1c218. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma ab_C : forall regs m (s d val : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z -> (val = 0 \/ val = 2 ^ d - 1)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 24 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x1c21c : word) m rom) (mkst regs' (0x1c328 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (if Z.eq_dec val 0 then 0 else 15)
      /\ regs_agree (fun r => In r [10; 11; 12; 24]%list) regs regs'.
  Proof.
    intros regs m s d val Hs Hs64 Hd Hval Rd H2 H24.
    assert (SCRIPT : forall dd vv : Z, (dd = 1 \/ dd = 8)%Z -> (vv = 0 \/ vv = 2 ^ dd - 1)%Z -> d = dd -> val = vv -> exists regs',
      msteps SEGS (mkst regs (0x1c21c : word) m rom) (mkst regs' (0x1c328 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (if Z.eq_dec vv 0 then 0 else 15) /\ regs_agree (fun r => In r [10; 11; 12; 24]%list) regs regs').
    { intros dd vv Hdd Hvv -> ->.
      destruct Hdd as [-> | ->]; destruct Hvv as [-> | ->]; cbn [Z.eq_dec Z.pow Z.sub] ; (eexists; split;
      [ first [ stepLD F_1c21c D_1c21c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rdn_addr (s - 92)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia)
              | stepLD F_1c21c D_1c21c (word_to_le_bytes 4 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdn_addr (s - 92)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia) ];
        sn F_1c220 D_1c220;
        stepb_tk F_1c224 D_1c224 ltac:(cond_compute);
        sn F_1c300 D_1c300; stepb_ft F_1c304 D_1c304 ltac:(cond_compute);
        sn F_1c308 D_1c308; sn F_1c30c D_1c30c; sn F_1c310 D_1c310; sn F_1c314 D_1c314;
        first [ stepb_ft F_1c318 D_1c318 ltac:(condG); sn F_1c31c D_1c31c; sn F_1c320 D_1c320
              | stepb_tk F_1c318 D_1c318 ltac:(condG); stepb_tk F_1c234 D_1c234 ltac:(cond_compute); sn F_1c324 D_1c324 ];
        apply mst_refl
      | repeat split; gres; pin; try reflexivity; solve_regs_agree ]). }
    exact (SCRIPT d val Hd Hval eq_refl eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma ab_C0 : forall regs m (s d : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 24 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x1c21c : word) m rom) (mkst regs' (0x1c328 : word) m rom)
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s d Hs Hs64 Hd Rd H2 H24.
    destruct (ab_C regs m s d 0 Hs Hs64 Hd (or_introl eq_refl) Rd H2 H24) as (regs' & RUN & W24 & AG).
    exists regs'. split; [exact RUN |].
    intros r Hr. destruct (decide (r = 24)) as [-> | N].
    - rewrite W24, H24. destruct (Z.eq_dec 0 0); [reflexivity | congruence].
    - apply AG. cbn [In]. intros [E | [E | [E | [E | []]]]]; first [ exact (N (eq_sym E)) | apply Hr; cbn [In]; tauto ].
  Qed.

  (* [comment removed for export] *)
  Lemma ab_C15 : forall regs m (s d val : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z -> val = (2 ^ d - 1)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 24 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x1c21c : word) m rom) (mkst regs' (0x1c328 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 15
      /\ regs_agree (fun r => In r [10; 11; 12; 24]%list) regs regs'.
  Proof.
    intros regs m s d val Hs Hs64 Hd Hv Rd H2 H24.
    destruct (ab_C regs m s d val Hs Hs64 Hd (or_intror Hv) Rd H2 H24) as (regs' & RUN & W24 & AG).
    exists regs'. split; [exact RUN | split; [| exact AG]].
    rewrite W24. destruct (Z.eq_dec val 0) as [E | _]; [| reflexivity].
    exfalso. rewrite Hv in E. destruct Hd as [-> | ->]; compute in E; discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_R1 : forall regs m (s pixd left hd op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 left -> getr regs 23 = Z_to_bv 64 hd ->
    getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x1c328 : word) m rom)
                  (mkst regs' (0x273f0 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1c350 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 left /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd left hd op Hs Hs64 SOK H2 H20 H18 H23 H24. eexists. split.
    - stepST F_1c328 D_1c328 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_1c32c D_1c32c. sn F_1c330 D_1c330. sn F_1c334 D_1c334. sn F_1c338 D_1c338. sn F_1c33c D_1c33c. sn F_1c340 D_1c340.
      sn F_1c344 D_1c344. sn F_1c348 D_1c348. sn F_1c34c D_1c34c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R2 : forall regs m (s pixd wd right hd op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= right <= wd)%Z -> (wd < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 21 = Z_to_bv 64 wd -> getr regs 22 = Z_to_bv 64 right ->
    getr regs 23 = Z_to_bv 64 hd -> getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x1c350 : word) m rom)
                  (mkst regs' (0x273f0 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1c384 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 (wd - right) /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 right /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd wd right hd op Hs Hs64 Hr Hwd SOK H2 H20 H21 H22 H23 H24. eexists. split.
    - sn F_1c350 D_1c350. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_1c354 D_1c354. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite subw_fit by lia; reflexivity).
      stepb_ft F_1c358 D_1c358 ltac:(condG).
      sn F_1c35c D_1c35c. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepST F_1c360 D_1c360 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_1c364 D_1c364. sn F_1c368 D_1c368. sn F_1c36c D_1c36c. sn F_1c370 D_1c370. sn F_1c374 D_1c374.
      sn F_1c378 D_1c378. sn F_1c37c D_1c37c. sn F_1c380 D_1c380. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R3 : forall regs m (s pixd wd top op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 21 = Z_to_bv 64 wd -> getr regs 9 = Z_to_bv 64 top ->
    getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x1c384 : word) m rom)
                  (mkst regs' (0x273f0 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1c3ac /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 top /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd wd top op Hs Hs64 SOK H2 H20 H21 H9 H24. eexists. split.
    - stepST F_1c384 D_1c384 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_1c388 D_1c388. sn F_1c38c D_1c38c. sn F_1c390 D_1c390. sn F_1c394 D_1c394. sn F_1c398 D_1c398. sn F_1c39c D_1c39c.
      sn F_1c3a0 D_1c3a0. sn F_1c3a4 D_1c3a4. sn F_1c3a8 D_1c3a8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R4 : forall regs m (s pixd hd wd bot op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= bot <= hd)%Z -> (hd < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 hd -> getr regs 21 = Z_to_bv 64 wd ->
    getr regs 19 = Z_to_bv 64 bot -> getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x1c3ac : word) m rom)
                  (mkst regs' (0x273f0 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1c3e0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (hd - bot)
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 bot /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd hd wd bot op Hs Hs64 Hb Hhd SOK H2 H20 H23 H21 H19 H24. eexists. split.
    - sn F_1c3ac D_1c3ac. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_1c3b0 D_1c3b0. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite subw_fit by lia; reflexivity).
      stepb_ft F_1c3b4 D_1c3b4 ltac:(condG).
      sn F_1c3b8 D_1c3b8. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepST F_1c3bc D_1c3bc (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_1c3c0 D_1c3c0. sn F_1c3c4 D_1c3c4. sn F_1c3c8 D_1c3c8. sn F_1c3cc D_1c3cc. sn F_1c3d0 D_1c3d0.
      sn F_1c3d4 D_1c3d4. sn F_1c3d8 D_1c3d8. sn F_1c3dc D_1c3dc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_R5 : forall regs m (s pixd pixs left top w h : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 84)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 88)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs -> getr regs 18 = Z_to_bv 64 left ->
    getr regs 9 = Z_to_bv 64 top ->
    exists regs',
      msteps SEGS (mkst regs (0x1c3e0 : word) m rom)
                  (mkst regs' (0x273f0 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1c408 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 left /\ getr regs' 12 = Z_to_bv 64 top
      /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top w h Hs Hs64 Hw Hh SOK Rw Rh H2 H20 H8 H18 H9. eexists. split.
    - stepLD F_1c3e0 D_1c3e0 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(rdn_addr (s - 84)%Z; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small w) by lia.
      stepLD F_1c3e4 D_1c3e4 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(rdn_addr (s - 88)%Z; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small h) by lia.
      sn F_1c3e8 D_1c3e8.
      stepST F_1c3ec D_1c3ec (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_1c3f0 D_1c3f0. sn F_1c3f4 D_1c3f4. sn F_1c3f8 D_1c3f8. sn F_1c3fc D_1c3fc. sn F_1c400 D_1c400. sn F_1c404 D_1c404.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition abfr (m : word -> option byte) (s : Z) (ret : word) (r0 : bvmap 5 word) (w h d : Z) : Prop :=
  cellsZ m (frameA s ret r0) /\
  rdn SEGS m (Z_to_bv 64 (s - 84)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  rdn SEGS m (Z_to_bv 64 (s - 88)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) /\
  rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)).

Lemma frameA_bounds : forall s ret r0, (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  Forall (fun av => s - 80 <= fst av /\ fst av + 8 <= s)%Z (frameA s ret r0).
Proof. intros s ret r0 Hs Hs64. unfold frameA. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. Qed.

Lemma DIMS_out : forall m a w h d (x : word), (8 <= a)%Z -> (a + 4 < 2 ^ 64)%Z -> ~ (a - 8 <= u x < a + 4)%Z -> DIMS m a w h d x = m x.
Proof.
  intros m a w h d x Ha Ha64 Hx. unfold DIMS.
  repeat (rewrite (wbytes_out_Z _ _ 4); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]). reflexivity.
Qed.
Lemma FRA_out : forall m s ret regs (x : word), (112 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 80 <= u x < s)%Z -> FRA m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold FRA.
  repeat (rewrite (wbytes_out_Z _ _ 8); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]). reflexivity.
Qed.

Lemma abfr_init : forall m s ret regs w h d, (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  abfr (DIMS (FRA m s ret regs) (s - 84) w h d) s ret regs w h d.
Proof.
  intros m s ret regs w h d Hs Hs64. unfold abfr. split.
  - apply (cellsZ_out (FRA m s ret regs) _ (s - 92) (s - 80)).
    + intros x Hx. apply DIMS_out; lia.
    + eapply Forall_impl; [|exact (frameA_bounds s ret regs Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
    + unfold frameA, FRA. cbn [cellsZ]. repeat split; rdn_solve.
  - unfold DIMS. replace (s - 88)%Z with (s - 84 - 4)%Z by lia. replace (s - 92)%Z with (s - 84 - 8)%Z by lia.
    repeat split; rdn_chain.
Qed.

Lemma abfr_frm : forall C s' m m' s ret r0 w h d, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 92)%Z -> (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  abfr m s ret r0 w h d -> abfr m' s ret r0 w h d.
Proof.
  intros C s' m m' s ret r0 w h d CK F H1 H2 Hs Hs64 (CE & Rw & Rh & Rd). unfold abfr.
  rewrite !(FRM_rdn16 C s' m m' _ 4 CK F) by (cbn; lia). split; [| repeat split; assumption].
  apply (cellsZ_frm C s' m m' _ CK F H1); [|exact CE].
  eapply Forall_impl; [|exact (frameA_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.

Lemma abfr_out : forall m m' (lo hi : Z) s ret r0 w h d, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 92 \/ s <= lo)%Z -> (112 <= s)%Z -> (s < 2 ^ 64)%Z ->
  abfr m s ret r0 w h d -> abfr m' s ret r0 w h d.
Proof.
  intros m m' lo hi s ret r0 w h d OUT Hd Hs Hs64 (CE & Rw & Rh & Rd). unfold abfr.
  split; [| repeat split; (eapply (rdn_after m m' lo hi); [exact OUT | lia | cbn; lia | cbn; lia | assumption])].
  apply (cellsZ_out m m' lo hi _ OUT); [|exact CE].
  eapply Forall_impl; [|exact (frameA_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.

Lemma str_pixAddBorderGeneral : str16 0x11378 19. Proof. str16_tac. Qed.

End GrayBorder.
