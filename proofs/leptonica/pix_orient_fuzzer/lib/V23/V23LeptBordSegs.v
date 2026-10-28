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
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptBordSegs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptErr V23LeptUb V23_code_port_bord.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
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
(* [comment removed for export] *)
Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM, u_Z2bv by lia; rewrite EQ; reflexivity).
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac condG := first [ condR | condZ ].

Section GrayBorder.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
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
      msteps SEGS (mkst regs (0x70ed8 : word) m rom)
                  (mkst regs' (0x6da3c : word) (DIMS (FRA m s ret regs) (s - 84) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x70f94
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
    - zv F_70ed8 D_70ed8 (Z_to_bv 64 (s - 112)).
      stepST F_70edc D_70edc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_70ee0 D_70ee0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_70ee4 D_70ee4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_70ee8 D_70ee8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_70eec D_70eec (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_70ef0 D_70ef0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_70ef4 D_70ef4 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_70ef8 D_70ef8 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_70efc D_70efc (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_70f00 D_70f00 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepb_ft F_70f04 D_70f04 ltac:(condZ).
      sn F_70f08 D_70f08. sn F_70f0c D_70f0c. sn F_70f10 D_70f10. sn F_70f14 D_70f14. sn F_70f18 D_70f18.
      stepat F_70f1c D_70f1c (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_70f20 D_70f20 (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_70f24 D_70f24 (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_70f28 D_70f28 ltac:(condZ).
      sn F_70f2c D_70f2c.
      zv F_70f30 D_70f30 (Z_to_bv 64 (s - 84)). zv F_70f34 D_70f34 (Z_to_bv 64 (s - 88)). zv F_70f38 D_70f38 (Z_to_bv 64 (s - 92)).
      sn F_70f3c D_70f3c. sn F_70f40 D_70f40.
      (* [comment removed for export] *)
      zand F_6e2a4 D_6e2a4 andi_3 SL84. stepb_ft F_6e2a8 D_6e2a8 ltac:(condZ). stepb_ft F_6e2ac D_6e2ac ltac:(condR).
      stepST F_6e2b0 D_6e2b0 (Z_to_bv 64 (s - 84)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_6e2b4 D_6e2b4 andi_3 SL88. stepb_ft F_6e2b8 D_6e2b8 ltac:(condZ). stepb_ft F_6e2bc D_6e2bc ltac:(condR).
      stepST F_6e2c0 D_6e2c0 (Z_to_bv 64 (s - 84 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_6e2c4 D_6e2c4 andi_3 SL92. stepb_ft F_6e2c8 D_6e2c8 ltac:(condZ). stepb_ft F_6e2cc D_6e2cc ltac:(condR).
      stepST F_6e2d0 D_6e2d0 (Z_to_bv 64 (s - 84 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_6e2d4 D_6e2d4 ltac:(condZ).
      zand F_6e2d8 D_6e2d8 andi_7 ALp.
      stepb_ft F_6e2dc D_6e2dc ltac:(condZ). sn F_6e2e0 D_6e2e0. stepb_ft F_6e2e4 D_6e2e4 ltac:(condR).
      stepLD F_6e2e8 D_6e2e8 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_6e2ec D_6e2ec (Z_to_bv 64 (s - 84)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_6e2f0 D_6e2f0 ltac:(condZ). sn F_6e2f4 D_6e2f4. stepb_ft F_6e2f8 D_6e2f8 ltac:(condR).
      stepLD F_6e2fc D_6e2fc (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_6e300 D_6e300 (Z_to_bv 64 (s - 84 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      stepb_ft F_6e304 D_6e304 ltac:(condZ). sn F_6e308 D_6e308. stepb_ft F_6e30c D_6e30c ltac:(condR).
      stepLD F_6e310 D_6e310 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_6e314 D_6e314 (Z_to_bv 64 (s - 84 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_6e318 D_6e318.
      stepret F_6e31c D_6e31c (0x70f44 : word) ltac:(bveq).
      (* [comment removed for export] *)
      ldcell F_70f44 D_70f44 (s - 84)%Z (p_w vs).
      sn F_70f48 D_70f48. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite zbv_add; reflexivity).
      sn F_70f4c D_70f4c. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_70f50 D_70f50 ltac:(condG).
      sn F_70f54 D_70f54. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_70f58 D_70f58. fixv (Z_to_bv 64 (p_w vs + left + right)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_70f5c D_70f5c. fixv (Z_to_bv 64 (p_w vs + left + right)) ltac:(rewrite zbv_add; reflexivity).
      stepb_ft F_70f60 D_70f60 ltac:(condG).
      ldcell F_70f64 D_70f64 (s - 84 - 4)%Z (p_h vs).
      sn F_70f68 D_70f68. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite zbv_add; reflexivity).
      sn F_70f6c D_70f6c. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_70f70 D_70f70 ltac:(condG).
      sn F_70f74 D_70f74. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_70f78 D_70f78. fixv (Z_to_bv 64 (p_h vs + top + bot)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_70f7c D_70f7c. fixv (Z_to_bv 64 (p_h vs + top + bot)) ltac:(rewrite zbv_add; reflexivity).
      stepb_ft F_70f80 D_70f80 ltac:(condG).
      ldcell F_70f84 D_70f84 (s - 84 - 8)%Z (p_d vs).
      sn F_70f88 D_70f88. sn F_70f8c D_70f8c. sn F_70f90 D_70f90.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x70f94 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x71084 /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x17116 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_70f94 D_70f94 ltac:(condZ).
      sn F_71058 D_71058.
      stepLD F_7105c D_7105c (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_71060 D_71060 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_71064 D_71064. stepb_ft F_71068 D_71068 ltac:(condZ).
      sn F_7106c D_7106c. sn F_71070 D_71070. sn F_71074 D_71074. sn F_71078 D_71078. sn F_7107c D_7107c. sn F_71080 D_71080.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F2 : forall regs m (res : Z),
    getr regs 10 = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (0x71084 : word) m rom) (mkst regs' (0x7119c : word) m rom)
      /\ getr regs' 20 = Z_to_bv 64 res /\ regs_agree (fun r => In r [20]%list) regs regs'.
  Proof.
    intros regs m res H10. eexists. split.
    - sn F_71084 D_71084. sn F_71088 D_71088. apply mst_refl.
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
      msteps SEGS (mkst regs (0x7119c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 res
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs r0 m s res ret Hs Hs64 Hret CE H2 H20. unfold frameA in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & _).
    eexists. split.
    - sn F_7119c D_7119c.
      stepLD8 F_711a0 D_711a0 ret. stepLD8 F_711a4 D_711a4 (getr r0 8). stepLD8 F_711a8 D_711a8 (getr r0 9).
      stepLD8 F_711ac D_711ac (getr r0 18). stepLD8 F_711b0 D_711b0 (getr r0 19). stepLD8 F_711b4 D_711b4 (getr r0 20).
      stepLD8 F_711b8 D_711b8 (getr r0 21). stepLD8 F_711bc D_711bc (getr r0 22). stepLD8 F_711c0 D_711c0 (getr r0 23).
      stepLD8 F_711c4 D_711c4 (getr r0 24).
      zv F_711c8 D_711c8 (Z_to_bv 64 s). stepret F_711cc D_711cc ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x70f94 : word) m rom) (mkst regs' (0x6e43c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x70fa4 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 20 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 20]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H8. eexists. split.
    - stepb_ft F_70f94 D_70f94 ltac:(condZ).
      sn F_70f98 D_70f98. sn F_70f9c D_70f9c. sn F_70fa0 D_70fa0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B2 : forall regs m (pixd pixs : Z),
    getr regs 20 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x70fa4 : word) m rom) (mkst regs' (0x6e4cc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x70fb0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H20 H8. eexists. split.
    - sn F_70fa4 D_70fa4. sn F_70fa8 D_70fa8. sn F_70fac D_70fac. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_C : forall regs m (s d val : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z -> (val = 0 \/ val = 2 ^ d - 1)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 24 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x70fb0 : word) m rom) (mkst regs' (0x710bc : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (if Z.eq_dec val 0 then 0 else 15)
      /\ regs_agree (fun r => In r [10; 11; 12; 24]%list) regs regs'.
  Proof.
    intros regs m s d val Hs Hs64 Hd Hval Rd H2 H24.
    assert (SCRIPT : forall dd vv : Z, (dd = 1 \/ dd = 8)%Z -> (vv = 0 \/ vv = 2 ^ dd - 1)%Z -> d = dd -> val = vv -> exists regs',
      msteps SEGS (mkst regs (0x70fb0 : word) m rom) (mkst regs' (0x710bc : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (if Z.eq_dec vv 0 then 0 else 15) /\ regs_agree (fun r => In r [10; 11; 12; 24]%list) regs regs').
    { intros dd vv Hdd Hvv -> ->.
      destruct Hdd as [-> | ->]; destruct Hvv as [-> | ->]; cbn [Z.eq_dec Z.pow Z.sub] ; (eexists; split;
      [ first [ stepLD F_70fb0 D_70fb0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rdn_addr (s - 92)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia)
              | stepLD F_70fb0 D_70fb0 (word_to_le_bytes 4 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdn_addr (s - 92)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia) ];
        sn F_70fb4 D_70fb4;
        stepb_tk F_70fb8 D_70fb8 ltac:(cond_compute);
        sn F_71094 D_71094; stepb_ft F_71098 D_71098 ltac:(cond_compute);
        sn F_7109c D_7109c; sn F_710a0 D_710a0; sn F_710a4 D_710a4; sn F_710a8 D_710a8;
        first [ stepb_ft F_710ac D_710ac ltac:(condG); sn F_710b0 D_710b0; sn F_710b4 D_710b4
              | stepb_tk F_710ac D_710ac ltac:(condG); stepb_tk F_70fc8 D_70fc8 ltac:(cond_compute); sn F_710b8 D_710b8 ];
        apply mst_refl
      | repeat split; gres; pin; try reflexivity; solve_regs_agree ]). }
    exact (SCRIPT d val Hd Hval eq_refl eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma ab_R1 : forall regs m (s pixd left hd op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 left -> getr regs 23 = Z_to_bv 64 hd ->
    getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x710bc : word) m rom)
                  (mkst regs' (0x7f13c : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x710e4 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 left /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd left hd op Hs Hs64 SOK H2 H20 H18 H23 H24. eexists. split.
    - stepST F_710bc D_710bc (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_710c0 D_710c0. sn F_710c4 D_710c4. sn F_710c8 D_710c8. sn F_710cc D_710cc. sn F_710d0 D_710d0. sn F_710d4 D_710d4.
      sn F_710d8 D_710d8. sn F_710dc D_710dc. sn F_710e0 D_710e0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R2 : forall regs m (s pixd wd right hd op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= right <= wd)%Z -> (wd < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 21 = Z_to_bv 64 wd -> getr regs 22 = Z_to_bv 64 right ->
    getr regs 23 = Z_to_bv 64 hd -> getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x710e4 : word) m rom)
                  (mkst regs' (0x7f13c : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x71118 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 (wd - right) /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 right /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd wd right hd op Hs Hs64 Hr Hwd SOK H2 H20 H21 H22 H23 H24. eexists. split.
    - sn F_710e4 D_710e4. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_710e8 D_710e8. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite subw_fit by lia; reflexivity).
      stepb_ft F_710ec D_710ec ltac:(condG).
      sn F_710f0 D_710f0. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepST F_710f4 D_710f4 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_710f8 D_710f8. sn F_710fc D_710fc. sn F_71100 D_71100. sn F_71104 D_71104. sn F_71108 D_71108.
      sn F_7110c D_7110c. sn F_71110 D_71110. sn F_71114 D_71114. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R3 : forall regs m (s pixd wd top op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 21 = Z_to_bv 64 wd -> getr regs 9 = Z_to_bv 64 top ->
    getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x71118 : word) m rom)
                  (mkst regs' (0x7f13c : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x71140 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 top /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd wd top op Hs Hs64 SOK H2 H20 H21 H9 H24. eexists. split.
    - stepST F_71118 D_71118 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_7111c D_7111c. sn F_71120 D_71120. sn F_71124 D_71124. sn F_71128 D_71128. sn F_7112c D_7112c. sn F_71130 D_71130.
      sn F_71134 D_71134. sn F_71138 D_71138. sn F_7113c D_7113c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R4 : forall regs m (s pixd hd wd bot op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= bot <= hd)%Z -> (hd < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 hd -> getr regs 21 = Z_to_bv 64 wd ->
    getr regs 19 = Z_to_bv 64 bot -> getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x71140 : word) m rom)
                  (mkst regs' (0x7f13c : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x71174 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (hd - bot)
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 bot /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd hd wd bot op Hs Hs64 Hb Hhd SOK H2 H20 H23 H21 H19 H24. eexists. split.
    - sn F_71140 D_71140. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_71144 D_71144. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite subw_fit by lia; reflexivity).
      stepb_ft F_71148 D_71148 ltac:(condG).
      sn F_7114c D_7114c. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepST F_71150 D_71150 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_71154 D_71154. sn F_71158 D_71158. sn F_7115c D_7115c. sn F_71160 D_71160. sn F_71164 D_71164.
      sn F_71168 D_71168. sn F_7116c D_7116c. sn F_71170 D_71170. apply mst_refl.
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
      msteps SEGS (mkst regs (0x71174 : word) m rom)
                  (mkst regs' (0x7f13c : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x7119c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 left /\ getr regs' 12 = Z_to_bv 64 top
      /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top w h Hs Hs64 Hw Hh SOK Rw Rh H2 H20 H8 H18 H9. eexists. split.
    - stepLD F_71174 D_71174 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(rdn_addr (s - 84)%Z; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small w) by lia.
      stepLD F_71178 D_71178 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(rdn_addr (s - 88)%Z; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small h) by lia.
      sn F_7117c D_7117c.
      stepST F_71180 D_71180 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_71184 D_71184. sn F_71188 D_71188. sn F_7118c D_7118c. sn F_71190 D_71190. sn F_71194 D_71194. sn F_71198 D_71198.
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

Lemma str_pixAddBorderGeneral : str16 0x17116 19. Proof. str16_tac. Qed.

End GrayBorder.
