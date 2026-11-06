(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRop GrayACELib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptStderr V14LeptBase V14LeptUb.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14CL7a.
Import V14CL7a.V14LeptErr. Import V14CL7a.V14LeptRop_iface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptPixHdr V14LeptPixCreate V14LeptCmapValid V14LeptCmap2 V14LeptPixCopyA V14LeptPixCopy V14LeptGrayA V14_code_gmACE.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
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
Context {PINS : @LeptPins AL LLU16} {P16 : V14Pins}.
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
      msteps SEGS (mkst regs (0x18424 : word) m rom)
                  (mkst regs' (0x15798 : word) (DIMS (FRA m s ret regs) (s - 84) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x184e0
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
    - zv F_18328 D_18328 (Z_to_bv 64 (s - 112)).
      stepST F_1832c D_1832c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_18330 D_18330 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_18334 D_18334 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_18338 D_18338 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_1833c D_1833c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_18340 D_18340 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_18344 D_18344 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_18348 D_18348 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_1834c D_1834c (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_18350 D_18350 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepb_ft F_18354 D_18354 ltac:(condZ).
      sn F_18358 D_18358. sn F_1835c D_1835c. sn F_18360 D_18360. sn F_18364 D_18364. sn F_18368 D_18368.
      stepat F_1836c D_1836c (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_18370 D_18370 (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_18374 D_18374 (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_18378 D_18378 ltac:(condZ).
      sn F_1837c D_1837c.
      zv F_18380 D_18380 (Z_to_bv 64 (s - 84)). zv F_18384 D_18384 (Z_to_bv 64 (s - 88)). zv F_18388 D_18388 (Z_to_bv 64 (s - 92)).
      sn F_1838c D_1838c. sn F_18390 D_18390.
      (* [comment removed for export] *)
      zand F_15f04 D_15f04 andi_3 SL84. stepb_ft F_15f08 D_15f08 ltac:(condZ). stepb_ft F_15f0c D_15f0c ltac:(condR).
      stepST F_15f10 D_15f10 (Z_to_bv 64 (s - 84)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_15f14 D_15f14 andi_3 SL88. stepb_ft F_15f18 D_15f18 ltac:(condZ). stepb_ft F_15f1c D_15f1c ltac:(condR).
      stepST F_15f20 D_15f20 (Z_to_bv 64 (s - 84 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_15f24 D_15f24 andi_3 SL92. stepb_ft F_15f28 D_15f28 ltac:(condZ). stepb_ft F_15f2c D_15f2c ltac:(condR).
      stepST F_15f30 D_15f30 (Z_to_bv 64 (s - 84 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15f34 D_15f34 ltac:(condZ).
      zand F_15f38 D_15f38 andi_7 ALp.
      stepb_ft F_15f3c D_15f3c ltac:(condZ). sn F_15f40 D_15f40. stepb_ft F_15f44 D_15f44 ltac:(condR).
      stepLD F_15f48 D_15f48 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_15f4c D_15f4c (Z_to_bv 64 (s - 84)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_15f50 D_15f50 ltac:(condZ). sn F_15f54 D_15f54. stepb_ft F_15f58 D_15f58 ltac:(condR).
      stepLD F_15f5c D_15f5c (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_15f60 D_15f60 (Z_to_bv 64 (s - 84 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      stepb_ft F_15f64 D_15f64 ltac:(condZ). sn F_15f68 D_15f68. stepb_ft F_15f6c D_15f6c ltac:(condR).
      stepLD F_15f70 D_15f70 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_15f74 D_15f74 (Z_to_bv 64 (s - 84 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_15f78 D_15f78.
      stepret F_15f7c D_15f7c (0x18490 : word) ltac:(bveq).
      (* [comment removed for export] *)
      ldcell F_18394 D_18394 (s - 84)%Z (p_w vs).
      sn F_18398 D_18398. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite zbv_add; reflexivity).
      sn F_1839c D_1839c. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_183a0 D_183a0 ltac:(condG).
      sn F_183a4 D_183a4. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_183a8 D_183a8. fixv (Z_to_bv 64 (p_w vs + left + right)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_183ac D_183ac. fixv (Z_to_bv 64 (p_w vs + left + right)) ltac:(rewrite zbv_add; reflexivity).
      stepb_ft F_183b0 D_183b0 ltac:(condG).
      ldcell F_183b4 D_183b4 (s - 84 - 4)%Z (p_h vs).
      sn F_183b8 D_183b8. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite zbv_add; reflexivity).
      sn F_183bc D_183bc. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_183c0 D_183c0 ltac:(condG).
      sn F_183c4 D_183c4. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_183c8 D_183c8. fixv (Z_to_bv 64 (p_h vs + top + bot)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_183cc D_183cc. fixv (Z_to_bv 64 (p_h vs + top + bot)) ltac:(rewrite zbv_add; reflexivity).
      stepb_ft F_183d0 D_183d0 ltac:(condG).
      ldcell F_183d4 D_183d4 (s - 84 - 8)%Z (p_d vs).
      sn F_183d8 D_183d8. sn F_183dc D_183dc. sn F_183e0 D_183e0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x184e0 : word) m rom) (mkst regs' (0x1554c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x185d0 /\ getr regs' 10 = Z_to_bv 64 0x104bd /\ getr regs' 11 = Z_to_bv 64 0x10ba8 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_183e4 D_183e4 ltac:(condZ).
      sn F_184a8 D_184a8.
      stepLD F_184ac D_184ac (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_184b0 D_184b0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_184b4 D_184b4. stepb_ft F_184b8 D_184b8 ltac:(condZ).
      sn F_184bc D_184bc. sn F_184c0 D_184c0. sn F_184c4 D_184c4. sn F_184c8 D_184c8. sn F_184cc D_184cc. sn F_184d0 D_184d0.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F2 : forall regs m (res : Z),
    getr regs 10 = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (0x185d0 : word) m rom) (mkst regs' (0x186e8 : word) m rom)
      /\ getr regs' 20 = Z_to_bv 64 res /\ regs_agree (fun r => In r [20]%list) regs regs'.
  Proof.
    intros regs m res H10. eexists. split.
    - sn F_184d4 D_184d4. sn F_184d8 D_184d8. apply mst_refl.
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
      msteps SEGS (mkst regs (0x186e8 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 res
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs r0 m s res ret Hs Hs64 Hret CE H2 H20. unfold frameA in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & _).
    eexists. split.
    - sn F_185ec D_185ec.
      stepLD8 F_185f0 D_185f0 ret. stepLD8 F_185f4 D_185f4 (getr r0 8). stepLD8 F_185f8 D_185f8 (getr r0 9).
      stepLD8 F_185fc D_185fc (getr r0 18). stepLD8 F_18600 D_18600 (getr r0 19). stepLD8 F_18604 D_18604 (getr r0 20).
      stepLD8 F_18608 D_18608 (getr r0 21). stepLD8 F_1860c D_1860c (getr r0 22). stepLD8 F_18610 D_18610 (getr r0 23).
      stepLD8 F_18614 D_18614 (getr r0 24).
      zv F_18618 D_18618 (Z_to_bv 64 s). stepret F_1861c D_1861c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x184e0 : word) m rom) (mkst regs' (0x16198 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x184f0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 20 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 20]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H8. eexists. split.
    - stepb_ft F_183e4 D_183e4 ltac:(condZ).
      sn F_183e8 D_183e8. sn F_183ec D_183ec. sn F_183f0 D_183f0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B2 : forall regs m (pixd pixs : Z),
    getr regs 20 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x184f0 : word) m rom) (mkst regs' (0x16228 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x184fc /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H20 H8. eexists. split.
    - sn F_183f4 D_183f4. sn F_183f8 D_183f8. sn F_183fc D_183fc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_C : forall regs m (s d val : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z -> (val = 0 \/ val = 2 ^ d - 1)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 24 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x184fc : word) m rom) (mkst regs' (0x18608 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (if Z.eq_dec val 0 then 0 else 15)
      /\ regs_agree (fun r => In r [10; 11; 12; 24]%list) regs regs'.
  Proof.
    intros regs m s d val Hs Hs64 Hd Hval Rd H2 H24.
    assert (SCRIPT : forall dd vv : Z, (dd = 1 \/ dd = 8)%Z -> (vv = 0 \/ vv = 2 ^ dd - 1)%Z -> d = dd -> val = vv -> exists regs',
      msteps SEGS (mkst regs (0x184fc : word) m rom) (mkst regs' (0x18608 : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (if Z.eq_dec vv 0 then 0 else 15) /\ regs_agree (fun r => In r [10; 11; 12; 24]%list) regs regs').
    { intros dd vv Hdd Hvv -> ->.
      destruct Hdd as [-> | ->]; destruct Hvv as [-> | ->]; cbn [Z.eq_dec Z.pow Z.sub] ; (eexists; split;
      [ first [ stepLD F_18400 D_18400 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rdn_addr (s - 92)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia)
              | stepLD F_18400 D_18400 (word_to_le_bytes 4 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdn_addr (s - 92)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia) ];
        sn F_18404 D_18404;
        stepb_tk F_18408 D_18408 ltac:(cond_compute);
        sn F_184e4 D_184e4; stepb_ft F_184e8 D_184e8 ltac:(cond_compute);
        sn F_184ec D_184ec; sn F_184f0 D_184f0; sn F_184f4 D_184f4; sn F_184f8 D_184f8;
        first [ stepb_ft F_184fc D_184fc ltac:(condG); sn F_18500 D_18500; sn F_18504 D_18504
              | stepb_tk F_184fc D_184fc ltac:(condG); stepb_tk F_18418 D_18418 ltac:(cond_compute); sn F_18508 D_18508 ];
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
      msteps SEGS (mkst regs (0x18608 : word) m rom)
                  (mkst regs' (0x1e8a4 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x18630 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 left /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd left hd op Hs Hs64 SOK H2 H20 H18 H23 H24. eexists. split.
    - stepST F_1850c D_1850c (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_18510 D_18510. sn F_18514 D_18514. sn F_18518 D_18518. sn F_1851c D_1851c. sn F_18520 D_18520. sn F_18524 D_18524.
      sn F_18528 D_18528. sn F_1852c D_1852c. sn F_18530 D_18530. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R2 : forall regs m (s pixd wd right hd op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= right <= wd)%Z -> (wd < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 21 = Z_to_bv 64 wd -> getr regs 22 = Z_to_bv 64 right ->
    getr regs 23 = Z_to_bv 64 hd -> getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x18630 : word) m rom)
                  (mkst regs' (0x1e8a4 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x18664 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 (wd - right) /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 right /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd wd right hd op Hs Hs64 Hr Hwd SOK H2 H20 H21 H22 H23 H24. eexists. split.
    - sn F_18534 D_18534. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_18538 D_18538. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite subw_fit by lia; reflexivity).
      stepb_ft F_1853c D_1853c ltac:(condG).
      sn F_18540 D_18540. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepST F_18544 D_18544 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_18548 D_18548. sn F_1854c D_1854c. sn F_18550 D_18550. sn F_18554 D_18554. sn F_18558 D_18558.
      sn F_1855c D_1855c. sn F_18560 D_18560. sn F_18564 D_18564. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R3 : forall regs m (s pixd wd top op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 21 = Z_to_bv 64 wd -> getr regs 9 = Z_to_bv 64 top ->
    getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x18664 : word) m rom)
                  (mkst regs' (0x1e8a4 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1868c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 top /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd wd top op Hs Hs64 SOK H2 H20 H21 H9 H24. eexists. split.
    - stepST F_18568 D_18568 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_1856c D_1856c. sn F_18570 D_18570. sn F_18574 D_18574. sn F_18578 D_18578. sn F_1857c D_1857c. sn F_18580 D_18580.
      sn F_18584 D_18584. sn F_18588 D_18588. sn F_1858c D_1858c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R4 : forall regs m (s pixd hd wd bot op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= bot <= hd)%Z -> (hd < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 hd -> getr regs 21 = Z_to_bv 64 wd ->
    getr regs 19 = Z_to_bv 64 bot -> getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x1868c : word) m rom)
                  (mkst regs' (0x1e8a4 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x186c0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (hd - bot)
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 bot /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd hd wd bot op Hs Hs64 Hb Hhd SOK H2 H20 H23 H21 H19 H24. eexists. split.
    - sn F_18590 D_18590. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_18594 D_18594. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite subw_fit by lia; reflexivity).
      stepb_ft F_18598 D_18598 ltac:(condG).
      sn F_1859c D_1859c. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepST F_185a0 D_185a0 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_185a4 D_185a4. sn F_185a8 D_185a8. sn F_185ac D_185ac. sn F_185b0 D_185b0. sn F_185b4 D_185b4.
      sn F_185b8 D_185b8. sn F_185bc D_185bc. sn F_185c0 D_185c0. apply mst_refl.
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
      msteps SEGS (mkst regs (0x186c0 : word) m rom)
                  (mkst regs' (0x1e8a4 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x186e8 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 left /\ getr regs' 12 = Z_to_bv 64 top
      /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top w h Hs Hs64 Hw Hh SOK Rw Rh H2 H20 H8 H18 H9. eexists. split.
    - stepLD F_185c4 D_185c4 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(rdn_addr (s - 84)%Z; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small w) by lia.
      stepLD F_185c8 D_185c8 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(rdn_addr (s - 88)%Z; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small h) by lia.
      sn F_185cc D_185cc.
      stepST F_185d0 D_185d0 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_185d4 D_185d4. sn F_185d8 D_185d8. sn F_185dc D_185dc. sn F_185e0 D_185e0. sn F_185e4 D_185e4. sn F_185e8 D_185e8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FRR (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 23)).
Definition frameR (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, getr r0 19); ((s - 48)%Z, getr r0 20);
   ((s - 56)%Z, getr r0 21); ((s - 64)%Z, getr r0 23)].

Section SegsR.
Variable rom : word -> option byte.

  Ltac rb_prologue s ret regs SOK :=
    zv F_18624 D_18624 (Z_to_bv 64 (s - 96));
    stepST F_18628 D_18628 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
    stepST F_1862c D_1862c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
    stepST F_18630 D_18630 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
    stepST F_18634 D_18634 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
    stepST F_18638 D_18638 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK);
    stepST F_1863c D_1863c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK);
    stepST F_18640 D_18640 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK);
    stepST F_18644 D_18644 (Z_to_bv 64 (s - 64)) (getr regs 23) ltac:(sok_in SOK).

  (* [comment removed for export] *)
  Lemma rb_A : forall regs m (s pixs left right top bot : Z) (vs : pixv) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 96 \/ s <= pixs)%Z ->
    (0 <= left <= 64)%Z -> (0 <= right <= 64)%Z -> (0 <= top <= 64)%Z -> (0 <= bot <= 64)%Z ->
    (1 <= p_w vs <= 20000)%Z -> (1 <= p_h vs <= 20000)%Z -> (1 <= p_w vs - left - right)%Z -> (1 <= p_h vs - top - bot)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot ->
    exists regs',
      msteps SEGS (mkst regs (0x18720 : word) m rom)
                  (mkst regs' (0x15798 : word) (DIMS (FRR m s ret regs) (s - 68) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x187d4
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
      stepb_ft F_18648 D_18648 ltac:(condZ).
      sn F_1864c D_1864c. sn F_18650 D_18650. sn F_18654 D_18654. sn F_18658 D_18658.
      stepat F_1865c D_1865c (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_18660 D_18660 (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_18664 D_18664 (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_18668 D_18668 ltac:(condZ).
      zv F_1866c D_1866c (Z_to_bv 64 (s - 68)). zv F_18670 D_18670 (Z_to_bv 64 (s - 72)). zv F_18674 D_18674 (Z_to_bv 64 (s - 76)).
      sn F_18678 D_18678. sn F_1867c D_1867c.
      (* [comment removed for export] *)
      zand F_15f04 D_15f04 andi_3 SL68. stepb_ft F_15f08 D_15f08 ltac:(condZ). stepb_ft F_15f0c D_15f0c ltac:(condR).
      stepST F_15f10 D_15f10 (Z_to_bv 64 (s - 68)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_15f14 D_15f14 andi_3 SL72. stepb_ft F_15f18 D_15f18 ltac:(condZ). stepb_ft F_15f1c D_15f1c ltac:(condR).
      stepST F_15f20 D_15f20 (Z_to_bv 64 (s - 68 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_15f24 D_15f24 andi_3 SL76. stepb_ft F_15f28 D_15f28 ltac:(condZ). stepb_ft F_15f2c D_15f2c ltac:(condR).
      stepST F_15f30 D_15f30 (Z_to_bv 64 (s - 68 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15f34 D_15f34 ltac:(condZ).
      zand F_15f38 D_15f38 andi_7 ALp.
      stepb_ft F_15f3c D_15f3c ltac:(condZ). sn F_15f40 D_15f40. stepb_ft F_15f44 D_15f44 ltac:(condR).
      stepLD F_15f48 D_15f48 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_15f4c D_15f4c (Z_to_bv 64 (s - 68)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_15f50 D_15f50 ltac:(condZ). sn F_15f54 D_15f54. stepb_ft F_15f58 D_15f58 ltac:(condR).
      stepLD F_15f5c D_15f5c (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_15f60 D_15f60 (Z_to_bv 64 (s - 68 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      stepb_ft F_15f64 D_15f64 ltac:(condZ). sn F_15f68 D_15f68. stepb_ft F_15f6c D_15f6c ltac:(condR).
      stepLD F_15f70 D_15f70 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_15f74 D_15f74 (Z_to_bv 64 (s - 68 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_15f78 D_15f78.
      stepret F_15f7c D_15f7c (0x1877c : word) ltac:(bveq).
      (* [comment removed for export] *)
      ldcell F_18680 D_18680 (s - 68)%Z (p_w vs).
      sn F_18684 D_18684. fixv (Z_to_bv 64 (p_w vs - left)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_18688 D_18688. fixv (Z_to_bv 64 (p_w vs - left)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_1868c D_1868c ltac:(condG).
      sn F_18690 D_18690. fixv (Z_to_bv 64 (p_w vs - left)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_18694 D_18694. fixv (Z_to_bv 64 (p_w vs - left - right)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      sn F_18698 D_18698. fixv (Z_to_bv 64 (p_w vs - left - right)) ltac:(rewrite zbv_sub; reflexivity).
      stepb_ft F_1869c D_1869c ltac:(condG).
      ldcell F_186a0 D_186a0 (s - 68 - 4)%Z (p_h vs).
      sn F_186a4 D_186a4. fixv (Z_to_bv 64 (p_h vs - top)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_186a8 D_186a8. fixv (Z_to_bv 64 (p_h vs - top)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_186ac D_186ac ltac:(condG).
      sn F_186b0 D_186b0. fixv (Z_to_bv 64 (p_h vs - top)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_186b4 D_186b4. fixv (Z_to_bv 64 (p_h vs - top - bot)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      sn F_186b8 D_186b8. fixv (Z_to_bv 64 (p_h vs - top - bot)) ltac:(rewrite zbv_sub; reflexivity).
      stepb_ft F_186bc D_186bc ltac:(condG).
      stepb_ft F_186c0 D_186c0 ltac:(condZ).
      stepb_ft F_186c4 D_186c4 ltac:(condZ).
      ldcell F_186c8 D_186c8 (s - 68 - 8)%Z (p_d vs).
      sn F_186cc D_186cc. sn F_186d0 D_186d0. sn F_186d4 D_186d4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_N1 : forall regs m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x18720 : word) m rom) (mkst regs' (0x1886c : word) (FRR m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96)
      /\ regs_agree (fun r => In r [2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10. unfold FRR. eexists. split.
    - rb_prologue s ret regs SOK.
      stepb_tk F_18648 D_18648 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_N2 : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameR s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x1886c : word) m rom) (mkst regs' (0x1554c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10cf4
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Rg Rs CE H2. unfold frameR in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    eexists. split.
    - sn F_18770 D_18770.
      stepLD F_18774 D_18774 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_18778 D_18778 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_1877c D_1877c. stepb_ft F_18780 D_18780 ltac:(condZ).
      sn F_18784 D_18784. sn F_18788 D_18788. sn F_1878c D_1878c. sn F_18790 D_18790. sn F_18794 D_18794.
      sn F_187bc D_187bc.
      stepLD8 F_187c0 D_187c0 ret. stepLD8 F_187c4 D_187c4 (getr r0 8). stepLD8 F_187c8 D_187c8 (getr r0 9).
      stepLD8 F_187cc D_187cc (getr r0 18). stepLD8 F_187d0 D_187d0 (getr r0 19). stepLD8 F_187d4 D_187d4 (getr r0 20).
      stepLD8 F_187d8 D_187d8 (getr r0 21). stepLD8 F_187dc D_187dc (getr r0 23).
      zv F_187e0 D_187e0 (Z_to_bv 64 s). sn F_187e4 D_187e4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x187d4 : word) m rom) (mkst regs' (0x1554c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x18960 /\ getr regs' 10 = Z_to_bv 64 0x104bd /\ getr regs' 11 = Z_to_bv 64 0x10cf4 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_186d8 D_186d8 ltac:(condZ).
      sn F_18838 D_18838.
      stepLD F_1883c D_1883c (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_18840 D_18840 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_18844 D_18844. stepb_ft F_18848 D_18848 ltac:(condZ).
      sn F_1884c D_1884c. sn F_18850 D_18850. sn F_18854 D_18854. sn F_18858 D_18858. sn F_1885c D_1885c. sn F_18860 D_18860.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_E : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameR s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x18968 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Hret CE H2. unfold frameR in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    eexists. split.
    - stepLD8 F_1886c D_1886c ret. stepLD8 F_18870 D_18870 (getr r0 8). stepLD8 F_18874 D_18874 (getr r0 9).
      stepLD8 F_18878 D_18878 (getr r0 18). stepLD8 F_1887c D_1887c (getr r0 19). stepLD8 F_18880 D_18880 (getr r0 20).
      stepLD8 F_18884 D_18884 (getr r0 21). stepLD8 F_18888 D_18888 (getr r0 23).
      zv F_1888c D_1888c (Z_to_bv 64 s). stepret F_18890 D_18890 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  Lemma rb_F2 : forall regs m, exists regs',
      msteps SEGS (mkst regs (0x18960 : word) m rom) (mkst regs' (0x18968 : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_18864 D_18864; apply mst_refl | solve_regs_agree]. Qed.

  (* [comment removed for export] *)
  Lemma rb_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x187d4 : word) m rom) (mkst regs' (0x16198 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x187e4 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 21 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 21]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H18. eexists. split.
    - stepb_ft F_186d8 D_186d8 ltac:(condZ).
      sn F_186dc D_186dc. sn F_186e0 D_186e0. sn F_186e4 D_186e4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma rb_B2 : forall regs m (pixd pixs : Z),
    getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x187e4 : word) m rom) (mkst regs' (0x160bc : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x187f0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H21 H18. eexists. split.
    - sn F_186e8 D_186e8. sn F_186ec D_186ec. sn F_186f0 D_186f0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma rb_B3 : forall regs m (pixd pixs : Z),
    getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x187f0 : word) m rom) (mkst regs' (0x16228 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x187fc /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H21 H18. eexists. split.
    - sn F_186f4 D_186f4. sn F_186f8 D_186f8. sn F_186fc D_186fc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_R : forall regs m (s pixd pixs left top wd hd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs -> getr regs 9 = Z_to_bv 64 left ->
    getr regs 8 = Z_to_bv 64 top -> getr regs 19 = Z_to_bv 64 wd -> getr regs 20 = Z_to_bv 64 hd ->
    exists regs',
      msteps SEGS (mkst regs (0x187fc : word) m rom)
                  (mkst regs' (0x1e8a4 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 top))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x18828 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 left /\ getr regs' 23 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 23]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top wd hd Hs Hs64 SOK H2 H21 H18 H9 H8 H19 H20. eexists. split.
    - sn F_18700 D_18700.
      stepST F_18704 D_18704 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 top) ltac:(sok_in SOK).
      sn F_18708 D_18708. sn F_1870c D_1870c. sn F_18710 D_18710. sn F_18714 D_18714. sn F_18718 D_18718. sn F_1871c D_1871c.
      sn F_18720 D_18720. sn F_18724 D_18724. sn F_18728 D_18728. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_D : forall regs m (pixs pixd : Z) (vs : pixv),
    (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> (p_d vs = 1 \/ p_d vs = 8)%Z ->
    getr regs 18 = Z_to_bv 64 pixs -> getr regs 23 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x18828 : word) m rom) (mkst regs' (0x18968 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixs pixd vs Hp ALp PX Hd H18 H23. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd.
    eexists. split.
    - sn F_1872c D_1872c. sn F_18730 D_18730.
      stepb_ft F_16c40 D_16c40 ltac:(condZ).
      zand F_16c44 D_16c44 andi_7 ALp. stepb_ft F_16c48 D_16c48 ltac:(condR).
      stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepret F_16c50 D_16c50 (0x18830 : word) ltac:(bveq).
      sn F_18734 D_18734.
      stepb_tk F_18738 D_18738 ltac:(condZ).
      sn F_18768 D_18768. sn F_1876c D_1876c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsR.

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

Lemma str_pixAddBorderGeneral : str16 0x10ba8 19. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Definition rbfr (m : word -> option byte) (s : Z) (ret : word) (r0 : bvmap 5 word) (w h d : Z) : Prop :=
  cellsZ m (frameR s ret r0) /\
  rdn SEGS m (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  rdn SEGS m (Z_to_bv 64 (s - 72)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) /\
  rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)).

Lemma frameR_bounds : forall s ret r0, (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  Forall (fun av => s - 64 <= fst av /\ fst av + 8 <= s)%Z (frameR s ret r0).
Proof. intros s ret r0 Hs Hs64. unfold frameR. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. Qed.

Lemma FRR_out : forall m s ret regs (x : word), (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 64 <= u x < s)%Z -> FRR m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold FRR.
  repeat (rewrite (wbytes_out_Z _ _ 8); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]). reflexivity.
Qed.

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

Lemma str_pixRemoveBorderGeneral : str16 0x10cf4 22. Proof. str16_tac. Qed.
Lemma str_msg_pixs_undef : str16 0x10298 16. Proof. str16_tac. Qed.

End GrayBorder.
