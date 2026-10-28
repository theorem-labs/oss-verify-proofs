(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRop GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase V10LeptUb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptErr. Import V10CL7a.V10LeptRop_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptPixCreate V10LeptCmapValid V10LeptCmap2 V10LeptPixCopyA V10LeptPixCopy V10LeptGrayA V10_code_fhH.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
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
Context {PINS : @LeptPins AL LLU16} {P16 : V10Pins}.
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
      msteps SEGS (mkst regs (0x17fb8 : word) m rom)
                  (mkst regs' (0x15c00 : word) (DIMS (FRA m s ret regs) (s - 84) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x18074
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
    - zv F_17ebc D_17ebc (Z_to_bv 64 (s - 112)).
      stepST F_17ec0 D_17ec0 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_17ec4 D_17ec4 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_17ec8 D_17ec8 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_17ecc D_17ecc (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_17ed0 D_17ed0 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_17ed4 D_17ed4 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_17ed8 D_17ed8 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_17edc D_17edc (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_17ee0 D_17ee0 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_17ee4 D_17ee4 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepb_ft F_17ee8 D_17ee8 ltac:(condZ).
      sn F_17eec D_17eec. sn F_17ef0 D_17ef0. sn F_17ef4 D_17ef4. sn F_17ef8 D_17ef8. sn F_17efc D_17efc.
      stepat F_17f00 D_17f00 (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_17f04 D_17f04 (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_17f08 D_17f08 (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_17f0c D_17f0c ltac:(condZ).
      sn F_17f10 D_17f10.
      zv F_17f14 D_17f14 (Z_to_bv 64 (s - 84)). zv F_17f18 D_17f18 (Z_to_bv 64 (s - 88)). zv F_17f1c D_17f1c (Z_to_bv 64 (s - 92)).
      sn F_17f20 D_17f20. sn F_17f24 D_17f24.
      (* [comment removed for export] *)
      zand F_1636c D_1636c andi_3 SL84. stepb_ft F_16370 D_16370 ltac:(condZ). stepb_ft F_16374 D_16374 ltac:(condR).
      stepST F_16378 D_16378 (Z_to_bv 64 (s - 84)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_1637c D_1637c andi_3 SL88. stepb_ft F_16380 D_16380 ltac:(condZ). stepb_ft F_16384 D_16384 ltac:(condR).
      stepST F_16388 D_16388 (Z_to_bv 64 (s - 84 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_1638c D_1638c andi_3 SL92. stepb_ft F_16390 D_16390 ltac:(condZ). stepb_ft F_16394 D_16394 ltac:(condR).
      stepST F_16398 D_16398 (Z_to_bv 64 (s - 84 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_1639c D_1639c ltac:(condZ).
      zand F_163a0 D_163a0 andi_7 ALp.
      stepb_ft F_163a4 D_163a4 ltac:(condZ). sn F_163a8 D_163a8. stepb_ft F_163ac D_163ac ltac:(condR).
      stepLD F_163b0 D_163b0 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_163b4 D_163b4 (Z_to_bv 64 (s - 84)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_163b8 D_163b8 ltac:(condZ). sn F_163bc D_163bc. stepb_ft F_163c0 D_163c0 ltac:(condR).
      stepLD F_163c4 D_163c4 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_163c8 D_163c8 (Z_to_bv 64 (s - 84 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      stepb_ft F_163cc D_163cc ltac:(condZ). sn F_163d0 D_163d0. stepb_ft F_163d4 D_163d4 ltac:(condR).
      stepLD F_163d8 D_163d8 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_163dc D_163dc (Z_to_bv 64 (s - 84 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_163e0 D_163e0.
      stepret F_163e4 D_163e4 (0x18024 : word) ltac:(bveq).
      (* [comment removed for export] *)
      ldcell F_17f28 D_17f28 (s - 84)%Z (p_w vs).
      sn F_17f2c D_17f2c. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite zbv_add; reflexivity).
      sn F_17f30 D_17f30. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_17f34 D_17f34 ltac:(condG).
      sn F_17f38 D_17f38. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_17f3c D_17f3c. fixv (Z_to_bv 64 (p_w vs + left + right)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_17f40 D_17f40. fixv (Z_to_bv 64 (p_w vs + left + right)) ltac:(rewrite zbv_add; reflexivity).
      stepb_ft F_17f44 D_17f44 ltac:(condG).
      ldcell F_17f48 D_17f48 (s - 84 - 4)%Z (p_h vs).
      sn F_17f4c D_17f4c. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite zbv_add; reflexivity).
      sn F_17f50 D_17f50. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_17f54 D_17f54 ltac:(condG).
      sn F_17f58 D_17f58. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_17f5c D_17f5c. fixv (Z_to_bv 64 (p_h vs + top + bot)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_17f60 D_17f60. fixv (Z_to_bv 64 (p_h vs + top + bot)) ltac:(rewrite zbv_add; reflexivity).
      stepb_ft F_17f64 D_17f64 ltac:(condG).
      ldcell F_17f68 D_17f68 (s - 84 - 8)%Z (p_d vs).
      sn F_17f6c D_17f6c. sn F_17f70 D_17f70. sn F_17f74 D_17f74.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x33d90) 8 = Some (Z_to_le_bytes 8 0x34e00) -> rdn SEGS m (Z_to_bv 64 0x34e00) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x18074 : word) m rom) (mkst regs' (0x1586c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x18164 /\ getr regs' 10 = Z_to_bv 64 0x1054a /\ getr regs' 11 = Z_to_bv 64 0x10cd9 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_17f78 D_17f78 ltac:(condZ).
      sn F_1803c D_1803c.
      stepLD F_18040 D_18040 (Z_to_le_bytes 8 0x34e00) (Z_to_bv 64 0x34e00) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_18044 D_18044 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_18048 D_18048. stepb_ft F_1804c D_1804c ltac:(condZ).
      sn F_18050 D_18050. sn F_18054 D_18054. sn F_18058 D_18058. sn F_1805c D_1805c. sn F_18060 D_18060. sn F_18064 D_18064.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F2 : forall regs m (res : Z),
    getr regs 10 = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (0x18164 : word) m rom) (mkst regs' (0x1827c : word) m rom)
      /\ getr regs' 20 = Z_to_bv 64 res /\ regs_agree (fun r => In r [20]%list) regs regs'.
  Proof.
    intros regs m res H10. eexists. split.
    - sn F_18068 D_18068. sn F_1806c D_1806c. apply mst_refl.
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
      msteps SEGS (mkst regs (0x1827c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 res
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs r0 m s res ret Hs Hs64 Hret CE H2 H20. unfold frameA in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & _).
    eexists. split.
    - sn F_18180 D_18180.
      stepLD8 F_18184 D_18184 ret. stepLD8 F_18188 D_18188 (getr r0 8). stepLD8 F_1818c D_1818c (getr r0 9).
      stepLD8 F_18190 D_18190 (getr r0 18). stepLD8 F_18194 D_18194 (getr r0 19). stepLD8 F_18198 D_18198 (getr r0 20).
      stepLD8 F_1819c D_1819c (getr r0 21). stepLD8 F_181a0 D_181a0 (getr r0 22). stepLD8 F_181a4 D_181a4 (getr r0 23).
      stepLD8 F_181a8 D_181a8 (getr r0 24).
      zv F_181ac D_181ac (Z_to_bv 64 s). stepret F_181b0 D_181b0 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x18074 : word) m rom) (mkst regs' (0x16600 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x18084 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 20 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 20]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H8. eexists. split.
    - stepb_ft F_17f78 D_17f78 ltac:(condZ).
      sn F_17f7c D_17f7c. sn F_17f80 D_17f80. sn F_17f84 D_17f84. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B2 : forall regs m (pixd pixs : Z),
    getr regs 20 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x18084 : word) m rom) (mkst regs' (0x16690 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x18090 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H20 H8. eexists. split.
    - sn F_17f88 D_17f88. sn F_17f8c D_17f8c. sn F_17f90 D_17f90. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_C : forall regs m (s d val : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z -> (val = 0 \/ val = 2 ^ d - 1)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 92)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)) ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 24 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x18090 : word) m rom) (mkst regs' (0x1819c : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (if Z.eq_dec val 0 then 0 else 15)
      /\ regs_agree (fun r => In r [10; 11; 12; 24]%list) regs regs'.
  Proof.
    intros regs m s d val Hs Hs64 Hd Hval Rd H2 H24.
    assert (SCRIPT : forall dd vv : Z, (dd = 1 \/ dd = 8)%Z -> (vv = 0 \/ vv = 2 ^ dd - 1)%Z -> d = dd -> val = vv -> exists regs',
      msteps SEGS (mkst regs (0x18090 : word) m rom) (mkst regs' (0x1819c : word) m rom)
      /\ getr regs' 24 = Z_to_bv 64 (if Z.eq_dec vv 0 then 0 else 15) /\ regs_agree (fun r => In r [10; 11; 12; 24]%list) regs regs').
    { intros dd vv Hdd Hvv -> ->.
      destruct Hdd as [-> | ->]; destruct Hvv as [-> | ->]; cbn [Z.eq_dec Z.pow Z.sub] ; (eexists; split;
      [ first [ stepLD F_17f94 D_17f94 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rdn_addr (s - 92)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia)
              | stepLD F_17f94 D_17f94 (word_to_le_bytes 4 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdn_addr (s - 92)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia) ];
        sn F_17f98 D_17f98;
        stepb_tk F_17f9c D_17f9c ltac:(cond_compute);
        sn F_18078 D_18078; stepb_ft F_1807c D_1807c ltac:(cond_compute);
        sn F_18080 D_18080; sn F_18084 D_18084; sn F_18088 D_18088; sn F_1808c D_1808c;
        first [ stepb_ft F_18090 D_18090 ltac:(condG); sn F_18094 D_18094; sn F_18098 D_18098
              | stepb_tk F_18090 D_18090 ltac:(condG); stepb_tk F_17fac D_17fac ltac:(cond_compute); sn F_1809c D_1809c ];
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
      msteps SEGS (mkst regs (0x1819c : word) m rom)
                  (mkst regs' (0x1e488 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x181c4 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 left /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd left hd op Hs Hs64 SOK H2 H20 H18 H23 H24. eexists. split.
    - stepST F_180a0 D_180a0 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_180a4 D_180a4. sn F_180a8 D_180a8. sn F_180ac D_180ac. sn F_180b0 D_180b0. sn F_180b4 D_180b4. sn F_180b8 D_180b8.
      sn F_180bc D_180bc. sn F_180c0 D_180c0. sn F_180c4 D_180c4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R2 : forall regs m (s pixd wd right hd op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= right <= wd)%Z -> (wd < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 21 = Z_to_bv 64 wd -> getr regs 22 = Z_to_bv 64 right ->
    getr regs 23 = Z_to_bv 64 hd -> getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x181c4 : word) m rom)
                  (mkst regs' (0x1e488 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x181f8 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 (wd - right) /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 right /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd wd right hd op Hs Hs64 Hr Hwd SOK H2 H20 H21 H22 H23 H24. eexists. split.
    - sn F_180c8 D_180c8. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_180cc D_180cc. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite subw_fit by lia; reflexivity).
      stepb_ft F_180d0 D_180d0 ltac:(condG).
      sn F_180d4 D_180d4. fixv (Z_to_bv 64 (wd - right)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepST F_180d8 D_180d8 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_180dc D_180dc. sn F_180e0 D_180e0. sn F_180e4 D_180e4. sn F_180e8 D_180e8. sn F_180ec D_180ec.
      sn F_180f0 D_180f0. sn F_180f4 D_180f4. sn F_180f8 D_180f8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R3 : forall regs m (s pixd wd top op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 21 = Z_to_bv 64 wd -> getr regs 9 = Z_to_bv 64 top ->
    getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x181f8 : word) m rom)
                  (mkst regs' (0x1e488 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x18220 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 top /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd wd top op Hs Hs64 SOK H2 H20 H21 H9 H24. eexists. split.
    - stepST F_180fc D_180fc (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_18100 D_18100. sn F_18104 D_18104. sn F_18108 D_18108. sn F_1810c D_1810c. sn F_18110 D_18110. sn F_18114 D_18114.
      sn F_18118 D_18118. sn F_1811c D_1811c. sn F_18120 D_18120. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R4 : forall regs m (s pixd hd wd bot op : Z),
    (112 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= bot <= hd)%Z -> (hd < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 hd -> getr regs 21 = Z_to_bv 64 wd ->
    getr regs 19 = Z_to_bv 64 bot -> getr regs 24 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x18220 : word) m rom)
                  (mkst regs' (0x1e488 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x18254 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (hd - bot)
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 bot /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd hd wd bot op Hs Hs64 Hb Hhd SOK H2 H20 H23 H21 H19 H24. eexists. split.
    - sn F_18124 D_18124. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_18128 D_18128. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite subw_fit by lia; reflexivity).
      stepb_ft F_1812c D_1812c ltac:(condG).
      sn F_18130 D_18130. fixv (Z_to_bv 64 (hd - bot)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      stepST F_18134 D_18134 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_18138 D_18138. sn F_1813c D_1813c. sn F_18140 D_18140. sn F_18144 D_18144. sn F_18148 D_18148.
      sn F_1814c D_1814c. sn F_18150 D_18150. sn F_18154 D_18154. apply mst_refl.
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
      msteps SEGS (mkst regs (0x18254 : word) m rom)
                  (mkst regs' (0x1e488 : word) (wbytes m (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1827c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 left /\ getr regs' 12 = Z_to_bv 64 top
      /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top w h Hs Hs64 Hw Hh SOK Rw Rh H2 H20 H8 H18 H9. eexists. split.
    - stepLD F_18158 D_18158 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(rdn_addr (s - 84)%Z; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small w) by lia.
      stepLD F_1815c D_1815c (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(rdn_addr (s - 88)%Z; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small h) by lia.
      sn F_18160 D_18160.
      stepST F_18164 D_18164 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_18168 D_18168. sn F_1816c D_1816c. sn F_18170 D_18170. sn F_18174 D_18174. sn F_18178 D_18178. sn F_1817c D_1817c.
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
    zv F_18208 D_18208 (Z_to_bv 64 (s - 96));
    stepST F_1820c D_1820c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
    stepST F_18210 D_18210 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
    stepST F_18214 D_18214 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
    stepST F_18218 D_18218 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
    stepST F_1821c D_1821c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK);
    stepST F_18220 D_18220 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK);
    stepST F_18224 D_18224 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK);
    stepST F_18228 D_18228 (Z_to_bv 64 (s - 64)) (getr regs 23) ltac:(sok_in SOK).

  (* [comment removed for export] *)
  Lemma rb_A : forall regs m (s pixs left right top bot : Z) (vs : pixv) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 96 \/ s <= pixs)%Z ->
    (0 <= left <= 64)%Z -> (0 <= right <= 64)%Z -> (0 <= top <= 64)%Z -> (0 <= bot <= 64)%Z ->
    (1 <= p_w vs <= 20000)%Z -> (1 <= p_h vs <= 20000)%Z -> (1 <= p_w vs - left - right)%Z -> (1 <= p_h vs - top - bot)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot ->
    exists regs',
      msteps SEGS (mkst regs (0x18304 : word) m rom)
                  (mkst regs' (0x15c00 : word) (DIMS (FRR m s ret regs) (s - 68) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x183b8
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
      stepb_ft F_1822c D_1822c ltac:(condZ).
      sn F_18230 D_18230. sn F_18234 D_18234. sn F_18238 D_18238. sn F_1823c D_1823c.
      stepat F_18240 D_18240 (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_18244 D_18244 (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_18248 D_18248 (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_1824c D_1824c ltac:(condZ).
      zv F_18250 D_18250 (Z_to_bv 64 (s - 68)). zv F_18254 D_18254 (Z_to_bv 64 (s - 72)). zv F_18258 D_18258 (Z_to_bv 64 (s - 76)).
      sn F_1825c D_1825c. sn F_18260 D_18260.
      (* [comment removed for export] *)
      zand F_1636c D_1636c andi_3 SL68. stepb_ft F_16370 D_16370 ltac:(condZ). stepb_ft F_16374 D_16374 ltac:(condR).
      stepST F_16378 D_16378 (Z_to_bv 64 (s - 68)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_1637c D_1637c andi_3 SL72. stepb_ft F_16380 D_16380 ltac:(condZ). stepb_ft F_16384 D_16384 ltac:(condR).
      stepST F_16388 D_16388 (Z_to_bv 64 (s - 68 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_1638c D_1638c andi_3 SL76. stepb_ft F_16390 D_16390 ltac:(condZ). stepb_ft F_16394 D_16394 ltac:(condR).
      stepST F_16398 D_16398 (Z_to_bv 64 (s - 68 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_1639c D_1639c ltac:(condZ).
      zand F_163a0 D_163a0 andi_7 ALp.
      stepb_ft F_163a4 D_163a4 ltac:(condZ). sn F_163a8 D_163a8. stepb_ft F_163ac D_163ac ltac:(condR).
      stepLD F_163b0 D_163b0 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_163b4 D_163b4 (Z_to_bv 64 (s - 68)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_163b8 D_163b8 ltac:(condZ). sn F_163bc D_163bc. stepb_ft F_163c0 D_163c0 ltac:(condR).
      stepLD F_163c4 D_163c4 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_163c8 D_163c8 (Z_to_bv 64 (s - 68 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      stepb_ft F_163cc D_163cc ltac:(condZ). sn F_163d0 D_163d0. stepb_ft F_163d4 D_163d4 ltac:(condR).
      stepLD F_163d8 D_163d8 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_163dc D_163dc (Z_to_bv 64 (s - 68 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_163e0 D_163e0.
      stepret F_163e4 D_163e4 (0x18360 : word) ltac:(bveq).
      (* [comment removed for export] *)
      ldcell F_18264 D_18264 (s - 68)%Z (p_w vs).
      sn F_18268 D_18268. fixv (Z_to_bv 64 (p_w vs - left)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_1826c D_1826c. fixv (Z_to_bv 64 (p_w vs - left)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_18270 D_18270 ltac:(condG).
      sn F_18274 D_18274. fixv (Z_to_bv 64 (p_w vs - left)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_18278 D_18278. fixv (Z_to_bv 64 (p_w vs - left - right)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      sn F_1827c D_1827c. fixv (Z_to_bv 64 (p_w vs - left - right)) ltac:(rewrite zbv_sub; reflexivity).
      stepb_ft F_18280 D_18280 ltac:(condG).
      ldcell F_18284 D_18284 (s - 68 - 4)%Z (p_h vs).
      sn F_18288 D_18288. fixv (Z_to_bv 64 (p_h vs - top)) ltac:(rewrite zbv_sub; reflexivity).
      sn F_1828c D_1828c. fixv (Z_to_bv 64 (p_h vs - top)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      stepb_ft F_18290 D_18290 ltac:(condG).
      sn F_18294 D_18294. fixv (Z_to_bv 64 (p_h vs - top)) ltac:(rewrite zbv_addiw_small by lia; f_equal; lia).
      sn F_18298 D_18298. fixv (Z_to_bv 64 (p_h vs - top - bot)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      sn F_1829c D_1829c. fixv (Z_to_bv 64 (p_h vs - top - bot)) ltac:(rewrite zbv_sub; reflexivity).
      stepb_ft F_182a0 D_182a0 ltac:(condG).
      stepb_ft F_182a4 D_182a4 ltac:(condZ).
      stepb_ft F_182a8 D_182a8 ltac:(condZ).
      ldcell F_182ac D_182ac (s - 68 - 8)%Z (p_d vs).
      sn F_182b0 D_182b0. sn F_182b4 D_182b4. sn F_182b8 D_182b8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_N1 : forall regs m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x18304 : word) m rom) (mkst regs' (0x18450 : word) (FRR m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96)
      /\ regs_agree (fun r => In r [2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10. unfold FRR. eexists. split.
    - rb_prologue s ret regs SOK.
      stepb_tk F_1822c D_1822c ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_N2 : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x33d90) 8 = Some (Z_to_le_bytes 8 0x34e00) -> rdn SEGS m (Z_to_bv 64 0x34e00) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameR s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x18450 : word) m rom) (mkst regs' (0x1586c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10e5b
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Rg Rs CE H2. unfold frameR in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    eexists. split.
    - sn F_18354 D_18354.
      stepLD F_18358 D_18358 (Z_to_le_bytes 8 0x34e00) (Z_to_bv 64 0x34e00) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_1835c D_1835c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_18360 D_18360. stepb_ft F_18364 D_18364 ltac:(condZ).
      sn F_18368 D_18368. sn F_1836c D_1836c. sn F_18370 D_18370. sn F_18374 D_18374. sn F_18378 D_18378.
      sn F_183a0 D_183a0.
      stepLD8 F_183a4 D_183a4 ret. stepLD8 F_183a8 D_183a8 (getr r0 8). stepLD8 F_183ac D_183ac (getr r0 9).
      stepLD8 F_183b0 D_183b0 (getr r0 18). stepLD8 F_183b4 D_183b4 (getr r0 19). stepLD8 F_183b8 D_183b8 (getr r0 20).
      stepLD8 F_183bc D_183bc (getr r0 21). stepLD8 F_183c0 D_183c0 (getr r0 23).
      zv F_183c4 D_183c4 (Z_to_bv 64 s). sn F_183c8 D_183c8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x33d90) 8 = Some (Z_to_le_bytes 8 0x34e00) -> rdn SEGS m (Z_to_bv 64 0x34e00) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x183b8 : word) m rom) (mkst regs' (0x1586c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x18544 /\ getr regs' 10 = Z_to_bv 64 0x1054a /\ getr regs' 11 = Z_to_bv 64 0x10e5b /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_182bc D_182bc ltac:(condZ).
      sn F_1841c D_1841c.
      stepLD F_18420 D_18420 (Z_to_le_bytes 8 0x34e00) (Z_to_bv 64 0x34e00) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_18424 D_18424 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_18428 D_18428. stepb_ft F_1842c D_1842c ltac:(condZ).
      sn F_18430 D_18430. sn F_18434 D_18434. sn F_18438 D_18438. sn F_1843c D_1843c. sn F_18440 D_18440. sn F_18444 D_18444.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_E : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameR s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x1854c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Hret CE H2. unfold frameR in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    eexists. split.
    - stepLD8 F_18450 D_18450 ret. stepLD8 F_18454 D_18454 (getr r0 8). stepLD8 F_18458 D_18458 (getr r0 9).
      stepLD8 F_1845c D_1845c (getr r0 18). stepLD8 F_18460 D_18460 (getr r0 19). stepLD8 F_18464 D_18464 (getr r0 20).
      stepLD8 F_18468 D_18468 (getr r0 21). stepLD8 F_1846c D_1846c (getr r0 23).
      zv F_18470 D_18470 (Z_to_bv 64 s). stepret F_18474 D_18474 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  Lemma rb_F2 : forall regs m, exists regs',
      msteps SEGS (mkst regs (0x18544 : word) m rom) (mkst regs' (0x1854c : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_18448 D_18448; apply mst_refl | solve_regs_agree]. Qed.

  (* [comment removed for export] *)
  Lemma rb_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x183b8 : word) m rom) (mkst regs' (0x16600 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x183c8 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 21 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 21]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H18. eexists. split.
    - stepb_ft F_182bc D_182bc ltac:(condZ).
      sn F_182c0 D_182c0. sn F_182c4 D_182c4. sn F_182c8 D_182c8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma rb_B2 : forall regs m (pixd pixs : Z),
    getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x183c8 : word) m rom) (mkst regs' (0x16524 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x183d4 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H21 H18. eexists. split.
    - sn F_182cc D_182cc. sn F_182d0 D_182d0. sn F_182d4 D_182d4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma rb_B3 : forall regs m (pixd pixs : Z),
    getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x183d4 : word) m rom) (mkst regs' (0x16690 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x183e0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H21 H18. eexists. split.
    - sn F_182d8 D_182d8. sn F_182dc D_182dc. sn F_182e0 D_182e0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_R : forall regs m (s pixd pixs left top wd hd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs -> getr regs 9 = Z_to_bv 64 left ->
    getr regs 8 = Z_to_bv 64 top -> getr regs 19 = Z_to_bv 64 wd -> getr regs 20 = Z_to_bv 64 hd ->
    exists regs',
      msteps SEGS (mkst regs (0x183e0 : word) m rom)
                  (mkst regs' (0x1e488 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 top))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1840c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 left /\ getr regs' 23 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 23]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top wd hd Hs Hs64 SOK H2 H21 H18 H9 H8 H19 H20. eexists. split.
    - sn F_182e4 D_182e4.
      stepST F_182e8 D_182e8 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 top) ltac:(sok_in SOK).
      sn F_182ec D_182ec. sn F_182f0 D_182f0. sn F_182f4 D_182f4. sn F_182f8 D_182f8. sn F_182fc D_182fc. sn F_18300 D_18300.
      sn F_18304 D_18304. sn F_18308 D_18308. sn F_1830c D_1830c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_D : forall regs m (pixs pixd : Z) (vs : pixv),
    (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> (p_d vs = 1 \/ p_d vs = 8)%Z ->
    getr regs 18 = Z_to_bv 64 pixs -> getr regs 23 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x1840c : word) m rom) (mkst regs' (0x1854c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixs pixd vs Hp ALp PX Hd H18 H23. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd.
    eexists. split.
    - sn F_18310 D_18310. sn F_18314 D_18314.
      stepb_ft F_170a8 D_170a8 ltac:(condZ).
      zand F_170ac D_170ac andi_7 ALp. stepb_ft F_170b0 D_170b0 ltac:(condR).
      stepLD F_170b4 D_170b4 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepret F_170b8 D_170b8 (0x18414 : word) ltac:(bveq).
      sn F_18318 D_18318.
      stepb_tk F_1831c D_1831c ltac:(condZ).
      sn F_1834c D_1834c. sn F_18350 D_18350.
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

Lemma str_pixAddBorderGeneral : str16 0x10cd9 19. Proof. str16_tac. Qed.

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

Lemma str_pixRemoveBorderGeneral : str16 0x10e5b 22. Proof. str16_tac. Qed.
Lemma str_msg_pixs_undef : str16 0x10298 16. Proof. str16_tac. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SegsWrap.
Variable rom : word -> option byte.

  Lemma pab_run : forall regs m (pixs npix val : Z),
    (1 <= pixs < 2 ^ 64)%Z -> (1 <= npix < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 npix -> getr regs 12 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x17f64 : word) m rom) (mkst regs' (0x17fb8 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 npix /\ getr regs' 13 = Z_to_bv 64 npix /\ getr regs' 14 = Z_to_bv 64 npix /\ getr regs' 15 = Z_to_bv 64 val
      /\ regs_agree (fun r => In r [12; 13; 14; 15]%list) regs regs'.
  Proof.
    intros regs m pixs npix val Hp Hn H10 H11 H12. eexists. split.
    - stepb_ft F_17e68 D_17e68 ltac:(condZ). stepb_ft F_17e6c D_17e6c ltac:(condZ).
      sn F_17e70 D_17e70. sn F_17e74 D_17e74. sn F_17e78 D_17e78. sn F_17e7c D_17e7c. sn F_17e80 D_17e80.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma prb_run : forall regs m (pixs npix : Z),
    (1 <= pixs < 2 ^ 64)%Z -> (1 <= npix < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 npix ->
    exists regs',
      msteps SEGS (mkst regs (0x182b4 : word) m rom) (mkst regs' (0x18304 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 npix /\ getr regs' 13 = Z_to_bv 64 npix /\ getr regs' 14 = Z_to_bv 64 npix
      /\ regs_agree (fun r => In r [12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m pixs npix Hp Hn H10 H11. eexists. split.
    - stepb_ft F_181b8 D_181b8 ltac:(condZ). stepb_ft F_181bc D_181bc ltac:(condZ).
      sn F_181c0 D_181c0. sn F_181c4 D_181c4. sn F_181c8 D_181c8. sn F_181cc D_181cc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma prb_N : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x33d90) 8 = Some (Z_to_le_bytes 8 0x34e00) -> rdn SEGS m (Z_to_bv 64 0x34e00) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x182b4 : word) m rom) (mkst regs' (0x1586c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10ced /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_181b8 D_181b8 ltac:(condZ).
      sn F_181d0 D_181d0.
      stepLD F_181d4 D_181d4 (Z_to_le_bytes 8 0x34e00) (Z_to_bv 64 0x34e00) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_181d8 D_181d8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_181dc D_181dc. stepb_ft F_181e0 D_181e0 ltac:(condZ).
      sn F_181e4 D_181e4. sn F_181e8 D_181e8. sn F_181ec D_181ec. sn F_181f0 D_181f0. sn F_181f4 D_181f4. sn F_181f8 D_181f8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsWrap.

Lemma str_pixRemoveBorder : str16 0x10ced 15. Proof. str16_tac. Qed.
Definition PC_pixAddBorder : Z := 0x17f64.
Definition PC_pixRemoveBorder : Z := 0x182b4.

End GrayBorder.
