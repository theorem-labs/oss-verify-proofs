(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10LeptStderr O10LeptBase.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10CL7a.
Import O10CL7a.O10LeptErr. Import O10CL7a.O10LeptRop_iface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10CL8a.
Import O10CL8a.O10LeptPixHdr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10LeptPixCreate O10LeptCmapValid O10LeptCmap2 O10LeptPixCopyA O10LeptPixCopy O10LeptGrayA O10_code_fhH.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
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

Section GrayBorder.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O10Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition FRA (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
    (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)).
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
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 128 \/ s <= pixs)%Z ->
    (0 <= left <= 64)%Z -> (0 <= right <= 64)%Z -> (0 <= top <= 64)%Z -> (0 <= bot <= 64)%Z ->
    (1 <= p_w vs <= 20000)%Z -> (1 <= p_h vs <= 20000)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 128)) 128 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot ->
    getr regs 15 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x177d4 : word) m rom)
                  (mkst regs' (0x15ab0 : word) (DIMS (FRA m s ret regs) (s - 100) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 1 = Z_to_bv 64 0x17870
      /\ getr regs' 10 = Z_to_bv 64 (p_w vs + left + right) /\ getr regs' 11 = Z_to_bv 64 (p_h vs + top + bot) /\ getr regs' 12 = Z_to_bv 64 (p_d vs)
      /\ getr regs' 8 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 left /\ getr regs' 21 = Z_to_bv 64 right
      /\ getr regs' 9 = Z_to_bv 64 top /\ getr regs' 20 = Z_to_bv 64 bot /\ getr regs' 26 = Z_to_bv 64 val
      /\ getr regs' 24 = Z_to_bv 64 (p_w vs + left) /\ getr regs' 23 = Z_to_bv 64 (p_h vs + top)
      /\ getr regs' 22 = Z_to_bv 64 (p_w vs + left + right) /\ getr regs' 25 = Z_to_bv 64 (p_h vs + top + bot)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s pixs left right top bot val vs ret Hs Hs64 Hp PX DJ Hl Hr Ht Hb Hw Hh SOK H2 H1 H10 H11 H12 H13 H14 H15.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof (lor_small right left 31 ltac:(lia) ltac:(lia) ltac:(lia)) as O1.
    pose proof (lor_small top bot 31 ltac:(lia) ltac:(lia) ltac:(lia)) as O2.
    pose proof (lor_small _ _ 31 ltac:(lia) O1 O2) as O3.
    assert (PX1 : PIXat (FRA m s ret regs) pixs vs).
    { unfold FRA. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    assert (PXk : forall M a bs, PIXat M pixs vs -> (s - 128 <= a)%Z -> (a + Z.of_nat (length bs) <= s)%Z -> PIXat (wbytes M (Z_to_bv 64 a) bs) pixs vs).
    { intros M a bs P Ha Hb'. apply PIXat_out; [exact P | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia]. }
    unfold DIMS, FRA in *. eexists. split.
    - zv F_176d8 D_176d8 (Z_to_bv 64 (s - 128)).
      stepST F_176dc D_176dc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_176e0 D_176e0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_176e4 D_176e4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_176e8 D_176e8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_176ec D_176ec (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_176f0 D_176f0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_176f4 D_176f4 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_176f8 D_176f8 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_176fc D_176fc (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_17700 D_17700 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_17704 D_17704 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_17708 D_17708 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepb_ft F_1770c D_1770c ltac:(condZ).
      sn F_17710 D_17710. sn F_17714 D_17714. sn F_17718 D_17718. sn F_1771c D_1771c. sn F_17720 D_17720.
      stepat F_17724 D_17724 (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_17728 D_17728 (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_1772c D_1772c (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_17730 D_17730 ltac:(condZ).
      sn F_17734 D_17734.
      zv F_17738 D_17738 (Z_to_bv 64 (s - 100)). zv F_1773c D_1773c (Z_to_bv 64 (s - 104)). zv F_17740 D_17740 (Z_to_bv 64 (s - 108)).
      sn F_17744 D_17744. sn F_17748 D_17748.
      (* [comment removed for export] *)
      stepb_ft F_16174 D_16174 ltac:(condZ).
      stepST F_16178 D_16178 (Z_to_bv 64 (s - 100)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_1617c D_1617c ltac:(condZ).
      stepST F_16180 D_16180 (Z_to_bv 64 (s - 100 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_16184 D_16184 ltac:(condZ).
      stepST F_16188 D_16188 (Z_to_bv 64 (s - 100 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_1618c D_1618c ltac:(condZ).
      stepb_ft F_16190 D_16190 ltac:(condZ).
      stepLD F_16194 D_16194 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_16198 D_16198 (Z_to_bv 64 (s - 100)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_1619c D_1619c ltac:(condZ).
      stepLD F_161a0 D_161a0 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_161a4 D_161a4 (Z_to_bv 64 (s - 100 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      sn F_161a8 D_161a8.
      stepb_ft F_161ac D_161ac ltac:(condZ).
      stepLD F_161b0 D_161b0 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_161b4 D_161b4 (Z_to_bv 64 (s - 100 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_161b8 D_161b8.
      stepret F_161bc D_161bc (0x17848 : word) ltac:(bveq).
      (* [comment removed for export] *)
      ldcell F_1774c D_1774c (s - 100)%Z (p_w vs).
      ldcell F_17750 D_17750 (s - 100 - 4)%Z (p_h vs).
      ldcell F_17754 D_17754 (s - 100 - 8)%Z (p_d vs).
      sn F_17758 D_17758. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_1775c D_1775c. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_17760 D_17760. fixv (Z_to_bv 64 (p_w vs + left + right)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_17764 D_17764. fixv (Z_to_bv 64 (p_h vs + top + bot)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_17768 D_17768. sn F_1776c D_1776c. sn F_17770 D_17770.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x17870 : word) m rom) (mkst regs' (0x1573c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17a04 /\ getr regs' 10 = Z_to_bv 64 0x1054a /\ getr regs' 11 = Z_to_bv 64 0x10cd9 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_17774 D_17774 ltac:(condZ).
      sn F_178dc D_178dc.
      stepLD F_178e0 D_178e0 (Z_to_le_bytes 8 0x2ca88) (Z_to_bv 64 0x2ca88) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_178e4 D_178e4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_178e8 D_178e8. stepb_ft F_178ec D_178ec ltac:(condZ).
      sn F_178f0 D_178f0. sn F_178f4 D_178f4. sn F_178f8 D_178f8. sn F_178fc D_178fc. sn F_17900 D_17900. sn F_17904 D_17904.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F2 : forall regs m (res : Z),
    getr regs 10 = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (0x17a04 : word) m rom) (mkst regs' (0x17a54 : word) m rom)
      /\ getr regs' 19 = Z_to_bv 64 res /\ regs_agree (fun r => In r [19]%list) regs regs'.
  Proof.
    intros regs m res H10. eexists. split.
    - sn F_17908 D_17908. sn F_1790c D_1790c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition frameA (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
    [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, getr r0 19); ((s - 48)%Z, getr r0 20);
     ((s - 56)%Z, getr r0 21); ((s - 64)%Z, getr r0 22); ((s - 72)%Z, getr r0 23); ((s - 80)%Z, getr r0 24); ((s - 88)%Z, getr r0 25); ((s - 96)%Z, getr r0 26)].

  (* [comment removed for export] *)
  Lemma ab_E : forall regs r0 m (s res : Z) (ret : word),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameA s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 19 = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (0x17a54 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 res
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs r0 m s res ret Hs Hs64 Hret CE H2 H19. unfold frameA in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & _).
    eexists. split.
    - sn F_17958 D_17958.
      stepLD8 F_1795c D_1795c ret. stepLD8 F_17960 D_17960 (getr r0 8). stepLD8 F_17964 D_17964 (getr r0 9).
      stepLD8 F_17968 D_17968 (getr r0 18). stepLD8 F_1796c D_1796c (getr r0 19). stepLD8 F_17970 D_17970 (getr r0 20).
      stepLD8 F_17974 D_17974 (getr r0 21). stepLD8 F_17978 D_17978 (getr r0 22). stepLD8 F_1797c D_1797c (getr r0 23).
      stepLD8 F_17980 D_17980 (getr r0 24). stepLD8 F_17984 D_17984 (getr r0 25). stepLD8 F_17988 D_17988 (getr r0 26).
      zv F_1798c D_1798c (Z_to_bv 64 s). stepret F_17990 D_17990 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x17870 : word) m rom) (mkst regs' (0x163c0 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17880 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 19 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 19]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H8. eexists. split.
    - stepb_ft F_17774 D_17774 ltac:(condZ).
      sn F_17778 D_17778. sn F_1777c D_1777c. sn F_17780 D_17780. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B2 : forall regs m (pixd pixs : Z),
    getr regs 19 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x17880 : word) m rom) (mkst regs' (0x16448 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1788c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H19 H8. eexists. split.
    - sn F_17784 D_17784. sn F_17788 D_17788. sn F_1778c D_1778c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_C0 : forall regs m,
    getr regs 26 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x1788c : word) m rom) (mkst regs' (0x178ac : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros regs m H26. eexists. split.
    - stepb_tk F_17790 D_17790 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_C15 : forall regs m (s d val : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z -> val = (2 ^ d - 1)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)) ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 26 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x1788c : word) m rom) (mkst regs' (0x178ac : word) m rom)
      /\ getr regs' 26 = Z_to_bv 64 15
      /\ regs_agree (fun r => In r [10; 11; 12; 26]%list) regs regs'.
  Proof.
    intros regs m s d val Hs Hs64 Hd Hval Rd H2 H26.
    assert (SCRIPT : forall dd : Z, (dd = 1 \/ dd = 8)%Z -> d = dd -> exists regs',
      msteps SEGS (mkst regs (0x1788c : word) m rom) (mkst regs' (0x178ac : word) m rom)
      /\ getr regs' 26 = Z_to_bv 64 15 /\ regs_agree (fun r => In r [10; 11; 12; 26]%list) regs regs').
    { intros dd Hdd ->. subst val.
      destruct Hdd as [-> | ->]; (eexists; split;
      [ stepb_ft F_17790 D_17790 ltac:(condZ);
        sn F_17794 D_17794;
        first [ stepLD F_17798 D_17798 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rdn_addr (s - 108)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia)
              | stepLD F_17798 D_17798 (word_to_le_bytes 4 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdn_addr (s - 108)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia) ];
        sn F_1779c D_1779c;
        stepb_tk F_177a0 D_177a0 ltac:(condZ);
        sn F_17918 D_17918; sn F_1791c D_1791c; sn F_17920 D_17920;
        stepb_tk F_17924 D_17924 ltac:(cond_compute);
        sn F_177ac D_177ac;
        apply mst_refl
      | repeat split; gres; pin; try reflexivity; solve_regs_agree ]). }
    exact (SCRIPT d Hd eq_refl).
  Qed.

  (* [comment removed for export] *)
  Lemma ab_R1 : forall regs m (s pixd left hd op : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 left -> getr regs 25 = Z_to_bv 64 hd ->
    getr regs 26 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x178ac : word) m rom)
                  (mkst regs' (0x1c5a4 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x178d4 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 left /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd left hd op Hs Hs64 SOK H2 H19 H18 H25 H26. eexists. split.
    - stepST F_177b0 D_177b0 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_177b4 D_177b4. sn F_177b8 D_177b8. sn F_177bc D_177bc. sn F_177c0 D_177c0. sn F_177c4 D_177c4. sn F_177c8 D_177c8.
      sn F_177cc D_177cc. sn F_177d0 D_177d0. sn F_177d4 D_177d4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R2 : forall regs m (s pixd x right hd op : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 24 = Z_to_bv 64 x -> getr regs 21 = Z_to_bv 64 right ->
    getr regs 25 = Z_to_bv 64 hd -> getr regs 26 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x178d4 : word) m rom)
                  (mkst regs' (0x1c5a4 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x178fc /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 x /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 right /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd x right hd op Hs Hs64 SOK H2 H19 H24 H21 H25 H26. eexists. split.
    - stepST F_177d8 D_177d8 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_177dc D_177dc. sn F_177e0 D_177e0. sn F_177e4 D_177e4. sn F_177e8 D_177e8. sn F_177ec D_177ec. sn F_177f0 D_177f0.
      sn F_177f4 D_177f4. sn F_177f8 D_177f8. sn F_177fc D_177fc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R3 : forall regs m (s pixd wd top op : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 22 = Z_to_bv 64 wd -> getr regs 9 = Z_to_bv 64 top ->
    getr regs 26 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x178fc : word) m rom)
                  (mkst regs' (0x1c5a4 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17924 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 top /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd wd top op Hs Hs64 SOK H2 H19 H22 H9 H26. eexists. split.
    - stepST F_17800 D_17800 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_17804 D_17804. sn F_17808 D_17808. sn F_1780c D_1780c. sn F_17810 D_17810. sn F_17814 D_17814. sn F_17818 D_17818.
      sn F_1781c D_1781c. sn F_17820 D_17820. sn F_17824 D_17824. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R4 : forall regs m (s pixd y wd bot op : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 y -> getr regs 22 = Z_to_bv 64 wd ->
    getr regs 20 = Z_to_bv 64 bot -> getr regs 26 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x17924 : word) m rom)
                  (mkst regs' (0x1c5a4 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1794c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 y
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 bot /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd y wd bot op Hs Hs64 SOK H2 H19 H23 H22 H20 H26. eexists. split.
    - stepST F_17828 D_17828 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_1782c D_1782c. sn F_17830 D_17830. sn F_17834 D_17834. sn F_17838 D_17838. sn F_1783c D_1783c. sn F_17840 D_17840.
      sn F_17844 D_17844. sn F_17848 D_17848. sn F_1784c D_1784c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_R5 : forall regs m (s pixd pixs left top w h : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 100)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
    rdn SEGS m (Z_to_bv 64 (s - 104)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs -> getr regs 18 = Z_to_bv 64 left ->
    getr regs 9 = Z_to_bv 64 top ->
    exists regs',
      msteps SEGS (mkst regs (0x1794c : word) m rom)
                  (mkst regs' (0x1c5a4 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17a54 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 left /\ getr regs' 12 = Z_to_bv 64 top
      /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top w h Hs Hs64 Hw Hh SOK Rw Rh H2 H19 H8 H18 H9. eexists. split.
    - sn F_17850 D_17850.
      stepLD F_17930 D_17930 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(rdn_addr (s - 100)%Z; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small w) by lia.
      stepLD F_17934 D_17934 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(rdn_addr (s - 104)%Z; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small h) by lia.
      sn F_17938 D_17938.
      stepST F_1793c D_1793c (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_17940 D_17940. sn F_17944 D_17944. sn F_17948 D_17948. sn F_1794c D_1794c. sn F_17950 D_17950. sn F_17954 D_17954.
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
    zv F_179e4 D_179e4 (Z_to_bv 64 (s - 96));
    stepST F_179e8 D_179e8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
    stepST F_179ec D_179ec (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
    stepST F_179f0 D_179f0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
    stepST F_179f4 D_179f4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
    stepST F_179f8 D_179f8 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK);
    stepST F_179fc D_179fc (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK);
    stepST F_17a00 D_17a00 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK);
    stepST F_17a04 D_17a04 (Z_to_bv 64 (s - 64)) (getr regs 23) ltac:(sok_in SOK).

  (* [comment removed for export] *)
  Lemma rb_A : forall regs m (s pixs left right top bot : Z) (vs : pixv) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 96 \/ s <= pixs)%Z ->
    (0 <= left <= 64)%Z -> (0 <= right <= 64)%Z -> (0 <= top <= 64)%Z -> (0 <= bot <= 64)%Z ->
    (1 <= p_w vs <= 20000)%Z -> (1 <= p_h vs <= 20000)%Z -> (1 <= p_w vs - left - right)%Z -> (1 <= p_h vs - top - bot)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot ->
    exists regs',
      msteps SEGS (mkst regs (0x17ae0 : word) m rom)
                  (mkst regs' (0x15ab0 : word) (DIMS (FRR m s ret regs) (s - 68) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x17b6c
      /\ getr regs' 10 = Z_to_bv 64 (p_w vs - left - right) /\ getr regs' 11 = Z_to_bv 64 (p_h vs - top - bot) /\ getr regs' 12 = Z_to_bv 64 (p_d vs)
      /\ getr regs' 8 = Z_to_bv 64 top /\ getr regs' 9 = Z_to_bv 64 left /\ getr regs' 18 = Z_to_bv 64 pixs
      /\ getr regs' 19 = Z_to_bv 64 (p_w vs - left - right) /\ getr regs' 20 = Z_to_bv 64 (p_h vs - top - bot)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s pixs left right top bot vs ret Hs Hs64 Hp PX DJ Hl Hr Ht Hb Hw Hh Hwd Hhd SOK H2 H1 H10 H11 H12 H13 H14.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof (lor_small right left 31 ltac:(lia) ltac:(lia) ltac:(lia)) as O1.
    pose proof (lor_small top bot 31 ltac:(lia) ltac:(lia) ltac:(lia)) as O2.
    pose proof (lor_small _ _ 31 ltac:(lia) O1 O2) as O3.
    assert (PXk : forall M a bs, PIXat M pixs vs -> (s - 96 <= a)%Z -> (a + Z.of_nat (length bs) <= s)%Z -> PIXat (wbytes M (Z_to_bv 64 a) bs) pixs vs).
    { intros M a bs P Ha Hb'. apply PIXat_out; [exact P | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia]. }
    unfold DIMS, FRR in *. eexists. split.
    - rb_prologue s ret regs SOK.
      stepb_ft F_17a08 D_17a08 ltac:(condZ).
      sn F_17a0c D_17a0c. sn F_17a10 D_17a10. sn F_17a14 D_17a14.
      stepat F_17a18 D_17a18 (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_17a1c D_17a1c (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_17a20 D_17a20 (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_17a24 D_17a24 ltac:(condZ).
      sn F_17a28 D_17a28.
      zv F_17a2c D_17a2c (Z_to_bv 64 (s - 68)). zv F_17a30 D_17a30 (Z_to_bv 64 (s - 72)). zv F_17a34 D_17a34 (Z_to_bv 64 (s - 76)).
      sn F_17a38 D_17a38. sn F_17a3c D_17a3c.
      (* [comment removed for export] *)
      stepb_ft F_16174 D_16174 ltac:(condZ).
      stepST F_16178 D_16178 (Z_to_bv 64 (s - 68)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_1617c D_1617c ltac:(condZ).
      stepST F_16180 D_16180 (Z_to_bv 64 (s - 68 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_16184 D_16184 ltac:(condZ).
      stepST F_16188 D_16188 (Z_to_bv 64 (s - 68 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_1618c D_1618c ltac:(condZ).
      stepb_ft F_16190 D_16190 ltac:(condZ).
      stepLD F_16194 D_16194 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_16198 D_16198 (Z_to_bv 64 (s - 68)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_1619c D_1619c ltac:(condZ).
      stepLD F_161a0 D_161a0 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_161a4 D_161a4 (Z_to_bv 64 (s - 68 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      sn F_161a8 D_161a8.
      stepb_ft F_161ac D_161ac ltac:(condZ).
      stepLD F_161b0 D_161b0 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_161b4 D_161b4 (Z_to_bv 64 (s - 68 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_161b8 D_161b8.
      stepret F_161bc D_161bc (0x17b3c : word) ltac:(bveq).
      (* [comment removed for export] *)
      ldcell F_17a40 D_17a40 (s - 68)%Z (p_w vs).
      zv F_17a44 D_17a44 (Z_to_bv 64 (right + left)).
      sn F_17a48 D_17a48. fixv (Z_to_bv 64 (p_w vs - left - right)) ltac:(rewrite v_subw_Z, sw32_small by lia; f_equal; lia).
      stepb_ft F_17a4c D_17a4c ltac:(condZ).
      ldcell F_17a50 D_17a50 (s - 68 - 4)%Z (p_h vs).
      zv F_17a54 D_17a54 (Z_to_bv 64 (bot + top)).
      sn F_17a58 D_17a58. fixv (Z_to_bv 64 (p_h vs - top - bot)) ltac:(rewrite v_subw_Z, sw32_small by lia; f_equal; lia).
      stepb_ft F_17a5c D_17a5c ltac:(condZ).
      ldcell F_17a60 D_17a60 (s - 68 - 8)%Z (p_d vs).
      sn F_17a64 D_17a64. sn F_17a68 D_17a68. sn F_17a6c D_17a6c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_N1 : forall regs m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x17ae0 : word) m rom) (mkst regs' (0x17c04 : word) (FRR m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96)
      /\ regs_agree (fun r => In r [2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10. unfold FRR. eexists. split.
    - rb_prologue s ret regs SOK.
      stepb_tk F_17a08 D_17a08 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_N2 : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameR s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x17c04 : word) m rom) (mkst regs' (0x1573c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10e5b
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Rg Rs CE H2. unfold frameR in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    eexists. split.
    - sn F_17b08 D_17b08.
      stepLD F_17b0c D_17b0c (Z_to_le_bytes 8 0x2ca88) (Z_to_bv 64 0x2ca88) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_17b10 D_17b10 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_17b14 D_17b14. stepb_ft F_17b18 D_17b18 ltac:(condZ).
      sn F_17b1c D_17b1c. sn F_17b20 D_17b20. sn F_17b24 D_17b24. sn F_17b28 D_17b28. sn F_17b2c D_17b2c.
      sn F_17b54 D_17b54.
      stepLD8 F_17b58 D_17b58 ret. stepLD8 F_17b5c D_17b5c (getr r0 8). stepLD8 F_17b60 D_17b60 (getr r0 9).
      stepLD8 F_17b64 D_17b64 (getr r0 18). stepLD8 F_17b68 D_17b68 (getr r0 19). stepLD8 F_17b6c D_17b6c (getr r0 20).
      stepLD8 F_17b70 D_17b70 (getr r0 21). stepLD8 F_17b74 D_17b74 (getr r0 23).
      zv F_17b78 D_17b78 (Z_to_bv 64 s). sn F_17b7c D_17b7c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x17b6c : word) m rom) (mkst regs' (0x1573c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17cf8 /\ getr regs' 10 = Z_to_bv 64 0x1054a /\ getr regs' 11 = Z_to_bv 64 0x10e5b /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_17a70 D_17a70 ltac:(condZ).
      sn F_17bd0 D_17bd0.
      stepLD F_17bd4 D_17bd4 (Z_to_le_bytes 8 0x2ca88) (Z_to_bv 64 0x2ca88) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_17bd8 D_17bd8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_17bdc D_17bdc. stepb_ft F_17be0 D_17be0 ltac:(condZ).
      sn F_17be4 D_17be4. sn F_17be8 D_17be8. sn F_17bec D_17bec. sn F_17bf0 D_17bf0. sn F_17bf4 D_17bf4. sn F_17bf8 D_17bf8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_E : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameR s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x17d00 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Hret CE H2. unfold frameR in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    eexists. split.
    - stepLD8 F_17c04 D_17c04 ret. stepLD8 F_17c08 D_17c08 (getr r0 8). stepLD8 F_17c0c D_17c0c (getr r0 9).
      stepLD8 F_17c10 D_17c10 (getr r0 18). stepLD8 F_17c14 D_17c14 (getr r0 19). stepLD8 F_17c18 D_17c18 (getr r0 20).
      stepLD8 F_17c1c D_17c1c (getr r0 21). stepLD8 F_17c20 D_17c20 (getr r0 23).
      zv F_17c24 D_17c24 (Z_to_bv 64 s). stepret F_17c28 D_17c28 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  Lemma rb_F2 : forall regs m, exists regs',
      msteps SEGS (mkst regs (0x17cf8 : word) m rom) (mkst regs' (0x17d00 : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_17bfc D_17bfc; apply mst_refl | solve_regs_agree]. Qed.

  (* [comment removed for export] *)
  Lemma rb_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x17b6c : word) m rom) (mkst regs' (0x163c0 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17b7c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 21 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 21]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H18. eexists. split.
    - stepb_ft F_17a70 D_17a70 ltac:(condZ).
      sn F_17a74 D_17a74. sn F_17a78 D_17a78. sn F_17a7c D_17a7c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma rb_B2 : forall regs m (pixd pixs : Z),
    getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x17b7c : word) m rom) (mkst regs' (0x162f0 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17b88 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H21 H18. eexists. split.
    - sn F_17a80 D_17a80. sn F_17a84 D_17a84. sn F_17a88 D_17a88. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma rb_B3 : forall regs m (pixd pixs : Z),
    getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x17b88 : word) m rom) (mkst regs' (0x16448 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17b94 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H21 H18. eexists. split.
    - sn F_17a8c D_17a8c. sn F_17a90 D_17a90. sn F_17a94 D_17a94. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_R : forall regs m (s pixd pixs left top wd hd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs -> getr regs 9 = Z_to_bv 64 left ->
    getr regs 8 = Z_to_bv 64 top -> getr regs 19 = Z_to_bv 64 wd -> getr regs 20 = Z_to_bv 64 hd ->
    exists regs',
      msteps SEGS (mkst regs (0x17b94 : word) m rom)
                  (mkst regs' (0x1c5a4 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 top))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17bc0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 left /\ getr regs' 23 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 23]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top wd hd Hs Hs64 SOK H2 H21 H18 H9 H8 H19 H20. eexists. split.
    - sn F_17a98 D_17a98.
      stepST F_17a9c D_17a9c (Z_to_bv 64 (s - 96)) (Z_to_bv 64 top) ltac:(sok_in SOK).
      sn F_17aa0 D_17aa0. sn F_17aa4 D_17aa4. sn F_17aa8 D_17aa8. sn F_17aac D_17aac. sn F_17ab0 D_17ab0. sn F_17ab4 D_17ab4.
      sn F_17ab8 D_17ab8. sn F_17abc D_17abc. sn F_17ac0 D_17ac0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_D : forall regs m (pixs pixd : Z) (vs : pixv),
    (1 <= pixs)%Z -> PIXat m pixs vs -> (p_d vs = 1 \/ p_d vs = 8)%Z ->
    getr regs 18 = Z_to_bv 64 pixs -> getr regs 23 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x17bc0 : word) m rom) (mkst regs' (0x17d00 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixs pixd vs Hp PX Hd H18 H23. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd.
    eexists. split.
    - sn F_17ac4 D_17ac4. sn F_17ac8 D_17ac8.
      stepb_ft F_16bf0 D_16bf0 ltac:(condZ).
      stepLD F_16bf4 D_16bf4 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepret F_16bf8 D_16bf8 (0x17bc8 : word) ltac:(bveq).
      sn F_17acc D_17acc.
      stepb_tk F_17ad0 D_17ad0 ltac:(condZ).
      sn F_17b00 D_17b00. sn F_17b04 D_17b04.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition abfr (m : word -> option byte) (s : Z) (ret : word) (r0 : bvmap 5 word) (w h d : Z) : Prop :=
  cellsZ m (frameA s ret r0) /\
  rdn SEGS m (Z_to_bv 64 (s - 100)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  rdn SEGS m (Z_to_bv 64 (s - 104)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) /\
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)).

Lemma frameA_bounds : forall s ret r0, (128 <= s)%Z -> (s < 2 ^ 64)%Z ->
  Forall (fun av => s - 96 <= fst av /\ fst av + 8 <= s)%Z (frameA s ret r0).
Proof. intros s ret r0 Hs Hs64. unfold frameA. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. Qed.

Lemma DIMS_out : forall m a w h d (x : word), (8 <= a)%Z -> (a + 4 < 2 ^ 64)%Z -> ~ (a - 8 <= u x < a + 4)%Z -> DIMS m a w h d x = m x.
Proof.
  intros m a w h d x Ha Ha64 Hx. unfold DIMS.
  repeat (rewrite (wbytes_out_Z _ _ 4); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]). reflexivity.
Qed.
Lemma FRA_out : forall m s ret regs (x : word), (128 <= s)%Z -> (s < 2 ^ 64)%Z -> ~ (s - 96 <= u x < s)%Z -> FRA m s ret regs x = m x.
Proof.
  intros m s ret regs x Hs Hs64 Hx. unfold FRA.
  repeat (rewrite (wbytes_out_Z _ _ 8); [| rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]). reflexivity.
Qed.

Lemma abfr_init : forall m s ret regs w h d, (128 <= s)%Z -> (s < 2 ^ 64)%Z ->
  abfr (DIMS (FRA m s ret regs) (s - 100) w h d) s ret regs w h d.
Proof.
  intros m s ret regs w h d Hs Hs64. unfold abfr. split.
  - apply (cellsZ_out (FRA m s ret regs) _ (s - 108) (s - 96)).
    + intros x Hx. apply DIMS_out; lia.
    + eapply Forall_impl; [|exact (frameA_bounds s ret regs Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
    + unfold frameA, FRA. cbn [cellsZ]. repeat split; rdn_solve.
  - unfold DIMS. replace (s - 104)%Z with (s - 100 - 4)%Z by lia. replace (s - 108)%Z with (s - 100 - 8)%Z by lia.
    repeat split; rdn_chain.
Qed.

Lemma abfr_frm : forall C s' m m' s ret r0 w h d, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 108)%Z -> (128 <= s)%Z -> (s < 2 ^ 64)%Z ->
  abfr m s ret r0 w h d -> abfr m' s ret r0 w h d.
Proof.
  intros C s' m m' s ret r0 w h d CK F H1 H2 Hs Hs64 (CE & Rw & Rh & Rd). unfold abfr.
  rewrite !(FRM_rdn16 C s' m m' _ 4 CK F) by (cbn; lia). split; [| repeat split; assumption].
  apply (cellsZ_frm C s' m m' _ CK F H1); [|exact CE].
  eapply Forall_impl; [|exact (frameA_bounds s ret r0 Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.

Lemma abfr_out : forall m m' (lo hi : Z) s ret r0 w h d, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 108 \/ s <= lo)%Z -> (128 <= s)%Z -> (s < 2 ^ 64)%Z ->
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
      msteps SEGS (mkst regs (0x17780 : word) m rom) (mkst regs' (0x177d4 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 npix /\ getr regs' 13 = Z_to_bv 64 npix /\ getr regs' 14 = Z_to_bv 64 npix /\ getr regs' 15 = Z_to_bv 64 val
      /\ regs_agree (fun r => In r [12; 13; 14; 15]%list) regs regs'.
  Proof.
    intros regs m pixs npix val Hp Hn H10 H11 H12. eexists. split.
    - stepb_ft F_17684 D_17684 ltac:(condZ). stepb_ft F_17688 D_17688 ltac:(condZ).
      sn F_1768c D_1768c. sn F_17690 D_17690. sn F_17694 D_17694. sn F_17698 D_17698. sn F_1769c D_1769c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma prb_run : forall regs m (pixs npix : Z),
    (1 <= pixs < 2 ^ 64)%Z -> (1 <= npix < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 npix ->
    exists regs',
      msteps SEGS (mkst regs (0x17a90 : word) m rom) (mkst regs' (0x17ae0 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 npix /\ getr regs' 13 = Z_to_bv 64 npix /\ getr regs' 14 = Z_to_bv 64 npix
      /\ regs_agree (fun r => In r [12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m pixs npix Hp Hn H10 H11. eexists. split.
    - stepb_ft F_17994 D_17994 ltac:(condZ). stepb_ft F_17998 D_17998 ltac:(condZ).
      sn F_1799c D_1799c. sn F_179a0 D_179a0. sn F_179a4 D_179a4. sn F_179a8 D_179a8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma prb_N : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x17a90 : word) m rom) (mkst regs' (0x1573c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10ced /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_17994 D_17994 ltac:(condZ).
      sn F_179ac D_179ac.
      stepLD F_179b0 D_179b0 (Z_to_le_bytes 8 0x2ca88) (Z_to_bv 64 0x2ca88) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_179b4 D_179b4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_179b8 D_179b8. stepb_ft F_179bc D_179bc ltac:(condZ).
      sn F_179c0 D_179c0. sn F_179c4 D_179c4. sn F_179c8 D_179c8. sn F_179cc D_179cc. sn F_179d0 D_179d0. sn F_179d4 D_179d4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsWrap.

Lemma str_pixRemoveBorder : str16 0x10ced 15. Proof. str16_tac. Qed.
Definition PC_pixAddBorder : Z := 0x17780.
Definition PC_pixRemoveBorder : Z := 0x17a90.

End GrayBorder.
