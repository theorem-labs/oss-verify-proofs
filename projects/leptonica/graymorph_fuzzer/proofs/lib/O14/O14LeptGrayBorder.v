(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptStderr O14LeptBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14CL7a.
Import O14CL7a.O14LeptErr. Import O14CL7a.O14LeptRop_iface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptPixHdr O14LeptPixCreate O14LeptCmapValid O14LeptCmap2 O14LeptPixCopyA O14LeptPixCopy O14LeptGrayA O14_code_gmACE.
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

Section GrayBorder.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
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
      msteps SEGS (mkst regs (0x178a4 : word) m rom)
                  (mkst regs' (0x15674 : word) (DIMS (FRA m s ret regs) (s - 100) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 128) /\ getr regs' 1 = Z_to_bv 64 0x17940
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
    - zv F_177a8 D_177a8 (Z_to_bv 64 (s - 128)).
      stepST F_177ac D_177ac (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_177b0 D_177b0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_177b4 D_177b4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_177b8 D_177b8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_177bc D_177bc (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_177c0 D_177c0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_177c4 D_177c4 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_177c8 D_177c8 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_177cc D_177cc (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_177d0 D_177d0 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_177d4 D_177d4 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_177d8 D_177d8 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepb_ft F_177dc D_177dc ltac:(condZ).
      sn F_177e0 D_177e0. sn F_177e4 D_177e4. sn F_177e8 D_177e8. sn F_177ec D_177ec. sn F_177f0 D_177f0.
      stepat F_177f4 D_177f4 (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_177f8 D_177f8 (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_177fc D_177fc (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_17800 D_17800 ltac:(condZ).
      sn F_17804 D_17804.
      zv F_17808 D_17808 (Z_to_bv 64 (s - 100)). zv F_1780c D_1780c (Z_to_bv 64 (s - 104)). zv F_17810 D_17810 (Z_to_bv 64 (s - 108)).
      sn F_17814 D_17814. sn F_17818 D_17818.
      (* [comment removed for export] *)
      stepb_ft F_15d38 D_15d38 ltac:(condZ).
      stepST F_15d3c D_15d3c (Z_to_bv 64 (s - 100)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15d40 D_15d40 ltac:(condZ).
      stepST F_15d44 D_15d44 (Z_to_bv 64 (s - 100 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15d48 D_15d48 ltac:(condZ).
      stepST F_15d4c D_15d4c (Z_to_bv 64 (s - 100 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15d50 D_15d50 ltac:(condZ).
      stepb_ft F_15d54 D_15d54 ltac:(condZ).
      stepLD F_15d58 D_15d58 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_15d5c D_15d5c (Z_to_bv 64 (s - 100)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_15d60 D_15d60 ltac:(condZ).
      stepLD F_15d64 D_15d64 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_15d68 D_15d68 (Z_to_bv 64 (s - 100 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      sn F_15d6c D_15d6c.
      stepb_ft F_15d70 D_15d70 ltac:(condZ).
      stepLD F_15d74 D_15d74 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_15d78 D_15d78 (Z_to_bv 64 (s - 100 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_15d7c D_15d7c.
      stepret F_15d80 D_15d80 (0x17918 : word) ltac:(bveq).
      (* [comment removed for export] *)
      ldcell F_1781c D_1781c (s - 100)%Z (p_w vs).
      ldcell F_17820 D_17820 (s - 100 - 4)%Z (p_h vs).
      ldcell F_17824 D_17824 (s - 100 - 8)%Z (p_d vs).
      sn F_17828 D_17828. fixv (Z_to_bv 64 (p_w vs + left)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_1782c D_1782c. fixv (Z_to_bv 64 (p_h vs + top)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_17830 D_17830. fixv (Z_to_bv 64 (p_w vs + left + right)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_17834 D_17834. fixv (Z_to_bv 64 (p_h vs + top + bot)) ltac:(rewrite v_addw_Z, sw32_small by lia; reflexivity).
      sn F_17838 D_17838. sn F_1783c D_1783c. sn F_17840 D_17840.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x2aa40) 8 = Some (Z_to_le_bytes 8 0x2bab0) -> rdn SEGS m (Z_to_bv 64 0x2bab0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x17940 : word) m rom) (mkst regs' (0x1543c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17ad4 /\ getr regs' 10 = Z_to_bv 64 0x104bd /\ getr regs' 11 = Z_to_bv 64 0x10ba8 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_17844 D_17844 ltac:(condZ).
      sn F_179ac D_179ac.
      stepLD F_179b0 D_179b0 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_179b4 D_179b4 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_179b8 D_179b8. stepb_ft F_179bc D_179bc ltac:(condZ).
      sn F_179c0 D_179c0. sn F_179c4 D_179c4. sn F_179c8 D_179c8. sn F_179cc D_179cc. sn F_179d0 D_179d0. sn F_179d4 D_179d4.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_F2 : forall regs m (res : Z),
    getr regs 10 = Z_to_bv 64 res ->
    exists regs',
      msteps SEGS (mkst regs (0x17ad4 : word) m rom) (mkst regs' (0x17b24 : word) m rom)
      /\ getr regs' 19 = Z_to_bv 64 res /\ regs_agree (fun r => In r [19]%list) regs regs'.
  Proof.
    intros regs m res H10. eexists. split.
    - sn F_179d8 D_179d8. sn F_179dc D_179dc. apply mst_refl.
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
      msteps SEGS (mkst regs (0x17b24 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 res
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs r0 m s res ret Hs Hs64 Hret CE H2 H19. unfold frameA in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & _).
    eexists. split.
    - sn F_17a28 D_17a28.
      stepLD8 F_17a2c D_17a2c ret. stepLD8 F_17a30 D_17a30 (getr r0 8). stepLD8 F_17a34 D_17a34 (getr r0 9).
      stepLD8 F_17a38 D_17a38 (getr r0 18). stepLD8 F_17a3c D_17a3c (getr r0 19). stepLD8 F_17a40 D_17a40 (getr r0 20).
      stepLD8 F_17a44 D_17a44 (getr r0 21). stepLD8 F_17a48 D_17a48 (getr r0 22). stepLD8 F_17a4c D_17a4c (getr r0 23).
      stepLD8 F_17a50 D_17a50 (getr r0 24). stepLD8 F_17a54 D_17a54 (getr r0 25). stepLD8 F_17a58 D_17a58 (getr r0 26).
      zv F_17a5c D_17a5c (Z_to_bv 64 s). stepret F_17a60 D_17a60 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x17940 : word) m rom) (mkst regs' (0x15f84 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17950 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 19 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 19]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H8. eexists. split.
    - stepb_ft F_17844 D_17844 ltac:(condZ).
      sn F_17848 D_17848. sn F_1784c D_1784c. sn F_17850 D_17850. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_B2 : forall regs m (pixd pixs : Z),
    getr regs 19 = Z_to_bv 64 pixd -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x17950 : word) m rom) (mkst regs' (0x1600c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x1795c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H19 H8. eexists. split.
    - sn F_17854 D_17854. sn F_17858 D_17858. sn F_1785c D_1785c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_C0 : forall regs m,
    getr regs 26 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x1795c : word) m rom) (mkst regs' (0x1797c : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof.
    intros regs m H26. eexists. split.
    - stepb_tk F_17860 D_17860 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ab_C15 : forall regs m (s d val : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (d = 1 \/ d = 8)%Z -> val = (2 ^ d - 1)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 d)) ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 26 = Z_to_bv 64 val ->
    exists regs',
      msteps SEGS (mkst regs (0x1795c : word) m rom) (mkst regs' (0x1797c : word) m rom)
      /\ getr regs' 26 = Z_to_bv 64 15
      /\ regs_agree (fun r => In r [10; 11; 12; 26]%list) regs regs'.
  Proof.
    intros regs m s d val Hs Hs64 Hd Hval Rd H2 H26.
    assert (SCRIPT : forall dd : Z, (dd = 1 \/ dd = 8)%Z -> d = dd -> exists regs',
      msteps SEGS (mkst regs (0x1795c : word) m rom) (mkst regs' (0x1797c : word) m rom)
      /\ getr regs' 26 = Z_to_bv 64 15 /\ regs_agree (fun r => In r [10; 11; 12; 26]%list) regs regs').
    { intros dd Hdd ->. subst val.
      destruct Hdd as [-> | ->]; (eexists; split;
      [ stepb_ft F_17860 D_17860 ltac:(condZ);
        sn F_17864 D_17864;
        first [ stepLD F_17868 D_17868 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rdn_addr (s - 108)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia)
              | stepLD F_17868 D_17868 (word_to_le_bytes 4 (Z_to_bv 64 8)) (Z_to_bv 64 8) ltac:(rdn_addr (s - 108)%Z; exact Rd) ltac:(apply bytes_le_to_Z_4; unorm; lia) ];
        sn F_1786c D_1786c;
        stepb_tk F_17870 D_17870 ltac:(condZ);
        sn F_179e8 D_179e8; sn F_179ec D_179ec; sn F_179f0 D_179f0;
        stepb_tk F_179f4 D_179f4 ltac:(cond_compute);
        sn F_1787c D_1787c;
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
      msteps SEGS (mkst regs (0x1797c : word) m rom)
                  (mkst regs' (0x1c624 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x179a4 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 left /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd left hd op Hs Hs64 SOK H2 H19 H18 H25 H26. eexists. split.
    - stepST F_17880 D_17880 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_17884 D_17884. sn F_17888 D_17888. sn F_1788c D_1788c. sn F_17890 D_17890. sn F_17894 D_17894. sn F_17898 D_17898.
      sn F_1789c D_1789c. sn F_178a0 D_178a0. sn F_178a4 D_178a4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R2 : forall regs m (s pixd x right hd op : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 24 = Z_to_bv 64 x -> getr regs 21 = Z_to_bv 64 right ->
    getr regs 25 = Z_to_bv 64 hd -> getr regs 26 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x179a4 : word) m rom)
                  (mkst regs' (0x1c624 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x179cc /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 x /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 right /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd x right hd op Hs Hs64 SOK H2 H19 H24 H21 H25 H26. eexists. split.
    - stepST F_178a8 D_178a8 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_178ac D_178ac. sn F_178b0 D_178b0. sn F_178b4 D_178b4. sn F_178b8 D_178b8. sn F_178bc D_178bc. sn F_178c0 D_178c0.
      sn F_178c4 D_178c4. sn F_178c8 D_178c8. sn F_178cc D_178cc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R3 : forall regs m (s pixd wd top op : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 22 = Z_to_bv 64 wd -> getr regs 9 = Z_to_bv 64 top ->
    getr regs 26 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x179cc : word) m rom)
                  (mkst regs' (0x1c624 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x179f4 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 top /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd wd top op Hs Hs64 SOK H2 H19 H22 H9 H26. eexists. split.
    - stepST F_178d0 D_178d0 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_178d4 D_178d4. sn F_178d8 D_178d8. sn F_178dc D_178dc. sn F_178e0 D_178e0. sn F_178e4 D_178e4. sn F_178e8 D_178e8.
      sn F_178ec D_178ec. sn F_178f0 D_178f0. sn F_178f4 D_178f4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma ab_R4 : forall regs m (s pixd y wd bot op : Z),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 128)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 128) -> getr regs 19 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 y -> getr regs 22 = Z_to_bv 64 wd ->
    getr regs 20 = Z_to_bv 64 bot -> getr regs 26 = Z_to_bv 64 op ->
    exists regs',
      msteps SEGS (mkst regs (0x179f4 : word) m rom)
                  (mkst regs' (0x1c624 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17a1c /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 y
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 bot /\ getr regs' 15 = Z_to_bv 64 op
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd y wd bot op Hs Hs64 SOK H2 H19 H23 H22 H20 H26. eexists. split.
    - stepST F_178f8 D_178f8 (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_178fc D_178fc. sn F_17900 D_17900. sn F_17904 D_17904. sn F_17908 D_17908. sn F_1790c D_1790c. sn F_17910 D_17910.
      sn F_17914 D_17914. sn F_17918 D_17918. sn F_1791c D_1791c. apply mst_refl.
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
      msteps SEGS (mkst regs (0x17a1c : word) m rom)
                  (mkst regs' (0x1c624 : word) (wbytes m (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17b24 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 left /\ getr regs' 12 = Z_to_bv 64 top
      /\ getr regs' 13 = Z_to_bv 64 w /\ getr regs' 14 = Z_to_bv 64 h /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top w h Hs Hs64 Hw Hh SOK Rw Rh H2 H19 H8 H18 H9. eexists. split.
    - sn F_17920 D_17920.
      stepLD F_17a00 D_17a00 (word_to_le_bytes 4 (Z_to_bv 64 w)) (Z_to_bv 64 w) ltac:(rdn_addr (s - 100)%Z; exact Rw) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small w) by lia.
      stepLD F_17a04 D_17a04 (word_to_le_bytes 4 (Z_to_bv 64 h)) (Z_to_bv 64 h) ltac:(rdn_addr (s - 104)%Z; exact Rh) ltac:(apply bytes_le_to_Z_4; unorm; lia).
      rewrite ?(v_lw_small h) by lia.
      sn F_17a08 D_17a08.
      stepST F_17a0c D_17a0c (Z_to_bv 64 (s - 128)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_17a10 D_17a10. sn F_17a14 D_17a14. sn F_17a18 D_17a18. sn F_17a1c D_17a1c. sn F_17a20 D_17a20. sn F_17a24 D_17a24.
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
    zv F_17a64 D_17a64 (Z_to_bv 64 (s - 96));
    stepST F_17a68 D_17a68 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
    stepST F_17a6c D_17a6c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
    stepST F_17a70 D_17a70 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
    stepST F_17a74 D_17a74 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
    stepST F_17a78 D_17a78 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK);
    stepST F_17a7c D_17a7c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK);
    stepST F_17a80 D_17a80 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK);
    stepST F_17a84 D_17a84 (Z_to_bv 64 (s - 64)) (getr regs 23) ltac:(sok_in SOK).

  (* [comment removed for export] *)
  Lemma rb_A : forall regs m (s pixs left right top bot : Z) (vs : pixv) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 96 \/ s <= pixs)%Z ->
    (0 <= left <= 64)%Z -> (0 <= right <= 64)%Z -> (0 <= top <= 64)%Z -> (0 <= bot <= 64)%Z ->
    (1 <= p_w vs <= 20000)%Z -> (1 <= p_h vs <= 20000)%Z -> (1 <= p_w vs - left - right)%Z -> (1 <= p_h vs - top - bot)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot ->
    exists regs',
      msteps SEGS (mkst regs (0x17b60 : word) m rom)
                  (mkst regs' (0x15674 : word) (DIMS (FRR m s ret regs) (s - 68) (p_w vs) (p_h vs) (p_d vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x17bec
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
      stepb_ft F_17a88 D_17a88 ltac:(condZ).
      sn F_17a8c D_17a8c. sn F_17a90 D_17a90. sn F_17a94 D_17a94.
      stepat F_17a98 D_17a98 (Z_to_bv 64 (Z.lor right left)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_17a9c D_17a9c (Z_to_bv 64 (Z.lor top bot)) ltac:(gres; pin; apply v_or_Z; lia).
      stepat F_17aa0 D_17aa0 (Z_to_bv 64 (Z.lor (Z.lor right left) (Z.lor top bot))) ltac:(gres; pin; apply v_or_Z; lia).
      stepb_ft F_17aa4 D_17aa4 ltac:(condZ).
      sn F_17aa8 D_17aa8.
      zv F_17aac D_17aac (Z_to_bv 64 (s - 68)). zv F_17ab0 D_17ab0 (Z_to_bv 64 (s - 72)). zv F_17ab4 D_17ab4 (Z_to_bv 64 (s - 76)).
      sn F_17ab8 D_17ab8. sn F_17abc D_17abc.
      (* [comment removed for export] *)
      stepb_ft F_15d38 D_15d38 ltac:(condZ).
      stepST F_15d3c D_15d3c (Z_to_bv 64 (s - 68)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15d40 D_15d40 ltac:(condZ).
      stepST F_15d44 D_15d44 (Z_to_bv 64 (s - 68 - 4)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15d48 D_15d48 ltac:(condZ).
      stepST F_15d4c D_15d4c (Z_to_bv 64 (s - 68 - 8)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15d50 D_15d50 ltac:(condZ).
      stepb_ft F_15d54 D_15d54 ltac:(condZ).
      stepLD F_15d58 D_15d58 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs))
        ltac:(addr_norm; rewrite ?Z.add_0_r; apply PIX_rd_w; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_15d5c D_15d5c (Z_to_bv 64 (s - 68)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_15d60 D_15d60 ltac:(condZ).
      stepLD F_15d64 D_15d64 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs))
        ltac:(addr_norm; apply PIX_rd_h; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_15d68 D_15d68 (Z_to_bv 64 (s - 68 - 4)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      sn F_15d6c D_15d6c.
      stepb_ft F_15d70 D_15d70 ltac:(condZ).
      stepLD F_15d74 D_15d74 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs))
        ltac:(addr_norm; apply PIX_rd_d; repeat (apply PXk; [| lia | rewrite ?length_N_to_le_bytes; cbn; lia]); exact PX) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepST F_15d78 D_15d78 (Z_to_bv 64 (s - 68 - 8)) (Z_to_bv 64 (p_d vs)) ltac:(sok_in SOK).
      sn F_15d7c D_15d7c.
      stepret F_15d80 D_15d80 (0x17bbc : word) ltac:(bveq).
      (* [comment removed for export] *)
      ldcell F_17ac0 D_17ac0 (s - 68)%Z (p_w vs).
      zv F_17ac4 D_17ac4 (Z_to_bv 64 (right + left)).
      sn F_17ac8 D_17ac8. fixv (Z_to_bv 64 (p_w vs - left - right)) ltac:(rewrite v_subw_Z, sw32_small by lia; f_equal; lia).
      stepb_ft F_17acc D_17acc ltac:(condZ).
      ldcell F_17ad0 D_17ad0 (s - 68 - 4)%Z (p_h vs).
      zv F_17ad4 D_17ad4 (Z_to_bv 64 (bot + top)).
      sn F_17ad8 D_17ad8. fixv (Z_to_bv 64 (p_h vs - top - bot)) ltac:(rewrite v_subw_Z, sw32_small by lia; f_equal; lia).
      stepb_ft F_17adc D_17adc ltac:(condZ).
      ldcell F_17ae0 D_17ae0 (s - 68 - 8)%Z (p_d vs).
      sn F_17ae4 D_17ae4. sn F_17ae8 D_17ae8. sn F_17aec D_17aec.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_N1 : forall regs m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x17b60 : word) m rom) (mkst regs' (0x17c84 : word) (FRR m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96)
      /\ regs_agree (fun r => In r [2]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK H2 H1 H10. unfold FRR. eexists. split.
    - rb_prologue s ret regs SOK.
      stepb_tk F_17a88 D_17a88 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_N2 : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x2aa40) 8 = Some (Z_to_le_bytes 8 0x2bab0) -> rdn SEGS m (Z_to_bv 64 0x2bab0) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameR s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x17c84 : word) m rom) (mkst regs' (0x1543c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10cf4
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Rg Rs CE H2. unfold frameR in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    eexists. split.
    - sn F_17b88 D_17b88.
      stepLD F_17b8c D_17b8c (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_17b90 D_17b90 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_17b94 D_17b94. stepb_ft F_17b98 D_17b98 ltac:(condZ).
      sn F_17b9c D_17b9c. sn F_17ba0 D_17ba0. sn F_17ba4 D_17ba4. sn F_17ba8 D_17ba8. sn F_17bac D_17bac.
      sn F_17bd4 D_17bd4.
      stepLD8 F_17bd8 D_17bd8 ret. stepLD8 F_17bdc D_17bdc (getr r0 8). stepLD8 F_17be0 D_17be0 (getr r0 9).
      stepLD8 F_17be4 D_17be4 (getr r0 18). stepLD8 F_17be8 D_17be8 (getr r0 19). stepLD8 F_17bec D_17bec (getr r0 20).
      stepLD8 F_17bf0 D_17bf0 (getr r0 21). stepLD8 F_17bf4 D_17bf4 (getr r0 23).
      zv F_17bf8 D_17bf8 (Z_to_bv 64 s). sn F_17bfc D_17bfc.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_F : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x2aa40) 8 = Some (Z_to_le_bytes 8 0x2bab0) -> rdn SEGS m (Z_to_bv 64 0x2bab0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x17bec : word) m rom) (mkst regs' (0x1543c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17d78 /\ getr regs' 10 = Z_to_bv 64 0x104bd /\ getr regs' 11 = Z_to_bv 64 0x10cf4 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m Rg Rs H10. eexists. split.
    - stepb_tk F_17af0 D_17af0 ltac:(condZ).
      sn F_17c50 D_17c50.
      stepLD F_17c54 D_17c54 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_17c58 D_17c58 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_17c5c D_17c5c. stepb_ft F_17c60 D_17c60 ltac:(condZ).
      sn F_17c64 D_17c64. sn F_17c68 D_17c68. sn F_17c6c D_17c6c. sn F_17c70 D_17c70. sn F_17c74 D_17c74. sn F_17c78 D_17c78.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_E : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameR s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs',
      msteps SEGS (mkst regs (0x17d80 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 23]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 23]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Hret CE H2. unfold frameR in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
    eexists. split.
    - stepLD8 F_17c84 D_17c84 ret. stepLD8 F_17c88 D_17c88 (getr r0 8). stepLD8 F_17c8c D_17c8c (getr r0 9).
      stepLD8 F_17c90 D_17c90 (getr r0 18). stepLD8 F_17c94 D_17c94 (getr r0 19). stepLD8 F_17c98 D_17c98 (getr r0 20).
      stepLD8 F_17c9c D_17c9c (getr r0 21). stepLD8 F_17ca0 D_17ca0 (getr r0 23).
      zv F_17ca4 D_17ca4 (Z_to_bv 64 s). stepret F_17ca8 D_17ca8 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  Lemma rb_F2 : forall regs m, exists regs',
      msteps SEGS (mkst regs (0x17d78 : word) m rom) (mkst regs' (0x17d80 : word) m rom)
      /\ regs_agree (fun r => In r []%list) regs regs'.
  Proof. intros regs m. eexists. split; [sn F_17c7c D_17c7c; apply mst_refl | solve_regs_agree]. Qed.

  (* [comment removed for export] *)
  Lemma rb_B1 : forall regs m (pixd pixs : Z),
    (1 <= pixd < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x17bec : word) m rom) (mkst regs' (0x15f84 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17bfc /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs /\ getr regs' 21 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 11; 21]%list) regs regs'.
  Proof.
    intros regs m pixd pixs Hp H10 H18. eexists. split.
    - stepb_ft F_17af0 D_17af0 ltac:(condZ).
      sn F_17af4 D_17af4. sn F_17af8 D_17af8. sn F_17afc D_17afc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma rb_B2 : forall regs m (pixd pixs : Z),
    getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x17bfc : word) m rom) (mkst regs' (0x15eb4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17c08 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H21 H18. eexists. split.
    - sn F_17b00 D_17b00. sn F_17b04 D_17b04. sn F_17b08 D_17b08. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma rb_B3 : forall regs m (pixd pixs : Z),
    getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x17c08 : word) m rom) (mkst regs' (0x1600c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17c14 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixd pixs H21 H18. eexists. split.
    - sn F_17b0c D_17b0c. sn F_17b10 D_17b10. sn F_17b14 D_17b14. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_R : forall regs m (s pixd pixs left top wd hd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 21 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs -> getr regs 9 = Z_to_bv 64 left ->
    getr regs 8 = Z_to_bv 64 top -> getr regs 19 = Z_to_bv 64 wd -> getr regs 20 = Z_to_bv 64 hd ->
    exists regs',
      msteps SEGS (mkst regs (0x17c14 : word) m rom)
                  (mkst regs' (0x1c624 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 top))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x17c40 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 13 = Z_to_bv 64 wd /\ getr regs' 14 = Z_to_bv 64 hd /\ getr regs' 15 = Z_to_bv 64 12 /\ getr regs' 16 = Z_to_bv 64 pixs
      /\ getr regs' 17 = Z_to_bv 64 left /\ getr regs' 23 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17; 23]%list) regs regs'.
  Proof.
    intros regs m s pixd pixs left top wd hd Hs Hs64 SOK H2 H21 H18 H9 H8 H19 H20. eexists. split.
    - sn F_17b18 D_17b18.
      stepST F_17b1c D_17b1c (Z_to_bv 64 (s - 96)) (Z_to_bv 64 top) ltac:(sok_in SOK).
      sn F_17b20 D_17b20. sn F_17b24 D_17b24. sn F_17b28 D_17b28. sn F_17b2c D_17b2c. sn F_17b30 D_17b30. sn F_17b34 D_17b34.
      sn F_17b38 D_17b38. sn F_17b3c D_17b3c. sn F_17b40 D_17b40. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma rb_D : forall regs m (pixs pixd : Z) (vs : pixv),
    (1 <= pixs)%Z -> PIXat m pixs vs -> (p_d vs = 1 \/ p_d vs = 8)%Z ->
    getr regs 18 = Z_to_bv 64 pixs -> getr regs 23 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x17c40 : word) m rom) (mkst regs' (0x17d80 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m pixs pixd vs Hp PX Hd H18 H23. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as Cd.
    eexists. split.
    - sn F_17b44 D_17b44. sn F_17b48 D_17b48.
      stepb_ft F_167b4 D_167b4 ltac:(condZ).
      stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepret F_167bc D_167bc (0x17c48 : word) ltac:(bveq).
      sn F_17b4c D_17b4c.
      stepb_tk F_17b50 D_17b50 ltac:(condZ).
      sn F_17b80 D_17b80. sn F_17b84 D_17b84.
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
