(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import RelocKitOL RelocTacOL CanonImgOL RCodeOL_24000_24fe0.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.OL Require Import LeptStderr LeptBase LeptErr LeptCmap CmapFill.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac zval ::= rl_zval.      (* [comment removed for export] *)
#[local] Ltac condZ ::= rl_condZ.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Definition cdepth (nc : Z) : Z := if (16 <? nc)%Z then 8 else if (4 <? nc)%Z then 4 else if (nc <? 3)%Z then 1 else 2.

Lemma cdepth_cases : forall nc, (cdepth nc = 1 \/ cdepth nc = 2 \/ cdepth nc = 4 \/ cdepth nc = 8)%Z.
Proof. intros nc. unfold cdepth. destruct (16 <? nc)%Z; [|destruct (4 <? nc)%Z; [|destruct (nc <? 3)%Z]]; lia. Qed.

Lemma cdepth_fits : forall nc, (1 <= nc <= 256)%Z -> (nc <= 2 ^ cdepth nc)%Z /\ (2 <= 2 ^ cdepth nc <= 256)%Z.
Proof.
  intros nc Hnc. unfold cdepth.
  destruct (16 <? nc)%Z eqn:E1; [apply Z.ltb_lt in E1; cbn; lia|apply Z.ltb_ge in E1].
  destruct (4 <? nc)%Z eqn:E2; [apply Z.ltb_lt in E2; cbn; lia|apply Z.ltb_ge in E2].
  destruct (nc <? 3)%Z eqn:E3; [apply Z.ltb_lt in E3; cbn; lia|apply Z.ltb_ge in E3; cbn; lia].
Qed.

Section CmapDeser.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeOL RLOC} {RSITESF : RelocSitesOL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgOL RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC} {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvOL RLOC} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLG} {PG : PinsG}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  #[local] Definition FR10 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
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

  Ltac prologue10 SOK regs ret s :=
      zv constr:(F_24498) constr:(D_24498) (Z_to_bv 64 (s - 80));
      stepST constr:(F_2449c) constr:(D_2449c) (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
      stepST constr:(F_244a0) constr:(D_244a0) (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
      stepST constr:(F_244a4) constr:(D_244a4) (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
      stepST constr:(F_244a8) constr:(D_244a8) (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
      stepST constr:(F_244ac) constr:(D_244ac) (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK);
      stepST constr:(F_244b0) constr:(D_244b0) (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK);
      stepST constr:(F_244b4) constr:(D_244b4) (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK);
      stepST constr:(F_244b8) constr:(D_244b8) (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK);
      stepST constr:(F_244bc) constr:(D_244bc) (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK);
      stepST constr:(F_244c0) constr:(D_244c0) (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK);
      stepb_ft constr:(F_244c4) constr:(D_244c4) ltac:(condZ);
      sn constr:(F_244c8) constr:(D_244c8);
      sn constr:(F_244cc) constr:(D_244cc);
      sn constr:(F_244d0) constr:(D_244d0);
      stepb_tk constr:(F_244d4) constr:(D_244d4) ltac:(idtac).

  (* [comment removed for export] *)
  Ltac to_calloc1 :=
      sn constr:(F_245fc) constr:(D_245fc); sn constr:(F_24600) constr:(D_24600); sn constr:(F_24604) constr:(D_24604); sn constr:(F_24608) constr:(D_24608); sn constr:(F_2460c) constr:(D_2460c); apply mst_refl.

  (* [comment removed for export] *)
  Lemma pcd_A : forall regs m (s dp nc : Z) (ret : word),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= dp < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 80)) 80 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 4 -> getr regs 12 = Z_to_bv 64 nc ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_24498 0x24498) m rom) (mkst regs' (rl dF_15a00 0x15a00) (FR10 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 80) /\ getr regs' 1 = rl dOL_24498 0x24610
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 24
      /\ getr regs' 8 = Z_to_bv 64 4 /\ getr regs' 21 = Z_to_bv 64 dp /\ getr regs' 18 = Z_to_bv 64 (cdepth nc)
      /\ getr regs' 19 = Z_to_bv 64 1 /\ getr regs' 22 = Z_to_bv 64 nc
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 13; 18; 19; 21; 22]%list) regs regs'.
  Proof.
    intros regs m s dp nc ret Hs Hs64 Hdp Hnc SOK H2 H1 H10 H11 H12. unfold FR10, cdepth.
    destruct (16 <? nc)%Z eqn:E1; [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1; destruct (4 <? nc)%Z eqn:E2;
      [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2; destruct (nc <? 3)%Z eqn:E3; [apply Z.ltb_lt in E3 | apply Z.ltb_ge in E3]]];
      eexists; split.
    - prologue10 SOK regs ret s. 1: rl_vmc_OL.
      stepb_ft F_24518 D_24518 ltac:(condZ).
      sn F_2451c D_2451c. stepb_tk F_24520 D_24520 ltac:(condZ).
      sn F_245d4 D_245d4. sn F_245d8 D_245d8.
      stepb_ft F_245dc D_245dc ltac:(condZ).
      sn F_245e0 D_245e0. sn F_245e4 D_245e4.
      to_calloc1.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - prologue10 SOK regs ret s. 1: rl_vmc_OL.
      stepb_ft F_24518 D_24518 ltac:(condZ).
      sn F_2451c D_2451c. stepb_tk F_24520 D_24520 ltac:(condZ).
      sn F_245d4 D_245d4. sn F_245d8 D_245d8.
      stepb_tk F_245dc D_245dc ltac:(condZ).
      sn F_245e8 D_245e8.
      stepb_tk F_245ec D_245ec ltac:(condZ).
      to_calloc1.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - prologue10 SOK regs ret s. 1: rl_vmc_OL.
      stepb_ft F_24518 D_24518 ltac:(condZ).
      sn F_2451c D_2451c. stepb_tk F_24520 D_24520 ltac:(condZ).
      sn F_245d4 D_245d4. sn F_245d8 D_245d8.
      stepb_tk F_245dc D_245dc ltac:(condZ).
      sn F_245e8 D_245e8.
      stepb_ft F_245ec D_245ec ltac:(condZ).
      stepat F_245f0 D_245f0 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite v_sltiu_Z by lia; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
      sn F_245f4 D_245f4. sn F_245f8 D_245f8.
      to_calloc1.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - prologue10 SOK regs ret s. 1: rl_vmc_OL.
      stepb_ft F_24518 D_24518 ltac:(condZ).
      sn F_2451c D_2451c. stepb_tk F_24520 D_24520 ltac:(condZ).
      sn F_245d4 D_245d4. sn F_245d8 D_245d8.
      stepb_tk F_245dc D_245dc ltac:(condZ).
      sn F_245e8 D_245e8.
      stepb_ft F_245ec D_245ec ltac:(condZ).
      stepat F_245f0 D_245f0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_sltiu_Z by lia; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
      sn F_245f4 D_245f4. sn F_245f8 D_245f8.
      to_calloc1.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcd_A2 : forall regs m (d cm : Z),
    (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z -> (1 <= cm)%Z -> (cm + 24 < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 cm) 24 = true ->
    getr regs 10 = Z_to_bv 64 cm -> getr regs 18 = Z_to_bv 64 d -> getr regs 19 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_24498 0x24610) m rom)
                  (mkst regs' (rl dF_15a00 0x15a00)
                        (wbytes (wbytes m (Z_to_bv 64 (cm + 8)) (word_to_le_bytes 4 (Z_to_bv 64 d)))
                                (Z_to_bv 64 (cm + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (2 ^ d)))) rom)
      /\ getr regs' 1 = rl dOL_24498 0x2462c
      /\ getr regs' 10 = Z_to_bv 64 (2 ^ d) /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 9 = Z_to_bv 64 cm /\ getr regs' 20 = Z_to_bv 64 4
      /\ regs_agree (fun r => In r [1; 9; 10; 11; 20]%list) regs regs'.
  Proof.
    intros regs m d cm Hd Hcm Hcm64 SOK H10 H18 H19.
    eexists. split.
    - sn F_24610 D_24610.
      sn F_24614 D_24614. rewrite (sllw_1 d Hd).
      stepST F_24618 D_24618 (Z_to_bv 64 (cm + 8)) (Z_to_bv 64 d) ltac:(sok_in SOK).
      stepST F_2461c D_2461c (Z_to_bv 64 (cm + 12)) (Z_to_bv 64 (2 ^ d)) ltac:(sok_in SOK).
      sn F_24620 D_24620.
      sn F_24624 D_24624.
      sn F_24628 D_24628.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcd_B : forall regs m (dp nc cm arr : Z),
    (1 <= dp)%Z -> (dp + 3 < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z -> (1 <= cm)%Z -> (cm + 24 < 2 ^ 64)%Z -> (1 <= arr)%Z -> (arr < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 cm) 24 = true ->
    rdn SEGS (wbytes (wbytes m (Z_to_bv 64 cm) (word_to_le_bytes 8 (Z_to_bv 64 arr))) (Z_to_bv 64 (cm + 16)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
        (rl dA_1e3a0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) ->
    getr regs 10 = Z_to_bv 64 arr -> getr regs 9 = Z_to_bv 64 cm -> getr regs 21 = Z_to_bv 64 dp -> getr regs 22 = Z_to_bv 64 nc ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_24498 0x2462c) m rom)
                  (mkst regs' (rl dOL_24498 0x2469c)
                        (wbytes (wbytes m (Z_to_bv 64 cm) (word_to_le_bytes 8 (Z_to_bv 64 arr)))
                                (Z_to_bv 64 (cm + 16)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 9 = Z_to_bv 64 cm /\ getr regs' 21 = Z_to_bv 64 (dp + 3) /\ getr regs' 23 = Z_to_bv 64 nc
      /\ getr regs' 22 = Z_to_bv 64 5 /\ getr regs' 24 = rl dA_1f3f8 0x1f420 /\ getr regs' 18 = rl dOLS_108d3 0x108d3
      /\ getr regs' 19 = rl dOLS_102c7 0x102c7
      /\ regs_agree (fun r => In r [10; 11; 18; 19; 21; 22; 23; 24]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3a0 :: dA_1f3f8 :: nil).
    intros regs m dp nc cm arr Hdp Hdp64 Hnc Hcm Hcm64 Harr Harr64 SOK Rg H10 H9 H21 H22. eexists. split.
    - stepST F_2462c D_2462c (Z_to_bv 64 cm) (Z_to_bv 64 arr) ltac:(sok_in SOK).
      stepST F_24630 D_24630 (Z_to_bv 64 (cm + 16)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepiv F_24634 D_24634 (Z_to_bv 64 (nc * 2 ^ 32)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; reflexivity).
      zv F_24638 D_24638 (Z_to_bv 64 (dp + 3)).
      sn F_2463c D_2463c. sn F_24640 D_24640.
      sn F_24644 D_24644. fixv (Z_to_bv 64 nc) ltac:(rewrite zbv_srli by (cbn; lia); f_equal; rewrite Z.div_mul by lia; reflexivity).
      stepLD F_24648 D_24648 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420)
        ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      sn F_2464c D_2464c. sn F_24650 D_24650. sn F_24654 D_24654. sn F_24658 D_24658. sn F_2465c D_2465c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pcd_C : forall regs m (s : Z) (cm ret : word) (sv : nat -> word),
    (80 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (sv 8%nat)) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (sv 9%nat)) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (sv 18%nat)) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (sv 19%nat)) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (sv 20%nat)) ->
    rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (sv 21%nat)) ->
    rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (sv 22%nat)) ->
    rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (sv 23%nat)) ->
    rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (sv 24%nat)) ->
    getr regs 2 = Z_to_bv 64 (s - 80) -> getr regs 9 = cm ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_24498 0x245a0) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = cm
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ getr regs' 24 = sv 24%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs m s cm ret sv Hs Hs64 Hret R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 H2 H9. eexists. split.
    - sn F_245a0 D_245a0.
      stepLD8 F_245a4 D_245a4 ret. stepLD8 F_245a8 D_245a8 (sv 8%nat). stepLD8 F_245ac D_245ac (sv 9%nat).
      stepLD8 F_245b0 D_245b0 (sv 18%nat). stepLD8 F_245b4 D_245b4 (sv 19%nat). stepLD8 F_245b8 D_245b8 (sv 20%nat).
      stepLD8 F_245bc D_245bc (sv 21%nat). stepLD8 F_245c0 D_245c0 (sv 22%nat). stepLD8 F_245c4 D_245c4 (sv 23%nat).
      stepLD8 F_245c8 D_245c8 (sv 24%nat).
      zv F_245cc D_245cc (Z_to_bv 64 s).
      stepret F_245d0 D_245d0 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

End Segs.

Definition frame10 (s : Z) (ret : word) (regs : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr regs 8); ((s - 24)%Z, getr regs 9); ((s - 32)%Z, getr regs 18); ((s - 40)%Z, getr regs 19);
   ((s - 48)%Z, getr regs 20); ((s - 56)%Z, getr regs 21); ((s - 64)%Z, getr regs 22); ((s - 72)%Z, getr regs 23);
   ((s - 80)%Z, getr regs 24)].

Lemma cells_FR10 : forall m s ret regs, (80 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FR10 m s ret regs) (frame10 s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold frame10, FR10. cbn [cellsZ]. repeat split; rdn_solve. Qed.


(* [comment removed for export] *)
Definition cmapd_new (C : lctx) (A A' : AS) (m' : word -> option byte) (cm arr nc : Z) : Prop :=
  (1 <= cm)%Z /\ (cm + 24 <= alloc_top (c_vm C))%Z /\ (cm mod 16 = 0)%Z /\
  (1 <= arr)%Z /\ (arr + 4 * 2 ^ cdepth nc <= alloc_top (c_vm C))%Z /\ (arr mod 16 = 0)%Z /\ cm <> arr /\
  live A (Z_to_bv 64 cm) = None /\ live A (Z_to_bv 64 arr) = None /\
  live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  live A' (Z_to_bv 64 cm) = Some 24%Z /\ live A' (Z_to_bv 64 arr) = Some (4 * 2 ^ cdepth nc)%Z /\
  (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 arr -> live A' q = live A q) /\
  CMAPat m' cm (CMAPV arr (cdepth nc) (2 ^ cdepth nc) nc 0).

(* [comment removed for export] *)
Lemma blk_rdn : forall C A m md (p : word) (n a : Z) (k : nat), Cok C -> W C A m md -> live A p = Some n ->
  (u p <= a)%Z -> (a + Z.of_nat k <= u p + n)%Z -> exists bs, rdn SEGS m (Z_to_bv 64 a) k = Some bs.
Proof.
  intros C A m md p n a k CK HW L Ha Hk. pose proof (u64_range p).
  pose proof (alloc_top_lt (m_vmmaps md)) as T. unfold two_pow_64 in T.
  pose proof (ai_live_hull A m (m_vmmaps md) p n (w_inv _ _ _ _ HW) L) as (Hn0 & _ & TOP & _). pose proof (round16_ge n Hn0).
  revert a Ha Hk. induction k as [|k IH]; intros a Ha Hk; [exists []; reflexivity|].
  cbn [rdn]. destruct (blk_byte C A m md p n (Z_to_bv 64 a) CK HW L ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _).
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [|exfalso; exact (D eq_refl)].
  destruct (IH (a + 1)%Z ltac:(lia) ltac:(lia)) as [bs Hbs]. rewrite zbv_plus1, Hbs. exists (b :: bs). reflexivity.
Qed.

Theorem pixcmapDeserialize_W : forall C A m md regs (s dp nc : Z) (pb : word) (kb : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 4 -> getr regs 12 = Z_to_bv 64 nc -> (1 <= nc <= 256)%Z ->
  live (c_A0 C) pb = Some kb -> (u pb <= dp)%Z -> (dp + 4 * nc <= u pb + kb)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmap <= kR)%Z -> (RB_cmap <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists cm arr, getr regs' 10 = Z_to_bv 64 cm /\ cmapd_new C A A' m' cm arr nc)) ->
     aroom A' vm' (kR - RK_cmap) (bR - RB_cmap) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (rl dOL_24498 0x24498) m al_rom) md) S.
Proof.
  intros C A m md regs s dp nc pb kb ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hnc Lpb0 Hdp1 Hdp2 kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  pose proof (W_sub0 _ _ _ _ HW _ _ Lpb0) as Lpb.
  destruct (blk_range C A m md pb kb CK HW Lpb ltac:(lia)) as [Gpb TOPpb].
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (W_sok_win C A m md (s - 80) 80 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  pose proof (cdepth_cases nc) as Hdc. pose proof (cdepth_fits nc Hnc) as [Hfit Hpow].
  set (d := cdepth nc) in *.
  pose proof (alloc_margin_le (1 * 24)) as MG1. pose proof (alloc_margin_le (2 ^ d * 4)) as MG2.
  assert (Hrk' : (2 <= kR)%Z) by (unfold RK_cmap in Hrk; exact Hrk).
  assert (Hrb' : (2 ^ 24 <= bR)%Z) by (unfold RB_cmap in Hrb; exact Hrb).
  (* [comment removed for export] *)
  destruct (pcd_A al_rom regs m s dp nc ret ltac:(lia) ltac:(lia) ltac:(lia) Hnc SOK H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q21 & Q18 & Q19 & Q22 & AG1).
  fold d in Q18.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR10 m s ret regs) md /\ POSTM C A s m (FR10 m s ret regs)) by (unfold FR10; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR10 m s ret regs) in *.
  pose proof (cells_FR10 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (Q4 : getr r1 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
  apply (W_calloc16_sure C A M1 md r1 1 24 kR bR (rl dOL_24498 0x24610) (s - 80) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           Hrm ltac:(lia) ltac:(change (2 ^ 22)%Z with 4194304%Z in MG1; change (2 ^ 24)%Z with 16777216%Z in Hrb'; lia)
           ltac:(unfold ROOM_NMAX; cbn; lia) Q1
           ltac:(rl_ret_ok_OL) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa Hroom1.
  assert (E2a : getr r2 2 = Z_to_bv 64 (s - 80)) by (csr; reflexivity).
  assert (E18a : getr r2 18 = Z_to_bv 64 d) by (csr; reflexivity).
  assert (E19a : getr r2 19 = Z_to_bv 64 1) by (csr; reflexivity).
  assert (E4a : getr r2 4 = rl dA_2f6b0 0x2f7b8) by (csr; reflexivity).
  assert (Hcm : (1 <= u res)%Z /\ (u res + 32 <= alloc_top (c_vm C))%Z).
  { pose proof (u64_range res). unfold round16 in TOP.
    change ((1 * 24 + 15) / 16)%Z with 2%Z in TOP. lia. }
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (cm := u res) in *. clearbody cm.
  rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
  assert (CM0 : CMAPat m1 cm cmap0).
  { apply CMAPat_zero; [lia | lia |]. intros i Hi. unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
  (* [comment removed for export] *)
  destruct (pcd_A2 al_rom r2 m1 d cm Hdc ltac:(lia) ltac:(lia)) as (r3 & RUN3 & P1 & P10 & P11 & P9 & P20 & AG3).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso. exact (CMAPat_defined m1 cm cmap0 x CM0 ltac:(lia) E). }
  { exact Hres. } { exact E18a. } { exact E19a. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  set (M2 := wbytes (wbytes m1 _ _) _ _).
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A (s - 80) M1 M2).
  { subst M2. apply (WP_blk C A A1 M1 _ _ (Z_to_bv 64 cm) _ 24); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    apply (WP_blk C A A1 M1 _ _ (Z_to_bv 64 cm) _ 24); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HWa | exact PMa]. }
  destruct WP2 as [HW2 PM2].
  assert (CM2 : CMAPat M2 cm (CMAPV 0 d (2 ^ d) 0 0)).
  { subst M2. apply (CMAP_wr_nalloc _ cm (CMAPV 0 d 0 0 0) (2 ^ d)); [|lia].
    apply (CMAP_wr_d m1 cm cmap0 d); [exact CM0 | lia]. }
  assert (P4 : getr r3 4 = rl dA_2f6b0 0x2f7b8) by (rewrite (AG3 4) by (cbv; intuition discriminate); exact E4a).
  assert (P2 : getr r3 2 = Z_to_bv 64 (s - 80)) by (rewrite (AG3 2) by (cbv; intuition discriminate); exact E2a).
  apply (W_calloc16_sure C A1 M2 _ r3 (2 ^ d) 4 (kR - 1) (bR - alloc_margin (1 * 24)) (rl dOL_24498 0x2462c) (s - 80) S CK HW2 P10 P11 ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(rewrite with_vmmaps_vmmaps; exact Hroom1) ltac:(lia)
           ltac:(change (2 ^ 22)%Z with 4194304%Z in MG1, MG2; change (2 ^ 24)%Z with 16777216%Z in Hrb'; lia)
           ltac:(unfold ROOM_NMAX; change (2 ^ 28)%Z with 268435456%Z; lia) P1
           ltac:(rl_ret_ok_OL) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 res2 HWb Hres2 CSb Hnz2 J0 J1 J00 JEQ ZERO2 AL16b TOP2 PMb Hroom2. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
  assert (E2b : getr r4 2 = Z_to_bv 64 (s - 80)) by (csr; reflexivity).
  assert (E9b : getr r4 9 = Z_to_bv 64 cm) by (csr; reflexivity).
  assert (E8b : getr r4 8 = Z_to_bv 64 4) by (csr; reflexivity).
  assert (E20b : getr r4 20 = Z_to_bv 64 4) by (csr; reflexivity).
  assert (E21b : getr r4 21 = Z_to_bv 64 dp) by (csr; reflexivity).
  assert (E22b : getr r4 22 = Z_to_bv 64 nc) by (csr; reflexivity).
  (* [comment removed for export] *)
  assert (CM3 : CMAPat m2 cm (CMAPV 0 d (2 ^ d) 0 0)).
  { apply (CMAPat_frame M2); [exact CM2|]. intros x Hx. pose proof (proj2 PMb (Z_to_bv 64 cm) 24%Z (u x - cm)%Z L1 ltac:(lia)) as E.
    unfold at_ in E. rewrite u_Z2bv in E by lia. replace (cm + (u x - cm))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
  assert (PMb' : POSTM C A (s - 80) M1 m2).
  { eapply POSTM_trans; [exact PM2|]. apply (POSTM_sub C A A1); [exact SUBa|]. exact PMb. }
  assert (Harr : (1 <= u res2)%Z /\ (u res2 + 4 * 2 ^ d <= alloc_top (c_vm C))%Z).
  { pose proof (u64_range res2). pose proof (round16_ge (2 ^ d * 4) ltac:(lia)). lia. }
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  set (arr := u res2) in *. clearbody arr.
  rewrite Eres2 in Hres2, J0, J1, J00, JEQ.
  assert (NEca : cm <> arr) by (intros E; rewrite <- E in J0; congruence).
  assert (NEw : Z_to_bv 64 cm <> Z_to_bv 64 arr).
  { intros E. apply NEca. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. }
  assert (Lc1 : live A2 (Z_to_bv 64 cm) = Some 24%Z) by (rewrite (JEQ _ NEw); exact L1).
  assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
  assert (SOKc2 : store_ok SEGS m2 (Z_to_bv 64 cm) 24 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (CMAPat_defined m2 cm _ x CM3 ltac:(lia) E). }
  set (M3 := wbytes (wbytes m2 (Z_to_bv 64 cm) (word_to_le_bytes 8 (Z_to_bv 64 arr))) (Z_to_bv 64 (cm + 16)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A (s - 80) M1 M3).
  { subst M3. apply (WP_blk C A A2 M1 _ _ (Z_to_bv 64 cm) _ 24); [exact CK | | exact Lc1 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    apply (WP_blk C A A2 M1 _ _ (Z_to_bv 64 cm) _ 24); [exact CK | | exact Lc1 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HWb | exact PMb']. }
  destruct WP3 as [HW3 PM3].
  assert (PM3s : POSTM C A s m M3) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM3]; lia]).
  assert (LAarr : live A (Z_to_bv 64 arr) = None) by (rewrite <- (LEQ _ (not_eq_sym NEw)); exact J0).
  assert (La1 : live A2 (Z_to_bv 64 arr) = Some (4 * 2 ^ d)%Z) by (rewrite Z.mul_comm; exact J1).
  assert (EQ2 : forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 arr -> live A2 q = live A q).
  { intros q N1 N2. rewrite (JEQ q N2). apply LEQ. exact N1. }
  assert (CM4 : CMAPat M3 cm (CMAPV arr d (2 ^ d) 0 0)).
  { subst M3. apply (CMAP_wr_n _ cm (CMAPV arr d (2 ^ d) 0 0) 0); [|lia]. apply (CMAP_wr_arr m2 cm (CMAPV 0 d (2 ^ d) 0 0) arr CM3). lia. }
  (* [comment removed for export] *)
  destruct (pcd_B al_rom r4 m2 dp nc cm arr ltac:(lia) ltac:(lia) Hnc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOKc2
              (W_sev_got C A2 M3 _ HW3) Hres2 E9b E21b E22b)
    as (r5 & RUN5 & V9 & V21 & V23 & V22 & V24 & V18 & V19 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
  fold M3.
  assert (V2 : getr r5 2 = Z_to_bv 64 (s - 80)) by (csr; reflexivity).
  assert (V8 : getr r5 8 = Z_to_bv 64 4) by (csr; reflexivity).
  assert (V20 : getr r5 20 = Z_to_bv 64 4) by (csr; reflexivity).
  assert (CE3 : cellsZ M3 (frame10 s ret regs)).
  { apply (cellsZ_frm C (s - 80) M1 M3 _ CK (proj1 PM3) ltac:(lia)); [|exact CE1]. unfold frame10.
    repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. }
  (* [comment removed for export] *)
  assert (Lpb2 : live A2 pb = Some kb) by (exact (W_sub0 _ _ _ _ HW3 _ _ Lpb0)).
  destruct (blk_rdn C A2 M3 _ pb kb dp (Z.to_nat (4 * nc)) CK HW3 Lpb2 ltac:(lia) ltac:(lia)) as [pbs Hpbs].
  set (sv := fun i : nat => match i with 8%nat => getr regs 8 | 9%nat => getr regs 9 | 18%nat => getr regs 18 | 19%nat => getr regs 19
              | 20%nat => getr regs 20 | 21%nat => getr regs 21 | 22%nat => getr regs 22 | 23%nat => getr regs 23 | _ => getr regs 24 end).
  pose proof (ai_live_disjoint A2 M3 _ _ _ _ _ (w_inv _ _ _ _ HW3) Lc1 La1 NEw) as Dca. rewrite !u_Z2bv in Dca by lia.
  unfold round16 in Dca at 1. change ((24 + 15) / 16)%Z with 2%Z in Dca. pose proof (round16_ge (4 * 2 ^ d) ltac:(lia)) as R16a.
  assert (NEcp : Z_to_bv 64 cm <> pb) by (intros E; rewrite E in L0; pose proof (W_sub0 _ _ _ _ HW _ _ Lpb0); congruence).
  assert (NEap : Z_to_bv 64 arr <> pb) by (intros E; rewrite E in LAarr; pose proof (W_sub0 _ _ _ _ HW _ _ Lpb0); congruence).
  pose proof (ai_live_disjoint A2 M3 _ _ _ _ _ (w_inv _ _ _ _ HW3) Lc1 Lpb2 NEcp) as Dcp. rewrite u_Z2bv in Dcp by lia.
  unfold round16 in Dcp at 1. change ((24 + 15) / 16)%Z with 2%Z in Dcp. pose proof (round16_ge kb ltac:(lia)) as R16b.
  pose proof (ai_live_disjoint A2 M3 _ _ _ _ _ (w_inv _ _ _ _ HW3) La1 Lpb2 NEap) as Dap. rewrite u_Z2bv in Dap by lia.
  assert (SOKa : store_ok SEGS M3 (Z_to_bv 64 arr) (Z.to_nat (4 * 2 ^ d)) = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
    unfold wview. destruct (M3 x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A2 M3 _ (Z_to_bv 64 arr) _ x CK HW3 La1 ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
  assert (SOKc : store_ok SEGS M3 (Z_to_bv 64 cm) (Z.to_nat 24) = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (M3 x) eqn:E; [discriminate|]. exfalso. exact (CMAPat_defined M3 cm _ x CM4 ltac:(lia) E). }
  assert (PRE : SSP.spec_pre SEGS (SSP.spec_cmapfill (0x2469c + dOL_24498) (0x245a0 + dOL_24498) 9 21 3 23 [(8%nat,4%Z);(20%nat,4%Z)] CMAP_CLOB)
                 [cm; dp + 3; nc; arr; 2 ^ d; 0; 4; 4]%Z r5 M3).
  { unfold SSP.spec_cmapfill. cbn [SSP.lit_items app]. SSP.spec_unfold. cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
    rewrite V9, V21, V23, V8, V20. replace (dp + 3 + - (3))%Z with dp by lia. rewrite !Z.add_0_r.
    split; [|split; [|split; exact I]].
    - split; [split; [reflexivity | lia]|]. split; [lia|]. split; [split; [lia | rewrite <- (Z.add_0_r cm); apply mod16_plus_mod8; [exact AL16 | reflexivity]]|].
      split; [split; [reflexivity | lia]|]. split; [split; [reflexivity | lia]|]. split; [lia|]. split; [lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (CMAP_rd_arr SEGS M3 cm _ CM4)]]]|]. split; [lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [lia | exact (CMAP_rd_nalloc SEGS M3 cm _ CM4)]]]|]. split; [lia|]. split; [lia|].
      split; [split; [cbn; lia | split; [unfold SSP.flatZ; cbn; lia | split; [cbn; lia | exact (CMAP_rd_n SEGS M3 cm _ CM4)]]]|]. split; [reflexivity|].
      split; [split; [unfold SSP.flatZ; lia | exists pbs; exact Hpbs]|].
      split; [split; [unfold SSP.flatZ; lia | exact SOKa]|].
      split; [split; [unfold SSP.flatZ; lia | exact SOKc]|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [split; [reflexivity | lia]|]. split; [reflexivity|]. split; [split; [reflexivity | lia]|]. split; [reflexivity | exact I].
    - split; [unfold SSP.flatZ; lia|]. split; [cbn; lia|]. split; [unfold SSP.flatZ; cbn; lia | exact I]. }
  pose proof (cmapfill_contract (fx:=fx)) as CT. unfold SSP.sum_contract in CT.
  destruct (CT [cm; dp + 3; nc; arr; 2 ^ d; 0; 4; 4]%Z r5 M3 al_rom eq_refl PRE) as (outs & R' & M' & _ & RUN & POST).
  unfold SSP.spec_cmapfill, CMAP_CLOB in POST. cbn [SSP.lit_items app] in POST. SSP.spec_unfold_in POST.
  destruct POST as (KEPT & _ & FRMx & GR & (_ & CELLn & _) & _).
  cbn [SSP.su_entry SSP.exit_target SSP.su_exit SSP.spec_cmapfill] in RUN.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul] in FRMx, CELLn.
  replace (nc mod 2 ^ 32)%Z with nc in CELLn by (symmetry; apply Z.mod_small; lia).
  assert (OUT : forall a : word, ~ (arr <= u a < arr + 4 * nc)%Z -> ~ (cm + 16 <= u a < cm + 20)%Z -> M' a = M3 a).
  { intros a H1' H2'. apply FRMx. split; [lia | split; [lia | exact I]]. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | |].
  { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ => replace pc with (rl dOL_24498 0x2469c) by (apply bv_eq; reflexivity) end. exact RUN. }
  destruct KEPT as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K17 & K18 & K19 & K20 & K22 & K23 & K25 & K26 & K27 & K28 & K29 & K30 & K31 & _).
  assert (CH : forall a, M' a <> M3 a -> scratch C s a \/ (exists p n, live A2 p = Some n /\ live A p = None /\ (u p <= u a < u p + n)%Z)).
  { intros a NE. right. destruct (Z_lt_ge_dec (u a) arr) as [B1|B1]; [| destruct (Z_lt_ge_dec (u a) (arr + 4 * nc)) as [B2|B2]].
    - exists (Z_to_bv 64 cm), 24%Z. rewrite u_Z2bv by lia. split; [exact Lc1 | split; [exact L0|]].
      destruct (Z_lt_ge_dec (u a) (cm + 16)); [exfalso; apply NE; apply OUT; lia|]. destruct (Z_lt_ge_dec (u a) (cm + 20)); [lia|]. exfalso; apply NE; apply OUT; lia.
    - exists (Z_to_bv 64 arr), (4 * 2 ^ d)%Z. rewrite u_Z2bv by lia. split; [exact La1 | split; [exact LAarr | lia]].
    - exists (Z_to_bv 64 cm), 24%Z. rewrite u_Z2bv by lia. split; [exact Lc1 | split; [exact L0|]].
      destruct (Z_lt_ge_dec (u a) (cm + 16)); [exfalso; apply NE; apply OUT; lia|]. destruct (Z_lt_ge_dec (u a) (cm + 20)); [lia|]. exfalso; apply NE; apply OUT; lia. }
  assert (HW4 : W C A2 M' (with_vmmaps vm2 md)).
  { apply (W_local C A2 M3 _ M' s CK HW3 Hhi); [|exact GR]. intros a NE. destruct (CH a NE) as [X|(p & n & L & L0' & R)]; [left; exact X | right].
    exists p, n. split; [exact L | split; [|exact R]].
    destruct (bv_eq_dec _ p (Z_to_bv 64 cm)) as [->|N1]; [exact L00|]. destruct (bv_eq_dec _ p (Z_to_bv 64 arr)) as [->|N2]; [exact J00|].
    rewrite (EQ2 p N1 N2) in L. exfalso. (* [comment removed for export] *) rewrite L0' in L. discriminate. }
  pose proof (sub_live_new2 _ _ _ _ _ _ L0 LAarr Lc1 La1 EQ2) as SUBf.
  assert (PM4 : POSTM C A s m M') by (eapply POSTM_trans; [exact PM3s | exact (POSTM_local C A A2 M3 _ M' s CK HW3 SUBf CH)]).
  assert (CM5 : CMAPat M' cm (CMAPV arr (d) (2 ^ d) nc 0)).
  { apply (CMAPat_set_n SEGS M3 M' cm (CMAPV arr (d) (2 ^ d) 0 0) nc CM4 ltac:(lia)).
    - intros x Hx Hn. apply OUT; lia.
    - intros x Hx. destruct (blk_byte C A2 M' _ (Z_to_bv 64 cm) 24 x CK HW4 Lc1 ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact D.
    - destruct CELLn as [_ R]. change (8 * 4)%Z with 32%Z in R. rewrite Z.mod_small in R by lia. exact R. }
  assert (OUTw : forall a : word, (s - 80 <= u a < s)%Z -> M' a = M3 a) by (intros a Ha; apply OUT; lia).
  assert (Hs96 : (80 <= s < 2 ^ 64)%Z) by lia.
  assert (CE4 : cellsZ M' (frame10 s ret regs)).
  { apply (cellsZ_keep M3 M'); [|exact CE3]. unfold frame10. generalize OUTw. generalize Hs96. clear. intros Hs96 OUTw.
    repeat (apply Forall_cons; [cbn [fst snd]; split; [lia | split; [lia | intros x Hx; apply OUTw; lia]] |]). apply Forall_nil. }
  unfold frame10 in CE4. cbn [cellsZ] in CE4. destruct CE4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & _).
  destruct (pcd_C al_rom R' M' s (Z_to_bv 64 cm) ret sv ltac:(lia) ltac:(lia) Hret C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 ltac:(rewrite K2; exact V2) ltac:(rewrite K9; exact V9))
    as (r6 & RUN6 & U2 & U1 & U10 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & U23 & U24 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |].
  apply (HK A2 M' vm2 r6 HW4).
  + apply cs_kept_intro; csr; reflexivity.
  + exact PM4.
  + right. exists cm, arr. split; [exact U10|]. unfold cmapd_new. fold d. do 14 (split; [first [assumption | lia] |]). exact CM5.
  + room_tac.
Qed.

End CmapDeser.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
