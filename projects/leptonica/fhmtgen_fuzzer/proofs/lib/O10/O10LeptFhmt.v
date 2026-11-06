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
Import O10CL7a.O10LeptErr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10CL8a.
Import O10CL8a.O10LeptPixHdr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10_code_fhH.
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

Definition PC_pixFHMTGen_1 : Z := 0x210e0.
Definition PC_pixHMTDwa_1 : Z := 0x20fc0.
Definition A_SELNAMES : Z := 0x2caa8.        (* [comment removed for export] *)

Section Fhmt.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition FRG (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
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
Definition frameG (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, getr r0 19); ((s - 48)%Z, getr r0 20);
   ((s - 56)%Z, getr r0 21); ((s - 64)%Z, getr r0 22); ((s - 72)%Z, getr r0 23); ((s - 80)%Z, getr r0 24)].

Lemma v_slliw_5 : forall a, v_slliw (Z_to_bv 64 a) 5 = Z_to_bv 64 (sw32 (a * 32)).
Proof.
  intros a. unfold v_slliw. rewrite u_zbv, sw32_eq, Z.shiftl_mul_pow2 by lia. unfold zx. f_equal. change (2 ^ 5)%Z with 32%Z.
  rewrite <- (sw32_mod (a mod 2 ^ 64 * 32) ((a / 2 ^ 64) * 2 ^ 37)). f_equal.
  pose proof (Z.div_mod a (2 ^ 64) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma c_eq_small_ne0 : forall z : Z, (- 256 < z < 256)%Z -> z <> 0%Z -> c_eq (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof.
  intros z Hz Hnz. rewrite c_eq_Zm. apply Z.eqb_neq. rewrite (Z.mod_small 0) by lia. intros E.
  destruct (Z_lt_ge_dec z 0) as [N|N]; [| rewrite Z.mod_small in E by lia; lia].
  rewrite <- (Z_mod_plus_full z 1 (2 ^ 64)) in E. rewrite Z.mod_small in E by lia. lia.
Qed.

Section Segs.
Variable rom : word -> option byte.

  Ltac fg_prologue s ret regs SOK :=
    zv F_20fe4 D_20fe4 (Z_to_bv 64 (s - 96));
    stepST F_20fe8 D_20fe8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
    stepST F_20fec D_20fec (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
    stepST F_20ff0 D_20ff0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
    stepST F_20ff4 D_20ff4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
    stepST F_20ff8 D_20ff8 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK);
    stepST F_20ffc D_20ffc (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK);
    stepST F_21000 D_21000 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK);
    stepST F_21004 D_21004 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK);
    stepST F_21008 D_21008 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK);
    stepST F_2100c D_2100c (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK);
    sn F_21010 D_21010.

  (* [comment removed for export] *)
  Lemma fg_A : forall regs m (s pixd0 pixs name : Z) (vs : pixv) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> PIXat m pixs vs -> p_d vs = 1%Z -> (pixs + 64 <= s - 96 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 name ->
    exists regs',
      msteps SEGS (mkst regs (0x210e0 : word) m rom) (mkst regs' (0x2a4c4 : word) (FRG m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x21140 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 0x2caa8
      /\ getr regs' 8 = Z_to_bv 64 pixd0 /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 name /\ getr regs' 19 = Z_to_bv 64 0x2caa8
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pixd0 pixs name vs ret Hs Hs64 Hp PX Hd DJ SOK H2 H1 H10 H11 H12.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (PX1 : PIXat (FRG m s ret regs) pixs vs).
    { unfold FRG. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd.
    unfold FRG in *. eexists. split.
    - fg_prologue s ret regs SOK.
      stepb_ft F_21014 D_21014 ltac:(condZ).
      sn F_21018 D_21018. sn F_2101c D_2101c. sn F_21020 D_21020. sn F_21024 D_21024.
      stepb_ft F_16bf0 D_16bf0 ltac:(condZ).
      stepLD F_16bf4 D_16bf4 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite ?(v_lw_small 1) by lia.
      stepret F_16bf8 D_16bf8 (0x21124 : word) ltac:(bveq).
      sn F_21028 D_21028. stepb_ft F_2102c D_2102c ltac:(condZ).
      sn F_21030 D_21030. sn F_21034 D_21034. sn F_21038 D_21038. sn F_2103c D_2103c. sn F_21040 D_21040.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fg_N1 : forall regs m (s pixd0 : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd0 -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x210e0 : word) m rom) (mkst regs' (0x211fc : word) (FRG m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 8 = Z_to_bv 64 pixd0
      /\ regs_agree (fun r => In r [2; 8]%list) regs regs'.
  Proof.
    intros regs m s pixd0 ret Hs Hs64 SOK H2 H1 H10 H11. unfold FRG. eexists. split.
    - fg_prologue s ret regs SOK.
      stepb_tk F_21014 D_21014 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Ltac fg_restore r0 ret s :=
    stepLD8 F_21150 D_21150 ret; stepLD8 F_21154 D_21154 (getr r0 8); stepLD8 F_21158 D_21158 (getr r0 9);
    stepLD8 F_2115c D_2115c (getr r0 18); stepLD8 F_21160 D_21160 (getr r0 19); stepLD8 F_21164 D_21164 (getr r0 20);
    stepLD8 F_21168 D_21168 (getr r0 21); stepLD8 F_2116c D_2116c (getr r0 22); stepLD8 F_21170 D_21170 (getr r0 23);
    stepLD8 F_21174 D_21174 (getr r0 24); zv F_21178 D_21178 (Z_to_bv 64 s); sn F_2117c D_2117c.

  (* [comment removed for export] *)
  Lemma fg_N2 : forall regs r0 m (s pixd0 : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameG s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 8 = Z_to_bv 64 pixd0 ->
    exists regs',
      msteps SEGS (mkst regs (0x211fc : word) m rom) (mkst regs' (0x1573c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x108aa
      /\ getr regs' 12 = Z_to_bv 64 pixd0
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs r0 m s pixd0 ret Hs Hs64 Rg Rs CE H2 H8. unfold frameG in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & _).
    eexists. split.
    - sn F_21100 D_21100.
      stepLD F_21104 D_21104 (Z_to_le_bytes 8 0x2ca88) (Z_to_bv 64 0x2ca88) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_21108 D_21108 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_2110c D_2110c. stepb_ft F_21110 D_21110 ltac:(condZ).
      sn F_21114 D_21114. sn F_21118 D_21118. sn F_2111c D_2111c. sn F_21120 D_21120. sn F_21124 D_21124.
      sn F_2114c D_2114c.
      fg_restore r0 ret s.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fg_hit_0 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x21140 : word) m rom) (mkst regs' (0x212c8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_21044 D_21044 ltac:(condZ). sn F_21180 D_21180. sn F_21184 D_21184. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_0 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x21140 : word) m rom) (mkst regs (0x21144 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_21044 D_21044 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_1 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x2caa8 ->
    exists regs',
      msteps SEGS (mkst regs (0x21144 : word) m rom) (mkst regs' (0x2a4c4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x21150 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x2caa8 + 80 * 1)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_21048 D_21048 (Z_to_bv 64 (0x2caa8 + 80 * 1)). sn F_2104c D_2104c. sn F_21050 D_21050. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_1 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x21150 : word) m rom) (mkst regs' (0x212c8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_21054 D_21054 ltac:(condZ). sn F_21188 D_21188. sn F_2118c D_2118c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_1 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x21150 : word) m rom) (mkst regs (0x21154 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_21054 D_21054 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_2 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x2caa8 ->
    exists regs',
      msteps SEGS (mkst regs (0x21154 : word) m rom) (mkst regs' (0x2a4c4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x21160 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x2caa8 + 80 * 2)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_21058 D_21058 (Z_to_bv 64 (0x2caa8 + 80 * 2)). sn F_2105c D_2105c. sn F_21060 D_21060. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_2 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x21160 : word) m rom) (mkst regs' (0x212c8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_21064 D_21064 ltac:(condZ). sn F_21190 D_21190. sn F_21194 D_21194. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_2 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x21160 : word) m rom) (mkst regs (0x21164 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_21064 D_21064 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_3 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x2caa8 ->
    exists regs',
      msteps SEGS (mkst regs (0x21164 : word) m rom) (mkst regs' (0x2a4c4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x21170 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x2caa8 + 80 * 3)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_21068 D_21068 (Z_to_bv 64 (0x2caa8 + 80 * 3)). sn F_2106c D_2106c. sn F_21070 D_21070. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_3 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x21170 : word) m rom) (mkst regs' (0x212c8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 3
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_21074 D_21074 ltac:(condZ). sn F_21198 D_21198. sn F_2119c D_2119c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_3 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x21170 : word) m rom) (mkst regs (0x21174 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_21074 D_21074 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_4 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x2caa8 ->
    exists regs',
      msteps SEGS (mkst regs (0x21174 : word) m rom) (mkst regs' (0x2a4c4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x21180 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x2caa8 + 80 * 4)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_21078 D_21078 (Z_to_bv 64 (0x2caa8 + 80 * 4)). sn F_2107c D_2107c. sn F_21080 D_21080. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_4 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x21180 : word) m rom) (mkst regs' (0x212c8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 4
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_21084 D_21084 ltac:(condZ). sn F_211a0 D_211a0. sn F_211a4 D_211a4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_4 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x21180 : word) m rom) (mkst regs (0x21184 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_21084 D_21084 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_5 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x2caa8 ->
    exists regs',
      msteps SEGS (mkst regs (0x21184 : word) m rom) (mkst regs' (0x2a4c4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x21190 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x2caa8 + 80 * 5)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_21088 D_21088 (Z_to_bv 64 (0x2caa8 + 80 * 5)). sn F_2108c D_2108c. sn F_21090 D_21090. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_5 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x21190 : word) m rom) (mkst regs' (0x212c8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 5
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_21094 D_21094 ltac:(condZ). sn F_211a8 D_211a8. sn F_211ac D_211ac. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_5 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x21190 : word) m rom) (mkst regs (0x21194 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_21094 D_21094 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_6 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x2caa8 ->
    exists regs',
      msteps SEGS (mkst regs (0x21194 : word) m rom) (mkst regs' (0x2a4c4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x211a0 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x2caa8 + 80 * 6)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_21098 D_21098 (Z_to_bv 64 (0x2caa8 + 80 * 6)). sn F_2109c D_2109c. sn F_210a0 D_210a0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_6 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x211a0 : word) m rom) (mkst regs' (0x212c8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 6
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_210a4 D_210a4 ltac:(condZ). sn F_211b0 D_211b0. sn F_211b4 D_211b4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_6 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x211a0 : word) m rom) (mkst regs (0x211a4 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_210a4 D_210a4 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_7 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x2caa8 ->
    exists regs',
      msteps SEGS (mkst regs (0x211a4 : word) m rom) (mkst regs' (0x2a4c4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x211b0 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x2caa8 + 80 * 7)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_210a8 D_210a8 (Z_to_bv 64 (0x2caa8 + 80 * 7)). sn F_210ac D_210ac. sn F_210b0 D_210b0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_7 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x211b0 : word) m rom) (mkst regs' (0x212c8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 7
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_210b4 D_210b4 ltac:(condZ). sn F_211b8 D_211b8. sn F_211bc D_211bc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_7 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x211b0 : word) m rom) (mkst regs (0x211b4 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_210b4 D_210b4 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_8 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x2caa8 ->
    exists regs',
      msteps SEGS (mkst regs (0x211b4 : word) m rom) (mkst regs' (0x2a4c4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x211c0 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x2caa8 + 80 * 8)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_210b8 D_210b8 (Z_to_bv 64 (0x2caa8 + 80 * 8)). sn F_210bc D_210bc. sn F_210c0 D_210c0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_8 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x211c0 : word) m rom) (mkst regs' (0x212c8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 8
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_210c4 D_210c4 ltac:(condZ). sn F_211c0 D_211c0. sn F_211c4 D_211c4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_8 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x211c0 : word) m rom) (mkst regs (0x211c4 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_210c4 D_210c4 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_9 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x2caa8 ->
    exists regs',
      msteps SEGS (mkst regs (0x211c4 : word) m rom) (mkst regs' (0x2a4c4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x211d0 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x2caa8 + 80 * 9)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_210c8 D_210c8 (Z_to_bv 64 (0x2caa8 + 80 * 9)). sn F_210cc D_210cc. sn F_210d0 D_210d0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_9 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x211d0 : word) m rom) (mkst regs' (0x212c8 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 9
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_210d4 D_210d4 ltac:(condZ). sn F_211c8 D_211c8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fg_B : forall regs m (pixs : Z),
    getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x212c8 : word) m rom) (mkst regs' (0x16080 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x212e4 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m pixs H8 H9. eexists. split.
    - stepb_tk F_211cc D_211cc ltac:(condZ). sn F_211e0 D_211e0. sn F_211e4 D_211e4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fg_F : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameG s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x212e4 : word) m rom) (mkst regs' (0x1573c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x1054a /\ getr regs' 11 = Z_to_bv 64 0x108aa
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Rg Rs CE H2 H10. unfold frameG in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & _).
    eexists. split.
    - sn F_211e8 D_211e8. stepb_tk F_211ec D_211ec ltac:(condZ).
      sn F_212c4 D_212c4.
      stepLD F_212c8 D_212c8 (Z_to_le_bytes 8 0x2ca88) (Z_to_bv 64 0x2ca88) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_212cc D_212cc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_212d0 D_212d0. stepb_ft F_212d4 D_212d4 ltac:(condZ).
      sn F_212d8 D_212d8. sn F_212dc D_212dc. sn F_212e0 D_212e0. sn F_212e4 D_212e4. sn F_212e8 D_212e8. sn F_212ec D_212ec.
      fg_restore r0 ret s.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fg_C : forall regs m (pixs pixd index : Z) (vs vd : pixv),
    (1 <= pixs)%Z -> (1 <= pixd)%Z -> pixs <> pixd -> PIXat m pixs vs -> PIXat m pixd vd ->
    (65 <= p_w vs <= 20000)%Z -> (65 <= p_h vs <= 20000)%Z -> (1 <= p_wpl vs <= 627)%Z -> (1 <= p_wpl vd <= 627)%Z ->
    (p_data vs + 128 * p_wpl vs + 4 < 2 ^ 64)%Z -> (p_data vd + 128 * p_wpl vd + 4 < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs -> getr regs 18 = Z_to_bv 64 index ->
    exists regs',
      msteps SEGS (mkst regs (0x212e4 : word) m rom) (mkst regs' (0x2144c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2136c /\ getr regs' 8 = Z_to_bv 64 pixd
      /\ getr regs' 10 = Z_to_bv 64 (p_data vd + 128 * p_wpl vd + 4) /\ getr regs' 11 = Z_to_bv 64 (p_w vs - 64) /\ getr regs' 12 = Z_to_bv 64 (p_h vs - 64)
      /\ getr regs' 13 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 14 = Z_to_bv 64 (p_data vs + 128 * p_wpl vs + 4) /\ getr regs' 15 = Z_to_bv 64 (p_wpl vs)
      /\ getr regs' 16 = Z_to_bv 64 index
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 14; 15; 16; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs m pixs pixd index vs vd Hps Hpd NE PXs PXd Hw Hh Hwpls Hwpld Hds Hdd H10 H9 H18.
    pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    pose proof (wf_data _ WFs) as Rds. pose proof (wf_data _ WFd) as Rdd.
    pose proof (PIX_rd_wpl SEGS _ _ _ PXs) as Cwpls. pose proof (PIX_rd_wpl SEGS _ _ _ PXd) as Cwpld.
    pose proof (PIX_rd_w SEGS _ _ _ PXs) as Cw. pose proof (PIX_rd_h SEGS _ _ _ PXs) as Ch.
    pose proof (PIX_rd_data SEGS _ _ _ PXs) as Cds. pose proof (PIX_rd_data SEGS _ _ _ PXd) as Cdd.
    eexists. split.
    - sn F_211e8 D_211e8. stepb_ft F_211ec D_211ec ltac:(condZ).
      sn F_211f0 D_211f0. sn F_211f4 D_211f4.
      stepb_ft F_15e78 D_15e78 ltac:(condZ).
      stepLD F_15e7c D_15e7c (Z_to_le_bytes 4 (p_wpl vs)) (Z_to_bv 64 (p_wpl vs)) ltac:(addr_norm; exact Cwpls) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl vs)) by lia.
      stepret F_15e80 D_15e80 (0x212f4 : word) ltac:(bveq).
      sn F_211f8 D_211f8. sn F_211fc D_211fc. sn F_21200 D_21200.
      stepb_ft F_15e78 D_15e78 ltac:(condZ).
      stepLD F_15e7c D_15e7c (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; exact Cwpld) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl vd)) by lia.
      stepret F_15e80 D_15e80 (0x21300 : word) ltac:(bveq).
      sn F_21204 D_21204. sn F_21208 D_21208. sn F_2120c D_2120c.
      stepb_ft F_16d30 D_16d30 ltac:(condZ).
      stepLD F_16d34 D_16d34 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Cw) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepret F_16d38 D_16d38 (0x2130c : word) ltac:(bveq).
      sn F_21210 D_21210. fixv (Z_to_bv 64 (p_w vs - 64)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      sn F_21214 D_21214. sn F_21218 D_21218.
      stepb_ft F_16944 D_16944 ltac:(condZ).
      stepLD F_16948 D_16948 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepret F_1694c D_1694c (0x21318 : word) ltac:(bveq).
      sn F_2121c D_2121c. fixv (Z_to_bv 64 (p_h vs - 64)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      sn F_21220 D_21220. sn F_21224 D_21224.
      stepb_ft F_16cb0 D_16cb0 ltac:(condZ).
      stepLD F_16cb4 D_16cb4 (Z_to_le_bytes 8 (p_data vs)) (Z_to_bv 64 (p_data vs)) ltac:(addr_norm; exact Cds) ltac:(apply lez8; lia).
      stepret F_16cb8 D_16cb8 (0x21324 : word) ltac:(bveq).
      sn F_21228 D_21228.
      sn F_2122c D_2122c. fixv (Z_to_bv 64 (32 * p_wpl vs)) ltac:(rewrite v_slliw_5, sw32_small by lia; f_equal; lia).
      sn F_21230 D_21230. sn F_21234 D_21234.
      stepb_ft F_16cb0 D_16cb0 ltac:(condZ).
      stepLD F_16cb4 D_16cb4 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdd) ltac:(apply lez8; lia).
      stepret F_16cb8 D_16cb8 (0x21334 : word) ltac:(bveq).
      sn F_21238 D_21238. fixv (Z_to_bv 64 (32 * p_wpl vd)) ltac:(rewrite v_slliw_5, sw32_small by lia; f_equal; lia).
      stepiv F_2123c D_2123c (Z_to_bv 64 (128 * p_wpl vd)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_21240 D_21240 (Z_to_bv 64 (p_data vd + 128 * p_wpl vd)).
      zv F_21244 D_21244 (Z_to_bv 64 (p_data vd + 128 * p_wpl vd + 4)).
      stepb_ft F_21248 D_21248 ltac:(condZ).
      stepiv F_2124c D_2124c (Z_to_bv 64 (128 * p_wpl vs)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_21250 D_21250 (Z_to_bv 64 (p_data vs + 128 * p_wpl vs)).
      zv F_21254 D_21254 (Z_to_bv 64 (p_data vs + 128 * p_wpl vs + 4)).
      sn F_21258 D_21258. sn F_2125c D_2125c. sn F_21260 D_21260. sn F_21264 D_21264. sn F_21268 D_21268. sn F_2126c D_2126c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fg_D : forall regs r0 m (s pixd : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameG s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 8 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x2136c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs r0 m s pixd ret Hs Hs64 Hret CE H2 H8. unfold frameG in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & _).
    eexists. split.
    - sn F_21270 D_21270. sn F_2131c D_2131c.
      stepLD8 F_21320 D_21320 ret. stepLD8 F_21324 D_21324 (getr r0 8). stepLD8 F_21328 D_21328 (getr r0 9).
      stepLD8 F_2132c D_2132c (getr r0 18). stepLD8 F_21330 D_21330 (getr r0 19). stepLD8 F_21334 D_21334 (getr r0 20).
      stepLD8 F_21338 D_21338 (getr r0 21). stepLD8 F_2133c D_2133c (getr r0 22). stepLD8 F_21340 D_21340 (getr r0 23).
      stepLD8 F_21344 D_21344 (getr r0 24). zv F_21348 D_21348 (Z_to_bv 64 s). stepret F_2134c D_2134c ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.
End Segs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FRD (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)).
Definition frameD (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18)].

Section SegsD.
Variable rom : word -> option byte.

  Ltac hd_prologue s ret regs SOK :=
    zv F_20ec4 D_20ec4 (Z_to_bv 64 (s - 64));
    stepST F_20ec8 D_20ec8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
    stepST F_20ecc D_20ecc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
    stepST F_20ed0 D_20ed0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
    stepST F_20ed4 D_20ed4 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
    sn F_20ed8 D_20ed8.

  (* [comment removed for export] *)
  Lemma hd_A0 : forall regs m (s pixd0 pixs name : Z) (vs : pixv) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 64 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 name ->
    exists regs',
      msteps SEGS (mkst regs (0x20fc0 : word) m rom) (mkst regs' (0x20fec : word) (FRD m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 10 = Z_to_bv 64 (p_d vs)
      /\ getr regs' 8 = Z_to_bv 64 pixd0 /\ getr regs' 18 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 name
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18]%list) regs regs'.
  Proof.
    intros regs m s pixd0 pixs name vs ret Hs Hs64 Hp PX DJ SOK H2 H1 H10 H11 H12.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    assert (PX1 : PIXat (FRD m s ret regs) pixs vs).
    { unfold FRD. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
    unfold FRD in *. eexists. split.
    - hd_prologue s ret regs SOK.
      stepb_ft F_20edc D_20edc ltac:(condZ).
      sn F_20ee0 D_20ee0. sn F_20ee4 D_20ee4. sn F_20ee8 D_20ee8. sn F_20eec D_20eec.
      stepb_ft F_16bf0 D_16bf0 ltac:(condZ).
      stepLD F_16bf4 D_16bf4 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepret F_16bf8 D_16bf8 (0x20fec : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_A1 : forall regs m (pixs : Z),
    getr regs 10 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x20fec : word) m rom) (mkst regs' (0x17780 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x21004 /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 32 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixs H10 H18. eexists. split.
    - sn F_20ef0 D_20ef0. stepb_ft F_20ef4 D_20ef4 ltac:(condZ).
      sn F_20ef8 D_20ef8. sn F_20efc D_20efc. sn F_20f00 D_20f00. sn F_20f04 D_20f04. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Ltac hd_exit r0 ret s :=
    sn F_20fa8 D_20fa8;
    stepLD8 F_20fac D_20fac ret; stepLD8 F_20fb0 D_20fb0 (getr r0 8); stepLD8 F_20fb4 D_20fb4 (getr r0 9); stepLD8 F_20fb8 D_20fb8 (getr r0 18);
    zv F_20fbc D_20fbc (Z_to_bv 64 s); sn F_20fc0 D_20fc0.

  (* [comment removed for export] *)
  Lemma hd_AD : forall regs r0 m (s d pixd0 : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 32)%Z -> d <> 1%Z ->
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameD s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 d -> getr regs 8 = Z_to_bv 64 pixd0 ->
    exists regs',
      msteps SEGS (mkst regs (0x20fec : word) m rom) (mkst regs' (0x1573c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x11035 /\ getr regs' 11 = Z_to_bv 64 0x10728
      /\ getr regs' 12 = Z_to_bv 64 pixd0
      /\ (forall x, In x [8; 9; 18]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18]%list) regs regs'.
  Proof.
    intros regs r0 m s d pixd0 ret Hs Hs64 Hd Hd1 Rg Rs CE H2 H10 H8. unfold frameD in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & _).
    eexists. split.
    - sn F_20ef0 D_20ef0. stepb_tk F_20ef4 D_20ef4 ltac:(condZ).
      sn F_20f84 D_20f84.
      stepLD F_20f88 D_20f88 (Z_to_le_bytes 8 0x2ca88) (Z_to_bv 64 0x2ca88) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_20f8c D_20f8c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_20f90 D_20f90. stepb_ft F_20f94 D_20f94 ltac:(condZ).
      sn F_20f98 D_20f98. sn F_20f9c D_20f9c. sn F_20fa0 D_20fa0. sn F_20fa4 D_20fa4.
      hd_exit r0 ret s.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_N1 : forall regs m (s pixd0 : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd0 -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x20fc0 : word) m rom) (mkst regs' (0x21058 : word) (FRD m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 8 = Z_to_bv 64 pixd0
      /\ regs_agree (fun r => In r [2; 8]%list) regs regs'.
  Proof.
    intros regs m s pixd0 ret Hs Hs64 SOK H2 H1 H10 H11. unfold FRD. eexists. split.
    - hd_prologue s ret regs SOK. stepb_tk F_20edc D_20edc ltac:(condZ). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma hd_N2 : forall regs r0 m (s pixd0 : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x2ba18) 8 = Some (Z_to_le_bytes 8 0x2ca88) -> rdn SEGS m (Z_to_bv 64 0x2ca88) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameD s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 8 = Z_to_bv 64 pixd0 ->
    exists regs',
      msteps SEGS (mkst regs (0x21058 : word) m rom) (mkst regs' (0x1573c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10728
      /\ getr regs' 12 = Z_to_bv 64 pixd0
      /\ (forall x, In x [8; 9; 18]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18]%list) regs regs'.
  Proof.
    intros regs r0 m s pixd0 ret Hs Hs64 Rg Rs CE H2 H8. unfold frameD in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & _).
    eexists. split.
    - sn F_20f5c D_20f5c.
      stepLD F_20f60 D_20f60 (Z_to_le_bytes 8 0x2ca88) (Z_to_bv 64 0x2ca88) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_20f64 D_20f64 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_20f68 D_20f68. stepb_ft F_20f6c D_20f6c ltac:(condZ).
      sn F_20f70 D_20f70. sn F_20f74 D_20f74. sn F_20f78 D_20f78. sn F_20f7c D_20f7c. sn F_20f80 D_20f80.
      hd_exit r0 ret s.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_B : forall regs m (s pixt1 name : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 40)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 pixt1 -> getr regs 9 = Z_to_bv 64 name ->
    exists regs',
      msteps SEGS (mkst regs (0x21004 : word) m rom) (mkst regs' (0x210e0 : word) (wbytes m (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 pixt1))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x21018 /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixt1 /\ getr regs' 12 = Z_to_bv 64 name
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixt1 name Hs Hs64 SOK H2 H10 H9. eexists. split.
    - sn F_20f08 D_20f08.
      stepST F_20f0c D_20f0c (Z_to_bv 64 (s - 40)) (Z_to_bv 64 pixt1) ltac:(sok_in SOK).
      sn F_20f10 D_20f10. sn F_20f14 D_20f14. sn F_20f18 D_20f18. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_C : forall regs m (s pixt2 : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 pixt2 ->
    exists regs',
      msteps SEGS (mkst regs (0x21018 : word) m rom) (mkst regs' (0x17a90 : word) (wbytes m (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixt2))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x21024 /\ getr regs' 10 = Z_to_bv 64 pixt2 /\ getr regs' 11 = Z_to_bv 64 32
      /\ regs_agree (fun r => In r [1; 11]%list) regs regs'.
  Proof.
    intros regs m s pixt2 Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_20f1c D_20f1c (Z_to_bv 64 (s - 48)) (Z_to_bv 64 pixt2) ltac:(sok_in SOK).
      sn F_20f20 D_20f20. sn F_20f24 D_20f24. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_D : forall regs m (s pixt3 : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 56)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 pixt3 ->
    exists regs',
      msteps SEGS (mkst regs (0x21024 : word) m rom) (mkst regs' (0x15fb4 : word) (wbytes m (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pixt3))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x21034 /\ getr regs' 10 = Z_to_bv 64 (s - 40) /\ getr regs' 9 = Z_to_bv 64 pixt3
      /\ regs_agree (fun r => In r [1; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pixt3 Hs Hs64 SOK H2 H10. eexists. split.
    - sn F_20f28 D_20f28.
      stepST F_20f2c D_20f2c (Z_to_bv 64 (s - 56)) (Z_to_bv 64 pixt3) ltac:(sok_in SOK).
      zv F_20f30 D_20f30 (Z_to_bv 64 (s - 40)). sn F_20f34 D_20f34. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_E : forall regs m (s : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x21034 : word) m rom) (mkst regs' (0x15fb4 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x2103c /\ getr regs' 10 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_20f38 D_20f38 (Z_to_bv 64 (s - 48)). sn F_20f3c D_20f3c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_F : forall regs r0 m (s pixt3 : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameD s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 pixt3 ->
    exists regs',
      msteps SEGS (mkst regs (0x2103c : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixt3
      /\ (forall x, In x [8; 9; 18]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18]%list) regs regs'.
  Proof.
    intros regs r0 m s pixt3 ret Hs Hs64 Hret CE H2 H8 H9. unfold frameD in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & _).
    eexists. split.
    - stepb_tk F_20f40 D_20f40 ltac:(condZ).
      sn F_20fc4 D_20fc4. sn F_20fc8 D_20fc8.
      stepLD8 F_20fcc D_20fcc ret. stepLD8 F_20fd0 D_20fd0 (getr r0 8). stepLD8 F_20fd4 D_20fd4 (getr r0 9). stepLD8 F_20fd8 D_20fd8 (getr r0 18).
      zv F_20fdc D_20fdc (Z_to_bv 64 s). stepret F_20fe0 D_20fe0 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pixDestroy_null : forall regs m (s pp : Z) (ret : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs', msteps SEGS (mkst regs (0x15fb4 : word) m rom)
      (mkst regs' ret (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                  (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9]%list) regs regs'.
  Proof.
    intros regs m s pp ret Hs Hpp Hpp64 Hret SOK Rpp H2 H1 H10. eexists. split.
    - zv F_15eb8 D_15eb8 (Z_to_bv 64 (s - 32)).
      stepST F_15ebc D_15ebc (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15ec0 D_15ec0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15ec4 D_15ec4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_15ec8 D_15ec8 ltac:(condZ).
      stepLD F_15ecc D_15ecc (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact Rpp) ltac:(apply W2Lib.lez8; lia).
      stepb_tk F_15ed0 D_15ed0 ltac:(condZ).
      stepLD8 F_15f70 D_15f70 ret. stepLD8 F_15f74 D_15f74 (getr regs 8). stepLD8 F_15f78 D_15f78 (getr regs 9).
      zv F_15f7c D_15f7c (Z_to_bv 64 s). stepret F_15f80 D_15f80 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsD.
End Fhmt.
