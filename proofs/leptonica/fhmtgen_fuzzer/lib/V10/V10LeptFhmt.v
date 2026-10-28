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
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 GrayACELib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10LeptStderr V10LeptBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL7a.
Import V10CL7a.V10LeptErr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10CL8a.
Import V10CL8a.V10LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10_code_fhH.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac guard8 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite EQ; reflexivity).
Ltac fixv' v tac := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => first [ constr_eq x v | replace x with v by (symmetry; tac) ] end.
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
(* [comment removed for export] *)
Ltac seqz0 F D := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
Ltac sltu0 F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
Ltac slti0 F D := sn F D; fixv' (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
Ltac snez1 F D := sn F D; fixv' (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
Ltac lit F D v := sn F D; fixv' (Z_to_bv 64 v) ltac:(apply bv_eq; reflexivity).
Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Definition PC_pixFHMTGen_1 : Z := 0x283dc.
Definition PC_pixHMTDwa_1 : Z := 0x282bc.
Definition A_SELNAMES : Z := 0x34e20.        (* [comment removed for export] *)

Section Fhmt.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition FRG (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
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
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)).
Definition frameG (s : Z) (ret : word) (r0 : bvmap 5 word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, getr r0 8); ((s - 24)%Z, getr r0 9); ((s - 32)%Z, getr r0 18); ((s - 40)%Z, getr r0 19); ((s - 48)%Z, getr r0 20);
   ((s - 56)%Z, getr r0 21); ((s - 64)%Z, getr r0 22); ((s - 72)%Z, getr r0 23); ((s - 80)%Z, getr r0 24); ((s - 88)%Z, getr r0 25)].

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
    zv F_282e0 D_282e0 (Z_to_bv 64 (s - 96));
    stepST F_282e4 D_282e4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
    stepST F_282e8 D_282e8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
    stepST F_282ec D_282ec (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
    stepST F_282f0 D_282f0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
    stepST F_282f4 D_282f4 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK);
    stepST F_282f8 D_282f8 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK);
    stepST F_282fc D_282fc (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK);
    stepST F_28300 D_28300 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK);
    stepST F_28304 D_28304 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK);
    stepST F_28308 D_28308 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK);
    stepST F_2830c D_2830c (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK);
    sn F_28310 D_28310.

  (* [comment removed for export] *)
  Lemma fg_A : forall regs m (s pixd0 pixs name : Z) (vs : pixv) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> p_d vs = 1%Z -> (pixs + 64 <= s - 96 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 name ->
    exists regs',
      msteps SEGS (mkst regs (0x283dc : word) m rom) (mkst regs' (0x32838 : word) (FRG m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x28440 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 0x34e20
      /\ getr regs' 8 = Z_to_bv 64 pixd0 /\ getr regs' 9 = Z_to_bv 64 pixs /\ getr regs' 18 = Z_to_bv 64 name /\ getr regs' 19 = Z_to_bv 64 0x34e20
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs'.
  Proof.
    intros regs m s pixd0 pixs name vs ret Hs Hs64 Hp AL8 PX Hd DJ SOK H2 H1 H10 H11 H12.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (PX1 : PIXat (FRG m s ret regs) pixs vs).
    { unfold FRG. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd.
    unfold FRG in *. eexists. split.
    - fg_prologue s ret regs SOK.
      stepb_ft F_28314 D_28314 ltac:(condZ).
      sn F_28318 D_28318. sn F_2831c D_2831c. sn F_28320 D_28320. sn F_28324 D_28324.
      stepb_ft F_170a8 D_170a8 ltac:(condZ).
      guard8 F_170ac D_170ac AL8. stepb_ft F_170b0 D_170b0 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_170b4 D_170b4 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite ?(v_lw_small 1) by lia.
      stepret F_170b8 D_170b8 (0x28424 : word) ltac:(bveq).
      sn F_28328 D_28328. stepb_ft F_2832c D_2832c ltac:(condZ).
      sn F_28330 D_28330. sn F_28334 D_28334. sn F_28338 D_28338. sn F_2833c D_2833c. sn F_28340 D_28340.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fg_N1 : forall regs m (s pixd0 : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd0 -> getr regs 11 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x283dc : word) m rom) (mkst regs' (0x284fc : word) (FRG m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 8 = Z_to_bv 64 pixd0
      /\ regs_agree (fun r => In r [2; 8]%list) regs regs'.
  Proof.
    intros regs m s pixd0 ret Hs Hs64 SOK H2 H1 H10 H11. unfold FRG. eexists. split.
    - fg_prologue s ret regs SOK.
      stepb_tk F_28314 D_28314 ltac:(condZ).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Ltac fg_restore r0 ret s :=
    stepLD8 F_28450 D_28450 ret; stepLD8 F_28454 D_28454 (getr r0 8); stepLD8 F_28458 D_28458 (getr r0 9);
    stepLD8 F_2845c D_2845c (getr r0 18); stepLD8 F_28460 D_28460 (getr r0 19); stepLD8 F_28464 D_28464 (getr r0 20);
    stepLD8 F_28468 D_28468 (getr r0 21); stepLD8 F_2846c D_2846c (getr r0 22); stepLD8 F_28470 D_28470 (getr r0 23);
    stepLD8 F_28474 D_28474 (getr r0 24); stepLD8 F_28478 D_28478 (getr r0 25); zv F_2847c D_2847c (Z_to_bv 64 s); sn F_28480 D_28480.

  (* [comment removed for export] *)
  Lemma fg_N2 : forall regs r0 m (s pixd0 : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x33d90) 8 = Some (Z_to_le_bytes 8 0x34e00) -> rdn SEGS m (Z_to_bv 64 0x34e00) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameG s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 8 = Z_to_bv 64 pixd0 ->
    exists regs',
      msteps SEGS (mkst regs (0x284fc : word) m rom) (mkst regs' (0x1586c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x108aa
      /\ getr regs' 12 = Z_to_bv 64 pixd0
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros regs r0 m s pixd0 ret Hs Hs64 Rg Rs CE H2 H8. unfold frameG in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & _).
    eexists. split.
    - sn F_28400 D_28400.
      stepLD F_28404 D_28404 (Z_to_le_bytes 8 0x34e00) (Z_to_bv 64 0x34e00) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_28408 D_28408 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_2840c D_2840c. stepb_ft F_28410 D_28410 ltac:(condZ).
      sn F_28414 D_28414. sn F_28418 D_28418. sn F_2841c D_2841c. sn F_28420 D_28420. sn F_28424 D_28424.
      sn F_2844c D_2844c.
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
      msteps SEGS (mkst regs (0x28440 : word) m rom) (mkst regs' (0x285cc : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_28344 D_28344 ltac:(condZ). sn F_28484 D_28484. sn F_28488 D_28488. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_0 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x28440 : word) m rom) (mkst regs (0x28444 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_28344 D_28344 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_1 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x34e20 ->
    exists regs',
      msteps SEGS (mkst regs (0x28444 : word) m rom) (mkst regs' (0x32838 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28450 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x34e20 + 80 * 1)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_28348 D_28348 (Z_to_bv 64 (0x34e20 + 80 * 1)). sn F_2834c D_2834c. sn F_28350 D_28350. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_1 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x28450 : word) m rom) (mkst regs' (0x285cc : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_28354 D_28354 ltac:(condZ). sn F_2848c D_2848c. sn F_28490 D_28490. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_1 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x28450 : word) m rom) (mkst regs (0x28454 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_28354 D_28354 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_2 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x34e20 ->
    exists regs',
      msteps SEGS (mkst regs (0x28454 : word) m rom) (mkst regs' (0x32838 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28460 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x34e20 + 80 * 2)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_28358 D_28358 (Z_to_bv 64 (0x34e20 + 80 * 2)). sn F_2835c D_2835c. sn F_28360 D_28360. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_2 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x28460 : word) m rom) (mkst regs' (0x285cc : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 2
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_28364 D_28364 ltac:(condZ). sn F_28494 D_28494. sn F_28498 D_28498. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_2 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x28460 : word) m rom) (mkst regs (0x28464 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_28364 D_28364 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_3 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x34e20 ->
    exists regs',
      msteps SEGS (mkst regs (0x28464 : word) m rom) (mkst regs' (0x32838 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28470 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x34e20 + 80 * 3)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_28368 D_28368 (Z_to_bv 64 (0x34e20 + 80 * 3)). sn F_2836c D_2836c. sn F_28370 D_28370. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_3 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x28470 : word) m rom) (mkst regs' (0x285cc : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 3
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_28374 D_28374 ltac:(condZ). sn F_2849c D_2849c. sn F_284a0 D_284a0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_3 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x28470 : word) m rom) (mkst regs (0x28474 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_28374 D_28374 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_4 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x34e20 ->
    exists regs',
      msteps SEGS (mkst regs (0x28474 : word) m rom) (mkst regs' (0x32838 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28480 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x34e20 + 80 * 4)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_28378 D_28378 (Z_to_bv 64 (0x34e20 + 80 * 4)). sn F_2837c D_2837c. sn F_28380 D_28380. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_4 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x28480 : word) m rom) (mkst regs' (0x285cc : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 4
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_28384 D_28384 ltac:(condZ). sn F_284a4 D_284a4. sn F_284a8 D_284a8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_4 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x28480 : word) m rom) (mkst regs (0x28484 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_28384 D_28384 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_5 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x34e20 ->
    exists regs',
      msteps SEGS (mkst regs (0x28484 : word) m rom) (mkst regs' (0x32838 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28490 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x34e20 + 80 * 5)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_28388 D_28388 (Z_to_bv 64 (0x34e20 + 80 * 5)). sn F_2838c D_2838c. sn F_28390 D_28390. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_5 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x28490 : word) m rom) (mkst regs' (0x285cc : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 5
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_28394 D_28394 ltac:(condZ). sn F_284ac D_284ac. sn F_284b0 D_284b0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_5 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x28490 : word) m rom) (mkst regs (0x28494 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_28394 D_28394 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_6 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x34e20 ->
    exists regs',
      msteps SEGS (mkst regs (0x28494 : word) m rom) (mkst regs' (0x32838 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x284a0 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x34e20 + 80 * 6)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_28398 D_28398 (Z_to_bv 64 (0x34e20 + 80 * 6)). sn F_2839c D_2839c. sn F_283a0 D_283a0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_6 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x284a0 : word) m rom) (mkst regs' (0x285cc : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 6
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_283a4 D_283a4 ltac:(condZ). sn F_284b4 D_284b4. sn F_284b8 D_284b8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_6 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x284a0 : word) m rom) (mkst regs (0x284a4 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_283a4 D_283a4 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_7 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x34e20 ->
    exists regs',
      msteps SEGS (mkst regs (0x284a4 : word) m rom) (mkst regs' (0x32838 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x284b0 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x34e20 + 80 * 7)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_283a8 D_283a8 (Z_to_bv 64 (0x34e20 + 80 * 7)). sn F_283ac D_283ac. sn F_283b0 D_283b0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_7 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x284b0 : word) m rom) (mkst regs' (0x285cc : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 7
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_283b4 D_283b4 ltac:(condZ). sn F_284bc D_284bc. sn F_284c0 D_284c0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_7 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x284b0 : word) m rom) (mkst regs (0x284b4 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_283b4 D_283b4 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_8 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x34e20 ->
    exists regs',
      msteps SEGS (mkst regs (0x284b4 : word) m rom) (mkst regs' (0x32838 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x284c0 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x34e20 + 80 * 8)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_283b8 D_283b8 (Z_to_bv 64 (0x34e20 + 80 * 8)). sn F_283bc D_283bc. sn F_283c0 D_283c0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_8 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x284c0 : word) m rom) (mkst regs' (0x285cc : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 8
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_283c4 D_283c4 ltac:(condZ). sn F_284c4 D_284c4. sn F_284c8 D_284c8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_miss_8 : forall regs m (z : Z),
    (- 256 < z < 256)%Z -> z <> 0%Z -> getr regs 10 = Z_to_bv 64 z ->
    msteps SEGS (mkst regs (0x284c0 : word) m rom) (mkst regs (0x284c4 : word) m rom).
  Proof.
    intros regs m z Hz Hnz H10.
    stepb_ft F_283c4 D_283c4 ltac:(pin; exact (c_eq_small_ne0 z Hz Hnz)).
    apply mst_refl.
  Qed.
  Lemma fg_call_9 : forall regs m (name : Z),
    getr regs 18 = Z_to_bv 64 name -> getr regs 19 = Z_to_bv 64 0x34e20 ->
    exists regs',
      msteps SEGS (mkst regs (0x284c4 : word) m rom) (mkst regs' (0x32838 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x284d0 /\ getr regs' 10 = Z_to_bv 64 name /\ getr regs' 11 = Z_to_bv 64 (0x34e20 + 80 * 9)
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m name H18 H19. eexists. split.
    - zv F_283c8 D_283c8 (Z_to_bv 64 (0x34e20 + 80 * 9)). sn F_283cc D_283cc. sn F_283d0 D_283d0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma fg_hit_9 : forall regs m,
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x284d0 : word) m rom) (mkst regs' (0x285cc : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 9
      /\ regs_agree (fun r => In r [18]%list) regs regs'.
  Proof.
    intros regs m H10. eexists. split.
    - stepb_tk F_283d4 D_283d4 ltac:(condZ). sn F_284cc D_284cc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fg_B : forall regs m (pixs : Z),
    getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x285cc : word) m rom) (mkst regs' (0x1623c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x285e8 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m pixs H8 H9. eexists. split.
    - stepb_tk F_284d0 D_284d0 ltac:(condZ). sn F_284e4 D_284e4. sn F_284e8 D_284e8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fg_F : forall regs r0 m (s : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x33d90) 8 = Some (Z_to_le_bytes 8 0x34e00) -> rdn SEGS m (Z_to_bv 64 0x34e00) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameG s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x285e8 : word) m rom) (mkst regs' (0x1586c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x1054a /\ getr regs' 11 = Z_to_bv 64 0x108aa
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros regs r0 m s ret Hs Hs64 Rg Rs CE H2 H10. unfold frameG in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & _).
    eexists. split.
    - sn F_284ec D_284ec. stepb_tk F_284f0 D_284f0 ltac:(condZ).
      sn F_28668 D_28668.
      stepLD F_2866c D_2866c (Z_to_le_bytes 8 0x34e00) (Z_to_bv 64 0x34e00) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_28670 D_28670 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_28674 D_28674. stepb_ft F_28678 D_28678 ltac:(condZ).
      sn F_2867c D_2867c. sn F_28680 D_28680. sn F_28684 D_28684. sn F_28688 D_28688. sn F_2868c D_2868c. sn F_28690 D_28690.
      fg_restore r0 ret s.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fg_C : forall regs m (pixs pixd index : Z) (vs vd : pixv),
    (1 <= pixs)%Z -> (1 <= pixd)%Z -> (pixs mod 8 = 0)%Z -> (pixd mod 8 = 0)%Z -> pixs <> pixd -> PIXat m pixs vs -> PIXat m pixd vd ->
    (65 <= p_w vs <= 20000)%Z -> (65 <= p_h vs <= 20000)%Z -> (1 <= p_wpl vs <= 627)%Z -> (1 <= p_wpl vd <= 627)%Z ->
    (1 <= p_data vs)%Z -> (1 <= p_data vd)%Z ->
    (p_data vs + 128 * p_wpl vs + 4 < 2 ^ 64)%Z -> (p_data vd + 128 * p_wpl vd + 4 < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 pixs -> getr regs 18 = Z_to_bv 64 index ->
    exists regs',
      msteps SEGS (mkst regs (0x285e8 : word) m rom) (mkst regs' (0x287f8 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x286ec /\ getr regs' 8 = Z_to_bv 64 pixd
      /\ getr regs' 10 = Z_to_bv 64 (p_data vd + 128 * p_wpl vd + 4) /\ getr regs' 11 = Z_to_bv 64 (p_w vs - 64) /\ getr regs' 12 = Z_to_bv 64 (p_h vs - 64)
      /\ getr regs' 13 = Z_to_bv 64 (p_wpl vd) /\ getr regs' 14 = Z_to_bv 64 (p_data vs + 128 * p_wpl vs + 4) /\ getr regs' 15 = Z_to_bv 64 (p_wpl vs)
      /\ getr regs' 16 = Z_to_bv 64 index
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 14; 15; 16; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros regs m pixs pixd index vs vd Hps Hpd ALs ALd NE PXs PXd Hw Hh Hwpls Hwpld Hds1 Hdd1 Hds Hdd H10 H9 H18.
    pose proof PXs as (Hs0 & Hs64 & WFs & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    pose proof (wf_data _ WFs) as Rds. pose proof (wf_data _ WFd) as Rdd.
    pose proof (PIX_rd_wpl SEGS _ _ _ PXs) as Cwpls. pose proof (PIX_rd_wpl SEGS _ _ _ PXd) as Cwpld.
    pose proof (PIX_rd_w SEGS _ _ _ PXs) as Cw. pose proof (PIX_rd_h SEGS _ _ _ PXs) as Ch.
    pose proof (PIX_rd_data SEGS _ _ _ PXs) as Cds. pose proof (PIX_rd_data SEGS _ _ _ PXd) as Cdd.
    eexists. split.
    - sn F_284ec D_284ec. stepb_ft F_284f0 D_284f0 ltac:(condZ).
      sn F_284f4 D_284f4. sn F_284f8 D_284f8.
      stepb_ft F_16014 D_16014 ltac:(condZ). guard8 F_16018 D_16018 ALs. stepb_ft F_1601c D_1601c ltac:(condZ).
      stepLD F_16020 D_16020 (Z_to_le_bytes 4 (p_wpl vs)) (Z_to_bv 64 (p_wpl vs)) ltac:(addr_norm; exact Cwpls) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl vs)) by lia.
      stepret F_16024 D_16024 (0x285f8 : word) ltac:(bveq).
      sn F_284fc D_284fc. sn F_28500 D_28500. sn F_28504 D_28504.
      stepb_ft F_16014 D_16014 ltac:(condZ). guard8 F_16018 D_16018 ALd. stepb_ft F_1601c D_1601c ltac:(condZ).
      stepLD F_16020 D_16020 (Z_to_le_bytes 4 (p_wpl vd)) (Z_to_bv 64 (p_wpl vd)) ltac:(addr_norm; exact Cwpld) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_wpl vd)) by lia.
      stepret F_16024 D_16024 (0x28604 : word) ltac:(bveq).
      sn F_28508 D_28508. sn F_2850c D_2850c. sn F_28510 D_28510.
      stepb_ft F_17218 D_17218 ltac:(condZ). guard8 F_1721c D_1721c ALs. stepb_ft F_17220 D_17220 ltac:(condZ).
      stepLD F_17224 D_17224 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Cw) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepret F_17228 D_17228 (0x28610 : word) ltac:(bveq).
      sn F_28514 D_28514. fixv (Z_to_bv 64 (p_w vs - 64)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      stepb_ft F_28518 D_28518 ltac:(condZ).                (* [comment removed for export] *)
      sn F_2851c D_2851c. sn F_28520 D_28520.
      stepb_ft F_16dbc D_16dbc ltac:(condZ). guard8 F_16dc0 D_16dc0 ALs. stepb_ft F_16dc4 D_16dc4 ltac:(condZ).
      stepLD F_16dc8 D_16dc8 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; exact Ch) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepret F_16dcc D_16dcc (0x28620 : word) ltac:(bveq).
      sn F_28524 D_28524. fixv (Z_to_bv 64 (p_h vs - 64)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      stepb_ft F_28528 D_28528 ltac:(condZ).                (* [comment removed for export] *)
      sn F_2852c D_2852c. sn F_28530 D_28530.
      stepb_ft F_17180 D_17180 ltac:(condZ). guard8 F_17184 D_17184 ALs. stepb_ft F_17188 D_17188 ltac:(condZ).
      stepLD F_1718c D_1718c (Z_to_le_bytes 8 (p_data vs)) (Z_to_bv 64 (p_data vs)) ltac:(addr_norm; exact Cds) ltac:(apply lez8; lia).
      stepret F_17190 D_17190 (0x28630 : word) ltac:(bveq).
      (* [comment removed for export] *)
      lit F_28534 D_28534 67108864%Z.                       (* [comment removed for export] *)
      zv F_28538 D_28538 (Z_to_bv 64 (p_wpl vs + 67108864)).
      sn F_2853c D_2853c. fixv' (Z_to_bv 64 0) ltac:(rewrite zbv_srliw_small by lia; f_equal; change (2 ^ 27)%Z with 134217728%Z; apply Z.div_small; lia).
      stepb_ft F_28540 D_28540 ltac:(condZ).                (* [comment removed for export] *)
      sn F_28544 D_28544. fixv (Z_to_bv 64 (32 * p_wpl vs)) ltac:(rewrite v_slliw_5, sw32_small by lia; f_equal; lia).
      stepiv F_28548 D_28548 (Z_to_bv 64 (128 * p_wpl vs)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_2854c D_2854c (Z_to_bv 64 (p_data vs + 128 * p_wpl vs)).
      snez1 F_28550 D_28550. seqz0 F_28554 D_28554.
      stepb_ft F_28558 D_28558 ltac:(condR).                (* [comment removed for export] *)
      sltu0 F_2855c D_2855c. slti0 F_28560 D_28560. sn F_28564 D_28564. sn F_28568 D_28568.
      stepb_ft F_2856c D_2856c ltac:(condR).                (* [comment removed for export] *)
      stepb_ft F_28570 D_28570 ltac:(condZ).                (* [comment removed for export] *)
      lit F_28574 D_28574 18446744073709551611%Z.           (* [comment removed for export] *)
      stepb_ft F_28578 D_28578 ltac:(condZ).                (* [comment removed for export] *)
      sn F_2857c D_2857c. sn F_28580 D_28580.
      stepb_ft F_17180 D_17180 ltac:(condZ). guard8 F_17184 D_17184 ALd. stepb_ft F_17188 D_17188 ltac:(condZ).
      stepLD F_1718c D_1718c (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdd) ltac:(apply lez8; lia).
      stepret F_17190 D_17190 (0x28680 : word) ltac:(bveq).
      lit F_28584 D_28584 67108864%Z.
      zv F_28588 D_28588 (Z_to_bv 64 (p_wpl vd + 67108864)).
      sn F_2858c D_2858c. fixv' (Z_to_bv 64 0) ltac:(rewrite zbv_srliw_small by lia; f_equal; change (2 ^ 27)%Z with 134217728%Z; apply Z.div_small; lia).
      stepb_ft F_28590 D_28590 ltac:(condZ).
      sn F_28594 D_28594. fixv (Z_to_bv 64 (32 * p_wpl vd)) ltac:(rewrite v_slliw_5, sw32_small by lia; f_equal; lia).
      stepiv F_28598 D_28598 (Z_to_bv 64 (128 * p_wpl vd)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_2859c D_2859c (Z_to_bv 64 (p_data vd + 128 * p_wpl vd)).
      snez1 F_285a0 D_285a0. seqz0 F_285a4 D_285a4.
      stepb_ft F_285a8 D_285a8 ltac:(condR).
      sltu0 F_285ac D_285ac. slti0 F_285b0 D_285b0. sn F_285b4 D_285b4. sn F_285b8 D_285b8.
      stepb_ft F_285bc D_285bc ltac:(condR).
      stepb_ft F_285c0 D_285c0 ltac:(condZ).
      lit F_285c4 D_285c4 18446744073709551611%Z.
      stepb_ft F_285c8 D_285c8 ltac:(condZ).
      zv F_285cc D_285cc (Z_to_bv 64 (p_data vd + 128 * p_wpl vd + 4)).
      stepb_ft F_285d0 D_285d0 ltac:(condZ).
      zv F_285d4 D_285d4 (Z_to_bv 64 (p_data vs + 128 * p_wpl vs + 4)).
      sn F_285d8 D_285d8. sn F_285dc D_285dc. sn F_285e0 D_285e0. sn F_285e4 D_285e4. sn F_285e8 D_285e8. sn F_285ec D_285ec.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  (* [comment removed for export] *)
  Lemma fg_D : forall regs r0 m (s pixd : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameG s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 8 = Z_to_bv 64 pixd ->
    exists regs',
      msteps SEGS (mkst regs (0x286ec : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros regs r0 m s pixd ret Hs Hs64 Hret CE H2 H8. unfold frameG in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & _).
    eexists. split.
    - sn F_285f0 D_285f0. sn F_286c0 D_286c0.
      stepLD8 F_286c4 D_286c4 ret. stepLD8 F_286c8 D_286c8 (getr r0 8). stepLD8 F_286cc D_286cc (getr r0 9).
      stepLD8 F_286d0 D_286d0 (getr r0 18). stepLD8 F_286d4 D_286d4 (getr r0 19). stepLD8 F_286d8 D_286d8 (getr r0 20).
      stepLD8 F_286dc D_286dc (getr r0 21). stepLD8 F_286e0 D_286e0 (getr r0 22). stepLD8 F_286e4 D_286e4 (getr r0 23).
      stepLD8 F_286e8 D_286e8 (getr r0 24). stepLD8 F_286ec D_286ec (getr r0 25). zv F_286f0 D_286f0 (Z_to_bv 64 s). stepret F_286f4 D_286f4 ret ltac:(bveq).
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
    zv F_281c0 D_281c0 (Z_to_bv 64 (s - 64));
    stepST F_281c4 D_281c4 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK);
    stepST F_281c8 D_281c8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK);
    stepST F_281cc D_281cc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK);
    stepST F_281d0 D_281d0 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK);
    sn F_281d4 D_281d4.

  (* [comment removed for export] *)
  Lemma hd_A0 : forall regs m (s pixd0 pixs name : Z) (vs : pixv) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> (pixs + 64 <= s - 64 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixd0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 12 = Z_to_bv 64 name ->
    exists regs',
      msteps SEGS (mkst regs (0x282bc : word) m rom) (mkst regs' (0x282e8 : word) (FRD m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 10 = Z_to_bv 64 (p_d vs)
      /\ getr regs' 8 = Z_to_bv 64 pixd0 /\ getr regs' 18 = Z_to_bv 64 pixs /\ getr regs' 9 = Z_to_bv 64 name
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pixd0 pixs name vs ret Hs Hs64 Hp AL8 PX DJ SOK H2 H1 H10 H11 H12.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_d _ WF) as Rd.
    assert (PX1 : PIXat (FRD m s ret regs) pixs vs).
    { unfold FRD. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd.
    unfold FRD in *. eexists. split.
    - hd_prologue s ret regs SOK.
      stepb_ft F_281d8 D_281d8 ltac:(condZ).
      sn F_281dc D_281dc. sn F_281e0 D_281e0. sn F_281e4 D_281e4. sn F_281e8 D_281e8.
      stepb_ft F_170a8 D_170a8 ltac:(condZ).
      guard8 F_170ac D_170ac AL8. stepb_ft F_170b0 D_170b0 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_170b4 D_170b4 (Z_to_le_bytes 4 (p_d vs)) (Z_to_bv 64 (p_d vs)) ltac:(addr_norm; exact Cd) ltac:(apply lez4; lia).
      rewrite (v_lw_small (p_d vs)) by lia.
      stepret F_170b8 D_170b8 (0x282e8 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_A1 : forall regs m (pixs : Z),
    getr regs 10 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x282e8 : word) m rom) (mkst regs' (0x17f64 : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28300 /\ getr regs' 10 = Z_to_bv 64 pixs /\ getr regs' 11 = Z_to_bv 64 32 /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m pixs H10 H18. eexists. split.
    - sn F_281ec D_281ec. stepb_ft F_281f0 D_281f0 ltac:(condZ).
      sn F_281f4 D_281f4. sn F_281f8 D_281f8. sn F_281fc D_281fc. sn F_28200 D_28200. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Ltac hd_exit r0 ret s :=
    sn F_282a4 D_282a4;
    stepLD8 F_282a8 D_282a8 ret; stepLD8 F_282ac D_282ac (getr r0 8); stepLD8 F_282b0 D_282b0 (getr r0 9); stepLD8 F_282b4 D_282b4 (getr r0 18);
    zv F_282b8 D_282b8 (Z_to_bv 64 s); sn F_282bc D_282bc.

  (* [comment removed for export] *)
  Lemma hd_AD : forall regs r0 m (s d pixd0 : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 32)%Z -> d <> 1%Z ->
    rdn SEGS m (Z_to_bv 64 0x33d90) 8 = Some (Z_to_le_bytes 8 0x34e00) -> rdn SEGS m (Z_to_bv 64 0x34e00) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameD s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 d -> getr regs 8 = Z_to_bv 64 pixd0 ->
    exists regs',
      msteps SEGS (mkst regs (0x282e8 : word) m rom) (mkst regs' (0x1586c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x11035 /\ getr regs' 11 = Z_to_bv 64 0x10728
      /\ getr regs' 12 = Z_to_bv 64 pixd0
      /\ (forall x, In x [8; 9; 18]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18]%list) regs regs'.
  Proof.
    intros regs r0 m s d pixd0 ret Hs Hs64 Hd Hd1 Rg Rs CE H2 H10 H8. unfold frameD in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & _).
    eexists. split.
    - sn F_281ec D_281ec. stepb_tk F_281f0 D_281f0 ltac:(condZ).
      sn F_28280 D_28280.
      stepLD F_28284 D_28284 (Z_to_le_bytes 8 0x34e00) (Z_to_bv 64 0x34e00) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_28288 D_28288 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_2828c D_2828c. stepb_ft F_28290 D_28290 ltac:(condZ).
      sn F_28294 D_28294. sn F_28298 D_28298. sn F_2829c D_2829c. sn F_282a0 D_282a0.
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
      msteps SEGS (mkst regs (0x282bc : word) m rom) (mkst regs' (0x28354 : word) (FRD m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 8 = Z_to_bv 64 pixd0
      /\ regs_agree (fun r => In r [2; 8]%list) regs regs'.
  Proof.
    intros regs m s pixd0 ret Hs Hs64 SOK H2 H1 H10 H11. unfold FRD. eexists. split.
    - hd_prologue s ret regs SOK. stepb_tk F_281d8 D_281d8 ltac:(condZ). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
  Lemma hd_N2 : forall regs r0 m (s pixd0 : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x33d90) 8 = Some (Z_to_le_bytes 8 0x34e00) -> rdn SEGS m (Z_to_bv 64 0x34e00) 4 = Some (Z_to_le_bytes 4 3) ->
    cellsZ m (frameD s ret r0) -> getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 8 = Z_to_bv 64 pixd0 ->
    exists regs',
      msteps SEGS (mkst regs (0x28354 : word) m rom) (mkst regs' (0x1586c : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10728
      /\ getr regs' 12 = Z_to_bv 64 pixd0
      /\ (forall x, In x [8; 9; 18]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18]%list) regs regs'.
  Proof.
    intros regs r0 m s pixd0 ret Hs Hs64 Rg Rs CE H2 H8. unfold frameD in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & _).
    eexists. split.
    - sn F_28258 D_28258.
      stepLD F_2825c D_2825c (Z_to_le_bytes 8 0x34e00) (Z_to_bv 64 0x34e00) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_28260 D_28260 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
      sn F_28264 D_28264. stepb_ft F_28268 D_28268 ltac:(condZ).
      sn F_2826c D_2826c. sn F_28270 D_28270. sn F_28274 D_28274. sn F_28278 D_28278. sn F_2827c D_2827c.
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
      msteps SEGS (mkst regs (0x28300 : word) m rom) (mkst regs' (0x283dc : word) (wbytes m (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 pixt1))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28314 /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixt1 /\ getr regs' 12 = Z_to_bv 64 name
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixt1 name Hs Hs64 SOK H2 H10 H9. eexists. split.
    - sn F_28204 D_28204.
      stepST F_28208 D_28208 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 pixt1) ltac:(sok_in SOK).
      sn F_2820c D_2820c. sn F_28210 D_28210. sn F_28214 D_28214. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_C : forall regs m (s pixt2 : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 pixt2 ->
    exists regs',
      msteps SEGS (mkst regs (0x28314 : word) m rom) (mkst regs' (0x182b4 : word) (wbytes m (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixt2))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28320 /\ getr regs' 10 = Z_to_bv 64 pixt2 /\ getr regs' 11 = Z_to_bv 64 32
      /\ regs_agree (fun r => In r [1; 11]%list) regs regs'.
  Proof.
    intros regs m s pixt2 Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_28218 D_28218 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 pixt2) ltac:(sok_in SOK).
      sn F_2821c D_2821c. sn F_28220 D_28220. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_D : forall regs m (s pixt3 : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 56)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 pixt3 ->
    exists regs',
      msteps SEGS (mkst regs (0x28320 : word) m rom) (mkst regs' (0x1615c : word) (wbytes m (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (Z_to_bv 64 pixt3))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28330 /\ getr regs' 10 = Z_to_bv 64 (s - 40) /\ getr regs' 9 = Z_to_bv 64 pixt3
      /\ regs_agree (fun r => In r [1; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pixt3 Hs Hs64 SOK H2 H10. eexists. split.
    - sn F_28224 D_28224.
      stepST F_28228 D_28228 (Z_to_bv 64 (s - 56)) (Z_to_bv 64 pixt3) ltac:(sok_in SOK).
      zv F_2822c D_2822c (Z_to_bv 64 (s - 40)). sn F_28230 D_28230. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_E : forall regs m (s : Z),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x28330 : word) m rom) (mkst regs' (0x1615c : word) m rom)
      /\ getr regs' 1 = Z_to_bv 64 0x28338 /\ getr regs' 10 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_28234 D_28234 (Z_to_bv 64 (s - 48)). sn F_28238 D_28238. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma hd_F : forall regs r0 m (s pixt3 : Z) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cellsZ m (frameD s ret r0) ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 pixt3 ->
    exists regs',
      msteps SEGS (mkst regs (0x28338 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pixt3
      /\ (forall x, In x [8; 9; 18]%bv -> getr regs' x = getr r0 x)
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18]%list) regs regs'.
  Proof.
    intros regs r0 m s pixt3 ret Hs Hs64 Hret CE H2 H8 H9. unfold frameD in CE. cbn [cellsZ] in CE.
    destruct CE as (C1 & C2 & C3 & C4 & _).
    eexists. split.
    - stepb_tk F_2823c D_2823c ltac:(condZ).
      sn F_282c0 D_282c0. sn F_282c4 D_282c4.
      stepLD8 F_282c8 D_282c8 ret. stepLD8 F_282cc D_282cc (getr r0 8). stepLD8 F_282d0 D_282d0 (getr r0 9). stepLD8 F_282d4 D_282d4 (getr r0 18).
      zv F_282d8 D_282d8 (Z_to_bv 64 s). stepret F_282dc D_282dc ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity.
      + intros x Hx. cbn [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pixDestroy_null : forall regs m (s pp : Z) (ret : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pp mod 8 = 0)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs', msteps SEGS (mkst regs (0x1615c : word) m rom)
      (mkst regs' ret (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                  (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11]%list) regs regs'.
  Proof.
    intros regs m s pp ret Hs Hpp Hpp64 ALpp Hret SOK Rpp H2 H1 H10. eexists. split.
    - zv F_16060 D_16060 (Z_to_bv 64 (s - 32)).
      stepST F_16064 D_16064 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_16068 D_16068 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1606c D_1606c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_16070 D_16070 ltac:(condZ).
      guard8 F_16074 D_16074 ALpp. stepb_ft F_16078 D_16078 ltac:(condZ).   (* [comment removed for export] *)
      stepLD F_1607c D_1607c (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact Rpp) ltac:(apply W2Lib.lez8; lia).
      stepb_tk F_16080 D_16080 ltac:(condZ).
      stepLD8 F_16128 D_16128 ret. stepLD8 F_1612c D_1612c (getr regs 8). stepLD8 F_16130 D_16130 (getr regs 9).
      zv F_16134 D_16134 (Z_to_bv 64 s). stepret F_16138 D_16138 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsD.
End Fhmt.
