(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_RGl LbB_RGt LbB_RG2 LbB_RGb1 LbB_RGb2 LbB_RGb3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac subfp_solve :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [app outside] in Hx |- *;
  repeat match type of Hx with _ /\ _ => let N := fresh "N" in destruct Hx as [N Hx] end;
  repeat split; let K := fresh "K" in intro K;
  match goal with N : ~ _ |- _ => apply N; clear - K; lia end.

Lemma rg_cells_size : Z.of_nat (cells_size rg_cells) = 2504.
Proof. vm_compute. reflexivity. Qed.

Lemma rg_b2 : forall (x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (ff sph D N lo : Z),
  1 <= N <= 2 ^ 26 -> 1 <= D -> D + N <= 2 ^ 47 ->
  ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 128 <= 2 ^ 47 ->
  (ff + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
  sph mod 32 = 0 -> 2 ^ 45 <= sph <= 2 ^ 47 ->
  wr_at asegs m ff 128 -> wr_at asegs m (sh ff) 16 -> stk asegs m lo sph -> lo <= sph - 2592 -> ff + 128 <= lo ->
  mem_inv asegs m -> ACONST m ->
  exists R' M' (st : Z) (kk : nat),
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 CS_SM_RET2) (Z_to_bv 64 (sph - 2592)) x3 x4 x5 x6 x7 (Z_to_bv 64 (sph - 2528)) (Z_to_bv 64 (sph - 2592))
               (Z_to_bv 64 ff) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 N) (Z_to_bv 64 D) (Z_to_bv 64 0x7fff8000)
               x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 CS_SM_RET2) fc None m ro)
      (MS R' F (Z_to_bv 64 LH_HEAD) fc None M' ro)
    /\ 0 <= st /\ st + Z.of_nat (S kk) <= N /\ (Z.of_nat (S kk) <= 32)%Z
    /\ getr R' 19 = Z_to_bv 64 (D + st) /\ getr R' 15 = Z_to_bv 64 0 /\ getr R' 16 = Z_to_bv 64 (Z.of_nat (S kk))
    /\ getr R' 5 = Z_to_bv 64 (2 ^ 64 - 1 - (D + st))
    /\ getr R' 20 = Z_to_bv 64 0x7fff8000 /\ getr R' 10 = Z_to_bv 64 ff /\ getr R' 13 = Z_to_bv 64 (sh ff) /\ getr R' 14 = Z_to_bv 64 ff
    /\ getr R' 2 = Z_to_bv 64 (sph - 2592) /\ getr R' 3 = x3 /\ getr R' 4 = x4
    /\ getr R' 8 = Z_to_bv 64 (sph - 2528) /\ getr R' 9 = Z_to_bv 64 (sph - 2592)
    /\ getr R' 21 = x21 /\ getr R' 22 = x22 /\ getr R' 23 = x23 /\ getr R' 24 = x24 /\ getr R' 25 = x25 /\ getr R' 26 = x26 /\ getr R' 27 = x27
    /\ munch [(ff, ff + 72); (sh ff, sh ff + 12); (sph - 2584, sph - 2576)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
    /\ stk asegs M' lo sph.
Proof.
  intros until lo. intros HN HD0 HD1 F64 FLO FHI FB SP32 SPR WF WS ST LO FST MI AC.
  assert (NC : (1 <= N <= 3) \/ (4 <= N <= 8) \/ (9 <= N <= 36) \/ (37 <= N <= 2 ^ 26)) by lia.
  destruct NC as [NC | [NC | [NC | NC]]].
  - destruct (rg_b2_a x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ro ff sph D N lo
                 NC HD0 HD1 F64 FLO FHI FB SP32 SPR WF WS ST LO FST MI AC)
      as (R' & M' & RUN & G19 & G15 & G16 & G5 & G20 & G10 & G13 & G14 & G1 & G2 & G3 & G4 & G8 & G9 & G18
          & G21 & G22 & G23 & G24 & G25 & G26 & G27 & MU & WM & MI' & ST').
    exists R', M', 0, (Z.to_nat (N - 1)).
    split; [exact RUN|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact G19|]. split; [exact G15|]. split; [rewrite G16; first [reflexivity | f_equal; lia]|]. split; [exact G5|].
    repeat (split; [assumption|]). assumption.
  - destruct (rg_b2_b x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ro ff sph D N lo
                 NC HD0 HD1 F64 FLO FHI FB SP32 SPR WF WS ST LO FST MI AC)
      as (R' & M' & RUN & G19 & G15 & G16 & G5 & G20 & G10 & G13 & G14 & G1 & G2 & G3 & G4 & G8 & G9 & G18
          & G21 & G22 & G23 & G24 & G25 & G26 & G27 & MU & WM & MI' & ST').
    exists R', M', (N - 4), 3%nat.
    split; [exact RUN|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact G19|]. split; [exact G15|]. split; [rewrite G16; first [reflexivity | f_equal; lia]|]. split; [exact G5|].
    repeat (split; [assumption|]). assumption.
  - destruct (rg_b2_c x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ro ff sph D N lo
                 NC HD0 HD1 F64 FLO FHI FB SP32 SPR WF WS ST LO FST MI AC)
      as (R' & M' & RUN & G19 & G15 & G16 & G5 & G20 & G10 & G13 & G14 & G1 & G2 & G3 & G4 & G8 & G9 & G18
          & G21 & G22 & G23 & G24 & G25 & G26 & G27 & MU & WM & MI' & ST').
    exists R', M', 5, (Z.to_nat (N - 6)).
    split; [exact RUN|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact G19|]. split; [exact G15|]. split; [rewrite G16; first [reflexivity | f_equal; lia]|]. split; [exact G5|].
    repeat (split; [assumption|]). assumption.
  - destruct (rg_b2_d x3 x4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m ro ff sph D N lo
                 NC HD0 HD1 F64 FLO FHI FB SP32 SPR WF WS ST LO FST MI AC)
      as (R' & M' & RUN & G19 & G15 & G16 & G5 & G20 & G10 & G13 & G14 & G1 & G2 & G3 & G4 & G8 & G9 & G18
          & G21 & G22 & G23 & G24 & G25 & G26 & G27 & MU & WM & MI' & ST').
    exists R', M', 5, 31%nat.
    split; [exact RUN|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact G19|]. split; [exact G15|]. split; [rewrite G16; first [reflexivity | f_equal; lia]|]. split; [exact G5|].
    repeat (split; [assumption|]). assumption.
Qed.

Section RG.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Definition rgh_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LF : list fframe) (ff fp sph : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(ff, ff + 8); (sh ff, sh ff + 16); (fp, fp + 1); (sph - 2520, sph - 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ as_RFS H LF m'.

  Lemma rg_tail2 : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (LF : list fframe)
      (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (ff fp sph lo c : Z) (k : nat),
    rfull R ->
    getr R 19 = Z_to_bv 64 c -> getr R 15 = Z_to_bv 64 0 -> getr R 16 = Z_to_bv 64 (Z.of_nat (S k)) ->
    getr R 5 = Z_to_bv 64 (2 ^ 64 - 1 - c) ->
    getr R 20 = Z_to_bv 64 0x7fff8000 -> getr R 10 = Z_to_bv 64 ff -> getr R 13 = Z_to_bv 64 (sh ff) -> getr R 14 = Z_to_bv 64 ff ->
    getr R 2 = Z_to_bv 64 (sph - 2592) -> getr R 3 = gp -> getr R 4 = tp ->
    getr R 8 = Z_to_bv 64 (sph - 2528) -> getr R 9 = Z_to_bv 64 (sph - 2592) ->
    getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 25 = s9 -> getr R 26 = s10 -> getr R 27 = s11 ->
    (Z.of_nat (S k) <= 32)%Z -> 0 <= c -> c + Z.of_nat (S k) < 2 ^ 47 ->
    accessible m c (Z.of_nat (S k)) ->
    (forall j, 0 <= j < Z.of_nat (S k) -> exists z, 0 <= z < 256 /\ rdn asegs m (Z_to_bv 64 (c + j)) 1 = Some [Z_to_bv 8 z]) ->
    rw_cells asegs m (sph - 2576) [C8 s4; C8 s3; C8 s2; C8 s1; C8 (wz MT_FA); C8 (wz CS_RET_RA)] ->
    rw_cells asegs m (sph - 16) [C8 s0; C8 ra] ->
    rw_cells asegs m (ff + 120) [C8 (wz fp)] -> wr_at asegs m ff 8 -> wr_at asegs m (sh ff) 16 -> wr_at asegs m fp 1 ->
    as_RFS H ((1, ff, fp) :: LF) m ->
    stk asegs m lo sph -> aceil <= lo -> lo <= sph - 2592 -> sph mod 32 = 0 -> sph <= 2 ^ 47 ->
    mem_inv asegs m ->
    evt asegs (rgh_post ra (Z_to_bv 64 sph) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF ff fp sph m)
      (MS R F (Z_to_bv 64 LH_HEAD) fc None m (seg_rom asegs)).
  Proof.
    intros until k. intros HF H19 H15 H16 H5 H20 H10 H13 H14 H2 H3 H4 H8 H9 H21 H22 H23 H24 H25 H26 H27 Hk Hc0 Hc1 ACC BYT
      CSF CTF CFP WFF WSH WFP RF ST CE LO SP32 SP47 MI.
    assert (H16' : getr R 16 = Z_to_bv 64 (0 + Z.of_nat (S k))) by (rewrite H16; f_equal; lia).
    assert (ACC0 : accessible m (c + 0) (Z.of_nat (S k))) by (replace (c + 0) with c by lia; exact ACC).
    assert (BYT0 : forall t, 0 <= t < Z.of_nat (S k) -> exists z, 0 <= z < 256 /\ rdn asegs m (Z_to_bv 64 (c + 0 + t)) 1 = Some [Z_to_bv 8 z]).
    { intros t Ht. replace (c + 0 + t) with (c + t) by lia. exact (BYT t Ht). }
    destruct (lh_loop k R F fc m (seg_rom asegs) c 0 H19 H15 H16' H5 H20 Hc0 ltac:(lia) ltac:(lia) ACC0 BYT0)
      as (R1 & RUN & GK & G20 & G15).
    eapply evt_of_msteps; [exact RUN|].
    pose proof (msteps_full asegs _ _ RUN HF) as HF1. cbn [ms_regs] in HF1.
    rewrite (MS_full_eq R1 F (Z_to_bv 64 LH_EXIT) fc m (seg_rom asegs) HF1).
    rewrite (GK 2%bv ltac:(inb)), (GK 3%bv ltac:(inb)), (GK 4%bv ltac:(inb)), (GK 8%bv ltac:(inb)), (GK 9%bv ltac:(inb)),
            (GK 10%bv ltac:(inb)), (GK 13%bv ltac:(inb)), (GK 14%bv ltac:(inb)), G20,
            (GK 21%bv ltac:(inb)), (GK 22%bv ltac:(inb)), (GK 23%bv ltac:(inb)), (GK 24%bv ltac:(inb)), (GK 25%bv ltac:(inb)),
            (GK 26%bv ltac:(inb)), (GK 27%bv ltac:(inb)).
    rewrite H2, H3, H4, H8, H9, H10, H13, H14, H21, H22, H23, H24, H25, H26, H27.
    eapply evt_mono; [eapply (rgt_evt H HH) with (s0 := s0) (ra := ra); eassumption |].
    intros ms' POST. exact POST.
  Qed.

  Definition rg_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (obj sph lo : Z) (m : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (XS : list (Z * Z)),
      ms' = MS (mkR ra (Z_to_bv 64 sph) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ Forall (fs_scratch H LF) XS
      /\ munch ([(obj, obj + 2504); (sph - RG_STACK, sph)] ++ XS) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo sph /\ as_RFS H LF m' /\ ACONST m' /\ as_RHEAP H s LB m'
      /\ rw_cells asegs m' obj rg_cells.

  Lemma bytes_rdn : forall M A bs (j : nat), bytes_at asegs M A bs -> (j < length bs)%nat ->
    exists z, 0 <= z < 256 /\ rdn asegs M (Z_to_bv 64 (A + Z.of_nat j)) 1 = Some [Z_to_bv 8 z].
  Proof.
    intros M A bs j (B0 & B1 & B) Hj. specialize (B j Hj).
    destruct (nth_error bs j) as [b|] eqn:E; [| apply nth_error_None in E; lia].
    exists (bv_unsigned b). split; [pose proof (bv_unsigned_in_range 8 b) as R; change (bv_modulus 8) with 256 in R; lia|].
    rewrite <- rdn_HL. replace (Z_to_bv 8 (bv_unsigned b)) with b
      by (apply bv_eq; rewrite Z_to_bv_unsigned; rewrite bv_wrap_small; [reflexivity | apply bv_unsigned_in_range]).
    exact (rdn1_of_mrd asegs M _ b B).
  Qed.

  Definition rg_W02 (obj sph ff fp : Z) : list (Z * Z) :=
    [(obj, obj + 2504); (sph - 2592, sph); (sph - 2592 - 1024, sph - 2592); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1);
     (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)].
  Definition rg_W3 (sph ff : Z) : list (Z * Z) := [(ff, ff + 72); (sh ff, sh ff + 12); (sph - 2584, sph - 2576)].
  Definition rg_W4 (ff fp sph : Z) : list (Z * Z) := [(ff, ff + 8); (sh ff, sh ff + 16); (fp, fp + 1); (sph - 2520, sph - 24)].

  Lemma rg_data_windows : forall LF ff fp obj sph lo D N fo,
    fresh_frame H LF 1 ff fp -> aframe_range H (ff_class fo) (ff_addr fo) (ff_flag fo) ->
    ff_addr fo <= obj -> obj + 2504 <= ff_addr fo + fsz (ff_class fo) ->
    aceil <= lo -> lo <= sph - 3616 -> 2 ^ 45 <= sph -> ablock_range H D N ->
    disjoint_from (rg_W02 obj sph ff fp ++ rg_W3 sph ff) D N
    /\ (forall x, D <= x < D + N -> outside (rg_W02 obj sph ff fp ++ rg_W3 sph ff) (sh x)).
  Proof.
    intros LF ff fp obj sph lo D N fo FFR FAR FO1 FO2 CE LO SP BR.
    pose proof aceil_facts as ACF.
    pose proof (fresh_frame_facts H LF 1 ff fp FFR) as (K1 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
    destruct FAR as (FK & FA1 & FA2 & _ & _).
    pose proof (fsz_pos (ff_class fo) ltac:(lia)) as FSZ.
    destruct BR as (D0 & D16 & N0 & DI & DC & DF & DA).
    change (fsz 1) with 128 in *.
    unfold rg_W02, rg_W3. change (fshn 1) with 16. change (fsz 1) with 128.
    unfold AIMG_TOP, AFS_HDR, AFS_FLAGS, AFS_SIZE in P1, P2, P5, P7, P8, P9, P10, P11, P12, FA1, FA2, DI, DF.
    pose proof (aapp_disjoint_sh D N ff 128 DA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S1.
    unfold nsh in S1. change ((128 + 7) / 8) with 16 in S1.
    split.
    - cbn [app disjoint_from]. unfold AFS_FLAGS. repeat split; lia.
    - intros x Hx.
      pose proof (sh_in_shadowland x ltac:(unfold AAPP_HI; lia)) as SX.
      pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE x 1 P13 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S2.
      unfold nsh in S2. change ((1 + 7) / 8) with 1 in S2. unfold AFS_SIZE in S2.
      assert (S3 : sh x < sh ff \/ sh ff + 16 <= sh x).
      { clear - Hx DF P9 P10 P4. unfold sh. Z.div_mod_to_equations. lia. }
      cbn [app outside]. unfold AHI_LO, ALOWSH_LO, AFS_FLAGS in *. repeat split; lia.
  Qed.

  Lemma rg_obj_windows : forall LF ff fp obj sph lo fo,
    fresh_frame H LF 1 ff fp -> In fo LF -> aframe_range H (ff_class fo) (ff_addr fo) (ff_flag fo) ->
    ff_addr fo <= obj -> obj + 2504 <= ff_addr fo + fsz (ff_class fo) ->
    aceil <= lo -> lo <= sph - 3616 ->
    disjoint_from (rg_W3 sph ff ++ rg_W4 ff fp sph) obj 2504.
  Proof.
    intros LF ff fp obj sph lo fo FFR INF FAR FO1 FO2 CE LO.
    pose proof aceil_facts as ACF.
    pose proof (fresh_frame_facts H LF 1 ff fp FFR) as (K1 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
    destruct FFR as (_ & _ & FDJ). destruct (FDJ fo INF) as [FD _].
    destruct FAR as (FK & FA1 & FA2 & _ & _).
    pose proof (fsz_pos (ff_class fo) ltac:(lia)) as FSZ.
    change (fsz 1) with 128 in *.
    pose proof (aapp_sub (as_FSB H) AFS_SIZE obj 2504 P13 ltac:(unfold AFS_HDR in *; lia) ltac:(lia)) as OA.
    unfold AIMG_TOP, AFS_HDR, AFS_FLAGS, AFS_SIZE in P1, P2, P5, P7, P8, P9, P10, P11, P12, FA1, FA2.
    pose proof (aapp_disjoint_sh obj 2504 ff 128 OA ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S1.
    unfold nsh in S1. change ((128 + 7) / 8) with 16 in S1.
    unfold rg_W3, rg_W4. cbn [app disjoint_from]. repeat split; lia.
  Qed.

  Lemma rg_w34_ok : forall LB LF ff fp sph lo,
    fresh_frame H LF 1 ff fp -> aceil <= lo -> lo <= sph - 3616 ->
    Forall (aclient_write_ok H LB) (rg_W3 sph ff ++ rg_W4 ff fp sph) /\ Forall aconst_ok (rg_W3 sph ff ++ rg_W4 ff fp sph)
    /\ Forall (afs_write_ok H ((1, ff, fp) :: LF)) (rg_W3 sph ff).
  Proof.
    intros LB LF ff fp sph lo FFR CE LO.
    pose proof aceil_facts as ACF.
    pose proof (fresh_frame_facts H LF 1 ff fp FFR) as (K1 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
    change (fsz 1) with 128 in *.
    assert (SF1 : sh (as_FSB H) <= sh ff /\ sh ff + 16 <= sh (as_FSB H + AFS_SIZE)).
    { clear - P4 P9 P10. unfold sh, AFS_SIZE, AFS_HDR in *. Z.div_mod_to_equations. lia. }
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE ff 128 P13 ltac:(unfold AIMG_TOP, AFS_HDR in *; lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as SF4.
    unfold nsh in SF4. change ((128 + 7) / 8) with 16 in SF4.
    unfold AIMG_TOP, AFS_HDR, AFS_FLAGS, AFS_SIZE in P1, P2, P5, P7, P8, P9, P10, P11, P12, SF4.
    assert (SF2 : 0x800d5000 <= sh ff) by (clear - P1; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    assert (SHT : sh AIMG_TOP = 0x800d5000) by reflexivity.
    unfold rg_W3, rg_W4. cbn [app].
    split; [|split].
    - repeat apply Forall_cons; try apply Forall_nil.
      + right; right; right; right; left. cbn [fst snd]. unfold AFS_SIZE. lia.
      + right; right; right; right; right; left. cbn [fst snd]. lia.
      + left. cbn [fst]. lia.
      + right; right; right; right; left. cbn [fst snd]. unfold AFS_SIZE. lia.
      + right; right; right; right; right; left. cbn [fst snd]. lia.
      + right; right; right; right; left. cbn [fst snd]. unfold AFS_SIZE. lia.
      + left. cbn [fst]. lia.
    - repeat apply Forall_cons; try apply Forall_nil.
      + eapply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P13 | lia | unfold AFS_SIZE; lia].
      + apply aconst_ok_high; cbn [fst snd]; [rewrite SHT; lia | right; left; lia].
      + apply aconst_ok_high; cbn [fst snd]; [rewrite SHT; lia | right; left; lia].
      + eapply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P13 | lia | unfold AFS_SIZE; lia].
      + apply aconst_ok_high; cbn [fst snd]; [rewrite SHT; lia | right; left; lia].
      + eapply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact P13 | lia | unfold AFS_SIZE; lia].
      + apply aconst_ok_high; cbn [fst snd]; [rewrite SHT; lia | right; left; lia].
    - repeat apply Forall_cons; try apply Forall_nil.
      + right. exists (1, ff, fp). split; [left; reflexivity | cbn [ff_addr ff_class fst snd]; change (fsz 1) with 128; lia].
      + left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. split; lia.
      + left. cbn [fst snd]. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. split; lia.
  Qed.

  Lemma rg_fp_sub : forall obj sph ff fp,
    sub_fp (rg_W02 obj sph ff fp ++ (rg_W3 sph ff ++ rg_W4 ff fp sph))
           ([(obj, obj + 2504); (sph - RG_STACK, sph)] ++ [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)]).
  Proof.
    intros obj sph ff fp. unfold rg_W02, rg_W3, rg_W4, RG_STACK, AFS_STACK. change (fsz 1) with 128. change (fshn 1) with 16.
    subfp_solve.
  Qed.

  Lemma rg_after : forall (R2 : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m m2 M2 : mem) (s : as_St H) (LB : list block)
      (LF : list fframe) (pD : bptr) (obj D N sph lo st ff fp : Z) (kk : nat) (ds junk1 junk2 : list byte) (w : word)
      (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word),
    rfull R2 ->
    getr R2 19 = Z_to_bv 64 (D + st) -> getr R2 15 = Z_to_bv 64 0 -> getr R2 16 = Z_to_bv 64 (Z.of_nat (S kk)) ->
    getr R2 5 = Z_to_bv 64 (2 ^ 64 - 1 - (D + st)) ->
    getr R2 20 = Z_to_bv 64 0x7fff8000 -> getr R2 10 = Z_to_bv 64 ff -> getr R2 13 = Z_to_bv 64 (sh ff) -> getr R2 14 = Z_to_bv 64 ff ->
    getr R2 2 = Z_to_bv 64 (sph - 2592) -> getr R2 3 = gp -> getr R2 4 = tp ->
    getr R2 8 = Z_to_bv 64 (sph - 2528) -> getr R2 9 = Z_to_bv 64 (sph - 2592) ->
    getr R2 21 = s5 -> getr R2 22 = s6 -> getr R2 23 = s7 -> getr R2 24 = s8 -> getr R2 25 = s9 -> getr R2 26 = s10 -> getr R2 27 = s11 ->
    0 <= st -> st + Z.of_nat (S kk) <= N -> (Z.of_nat (S kk) <= 32)%Z ->
    munch [(ff, ff + 72); (sh ff, sh ff + 12); (sph - 2584, sph - 2576)] m2 M2 -> wmono asegs m2 M2 -> mem_inv asegs M2 -> stk asegs M2 lo sph ->
    munch [(obj, obj + 2504); (sph - 2592, sph); (sph - 2592 - 1024, sph - 2592); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1);
           (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] m m2 -> wmono asegs m m2 ->
    aceil <= lo -> lo <= sph - 3616 -> sph mod 32 = 0 -> 2 ^ 45 <= sph <= 2 ^ 47 ->
    as_RFS H ((1, ff, fp) :: LF) m2 -> fresh_frame H LF 1 ff fp ->
    rw_cells asegs m2 ff [CB 24 junk1; C8 w; CB (Z.to_nat (fsz 1 - 40)) junk2; C8 (Z_to_bv 64 fp)] ->
    SHAD m2 ff (poison_bytes (Z.to_nat (fshn 1)) 0) -> rw_cells asegs m2 fp [C1 (b8 1)] ->
    ACONST m2 -> as_RHEAP H s LB m2 -> rw_cells asegs m2 obj rg_cells ->
    rw_cells asegs m2 (sph - 2576) [C8 s4; C8 s3; C8 s2; C8 s1; C8 (wz MT_FA); C8 (wz CS_RET_RA)] ->
    rw_cells asegs m2 (sph - 16) [C8 s0; C8 ra] ->
    accessible m D N -> bytes_at asegs m D ds -> Z.of_nat (length ds) = N -> In (pD, D, N) LB ->
    (exists f, In f LF /\ ff_addr f <= obj /\ obj + 2504 <= ff_addr f + fsz (ff_class f)) ->
    evt asegs (rg_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF obj sph lo m)
      (MS R2 F (Z_to_bv 64 LH_HEAD) fc None M2 (seg_rom asegs)).
  Proof.
    intros until s11. intros HF H19 H15 H16 H5 H20 H10 H13 H14 H2 H3 H4 H8 H9 H21 H22 H23 H24 H25 H26 H27 Hst Hsk Hk
      MU3 WM3 MI3 ST3 MU02 WM02 CE LO SP32 SPR RF2 FFR CF2 SF2 FP2 AC2 RH2 CO2 CSF2 CTF2 ACC BY HLEN HDB OFS.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    destruct OFS as (fo & INF & FO1 & FO2).
    pose proof (proj2 (ah_RFS_range H HH _ _ RF2) fo (or_intror INF)) as FAR.
    pose proof (ah_blocks H HH _ _ _ _ RH2 HDB) as BR.
    assert (DB : 0 < D /\ D + N <= aceil) by (destruct BR as (? & _ & _ & _ & ? & _); split; assumption).
    destruct (rg_data_windows LF ff fp obj sph lo D N fo FFR FAR FO1 FO2 CE LO ltac:(lia) BR) as [DDJ DSH].
    pose proof (rg_obj_windows LF ff fp obj sph lo fo FFR INF FAR FO1 FO2 CE LO) as ODJ.
    destruct (rg_w34_ok LB LF ff fp sph lo FFR CE LO) as (WC & WK & WF).
    pose proof (fresh_frame_facts H LF 1 ff fp FFR) as (K1 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE ff 128 P13 ltac:(unfold AIMG_TOP, AFS_HDR in P1; lia) ltac:(change (fsz 1) with 128 in P2; unfold AAPP_HI; lia) ltac:(lia)) as SF4.
    unfold nsh in SF4. change ((128 + 7) / 8) with 16 in SF4.
    change (fsz 1) with 128 in P2, P10, CF2. change (fshn 1) with 16 in SF2.
    unfold AIMG_TOP, AFS_HDR, AFS_FLAGS, AFS_SIZE in P1, P2, P5, P7, P8, P9, P10, P11, P12, SF4.
    pose proof (sh_nsh_high ff 128 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as SHF. unfold nsh, AHI_LO in SHF.
    change ((128 + 7) / 8) with 16 in SHF.

    pose proof (munch_app _ _ _ _ _ MU02 MU3) as MU03.

    assert (ACC3 : accessible M2 D N) by (eapply accessible_transport; [exact ACC | exact MU03 | exact DSH]).
    assert (BY3 : bytes_at asegs M2 D ds) by (eapply bytes_at_transport; [exact BY | exact MU03 | rewrite HLEN; exact DDJ]).
    assert (CSF3 : rw_cells asegs M2 (sph - 2576) [C8 s4; C8 s3; C8 s2; C8 s1; C8 (wz MT_FA); C8 (wz CS_RET_RA)])
      by (eapply rw_cells_transport; [exact CSF2 | exact MU3 | exact WM3 | cbn; lia]).
    assert (CTF3 : rw_cells asegs M2 (sph - 16) [C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact CTF2 | exact MU3 | exact WM3 | cbn; lia]).
    assert (WFF2 : wr_at asegs m2 ff 128) by (eapply rw_cells_wr_at; [exact CF2 | cbn; lia]).
    assert (CFP3 : rw_cells asegs M2 (ff + 120) [C8 (wz fp)]).
    { change [CB 24 junk1; C8 w; CB (Z.to_nat (128 - 40)) junk2; C8 (Z_to_bv 64 fp)]
        with ([CB 24 junk1; C8 w; CB (Z.to_nat (128 - 40)) junk2] ++ [C8 (Z_to_bv 64 fp)]) in CF2.
      apply rw_cells_app in CF2. destruct CF2 as [_ CF].
      assert (E : Z.of_nat (cells_size [CB 24 junk1; C8 w; CB (Z.to_nat (128 - 40)) junk2]) = 120) by reflexivity.
      rewrite E in CF. eapply rw_cells_transport; [exact CF | exact MU3 | exact WM3 | cbn; lia]. }
    assert (WFF3 : wr_at asegs M2 ff 8).
    { eapply wr_at_transport; [| exact WM3]. destruct WFF2 as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi. apply W. lia. }
    assert (WSH3 : wr_at asegs M2 (sh ff) 16).
    { destruct SF2 as (_ & _ & (_ & W)).
      assert (L : Z.of_nat (length (poison_bytes (Z.to_nat 16) 0)) = 16) by reflexivity. rewrite L in W.
      eapply wr_at_transport; [exact W | exact WM3]. }
    assert (WFP3 : wr_at asegs M2 fp 1) by (eapply wr_at_transport; [eapply rw_cells_wr_at; [exact FP2 | cbn; lia] | exact WM3]).
    assert (RF3 : as_RFS H ((1, ff, fp) :: LF) M2) by (eapply (ah_RFS_frame H HH); [exact RF2 | exact MU3 | exact WM3 | exact WF]).

    eapply evt_mono.
    { eapply (rg_tail2 R2 F fc M2 LF ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ff fp sph lo (D + st) kk HF H19 H15 H16 H5 H20 H10 H13 H14
                H2 H3 H4 H8 H9 H21 H22 H23 H24 H25 H26 H27 Hk ltac:(lia) ltac:(lia)
                ltac:(eapply accessible_sub; [exact ACC3 | lia | lia | lia])).
      - intros j Hj. destruct (bytes_rdn M2 D ds (Z.to_nat (st + j)) BY3 ltac:(lia)) as (z & Z1 & Z2).
        exists z. split; [exact Z1|]. rewrite Z2Nat.id in Z2 by lia. replace (D + st + j) with (D + (st + j)) by lia. exact Z2.
      - exact CSF3.
      - exact CTF3.
      - exact CFP3.
      - exact WFF3.
      - exact WSH3.
      - exact WFP3.
      - exact RF3.
      - exact ST3.
      - exact CE.
      - lia.
      - exact SP32.
      - lia.
      - exact MI3. }
    intros ms' (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EQ & MU4 & WM4 & MI4 & RF4).
    pose proof (munch_app _ _ _ _ _ MU3 MU4) as MU34.
    pose proof (wmono_trans asegs _ _ _ WM3 WM4) as WM34.
    exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m',
      [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)].
    split; [exact EQ|].
    split; [exact (fs_scratch_of_fresh H LF 1 ff fp FFR)|].
    split; [eapply munch_weaken; [exact (rg_fp_sub obj sph ff fp) | exact (munch_app _ _ _ _ _ MU02 MU34)]|].
    split; [exact (wmono_trans asegs _ _ _ WM02 WM34)|].
    split; [exact MI4|].
    split; [eapply BakeStackRep.stk_high_transport; [exact ST3 | exact WM4 | unfold AIMG_TOP; lia]|].
    split; [exact RF4|].
    split; [eapply ACONST_frame; [exact AC2 | exact MU34 | exact WM34 | exact WK]|].
    split; [eapply (ah_RHEAP_frame H HH); [exact RH2 | exact MU34 | exact WM34 | exact WC]|].
    eapply rw_cells_transport; [exact CO2 | exact MU34 | exact WM34 | rewrite rg_cells_size; exact ODJ].
  Qed.

  Lemma rg_ctor_evt : forall (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe) (pD : bptr)
      (obj D N sph lo : Z) (ds : list byte),
    sph mod 32 = 0 -> 2 ^ 45 <= sph <= 2 ^ 47 ->

    wr_at asegs m obj 2504 -> SHAD m obj (repeat (b8 0) 313) -> obj mod 8 = 0 ->
    (exists f, In f LF /\ ff_addr f <= obj /\ obj + 2504 <= ff_addr f + fsz (ff_class f)) ->

    1 <= N < 2 ^ 26 -> In (pD, D, N) LB -> accessible m D N -> bytes_at asegs m D ds -> Z.of_nat (length ds) = N ->

    stk asegs m lo sph -> aceil <= lo -> lo <= sph - RG_STACK ->
    as_RFS H LF m -> (length LF < AFS_MAXLIVE)%nat -> as_RHEAP H s LB m ->
    mem_inv asegs m -> tp = Z_to_bv 64 ATP -> ACONST m ->
    evt asegs (rg_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF obj sph lo m)
      (MS (mkR ra (Z_to_bv 64 sph) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 obj) (Z_to_bv 64 D) (Z_to_bv 64 N) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RG_CTOR) fc None m (seg_rom asegs)).
  Proof.
    intros until ds. intros SP32 SPR OWR OSH O8 OFS HN HDB HACC HBY HLEN ST CE LO RF LFL RH MI TP AC.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4).
    destruct OFS as (fo & INF & FO1 & FO2).
    pose proof (FR fo INF) as (FK & FA1 & FA2 & (FA3 & _) & FA5).
    pose proof (fsz_pos (ff_class fo) ltac:(lia)) as FSZ.
    unfold AFS_HDR, AFS_SIZE, AFS_FLAGS in FA1, FA2, FA5. unfold AFS_SIZE in FS2, FS4. unfold AIMG_TOP in FS1.
    assert (OIN : as_FSB H + 0x9000 <= obj /\ obj + 2504 <= as_FSB H + 0xb09000) by lia.
    assert (OBD : oband obj 2504).
    { unfold oband. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in FS4. destruct FS4; [left | right]; lia. }
    pose proof (ah_blocks H HH _ _ _ _ RH HDB) as (D0 & D16 & Dn & DI & DC & DF & DAPP).
    unfold blk_addr, blk_size in D0, D16, Dn, DI, DC, DF, DAPP. cbn [fst snd] in D0, D16, Dn, DI, DC, DF, DAPP.
    unfold RG_STACK, AFS_STACK in LO.

    destruct (rg_b1 ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (seg_rom asegs) obj D N sph lo
                SP32 SPR OWR OSH O8 ltac:(unfold AIMG_TOP in DI; lia) ltac:(lia) OBD ltac:(unfold RG_STACK, AFS_STACK; lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ST CE ltac:(unfold RG_STACK, AFS_STACK; lia) MI AC)
      as (R1 & M1 & RUN1 & HR1 & MU1 & WM1 & MI1 & ST1 & CO1 & CSF1 & CTF1).
    eapply evt_of_msteps; [exact RUN1|]. rewrite HR1.

    assert (W1 : Forall (aclient_write_ok H LB) [(obj, obj + 2504); (sph - 2592, sph)]
               /\ Forall (afs_write_ok H LF) [(obj, obj + 2504); (sph - 2592, sph)]
               /\ Forall aconst_ok [(obj, obj + 2504); (sph - 2592, sph)]).
    { pose proof (stack_window_ok H LB LF (sph - 2592) sph) as SWa. destruct SWa as (SWa1 & SWa2 & SWa3); [lia | unfold AFS_SIZE; lia |].
      split; [apply Forall_cons; [right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE; lia | apply Forall_cons; [exact SWa1 | apply Forall_nil]]|].
      split; [apply Forall_cons; [right; exists fo; cbn [fst snd]; split; [exact INF | lia] | apply Forall_cons; [exact SWa2 | apply Forall_nil]]|].
      apply Forall_cons; [eapply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact FS4 | cbn; lia | cbn; unfold AFS_SIZE; lia] | apply Forall_cons; [exact SWa3 | apply Forall_nil]]. }
    destruct W1 as (W11 & W12 & W13).
    assert (RH1 : as_RHEAP H s LB M1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W11]).
    assert (RF1 : as_RFS H LF M1) by (eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W12]).
    assert (AC1 : ACONST M1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | exact W13]).
    pose proof (ah_thr H HH _ _ _ RH1) as ATH1.

    eapply evt_cut.
    { eapply (ah_fs1 H HH) with (LF := LF) (lo := lo); [exact RF1 | exact LFL | rewrite u64_of_Z by lia; exact (proj1 (stk_split asegs M1 lo (sph - 2592) sph ST1 ltac:(lia)))
        | exact CE | rewrite u64_of_Z by lia; unfold AFS_STACK; lia | exact MI1 | exact TP | exact AC1 | exact ATH1]. }
    intros ms2 POST2.
    destruct POST2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & ff & fp & junk1 & junk2
                       & EQ2 & MU2 & WM2 & MI2 & ST2 & RF2 & CF2 & SF2 & FP2 & AC2).
    subst ms2. rewrite u64_of_Z in MU2, ST2 by lia. unfold AFS_STACK in MU2.
    rewrite (ret_pc_even CS_SM_RET ltac:(unfold CS_SM_RET; lia) eq_refl).
    pose proof (fresh_of_RFS H HH LF 1 ff fp m2 RF2) as FFR.
    pose proof (fresh_frame_facts H LF 1 ff fp FFR) as (K1 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13).
    unfold AIMG_TOP, AFS_HDR, AFS_FLAGS, AFS_SIZE, fsz in P1, P2, P5, P7, P8, P9, P10, P11, P12. cbn in P2, P10.

    assert (SHF : sh ff + 16 <= 0x10007fff8000).
    { pose proof (sh_nsh_high ff 128 ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X. unfold nsh, AHI_LO in X.
      change ((128 + 7) / 8) with 16 in X. exact X. }
    assert (ST2f : stk asegs m2 lo sph).
    { destruct (stk_split asegs M1 lo (sph - 2592) sph ST1 ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 (sph - 2592) sph).
      { eapply stk_transport_disjoint; [exact STu | exact MU2 | exact WM2 | cbn; unfold AFS_FLAGS; change (fsz 1) with 128; change (fshn 1) with 16; lia]. }
      exact (stk_merge asegs m2 lo (sph - 2592) sph ST2 STu2 ltac:(lia)). }
    assert (RH2 : as_RHEAP H s LB m2).
    { eapply (ah_RHEAP_frame H HH); [exact RH1 | exact MU2 | exact WM2 |].
      assert (SF1 : sh (as_FSB H) <= sh ff /\ sh ff + 16 <= sh (as_FSB H + AFS_SIZE)).
      { clear - P4 P9 P10. unfold sh, AFS_SIZE in *. Z.div_mod_to_equations. lia. }
      repeat apply Forall_cons; try apply Forall_nil.
      - left. cbn [fst]. lia.
      - right; right; right; right; left. cbn [fst snd]. unfold AFS_SIZE, AFS_FLAGS. lia.
      - right; right; right; right; left. cbn [fst snd]. unfold AFS_SIZE. lia.
      - right; right; right; right; left. cbn [fst snd]. unfold AFS_SIZE. change (fsz 1) with 128. lia.
      - right; right; right; right; right; left. cbn [fst snd]. change (fshn 1) with 16. exact SF1. }
    assert (OAPP : aapp obj 2504) by (eapply aapp_sub; [exact FS4 | lia | lia]).
    assert (CO2 : rw_cells asegs m2 obj rg_cells).
    { eapply rw_cells_transport; [exact CO1 | exact MU2 | exact WM2 |]. rewrite rg_cells_size.
      eapply (fsobj_disjoint H HH LF obj 2504 1 ff fp M1 (sph - 2592 - 1024) (sph - 2592));
        [exact RF1 | exact (fsobj_inframe H LF fo obj 2504 INF FO1 FO2) | exact FFR | lia | lia | unfold AAPP_HI; lia | exact OAPP | left; lia]. }
    assert (CSF2 : rw_cells asegs m2 (sph - 2576) [C8 s4; C8 s3; C8 s2; C8 s1; C8 (wz MT_FA); C8 (wz CS_RET_RA)])
      by (eapply rw_cells_transport; [exact CSF1 | exact MU2 | exact WM2 | cbn; unfold AFS_FLAGS; change (fsz 1) with 128; change (fshn 1) with 16; lia]).
    assert (CTF2 : rw_cells asegs m2 (sph - 16) [C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact CTF1 | exact MU2 | exact WM2 | cbn; unfold AFS_FLAGS; change (fsz 1) with 128; change (fshn 1) with 16; lia]).
    assert (FBAND : ff + 128 <= 0x7fff7000 \/ 0x10007fff8000 <= ff).
    { clear - FS4 P9 P10. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in FS4. lia. }
    assert (WFF2 : wr_at asegs m2 ff 128) by (eapply rw_cells_wr_at; [exact CF2 | change (fsz 1) with 128; cbn; lia]).
    assert (WSH2 : wr_at asegs m2 (sh ff) 16).
    { destruct SF2 as (_ & _ & (_ & W)).
      assert (L : Z.of_nat (length (poison_bytes (Z.to_nat (fshn 1)) 0)) = 16) by reflexivity. rewrite L in W. exact W. }
    clear W11 W12 W13.

    destruct (rg_b2 gp tp u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2 (seg_rom asegs) ff sph D N lo
                ltac:(lia) ltac:(lia) ltac:(lia) P3 ltac:(lia) ltac:(lia) FBAND SP32 SPR WFF2 WSH2 ST2f ltac:(lia) ltac:(lia) MI2 AC2)
      as (R2 & M2 & st & kk & RUN2 & Hst & Hsk & Hk & G19 & G15 & G16 & G5 & G20 & G10 & G13 & G14 & G2 & G3 & G4 & G8 & G9
          & G21 & G22 & G23 & G24 & G25 & G26 & G27 & MU3 & WM3 & MI3 & ST3).
    eapply evt_of_msteps; [exact RUN2|].
    pose proof (msteps_full asegs _ _ RUN2 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as HF2.
    cbn [ms_regs] in HF2.
    exact (rg_after R2 F fc m m2 M2 s LB LF pD obj D N sph lo st ff fp kk ds junk1 junk2 (Z_to_bv 64 (sph - 2592))
             ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             HF2 G19 G15 G16 G5 G20 G10 G13 G14 G2 G3 G4 G8 G9 G21 G22 G23 G24 G25 G26 G27 Hst Hsk Hk
             MU3 WM3 MI3 ST3 (munch_app _ _ _ _ _ MU1 MU2) (wmono_trans asegs _ _ _ WM1 WM2)
             CE ltac:(lia) SP32 SPR RF2 FFR CF2 SF2 FP2 AC2 RH2 CO2 CSF2 CTF2 HACC HBY HLEN HDB
             (ex_intro _ fo (conj INF (conj FO1 FO2)))).
  Qed.
End RG.
