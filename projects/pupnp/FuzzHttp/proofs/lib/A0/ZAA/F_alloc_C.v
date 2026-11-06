(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim APrimLem AFrame ATacA ACells LJ LJU PEnv ATacFix F_poison F_memset F_gct F_prim_L0 F_hooks F_depot F_depot_C AQuarS F_alloc_env F_alloc_A F_alloc_B.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section MSTEP.
  Context {HC : HasCeiling}.

  Definition mstep (W : list (Z * Z)) (m m' : mem) : Prop := munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'.
End MSTEP.

Section BACK1.
  Context {HC : HasCeiling}.
  Variable D : dlayout.
  Variables (gp t2 s0 s6 t3 t4 t5 t6 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (SP lo B M rz size needed n THR CTX STK TR total : Z) (m : mem) (hs : list Z) (ws : list word) (tr : list Z).
  Hypothesis DLO : dl_ok D.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= SP - 224.
  Hypothesis SPR : SP mod 16 = 0 /\ SP + 128 <= 2^47.
  Hypothesis THRR : 0 < THR < 2^64.
  Hypothesis BR : 0 <= B /\ B mod 8 = 0 /\ B + needed <= 2^47.
  Hypothesis RZ : 16 <= rz <= 2048 /\ rz mod 16 = 0.
  Hypothesis SZ : 1 <= size <= 2^28 /\ rz + size <= needed /\ 0 <= n <= 2^28.
  Hypothesis HM : M = B + rz - 16.

  Hypothesis MDJ : 6328320 <= M /\ M + 16 <= lo /\ (M + 16 <= DN0 D \/ DN0 D + 2^20 <= M) /\ (M + 16 <= SS0 D \/ SS0 D + SWIN D <= M).

  Notation Wd := [(SP - 224, SP); (DT + 4 * bkt (depot_hash tr), DT + 4 * bkt (depot_hash tr) + 4); (DNI, DNI + 4);
                  (DN0 D + 16 * (zlen hs + 1), DN0 D + 16 * (zlen hs + 1) + 16); (SSA, SSA + 8); (SSD + 8, SSD + 12);
                  (SS0 D + 8 * total, SS0 D + 8 * total + 8 + 8 * Z.of_nat (length tr))].

  Definition back1_post (b0 : byte) : machine_state -> Prop :=
    fun ms' => exists ra' t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s8 m4 mD m' hs' total' (bits : byte) actx,
      ms' = MS (mkR ra' (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz B) (wz needed) (wz (M + 16)) (wz M) s6 (wz STK) s8 (wz (M + 16 + size)) (wz THR) (wz 1) t3 t4 t5 t6)
               F_ (wz 0x33a14) fc None m' (seg_rom asegs)
      /\ mstep [(M, M + 8)] m m4 /\ mstep Wd m4 mD /\ mstep [(M + 8, M + 16)] mD m'
      /\ stk asegs m' lo SP /\ RDEPOT D hs' total' m'
      /\ ((dfind hs (depot_hash tr) <> 0 /\ hs' = hs /\ total' = total)
          \/ (dfind hs (depot_hash tr) = 0 /\ hs' = hs ++ [depot_hash tr] /\ total' = total + Z.of_nat (length tr) + 1))
      /\ Z.land (bv_unsigned bits) 3 = 1
      /\ rw_cells asegs m' M [C1 b0; C1 bits; C2 (wz 0); C4 (wz size)] /\ rw_cells asegs m' (M + 8) [C8 actx].

  #[using="HC DLO CLO LOQ SPR THRR BR RZ SZ HM MDJ"] Lemma back1_spec : forall (ra t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 tid : word) (b0 b1 : byte) (j2 j4 j8 : list byte),
    mem_inv asegs m -> stk asegs m lo SP ->
    rw_cells asegs m (SP + 16) [C8 (wz 16)] ->
    rw_cells asegs m M [C1 b0; C1 b1; CB 2 j2; CB 4 j4] -> rw_cells asegs m (M + 8) [CB 8 j8] ->
    rw_cells asegs m THR [C8 (wz CTX)] -> rw_cells asegs m (CTX + 8) [C4 tid] ->
    rw_cells asegs m STK [C8 (wz TR); C8 (wz (Z.of_nat (length tr)))] ->
    RDEPOT D hs total m -> u64arr asegs m TR ws -> firstn (length tr) ws = map wz tr -> (length tr <= length ws)%nat -> (1 <= length tr <= 30)%nat ->
    Forall (fun x => 0 <= x < 2^64) tr -> SP <= TR -> TR + 8 * Z.of_nat (length ws) <= 2^47 -> SP <= STK -> STK + 16 <= 2^47 ->
    16 * (zlen hs + 2) <= 2^20 -> 8 * (total + Z.of_nat (length tr) + 1) <= SWIN D -> total + Z.of_nat (length tr) + 1 < 2^20 ->

    (THR + 8 <= M \/ M + 16 <= THR) -> (CTX + 12 <= M \/ M + 16 <= CTX + 8) ->
    evt asegs (back1_post b0)
      (MS (mkR ra (wz SP) gp (wz A0_TP) t0 t1 t2 s0 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
               (wz B) (wz needed) (wz rz) (wz n) s6 (wz STK) (Z_to_bv 64 (-8)) (wz 7) (wz THR) (wz 1) t3 t4 t5 t6)
          F_ (wz 0x33900) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 tid b0 b1 j2 j4 j8 MI ST FR16 HD1 HD2 THC TIDC SOBJ RD BUF TRW LENW LTR RNG QTR TRH QSTK STKH ROOM_N ROOM_F ROOM_T DJT DJC.
    destruct MDJ as (MLO & MHI & MDN & MSS).
    callk (hdr_spec _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc SP B M rz size needed n m BR RZ SZ HM _ _ _ _ b0 b1 j2 j4);
      [ exact MI | exact FR16 | exact HD1 | right; clear - MHI LOQ; lia | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    rename MUk into MU4, WMk into WM4, MI0 into MI4.
    rename PC into B3, POST into HDN.
    assert (RD4 : RDEPOT D hs total m4).
    { eapply RDEPOT_frame; [exact RD| exact MU4| exact WM4|]. unfold depot_apart. constructor; [| constructor]. cbn [fst snd].
      clear - MLO MDN MSS. lia. }
    pose proof (bkt_range (depot_hash tr)) as BKR.
    hideB MU4. hideB WM4. pose proof MI4 as MI4c. hideB MI4c.
    destruct SPR as (SP16 & SPH).
    assert (SPR2 : SP mod 16 = 0 /\ SP <= 2^47) by (split; [exact SP16| clear - SPH; lia]).
    assert (MR2 : 0 <= M /\ M + 16 <= 2^47) by (pose proof alloc_ceiling_range as ACR; unfold alloc_floor, alloc_ceiling_max in ACR; clear - MLO MHI CLO LOQ SPH; lia).
    assert (T0 : 0 <= total) by (destruct RD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & T0 & _); exact T0).
    pose proof DLO as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9).
    assert (DJH : disjoint_from Wd M 8).
    { cbn [disjoint_from]. unfold zlen in *. clear - MLO MHI MDN MSS BKR T0 ROOM_N ROOM_F LOQ DL7. lia. }
    clear DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9.
    clear DJT DJC FR16. hideB HDN. hideB THC. hideB TIDC. hideB SOBJ. hideB HD2. hideB BUF.
    callk (ctx_spec D _ gp _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc SP lo M THR CTX STK TR total m4 hs ws tr DLO CLO LOQ SPR2 THRR MR2
             _ _ _ _ _ _ _ _ _ _ _ tid j8);
      [ exact MI4 | assumption | exact THC | exact TIDC | exact SOBJ | exact HD2 | exact RD4 | exact BUF | exact TRW | exact LENW | exact LTR | exact RNG | exact QTR | exact TRH
      | exact ROOM_N | exact ROOM_F | exact ROOM_T | left; clear - MHI; lia | right; clear - MLO; lia | clear - MDN; lia | clear - MSS; lia | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    rename MI0 into MI5, PC into ST5, PC0 into RD5, PC1 into RES, PC2 into ACX. destruct POST as (mD & MUD & WMD & MID & MUS & WMS).
    unhideB HDN. eapply (rw_cells_transport asegs _ m4 m5) in HDN; [| exact MUk| exact WMk| cbn [cells_size csize Nat.add]; split; [clear; lia| exact DJH]].
    unhideB MU4. unhideB WM4. unhideB MI4c.
    apply evt_done. unfold back1_post, mstep.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, m4, mD, m5, _, _, _, _. split; [reflexivity|].
    split; [split; [exact MU4| split; [exact WM4| exact MI4c]]|]. split; [split; [exact MUD| split; [exact WMD| exact MID]]|].
    split; [split; [exact MUS| split; [exact WMS| exact MI5]]|].
    split; [exact ST5|]. split; [exact RD5|]. split; [exact RES|]. split; [exact B3|]. split; [exact HDN| exact ACX].
  Qed.
End BACK1.

Section BACK2.
  Context {HC : HasCeiling}.
  Variables (E : penv) (L : athread).
  Variables (gp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Variables (SP lo B M size needed : Z) (m : mem).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= SP - 64.
  Hypothesis SPR : SP mod 16 = 0 /\ SP + 128 <= 2^47.
  Hypothesis TL : thread_layout_ok L.
  Hypothesis BR : 6328320 <= B /\ (B = M \/ B + 16 <= M) /\ M mod 8 = 0 /\ M + 16 + size + 8 <= lo.
  Hypothesis SZ : 1 <= size <= 2^28 /\ size + 16 <= needed <= 2^40.
  Hypothesis UG : M + 16 + size + 8 <= 2147450880 \/ 17594333495296 <= B.
  Hypothesis TB : at_thr L + 4096 <= B \/ M + 16 + size + 8 <= at_thr L.

  Notation U := (M + 16).
  Notation THR := (at_thr L).

  Definition back2_post : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m6 m7 m8 m9 m' (bits' : byte) ub' ts',
      ms' = MS (mkR ra (wz (SP + 128)) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz U) a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mstep [(SP - 64, SP); (sh U, sh U + size / 8)] m m6
      /\ mstep [(sh U + size / 8, sh U + size / 8 + 1)] m6 m7
      /\ mstep [(SP - 32, SP); (THR + 2800, THR + 3168)] m7 m8
      /\ mstep [(U, U + Z.min size 4096)] m8 m9
      /\ mstep [(SP - 32, SP); (M, M + 2); (B, B + 16)] m9 m'
      /\ stk asegs m' lo (SP + 128)
      /\ Z.land (bv_unsigned bits') 3 = 1
      /\ rw_cells asegs m' M [C1 (Z_to_bv 8 2); C1 bits']
      /\ (B <> M -> rw_cells asegs m' B [C8 (wz 14730877155918386873); C8 (wz M)])
      /\ rw_cells asegs m' U [CB (Z.to_nat size) ub']
      /\ rw_cells asegs m' (sh U) [CB (Z.to_nat (size / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (size / 8)))]
      /\ (size mod 8 <> 0 -> rw_cells asegs m' (sh U + size / 8) [C1 (Z_to_bv 8 (size mod 8))])
      /\ rw_cells asegs m8 (THR + 2800) [CB 368 ts']
      /\ (size mod 8 = 0 -> m7 = m6)
      /\ (B = M -> munch [(SP - 32, SP); (M, M + 2)] m9 m').

  #[using="HC LOH CLO LOQ SPR TL BR SZ UG TB"] Lemma back2_spec : forall (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x8 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (b0 bits : byte) (j ub ju ts : list byte) (c2 : word),
    mem_inv asegs m -> stk asegs m lo SP -> poison_env E m -> alloc_env m -> hooks_env m -> thread_env L m ->
    rw_cells asegs m SP [CB 8 j; C8 (wz 1); C8 c2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m M [C1 b0; C1 bits] -> Z.land (bv_unsigned bits) 3 = 1 ->
    (B <> M -> exists lj, rw_cells asegs m B [CB 16 lj]) ->
    rw_cells asegs m U [CB (Z.to_nat size) ub] ->
    rw_cells asegs m (sh U) [CB (Z.to_nat (size / 8)) ju] ->
    (size mod 8 <> 0 -> exists bp, rw_cells asegs m (sh U + size / 8) [C1 bp]) ->
    rw_cells asegs m (THR + 2800) [CB 368 ts] ->
    evt asegs back2_post
      (MS (mkR ra' (wz SP) gp (wz A0_TP) t0 t1 t2 x8 (wz size) a0 a1 a2 a3 a4 a5 a6 a7
               (wz B) (wz needed) (wz U) (wz M) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F_ (wz 0x33af0) fc None m (seg_rom asegs)).
  Proof.
    intros ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x8 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 b0 bits j ub ju ts c2
      MI ST PE AE HKE TE FR HDc B3 LCH UB SHU SHP TS.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    destruct BR as (BLO & BM & M8 & MHI). destruct SZ as (SZ1 & SZ2). destruct SPR as (SP16 & SPH).
    pose proof TL as (_ & _ & T3 & T4 & _).
    assert (SHRG : 2147450880 <= sh U /\ sh U + size / 8 + 1 <= 17594333495296)
      by (unfold sh, SHADOW_OFF; clear - BLO BM M8 MHI LOQ SPH SZ1; Z.div_mod_to_equations; lia).
    unfold hooks_env in HKE. ae_split AE.
    hideB FR. hideB HDc. hideB UB. hideB TS.

    assert (QBp : 0x10007fff8000 <= lo /\ lo <= SP - 64 /\ SP <= 2^47) by (split; [exact LOH| split; [exact LOQ| clear - SPH; lia]]).
    assert (URp : 0 <= U /\ U mod 8 = 0 /\ 1 <= size <= 2^28) by (split; [clear - BLO BM; lia| split; [clear - M8; Z.div_mod_to_equations; lia| exact SZ1]]).
    assert (UGp : U + size + 8 <= 2147450880 \/ (17594333495296 <= U /\ U + size + 8 <= 2^47)) by (clear - UG BM MHI LOQ SPH; lia).
    callk (unpa_spec E gp _ _ _ _ _ _ _ _ _ F_ fc SP lo U size m QBp URp UGp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ju);
      [ exact MI | exact ST | exact PE | exact SHU | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    rename MUk into MU6, WMk into WM6, MI0 into MI6, PC into ST6, PC0 into PE6, POST into SHZ.
    hideB MU6. hideB WM6. pose proof MI6 as MI6c. hideB MI6c. hideB SHZ.

    assert (SHP6 : size mod 8 <> 0 -> exists bp, rw_cells asegs m6 (sh U + size / 8) [C1 bp]).
    { intros NE. destruct (SHP NE) as (bp & PC). exists bp. unhideB MU6. unhideB WM6.
      eapply (rw_cells_transport asegs _ m m6) in PC; [exact PC| exact MU6| exact WM6|].
      cbn [disjoint_from cells_size csize Nat.add]. clear - SHRG LOH LOQ. lia. }
    clear SHP.
    callk (unpb_spec E gp _ _ _ _ _ _ _ _ _ F_ fc SP U size m6 URp UGp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [ exact MI6 | exact PE6 | exact AE_partial | exact SHP6 | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    rename MUk into MU7, WMk into WM7, MI0 into MI7, PC into SHPZ, POST into EQ7.
    hideB SHPZ. pose proof MI7 as MI7c. hideB MI7c.

    pose proof TL as (T1 & T2 & _ & _ & T5 & _).
    unhideB MU6. unhideB WM6.
    assert (S8 : 0 <= size / 8) by (apply Z.div_pos; clear - SZ1; lia).
    assert (DJ67 : forall A k0, (A + k0 <= 2147450880 \/ 17594333495296 <= A) -> (A + k0 <= SP - 64 \/ SP <= A) ->
              disjoint_from [(SP - 64, SP); (sh U, sh U + size / 8)] A k0 /\ disjoint_from [(sh U + size / 8, sh U + size / 8 + 1)] A k0).
    { intros A k0 H1 H2. cbn [disjoint_from]. clear - H1 H2 SHRG S8. lia. }
    assert (TE7 : thread_env L m7).
    { eapply thread_env_frame; [| exact MU7| exact WM7|].
      - eapply thread_env_frame; [exact TE| exact MU6| exact WM6|]. unfold thread_clear. constructor; [| constructor; [| constructor]]; cbn [fst snd].
        + clear - LOH LOQ CLO T1 T2 T3 T4 ACR. lia.
        + clear - SHRG S8 T1 T2 T3 T4 ACR. lia.
      - unfold thread_clear. constructor; [| constructor]. cbn [fst snd]. clear - SHRG S8 T1 T2 T3 T4 ACR. lia. }
    unhideB FR. eapply (rw_cells_transport asegs _ m m6) in FR; [| exact MU6| exact WM6| apply DJ67; cbn [cells_size csize Nat.add]; clear - LOH LOQ SPH; lia].
    eapply (rw_cells_transport asegs _ m6 m7) in FR; [| exact MU7| exact WM7| apply DJ67; cbn [cells_size csize Nat.add]; clear - LOH LOQ SPH; lia].
    unhideB TS. eapply (rw_cells_transport asegs _ m m6) in TS; [| exact MU6| exact WM6| apply DJ67; cbn [cells_size csize Nat.add]; clear - LOH CLO LOQ T3 T4 ACR; lia].
    eapply (rw_cells_transport asegs _ m6 m7) in TS; [| exact MU7| exact WM7| apply DJ67; cbn [cells_size csize Nat.add]; clear - LOH CLO LOQ T3 T4 ACR; lia].
    pose proof FR as FRc. split_chunk FRc 1%nat FRa FRb. split_chunk FRb 1%nat FR8 FRd. clear FRa FRd. change (Z.of_nat 8) with 8 in FR8.
    hideB MU6. hideB WM6. hideB FR. clear T1 T2 T5.
    hideB MU7. hideB WM7.
    assert (SPR3 : SP mod 16 = 0 /\ SP + 16 <= 2^47) by (split; [exact SP16| clear - SPH; lia]).
    assert (SZ3 : 1 <= size /\ size + 16 <= needed <= 2^40) by (clear - SZ1 SZ2; lia).
    callk (stats_spec L gp _ _ _ _ _ _ _ _ _ _ F_ fc SP lo size needed m7 CLO ltac:(clear - LOQ; lia) SPR3 SZ3 TL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ts);
      [ exact MI7 | assumption | exact TE7 | exact FR8 | exact TS | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
    rename MUk into MU8, WMk into WM8, MI0 into MI8, PC into ST8, PC0 into TE8, POST into TS8.
    hideB MU8. hideB WM8. pose proof MI8 as MI8c. hideB MI8c. hideB TS8.

    unhideB MU6. unhideB WM6. unhideB MU7. unhideB WM7. unhideB MU8. unhideB WM8.
    assert (IMGQ : forall lo0 hi0, (hi0 <= 0x10000 \/ 0x609000 <= lo0) -> img_out_q (lo0, hi0)) by (intros lo0 hi0 HH; unfold img_out_q; cbn [fst snd]; clear - HH; lia).
    assert (PE8 : poison_env E m8).
    { eapply poison_env_frame_q; [| exact MU8| exact WM8|].
      - eapply poison_env_frame_q; [exact PE6| exact MU7| exact WM7|]. constructor; [| constructor]. apply IMGQ. clear - SHRG S8. lia.
      - constructor; [| constructor; [| constructor]]; apply IMGQ; [clear - LOH LOQ; lia| clear - T3; lia]. }
    assert (AE8 : alloc_env m8) by (unfold alloc_env; repeat match goal with |- _ /\ _ => split end; assumption).
    unhideB UB.
    eapply (rw_cells_transport asegs _ m m6) in UB; [| exact MU6| exact WM6| apply DJ67; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - SZ1; lia); [clear - UG BM SZ1; lia| clear - MHI LOQ; lia]].
    eapply (rw_cells_transport asegs _ m6 m7) in UB; [| exact MU7| exact WM7| apply DJ67; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - SZ1; lia); [clear - UG BM SZ1; lia| clear - MHI LOQ; lia]].
    eapply (rw_cells_transport asegs _ m7 m8) in UB; [| exact MU8| exact WM8| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - SZ1; lia); clear - MHI LOQ TB BM; lia].
    hideB MU6. hideB WM6. hideB MU7. hideB WM7. hideB MU8. hideB WM8.
    assert (URf : 0 <= U /\ U + size <= 2^47 /\ 1 <= size <= 2^28) by (clear - BLO BM MHI LOQ SPH SZ1; lia).
    callk (fill_spec E gp _ _ _ _ _ _ _ _ _ _ F_ fc SP U size m8 URf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ub);
      [ exact MI8 | exact PE8 | exact AE8 | exact UB | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    rename MUk into MU9, WMk into WM9, MI0 into MI9, POST into UB9.
    hideB MU9. hideB WM9. pose proof MI9 as MI9c. hideB MI9c. hideB UB9.

    unhideB MU6. unhideB WM6. unhideB MU7. unhideB WM7. unhideB MU8. unhideB WM8. unhideB MU9. unhideB WM9.
    assert (AE9 : alloc_env m9) by (unfold alloc_env; repeat match goal with |- _ /\ _ => split end; assumption).
    unhideB FR.
    eapply (rw_cells_transport asegs _ m7 m8) in FR; [| exact MU8| exact WM8| cbn [disjoint_from cells_size csize Nat.add]; clear - LOH CLO LOQ T4 ACR; lia].
    eapply (rw_cells_transport asegs _ m8 m9) in FR; [| exact MU9| exact WM9| cbn [disjoint_from cells_size csize Nat.add]; clear - MHI LOQ SZ1; lia].
    assert (DJB : forall A k0, B <= A -> A + k0 <= M + 2 -> 0 <= k0 ->
              (disjoint_from [(SP - 64, SP); (sh U, sh U + size / 8)] A k0 /\ disjoint_from [(sh U + size / 8, sh U + size / 8 + 1)] A k0)
              /\ disjoint_from [(SP - 32, SP); (THR + 2800, THR + 3168)] A k0 /\ disjoint_from [(U, U + Z.min size 4096)] A k0).
    { intros A k0 HA1 HA2 HK. split; [apply DJ67; [clear - HA1 HA2 HK UG BM SZ1; lia| clear - HA2 MHI LOQ SZ1; lia]|].
      cbn [disjoint_from]. clear - HA1 HA2 HK MHI LOQ SZ1 TB. lia. }
    unhideB HDc.
    eapply (rw_cells_transport asegs _ m m6) in HDc; [| exact MU6| exact WM6| apply (DJB M 2); cbn [cells_size csize Nat.add]; clear - BM; lia].
    eapply (rw_cells_transport asegs _ m6 m7) in HDc; [| exact MU7| exact WM7| apply (DJB M 2); cbn [cells_size csize Nat.add]; clear - BM; lia].
    eapply (rw_cells_transport asegs _ m7 m8) in HDc; [| exact MU8| exact WM8| apply (DJB M 2); cbn [cells_size csize Nat.add]; clear - BM; lia].
    eapply (rw_cells_transport asegs _ m8 m9) in HDc; [| exact MU9| exact WM9| apply (DJB M 2); cbn [cells_size csize Nat.add]; clear - BM; lia].
    assert (LCH9 : B <> M -> exists lj, rw_cells asegs m9 B [CB 16 lj]).
    { intros NE. destruct (LCH NE) as (lj & LC). exists lj. assert (BM16 : B + 16 <= M) by (clear - BM NE; lia).
      eapply (rw_cells_transport asegs _ m m6) in LC; [| exact MU6| exact WM6| apply (DJB B 16); cbn [cells_size csize Nat.add]; clear - BM16; lia].
      eapply (rw_cells_transport asegs _ m6 m7) in LC; [| exact MU7| exact WM7| apply (DJB B 16); cbn [cells_size csize Nat.add]; clear - BM16; lia].
      eapply (rw_cells_transport asegs _ m7 m8) in LC; [| exact MU8| exact WM8| apply (DJB B 16); cbn [cells_size csize Nat.add]; clear - BM16; lia].
      eapply (rw_cells_transport asegs _ m8 m9) in LC; [exact LC| exact MU9| exact WM9| apply (DJB B 16); cbn [cells_size csize Nat.add]; clear - BM16; lia]. }
    hideB MU6. hideB WM6. hideB MU7. hideB WM7. hideB MU8. hideB WM8. hideB MU9. hideB WM9.
    assert (BRt : 6328320 <= B /\ (B = M \/ B + 16 <= M) /\ M + 16 <= lo /\ 1 <= size <= 2^28) by (clear - BLO BM MHI SZ1; lia).
    hideB DJ67. hideB DJB.
    callk (tail_spec gp F_ fc ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo B M size m9 CLO ltac:(clear - LOQ; lia) (conj SP16 SPH) BRt
             _ _ _ _ _ _ _ _ _ _ _ _ _ (wz 0) (wz 0) _ _ _ _ _ _ _ _ _ _ _ b0 bits j (wz 1) c2);
      [ exact MI9 | assumption | exact HKE | exact AE9 | exact FR | exact HDc | exact B3 | exact LCH9 | ].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mZ end.
    rename MUk into MUZ, WMk into WMZ, MI0 into MIZ.
    rename PC into STZ, PC0 into B3Z, PC1 into HDZ, PC2 into LCHZ, POST into MUZp.
    unhideB MU7. unhideB WM7. unhideB MU8. unhideB WM8. unhideB MU9. unhideB WM9.
    assert (DJS : forall A k0, sh U <= A -> A + k0 <= sh U + size / 8 + 1 ->
              disjoint_from [(SP - 32, SP); (THR + 2800, THR + 3168)] A k0 /\ disjoint_from [(U, U + Z.min size 4096)] A k0
              /\ disjoint_from [(SP - 32, SP); (M, M + 2); (B, B + 16)] A k0).
    { intros A k0 HA1 HA2. cbn [disjoint_from]. clear - HA1 HA2 SHRG LOH LOQ T3 T4 ACR CLO UG BM MHI SZ1 BLO. lia. }
    unhideB SHZ.
    eapply (rw_cells_transport asegs _ m6 m7) in SHZ; [| exact MU7| exact WM7| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by exact S8; clear; lia].
    eapply (rw_cells_transport asegs _ m7 m8) in SHZ; [| exact MU8| exact WM8| apply DJS; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by exact S8; clear; lia].
    eapply (rw_cells_transport asegs _ m8 m9) in SHZ; [| exact MU9| exact WM9| apply DJS; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by exact S8; clear; lia].
    eapply (rw_cells_transport asegs _ m9 mZ) in SHZ; [| exact MUZ| exact WMZ| apply DJS; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by exact S8; clear; lia].
    unhideB SHPZ.
    assert (SHPF : size mod 8 <> 0 -> rw_cells asegs mZ (sh U + size / 8) [C1 (Z_to_bv 8 (size mod 8))]).
    { intros NE. pose proof (SHPZ NE) as PC.
      eapply (rw_cells_transport asegs _ m7 m8) in PC; [| exact MU8| exact WM8| apply DJS; cbn [cells_size csize Nat.add]; clear - S8; lia].
      eapply (rw_cells_transport asegs _ m8 m9) in PC; [| exact MU9| exact WM9| apply DJS; cbn [cells_size csize Nat.add]; clear - S8; lia].
      eapply (rw_cells_transport asegs _ m9 mZ) in PC; [exact PC| exact MUZ| exact WMZ| apply DJS; cbn [cells_size csize Nat.add]; clear - S8; lia]. }
    unhideB UB9.
    eapply (rw_cells_transport asegs _ m9 mZ) in UB9; [| exact MUZ| exact WMZ| cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear - SZ1; lia); clear - MHI LOQ BM; lia].
    unhideB MU6. unhideB WM6. unhideB MI6c. unhideB MI7c. unhideB MI8c. unhideB MI9c. unhideB TS8.
    apply evt_done. unfold back2_post, mstep.
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, m6, m7, m8, m9, mZ, _, _, _. split; [reflexivity|].
    split; [split; [exact MU6| split; [exact WM6| exact MI6c]]|]. split; [split; [exact MU7| split; [exact WM7| exact MI7c]]|].
    split; [split; [exact MU8| split; [exact WM8| exact MI8c]]|]. split; [split; [exact MU9| split; [exact WM9| exact MI9c]]|].
    split; [split; [exact MUZ| split; [exact WMZ| exact MIZ]]|].
    split; [exact STZ|]. split; [exact B3Z|]. split; [exact HDZ|]. split; [exact LCHZ|]. split; [exact UB9|]. split; [exact SHZ|]. split; [exact SHPF|]. split; [exact TS8|]. split; [exact EQ7| exact MUZp].
  Qed.
End BACK2.

