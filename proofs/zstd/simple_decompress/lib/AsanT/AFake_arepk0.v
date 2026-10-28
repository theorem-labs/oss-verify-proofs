(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt
     FsKit AFake_iface F_tlsga F_m2s_b AFake_sm0 AFake_arep AFake_smk0 AZ_kit AFakeK_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation AH := (AFake_arep.AH DI AQ ASEC).
Notation sm0_postP := (AFake_arep.sm0_postP DI AQ ASEC CI).
Notation FB0 F := (mkABlock (ABFake 0) F 64).
(* [comment removed for export] *)
Definition sm0_postPK (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB0 F :: LB) m'
    /\ F mod 64 = 0 /\ ablk F (F + 64) /\ F + 64 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 (fflag L 0 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0)]
    /\ rng RNG F 64 /\ rng RNG (shad F) 8
    (* [comment removed for export] *)
    /\ munch (fake_area L ++ [(bv_unsigned sp - SMK_STACK, bv_unsigned sp)]) m m' /\ wmono bsegs m m'
    /\ al_fake L <= F /\ F + 64 <= al_fake L + FAKESZ.

Theorem stack_malloc_0k_P : forall (k : nat) (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  fake_le 0 k LB -> Z.of_nat k < 16384 ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm0_postPK L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros AHP LEK KB MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.   (* [comment removed for export] *)
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).
  (* [comment removed for export] *)
  destruct (AREP_cells _ _ _ L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  (* [comment removed for export] *)
  pose proof (relro_word m 0xc7358 0x15f798 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xc8048 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0xc8038 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  set (h := bv_unsigned h0).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  (* [comment removed for export] *)
  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
  (* [comment removed for export] *)
  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).
  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  clearbody h.
  (* [comment removed for export] *)
  assert (EFLg : forall pos, (al_fake L) + 4096 + pos = fk_flag L 0 pos)
    by (intros pos; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFRg : forall pos, (al_fake L) + 36864 + pos * 64 = fk_frame L 0 pos)
    by (intros pos; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (FLB : forall pos, 0 <= pos < 16384 -> exists fb, rw_cells bsegs m ((al_fake L) + 4096 + pos) [C1 fb]).
  { intros pos PB. pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) ((al_fake L) + 4096 + pos) 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
    exact (c1_of_dc m _ D3). }
  assert (FLV : forall pos fb, 0 <= pos < 16384 -> rw_cells bsegs m ((al_fake L) + 4096 + pos) [C1 fb] -> fb <> Z_to_bv 8 0 ->
             In (FB0 (fk_frame L 0 pos)) LB /\ fb = Z_to_bv 8 1).
  { intros pos fb PB FLx NE.
    assert (IN : In (FB0 (fk_frame L 0 pos)) LB).
    { change 64 with (fk_fsize 0). apply (FL 0 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
      rewrite <- EFLg. apply (rw_C1_high m _ fb FLx). lia. }
    split; [exact IN|].
    destruct (LV 0 _ _ IN) as (_ & _ & pos' & Hp' & HF' & B1).
    assert (pos' = pos) as ->.
    { unfold fk_frame, fk_frames, fk_fsize in HF'. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in HF'. unfold fk_nframes in Hp'. cbn in Hp'. lia. }
    rewrite <- EFLg in B1. pose proof (rw_C1_high m _ fb FLx ltac:(lia)) as B2. congruence. }
  (* [comment removed for export] *)
  assert (CHOICE : exists pos hn, 0 <= pos < 16384 /\ rw_cells bsegs m ((al_fake L) + 4096 + pos) [C1 (Z_to_bv 8 0)] /\
            forall (j24 j56 sh0 : word),
              rw_cells bsegs m ((al_fake L) + 36864 + pos * 64 + 24) [C8 j24] -> rw_cells bsegs m ((al_fake L) + 36864 + pos * 64 + 56) [C8 j56] ->
              rw_cells bsegs m (shad ((al_fake L) + 36864 + pos * 64)) [C8 sh0] ->
              evtF bsegs RNG (sm0_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo (al_fake L) hn
                                ((al_fake L) + 4096 + pos) ((al_fake L) + 36864 + pos * 64) h1 h2 hs m)
                (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs))).
  { (* [comment removed for export] *)
    set (fa := fun j => (al_fake L) + 4096 + Z.land (h + j) 16383).
    assert (PBj : forall j, 0 <= Z.land (h + j) 16383 < 16384) by (intros j; apply land16383_bound).
    assert (DEC : forall j, (exists fb, rw_cells bsegs m (fa j) [C1 fb] /\ fb = Z_to_bv 8 0)
                         \/ (exists fb, rw_cells bsegs m (fa j) [C1 fb] /\ fb <> Z_to_bv 8 0)).
    { intros j. destruct (FLB (Z.land (h + j) 16383) (PBj j)) as [fb FLj].
      destruct (decide (fb = Z_to_bv 8 0)) as [E|NE]; [left| right]; exists fb; split; assumption. }
    (* [comment removed for export] *)
    assert (SRCH : forall K : nat,
              (exists n, 0 <= n <= Z.of_nat K /\ (exists fb, rw_cells bsegs m (fa n) [C1 fb] /\ fb = Z_to_bv 8 0)
                         /\ forall j, 0 <= j < n -> exists b, rw_cells bsegs m (fa j) [C1 b] /\ b <> Z_to_bv 8 0)
              \/ (forall j, 0 <= j <= Z.of_nat K -> exists b, rw_cells bsegs m (fa j) [C1 b] /\ b <> Z_to_bv 8 0)).
    { induction K as [|K IH].
      - destruct (DEC 0) as [FR0|BS0].
        + left. exists 0. split; [lia|]. split; [exact FR0|]. intros j Hj. lia.
        + right. intros j Hj. replace j with 0 by lia. exact BS0.
      - destruct IH as [IHL|IHR]; [left; destruct IHL as (n & Hn & HF & HB0); exists n; split; [lia|]; split; [exact HF| exact HB0]|].
        destruct (DEC (Z.of_nat (S K))) as [FRK|BSK].
        + left. exists (Z.of_nat (S K)). split; [lia|]. split; [exact FRK|]. intros j Hj. apply IHR. lia.
        + right. intros j Hj. destruct (Z.eq_dec j (Z.of_nat (S K))) as [->|NE]; [exact BSK| apply IHR; lia]. }
    destruct (SRCH k) as [(n & HN & (fb0 & FLn & E0) & BUSY)|ALLB].
    - subst fb0. exists (Z.land (h + n) 16383), (h + n). split; [apply PBj|]. split; [exact FLn|].
      intros j24 j56 sh0 F24 F56 SH0.
      eapply (stack_malloc0_cspecK RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x602cb0 (al_fake L) h n (Z.land (h + n) 16383)
                 ((al_fake L) + 4096 + Z.land (h + n) 16383) ((al_fake L) + 36864 + Z.land (h + n) 16383 * 64) j24 j56 sh0 h1 h2 hs);
        try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
      all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
        split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
        split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
      all: try (eapply rng_sub'; [exact RSTK| lia]).
      all: try (eapply rng_sub'; [exact A3| lia]).
    - (* [comment removed for export] *)
      exfalso.
      set (fr := fun j : nat => fk_frame L 0 (Z.land (h + Z.of_nat j) 16383)).
      assert (INL : forall j : nat, (j <= k)%nat -> In (FB0 (fr j)) LB).
      { intros j Hj. destruct (ALLB (Z.of_nat j) ltac:(lia)) as (b & Hb & Nb).
        exact (proj1 (FLV (Z.land (h + Z.of_nat j) 16383) b (PBj _) Hb Nb)). }
      assert (INJ : forall i j : nat, (i <= k)%nat -> (j <= k)%nat -> fr i = fr j -> i = j).
      { intros i j Hi Hj E. unfold fr, fk_frame, fk_frames, fk_fsize in E. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in E.
        assert (E2 : Z.land (h + Z.of_nat i) 16383 = Z.land (h + Z.of_nat j) 16383) by lia.
        destruct (Nat.lt_total i j) as [LT|[EQ|GT]]; [| exact EQ|].
        - exfalso. apply (land16383_inj h (Z.of_nat i) (Z.of_nat j)); [lia| lia| exact E2].
        - exfalso. apply (land16383_inj h (Z.of_nat j) (Z.of_nat i)); [lia| lia| symmetry; exact E2]. }
      assert (ND : List.NoDup (map fr (seq 0 (S k)))).
      { apply List.NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup]. intros i j Hi Hj E. apply in_seq in Hi, Hj. apply INJ; [lia| lia| exact E]. }
      pose proof (LEK (map fr (seq 0 (S k))) ND) as LL.
      rewrite length_map, length_seq in LL.
      assert (S k <= k)%nat; [apply LL|lia].
      intros F' HF'. apply in_map_iff in HF'. destruct HF' as (j & <- & Hj). apply in_seq in Hj. exists 64. apply INL. lia. }
  destruct CHOICE as (pos & hn & PB & FL0 & WALK).
  set (flag := (al_fake L) + 4096 + pos) in *. set (F := (al_fake L) + 36864 + pos * 64) in *.
  assert (EFL : flag = fk_flag L 0 pos) by (subst flag; apply EFLg).
  assert (EFR : F = fk_frame L 0 pos) by (subst F; apply EFRg).
  assert (EFF : fflag L 0 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHB : shad (al_fake L) + 4608 + 8 * pos = shad F /\ shad F + 8 <= shad (al_fake L) + 1446400 /\ shad F + 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8_of_dc m _ DS2) as [sh0 SH0].
  assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
  clearbody flag F.
  (* [comment removed for export] *)
  assert (NOTIN : ~ In (FB0 F) LB).
  { intros IN. destruct (LV 0 F 64 IN) as (_ & _ & pos' & Hp' & HF' & B1).
    assert (pos' = pos) as ->.
    { rewrite EFR in HF'. unfold fk_frame, fk_frames, fk_fsize in HF'. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in HF'.
      unfold fk_nframes in Hp'. cbn in Hp'. lia. }
    rewrite <- EFL in B1. pose proof (rw_C1_high m flag _ FL0 ltac:(lia)) as B0. rewrite B0 in B1. injection B1 as B1.
    vm_compute in B1. discriminate B1. }
  eapply evtF_mono; [exact (WALK j24 j56 sh0 F24 F56 SH0)|].

  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm0_W in MU. rewrite SHF in MU.
  (* [comment removed for export] *)
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) <= a < (al_fake L) + 8) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 56 <= a < F + 64) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 8) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 64 = 0) by (rewrite EFR; apply fk_frame_al64; [exact G1| lia]).
  (* [comment removed for export] *)
  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].   (* [comment removed for export] *)
  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm0 _ _ _ HL L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (HFK' : AFAKE L (FB0 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }   (* [comment removed for export] *)
    split; [exists (Z_to_bv 64 (hn + 1)), h1, h2, hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 0) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 0 pos' 0 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 0 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 0 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 0 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. unfold fk_fsize in Hin.
          cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in Hin. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }
  (* [comment removed for export] *)
  assert (BL' : ablocks L st X (FB0 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB0 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP   (* [comment removed for export] *)
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 64 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE _ _ _ L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (0, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 0) with 64 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 0 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 0) with 64 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->   (* [comment removed for export] *)
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 64)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
        D24 D56 DS2 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.   (* [comment removed for export] *)
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 24 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 24) with 24%nat in J1.
  assert (LJ : length junk1 = 24%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 32 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 0 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app bsegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 32 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app bsegs m' (F + 24) [C8 sp] [CB 24 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 32) with (F + 56) by lia. exact F56'. }
  (* [comment removed for export] *)
  unfold sm0_postPK. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].   (* [comment removed for export] *)
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]|].
  (* [comment removed for export] *)
  split; [eapply munch_weaken; [| exact MU]; intros x; unfold fake_area, SMK_STACK; change (FAKESZ / 8) with 1446400; unfold FAKESZ;
          cbn [outside app]; clear - SB1 SB2 SHF HFF HFLAG PB LO; lia|].
  split; [exact WM|]. unfold FAKESZ. clear - HFF PB; lia.
Qed.

(* [comment removed for export] *)
Section Inst.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P AH.
  Hypothesis EC : aci AI = CI.

  Lemma stack_malloc_0k_AI : forall k, Z.of_nat k < 16384 -> stack_malloc_0k_stmt AI fflag afake_rng k.
  Proof.
    intros k KB. unfold stack_malloc_0k_stmt. intros until lo. intros AHx LE MI ST BOT LO SPT TP RSTK RI RFS.
    rewrite E in AHx.
    eapply evtF_mono; [eapply (stack_malloc_0k_P k); eassumption|].
    cbv beta. intros ms' PO. unfold sm0_postPK in PO. unfold sm0k_post.
    destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
    exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
    rewrite E, EC. repeat (split; [assumption|]). exact REST.
  Qed.
  Lemma fake_flag_AI : fake_flag_law AI fflag.
  Proof.
    unfold fake_flag_law. intros L RNG st LB m cls F N AHx Hin. rewrite E in AHx. rewrite EC.
    eapply fake_flag_P; eassumption.
  Qed.
  Lemma fake_release_AI : fake_release_law AI fflag.
  Proof. unfold fake_release_law. intros L RNG st LB m cls F N AHx. rewrite E in AHx |- *. eapply fake_release_P; eassumption. Qed.
End Inst.
End S.
End CANSEC1.
