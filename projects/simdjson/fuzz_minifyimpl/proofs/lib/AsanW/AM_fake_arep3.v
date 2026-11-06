(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt
     FsKit AFake_iface F_tlsga F_m2s_b AFake_arep AU_fake_arep AM_fake_sm3 AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].

Section CANSEC1. Context {rc : runConstT}.
Notation FB3 F := (mkABlock (ABFake 3) F 512).
Definition SM3_STACK_P : Z := 4096.   (* [comment removed for export] *)

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Hypothesis HL : ahole_laws (AFake_arep.AH DI AQ ASEC).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation AH := (AFake_arep.AH DI AQ ASEC).

Definition sm3_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB3 F :: LB) m'
    /\ F mod 512 = 0 /\ ablk F (F + 512) /\ F + 512 <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 480 junk; C8 (Z_to_bv 64 (fflag L 3 F))]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                                  C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 512 /\ rng RNG (shad F) 64.

(* [comment removed for export] *)
Lemma arep_ext_sm3 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AH L st X m ->
  munch [(sp - 208, sp); (fs + 24, fs + 32); (flag, flag + 1); (F + 24, F + 32); (F + 504, F + 512); (2147450880 + F / 8, 2147450880 + F / 8 + 64)] m m' ->
  wmono asegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 512 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 64 <= shad fs + 1446400 ->
  AREP AH L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' DI AQ ASEC HL L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.

Theorem stack_malloc_3_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  (forall F n, ~ In (mkABlock (ABFake 3) F n) LB) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM3_STACK_P ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm3_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC3x) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros AHP NOFK MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).
  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  (* [comment removed for export] *)
  destruct (AREP_cells DI AQ ASEC L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  (* [comment removed for export] *)
  pose proof (relro_word m 0x167068 0x1ffe58 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0x167e58 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0x167e48 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM3_STACK_P in *.
  (* [comment removed for export] *)
  assert (DH : dc_at m (al_fake L) 88).
  { pose proof (dc_of_cells m (al_fake L) _ HNT) as D. exact D. }
  destruct (dc_take m (al_fake L) 88 24 DH ltac:(lia)) as [DHA DHB]. replace (88 - 24) with 64 in DHB by reflexivity.
  destruct (dc_take m (al_fake L) 24 8 DHA ltac:(lia)) as [DH0 DH12]. replace (24 - 8) with 16 in DH12 by reflexivity.
  destruct (c8_of_dc m _ DH0) as [g0 HG0]. destruct (c8c8_of_dc m _ DH12) as (g1 & g2 & HG12).
  destruct (dc_take m (al_fake L + 24) 64 8 DHB ltac:(lia)) as [DH3 DH4]. replace (64 - 8) with 56 in DH4 by reflexivity.
  destruct (c8_of_dc m _ DH3) as [hw HW]. destruct DH4 as [hs4 HS4]. change (Z.to_nat 56) with 56%nat in HS4.
  set (h := bv_unsigned hw).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (HNT' : rw_cells asegs m (al_fake L) [C8 g0; C8 g1; C8 g2; C8 (Z_to_bv 64 h); CB 56 hs4]).
  { apply (proj2 (rw_cells_app asegs m (al_fake L) [C8 g0] _)). split; [exact HG0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m (al_fake L + Z.of_nat 8) [C8 g1; C8 g2] _)). split; [replace (al_fake L + Z.of_nat 8) with (al_fake L + 8) by lia; exact HG12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m (al_fake L + Z.of_nat 8 + Z.of_nat 16) [C8 (Z_to_bv 64 h)] _)). split.
    - replace (al_fake L + Z.of_nat 8 + Z.of_nat 16) with (al_fake L + 24) by lia. subst h. rewrite Z_to_bv_bv_unsigned. exact HW.
    - cbn [cells_size csize Nat.add]. replace (al_fake L + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 8) with (al_fake L + 24 + 8) by lia. exact HS4. }
  clear HW HG0 HG12.
  set (pos := Z.land h 2047). set (flag := (al_fake L) + 32768 + pos). set (F := (al_fake L) + 3182592 + pos * 512).
  assert (PB : 0 <= pos < 2048).
  { subst pos. change 2047 with (Z.ones 11). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 3 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 3 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 3 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 397824 + 64 * pos = shad F /\ shad F + 64 <= shad (al_fake L) + 1446400 /\ shad F + 64 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 64 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  destruct (c1_of_dc m flag D3) as [fb FL0].
  assert (fb = Z_to_bv 8 0) as ->.
  { destruct (decide (fb = Z_to_bv 8 0)) as [E|NE]; [exact E| exfalso].
    apply (NOFK (fk_frame L 3 pos) (fk_fsize 3)). apply (FL 3 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
    rewrite <- EFL. apply (rw_C1_high m flag fb FL0). subst flag. lia. }
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 472 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 504) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
  (* [comment removed for export] *)
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 64 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS.
  destruct (dc_take m (shad F) 64 16 DS ltac:(lia)) as [DS0 DSR]. replace (64 - 16) with 48 in DSR by reflexivity.
  destruct (dc_take m (shad F + 16) 48 16 DSR ltac:(lia)) as [DS1 DSR']. replace (48 - 16) with 32 in DSR' by reflexivity.
  destruct (dc_take m (shad F + 16 + 16) 32 16 DSR' ltac:(lia)) as [DS2 DS3]. replace (32 - 16) with 16 in DS3 by reflexivity.
  destruct (c8c8_of_dc m _ DS0) as (sh0 & sh1 & SH01). destruct (c8c8_of_dc m _ DS1) as (sh2 & sh3 & SH23).
  destruct (c8c8_of_dc m _ DS2) as (sh4 & sh5 & SH45). destruct (c8c8_of_dc m _ DS3) as (sh6 & sh7 & SH67).
  assert (SH0 : rw_cells asegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3; C8 sh4; C8 sh5; C8 sh6; C8 sh7]).
  { apply (proj2 (rw_cells_app asegs m (shad F) [C8 sh0; C8 sh1] _)). split; [exact SH01|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m (shad F + Z.of_nat 16) [C8 sh2; C8 sh3] _)). split; [replace (shad F + Z.of_nat 16) with (shad F + 16) by lia; exact SH23|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m (shad F + Z.of_nat 16 + Z.of_nat 16) [C8 sh4; C8 sh5] _)). split;
      [replace (shad F + Z.of_nat 16 + Z.of_nat 16) with (shad F + 16 + 16) by lia; exact SH45|].
    cbn [cells_size csize Nat.add]. replace (shad F + Z.of_nat 16 + Z.of_nat 16 + Z.of_nat 16) with (shad F + 16 + 16 + 16) by lia. exact SH67. }
  clear SH01 SH23 SH45 SH67 DS0 DS1 DS2 DS3 DSR DSR'.
  (* [comment removed for export] *)
  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
  (* [comment removed for export] *)
  assert (HPOS : pos = Z.land h 2047) by reflexivity. assert (HFLAG : flag = (al_fake L) + 32768 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 3182592 + pos * 512) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc3_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x6a4de8 (al_fake L) h pos flag F j24 j56 sh0 sh1 sh2 sh3 sh4 sh5 sh6 sh7 g0 g1 g2 hs4);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm3_W in MU. rewrite SHF in MU.
  (* [comment removed for export] *)
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 24 <= a < (al_fake L) + 32) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 504 <= a < F + 512) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 64) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 512 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (8 * k + 6216 + pos). lia. }
  (* [comment removed for export] *)
  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm3 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB3 F) LB) by (apply NOFK).
  assert (HFK' : AFAKE L (FB3 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split.
    { (* [comment removed for export] *)
      exists g0, g1, g2, (le8 (Z_to_bv 64 (h + 1)) ++ hs4).
      pose proof HNT2 as HN. apply (proj1 (rw_cells_app asegs m' (al_fake L) [C8 g0; C8 g1; C8 g2] [C8 (Z_to_bv 64 (h + 1)); CB 56 hs4])) in HN.
      destruct HN as [HN1 HN2]. cbn [cells_size csize Nat.add] in HN2.
      assert (LH : length hs4 = 56%nat) by (destruct HS4 as [[[WF _] _] _]; cbn in WF; lia).
      apply (proj2 (rw_cells_app asegs m' (al_fake L) [C8 g0; C8 g1; C8 g2] [CB 64 (le8 (Z_to_bv 64 (h + 1)) ++ hs4)])).
      split; [exact HN1|]. cbn [cells_size csize Nat.add].
      eapply rw_cells_recast; [exact HN2| | | reflexivity].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LH. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity. }
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 3) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 3 pos' 3 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 3 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 3 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 3 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 3) with 512 in Hin by reflexivity. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }
  (* [comment removed for export] *)
  assert (BL' : ablocks L st X (FB3 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB3 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 512 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE DI AQ ASEC L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (3, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 3) with 512 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 3 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 3) with 512 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 512)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); unfold AIMG_HI in H; clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 DH DHA DHB DH0 DH12 DH3
        D3 D24 D56 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). unfold AIMG_HI in H. apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 472 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 472) with 472%nat in J1.
  assert (LJ : length junk1 = 472%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 480 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 3 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 480 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 472 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 480) with (F + 504) by lia. exact F56'. }
  (* [comment removed for export] *)
  unfold sm3_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  eapply rng_sub'; [exact A8| clear - SB1 SB2 PB; lia].
Qed.
End S.

(* [comment removed for export] *)
Section Inst.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Hypothesis HL : ahole_laws (AFake_arep.AH DI AQ ASEC).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Variable AI : AMallocIface.
Hypothesis E : AHEAP AI = AHEAP_P (AFake_arep.AH DI AQ ASEC).
Hypothesis EC : aci AI = CI.
Lemma stack_malloc_3_AI : stack_malloc_3_stmt AI fflag afake_rng.
Proof.
  unfold stack_malloc_3_stmt. intros until lo. intros AHx NOFK MI ST BOT LO SPT TP RSTK RI RFS.
  rewrite E in AHx.
  eapply evtF_mono; [eapply (stack_malloc_3_P DI AQ ASEC HL CI CI_OK); try eassumption; unfold SM3_STACK_P, SM3_STACK, ASTKMALLOC3, ASTKMALLOC3x in *; first [lia | reflexivity]|].
  cbv beta. intros ms' PO. unfold sm3_postP in PO. unfold sm3_post.
  destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
  exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
  rewrite E, EC. repeat (split; [assumption|]). exact REST.
Qed.
End Inst.
End CANSEC1.
