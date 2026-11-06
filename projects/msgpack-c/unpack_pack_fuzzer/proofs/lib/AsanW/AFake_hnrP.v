(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt FsKit AKit AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_ahnr. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AFake_cnt AFake_gcl. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMallocS_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocS_x.AMallocS_x.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition HNR_STACK : Z := 12288.
Definition hnr_bottom (sp : word) : Z := (bv_unsigned sp - 4160) / 4096 * 4096.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHg g := (AFake_arep.AFake_arep.AH (gb:=g) DI AQ ASEC).
Variable g : bool.
Hypothesis HL : ahole_laws (AHg g).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

Definition hnr_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ AHEAP_P (AHg true) L RNG st LB m'
    /\ (forall a, 0 <= a < 2^64 -> aclient_addr CI LB (bv_unsigned sp) a ->
          ~ (shad (hnr_bottom sp) <= a < shad (al_top L)) ->
          m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None))
    /\ rw_cells asegs m' (shad (hnr_bottom sp))
         [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (al_top L - hnr_bottom sp))))].

Theorem hnr_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (junk : list byte),
  AHEAP_P (AHg g) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HNR_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->

  rw_cells asegs m (shad (hnr_bottom sp)) [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) junk] ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  rng RNG (shad (hnr_bottom sp)) (shlen (al_top L - hnr_bottom sp)) ->
  evtF asegs RNG (hnr_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AHNR) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros AHP MI ST BOT LO SPT TP DST RSTK RIMG (RF & RSH & RD) RSHD.
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.AFake_arep.AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AFake_arep.AFake_arep.AREP_cells DI AQ ASEC L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  pose proof AR as ARx. destruct ARx as (_ & RTx & _ & THRx & _). destruct THRx as (T0x & T40x & _).
  pose proof (poison_cells_of_rt' L m RTx) as PCx.
  pose proof RTx as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REALx & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  rw_split T0x 1%nat T0a T0b.
  pose proof (relro_word m 0xd1558 1 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as SEAL.
  unfold FAKESZ, AIMG_HI, HNR_STACK, hnr_bottom in *.
  set (bottom := (bv_unsigned sp - 4160) / 4096 * 4096) in *. set (size := al_top L - bottom) in *.
  word_range sp SPR.
  assert (BLO : bv_unsigned sp - 4160 - 4096 < bottom <= bv_unsigned sp - 4160) by (subst bottom; clear - SPR; Z.div_mod_to_equations; lia).
  assert (SZR : 0 < size <= 0x4000000) by (subst size; clear - BLO SPT SK1 SK3 BOT LO; lia).
  assert (T8 : al_top L mod 8 = 0).
  { pose proof (ao_stack L ALO) as OS. clear - OS SK1. destruct OS as (O1 & O2 & _). Z.div_mod_to_equations. lia. }
  eapply evtF_mono.
  { eapply (handle_no_return_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              FR fc m lo (al_ctx L) (al_t L) (al_top L) (al_bot L) (al_fake L) bottom size _ junk);
      try exact MI; try exact ST; try exact TP; try exact SEAL; try exact PCx; try exact T0b; try exact T40x; try exact TFSC; try exact NGC; try exact DST;
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (pose proof ARNG as (A1 & A2 & A3 & _); first [exact A2 | eapply rng_sub'; [exact A3| clear; lia]]).
    all: try (pose proof CL1 as CLx; unfold sclr, KLS in *; clear - CLx; lia).
    all: match goal with |- ?GG => idtac "REMHNR" GG end. }
  cbv beta. intros ms' PO. unfold hnr_post in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & MU & WM & MI' & ST' & ZSH & NGC').
  assert (BAL : bottom mod 4096 = 0) by (subst bottom; apply Z.mod_mul; lia).
  assert (SHR : 0x7fff8000 <= shad bottom /\ shad bottom + shlen size = shad (al_top L) /\ shad (al_top L) <= 0x10007fff8000 /\ shad ATOP <= shad bottom
                /\ shad (al_top L) <= shad (2^47)).
  { rewrite !gc_shad_eq. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. subst size.
    clear - BLO BAL T8 SK2 BOT LO SPR SPT. Z.div_mod_to_equations. lia. }
  destruct SHR as (SH1 & SH2 & SH3 & SH4 & SH5).
  assert (OUT : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ (shad bottom <= a < shad (al_top L)) ->
            a <> al_fake L + 96 -> m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3. apply MU. rewrite wa_unsigned by lia. cbn [outside]. rewrite SH2. repeat split; lia. }
  Local Ltac xportH H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
  assert (AR' : AREP (AHg g) L st X m').
  { eapply (AREP_frame_ext (AHg g) HL L st X m m' _ ALO AR MU WM).
    lazymatch goal with |- Forall _ ?W => change (Forall (aext L) W) end.
    apply Forall_cons; [unfold aext; cbn [fst snd]; intros _; right; right; left; clear - BOT LO; lia|].
    apply Forall_cons; [unfold aext; cbn [fst snd]; intros _; right; right; right; rewrite SH2; clear - SH4 SH5; lia|].
    apply Forall_cons; [unfold aext; cbn [fst snd]; intros _; left; clear; lia| apply Forall_nil]. }
  assert (SHFK : 0x7fff8000 <= shad (al_fake L) /\ shad (al_fake L) + 1446400 <= 0x10007fff8000
                 /\ (shad (al_fake L) + 1446400 <= shad bottom \/ shad (al_top L) <= shad (al_fake L))).
  { rewrite !gc_shad_eq. clear - G1 G2c G3 BLO BAL BOT LO ATR. Z.div_mod_to_equations. lia. }
  destruct SHFK as (SF1 & SF2 & SF3).
  assert (TFS' : rw_cells asegs m' (al_t L + 72) [C8 (Z_to_bv 64 (al_fake L))]).
  { xportH TFSC MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 SH3 TL1 TL2 TL3 TL4 G7s G7I G10 G11 G2c G3). }
  assert (HFK' : AFAKE (gb:=true) L LB m').
  { split; [exact G|]. split.
    { unfold afake_cells.
      split; [xportH REAL MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|]. split; [xportH DTVP MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|].
      split; [xportH DV MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|]. split; [xportH DTV1 MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|].
      split; [xportH BD MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 SH3 G5s G6 G9 GL1 G3)|]. split; [xportH CF MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|].
      split; [xportH VERB MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists h0, h1, h2, hs; xportH HNT MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 SH3 G2c G3)|].
    split; [xportH LOG MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 SH3 G2c G3)|].
    split; [exact NGC'|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    assert (FLOUT : forall c pos, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c -> m' (wa (fk_flag L c pos)) = m (wa (fk_flag L c pos))).
    { intros c pos Hc Hp. pose proof (fk_flag_range L c pos Hc Hp) as FRG. apply OUT; clear - FRG G2c G3 BOT LO ATR SH1 SH3; lia. }
    split.
    - intros c pos b Hc Hp Hb NZ. rewrite (FLOUT c pos Hc Hp) in Hb. eapply FL; eauto.
    - split; [| exact TFS']. intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos' & Hp' & HF' & B1).
      split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp'|]. split; [exact HF'|]. rewrite (FLOUT c pos' Hc Hp'). exact B1. }
  assert (AHP' : AHEAP_P (AHg true) L RNG st LB m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|]. cbn [AFake_arep.AFake_arep.AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (AFake_arep.AFake_arep.HB_FAKE DI AQ ASEC L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. clear - Q2 Q3 Q4 D G1 G3 GL1 ATR. lia.
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & _). split; [exact X3|]. clear - X1 X2 X4. lia. }
  unfold hnr_postP. do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AHP'|].
  split; [| fold bottom size; exact ZSH].
  intros a Ha Hc NSH. split; [| intros W0; apply WM; exact W0]. fold bottom in NSH.
  destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - apply OUT; [exact Ha| clear - Hs; lia| exact NSH| clear - Hs G3 BOT LO; lia].
  - pose proof (CI_OK iv Hiv). apply OUT; [exact Ha| clear - H Hr BOT LO ATR; unfold AIMG_HI in *; lia| exact NSH| clear - H Hr GL1; unfold AIMG_HI in *; lia].
  - destruct (BLK b Hb) as (Y1 & Y2 & Y3). apply OUT; [exact Ha| clear - Hr Y2 BOT LO; lia| exact NSH| clear - Hr Y3; lia].
  - assert (A'R : 0 <= a' < 2^47).
    { destruct Ha' as [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]]; [clear - X1 ATR; lia| pose proof (CI_OK iv Hiv); clear - H Hr; unfold AIMG_HI in *; lia|].
      destruct (BLK _ Hb) as (Y1 & Y2 & Y3). cbn [ab_addr ab_size] in Y1, Y2. apply ablk_lin in Y1. clear - Y1 Y2 Hr ATR. lia. }
    apply OUT; [exact Ha| | exact NSH|].
    + rewrite gc_shad_eq. clear - A'R BOT LO ATR. Z.div_mod_to_equations. lia.
    + rewrite gc_shad_eq. clear - A'R G2c. Z.div_mod_to_equations. lia.
Qed.
End S.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import RtCells.TwinB AProto.TwinB ABase.TwinB ABytes.TwinB AMalloc_iface.TwinB ADepot_iface.TwinB ARep.TwinB ALayout.TwinB AHeapP.TwinB ARepExt.TwinB FsKit.TwinB AKit.TwinB AFake_iface.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import F_ahnr.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep. Import AFake_cnt.TwinB AFake_gcl.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocS_x.TwinB.AMallocS_x.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition HNR_STACK : Z := 12288.
Definition hnr_bottom (sp : word) : Z := (bv_unsigned sp - 4160) / 4096 * 4096.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHg g := (AFake_arep.TwinB.AFake_arep.AH (gb:=g) DI AQ ASEC).
Variable g : bool.
Hypothesis HL : ahole_laws (AHg g).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

Definition hnr_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ AHEAP_P (AHg true) L RNG st LB m'
    /\ (forall a, 0 <= a < 2^64 -> aclient_addr CI LB (bv_unsigned sp) a ->
          ~ (shad (hnr_bottom sp) <= a < shad (al_top L)) ->
          m' (wa a) = m (wa a) /\ (wview bsegs m (wa a) <> None -> wview bsegs m' (wa a) <> None))
    /\ rw_cells bsegs m' (shad (hnr_bottom sp))
         [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (al_top L - hnr_bottom sp))))].

Theorem hnr_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (junk : list byte),
  AHEAP_P (AHg g) L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - HNR_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->

  rw_cells bsegs m (shad (hnr_bottom sp)) [CB (Z.to_nat (shlen (al_top L - hnr_bottom sp))) junk] ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  rng RNG (shad (hnr_bottom sp)) (shlen (al_top L - hnr_bottom sp)) ->
  evtF bsegs RNG (hnr_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 AHNR) fc None m (seg_rom bsegs)).
Proof.
  intros until junk. intros AHP MI ST BOT LO SPT TP DST RSTK RIMG (RF & RSH & RD) RSHD.
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.TwinB.AFake_arep.AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AFake_arep.TwinB.AFake_arep.AREP_cells DI AQ ASEC L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  pose proof AR as ARx. destruct ARx as (_ & RTx & _ & THRx & _). destruct THRx as (T0x & T40x & _).
  pose proof (poison_cells_of_rt' L m RTx) as PCx.
  pose proof RTx as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REALx & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  rw_split T0x 1%nat T0a T0b.
  pose proof (relro_word m 0xd3670 1 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as SEAL.
  unfold FAKESZ, AIMG_HI, HNR_STACK, hnr_bottom in *.
  set (bottom := (bv_unsigned sp - 4160) / 4096 * 4096) in *. set (size := al_top L - bottom) in *.
  word_range sp SPR.
  assert (BLO : bv_unsigned sp - 4160 - 4096 < bottom <= bv_unsigned sp - 4160) by (subst bottom; clear - SPR; Z.div_mod_to_equations; lia).
  assert (SZR : 0 < size <= 0x4000000) by (subst size; clear - BLO SPT SK1 SK3 BOT LO; lia).
  assert (T8 : al_top L mod 8 = 0).
  { pose proof (ao_stack L ALO) as OS. clear - OS SK1. destruct OS as (O1 & O2 & _). Z.div_mod_to_equations. lia. }
  eapply evtF_mono.
  { eapply (handle_no_return_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              FR fc m lo (al_ctx L) (al_t L) (al_top L) (al_bot L) (al_fake L) bottom size _ junk);
      try exact MI; try exact ST; try exact TP; try exact SEAL; try exact PCx; try exact T0b; try exact T40x; try exact TFSC; try exact NGC; try exact DST;
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (pose proof ARNG as (A1 & A2 & A3 & _); first [exact A2 | eapply rng_sub'; [exact A3| clear; lia]]).
    all: try (pose proof CL1 as CLx; unfold sclr, KLS in *; clear - CLx; lia).
    all: match goal with |- ?GG => idtac "REMHNR" GG end. }
  cbv beta. intros ms' PO. unfold hnr_post in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m' & -> & MU & WM & MI' & ST' & ZSH & NGC').
  assert (BAL : bottom mod 4096 = 0) by (subst bottom; apply Z.mod_mul; lia).
  assert (SHR : 0x7fff8000 <= shad bottom /\ shad bottom + shlen size = shad (al_top L) /\ shad (al_top L) <= 0x10007fff8000 /\ shad ATOP <= shad bottom
                /\ shad (al_top L) <= shad (2^47)).
  { rewrite !gc_shad_eq. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. subst size.
    clear - BLO BAL T8 SK2 BOT LO SPR SPT. Z.div_mod_to_equations. lia. }
  destruct SHR as (SH1 & SH2 & SH3 & SH4 & SH5).
  assert (OUT : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ (shad bottom <= a < shad (al_top L)) ->
            a <> al_fake L + 96 -> m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3. apply MU. rewrite wa_unsigned by lia. cbn [outside]. rewrite SH2. repeat split; lia. }
  Local Ltac xportH H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
  assert (AR' : AREP (AHg g) L st X m').
  { eapply (AREP_frame_ext (AHg g) HL L st X m m' _ ALO AR MU WM).
    lazymatch goal with |- Forall _ ?W => change (Forall (aext L) W) end.
    apply Forall_cons; [unfold aext; cbn [fst snd]; intros _; right; right; left; clear - BOT LO; lia|].
    apply Forall_cons; [unfold aext; cbn [fst snd]; intros _; right; right; right; rewrite SH2; clear - SH4 SH5; lia|].
    apply Forall_cons; [unfold aext; cbn [fst snd]; intros _; left; clear; lia| apply Forall_nil]. }
  assert (SHFK : 0x7fff8000 <= shad (al_fake L) /\ shad (al_fake L) + 1446400 <= 0x10007fff8000
                 /\ (shad (al_fake L) + 1446400 <= shad bottom \/ shad (al_top L) <= shad (al_fake L))).
  { rewrite !gc_shad_eq. clear - G1 G2c G3 BLO BAL BOT LO ATR. Z.div_mod_to_equations. lia. }
  destruct SHFK as (SF1 & SF2 & SF3).
  assert (TFS' : rw_cells bsegs m' (al_t L + 72) [C8 (Z_to_bv 64 (al_fake L))]).
  { xportH TFSC MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 SH3 TL1 TL2 TL3 TL4 G7s G7I G10 G11 G2c G3). }
  assert (HFK' : AFAKE (gb:=true) L LB m').
  { split; [exact G|]. split.
    { unfold afake_cells.
      split; [xportH REAL MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|]. split; [xportH DTVP MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|].
      split; [xportH DV MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|]. split; [xportH DTV1 MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|].
      split; [xportH BD MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 SH3 G5s G6 G9 GL1 G3)|]. split; [xportH CF MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|].
      split; [xportH VERB MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 GL1 G3)|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists h0, h1, h2, hs; xportH HNT MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 SH3 G2c G3)|].
    split; [xportH LOG MU WM ltac:(rewrite ?SH2; clear - BOT LO ATR SH1 SH3 G2c G3)|].
    split; [exact NGC'|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    assert (FLOUT : forall c pos, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c -> m' (wa (fk_flag L c pos)) = m (wa (fk_flag L c pos))).
    { intros c pos Hc Hp. pose proof (fk_flag_range L c pos Hc Hp) as FRG. apply OUT; clear - FRG G2c G3 BOT LO ATR SH1 SH3; lia. }
    split.
    - intros c pos b Hc Hp Hb NZ. rewrite (FLOUT c pos Hc Hp) in Hb. eapply FL; eauto.
    - split; [| exact TFS']. intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos' & Hp' & HF' & B1).
      split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp'|]. split; [exact HF'|]. rewrite (FLOUT c pos' Hc Hp'). exact B1. }
  assert (AHP' : AHEAP_P (AHg true) L RNG st LB m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|]. cbn [AFake_arep.TwinB.AFake_arep.AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (AFake_arep.TwinB.AFake_arep.HB_FAKE DI AQ ASEC L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. clear - Q2 Q3 Q4 D G1 G3 GL1 ATR. lia.
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & _). split; [exact X3|]. clear - X1 X2 X4. lia. }
  unfold hnr_postP. do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact AHP'|].
  split; [| fold bottom size; exact ZSH].
  intros a Ha Hc NSH. split; [| intros W0; apply WM; exact W0]. fold bottom in NSH.
  destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - apply OUT; [exact Ha| clear - Hs; lia| exact NSH| clear - Hs G3 BOT LO; lia].
  - pose proof (CI_OK iv Hiv). apply OUT; [exact Ha| clear - H Hr BOT LO ATR; unfold AIMG_HI in *; lia| exact NSH| clear - H Hr GL1; unfold AIMG_HI in *; lia].
  - destruct (BLK b Hb) as (Y1 & Y2 & Y3). apply OUT; [exact Ha| clear - Hr Y2 BOT LO; lia| exact NSH| clear - Hr Y3; lia].
  - assert (A'R : 0 <= a' < 2^47).
    { destruct Ha' as [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]]; [clear - X1 ATR; lia| pose proof (CI_OK iv Hiv); clear - H Hr; unfold AIMG_HI in *; lia|].
      destruct (BLK _ Hb) as (Y1 & Y2 & Y3). cbn [ab_addr ab_size] in Y1, Y2. apply ablk_lin in Y1. clear - Y1 Y2 Hr ATR. lia. }
    apply OUT; [exact Ha| | exact NSH|].
    + rewrite gc_shad_eq. clear - A'R BOT LO ATR. Z.div_mod_to_equations. lia.
    + rewrite gc_shad_eq. clear - A'R G2c. Z.div_mod_to_equations. lia.
Qed.
End S.
End CANSEC1.
End TwinB.
