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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt FsKit AKit AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsgaG. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition TLSGA_STACK : Z := 176.
Definition ATLSADDR : Z := ATP + 0x800.

Lemma tls_shad_eq : forall x, shad x = 0x7fff8000 + x / 8.
Proof. intros x. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHg g := (AFake_arep.AFake_arep.AH (gb:=g) DI AQ ASEC).
Variable g : bool.
Hypothesis HL : ahole_laws (AHg g).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

Definition tlsga_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATLSADDR) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ munch [(bv_unsigned sp - TLSGA_STACK, bv_unsigned sp)] m m' /\ wmono asegs m m'
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P (AHg g) L RNG st LB m'.

Theorem tlsga_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo A : Z),
  AHEAP_P (AHg g) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - TLSGA_STACK ->
  tp = Z_to_bv 64 ATP ->

  a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  ro_cells asegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG A 16 ->
  evtF asegs RNG (tlsga_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom asegs)).
Proof.
  intros until A. intros AHP MI ST BOT LO TP A0 ABV DESC RSTK RA.
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.AFake_arep.AH ah_fake] in HFK.
  pose proof HFK as (G & CE & _).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l). pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  destruct (AFake_arep.AFake_arep.AREP_cells DI AQ ASEC L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  pose proof (relro_word m 0xd1568 0x169558 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd22a8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  unfold TLSGA_STACK, AIMG_HI in *.
  eapply evtF_mono.
  { eapply (tlsga_icpt_gspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60cc80 (Z_to_bv 64 (al_fake L)) A);
      try exact MI; try exact ST; try exact TP; try exact A0; try exact ABV; try exact DESC; try exact RA; try exact A1;
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_gcells; split; [exact REAL|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]).
    all: match goal with |- ?GG => idtac "REMTLS" GG end. }
  cbv beta. intros ms' PO. unfold tlsga_icpt_gpost in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & ST').
  assert (OUT : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 176 <= a < bv_unsigned sp) -> m' (wa a) = m (wa a)).
  { intros a Ha N1. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (AR' : AREP (AHg g) L st X m').
  { eapply (AREP_frame_ext (AHg g) HL L st X m m' _ ALO AR MU WM).
    apply Forall_cons; [unfold aext; cbn [fst snd]; intros _; right; right; left; clear - BOT LO; lia| apply Forall_nil]. }
  assert (HFK' : ah_fake (AHg g) L LB m').
  { eapply (hf_frame (AHg g) HL L LB m m' _ HFK MU WM).
    - cbn [disjoint_from]. split; [| exact I]. cbn [fst snd]. clear - TL1 TL2 TL3 TL4 BOT LO ATR. lia.
    - unfold fake_untouched. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4).
      assert (SHF : shad (al_fake L) + shlen 11571200 <= ATOP).
      { rewrite tls_shad_eq. replace (shlen 11571200) with 1446400 by reflexivity. unfold FAKESZ in G3. clear - GL2 G3 ATR. Z.div_mod_to_equations. lia. }
      repeat split; right; clear - BOT LO GL3 SHF G3 G6 ATR; unfold FAKESZ in *; lia. }
  assert (AHP' : AHEAP_P (AHg g) L RNG st LB m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|]. exact HFK'. }
  assert (BLK : forall b, In b LB -> 0 <= ab_addr b /\ ab_addr b + ab_size b <= ATOP).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (AFake_arep.AFake_arep.HB_FAKE DI AQ ASEC L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. apply ablk_lin in Q1. clear - Q1. lia.
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & _). apply ablk_lin in X3. clear - X3. lia. }
  unfold tlsga_postP, ATLSADDR, TLSGA_STACK. do 14 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact MU|]. split; [exact WM|]. split; [| exact AHP'].
  intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
  apply OUT; [exact Ha|].
  destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - clear - Hs. lia.
  - pose proof (CI_OK iv Hiv) as H. unfold AIMG_HI in H. clear - H Hr BOT LO ATR. lia.
  - pose proof (BLK b Hb) as [Y0 Y]. clear - Hr Y BOT LO. lia.
  - assert (A'R : 0 <= a' < 2^47).
    { destruct Ha' as [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]]; [clear - X1 ATR; lia| pose proof (CI_OK iv Hiv) as H; unfold AIMG_HI in H; clear - H Hr; lia|].
      pose proof (BLK _ Hb) as [Y0 Y]. cbn [ab_addr ab_size] in Y0, Y. clear - Y0 Y Hr ATR. lia. }
    rewrite tls_shad_eq. clear - A'R BOT LO ATR. Z.div_mod_to_equations. lia.
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

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsgaG.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition TLSGA_STACK : Z := 176.
Definition ATLSADDR : Z := ATP + 0x800.

Lemma tls_shad_eq : forall x, shad x = 0x7fff8000 + x / 8.
Proof. intros x. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHg g := (AFake_arep.TwinB.AFake_arep.AH (gb:=g) DI AQ ASEC).
Variable g : bool.
Hypothesis HL : ahole_laws (AHg g).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

Definition tlsga_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ATLSADDR) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ munch [(bv_unsigned sp - TLSGA_STACK, bv_unsigned sp)] m m' /\ wmono bsegs m m'
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P (AHg g) L RNG st LB m'.

Theorem tlsga_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo A : Z),
  AHEAP_P (AHg g) L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - TLSGA_STACK ->
  tp = Z_to_bv 64 ATP ->

  a0 = Z_to_bv 64 A -> bv_unsigned sp <= A ->
  ro_cells bsegs m A [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0)] ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG A 16 ->
  evtF bsegs RNG (tlsga_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ATLSGA_ICPT) fc None m (seg_rom bsegs)).
Proof.
  intros until A. intros AHP MI ST BOT LO TP A0 ABV DESC RSTK RA.
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.TwinB.AFake_arep.AH ah_fake] in HFK.
  pose proof HFK as (G & CE & _).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l). pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  destruct (AFake_arep.TwinB.AFake_arep.AREP_cells DI AQ ASEC L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  pose proof (relro_word m 0xd3680 0x16b718 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd43c0 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  unfold TLSGA_STACK, AIMG_HI in *.
  eapply evtF_mono.
  { eapply (tlsga_icpt_gspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60ee40 (Z_to_bv 64 (al_fake L)) A);
      try exact MI; try exact ST; try exact TP; try exact A0; try exact ABV; try exact DESC; try exact RA; try exact A1;
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_gcells; split; [exact REAL|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]).
    all: match goal with |- ?GG => idtac "REMTLS" GG end. }
  cbv beta. intros ms' PO. unfold tlsga_icpt_gpost in PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & ST').
  assert (OUT : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 176 <= a < bv_unsigned sp) -> m' (wa a) = m (wa a)).
  { intros a Ha N1. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (AR' : AREP (AHg g) L st X m').
  { eapply (AREP_frame_ext (AHg g) HL L st X m m' _ ALO AR MU WM).
    apply Forall_cons; [unfold aext; cbn [fst snd]; intros _; right; right; left; clear - BOT LO; lia| apply Forall_nil]. }
  assert (HFK' : ah_fake (AHg g) L LB m').
  { eapply (hf_frame (AHg g) HL L LB m m' _ HFK MU WM).
    - cbn [disjoint_from]. split; [| exact I]. cbn [fst snd]. clear - TL1 TL2 TL3 TL4 BOT LO ATR. lia.
    - unfold fake_untouched. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4).
      assert (SHF : shad (al_fake L) + shlen 11571200 <= ATOP).
      { rewrite tls_shad_eq. replace (shlen 11571200) with 1446400 by reflexivity. unfold FAKESZ in G3. clear - GL2 G3 ATR. Z.div_mod_to_equations. lia. }
      repeat split; right; clear - BOT LO GL3 SHF G3 G6 ATR; unfold FAKESZ in *; lia. }
  assert (AHP' : AHEAP_P (AHg g) L RNG st LB m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL]|]. exact HFK'. }
  assert (BLK : forall b, In b LB -> 0 <= ab_addr b /\ ab_addr b + ab_size b <= ATOP).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (AFake_arep.TwinB.AFake_arep.HB_FAKE DI AQ ASEC L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. apply ablk_lin in Q1. clear - Q1. lia.
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & _). apply ablk_lin in X3. clear - X3. lia. }
  unfold tlsga_postP, ATLSADDR, TLSGA_STACK. do 14 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact MU|]. split; [exact WM|]. split; [| exact AHP'].
  intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
  apply OUT; [exact Ha|].
  destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
  - clear - Hs. lia.
  - pose proof (CI_OK iv Hiv) as H. unfold AIMG_HI in H. clear - H Hr BOT LO ATR. lia.
  - pose proof (BLK b Hb) as [Y0 Y]. clear - Hr Y BOT LO. lia.
  - assert (A'R : 0 <= a' < 2^47).
    { destruct Ha' as [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]]; [clear - X1 ATR; lia| pose proof (CI_OK iv Hiv) as H; unfold AIMG_HI in H; clear - H Hr; lia|].
      pose proof (BLK _ Hb) as [Y0 Y]. cbn [ab_addr ab_size] in Y0, Y. clear - Y0 Y Hr ATR. lia. }
    rewrite tls_shad_eq. clear - A'R BOT LO ATR. Z.div_mod_to_equations. lia.
Qed.
End S.
End CANSEC1.
End TwinB.
