(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require ExecF ITreeA Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt FsKit AFake_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_tlsga.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_m2s_b.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF.
Module AFake_arep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Definition AH : aholes := mkAHoles AQ ASEC (ADEPOT DI) AFAKE.
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

Lemma HB_FAKE : forall L RNG st LB m p A n,
  AHEAP_P AH L RNG st LB m -> In (HB p A n) LB ->
  ablock_range A n /\ (A + n <= al_fake L \/ al_fake L + 11571200 <= A).
Proof. intros. split; [eapply AHEAP_P_hb_range; eauto| eapply AHEAP_P_hb_fake; eauto]. Qed.

Lemma AREP_frame_ext' : forall L st X m m' W,
  alayout_ok L -> AREP AH L st X m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => fst iv < snd iv ->
            (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
         \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
         \/ ATOP <= fst iv) W ->
  AREP AH L st X m'.
Proof.

  intros L st X m m' W AL AR MU WM HW. eapply (AREP_frame_ext AH HL); [exact AL| exact AR| exact MU| exact WM|].
  eapply List.Forall_impl; [| exact HW]. cbv beta. intros iv H Hlt.
  destruct (H Hlt) as [A|[A|A]]; [left; exact A| right; left; exact A| right; right; left; exact A].
Qed.

Lemma AREP_cells : forall L st X m, AREP AH L st X m ->
  rt_got m /\ rt_shbase m
  /\ rw_cells asegs m 0xd9320 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xd9324 [C4 (Z_to_bv 64 0)]
  /\ rt_inited m /\ rt_layout m
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
  /\ (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None).
Proof.
  intros L st X m H. pose proof (AREP_relro AH L st X m H) as RR. unfold AREP, arep_rt in H. decompose [and] H.
  repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

Theorem fake_flag_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Proof.
  intros L RNG st LB m cls F N AHP Hin. pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof (afake_lb L LB m cls F N HFK Hin) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR).
  pose proof (afake_flag L LB m cls F N HFK Hin) as FL.
  destruct HFK as (G & _). destruct G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, KHIGH, AIMG_HI in *.
  destruct ARNG as (_ & _ & _ & _ & _ & _ & RF & _).
  split; [exact FL|]. split; [eapply rng_sub'; [exact RF| lia]|]. split; [eapply ablk_sub; [exact G2| lia| lia]|]. split; [lia|]. split.
  - intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    + pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [_ D]. lia.
    + pose proof (afake_lb L LB m c' A' n' (proj2 (proj2 (proj2 AHP))) Hb) as (_ & _ & _ & _ & X1 & X2 & _). lia.
  - intros (iv & Hiv & R). pose proof (CI_OK iv Hiv). lia.
Qed.

Lemma ablocks_tail : forall L st X b LB, ablocks L st X (b :: LB) -> ablocks L st X LB.
Proof.
  intros L st X b LB (H1 & H2 & H3 & H4). split; [|split; [|split]].
  - intros p A n Hin. apply (H1 p A n). right; exact Hin.
  - intros c A n Hin. apply (H2 c A n). right; exact Hin.
  - destruct b as [[p|c] A n]; cbn in H3; [inversion H3; assumption| exact H3].
  - inversion H4; assumption.
Qed.

Theorem fake_release_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP_P AH L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m cls F N AHP. pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof (afake_lb L _ m cls F N HFK ltac:(left; reflexivity)) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR).
  assert (NI : ~ In (mkABlock (ABFake cls) F N) LB) by (destruct BL as (_ & _ & _ & ND); inversion ND; assumption).
  destruct HFK as (G & HFK'). pose proof G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, AIMG_HI in *.
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [| eapply ablocks_tail; exact BL].
    eapply (AREP_frame_ext' _ _ _ _ _ [(fflag L cls F, fflag L cls F + 1)]); [exact ALO| exact AR| | |].
    + apply munch_write; [apply munch_refl| lia| cbn; lia|]. cbn. left. lia.
    + apply wmono_write, wmono_refl.
    + constructor; [|constructor]. cbn. intros _. left. lia.
  - cbn [AH ah_fake]. apply (afake_release L LB m cls F N); [exact (conj G HFK')| exact NI].
Qed.

Notation FB0 F := (mkABlock (ABFake 0) F 64).
Definition SM_STACK : Z := 4096.

Definition sm0_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB0 F :: LB) m'
    /\ F mod 64 = 0 /\ ablk F (F + 64) /\ F + 64 <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 (fflag L 0 F))]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0)]
    /\ rng RNG F 64 /\ rng RNG (shad F) 8.

Lemma relro_word : forall m A v,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b asegs A (le8 (Z_to_bv 64 v)) = true ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
  eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (le8 (Z_to_bv 64 v)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.

Lemma arep_ext_sm0 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AH L st X m ->
  munch [(sp - 208, sp); (fs, fs + 8); (flag, flag + 1); (F + 24, F + 32); (F + 56, F + 64); (2147450880 + F / 8, 2147450880 + F / 8 + 8)] m m' ->
  wmono asegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 64 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 8 <= shad fs + 1446400 ->
  AREP AH L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.

Theorem stack_malloc_0_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  gcbit = false ->
  (forall F n, ~ In (mkABlock (ABFake 0) F n) LB) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm0_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros AHP GCB0 NOFK MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). pose proof NGC as NGCg. rewrite GCB0 in NGC.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd1568 0x169558 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd22a8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0xd2298 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  set (h := bv_unsigned h0). set (pos := Z.land h 16383). set (flag := (al_fake L) + 4096 + pos). set (F := (al_fake L) + 36864 + pos * 64).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 0 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 0 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 0 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 4608 + 8 * pos = shad F /\ shad F + 8 <= shad (al_fake L) + 1446400 /\ shad F + 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  destruct (c1_of_dc m flag D3) as [fb FL0].
  assert (fb = Z_to_bv 8 0) as ->.
  { destruct (decide (fb = Z_to_bv 8 0)) as [E|NE]; [exact E| exfalso].
    apply (NOFK (fk_frame L 0 pos) (fk_fsize 0)). apply (FL 0 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
    rewrite <- EFL. apply (rw_C1_high m flag fb FL0). subst flag. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8_of_dc m _ DS2) as [sh0 SH0].

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells asegs m (al_fake L) [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land h 16383) by reflexivity. assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc0_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60cc80 (al_fake L) h pos flag F j24 j56 sh0 h1 h2 hs);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm0_W in MU. rewrite SHF in MU.

  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) <= a < (al_fake L) + 8) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 56 <= a < F + 64) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 8) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 64 = 0) by (rewrite EFR; apply fk_frame_al64; [exact G1| lia]).

  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm0 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB0 F) LB) by (apply NOFK).
  assert (HFK' : AFAKE L (FB0 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists (Z_to_bv 64 (h + 1)), h1, h2, hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGCg MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
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
    - split; [| xportk TFSC MU WM ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)].
      intros c F' n' [E|Hin].
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

  assert (BL' : ablocks L st X (FB0 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB0 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 64 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (0, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 0) with 64 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 0 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 0) with 64 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 64)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
        D3 D24 D56 DS2 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 24 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 24) with 24%nat in J1.
  assert (LJ : length junk1 = 24%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 32 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 0 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 32 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 24 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 32) with (F + 56) by lia. exact F56'. }

  unfold sm0_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
Qed.

Notation FB2 F := (mkABlock (ABFake 2) F 256).

Definition sm2_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB2 F :: LB) m'
    /\ F mod 256 = 0 /\ ablk F (F + 256) /\ F + 256 <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 (fflag L 2 F))]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 256 /\ rng RNG (shad F) 32.

Lemma arep_ext_sm2 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AH L st X m ->
  munch [(sp - 208, sp); (fs + 16, fs + 24); (flag, flag + 1); (F + 24, F + 32); (F + 248, F + 256); (2147450880 + F / 8, 2147450880 + F / 8 + 32)] m m' ->
  wmono asegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 256 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 32 <= shad fs + 1446400 ->
  AREP AH L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.

Theorem stack_malloc_2_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  gcbit = false ->
  (forall F n, ~ In (mkABlock (ABFake 2) F n) LB) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm2_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros AHP GCB0 NOFK MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). pose proof NGC as NGCg. rewrite GCB0 in NGC.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd1568 0x169558 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd22a8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0xd2298 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  set (h := bv_unsigned h2). set (pos := Z.land h 4095). set (flag := (al_fake L) + 28672 + pos). set (F := (al_fake L) + 2134016 + pos * 256).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 2 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 2 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 2 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 266752 + 32 * pos = shad F /\ shad F + 32 <= shad (al_fake L) + 1446400 /\ shad F + 32 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 32 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  destruct (c1_of_dc m flag D3) as [fb FL0].
  assert (fb = Z_to_bv 8 0) as ->.
  { destruct (decide (fb = Z_to_bv 8 0)) as [E|NE]; [exact E| exfalso].
    apply (NOFK (fk_frame L 2 pos) (fk_fsize 2)). apply (FL 2 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
    rewrite <- EFL. apply (rw_C1_high m flag fb FL0). subst flag. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 216 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 248) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F + 16) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS3.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH0). destruct (c8c8_of_dc m _ DS3) as (sh2 & sh3 & SH1).
  assert (SH4 : rw_cells asegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3]).
  { apply (proj2 (rw_cells_app asegs m (shad F) [C8 sh0; C8 sh1] [C8 sh2; C8 sh3])). split; [exact SH0|].
    cbn [cells_size csize Nat.add]. replace (shad F + Z.of_nat 16) with (shad F + 16) by lia. exact SH1. }

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells asegs m (al_fake L) [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land h 4095) by reflexivity. assert (HFLAG : flag = (al_fake L) + 28672 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 2134016 + pos * 256) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc2_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60cc80 (al_fake L) h pos flag F j24 j56 sh0 sh1 sh2 sh3 h0 h1 hs);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm2_W in MU. rewrite SHF in MU.

  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 16 <= a < (al_fake L) + 24) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 248 <= a < F + 256) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 32) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 256 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (16 * k + 8336 + pos). lia. }

  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm2 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB2 F) LB) by (apply NOFK).
  assert (HFK' : AFAKE L (FB2 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists h0, h1, (Z_to_bv 64 (h + 1)), hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGCg MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 2) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 2 pos' 2 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 2 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - split; [| xportk TFSC MU WM ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)].
      intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 2) with 256 in Hin by reflexivity. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }

  assert (BL' : ablocks L st X (FB2 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB2 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 256 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (2, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 2) with 256 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 2 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 2) with 256 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 256)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
        D3 D24 D56 DS2 DS3 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 216 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 216) with 216%nat in J1.
  assert (LJ : length junk1 = 216%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 224 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 2 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 224 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 216 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 224) with (F + 248) by lia. exact F56'. }

  unfold sm2_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
Qed.
End S.
End CANSEC1.

End AFake_arep.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_cnt.
Module AFake_sm0P.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0g.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AH := (AFake_arep.AH DI AQ ASEC).
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation AREP_cells := (AFake_arep.AREP_cells DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' DI AQ ASEC HL).
Notation arep_ext_sm0 := (AFake_arep.arep_ext_sm0 DI AQ ASEC HL).

Definition sm0_postG (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB0 F :: LB) m'
    /\ F mod 64 = 0 /\ ablk F (F + 64) /\ F + 64 <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 (fflag L 0 F))]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0)]
    /\ rng RNG F 64 /\ rng RNG (shad F) 8
    /\ rw_cells asegs m' (F + 24) [C8 sp].

Theorem stack_malloc_0_GA : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  gcbit = false ->
  Z.of_nat (fk_count 0 LB) < 16384 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm0_postG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros AHP GCB0 NOTFULL MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). pose proof NGC as NGCg. rewrite GCB0 in NGC.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd1568 0x169558 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd22a8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0xd2298 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h0).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (afake_first_free L LB m 0 h HFK NDLB ltac:(unfold FK_NCLS; lia) ltac:(change (fk_nframes 0) with 16384; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 0) with 16384 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 16384 = Z.land x 16383) by (intros x; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 16383). set (flag := (al_fake L) + 4096 + pos). set (F := (al_fake L) + 36864 + pos * 64).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 0 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 0 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 0 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 4608 + 8 * pos = shad F /\ shad F + 8 <= shad (al_fake L) + 1446400 /\ shad F + 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  assert (FL0 : rw_cells asegs m flag [C1 (Z_to_bv 8 0)]).
  { rewrite EFL. unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> exists b : byte, rw_cells asegs m (sm0_flag (al_fake L) (h + t)) [C1 b] /\ bv_unsigned b <> 0).
  { intros t Ht. rewrite EJ in Ht. destruct (BUSYz t Ht) as (b & Cb & NZb). exists b. split; [| exact NZb].
    unfold sm0_flag. rewrite <- LM. unfold fk_flag, fk_flags in Cb. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub] in Cb.
    eapply rw_cells_at_eq; [exact Cb| lia]. }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 0) F 64) LB).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8_of_dc m _ DS2) as [sh0 SH0].

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells asegs m (al_fake L) [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 16383) by reflexivity. assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
  assert (JB : Z.of_nat jn < 16384) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  eapply evtF_mono.
  { eapply (stack_malloc0_gspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60cc80 (al_fake L) h pos flag F jn j24 j56 sh0 h1 h2 hs);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm0_W in MU. rewrite SHF in MU.

  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) <= a < (al_fake L) + 8) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 56 <= a < F + 64) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 8) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 64 = 0) by (rewrite EFR; apply fk_frame_al64; [exact G1| lia]).

  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm0 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB0 F) LB) by exact NOTIN0.
  assert (HFK' : AFAKE L (FB0 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists (Z_to_bv 64 (h + Z.of_nat jn + 1)), h1, h2, hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGCg MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
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
    - split; [| xportk TFSC MU WM ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)].
      intros c F' n' [E|Hin].
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

  assert (BL' : ablocks L st X (FB0 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB0 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 64 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (0, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 0) with 64 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 0 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 0) with 64 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 64)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
        D3 D24 D56 DS2 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 24 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 24) with 24%nat in J1.
  assert (LJ : length junk1 = 24%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 32 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 0 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 32 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 24 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 32) with (F + 56) by lia. exact F56'. }

  unfold sm0_postG. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm0P.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_gc AFake_gcl AFake_gcf.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_gcP.
Module AFake_sm0PB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2gc.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcP.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHt := (AFake_arep.AH (gb:=true) DI AQ ASEC).
Notation AHf := (AFake_arep.AH (gb:=false) DI AQ ASEC).
Hypothesis HLt : ahole_laws AHt.
Notation AH := AHt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation AREP_cells := (AFake_arep.AREP_cells (gb:=true) DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE (gb:=true) DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' (gb:=true) DI AQ ASEC HLt).

Definition sm0_postGB (rsf : Z -> Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m'
    /\ AHEAP_P AHf L RNG st (FB0 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m'
    /\ F mod 64 = 0 /\ ablk F (F + 64) /\ F + 64 <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 (fflag L 0 F))]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0)]
    /\ rng RNG F 64 /\ rng RNG (shad F) 8
    /\ rw_cells asegs m' (F + 24) [C8 sp].

Theorem stack_malloc_0_GB : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (rsf : Z -> Z),
  AHEAP_P AH L RNG st LB m ->
  Z.of_nat (fk_count 0 LB) < 16384 ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> c <= 2) ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> 0 <= rsf F < 2^64 /\ rw_cells asegs m (F + 24) [C8 (Z_to_bv 64 (rsf F))]) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm0_postGB rsf L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Proof.
  intros until rsf. intros AHP NOTFULL CLS RS MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). change (rw_cells asegs m (al_fake L + 96) [C1 (Z_to_bv 8 1)]) in NGC. pose proof NGC as NGCg.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd1568 0x169558 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd22a8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0xd2298 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h0).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (gc_probe L LB m rsf (al_bot L) (bv_unsigned sp) HFK NDLB 0 h ltac:(lia) ltac:(change (fk_nframes 0) with 16384; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 0) with 16384 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 16384 = Z.land x 16383) by (intros x; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 16383). set (flag := (al_fake L) + 4096 + pos). set (F := (al_fake L) + 36864 + pos * 64).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 0 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 0 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 0 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 4608 + 8 * pos = shad F /\ shad F + 8 <= shad (al_fake L) + 1446400 /\ shad F + 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  pose proof I as FL0.
  assert (FREEc : gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 pos = Z_to_bv 8 0).
  { unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> bv_unsigned (gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 (Z.land (h + t) 16383)) <> 0).
  { intros t Ht. rewrite EJ in Ht. rewrite <- LM. exact (BUSYz t Ht). }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 0) F 64) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  assert (TBND : rw_cells asegs m (al_t L + 8) [C8 (Z_to_bv 64 (al_top L)); C8 (Z_to_bv 64 (al_bot L))] /\ rw_cells asegs m (al_t L + 40) [C1 (Z_to_bv 8 0)]).
  { pose proof AR as ARx. destruct ARx as (_ & _ & _ & THRx & _). destruct THRx as (T0x & T40x & _). split; [| exact T40x].
    rw_split T0x 1%nat T0a T0b. exact T0b. }
  destruct TBND as [TB8 TB40].

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8_of_dc m _ DS2) as [sh0 SH0].

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells asegs m (al_fake L) [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 16383) by reflexivity. assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
  assert (JB : Z.of_nat jn < 16384) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  pose proof (gfl_cell L LB m HFK) as GFLC. pose proof (grs_cell L LB m rsf HFK RS) as GRSC. pose proof (gfreed_shadow L LB m rsf (al_bot L) (bv_unsigned sp) HFK CLS) as GSHC.
  eapply evtF_mono.
  { eapply (stack_malloc0_gcspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60cc80 (al_fake L) h pos flag F (al_top L) (al_bot L) jn (Z_to_bv 8 1) (gfl L m) (grs L rsf) j24 j56 sh0 h1 h2 hs);
      try exact MI; try exact ST; try exact TP; try exact GFLC; try exact GRSC; try exact GSHC; try exact BUSYc; try exact FREEc; try exact TB8; try exact TB40;
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia); try (cbn; discriminate).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & NGC' & HNT2 & FL1 & F24' & F56' & SH' & FLAGS').
  unfold sm0gc_W in MU.

  assert (SHH : 0x7fff8000 <= shad (al_fake L + 36864) /\ shad (al_fake L + 11571200) <= 0x10007fff8000
                /\ shad (al_fake L + 11571200) = shad (al_fake L) + 1446400 /\ shad (al_fake L) <= shad (al_fake L + 36864)).
  { rewrite !gc_shad_eq. pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. clear - G1 G2c G3 ATR. Z.div_mod_to_equations. lia. }
  destruct SHH as (SHH1 & SHH2 & SHH3 & SHH4).
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 240 <= a < bv_unsigned sp) -> ~ (al_fake L <= a < al_fake L + 4096) -> a <> flag ->
            ~ (F <= a < F + 64) -> ~ (shad F <= a < shad F + 8) ->
            disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) a 1 ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 DG. apply MU. rewrite wa_unsigned by lia. cbn [outside].
    repeat (split; [lia|]). eapply disjoint_outside; [exact DG| lia]. }
  assert (DGH : forall A k, 0 <= k -> (A + k <= al_fake L + 4096 \/ al_fake L + 36864 <= A) ->
            (A + k <= shad (al_fake L + 36864) \/ shad (al_fake L + 11571200) <= A) -> disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) A k)
    by (intros A k K H1 H2; apply gcWall_disj_hulls; assumption).
  assert (F64 : F mod 64 = 0) by (rewrite EFR; apply fk_frame_al64; [exact G1| lia]).

  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
  pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c.
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext AH HLt L st X m m' _ ALO AR MU WM). assert (SHLx : shlen 11571200 = 1446400) by reflexivity.
    lazymatch goal with |- Forall _ ?W => change (Forall (aext L) W) end.
    repeat (apply Forall_cons; [unfold aext; rewrite ?SHLx; cbn [fst snd]; intros _;
      first [left; clear -HFLAG HFF PB; lia | right; left; clear -SB1 SB2 SB3 PB; lia | right; right; left; clear -BOT LO; lia]|]).
    exact (gcWall_aext L (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 G1). }
  assert (NOTIN : ~ In (FB0 F) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) by exact NOTIN0.
  Local Ltac xportG H MU WM DGH K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length];
      repeat (split; [first [K; lia | lia]|]); apply DGH; first [K; lia | lia]].
  assert (CE' : afake_cells L m').
  { unfold afake_cells. split; [xportG REAL MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTVP MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DV MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTV1 MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|].
    split; [xportG BD MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG CF MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG VERB MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
  assert (LOG' : rw_cells asegs m' (al_fake L + 88) [C8 (Z_to_bv 64 20)]) by (xportG LOG MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)).
  assert (HFK' : AFAKE (gb:=false) L (FB0 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { rewrite EFR. change 64 with (fk_fsize 0).
    eapply (afake_after_gc L LB m rsf (al_bot L) (bv_unsigned sp)) with (c0 := 0) (pos0 := pos).
    all: try lazymatch goal with
         | |- AFAKE _ _ _ => exact HFK
         | |- wmono _ _ _ => exact WM
         | |- afake_cells _ _ => exact CE'
         | |- rw_cells _ _ (_ + 88) _ => exact LOG'
         | |- rw_cells _ _ (_ + 96) _ => exact NGC'
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; CB 64 _] => exact HNT2
         | |- rw_cells _ _ (fk_flag _ _ _) _ => rewrite <- EFL; exact FL1
         | |- ~ In _ _ => rewrite <- EFR; exact NOTIN
         | |- rw_cells _ _ (_ + 72) _ => xportG TFSC MU WM DGH ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)
         | |- forall c p, _ => intros c' p' Hc' Hp' NE'; apply FLAGS'; [exact Hc'| exact Hp'|]; intros E'; apply NE'; rewrite E'; f_equal; rewrite HFLAG; lia
         end.
    all: try (change (gcN 0) with 16384; lia). all: try lia. }

  assert (BL' : ablocks L st X (FB0 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate|]. apply fk_kept_In in Hin as [Hin _]. exact (B1 p A n Hin).
    - intros c' A n [E|Hin]; [| apply fk_kept_In in Hin as [Hin _]; exact (B2 c' A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - change (List.NoDup (hb_ids (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))). rewrite fk_kept_hb_ids. exact B3.
    - constructor; [exact NOTIN| apply fk_kept_NoDup; exact B4]. }
  assert (AHP' : AHEAP_P AHf L RNG st (FB0 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 64 <= ab_addr b)).
  { intros b HbK. pose proof (proj1 (proj1 (fk_kept_In LB rsf (al_bot L) (bv_unsigned sp) b) HbK)) as Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (0, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in HbK. replace (fk_fsize 0) with 64 in HbK by reflexivity. exact HbK. }
      pose proof (fk_frames_disjoint L c' pos' 0 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 0) with 64 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 64)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
        D3 D24 D56 DS2 RR A10.
  assert (HPR : aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m').
  { assert (SHFLO : 2147450880 <= shad F) by (rewrite SHF; clear - GL1 HFF PB; Z.div_mod_to_equations; lia).
    intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; [exact Ha| clear - Hs; lia| clear - Hs G3 BOT LO; lia| clear - Hs G3 BOT LO HFLAG PB; lia| clear - Hs G3 BOT LO HFF PB; lia| clear - Hs SB3 BOT LO ATR; lia
                 | apply DGH; [lia| right; clear - Hs G3 BOT LO; lia| right; clear - Hs SHH2 BOT LO ATR; lia]].
    - pose proof (CI_OK iv Hiv) as HCI.
      apply OUT; [exact Ha| clear - HCI Hr BOT LO ATR; lia| clear - HCI Hr GL1; lia| clear - HCI Hr GL1 HFLAG PB; lia| clear - HCI Hr GL1 HFF PB; lia| clear - HCI Hr SHFLO; lia
                 | apply DGH; [lia| left; clear - HCI Hr GL1; lia| left; clear - HCI Hr SHH1; lia]].
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1.
      apply OUT; [exact Ha| clear - Hr Y2 BOT LO; lia| clear - Hr Y3; lia| clear - Hr Y3 HFLAG PB; lia| clear - Hr Y4; lia| clear - Hr Y1 SHFLO SB3; lia
                 | apply DGH; [lia| clear - Hr Y3; lia| clear - Hr Y1 SHH1 SHH2; lia]].
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      assert (F8 : F mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
      apply OUT; [lia| rewrite SHA; clear - A'R ATR LO BOT; lia| rewrite SHA; clear - A'R G2c; lia| rewrite SHA, HFLAG; clear - A'R G2c PB; lia
                 | rewrite SHA; clear - A'R G2c G3 HFF PB; lia| rewrite SHA, SHF; clear - A'R NA F8; Z.div_mod_to_equations; lia|].
      destruct Ha' as [SA|[(iv & Hiv & Hr)|(cls & FA & fn & HbK & Hr)]].
      + apply DGH; [lia| rewrite SHA; clear - SA ATR G2c G3; lia|]. right. rewrite SHA, gc_shad_eq. clear - SA G3. Z.div_mod_to_equations. lia.
      + pose proof (CI_OK iv Hiv). apply DGH; [lia| rewrite SHA; clear - A'R G2c; lia|]. left. rewrite SHA, gc_shad_eq. clear - H Hr GL1. unfold AIMG_HI in *. Z.div_mod_to_equations. lia.
      + apply fk_kept_In in HbK as [HbL ALIVE].
        pose proof (afake_lb L LB m cls FA fn HFK HbL) as (Hc' & Hn' & Np' & F64' & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
        pose proof HFK as (_ & _ & _ & _ & _ & _ & _ & _ & LVx & _). destruct (LVx _ _ _ HbL) as (_ & _ & pos2 & Hp2 & HF2 & B1x).
        assert (pos2 = pos') by (apply (fk_frame_inj L cls); [lia| congruence]). subst pos2.
        assert (E1 : gfl L m cls pos' = Z_to_bv 8 1) by (unfold gfl; rewrite B1x; reflexivity).
        assert (NF : gfreed (al_bot L) (bv_unsigned sp) (gfl L m cls pos') (grs L rsf cls pos') = false).
        { rewrite (gfreed_dead L m rsf (al_bot L) (bv_unsigned sp) cls pos' Hc' Hp') by (rewrite E1; discriminate). rewrite <- HF', <- Hn'. exact ALIVE. }
        pose proof (gc_pows cls Hc') as (_ & _ & _ & _ & P8 & PC). unfold fk_fsize in Hn'.
        eapply (gcWall_disj_kept_shadow (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 cls pos'); [exact Hc'| exact Hp'| exact NF| | | lia].
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. clear - Hr. Z.div_mod_to_equations. lia.
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. remember (2 ^ cls) as K. clear - Hr Hn' P8 PC F64'. Z.div_mod_to_equations. lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 24 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 24) with 24%nat in J1.
  assert (LJ : length junk1 = 24%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 32 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 0 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 32 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 24 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 32) with (F + 56) by lia. exact F56'. }

  unfold sm0_postGB. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm0PB.

Module AFake_sm1P.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm1g.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AH := (AFake_arep.AH DI AQ ASEC).
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Notation AREP_cells := (AFake_arep.AREP_cells DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' DI AQ ASEC HL).
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].

Definition sm1_postG (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB1 F :: LB) m'
    /\ F mod 128 = 0 /\ ablk F (F + 128) /\ F + 128 <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F))]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 128 /\ rng RNG (shad F) 16
    /\ rw_cells asegs m' (F + 24) [C8 sp].

Lemma arep_ext_sm1 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AH L st X m ->
  munch [(sp - 208, sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128); (2147450880 + F / 8, 2147450880 + F / 8 + 16)] m m' ->
  wmono asegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 128 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 16 <= shad fs + 1446400 ->
  AREP AH L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.

Theorem stack_malloc_1_GA : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  gcbit = false ->
  Z.of_nat (fk_count 1 LB) < 8192 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm1_postG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros AHP GCB0 NOTFULL MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). pose proof NGC as NGCg. rewrite GCB0 in NGC.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd1568 0x169558 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd22a8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0xd2298 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h1).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (afake_first_free L LB m 1 h HFK NDLB ltac:(unfold FK_NCLS; lia) ltac:(change (fk_nframes 1) with 8192; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 1) with 8192 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 8192 = Z.land x 8191) by (intros x; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 8191). set (flag := (al_fake L) + 20480 + pos). set (F := (al_fake L) + 1085440 + pos * 128).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 8192).
  { subst pos. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 1 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 1 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 1 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 135680 + 16 * pos = shad F /\ shad F + 16 <= shad (al_fake L) + 1446400 /\ shad F + 16 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 16 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  assert (FL0 : rw_cells asegs m flag [C1 (Z_to_bv 8 0)]).
  { rewrite EFL. unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> exists b : byte, rw_cells asegs m (sm1_flag (al_fake L) (h + t)) [C1 b] /\ bv_unsigned b <> 0).
  { intros t Ht. rewrite EJ in Ht. destruct (BUSYz t Ht) as (b & Cb & NZb). exists b. split; [| exact NZb].
    unfold sm1_flag. rewrite <- LM. unfold fk_flag, fk_flags in Cb. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub] in Cb.
    eapply rw_cells_at_eq; [exact Cb| lia]. }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 1) F 128) LB).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 88 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 120) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH4). pose proof SH4 as SH0. pose proof SH4 as SH1. pose proof DS2 as DS3.

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells asegs m (al_fake L) [C8 h0; C8 (Z_to_bv 64 h); C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 8191) by reflexivity. assert (HFLAG : flag = (al_fake L) + 20480 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 1085440 + pos * 128) by reflexivity.
  assert (JB : Z.of_nat jn < 8192) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  eapply evtF_mono.
  { eapply (stack_malloc1_gspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60cc80 (al_fake L) h pos flag F jn j24 j56 sh0 sh1 h0 h2 hs);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm1_W in MU. rewrite SHF in MU.

  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 8 <= a < (al_fake L) + 16) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 120 <= a < F + 128) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 16) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 128 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (32 * k + 8480 + pos). lia. }

  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm1 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB1 F) LB) by exact NOTIN0.
  assert (HFK' : AFAKE L (FB1 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists h0, (Z_to_bv 64 (h + Z.of_nat jn + 1)), h2, hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGCg MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 1) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 1 pos' 1 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 1 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 1 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - split; [| xportk TFSC MU WM ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)].
      intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 1 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 1) with 128 in Hin by reflexivity. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }

  assert (BL' : ablocks L st X (FB1 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB1 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 128 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (1, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 1) with 128 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 1 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 1) with 128 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 128)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
        D3 D24 D56 DS2 DS3 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 88 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 88) with 88%nat in J1.
  assert (LJ : length junk1 = 88%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 96 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 1 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 96 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 88 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 96) with (F + 120) by lia. exact F56'. }

  unfold sm1_postG. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm1P.

Module AFake_sm1PB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm1g. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2gc.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm1gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcP.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHt := (AFake_arep.AH (gb:=true) DI AQ ASEC).
Notation AHf := (AFake_arep.AH (gb:=false) DI AQ ASEC).
Hypothesis HLt : ahole_laws AHt.
Notation AH := AHt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Notation AREP_cells := (AFake_arep.AREP_cells (gb:=true) DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE (gb:=true) DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' (gb:=true) DI AQ ASEC HLt).
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].

Definition sm1_postGB (rsf : Z -> Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m'
    /\ AHEAP_P AHf L RNG st (FB1 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m'
    /\ F mod 128 = 0 /\ ablk F (F + 128) /\ F + 128 <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F))]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 128 /\ rng RNG (shad F) 16
    /\ rw_cells asegs m' (F + 24) [C8 sp].

Theorem stack_malloc_1_GB : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (rsf : Z -> Z),
  AHEAP_P AH L RNG st LB m ->
  Z.of_nat (fk_count 1 LB) < 8192 ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> c <= 2) ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> 0 <= rsf F < 2^64 /\ rw_cells asegs m (F + 24) [C8 (Z_to_bv 64 (rsf F))]) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm1_postGB rsf L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom asegs)).
Proof.
  intros until rsf. intros AHP NOTFULL CLS RS MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). change (rw_cells asegs m (al_fake L + 96) [C1 (Z_to_bv 8 1)]) in NGC. pose proof NGC as NGCg.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd1568 0x169558 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd22a8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0xd2298 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h1).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (gc_probe L LB m rsf (al_bot L) (bv_unsigned sp) HFK NDLB 1 h ltac:(lia) ltac:(change (fk_nframes 1) with 8192; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 1) with 8192 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 8192 = Z.land x 8191) by (intros x; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 8191). set (flag := (al_fake L) + 20480 + pos). set (F := (al_fake L) + 1085440 + pos * 128).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 8192).
  { subst pos. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 1 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 1 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 1 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 135680 + 16 * pos = shad F /\ shad F + 16 <= shad (al_fake L) + 1446400 /\ shad F + 16 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 16 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  pose proof I as FL0.
  assert (FREEc : gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 1 pos = Z_to_bv 8 0).
  { unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> bv_unsigned (gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 1 (Z.land (h + t) 8191)) <> 0).
  { intros t Ht. rewrite EJ in Ht. rewrite <- LM. exact (BUSYz t Ht). }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 1) F 128) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  assert (TBND : rw_cells asegs m (al_t L + 8) [C8 (Z_to_bv 64 (al_top L)); C8 (Z_to_bv 64 (al_bot L))] /\ rw_cells asegs m (al_t L + 40) [C1 (Z_to_bv 8 0)]).
  { pose proof AR as ARx. destruct ARx as (_ & _ & _ & THRx & _). destruct THRx as (T0x & T40x & _). split; [| exact T40x].
    rw_split T0x 1%nat T0a T0b. exact T0b. }
  destruct TBND as [TB8 TB40].

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 88 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 120) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH4). pose proof SH4 as SH0. pose proof SH4 as SH1. pose proof DS2 as DS3.

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells asegs m (al_fake L) [C8 h0; C8 (Z_to_bv 64 h); C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 8191) by reflexivity. assert (HFLAG : flag = (al_fake L) + 20480 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 1085440 + pos * 128) by reflexivity.
  assert (JB : Z.of_nat jn < 8192) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  pose proof (gfl_cell L LB m HFK) as GFLC. pose proof (grs_cell L LB m rsf HFK RS) as GRSC. pose proof (gfreed_shadow L LB m rsf (al_bot L) (bv_unsigned sp) HFK CLS) as GSHC.
  eapply evtF_mono.
  { eapply (stack_malloc1_gcspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60cc80 (al_fake L) h pos flag F (al_top L) (al_bot L) jn (Z_to_bv 8 1) (gfl L m) (grs L rsf) j24 j56 sh0 sh1 h0 h2 hs);
      try exact MI; try exact ST; try exact TP; try exact GFLC; try exact GRSC; try exact GSHC; try exact BUSYc; try exact FREEc; try exact TB8; try exact TB40;
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia); try (cbn; discriminate).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & NGC' & HNT2 & FL1 & F24' & F56' & SH' & FLAGS').
  unfold sm1gc_W in MU.

  assert (SHH : 0x7fff8000 <= shad (al_fake L + 36864) /\ shad (al_fake L + 11571200) <= 0x10007fff8000
                /\ shad (al_fake L + 11571200) = shad (al_fake L) + 1446400 /\ shad (al_fake L) <= shad (al_fake L + 36864)).
  { rewrite !gc_shad_eq. pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. clear - G1 G2c G3 ATR. Z.div_mod_to_equations. lia. }
  destruct SHH as (SHH1 & SHH2 & SHH3 & SHH4).
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 240 <= a < bv_unsigned sp) -> ~ (al_fake L <= a < al_fake L + 4096) -> a <> flag ->
            ~ (F <= a < F + 128) -> ~ (shad F <= a < shad F + 16) ->
            disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) a 1 ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 DG. apply MU. rewrite wa_unsigned by lia. cbn [outside].
    repeat (split; [lia|]). eapply disjoint_outside; [exact DG| lia]. }
  assert (DGH : forall A k, 0 <= k -> (A + k <= al_fake L + 4096 \/ al_fake L + 36864 <= A) ->
            (A + k <= shad (al_fake L + 36864) \/ shad (al_fake L + 11571200) <= A) -> disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) A k)
    by (intros A k K H1 H2; apply gcWall_disj_hulls; assumption).
  assert (F64 : F mod 128 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (32 * k + 8480 + pos). lia. }

  pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c.
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext AH HLt L st X m m' _ ALO AR MU WM). assert (SHLx : shlen 11571200 = 1446400) by reflexivity.
    lazymatch goal with |- Forall _ ?W => change (Forall (aext L) W) end.
    repeat (apply Forall_cons; [unfold aext; rewrite ?SHLx; cbn [fst snd]; intros _;
      first [left; clear -HFLAG HFF PB; lia | right; left; clear -SB1 SB2 SB3 PB; lia | right; right; left; clear -BOT LO; lia]|]).
    exact (gcWall_aext L (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 G1). }
  assert (NOTIN : ~ In (FB1 F) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) by exact NOTIN0.
  Local Ltac xportG H MU WM DGH K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length];
      repeat (split; [first [K; lia | lia]|]); apply DGH; first [K; lia | lia]].
  assert (CE' : afake_cells L m').
  { unfold afake_cells. split; [xportG REAL MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTVP MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DV MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTV1 MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|].
    split; [xportG BD MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG CF MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG VERB MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
  assert (LOG' : rw_cells asegs m' (al_fake L + 88) [C8 (Z_to_bv 64 20)]) by (xportG LOG MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)).
  assert (HFK' : AFAKE (gb:=false) L (FB1 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { rewrite EFR. change 128 with (fk_fsize 1).
    eapply (afake_after_gc L LB m rsf (al_bot L) (bv_unsigned sp)) with (c0 := 1) (pos0 := pos).
    all: try lazymatch goal with
         | |- AFAKE _ _ _ => exact HFK
         | |- wmono _ _ _ => exact WM
         | |- afake_cells _ _ => exact CE'
         | |- rw_cells _ _ (_ + 88) _ => exact LOG'
         | |- rw_cells _ _ (_ + 96) _ => exact NGC'
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; CB 64 _] => exact HNT2
         | |- rw_cells _ _ (fk_flag _ _ _) _ => rewrite <- EFL; exact FL1
         | |- ~ In _ _ => rewrite <- EFR; exact NOTIN
         | |- rw_cells _ _ (_ + 72) _ => xportG TFSC MU WM DGH ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)
         | |- forall c p, _ => intros c' p' Hc' Hp' NE'; apply FLAGS'; [exact Hc'| exact Hp'|]; intros E'; apply NE'; rewrite E'; f_equal; rewrite HFLAG; lia
         end.
    all: try (change (gcN 1) with 8192; lia). all: try lia. }

  assert (BL' : ablocks L st X (FB1 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate|]. apply fk_kept_In in Hin as [Hin _]. exact (B1 p A n Hin).
    - intros c' A n [E|Hin]; [| apply fk_kept_In in Hin as [Hin _]; exact (B2 c' A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - change (List.NoDup (hb_ids (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))). rewrite fk_kept_hb_ids. exact B3.
    - constructor; [exact NOTIN| apply fk_kept_NoDup; exact B4]. }
  assert (AHP' : AHEAP_P AHf L RNG st (FB1 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 128 <= ab_addr b)).
  { intros b HbK. pose proof (proj1 (proj1 (fk_kept_In LB rsf (al_bot L) (bv_unsigned sp) b) HbK)) as Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (1, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in HbK. replace (fk_fsize 1) with 128 in HbK by reflexivity. exact HbK. }
      pose proof (fk_frames_disjoint L c' pos' 1 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 1) with 128 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 128)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
        D3 D24 D56 DS2 DS3 RR A10.
  assert (HPR : aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m').
  { assert (SHFLO : 2147450880 <= shad F) by (rewrite SHF; clear - GL1 HFF PB; Z.div_mod_to_equations; lia).
    intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; [exact Ha| clear - Hs; lia| clear - Hs G3 BOT LO; lia| clear - Hs G3 BOT LO HFLAG PB; lia| clear - Hs G3 BOT LO HFF PB; lia| clear - Hs SB3 BOT LO ATR; lia
                 | apply DGH; [lia| right; clear - Hs G3 BOT LO; lia| right; clear - Hs SHH2 BOT LO ATR; lia]].
    - pose proof (CI_OK iv Hiv) as HCI.
      apply OUT; [exact Ha| clear - HCI Hr BOT LO ATR; lia| clear - HCI Hr GL1; lia| clear - HCI Hr GL1 HFLAG PB; lia| clear - HCI Hr GL1 HFF PB; lia| clear - HCI Hr SHFLO; lia
                 | apply DGH; [lia| left; clear - HCI Hr GL1; lia| left; clear - HCI Hr SHH1; lia]].
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1.
      apply OUT; [exact Ha| clear - Hr Y2 BOT LO; lia| clear - Hr Y3; lia| clear - Hr Y3 HFLAG PB; lia| clear - Hr Y4; lia| clear - Hr Y1 SHFLO SB3; lia
                 | apply DGH; [lia| clear - Hr Y3; lia| clear - Hr Y1 SHH1 SHH2; lia]].
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      assert (F8 : F mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
      apply OUT; [lia| rewrite SHA; clear - A'R ATR LO BOT; lia| rewrite SHA; clear - A'R G2c; lia| rewrite SHA, HFLAG; clear - A'R G2c PB; lia
                 | rewrite SHA; clear - A'R G2c G3 HFF PB; lia| rewrite SHA, SHF; clear - A'R NA F8; Z.div_mod_to_equations; lia|].
      destruct Ha' as [SA|[(iv & Hiv & Hr)|(cls & FA & fn & HbK & Hr)]].
      + apply DGH; [lia| rewrite SHA; clear - SA ATR G2c G3; lia|]. right. rewrite SHA, gc_shad_eq. clear - SA G3. Z.div_mod_to_equations. lia.
      + pose proof (CI_OK iv Hiv). apply DGH; [lia| rewrite SHA; clear - A'R G2c; lia|]. left. rewrite SHA, gc_shad_eq. clear - H Hr GL1. unfold AIMG_HI in *. Z.div_mod_to_equations. lia.
      + apply fk_kept_In in HbK as [HbL ALIVE].
        pose proof (afake_lb L LB m cls FA fn HFK HbL) as (Hc' & Hn' & Np' & F64' & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
        pose proof HFK as (_ & _ & _ & _ & _ & _ & _ & _ & LVx & _). destruct (LVx _ _ _ HbL) as (_ & _ & pos2 & Hp2 & HF2 & B1x).
        assert (pos2 = pos') by (apply (fk_frame_inj L cls); [lia| congruence]). subst pos2.
        assert (E1 : gfl L m cls pos' = Z_to_bv 8 1) by (unfold gfl; rewrite B1x; reflexivity).
        assert (NF : gfreed (al_bot L) (bv_unsigned sp) (gfl L m cls pos') (grs L rsf cls pos') = false).
        { rewrite (gfreed_dead L m rsf (al_bot L) (bv_unsigned sp) cls pos' Hc' Hp') by (rewrite E1; discriminate). rewrite <- HF', <- Hn'. exact ALIVE. }
        pose proof (gc_pows cls Hc') as (_ & _ & _ & _ & P8 & PC). unfold fk_fsize in Hn'.
        eapply (gcWall_disj_kept_shadow (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 cls pos'); [exact Hc'| exact Hp'| exact NF| | | lia].
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. clear - Hr. Z.div_mod_to_equations. lia.
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. remember (2 ^ cls) as K. clear - Hr Hn' P8 PC F64'. Z.div_mod_to_equations. lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 88 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 88) with 88%nat in J1.
  assert (LJ : length junk1 = 88%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 96 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 1 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 96 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 88 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 96) with (F + 120) by lia. exact F56'. }

  unfold sm1_postGB. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm1PB.

Module AFake_sm2P.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2g.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AH := (AFake_arep.AH DI AQ ASEC).
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation AREP_cells := (AFake_arep.AREP_cells DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' DI AQ ASEC HL).
Notation arep_ext_sm2 := (AFake_arep.arep_ext_sm2 DI AQ ASEC HL).
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].

Definition sm2_postG (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB2 F :: LB) m'
    /\ F mod 256 = 0 /\ ablk F (F + 256) /\ F + 256 <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 (fflag L 2 F))]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 256 /\ rng RNG (shad F) 32
    /\ rw_cells asegs m' (F + 24) [C8 sp].

Theorem stack_malloc_2_GA : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  gcbit = false ->
  Z.of_nat (fk_count 2 LB) < 4096 ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm2_postG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros AHP GCB0 NOTFULL MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). pose proof NGC as NGCg. rewrite GCB0 in NGC.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd1568 0x169558 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd22a8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0xd2298 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h2).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (afake_first_free L LB m 2 h HFK NDLB ltac:(unfold FK_NCLS; lia) ltac:(change (fk_nframes 2) with 4096; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 2) with 4096 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 4096 = Z.land x 4095) by (intros x; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 4095). set (flag := (al_fake L) + 28672 + pos). set (F := (al_fake L) + 2134016 + pos * 256).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 2 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 2 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 2 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 266752 + 32 * pos = shad F /\ shad F + 32 <= shad (al_fake L) + 1446400 /\ shad F + 32 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 32 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  assert (FL0 : rw_cells asegs m flag [C1 (Z_to_bv 8 0)]).
  { rewrite EFL. unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> exists b : byte, rw_cells asegs m (sm2_flag (al_fake L) (h + t)) [C1 b] /\ bv_unsigned b <> 0).
  { intros t Ht. rewrite EJ in Ht. destruct (BUSYz t Ht) as (b & Cb & NZb). exists b. split; [| exact NZb].
    unfold sm2_flag. rewrite <- LM. unfold fk_flag, fk_flags in Cb. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub] in Cb.
    eapply rw_cells_at_eq; [exact Cb| lia]. }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 2) F 256) LB).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 216 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 248) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F + 16) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS3.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH0). destruct (c8c8_of_dc m _ DS3) as (sh2 & sh3 & SH1).
  assert (SH4 : rw_cells asegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3]).
  { apply (proj2 (rw_cells_app asegs m (shad F) [C8 sh0; C8 sh1] [C8 sh2; C8 sh3])). split; [exact SH0|].
    cbn [cells_size csize Nat.add]. replace (shad F + Z.of_nat 16) with (shad F + 16) by lia. exact SH1. }

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells asegs m (al_fake L) [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 4095) by reflexivity. assert (HFLAG : flag = (al_fake L) + 28672 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 2134016 + pos * 256) by reflexivity.
  assert (JB : Z.of_nat jn < 4096) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  eapply evtF_mono.
  { eapply (stack_malloc2_gspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60cc80 (al_fake L) h pos flag F jn j24 j56 sh0 sh1 sh2 sh3 h0 h1 hs);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm2_W in MU. rewrite SHF in MU.

  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 16 <= a < (al_fake L) + 24) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 248 <= a < F + 256) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 32) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 256 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (16 * k + 8336 + pos). lia. }

  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm2 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB2 F) LB) by exact NOTIN0.
  assert (HFK' : AFAKE L (FB2 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists h0, h1, (Z_to_bv 64 (h + Z.of_nat jn + 1)), hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGCg MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 2) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 2 pos' 2 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 2 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - split; [| xportk TFSC MU WM ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)].
      intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 2) with 256 in Hin by reflexivity. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }

  assert (BL' : ablocks L st X (FB2 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB2 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 256 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (2, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 2) with 256 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 2 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 2) with 256 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 256)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
        D3 D24 D56 DS2 DS3 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 216 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 216) with 216%nat in J1.
  assert (LJ : length junk1 = 216%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 224 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 2 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 224 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 216 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 224) with (F + 248) by lia. exact F56'. }

  unfold sm2_postG. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm2P.

Module AFake_sm2PB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2gc.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcP.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHt := (AFake_arep.AH (gb:=true) DI AQ ASEC).
Notation AHf := (AFake_arep.AH (gb:=false) DI AQ ASEC).
Hypothesis HLt : ahole_laws AHt.
Notation AH := AHt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation AREP_cells := (AFake_arep.AREP_cells (gb:=true) DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE (gb:=true) DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' (gb:=true) DI AQ ASEC HLt).
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].

Definition sm2_postGB (rsf : Z -> Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m'
    /\ AHEAP_P AHf L RNG st (FB2 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m'
    /\ F mod 256 = 0 /\ ablk F (F + 256) /\ F + 256 <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 (fflag L 2 F))]
    /\ rw_cells asegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 256 /\ rng RNG (shad F) 32
    /\ rw_cells asegs m' (F + 24) [C8 sp].

Theorem stack_malloc_2_GB : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (rsf : Z -> Z),
  AHEAP_P AH L RNG st LB m ->
  Z.of_nat (fk_count 2 LB) < 4096 ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> c <= 2) ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> 0 <= rsf F < 2^64 /\ rw_cells asegs m (F + 24) [C8 (Z_to_bv 64 (rsf F))]) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF asegs RNG (sm2_postGB rsf L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom asegs)).
Proof.
  intros until rsf. intros AHP NOTFULL CLS RS MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). change (rw_cells asegs m (al_fake L + 96) [C1 (Z_to_bv 8 1)]) in NGC. pose proof NGC as NGCg.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd1568 0x169558 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd22a8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0xd2298 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h2).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (gc_probe L LB m rsf (al_bot L) (bv_unsigned sp) HFK NDLB 2 h ltac:(lia) ltac:(change (fk_nframes 2) with 4096; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 2) with 4096 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 4096 = Z.land x 4095) by (intros x; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 4095). set (flag := (al_fake L) + 28672 + pos). set (F := (al_fake L) + 2134016 + pos * 256).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 2 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 2 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 2 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 266752 + 32 * pos = shad F /\ shad F + 32 <= shad (al_fake L) + 1446400 /\ shad F + 32 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 32 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  pose proof I as FL0.
  assert (FREEc : gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 2 pos = Z_to_bv 8 0).
  { unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> bv_unsigned (gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 2 (Z.land (h + t) 4095)) <> 0).
  { intros t Ht. rewrite EJ in Ht. rewrite <- LM. exact (BUSYz t Ht). }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 2) F 256) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  assert (TBND : rw_cells asegs m (al_t L + 8) [C8 (Z_to_bv 64 (al_top L)); C8 (Z_to_bv 64 (al_bot L))] /\ rw_cells asegs m (al_t L + 40) [C1 (Z_to_bv 8 0)]).
  { pose proof AR as ARx. destruct ARx as (_ & _ & _ & THRx & _). destruct THRx as (T0x & T40x & _). split; [| exact T40x].
    rw_split T0x 1%nat T0a T0b. exact T0b. }
  destruct TBND as [TB8 TB40].

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 216 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 248) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F + 16) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS3.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH0). destruct (c8c8_of_dc m _ DS3) as (sh2 & sh3 & SH1).
  assert (SH4 : rw_cells asegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3]).
  { apply (proj2 (rw_cells_app asegs m (shad F) [C8 sh0; C8 sh1] [C8 sh2; C8 sh3])). split; [exact SH0|].
    cbn [cells_size csize Nat.add]. replace (shad F + Z.of_nat 16) with (shad F + 16) by lia. exact SH1. }

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells asegs m (al_fake L) [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 4095) by reflexivity. assert (HFLAG : flag = (al_fake L) + 28672 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 2134016 + pos * 256) by reflexivity.
  assert (JB : Z.of_nat jn < 4096) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  pose proof (gfl_cell L LB m HFK) as GFLC. pose proof (grs_cell L LB m rsf HFK RS) as GRSC. pose proof (gfreed_shadow L LB m rsf (al_bot L) (bv_unsigned sp) HFK CLS) as GSHC.
  eapply evtF_mono.
  { eapply (stack_malloc2_gcspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60cc80 (al_fake L) h pos flag F (al_top L) (al_bot L) jn (Z_to_bv 8 1) (gfl L m) (grs L rsf) j24 j56 sh0 sh1 sh2 sh3 h0 h1 hs);
      try exact MI; try exact ST; try exact TP; try exact GFLC; try exact GRSC; try exact GSHC; try exact BUSYc; try exact FREEc; try exact TB8; try exact TB40;
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia); try (cbn; discriminate).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & NGC' & HNT2 & FL1 & F24' & F56' & SH' & FLAGS').
  unfold sm2gc_W in MU.

  assert (SHH : 0x7fff8000 <= shad (al_fake L + 36864) /\ shad (al_fake L + 11571200) <= 0x10007fff8000
                /\ shad (al_fake L + 11571200) = shad (al_fake L) + 1446400 /\ shad (al_fake L) <= shad (al_fake L + 36864)).
  { rewrite !gc_shad_eq. pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. clear - G1 G2c G3 ATR. Z.div_mod_to_equations. lia. }
  destruct SHH as (SHH1 & SHH2 & SHH3 & SHH4).
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 240 <= a < bv_unsigned sp) -> ~ (al_fake L <= a < al_fake L + 4096) -> a <> flag ->
            ~ (F <= a < F + 256) -> ~ (shad F <= a < shad F + 32) ->
            disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) a 1 ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 DG. apply MU. rewrite wa_unsigned by lia. cbn [outside].
    repeat (split; [lia|]). eapply disjoint_outside; [exact DG| lia]. }
  assert (DGH : forall A k, 0 <= k -> (A + k <= al_fake L + 4096 \/ al_fake L + 36864 <= A) ->
            (A + k <= shad (al_fake L + 36864) \/ shad (al_fake L + 11571200) <= A) -> disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) A k)
    by (intros A k K H1 H2; apply gcWall_disj_hulls; assumption).
  assert (F64 : F mod 256 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (16 * k + 8336 + pos). lia. }

  pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c.
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext AH HLt L st X m m' _ ALO AR MU WM). assert (SHLx : shlen 11571200 = 1446400) by reflexivity.
    lazymatch goal with |- Forall _ ?W => change (Forall (aext L) W) end.
    repeat (apply Forall_cons; [unfold aext; rewrite ?SHLx; cbn [fst snd]; intros _;
      first [left; clear -HFLAG HFF PB; lia | right; left; clear -SB1 SB2 SB3 PB; lia | right; right; left; clear -BOT LO; lia]|]).
    exact (gcWall_aext L (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 G1). }
  assert (NOTIN : ~ In (FB2 F) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) by exact NOTIN0.
  Local Ltac xportG H MU WM DGH K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length];
      repeat (split; [first [K; lia | lia]|]); apply DGH; first [K; lia | lia]].
  assert (CE' : afake_cells L m').
  { unfold afake_cells. split; [xportG REAL MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTVP MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DV MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTV1 MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|].
    split; [xportG BD MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG CF MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG VERB MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
  assert (LOG' : rw_cells asegs m' (al_fake L + 88) [C8 (Z_to_bv 64 20)]) by (xportG LOG MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)).
  assert (HFK' : AFAKE (gb:=false) L (FB2 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { rewrite EFR. change 256 with (fk_fsize 2).
    eapply (afake_after_gc L LB m rsf (al_bot L) (bv_unsigned sp)) with (c0 := 2) (pos0 := pos).
    all: try lazymatch goal with
         | |- AFAKE _ _ _ => exact HFK
         | |- wmono _ _ _ => exact WM
         | |- afake_cells _ _ => exact CE'
         | |- rw_cells _ _ (_ + 88) _ => exact LOG'
         | |- rw_cells _ _ (_ + 96) _ => exact NGC'
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; CB 64 _] => exact HNT2
         | |- rw_cells _ _ (fk_flag _ _ _) _ => rewrite <- EFL; exact FL1
         | |- ~ In _ _ => rewrite <- EFR; exact NOTIN
         | |- rw_cells _ _ (_ + 72) _ => xportG TFSC MU WM DGH ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)
         | |- forall c p, _ => intros c' p' Hc' Hp' NE'; apply FLAGS'; [exact Hc'| exact Hp'|]; intros E'; apply NE'; rewrite E'; f_equal; rewrite HFLAG; lia
         end.
    all: try (change (gcN 2) with 4096; lia). all: try lia. }

  assert (BL' : ablocks L st X (FB2 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate|]. apply fk_kept_In in Hin as [Hin _]. exact (B1 p A n Hin).
    - intros c' A n [E|Hin]; [| apply fk_kept_In in Hin as [Hin _]; exact (B2 c' A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - change (List.NoDup (hb_ids (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))). rewrite fk_kept_hb_ids. exact B3.
    - constructor; [exact NOTIN| apply fk_kept_NoDup; exact B4]. }
  assert (AHP' : AHEAP_P AHf L RNG st (FB2 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 256 <= ab_addr b)).
  { intros b HbK. pose proof (proj1 (proj1 (fk_kept_In LB rsf (al_bot L) (bv_unsigned sp) b) HbK)) as Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (2, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in HbK. replace (fk_fsize 2) with 256 in HbK by reflexivity. exact HbK. }
      pose proof (fk_frames_disjoint L c' pos' 2 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 2) with 256 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 256)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
        D3 D24 D56 DS2 DS3 RR A10.
  assert (HPR : aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m').
  { assert (SHFLO : 2147450880 <= shad F) by (rewrite SHF; clear - GL1 HFF PB; Z.div_mod_to_equations; lia).
    intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; [exact Ha| clear - Hs; lia| clear - Hs G3 BOT LO; lia| clear - Hs G3 BOT LO HFLAG PB; lia| clear - Hs G3 BOT LO HFF PB; lia| clear - Hs SB3 BOT LO ATR; lia
                 | apply DGH; [lia| right; clear - Hs G3 BOT LO; lia| right; clear - Hs SHH2 BOT LO ATR; lia]].
    - pose proof (CI_OK iv Hiv) as HCI.
      apply OUT; [exact Ha| clear - HCI Hr BOT LO ATR; lia| clear - HCI Hr GL1; lia| clear - HCI Hr GL1 HFLAG PB; lia| clear - HCI Hr GL1 HFF PB; lia| clear - HCI Hr SHFLO; lia
                 | apply DGH; [lia| left; clear - HCI Hr GL1; lia| left; clear - HCI Hr SHH1; lia]].
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1.
      apply OUT; [exact Ha| clear - Hr Y2 BOT LO; lia| clear - Hr Y3; lia| clear - Hr Y3 HFLAG PB; lia| clear - Hr Y4; lia| clear - Hr Y1 SHFLO SB3; lia
                 | apply DGH; [lia| clear - Hr Y3; lia| clear - Hr Y1 SHH1 SHH2; lia]].
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      assert (F8 : F mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
      apply OUT; [lia| rewrite SHA; clear - A'R ATR LO BOT; lia| rewrite SHA; clear - A'R G2c; lia| rewrite SHA, HFLAG; clear - A'R G2c PB; lia
                 | rewrite SHA; clear - A'R G2c G3 HFF PB; lia| rewrite SHA, SHF; clear - A'R NA F8; Z.div_mod_to_equations; lia|].
      destruct Ha' as [SA|[(iv & Hiv & Hr)|(cls & FA & fn & HbK & Hr)]].
      + apply DGH; [lia| rewrite SHA; clear - SA ATR G2c G3; lia|]. right. rewrite SHA, gc_shad_eq. clear - SA G3. Z.div_mod_to_equations. lia.
      + pose proof (CI_OK iv Hiv). apply DGH; [lia| rewrite SHA; clear - A'R G2c; lia|]. left. rewrite SHA, gc_shad_eq. clear - H Hr GL1. unfold AIMG_HI in *. Z.div_mod_to_equations. lia.
      + apply fk_kept_In in HbK as [HbL ALIVE].
        pose proof (afake_lb L LB m cls FA fn HFK HbL) as (Hc' & Hn' & Np' & F64' & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
        pose proof HFK as (_ & _ & _ & _ & _ & _ & _ & _ & LVx & _). destruct (LVx _ _ _ HbL) as (_ & _ & pos2 & Hp2 & HF2 & B1x).
        assert (pos2 = pos') by (apply (fk_frame_inj L cls); [lia| congruence]). subst pos2.
        assert (E1 : gfl L m cls pos' = Z_to_bv 8 1) by (unfold gfl; rewrite B1x; reflexivity).
        assert (NF : gfreed (al_bot L) (bv_unsigned sp) (gfl L m cls pos') (grs L rsf cls pos') = false).
        { rewrite (gfreed_dead L m rsf (al_bot L) (bv_unsigned sp) cls pos' Hc' Hp') by (rewrite E1; discriminate). rewrite <- HF', <- Hn'. exact ALIVE. }
        pose proof (gc_pows cls Hc') as (_ & _ & _ & _ & P8 & PC). unfold fk_fsize in Hn'.
        eapply (gcWall_disj_kept_shadow (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 cls pos'); [exact Hc'| exact Hp'| exact NF| | | lia].
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. clear - Hr. Z.div_mod_to_equations. lia.
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. remember (2 ^ cls) as K. clear - Hr Hn' P8 PC F64'. Z.div_mod_to_equations. lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 216 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 216) with 216%nat in J1.
  assert (LJ : length junk1 = 216%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 224 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 2 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 224 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 216 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 224) with (F + 248) by lia. exact F56'. }

  unfold sm2_postGB. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm2PB.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.
Import stdpp.gmap.

Module AFake_arep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Definition AH : aholes := mkAHoles AQ ASEC (ADEPOT DI) AFAKE.
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.

Lemma HB_FAKE : forall L RNG st LB m p A n,
  AHEAP_P AH L RNG st LB m -> In (HB p A n) LB ->
  ablock_range A n /\ (A + n <= al_fake L \/ al_fake L + 11571200 <= A).
Proof. intros. split; [eapply AHEAP_P_hb_range; eauto| eapply AHEAP_P_hb_fake; eauto]. Qed.

Lemma AREP_frame_ext' : forall L st X m m' W,
  alayout_ok L -> AREP AH L st X m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => fst iv < snd iv ->
            (al_fake L <= fst iv /\ snd iv <= al_fake L + 11571200)
         \/ (shad (al_fake L) <= fst iv /\ snd iv <= shad (al_fake L) + shlen 11571200)
         \/ ATOP <= fst iv) W ->
  AREP AH L st X m'.
Proof.

  intros L st X m m' W AL AR MU WM HW. eapply (AREP_frame_ext AH HL); [exact AL| exact AR| exact MU| exact WM|].
  eapply List.Forall_impl; [| exact HW]. cbv beta. intros iv H Hlt.
  destruct (H Hlt) as [A|[A|A]]; [left; exact A| right; left; exact A| right; right; left; exact A].
Qed.

Lemma AREP_cells : forall L st X m, AREP AH L st X m ->
  rt_got m /\ rt_shbase m
  /\ rw_cells bsegs m 0xdb4e0 [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0xdb4e4 [C4 (Z_to_bv 64 0)]
  /\ rt_inited m /\ rt_layout m
  /\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]
  /\ rw_cells bsegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))]
  /\ (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None).
Proof.
  intros L st X m H. pose proof (AREP_relro AH L st X m H) as RR. unfold AREP, arep_rt in H. decompose [and] H.
  repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

Theorem fake_flag_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Proof.
  intros L RNG st LB m cls F N AHP Hin. pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof (afake_lb L LB m cls F N HFK Hin) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR).
  pose proof (afake_flag L LB m cls F N HFK Hin) as FL.
  destruct HFK as (G & _). destruct G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, KHIGH, AIMG_HI in *.
  destruct ARNG as (_ & _ & _ & _ & _ & _ & RF & _).
  split; [exact FL|]. split; [eapply rng_sub'; [exact RF| lia]|]. split; [eapply ablk_sub; [exact G2| lia| lia]|]. split; [lia|]. split.
  - intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    + pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [_ D]. lia.
    + pose proof (afake_lb L LB m c' A' n' (proj2 (proj2 (proj2 AHP))) Hb) as (_ & _ & _ & _ & X1 & X2 & _). lia.
  - intros (iv & Hiv & R). pose proof (CI_OK iv Hiv). lia.
Qed.

Lemma ablocks_tail : forall L st X b LB, ablocks L st X (b :: LB) -> ablocks L st X LB.
Proof.
  intros L st X b LB (H1 & H2 & H3 & H4). split; [|split; [|split]].
  - intros p A n Hin. apply (H1 p A n). right; exact Hin.
  - intros c A n Hin. apply (H2 c A n). right; exact Hin.
  - destruct b as [[p|c] A n]; cbn in H3; [inversion H3; assumption| exact H3].
  - inversion H4; assumption.
Qed.

Theorem fake_release_P : forall L RNG st LB m cls F N,
  AHEAP_P AH L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP_P AH L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m cls F N AHP. pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof (afake_lb L _ m cls F N HFK ltac:(left; reflexivity)) as (Hc & Hn & Npos & F64 & FLO & FHI & FK & FC & pos & Hp & HF & EF & FR).
  assert (NI : ~ In (mkABlock (ABFake cls) F N) LB) by (destruct BL as (_ & _ & _ & ND); inversion ND; assumption).
  destruct HFK as (G & HFK'). pose proof G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold FAKESZ, AIMG_HI in *.
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [| eapply ablocks_tail; exact BL].
    eapply (AREP_frame_ext' _ _ _ _ _ [(fflag L cls F, fflag L cls F + 1)]); [exact ALO| exact AR| | |].
    + apply munch_write; [apply munch_refl| lia| cbn; lia|]. cbn. left. lia.
    + apply wmono_write, wmono_refl.
    + constructor; [|constructor]. cbn. intros _. left. lia.
  - cbn [AH ah_fake]. apply (afake_release L LB m cls F N); [exact (conj G HFK')| exact NI].
Qed.

Notation FB0 F := (mkABlock (ABFake 0) F 64).
Definition SM_STACK : Z := 4096.

Definition sm0_postP (L : alayout) (RNG : footprint)
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
    /\ rng RNG F 64 /\ rng RNG (shad F) 8.

Lemma relro_word : forall m A v,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b bsegs A (le8 (Z_to_bv 64 v)) = true ->
  rw_cells bsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
  eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m A (le8 (Z_to_bv 64 v)));
    [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
    | exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.

Lemma arep_ext_sm0 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AH L st X m ->
  munch [(sp - 208, sp); (fs, fs + 8); (flag, flag + 1); (F + 24, F + 32); (F + 56, F + 64); (2147450880 + F / 8, 2147450880 + F / 8 + 8)] m m' ->
  wmono bsegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 64 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 8 <= shad fs + 1446400 ->
  AREP AH L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.

Theorem stack_malloc_0_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  gcbit = false ->
  (forall F n, ~ In (mkABlock (ABFake 0) F n) LB) ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm0_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros AHP GCB0 NOFK MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). pose proof NGC as NGCg. rewrite GCB0 in NGC.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd3680 0x16b718 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd43c0 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0xd43b0 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  set (h := bv_unsigned h0). set (pos := Z.land h 16383). set (flag := (al_fake L) + 4096 + pos). set (F := (al_fake L) + 36864 + pos * 64).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 0 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 0 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 0 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 4608 + 8 * pos = shad F /\ shad F + 8 <= shad (al_fake L) + 1446400 /\ shad F + 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  destruct (c1_of_dc m flag D3) as [fb FL0].
  assert (fb = Z_to_bv 8 0) as ->.
  { destruct (decide (fb = Z_to_bv 8 0)) as [E|NE]; [exact E| exfalso].
    apply (NOFK (fk_frame L 0 pos) (fk_fsize 0)). apply (FL 0 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
    rewrite <- EFL. apply (rw_C1_high m flag fb FL0). subst flag. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8_of_dc m _ DS2) as [sh0 SH0].

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land h 16383) by reflexivity. assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc0_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60ee40 (al_fake L) h pos flag F j24 j56 sh0 h1 h2 hs);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm0_W in MU. rewrite SHF in MU.

  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) <= a < (al_fake L) + 8) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 56 <= a < F + 64) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 8) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 64 = 0) by (rewrite EFR; apply fk_frame_al64; [exact G1| lia]).

  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm0 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB0 F) LB) by (apply NOFK).
  assert (HFK' : AFAKE L (FB0 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists (Z_to_bv 64 (h + 1)), h1, h2, hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGCg MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
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
    - split; [| xportk TFSC MU WM ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)].
      intros c F' n' [E|Hin].
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

  assert (BL' : ablocks L st X (FB0 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB0 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 64 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (0, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 0) with 64 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 0 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 0) with 64 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 64)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
        D3 D24 D56 DS2 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }

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

  unfold sm0_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
Qed.

Notation FB2 F := (mkABlock (ABFake 2) F 256).

Definition sm2_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB2 F :: LB) m'
    /\ F mod 256 = 0 /\ ablk F (F + 256) /\ F + 256 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 (fflag L 2 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 256 /\ rng RNG (shad F) 32.

Lemma arep_ext_sm2 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AH L st X m ->
  munch [(sp - 208, sp); (fs + 16, fs + 24); (flag, flag + 1); (F + 24, F + 32); (F + 248, F + 256); (2147450880 + F / 8, 2147450880 + F / 8 + 32)] m m' ->
  wmono bsegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 256 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 32 <= shad fs + 1446400 ->
  AREP AH L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.

Theorem stack_malloc_2_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  gcbit = false ->
  (forall F n, ~ In (mkABlock (ABFake 2) F n) LB) ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm2_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros AHP GCB0 NOFK MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). pose proof NGC as NGCg. rewrite GCB0 in NGC.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd3680 0x16b718 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd43c0 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0xd43b0 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  set (h := bv_unsigned h2). set (pos := Z.land h 4095). set (flag := (al_fake L) + 28672 + pos). set (F := (al_fake L) + 2134016 + pos * 256).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 2 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 2 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 2 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 266752 + 32 * pos = shad F /\ shad F + 32 <= shad (al_fake L) + 1446400 /\ shad F + 32 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 32 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  destruct (c1_of_dc m flag D3) as [fb FL0].
  assert (fb = Z_to_bv 8 0) as ->.
  { destruct (decide (fb = Z_to_bv 8 0)) as [E|NE]; [exact E| exfalso].
    apply (NOFK (fk_frame L 2 pos) (fk_fsize 2)). apply (FL 2 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
    rewrite <- EFL. apply (rw_C1_high m flag fb FL0). subst flag. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 216 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 248) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F + 16) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS3.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH0). destruct (c8c8_of_dc m _ DS3) as (sh2 & sh3 & SH1).
  assert (SH4 : rw_cells bsegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3]).
  { apply (proj2 (rw_cells_app bsegs m (shad F) [C8 sh0; C8 sh1] [C8 sh2; C8 sh3])). split; [exact SH0|].
    cbn [cells_size csize Nat.add]. replace (shad F + Z.of_nat 16) with (shad F + 16) by lia. exact SH1. }

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land h 4095) by reflexivity. assert (HFLAG : flag = (al_fake L) + 28672 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 2134016 + pos * 256) by reflexivity.
  clearbody h pos flag F.
  eapply evtF_mono.
  { eapply (stack_malloc2_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60ee40 (al_fake L) h pos flag F j24 j56 sh0 sh1 sh2 sh3 h0 h1 hs);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm2_W in MU. rewrite SHF in MU.

  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 16 <= a < (al_fake L) + 24) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 248 <= a < F + 256) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 32) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 256 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (16 * k + 8336 + pos). lia. }

  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm2 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB2 F) LB) by (apply NOFK).
  assert (HFK' : AFAKE L (FB2 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists h0, h1, (Z_to_bv 64 (h + 1)), hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGCg MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 2) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 2 pos' 2 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 2 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - split; [| xportk TFSC MU WM ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)].
      intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 2) with 256 in Hin by reflexivity. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }

  assert (BL' : ablocks L st X (FB2 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB2 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 256 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (2, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 2) with 256 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 2 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 2) with 256 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 256)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
        D3 D24 D56 DS2 DS3 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 216 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 216) with 216%nat in J1.
  assert (LJ : length junk1 = 216%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 224 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 2 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app bsegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 224 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app bsegs m' (F + 24) [C8 sp] [CB 216 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 224) with (F + 248) by lia. exact F56'. }

  unfold sm2_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
Qed.
End S.
End CANSEC1.

End AFake_arep.

Module AFake_sm0P.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0g.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AH := (AFake_arep.AH DI AQ ASEC).
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation AREP_cells := (AFake_arep.AREP_cells DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' DI AQ ASEC HL).
Notation arep_ext_sm0 := (AFake_arep.arep_ext_sm0 DI AQ ASEC HL).

Definition sm0_postG (L : alayout) (RNG : footprint)
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
    /\ rw_cells bsegs m' (F + 24) [C8 sp].

Theorem stack_malloc_0_GA : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  gcbit = false ->
  Z.of_nat (fk_count 0 LB) < 16384 ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm0_postG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros AHP GCB0 NOTFULL MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). pose proof NGC as NGCg. rewrite GCB0 in NGC.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd3680 0x16b718 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd43c0 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0xd43b0 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h0).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (afake_first_free L LB m 0 h HFK NDLB ltac:(unfold FK_NCLS; lia) ltac:(change (fk_nframes 0) with 16384; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 0) with 16384 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 16384 = Z.land x 16383) by (intros x; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 16383). set (flag := (al_fake L) + 4096 + pos). set (F := (al_fake L) + 36864 + pos * 64).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 0 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 0 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 0 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 4608 + 8 * pos = shad F /\ shad F + 8 <= shad (al_fake L) + 1446400 /\ shad F + 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  assert (FL0 : rw_cells bsegs m flag [C1 (Z_to_bv 8 0)]).
  { rewrite EFL. unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> exists b : byte, rw_cells bsegs m (sm0_flag (al_fake L) (h + t)) [C1 b] /\ bv_unsigned b <> 0).
  { intros t Ht. rewrite EJ in Ht. destruct (BUSYz t Ht) as (b & Cb & NZb). exists b. split; [| exact NZb].
    unfold sm0_flag. rewrite <- LM. unfold fk_flag, fk_flags in Cb. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub] in Cb.
    eapply rw_cells_at_eq; [exact Cb| lia]. }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 0) F 64) LB).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8_of_dc m _ DS2) as [sh0 SH0].

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 16383) by reflexivity. assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
  assert (JB : Z.of_nat jn < 16384) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  eapply evtF_mono.
  { eapply (stack_malloc0_gspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60ee40 (al_fake L) h pos flag F jn j24 j56 sh0 h1 h2 hs);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm0_W in MU. rewrite SHF in MU.

  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) <= a < (al_fake L) + 8) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 56 <= a < F + 64) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 8) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 64 = 0) by (rewrite EFR; apply fk_frame_al64; [exact G1| lia]).

  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm0 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB0 F) LB) by exact NOTIN0.
  assert (HFK' : AFAKE L (FB0 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists (Z_to_bv 64 (h + Z.of_nat jn + 1)), h1, h2, hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGCg MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
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
    - split; [| xportk TFSC MU WM ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)].
      intros c F' n' [E|Hin].
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

  assert (BL' : ablocks L st X (FB0 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB0 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 64 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (0, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 0) with 64 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 0 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 0) with 64 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 64)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
        D3 D24 D56 DS2 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }

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

  unfold sm0_postG. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm0P.

Module AFake_sm0PB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2gc.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcP.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHt := (AFake_arep.AH (gb:=true) DI AQ ASEC).
Notation AHf := (AFake_arep.AH (gb:=false) DI AQ ASEC).
Hypothesis HLt : ahole_laws AHt.
Notation AH := AHt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation AREP_cells := (AFake_arep.AREP_cells (gb:=true) DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE (gb:=true) DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' (gb:=true) DI AQ ASEC HLt).

Definition sm0_postGB (rsf : Z -> Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m'
    /\ AHEAP_P AHf L RNG st (FB0 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m'
    /\ F mod 64 = 0 /\ ablk F (F + 64) /\ F + 64 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 32 junk; C8 (Z_to_bv 64 (fflag L 0 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0)]
    /\ rng RNG F 64 /\ rng RNG (shad F) 8
    /\ rw_cells bsegs m' (F + 24) [C8 sp].

Theorem stack_malloc_0_GB : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (rsf : Z -> Z),
  AHEAP_P AH L RNG st LB m ->
  Z.of_nat (fk_count 0 LB) < 16384 ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> c <= 2) ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> 0 <= rsf F < 2^64 /\ rw_cells bsegs m (F + 24) [C8 (Z_to_bv 64 (rsf F))]) ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm0_postGB rsf L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom bsegs)).
Proof.
  intros until rsf. intros AHP NOTFULL CLS RS MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). change (rw_cells bsegs m (al_fake L + 96) [C1 (Z_to_bv 8 1)]) in NGC. pose proof NGC as NGCg.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd3680 0x16b718 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd43c0 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0xd43b0 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h0).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (gc_probe L LB m rsf (al_bot L) (bv_unsigned sp) HFK NDLB 0 h ltac:(lia) ltac:(change (fk_nframes 0) with 16384; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 0) with 16384 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 16384 = Z.land x 16383) by (intros x; change 16383 with (Z.ones 14); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 16383). set (flag := (al_fake L) + 4096 + pos). set (F := (al_fake L) + 36864 + pos * 64).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 16384).
  { subst pos. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 0 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 0 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 0 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 4608 + 8 * pos = shad F /\ shad F + 8 <= shad (al_fake L) + 1446400 /\ shad F + 8 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  pose proof I as FL0.
  assert (FREEc : gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 pos = Z_to_bv 8 0).
  { unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> bv_unsigned (gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 (Z.land (h + t) 16383)) <> 0).
  { intros t Ht. rewrite EJ in Ht. rewrite <- LM. exact (BUSYz t Ht). }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 0) F 64) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  assert (TBND : rw_cells bsegs m (al_t L + 8) [C8 (Z_to_bv 64 (al_top L)); C8 (Z_to_bv 64 (al_bot L))] /\ rw_cells bsegs m (al_t L + 40) [C1 (Z_to_bv 8 0)]).
  { pose proof AR as ARx. destruct ARx as (_ & _ & _ & THRx & _). destruct THRx as (T0x & T40x & _). split; [| exact T40x].
    rw_split T0x 1%nat T0a T0b. exact T0b. }
  destruct TBND as [TB8 TB40].

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8_of_dc m _ DS2) as [sh0 SH0].

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 16383) by reflexivity. assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
  assert (JB : Z.of_nat jn < 16384) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  pose proof (gfl_cell L LB m HFK) as GFLC. pose proof (grs_cell L LB m rsf HFK RS) as GRSC. pose proof (gfreed_shadow L LB m rsf (al_bot L) (bv_unsigned sp) HFK CLS) as GSHC.
  eapply evtF_mono.
  { eapply (stack_malloc0_gcspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60ee40 (al_fake L) h pos flag F (al_top L) (al_bot L) jn (Z_to_bv 8 1) (gfl L m) (grs L rsf) j24 j56 sh0 h1 h2 hs);
      try exact MI; try exact ST; try exact TP; try exact GFLC; try exact GRSC; try exact GSHC; try exact BUSYc; try exact FREEc; try exact TB8; try exact TB40;
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia); try (cbn; discriminate).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & NGC' & HNT2 & FL1 & F24' & F56' & SH' & FLAGS').
  unfold sm0gc_W in MU.

  assert (SHH : 0x7fff8000 <= shad (al_fake L + 36864) /\ shad (al_fake L + 11571200) <= 0x10007fff8000
                /\ shad (al_fake L + 11571200) = shad (al_fake L) + 1446400 /\ shad (al_fake L) <= shad (al_fake L + 36864)).
  { rewrite !gc_shad_eq. pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. clear - G1 G2c G3 ATR. Z.div_mod_to_equations. lia. }
  destruct SHH as (SHH1 & SHH2 & SHH3 & SHH4).
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 240 <= a < bv_unsigned sp) -> ~ (al_fake L <= a < al_fake L + 4096) -> a <> flag ->
            ~ (F <= a < F + 64) -> ~ (shad F <= a < shad F + 8) ->
            disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) a 1 ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 DG. apply MU. rewrite wa_unsigned by lia. cbn [outside].
    repeat (split; [lia|]). eapply disjoint_outside; [exact DG| lia]. }
  assert (DGH : forall A k, 0 <= k -> (A + k <= al_fake L + 4096 \/ al_fake L + 36864 <= A) ->
            (A + k <= shad (al_fake L + 36864) \/ shad (al_fake L + 11571200) <= A) -> disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) A k)
    by (intros A k K H1 H2; apply gcWall_disj_hulls; assumption).
  assert (F64 : F mod 64 = 0) by (rewrite EFR; apply fk_frame_al64; [exact G1| lia]).

  Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
  Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
  pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c.
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext AH HLt L st X m m' _ ALO AR MU WM). assert (SHLx : shlen 11571200 = 1446400) by reflexivity.
    lazymatch goal with |- Forall _ ?W => change (Forall (aext L) W) end.
    repeat (apply Forall_cons; [unfold aext; rewrite ?SHLx; cbn [fst snd]; intros _;
      first [left; clear -HFLAG HFF PB; lia | right; left; clear -SB1 SB2 SB3 PB; lia | right; right; left; clear -BOT LO; lia]|]).
    exact (gcWall_aext L (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 G1). }
  assert (NOTIN : ~ In (FB0 F) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) by exact NOTIN0.
  Local Ltac xportG H MU WM DGH K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length];
      repeat (split; [first [K; lia | lia]|]); apply DGH; first [K; lia | lia]].
  assert (CE' : afake_cells L m').
  { unfold afake_cells. split; [xportG REAL MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTVP MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DV MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTV1 MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|].
    split; [xportG BD MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG CF MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG VERB MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
  assert (LOG' : rw_cells bsegs m' (al_fake L + 88) [C8 (Z_to_bv 64 20)]) by (xportG LOG MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)).
  assert (HFK' : AFAKE (gb:=false) L (FB0 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { rewrite EFR. change 64 with (fk_fsize 0).
    eapply (afake_after_gc L LB m rsf (al_bot L) (bv_unsigned sp)) with (c0 := 0) (pos0 := pos).
    all: try lazymatch goal with
         | |- AFAKE _ _ _ => exact HFK
         | |- wmono _ _ _ => exact WM
         | |- afake_cells _ _ => exact CE'
         | |- rw_cells _ _ (_ + 88) _ => exact LOG'
         | |- rw_cells _ _ (_ + 96) _ => exact NGC'
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; CB 64 _] => exact HNT2
         | |- rw_cells _ _ (fk_flag _ _ _) _ => rewrite <- EFL; exact FL1
         | |- ~ In _ _ => rewrite <- EFR; exact NOTIN
         | |- rw_cells _ _ (_ + 72) _ => xportG TFSC MU WM DGH ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)
         | |- forall c p, _ => intros c' p' Hc' Hp' NE'; apply FLAGS'; [exact Hc'| exact Hp'|]; intros E'; apply NE'; rewrite E'; f_equal; rewrite HFLAG; lia
         end.
    all: try (change (gcN 0) with 16384; lia). all: try lia. }

  assert (BL' : ablocks L st X (FB0 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate|]. apply fk_kept_In in Hin as [Hin _]. exact (B1 p A n Hin).
    - intros c' A n [E|Hin]; [| apply fk_kept_In in Hin as [Hin _]; exact (B2 c' A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - change (List.NoDup (hb_ids (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))). rewrite fk_kept_hb_ids. exact B3.
    - constructor; [exact NOTIN| apply fk_kept_NoDup; exact B4]. }
  assert (AHP' : AHEAP_P AHf L RNG st (FB0 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 64 <= ab_addr b)).
  { intros b HbK. pose proof (proj1 (proj1 (fk_kept_In LB rsf (al_bot L) (bv_unsigned sp) b) HbK)) as Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (0, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in HbK. replace (fk_fsize 0) with 64 in HbK by reflexivity. exact HbK. }
      pose proof (fk_frames_disjoint L c' pos' 0 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 0) with 64 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 64)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
        D3 D24 D56 DS2 RR A10.
  assert (HPR : aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m').
  { assert (SHFLO : 2147450880 <= shad F) by (rewrite SHF; clear - GL1 HFF PB; Z.div_mod_to_equations; lia).
    intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; [exact Ha| clear - Hs; lia| clear - Hs G3 BOT LO; lia| clear - Hs G3 BOT LO HFLAG PB; lia| clear - Hs G3 BOT LO HFF PB; lia| clear - Hs SB3 BOT LO ATR; lia
                 | apply DGH; [lia| right; clear - Hs G3 BOT LO; lia| right; clear - Hs SHH2 BOT LO ATR; lia]].
    - pose proof (CI_OK iv Hiv) as HCI.
      apply OUT; [exact Ha| clear - HCI Hr BOT LO ATR; lia| clear - HCI Hr GL1; lia| clear - HCI Hr GL1 HFLAG PB; lia| clear - HCI Hr GL1 HFF PB; lia| clear - HCI Hr SHFLO; lia
                 | apply DGH; [lia| left; clear - HCI Hr GL1; lia| left; clear - HCI Hr SHH1; lia]].
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1.
      apply OUT; [exact Ha| clear - Hr Y2 BOT LO; lia| clear - Hr Y3; lia| clear - Hr Y3 HFLAG PB; lia| clear - Hr Y4; lia| clear - Hr Y1 SHFLO SB3; lia
                 | apply DGH; [lia| clear - Hr Y3; lia| clear - Hr Y1 SHH1 SHH2; lia]].
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      assert (F8 : F mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
      apply OUT; [lia| rewrite SHA; clear - A'R ATR LO BOT; lia| rewrite SHA; clear - A'R G2c; lia| rewrite SHA, HFLAG; clear - A'R G2c PB; lia
                 | rewrite SHA; clear - A'R G2c G3 HFF PB; lia| rewrite SHA, SHF; clear - A'R NA F8; Z.div_mod_to_equations; lia|].
      destruct Ha' as [SA|[(iv & Hiv & Hr)|(cls & FA & fn & HbK & Hr)]].
      + apply DGH; [lia| rewrite SHA; clear - SA ATR G2c G3; lia|]. right. rewrite SHA, gc_shad_eq. clear - SA G3. Z.div_mod_to_equations. lia.
      + pose proof (CI_OK iv Hiv). apply DGH; [lia| rewrite SHA; clear - A'R G2c; lia|]. left. rewrite SHA, gc_shad_eq. clear - H Hr GL1. unfold AIMG_HI in *. Z.div_mod_to_equations. lia.
      + apply fk_kept_In in HbK as [HbL ALIVE].
        pose proof (afake_lb L LB m cls FA fn HFK HbL) as (Hc' & Hn' & Np' & F64' & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
        pose proof HFK as (_ & _ & _ & _ & _ & _ & _ & _ & LVx & _). destruct (LVx _ _ _ HbL) as (_ & _ & pos2 & Hp2 & HF2 & B1x).
        assert (pos2 = pos') by (apply (fk_frame_inj L cls); [lia| congruence]). subst pos2.
        assert (E1 : gfl L m cls pos' = Z_to_bv 8 1) by (unfold gfl; rewrite B1x; reflexivity).
        assert (NF : gfreed (al_bot L) (bv_unsigned sp) (gfl L m cls pos') (grs L rsf cls pos') = false).
        { rewrite (gfreed_dead L m rsf (al_bot L) (bv_unsigned sp) cls pos' Hc' Hp') by (rewrite E1; discriminate). rewrite <- HF', <- Hn'. exact ALIVE. }
        pose proof (gc_pows cls Hc') as (_ & _ & _ & _ & P8 & PC). unfold fk_fsize in Hn'.
        eapply (gcWall_disj_kept_shadow (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 cls pos'); [exact Hc'| exact Hp'| exact NF| | | lia].
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. clear - Hr. Z.div_mod_to_equations. lia.
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. remember (2 ^ cls) as K. clear - Hr Hn' P8 PC F64'. Z.div_mod_to_equations. lia. }

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

  unfold sm0_postGB. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm0PB.

Module AFake_sm1P.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm1g.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AH := (AFake_arep.AH DI AQ ASEC).
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Notation AREP_cells := (AFake_arep.AREP_cells DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' DI AQ ASEC HL).
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].

Definition sm1_postG (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB1 F :: LB) m'
    /\ F mod 128 = 0 /\ ablk F (F + 128) /\ F + 128 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 128 /\ rng RNG (shad F) 16
    /\ rw_cells bsegs m' (F + 24) [C8 sp].

Lemma arep_ext_sm1 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AH L st X m ->
  munch [(sp - 208, sp); (fs + 8, fs + 16); (flag, flag + 1); (F + 24, F + 32); (F + 120, F + 128); (2147450880 + F / 8, 2147450880 + F / 8 + 16)] m m' ->
  wmono bsegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 128 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 16 <= shad fs + 1446400 ->
  AREP AH L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.

Theorem stack_malloc_1_GA : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  gcbit = false ->
  Z.of_nat (fk_count 1 LB) < 8192 ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm1_postG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros AHP GCB0 NOTFULL MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). pose proof NGC as NGCg. rewrite GCB0 in NGC.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd3680 0x16b718 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd43c0 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0xd43b0 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h1).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (afake_first_free L LB m 1 h HFK NDLB ltac:(unfold FK_NCLS; lia) ltac:(change (fk_nframes 1) with 8192; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 1) with 8192 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 8192 = Z.land x 8191) by (intros x; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 8191). set (flag := (al_fake L) + 20480 + pos). set (F := (al_fake L) + 1085440 + pos * 128).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 8192).
  { subst pos. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 1 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 1 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 1 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 135680 + 16 * pos = shad F /\ shad F + 16 <= shad (al_fake L) + 1446400 /\ shad F + 16 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 16 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  assert (FL0 : rw_cells bsegs m flag [C1 (Z_to_bv 8 0)]).
  { rewrite EFL. unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> exists b : byte, rw_cells bsegs m (sm1_flag (al_fake L) (h + t)) [C1 b] /\ bv_unsigned b <> 0).
  { intros t Ht. rewrite EJ in Ht. destruct (BUSYz t Ht) as (b & Cb & NZb). exists b. split; [| exact NZb].
    unfold sm1_flag. rewrite <- LM. unfold fk_flag, fk_flags in Cb. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub] in Cb.
    eapply rw_cells_at_eq; [exact Cb| lia]. }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 1) F 128) LB).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 88 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 120) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH4). pose proof SH4 as SH0. pose proof SH4 as SH1. pose proof DS2 as DS3.

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 h0; C8 (Z_to_bv 64 h); C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 8191) by reflexivity. assert (HFLAG : flag = (al_fake L) + 20480 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 1085440 + pos * 128) by reflexivity.
  assert (JB : Z.of_nat jn < 8192) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  eapply evtF_mono.
  { eapply (stack_malloc1_gspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60ee40 (al_fake L) h pos flag F jn j24 j56 sh0 sh1 h0 h2 hs);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm1_W in MU. rewrite SHF in MU.

  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 8 <= a < (al_fake L) + 16) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 120 <= a < F + 128) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 16) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 128 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (32 * k + 8480 + pos). lia. }

  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm1 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB1 F) LB) by exact NOTIN0.
  assert (HFK' : AFAKE L (FB1 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists h0, (Z_to_bv 64 (h + Z.of_nat jn + 1)), h2, hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGCg MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 1) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 1 pos' 1 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 1 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 1 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - split; [| xportk TFSC MU WM ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)].
      intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 1 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 1) with 128 in Hin by reflexivity. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }

  assert (BL' : ablocks L st X (FB1 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB1 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 128 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (1, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 1) with 128 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 1 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 1) with 128 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 128)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
        D3 D24 D56 DS2 DS3 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 88 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 88) with 88%nat in J1.
  assert (LJ : length junk1 = 88%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 96 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 1 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app bsegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 96 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app bsegs m' (F + 24) [C8 sp] [CB 88 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 96) with (F + 120) by lia. exact F56'. }

  unfold sm1_postG. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm1P.

Module AFake_sm1PB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm1g. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2gc.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm1gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcP.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHt := (AFake_arep.AH (gb:=true) DI AQ ASEC).
Notation AHf := (AFake_arep.AH (gb:=false) DI AQ ASEC).
Hypothesis HLt : ahole_laws AHt.
Notation AH := AHt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Notation AREP_cells := (AFake_arep.AREP_cells (gb:=true) DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE (gb:=true) DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' (gb:=true) DI AQ ASEC HLt).
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].

Definition sm1_postGB (rsf : Z -> Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m'
    /\ AHEAP_P AHf L RNG st (FB1 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m'
    /\ F mod 128 = 0 /\ ablk F (F + 128) /\ F + 128 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 96 junk; C8 (Z_to_bv 64 (fflag L 1 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 128 /\ rng RNG (shad F) 16
    /\ rw_cells bsegs m' (F + 24) [C8 sp].

Theorem stack_malloc_1_GB : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (rsf : Z -> Z),
  AHEAP_P AH L RNG st LB m ->
  Z.of_nat (fk_count 1 LB) < 8192 ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> c <= 2) ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> 0 <= rsf F < 2^64 /\ rw_cells bsegs m (F + 24) [C8 (Z_to_bv 64 (rsf F))]) ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm1_postGB rsf L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC1) fc None m (seg_rom bsegs)).
Proof.
  intros until rsf. intros AHP NOTFULL CLS RS MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). change (rw_cells bsegs m (al_fake L + 96) [C1 (Z_to_bv 8 1)]) in NGC. pose proof NGC as NGCg.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd3680 0x16b718 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd43c0 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0xd43b0 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h1).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (gc_probe L LB m rsf (al_bot L) (bv_unsigned sp) HFK NDLB 1 h ltac:(lia) ltac:(change (fk_nframes 1) with 8192; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 1) with 8192 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 8192 = Z.land x 8191) by (intros x; change 8191 with (Z.ones 13); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 8191). set (flag := (al_fake L) + 20480 + pos). set (F := (al_fake L) + 1085440 + pos * 128).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 8192).
  { subst pos. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 1 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 1 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 1 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 135680 + 16 * pos = shad F /\ shad F + 16 <= shad (al_fake L) + 1446400 /\ shad F + 16 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 16 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  pose proof I as FL0.
  assert (FREEc : gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 1 pos = Z_to_bv 8 0).
  { unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> bv_unsigned (gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 1 (Z.land (h + t) 8191)) <> 0).
  { intros t Ht. rewrite EJ in Ht. rewrite <- LM. exact (BUSYz t Ht). }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 1) F 128) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  assert (TBND : rw_cells bsegs m (al_t L + 8) [C8 (Z_to_bv 64 (al_top L)); C8 (Z_to_bv 64 (al_bot L))] /\ rw_cells bsegs m (al_t L + 40) [C1 (Z_to_bv 8 0)]).
  { pose proof AR as ARx. destruct ARx as (_ & _ & _ & THRx & _). destruct THRx as (T0x & T40x & _). split; [| exact T40x].
    rw_split T0x 1%nat T0a T0b. exact T0b. }
  destruct TBND as [TB8 TB40].

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 88 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 120) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH4). pose proof SH4 as SH0. pose proof SH4 as SH1. pose proof DS2 as DS3.

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 h0; C8 (Z_to_bv 64 h); C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 8191) by reflexivity. assert (HFLAG : flag = (al_fake L) + 20480 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 1085440 + pos * 128) by reflexivity.
  assert (JB : Z.of_nat jn < 8192) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  pose proof (gfl_cell L LB m HFK) as GFLC. pose proof (grs_cell L LB m rsf HFK RS) as GRSC. pose proof (gfreed_shadow L LB m rsf (al_bot L) (bv_unsigned sp) HFK CLS) as GSHC.
  eapply evtF_mono.
  { eapply (stack_malloc1_gcspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60ee40 (al_fake L) h pos flag F (al_top L) (al_bot L) jn (Z_to_bv 8 1) (gfl L m) (grs L rsf) j24 j56 sh0 sh1 h0 h2 hs);
      try exact MI; try exact ST; try exact TP; try exact GFLC; try exact GRSC; try exact GSHC; try exact BUSYc; try exact FREEc; try exact TB8; try exact TB40;
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia); try (cbn; discriminate).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & NGC' & HNT2 & FL1 & F24' & F56' & SH' & FLAGS').
  unfold sm1gc_W in MU.

  assert (SHH : 0x7fff8000 <= shad (al_fake L + 36864) /\ shad (al_fake L + 11571200) <= 0x10007fff8000
                /\ shad (al_fake L + 11571200) = shad (al_fake L) + 1446400 /\ shad (al_fake L) <= shad (al_fake L + 36864)).
  { rewrite !gc_shad_eq. pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. clear - G1 G2c G3 ATR. Z.div_mod_to_equations. lia. }
  destruct SHH as (SHH1 & SHH2 & SHH3 & SHH4).
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 240 <= a < bv_unsigned sp) -> ~ (al_fake L <= a < al_fake L + 4096) -> a <> flag ->
            ~ (F <= a < F + 128) -> ~ (shad F <= a < shad F + 16) ->
            disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) a 1 ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 DG. apply MU. rewrite wa_unsigned by lia. cbn [outside].
    repeat (split; [lia|]). eapply disjoint_outside; [exact DG| lia]. }
  assert (DGH : forall A k, 0 <= k -> (A + k <= al_fake L + 4096 \/ al_fake L + 36864 <= A) ->
            (A + k <= shad (al_fake L + 36864) \/ shad (al_fake L + 11571200) <= A) -> disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) A k)
    by (intros A k K H1 H2; apply gcWall_disj_hulls; assumption).
  assert (F64 : F mod 128 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (32 * k + 8480 + pos). lia. }

  pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c.
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext AH HLt L st X m m' _ ALO AR MU WM). assert (SHLx : shlen 11571200 = 1446400) by reflexivity.
    lazymatch goal with |- Forall _ ?W => change (Forall (aext L) W) end.
    repeat (apply Forall_cons; [unfold aext; rewrite ?SHLx; cbn [fst snd]; intros _;
      first [left; clear -HFLAG HFF PB; lia | right; left; clear -SB1 SB2 SB3 PB; lia | right; right; left; clear -BOT LO; lia]|]).
    exact (gcWall_aext L (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 G1). }
  assert (NOTIN : ~ In (FB1 F) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) by exact NOTIN0.
  Local Ltac xportG H MU WM DGH K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length];
      repeat (split; [first [K; lia | lia]|]); apply DGH; first [K; lia | lia]].
  assert (CE' : afake_cells L m').
  { unfold afake_cells. split; [xportG REAL MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTVP MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DV MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTV1 MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|].
    split; [xportG BD MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG CF MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG VERB MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
  assert (LOG' : rw_cells bsegs m' (al_fake L + 88) [C8 (Z_to_bv 64 20)]) by (xportG LOG MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)).
  assert (HFK' : AFAKE (gb:=false) L (FB1 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { rewrite EFR. change 128 with (fk_fsize 1).
    eapply (afake_after_gc L LB m rsf (al_bot L) (bv_unsigned sp)) with (c0 := 1) (pos0 := pos).
    all: try lazymatch goal with
         | |- AFAKE _ _ _ => exact HFK
         | |- wmono _ _ _ => exact WM
         | |- afake_cells _ _ => exact CE'
         | |- rw_cells _ _ (_ + 88) _ => exact LOG'
         | |- rw_cells _ _ (_ + 96) _ => exact NGC'
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; CB 64 _] => exact HNT2
         | |- rw_cells _ _ (fk_flag _ _ _) _ => rewrite <- EFL; exact FL1
         | |- ~ In _ _ => rewrite <- EFR; exact NOTIN
         | |- rw_cells _ _ (_ + 72) _ => xportG TFSC MU WM DGH ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)
         | |- forall c p, _ => intros c' p' Hc' Hp' NE'; apply FLAGS'; [exact Hc'| exact Hp'|]; intros E'; apply NE'; rewrite E'; f_equal; rewrite HFLAG; lia
         end.
    all: try (change (gcN 1) with 8192; lia). all: try lia. }

  assert (BL' : ablocks L st X (FB1 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate|]. apply fk_kept_In in Hin as [Hin _]. exact (B1 p A n Hin).
    - intros c' A n [E|Hin]; [| apply fk_kept_In in Hin as [Hin _]; exact (B2 c' A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - change (List.NoDup (hb_ids (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))). rewrite fk_kept_hb_ids. exact B3.
    - constructor; [exact NOTIN| apply fk_kept_NoDup; exact B4]. }
  assert (AHP' : AHEAP_P AHf L RNG st (FB1 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 128 <= ab_addr b)).
  { intros b HbK. pose proof (proj1 (proj1 (fk_kept_In LB rsf (al_bot L) (bv_unsigned sp) b) HbK)) as Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (1, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in HbK. replace (fk_fsize 1) with 128 in HbK by reflexivity. exact HbK. }
      pose proof (fk_frames_disjoint L c' pos' 1 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 1) with 128 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 128)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
        D3 D24 D56 DS2 DS3 RR A10.
  assert (HPR : aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m').
  { assert (SHFLO : 2147450880 <= shad F) by (rewrite SHF; clear - GL1 HFF PB; Z.div_mod_to_equations; lia).
    intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; [exact Ha| clear - Hs; lia| clear - Hs G3 BOT LO; lia| clear - Hs G3 BOT LO HFLAG PB; lia| clear - Hs G3 BOT LO HFF PB; lia| clear - Hs SB3 BOT LO ATR; lia
                 | apply DGH; [lia| right; clear - Hs G3 BOT LO; lia| right; clear - Hs SHH2 BOT LO ATR; lia]].
    - pose proof (CI_OK iv Hiv) as HCI.
      apply OUT; [exact Ha| clear - HCI Hr BOT LO ATR; lia| clear - HCI Hr GL1; lia| clear - HCI Hr GL1 HFLAG PB; lia| clear - HCI Hr GL1 HFF PB; lia| clear - HCI Hr SHFLO; lia
                 | apply DGH; [lia| left; clear - HCI Hr GL1; lia| left; clear - HCI Hr SHH1; lia]].
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1.
      apply OUT; [exact Ha| clear - Hr Y2 BOT LO; lia| clear - Hr Y3; lia| clear - Hr Y3 HFLAG PB; lia| clear - Hr Y4; lia| clear - Hr Y1 SHFLO SB3; lia
                 | apply DGH; [lia| clear - Hr Y3; lia| clear - Hr Y1 SHH1 SHH2; lia]].
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      assert (F8 : F mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
      apply OUT; [lia| rewrite SHA; clear - A'R ATR LO BOT; lia| rewrite SHA; clear - A'R G2c; lia| rewrite SHA, HFLAG; clear - A'R G2c PB; lia
                 | rewrite SHA; clear - A'R G2c G3 HFF PB; lia| rewrite SHA, SHF; clear - A'R NA F8; Z.div_mod_to_equations; lia|].
      destruct Ha' as [SA|[(iv & Hiv & Hr)|(cls & FA & fn & HbK & Hr)]].
      + apply DGH; [lia| rewrite SHA; clear - SA ATR G2c G3; lia|]. right. rewrite SHA, gc_shad_eq. clear - SA G3. Z.div_mod_to_equations. lia.
      + pose proof (CI_OK iv Hiv). apply DGH; [lia| rewrite SHA; clear - A'R G2c; lia|]. left. rewrite SHA, gc_shad_eq. clear - H Hr GL1. unfold AIMG_HI in *. Z.div_mod_to_equations. lia.
      + apply fk_kept_In in HbK as [HbL ALIVE].
        pose proof (afake_lb L LB m cls FA fn HFK HbL) as (Hc' & Hn' & Np' & F64' & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
        pose proof HFK as (_ & _ & _ & _ & _ & _ & _ & _ & LVx & _). destruct (LVx _ _ _ HbL) as (_ & _ & pos2 & Hp2 & HF2 & B1x).
        assert (pos2 = pos') by (apply (fk_frame_inj L cls); [lia| congruence]). subst pos2.
        assert (E1 : gfl L m cls pos' = Z_to_bv 8 1) by (unfold gfl; rewrite B1x; reflexivity).
        assert (NF : gfreed (al_bot L) (bv_unsigned sp) (gfl L m cls pos') (grs L rsf cls pos') = false).
        { rewrite (gfreed_dead L m rsf (al_bot L) (bv_unsigned sp) cls pos' Hc' Hp') by (rewrite E1; discriminate). rewrite <- HF', <- Hn'. exact ALIVE. }
        pose proof (gc_pows cls Hc') as (_ & _ & _ & _ & P8 & PC). unfold fk_fsize in Hn'.
        eapply (gcWall_disj_kept_shadow (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 cls pos'); [exact Hc'| exact Hp'| exact NF| | | lia].
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. clear - Hr. Z.div_mod_to_equations. lia.
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. remember (2 ^ cls) as K. clear - Hr Hn' P8 PC F64'. Z.div_mod_to_equations. lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 88 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 88) with 88%nat in J1.
  assert (LJ : length junk1 = 88%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 96 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 1 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app bsegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 96 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app bsegs m' (F + 24) [C8 sp] [CB 88 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 96) with (F + 120) by lia. exact F56'. }

  unfold sm1_postGB. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm1PB.

Module AFake_sm2P.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2g.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AH := (AFake_arep.AH DI AQ ASEC).
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation AREP_cells := (AFake_arep.AREP_cells DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' DI AQ ASEC HL).
Notation arep_ext_sm2 := (AFake_arep.arep_ext_sm2 DI AQ ASEC HL).
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].

Definition sm2_postG (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB2 F :: LB) m'
    /\ F mod 256 = 0 /\ ablk F (F + 256) /\ F + 256 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 (fflag L 2 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 256 /\ rng RNG (shad F) 32
    /\ rw_cells bsegs m' (F + 24) [C8 sp].

Theorem stack_malloc_2_GA : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  gcbit = false ->
  Z.of_nat (fk_count 2 LB) < 4096 ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm2_postG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros AHP GCB0 NOTFULL MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). pose proof NGC as NGCg. rewrite GCB0 in NGC.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd3680 0x16b718 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd43c0 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0xd43b0 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h2).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (afake_first_free L LB m 2 h HFK NDLB ltac:(unfold FK_NCLS; lia) ltac:(change (fk_nframes 2) with 4096; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 2) with 4096 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 4096 = Z.land x 4095) by (intros x; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 4095). set (flag := (al_fake L) + 28672 + pos). set (F := (al_fake L) + 2134016 + pos * 256).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 2 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 2 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 2 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 266752 + 32 * pos = shad F /\ shad F + 32 <= shad (al_fake L) + 1446400 /\ shad F + 32 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 32 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  assert (FL0 : rw_cells bsegs m flag [C1 (Z_to_bv 8 0)]).
  { rewrite EFL. unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> exists b : byte, rw_cells bsegs m (sm2_flag (al_fake L) (h + t)) [C1 b] /\ bv_unsigned b <> 0).
  { intros t Ht. rewrite EJ in Ht. destruct (BUSYz t Ht) as (b & Cb & NZb). exists b. split; [| exact NZb].
    unfold sm2_flag. rewrite <- LM. unfold fk_flag, fk_flags in Cb. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub] in Cb.
    eapply rw_cells_at_eq; [exact Cb| lia]. }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 2) F 256) LB).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 216 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 248) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F + 16) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS3.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH0). destruct (c8c8_of_dc m _ DS3) as (sh2 & sh3 & SH1).
  assert (SH4 : rw_cells bsegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3]).
  { apply (proj2 (rw_cells_app bsegs m (shad F) [C8 sh0; C8 sh1] [C8 sh2; C8 sh3])). split; [exact SH0|].
    cbn [cells_size csize Nat.add]. replace (shad F + Z.of_nat 16) with (shad F + 16) by lia. exact SH1. }

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 4095) by reflexivity. assert (HFLAG : flag = (al_fake L) + 28672 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 2134016 + pos * 256) by reflexivity.
  assert (JB : Z.of_nat jn < 4096) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  eapply evtF_mono.
  { eapply (stack_malloc2_gspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60ee40 (al_fake L) h pos flag F jn j24 j56 sh0 sh1 sh2 sh3 h0 h1 hs);
      try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm2_W in MU. rewrite SHF in MU.

  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 16 <= a < (al_fake L) + 24) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 248 <= a < F + 256) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 32) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 256 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (16 * k + 8336 + pos). lia. }

  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm2 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB2 F) LB) by exact NOTIN0.
  assert (HFK' : AFAKE L (FB2 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split; [exists h0, h1, (Z_to_bv 64 (h + Z.of_nat jn + 1)), hs; exact HNT2|].
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGCg MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 2) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 2 pos' 2 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 2 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - split; [| xportk TFSC MU WM ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)].
      intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 2) with 256 in Hin by reflexivity. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }

  assert (BL' : ablocks L st X (FB2 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB2 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 256 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (2, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 2) with 256 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 2 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 2) with 256 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 256)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
        D3 D24 D56 DS2 DS3 RR A10.
  assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
  { intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA in Ha |- *.
      pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
      apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 216 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 216) with 216%nat in J1.
  assert (LJ : length junk1 = 216%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 224 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 2 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app bsegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 224 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app bsegs m' (F + 24) [C8 sp] [CB 216 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 224) with (F + 248) by lia. exact F56'. }

  unfold sm2_postG. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm2P.

Module AFake_sm2PB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RtCells.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.FsKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_tlsga.TwinB.F_tlsga. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_m2s_b.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm0.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_cnt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcl.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcf.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2gc.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2gc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_gcP.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AHt := (AFake_arep.AH (gb:=true) DI AQ ASEC).
Notation AHf := (AFake_arep.AH (gb:=false) DI AQ ASEC).
Hypothesis HLt : ahole_laws AHt.
Notation AH := AHt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation AREP_cells := (AFake_arep.AREP_cells (gb:=true) DI AQ ASEC).
Notation HB_FAKE := (AFake_arep.HB_FAKE (gb:=true) DI AQ ASEC).
Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' (gb:=true) DI AQ ASEC HLt).
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].

Definition sm2_postGB (rsf : Z -> Z) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m'
    /\ AHEAP_P AHf L RNG st (FB2 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m'
    /\ F mod 256 = 0 /\ ablk F (F + 256) /\ F + 256 <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 224 junk; C8 (Z_to_bv 64 (fflag L 2 F))]
    /\ rw_cells bsegs m' (shad F) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rng RNG F 256 /\ rng RNG (shad F) 32
    /\ rw_cells bsegs m' (F + 24) [C8 sp].

Theorem stack_malloc_2_GB : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z) (rsf : Z -> Z),
  AHEAP_P AH L RNG st LB m ->
  Z.of_nat (fk_count 2 LB) < 4096 ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> c <= 2) ->
  (forall c F n, In (mkABlock (ABFake c) F n) LB -> 0 <= rsf F < 2^64 /\ rw_cells bsegs m (F + 24) [C8 (Z_to_bv 64 (rsf F))]) ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm2_postGB rsf L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom bsegs)).
Proof.
  intros until rsf. intros AHP NOTFULL CLS RS MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV & TFSC). change (rw_cells bsegs m (al_fake L + 96) [C1 (Z_to_bv 8 1)]) in NGC. pose proof NGC as NGCg.
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).

  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).

  pose proof (relro_word m 0xd3680 0x16b718 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd43c0 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0xd43b0 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.

  set (h := bv_unsigned h2).
  assert (NDLB : List.NoDup LB) by (destruct BL as (_ & _ & _ & ND4); exact ND4).
  destruct (gc_probe L LB m rsf (al_bot L) (bv_unsigned sp) HFK NDLB 2 h ltac:(lia) ltac:(change (fk_nframes 2) with 4096; exact NOTFULL))
    as (jz & JZ & BUSYz & FREEz & NOTINz).
  change (fk_nframes 2) with 4096 in JZ, BUSYz, FREEz, NOTINz.
  set (jn := Z.to_nat jz). assert (EJ : Z.of_nat jn = jz) by (subst jn; apply Z2Nat.id; lia).
  assert (LM : forall x, x mod 4096 = Z.land x 4095) by (intros x; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; reflexivity).
  set (pos := Z.land (h + Z.of_nat jn) 4095). set (flag := (al_fake L) + 28672 + pos). set (F := (al_fake L) + 2134016 + pos * 256).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (PB : 0 <= pos < 4096).
  { subst pos. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL : flag = fk_flag L 2 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 2 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 2 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 266752 + 32 * pos = shad F /\ shad F + 32 <= shad (al_fake L) + 1446400 /\ shad F + 32 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 32 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
  pose proof I as FL0.
  assert (FREEc : gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 2 pos = Z_to_bv 8 0).
  { unfold pos. rewrite <- LM, EJ. exact FREEz. }
  assert (BUSYc : forall t, 0 <= t < Z.of_nat jn -> bv_unsigned (gfl' (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 2 (Z.land (h + t) 4095)) <> 0).
  { intros t Ht. rewrite EJ in Ht. rewrite <- LM. exact (BUSYz t Ht). }
  assert (NOTIN0 : ~ In (mkABlock (ABFake 2) F 256) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))).
  { rewrite EFR. unfold pos. rewrite <- LM, EJ. exact NOTINz. }

  assert (TBND : rw_cells bsegs m (al_t L + 8) [C8 (Z_to_bv 64 (al_top L)); C8 (Z_to_bv 64 (al_bot L))] /\ rw_cells bsegs m (al_t L + 40) [C1 (Z_to_bv 8 0)]).
  { pose proof AR as ARx. destruct ARx as (_ & _ & _ & THRx & _). destruct THRx as (T0x & T40x & _). split; [| exact T40x].
    rw_split T0x 1%nat T0a T0b. exact T0b. }
  destruct TBND as [TB8 TB40].

  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 216 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 248) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].

  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F + 16) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS3.
  destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH0). destruct (c8c8_of_dc m _ DS3) as (sh2 & sh3 & SH1).
  assert (SH4 : rw_cells bsegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3]).
  { apply (proj2 (rw_cells_app bsegs m (shad F) [C8 sh0; C8 sh1] [C8 sh2; C8 sh3])). split; [exact SH0|].
    cbn [cells_size csize Nat.add]. replace (shad F + Z.of_nat 16) with (shad F + 16) by lia. exact SH1. }

  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').

  assert (HNT' : rw_cells bsegs m (al_fake L) [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).

  pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (HPOS : pos = Z.land (h + Z.of_nat jn) 4095) by reflexivity. assert (HFLAG : flag = (al_fake L) + 28672 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 2134016 + pos * 256) by reflexivity.
  assert (JB : Z.of_nat jn < 4096) by (rewrite EJ; lia). clearbody h pos flag F. clear BUSYz FREEz NOTINz.
  pose proof (gfl_cell L LB m HFK) as GFLC. pose proof (grs_cell L LB m rsf HFK RS) as GRSC. pose proof (gfreed_shadow L LB m rsf (al_bot L) (bv_unsigned sp) HFK CLS) as GSHC.
  eapply evtF_mono.
  { eapply (stack_malloc2_gcspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
               FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x60ee40 (al_fake L) h pos flag F (al_top L) (al_bot L) jn (Z_to_bv 8 1) (gfl L m) (grs L rsf) j24 j56 sh0 sh1 sh2 sh3 h0 h1 hs);
      try exact MI; try exact ST; try exact TP; try exact GFLC; try exact GRSC; try exact GSHC; try exact BUSYc; try exact FREEc; try exact TB8; try exact TB40;
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia); try (cbn; discriminate).
    all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
      split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
      split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    all: try (eapply rng_sub'; [exact A3| lia]). }
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & NGC' & HNT2 & FL1 & F24' & F56' & SH' & FLAGS').
  unfold sm2gc_W in MU.

  assert (SHH : 0x7fff8000 <= shad (al_fake L + 36864) /\ shad (al_fake L + 11571200) <= 0x10007fff8000
                /\ shad (al_fake L + 11571200) = shad (al_fake L) + 1446400 /\ shad (al_fake L) <= shad (al_fake L + 36864)).
  { rewrite !gc_shad_eq. pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. clear - G1 G2c G3 ATR. Z.div_mod_to_equations. lia. }
  destruct SHH as (SHH1 & SHH2 & SHH3 & SHH4).
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 240 <= a < bv_unsigned sp) -> ~ (al_fake L <= a < al_fake L + 4096) -> a <> flag ->
            ~ (F <= a < F + 256) -> ~ (shad F <= a < shad F + 32) ->
            disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) a 1 ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 DG. apply MU. rewrite wa_unsigned by lia. cbn [outside].
    repeat (split; [lia|]). eapply disjoint_outside; [exact DG| lia]. }
  assert (DGH : forall A k, 0 <= k -> (A + k <= al_fake L + 4096 \/ al_fake L + 36864 <= A) ->
            (A + k <= shad (al_fake L + 36864) \/ shad (al_fake L + 11571200) <= A) -> disjoint_from (gcWall (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) 0 GC_NCLS) A k)
    by (intros A k K H1 H2; apply gcWall_disj_hulls; assumption).
  assert (F64 : F mod 256 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (16 * k + 8336 + pos). lia. }

  pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c.
  assert (AR' : AREP AH L st X m').
  { eapply (AREP_frame_ext AH HLt L st X m m' _ ALO AR MU WM). assert (SHLx : shlen 11571200 = 1446400) by reflexivity.
    lazymatch goal with |- Forall _ ?W => change (Forall (aext L) W) end.
    repeat (apply Forall_cons; [unfold aext; rewrite ?SHLx; cbn [fst snd]; intros _;
      first [left; clear -HFLAG HFF PB; lia | right; left; clear -SB1 SB2 SB3 PB; lia | right; right; left; clear -BOT LO; lia]|]).
    exact (gcWall_aext L (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 G1). }
  assert (NOTIN : ~ In (FB2 F) (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) by exact NOTIN0.
  Local Ltac xportG H MU WM DGH K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length];
      repeat (split; [first [K; lia | lia]|]); apply DGH; first [K; lia | lia]].
  assert (CE' : afake_cells L m').
  { unfold afake_cells. split; [xportG REAL MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTVP MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DV MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG DTV1 MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|].
    split; [xportG BD MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG CF MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. split; [xportG VERB MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
  assert (LOG' : rw_cells bsegs m' (al_fake L + 88) [C8 (Z_to_bv 64 20)]) by (xportG LOG MU WM DGH ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)).
  assert (HFK' : AFAKE (gb:=false) L (FB2 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { rewrite EFR. change 256 with (fk_fsize 2).
    eapply (afake_after_gc L LB m rsf (al_bot L) (bv_unsigned sp)) with (c0 := 2) (pos0 := pos).
    all: try lazymatch goal with
         | |- AFAKE _ _ _ => exact HFK
         | |- wmono _ _ _ => exact WM
         | |- afake_cells _ _ => exact CE'
         | |- rw_cells _ _ (_ + 88) _ => exact LOG'
         | |- rw_cells _ _ (_ + 96) _ => exact NGC'
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; CB 64 _] => exact HNT2
         | |- rw_cells _ _ (fk_flag _ _ _) _ => rewrite <- EFL; exact FL1
         | |- ~ In _ _ => rewrite <- EFR; exact NOTIN
         | |- rw_cells _ _ (_ + 72) _ => xportG TFSC MU WM DGH ltac:(clear -G7s G8 G11 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR SHH1 SHH2 G2c)
         | |- forall c p, _ => intros c' p' Hc' Hp' NE'; apply FLAGS'; [exact Hc'| exact Hp'|]; intros E'; apply NE'; rewrite E'; f_equal; rewrite HFLAG; lia
         end.
    all: try (change (gcN 2) with 4096; lia). all: try lia. }

  assert (BL' : ablocks L st X (FB2 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate|]. apply fk_kept_In in Hin as [Hin _]. exact (B1 p A n Hin).
    - intros c' A n [E|Hin]; [| apply fk_kept_In in Hin as [Hin _]; exact (B2 c' A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - change (List.NoDup (hb_ids (fk_kept LB rsf (al_bot L) (bv_unsigned sp)))). rewrite fk_kept_hb_ids. exact B3.
    - constructor; [exact NOTIN| apply fk_kept_NoDup; exact B4]. }
  assert (AHP' : AHEAP_P AHf L RNG st (FB2 F :: (fk_kept LB rsf (al_bot L) (bv_unsigned sp))) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }

  assert (BLK : forall b, In b (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 256 <= ab_addr b)).
  { intros b HbK. pose proof (proj1 (proj1 (fk_kept_In LB rsf (al_bot L) (bv_unsigned sp) b) HbK)) as Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (2, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in HbK. replace (fk_fsize 2) with 256 in HbK by reflexivity. exact HbK. }
      pose proof (fk_frames_disjoint L c' pos' 2 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 2) with 256 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 256)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC NGCg DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
        D3 D24 D56 DS2 DS3 RR A10.
  assert (HPR : aheap_pres CI (fk_kept LB rsf (al_bot L) (bv_unsigned sp)) (bv_unsigned sp) m m').
  { assert (SHFLO : 2147450880 <= shad F) by (rewrite SHF; clear - GL1 HFF PB; Z.div_mod_to_equations; lia).
    intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
    destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - apply OUT; [exact Ha| clear - Hs; lia| clear - Hs G3 BOT LO; lia| clear - Hs G3 BOT LO HFLAG PB; lia| clear - Hs G3 BOT LO HFF PB; lia| clear - Hs SB3 BOT LO ATR; lia
                 | apply DGH; [lia| right; clear - Hs G3 BOT LO; lia| right; clear - Hs SHH2 BOT LO ATR; lia]].
    - pose proof (CI_OK iv Hiv) as HCI.
      apply OUT; [exact Ha| clear - HCI Hr BOT LO ATR; lia| clear - HCI Hr GL1; lia| clear - HCI Hr GL1 HFLAG PB; lia| clear - HCI Hr GL1 HFF PB; lia| clear - HCI Hr SHFLO; lia
                 | apply DGH; [lia| left; clear - HCI Hr GL1; lia| left; clear - HCI Hr SHH1; lia]].
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1.
      apply OUT; [exact Ha| clear - Hr Y2 BOT LO; lia| clear - Hr Y3; lia| clear - Hr Y3 HFLAG PB; lia| clear - Hr Y4; lia| clear - Hr Y1 SHFLO SB3; lia
                 | apply DGH; [lia| clear - Hr Y3; lia| clear - Hr Y1 SHH1 SHH2; lia]].
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      assert (F8 : F mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
      apply OUT; [lia| rewrite SHA; clear - A'R ATR LO BOT; lia| rewrite SHA; clear - A'R G2c; lia| rewrite SHA, HFLAG; clear - A'R G2c PB; lia
                 | rewrite SHA; clear - A'R G2c G3 HFF PB; lia| rewrite SHA, SHF; clear - A'R NA F8; Z.div_mod_to_equations; lia|].
      destruct Ha' as [SA|[(iv & Hiv & Hr)|(cls & FA & fn & HbK & Hr)]].
      + apply DGH; [lia| rewrite SHA; clear - SA ATR G2c G3; lia|]. right. rewrite SHA, gc_shad_eq. clear - SA G3. Z.div_mod_to_equations. lia.
      + pose proof (CI_OK iv Hiv). apply DGH; [lia| rewrite SHA; clear - A'R G2c; lia|]. left. rewrite SHA, gc_shad_eq. clear - H Hr GL1. unfold AIMG_HI in *. Z.div_mod_to_equations. lia.
      + apply fk_kept_In in HbK as [HbL ALIVE].
        pose proof (afake_lb L LB m cls FA fn HFK HbL) as (Hc' & Hn' & Np' & F64' & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
        pose proof HFK as (_ & _ & _ & _ & _ & _ & _ & _ & LVx & _). destruct (LVx _ _ _ HbL) as (_ & _ & pos2 & Hp2 & HF2 & B1x).
        assert (pos2 = pos') by (apply (fk_frame_inj L cls); [lia| congruence]). subst pos2.
        assert (E1 : gfl L m cls pos' = Z_to_bv 8 1) by (unfold gfl; rewrite B1x; reflexivity).
        assert (NF : gfreed (al_bot L) (bv_unsigned sp) (gfl L m cls pos') (grs L rsf cls pos') = false).
        { rewrite (gfreed_dead L m rsf (al_bot L) (bv_unsigned sp) cls pos' Hc' Hp') by (rewrite E1; discriminate). rewrite <- HF', <- Hn'. exact ALIVE. }
        pose proof (gc_pows cls Hc') as (_ & _ & _ & _ & P8 & PC). unfold fk_fsize in Hn'.
        eapply (gcWall_disj_kept_shadow (al_fake L) (gfl L m) (grs L rsf) (al_bot L) (bv_unsigned sp) G2 G3 cls pos'); [exact Hc'| exact Hp'| exact NF| | | lia].
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. clear - Hr. Z.div_mod_to_equations. lia.
        * rewrite gframe_fk, <- HF', SHA, gc_shad_eq. remember (2 ^ cls) as K. clear - Hr Hn' P8 PC F64'. Z.div_mod_to_equations. lia. }

  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 216 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 216) with 216%nat in J1.
  assert (LJ : length junk1 = 216%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB 224 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 2 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app bsegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 224 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app bsegs m' (F + 24) [C8 sp] [CB 216 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 224) with (F + 248) by lia. exact F56'. }

  unfold sm2_postGB. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia]| exact F24'].
Qed.
End S.
End CANSEC1.
End AFake_sm2PB.
End TwinB.
