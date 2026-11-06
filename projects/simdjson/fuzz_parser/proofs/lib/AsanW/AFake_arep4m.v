(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt
     FsKit AFake_iface F_tlsga F_m2s_b AFake_arep AFake_sm4 AFake_sm4b AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].

Section CANSEC1. Context {rc : runConstT}.
Notation FB4 F := (mkABlock (ABFake 4) F 1024).
Definition SM4_STACK_P : Z := 4096.   (* [comment removed for export] *)

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Hypothesis HL : ahole_laws (AFake_arep.AH DI AQ ASEC).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation AH := (AFake_arep.AH DI AQ ASEC).

Definition sm4_postP (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP_P AH L RNG st (FB4 F :: LB) m'
    /\ F mod 1024 = 0 /\ ablk F (F + 1024) /\ F + 1024 <= ATOP
    /\ rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 992 junk; C8 (Z_to_bv 64 (fflag L 4 F))]
    /\ rw_cells asegs m' (shad F) (repeat (C8 (Z_to_bv 64 0)) 16)
    /\ rng RNG F 1024 /\ rng RNG (shad F) 128
    /\ (forall a, in_block LB a -> m' (wa (shad a)) = m (wa (shad a)))
    /\ (forall a, aclient_addr CI LB (bv_unsigned sp) a -> a < shad F \/ shad F + 128 <= a).

(* [comment removed for export] *)
Lemma arep_ext_sm4 : forall L st X m m' sp fs flag F,
  alayout_ok L -> AREP AH L st X m ->
  munch [(sp - 208, sp); (fs + 32, fs + 40); (flag, flag + 1); (F + 24, F + 32); (F + 1016, F + 1024); (2147450880 + F / 8, 2147450880 + F / 8 + 128)] m m' ->
  wmono asegs m m' ->
  fs = al_fake L -> ATOP <= sp - 208 -> fs + 4096 <= flag < fs + 36864 -> fs + 36864 <= F -> F + 1024 <= fs + 11571200 ->
  shad fs <= 2147450880 + F / 8 -> 2147450880 + F / 8 + 128 <= shad fs + 1446400 ->
  AREP AH L st X m'.
Proof.
  intros L st X m m' sp fs flag F ALO AR MU WM E S1 S2 S3 S4 S5 S6.
  assert (SHL : shlen 11571200 = 1446400) by reflexivity.
  eapply (AREP_frame_ext' DI AQ ASEC HL L st X m m' _ ALO AR MU WM). rewrite <- E, SHL. atop_facts.
  repeat (constructor; [cbn [fst snd]; intros _ |]); [right; right; lia| left; lia| left; lia| left; lia| left; lia| right; left; lia| constructor].
Qed.

Theorem stack_malloc_4_P : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  (forall F1 n1 F2 n2, In (mkABlock (ABFake 4) F1 n1) LB -> In (mkABlock (ABFake 4) F2 n2) LB -> F1 = F2) ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM4_STACK_P ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) ->
  evtF asegs RNG (sm4_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC4P) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros AHP ONE MI ST BOT LO SPT TP RSTK.
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
  pose proof (relro_word m 0x107350 0x19f598 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0x1080b8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0x1080a8 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM4_STACK_P in *.
  (* [comment removed for export] *)
  assert (DH : dc_at m (al_fake L) 88).
  { pose proof (dc_of_cells m (al_fake L) _ HNT) as D. exact D. }
  destruct (c8_of_dc m (al_fake L + 32) (dc_sub m (al_fake L) 88 (al_fake L + 32) 8 DH ltac:(lia) ltac:(lia) ltac:(lia))) as [hw HW].
  set (h := bv_unsigned hw).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  assert (HW' : rw_cells asegs m (al_fake L + 32) [C8 (Z_to_bv 64 h)]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HW).
  clear HW.
  (* [comment removed for export] *)
  set (pos0 := Z.land h 1023). set (flag0 := al_fake L + 34816 + pos0).
  assert (PB0 : 0 <= pos0 < 1024).
  { subst pos0. change 1023 with (Z.ones 10). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL0 : flag0 = fk_flag L 4 pos0) by (subst flag0; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag0 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D30.
  destruct (c1_of_dc m flag0 D30) as [fb0 FB0].
  assert (CH : exists k pos, (k = 0 \/ k = 1) /\ pos = Z.land (h + k) 1023 /\ 0 <= pos < 1024
               /\ rw_cells asegs m (al_fake L + 34816 + pos) [C1 (Z_to_bv 8 0)]
               /\ (k = 1 -> rw_cells asegs m flag0 [C1 (Z_to_bv 8 (bv_unsigned fb0))] /\ 0 < bv_unsigned fb0 < 256)).
  { destruct (decide (fb0 = Z_to_bv 8 0)) as [E|NE].
    - exists 0, pos0. split; [left; reflexivity|]. split; [subst pos0; f_equal; lia|]. split; [exact PB0|].
      split; [rewrite <- E; exact FB0| intros K; discriminate K].
    - assert (IN0 : In (FKB 4 (fk_frame L 4 pos0) (fk_fsize 4)) LB).
      { apply (FL 4 pos0 fb0); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
        rewrite <- EFL0. apply (rw_C1_high m flag0 fb0 FB0). subst flag0. lia. }
      set (pos1 := Z.land (h + 1) 1023).
      assert (PB1 : 0 <= pos1 < 1024).
      { subst pos1. change 1023 with (Z.ones 10). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
      assert (P01 : pos0 <> pos1).
      { subst pos0 pos1. change 1023 with (Z.ones 10). rewrite !Z.land_ones by lia. clear. Z.div_mod_to_equations. lia. }
      pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (al_fake L + 34816 + pos1) 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D31.
      destruct (c1_of_dc m _ D31) as [fb1 FB1].
      assert (fb1 = Z_to_bv 8 0) as ->.
      { destruct (decide (fb1 = Z_to_bv 8 0)) as [E1|NE1]; [exact E1| exfalso].
        assert (IN1 : In (FKB 4 (fk_frame L 4 pos1) (fk_fsize 4)) LB).
        { apply (FL 4 pos1 fb1); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE1].
          replace (fk_flag L 4 pos1) with (al_fake L + 34816 + pos1) by (unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
          apply (rw_C1_high m _ fb1 FB1). lia. }
        pose proof (ONE _ _ _ _ IN0 IN1) as EQF. unfold fk_frame, fk_fsize in EQF. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in EQF.
        apply P01. clear - EQF. lia. }
      exists 1, pos1. split; [right; reflexivity|]. split; [reflexivity|]. split; [exact PB1|]. split; [exact FB1|].
      intros _. split; [rewrite (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 fb0); exact FB0|].
      pose proof (bv_unsigned_in_range _ fb0) as R0. change (bv_modulus 8) with 256 in R0. split; [| lia].
      destruct (Z.eq_dec (bv_unsigned fb0) 0) as [Z0|Z0]; [| lia].
      exfalso. apply NE. apply bv_eq. rewrite Z0. reflexivity. }
  destruct CH as (k & pos & Hk & POS & PB & FL0 & K1).
  set (flag := (al_fake L) + 34816 + pos). set (F := (al_fake L) + 4231168 + pos * 1024).
  assert (EFL : flag = fk_flag L 4 pos) by (subst flag; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  assert (EFR : F = fk_frame L 4 pos) by (subst F; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
  assert (EFF : fflag L 4 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
  assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct SHS as [SHS SHL]. rewrite SHL in *.
  assert (SHB : shad (al_fake L) + 528896 + 128 * pos = shad F /\ shad F + 128 <= shad (al_fake L) + 1446400 /\ shad F + 128 <= 0x10007fff8000).
  { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  assert (SHD : shad F + 128 <= al_fake L \/ al_fake L + 11571200 <= shad F).
  { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }
  (* [comment removed for export] *)
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 984 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 1016) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
  destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
  (* [comment removed for export] *)
  pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 128 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS.
  destruct DS as [shj SH0]. change (Z.to_nat 128) with 128%nat in SH0.
  (* [comment removed for export] *)
  destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
  (* [comment removed for export] *)
  assert (HFLAG : flag = (al_fake L) + 34816 + pos) by reflexivity.
  assert (HFF : F = (al_fake L) + 4231168 + pos * 1024) by reflexivity.
  assert (HFLAG0 : flag0 = al_fake L + 34816 + pos0) by reflexivity. assert (HPOS0 : pos0 = Z.land h 1023) by reflexivity.
  clearbody h flag F pos0 flag0. rewrite <- HFLAG in FL0.
  assert (WALK : evtF asegs RNG (sm4_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo (al_fake L) (h + k + 1) flag F m)
                   (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       FR (Z_to_bv 64 ASTKMALLOC4P) fc None m (seg_rom asegs))).
  { destruct Hk as [-> | ->].
    - replace (h + 0 + 1) with (h + 1) by lia. rewrite Z.add_0_r in POS.
      eapply (stack_malloc4_cspec0 RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x642e70 (al_fake L) h pos flag F j24 j56 shj);
        try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
      all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
        split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
        split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
      all: try (eapply rng_sub'; [exact RSTK| lia]).
      all: try (eapply rng_sub'; [exact A3| lia]).
    - replace (h + 1 + 1) with (h + 2) by lia.
      destruct (K1 eq_refl) as (FB0' & B0R).
      eapply (stack_malloc4_cspec1 RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x642e70 (al_fake L) h pos0 flag0 (bv_unsigned fb0) pos flag F j24 j56 shj);
        try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
      all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
        split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
        split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
      all: try (eapply rng_sub'; [exact RSTK| lia]).
      all: try (eapply rng_sub'; [exact A3| lia]). }
  eapply evtF_mono; [exact WALK|].
  cbv beta. intros ms' PO.
  destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
  unfold sm4_W in MU. rewrite SHF in MU.
  (* [comment removed for export] *)
  assert (OUT : forall a, 0 <= a < 2^64 ->
            ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 32 <= a < (al_fake L) + 40) -> a <> flag ->
            ~ (F + 24 <= a < F + 32) -> ~ (F + 1016 <= a < F + 1024) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 128) ->
            m' (wa a) = m (wa a)).
  { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
  assert (F64 : F mod 1024 = 0).
  { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [kk Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (4 * kk + 4132 + pos). lia. }
  (* [comment removed for export] *)
  assert (AR' : AREP AH L st X m').
  { eapply (arep_ext_sm4 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
  assert (NOTIN : ~ In (FB4 F) LB).
  { intros Hin. destruct (LV 4 F 1024 Hin) as (_ & _ & pos' & Hp' & HF' & B1).
    assert (pos' = pos) as ->.
    { rewrite EFR in HF'. unfold fk_frame, fk_fsize in HF'. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in HF'. clear - HF'. lia. }
    rewrite <- EFL in B1. pose proof (rw_C1_high m flag _ FL0 ltac:(lia)) as B0.
    assert (E : Z_to_bv 8 1 = Z_to_bv 8 0) by congruence. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate E. }
  assert (HFK' : AFAKE L (FB4 F :: LB) m').
  { split; [exact G|]. split.
    { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
      split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
    split.
    { (* [comment removed for export] *)
      pose proof (dc_at_any m m' (al_fake L) 88 DH WM ltac:(lia)) as DH'.
      destruct (dc_take m' (al_fake L) 88 24 DH' ltac:(lia)) as [DA DB]. replace (88 - 24) with 64 in DB by reflexivity.
      destruct (dc_take m' (al_fake L) 24 8 DA ltac:(lia)) as [DA0 DA1]. replace (24 - 8) with 16 in DA1 by reflexivity.
      destruct (c8_of_dc m' _ DA0) as [w0 W0]. destruct (c8c8_of_dc m' _ DA1) as (w1 & w2 & W12). destruct DB as [hs' HS'].
      exists w0, w1, w2, hs'.
      apply (proj2 (rw_cells_app asegs m' (al_fake L) [C8 w0] _)). split; [exact W0|]. cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app asegs m' (al_fake L + Z.of_nat 8) [C8 w1; C8 w2] _)). split; [replace (al_fake L + Z.of_nat 8) with (al_fake L + 8) by lia; exact W12|].
      cbn [cells_size csize Nat.add]. replace (al_fake L + Z.of_nat 8 + Z.of_nat 16) with (al_fake L + 24) by lia. exact HS'. }
    split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
    split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
    split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
    split.
    - intros c pos' b Hc Hp Hb NZ.
      destruct (Z.eq_dec c 4) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
      + left. rewrite <- EFR. unfold fk_fsize. reflexivity.
      + right. pose proof (fk_flags_disjoint L 4 pos' 4 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L 4 pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
      + right. pose proof (fk_flags_disjoint L c pos' 4 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
        rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
        rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
    - intros c F' n' [E|Hin].
      + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
        exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
        rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
      + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
        split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
        assert (NE : fk_flag L c pos' <> flag).
        { rewrite EFL. apply (fk_flags_disjoint L c pos' 4 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
          intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 4) with 1024 in Hin by reflexivity. exact Hin. }
        pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }
  (* [comment removed for export] *)
  assert (BL' : ablocks L st X (FB4 F :: LB)).
  { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
    - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
    - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
    - cbn. exact B3.
    - constructor; [exact NOTIN| exact B4]. }
  assert (AHP' : AHEAP_P AH L RNG st (FB4 F :: LB) m').
  { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }
  (* [comment removed for export] *)
  assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
            /\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
            /\ (ab_addr b + ab_size b <= F \/ F + 1024 <= ab_addr b)).
  { intros b Hb. destruct b as [[p|c'] A' n']; cbn.
    - pose proof (HB_FAKE DI AQ ASEC L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
    - pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
      assert (NEQ : (c', pos') <> (4, pos)).
      { intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
        replace (fk_fsize 4) with 1024 in Hb by reflexivity. exact Hb. }
      pose proof (fk_frames_disjoint L c' pos' 4 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
      rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 4) with 1024 in DJ by reflexivity.
      split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
  assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
            0 <= a' < 2^47 /\ ~ (F <= a' < F + 1024)).
  { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
      [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); unfold AIMG_HI in H; clear - Hr H GL1 HFF PB; lia |].
    destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
  clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT LOG NGC DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 DH
        D30 D24 D56 RR A10 FB0 K1.
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
  assert (SHX : forall a, aclient_addr CI LB (bv_unsigned sp) a -> a < shad F \/ shad F + 128 <= a).
  { intros a Hca. rewrite SHF. pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
    destruct Hca as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - clear - Hs SK3 BOT LO SPT GL1 G3 HFF PB ATR G2b; Z.div_mod_to_equations; lia.
    - pose proof (CI_OK iv Hiv) as CIv. unfold AIMG_HI in CIv. clear - CIv Hr HFF PB G3 GL1 G2b ATR; Z.div_mod_to_equations; lia.
    - destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. clear - Hr Y1 Y2 HFF PB G3 GL1 G2b ATR; Z.div_mod_to_equations; lia.
    - destruct (CLA a' Ha') as [A'R NA].
      assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      rewrite SHA. clear - A'R NA F64 HFF PB G3 GL1 G2b ATR; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
  pose proof (dc_at_any m m' (F + 32) 984 DJ1 WM ltac:(lia)) as DJ1'.
  destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
  destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
  destruct DJ1' as [junk1 J1]. change (Z.to_nat 984) with 984%nat in J1.
  assert (LJ : length junk1 = 984%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
  assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 992 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 4 F))]).
  { rewrite EFF.
    apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
    cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 992 (le8 sp ++ junk1)] _)). split.
    - replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
      eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 984 junk1])); split; [exact F24'|];
        cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
      + cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
      + cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
      + reflexivity.
    - cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 992) with (F + 1016) by lia. exact F56'. }
  (* [comment removed for export] *)
  unfold sm4_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
  split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
  split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
  split; [exact FRM|]. split; [exact SH'|].
  split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
  split; [eapply rng_sub'; [exact A8| clear - SB1 SB2 PB; lia]|].
  split; [| exact SHX].
  (* [comment removed for export] *)
  intros a (b & Hb & Hr). destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4).
  assert (SHA : shad a = 2147450880 + a / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite SHA. pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b, Y1.
  apply OUT; clear - Hr Y1 Y2 Y3 Y4 G2b G3 HFF HFLAG PB LO SK3 BOT ATR F64; Z.div_mod_to_equations; lia.
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
Lemma stack_malloc_4_AI1 : stack_malloc_4_stmt1 AI fflag afake_rng.
Proof.
  unfold stack_malloc_4_stmt1. intros until lo. intros AHx ONE MI ST BOT LO SPT TP RSTK RI RFS.
  rewrite E in AHx.
  eapply evtF_mono; [eapply (stack_malloc_4_P DI AQ ASEC HL CI CI_OK); try eassumption; unfold SM4_STACK_P, SM4_STACK in *; lia|].
  cbv beta. intros ms' PO. unfold sm4_postP in PO. unfold sm4_post.
  destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
  exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
  rewrite E, EC. repeat (split; [assumption|]). exact REST.
Qed.
Lemma stack_malloc_4_AI : stack_malloc_4_stmt AI fflag afake_rng.
Proof. exact (sm4_of_sm4_1 AI fflag afake_rng stack_malloc_4_AI1). Qed.
End Inst.
End CANSEC1.
