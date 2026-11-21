(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt FsKit AFake_iface F_tlsga F_m2s_b AFake_sm0 AFake_sm2 AFake_sm2L AFake_arep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Notation AH := (AFake_arep.AH DI AQ ASEC).
Hypothesis HL : ahole_laws AH.
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Local Notation AREP_frame_ext' := (AFake_arep.AREP_frame_ext' DI AQ ASEC HL).
Local Notation AREP_cells := (AFake_arep.AREP_cells DI AQ ASEC).
Local Notation HB_FAKE := (AFake_arep.HB_FAKE DI AQ ASEC).
Local Notation arep_ext_sm2 := (AFake_arep.arep_ext_sm2 DI AQ ASEC HL).
Local Notation sm2_postP := (AFake_arep.sm2_postP DI AQ ASEC CI).
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
Notation FB2 F := (mkABlock (ABFake 2) F 256).

(* [comment removed for export] *)
Definition atmost1_c2 (LB : list ablock) : Prop :=
  forall F1 n1 F2 n2, In (mkABlock (ABFake 2) F1 n1) LB -> In (mkABlock (ABFake 2) F2 n2) LB -> F1 = F2.
Lemma atmost1_c2_none : forall LB, (forall F n, ~ In (mkABlock (ABFake 2) F n) LB) -> atmost1_c2 LB.
Proof. intros LB N F1 n1 F2 n2 H1 _. exfalso. exact (N _ _ H1). Qed.

Theorem stack_malloc_2_P1 : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP_P AH L RNG st LB m ->
  atmost1_c2 LB ->                                        (* [comment removed for export] *)
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
  evtF bsegs RNG (sm2_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ASTKMALLOC2) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros AHP ATM1 MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
  pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AH ah_fake] in HFK.
  pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV).
  pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
  unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.   (* [comment removed for export] *)
  destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).
  (* [comment removed for export] *)
  destruct (AREP_cells L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
  (* [comment removed for export] *)
  pose proof (relro_word m 0xd13f0 0x169618 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
  pose proof (relro_word m 0xd20d8 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
  assert (DESC : rw_cells bsegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
  { unfold AFSDESC. apply (proj2 (rw_cells_app bsegs m 0xd20c8 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
    split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
  unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
  set (h := bv_unsigned h2).
  assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
  (* [comment removed for export] *)
  set (pos1 := Z.land h 4095). set (flag1 := (al_fake L) + 28672 + pos1).
  assert (PB1 : 0 <= pos1 < 4096).
  { subst pos1. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (EFL1 : flag1 = fk_flag L 2 pos1) by (subst flag1; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
  pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag1 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D31.
  destruct (c1_of_dc m flag1 D31) as [fb1 FLP1].
  destruct (decide (fb1 = Z_to_bv 8 0)) as [E1|NE1].
  - (* [comment removed for export] *)
    subst fb1. subst flag1 pos1. clear D31.
    set (pos := Z.land h 4095). set (flag := (al_fake L) + 28672 + pos). set (F := (al_fake L) + 2134016 + pos * 256).
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
    { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
    destruct SHB as (SB1 & SB2 & SB3).
    assert (SHD : shad F + 32 <= al_fake L \/ al_fake L + 11571200 <= shad F).   (* [comment removed for export] *)
    { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
    assert (FL0 : rw_cells bsegs m flag [C1 (Z_to_bv 8 0)]) by exact FLP1.          (* [comment removed for export] *)
    assert (FLM : m (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m flag _ FL0); subst flag; lia).
    (* [comment removed for export] *)
    pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
    pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
    pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 216 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
    pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 248) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
    destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
    (* [comment removed for export] *)
    pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
    pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F + 16) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS3.
    destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH0). destruct (c8c8_of_dc m _ DS3) as (sh2 & sh3 & SH1).
    assert (SH4 : rw_cells bsegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3]).
    { apply (proj2 (rw_cells_app bsegs m (shad F) [C8 sh0; C8 sh1] [C8 sh2; C8 sh3])). split; [exact SH0|].
      cbn [cells_size csize Nat.add]. replace (shad F + Z.of_nat 16) with (shad F + 16) by lia. exact SH1. }
    (* [comment removed for export] *)
    destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
    (* [comment removed for export] *)
    assert (HNT' : rw_cells bsegs m (al_fake L) [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).
    (* [comment removed for export] *)
    pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    assert (HPOS : pos = Z.land h 4095) by reflexivity. assert (HFLAG : flag = (al_fake L) + 28672 + pos) by reflexivity.
    assert (HFF : F = (al_fake L) + 2134016 + pos * 256) by reflexivity.
    clearbody h pos flag F.
    eapply evtF_mono.
    { eapply (stack_malloc2_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x65cd38 (al_fake L) h pos flag F j24 j56 sh0 sh1 sh2 sh3 h0 h1 hs);
        try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
      all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
        split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
        split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
      all: try (eapply rng_sub'; [exact RSTK| lia]).
      all: try (eapply rng_sub'; [exact A3| lia]). }
    cbv beta. intros ms' PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FLN1 & F24' & F56' & SH').
    unfold sm2_W in MU. rewrite SHF in MU.
    (* [comment removed for export] *)
    assert (OUT : forall a, 0 <= a < 2^64 ->
              ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 16 <= a < (al_fake L) + 24) -> a <> flag ->
              ~ (F + 24 <= a < F + 32) -> ~ (F + 248 <= a < F + 256) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 32) ->
              m' (wa a) = m (wa a)).
    { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
    assert (F64 : F mod 256 = 0).
    { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (16 * k + 8336 + pos). lia. }
    (* [comment removed for export] *)
    assert (AR' : AREP AH L st X m').
    { eapply (arep_ext_sm2 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
    assert (NOTIN : ~ In (FB2 F) LB).
    { intros Hin. destruct (LV 2 F 256 Hin) as (_ & _ & pos' & Hp' & HF' & Hb').
      assert (pos' = pos) as ->.
      { rewrite HFF in HF'. unfold fk_frame, fk_frames, fk_fsize in HF'. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in HF'. unfold fk_nframes in Hp'. cbn in Hp'. clear - HF' Hp' PB. lia. }
      rewrite <- EFL in Hb'. rewrite FLM in Hb'. clear - Hb'. assert (X : Z_to_bv 8 0 = Z_to_bv 8 1) by congruence. apply (f_equal bv_unsigned) in X. vm_compute in X. discriminate. }
    assert (HFK' : AFAKE L (FB2 F :: LB) m').
    { split; [exact G|]. split.
      { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
        split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }   (* [comment removed for export] *)
      split; [exists h0, h1, (Z_to_bv 64 (h + 1)), hs; exact HNT2|].
      split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
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
      - intros c F' n' [E|Hin].
        + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
          exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
          rewrite <- EFL. apply (rw_C1_high m' flag _ FLN1). lia.
        + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
          split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
          assert (NE : fk_flag L c pos' <> flag).
          { rewrite EFL. apply (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
            intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 2) with 256 in Hin by reflexivity. exact Hin. }
          pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }
    (* [comment removed for export] *)
    assert (BL' : ablocks L st X (FB2 F :: LB)).
    { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
      - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
      - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
      - cbn. exact B3.
      - constructor; [exact NOTIN| exact B4]. }
    assert (AHP' : AHEAP_P AH L RNG st (FB2 F :: LB) m').
    { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }
    (* [comment removed for export] *)
    assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP   (* [comment removed for export] *)
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
    assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->   (* [comment removed for export] *)
              0 <= a' < 2^47 /\ ~ (F <= a' < F + 256)).
    { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
        [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
      destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
    clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
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
        pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.   (* [comment removed for export] *)
        apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    unfold AFake_arep.sm2_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
    split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].   (* [comment removed for export] *)
    split; [exact FRM|]. split; [exact SH'|].
    split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
    eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
  - (* [comment removed for export] *)
    assert (LIVE1 : In (FKB 2 (fk_frame L 2 pos1) (fk_fsize 2)) LB).
    { apply (FL 2 pos1 fb1); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE1]. rewrite <- EFL1. apply (rw_C1_high m flag1 fb1 FLP1). subst flag1. lia. }
    assert (V1 : 0 < bv_unsigned fb1 < 256).
    { pose proof (bv_unsigned_in_range 8 fb1) as R8. unfold bv_modulus in R8. change (2 ^ Z.of_N 8) with 256 in R8.
      destruct (Z.eq_dec (bv_unsigned fb1) 0) as [Z0|NZ]; [exfalso; apply NE1; apply bv_eq; rewrite Z0; reflexivity | lia]. }
    assert (E8 : Z_to_bv 8 (bv_unsigned fb1) = fb1) by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    assert (FLP1' : rw_cells bsegs m flag1 [C1 (Z_to_bv 8 (bv_unsigned fb1))]) by (rewrite E8; exact FLP1).
    assert (HPOS1 : pos1 = Z.land h 4095) by reflexivity. assert (HFLAG1 : flag1 = (al_fake L) + 28672 + pos1) by reflexivity.
    set (pos := Z.land ((h + 1) mod 18446744073709551616) 4095). set (flag := (al_fake L) + 28672 + pos). set (F := (al_fake L) + 2134016 + pos * 256).
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
    { rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
    destruct SHB as (SB1 & SB2 & SB3).
    assert (SHD : shad F + 32 <= al_fake L \/ al_fake L + 11571200 <= shad F).   (* [comment removed for export] *)
    { pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) flag 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
    destruct (c1_of_dc m flag D3) as [fb FL0].
    assert (fb = Z_to_bv 8 0) as ->.
    { destruct (decide (fb = Z_to_bv 8 0)) as [E|NE]; [exact E| exfalso].
      assert (LIVE2 : In (FKB 2 (fk_frame L 2 pos) (fk_fsize 2)) LB).
      { apply (FL 2 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE]. rewrite <- EFL. apply (rw_C1_high m flag fb FL0). subst flag. lia. }
      pose proof (ATM1 _ _ _ _ LIVE1 LIVE2) as EQF.
      unfold fk_frame, fk_frames, fk_fsize in EQF. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in EQF.
      assert (NEP : pos1 <> pos).
      { subst pos1 pos. change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia. change (2^12) with 4096. change (2^64) with 18446744073709551616. clear - HB. Z.div_mod_to_equations. lia. }
      clear - EQF NEP. lia. }
    assert (FLM : m (wa flag) = Some (Z_to_bv 8 0)) by (apply (rw_C1_high m flag _ FL0); subst flag; lia).
    (* [comment removed for export] *)
    pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
    pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
    pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 216 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
    pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 248) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
    destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
    (* [comment removed for export] *)
    pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
    pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F + 16) 16 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS3.
    destruct (c8c8_of_dc m _ DS2) as (sh0 & sh1 & SH0). destruct (c8c8_of_dc m _ DS3) as (sh2 & sh3 & SH1).
    assert (SH4 : rw_cells bsegs m (shad F) [C8 sh0; C8 sh1; C8 sh2; C8 sh3]).
    { apply (proj2 (rw_cells_app bsegs m (shad F) [C8 sh0; C8 sh1] [C8 sh2; C8 sh3])). split; [exact SH0|].
      cbn [cells_size csize Nat.add]. replace (shad F + Z.of_nat 16) with (shad F + 16) by lia. exact SH1. }
    (* [comment removed for export] *)
    destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
    (* [comment removed for export] *)
    assert (HNT' : rw_cells bsegs m (al_fake L) [C8 h0; C8 h1; C8 (Z_to_bv 64 h); CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).
    (* [comment removed for export] *)
    pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    assert (HPOS : pos = Z.land ((h + 1) mod 18446744073709551616) 4095) by reflexivity. assert (HFLAG : flag = (al_fake L) + 28672 + pos) by reflexivity.
    assert (HFF : F = (al_fake L) + 2134016 + pos * 256) by reflexivity.
    clearbody h pos flag F.
    eapply evtF_mono.
    { eapply (stack_malloc2L_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x65cd38 (al_fake L) h pos1 flag1 (bv_unsigned fb1) pos flag F j24 j56 sh0 sh1 sh2 sh3 h0 h1 hs);
        try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
      all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
        split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
        split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
      all: try (eapply rng_sub'; [exact RSTK| lia]).
      all: try (eapply rng_sub'; [exact A3| lia]). }
    cbv beta. intros ms' PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FLN1 & F24' & F56' & SH').
    unfold sm2_W in MU. rewrite SHF in MU.
    (* [comment removed for export] *)
    assert (OUT : forall a, 0 <= a < 2^64 ->
              ~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) + 16 <= a < (al_fake L) + 24) -> a <> flag ->
              ~ (F + 24 <= a < F + 32) -> ~ (F + 248 <= a < F + 256) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 32) ->
              m' (wa a) = m (wa a)).
    { intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
    assert (F64 : F mod 256 = 0).
    { rewrite HFF. clear - G1. apply Z.mod_divide in G1; [|lia]. destruct G1 as [k Hk]. rewrite Hk. apply Z.mod_divide; [lia|]. exists (16 * k + 8336 + pos). lia. }
    (* [comment removed for export] *)
    assert (AR' : AREP AH L st X m').
    { eapply (arep_ext_sm2 L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
    assert (NOTIN : ~ In (FB2 F) LB).
    { intros Hin. destruct (LV 2 F 256 Hin) as (_ & _ & pos' & Hp' & HF' & Hb').
      assert (pos' = pos) as ->.
      { rewrite HFF in HF'. unfold fk_frame, fk_frames, fk_fsize in HF'. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in HF'. unfold fk_nframes in Hp'. cbn in Hp'. clear - HF' Hp' PB. lia. }
      rewrite <- EFL in Hb'. rewrite FLM in Hb'. clear - Hb'. assert (X : Z_to_bv 8 0 = Z_to_bv 8 1) by congruence. apply (f_equal bv_unsigned) in X. vm_compute in X. discriminate. }
    assert (HFK' : AFAKE L (FB2 F :: LB) m').
    { split; [exact G|]. split.
      { unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
        split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }   (* [comment removed for export] *)
      split; [exists h0, h1, (Z_to_bv 64 (h + 2)), hs; exact HNT2|].
      split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
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
      - intros c F' n' [E|Hin].
        + injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
          exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
          rewrite <- EFL. apply (rw_C1_high m' flag _ FLN1). lia.
        + destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
          split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
          assert (NE : fk_flag L c pos' <> flag).
          { rewrite EFL. apply (fk_flags_disjoint L c pos' 2 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
            intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. replace (fk_fsize 2) with 256 in Hin by reflexivity. exact Hin. }
          pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }
    (* [comment removed for export] *)
    assert (BL' : ablocks L st X (FB2 F :: LB)).
    { destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
      - intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
      - intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
      - cbn. exact B3.
      - constructor; [exact NOTIN| exact B4]. }
    assert (AHP' : AHEAP_P AH L RNG st (FB2 F :: LB) m').
    { split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AH ah_fake]. exact HFK'. }
    (* [comment removed for export] *)
    assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP   (* [comment removed for export] *)
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
    assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->   (* [comment removed for export] *)
              0 <= a' < 2^47 /\ ~ (F <= a' < F + 256)).
    { intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
        [ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
      destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
    clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0 SH1 SH4
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
        pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.   (* [comment removed for export] *)
        apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    unfold AFake_arep.sm2_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
    split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].   (* [comment removed for export] *)
    split; [exact FRM|]. split; [exact SH'|].
    split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
    eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
Qed.
End S.
End CANSEC1.
