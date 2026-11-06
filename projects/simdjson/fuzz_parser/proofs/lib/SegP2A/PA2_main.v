(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AU_consts AU_iface AU_kit AU_parts_iface AU_fuzz_kit Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit PIosKitA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM SFPA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry S2G2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import APC_mpres.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface A2Lib PA2_kz PA2_reg PA2_exit PA2_head PA2_a2run PA2_a2pw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require PA2_t0c PA2_xsf PA2_xnew PA2_a2cnd.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require A2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Import ITree.Exc.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition SUMW_T (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop) (S : SP.summ) : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (data idxs : list Z) (F : Z),
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) -> (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  rng_aimg RNG -> rng_fs L RNG ->
  SP.summ_okHSC asegs (gp2 asegs data idxs) (AHM.hmH AI L RNG st (mkABlock (ABFake 5) F 2048 :: LB))
    (AHM.hmA AI (mkABlock (ABFake 5) F 2048 :: LB)) (AHM.hmC AI (mkABlock (ABFake 5) F 2048 :: LB)) AHM.hmR (AHM.hmF RNG) (AHM.hmS L RNG) S.
Definition SUMC_T (AI : AMallocIface) (rng_fs : alayout -> footprint -> Prop) (S : SP.summ) : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (data idxs : list Z) (F : Z) (p : AsanCtrl.aptr) (COPY n : Z),
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) -> (forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB) ->
  rng_aimg RNG -> rng_fs L RNG ->
  SP.summ_okHSC asegs (gp2 asegs data idxs) (AHM.hmH AI L RNG st (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB))
    (AHM.hmA AI (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB)) (AHM.hmC AI (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB))
    AHM.hmR (AHM.hmF RNG) (AHM.hmS L RNG) S.

Section M.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis SM5 : stack_malloc_5_stmt AI fflag rng_fs.
  Hypothesis SF5 : stack_free_5_stmt AI fflag.
  Hypothesis ONT : opnew_nt_stmtA AI.
  Hypothesis ODAW : opdelete_arr_wild_stmtA AI.
  Hypothesis A2SOUND : A2SOUND_T AI.

  (* [comment removed for export] *)
  Variables (L : alayout) (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (FR : bvmap 5 word) (fc : bv 32) (m : amem)
            (s : APS) (LB : list ablock) (lo : Z) (rstk : region) (d idx : list Z) (tr0 : list Z)
            (pim psi pcp ptp psb poc pia : AsanCtrl.aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
            (x24 x88 : word) (jtp jsb joc jia : list byte) (cls FA FN : Z).
  Hypothesis AH : AHEAP AI L RNG (aps_m s) LB m.
  Hypothesis ND : List.NoDup [pim; psi; pcp; ptp; psb; poc; pia].
  Hypothesis Ith : In (HB pim THIS nim) LB.
  Hypothesis Hnim : 96 <= nim.
  Hypothesis Isi : In (HB psi ASI nsi) LB.
  Hypothesis Hnsi : 4 * zlength idx + 16 <= nsi.
  Hypothesis Icp : In (HB pcp ACP ncp) LB.
  Hypothesis Hb1 : ACP <= BUF.
  Hypothesis Hb2 : BUF + zlength d + 64 <= ACP + ncp.
  Hypothesis Itp : In (HB ptp TPA ntp) LB.
  Hypothesis Isb : In (HB psb SBA nsb) LB.
  Hypothesis Ioc : In (HB poc AOC noc) LB.
  Hypothesis Hnoc : 8192 <= noc.
  Hypothesis Iia : In (HB pia AIA nia) LB.
  Hypothesis Hnia : 1024 <= nia.
  Hypothesis NO5 : forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB.
  Hypothesis NO4 : forall FA FN, ~ In (mkABlock (ABFake 4) FA FN) LB.
  Hypothesis Hntp8 : ntp mod 8 = 0.
  Hypothesis Hntp : 8 * (zlength idx + 3) <= ntp <= 2^27.
  Hypothesis Hnsb3 : 5 * zlength d + 182 <= 3 * nsb.
  Hypothesis Hnsb : zlength d + 60 <= nsb <= 2^24.
  Hypothesis Hbuf : bytes_at asegs m BUF (s1buf d).
  Hypothesis Hd : Forall (fun c => 0 <= c < 256) d.
  Hypothesis Hlen : zlength d + 64 <= 2^20.
  Hypothesis Hscan : scan d = (true, idx).
  Hypothesis HIDX : rw_cells asegs m ASI [CB (4 * (length idx + 3)) (u32bytes (idx ++ [zlength d; zlength d; 0]))].
  Hypothesis HO8 : rw_cells asegs m (THIS + 8) [C4 (Z_to_bv 64 (zlength idx))].
  Hypothesis HO16 : rw_cells asegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)].
  Hypothesis HO24 : rw_cells asegs m (THIS + 24) [C4 x24].
  Hypothesis HO40 : rw_cells asegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis HO56 : rw_cells asegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88].
  Hypothesis HDOC : rw_cells asegs m DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)].
  Hypothesis Hda : DOC mod 8 = 0.
  Hypothesis Ifk : In (mkABlock (ABFake cls) FA FN) LB.
  Hypothesis Hfk1 : FA <= DOC.
  Hypothesis Hfk2 : DOC + 16 <= FA + FN.
  Hypothesis Hfk3 : ablk FA (FA + FN).
  Hypothesis HDSH : rw_cells asegs m (Z.shiftr DOC 3 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis HDR : rng RNG DOC 16.
  Hypothesis HDSR : rng RNG (Z.shiftr DOC 3 + 2147450880) 2.
  Hypothesis HTB : rw_cells asegs m TPA [CB (Z.to_nat ntp) jtp].
  Hypothesis HSB : rw_cells asegs m SBA [CB (Z.to_nat nsb) jsb].
  Hypothesis HOC : rw_cells asegs m AOC [CB 8192 joc].
  Hypothesis HIA : rw_cells asegs m AIA [CB 1024 jia].
  Hypothesis HCIMG : client_img m.
  Hypothesis HCSH : client_sh m.
  Hypothesis HCI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis HUC : uchain m (al_top L) AFREE_PC (u sp) (u s0) (Nat.pred UDEPTH) tr0.
  Hypothesis Htr0 : (length tr0 <= 27)%nat.
  Hypothesis HS0 : u s0 < u sp \/ u sp + 16 <= u s0.
  Hypothesis Hra1 : 4096 <= u ra.
  Hypothesis Hra2 : u ra <> AFREE_PC.
  Hypothesis HUM : In [AMALLOC_PC; AOPNEW_RET] (al_U L).
  Hypothesis HSTK : stk asegs m lo (u sp).
  Hypothesis Hlo1 : ATOP + 4096 <= lo.
  Hypothesis Hlo2 : lo <= u sp - STAGE2_STACK_A.
  Hypothesis HCL : rclean m rstk.
  Hypothesis HCL1 : r_lo rstk <= lo.
  Hypothesis HCL2 : u sp <= r_hi rstk.
  Hypothesis HCL3 : ATOP <= r_rlo rstk.
  Hypothesis HCLR : rrng RNG rstk.
  Hypothesis Hsptop : u sp + 16 < al_top L.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis HMI : mem_inv asegs m.
  Hypothesis HZ : frm0 fc.
  Hypothesis HTP : tp = Z_to_bv 64 ATP.
  Hypothesis HRS : rng RNG lo (al_top L - lo).
  Hypothesis HRI : rng_aimg RNG.
  Hypothesis HRIS : rng_aimg_sh RNG.
  Hypothesis HRFS : rng_fs L RNG.
  Hypothesis HAOK : aps_ok L s.
  Hypothesis HFR : AFRESH (aps_m s).
  Hypothesis HDK : dk (aps_m s) < DWMAX.
  (* [comment removed for export] *)
  Local Notation IDXS := (idx ++ [zlength d; zlength d; 0]).
  Hypothesis SFPAS_ok : forall F, SP.summ_okHSC asegs (gp2 asegs d IDXS) (AHM.hmH AI L RNG (aps_m s) (mkABlock (ABFake 5) F 2048 :: LB))
    (AHM.hmA AI (mkABlock (ABFake 5) F 2048 :: LB)) (AHM.hmC AI (mkABlock (ABFake 5) F 2048 :: LB)) AHM.hmR (AHM.hmF RNG) (AHM.hmS L RNG) SFPAS.
  Hypothesis PFFAS_ok : forall F, SP.summ_okHSC asegs (gp2 asegs d IDXS) (AHM.hmH AI L RNG (aps_m s) (mkABlock (ABFake 5) F 2048 :: LB))
    (AHM.hmA AI (mkABlock (ABFake 5) F 2048 :: LB)) (AHM.hmC AI (mkABlock (ABFake 5) F 2048 :: LB)) AHM.hmR (AHM.hmF RNG) (AHM.hmS L RNG) PFFAS.
  Hypothesis SFPCAS_ok : forall F RNG4 st4 p COPY n, fp_le RNG RNG4 ->
    SP.summ_okHSC asegs (gp2 asegs d IDXS) (AHM.hmH AI L RNG4 st4 (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB))
      (AHM.hmA AI (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB)) (AHM.hmC AI (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB))
      AHM.hmR (AHM.hmF RNG4) (AHM.hmS L RNG4) SFPCAS.
  Hypothesis PFFCAS_ok : forall F RNG4 st4 p COPY n, fp_le RNG RNG4 ->
    SP.summ_okHSC asegs (gp2 asegs d IDXS) (AHM.hmH AI L RNG4 st4 (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB))
      (AHM.hmA AI (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB)) (AHM.hmC AI (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB))
      AHM.hmR (AHM.hmF RNG4) (AHM.hmS L RNG4) PFFCAS.

  Notation W := (s2_winA THIS TPA ntp SBA nsb AOC AIA).
  Notation Q := (s2_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo W m).

  Lemma stage2A_sec :
    implMA RNG (rn_copyA d idx) s Q
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 THIS) (Z_to_bv 64 DOC) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 ASTAGE2) fc None m (seg_rom asegs)).
  Proof using All.
    pose proof (s1_n _ _ _ (scan_S1OUT d idx Hscan)) as Sn.
    apply implMA_from_evtF.
    eapply evtF_cut.
    { eapply (a2_head AI fflag rng_fs SM5 L RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                FR fc m (aps_m s) LB lo rstk d idx pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF
                nim nsi ncp ntp nsb noc nia x24 x88 jtp jsb joc jia cls FA FN); eassumption. }
    intros ms2 HQ. destruct HQ as (F & SPAX & x5 & x6 & x7 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & x28 & x29 & x30 & x31 & FR2 & fc2 & m2 & HQ).
    cbv zeta in HQ.
    destruct HQ as (-> & HZ2 & MI2 & RG2 & KN2 & GH2 & FPL2 & AWG2 & HSPA32 & HSPA & AH2 & PRES2 & STK2 & HFm & HFb & HFt & HRF & HRFS' & HFL2 & HSHF).
    (* [comment removed for export] *)
    pose proof Hlo2 as Hlo2'. unfold STAGE2_STACK_A in Hlo2'. atop_facts. pose proof (u_rngE sp) as Rsp.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & HTOP & _).
    assert (Hsp47 : u sp <= 2 ^ 47) by (clear - HTOP Hsptop; lia).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Ith) as (_ & Ht0 & Ht1 & Ht2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Isi) as (_ & Hi0 & Hi1 & Hi2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Icp) as (_ & Hc0 & Hc1 & Hc2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Itp) as (_ & Hp0 & Hp1 & Hp2 & Hp3).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Isb) as (_ & Hs0 & Hs1 & Hs2 & Hs3).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Ioc) as (_ & Ho0 & Ho1 & Ho2 & _).
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH Iia) as (_ & Ha0 & Ha1 & Ha2 & _).
    assert (HFN : 0 <= FN) by (clear - Hfk1 Hfk2; lia).
    pose proof (fake_band FA FN Hfk3 HFN) as (_ & Hf0 & Hf1).
    (* [comment removed for export] *)
    assert (R_STKSH : rng RNG (2 * (u sp / 16) + SH - 1076) 1076).
    { pose proof (shclean_hull _ _ _ _ _ (rclean_shclean _ _ HCL)) as (HH1 & HH2 & HH3 & HH4 & HH5 & HH6).
      pose proof HCLR as HCLR'. unfold rrng in HCLR'. rewrite !shad_div in HCLR'. unfold ASHOFF in HCLR'. eapply rng_sub'; [exact HCLR'|].
      clear - HH1 HH2 HH5 HCL1 HCL2 Hlo2' Hsp16. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    pose (SP16 := u sp / 16). pose (T8 := THIS / 8). pose (DOC8 := DOC / 8). pose (B8 := BUF / 8). pose (LEN := zlength d).
    pose (I8 := ASI / 8). pose (N := zlength idx). pose (TB8 := TPA / 8). pose (CAPT := ntp / 8). pose (SB8 := SBA / 8). pose (CAPS := nsb).
    pose (OC8 := AOC / 8). pose (IA8 := AIA / 8). pose (F11 := F / 2048). pose (PB := (u sp - 384 - SPAX) / 16). pose (FLAG := fflag L 5 F).
    pose (BO := BUF mod 8). pose (BG := (zlength d + BUF mod 8 + 64) / 8). pose (IG := (4 * zlength idx + 12 + 7) / 8). pose (SG := nsb / 8).
    pose (rest := [u x5; u x6; u x7; u a1'; u a2'; u a3'; u a4'; u a5'; u a6'; u a7'; u s3; u s4; u s6; u s8; u s9; u s10; u s11;
                   u x28; u x29; u x30; u x31]).
    change (rng RNG (2 * SP16 + SH - 1076) 1076) in R_STKSH.
    assert (E_SP : u sp = 16 * SP16) by exact (e16_of_16 (u sp) Hsp16).
    assert (E_T8 : THIS = 8 * T8) by exact (e8_of_16 THIS Ht2).
    assert (E_DOC8 : DOC = 8 * DOC8) by exact (e8_of_8 DOC Hda).
    assert (E_B8 : BUF = 8 * B8 + BO) by (unfold B8, BO; clear; Z.div_mod_to_equations; lia).
    assert (E_I8 : ASI = 8 * I8) by exact (e8_of_16 ASI Hi2).
    assert (E_TB8 : TPA = 8 * TB8) by exact (e8_of_16 TPA Hp2).
    assert (E_CAPT : ntp = 8 * CAPT) by exact (e8_of_8 ntp Hntp8).
    assert (E_SB8 : SBA = 8 * SB8) by exact (e8_of_16 SBA Hs2).
    assert (E_CAPS : nsb = CAPS) by reflexivity.
    assert (E_OC8 : AOC = 8 * OC8) by exact (e8_of_16 AOC Ho2).
    assert (E_IA8 : AIA = 8 * IA8) by exact (e8_of_16 AIA Ha2).
    assert (E_F11 : F = 2048 * F11) by (unfold F11; clear - HFm; Z.div_mod_to_equations; lia).
    assert (E_PB : u sp - 384 - SPAX = 16 * PB) by (unfold PB; clear - HSPA HSPA32 Hsp16; Z.div_mod_to_equations; lia).
    assert (E_FLAG : FLAG = fflag L 5 F) by reflexivity.
    assert (E_LEN : LEN = zlength d) by reflexivity.
    assert (E_N : N = zlength idx) by reflexivity.
    assert (D_BO : 0 <= BO <= 7) by (unfold BO; clear; Z.div_mod_to_equations; lia).
    assert (D_BG : 0 <= LEN + BO + 64 - 8 * BG <= 7) by (unfold LEN, BO, BG; clear; Z.div_mod_to_equations; lia).
    assert (D_IG : 0 <= 8 * IG - (4 * N + 12) <= 7) by (unfold IG, N; clear; Z.div_mod_to_equations; lia).
    assert (D_SG : 0 <= CAPS - 8 * SG <= 7) by (unfold CAPS, SG; clear; Z.div_mod_to_equations; lia).
    assert (B_T : 0 <= THIS /\ THIS + 96 < M64) by (clear - Ht0 Ht1 Hnim; atop_facts; lia).
    assert (B_TB : 0 <= TPA /\ TPA + ntp < M64 /\ 0 <= ntp) by (clear - Hp0 Hp1 Hp3; atop_facts; lia).
    assert (B_SB : 0 <= SBA /\ SBA + nsb < M64 /\ 0 <= nsb) by (clear - Hs0 Hs1 Hs3; atop_facts; lia).
    assert (B_OC : 0 <= AOC /\ AOC + 8192 < M64) by (clear - Ho0 Ho1 Hnoc; atop_facts; lia).
    assert (B_IA : 0 <= AIA /\ AIA + 1024 < M64) by (clear - Ha0 Ha1 Hnia; atop_facts; lia).
    (* [comment removed for export] *)
    assert (E_SPR : 0x7fff00000000 <= 16 * SP16 <= 2^47) by (clear - E_SP Hlo1 Hlo2' Hsp47; atop_facts; lia).
    assert (H_PB : 0 <= PB <= 1) by (clear - E_PB HSPA; lia).
    assert (H_SZ : 0 <= CAPT /\ 0 <= CAPS /\ 0 <= BG /\ 0 <= IG /\ 0 <= SG) by (clear - E_CAPT E_CAPS Hp3 Hs3 D_BG D_IG D_SG Sn Hlen E_LEN E_N D_BO; lia).
    assert (H_LEN : 1 <= LEN <= 1048512) by (clear - Sn Hlen E_LEN; lia).
    assert (H_N : 1 <= N <= LEN) by (clear - Sn E_LEN E_N; lia).
    assert (H_LO : ATOP + 4096 <= lo /\ lo <= 16 * SP16 - 8608) by (clear - Hlo1 Hlo2' E_SP; lia).
    assert (Hnsi' : 4 * N + 12 <= nsi) by (clear - Hnsi E_N; lia).
    assert (Hb2' : BUF + LEN + 64 <= ACP + ncp) by (clear - Hb2 E_LEN; lia).
    assert (Hac : ACP mod 8 = 0) by (clear - Hc2; Z.div_mod_to_equations; lia).
    assert (B_ALL : 0x665000 <= THIS /\ THIS + 96 <= ATOP /\ 0x665000 <= DOC /\ DOC + 16 <= ATOP /\ 0x665000 <= BUF /\ BUF + LEN + 64 <= ATOP
                  /\ 0x665000 <= ASI /\ ASI + 4 * N + 12 <= ATOP /\ 0x665000 <= TPA /\ TPA + 8 * CAPT <= ATOP /\ 0x665000 <= SBA /\ SBA + CAPS <= ATOP
                  /\ 0x665000 <= AOC /\ AOC + 8192 <= ATOP /\ 0x665000 <= AIA /\ AIA + 1024 <= ATOP /\ 0x665000 <= F /\ F + 2048 <= ATOP).
    { clear - Ht0 Ht1 Hnim Hf0 Hf1 Hfk1 Hfk2 Hc0 Hc1 Hb1 Hb2' Hi0 Hi1 Hnsi' Hp0 Hp1 E_CAPT Hs0 Hs1 E_CAPS Ho0 Ho1 Hnoc Ha0 Ha1 Hnia HFb HFt.
      unfold ablk, AIMG_HI, KLS in HFb. atop_facts. repeat split; lia. }
    set (ZL := PA2_t0c.ZL_t0'' (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest).
    pose (CndA := fun E => SP.gagree 35 (mkEZ ZL) E /\ eb E = eb (mkEZ ZL)).
    assert (HCG : forall E E2, SP.gagree (SP.p_G A2_defs.A2) E E2 -> eb E = eb E2 -> CndA E -> CndA E2).
    { intros E E2 Hg2 Hb2x [HgX HbX]. split; [exact (SP.gagree_trans _ _ _ _ HgX Hg2) | congruence]. }
    assert (HCW : forall E, CndA E -> SP.wins_client (AHM.hmC AI (mkABlock (ABFake 5) F 2048 :: LB)) E (SP.p_W A2_defs.A2)).
    { intros E [HgX HbX].
      exact (PA2_a2cnd.cnd_W AI LB lo F pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia cls FA FN (u ra) SP16 (u gp) (u tp) (u s0) (u
          s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest
          E_SPR E_T8 E_DOC8 E_B8 E_I8 E_TB8 E_SB8 E_OC8 E_IA8 E_F11 E_CAPT E_CAPS D_BO D_BG D_IG D_SG H_PB H_SZ H_LEN H_N H_LO B_ALL Ith Hnim Isi Hnsi' Icp Hb1
          Hac Hb2' Itp Isb Ioc Hnoc Iia Hnia Ifk Hfk1 Hfk2 HCI
               E HgX HbX). }
    assert (HCR : forall E, CndA E -> forall w, In w (SP.p_CR A2_defs.A2) -> forall z, fst (SP.win_den E w) <= z < snd (SP.win_den E w) ->
                    AHM.hmA AI (mkABlock (ABFake 5) F 2048 :: LB) z).
    { intros E [HgX HbX].
      exact (PA2_a2cnd.cnd_CR AI LB lo F pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia cls FA FN (u ra) SP16 (u gp) (u tp) (u s0) (u
          s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest
          E_SPR E_T8 E_DOC8 E_B8 E_I8 E_TB8 E_SB8 E_OC8 E_IA8 E_F11 E_CAPT E_CAPS D_BO D_BG D_IG D_SG H_PB H_SZ H_LEN H_N H_LO B_ALL Ith Hnim Isi Hnsi' Icp Hb1
          Hac Hb2' Itp Isb Ioc Hnoc Iia Hnia Ifk Hfk1 Hfk2 HCI
               E HgX HbX). }
    assert (HIK : forall E M0, CndA E -> AHM.hmH AI L RNG (aps_m s) (mkABlock (ABFake 5) F 2048 :: LB) M0 -> know_ok asegs E M0 (SP.p_IK A2_defs.A2)).
    { intros E M0 _ HM.
      exact (PA2_a2cnd.cnd_IK AI LB lo F pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia cls FA FN (u ra) SP16 (u gp) (u tp) (u s0) (u
          s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest
          E_SPR E_T8 E_DOC8 E_B8 E_I8 E_TB8 E_SB8 E_OC8 E_IA8 E_F11 E_CAPT E_CAPS D_BO D_BG D_IG D_SG H_PB H_SZ H_LEN H_N H_LO B_ALL Ith Hnim Isi Hnsi' Icp Hb1
          Hac Hb2' Itp Isb Ioc Hnoc Iia Hnia Ifk Hfk1 Hfk2 HCI
               L RNG (aps_m s) E M0 HM). }
    assert (HSTK' : forall E, CndA E -> SP.hs_ok (AHM.hmS L RNG) E (SP.p_PS A2_defs.A2) (SP.p_W A2_defs.A2)).
    { intros E [HgX HbX]. unfold SP.hs_ok.
      assert (DS : SP.dstk (SP.p_PS A2_defs.A2) (SP.p_W A2_defs.A2) = Some (A2_defs.vSPA, 8192)) by reflexivity.
      rewrite DS.
      rewrite <- (SP.edenot_gagree 35 (mkEZ ZL) E A2_defs.vSPA HgX (eq_sym HbX) eq_refl), u_zden by reflexivity.
      cbv [A2_defs.vSPA A2_defs.vSP A2_defs.vSP16 A2_defs.vPB A2_defs.V A2_defs.mul A2_defs.add A2_defs.sub].
      unfold ZL. cbn [zden nth PA2_t0c.ZL_t0'' app].
      assert (ESPA0 : 16 * SP16 + -384 - 16 * PB = SPAX) by (clear - E_SP E_PB; lia).
      rewrite ESPA0, Z.mod_small by (clear - HSPA Rsp Hlo1 Hlo2'; atop_facts; lia).
      unfold AHM.hmS. split; [clear - HSPA Hlo1 Hlo2'; lia|]. split; [clear - HSPA Hsptop; lia|].
      eapply rng_sub; [exact HRS | clear - HSPA Hlo1 Hlo2'; lia | clear - HSPA Hsptop; lia]. }
    (* [comment removed for export] *)
    pose proof (a2_run AI A2SOUND L RNG (aps_m s) (mkABlock (ABFake 5) F 2048 :: LB) d IDXS (SFPAS_ok F) (PFFAS_ok F) CndA HCG HCW HCR HIK HSTK'
                  A2_defs.T0 ltac:(apply in_or_app; left; cbn [SP.p_tm A2_defs.A2 SP.PGH]; left; reflexivity) (mkEZ ZL) m2 (seg_rom asegs) _ FR2 fc2
                  eq_refl AWG2 (conj (SP.gagree_refl _ _) eq_refl) (conj AH2 MI2)
                  (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) RG2 KN2 GH2 MI2 HZ2) as RUN.
    eapply evtF_cut.
    { eapply evtF_weaken; [| exact RUN]. intros b j [Hj|Hj]; [exact (FPL2 b j Hj) | exact Hj]. }
    intros ms3 (X & E' & m3 & R3 & F3 & fc3 & HinX & -> & HZ3 & HF3 & HR3 & HK3 & HG3 & Hg & Hb & HH3 & FO3 & WM3 & MI3 & STK3).
    apply evtF_done.
    change (SP.gagree 35 (mkEZ ZL) E') in Hg.
    (* [comment removed for export] *)
    pose proof (proj1 HH3) as AH3.
    assert (ESF : shad F = 256 * F11 + SH) by (rewrite shad_div; unfold ASHOFF; rewrite E_F11; clear; Z.div_mod_to_equations; lia).
    assert (FR23 : forall a, 0 <= a < M64 ->
              outside [(u sp - 8608, u sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (TPA, TPA + ntp); (SBA, SBA + nsb);
                       (AOC, AOC + 8192); (AIA, AIA + 1024); (F, F + 2048); (shad F, shad F + 256)] a ->
              (SPAX <= a < 2^47 \/ AHM.hmA AI (mkABlock (ABFake 5) F 2048 :: LB) a) -> m3 (wa a) = m2 (wa a)).
    { intros a Ha HO HPa.
      eapply (a2_frame AI (mkABlock (ABFake 5) F 2048 :: LB) (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5)
                (u s6) (u s7) (u s8) (u s9) (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest m2 m3);
      [ clear - E_SP Hlo1 Hlo2' Hsp47; atop_facts; lia
      | clear - E_T8 B_T; lia
      | clear - E_TB8 E_CAPT B_TB; lia
      | clear - E_CAPT B_TB; lia
      | clear - E_SB8 E_CAPS B_SB; lia
      | clear - E_CAPS B_SB; lia
      | clear - E_OC8 B_OC; lia
      | clear - E_IA8 B_IA; lia
      | clear - E_F11 HFb HFt; unfold ablk, AIMG_HI, KLS in HFb; atop_facts; lia
      | clear - E_F11 HFb HFt; unfold ablk, AIMG_HI, KLS in HFb; atop_facts; lia
      | exact H_PB
      | exact FO3
      | exact Ha
      | rewrite <- E_SP, <- E_T8, <- E_TB8, <- E_CAPT, <- E_SB8, <- E_CAPS, <- E_OC8, <- E_IA8, <- E_F11, <- ESF; exact HO
      | replace (16 * SP16 - 384 - 16 * PB) with SPAX by (clear - E_PB E_SP; lia); exact HPa ]. }
    pose proof (a2_pres_WH AI L RNG (aps_m s) LB m2 m3 (u sp) SPAX F THIS TPA ntp SBA nsb AOC AIA AH2 NO5 HFb HFt
                  ltac:(clear - Hlo1 Hlo2'; lia) Hsp47 ltac:(clear - HSPA; lia) HSHF FR23 WM3) as PW23.
    assert (PW3 : aheap_pres_W CI LB (u sp) W m m3)
      by (eapply aheap_pres_W_trans; [apply aheap_pres_W_of_pres; exact PRES2 | exact PW23]).
    cbn [SP.p_ex A2_defs.A2 SP.PGH SP.PGX] in HinX. destruct HinX as [<-|[<-|[]]].
    - (* [comment removed for export] *)
      exact (PA2_xsf.xsf_branch AI fflag SF5 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo d idx m THIS TPA ntp SBA nsb AOC AIA pim ptp psb poc pia nim noc nia Ith
              Hnim Itp Isb Ioc Hnoc Iia Hnia (proj1 Sn) HRS Hlo1 Hlo2 Hsp16 Hsptop NO5 SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG
              rest F SPAX m2 E_SP E_T8 E_TB8 E_CAPT E_SB8 E_CAPS E_OC8 E_IA8 E_F11 E_PB E_FLAG B_T B_TB B_SB B_OC B_IA HSPA32 HSPA AH2 PRES2 STK2 HFm HFb HFt HFL2
              HSHF
               E' m3 R3 F3 fc3 Hg Hb HF3 HR3 HK3 HG3 AH3 PW3 WM3 MI3 STK3 HZ3).
    - (* [comment removed for export] *)
      pose proof (PA2_xnew.xnew_v2 d idx E' m3 HG3) as HV2.
      exact (PA2_xsf.xnew_call AI fflag SF5 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo d idx m THIS TPA ntp SBA nsb AOC AIA pim ptp psb poc pia nim noc nia Ith
              Hnim Itp Isb Ioc Hnoc Iia Hnia (proj1 Sn) HRS Hlo1 Hlo2 Hsp16 Hsptop NO5 SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG
              rest F SPAX m2 E_SP E_T8 E_TB8 E_CAPT E_SB8 E_CAPS E_OC8 E_IA8 E_F11 E_PB E_FLAG B_T B_TB B_SB B_OC B_IA HSPA32 HSPA AH2 PRES2 STK2 HFm HFb HFt HFL2
              HSHF
               E' m3 R3 F3 fc3 ONT HTP HUM HAOK E_LEN Hlen Hg Hb HF3 HR3 HK3 HG3 AH3 PW3 WM3 MI3 STK3 HZ3 HV2
               (PA2_xnew.xnb AI fflag SF5 L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo d idx m THIS TPA ntp SBA nsb AOC AIA pim ptp psb poc pia nim noc nia Ith
                Hnim Itp Isb Ioc Hnoc Iia Hnia (proj1 Sn) HRS Hlo1 Hlo2 Hsp16 Hsptop NO5 SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG
                rest F SPAX m2 E_SP E_T8 E_TB8 E_CAPT E_SB8 E_CAPS E_OC8 E_IA8 E_F11 E_PB E_FLAG B_T B_TB B_SB B_OC B_IA HSPA32 HSPA AH2 PRES2 STK2 HFm HFb HFt HFL2
                HSHF psi pcp ASI ACP DOC BUF nsi ncp x88 cls FA FN tr0 E_DOC8 E_B8 E_I8 E_LEN E_N D_BO D_BG D_IG D_SG ND Isi Hnsi Icp Hb1 Hb2 Hntp8 Hntp Hnsb3 Hnsb
                Hbuf Hd Hlen Hscan HIDX HO8 HO16 HO40 HO56 HDOC Hda Ifk Hfk1 Hfk2 Hfk3 HCIMG HCI HUC Htr0 HS0 Hra1 Hra2 HTP HRI HRIS HAOK HFR HDK HRF HRFS' HDR HDSR
                R_STKSH ODAW (SFPCAS_ok F) (PFFCAS_ok F) E' m3 R3 F3 fc3 Hg Hb HF3 HR3 HK3 HG3 AH3 PW3 MI3 STK3 HZ3 HV2)).
  Qed.
End M.

(* [comment removed for export] *)
Theorem stage2_proofA : forall (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop),
  stack_malloc_5_stmt AI fflag rng_fs -> stack_free_5_stmt AI fflag -> opnew_nt_stmtA AI -> opdelete_arr_wild_stmtA AI ->
  A2SOUND_T AI -> (forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R') ->
  SUMW_T AI rng_fs SFPAS -> SUMW_T AI rng_fs PFFAS -> SUMC_T AI rng_fs SFPCAS -> SUMC_T AI rng_fs PFFCAS ->
  stage2_stmtA AI rng_fs.
Proof.
  intros AI fflag rng_fs SM5 SF5 ONT ODAW A2S RFSM SW1 SW2 SC1 SC2.
  unfold stage2_stmtA.
  intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m s LB lo rstk d idx tr0
         pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia x24 x88 jtp jsb joc jia
         AH ND Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia NO5 NO4 Hntp8 Hntp Hnsb3 Hnsb Hbuf Hd Hlen Hscan HIDX HO8 HO16 HO24 HO40
         HO56 HDOC Hda (cls & FA & FN & Ifk & Hfk1 & Hfk2 & Hfk3) HDSH HDR HDSR HTB HSB HOC HIA HCIMG HCSH HCI HUC Htr0 HS0 Hra1 Hra2 HUM
         HSTK Hlo1 Hlo2 HCL HCL1 HCL2 HCL3 HCLR Hsptop Hsp16 HMI HZ HTP HRS HRI HRIS HRFS HAOK HFR HDK -> ->.
  exact (stage2A_sec AI fflag rng_fs SM5 SF5 ONT ODAW A2S L RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m s LB lo
        rstk d idx tr0 pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia x24 x88 jtp jsb joc jia cls FA FN AH ND
        Ith Hnim Isi Hnsi Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia NO5 NO4 Hntp8 Hntp Hnsb3 Hnsb Hbuf Hd Hlen Hscan HIDX HO8 HO16 HO24 HO40 HO56 HDOC Hda Ifk
        Hfk1 Hfk2 Hfk3 HDSH HDR HDSR HTB HSB HOC HIA HCIMG HCSH HCI HUC Htr0 HS0 Hra1 Hra2 HUM HSTK Hlo1 Hlo2 HCL HCL1 HCL2 HCL3 HCLR Hsptop Hsp16 HMI HZ HTP
        HRS HRI HRIS HRFS HAOK HFR HDK (fun F => SW1 L RNG (aps_m s) LB d (idx ++ [zlength d; zlength d; 0]) F NO5 NO4 HRI HRFS) (fun F => SW2 L RNG (aps_m s)
        LB d (idx ++ [zlength d; zlength d; 0]) F NO5 NO4 HRI HRFS) (fun F RNG4 st4 p COPY n HLE => SC1 L RNG4 st4 LB d (idx ++ [zlength d; zlength d; 0]) F p
        COPY n NO5 NO4 (rng_fp_le _ _ _ _ HLE HRI) (RFSM L RNG RNG4 HLE HRFS)) (fun F RNG4 st4 p COPY n HLE => SC2 L RNG4 st4 LB d (idx ++ [zlength d; zlength
        d; 0]) F p COPY n NO5 NO4 (rng_fp_le _ _ _ _ HLE HRI) (RFSM L RNG RNG4 HLE HRFS))).
Qed.
End CANSEC.
