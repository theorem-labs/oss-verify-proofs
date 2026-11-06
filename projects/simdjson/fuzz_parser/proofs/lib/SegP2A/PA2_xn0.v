(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim AsanCtrl AsanEmbed HarnessP SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface AU_iface AU_kit AU_fuzz_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require ABytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg SegBridge.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosKitA PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface A2Lib PA2_kz PA2_reg PA2_regN PA2_xlib PA2_sm5 PA2_head PA2_exit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require PA2_t0c PA2_t0nf A2N_defs A2D_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require A2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM SFPA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegGhost SegLib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2G2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import PA2_winN PA2_xcnd A2N_sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjStage1 SjS1Bytes SjInv.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

Section XN0.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variables (L : alayout) (RNG3 RNG4 : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (m m3 m4 : amem) (st3 st4 : astate) (LB : list ablock) (lo : Z) (d idx : list Z) (i0 : Z)
            (pim psi pcp ptp psb poc pia : AsanCtrl.aptr) (THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
            (x88 : word) (cls FA FN : Z) (F SPAX : Z) (rest3 rest4 : list Z) (E' : env) (p : AsanCtrl.aptr) (COPY : Z) (junk : list byte).
  (* [comment removed for export] *)
  Variables (SP16 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD : Z).
  Hypothesis E_SP : u sp = 16 * SP16.
  Hypothesis E_T8 : THIS = 8 * T8.
  Hypothesis E_DOC8 : DOC = 8 * DOC8.
  Hypothesis E_B8 : BUF = 8 * B8 + BO.
  Hypothesis E_I8 : ASI = 8 * I8.
  Hypothesis E_TB8 : TPA = 8 * TB8.
  Hypothesis E_SB8 : SBA = 8 * SB8.
  Hypothesis E_OC8 : AOC = 8 * OC8.
  Hypothesis E_IA8 : AIA = 8 * IA8.
  Hypothesis E_F11 : F = 2048 * F11.
  Hypothesis E_CP8 : COPY = 8 * CP8.
  Hypothesis E_LEN : LEN = zlength d.
  Hypothesis E_N : N = zlength idx.
  Hypothesis E_CAPT : ntp = 8 * CAPT.
  Hypothesis E_CAPS : nsb = CAPS.
  Hypothesis E_PB : u sp - 384 - SPAX = 16 * PB.
  Hypothesis E_FLAG : FLAG = fflag L 5 F.
  Hypothesis E_V : V = i0.
  Hypothesis D_BO : 0 <= BO <= 7.
  Hypothesis D_BG : 0 <= LEN + BO + 64 - 8 * BG <= 7.
  Hypothesis D_IG : 0 <= 8 * IG - (4 * N + 12) <= 7.
  Hypothesis D_SG : 0 <= CAPS - 8 * SG <= 7.
  Hypothesis D_CGF : 0 <= LEN - V + 64 - 8 * CGF <= 7.
  Hypothesis D_ZP : 0 <= ZP <= 1 /\ 1 <= LEN - V + 64 - 8 * CGF + 8 * ZP <= 8.
  Hypothesis D_DG : 0 <= 8 * DG - (LEN - V) <= 7.
  Hypothesis D_SD : 0 <= BO + V - 8 * SD <= 7.
  Hypothesis D_SRG : 0 <= 8 * SRG - (BO + LEN - 8 * SD) <= 7.
  Hypothesis D_HC : 0 <= COPY - 64 * HC <= 63.
  Hypothesis D_HCE : 0 <= 64 * HCE - (COPY + (LEN - V + 64)) <= 63.
  Hypothesis D_HBG : 0 <= BUF + V - 64 * HBG <= 63.
  Hypothesis D_HBGE : 0 <= 64 * HBGE - (BUF + LEN) <= 63.
  Hypothesis D_MD : 0 <= (LEN - V) - 8 * MD <= 7.
  (* [comment removed for export] *)
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
  Hypothesis Hntp8 : ntp mod 8 = 0.
  Hypothesis Hntp : 8 * (zlength idx + 3) <= ntp <= 2^27.
  Hypothesis Hnsb3 : 5 * zlength d + 182 <= 3 * nsb.
  Hypothesis Hnsb : zlength d + 60 <= nsb <= 2^24.
  Hypothesis Hbuf : bytes_at asegs m BUF (s1buf d).
  Hypothesis Hlen : zlength d + 64 <= 2^20.
  Hypothesis Sn : 1 <= zlength idx <= zlength d.
  Hypothesis HO8 : rw_cells asegs m (THIS + 8) [C4 (Z_to_bv 64 (zlength idx))].
  Hypothesis HO16 : rw_cells asegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)].
  Hypothesis HO40 : rw_cells asegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Hypothesis HO56 : rw_cells asegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88].
  Hypothesis HDOC : rw_cells asegs m DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)].
  Hypothesis Hda : DOC mod 8 = 0.
  Hypothesis Ifk : In (mkABlock (ABFake cls) FA FN) LB.
  Hypothesis Hfk1 : FA <= DOC.
  Hypothesis Hfk2 : DOC + 16 <= FA + FN.
  Hypothesis Hfk3 : ablk FA (FA + FN).
  Hypothesis HCIMG : client_img m.
  Hypothesis HCI : forall iv, In iv client_ranges -> In iv CI.
  Hypothesis Hlo1 : ATOP + 4096 <= lo.
  Hypothesis Hlo2 : lo <= u sp - STAGE2_STACK_A.
  Hypothesis Hsp16 : u sp mod 16 = 0.
  Hypothesis Hsp47 : u sp <= 2^47.
  Hypothesis HTP : tp = Z_to_bv 64 ATP.
  (* [comment removed for export] *)
  Hypothesis AH3 : AHEAP AI L RNG3 st3 (mkABlock (ABFake 5) F 2048 :: LB) m3.
  Hypothesis PW3 : aheap_pres_W CI LB (u sp) (s2_winA THIS TPA ntp SBA nsb AOC AIA) m m3.
  Hypothesis HSPA32 : SPAX mod 32 = 0.
  Hypothesis HSPA : 384 <= u sp - SPAX <= 415.
  Hypothesis HFm : F mod 2048 = 0.
  Hypothesis HFb : ablk F (F + 2048).
  Hypothesis HFt : F + 2048 <= ATOP.
  Let ZL3 : list Z :=
    PA2_t0c.ZL_t0'' (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8)
      (u s9) (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest3.
  Hypothesis Hg : SP.gagree 35 (mkEZ ZL3) E'.
  Hypothesis Hb : eb E' = eb (mkEZ ZL3).
  Hypothesis HK3 : know_ok asegs E' m3 A2_defs.XNEW_kn.
  Hypothesis HV2 : u (edenot E' (EVar 36)) = i0.
  Hypothesis Hi0 : znth idx 0 = i0.
  Hypothesis HI0 : 0 <= i0 /\ zlength d - i0 >= 1.
  Hypothesis STK3 : stk asegs m3 lo (u sp).
  (* [comment removed for export] *)
  Hypothesis MI4 : mem_inv asegs m4.
  Hypothesis STK4 : stk asegs m4 lo SPAX.
  Hypothesis PRES4 : aheap_pres CI (mkABlock (ABFake 5) F 2048 :: LB) SPAX m3 m4.
  Hypothesis AH4 : AHEAP AI L RNG4 st4 (HB p COPY (zlength d - i0 + 64) :: mkABlock (ABFake 5) F 2048 :: LB) m4.
  Hypothesis CB4 : rw_cells asegs m4 COPY [CB (Z.to_nat (zlength d - i0 + 64)) junk].

  Ltac kin := cbv [A2_defs.XNEW_kn]; repeat (first [left; reflexivity | right]).

  (* [comment removed for export] *)
  Lemma xw_gen : forall b k w v, In (KWord (SA b k) w v) A2_defs.XNEW_kn -> expr_vars_lt 35 b = true -> expr_vars_lt 35 v = true ->
    (zok b && zok v)%bool = true -> bytes_at asegs m3 (zden ZL3 b mod M64 + k) (word_to_le_bytes w (Z_to_bv 64 (zden ZL3 v))).
  Proof. intros b k w v Hin H1 H2 H3. exact (kx_word_g asegs 35 ZL3 E' m3 b k w v Hg (eq_sym Hb) H1 H2 H3 (proj1 (Forall_forall _ _) HK3 _ Hin)). Qed.
  Lemma xz_gen : forall b k n, In (KZero (SA b k) n) A2_defs.XNEW_kn -> expr_vars_lt 35 b = true -> expr_vars_lt 35 n = true ->
    (zok b && zok n)%bool = true ->
    forall i, 0 <= i < zden ZL3 n mod M64 -> m3 (Z_to_bv 64 (zden ZL3 b mod M64 + k + i)) = Some (Z_to_bv 8 0).
  Proof. intros b k n Hin H1 H2 H3. exact (kx_zero_g asegs 35 ZL3 E' m3 b k n Hg (eq_sym Hb) H1 H2 H3 (proj1 (Forall_forall _ _) HK3 _ Hin)). Qed.
  Lemma xr_gen : forall b k n, In (KWr (SA b k) n) A2_defs.XNEW_kn -> expr_vars_lt 35 b = true -> expr_vars_lt 35 n = true ->
    (zok b && zok n)%bool = true -> wr_at asegs m3 (zden ZL3 b mod M64 + k) (zden ZL3 n mod M64).
  Proof. intros b k n Hin H1 H2 H3. exact (kx_wr_g asegs 35 ZL3 E' m3 b k n Hg (eq_sym Hb) H1 H2 H3 (proj1 (Forall_forall _ _) HK3 _ Hin)). Qed.
  Ltac zc := cbv [A2_defs.vRA A2_defs.vSP A2_defs.vSP16 A2_defs.vGP A2_defs.vTP A2_defs.vS0 A2_defs.vS1 A2_defs.vS2 A2_defs.vS3
                  A2_defs.vS4 A2_defs.vS5 A2_defs.vS6 A2_defs.vS7 A2_defs.vS8 A2_defs.vS9 A2_defs.vS10 A2_defs.vS11 A2_defs.vSPA
                  A2_defs.vPB A2_defs.vF A2_defs.vF11 A2_defs.vFLAG A2_defs.vTHIS A2_defs.vT8 A2_defs.vDOC A2_defs.vDOC8 A2_defs.vIDX
                  A2_defs.vI8 A2_defs.vTBASE A2_defs.vTB8 A2_defs.vSBASE A2_defs.vSB8 A2_defs.vSHF A2_defs.V A2_defs.mul A2_defs.add
                  A2_defs.sub ZL3];
            cbn [zden nth PA2_t0c.ZL_t0'' app].
  Ltac zden_mod := repeat (rewrite (Z.mod_small _ M64) by (pose proof (u_rngE sp); Z.div_mod_to_equations; lia)).


  Lemma Rsp : 0 <= u sp < M64.
  Proof. apply u_rngE. Qed.
  Lemma ESPA : 16 * SP16 + -384 - 16 * PB = SPAX.
  Proof. lia. Qed.
  Lemma HSPAr : 0x665000 <= SPAX /\ SPAX + 384 <= u sp.
  Proof. clear - HSPA Hlo1 Hlo2 HSPA32. unfold STAGE2_STACK_A in Hlo2. atop_facts. lia. Qed.
  Lemma WSPA : forall k, 0 <= k -> k + 8 <= 384 -> wr_at asegs m3 (SPAX + k) 8.
  Proof.
    intros k H1 H2. pose proof HSPAr as HS. unfold STAGE2_STACK_A in Hlo2.
    apply (stk_wr_atA m3 lo (u sp)); [exact STK3 | clear - H1 HS Hlo2 HSPA; lia | clear - H2 HS HSPA; lia | lia].
  Qed.
  Ltac clr := repeat match goal with H : _ |- _ => clear H end.
  Ltac zcH H := unfold ZL3 in H;
    cbv [A2_defs.vRA A2_defs.vSP A2_defs.vSP16 A2_defs.vGP A2_defs.vTP A2_defs.vS0 A2_defs.vS1 A2_defs.vS2 A2_defs.vS3
         A2_defs.vS4 A2_defs.vS5 A2_defs.vS6 A2_defs.vS7 A2_defs.vS8 A2_defs.vS9 A2_defs.vS10 A2_defs.vS11 A2_defs.vSPA
         A2_defs.vPB A2_defs.vF A2_defs.vF11 A2_defs.vFLAG A2_defs.vTHIS A2_defs.vT8 A2_defs.vDOC A2_defs.vDOC8 A2_defs.vIDX
         A2_defs.vI8 A2_defs.vTBASE A2_defs.vTB8 A2_defs.vSBASE A2_defs.vSB8 A2_defs.vSHF A2_defs.V A2_defs.mul A2_defs.add
         A2_defs.sub] in H;
    cbn [zden nth PA2_t0c.ZL_t0'' app] in H.
  (* [comment removed for export] *)
  Ltac spa k v H :=
    let B := fresh "B" in
    pose proof (xw_gen A2_defs.vSPA k 8 v ltac:(kin) eq_refl eq_refl eq_refl) as B; zcH B;
    rewrite ESPA, (Z.mod_small SPAX) in B by (pose proof HSPAr as X; pose proof Rsp as Y; clear - X Y; lia);
    rewrite <- ?E_T8, <- ?E_I8, <- ?E_TB8, <- ?E_SB8, <- ?E_F11 in B;
    pose proof (aheap_pres_rw_cells CI _ _ m3 m4 _ _ PRES4 (rw8_of m3 _ _ B (WSPA k ltac:(clr; lia) ltac:(clr; lia)))
                  ltac:(apply acr_stack; cbn [cells_size csize]; pose proof HSPAr as X; pose proof Hsp47 as Y; clear - X Y; lia)) as H; clear B.
  Ltac sv k o v := let B := fresh "B" in
    pose proof (xw_gen A2_defs.vSP o 8 v ltac:(kin) eq_refl eq_refl eq_refl) as B; zcH B;
    rewrite <- E_SP, (Z.mod_small (u sp)) in B by (pose proof Rsp as X; clear - X; lia);
    replace (u sp + o) with (u sp - 8 - 8 * k) in B by (clr; lia);
    cbn [nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add];
    apply (aheap_pres_bytes_at CI _ _ m3 m4 _ _ PRES4 B);
    apply acr_stack; rewrite ?length_word_to_le_bytes; pose proof HSPAr as X; pose proof Hsp47 as Y; pose proof HSPA as Z; clear - X Y Z; lia.


  Ltac xpre :=
    unfold STAGE2_STACK_A in Hlo2; atop_facts;
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH3 (or_intror Ith)) as (_ & _ & _ & At & _);
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH3 (or_intror Isi)) as (_ & _ & Ai1 & Ai & _);
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH3 (or_intror Icp)) as (_ & _ & _ & Ac & _);
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH3 (or_intror Itp)) as (_ & _ & _ & Ap & _);
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH3 (or_intror Isb)) as (_ & _ & _ & As & _);
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH3 (or_intror Ioc)) as (_ & _ & _ & Ao & _);
    pose proof (hb_band AI _ _ _ _ _ _ _ _ AH3 (or_intror Iia)) as (_ & _ & _ & Aa & _).

  (* [comment removed for export] *)
  Lemma REG3 : a2_reg 8608 (u sp) THIS DOC BUF LEN ASI N TPA CAPT SBA CAPS AOC AIA.
  Proof.
    xpre.
    assert (HBO : BUF mod 8 = BO) by (rewrite E_B8; clear - D_BO; Z.div_mod_to_equations; lia).
    assert (HC8 : ntp / 8 = CAPT) by (rewrite E_CAPT; clear; Z.div_mod_to_equations; lia).
    assert (Hnsi' : 4 * zlength idx + 12 <= nsi) by (clear - Hnsi; lia).
    assert (Hlo2' : lo <= u sp - 8608) by (clear - Hlo2; lia).
    pose proof (a2_reg_of AI L RNG3 st3 (mkABlock (ABFake 5) F 2048 :: LB) m3 (u sp) lo 8608 d idx cls FA FN pim psi pcp ptp psb poc pia
                  THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia AH3 ND (or_intror Ith) Hnim (or_intror Isi) Hnsi'
                  (or_intror Icp) Hb1 Hb2 (or_intror Itp) (or_intror Isb) (or_intror Ioc) Hnoc (or_intror Iia) Hnia (or_intror Ifk) Hfk1 Hfk2 Hfk3
                  Hntp8 Hntp Hnsb3 Hnsb Hlen Sn Hlo1 Hlo2' ltac:(lia) Hsp47) as REG.
    unfold a2_reg in REG |- *. rewrite <- E_LEN, <- E_N, HC8, E_CAPS in REG. exact REG.
  Qed.
  Lemma REGF3 : a2_regF 8608 (u sp) F THIS DOC BUF LEN ASI N TPA CAPT SBA CAPS AOC AIA.
  Proof.
    xpre.
    assert (HC8 : ntp / 8 = CAPT) by (rewrite E_CAPT; clear; Z.div_mod_to_equations; lia).
    assert (Hnsi' : 4 * zlength idx + 12 <= nsi) by (clear - Hnsi; lia).
    assert (Hlo2' : lo <= u sp - 8608) by (clear - Hlo2; lia).
    assert (Hnsb' : nsb <= 2^24) by (clear - Hnsb; lia).
    pose proof (a2_regF_of AI L RNG3 st3 LB m3 (u sp) lo 8608 d idx cls FA FN F pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF
                  nim nsi ncp ntp nsb noc nia AH3 Ith Hnim Isi Hnsi' Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia Ifk Hfk1 Hfk2 Hntp8 Hnsb'
                  HFb HFt Hlo1 Hlo2' ltac:(lia)) as REGF.
    unfold a2_regF in REGF |- *. rewrite <- E_LEN, <- E_N, HC8, E_CAPS in REGF. exact REGF.
  Qed.
  Lemma REGC4 : a2_regC 8608 (u sp) F THIS DOC BUF LEN ASI N TPA CAPT SBA CAPS AOC AIA COPY (LEN - V + 64).
  Proof.
    xpre.
    assert (HC8 : ntp / 8 = CAPT) by (rewrite E_CAPT; clear; Z.div_mod_to_equations; lia).
    assert (Hnsi' : 4 * zlength idx + 12 <= nsi) by (clear - Hnsi; lia).
    assert (Hlo2' : lo <= u sp - 8608) by (clear - Hlo2; lia).
    assert (Hnsb' : nsb <= 2^24) by (clear - Hnsb; lia).
    pose proof (a2_regC_of AI L RNG4 st4 LB m4 (u sp) lo 8608 d idx cls FA FN F p COPY (zlength d - i0 + 64) pim psi pcp ptp psb poc pia
                  THIS ASI ACP TPA SBA AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia AH4 Ith Hnim Isi Hnsi' Icp Hb1 Hb2 Itp Isb Ioc Hnoc Iia Hnia
                  Ifk Hfk1 Hfk2 Hntp8 Hnsb' Hlo1 Hlo2' ltac:(lia)) as REGC.
    unfold a2_regC in REGC |- *. rewrite <- E_LEN, <- E_N, HC8, E_CAPS, <- E_V in REGC. exact REGC.
  Qed.
  Lemma HBO8 : BUF mod 8 = BO.
  Proof. rewrite E_B8. clear - D_BO. Z.div_mod_to_equations. lia. Qed.
  Ltac xreg := pose proof REG3 as REG; unfold a2_reg in REG; rewrite HBO8 in REG; destruct_a2_reg REG;
               pose proof REGF3 as REGF; unfold a2_regF in REGF; destruct_a2_regF REGF;
               pose proof REGC4 as REGC; unfold a2_regC in REGC; destruct_a2_regC REGC;
               assert (H_V : 0 <= V /\ 1 <= LEN - V) by (clear - HI0 E_V E_LEN; lia).
  Ltac xall := xpre; xreg.

  (* [comment removed for export] *)
  Lemma M_SPA152 : rw_cells asegs m4 (SPAX + 152) [C8 (Z_to_bv 64 (T8 + SH + 7))].
  Proof. spa 152 (A2_defs.add (A2_defs.add A2_defs.vT8 (ELit 2147450880)) (ELit 7)) X. exact X. Qed.
  Lemma M_SPA160 : rw_cells asegs m4 (SPAX + 160) [C8 (Z_to_bv 64 (THIS + 16))].
  Proof. spa 160 (A2_defs.add A2_defs.vTHIS (ELit 16)) X. exact X. Qed.
  Lemma M_SPA168 : rw_cells asegs m4 (SPAX + 168) [C8 (Z_to_bv 64 (ASI + 4))].
  Proof. spa 168 (A2_defs.add A2_defs.vIDX (ELit 4)) X. exact X. Qed.
  Lemma M_SPA176 : rw_cells asegs m4 (SPAX + 176) [C8 (Z_to_bv 64 (TPA + 8))].
  Proof. spa 176 (A2_defs.add A2_defs.vTBASE (ELit 8)) X. exact X. Qed.
  Lemma M_SPA184 : rw_cells asegs m4 (SPAX + 184) [C8 (Z_to_bv 64 (THIS + 8))].
  Proof. spa 184 (A2_defs.add A2_defs.vTHIS (ELit 8)) X. exact X. Qed.
  Lemma M_SPA192 : rw_cells asegs m4 (SPAX + 192) [C8 (Z_to_bv 64 (T8 + SH + 2))].
  Proof. spa 192 (A2_defs.add (A2_defs.add A2_defs.vT8 (ELit 2147450880)) (ELit 2)) X. exact X. Qed.
  Lemma M_SPA200 : rw_cells asegs m4 (SPAX + 200) [C8 (Z_to_bv 64 (T8 + SH + 1))].
  Proof. spa 200 (A2_defs.add (A2_defs.add A2_defs.vT8 (ELit 2147450880)) (ELit 1)) X. exact X. Qed.
  Lemma M_SPA208 : rw_cells asegs m4 (SPAX + 208) [C8 (Z_to_bv 64 (SBA))].
  Proof. spa 208 A2_defs.vSBASE X. exact X. Qed.
  Lemma M_SPA216 : rw_cells asegs m4 (SPAX + 216) [C8 (Z_to_bv 64 (THIS + 88))].
  Proof. spa 216 (A2_defs.add A2_defs.vTHIS (ELit 88)) X. exact X. Qed.
  Lemma M_SPA224 : rw_cells asegs m4 (SPAX + 224) [C8 (Z_to_bv 64 (T8 + SH + 11))].
  Proof. spa 224 (A2_defs.add (A2_defs.add A2_defs.vT8 (ELit 2147450880)) (ELit 11)) X. exact X. Qed.
  Lemma M_SPA232 : rw_cells asegs m4 (SPAX + 232) [C8 (Z_to_bv 64 (THIS))].
  Proof. spa 232 A2_defs.vTHIS X. exact X. Qed.
  Lemma M_SPA240 : rw_cells asegs m4 (SPAX + 240) [C8 (Z_to_bv 64 (F))].
  Proof. spa 240 A2_defs.vF X. exact X. Qed.
  Lemma M_SPA248 : rw_cells asegs m4 (SPAX + 248) [C8 (Z_to_bv 64 (SH))].
  Proof. spa 248 (ELit 2147450880) X. exact X. Qed.
  Lemma M_SPA264 : rw_cells asegs m4 (SPAX + 264) [C8 (Z_to_bv 64 (F))].
  Proof. spa 264 A2_defs.vF X. exact X. Qed.

  (* [comment removed for export] *)
  Lemma M_SAVED : forall k, 0 <= k < 13 ->
    bytes_at asegs m4 (u sp - 8 - 8 * k) (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [u ra; u s0; u s1; u s2; u s3; u s4; u s5; u s6; u s7; u s8; u s9; u s10; u s11] 0))).
  Proof.
    intros k Hk.
    assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
    destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]];
      [ sv 0 (-8) A2_defs.vRA | sv 1 (-16) A2_defs.vS0 | sv 2 (-24) A2_defs.vS1 | sv 3 (-32) A2_defs.vS2 | sv 4 (-40) A2_defs.vS3
      | sv 5 (-48) A2_defs.vS4 | sv 6 (-56) A2_defs.vS5 | sv 7 (-64) A2_defs.vS6 | sv 8 (-72) A2_defs.vS7 | sv 9 (-80) A2_defs.vS8
      | sv 10 (-88) A2_defs.vS9 | sv 11 (-96) A2_defs.vS10 | sv 12 (-104) A2_defs.vS11 ].
  Qed.

  (* [comment removed for export] *)
  Lemma M_O88 : rw_cells asegs m4 (THIS + 88) [C8 (Z_to_bv 64 DOC)].
  Proof.
    xall. destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 (or_intror Ith)) as (_ & _ & _ & _ & _ & W3T & _).
    pose proof (xw_gen A2_defs.vTHIS 88 8 A2_defs.vDOC ltac:(kin) eq_refl eq_refl eq_refl) as B; zcH B.
    rewrite <- E_T8, <- E_DOC8, (Z.mod_small THIS) in B by (clear - H_THIS; atop_facts; lia).
    apply (aheap_pres_rw_cells CI _ _ m3 m4 _ _ PRES4 (rw8_of m3 _ _ B (wr_at_sub m3 THIS nim (THIS + 88) 8 W3T ltac:(lia) ltac:(clear - Hnim; lia) ltac:(lia)))).
    apply (acr_blk CI (mkABlock (ABFake 5) F 2048 :: LB) SPAX _ _ _ (or_intror Ith)); cbn [ab_addr ab_size cells_size csize]; clear - Hnim; lia.
  Qed.
  Lemma W3F : wr_at asegs m3 F 2048.
  Proof.
    xall. pose proof (xr_gen A2_defs.vF 0 (ELit 2048) ltac:(kin) eq_refl eq_refl eq_refl) as W; zcH W.
    rewrite <- E_F11, (Z.mod_small F), Z.add_0_r, (Z.mod_small 2048) in W by (clear - H_F; atop_facts; lia). exact W.
  Qed.
  Lemma W_F : wr_at asegs m4 F 2048.
  Proof.
    apply (aheap_pres_wr_at CI _ _ m3 m4 _ _ PRES4 W3F). apply (acr_blk CI (mkABlock (ABFake 5) F 2048 :: LB) SPAX (mkABlock (ABFake 5) F 2048) _ _ (or_introl eq_refl));
      cbn [ab_addr ab_size]; lia.
  Qed.
  Lemma M_FL : rw_cells asegs m4 (F + 2040) [C8 (Z_to_bv 64 FLAG)].
  Proof.
    xall. pose proof (xw_gen A2_defs.vF 2040 8 A2_defs.vFLAG ltac:(kin) eq_refl eq_refl eq_refl) as B; zcH B.
    rewrite <- E_F11, (Z.mod_small F) in B by (clear - H_F; atop_facts; lia).
    apply (aheap_pres_rw_cells CI _ _ m3 m4 _ _ PRES4 (rw8_of m3 _ _ B (wr_at_sub m3 F 2048 (F + 2040) 8 W3F ltac:(lia) ltac:(lia) ltac:(lia)))).
    apply (acr_blk CI (mkABlock (ABFake 5) F 2048 :: LB) SPAX (mkABlock (ABFake 5) F 2048) _ _ (or_introl eq_refl)); cbn [ab_addr ab_size cells_size csize]; lia.
  Qed.
  Lemma M_SHF : wr_at asegs m4 (SH + 256 * F11) 256.
  Proof.
    xall. assert (HSF : 0 <= 256 * F11 + SH /\ 256 * F11 + SH + 256 < M64) by (clear - HFb E_F11; unfold ablk, AIMG_HI, KLS in HFb; lia).
    pose proof (xr_gen A2_defs.vSHF 0 (ELit 256) ltac:(kin) eq_refl eq_refl eq_refl) as B; zcH B.
    rewrite (Z.mod_small (256 * F11 + 2147450880)), Z.add_0_r, (Z.mod_small 256) in B by (clear - HSF; lia).
    replace (SH + 256 * F11) with (256 * F11 + 2147450880) by lia.
    apply (aheap_pres_wr_at CI _ _ m3 m4 _ _ PRES4 B). right; right. right; right. exists 5, F, 2048.
    split; [left; reflexivity|]. unfold ASHOFF. clear - E_F11; lia.
  Qed.
  Lemma M_IDX0 : rw_cells asegs m4 ASI [C4 (Z_to_bv 64 V)].
  Proof.
    xall. destruct (AI_block AI _ _ _ _ _ _ _ _ AH3 (or_intror Isi)) as (_ & _ & _ & _ & _ & W3I & _).
    assert (EV36 : edenot E' (EVar 36) = Z_to_bv 64 i0).
    { apply bv_eq. rewrite u_Z_to_bv, <- HV2, Z.mod_small by apply u_rngE. reflexivity. }
    assert (K : kentry_ok asegs E' m3 (KWord (SA A2_defs.vIDX 0) 4 (A2_defs.V 36))) by (apply (proj1 (Forall_forall _ _) HK3); kin).
    pose proof (SB.kx_word asegs E' m3 A2_defs.vIDX 0 4 (A2_defs.V 36) K) as B.
    rewrite <- (SP.edenot_gagree 35 (mkEZ ZL3) E' A2_defs.vIDX Hg (eq_sym Hb) eq_refl), u_zden in B by reflexivity.
    cbv [A2_defs.V] in B. rewrite EV36 in B. zcH B. rewrite <- E_I8, (Z.mod_small ASI), Z.add_0_r in B by (clear - H_IDX H_N; atop_facts; lia).
    rewrite E_V. apply (aheap_pres_rw_cells CI _ _ m3 m4 _ _ PRES4 (rw4_of m3 _ _ B (wr_at_sub m3 ASI nsi ASI 4 W3I ltac:(lia) ltac:(clear - Hnsi H_N E_N; lia) ltac:(lia)))).
    apply (acr_blk CI (mkABlock (ABFake 5) F 2048 :: LB) SPAX _ _ _ (or_intror Isi)); cbn [ab_addr ab_size cells_size csize]; clear - Hnsi H_N E_N; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma S_STK3 : forall i, 0 <= i < 1076 -> m3 (Z_to_bv 64 (SH + 2 * SP16 - 1076 + i)) = Some (Z_to_bv 8 0).
  Proof.
    xall.
    pose proof (xz_gen (A2_defs.mul 2 A2_defs.vSP16) 2147449804 (A2_defs.sub (ELit 1062) (A2_defs.mul 2 A2_defs.vPB))
                  ltac:(kin) eq_refl eq_refl eq_refl) as Z1.
    pose proof (xz_gen (A2_defs.sub (A2_defs.mul 2 A2_defs.vSP16) (A2_defs.mul 2 A2_defs.vPB)) 2147450866 (ELit 1)
                  ltac:(kin) eq_refl eq_refl eq_refl) as Z2.
    pose proof (xz_gen (A2_defs.sub (A2_defs.mul 2 A2_defs.vSP16) (A2_defs.mul 2 A2_defs.vPB)) 2147450867 (A2_defs.add (ELit 13) (A2_defs.mul 2 A2_defs.vPB))
                  ltac:(kin) eq_refl eq_refl eq_refl) as Z3.
    zcH Z1. zcH Z2. zcH Z3.
    assert (HPB : 0 <= PB <= 1) by (clear - E_PB HSPA; lia).
    assert (HS16 : 0x7fff00000000 <= 16 * SP16 <= 2^47) by (clear - H_SP E_SP; lia).
    rewrite !(Z.mod_small (2 * SP16)) in Z1 by (clear - HS16; lia). rewrite !(Z.mod_small (1062 - 2 * PB)) in Z1 by (clear - HPB; lia).
    rewrite !(Z.mod_small (2 * SP16 - 2 * PB)) in Z2, Z3 by (clear - HS16 HPB; lia).
    rewrite !(Z.mod_small 1) in Z2 by lia. rewrite !(Z.mod_small (13 + 2 * PB)) in Z3 by (clear - HPB; lia).
    intros i Hi.
    destruct (Z_lt_le_dec i (1062 - 2 * PB)) as [L1|L1]; [|destruct (Z.eq_dec i (1062 - 2 * PB)) as [L2|L2]].
    - replace (SH + 2 * SP16 - 1076 + i) with (2 * SP16 + 2147449804 + i) by lia. apply Z1. lia.
    - replace (SH + 2 * SP16 - 1076 + i) with (2 * SP16 - 2 * PB + 2147450866 + 0) by lia. apply Z2. lia.
    - replace (SH + 2 * SP16 - 1076 + i) with (2 * SP16 - 2 * PB + 2147450867 + (i - 1063 + 2 * PB)) by lia. apply Z3. lia.
  Qed.
  Lemma S_STK : forall i, 0 <= i < 1076 -> m4 (Z_to_bv 64 (SH + 2 * SP16 - 1076 + i)) = Some (Z_to_bv 8 0).
  Proof.
    xall. intros i Hi. replace (SH + 2 * SP16 - 1076 + i) with (SH + (2 * SP16 - 1076) + i) by lia.
    apply (shadow_pres CI _ SPAX m3 m4 (2 * SP16 - 1076) 1076 PRES4 ltac:(clear - H_SP E_SP; lia) ltac:(clear - H_SP E_SP; lia)); [| | lia].
    - intros i' Hi'. left. clear - E_SP Hlo1 Hlo2 Hi' H_SP. lia.
    - intros i' Hi'. replace (SH + (2 * SP16 - 1076) + i') with (SH + 2 * SP16 - 1076 + i') by lia. apply S_STK3; lia.
  Qed.
  Lemma S_DOC8 : forall i, 0 <= i < 2 -> m4 (Z_to_bv 64 (SH + DOC8 + i)) = Some (Z_to_bv 8 0).
  Proof.
    xall. pose proof (xz_gen A2_defs.vDOC8 2147450880 (ELit 2) ltac:(kin) eq_refl eq_refl eq_refl) as Z1. zcH Z1.
    rewrite (Z.mod_small DOC8), (Z.mod_small 2) in Z1 by (clear - H_DOC E_DOC8; atop_facts; lia).
    apply (shadow_pres CI _ SPAX m3 m4 DOC8 2 PRES4 ltac:(clear - H_DOC E_DOC8; lia) ltac:(clear - H_DOC E_DOC8; atop_facts; lia)).
    - intros i Hi. right; right. exists cls, FA, FN. split; [right; exact Ifk | clear - E_DOC8 Hfk1 Hfk2 Hi; lia].
    - intros i Hi. replace (SH + DOC8 + i) with (DOC8 + 2147450880 + i) by lia. apply Z1. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac outW := intros a Ha; unfold s2_winA; cbn [outside];
    repeat split; unfold DJ in *; cbn [cells_size csize length] in Ha; lia.
  Ltac tr2 H I := apply (aheap_pres_rw_cells CI _ _ m3 m4 _ _ PRES4);
    [|apply (acr_blk CI (mkABlock (ABFake 5) F 2048 :: LB) SPAX _ _ _ (or_intror I)); cbn; lia];
    apply (aheap_pres_W_rw_cells CI LB (u sp) _ m m3 _ _ PW3 H); [apply (acr_blk CI LB (u sp) _ _ _ I); cbn; lia|].
  Lemma M_O8 : rw_cells asegs m4 (THIS + 8) [C4 (Z_to_bv 64 N)].
  Proof. xall. rewrite E_N. tr2 HO8 Ith. clear - D4 D5 D6 D7 E_CAPT E_CAPS. outW. Qed.
  Lemma M_O16 : rw_cells asegs m4 (THIS + 16) [C8 (Z_to_bv 64 ASI)].
  Proof. xall. tr2 HO16 Ith. clear - D4 D5 D6 D7 E_CAPT E_CAPS. outW. Qed.
  Lemma M_O40 : rw_cells asegs m4 (THIS + 40) [C8 (Z_to_bv 64 1024); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Proof. xall. change 1024 with MAX_DEPTH. tr2 HO40 Ith. clear - D4 D5 D6 D7 E_CAPT E_CAPS. outW. Qed.
  (* [comment removed for export] *)
  Lemma M_O56 : rw_cells asegs m4 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 LEN); C8 (Z_to_bv 64 DOC)].
  Proof.
    xall. pose proof (proj1 (ABytes.rw_cells_app asegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d))]
                  [C8 x88]) HO56) as [HO56a _].
    assert (M56 : rw_cells asegs m4 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 LEN)])
      by (rewrite E_LEN; tr2 HO56a Ith; clear - D4 D5 D6 D7 E_CAPT E_CAPS; outW).
    apply (proj2 (ABytes.rw_cells_app asegs m4 (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 LEN)]
                    [C8 (Z_to_bv 64 DOC)])). split; [exact M56|]. cbn [cells_size csize Nat.add]. replace (THIS + 56 + Z.of_nat 32) with (THIS + 88) by lia.
    exact M_O88.
  Qed.
  Lemma M_DOC : rw_cells asegs m4 DOC [C8 (Z_to_bv 64 TPA); C8 (Z_to_bv 64 SBA)].
  Proof.
    xall. apply (aheap_pres_rw_cells CI _ _ m3 m4 _ _ PRES4);
      [|apply (acr_blk CI (mkABlock (ABFake 5) F 2048 :: LB) SPAX _ _ _ (or_intror Ifk)); cbn; lia].
    apply (aheap_pres_W_rw_cells CI LB (u sp) _ m m3 _ _ PW3 HDOC); [apply (acr_blk CI LB (u sp) _ _ _ Ifk); cbn; lia|].
    clear - D1 D10 D11 D12 D13 E_CAPT E_CAPS. outW.
  Qed.
  Lemma M_BUFl : Z.of_nat (length (s1buf d)) = LEN + 64.
  Proof. rewrite E_LEN. unfold s1buf, zlength. rewrite length_map, length_app, repeat_length. lia. Qed.
  Lemma M_BUF : bytes_at asegs m4 BUF (s1buf d).
  Proof.
    xall. pose proof M_BUFl as BL. apply (aheap_pres_bytes_at CI _ _ m3 m4 _ _ PRES4);
      [|apply (acr_blk CI (mkABlock (ABFake 5) F 2048 :: LB) SPAX _ _ _ (or_intror Icp)); cbn [ab_addr ab_size]; rewrite ?BL; lia].
    apply (aheap_pres_W_bytes_at CI LB (u sp) _ m m3 _ _ PW3 Hbuf); [apply (acr_blk CI LB (u sp) _ _ _ Icp); cbn [ab_addr ab_size]; rewrite ?BL; lia|].
    rewrite BL. clear - D2 D15 D16 D17 D18 E_CAPT E_CAPS. outW.
  Qed.
  Lemma M_BUFz : forall i, 0 <= i < 64 -> nth_error (s1buf d) (Z.to_nat (LEN + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros i Hi. unfold s1buf. rewrite nth_error_map. rewrite nth_error_app2 by (rewrite E_LEN; unfold zlength; lia).
    rewrite nth_error_repeat by (rewrite E_LEN; unfold zlength; lia). reflexivity.
  Qed.
  Lemma M_FMIN : rw_cells asegs m4 0x10b978 [C4 (Z_to_bv 64 8388608)].
  Proof.
    xall. pose proof (client_img_x m HCIMG) as (_ & FM0 & _ & _ & _).
    pose proof (fmin_pres_W AI LB (u sp) _ m m3 HCI FM0 PW3) as FM3.
    assert (FM3' : rt_fmin m3).
    { apply FM3. intros a Ha. unfold AFMIN in Ha. clear - Ha H_THIS H_TB H_SB H_OC H_IA E_CAPT E_CAPS. unfold s2_winA; cbn [outside].
      repeat split; lia. }
    unfold rt_fmin, AFMIN in FM3'. apply (aheap_pres_rw_cells CI _ _ m3 m4 _ _ PRES4 FM3').
    left; right; left. exists (0x10b978, 0x10b97c). split; [apply HCI; unfold client_ranges; cbn [In app]; tauto | cbn; lia].
  Qed.
  Lemma S_IMG : forall a n i, In (a, n) A2_IMGSH -> 0 <= i < n -> m4 (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).
  Proof.
    xall. pose proof (client_img_x m HCIMG) as (_ & _ & _ & _ & IM0).
    apply img_sh_pts. apply (img_sh_pres AI (mkABlock (ABFake 5) F 2048 :: LB) SPAX m3 m4 HCI); [|exact PRES4].
    apply (img_sh_pres_W AI LB (u sp) _ m m3 HCI IM0 PW3). intros a Ha.
    clear - Ha HB_THIS HB_TB HB_SB HB_OC HB_IA H_THIS H_TB H_SB H_OC H_IA E_CAPT E_CAPS. unfold s2_winA; cbn [outside]. unfold DJ in *.
    repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Ltac in4 I := right; right; exact I.
  Local Notation LB4 := (HB p COPY (zlength d - i0 + 64) :: mkABlock (ABFake 5) F 2048 :: LB).
  Lemma Ith4 : In (HB pim THIS nim) LB4. Proof. in4 Ith. Qed.
  Lemma Isi4 : In (HB psi ASI nsi) LB4. Proof. in4 Isi. Qed.
  Lemma Icp4 : In (HB pcp ACP ncp) LB4. Proof. in4 Icp. Qed.
  Lemma Itp4 : In (HB ptp TPA ntp) LB4. Proof. in4 Itp. Qed.
  Lemma Isb4 : In (HB psb SBA nsb) LB4. Proof. in4 Isb. Qed.
  Lemma Ioc4 : In (HB poc AOC noc) LB4. Proof. in4 Ioc. Qed.
  Lemma Iia4 : In (HB pia AIA nia) LB4. Proof. in4 Iia. Qed.
  Lemma Icy4 : In (HB p COPY (zlength d - i0 + 64)) LB4. Proof. left; reflexivity. Qed.
  Ltac shz I := eapply (shadow_zero_in_blk AI _ _ _ _ _ _ _ _ _ _ AH4 I).
  Lemma S_T8 : forall i, 0 <= i < 12 -> m4 (Z_to_bv 64 (SH + T8 + i)) = Some (Z_to_bv 8 0).
  Proof. shz Ith4; clear - E_T8 Hnim; lia. Qed.
  Lemma S_B8 : forall i, 0 <= i < BG -> m4 (Z_to_bv 64 (SH + B8 + i)) = Some (Z_to_bv 8 0).
  Proof. xpre. shz Icp4; clear - E_B8 Hb1 Hb2 D_BG D_BO Ac E_LEN; Z.div_mod_to_equations; lia. Qed.
  Lemma S_I8 : forall i, 0 <= i < IG -> m4 (Z_to_bv 64 (SH + I8 + i)) = Some (Z_to_bv 8 0).
  Proof. shz Isi4; clear - E_I8 D_IG Hnsi E_N; lia. Qed.
  Lemma S_TB8 : forall i, 0 <= i < CAPT -> m4 (Z_to_bv 64 (SH + TB8 + i)) = Some (Z_to_bv 8 0).
  Proof. shz Itp4; clear - E_TB8 E_CAPT; lia. Qed.
  Lemma S_SB8 : forall i, 0 <= i < SG -> m4 (Z_to_bv 64 (SH + SB8 + i)) = Some (Z_to_bv 8 0).
  Proof. shz Isb4; clear - E_SB8 D_SG E_CAPS; lia. Qed.
  Lemma S_OC8 : forall i, 0 <= i < 1024 -> m4 (Z_to_bv 64 (SH + OC8 + i)) = Some (Z_to_bv 8 0).
  Proof. shz Ioc4; clear - E_OC8 Hnoc; lia. Qed.
  Lemma S_IA8 : forall i, 0 <= i < 128 -> m4 (Z_to_bv 64 (SH + IA8 + i)) = Some (Z_to_bv 8 0).
  Proof. shz Iia4; clear - E_IA8 Hnia; lia. Qed.
  Lemma S_CP8 : forall i, 0 <= i < CGF -> m4 (Z_to_bv 64 (SH + CP8 + i)) = Some (Z_to_bv 8 0).
  Proof. shz Icy4; clear - E_CP8 D_CGF E_LEN E_V; lia. Qed.
  Ltac wrb I := destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 I) as (_ & _ & _ & _ & _ & ?W & _).
  Lemma W_TB : wr_at asegs m4 TPA (8 * CAPT).
  Proof. wrb Itp4. rewrite <- E_CAPT. assumption. Qed.
  Lemma W_SB : wr_at asegs m4 SBA CAPS.
  Proof. wrb Isb4. rewrite <- E_CAPS. assumption. Qed.
  Lemma W_OC : wr_at asegs m4 AOC 8192.
  Proof. wrb Ioc4. eapply wr_at_sub; [eassumption | lia..]. Qed.
  Lemma W_IA : wr_at asegs m4 AIA 1024.
  Proof. wrb Iia4. eapply wr_at_sub; [eassumption | lia..]. Qed.
  Lemma W_IDX : wr_at asegs m4 ASI (4 * N + 12).
  Proof. wrb Isi4. eapply wr_at_sub; [eassumption | clear - Hnsi E_N Sn; lia..]. Qed.
  Lemma W_O24 : wr_at asegs m4 (THIS + 24) 4.
  Proof. wrb Ith4. eapply wr_at_sub; [eassumption | clear - Hnim; lia..]. Qed.
  Lemma W_COPY : wr_at asegs m4 COPY (LEN - V + 64).
  Proof. wrb Icy4. rewrite E_LEN, E_V. assumption. Qed.
  Lemma W_HC : wr_at asegs m4 (SH + 8 * HC) (8 * (HCE - HC)).
  Proof.
    xall. destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 Icy4) as (_ & _ & _ & _ & _ & _ & _ & (RLC & RHC & RC1 & RC2 & RC3 & RC4 & _ & W_ARC)).
    rewrite shad_div, shlen_d8 in W_ARC. unfold ASHOFF in W_ARC.
    apply (wr_at_sub m4 _ _ _ _ W_ARC); clear - RC1 RC2 RC3 RC4 D_HC D_HCE E_LEN E_V H_COPY H_V; Z.div_mod_to_equations; lia.
  Qed.
  Lemma W_HB : wr_at asegs m4 (SH + 8 * HBG) (8 * (HBGE - HBG)).
  Proof.
    xall. destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 Icp4) as (_ & _ & _ & _ & _ & _ & _ & (RLB & RHB & RB1 & RB2 & RB3 & RB4 & _ & W_ARB)).
    rewrite shad_div, shlen_d8 in W_ARB. unfold ASHOFF in W_ARB.
    apply (wr_at_sub m4 _ _ _ _ W_ARB); clear - RB1 RB2 RB3 RB4 D_HBG D_HBGE E_LEN Hb1 Hb2 HI0 E_V H_BUF; Z.div_mod_to_equations; lia.
  Qed.
  Lemma M_COPY : bytes_at asegs m4 COPY junk.
  Proof. exact (proj1 (cb_bytesA m4 _ _ _ CB4)). Qed.
  Lemma M_COPYl : Z.of_nat (length junk) = LEN - V + 64.
  Proof. rewrite (proj2 (cb_bytesA m4 _ _ _ CB4)), Z2Nat.id by (clear - HI0; lia). rewrite E_LEN, E_V. reflexivity. Qed.
  Lemma M_LG : bytes_at asegs m4 (SH + CP8 + (CGF - ZP)) (word_to_le_bytes 1 (Z_to_bv 64 (LEN - V + 64 - 8 * (CGF - ZP) - 8 * ZP))).
  Proof.
    xall. assert (G1 : 0 <= CGF - ZP) by (clear - D_CGF D_ZP H_LEN H_V; lia).
    assert (G2 : 8 * (CGF - ZP) < zlength d - i0 + 64) by (clear - D_CGF D_ZP E_LEN E_V; lia).
    pose proof (blk_granule AI _ _ _ _ _ _ _ _ (CGF - ZP) AH4 Icy4 G1 G2) as G.
    rewrite shad_div in G. unfold ASHOFF in G. rewrite E_CP8, Z.mul_comm, Z.div_mul in G by lia.
    rewrite le1_small by (clear - D_CGF D_ZP; lia).
    apply bytes1_of; [clear - H_COPY E_CP8 D_CGF D_ZP H_V; lia | clear - H_COPY E_CP8 D_CGF D_ZP H_V; atop_facts; lia |].
    rewrite G. f_equal. f_equal.
    destruct (Z.leb_spec (8 * (CGF - ZP) + 8) (zlength d - i0 + 64)) as [HL|HL]; clear - D_CGF D_ZP E_LEN E_V HL; lia.
  Qed.
  Lemma M_GOT : rt_got m4.
  Proof. exact (proj1 (client_rt_of_aheap AI L RNG4 st4 _ m4 AH4)). Qed.
  Lemma M_SHB : rt_shbase m4.
  Proof. destruct (client_rt_of_aheap AI L RNG4 st4 _ m4 AH4) as (_ & _ & _ & X & _). exact X. Qed.
  Lemma M_SUAR : rt_suar m4.
  Proof. destruct (client_rt_of_aheap AI L RNG4 st4 _ m4 AH4) as (_ & _ & _ & _ & X & _). exact X. Qed.
  Lemma M_SUARG : rw_cells asegs m4 AGOT_SUAR [C8 (Z_to_bv 64 ASUAR)].
  Proof. exact (client_got_of_aheap AI L RNG4 st4 _ m4 AH4 MI4). Qed.
  Lemma M_NT : rw_cells asegs m4 0x107fa0 [C8 (Z_to_bv 64 0x2cb90)].
  Proof. exact (got_nothrow_cell AI L RNG4 st4 _ m4 AH4 MI4). Qed.

  (* [comment removed for export] *)
  Lemma M_STK : stk asegs m4 lo (u sp).
  Proof.
    pose proof HSPAr as HS. pose proof Hlo2 as Hl. unfold STAGE2_STACK_A in Hl.
    apply (stk_merge asegs m4 lo SPAX (u sp)); [exact STK4 | | lia].
    destruct (stk_split asegs m3 lo SPAX (u sp) STK3 ltac:(lia)) as [_ SU].
    eapply aheap_pres_stk; [exact PRES4 | exact SU | lia | lia].
  Qed.
  Lemma M_LO : 0x665000 <= lo <= u sp - 8608.
  Proof. clear - Hlo1 Hlo2. unfold STAGE2_STACK_A in Hlo2. atop_facts. lia. Qed.

  (* [comment removed for export] *)
  Lemma a2n_kn4 :
    know_ok asegs (mkEZ (PA2_t0nf.ZL_t0n''''' (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8)
                            (u s9) (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG
                            V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4))
            m4 A2N_defs.T0_kn.
  Proof.
    xall.
    assert (H_TP : u tp = 0x642e70) by (rewrite HTP, u_Z_to_bv; reflexivity).
    assert (H_BG : 8 <= BG <= 131080 /\ 0 <= LEN + BO + 64 - 8 * BG <= 7) by (clear - D_BG D_BO H_LEN; lia).
    assert (H_IG : 2 <= IG <= 0x200000 /\ 0 <= 8 * IG - (4 * N + 12) <= 7) by (clear - D_IG H_N H_LEN; lia).
    assert (H_SG : 7 <= SG <= 2097152 /\ 0 <= CAPS - 8 * SG <= 7) by (clear - D_SG H_CAPS H_LEN; lia).
    assert (H_IGB : ASI + 8 * IG <= ATOPM) by (clear - D_IG H_IDX Hnsi E_N Ai1 Ai; atop_facts; lia).
    assert (H_CGF : 8 <= CGF <= 131080 /\ 0 <= LEN - V + 64 - 8 * CGF <= 7) by (clear - D_CGF H_V H_LEN; lia).
    assert (H_ZP : 0 <= ZP <= 1 /\ 1 <= LEN - V + 64 - 8 * CGF + 8 * ZP <= 8) by exact D_ZP.
    assert (H_DG : 1 <= DG <= 131072 /\ 0 <= 8 * DG - (LEN - V) <= 7) by (clear - D_DG H_V H_LEN; lia).
    assert (H_SD : 0 <= SD <= 131072 /\ 0 <= BO + V - 8 * SD <= 7) by (clear - D_SD H_V H_LEN D_BO; lia).
    assert (H_SRG : 1 <= SRG <= 131080 /\ 0 <= 8 * SRG - (BO + LEN - 8 * SD) <= 7 /\ 0 <= BG - (SD + SRG) <= 131080)
      by (clear - D_SRG D_SD D_BG D_BO H_V H_LEN; lia).
    assert (H_HC : 0x19940 <= HC <= 0x1ffffffe000 /\ 0 <= COPY - 64 * HC <= 63) by (clear - D_HC H_COPY H_V; atop_facts; lia).
    assert (H_HCE : 0x19940 <= HCE <= 0x1ffffffe000 /\ 0 <= 64 * HCE - (COPY + (LEN - V + 64)) <= 63) by (clear - D_HCE H_COPY H_V; atop_facts; lia).
    assert (H_HB : 0x19940 <= HBG <= 0x1ffffffe000 /\ 0 <= BUF + V - 64 * HBG <= 63) by (clear - D_HBG H_BUF H_V D_BO; atop_facts; lia).
    assert (H_HBE : 0x19940 <= HBGE <= 0x1ffffffe000 /\ 0 <= 64 * HBGE - (BUF + LEN) <= 63) by (clear - D_HBGE H_BUF H_V D_BO; atop_facts; lia).
    assert (H_MD : 0 <= MD <= 131072 /\ 0 <= (LEN - V) - 8 * MD <= 7) by (clear - D_MD H_V H_LEN; lia).
    assert (H_SE : B8 + BG <= 0xfffffff0000 /\ I8 + IG <= 0xfffffff0000 /\ TB8 + CAPT <= 0xfffffff0000 /\ SB8 + SG <= 0xfffffff0000 /\ CP8 + CGF <= 0xfffffff0000)
      by (clear - E_B8 D_BG D_BO H_BUF E_I8 D_IG H_IDX H_IGB E_TB8 H_TB E_SB8 D_SG H_SB E_CP8 D_CGF H_COPY H_V H_N; atop_facts; lia).
    assert (H_SPA : 0 <= PB <= 1 /\ (u sp - 384 - 16 * PB) mod 32 = 0)
      by (clear - E_PB HSPA HSPA32; rewrite <- E_PB in *; split; [lia|]; replace (u sp - 384 - (u sp - 384 - SPAX)) with SPAX by lia; exact HSPA32).
    assert (E_SPA : SPAX = u sp - 384 - 16 * PB) by lia.
    assert (H_COPY' : 0x665000 <= COPY /\ COPY + LEN - V + 64 <= ATOPM /\ COPY + LEN - V + 64 + 8608 <= u sp) by (clear - H_COPY; lia).
    clear H_COPY.
    pose proof M_SPA152. pose proof M_SPA160. pose proof M_SPA168. pose proof M_SPA176. pose proof M_SPA184. pose proof M_SPA192.
    pose proof M_SPA200. pose proof M_SPA208. pose proof M_SPA216. pose proof M_SPA224. pose proof M_SPA232. pose proof M_SPA240.
    pose proof M_SPA248. pose proof M_SPA264. pose proof M_SAVED. pose proof M_O88. pose proof W_F. pose proof M_FL. pose proof M_SHF.
    pose proof M_IDX0. pose proof S_STK. pose proof S_DOC8. pose proof M_O8. pose proof M_O16. pose proof M_O40. pose proof M_O56.
    pose proof M_DOC. pose proof M_BUFl. pose proof M_BUF. pose proof M_BUFz. pose proof M_FMIN. pose proof S_IMG.
    pose proof S_T8. pose proof S_B8. pose proof S_I8. pose proof S_TB8. pose proof S_SB8. pose proof S_OC8. pose proof S_IA8. pose proof S_CP8.
    pose proof W_TB. pose proof W_SB. pose proof W_OC. pose proof W_IA. pose proof W_IDX. pose proof W_O24. pose proof W_COPY.
    pose proof W_HC. pose proof W_HB. pose proof M_COPY. pose proof M_COPYl. pose proof M_LG. pose proof M_GOT. pose proof M_SHB.
    pose proof M_SUAR. pose proof M_SUARG. pose proof M_NT. pose proof M_STK. pose proof M_LO.
    eapply (PA2_t0nf.t0n_kn (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
              T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4
              (u sp) THIS DOC BUF ASI TPA SBA AOC AIA F COPY).
    all: eassumption.
  Qed.
  (* [comment removed for export] *)
  Variables (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 x24 x26 t3 t4 t5 t6 : word) (FR4 : bvmap 5 word) (fc4 : bv 32).
  Hypothesis E_rest4 : rest4 = [0x9a5a0; u t0; u t1; u t2; u a1; u a2; u a3; u a4; u a5; u a6; u a7; u x23; u x24; u x26; u t3; u t4; u t5; u t6].
  Hypothesis HFZ4 : frm0 fc4.
  (* [comment removed for export] *)
  Hypothesis Hd : Forall (fun c => 0 <= c < 256) d.
  Hypothesis Hscan : scan d = (true, idx).
  Hypothesis HIDX : rw_cells asegs m ASI [CB (4 * (length idx + 3)) (u32bytes (idx ++ [zlength d; zlength d; 0]))].
  (* [comment removed for export] *)
  Hypothesis R_STK4 : rng RNG4 (16 * SP16 - 8608) 8608.
  Hypothesis R_STKSH4 : rng RNG4 (2 * SP16 + SH - 1076) 1076.
  Hypothesis HRI4 : rng_aimg RNG4.
  Hypothesis HRIS4 : rng_aimg_sh RNG4.
  Hypothesis R_D4 : rng RNG4 (8 * DOC8) 16.
  Hypothesis R_DS4 : rng RNG4 (DOC8 + SH) 2.
  Hypothesis R_F4 : rng RNG4 (2048 * F11) 2048.
  Hypothesis R_FS4 : rng RNG4 (256 * F11 + SH) 256.
  (* [comment removed for export] *)
  Local Notation IDXS := (idx ++ [zlength d; zlength d; 0]).
  Hypothesis SFPCAS_ok : SP.summ_okHSC asegs (gp2 asegs d IDXS) (AHM.hmH AI L RNG4 st4 LB4) (AHM.hmA AI LB4) (AHM.hmC AI LB4) AHM.hmR
                           (AHM.hmF RNG4) (AHM.hmS L RNG4) SFPCAS.
  Hypothesis PFFCAS_ok : SP.summ_okHSC asegs (gp2 asegs d IDXS) (AHM.hmH AI L RNG4 st4 LB4) (AHM.hmA AI LB4) (AHM.hmC AI LB4) AHM.hmR
                           (AHM.hmF RNG4) (AHM.hmS L RNG4) PFFCAS.
  (* [comment removed for export] *)
  Hypothesis HRS4 : rng RNG4 lo (al_top L - lo).
  Hypothesis Hsptop : u sp + 16 < al_top L.

  Local Notation ZL4 := (PA2_t0nf.ZL_t0n''''' (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8)
                            (u s9) (u s10) (u s11) T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG
                            V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4).
  Local Notation R4 := (mkR (Z_to_bv 64 0x9a5a0) (Z_to_bv 64 SPAX) gp tp t0 t1 t2 sp (Z_to_bv 64 SPAX) (Z_to_bv 64 COPY)
                            a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (I8 + SH)) (Z_to_bv 64 (256 * F11 + SH)) (Z_to_bv 64 F) (Z_to_bv 64 LEN)
                            (Z_to_bv 64 TPA) x23 x24 (Z_to_bv 64 ASI) x26 (Z_to_bv 64 (BUF + V)) t3 t4 t5 t6).

  Lemma ez_w4 : forall ZL e (w : word), zok e = true -> zden ZL e mod M64 = u w -> edenot (mkEZ ZL) e = w.
  Proof. intros ZL e w Hz H. rewrite zden_ok by exact Hz. apply bv_eq. rewrite u_Z_to_bv. exact H. Qed.

  (* [comment removed for export] *)
  Lemma a2n_regs4 : regs_ok (mkEZ ZL4) A2N_defs.T0_regs R4.
  Proof.
    rewrite E_rest4. apply regs_ok_mkR.
    change (map (fun k => edenot ?E (sr_get A2N_defs.T0_regs (Z_to_bv 5 k))) rkeys) with (map (edenot E) (tl A2N_defs.T0_regs)).
    cbn [tl A2N_defs.T0_regs map].
    assert (ESPA0 : 16 * SP16 + -384 - 16 * PB = SPAX) by lia.
    repeat (apply (f_equal2 (@cons word)); [apply ez_w4; [reflexivity|];
            cbv [A2N_defs.vRA A2N_defs.vSP A2N_defs.vSP16 A2N_defs.vGP A2N_defs.vTP A2N_defs.vSPA A2N_defs.vPB A2N_defs.vF A2N_defs.vF11
                 A2N_defs.vSHF A2N_defs.vCOPY A2N_defs.vC8 A2N_defs.vI8 A2N_defs.vLEN A2N_defs.vTBASE A2N_defs.vTB8 A2N_defs.vIDX
                 A2N_defs.vBUF A2N_defs.vB8 A2N_defs.vBO A2N_defs.vV A2N_defs.V A2N_defs.mul A2N_defs.add A2N_defs.sub];
            cbn [zden nth PA2_t0nf.ZL_t0n''''' app]; rewrite ?u_Z_to_bv;
            first [ reflexivity | (apply Z.mod_small; apply u_rngE) | (f_equal; lia)
                  | (rewrite Z.mod_small by (pose proof (u_rngE sp); lia); lia) ] |]).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma HIDX4 : rw_cells asegs m4 ASI [CB (4 * (length idx + 3)) (u32bytes IDXS)].
  Proof.
    assert (REG : a2_reg 8608 (u sp) THIS DOC BUF LEN ASI N TPA CAPT SBA CAPS AOC AIA) by exact REG3.
    unfold a2_reg in REG. destruct_a2_reg REG.
    apply (aheap_pres_rw_cells CI _ _ m3 m4 _ _ PRES4);
      [|apply (acr_blk CI (mkABlock (ABFake 5) F 2048 :: LB) SPAX _ _ _ (or_intror Isi)); cbn [ab_addr ab_size cells_size csize];
        rewrite ?Nat.add_0_r, ?Nat2Z.inj_mul; unfold zlength in Hnsi; lia].
    apply (aheap_pres_W_rw_cells CI LB (u sp) _ m m3 _ _ PW3 HIDX);
      [apply (acr_blk CI LB (u sp) _ _ _ Isi); cbn [ab_addr ab_size cells_size csize]; rewrite ?Nat.add_0_r, ?Nat2Z.inj_mul; unfold zlength in Hnsi; lia|].
    intros a Ha; cbn [cells_size csize] in Ha; rewrite ?Nat.add_0_r, ?Nat2Z.inj_mul in Ha. unfold s2_winA; cbn [outside].
    assert (EN' : Z.of_nat (length idx) = N) by (rewrite E_N; reflexivity).
    clear - Ha D3 D19 D20 D21 D22 E_CAPT E_CAPS EN'. unfold DJ in *. repeat split; lia.
  Qed.

  Lemma a2n_gh4 : SG.gholds (gp2 asegs d IDXS) (mkEZ ZL4) m4 (ST.t_ghost A2N_defs.T0).
  Proof.
    assert (REG : a2_reg 8608 (u sp) THIS DOC BUF LEN ASI N TPA CAPT SBA CAPS AOC AIA) by exact REG3.
    unfold a2_reg in REG. destruct_a2_reg REG.
    assert (MB : bytes_at asegs m4 BUF (s1buf d)) by exact M_BUF.
    pose proof (scan_S1OUT d idx Hscan) as S1.
    assert (BB : 0x665000 <= BUF /\ BUF + LEN + 64 <= 0x7FFFFF800000) by (clear - H_BUF; atop_facts; lia).
    assert (IB : 0x665000 <= ASI /\ ASI + 4 * N + 16 <= 0x7FFFFF800000).
    { pose proof (hb_band AI _ _ _ _ _ _ _ _ AH3 (or_intror Isi)) as (_ & Hj0 & Hj1 & _ & _). clear - Hj0 Hj1 Hnsi E_N. atop_facts. lia. }
    unfold SG.gholds. cbn [ST.t_ghost A2N_defs.T0]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      cbv [A2N_defs.vBUF A2N_defs.vB8 A2N_defs.vBO A2N_defs.vLEN A2N_defs.vIDX A2N_defs.vI8 A2N_defs.vN A2N_defs.V A2N_defs.mul A2N_defs.add];
      cbn [ST.g_id ST.g_args map gp2]; rewrite !u_zden by reflexivity; cbn [zden nth PA2_t0nf.ZL_t0n''''' app].
    - rewrite <- E_B8. rewrite !Z.mod_small by (clear - BB H_LEN; lia).
      split; [exact E_LEN|]. split; [clear - BB; lia|]. split; [exact Hd|]. rewrite bufbytes_eqA.
      apply mbytes_of_bytes_at_heapA; [exact MB | clear - BB; lia | rewrite s1buf_lenA, <- E_LEN; clear - BB; lia].
    - rewrite <- E_I8. rewrite !Z.mod_small by (clear - IB H_N; lia).
      assert (ZL3' : zlength IDXS = N + 3) by (rewrite E_N, zlength_app; reflexivity).
      rewrite ZL3'. replace (N + 3 - 3) with N by ring. rewrite E_N.
      split; [reflexivity|]. split; [exact S1|]. split; [rewrite <- E_N; clear - IB; lia|]. rewrite u32bytes_eqA.
      destruct (cb_bytesA m4 _ _ _ HIDX4) as [BI LI].
      apply mbytes_of_bytes_at_heapA; [exact BI | clear - IB; lia | rewrite LI, Nat2Z.inj_mul; unfold zlength in IB, E_N; clear - IB E_N; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma a2n_wins4 : fp_le (SX.fp_of (SP.p_A A2N_defs.A2N) (mkEZ ZL4)) RNG4 /\ SX.aw_genuine (mkEZ ZL4) (SP.p_A A2N_defs.A2N).
  Proof.
    xall.
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Ith4) as [RT RTS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Isi4) as [RI RIS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Icp4) as [RC RCS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Itp4) as [RP RPS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Isb4) as [RS RSS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Ioc4) as [RO ROS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Iia4) as [RA RAS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Icy4) as [RY RYS].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 Icy4) as (_ & _ & _ & _ & _ & _ & _ & (RLC & RHC & RC1 & RC2 & RC3 & RC4 & RAC & _)).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 Icp4) as (_ & _ & _ & _ & _ & _ & _ & (RLB & RHB & RB1 & RB2 & RB3 & RB4 & RAB & _)).
    rewrite shad_div, shlen_d8 in RAC, RAB. unfold ASHOFF in RAC, RAB.
    assert (R_T : rng RNG4 (8 * T8) 96) by (eapply rng_sub'; [exact RT | clear - E_T8 Hnim; lia]).
    assert (R_TS : rng RNG4 (T8 + SH) 12) by (eapply rng_sub'; [exact RTS | clear - E_T8 Hnim; Z.div_mod_to_equations; lia]).
    assert (R_B : rng RNG4 (8 * B8 + BO) (LEN + 64)) by (eapply rng_sub'; [exact RC | clear - E_B8 Hb1 Hb2 E_LEN; lia]).
    assert (R_BS : rng RNG4 (B8 + SH) BG) by (eapply rng_sub'; [exact RCS | clear - E_B8 Hb1 Hb2 E_LEN D_BG D_BO Ac; Z.div_mod_to_equations; lia]).
    assert (R_I : rng RNG4 (8 * I8) (4 * N + 12)) by (eapply rng_sub'; [exact RI | clear - E_I8 Hnsi E_N; lia]).
    assert (R_IS : rng RNG4 (I8 + SH) IG) by (eapply rng_sub'; [exact RIS | clear - E_I8 Hnsi E_N D_IG; Z.div_mod_to_equations; lia]).
    assert (R_TB : rng RNG4 (8 * TB8) (8 * CAPT)) by (eapply rng_sub'; [exact RP | clear - E_TB8 E_CAPT; lia]).
    assert (R_TBS : rng RNG4 (TB8 + SH) CAPT) by (eapply rng_sub'; [exact RPS | clear - E_TB8 E_CAPT; Z.div_mod_to_equations; lia]).
    assert (R_SB : rng RNG4 (8 * SB8) CAPS) by (eapply rng_sub'; [exact RS | clear - E_SB8 E_CAPS; lia]).
    assert (R_SBS : rng RNG4 (SB8 + SH) SG) by (eapply rng_sub'; [exact RSS | clear - E_SB8 E_CAPS D_SG; Z.div_mod_to_equations; lia]).
    assert (R_OC : rng RNG4 (8 * OC8) 8192) by (eapply rng_sub'; [exact RO | clear - E_OC8 Hnoc; lia]).
    assert (R_OCS : rng RNG4 (OC8 + SH) 1024) by (eapply rng_sub'; [exact ROS | clear - E_OC8 Hnoc; Z.div_mod_to_equations; lia]).
    assert (R_IA : rng RNG4 (8 * IA8) 1024) by (eapply rng_sub'; [exact RA | clear - E_IA8 Hnia; lia]).
    assert (R_IAS : rng RNG4 (IA8 + SH) 128) by (eapply rng_sub'; [exact RAS | clear - E_IA8 Hnia; Z.div_mod_to_equations; lia]).
    assert (R_CP : rng RNG4 (8 * CP8) (LEN - V + 64)) by (eapply rng_sub'; [exact RY | clear - E_CP8 E_LEN E_V; lia]).
    assert (R_CPS : rng RNG4 (CP8 + SH) CGF) by (eapply rng_sub'; [exact RYS | clear - E_CP8 E_LEN E_V D_CGF; Z.div_mod_to_equations; lia]).
    assert (R_HC : rng RNG4 (8 * HC + SH) (8 * (HCE - HC)))
      by (eapply rng_sub'; [exact RAC | clear - RC1 RC2 RC3 RC4 D_HC D_HCE E_LEN E_V H_V; Z.div_mod_to_equations; lia]).
    assert (R_HB : rng RNG4 (8 * HBG + SH) (8 * (HBGE - HBG)))
      by (eapply rng_sub'; [exact RAB | clear - RB1 RB2 RB3 RB4 D_HBG D_HBGE E_LEN Hb1 Hb2 HI0 E_V H_V; Z.div_mod_to_equations; lia]).
    assert (W_SP : 8608 <= 16 * SP16 <= 2 ^ 47) by (clear - H_SP E_SP; lia).
    assert (W_SZ : 0 <= LEN < 2^40 /\ 0 <= N < 2^40 /\ 1 <= CAPT < 2^40 /\ 1 <= CAPS < 2^40 /\ 1 <= BG < 2^40 /\ 1 <= IG < 2^40
                   /\ 1 <= SG < 2^40 /\ 0 <= BO < 8) by (clear - H_LEN H_N H_CAPT H_CAPS D_BG D_IG D_SG D_BO; lia).
    assert (W_B8 : 0 <= T8 /\ 0 <= DOC8 /\ 0 <= B8 /\ 0 <= I8 /\ 0 <= TB8 /\ 0 <= SB8 /\ 0 <= OC8 /\ 0 <= IA8 /\ 0 <= F11)
      by (clear - E_T8 E_DOC8 E_B8 E_I8 E_TB8 E_SB8 E_OC8 E_IA8 E_F11 H_THIS H_DOC H_BUF H_IDX H_TB H_SB H_OC H_IA H_F D_BO; lia).
    assert (W_NZ : 0 <= V <= LEN /\ 0 <= CP8 < 2^44 /\ 0 <= CGF < 2^40 /\ 0 <= HC < 2^44 /\ 0 <= HCE - HC < 2^40
                   /\ 0 <= HBG < 2^44 /\ 0 <= HBGE - HBG < 2^40)
      by (clear - H_V H_LEN E_CP8 H_COPY D_CGF D_HC D_HCE D_HBG D_HBGE H_BUF D_BO; atop_facts; lia).
    exact (a2n_wins RNG4 (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
             T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4
             W_SP W_SZ W_B8 W_NZ R_STK4 HRI4 R_STKSH4 HRIS4 R_T R_TS R_D4 R_DS4 R_B R_BS R_I R_IS R_TB R_TBS R_SB R_SBS R_OC R_OCS R_IA R_IAS
             R_F4 R_FS4 R_CP R_CPS R_HC R_HB).
  Qed.
  (* [comment removed for export] *)
  Lemma a2d_wins4 : fp_le (SX.fp_of (SP.p_A A2D_defs.A2D) (mkEZ ZL4)) RNG4 /\ SX.aw_genuine (mkEZ ZL4) (SP.p_A A2D_defs.A2D).
  Proof using All.
    xall.
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Ith4) as [RT RTS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Isi4) as [RI RIS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Icp4) as [RC RCS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Itp4) as [RP RPS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Isb4) as [RS RSS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Ioc4) as [RO ROS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Iia4) as [RA RAS].
    pose proof (blk_rngs8 AI _ _ _ _ _ _ _ _ AH4 Icy4) as [RY RYS].
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 Icy4) as (_ & _ & _ & _ & _ & _ & _ & (RLC & RHC & RC1 & RC2 & RC3 & RC4 & RAC & _)).
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 Icp4) as (_ & _ & _ & _ & _ & _ & _ & (RLB & RHB & RB1 & RB2 & RB3 & RB4 & RAB & _)).
    rewrite shad_div, shlen_d8 in RAC, RAB. unfold ASHOFF in RAC, RAB.
    assert (R_T : rng RNG4 (8 * T8) 96) by (eapply rng_sub'; [exact RT | clear - E_T8 Hnim; lia]).
    assert (R_TS : rng RNG4 (T8 + SH) 12) by (eapply rng_sub'; [exact RTS | clear - E_T8 Hnim; Z.div_mod_to_equations; lia]).
    assert (R_B : rng RNG4 (8 * B8 + BO) (LEN + 64)) by (eapply rng_sub'; [exact RC | clear - E_B8 Hb1 Hb2 E_LEN; lia]).
    assert (R_BS : rng RNG4 (B8 + SH) BG) by (eapply rng_sub'; [exact RCS | clear - E_B8 Hb1 Hb2 E_LEN D_BG D_BO Ac; Z.div_mod_to_equations; lia]).
    assert (R_I : rng RNG4 (8 * I8) (4 * N + 12)) by (eapply rng_sub'; [exact RI | clear - E_I8 Hnsi E_N; lia]).
    assert (R_IS : rng RNG4 (I8 + SH) IG) by (eapply rng_sub'; [exact RIS | clear - E_I8 Hnsi E_N D_IG; Z.div_mod_to_equations; lia]).
    assert (R_TB : rng RNG4 (8 * TB8) (8 * CAPT)) by (eapply rng_sub'; [exact RP | clear - E_TB8 E_CAPT; lia]).
    assert (R_TBS : rng RNG4 (TB8 + SH) CAPT) by (eapply rng_sub'; [exact RPS | clear - E_TB8 E_CAPT; Z.div_mod_to_equations; lia]).
    assert (R_SB : rng RNG4 (8 * SB8) CAPS) by (eapply rng_sub'; [exact RS | clear - E_SB8 E_CAPS; lia]).
    assert (R_SBS : rng RNG4 (SB8 + SH) SG) by (eapply rng_sub'; [exact RSS | clear - E_SB8 E_CAPS D_SG; Z.div_mod_to_equations; lia]).
    assert (R_OC : rng RNG4 (8 * OC8) 8192) by (eapply rng_sub'; [exact RO | clear - E_OC8 Hnoc; lia]).
    assert (R_OCS : rng RNG4 (OC8 + SH) 1024) by (eapply rng_sub'; [exact ROS | clear - E_OC8 Hnoc; Z.div_mod_to_equations; lia]).
    assert (R_IA : rng RNG4 (8 * IA8) 1024) by (eapply rng_sub'; [exact RA | clear - E_IA8 Hnia; lia]).
    assert (R_IAS : rng RNG4 (IA8 + SH) 128) by (eapply rng_sub'; [exact RAS | clear - E_IA8 Hnia; Z.div_mod_to_equations; lia]).
    assert (R_CP : rng RNG4 (8 * CP8) (LEN - V + 64)) by (eapply rng_sub'; [exact RY | clear - E_CP8 E_LEN E_V; lia]).
    assert (R_CPS : rng RNG4 (CP8 + SH) CGF) by (eapply rng_sub'; [exact RYS | clear - E_CP8 E_LEN E_V D_CGF; Z.div_mod_to_equations; lia]).
    assert (R_HC : rng RNG4 (8 * HC + SH) (8 * (HCE - HC)))
      by (eapply rng_sub'; [exact RAC | clear - RC1 RC2 RC3 RC4 D_HC D_HCE E_LEN E_V H_V; Z.div_mod_to_equations; lia]).
    assert (R_HB : rng RNG4 (8 * HBG + SH) (8 * (HBGE - HBG)))
      by (eapply rng_sub'; [exact RAB | clear - RB1 RB2 RB3 RB4 D_HBG D_HBGE E_LEN Hb1 Hb2 HI0 E_V H_V; Z.div_mod_to_equations; lia]).
    assert (W_SP : 8608 <= 16 * SP16 <= 2 ^ 47) by (clear - H_SP E_SP; lia).
    assert (W_SZ : 0 <= LEN < 2^40 /\ 0 <= N < 2^40 /\ 1 <= CAPT < 2^40 /\ 1 <= CAPS < 2^40 /\ 1 <= BG < 2^40 /\ 1 <= IG < 2^40
                   /\ 1 <= SG < 2^40 /\ 0 <= BO < 8) by (clear - H_LEN H_N H_CAPT H_CAPS D_BG D_IG D_SG D_BO; lia).
    assert (W_B8 : 0 <= T8 /\ 0 <= DOC8 /\ 0 <= B8 /\ 0 <= I8 /\ 0 <= TB8 /\ 0 <= SB8 /\ 0 <= OC8 /\ 0 <= IA8 /\ 0 <= F11)
      by (clear - E_T8 E_DOC8 E_B8 E_I8 E_TB8 E_SB8 E_OC8 E_IA8 E_F11 H_THIS H_DOC H_BUF H_IDX H_TB H_SB H_OC H_IA H_F D_BO; lia).
    assert (W_NZ : 0 <= V <= LEN /\ 0 <= CP8 < 2^44 /\ 0 <= CGF < 2^40 /\ 0 <= HC < 2^44 /\ 0 <= HCE - HC < 2^40
                   /\ 0 <= HBG < 2^44 /\ 0 <= HBGE - HBG < 2^40)
      by (clear - H_V H_LEN E_CP8 H_COPY D_CGF D_HC D_HCE D_HBG D_HBGE H_BUF D_BO; atop_facts; lia).
    exact (a2d_wins RNG4 (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
             T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4
             W_SP W_SZ W_B8 W_NZ R_STK4 HRI4 R_STKSH4 HRIS4 R_T R_TS R_D4 R_DS4 R_B R_BS R_I R_IS R_TB R_TBS R_SB R_SBS R_OC R_OCS R_IA R_IAS
             R_F4 R_FS4 R_CP R_CPS R_HC R_HB).
  Qed.
  (* [comment removed for export] *)
  Definition CndN (E : env) : Prop := SP.gagree 47 (mkEZ ZL4) E /\ eb E = eb (mkEZ ZL4).
  Lemma a2n_evt4 :
    ExecF.evtF asegs RNG4 (SLib.xpostH asegs (gp2 asegs d IDXS) (AHM.hmH AI L RNG4 st4 LB4) (AHM.hmA AI LB4) A2N_defs.A2N (mkEZ ZL4) m4 (seg_rom asegs))
      (MS R4 FR4 (Z_to_bv 64 0x9a5a0) fc4 None m4 (seg_rom asegs)).
  Proof using All.
    xall.
    destruct a2n_wins4 as [FPL AWG].
    eapply ExecF.evtF_weaken; cycle 1.
    change (Z_to_bv 64 0x9a5a0) with (Z_to_bv 64 (ST.t_pc A2N_defs.T0)).
    assert (E_SP' : 0x7fff00000000 <= 16 * SP16 <= 2^47) by (clear - H_SP E_SP; lia).
    assert (E_n : zlength d - i0 + 64 = LEN - V + 64) by (clear - E_LEN E_V; lia).
    assert (H_PB : 0 <= PB <= 1) by (clear - E_PB HSPA; lia).
    assert (H_SZ : 0 <= CAPT /\ 0 <= CAPS /\ 0 <= BG /\ 0 <= IG /\ 0 <= SG /\ 0 <= CGF) by (clear - H_CAPT H_CAPS D_BG D_IG D_SG D_CGF H_V H_LEN H_N D_BO; lia).
    assert (H_LO : ATOP + 4096 <= lo /\ lo <= 16 * SP16 - 8608) by (clear - Hlo1 Hlo2 E_SP; lia).
    assert (B_ALL : 0x665000 <= THIS /\ THIS + 96 <= ATOP /\ 0x665000 <= DOC /\ DOC + 16 <= ATOP /\ 0x665000 <= BUF /\ BUF + LEN + 64 <= ATOP
                  /\ 0x665000 <= ASI /\ ASI + 4 * N + 12 <= ATOP /\ 0x665000 <= TPA /\ TPA + 8 * CAPT <= ATOP /\ 0x665000 <= SBA /\ SBA + CAPS <= ATOP
                  /\ 0x665000 <= AOC /\ AOC + 8192 <= ATOP /\ 0x665000 <= AIA /\ AIA + 1024 <= ATOP /\ 0x665000 <= F /\ F + 2048 <= ATOP
                  /\ 0x665000 <= COPY /\ COPY + (zlength d - i0 + 64) <= ATOP).
    { pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 Ith4) as (_ & A1 & A2 & _). pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 Isi4) as (_ & B1 & B2 & _).
      pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 Icp4) as (_ & C1 & C2 & _). pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 Itp4) as (_ & P1 & P2 & _).
      pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 Isb4) as (_ & S1 & S2 & _). pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 Ioc4) as (_ & O1 & O2 & _).
      pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 Iia4) as (_ & I1 & I2 & _). pose proof (hb_band AI _ _ _ _ _ _ _ _ AH4 Icy4) as (_ & Y1 & Y2 & _).
      pose proof (fake_band FA FN Hfk3 ltac:(pose proof (AI_block_bounds AI _ _ _ _ _ _ AH3 (or_intror Ifk)) as BB; cbn [ab_size] in BB; lia)) as (_ & K1 & K2).
      pose proof (fake_band F 2048 HFb ltac:(lia)) as (_ & G1 & G2).
      clear - A1 A2 B1 B2 C1 C2 P1 P2 S1 S2 O1 O2 I1 I2 Y1 Y2 K1 K2 G1 G2 Hnim Hnsi Hb1 Hb2 Hnoc Hnia Hfk1 Hfk2 E_LEN E_N E_CAPT E_CAPS.
      repeat split; lia. }
    assert (Hnsi2 : 4 * N + 12 <= nsi) by (clear - Hnsi E_N; lia).
    assert (Hb2' : BUF + LEN + 64 <= ACP + ncp) by (clear - Hb2 E_LEN; lia).
    assert (Hac : ACP mod 8 = 0) by (clear - Ac; Z.div_mod_to_equations; lia).
    apply (a2n_run AI L RNG4 st4 LB4 d IDXS SFPCAS_ok PFFCAS_ok CndN).
    - intros E E2 Hgg2 Hbb2 [HgX HbX]. split; [exact (SP.gagree_trans _ _ _ _ HgX Hgg2) | congruence].
    - intros E [HgX HbX].
      eapply (cnd_W AI LB lo F p COPY (zlength d - i0 + 64) pim ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF nim ntp nsb noc nia
                (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4);
        eassumption.
    - intros E [HgX HbX].
      eapply (cnd_CR AI LB lo F p COPY (zlength d - i0 + 64) pim psi pcp ptp psb poc pia THIS ASI ACP TPA SBA AOC AIA DOC BUF
                nim nsi ncp ntp nsb noc nia cls FA FN
                (u ra) SP16 (u gp) (u tp) (u s0) (u s1) (u s2) (u s3) (u s4) (u s5) (u s6) (u s7) (u s8) (u s9) (u s10) (u s11)
                T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest4);
        eassumption.
    - intros E M0 _ HM. exact (cnd_IK AI LB F p COPY (zlength d - i0 + 64) ACP L RNG4 st4 E M0 HM).
    - intros E [HgX HbX]. unfold SP.hs_ok.
      assert (DS : SP.dstk (SP.p_PS A2N_defs.A2N) (SP.p_W A2N_defs.A2N) = Some (A2N_defs.vSPA, 8192)) by reflexivity.
      rewrite DS.
      rewrite <- (SP.edenot_gagree 47 (mkEZ ZL4) E A2N_defs.vSPA HgX (eq_sym HbX) eq_refl), u_zden by reflexivity.
      cbv [A2N_defs.vSPA A2N_defs.vSP A2N_defs.vSP16 A2N_defs.vPB A2N_defs.V A2N_defs.mul A2N_defs.add A2N_defs.sub].
      cbn [zden nth PA2_t0nf.ZL_t0n''''' app].
      assert (ESPA0 : 16 * SP16 + -384 - 16 * PB = SPAX) by lia.
      rewrite ESPA0, Z.mod_small by (pose proof HSPAr; lia).
      unfold AHM.hmS. pose proof HSPAr. split; [lia|]. split; [lia|].
      eapply rng_sub; [exact HRS4 | lia | lia].
    - cbn; tauto.
    - reflexivity.
    - exact AWG.
    - split; [apply SP.gagree_refl | reflexivity].
    - split; [exact AH4 | exact MI4].
    - apply rfull_mkR.
    - exact a2n_regs4.
    - exact a2n_kn4.
    - exact a2n_gh4.
    - exact MI4.
    - exact HFZ4.
    - intros b j [Hj|Hj]; [exact (FPL b j Hj) | exact Hj].
  Qed.

End XN0.
End CANSEC.
