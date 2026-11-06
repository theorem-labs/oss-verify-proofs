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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells ABase AMalloc_iface AU_iface AU_kit AU_client_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AHM.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface A2Lib PA2_exit PA2_winN.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require A2N_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma a2n_frame : forall (AI : AMallocIface) (LB4 : list ablock) (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD : Z)
    (rest : list Z) (m4 m5 : amem),
  8608 <= 16 * SP16 <= 2 ^ 47 -> 0 <= 8 * T8 /\ 8 * T8 + 96 < M64 -> 0 <= 8 * TB8 /\ 8 * TB8 + 8 * CAPT < M64 -> 0 <= CAPT ->
  0 <= 8 * SB8 /\ 8 * SB8 + CAPS < M64 -> 0 <= CAPS -> 0 <= 8 * OC8 /\ 8 * OC8 + 8192 < M64 -> 0 <= 8 * IA8 /\ 8 * IA8 + 1024 < M64 ->
  0 <= 2048 * F11 /\ 2048 * F11 + 2048 < M64 -> 0 <= 256 * F11 + SH /\ 256 * F11 + SH + 256 < M64 ->
  0 <= PB <= 1 -> 0 <= 8 * CP8 /\ 8 * CP8 + (LEN - V + 64) < M64 -> 0 <= LEN - V + 64 ->
  SP.frame_ok (AHM.hmA AI LB4)
    (mkEZ (ZLwn zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8
                F11 PB FLAG BO BG IG SG V CP8 CGF ZP DG SD SRG HC HCE HBG HBGE MD rest))
    (SP.p_W A2N_defs.A2N) (SP.p_PS A2N_defs.A2N) m4 m5 ->
  forall a, 0 <= a < M64 ->
    outside [(16 * SP16 - 8608, 16 * SP16); (8 * T8 + 24, 8 * T8 + 28); (8 * T8 + 88, 8 * T8 + 96); (8 * TB8, 8 * TB8 + 8 * CAPT);
             (8 * SB8, 8 * SB8 + CAPS); (8 * OC8, 8 * OC8 + 8192); (8 * IA8, 8 * IA8 + 1024); (2048 * F11, 2048 * F11 + 2048);
             (256 * F11 + SH, 256 * F11 + SH + 256); (8 * CP8, 8 * CP8 + (LEN - V + 64))] a ->
    (16 * SP16 - 384 - 16 * PB <= a < 2^47 \/ AHM.hmA AI LB4 a) ->
    m5 (wa a) = m4 (wa a).
Proof.
  intros until m5. intros H1 H2 H3 H3' H4 H4' H5 H6 H7 H8 HPB H9 H9' FO a Ha HO HP.
  cbn [SP.frame_ok SP.p_PS A2N_defs.A2N SP.PGH] in FO. apply FO; rewrite wa_unsigned by lia.
  - unfold SP.outside_wins. cbn [SP.p_W A2N_defs.A2N SP.PGH]. cbn [outside] in HO.
    destruct HO as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & _).
    cbv [A2N_defs.vSP A2N_defs.vSP16 A2N_defs.vTHIS A2N_defs.vT8 A2N_defs.vTBASE A2N_defs.vTB8 A2N_defs.vCAPT A2N_defs.vSBASE A2N_defs.vSB8
         A2N_defs.vCAPS A2N_defs.vOCB A2N_defs.vOC8 A2N_defs.vIAB A2N_defs.vIA8 A2N_defs.vF A2N_defs.vF11 A2N_defs.vSHF A2N_defs.V A2N_defs.mul
         A2N_defs.add A2N_defs.vSPA A2N_defs.vPB A2N_defs.sub A2N_defs.vCOPY A2N_defs.vC8 A2N_defs.vLEN A2N_defs.vV].
    repeat constructor; cbn [SP.win_den]; rewrite ?u_zden by reflexivity; cbn [zden nth ZLwn app];
      rewrite ?(Z.mod_small _ M64) by lia; lia.
  - destruct HP as [HP|HP]; [left | right; right; exact HP].
    cbv [A2N_defs.vSPA A2N_defs.vSP A2N_defs.vSP16 A2N_defs.vPB A2N_defs.V A2N_defs.mul A2N_defs.add A2N_defs.sub].
    rewrite u_zden by reflexivity. cbn [zden nth ZLwn app]. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma a2n_pres_W : forall (AI : AMallocIface) L RNG st LB (m4 m5 : amem) (sp SPAX F COPY n THIS TPA ntp SBA nsb AOC AIA : Z) p,
  AHEAP AI L RNG st (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB) m4 ->
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) ->
  ablk F (F + 2048) -> F + 2048 <= ATOP -> ATOP + 8608 <= sp -> sp <= 2^47 -> sp - 415 <= SPAX <= sp ->
  (forall a, aclient_addr (aci AI) LB SPAX a -> a < shad F \/ shad F + 256 <= a) ->
  (forall a, 0 <= a < M64 ->
     outside [(sp - 8608, sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (TPA, TPA + ntp); (SBA, SBA + nsb);
              (AOC, AOC + 8192); (AIA, AIA + 1024); (F, F + 2048); (shad F, shad F + 256); (COPY, COPY + n)] a ->
     (SPAX <= a < 2^47 \/ AHM.hmA AI (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB) a) -> m5 (wa a) = m4 (wa a)) ->
  wmono asegs m4 m5 ->
  aheap_pres_W (aci AI) LB sp (s2_winA THIS TPA ntp SBA nsb AOC AIA) m4 m5.
Proof.
  intros AI L RNG st LB m4 m5 sp SPAX F COPY n THIS TPA ntp SBA nsb AOC AIA p AH4 NO5 HFb HFt Hsp1 Hsp2 HSPX HSHF FR WM a Ha Hc Hout.
  atop_facts.
  assert (HSX : a < shad F \/ shad F + 256 <= a).
  { apply HSHF. destruct Hc as [X|[X|[X|X]]]; [left; lia | right; left; exact X | right; right; left; exact X | right; right; right; exact X]. }
  assert (SF : KLS <= shad F < 0x10007fff8000) by (apply shad_band1; unfold ablk, AIMG_HI, KLS, KEND in *; lia).
  pose proof (AI_block_bounds AI _ _ _ _ _ (HB p COPY n) AH4 (or_introl eq_refl)) as BC. cbn [ab_addr ab_size] in BC.
  destruct (AI_block AI _ _ _ _ _ _ _ _ AH4 (or_introl eq_refl)) as (_ & (ABC & _) & _).
  pose proof (AI_blocks_nodup AI _ _ _ _ _ AH4) as NDB. apply NoDup_cons_iff in NDB as [NC NDB]. apply NoDup_cons_iff in NDB as [NF _].
  assert (HO3 : ~ (sp - 8608 <= a < sp) /\ ~ (F <= a < F + 2048) /\ ~ (COPY <= a < COPY + n)).
  { destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - lia.
    - pose proof (AI_aci_img AI iv Hiv). unfold ablk, AIMG_HI in *. lia.
    - pose proof (AI_block_bounds AI _ _ _ _ _ b AH4 (or_intror (or_intror Hb))) as BB.
      assert (NE : b <> mkABlock (ABFake 5) F 2048) by (intros ->; exact (NO5 F 2048 Hb)).
      assert (NE2 : b <> HB p COPY n) by (intros ->; apply NC; right; exact Hb).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b (mkABlock (ABFake 5) F 2048) AH4 (or_intror (or_intror Hb)) (or_intror (or_introl eq_refl)) NE) as DJ.
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b (HB p COPY n) AH4 (or_intror (or_intror Hb)) (or_introl eq_refl) NE2) as DJ2.
      cbn [ab_addr ab_size] in DJ, DJ2. lia.
    - assert (A47 : 0 <= a' < KEND).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; unfold KEND;
          [lia | pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia |].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH4 (or_intror (or_intror Hb'))) as BB. cbn [ab_addr ab_size] in BB. unfold AIMG_HI in BB. lia. }
      pose proof (shad_band1 a' (proj1 A47) (proj2 A47)) as SB. unfold ablk, KLS in *. lia. }
  assert (HO : outside [(sp - 8608, sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (TPA, TPA + ntp); (SBA, SBA + nsb);
                        (AOC, AOC + 8192); (AIA, AIA + 1024); (F, F + 2048); (shad F, shad F + 256); (COPY, COPY + n)] a).
  { unfold s2_winA in Hout. cbn [outside] in Hout |- *. destruct Hout as (O1 & O2 & O3 & O4 & O5 & O6 & _).
    destruct HO3 as (O7 & O8 & O9). repeat split; try assumption. lia. }
  assert (HP : SPAX <= a < 2^47 \/ AHM.hmA AI (HB p COPY n :: mkABlock (ABFake 5) F 2048 :: LB) a).
  { destruct Hc as [X|[X|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - left. lia.
    - right. left. right. left. exact X.
    - right. left. right. right. left. exists b. split; [right; right; exact Hb | exact Hr].
    - right. left. right. right. right. exists a'. split; [|reflexivity].
      destruct Ha' as [X|[X|(c & FA' & fn & Hb' & X)]]; [left; exact X | right; left; exact X | right; right].
      exists c, FA', fn. split; [right; right; exact Hb' | exact X]. }
  split.
  - exact (FR a Ha HO HP).
  - intros Hw. apply WM. exact Hw.
Qed.
End CANSEC.
