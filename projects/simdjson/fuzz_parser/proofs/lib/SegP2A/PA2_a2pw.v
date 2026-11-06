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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface A2Lib PA2_exit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require PA2_t0c.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require A2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.
Local Notation SH := 2147450880%Z (only parsing).

Section CANSEC. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma a2_frame : forall (AI : AMallocIface) (LB6 : list ablock) (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (rest : list Z) (m2 m3 : amem),
  8608 <= 16 * SP16 <= 2 ^ 47 -> 0 <= 8 * T8 /\ 8 * T8 + 96 < M64 -> 0 <= 8 * TB8 /\ 8 * TB8 + 8 * CAPT < M64 -> 0 <= CAPT ->
  0 <= 8 * SB8 /\ 8 * SB8 + CAPS < M64 -> 0 <= CAPS -> 0 <= 8 * OC8 /\ 8 * OC8 + 8192 < M64 -> 0 <= 8 * IA8 /\ 8 * IA8 + 1024 < M64 ->
  0 <= 2048 * F11 /\ 2048 * F11 + 2048 < M64 -> 0 <= 256 * F11 + SH /\ 256 * F11 + SH + 256 < M64 -> 0 <= PB <= 1 ->
  SP.frame_ok (AHM.hmA AI LB6)
    (mkEZ (PA2_t0c.ZL_t0'' zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8
                F11 PB FLAG BO BG IG SG rest))
    (SP.p_W A2_defs.A2) (SP.p_PS A2_defs.A2) m2 m3 ->
  forall a, 0 <= a < M64 ->
    outside [(16 * SP16 - 8608, 16 * SP16); (8 * T8 + 24, 8 * T8 + 28); (8 * T8 + 88, 8 * T8 + 96); (8 * TB8, 8 * TB8 + 8 * CAPT);
             (8 * SB8, 8 * SB8 + CAPS); (8 * OC8, 8 * OC8 + 8192); (8 * IA8, 8 * IA8 + 1024); (2048 * F11, 2048 * F11 + 2048);
             (256 * F11 + SH, 256 * F11 + SH + 256)] a ->
    (16 * SP16 - 384 - 16 * PB <= a < 2^47 \/ AHM.hmA AI LB6 a) ->
    m3 (wa a) = m2 (wa a).
Proof.
  intros until m3. intros H1 H2 H3 H3' H4 H4' H5 H6 H7 H8 HPB FO a Ha HO HP.
  cbn [SP.frame_ok SP.p_PS A2_defs.A2 SP.PGH] in FO. apply FO; rewrite wa_unsigned by lia.
  - unfold SP.outside_wins. cbn [SP.p_W A2_defs.A2 SP.PGH]. cbn [outside] in HO.
    destruct HO as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & _).
    cbv [A2_defs.vSP A2_defs.vSP16 A2_defs.vTHIS A2_defs.vT8 A2_defs.vTBASE A2_defs.vTB8 A2_defs.vCAPT A2_defs.vSBASE A2_defs.vSB8
         A2_defs.vCAPS A2_defs.vOCB A2_defs.vOC8 A2_defs.vIAB A2_defs.vIA8 A2_defs.vF A2_defs.vF11 A2_defs.vSHF A2_defs.V A2_defs.mul
         A2_defs.add A2_defs.vSPA A2_defs.vPB A2_defs.sub].
    repeat constructor; cbn [SP.win_den]; rewrite ?u_zden by reflexivity; cbn [zden nth PA2_t0c.ZL_t0'' app];
      rewrite ?(Z.mod_small _ M64) by lia; lia.
  - destruct HP as [HP|HP]; [left | right; right; exact HP].
    cbv [A2_defs.vSPA A2_defs.vSP A2_defs.vSP16 A2_defs.vPB A2_defs.V A2_defs.mul A2_defs.add A2_defs.sub].
    rewrite u_zden by reflexivity. cbn [zden nth PA2_t0c.ZL_t0'' app]. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma a2_pres_WH : forall (AI : AMallocIface) L RNG st LB (m2 m3 : amem) (sp SPAX F THIS TPA ntp SBA nsb AOC AIA : Z),
  AHEAP AI L RNG st (mkABlock (ABFake 5) F 2048 :: LB) m2 ->
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) ->
  ablk F (F + 2048) -> F + 2048 <= ATOP -> ATOP + 8608 <= sp -> sp <= 2^47 -> sp - 415 <= SPAX <= sp ->
  (forall a, aclient_addr (aci AI) LB SPAX a -> a < shad F \/ shad F + 256 <= a) ->
  (forall a, 0 <= a < M64 ->
     outside [(sp - 8608, sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (TPA, TPA + ntp); (SBA, SBA + nsb);
              (AOC, AOC + 8192); (AIA, AIA + 1024); (F, F + 2048); (shad F, shad F + 256)] a ->
     (SPAX <= a < 2^47 \/ AHM.hmA AI (mkABlock (ABFake 5) F 2048 :: LB) a) -> m3 (wa a) = m2 (wa a)) ->
  wmono asegs m2 m3 ->
  aheap_pres_W (aci AI) LB sp (s2_winA THIS TPA ntp SBA nsb AOC AIA) m2 m3.
Proof.
  intros AI L RNG st LB m2 m3 sp SPAX F THIS TPA ntp SBA nsb AOC AIA AH2 NO5 HFb HFt Hsp1 Hsp2 HSPX HSHF FR WM a Ha Hc Hout.
  atop_facts.
  assert (HSX : a < shad F \/ shad F + 256 <= a).
  { apply HSHF. destruct Hc as [X|[X|[X|X]]]; [left; lia | right; left; exact X | right; right; left; exact X | right; right; right; exact X]. }
  assert (SF : KLS <= shad F < 0x10007fff8000) by (apply shad_band1; unfold ablk, AIMG_HI, KLS, KEND in *; lia).
  assert (HO3 : ~ (sp - 8608 <= a < sp) /\ ~ (F <= a < F + 2048)).
  { destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - lia.
    - pose proof (AI_aci_img AI iv Hiv). unfold ablk, AIMG_HI in *. lia.
    - pose proof (AI_block_bounds AI _ _ _ _ _ b AH2 (or_intror Hb)) as BB.
      assert (NE : b <> mkABlock (ABFake 5) F 2048) by (intros ->; exact (NO5 F 2048 Hb)).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b (mkABlock (ABFake 5) F 2048) AH2 (or_intror Hb) (or_introl eq_refl) NE) as DJ.
      cbn [ab_addr ab_size] in DJ. lia.
    - assert (A47 : 0 <= a' < KEND).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; unfold KEND;
          [lia | pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia |].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH2 (or_intror Hb')) as BB. cbn [ab_addr ab_size] in BB. unfold AIMG_HI in BB. lia. }
      pose proof (shad_band1 a' (proj1 A47) (proj2 A47)) as SB. unfold ablk, KLS in *. lia. }
  assert (HO : outside [(sp - 8608, sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (TPA, TPA + ntp); (SBA, SBA + nsb);
                        (AOC, AOC + 8192); (AIA, AIA + 1024); (F, F + 2048); (shad F, shad F + 256)] a).
  { unfold s2_winA in Hout. cbn [outside] in Hout |- *. destruct Hout as (O1 & O2 & O3 & O4 & O5 & O6 & _).
    destruct HO3 as (O7 & O8). repeat split; try assumption. lia. }
  assert (HP : SPAX <= a < 2^47 \/ AHM.hmA AI (mkABlock (ABFake 5) F 2048 :: LB) a).
  { destruct Hc as [X|[X|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - left. lia.
    - right. left. right. left. exact X.
    - right. left. right. right. left. exists b. split; [right; exact Hb | exact Hr].
    - right. left. right. right. right. exists a'. split; [|reflexivity].
      destruct Ha' as [X|[X|(c & FA' & fn & Hb' & X)]]; [left; exact X | right; left; exact X | right; right].
      exists c, FA', fn. split; [right; exact Hb' | exact X]. }
  split.
  - exact (FR a Ha HO HP).
  - intros Hw. apply WM. exact Hw.
Qed.
End CANSEC.
