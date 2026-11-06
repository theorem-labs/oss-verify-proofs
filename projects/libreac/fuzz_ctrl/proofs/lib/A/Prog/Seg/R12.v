(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2004 of its 2120 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F30.v, with its module paths, module names and addresses changed; 91 of its 111 lines of code are new or changed and 2100 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R13.v, with its module paths, module names, addresses and numbers changed; 88 of its 144 lines of code are new or changed and 55 lines of the source are left out. *)
(* Segment R12 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): S_R12, Inv_A81734_at -> Inv_A81708_at.
   0x81708 is the return of `jal reac_ctrl_identity_fragment` (0x81704) on the b = 6 arm: `li a1,1 ;
   beq a0,a1,81714` (0x81708 / 0x8170c) takes the branch because the fragment closed the record and returned 1
   (X81708's a0 = 1; B3Rtm.a_rtm_close makes the class FgClose, whose fg_ret is 1), so 0x81710 `j 82bf4` (the
   abort pair) is NOT reached. The run joins the shared ingest tail 0x81714 .. 0x81730 (RNIng.rn_ing_cont): the
   three argument cells at fr + 2448 / 2464 / 2496 are the fragment's CLOSE outputs (address fg_addr = 0x1000,
   payload pointer fr + 2256 + 19 inside the fragment record, length fg_T - 13 = 17, B3Rtm.a_rtm_close_vals).
   The ingest result is 1 (B3Rtm.a_rtm_ing6) and the record it writes is RID (S b) (B3Rtm.a_RS_56 with
   fg_rf = 1); the fragment record is already RFG (S b) (the CLOSE wrote it), as X81708 states. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts AsanRTInv PContract MemNorm
  AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcIdentModel RcFrag RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_rt_b2 Tac_rt2_b2 Tac_slot RNIng.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import RcPro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Rtm.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module ACy := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.

(* 0x81708 li a1,1 ; 0x8170c beq a0,a1,81714 (a0 = 1, taken; only a1 changes). *)
Lemma r12_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 1 ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81714) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81708) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ->.
  step. step. if_true. apply evt_done. eexists. reflexivity.
Qed.

Section R12.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACy.AsanAllocAPI ACy.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis INGC : reac_identity_ingest_contract.

Lemma seg_R12 : forall b : nat,
  Hat B APIf ra (Inv_A81734_at (fx := fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A81708_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros b Hexit g c HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & (BODY & HX)).
  destruct BODY as (Hgn & Hb6 & HHB & Hr23 & HOUR & HOUTA & HCUR & Hs112 & Hs128 & HPRO & Hs104 & Hs96 & Hs64 &
    Hs144 & Hs208 & HRWid & HRWjk & Hs280 & Hs240 & HRWjy & HRWj32 & Hs152 & Hr21 & HAD38).
  destruct HX as (Hbeq & Ha0 & HRFb & HRXS & HBa & HBp & HBn).
  subst c. subst b.
  change (Z.of_nat 6) with 6 in *.
  pose proof HRFb as (HRB & Hnz & Hr24 & HF).
  pose proof HRB as (_ & _ & _ & _ & HIDB & HFGB).
  (* the model facts of turn 6 *)
  pose proof (B3Rtm.a_rtm_close (g_in g) Hnz) as Hcls.
  destruct (B3Rtm.a_rtm_close_vals (g_in g) Hnz) as (Hfa & Hpll).
  pose proof (B3Rtm.a_rtm_ing6 (g_in g) Hnz) as HING1.
  destruct (B3Rtm.a_RS_56 (g_in g) 6%nat ltac:(right; reflexivity) ltac:(change (Z.of_nat 6) with 6; exact Hnz))
    as (EID & EFG).
  change (Z.of_nat 6) with 6 in EID, EFG.
  assert (Hrf : fg_rf (rt_n (g_in g) 6) (RFG (g_in g) 6) (rt_g (g_in g) 6) = 1).
  { unfold fg_rf. rewrite Hcls. reflexivity. }
  (* the payload: 17 bytes at fr + 2256 + 19 inside the closed fragment record *)
  pose proof (rn_RS_len (g_in g) 7%nat) as (_ & LFG7).
  assert (EPB : f_pl (rt_n (g_in g) 6) (RFG (g_in g) 6) (rt_g (g_in g) 6) =
                RcFrag.bsl (RFG (g_in g) 7%nat) 19 17).
  { unfold f_pl. rewrite <- EFG. rewrite Hpll. reflexivity. }
  assert (HPB : bytes_at rsegs mem (fr + 2256 + 19)
                  (f_pl (rt_n (g_in g) 6) (RFG (g_in g) 6) (rt_g (g_in g) 6))).
  { rewrite EPB. apply rn_bsl_at; [exact HFGB | lia | lia | rewrite LFG7; lia]. }
  assert (Hpblen : length (f_pl (rt_n (g_in g) 6) (RFG (g_in g) 6) (rt_g (g_in g) 6)) = Z.to_nat 17).
  { rewrite EPB. apply rn_bsl_len; [lia | lia | rewrite LFG7; lia]. }
  (* the payload is inside the fragment record, which RXS makes addressable *)
  pose proof HRXS as (H48 & H56 & H88 & H80 & H72 & H16 & H8 & H192 & H216 & HA72).
  assert (HAp : addressable mem (fr + 2256 + 19) 17).
  { apply (addressable_sub mem (fr + 2256) 72 19 17 HA72); lia. }
  (* run the two instructions to 0x81714 *)
  pose proof (proj1 FF) as SEGS.
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x81708) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81714 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26)
    (Post B APIf ra g)).
  { pose proof HFRA as HF2.
    destruct HF2 as (A & sp & s5v & HRT & HAH & Hro & Hsn & Hhalt & _). exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold a0v, rg in Ha0.
    eapply evt_mono.
    - apply r12_evt. exact Ha0.
    - intros ms' (a1' & ->). do 3 eexists. repeat (split; [reflexivity|]). reflexivity. }
  intros R pc' mem' regs'' md1
    (Hpc & Hmem & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26) Hreg Hmat.
  subst pc' mem'.
  assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
  assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
  assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
  assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (rnb g 6%nat)) regs'' mem md1)
    by exact (sl_fra_move B APIf ra g fr (hb1 phi (rnb g 6%nat)) regs regs'' mem md md1 HFRA
                E2 E3 E4 E8 E9 E19 E26 Hmat).
  assert (HENT'' : ENT (fx := fx) APIf g (hb1 phi (rnb g 6%nat)) mem md1)
    by (eapply ent_mat; [exact HENT | exact Hmat]).
  assert (KSP : forall off w, spill regs mem off w -> spill regs'' mem off w).
  { intros off w (A0 & HA0 & HQ). exists A0. split; [unfold rg in *; rewrite E9; exact HA0 | exact HQ]. }
  assert (HCUR'' : CUR g 7 regs'').
  { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
    split; [exact Hc0|]. split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25]. }
  assert (Hr23'' : rg regs'' 23 (Z.of_nat 6%nat)) by (unfold rg in *; rewrite E23; exact Hr23).
  assert (Hr24'' : rg regs'' 24 phi) by (unfold rg in *; rewrite E24; exact Hr24).
  assert (Hr21'' : rg regs'' 21 (fr + 2176)) by (unfold rg in *; rewrite E21; exact Hr21).
  assert (HRXS'' : RXS g fr regs'' mem).
  { unfold RXS. split; [exact (KSP 48 _ H48)|]. split; [exact (KSP 56 _ H56)|].
    split; [exact (KSP 88 _ H88)|]. split; [exact (KSP 80 _ H80)|]. split; [exact (KSP 72 _ H72)|].
    split; [exact (KSP 8 _ H16)|]. split; [exact (KSP 0 _ H8)|]. split; [exact (KSP 200 _ H192)|].
    split; [exact (KSP 216 _ H216) | exact HA72]. }
  rewrite <- SEGS.
  refine (rn_ing_cont B APIf ra empty FF INGC 6%nat Hexit g regs'' mem md1 fr phi
            (RcFrag.fg_addr (RFG (g_in g) 6) (rt_g (g_in g) 6)) (fr + 2256 + 19) 17
            (f_pl (rt_n (g_in g) 6) (RFG (g_in g) 6) (rt_g (g_in g) 6))
            HFRA'' HENT'' Hgn Hb6 HHB Hr23'' HOUR HOUTA HCUR''
            (KSP 112 _ Hs112) (KSP 128 _ Hs128) (rc_pro_regs g fr regs regs'' mem E9 HPRO) (KSP 104 _ Hs104)
            (KSP 96 _ Hs96)
            (KSP 64 _ Hs64) (KSP 144 _ Hs144) (KSP 192 _ Hs208) HRWid HRWjk
            (KSP 280 _ Hs280) (KSP 240 _ Hs240) HRWjy HRWj32 (KSP 152 _ Hs152) Hr21''
            HAD38 Hr24'' HIDB HFGB HRXS'' HBa _ _ _ _ Hpblen HPB HAp _ _ _ Hnz).
  - exact HBp.
  - unfold f_pll in Hpll. rewrite <- Hpll. exact HBn.
  - rewrite Hfa. lia.
  - lia.
  - right. split; lia.
  - exact HING1.
  - rewrite EID. unfold fg_id. rewrite Hrf. reflexivity.
Qed.

End R12.
