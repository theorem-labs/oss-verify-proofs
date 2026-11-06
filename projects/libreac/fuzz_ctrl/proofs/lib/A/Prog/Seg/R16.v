(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names, addresses and numbers changed; 118 of its 166 lines of code are new or changed and 1454 lines of the source are left out. *)
(* Segment R16 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): Inv_A817ec -> Inv_A81924.
   0x817ec is the head of the second 32-byte sum loop of the round trip, entered at index i (the cut carries
   i < 32, a0 = a2 = Phi_r + 18 + i, a3 = 32 - i, a1 = rsum g b i = the sum of the first i of the 32 bytes
   Phi_r[18 ..]).  Each turn loads the shadow byte of a0 and goes on (the 32 bytes at Phi_r + 18 are marked usable,
   so the error path at 0x81820 is not taken), adds the byte at a2 to a1 and counts a3 down; at a3 = 0 the loop
   leaves by 0x81814 `j 81910`.  At 0x81910 `zext.b a0,a1` is 0 because the block sum of X(b) closes for b <= 2
   (B3Rtm.a_rtm_sum with B3Loop.b3_sum_low / b3_blocksum), so `beqz a0,8191c` is taken and 0x81918 (the `j` to
   before_abort) is NOT reached.  From 0x8191c the shared free-call continuation R15.r_free_cont runs
   `mv a0,s8 ; jal wrapper_free` and re-establishes Inv_A81924_at.
   The loop reads memory only, so the exit facts are the entry ones: FRA moves with sl_fra_move, ENT with ent_mat,
   and the exit cut's RB at turn (S b) is the entry RFb's RB at turn b, since RID / RFG (S b) = RID / RFG b for
   b <= 2 (B3Rtm.a_RS_012). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import B3Loop.
Import ListNotations.
Open Scope Z_scope.

(* The run of R16 from the loop head at index i to 0x8191c, with a0 = 0: the loop (b3_loop2 at i) and the low-byte
   test (b3_tail2).  Only a0, a1, a2, a3, a4 and a5 change; memory is unchanged. *)
Lemma r16_run :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (xs : list byte) (i : nat),
    a0 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a1 = Z_to_bv 64 (psum xs i) ->
    a2 = Z_to_bv 64 (phi + 18 + Z.of_nat i) -> a3 = Z_to_bv 64 (32 - Z.of_nat i) ->
    s10 = Z_to_bv 64 ASAN_K -> (i < 32)%nat ->
    length xs = 32%nat -> bytes_at rsegs m (phi + 18) xs -> addressable m (phi + 18) 32 ->
    blocksum xs = 0 ->
    evt rsegs
      (fun ms' => exists a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (psum xs 32))
                       (Z_to_bv 64 (phi + 18 + 32)) (Z_to_bv 64 0) a4' a5' a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x8191c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x817ec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi xs i E0 E1 E2 E3 E10 Hi Hlen HB AD HS.
  pose proof (psum_range xs 32) as PR. change (Z.of_nat 32) with 32 in PR.
  eapply evt_cut.
  { apply (b3_loop2 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m (phi + 18) xs i);
      [ rewrite E0; f_equal; lia | exact E1 | rewrite E2; f_equal; lia | exact E3 | exact E10 | exact Hi
      | exact Hlen | exact HB | exact AD ]. }
  intros ms' (a4' & a5' & ->).
  eapply evt_cut.
  { apply (b3_tail2 ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (phi + 18 + 32)) (Z_to_bv 64 (psum xs 32))
             (Z_to_bv 64 (phi + 18 + 32)) (Z_to_bv 64 0) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m (psum xs 32) eq_refl ltac:(lia) (b3_sum_low _ HS)). }
  intros ms' ->. apply evt_done. cbv beta. exists a4', a5'. reflexivity.
Qed.

(* ===== seg_R16 ===== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_rt_b2 Tac_rt2_b2 R15.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Rtm.
(* Qualified: R15 requires BzBridge / KindBGlue, which load the image-independent lib/Reusable/YK11; after that a
   bare `Import YK11` is that one, whose getr / mkst / FPState are NOT the ones the cuts are built over. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF16 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

Section R16W.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC16.AsanAllocAPI AC16.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Notation API := (APIf rc).

(* The loop accumulator of the cut is the partial sum of the 32 frame bytes: a rewrite over variables, never a
   conversion at the concrete round-trip values (the kernel would compute rt_F through Z.modulo). *)
Lemma r16_rsum : forall g (b i : nat), rsum g b i = psum (skipn 18 (rt_g (g_in g) (Z.of_nat b))) i.
Proof. reflexivity. Qed.

Lemma seg_R16 : forall b : nat,
  Hat B APIf ra (Inv_A81924_at (fx := fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A817ec_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hexit g c HInv.
  destruct HInv as (phi & i & regs & mem & md & fr & Ec & HFRA & HENT &
    ((Hgn & Hb6 & HHB & Hr23 & Hour & Hout & Hcur & Hile & Hr10 & Hr12 & Hr13) &
     Hb12 & Hilt & Hr11 & HRFb & Hs128 & HPRO & Hs104 & Hs96 & Hs64 & Hr21 & Hs112 & Hs144 & Hs208 & HRWid &
     HRWjk & Hs280 & Hs240 & HRWjy & HRWsc & Hs152 & HAid & HRXS)).
  subst c.
  pose proof (proj1 FF) as SEGS.
  pose proof HRFb as (HRB & Hnz & Hr24 & HF).
  assert (Hble2 : (b <= 2)%nat) by (destruct Hb12 as [E|E]; rewrite E; lia).
  (* the 32 bytes of the block that the loop reads, and their block sum *)
  destruct (a_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & HLF).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in Hnb, HLF.
  pose proof HHB as (Hphinz & HAphi0).
  assert (Hsz : AC16.a_size (rnb g b) = rnb g b) by (unfold AC16.a_size; lia).
  rewrite Hsz in HAphi0.
  assert (HA18 : addressable mem (phi + 18) 32)
    by (apply (addressable_sub mem phi (rnb g b) 18 32 HAphi0); lia).
  assert (HLb : (50 <= length (rt_F (g_in g) (Z.of_nat b)))%nat) by (rewrite HLF; lia).
  destruct (b3_blk_at mem phi _ HF HLb) as (HBxs & Hlenxs).
  rewrite <- (b3_rt_g (g_in g) (Z.of_nat b)) in HBxs, Hlenxs.
  assert (HSum : blocksum (skipn 18 (rt_g (g_in g) (Z.of_nat b))) = 0) by (apply B3Rtm.a_rtm_sum; lia).
  rewrite r16_rsum in Hr11.
  unfold rg in Hr10, Hr11, Hr12, Hr13.
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hrest).
  unfold rg in Hr26.
  rewrite SEGS.
  (* 0x817ec .. 0x8191c: the loop and the low-byte test; memory unchanged, s-registers kept *)
  apply (sl_run_lib regs (Z_to_bv 64 0x817ec) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x8191c /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26)
    (Post B APIf ra g)).
  { exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    - apply (r16_run (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
               (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
               (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
               (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
               (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30)
               (getr regs 31) fp_regs fp_csr mem phi (skipn 18 (rt_g (g_in g) (Z.of_nat b))) i);
        [ exact Hr10 | exact Hr11 | exact Hr12 | exact Hr13 | exact Hr26 | exact Hilt
        | exact Hlenxs | exact HBxs | exact HA18 | exact HSum ].
    - intros ms' (a4' & a5' & ->). do 3 eexists. split; [reflexivity|].
      repeat (split; [reflexivity|]). reflexivity. }
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
  (* FRA and ENT at 0x8191c (the loop writes no memory; the model moved by mat_le) *)
  assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem md1)
    by exact (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs regs'' mem md md1 HFRA E2 E3 E4 E8 E9 E19 E26
                Hmat).
  assert (HENT'' : ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem md1)
    by (eapply ent_mat; [exact HENT | exact Hmat]).
  (* RB of turn (S b): on b <= 2 the round-trip state does not move *)
  destruct (B3Rtm.a_RS_012 (g_in g) b Hble2) as (EID & EFG).
  assert (HRB'' : RB g fr b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs'' mem).
  { rewrite EID, EFG. destruct HRB as (Rb6 & Rcur & Rour & Rr23 & Ridb & Rfgb).
    split; [exact Rb6|].
    split.
    { destruct Rcur as (Rc0 & Rc22 & Rc25). unfold CUR, rg in *.
      split; [exact Rc0|]. split; [rewrite E22; exact Rc22 | rewrite E25; exact Rc25]. }
    split; [exact Rour|].
    split; [unfold rg in *; rewrite E23; exact Rr23|].
    split; [exact Ridb | exact Rfgb]. }
  assert (Hr24'' : rg regs'' 24 phi) by (unfold rg in *; rewrite E24; exact Hr24).
  (* the facts R21 reads at 0x81924 and OUTA, carried across the loop: it writes no memory and no s-register *)
  assert (KSP'' : forall off w, spill regs mem off w -> spill regs'' mem off w).
  { intros off w (A0 & HA0 & HQ). exists A0. split; [unfold rg in *; rewrite E9; exact HA0 | exact HQ]. }
  assert (Hr21'' : rg regs'' 21 (fr + 2176)) by (unfold rg in *; rewrite E21; exact Hr21).
  assert (Hs144'' : spill regs'' mem 144 (fr + 2688)) by exact (KSP'' 144 _ Hs144).
  assert (Hs208'' : spill regs'' mem 192 (fr + 2768)) by exact (KSP'' 192 _ Hs208).
  assert (Hs152'' : spill regs'' mem 152 (Sfr fr + 68)) by exact (KSP'' 152 _ Hs152).
  rewrite <- SEGS.
  exact (r_free_cont B APIf ra empty FF b Hexit g regs'' mem md1 fr phi HFRA'' HENT'' Hgn HRB'' Hr24'' Hout
           (KSP'' 128 _ Hs128)
           (r15_pro_keep g fr regs regs'' mem mem (fun off v _ H => KSP'' off v H) (fun H => H) (fun _ H => H)
              (fun _ H => H) HPRO)
           (KSP'' 104 _ Hs104) (KSP'' 96 _ Hs96) (KSP'' 64 _ Hs64)
           Hr21'' (KSP'' 112 _ Hs112) Hs144'' Hs208'' HRWid HRWjk (KSP'' 280 _ Hs280) (KSP'' 240 _ Hs240)
           HRWjy HRWsc Hs152'' HAid
           (r15_rxs_keep g fr regs regs'' mem mem (fun off v _ H => KSP'' off v H) (fun H => H) HRXS)).
Qed.

End R16W.
