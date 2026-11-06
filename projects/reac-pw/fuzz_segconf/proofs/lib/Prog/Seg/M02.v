(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 265 of its 294 lines of code are new or changed and 545 lines of the source are left out. *)
(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): K13ae0 -> K13cac,
   [0x13ae0, 0x13cac), as SegEnd.seg_M02_stmt at CPseg.
   The slot side:
   - from the K13ae0 cut (CUTST at its own FP state, hb = hb_cm c m, P_K13ae0) the memory the inner walk needs
     (M02D.M02_mem) on the CJ-normalized memory WmcEnv.M1 mem (MemNorm.task_mem holds there: snprintf asks it),
     the six checks (MainBPure.mb_checks) and the registers; the inner walk (M02D.M02_inner, M02_I.v) runs from
     0x13ae0 to calloc's entry with ra = 0x13c9c, a0 = cap + 1, a1 = 18; WmcEnv.seg_lift_cj moves its post to the
     normalized memory, and Tac_slot.sl_mid_fp re-establishes FR at the run's own FP state;
   - calloc(cap + 1, 18) by Tac_b1.b1_calloc_call from hb_cm (calloc_contract_big at that FP state: seg_M02_stmt
     gives it at every FP state), then the run 0x13c9c .. 0x13ca8 (`mv s3,a0; li a1,20; mv a0,s4; jal calloc`) by
     sl_mid_fp with no write, calloc(cap + 1, 20) from (tab, 18 (cap + 1)) :: hb_cm;
   - at 0x13cac the cut K13cac: hb_end, both tables zero (calloc), tab kept across the second calloc (an hb block),
     c's and m's bytes and main's frame cells kept (outside M02_W, then kept by each calloc), blk_noimg of the two
     tables (Tac_b1.b1_blk_noimg_segs), s3 = tab, s4 = cap + 1, s6 = cap, a0 = mt.
   Part of the proof of LLVMFuzzerTestOneInput: this file is segment M02 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require KindBGlue CallocBigC.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_cuts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c SegEnd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import SegWalkMainA WmcEnv MainBPure M02D.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require MainB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require M02_A M02_B M02_C M02_D M02_I.
Import ListNotations.
Open Scope Z_scope.

(* M02_W lies inside the window seg_W and sl_mid_fp allow: [S - 65536, S - 104). *)
Lemma m02_W_in : forall S x, ~ outside (M02_W S) x -> S - 65536 <= x < S - 104.
Proof.
  intros S x O. unfold M02_W, M02_FRAME in O. cbn [outside] in O.
  assert (H1 : S - 65536 <= x < S - 208 \/ S - 208 + 0x40 <= x < S - 208 + 0x52).
  { destruct (Z_le_dec (S - 65536) x), (Z_lt_dec x (S - 208)), (Z_le_dec (S - 208 + 0x40) x),
      (Z_lt_dec x (S - 208 + 0x52)); try (left; lia); try (right; lia);
      exfalso; apply O; (split; [lia | split; [lia | exact I]]). }
  lia.
Qed.

(* calloc's zero bytes as a byte list. *)
Lemma m02_zeros : forall m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> mbyte rsegs m (a + i) = Some (Z_to_bv 8 0)) ->
  bytes_at rsegs m a (repeat ZERO (Z.to_nat n)).
Proof.
  intros m a n H0 Hn H1 H. split; [exact H0|]. rewrite repeat_length, Z2Nat.id by lia. split; [exact H1|].
  intros i Hi. rewrite nth_error_repeat by exact Hi.
  exact (H (Z.of_nat i) ltac:(lia)).
Qed.

(* The frame cells main keeps: their bytes stay through a calloc (it keeps [fsp, S)). *)
Lemma m02_cell_keep : forall (m m' : word -> option byte) S a bs, bytes_at rsegs m a bs ->
  S - 208 <= a -> a + Z.of_nat (length bs) <= S ->
  (forall x, S - 208 <= x < S -> mbyte rsegs m' x = mbyte rsegs m x) -> bytes_at rsegs m' a bs.
Proof. intros m m' S a bs H H1 H2 HK. apply (b1_ba_mbyte m m' a bs H). intros i Hi. apply HK. lia. Qed.

(* A block's bytes stay through a calloc (it keeps every hb block). *)
Lemma m02_blk_keep : forall (m m' : word -> option byte) hb a k bs, bytes_at rsegs m a bs -> In (a, k) hb ->
  Z.of_nat (length bs) <= k ->
  (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof. intros m m' hb a k bs H Hin Hk HK. apply (b1_ba_mbyte m m' a bs H). intros i Hi. apply (HK a k); [exact Hin | lia]. Qed.

(* A run that writes nothing: bytes from mem to the next memory. *)
Lemma m02_keep0 : forall (mem m' : word -> option byte) a bs, ro_agree rsegs mem ->
  mem_rel rsegs m' (normalize rsegs mem) -> bytes_at rsegs mem a bs -> bytes_at rsegs m' a bs.
Proof.
  intros mem m' a bs Hro Hrel H. exact (b1_keep [] mem (normalize rsegs mem) m' a bs Hro (munch_refl _ _) Hrel I H).
Qed.

Section M02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis INNER : M02_inner.
Hypothesis CAL : forall fx' : FPState, CallocBigC.calloc_contract_big (fx:=fx') B (APIf rc) CallocBigC.CALLOC_PC.

Lemma seg_M02_of_inner : S_M02 B APIf ra empty CPseg.
Proof using fx rc B APIf LS SH SK ra empty FF INNER CAL.
  unfold S_M02. intros HK g c (bc & bm & (fx1 & L & A & regs & mem & md & -> & Hfrm & HFR & HP & HPre)).
  unfold CPseg in HPre. cbn [cp_K13ae0] in HPre.
  destruct HPre as ((H8 & H26 & C8 & C10 & C30 & Hc16 & Hm16 & Hcn & Hmn) & H24 & C18 & H20 & Hrc & Hmc).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof HGV as (_ & _ & _ & HS16 & HSKc & HS47c & _).
  pose proof alloc_ceiling_value as HAC.
  assert (HAC1 : 0x7fff7f800000 <= YM05.alloc_ceiling) by exact (proj1 (proj1 HAC)).
  pose proof (@YM05.alloc_ceiling_lt rc) as HACl.
  assert (TS : TASK_SIZE = 2 ^ 47) by reflexivity.
  pose proof (mb_checks (g_in g)) as (K1 & K2 & K3 & K4 & K5 & K6 & _).
  pose proof (mb_cap (g_in g)) as Hcap.
  set (cap := seg_cap (g_in g)) in *.
  set (rc0 := seg_rc (run (seg_pay (g_in g)))) in *.
  set (mc0 := seg_mc (run (seg_pay (g_in g)))) in *.
  set (ret0 := seg_ret (run (seg_pay (g_in g)))) in *.
  unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME in *.
  (* the two live blocks *)
  assert (Im : In (bm, M_SIZE) (hb_cm bc bm)) by (left; reflexivity).
  assert (Ic : In (bc, C_SIZE) (hb_cm bc bm)) by (right; left; reflexivity).
  destruct (b1_hb B APIf ra empty FF g _ bm M_SIZE L A regs mem md HFR HP Im) as (_ & Hm4 & Hmc').
  destruct (b1_hb B APIf ra empty FF g _ bc C_SIZE L A regs mem md HFR HP Ic) as (_ & Hc4 & Hcc).
  unfold C_SIZE, M_SIZE in *.
  (* the memory the inner walk runs on *)
  assert (HMEM : M02_mem (g_S g) bc bm cap rc0 mc0 (M1 mem)).
  { unfold M02_mem.
    split; [apply m1_mem_inv|]. split; [apply m1_task_mem|].
    split.
    { destruct (ax_statics (b8_ax B APIf ra empty FF) L A mem md HM) as (Hgg & (gv & Hgv & Hgw) & _).
      rewrite (ff_got_guard B APIf ra empty FF), (ff_guard B APIf ra empty FF) in Hgg.
      rewrite (ff_guard B APIf ra empty FF) in Hgw. rewrite SEGS in Hgg, Hgw.
      unfold ssp_ok. change (sa_got_guard SA) with 0x21818. change (sa_guard SA) with 0x52e80.
      split.
      - apply bytes_m1; [exact HMI | rewrite length_le8, TS; lia |].
        apply (KindBGlue.word_mem_le8 rsegs); [exact Hgg | lia | lia | lia].
      - exists (Z_to_bv 64 gv). apply bytes_m1; [exact HMI | rewrite length_le8, TS; lia |].
        apply (KindBGlue.word_mem_le8 rsegs); [exact Hgw | lia | lia | lia]. }
    split; [exact HS16|]. split; [lia|]. split; [exact HS47c|].
    split; [apply stk_m1; [exact ST | rewrite TS; lia]|].
    split; [intros a Ha; apply (b8_seg_rom_hi B APIf ra empty FF); lia|].
    split; [apply bytes_m1; [exact HMI | rewrite length_le8, TS; unfold M02_FRAME; lia | exact C18]|].
    split; [lia|]. split; [exact Hc16|]. split; [unfold SEG_C_SIZE; lia|].
    split; [lia|]. split; [exact Hm16|]. split; [unfold SEG_M_SIZE; lia|].
    split.
    { destruct Hrc as (bs & Hb & He). exists bs. split; [|exact He].
      apply bytes_m1; [exact HMI | | exact Hb]. destruct He as (Hl & _). rewrite Hl, TS. unfold SEG_C_SIZE. lia. }
    { destruct Hmc as (bs & Hb & He). exists bs. split; [|exact He].
      apply bytes_m1; [exact HMI | | exact Hb]. destruct He as (Hl & _). rewrite Hl, TS. unfold SEG_M_SIZE. lia. } }
  (* what the run leaves in the registers at calloc's entry *)
  set (Pst := fun (regs' : bvmap 5 word) (_ : word -> option byte) =>
    YK11.getr regs' 1 = Z_to_bv 64 M02_RA /\ YK11.getr regs' 10 = Z_to_bv 64 (cap + 1) /\
    YK11.getr regs' 11 = Z_to_bv 64 18 /\ YK11.getr regs' 20 = Z_to_bv 64 (cap + 1) /\
    YK11.getr regs' 22 = Z_to_bv 64 cap /\ YK11.getr regs' 8 = Z_to_bv 64 bm /\
    YK11.getr regs' 26 = Z_to_bv 64 (bm + MC_N)).
  (* the run 0x13ae0 .. calloc's entry *)
  apply (sl_mid_fp (fx := fx1) B APIf ra empty FF g (hb_cm bc bm) L A regs mem md (Z_to_bv 64 0x13ae0)
           (fun ms => exists R' F' fc' m', ms = MS R' F' (Z_to_bv 64 M02_CALLOC) fc' None m' (seg_rom rsegs) /\
              frm_zero fc' /\ munch (M02_W (g_S g)) (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
              YK11.getr R' 2 = YK11.getr regs 2 /\ YK11.getr R' 3 = YK11.getr regs 3 /\
              YK11.getr R' 4 = YK11.getr regs 4 /\
              (forall regs' m, Regs6ss.xregs_eqv R' regs' -> mem_rel rsegs m m' -> Pst regs' m))
           (Post B APIf ra g) HFR HP).
  - apply (seg_lift_cj mem (Regs6ss.mkR_of regs) (@fp_regs fx1) (Z_to_bv 64 0x13ae0) (@fp_csr fx1) M02_CALLOC
             (M02_W (g_S g)) (M02_W (g_S g)) (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) Pst Pst).
    + intros x Hx. exact Hx.
    + intros R' m1' m' m regs' HPs _ _ Hx. unfold Pst in *. rewrite !(sl_getr_eqv _ _ _ Hx). exact HPs.
    + rewrite sl_mkR_of. eapply evt_mono.
      * apply (INNER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (M1 mem) (g_S g) bc bm cap
                 rc0 mc0 ret0).
        -- rewrite Hsp. reflexivity.
        -- exact H8.
        -- exact H24.
        -- exact H26.
        -- exact H20.
        -- exact Hfrm.
        -- unfold M02_model. refine (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 K6))))).
        -- exact HMEM.
      * intros ms (t0' & t1' & t2' & s1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s5' & s7' & s9' & s11' &
                   t3' & t4' & t5' & t6' & F' & fc' & m' & -> & Hz & (MU & WM & _)).
        do 4 eexists. split; [reflexivity|]. split; [exact Hz|]. split; [exact MU|]. split; [exact WM|].
        split; [rewrite Hsp; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        unfold Pst. repeat split; reflexivity.
  - intros ms (R' & F' & fc' & m' & -> & Hz & MU & WM & E2 & E3 & E4 & _).
    exists R', F', (Z_to_bv 64 M02_CALLOC), fc', m'. split; [reflexivity|]. split; [exact Hz|].
    split; [exists (M02_W (g_S g)); split; [exact MU|]; split; [exact WM|];
            intros x _ O; exact (m02_W_in (g_S g) x O)|].
    split; [exact E2|]. split; [exact E3 | exact E4].
  - intros R F' pc' fc' m0' regs' m' HQ Hx Hrel Hz HFR'.
    destruct HQ as (R1 & F1 & fc1 & m1 & E & Hz1 & MU & _ & _ & _ & _ & HPs).
    injection E as ER EF Epc Efc Em. subst R F' pc' fc' m0'.
    destruct (HPs regs' m' Hx Hrel) as (P1 & P10 & P11 & P20 & P22 & P8 & P26).
    (* calloc(cap + 1, 18) *)
    apply (b1_calloc_call (fx := mkFP F1 fc1) B APIf ra empty FF g (hb_cm bc bm) L A regs' m' md regs' (cap + 1) 18
             (Post B APIf ra g) (CAL (mkFP F1 fc1)) HFR' HP);
      [cbn; lia | unfold hb_bytes, hb_cm, M_SIZE, C_SIZE; cbn; lia | reflexivity | reflexivity | reflexivity
      | rewrite P1; vm_compute; reflexivity | exact P10 | exact P11 | lia | lia
      | unfold CallocBigC.CALLOC_BIG_CAP; lia |].
    intros L2 A2 regs2 mem2 md2 tab HF2 HP2 RP2 H10t Htab0 Htab16 HKS2 HKH2 HZ2.
    rewrite P1.
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HF2) as (_ & _ & _ & _ & HMI2).
    assert (R20 : YK11.getr regs2 20 = Z_to_bv 64 (cap + 1)).
    { rewrite <- P20. exact (RP2 20 ltac:(unfold callee_saved; lia)). }
    assert (R22 : YK11.getr regs2 22 = Z_to_bv 64 cap).
    { rewrite <- P22. exact (RP2 22 ltac:(unfold callee_saved; lia)). }
    assert (R8 : YK11.getr regs2 8 = Z_to_bv 64 bm).
    { rewrite <- P8. exact (RP2 8 ltac:(unfold callee_saved; lia)). }
    assert (R26 : YK11.getr regs2 26 = Z_to_bv 64 (bm + MC_N)).
    { rewrite <- P26. exact (RP2 26 ltac:(unfold callee_saved; lia)). }
    (* the run 0x13c9c .. calloc's entry: s3 = tab, a1 = 20, a0 = s4 *)
    apply (sl_mid_fp (fx := mkFP F1 fc1) B APIf ra empty FF g ((tab, (cap + 1) * 18) :: hb_cm bc bm)
             L2 A2 regs2 mem2 md2 (Z_to_bv 64 M02_RA)
             (fun ms => exists R2, ms = MS R2 F1 (Z_to_bv 64 M02_CALLOC) fc1 None (normalize rsegs mem2) (seg_rom rsegs) /\
                YK11.getr R2 1 = Z_to_bv 64 0x13cac /\ YK11.getr R2 10 = Z_to_bv 64 (cap + 1) /\
                YK11.getr R2 11 = Z_to_bv 64 20 /\ YK11.getr R2 19 = Z_to_bv 64 tab /\
                YK11.getr R2 2 = YK11.getr regs2 2 /\ YK11.getr R2 3 = YK11.getr regs2 3 /\
                YK11.getr R2 4 = YK11.getr regs2 4 /\ YK11.getr R2 8 = Z_to_bv 64 bm /\
                YK11.getr R2 20 = Z_to_bv 64 (cap + 1) /\ YK11.getr R2 22 = Z_to_bv 64 cap /\
                YK11.getr R2 26 = Z_to_bv 64 (bm + MC_N))
             (Post B APIf ra g) HF2 HP2).
    + rewrite sl_mkR_of. unfold M02_RA.
      do 4 step.
      apply evt_done. eexists. split; [reflexivity|].
      rewrite <- R20, <- H10t, <- R8, <- R22, <- R26.
      repeat split; reflexivity.
    + intros ms (R2 & -> & _ & _ & _ & _ & G2 & G3 & G4 & _).
      exists R2, F1, (Z_to_bv 64 M02_CALLOC), fc1, (normalize rsegs mem2). split; [reflexivity|].
      split; [exact Hz1|].
      split; [exists []; split; [apply munch_refl|]; split; [apply wmono_refl|];
              intros x _ O; exfalso; apply O; exact I|].
      split; [exact G2|]. split; [exact G3 | exact G4].
    + intros R F'' pc'' fc'' m0'' regs3 mem3 HQ2 Hx2 Hrel2 Hz2 HF3.
      destruct HQ2 as (R2 & E2 & G1 & G10 & G11 & G19 & _ & _ & _ & G8 & G20 & G22 & G26).
      injection E2 as ER EF Epc Efc Em. subst R F'' pc'' fc'' m0''.
      pose proof (fun r => sl_getr_eqv R2 regs3 r Hx2) as GE.
      rewrite <- GE in G1. rewrite <- GE in G10. rewrite <- GE in G11. rewrite <- GE in G19.
      rewrite <- GE in G8. rewrite <- GE in G20. rewrite <- GE in G22. rewrite <- GE in G26.
      (* calloc(cap + 1, 20) *)
      apply (b1_calloc_call (fx := mkFP F1 fc1) B APIf ra empty FF g ((tab, (cap + 1) * 18) :: hb_cm bc bm)
               L2 A2 regs3 mem3 md2 regs3 (cap + 1) 20 (Post B APIf ra g) (CAL (mkFP F1 fc1)) HF3 HP2);
        [cbn; lia | unfold hb_bytes, hb_cm, M_SIZE, C_SIZE; cbn; lia | reflexivity | reflexivity | reflexivity
        | rewrite G1; vm_compute; reflexivity | exact G10 | exact G11 | lia | lia
        | unfold CallocBigC.CALLOC_BIG_CAP; lia |].
      intros L4 A4 regs4 mem4 md4 mt HF4 HP4 RP4 H10m Hmt0 Hmt16 HKS4 HKH4 HZ4.
      rewrite G1.
      assert (Q19 : YK11.getr regs4 19 = Z_to_bv 64 tab).
      { rewrite <- G19. exact (RP4 19 ltac:(unfold callee_saved; lia)). }
      assert (Q20 : YK11.getr regs4 20 = Z_to_bv 64 (cap + 1)).
      { rewrite <- G20. exact (RP4 20 ltac:(unfold callee_saved; lia)). }
      assert (Q22 : YK11.getr regs4 22 = Z_to_bv 64 cap).
      { rewrite <- G22. exact (RP4 22 ltac:(unfold callee_saved; lia)). }
      assert (Q8 : YK11.getr regs4 8 = Z_to_bv 64 bm).
      { rewrite <- G8. exact (RP4 8 ltac:(unfold callee_saved; lia)). }
      assert (Q26 : YK11.getr regs4 26 = Z_to_bv 64 (bm + MC_N)).
      { rewrite <- G26. exact (RP4 26 ltac:(unfold callee_saved; lia)). }
      (* the facts at 0x13cac, carried from the cut through the run and the two callocs *)
      assert (CARRY : forall a bs, bytes_at rsegs mem a bs -> disjoint_from (M02_W (g_S g)) a (Z.of_nat (length bs)) ->
                (exists k, In (a, k) (hb_cm bc bm) /\ Z.of_nat (length bs) <= k) \/
                (g_S g - 208 <= a /\ a + Z.of_nat (length bs) <= g_S g) ->
                bytes_at rsegs mem4 a bs).
      { intros a bs H Hd Hw.
        pose proof (b1_keep _ mem _ m' a bs HMI MU Hrel Hd H) as H1.
        assert (H2 : bytes_at rsegs mem2 a bs).
        { destruct Hw as [(k & Hin & Hk) | Hw].
          - exact (m02_blk_keep m' mem2 (hb_cm bc bm) a k bs H1 Hin Hk HKH2).
          - apply (m02_cell_keep m' mem2 (g_S g) a bs H1); [lia | lia |]. intros x Hx'. apply HKS2.
            unfold fsp, SLOT_FRAME. lia. }
        pose proof (m02_keep0 mem2 mem3 a bs HMI2 Hrel2 H2) as H3.
        destruct Hw as [(k & Hin & Hk) | Hw].
        - exact (m02_blk_keep mem3 mem4 ((tab, (cap + 1) * 18) :: hb_cm bc bm) a k bs H3 (or_intror Hin) Hk HKH4).
        - apply (m02_cell_keep mem3 mem4 (g_S g) a bs H3); [lia | lia |]. intros x Hx'. apply HKS4.
          unfold fsp, SLOT_FRAME. lia. }
      apply HK. exists bc, bm, tab, ((cap + 1) * 18), mt, ((cap + 1) * 20).
      exists (mkFP F1 fc1), L4, A4, regs4, mem4, md4.
      split; [reflexivity|]. split; [exact Hz1|]. split; [exact HF4|]. split; [exact HP4|].
      unfold CPseg. cbn [cp_K13cac].
      unfold seg_cuts.P_K13cac, seg_cuts.P_mcore, seg_cuts.rgz, seg_cuts.celz, seg_cuts.TAB_N, seg_cuts.MT_N,
        seg_cuts.SEG_FRAME.
      split; [unfold RVLAN_SIZE; lia|]. split; [unfold MVLAN_SIZE; lia|].
      split.
      { split; [exact Q8|]. split; [exact Q26|].
        split; [apply CARRY; [exact C8 | rewrite length_le8; unfold M02_W, M02_FRAME; cbn [disjoint_from];
                              repeat split; lia | right; rewrite length_le8; lia]|].
        split; [apply CARRY; [exact C10 | rewrite length_le8; unfold M02_W, M02_FRAME; cbn [disjoint_from];
                              repeat split; lia | right; rewrite length_le8; lia]|].
        split; [apply CARRY; [exact C30 | rewrite length_le8; unfold M02_W, M02_FRAME; cbn [disjoint_from];
                              repeat split; lia | right; rewrite length_le8; lia]|].
        split; [exact Hc16|]. split; [exact Hm16|]. split; [exact Hcn | exact Hmn]. }
      split; [exact H10m|]. split; [exact Q19|]. split; [exact Q20|]. split; [exact Q22|].
      assert (Ht : In (tab, (cap + 1) * 18) ((mt, (cap + 1) * 20) :: (tab, (cap + 1) * 18) :: hb_cm bc bm))
        by (right; left; reflexivity).
      assert (Hm : In (mt, (cap + 1) * 20) ((mt, (cap + 1) * 20) :: (tab, (cap + 1) * 18) :: hb_cm bc bm))
        by (left; reflexivity).
      destruct (b1_hb B APIf ra empty FF g _ tab ((cap + 1) * 18) L4 A4 regs4 mem4 md4 HF4 HP4 Ht)
        as (_ & Ht4 & Htc).
      destruct (b1_hb B APIf ra empty FF g _ mt ((cap + 1) * 20) L4 A4 regs4 mem4 md4 HF4 HP4 Hm)
        as (_ & Hmt4 & Hmtc).
      split.
      { assert (Z2 : bytes_at rsegs mem2 tab (repeat ZERO (Z.to_nat ((cap + 1) * 18)))).
        { apply m02_zeros; [lia | lia | lia |]. intros i Hi. exact (HZ2 i Hi). }
        pose proof (m02_keep0 mem2 mem3 _ _ HMI2 Hrel2 Z2) as Z3.
        apply (m02_blk_keep mem3 mem4 ((tab, (cap + 1) * 18) :: hb_cm bc bm) tab ((cap + 1) * 18) _ Z3
                 (or_introl eq_refl)); [|exact HKH4].
        rewrite repeat_length, Z2Nat.id by lia. lia. }
      split.
      { apply m02_zeros; [lia | lia | lia |]. intros i Hi. exact (HZ4 i Hi). }
      split; [exact Htab16|]. split; [exact Hmt16|].
      split; [exact (b1_blk_noimg_segs B APIf ra empty FF g _ tab _ L4 A4 regs4 mem4 md4 HF4 HP4 Ht)|].
      split; [exact (b1_blk_noimg_segs B APIf ra empty FF g _ mt _ L4 A4 regs4 mem4 md4 HF4 HP4 Hm)|].
      split.
      { destruct Hrc as (bs & Hb & He). exists bs. split; [|exact He].
        apply CARRY; [exact Hb | | left; exists 16616; split; [right; left; reflexivity|]];
          destruct He as (Hl & _); rewrite Hl; unfold SEG_C_SIZE, M02_W, M02_FRAME; cbn [disjoint_from];
          repeat split; lia. }
      { destruct Hmc as (bs & Hb & He). exists bs. split; [|exact He].
        apply CARRY; [exact Hb | | left; exists 9236; split; [left; reflexivity|]];
          destruct He as (Hl & _); rewrite Hl; unfold SEG_M_SIZE, M02_W, M02_FRAME; cbn [disjoint_from];
          repeat split; lia. }
Qed.

End M02.

(* The inner walk from the segment's callee contracts: pieces A (check_segments and the per-segment checks), B
   (the refusal checks), C (the probes), D ("nosuch0" and calloc's arguments), composed by m02_compose. *)
Theorem m02_inner_holds : MainB.K_M02 -> M02_inner.
Proof.
  intros (KCS & KRO & KCR & KMO & KCM & KIG & KCI & KRF & KIF & KCP & KCRF & KCA & KCK & KSN & KSL & KMF & KAB).
  apply M02_I.m02_compose.
  - exact (M02_A.m02_A KCS KRO KCR KMO KCM KIG KCI KRF KIF KCP).
  - exact (M02_B.m02_B KCRF KCA KCK).
  - exact (M02_C.m02_C KSN KSL KMF KAB).
  - exact (M02_D.m02_D KMF KAB).
Qed.

Theorem seg_M02 : SegEnd.seg_M02_stmt SegWalkMainA.CPseg MainB.K_M02.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF HK CAL.
  exact (seg_M02_of_inner (fx := fx) (rc := rc) (LS := LS) (SH := SH) (SK := SK) B APIf ra empty FF
           (m02_inner_holds HK) CAL).
Qed.
