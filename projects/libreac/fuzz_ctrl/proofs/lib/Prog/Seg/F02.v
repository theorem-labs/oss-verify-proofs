(* Segment F02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x136d4, 0x136f4], K136d4 -> K136f8 (len != 0:
   memcpy(Φ, p + body, len)) and K13734 (len = 0). #40 is not taken: malloc's Φ != 0 (C1.1). *)
(* libreac v1.9.0 (CHANGED branch-target, new-insert, register; segment table 5a S_F02): v1.8 [0x136cc, 0x136e8]
   K136cc -> K136ec / K13728. The new 0x136e0 `sd s0,32(sp)` spills the body pointer (s0; v1.8 s3, never spilled)
   before the len = 0 test, so both exits carry FC's [sp+32] (SlotInv.v FC); the `bnez a0` at 0x136d8 now targets
   the spill 0x136e0. memcpy at 0x1d3d8, return 0x136f8. The entry cut K136d4 changed (LIp, FCr), so seg_F02 is
   stated on it; the exit cuts K136f8 / K13734 are v1.8 K136ec / K13728 renamed. rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b4.
Import ListNotations.
Open Scope Z_scope.

(* len = 0: Φ != 0 passes 0x136d8, 0x136e0 spills s0 to [sp+32], then 0x136e4 goes to 0x13734. *)
Lemma f02z_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi sa : Z) (junk : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 phi -> s0 = Z_to_bv 64 sa -> s4 = Z_to_bv 64 0 -> 0 < phi < 2 ^ 64 ->
    0 <= spv -> spv + 1936 < 2 ^ 64 ->
    Step.rw_cells rsegs m (spv + 32) [Cells.CB 8 junk] ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sa) s1 (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7 s2 s3
                       (Z_to_bv 64 0) (Z_to_bv 64 phi) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13734) fc None m' (seg_rom rsegs) /\
         munch [(spv + 32, spv + 40)] m m' /\ wmono rsegs m m' /\ q64 m' (spv + 32) sa)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x136d4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi sa junk -> -> -> -> Hphi Hs0 Hs1 HC.
  pose proof (Step.rw_cells_store_ok rsegs m (spv + 32) [Cells.CB 8 junk] 0 (Cells.CB 8 junk) 8 HC
                eq_refl eq_refl) as HS.
  pose proof (munch_refl [(spv + 32, spv + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. if_true_by (f_equal negb (b1_beq0 phi Hphi)).
  step. step. if_true.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  pose proof (sl_cells_bytes _ _ _ HC) as HB. cbn [Cells.cells_bytes Cells.cbytes] in HB.
  rewrite app_nil_r in HB. exact HB.
Qed.

(* len != 0: the spill, then memcpy(Φ, p + body, len), back at 0x136f8. *)
Lemma f02_evt : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi sa n : Z) (src junk j32 : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 phi -> s0 = Z_to_bv 64 sa -> s4 = Z_to_bv 64 n ->
    0 < phi -> phi + n <= spv -> 0 < n -> 0 <= sa -> sa + n <= spv -> (sa + n <= phi \/ phi + n <= sa) ->
    spv + 1936 < 2 ^ 64 ->
    bytes_at rsegs m sa src -> length src = Z.to_nat n ->
    rw_cells rsegs m phi [Cells.CB (Z.to_nat n) junk] -> Step.rw_cells rsegs m (spv + 32) [Cells.CB 8 j32] ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x136f8) sp gp tp t0' t1' t2' (Z_to_bv 64 sa) s1 (Z_to_bv 64 phi)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 n) (Z_to_bv 64 phi) s6 s7 s8 s9 s10 s11
                       t3' t4' t5' t6')
                  F (Z_to_bv 64 0x136f8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 32, spv + 40); (phi, phi + n)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' phi src /\
         q64 m' (spv + 32) sa)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x136d4) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi sa n src junk j32 -> -> -> -> Hph0 Hph Hn0 Hsa0 Hsa Hdj Hsp HB HL HC H32 MI.
  assert (HLz : Z.of_nat (length src) = n) by lia.
  pose proof (Step.rw_cells_store_ok rsegs m (spv + 32) [Cells.CB 8 j32] 0 (Cells.CB 8 j32) 8 H32
                eq_refl eq_refl) as HS.
  pose proof (munch_refl [(spv + 32, spv + 40); (phi, phi + n)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. if_true_by (f_equal negb (b1_beq0 phi ltac:(lia))).
  step. step. if_false_by (b1_beq0 n ltac:(lia)).
  step. step. step. step.
  pose proof (sl_cells_bytes _ _ _ H32) as HB32. cbn [Cells.cells_bytes Cells.cbytes] in HB32.
  rewrite app_nil_r in HB32.
  eapply evt_cut.
  { eapply MCPY with (src := src) (junk := junk); rewrite ?MState.unsigned_lit by lia.
    - exact HB.
    - exact HL.
    - exact HC.
    - lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & HZ & _).
  subst ms'. rewrite !MState.unsigned_lit in MUc, HZ by lia.
  rewrite (MState.ret_pc_even 0x136f8) by (first [reflexivity | lia]).
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split.
  { eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUc]].
    unfold sub_fp. cbn [outside]. intros x (O1 & O2 & _). split; [exact O2 | exact I]. }
  split; [exact (wmono_trans _ _ _ _ WM WMc)|].
  split; [exact (sl_rw_bytes _ _ _ _ HZ)|].
  unfold q64. apply (bytes_at_transport rsegs _ _ m' _ _ HB32 MUc).
  rewrite length_le8. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Section F02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MCPY : memcpy_contract.

Lemma seg_F02 : forall j : nat, Hat B APIf ra (Inv_K136f8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13734_at B APIf ra empty) j -> Hat B APIf ra (Inv_K136d4_at B APIf ra empty) j.
Proof.
  intros j H1 H0 g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HLI & HFC & H10 & Hphi0)).
  pose proof HLI as (Hj & H26 & _ & _ & HOUR & HIFS & HM7).
  pose proof HFC as (H27 & H8 & H20).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (b1_hb B APIf ra empty FF g phi (t_len (g_in g) j) L A regs mem md HFR HP) as (STb & Hphi & Hphin).
  pose proof alloc_ceiling_value as Hac.
  pose proof (b4_len_range (g_in g) j) as (Hl0 & Hb0 & Hbn).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (HGV & _).
  pose proof HGV as (_ & _ & _ & _ & HSKc & _).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 32) 8 ST ltac:(lia) ltac:(lia)) as (j32 & H32).
  destruct (Z.eq_dec (t_len (g_in g) j) 0) as [Hz|Hnz].
  - (* len = 0: the spill, to 0x13734 *)
    set (W := [(g_S g - 1936 + 32, g_S g - 1936 + 40)]).
    eapply (b4_mid B APIf ra empty FF g _ L A regs mem md _ W); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (b4_fp g W x _ Hx O). unfold W, SLOT_K, SLOT_STACK.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
    + rewrite sl_mkR_of.
      apply f02z_evt with (spv := g_S g - 1936) (phi := phi) (sa := g_p g + t_body (g_in g) j) (junk := j32);
        [exact Hsp | exact H10 | exact H8 | rewrite Hz in H20; exact H20 | lia | lia | lia | exact H32].
    + intros ms (m' & -> & MU & WM & _). do 3 eexists. split; [reflexivity|]. split; [exact MU|].
      split; [exact WM|]. split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (m'' & HE & _ & _ & H32'). injection HE; intros; subst.
      apply H0. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (KA : b4_keep mem m' (spk g 8) (spk g 32)).
      { apply (b4_keep_munch W mem m' _ _ MU'); [|unfold spk, fsp, SLOT_FRAME; lia..].
        unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. repeat split; lia. }
      assert (KB : b4_keep mem m' (spk g 40) (spk g 192)).
      { apply (b4_keep_munch W mem m' _ _ MU'); [|unfold spk, fsp, SLOT_FRAME; lia..].
        unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. repeat split; lia. }
      assert (E0 : t_phi (g_in g) j = []) by (apply length_zero_iff_nil; rewrite b4_phi_len, Hz; reflexivity).
      split; [|split; [exact Hz|]].
      * unfold FT, FC, rg. rewrite !(sl_getr_eqv _ _ _ Hx).
        split; [exact Hj|]. split; [exact H26|].
        split; [split; [exact H27 | split; [exact (b1_out _ _ _ _ Hrel H32') | rewrite Hz; reflexivity]]|].
        split; [reflexivity|].
        split; [rewrite E0; apply sl_bytes_nil; lia|].
        split.
        -- apply (b4_OUR_keep g mem m'); [eapply b4_keep_sub; [exact KB | unfold spk; lia | unfold spk; lia] | exact HOUR].
        -- apply (b4_M7_keep g mem m'); [eapply b4_keep_sub; [exact KA | unfold spk; lia | unfold spk; lia] | exact HM7].
      * apply (b4_IFS_keep2 g j regs regs' mem m');
          [eapply b4_keep_sub; [exact KA | unfold spk; lia | unfold spk; lia] | exact KB
          | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity | exact HIFS].
  - (* len != 0: the spill, then memcpy(Φ, p + body, len) *)
    set (N := t_len (g_in g) j) in *.
    assert (Hn : 0 < g_n g) by (unfold g_n; lia).
    destruct (b4_in_all B APIf ra empty FF g _ L A regs mem md HFR HP Hn) as (Hp0 & Hpn & HIN).
    pose proof (b4_ba_sub mem (g_p g) (g_in g) (Z.to_nat (t_body (g_in g) j)) (Z.to_nat N) HIN
                  ltac:(unfold nlen in Hbn; lia)) as HSRC.
    rewrite Z2Nat.id in HSRC by lia.
    change (firstn (Z.to_nat N) (skipn (Z.to_nat (t_body (g_in g) j)) (g_in g))) with (t_phi (g_in g) j) in HSRC.
    pose proof (b4_phi_len (g_in g) j) as HL. fold N in HL.
    destruct (sl_rw_of_stk _ _ _ phi (Z.to_nat N) STb ltac:(lia) ltac:(lia)) as (junk & HC).
    pose proof (b4_hb_disj B APIf ra empty g phi N L A regs mem md (g_p g) (g_n g) HFR HP
                  (b4_in_blk B empty g HGV Hn)) as HD.
    assert (Hsa : g_p g + t_body (g_in g) j + N <= g_S g - 1936) by (unfold g_n, nlen in *; lia).
    pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
    destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
    rewrite SEGS.
    eapply (sl_run regs (Z_to_bv 64 0x136d4) mem md _ _ Hh Hl HMI).
    + rewrite sl_mkR_of.
      apply (f02_evt MCPY) with (spv := g_S g - 1936) (phi := phi) (sa := g_p g + t_body (g_in g) j) (n := N)
        (src := t_phi (g_in g) j) (junk := junk) (j32 := j32);
        [exact Hsp | exact H10 | exact H8 | exact H20 | lia | lia | lia | lia | lia | | lia
        | | exact HL | exact HC | exact H32 | exact (mem_inv_normalize rsegs mem)].
      * unfold g_n, nlen in *. lia.
      * exact (bytes_at_normalize rsegs mem _ _ HMI HSRC).
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & _). do 3 eexists. reflexivity.
    + intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & WM & HZ & H32').
      injection HE; intros; subst.
      pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
      set (W := [(g_S g - 1936 + 32, g_S g - 1936 + 40); (phi, phi + N)]) in *.
      assert (MU' : Frame.munch W mem m')
        by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m'' HR0 Hrel Hsame MU).
      assert (WM' : Frame.wmono rsegs mem m')
        by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m'' HR0 Hrel Hsame WM).
      assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' HMI Hsame).
      pose proof (b1_out _ _ _ _ Hrel HZ) as HZ'.
      pose proof (b1_out _ _ _ _ Hrel H32') as H32''.
      assert (KA : b4_keep mem m' (spk g 8) (spk g 32)).
      { apply (b4_keep_munch _ mem m' _ _ MU'); [|unfold spk, fsp, SLOT_FRAME; lia..].
        unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. repeat split; lia. }
      assert (KB : b4_keep mem m' (spk g 40) (spk g 192)).
      { apply (b4_keep_munch _ mem m' _ _ MU'); [|unfold spk, fsp, SLOT_FRAME; lia..].
        unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. repeat split; lia. }
      rewrite <- SEGS. apply H1. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split.
      { apply (b1_fr_hb B APIf ra empty FF g phi N L A regs mem md regs' m' HFR HP).
        - intros a Ha Hs Hn'. apply MU'. rewrite MState.unsigned_lit by lia. unfold W. cbn [outside].
          unfold SLOT_K, SLOT_STACK in Hs.
          split; [lia | split; [exact Hn' | exact I]].
        - intros a Ha. destruct HZ' as (_ & _ & H3).
          assert (Hk : (Z.to_nat (a - phi) < length (t_phi (g_in g) j))%nat) by lia.
          destruct (nth_error (t_phi (g_in g) j) (Z.to_nat (a - phi))) as [bb|] eqn:En;
            [|apply nth_error_None in En; lia].
          exists bb. rewrite <- En, <- (H3 _ Hk). f_equal. unfold wa. f_equal. lia.
        - exact WM'.
        - exact Hro'.
        - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
        - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
        - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
      split; [exact HP|].
      split; [|split; [exact Hnz|]].
      * unfold FT, FC, rg. rewrite !(sl_getr_eqv _ _ _ Hx).
        split; [exact Hj|]. split; [exact H26|].
        split; [split; [exact H27 | split; [exact H32'' | reflexivity]]|].
        split; [reflexivity|].
        split; [exact HZ'|].
        split.
        -- apply (b4_OUR_keep g mem m'); [eapply b4_keep_sub; [exact KB | unfold spk; lia | unfold spk; lia] | exact HOUR].
        -- apply (b4_M7_keep g mem m'); [eapply b4_keep_sub; [exact KA | unfold spk; lia | unfold spk; lia] | exact HM7].
      * apply (b4_IFS_keep2 g j regs regs' mem m');
          [eapply b4_keep_sub; [exact KA | unfold spk; lia | unfold spk; lia] | exact KB
          | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity | exact HIFS].
Qed.

End F02.
