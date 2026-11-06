(* Segment F02 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13820, 0x13840], U13820 -> U13844
   (v1.8 U13848); U13898 (v1.8 U1389c). s7 = Φ; #40 not taken (Φ != 0); left - h (s3) to sp+24 (the v1.8
   sp+64; v1.9 has no `li s0,1` here: it keeps 1 in s2); len (s6) = 0 -> U13898; else memcpy(Φ, p + body (s5), len)
   from the input block, memcpy at 0x1e2fc. Port of the plain seg_F02 (a working branch lib/Prog/Seg/F02.v). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u1 Tac_u4.
Import ListNotations.
Open Scope Z_scope.

(* len = 0: Φ to s7, left - h to sp+24, then 0x13830 goes to 0x13898. *)
Lemma f02z_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi lh : Z) (jt : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 phi -> s6 = Z_to_bv 64 0 -> s3 = Z_to_bv 64 lh ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    rw_cells rsegs m (spv + 24) [CB 8 jt] ->
    evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 lh) s4 s5 (Z_to_bv 64 0) (Z_to_bv 64 phi) s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13898) fc None m' (seg_rom rsegs) /\
         munch [(spv + 24, spv + 32)] m m' /\ wmono rsegs m m' /\ q64 m' (spv + 24) lh)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13820) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi lh jt -> -> -> -> Hlo Hhi Hjt.
  pose proof (munch_refl [(spv + 24, spv + 32)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. if_true.
  step. step. if_true.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  unfold q64. exact (u4_c_bytes _ _ _ Hjt).
Qed.

(* len != 0: the same store, then memcpy(Φ, p + body, len), back at 0x13844. *)
Lemma f02_evt : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi sa n lh : Z)
         (jt src junk : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 phi -> s5 = Z_to_bv 64 sa -> s6 = Z_to_bv 64 n -> s3 = Z_to_bv 64 lh ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 ->
    0 < phi -> phi + n < 2 ^ 64 -> 0 < n -> 0 <= sa -> sa + n < 2 ^ 64 -> (sa + n <= phi \/ phi + n <= sa) ->
    phi + n <= spv + 24 -> sa + n <= spv + 24 ->
    rw_cells rsegs m (spv + 24) [CB 8 jt] ->
    bytes_at rsegs m sa src -> length src = Z.to_nat n ->
    rw_cells rsegs m phi [Cells.CB (Z.to_nat n) junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13844) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 phi)
                       a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 lh) s4 (Z_to_bv 64 sa) (Z_to_bv 64 n)
                       (Z_to_bv 64 phi) s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13844) fc None m' (seg_rom rsegs) /\
         munch [(spv + 24, spv + 32); (phi, phi + n)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' phi src /\ q64 m' (spv + 24) lh)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13820) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi sa n lh jt src junk -> -> -> -> -> Hlo Hhi Hph0 Hph Hn0 Hsa0 Hsa Hdj Hpb Hsb Hjt HB HL HC MI.
  pose proof (munch_refl [(spv + 24, spv + 32); (phi, phi + n)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. if_false_by (u4_eqb0 n ltac:(lia)).
  step. if_false_by (u4_eqb0 phi ltac:(lia)).
  step. step. if_false_by (u4_eqb0 n ltac:(lia)).
  step. step. step. step.
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
  rewrite (MState.ret_pc_even 0x13844) by (first [reflexivity | lia]).
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split.
  { apply (munch_trans _ m _ m' MU). eapply munch_weaken; [|exact MUc].
    intros x (O1 & O2 & _). cbn [Frame.outside]. split; [exact O2 | exact I]. }
  split; [exact (wmono_trans rsegs _ _ m' WM WMc)|].
  split; [exact (sl_rw_bytes _ _ _ _ HZ)|].
  unfold q64. apply (bytes_at_transport rsegs _ _ m' _ _ (u4_c_bytes _ _ _ Hjt) MUc).
  cbn [disjoint_from Cells.cbytes]. rewrite length_le8. repeat split; try exact I; lia.
Qed.

Section F02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MCPY : memcpy_contract.

Lemma seg_F02 : forall j : nat, Hat B APIf ra (Inv_U13844_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13898_at B APIf ra empty) j -> Hat B APIf ra (Inv_U13820_at B APIf ra empty) j.
Proof.
  intros j H1 H0 g c (phi & L & A & regs & mem & md & -> & HFR & HP &
                      (HLK & Hl1 & HIFS & H21 & H22 & H19 & H10 & Hphi0)).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (u1_hb B APIf ra empty FF g phi (t_len (g_in g) j) L A regs mem md HFR HP) as (STb & Hphi & Hphin).
  pose proof alloc_ceiling_value as Hac.
  pose proof (u4_len_range (g_in g) j) as (Hl0 & Hb0 & Hbn).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HFR as (HGV & _).
  pose proof HGV as ((Hn26 & _) & _ & _ & _ & HSKc & _).
  assert (Hlh : 0 <= t_left (g_in g) j - t_h (g_in g) j <= g_n g).
  { unfold t_left, t_h, f_h, f_left, t_c in *. unfold g_n in *. pose proof (u4_fc_range (g_in g) j). lia. }
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 24) 8 ST ltac:(lia) ltac:(lia)) as (jt & Hjt).
  destruct (Z.eq_dec (t_len (g_in g) j) 0) as [Hz|Hnz].
  - (* len = 0: to U13898 *)
    eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ [(g_S g - 1936 + 24, g_S g - 1936 + 32)]);
      [exact HFR | exact HP | u4_fp_tac | | |].
    + rewrite sl_mkR_of.
      apply f02z_evt with (spv := g_S g - 1936) (phi := phi) (lh := t_left (g_in g) j - t_h (g_in g) j) (jt := jt);
        [exact Hsp | exact H10 | rewrite Hz in H22; exact H22 | exact H19 | lia | lia | exact Hjt].
    + intros ms (m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (m'' & HE & _ & _ & H24).
      injection HE; intros; subst.
      apply H0. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (E0 : t_phi (g_in g) j = []) by (apply length_zero_iff_nil; rewrite u4_phi_len, Hz; reflexivity).
      split; [|split; [lia|]].
      * split; [|split; [|split; [|split]]].
        -- eapply (u4_LK_keep g j regs regs' mem m' _ HLK); [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity
             | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity
             | exact MU' | u4_dj | u4_dj].
        -- unfold FC, rg. rewrite !(sl_getr_eqv _ _ _ Hx). split; [|split].
           ++ apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). unfold spk, fsp, SLOT_FRAME. exact H24.
           ++ exact H21.
           ++ rewrite Hz. reflexivity.
        -- unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
        -- rewrite E0. apply sl_bytes_nil. lia.
        -- unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). exact (u4_LK_s2 g j regs mem HLK).
      * apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj.
  - (* len != 0: memcpy(Φ, p + body, len) *)
    set (N := t_len (g_in g) j) in *.
    assert (Hn : 0 < g_n g) by (unfold g_n; lia).
    destruct (u4_in_all B APIf ra empty FF g _ L A regs mem md HFR HP Hn) as (Hp0 & Hpn & HIN).
    pose proof (u4_ba_sub mem (g_p g) (g_in g) (Z.to_nat (t_body (g_in g) j)) (Z.to_nat N) HIN
                  ltac:(unfold nlen in Hbn; lia)) as HSRC.
    rewrite Z2Nat.id in HSRC by lia.
    change (firstn (Z.to_nat N) (skipn (Z.to_nat (t_body (g_in g) j)) (g_in g))) with (t_phi (g_in g) j) in HSRC.
    pose proof (u4_phi_len (g_in g) j) as HL. fold N in HL.
    destruct (sl_rw_of_stk _ _ _ phi (Z.to_nat N) STb ltac:(lia) ltac:(lia)) as (junk & HC).
    pose proof (u4_hb_disj B APIf ra empty g phi N L A regs mem md (g_p g) (g_n g) HFR HP
                  (u4_in_blk B empty g HGV Hn)) as HD.
    pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
    destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
    rewrite SEGS.
    eapply (sl_run regs (Z_to_bv 64 0x13820) mem md _ _ Hh Hl HMI).
    + rewrite sl_mkR_of.
      apply (f02_evt MCPY) with (spv := g_S g - 1936) (phi := phi) (sa := g_p g + t_body (g_in g) j) (n := N)
        (lh := t_left (g_in g) j - t_h (g_in g) j) (jt := jt) (src := t_phi (g_in g) j) (junk := junk);
        [exact Hsp | exact H10 | exact H21 | exact H22 | exact H19 | lia | lia | lia | lia | lia | lia
        | unfold g_n in Hpn; lia | | lia | unfold g_n, nlen in *; lia | exact Hjt | | exact HL | exact HC
        | exact (mem_inv_normalize rsegs mem)].
      * unfold g_n, nlen in *. lia.
      * exact (bytes_at_normalize rsegs mem _ _ HMI HSRC).
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & _). do 3 eexists. reflexivity.
    + intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & WM & HZ & H24).
      injection HE; intros; subst.
      pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
      assert (MU' : Frame.munch [(g_S g - 1936 + 24, g_S g - 1936 + 32); (phi, phi + N)] mem m')
        by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m'' HR0 Hrel Hsame MU).
      assert (WM' : Frame.wmono rsegs mem m')
        by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m'' HR0 Hrel Hsame WM).
      assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' HMI Hsame).
      pose proof (u1_out _ _ _ _ Hrel HZ) as HZ'.
      pose proof (u1_out _ _ _ _ Hrel H24) as H24'.
      rewrite <- SEGS. apply H1. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split.
      { apply (u1_fr_hb B APIf ra empty FF g phi N L A regs mem md regs' m' HFR HP).
        - intros a Ha HS Hn'. apply MU'. rewrite MState.unsigned_lit by lia. cbn [outside].
          unfold SLOT_K, SLOT_STACK in HS. split; [lia|]. split; [exact Hn' | exact I].
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
      * split; [|split; [|split; [|split]]].
        -- eapply (u4_LK_keep g j regs regs' mem m' _ HLK); [rewrite (sl_getr_eqv _ _ _ Hx); reflexivity
             | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity
             | exact MU' | u4_dj | u4_dj].
        -- unfold FC, rg. rewrite !(sl_getr_eqv _ _ _ Hx). split; [|split].
           ++ unfold spk, fsp, SLOT_FRAME. exact H24'.
           ++ reflexivity.
           ++ reflexivity.
        -- unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
        -- exact HZ'.
        -- unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). exact (u4_LK_s2 g j regs mem HLK).
      * apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj.
Qed.

End F02.
