From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac ZBridge
Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec RcIdentModel SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sb2.
Import ListNotations.
Open Scope Z_scope.

Ltac sb2_br b rw :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; rw; solve_cond]
  end.

Section Seg.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_B12 : forall i,
  Hrec B APIf ra (Inv_K1328c_at B APIf ra empty) i ->
  Hrec B APIf ra (Inv_K13440_at B APIf ra empty) i ->
  Hrec B APIf ra (Inv_K132d8_at B APIf ra empty) i ->
  Hrec B APIf ra (fun g i c => Inv_K131c8_at B APIf ra empty g i 0 c) i ->
  Hrec B APIf ra (Inv_K13188_at B APIf ra empty) i.
Proof.
  intros i H1 H2 H3 H4 g c (pl & L & A & regs & mem & md & -> & HFR & HPERM & HP).
  destruct HP as (HRB & HS7 & HFALL & HRR & HA0).
  pose proof HFR as HFR'. unfold FR in HFR'. cbv zeta in HFR'.
  destruct HFR' as (HGV & H2s & _ & _ & _ & _ & _ & _ & HMR & _).
  pose proof (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hlz & _).
  pose proof HRB as (HREC & H21 & H20 & H22 & HPLB & HID & HAGN & HBEF & HLPm).
  assert (LID : length (rec_id (g_in g) (S i)) = 38%nat) by (rewrite rec_id_length; reflexivity).
  assert (RDa : ov_read_bytes rsegs mem (wa (fsp g + 262)) 1 = Some [nth 36 (rec_id (g_in g) (S i)) (zb 0)]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 226) _ 36 _ HAGN); [rewrite LID; lia | unfold spk; lia]. }
  assert (RDb : ov_read_bytes rsegs mem (wa (fsp g + 166)) 1 = Some [nth 36 (rec_id (g_in g) (S i)) (zb 0)]).
  { apply (sb2_bytes_at_rd1' rsegs mem (spk g 130) _ 36 _ HID); [rewrite LID; lia | unfold spk; lia]. }
  assert (G2 : reg_get regs 2 = Z_to_bv 64 (fsp g)) by exact H2s.
  assert (G10 : reg_get regs 10 = Z_to_bv 64 0) by exact HA0.
  assert (G9 : reg_get regs 9 = Z_to_bv 64 (rec_r (g_in g) i)) by exact HRR.
  assert (G23 : reg_get regs 23 = Z_to_bv 64 (rec_addr (g_in g) i)) by exact HS7.
  assert (G21 : reg_get regs 21 = Z_to_bv 64 (rec_k (g_in g) i)) by exact H21.
  assert (G8 : reg_get regs 8 = Z_to_bv 64 (has_fw (rec_id (g_in g) (S i)))) by exact (proj1 (proj2 HFALL)).
  assert (G22 : reg_get regs 22 = Z_to_bv 64 pl) by exact H22.
  pose proof (sb2_rec_addr_range (g_in g) i) as AR.
  pose proof (rec_k_range (g_in g) i) as KR.
  destruct (rec_r_range (g_in g) i) as [R0|R1].
  - eapply (sb2_seg_run B APIf ra empty FF regs 0x13188 mem md _
      (fun R pc' m' => pc' = 0x1328c /\ m' = mem /\
         sb2_agree regs R [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] /\
         getr R 10 = Z_to_bv 64 (has_reac_version (rec_id (g_in g) (S i)))) Hh Hlz).
    + unfold Regs6ss.mkR_of. rewrite G2.
      step. sb2_br false ltac:(rewrite G10).
      step. step. step. sb2_br false idtac.
      step. sb2_br true ltac:(rewrite G9, R0).
      apply evt_done. do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
      intros k Hk. cbn [In] in Hk. repeat destruct Hk as [<-|Hk]; try contradiction;
        first [reflexivity | rewrite <- G2; reflexivity].
    + intros R R' pc' m' (-> & -> & AG & HA) XR.
      assert (AG' : sb2_agree regs R' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27])
        by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
            repeat destruct Hk as [<-|Hk]; try contradiction; lia).
      apply H1. exists pl, L, A, R', mem, md. split; [reflexivity|].
      split; [apply (sb2_FR_regs B APIf ra empty FF g _ _ L A regs mem md R' HFR HPERM);
              apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [exact HPERM|].
      split; [apply (sb2_RB12 g i pl regs R' mem HRB); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [apply (sb2_S7A g i regs R' HS7); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [apply (sb2_FALL g i regs R' HFALL); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [apply (sb2_RRr g i regs R' HRR); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
      split; [exact R0|].
      rewrite (sb2_getr_x R R' _ XR) by reflexivity. exact HA.
  - assert (PRE : forall Q : machine_state -> Prop,
      Exec.evt rsegs Q (MS (mkR (reg_get regs 1) (Z_to_bv 64 (fsp g)) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
        (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (zxb (nth 36 (rec_id (g_in g) (S i)) (zb 0)))
        (Z_to_bv 64 4096) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16)
        (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
        (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28)
        (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)) fp_regs (Z_to_bv 64 0x131a0) fp_csr None mem (seg_rom rsegs)) ->
      Exec.evt rsegs Q (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x13188) fp_csr None mem (seg_rom rsegs))).
    { intros Q HQ. unfold Regs6ss.mkR_of. rewrite G2.
      step. sb2_br false ltac:(rewrite G10).
      step. step. step. sb2_br false idtac.
      step. sb2_br false ltac:(rewrite G9, R1).
      step. exact HQ. }
    destruct (Z.eq_dec (rec_addr (g_in g) i) ADDR_MODEL_NAME) as [EA|NA].
    + eapply (sb2_seg_run B APIf ra empty FF regs 0x13188 mem md _
        (fun R pc' m' => pc' = 0x13440 /\ m' = mem /\
           sb2_agree regs R [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) Hh Hlz).
      * apply PRE. step. sb2_br true ltac:(rewrite G23, EA).
        apply evt_done. do 3 eexists. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|].
        intros k Hk. cbn [In] in Hk. repeat destruct Hk as [<-|Hk]; try contradiction;
          first [reflexivity | rewrite <- G2; reflexivity].
      * intros R R' pc' m' (-> & -> & AG) XR.
        assert (AG' : sb2_agree regs R' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27])
          by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
              repeat destruct Hk as [<-|Hk]; try contradiction; lia).
        apply H2. exists pl, L, A, R', mem, md. split; [reflexivity|].
        split; [apply (sb2_FR_regs B APIf ra empty FF g _ _ L A regs mem md R' HFR HPERM);
                apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
        split; [exact HPERM|].
        split; [apply (sb2_RB12 g i pl regs R' mem HRB); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
        split; [apply (sb2_S7A g i regs R' HS7); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
        split; [apply (sb2_FALL g i regs R' HFALL); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
        split; [apply (sb2_RRr g i regs R' HRR); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
        split; [exact R1 | exact EA].
    + destruct (Z.eq_dec (rec_addr (g_in g) i) ADDR_REAC_VERSION) as [EV|NV].
      * eapply (sb2_seg_run B APIf ra empty FF regs 0x13188 mem md _
          (fun R pc' m' => pc' = 0x132d8 /\ m' = mem /\
             sb2_agree regs R [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] /\
             getr R 10 = Z_to_bv 64 (has_reac_version (rec_id (g_in g) (S i)))) Hh Hlz).
        -- apply PRE. step. sb2_br false ltac:(rewrite G23, EV).
           step. step. sb2_br true ltac:(rewrite G23, EV).
           apply evt_done. do 3 eexists. split; [reflexivity|].
           split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
           intros k Hk. cbn [In] in Hk. repeat destruct Hk as [<-|Hk]; try contradiction;
             first [reflexivity | rewrite <- G2; reflexivity].
        -- intros R R' pc' m' (-> & -> & AG & HA) XR.
           assert (AG' : sb2_agree regs R' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27])
             by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
                 repeat destruct Hk as [<-|Hk]; try contradiction; lia).
           apply H3. exists pl, L, A, R', mem, md. split; [reflexivity|].
           split; [apply (sb2_FR_regs B APIf ra empty FF g _ _ L A regs mem md R' HFR HPERM);
                   apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
           split; [exact HPERM|].
           split; [apply (sb2_RB12 g i pl regs R' mem HRB); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
           split; [apply (sb2_S7A g i regs R' HS7); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
           split; [apply (sb2_FALL g i regs R' HFALL); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
           split; [apply (sb2_RRr g i regs R' HRR); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
           split; [split; [exact R1 | exact EV]|].
           rewrite (sb2_getr_x R R' _ XR) by reflexivity. exact HA.
      * destruct (sb2_rec_fw (g_in g) i R1 NA NV) as (EF & K4 & DIG & HF1 & FWM & FWR).
        eapply (sb2_seg_run B APIf ra empty FF regs 0x13188 mem md _
          (fun R pc' m' => pc' = 0x131c8 /\ m' = mem /\
             sb2_agree regs R [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] /\
             getr R 14 = Z_to_bv 64 10 /\ getr R 10 = Z_to_bv 64 4 /\ getr R 11 = Z_to_bv 64 pl) Hh Hlz).
        -- apply PRE. step. sb2_br false ltac:(rewrite G23, EF).
           step. step. sb2_br false ltac:(rewrite G23, EF).
           step. sb2_br false ltac:(rewrite G23, EF).
           step. step. step.
           sb2_br false ltac:(rewrite G21; unfold bv_ltu; rewrite (MState.unsigned_lit (rec_k (g_in g) i)) by lia).
           step. sb2_br false ltac:(rewrite G8, HF1).
           step. step.
           apply evt_done. do 3 eexists. split; [reflexivity|].
           split; [reflexivity|]. split; [reflexivity|].
           split; [intros k Hk; cbn [In] in Hk; repeat destruct Hk as [<-|Hk]; try contradiction;
                   first [reflexivity | rewrite <- G2; reflexivity]|].
           split; [reflexivity|]. split; [reflexivity|]. rewrite <- G22. reflexivity.
        -- intros R R' pc' m' (-> & -> & AG & HA14 & HA10 & HA11) XR.
           assert (AG' : sb2_agree regs R' [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27])
             by (apply (sb2_agree_eqv regs R R' _ AG XR); intros k Hk; cbn [In] in Hk;
                 repeat destruct Hk as [<-|Hk]; try contradiction; lia).
           apply H4. exists pl, L, A, R', mem, md. split; [reflexivity|].
           split; [apply (sb2_FR_regs B APIf ra empty FF g _ _ L A regs mem md R' HFR HPERM);
                   apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
           split; [exact HPERM|].
           split; [lia|].
           split; [apply (sb2_RB12 g i pl regs R' mem HRB); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
           split; [apply (sb2_S7A g i regs R' HS7); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
           split; [apply (sb2_FALL g i regs R' HFALL); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
           split; [apply (sb2_RRr g i regs R' HRR); apply (sb2_agree_sub regs R' _ _ AG'); cbn [In]; tauto|].
           split; [split; [exact R1 | exact EF]|].
           split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact HA14|].
           split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; exact HA10|].
           split; [rewrite (sb2_getr_x R R' _ XR) by reflexivity; rewrite Z.add_0_r; exact HA11|].
           intros j Hj. lia.
Qed.

End Seg.
