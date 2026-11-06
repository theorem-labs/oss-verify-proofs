From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sef.
Import ListNotations.
Open Scope Z_scope.

Section KA.
Context {fx : YK11.FPState}.

Lemma F01_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp v lo : Z),
  put_dec_contract -> ro_agree rsegs m ->
  x2 = Z_to_bv 64 sp -> x20 = Z_to_bv 64 v ->
  0 <= v < 65536 -> IMG_HI <= lo -> lo + 64 <= sp -> sp + 368 <= 2 ^ 64 -> sp mod 16 = 0 ->
  stk rsegs m lo sp -> wr_at rsegs m sp 368 ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x13664) x2 x3 x4 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
                (Z_to_bv 64 (v / 1000)) (Z_to_bv 64 (sp + 48)) x23 x24 x25 x26 x27 t3 t4 t5 t6) /\
       pc' = Z_to_bv 64 0x13664 /\
       munch [(sp - 64, sp); (sp + 176, sp + 176 + 8); (sp + 48, sp + 48 + dec_len (v / 1000) 1)] m m' /\
       wmono rsegs m m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' (sp + 48) (DEC (v / 1000) 1) /\
       bytes_at rsegs m' (sp + 176) (le8 (Z_to_bv 64 (dec_len (v / 1000) 1))))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x13630) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp v lo PD HRO E2 E20 Hv HLO HL Hsp Hal ST WR.
  subst x2 x20.
  unfold IMG_HI in HLO.
  pose proof (sf_dec1_len (v / 1000) ltac:(Z.div_mod_to_equations; lia)) as HDL.
  pose proof (wr_at_store_ok rsegs m sp 368 176 8 WR ltac:(lia) ltac:(lia)) as HS.
  step.
  assert (B1 : bytes_at rsegs (write_to_mem m (Z_to_bv 64 (sp + 176)) (le8 (Z_to_bv 64 0))) (sp + 176)
                 (le8 (Z_to_bv 64 0))) by (apply bytes_at_write_same; rewrite ?length_le8; lia).
  assert (W1 : wr_at rsegs (write_to_mem m (Z_to_bv 64 (sp + 176)) (le8 (Z_to_bv 64 0))) sp 368)
    by (apply wr_at_write; exact WR).
  assert (R1 : ro_agree rsegs (write_to_mem m (wa (sp + 176)) (le8 (Z_to_bv 64 0))))
    by (apply sf_ro_write; [exact HRO | unfold IMG_HI; lia | rewrite length_le8; lia]).
  assert (S1 : stk rsegs (write_to_mem m (wa (sp + 176)) (le8 (Z_to_bv 64 0))) lo sp)
    by (apply stk_write; [exact ST | lia | rewrite length_le8; lia]).
  assert (M1 : munch [(sp - 64, sp); (sp + 176, sp + 176 + 8); (sp + 48, sp + 48 + dec_len (v / 1000) 1)] m
                 (write_to_mem m (wa (sp + 176)) (le8 (Z_to_bv 64 0)))).
  { apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia |].
    rewrite length_le8. cbn [Frame.inside]. lia. }
  assert (WM1 : wmono rsegs m (write_to_mem m (wa (sp + 176)) (le8 (Z_to_bv 64 0))))
    by (apply wmono_write; apply wmono_refl).
  change (wa (sp + 176)) with (Z_to_bv 64 (sp + 176)) in R1, S1, M1, WM1.
  set (m1 := write_to_mem m (Z_to_bv 64 (sp + 176)) (le8 (Z_to_bv 64 0))) in *.
  clearbody m1.
  step. step. step. step. step. step. step. step. step. step. step. step.
  rewrite (sf_div1000 v Hv).
  eapply (sf_put_dec_call PD) with (lo := lo) (b := sp + 48) (p := sp + 176) (v := v / 1000) (mn := 1)
    (N := Z_to_bv 64 0).
  - reflexivity.
  - reflexivity.
  - rewrite unsigned_lit by (Z.div_mod_to_equations; lia). apply Z.mod_small. Z.div_mod_to_equations; lia.
  - left. rewrite unsigned_lit by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia.
  - reflexivity.
  - lia.
  - exact B1.
  - apply (sf_wr_sub _ sp 368); [exact W1 | lia | lia | lia].
  - lia.
  - change (bv_unsigned (Z_to_bv 64 0)) with 0. apply (sf_wr_sub _ sp 368); [exact W1 | lia | lia | lia].
  - exact R1.
  - rewrite unsigned_lit by lia. exact S1.
  - rewrite unsigned_lit by lia. unfold PUT_DEC_FRAME. lia.
  - unfold IMG_HI. lia.
  - unfold IMG_HI. lia.
  - lia.
  - change (bv_unsigned (Z_to_bv 64 0)) with 0. unfold IMG_HI. lia.
  - change (bv_unsigned (Z_to_bv 64 0)) with 0. lia.
  - change (bv_unsigned (Z_to_bv 64 0)) with 0. right. lia.
  - rewrite unsigned_lit by lia. right. lia.
  - change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite unsigned_lit by lia. right. lia.
  - intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO HD HN.
    change (bv_unsigned (Z_to_bv 64 0)) with 0 in MU, HD, HN.
    rewrite (unsigned_lit sp) in MU by lia. unfold PUT_DEC_FRAME in MU.
    rewrite Z.add_0_r in MU, HD. rewrite Z.add_0_l in HN.
    rewrite sf_ret_pc_lit by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [do 15 eexists; reflexivity|].
    split; [reflexivity|].
    replace (sp + 176 + 8) with (sp + 184) in M1, MU by lia.
    split; [exact (munch_trans _ _ _ _ M1 MU)|].
    split; [eapply wmono_trans; [exact WM1 | exact WM]|].
    split; [exact RO|]. split; [exact HD | exact HN].
Qed.

End KA.

Section F01.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PD : put_dec_contract.

Lemma seg_F01 : Hcut B APIf ra (Inv_K13664 B APIf ra empty) -> Hcut B APIf ra (Inv_K13630 B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & HE).
  pose proof (sf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & _).
  destruct (sf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HE as (HTID & HTL & H20).
  set (v := t_any_fw (g_in g)) in *.
  assert (Hv : 0 <= v < 65536).
  { unfold v, t_any_fw, tb. pose proof (inb_range (g_in g) (cT (g_in g) + 9)).
    pose proof (inb_range (g_in g) (cT (g_in g) + 10)). lia. }
  pose proof (sf_dec1_len (v / 1000) ltac:(Z.div_mod_to_equations; lia)) as HDL.
  assert (WR : wr_at rsegs mem (fsp g) 368).
  { split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hwin (fsp g + i) ltac:(lia)) as W.
    rewrite SEG in W. exact W. }
  eapply (sf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x13630) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (F01_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) v (g_S g - SLOT_K) PD).
    - rewrite <- SEG. exact HMI.
    - rewrite <- (sf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (sf_getr_reg regs 20) by reflexivity. exact H20.
    - exact Hv.
    - exact HI.
    - lia.
    - lia.
    - unfold fsp, SLOT_FRAME. Z.div_mod_to_equations. lia.
    - exact ST.
    - exact WR. }
  intros R pc' m' regs1 (Hreg & -> & MU & WM & RO & HD & HN) XR.
  destruct Hreg as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->).
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27] regs regs1) by sf_kp XR regs.
  assert (G21 : getr regs1 21 = Z_to_bv 64 (v / 1000)) by (rewrite (sf_getr_x _ _ 21 XR) by reflexivity; reflexivity).
  assert (G22 : getr regs1 22 = Z_to_bv 64 (spk g 48)) by (rewrite (sf_getr_x _ _ 22 XR) by reflexivity; reflexivity).
  assert (HWin : forall lo hi y,
            In (lo, hi) [(fsp g - 64, fsp g); (fsp g + 176, fsp g + 176 + 8);
                         (fsp g + 48, fsp g + 48 + dec_len (v / 1000) 1)] -> lo <= y < hi ->
            fsp g - 64 <= y < fsp g \/ fsp g + 176 <= y < fsp g + 184 \/ fsp g + 48 <= y < fsp g + 50).
  { intros lo hi y Hy Hr. destruct Hy as [Hy|[Hy|[Hy|[]]]]; injection Hy as <- <-; lia. }
  assert (OUT : FRout g [(fsp g - 64, fsp g); (fsp g + 176, fsp g + 176 + 8);
                         (fsp g + 48, fsp g + 48 + dec_len (v / 1000) 1)]).
  { intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr). unfold spk. lia. }
  apply HX. exists L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (sf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' _ HF HP
             (KP1 2 ltac:(sf_in)) (KP1 3 ltac:(sf_in)) (KP1 4 ltac:(sf_in)) MU WM).
    intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr). left. lia. }
  split; [exact HP|].
  split.
  - split; [exact (sf_TID_munch g _ mem m' MU OUT HTID)|].
    split; [exact (sf_TL_munch g _ regs regs1 mem m'
                     (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) MU OUT HTL)|].
    sf_k KP1 20. exact H20.
  - split; [exact G21|]. split; [exact G22|]. split; [exact HN | exact HD].
Qed.

End F01.
