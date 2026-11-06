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

Lemma F02_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp v n lo : Z),
  put_dec_contract -> ro_agree rsegs m ->
  x2 = Z_to_bv 64 sp -> x20 = Z_to_bv 64 v -> x21 = Z_to_bv 64 (v / 1000) -> x22 = Z_to_bv 64 (sp + 48) ->
  0 <= v < 65536 -> 1 <= n <= 2 -> IMG_HI <= lo -> lo + 64 <= sp -> sp + 368 <= 2 ^ 64 -> sp mod 16 = 0 ->
  stk rsegs m lo sp -> wr_at rsegs m sp 368 ->
  ov_read_bytes rsegs m (wa (sp + 176)) 8 = Some (le8 (Z_to_bv 64 n)) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x136a4) x2 x3 x4 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
                x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) /\
       pc' = Z_to_bv 64 0x136a4 /\
       munch [(sp - 64, sp); (sp + 176, sp + 184); (sp + 48 + n, sp + 48 + n + 4)] m m' /\
       wmono rsegs m m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' (sp + 48 + n) [dot] /\ bytes_at rsegs m' (sp + 48 + n + 1) (DEC (v mod 1000) 3) /\
       bytes_at rsegs m' (sp + 176) (le8 (Z_to_bv 64 (n + 1 + 3))))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x13664) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp v n lo PD HRO E2 E20 E21 E22 Hv Hn HLO HL Hsp Hal ST WR RD.
  subst x2 x20 x21 x22.
  unfold IMG_HI in HLO.
  pose proof (sf_dec3_len (v mod 1000) ltac:(apply Z.mod_pos_bound; lia)) as HD3.
  step. step. step.
  pose proof (wr_at_store_ok rsegs m sp 368 (48 + n) 1 WR ltac:(lia) ltac:(lia)) as HS.
  replace (sp + (48 + n)) with (sp + 48 + n) in HS by lia.
  step.
  remember (write_to_mem m (Z_to_bv 64 (sp + 48 + n)) (le1 (Z_to_bv 64 46))) as m1 eqn:Em1.
  assert (W1 : wr_at rsegs m1 sp 368) by (rewrite Em1; apply wr_at_write; exact WR).
  assert (B1 : bytes_at rsegs m1 (sp + 48 + n) [dot]).
  { rewrite Em1, <- sf_le1_dot. apply bytes_at_write_same; unfold le1; rewrite ?length_Z_to_le_bytes; lia. }
  assert (R1 : ro_agree rsegs m1).
  { rewrite Em1. apply sf_ro_write; [exact HRO | unfold IMG_HI; lia | unfold le1; rewrite length_Z_to_le_bytes; lia]. }
  assert (S1 : stk rsegs m1 lo sp).
  { rewrite Em1. apply stk_write; [exact ST | lia | unfold le1; rewrite length_Z_to_le_bytes; lia]. }
  assert (M1 : munch [(sp - 64, sp); (sp + 176, sp + 184); (sp + 48 + n, sp + 48 + n + 4)] m m1).
  { rewrite Em1. apply munch_write; [apply munch_refl | lia | unfold le1; rewrite length_Z_to_le_bytes; lia |].
    unfold le1. rewrite length_Z_to_le_bytes. cbn [Frame.inside]. lia. }
  assert (WM1 : wmono rsegs m m1) by (rewrite Em1; apply wmono_write; apply wmono_refl).
  clear Em1.
  step. step. step. step. step. step.
  pose proof (wr_at_store_ok rsegs m1 sp 368 176 8 W1 ltac:(lia) ltac:(lia)) as HS2.
  step.
  remember (write_to_mem m1 (Z_to_bv 64 (sp + 176)) (le8 (Z_to_bv 64 (n + 1)))) as m2 eqn:Em2.
  assert (W2 : wr_at rsegs m2 sp 368) by (rewrite Em2; apply wr_at_write; exact W1).
  assert (B2 : bytes_at rsegs m2 (sp + 176) (le8 (Z_to_bv 64 (n + 1))))
    by (rewrite Em2; apply bytes_at_write_same; rewrite ?length_le8; lia).
  assert (D2 : bytes_at rsegs m2 (sp + 48 + n) [dot]).
  { rewrite Em2. apply bytes_at_write_other; [exact B1 | lia | rewrite length_le8; lia | cbn [Datatypes.length]; lia]. }
  assert (R2 : ro_agree rsegs m2).
  { rewrite Em2. apply sf_ro_write; [exact R1 | unfold IMG_HI; lia | rewrite length_le8; lia]. }
  assert (S2 : stk rsegs m2 lo sp) by (rewrite Em2; apply stk_write; [exact S1 | lia | rewrite length_le8; lia]).
  assert (M2 : munch [(sp - 64, sp); (sp + 176, sp + 184); (sp + 48 + n, sp + 48 + n + 4)] m m2).
  { rewrite Em2. apply munch_write; [exact M1 | lia | rewrite length_le8; lia |].
    rewrite length_le8. cbn [Frame.inside]. lia. }
  assert (WM2 : wmono rsegs m m2) by (rewrite Em2; apply wmono_write; exact WM1).
  clear Em2.
  step. step. step. step. step.
  rewrite (sf_mod1000 v Hv).
  eapply (sf_put_dec_call PD) with (lo := lo) (b := sp + 48) (p := sp + 176) (v := v mod 1000) (mn := 3)
    (N := Z_to_bv 64 (n + 1)).
  - reflexivity.
  - reflexivity.
  - rewrite unsigned_lit by (pose proof (Z.mod_pos_bound v 1000); lia). apply Z.mod_small.
    pose proof (Z.mod_pos_bound v 1000). lia.
  - left. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound v 1000); lia). pose proof (Z.mod_pos_bound v 1000). lia.
  - reflexivity.
  - lia.
  - exact B2.
  - apply (sf_wr_sub _ sp 368); [exact W2 | lia | lia | lia].
  - lia.
  - rewrite (unsigned_lit (n + 1)) by lia. rewrite HD3. apply (sf_wr_sub _ sp 368); [exact W2 | lia | lia | lia].
  - exact R2.
  - rewrite unsigned_lit by lia. exact S2.
  - rewrite unsigned_lit by lia. unfold PUT_DEC_FRAME. lia.
  - unfold IMG_HI. lia.
  - unfold IMG_HI. lia.
  - lia.
  - rewrite (unsigned_lit (n + 1)) by lia. unfold IMG_HI. lia.
  - rewrite (unsigned_lit (n + 1)) by lia. rewrite HD3. lia.
  - rewrite (unsigned_lit (n + 1)) by lia. rewrite HD3. right. lia.
  - rewrite unsigned_lit by lia. right. lia.
  - rewrite (unsigned_lit (n + 1)) by lia. rewrite (unsigned_lit sp) by lia. right. lia.
  - intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO HD HN.
    rewrite (unsigned_lit (n + 1)) in MU, HD, HN by lia.
    rewrite (unsigned_lit sp) in MU by lia. unfold PUT_DEC_FRAME in MU. rewrite HD3 in MU, HN.
    rewrite sf_ret_pc_lit by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [do 15 eexists; reflexivity|].
    split; [reflexivity|].
    split.
    { apply (munch_trans _ m m2 m' M2). eapply munch_weaken; [|exact MU]. sf_subfp. }
    split; [eapply wmono_trans; [exact WM2 | exact WM]|].
    split; [exact RO|].
    split.
    { apply (bytes_at_transport rsegs _ m2 m' _ _ D2 MU). cbn [disjoint_from Datatypes.length]. repeat split; lia. }
    split.
    { replace (sp + 48 + n + 1) with (sp + 48 + (n + 1)) by lia. exact HD. }
    replace (n + 1 + 3) with (n + 4) in HN by lia. exact HN.
Qed.

End KA.

Section F02.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PD : put_dec_contract.

Lemma seg_F02 : Hcut B APIf ra (Inv_K136a4 B APIf ra empty) -> Hcut B APIf ra (Inv_K13664 B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & HE & H21 & H22 & HQ & HD1).
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
  set (n := dec_len (v / 1000) 1) in *.
  assert (WR : wr_at rsegs mem (fsp g) 368).
  { split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hwin (fsp g + i) ltac:(lia)) as W.
    rewrite SEG in W. exact W. }
  assert (RD : ov_read_bytes rsegs mem (wa (fsp g + 176)) 8 = Some (le8 (Z_to_bv 64 n)))
    by (apply sf_rd_q64; exact HQ).
  eapply (sf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x13664) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (F02_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) v n (g_S g - SLOT_K) PD).
    - rewrite <- SEG. exact HMI.
    - rewrite <- (sf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (sf_getr_reg regs 20) by reflexivity. exact H20.
    - rewrite <- (sf_getr_reg regs 21) by reflexivity. exact H21.
    - rewrite <- (sf_getr_reg regs 22) by reflexivity. exact H22.
    - exact Hv.
    - exact HDL.
    - exact HI.
    - lia.
    - lia.
    - unfold fsp, SLOT_FRAME. Z.div_mod_to_equations. lia.
    - exact ST.
    - exact WR.
    - exact RD. }
  intros R pc' m' regs1 (Hreg & -> & MU & WM & RO & HDOT & HD3 & HN) XR.
  destruct Hreg as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->).
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by sf_kp XR regs.
  assert (HWin : forall lo hi y,
            In (lo, hi) [(fsp g - 64, fsp g); (fsp g + 176, fsp g + 184); (fsp g + 48 + n, fsp g + 48 + n + 4)] ->
            lo <= y < hi -> fsp g - 64 <= y < fsp g \/ fsp g + 176 <= y < fsp g + 184 \/ fsp g + 49 <= y < fsp g + 54).
  { intros lo hi y Hy Hr. destruct Hy as [Hy|[Hy|[Hy|[]]]]; injection Hy as <- <-; lia. }
  assert (OUT : FRout g [(fsp g - 64, fsp g); (fsp g + 176, fsp g + 184); (fsp g + 48 + n, fsp g + 48 + n + 4)]).
  { intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr). unfold spk. lia. }
  assert (D1 : bytes_at rsegs m' (fsp g + 48) (DEC (v / 1000) 1)).
  { unfold spk in HD1. apply (bytes_at_transport rsegs _ mem m' _ _ HD1 MU).
    change (Z.of_nat (length (DEC (v / 1000) 1))) with n. cbn [disjoint_from]. repeat split; lia. }
  assert (EL : zlen (t_EF (g_in g)) = n + 1 + 3).
  { unfold zlen, t_EF. fold v. rewrite !length_app. cbn [Datatypes.length].
    pose proof (sf_dec3_len (v mod 1000) ltac:(apply Z.mod_pos_bound; lia)) as E3. unfold dec_len in E3.
    assert (En : n = Z.of_nat (length (DEC (v / 1000) 1))) by reflexivity. lia. }
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
  - split; [sf_k KP1 21; exact H21|]. split; [sf_k KP1 22; exact H22|].
    split; [unfold q64; rewrite EL; exact HN|].
    unfold t_EF. fold v. unfold spk.
    apply bytes_at_app. split; [exact D1|].
    apply bytes_at_app. split.
    + change (Z.of_nat (length (DEC (v / 1000) 1))) with n. exact HDOT.
    + cbn [Datatypes.length]. change (Z.of_nat (length (DEC (v / 1000) 1))) with n.
      replace (fsp g + 48 + n + Z.of_nat 1) with (fsp g + 48 + n + 1) by lia. exact HD3.
Qed.

End F02.
