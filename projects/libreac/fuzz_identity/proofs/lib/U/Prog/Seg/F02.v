From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotInv write_uint_c reac_identity_fw_str_c
  reac_identity_reac_ver_str_c put_dec_c reac_box_family_of_c.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(bsz, z8, zlen, fw_res, fw_out, id_VER, ver_res,
  ver_out, HWT_ADDR).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_fw_str_c(FW, L, reac_identity_fw_str_c3,
  reac_identity_fw_str_c3_len, reac_identity_fw_str_c3_nz, reac_identity_fw_str_dec_h, reac_identity_fw_str_dec_f).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_identity_reac_ver_str_c(reac_ver_str_VER,
  reac_ver_str_LV, reac_ver_str_DEC2).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_ucg.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import put_dec_c.

Lemma f02_mod : forall v, 0 <= v < 65536 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32
    (bv_unsigned (Z_to_bv 64 v) - bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (v / 1000)) * 1000))))))
    48))) 48) = Z_to_bv 64 (v mod 1000).
Proof.
  intros v Hv.
  rewrite (unsigned_lit v) by lia.
  rewrite (unsigned_lit (v / 1000)) by (Z.div_mod_to_equations; lia).
  rewrite (unsigned_lit (v / 1000 * 1000)) by (Z.div_mod_to_equations; lia).
  assert (E : v - v / 1000 * 1000 = v mod 1000) by (Z.div_mod_to_equations; lia).
  rewrite E. pose proof (Z.mod_pos_bound v 1000 ltac:(lia)) as Hm.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia).
  rewrite (unsigned_lit (v mod 1000)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (unsigned_lit (v mod 1000 * 2 ^ 48)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Ltac f02_br :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota|symmetry]
  end.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma F02_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp v n lo : Z),
  put_dec_contract -> ro_agree rsegs m ->
  x2 = Z_to_bv 64 sp -> x22 = Z_to_bv 64 v -> x20 = Z_to_bv 64 (v / 1000) -> x8 = Z_to_bv 64 (sp + 64) ->
  0 <= v < 65536 -> 1 <= n <= 2 -> IMG_HI <= lo -> lo + 64 <= sp -> sp + 384 <= 2 ^ 64 -> sp mod 16 = 0 ->
  stk rsegs m lo sp -> wr_at rsegs m sp 384 ->
  ov_read_bytes rsegs m (wa (sp + 192)) 8 = Some (le8 (Z_to_bv 64 n)) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x1389c) x2 x3 x4 t0 t1 t2 (Z_to_bv 64 (18446744073709551615 - (sp + 64))) x9
                a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) /\
       pc' = Z_to_bv 64 0x1389c /\
       munch [(sp - 16, sp); (sp + 192, sp + 200); (sp + 64 + n, sp + 64 + n + 4)] m m' /\
       wmono rsegs m m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' (sp + 64 + n) [dot] /\ bytes_at rsegs m' (sp + 64 + n + 1) (DEC (v mod 1000) 3) /\
       bytes_at rsegs m' (sp + 192) (le8 (Z_to_bv 64 (n + 4))))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x1384c) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp v n lo PD HRO E2 E22 E20 E8 Hv Hn HLO HL Hsp Hal ST WR RD.
  subst x2 x22 x20 x8.
  unfold IMG_HI in HLO.
  pose proof (uf_dec3_len (v mod 1000) ltac:(apply Z.mod_pos_bound; lia)) as HD3.
  pose proof (wr_at_store_ok rsegs m sp 384 192 8 WR ltac:(lia) ltac:(lia)) as HS.
  step. step. step. step.
  remember (write_to_mem m (Z_to_bv 64 (sp + 192)) (le8 (Z_to_bv 64 (n + 1)))) as m1 eqn:Em1.
  assert (W1 : wr_at rsegs m1 sp 384) by (rewrite Em1; apply wr_at_write; exact WR).
  assert (B1 : bytes_at rsegs m1 (sp + 192) (le8 (Z_to_bv 64 (n + 1))))
    by (rewrite Em1; apply bytes_at_write_same; rewrite ?length_le8; lia).
  assert (R1 : ro_agree rsegs m1).
  { rewrite Em1. apply uf_ro_write; [exact HRO | unfold IMG_HI; lia | rewrite length_le8; lia]. }
  assert (S1 : stk rsegs m1 lo sp) by (rewrite Em1; apply stk_write; [exact ST | lia | rewrite length_le8; lia]).
  assert (M1 : munch [(sp - 16, sp); (sp + 192, sp + 200); (sp + 64 + n, sp + 64 + n + 4)] m m1).
  { rewrite Em1. apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia |].
    rewrite length_le8. cbn [Frame.inside]. lia. }
  assert (WM1 : wmono rsegs m m1) by (rewrite Em1; apply wmono_write; apply wmono_refl).
  clear Em1.
  step. f02_br.
  2: { rewrite uf_ltu by lia. destruct (Z.ltb_spec n 16); [reflexivity | lia]. }
  step.
  rewrite (unsigned_lit (sp + 64)) by lia. rewrite ZBridge.zb_lxor_ones by lia.
  step. f02_br.
  2: { rewrite uf_ltu by lia. destruct (Z.ltb_spec (18446744073709551615 - (sp + 64)) n); [lia | reflexivity]. }
  step. step. step. step.
  pose proof (wr_at_store_ok rsegs m1 sp 384 (64 + n) 1 W1 ltac:(lia) ltac:(lia)) as HS2.
  replace (sp + (64 + n)) with (sp + 64 + n) in HS2 by lia.
  step. step.
  remember (write_to_mem m1 (Z_to_bv 64 (sp + 64 + n)) (le1 (Z_to_bv 64 46))) as m2 eqn:Em2.
  assert (W2 : wr_at rsegs m2 sp 384) by (rewrite Em2; apply wr_at_write; exact W1).
  assert (D2 : bytes_at rsegs m2 (sp + 64 + n) [dot]).
  { rewrite Em2, <- uf_le1_dot. apply bytes_at_write_same; unfold le1; rewrite ?length_Z_to_le_bytes; lia. }
  assert (B2 : bytes_at rsegs m2 (sp + 192) (le8 (Z_to_bv 64 (n + 1)))).
  { rewrite Em2. apply bytes_at_write_other; [exact B1 | lia | unfold le1; rewrite length_Z_to_le_bytes; lia |].
    unfold le1. rewrite length_Z_to_le_bytes, length_le8. lia. }
  assert (R2 : ro_agree rsegs m2).
  { rewrite Em2. apply uf_ro_write; [exact R1 | unfold IMG_HI; lia | unfold le1; rewrite length_Z_to_le_bytes; lia]. }
  assert (S2 : stk rsegs m2 lo sp).
  { rewrite Em2. apply stk_write; [exact S1 | lia | unfold le1; rewrite length_Z_to_le_bytes; lia]. }
  assert (M2 : munch [(sp - 16, sp); (sp + 192, sp + 200); (sp + 64 + n, sp + 64 + n + 4)] m m2).
  { rewrite Em2. apply munch_write; [exact M1 | lia | unfold le1; rewrite length_Z_to_le_bytes; lia |].
    unfold le1. rewrite length_Z_to_le_bytes. cbn [Frame.inside]. lia. }
  assert (WM2 : wmono rsegs m m2) by (rewrite Em2; apply wmono_write; exact WM1).
  clear Em2.
  step. step. step. step. step. step. step.
  rewrite (f02_mod v Hv).
  eapply (uf_put_dec_call PD) with (lo := lo) (b := sp + 64) (p := sp + 192) (v := v mod 1000) (mn := 3)
    (N := Z_to_bv 64 (n + 1)).
  - reflexivity.
  - lia.
  - reflexivity.
  - rewrite unsigned_lit by (pose proof (Z.mod_pos_bound v 1000); lia). apply Z.mod_small.
    pose proof (Z.mod_pos_bound v 1000). lia.
  - left. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound v 1000); lia). pose proof (Z.mod_pos_bound v 1000). lia.
  - reflexivity.
  - lia.
  - exact B2.
  - apply (uf_wr_sub _ sp 384); [exact W2 | lia | lia | lia].
  - lia.
  - rewrite (unsigned_lit (n + 1)) by lia. rewrite HD3. apply (uf_wr_sub _ sp 384); [exact W2 | lia | lia | lia].
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
    rewrite uf_ret_pc_lit by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [do 15 eexists; reflexivity|].
    split; [reflexivity|].
    split.
    { apply (munch_trans _ m m2 m' M2). eapply munch_weaken; [|exact MU]. uf_subfp. }
    split; [eapply wmono_trans; [exact WM2 | exact WM]|].
    split; [exact RO|].
    split.
    { apply (bytes_at_transport rsegs _ m2 m' _ _ D2 MU). cbn [disjoint_from Datatypes.length]. repeat split; lia. }
    split.
    { replace (sp + 64 + n + 1) with (sp + 64 + (n + 1)) by lia. exact HD. }
    replace (n + 1 + 3) with (n + 4) in HN by lia. exact HN.
Qed.

End KA.

Section F02.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis PD : put_dec_contract.

Lemma seg_F02 : Hcut B APIf ra (Inv_U1389c B APIf ra empty) -> Hcut B APIf ra (Inv_U1384c B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & HE & H20 & H8 & HQ & HD1).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & _).
  destruct (uf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HE as (HTID & HTL & H22).
  set (v := t_any_fw (g_in g)) in *.
  assert (Hv : 0 <= v < 65536).
  { unfold v, t_any_fw, tb. pose proof (inb_range (g_in g) (cT (g_in g) + 9)).
    pose proof (inb_range (g_in g) (cT (g_in g) + 10)). lia. }
  pose proof (uf_dec1_len (v / 1000) ltac:(Z.div_mod_to_equations; lia)) as HDL.
  set (n := dec_len (v / 1000) 1) in *.
  assert (WR : wr_at rsegs mem (fsp g) 384).
  { split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hwin (fsp g + i) ltac:(lia)) as W.
    rewrite SEG in W. exact W. }
  assert (RD : ov_read_bytes rsegs mem (wa (fsp g + 192)) 8 = Some (le8 (Z_to_bv 64 n)))
    by (apply uf_rd_q64; exact HQ).
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x1384c) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (F02_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) v n (g_S g - SLOT_K) PD).
    - rewrite <- SEG. exact HMI.
    - rewrite <- (uf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (uf_getr_reg regs 22) by reflexivity. exact H22.
    - rewrite <- (uf_getr_reg regs 20) by reflexivity. exact H20.
    - rewrite <- (uf_getr_reg regs 8) by reflexivity. exact H8.
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
  assert (KP1 : KP [2; 3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
  assert (G8 : getr regs1 8 = notw (spk g 64)).
  { rewrite (uf_getr_x _ _ 8 XR) by reflexivity. unfold notw, spk. f_equal. }
  assert (HWin : forall lo hi y,
            In (lo, hi) [(fsp g - 16, fsp g); (fsp g + 192, fsp g + 200); (fsp g + 64 + n, fsp g + 64 + n + 4)] ->
            lo <= y < hi -> fsp g - 16 <= y < fsp g \/ fsp g + 192 <= y < fsp g + 200 \/ fsp g + 65 <= y < fsp g + 70).
  { intros lo hi y Hy Hr. destruct Hy as [Hy|[Hy|[Hy|[]]]]; injection Hy as <- <-; lia. }
  assert (OUT : FRout g [(fsp g - 16, fsp g); (fsp g + 192, fsp g + 200); (fsp g + 64 + n, fsp g + 64 + n + 4)]).
  { intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr). unfold spk. lia. }
  assert (D1 : bytes_at rsegs m' (fsp g + 64) (DEC (v / 1000) 1)).
  { unfold spk in HD1. apply (bytes_at_transport rsegs _ mem m' _ _ HD1 MU).
    change (Z.of_nat (length (DEC (v / 1000) 1))) with n. cbn [disjoint_from]. repeat split; lia. }
  assert (EL : zlen (t_EF (g_in g)) = n + 4).
  { unfold zlen, t_EF. fold v. rewrite !length_app. cbn [Datatypes.length].
    pose proof (uf_dec3_len (v mod 1000) ltac:(apply Z.mod_pos_bound; lia)) as E3. unfold dec_len in E3.
    assert (En : n = Z.of_nat (length (DEC (v / 1000) 1))) by reflexivity. lia. }
  apply HX. exists L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (uf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' _ HF HP
             (KP1 2 ltac:(uf_in)) (KP1 3 ltac:(uf_in)) (KP1 4 ltac:(uf_in)) MU WM).
    intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr). left. lia. }
  split; [exact HP|].
  split.
  - split; [exact (uf_TID_munch g _ mem m' MU OUT HTID)|].
    split; [exact (uf_TL_munch g _ regs regs1 mem m'
                     (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) MU OUT HTL)|].
    uf_k KP1 22. exact H22.
  - split; [uf_k KP1 20; exact H20|]. split; [exact G8|].
    split; [unfold q64; rewrite EL; exact HN|].
    unfold t_EF. fold v. unfold spk.
    apply bytes_at_app. split; [exact D1|].
    apply bytes_at_app. split.
    + change (Z.of_nat (length (DEC (v / 1000) 1))) with n. exact HDOT.
    + cbn [Datatypes.length]. change (Z.of_nat (length (DEC (v / 1000) 1))) with n.
      replace (fsp g + 64 + n + Z.of_nat 1) with (fsp g + 64 + n + 1) by lia. exact HD3.
Qed.

End F02.
