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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require reac_box_family_of_c.

Lemma c01_fam : forall a idb, a <> 0 -> lib.Prog.reac_box_family_of_c.FAMOF_FAM a idb = FAM idb.
Proof.
  intros a idb H. unfold FAM, lib.Prog.reac_box_family_of_c.FAMOF_FAM.
  destruct (Z.eqb_spec a 0); [lia|]. reflexivity.
Qed.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma C01_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp h lo : Z) (idb : list byte),
  U.Prog.reac_box_family_of_c.reac_box_family_of_contract -> ro_agree rsegs m ->
  x2 = Z_to_bv 64 sp -> 0 <= h < 2 ^ 32 ->
  ov_read_bytes rsegs m (wa (sp + 32)) 8 = Some (le8 (Z_to_bv 64 h)) ->
  0 <= sp -> sp + 384 <= 2 ^ 64 -> sp mod 16 = 0 -> wr_at rsegs m sp 384 ->
  stk rsegs m lo sp -> lo + 32 <= sp -> IMG_HI <= lo ->
  bytes_at rsegs m (sp + 146) idb -> length idb = 38%nat ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x136b0) x2 x3 x4 t0 t1 t2 (Z_to_bv 64 h) x9 (Z_to_bv 64 (FAM idb))
                a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) /\
       pc' = Z_to_bv 64 0x136b0 /\ munch [(sp - 32, sp); (sp + 128, sp + 132)] m m' /\ wmono rsegs m m' /\
       ro_agree rsegs m' /\ bytes_at rsegs m' (sp + 128) (le4 (Z_to_bv 64 h)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x136a0) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp h lo idb FO HRO E2 Hh RD Hsp Hsp2 Hal WR ST HL HI BID Hlid.
  subst x2. unfold IMG_HI in HI.
  pose proof (wr_at_store_ok rsegs m sp 384 128 4 WR ltac:(lia) ltac:(lia)) as HS.
  step. step.
  match goal with |- Exec.evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?aa ?bs) _) =>
    replace aa with (Z_to_bv 64 (sp + 128)) by (first [reflexivity | f_equal; lia]);
    change bs with (le4 (Z_to_bv 64 h))
  end.
  remember (write_to_mem m (Z_to_bv 64 (sp + 128)) (le4 (Z_to_bv 64 h))) as m1 eqn:Em1.
  assert (B1 : bytes_at rsegs m1 (sp + 128) (le4 (Z_to_bv 64 h)))
    by (rewrite Em1; apply bytes_at_write_same; rewrite ?length_le4; lia).
  assert (R1 : ro_agree rsegs m1).
  { rewrite Em1. apply uf_ro_write; [exact HRO | unfold IMG_HI; lia | rewrite length_le4; lia]. }
  assert (S1 : stk rsegs m1 lo sp) by (rewrite Em1; apply stk_write; [exact ST | lia | rewrite length_le4; lia]).
  assert (M1 : munch [(sp - 32, sp); (sp + 128, sp + 132)] m m1).
  { rewrite Em1. apply munch_write; [apply munch_refl | lia | rewrite length_le4; lia |].
    rewrite length_le4. cbn [Frame.inside]. lia. }
  assert (WM1 : wmono rsegs m m1) by (rewrite Em1; apply wmono_write; apply wmono_refl).
  assert (D1 : bytes_at rsegs m1 (sp + 146) idb).
  { rewrite Em1. apply bytes_at_write_other; [exact BID | lia | rewrite length_le4; lia |].
    rewrite length_le4, Hlid. lia. }
  clear Em1.
  step. step.
  eapply (uf_famof_call FO) with (lo := lo) (a := sp + 146) (idb := idb).
  - exact R1.
  - reflexivity.
  - lia.
  - rewrite unsigned_lit by lia. exact S1.
  - rewrite unsigned_lit by lia. lia.
  - unfold IMG_HI. lia.
  - right. split; [exact D1|]. split; [exact Hlid|]. split; [Z.div_mod_to_equations; lia|].
    right. rewrite unsigned_lit by lia. lia.
  - intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO.
    rewrite (c01_fam (sp + 146) idb) by lia.
    rewrite unsigned_lit in MU by lia.
    rewrite uf_ret_pc_lit by lia.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [do 14 eexists; reflexivity|].
    split; [reflexivity|].
    split.
    { apply (munch_trans _ m m1 m' M1). eapply munch_weaken; [|exact MU]. uf_subfp. }
    split; [eapply wmono_trans; [exact WM1 | exact WM]|].
    split; [exact RO|].
    apply (uf_bytes_munch1 _ _ m1 m' _ _ MU); [|exact B1]. right. lia.
Qed.

End KA.

Section C01.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis FO : U.Prog.reac_box_family_of_c.reac_box_family_of_contract.

Lemma seg_C01 : Hcut B APIf ra (Inv_U136b0 B APIf ra empty) -> Hcut B APIf ra (Inv_U136a0 B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & HCB & H9).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & _).
  destruct (uf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HCB as (HNR & HNRb & HG24 & (HW1 & HW2 & HW3) & HCUR & HID).
  assert (Hhv : 0 <= haveT (g_in g) < 2) by (unfold haveT, rec_have; destruct (rec_hw _ _); lia).
  assert (WR : wr_at rsegs mem (fsp g) 384).
  { split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hwin (fsp g + i) ltac:(lia)) as W.
    rewrite SEG in W. exact W. }
  assert (RD : ov_read_bytes rsegs mem (wa (fsp g + 32)) 8 = Some (le8 (Z_to_bv 64 (haveT (g_in g)))))
    by (apply uf_rd_q64; exact HW1).
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x136a0) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (C01_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) (haveT (g_in g))
             (g_S g - SLOT_K) (idT (g_in g)) FO).
    - rewrite <- SEG. exact HMI.
    - rewrite <- (uf_getr_reg regs 2) by reflexivity. exact Hsp.
    - lia.
    - exact RD.
    - lia.
    - lia.
    - unfold fsp, SLOT_FRAME. Z.div_mod_to_equations. lia.
    - exact WR.
    - exact ST.
    - lia.
    - exact HI.
    - exact HID.
    - apply rec_id_length. }
  intros R pc' m' regs1 (Hreg & -> & MU & WM & RO & B128) XR.
  destruct Hreg as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->).
  assert (KP1 : KP [2; 3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
  assert (G8 : getr regs1 8 = Z_to_bv 64 (haveT (g_in g))) by (rewrite (uf_getr_x _ _ 8 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (FAM (idT (g_in g))))
    by (rewrite (uf_getr_x _ _ 10 XR) by reflexivity; reflexivity).
  set (W := [(fsp g - 32, fsp g); (fsp g + 128, fsp g + 132)]) in *.
  assert (HWin : forall lo hi y, In (lo, hi) W -> lo <= y < hi -> fsp g - 32 <= y < fsp g \/ fsp g + 128 <= y < fsp g + 132).
  { intros lo hi y Hy Hr. unfold W in Hy. destruct Hy as [Hy|[Hy|[]]]; injection Hy as <- <-; lia. }
  assert (KEEP : forall a bs, bytes_at rsegs mem a bs ->
            (a + Z.of_nat (length bs) <= fsp g - 32 \/ (fsp g <= a /\ a + Z.of_nat (length bs) <= fsp g + 128) \/
             fsp g + 132 <= a) -> bytes_at rsegs m' a bs).
  { intros a bs H Hd. apply (uf_bytes_munchP (fun y => fsp g - 32 <= y < fsp g \/ fsp g + 128 <= y < fsp g + 132)
      W mem m' a bs MU HWin); [|exact H]. intros i Hi. lia. }
  apply HX. exists L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (uf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' W HF HP
             (KP1 2 ltac:(uf_in)) (KP1 3 ltac:(uf_in)) (KP1 4 ltac:(uf_in)) MU WM).
    intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr). left. lia. }
  split; [exact HP|].
  split; [|split; [exact G8 | exact G10]].
  split; [exact HNR|].
  split; [unfold NRb, q64, spk in *; apply KEEP; [exact HNRb | rewrite length_le8; lia]|].
  split; [unfold G24, q64, spk in *; apply KEEP; [exact HG24 | rewrite length_le8; lia]|].
  split.
  { split; [unfold q64, spk in *; apply KEEP; [exact HW1 | rewrite length_le8; lia]|].
    split; [unfold u32, spk; exact B128|].
    unfold spk in *. apply KEEP; [exact HW3|]. right; right. lia. }
  split.
  { destruct HCUR as (C1 & C2 & C3). split; [exact C1|]. split; [uf_k KP1 26; exact C2 | uf_k KP1 25; exact C3]. }
  unfold IDb, spk in *. apply KEEP; [exact HID | right; right; lia].
Qed.

End C01.
