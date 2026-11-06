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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Spec Require StrFun.

Lemma f4_mm_refl : forall l n, (n <= length l)%nat -> U.Spec.StrFun.memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros l H; [reflexivity|].
  destruct l as [|b l]; cbn in *; [lia|]. rewrite Z.eqb_refl. apply IH. lia.
Qed.

Ltac f4_br :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota|symmetry]
  end.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma F04_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp n : Z) (ef : list byte),
  U.Prog.bcmp_c.bcmp_contract -> mem_inv rsegs m ->
  x2 = Z_to_bv 64 sp -> x10 = Z_to_bv 64 n -> x18 = Z_to_bv 64 n ->
  0 <= sp -> sp + 384 <= 2 ^ 64 -> 5 <= n <= 6 -> Z.of_nat (length ef) = n ->
  bytes_at rsegs m (sp + 242) (ef ++ [z8]) -> bytes_at rsegs m (sp + 64) (ef ++ [z8]) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x138e0) x2 x3 x4 t0 t1 t2 x8 x9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                (Z_to_bv 64 n) x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) /\
       pc' = Z_to_bv 64 0x138e0 /\ munch [] m m')
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x138c8) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp n ef BC MI E2 E10 E18 Hsp Hsp2 Hn Hl B242 B64.
  subst x2 x10 x18.
  step. f4_br.
  2: { first [ rewrite uf_lts by lia; apply Z.ltb_ge; lia
             | unfold bv_lts; rewrite !Z_to_bv_signed;
               rewrite !bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn; lia); apply Z.ltb_ge; lia
             | vm_compute; reflexivity ]. }
  step. f4_br.
  2: { first [ unfold bv_eqb; rewrite Z.eqb_refl; reflexivity
             | rewrite uf_eqb by lia; rewrite Z.eqb_refl; reflexivity
             | cbv [negb]; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]. }
  step. step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := ef ++ [z8]) (rs := ef ++ [z8]) (v := 0).
    - rewrite unsigned_lit by lia. exact B242.
    - rewrite unsigned_lit by lia. exact B64.
    - rewrite unsigned_lit by lia. apply f4_mm_refl. rewrite length_app. cbn [Datatypes.length]. lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & _).
  rewrite uf_ret_pc_lit by lia.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [do 14 eexists; reflexivity|].
  split; [reflexivity | exact MU].
Qed.

End KA.

Section F04.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis BC : U.Prog.bcmp_c.bcmp_contract.

Lemma seg_F04 : Hcut B APIf ra (Inv_U138e0 B APIf ra empty) -> Hcut B APIf ra (Inv_U138c8 B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & (HE & H18 & HC64 & HC242) & H10).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  destruct (uf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HE as (HTID & HTL & H22).
  set (v := t_any_fw (g_in g)) in *.
  assert (Hv : 0 <= v < 65536).
  { unfold v, t_any_fw, tb. pose proof (inb_range (g_in g) (cT (g_in g) + 9)).
    pose proof (inb_range (g_in g) (cT (g_in g) + 10)). lia. }
  pose proof (reac_identity_fw_str_c3_len v Hv) as (_ & HLv).
  assert (HLr : 5 <= lib.Prog.reac_identity_fw_str_c.L v <= 6) by (destruct (v <? 10000); lia).
  assert (EFW : FW v = t_EF (g_in g)) by (rewrite reac_identity_fw_str_c3 by exact Hv; reflexivity).
  assert (EZ : zlen (t_EF (g_in g)) = lib.Prog.reac_identity_fw_str_c.L v) by (rewrite <- EFW; reflexivity).
  rewrite EZ in H18.
  rewrite <- EFW in HC64.
  assert (HRO : ro_agree rsegs mem) by (rewrite <- SEG; exact HMI).
  eapply (uf_kA_run B APIf ra empty FF regs (Z_to_bv 64 0x138c8) mem md); [exact Hh | exact Hl | exact HMI | |].
  { unfold mkR_of.
    apply (F04_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (normalize rsegs mem) (fsp g)
             (lib.Prog.reac_identity_fw_str_c.L v) (FW v) BC).
    - apply mem_inv_normalize.
    - rewrite <- (uf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (uf_getr_reg regs 10) by reflexivity. exact H10.
    - rewrite <- (uf_getr_reg regs 18) by reflexivity. exact H18.
    - lia.
    - lia.
    - exact HLr.
    - reflexivity.
    - apply bytes_at_normalize; [exact HRO | exact HC242].
    - apply bytes_at_normalize; [exact HRO | exact HC64]. }
  intros R pc' m' regs1 mem1 (Hreg & -> & MU) XR Hmr Hsame.
  destruct Hreg as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->).
  pose proof (uf_nowrite0 mem mem1 m' Hmr Hsame MU) as EQM.
  assert (KP1 : KP [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
  assert (G18 : getr regs1 18 = Z_to_bv 64 (lib.Prog.reac_identity_fw_str_c.L v))
    by (rewrite (uf_getr_x _ _ 18 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 0) by (rewrite (uf_getr_x _ _ 10 XR) by reflexivity; reflexivity).
  assert (FRe : FReq g mem mem1) by (apply uf_FReq_eq; exact EQM).
  assert (BS : forall a bs, bytes_at rsegs mem a bs -> bytes_at rsegs mem1 a bs).
  { intros a bs HB. apply (uf_bytes_same rsegs mem mem1 a bs); [|exact HB]. intros i _. apply EQM. }
  apply HX. exists L, A, regs1, mem1, md. split; [reflexivity|].
  split.
  { apply (uf_FR_kA B APIf ra empty FF g _ _ L A regs mem md regs1 mem1 HF HP
             (KP1 2 ltac:(uf_in)) (KP1 3 ltac:(uf_in)) (KP1 4 ltac:(uf_in))).
    - intros x _ _. apply EQM.
    - apply uf_wmono_eq. exact EQM. }
  split; [exact HP|].
  split; [|exact G10].
  split.
  { split; [exact (uf_TID_tr g mem mem1 FRe HTID)|].
    split; [exact (uf_TL_kp g regs regs1 mem mem1 (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) FRe HTL)|].
    uf_k KP1 22. exact H22. }
  split; [rewrite EZ; exact G18|].
  split; [rewrite <- EFW; exact (BS _ _ HC64) | exact (BS _ _ HC242)].
Qed.

End F04.
