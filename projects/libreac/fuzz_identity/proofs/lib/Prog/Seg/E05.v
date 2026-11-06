From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv
  reac_identity_fw_str_c check_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sef.
Import ListNotations.
Open Scope Z_scope.

Section KA.
Context {fx : YK11.FPState}.

Lemma E05_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp s cap r lo : Z) (str slack : list byte),
  check_str_contract -> ro_agree rsegs m ->
  x2 = Z_to_bv 64 sp -> x23 = Z_to_bv 64 s -> x22 = Z_to_bv 64 cap -> x10 = Z_to_bv 64 r ->
  0 <= sp < 2 ^ 64 -> -2 ^ 31 <= r < 2 ^ 31 -> 0 <= s < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  (0 <= r -> check_str_ok m (Z_to_bv 64 sp) r s cap str slack) ->
  stk rsegs m lo sp -> lo + 16 <= sp -> IMG_HI <= lo ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x135e8) x2 x3 x4 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24
                x25 x26 x27 t3 t4 t5 t6) /\
       pc' = Z_to_bv 64 0x135e8 /\ munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m')
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x135dc) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp s cap r lo str slack CS Hro E2 E23 E22 E10 Hsp Hr Hs Hc OK ST HL HI.
  subst x2 x23 x22 x10.
  step. step. step.
  eapply (sf_check_str_call CS) with (r := r) (o := s) (c := cap) (lo := lo) (str := str) (slack := slack);
    [exact Hro | exact Hr | reflexivity | exact Hs | reflexivity | exact Hc | reflexivity | exact OK
    | rewrite unsigned_lit by exact Hsp; exact ST | rewrite unsigned_lit by exact Hsp; unfold CHECK_STR_FRAME; lia
    | exact HI |].
  intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO.
  rewrite sf_ret_pc_lit by lia.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [do 15 eexists; reflexivity|].
  split; [reflexivity|].
  rewrite unsigned_lit in MU by exact Hsp. unfold CHECK_STR_FRAME in MU.
  split; [exact MU|]. split; [exact WM | exact RO].
Qed.

End KA.

Section E05.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CHK : check_str_contract.

Lemma seg_E05 : Hcut B APIf ra (Inv_K135e8 B APIf ra empty) -> Hcut B APIf ra (Inv_K135dc B APIf ra empty).
Proof.
  intros HX g c (s & L & A & regs & mem & md & -> & HF & HP & HE & H10 & HO).
  pose proof (sf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  destruct (sf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HE as (HTID & HTL & H21 & H22 & H23 & H20).
  set (cap := t_cap_fw (g_in g)) in *.
  assert (Hcap : 0 <= cap < 16) by (unfold cap, t_cap_fw; apply Z.mod_pos_bound; lia).
  assert (Hin : In (s, bsz cap) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (sf_hb_blk B APIf ra empty FF g _ _ L A regs mem md s (bsz cap) HF HP (or_introl eq_refl))
    as (HBW & Hs1 & Hs2 & Hs16).
  set (v := t_any_fw (g_in g)) in *.
  assert (Hv : 0 <= v < 65536).
  { unfold v, t_any_fw, tb. pose proof (inb_range (g_in g) (cT (g_in g) + 9)).
    pose proof (inb_range (g_in g) (cT (g_in g) + 10)). lia. }
  pose proof (reac_identity_fw_str_c3_len v Hv) as (_ & HLv).
  assert (HLr : 5 <= reac_identity_fw_str_c.L v <= 6) by (destruct (v <? 10000); lia).
  assert (ELv : reac_identity_fw_str_c.L v = Z.of_nat (length (FW v))) by reflexivity.
  assert (Hr : -2 ^ 31 <= fw_res v cap < 2 ^ 31) by (unfold fw_res; destruct (cap <? 8); lia).
  assert (SL : exists slack, 0 <= fw_res v cap ->
             check_str_ok mem (Z_to_bv 64 (fsp g)) (fw_res v cap) s cap (FW v) slack).
  { unfold fw_res. destruct (Z.ltb_spec cap 8) as [Hq|Hq]; [exists []; intros Hq'; lia|].
    destruct (sf_slack B APIf ra empty FF L A mem md s (bsz cap) (FW v) HMR Hin (HO Hq)
                ltac:(unfold bsz; lia)) as (slack & SB & SM & SBd).
    exists slack. intros _. unfold check_str_ok. rewrite unsigned_lit by lia.
    split; [lia|]. split; [exact (eq_sym ELv)|]. split; [exact SB|].
    split; [intros Hz; apply (reac_identity_fw_str_c3_nz v Hv _ Hz); reflexivity|].
    split; [rewrite ELv; exact SM|]. left. unfold CHECK_STR_FRAME. lia. }
  destruct SL as (slack & OK).
  eapply (sf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x135dc) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (E05_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) s cap (fw_res v cap)
             (g_S g - SLOT_K) (FW v) slack CHK).
    - rewrite <- SEG. exact HMI.
    - rewrite <- (sf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (sf_getr_reg regs 23) by reflexivity. exact H23.
    - rewrite <- (sf_getr_reg regs 22) by reflexivity. exact H22.
    - rewrite <- (sf_getr_reg regs 10) by reflexivity. exact H10.
    - lia.
    - exact Hr.
    - unfold bsz in Hs2. lia.
    - lia.
    - exact OK.
    - exact ST.
    - lia.
    - exact HI. }
  intros R pc' m' regs1 (Hreg & -> & MU & WM & RO) XR.
  destruct Hreg as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->).
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25] regs regs1) by sf_kp XR regs.
  assert (FRe : FReq g mem m').
  { unfold FReq. apply (sf_FReq_munch g _ mem m' MU); [| lia | lia].
    intros lo hi y Hy Hr'. destruct Hy as [Hy|[]]. injection Hy as <- <-. left. lia. }
  apply HX. exists s, L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (sf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' _ HF HP
             (KP1 2 ltac:(sf_in)) (KP1 3 ltac:(sf_in)) (KP1 4 ltac:(sf_in)) MU WM).
    intros lo hi y Hy Hr'. destruct Hy as [Hy|[]]. injection Hy as <- <-. left. lia. }
  split; [exact HP|].
  split.
  - split; [exact (sf_TID_tr g mem m' FRe HTID)|].
    split; [exact (sf_TL_kp g regs regs1 mem m' (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) FRe HTL)|].
    split; [sf_k KP1 21; exact H21|]. split; [sf_k KP1 22; exact H22|].
    split; [sf_k KP1 23; exact H23 | sf_k KP1 20; exact H20].
  - intros Hq. change (t_cap_fw (g_in g)) with cap in Hq. change (t_any_fw (g_in g)) with v.
    apply (sf_bytes_munch1 _ _ mem m' s _ MU); [|exact (HO Hq)].
    left. rewrite length_app. cbn [Datatypes.length]. unfold bsz in Hs2. lia.
Qed.

End E05.
