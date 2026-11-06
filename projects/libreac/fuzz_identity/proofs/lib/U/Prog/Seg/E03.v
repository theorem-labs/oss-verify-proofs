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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import check_str_c.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma E03_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp s cap r lo pc0 pc1 : Z) (str slack : list byte),
  check_str_contract -> ro_agree rsegs m ->
  x2 = Z_to_bv 64 sp -> x23 = Z_to_bv 64 s -> x20 = Z_to_bv 64 cap -> x10 = Z_to_bv 64 r ->
  0 <= sp < 2 ^ 64 -> -2 ^ 31 <= r < 2 ^ 31 -> 0 <= s < 2 ^ 64 -> 0 <= cap < 2 ^ 64 ->
  (0 <= r -> check_str_ok m (Z_to_bv 64 sp) r s cap str slack) ->
  stk rsegs m lo sp -> lo + 16 <= sp -> IMG_HI <= lo ->
  (pc0 = 0x137ac /\ pc1 = 0x137b8 \/ pc0 = 0x137c8 /\ pc1 = 0x137d4) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 pc1) x2 x3 x4 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24
                x25 x26 x27 t3 t4 t5 t6) /\
       pc' = Z_to_bv 64 pc1 /\ munch [(sp - 16, sp)] m m' /\ wmono rsegs m m' /\ ro_agree rsegs m')
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 pc0) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp s cap r lo pc0 pc1 str slack CS Hro E2 E23 E20 E10 Hsp Hr Hs Hc OK ST HL HI PCS.
  subst x2 x23 x20 x10.
  destruct PCS as [[-> ->]|[-> ->]]; step; step; step.
  all: eapply (uf_check_str_call CS) with (r := r) (o := s) (c := cap) (lo := lo) (str := str) (slack := slack).
  all: try exact Hro; try exact Hr; try reflexivity; try exact Hs; try exact Hc; try exact OK; try exact HI.
  all: try (rewrite unsigned_lit by exact Hsp; exact ST).
  all: try (rewrite unsigned_lit by exact Hsp; unfold CHECK_STR_FRAME; lia).
  all: intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' MU WM RO.
  all: rewrite uf_ret_pc_lit by lia.
  all: apply evt_done; do 3 eexists; split; [reflexivity|].
  all: split; [do 15 eexists; reflexivity|].
  all: split; [reflexivity|].
  all: rewrite unsigned_lit in MU by exact Hsp; unfold CHECK_STR_FRAME in MU.
  all: split; [exact MU|]; split; [exact WM | exact RO].
Qed.

End KA.

Section E03.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis CHK : check_str_contract.

Lemma e03_core : forall g v pc0 pc1 (Q : config -> Prop),
  (pc0 = 0x137ac /\ pc1 = 0x137b8 \/ pc0 = 0x137c8 /\ pc1 = 0x137d4) ->
  0 <= v < 65536 ->
  (forall s regs1 m' md,
     CUTST B APIf ra empty g pc1 (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
       (fun regs m => E794 g regs m /\ getr regs 23 = Z_to_bv 64 s /\ fw_out m v (t_cap_fw (g_in g)) s)
       (mkCfg (mkst regs1 (Z_to_bv 64 pc1) m' (seg_rom (ms_segs B))) md) ->
     Q (mkCfg (mkst regs1 (Z_to_bv 64 pc1) m' (seg_rom (ms_segs B))) md) ) ->
  (forall c, Q c -> Rz (ms_segs B) c (Post B APIf ra g)) ->
  forall c, (exists s, CUTST B APIf ra empty g pc0 (2 * NR g + 1) [(s, bsz (t_cap_fw (g_in g)))]
    (fun regs m => E794 g regs m /\ getr regs 23 = Z_to_bv 64 s /\
       getr regs 10 = Z_to_bv 64 (fw_res v (t_cap_fw (g_in g))) /\ fw_out m v (t_cap_fw (g_in g)) s) c) ->
  Rz (ms_segs B) c (Post B APIf ra g).
Proof.
  intros g v pc0 pc1 Q PCS Hv HQ HX c (s & L & A & regs & mem & md & -> & HF & HP & HE & H23 & H10 & HO).
  pose proof (uf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  destruct (uf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HE as (HTID & HTL & H20 & H21 & H22).
  set (cap := t_cap_fw (g_in g)) in *.
  assert (Hcap : 0 <= cap < 16) by (unfold cap, t_cap_fw; apply Z.mod_pos_bound; lia).
  assert (Hin : In (s, bsz cap) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (uf_hb_blk B APIf ra empty FF g _ _ L A regs mem md s (bsz cap) HF HP (or_introl eq_refl))
    as (HBW & Hs1 & Hs2 & Hs16).
  pose proof (reac_identity_fw_str_c3_len v Hv) as (_ & HLv).
  assert (HLr : 5 <= lib.Prog.reac_identity_fw_str_c.L v <= 6) by (destruct (v <? 10000); lia).
  assert (ELv : lib.Prog.reac_identity_fw_str_c.L v = Z.of_nat (length (FW v))) by reflexivity.
  assert (Hr : -2 ^ 31 <= fw_res v cap < 2 ^ 31) by (unfold fw_res; destruct (cap <? 8); lia).
  assert (SL : exists slack, 0 <= fw_res v cap ->
             check_str_ok mem (Z_to_bv 64 (fsp g)) (fw_res v cap) s cap (FW v) slack).
  { unfold fw_res. destruct (Z.ltb_spec cap 8) as [Hq|Hq]; [exists []; intros Hq'; lia|].
    destruct (uf_slack B APIf ra empty FF L A mem md s (bsz cap) (FW v) HMR Hin (HO Hq)
                ltac:(unfold bsz; lia)) as (slack & SB & SM & SBd).
    exists slack. intros _. unfold check_str_ok. rewrite unsigned_lit by lia.
    split; [lia|]. split; [exact (eq_sym ELv)|]. split; [exact SB|].
    split; [intros Hz; apply (reac_identity_fw_str_c3_nz v Hv _ Hz); reflexivity|].
    split; [rewrite ELv; exact SM|]. left. unfold CHECK_STR_FRAME. lia. }
  destruct SL as (slack & OK).
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 pc0) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (E03_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) s cap (fw_res v cap)
             (g_S g - SLOT_K) pc0 pc1 (FW v) slack CHK).
    - rewrite <- SEG. exact HMI.
    - rewrite <- (uf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (uf_getr_reg regs 23) by reflexivity. exact H23.
    - rewrite <- (uf_getr_reg regs 20) by reflexivity. exact H20.
    - rewrite <- (uf_getr_reg regs 10) by reflexivity. exact H10.
    - lia.
    - exact Hr.
    - unfold bsz in Hs2. lia.
    - lia.
    - exact OK.
    - exact ST.
    - lia.
    - exact HI.
    - exact PCS. }
  intros R pc' m' regs1 (Hreg & -> & MU & WM & RO) XR.
  destruct Hreg as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->).
  assert (KP1 : KP [2; 3; 4; 9; 19; 20; 21; 22; 23; 24; 25; 27] regs regs1) by uf_kp XR regs.
  assert (FRe : FReq g mem m').
  { unfold FReq. apply (uf_FReq_munch g _ mem m' MU); [| lia | lia].
    intros lo hi y Hy Hr'. destruct Hy as [Hy|[]]. injection Hy as <- <-. left. lia. }
  apply HX. apply (HQ s). exists L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (uf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' _ HF HP
             (KP1 2 ltac:(uf_in)) (KP1 3 ltac:(uf_in)) (KP1 4 ltac:(uf_in)) MU WM).
    intros lo hi y Hy Hr'. destruct Hy as [Hy|[]]. injection Hy as <- <-. left. lia. }
  split; [exact HP|].
  split.
  - split; [exact (uf_TID_tr g mem m' FRe HTID)|].
    split; [exact (uf_TL_kp g regs regs1 mem m' (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) FRe HTL)|].
    split; [uf_k KP1 20; exact H20|]. split; [uf_k KP1 21; exact H21 | uf_k KP1 22; exact H22].
  - split; [uf_k KP1 23; exact H23|].
    intros Hq. change (t_cap_fw (g_in g)) with cap in Hq.
    apply (uf_bytes_munch1 _ _ mem m' s _ MU); [|exact (HO Hq)].
    left. rewrite length_app. cbn [Datatypes.length]. unfold bsz in Hs2. lia.
Qed.

Lemma seg_E03 : Hcut B APIf ra (Inv_U137b8 B APIf ra empty) -> Hcut B APIf ra (Inv_U137ac B APIf ra empty).
Proof.
  intros HX g c Hc.
  assert (Hv : 0 <= fwT g < 65536).
  { unfold fwT, RcIdentModel.fw_milli. pose proof (uf_bz_range (RcIdentModel.nthb (idT (g_in g)) 0)).
    pose proof (uf_bz_range (RcIdentModel.nthb (idT (g_in g)) 1)). unfold RcIdentModel.bz. lia. }
  apply (e03_core g (fwT g) 0x137ac 0x137b8 (Inv_U137b8 B APIf ra empty g) (or_introl (conj eq_refl eq_refl)) Hv);
    [| exact (HX g) | exact Hc].
  intros s regs1 m' md H. exists s. exact H.
Qed.

End E03.
