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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv put_dec_c
  reac_identity_fw_str_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_sef.
Import ListNotations.
Open Scope Z_scope.

Section KA.
Context {fx : YK11.FPState}.

Lemma F03_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp v z : Z),
  reac_identity_fw_str_contract ->
  x2 = Z_to_bv 64 sp -> x20 = Z_to_bv 64 v -> x22 = Z_to_bv 64 (sp + 48) ->
  0 <= v < 65536 -> 5 <= z <= 6 -> 0 <= sp -> sp + 368 <= 2 ^ 64 -> wr_at rsegs m sp 368 ->
  ov_read_bytes rsegs m (wa (sp + 176)) 8 = Some (le8 (Z_to_bv 64 z)) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x136c0) x2 x3 x4 t0 t1 t2 x8 x9 r a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
                (Z_to_bv 64 z) (Z_to_bv 64 (sp + 48 + z)) x23 x24 x25 x26 x27 t3 t4 t5 t6 /\
          r = Z_to_bv 64 (L v)) /\
       pc' = Z_to_bv 64 0x136c0 /\ wmono rsegs m m' /\
       munch [(sp + 48 + z, sp + 48 + z + 1); (sp + 226, sp + 226 + L v + 1)] m m' /\
       bytes_at rsegs m' (sp + 48 + z) [z8] /\ bytes_at rsegs m' (sp + 226) (FW v ++ [Z_to_bv 8 0]))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x136a4) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp v z FWS E2 E20 E22 Hv Hz Hsp Hsp2 WR RD.
  subst x2 x20 x22.
  pose proof (wr_at_store_ok rsegs m sp 368 (48 + z) 1 WR ltac:(lia) ltac:(lia)) as HS.
  replace (sp + (48 + z)) with (sp + 48 + z) in HS by lia.
  step. step. step.
  match goal with |- Exec.evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
    replace bs with [z8] by (first [ reflexivity | unfold le1, z8; rewrite ?unsigned_lit by lia; reflexivity ])
  end.
  remember (write_to_mem m (Z_to_bv 64 (sp + 48 + z)) [z8]) as m1 eqn:Em1.
  assert (W1 : wr_at rsegs m1 sp 368) by (rewrite Em1; apply wr_at_write; exact WR).
  assert (B1 : bytes_at rsegs m1 (sp + 48 + z) [z8])
    by (rewrite Em1; apply bytes_at_write_same; cbn [Datatypes.length]; lia).
  assert (M1 : munch [(sp + 48 + z, sp + 48 + z + 1); (sp + 226, sp + 226 + L v + 1)] m m1).
  { rewrite Em1. apply munch_write; [apply munch_refl | lia | cbn [Datatypes.length]; lia |].
    cbn [Datatypes.length Frame.inside]. lia. }
  assert (WM1 : wmono rsegs m m1) by (rewrite Em1; apply wmono_write; apply wmono_refl).
  clear Em1.
  step. step. step. step.
  eapply evt_cut.
  { eapply FWS; try reflexivity; try lia.
    intros _ _. apply (sf_wr_sub _ sp 368); [exact W1 | lia | lia | lia]. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & HW
    & HA & HB).
  destruct (HB ltac:(lia) ltac:(lia)) as (Er & BY & MU).
  rewrite sf_ret_pc_lit by lia.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [do 15 eexists; split; [reflexivity | exact Er]|].
  split; [reflexivity|].
  split; [eapply wmono_trans; [exact WM1 | exact HW]|].
  split.
  { apply (munch_trans _ m m1 m' M1). eapply munch_weaken; [|exact MU]. sf_subfp. }
  split; [|exact BY].
  apply (bytes_at_transport rsegs _ m1 m' _ _ B1 MU). cbn [disjoint_from Datatypes.length]. repeat split; lia.
Qed.

End KA.

Section F03.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis FWS : reac_identity_fw_str_contract.

Lemma seg_F03 : Hcut B APIf ra (Inv_K136c0 B APIf ra empty) -> Hcut B APIf ra (Inv_K136a4 B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & HE & H21 & H22 & HQ & HEF).
  pose proof (sf_segs B APIf ra empty FF) as SEG.
  pose proof HF as (HGV & Hsp & Hgp & Htp & Hsv & Hstk & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & Hsk & HRS & Hwin).
  destruct (sf_stk_fsp B APIf ra empty g _ _ L A regs mem md HF) as (ST & HI & HL & Hfs & HSc & HS47 & HK & _).
  pose proof (@YM05.alloc_ceiling_val rc) as HAC.
  destruct (mr_model B _ (aa_laws (APIf rc)) L A mem md HMR) as (Hh & Hl & _).
  pose proof HE as (HTID & HTL & H20).
  set (v := t_any_fw (g_in g)) in *.
  assert (Hv : 0 <= v < 65536).
  { unfold v, t_any_fw, tb. pose proof (inb_range (g_in g) (cT (g_in g) + 9)).
    pose proof (inb_range (g_in g) (cT (g_in g) + 10)). lia. }
  pose proof (reac_identity_fw_str_c3_len v Hv) as (_ & HLv).
  assert (HLr : 5 <= reac_identity_fw_str_c.L v <= 6) by (destruct (v <? 10000); lia).
  assert (EL : 5 <= zlen (t_EF (g_in g)) <= 6).
  { unfold zlen, t_EF. fold v. rewrite !length_app. cbn [Datatypes.length].
    pose proof (sf_dec1_len (v / 1000) ltac:(Z.div_mod_to_equations; lia)) as E1.
    pose proof (sf_dec3_len (v mod 1000) ltac:(apply Z.mod_pos_bound; lia)) as E3.
    unfold dec_len in E1, E3. lia. }
  set (z := zlen (t_EF (g_in g))) in *.
  assert (Ez : Z.of_nat (length (t_EF (g_in g))) = z) by reflexivity.
  assert (WR : wr_at rsegs mem (fsp g) 368).
  { split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hwin (fsp g + i) ltac:(lia)) as W.
    rewrite SEG in W. exact W. }
  assert (RD : ov_read_bytes rsegs mem (wa (fsp g + 176)) 8 = Some (le8 (Z_to_bv 64 z)))
    by (apply sf_rd_q64; exact HQ).
  eapply (sf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x136a4) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (F03_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) v z FWS).
    - rewrite <- (sf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (sf_getr_reg regs 20) by reflexivity. exact H20.
    - rewrite <- (sf_getr_reg regs 22) by reflexivity. exact H22.
    - exact Hv.
    - exact EL.
    - lia.
    - lia.
    - exact WR.
    - exact RD. }
  intros R pc' m' regs1 (Hreg & -> & WM & MU & B0 & BY) XR.
  destruct Hreg as (t0 & t1 & t2 & r & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & -> & Er).
  assert (KP1 : KP [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27] regs regs1) by sf_kp XR regs.
  assert (G21 : getr regs1 21 = Z_to_bv 64 z) by (rewrite (sf_getr_x _ _ 21 XR) by reflexivity; reflexivity).
  assert (G22 : getr regs1 22 = Z_to_bv 64 (spk g 48 + z))
    by (rewrite (sf_getr_x _ _ 22 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (reac_identity_fw_str_c.L v))
    by (rewrite (sf_getr_x _ _ 10 XR) by reflexivity; exact Er).
  assert (HWin : forall lo hi y,
            In (lo, hi) [(fsp g + 48 + z, fsp g + 48 + z + 1);
                         (fsp g + 226, fsp g + 226 + reac_identity_fw_str_c.L v + 1)] ->
            lo <= y < hi -> fsp g + 53 <= y < fsp g + 55 \/ fsp g + 226 <= y < fsp g + 233).
  { intros lo hi y Hy Hr. destruct Hy as [Hy|[Hy|[]]]; injection Hy as <- <-; lia. }
  assert (OUT : FRout g [(fsp g + 48 + z, fsp g + 48 + z + 1);
                         (fsp g + 226, fsp g + 226 + reac_identity_fw_str_c.L v + 1)]).
  { intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr). unfold spk. lia. }
  apply HX. exists L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (sf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' _ HF HP
             (KP1 2 ltac:(sf_in)) (KP1 3 ltac:(sf_in)) (KP1 4 ltac:(sf_in)) MU WM).
    intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr). left. lia. }
  split; [exact HP|].
  split; [|exact G10].
  split.
  { split; [exact (sf_TID_munch g _ mem m' MU OUT HTID)|].
    split; [exact (sf_TL_munch g _ regs regs1 mem m'
                     (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) MU OUT HTL)|].
    sf_k KP1 20. exact H20. }
  split; [exact G21|]. split; [exact G22|].
  split.
  - unfold cstr. apply bytes_at_app. split.
    + unfold spk in HEF. apply (bytes_at_transport rsegs _ mem m' _ _ HEF MU).
      rewrite Ez. cbn [disjoint_from]. repeat split; lia.
    + rewrite Ez. unfold spk. exact B0.
  - unfold cstr, spk. exact BY.
Qed.

End F03.
