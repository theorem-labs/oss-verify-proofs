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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_identity_fw_str_c.

Ltac f03_br :=
  lazymatch goal with
  | |- Exec.evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota|symmetry]
  end.

Section KA.
Context {fx : lib.Reusable.YK11.FPState}.

Lemma F03_x : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (m : word -> option byte) (sp v z : Z),
  reac_identity_fw_str_contract ->
  x2 = Z_to_bv 64 sp -> x22 = Z_to_bv 64 v -> x8 = Z_to_bv 64 (18446744073709551615 - (sp + 64)) ->
  0 <= v < 65536 -> 5 <= z <= 6 -> 0 <= sp -> sp + 384 <= 2 ^ 64 -> wr_at rsegs m sp 384 ->
  ov_read_bytes rsegs m (wa (sp + 192)) 8 = Some (le8 (Z_to_bv 64 z)) ->
  Exec.evt rsegs
    (fun ms => exists R pc' m', ms = MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
       (exists t0 t1 t2 r a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
          R = mkR (Z_to_bv 64 0x138c8) x2 x3 x4 t0 t1 t2 x8 x9 r a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 z) x19 x20
                x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 /\
          r = Z_to_bv 64 (L v)) /\
       pc' = Z_to_bv 64 0x138c8 /\ wmono rsegs m m' /\
       munch [(sp + 64 + z, sp + 64 + z + 1); (sp + 242, sp + 242 + L v + 1)] m m' /\
       bytes_at rsegs m' (sp + 64 + z) [z8] /\ bytes_at rsegs m' (sp + 242) (FW v ++ [Z_to_bv 8 0]))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        fp_regs (Z_to_bv 64 0x1389c) fp_csr None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 m sp v z FWS E2 E22 E8 Hv Hz Hsp Hsp2 WR RD.
  subst x2 x22 x8.
  pose proof (wr_at_store_ok rsegs m sp 384 (64 + z) 1 WR ltac:(lia) ltac:(lia)) as HS.
  replace (sp + (64 + z)) with (sp + 64 + z) in HS by lia.
  step. step. step. f03_br.
  2: { rewrite uf_ltu by lia. destruct (Z.ltb_spec 15 z); [lia | reflexivity]. }
  step. f03_br.
  2: { rewrite uf_ltu by lia. destruct (Z.ltb_spec (18446744073709551615 - (sp + 64)) z); [lia | reflexivity]. }
  step. step. step.
  match goal with |- Exec.evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ ?bs) _) =>
    replace bs with [z8] by (first [ reflexivity | unfold le1, z8; rewrite ?unsigned_lit by lia; reflexivity ])
  end.
  remember (write_to_mem m (Z_to_bv 64 (sp + 64 + z)) [z8]) as m1 eqn:Em1.
  assert (W1 : wr_at rsegs m1 sp 384) by (rewrite Em1; apply wr_at_write; exact WR).
  assert (B1 : bytes_at rsegs m1 (sp + 64 + z) [z8])
    by (rewrite Em1; apply bytes_at_write_same; cbn [Datatypes.length]; lia).
  assert (M1 : munch [(sp + 64 + z, sp + 64 + z + 1); (sp + 242, sp + 242 + L v + 1)] m m1).
  { rewrite Em1. apply munch_write; [apply munch_refl | lia | cbn [Datatypes.length]; lia |].
    cbn [Datatypes.length Frame.inside]. lia. }
  assert (WM1 : wmono rsegs m m1) by (rewrite Em1; apply wmono_write; apply wmono_refl).
  clear Em1.
  step. step. step. step.
  eapply evt_cut.
  { eapply FWS; try reflexivity; try lia.
    intros _ _. apply (uf_wr_sub _ sp 384); [exact W1 | lia | lia | lia]. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & HW
    & HA & HB).
  destruct (HB ltac:(lia) ltac:(lia)) as (Er & BY & MU).
  rewrite uf_ret_pc_lit by lia.
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [do 15 eexists; split; [reflexivity | exact Er]|].
  split; [reflexivity|].
  split; [eapply wmono_trans; [exact WM1 | exact HW]|].
  split.
  { apply (munch_trans _ m m1 m' M1). eapply munch_weaken; [|exact MU]. uf_subfp. }
  split; [|exact BY].
  apply (bytes_at_transport rsegs _ m1 m' _ _ B1 MU). cbn [disjoint_from Datatypes.length]. repeat split; lia.
Qed.

End KA.

Section F03.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis FWS : reac_identity_fw_str_contract.

Lemma seg_F03 : Hcut B APIf ra (Inv_U138c8 B APIf ra empty) -> Hcut B APIf ra (Inv_U1389c B APIf ra empty).
Proof.
  intros HX g c (L & A & regs & mem & md & -> & HF & HP & HE & H20 & H8 & HQ & HEF).
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
  assert (EL : 5 <= zlen (t_EF (g_in g)) <= 6).
  { unfold zlen, t_EF. fold v. rewrite !length_app. cbn [Datatypes.length].
    pose proof (uf_dec1_len (v / 1000) ltac:(Z.div_mod_to_equations; lia)) as E1.
    pose proof (uf_dec3_len (v mod 1000) ltac:(apply Z.mod_pos_bound; lia)) as E3.
    unfold dec_len in E1, E3. lia. }
  set (z := zlen (t_EF (g_in g))) in *.
  assert (Ez : Z.of_nat (length (t_EF (g_in g))) = z) by reflexivity.
  assert (WR : wr_at rsegs mem (fsp g) 384).
  { split; [lia|]. split; [lia|]. intros i Hi. pose proof (Hwin (fsp g + i) ltac:(lia)) as W.
    rewrite SEG in W. exact W. }
  assert (RD : ov_read_bytes rsegs mem (wa (fsp g + 192)) 8 = Some (le8 (Z_to_bv 64 z)))
    by (apply uf_rd_q64; exact HQ).
  eapply (uf_kA_run0 B APIf ra empty FF regs (Z_to_bv 64 0x1389c) mem md); [exact Hh | exact Hl | |].
  { unfold mkR_of.
    apply (F03_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem (fsp g) v z FWS).
    - rewrite <- (uf_getr_reg regs 2) by reflexivity. exact Hsp.
    - rewrite <- (uf_getr_reg regs 22) by reflexivity. exact H22.
    - rewrite <- (uf_getr_reg regs 8) by reflexivity. rewrite H8. unfold notw, spk. f_equal.
    - exact Hv.
    - exact EL.
    - lia.
    - lia.
    - exact WR.
    - exact RD. }
  intros R pc' m' regs1 (Hreg & -> & WM & MU & B0 & BY) XR.
  destruct Hreg as (t0 & t1 & t2 & r & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & -> & Er).
  assert (KP1 : KP [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by uf_kp XR regs.
  assert (G18 : getr regs1 18 = Z_to_bv 64 z) by (rewrite (uf_getr_x _ _ 18 XR) by reflexivity; reflexivity).
  assert (G10 : getr regs1 10 = Z_to_bv 64 (lib.Prog.reac_identity_fw_str_c.L v))
    by (rewrite (uf_getr_x _ _ 10 XR) by reflexivity; exact Er).
  assert (HWin : forall lo hi y,
            In (lo, hi) [(fsp g + 64 + z, fsp g + 64 + z + 1);
                         (fsp g + 242, fsp g + 242 + lib.Prog.reac_identity_fw_str_c.L v + 1)] ->
            lo <= y < hi -> fsp g + 69 <= y < fsp g + 71 \/ fsp g + 242 <= y < fsp g + 249).
  { intros lo hi y Hy Hr. destruct Hy as [Hy|[Hy|[]]]; injection Hy as <- <-; lia. }
  assert (OUT : FRout g [(fsp g + 64 + z, fsp g + 64 + z + 1);
                         (fsp g + 242, fsp g + 242 + lib.Prog.reac_identity_fw_str_c.L v + 1)]).
  { intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr). unfold spk. lia. }
  apply HX. exists L, A, regs1, m', md. split; [reflexivity|].
  split.
  { apply (uf_FR_munch B APIf ra empty FF g _ _ L A regs mem md regs1 m' _ HF HP
             (KP1 2 ltac:(uf_in)) (KP1 3 ltac:(uf_in)) (KP1 4 ltac:(uf_in)) MU WM).
    intros lo hi y Hy Hr. pose proof (HWin lo hi y Hy Hr). left. lia. }
  split; [exact HP|].
  split; [|exact G10].
  split.
  { split; [exact (uf_TID_munch g _ mem m' MU OUT HTID)|].
    split; [exact (uf_TL_munch g _ regs regs1 mem m'
                     (fun k Hk => KP1 k ltac:(cbn [In] in Hk |- *; tauto)) MU OUT HTL)|].
    uf_k KP1 22. exact H22. }
  split; [exact G18|].
  split.
  - unfold cstr. apply bytes_at_app. split.
    + unfold spk in HEF. apply (bytes_at_transport rsegs _ mem m' _ _ HEF MU).
      rewrite Ez. cbn [disjoint_from]. repeat split; lia.
    + rewrite Ez. unfold spk. exact B0.
  - unfold cstr, spk. exact BY.
Qed.

End F03.
