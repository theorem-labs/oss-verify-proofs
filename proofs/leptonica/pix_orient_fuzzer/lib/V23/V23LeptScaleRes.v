(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptScaleRes.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23_code_port_scaleres.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
Ltac fld_at F D aa bb C :=
  chain_step; [ reflexivity
              | eapply fp_step_fld with (a := aa) (bs := bb); [exact F | reflexivity | exact D | gres; imm_norm; addr_tac | repeat rdn_peel1; exact C]
              | step_simpl ]; fpn.
Ltac cvt_ff F D FZ :=
  chain_step; [ reflexivity
              | eapply fpv_step_fcvt_f_of_f; [exact F | reflexivity | exact D | right; split; reflexivity | left; split; reflexivity
                                             | cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ | reflexivity]
              | step_simpl ]; fpn.
Ltac cvt_fx F D FZ :=
  chain_step; [ reflexivity
              | eapply fpv_step_fcvt_f_of_x; [exact F | reflexivity | exact D | left; split; reflexivity | left; repeat split; reflexivity
                                             | cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ | reflexivity]
              | step_simpl ]; gres; fpn.
Ltac cvt_xf F D FZ :=
  chain_step; [ reflexivity
              | eapply fpv_step_fcvt_x_of_f; [exact F | reflexivity | exact D | right; left; repeat split; reflexivity | right; split; reflexivity
                                             | cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ | reflexivity]
              | step_simpl ]; fpn; fixv' (Z_to_bv 64 0) ltac:(vm_compute; reflexivity).
Ltac fma_at F D FZ :=
  chain_step; [ reflexivity
              | eapply fpv_step_fma; [exact F | reflexivity | exact D | cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ | reflexivity]
              | step_simpl ]; fpn.
Ltac fmin_at F D := chain_step; [ reflexivity | eapply fpv_step_fminmax; [exact F | reflexivity | exact D] | step_simpl ]; fpn.
Ltac fcmp_at F D := chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F | reflexivity | exact D] | step_simpl ]; fpn.

Definition PC_pixScaleResolution : Z := 0x6f748.

(* [comment removed for export] *)
Lemma sr_c05 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1ed08) 8 = Some (Z_to_le_bytes 8 0x3fe0000000000000).
Proof. vm_refl_bv. Qed.
Lemma sr_c1e8 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1ead0) 8 = Some (Z_to_le_bytes 8 0x4197d78400000000).
Proof. vm_refl_bv. Qed.
Lemma sr_cm1 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1eb38) 8 = Some (Z_to_le_bytes 8 0xbff0000000000000).
Proof. vm_refl_bv. Qed.
Lemma sr_c2p32 : rdn SEGS (fun _ => None) (Z_to_bv 64 0x1ec20) 8 = Some (Z_to_le_bytes 8 0x41f0000000000000).
Proof. vm_refl_bv. Qed.

Section ScaleRes.
Variable rom : word -> option byte.

Lemma sr05_seg : forall (fr : bvmap 5 word) (cs : bv 32) regs m (pix : Z) (v : pixv) (ret : word),
  frm_zero cs -> (1 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z -> (pix mod 8 = 0)%Z -> PIXat m pix v -> p_xres v = 0%Z -> p_yres v = 0%Z ->
  fpv_read fr FMT_S 10 = F05 -> fpv_read fr FMT_S 11 = F05 ->
  rdn SEGS m (Z_to_bv 64 0x1ed08) 8 = Some (Z_to_le_bytes 8 0x3fe0000000000000) ->
  rdn SEGS m (Z_to_bv 64 0x1ead0) 8 = Some (Z_to_le_bytes 8 0x4197d78400000000) ->
  rdn SEGS m (Z_to_bv 64 0x1eb38) 8 = Some (Z_to_le_bytes 8 0xbff0000000000000) ->
  rdn SEGS m (Z_to_bv 64 0x1ec20) 8 = Some (Z_to_le_bytes 8 0x41f0000000000000) ->
  store_ok SEGS m (Z_to_bv 64 (pix + 24)) 8 = true ->
  getr regs 10 = Z_to_bv 64 pix -> getr regs 1 = ret -> ret_ok ret ->
  exists fr' cs' regs',
    msteps SEGS (@mkst (mkFP fr cs) regs (0x6f748 : word) m rom)
                (@mkst (mkFP fr' cs') regs' ret
                   (wbytes (wbytes m (Z_to_bv 64 (pix + 24)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (pix + 28)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
    /\ frm_zero cs' /\ (forall r : reg, In (bv_unsigned r) fs_list -> reg_get fr' r = reg_get fr r)
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs'.
Proof.
  intros fr cs regs m pix v ret FZ Hp1 Hp64 AL8 PX X0 Y0 F10 F11 C05 C1E8 CM1 C2P32 SOK H10 H1 Hret.
  pose proof (sr_rd_xres SEGS m pix v PX) as RX. rewrite X0 in RX.
  pose proof (sr_rd_yres SEGS m pix v PX) as RY. rewrite Y0 in RY.
  eexists _, _, _. split.
  - stepb_ft F_6f748 D_6f748 ltac:(condZ).
    chain_step; [ reflexivity | eapply fp_step_fmv_w_x; [exact F_6f74c | reflexivity | exact D_6f74c] | step_simpl ]; gres; fpn.
    fcmp_at F_6f750 D_6f750. rewrite ?F10, ?F11.
    stepb_ft F_6f754 D_6f754 ltac:(condR).
    fcmp_at F_6f758 D_6f758. rewrite ?F10, ?F11.
    stepb_ft F_6f75c D_6f75c ltac:(condR).
    guard8 F_6f760 D_6f760 AL8.
    stepb_ft F_6f764 D_6f764 ltac:(condR).
    stepLD F_6f768 D_6f768 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; exact RX) ltac:(apply lez4; lia).
    sn F_6f76c D_6f76c.
    fld_at F_6f770 D_6f770 (Z_to_bv 64 0x1ed08) (Z_to_le_bytes 8 0x3fe0000000000000) C05.
    sn F_6f774 D_6f774.
    fld_at F_6f778 D_6f778 (Z_to_bv 64 0x1ead0) (Z_to_le_bytes 8 0x4197d78400000000) C1E8.
    cvt_ff F_6f77c D_6f77c FZ. rewrite ?F10, ?F11.
    cvt_fx F_6f780 D_6f780 FZ.
    sn F_6f784 D_6f784.
    fld_at F_6f788 D_6f788 (Z_to_bv 64 0x1eb38) (Z_to_le_bytes 8 0xbff0000000000000) CM1.
    cvt_ff F_6f78c D_6f78c FZ.
    fma_at F_6f790 D_6f790 FZ.
    fmin_at F_6f794 D_6f794.
    fcmp_at F_6f798 D_6f798.
    stepb_ft F_6f79c D_6f79c ltac:(condR).
    sn F_6f7a0 D_6f7a0.
    fld_at F_6f7a4 D_6f7a4 (Z_to_bv 64 0x1ec20) (Z_to_le_bytes 8 0x41f0000000000000) C2P32.
    fcmp_at F_6f7a8 D_6f7a8.
    stepb_ft F_6f7ac D_6f7ac ltac:(condR).
    stepLD F_6f7b0 D_6f7b0 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; exact RY) ltac:(apply lez4; lia).
    cvt_ff F_6f7b4 D_6f7b4 FZ. rewrite ?F10, ?F11.
    cvt_fx F_6f7b8 D_6f7b8 FZ.
    cvt_ff F_6f7bc D_6f7bc FZ.
    fma_at F_6f7c0 D_6f7c0 FZ.
    cvt_xf F_6f7c4 D_6f7c4 FZ.
    fmin_at F_6f7c8 D_6f7c8.
    fcmp_at F_6f7cc D_6f7cc.
    stepST F_6f7d0 D_6f7d0 (Z_to_bv 64 (pix + 24)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    stepb_ft F_6f7d4 D_6f7d4 ltac:(condR).
    fcmp_at F_6f7d8 D_6f7d8.
    stepb_ft F_6f7dc D_6f7dc ltac:(condR).
    cvt_xf F_6f7e0 D_6f7e0 FZ.
    stepST F_6f7e4 D_6f7e4 (Z_to_bv 64 (pix + 28)) (Z_to_bv 64 0) ltac:(sok_in SOK).
    sn F_6f7e8 D_6f7e8.
    stepret F_6f7ec D_6f7ec ret ltac:(exact H1).
    apply mst_refl.
  - cbn [fp_regs fp_csr]. split; [repeat apply fpv_frm_acc; exact FZ|].
    split; [intros r Hr; repeat (rewrite fpv_get_other; [| intros ->; cbv in Hr; lia]); reflexivity|].
    repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.
End ScaleRes.

Section ScaleResW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Theorem pixScaleResolution_05_W : forall fr cs C A m md regs (pix : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pix ->
  fpv_read fr FMT_S 10 = F05 -> fpv_read fr FMT_S 11 = F05 ->
  PIXat m pix v -> p_xres v = 0%Z -> p_yres v = 0%Z -> live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall fr' cs' m' regs', W C A m' md -> frm_zero cs' -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     regs_agree (fun r => In r [10; 11; 12; 13]%list) regs regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     PIXat m' pix v -> (forall a : word, ~ (pix + 24 <= u a < pix + 32)%Z -> m' a = m a) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0x6f748 : word) m al_rom) md) S.
Proof.
  intros fr cs C A m md regs pix v ret S CK HW FZ H1 Hret H10 F10 F11 PX X0 Y0 LA LA0 K.
  pose proof PX as (Hp0 & Hp64 & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW LA ltac:(lia)) as [G TOP]. rewrite u_Z2bv in G, TOP by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) LA) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (RO : forall (a : Z) (n : nat), (0x10000 <= a)%Z -> (a + Z.of_nat n <= 0x123000)%Z ->
                 rdn SEGS m (Z_to_bv 64 a) n = rdn SEGS (fun _ => None) (Z_to_bv 64 a) n).
  { intros a n Ha Hn. rewrite <- p16_segs. apply (W_rdn_ro C A m md a n HW); cbv [fst snd ll_ro LLU16]; lia. }
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (pix + 24)) 8 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]. intros x Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A m _ (Z_to_bv 64 pix) _ x CK HW LA ltac:(rewrite u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia)) as (_ & D & _).
    exact (D E). }
  destruct (sr05_seg al_rom fr cs regs m pix v ret FZ ltac:(lia) Hp64 (al16_mod8 _ ALp) PX X0 Y0 F10 F11
              ltac:(rewrite RO by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact sr_c05)
              ltac:(rewrite RO by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact sr_c1e8)
              ltac:(rewrite RO by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact sr_cm1)
              ltac:(rewrite RO by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); exact sr_c2p32)
              SOK H10 H1 Hret)
    as (fr' & cs' & regs' & RUN & FZ' & FS & R10 & AG).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  assert (HW1 : W C A (wbytes m (Z_to_bv 64 (pix + 24)) (word_to_le_bytes 4 (Z_to_bv 64 0))) md).
  { apply (W_store_blk C A m md (Z_to_bv 64 pix) _ 64 _ CK HW LA LA0);
      rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  apply K.
  - apply (W_store_blk C A _ md (Z_to_bv 64 pix) _ 64 _ CK HW1 LA LA0);
      rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
  - exact FZ'.
  - exact FS.
  - exact AG.
  - exact R10.
  - apply sr_wr_yres0; [apply sr_wr_xres0; [exact PX | exact X0] | exact Y0].
  - intros x Hx. rewrite !MemSplit.wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
      try reflexivity; lia.
Qed.

End ScaleResW.
