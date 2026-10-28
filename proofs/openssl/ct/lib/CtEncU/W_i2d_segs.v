(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApWalkTac W_asn1_string W_item_d2i_img.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep W_sct_leaves W_sk_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncPure EncStmt EncKit W_asn1_enc_leaves W_asn1_i2d W_asn1_i2d2 W_i2o_sct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling. Context {CE__ : Ceiling}.
Local Notation mem := (word -> option byte).
Ltac xport H MU WM := apply (fun H0 => rw_cells_transport _ _ _ _ _ _ H0 MU WM) in H; [| cbn [cells_size csize]; rewrite ?Nat.add_0_r, ?Z2Nat.id by lia; cbn; lia].

Definition SKNUM_RET : Z := 0x19d168.      (* [comment removed for export] *)
Definition I2O_LIST_EPI : Z := 0x19d2f8.   (* [comment removed for export] *)
Definition I2O_LIST_FIN : Z := 0x19d228.   (* [comment removed for export] *)
Definition I2D_RET1 : Z := 0x19d440.       (* [comment removed for export] *)
Definition I2D_RET2 : Z := 0x19d450.       (* [comment removed for export] *)
Definition I2D_EPI : Z := 0x19d498.        (* [comment removed for export] *)
Definition ASN1_OCTET_STRING_NEW : Z := 0x1150d8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i2d_entry_seg : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo SA n DER : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 272 -> bv_unsigned sp mod 16 = 0 ->
  0 < SA -> SA + STACK_SIZE <= lo -> SA mod 8 = 0 -> ro_cells ctusegs m SA [C4 (wz n)] -> 0 <= n < 2^31 ->
  a0 = wz SA -> a1 = Z_to_bv 64 DER ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' j1 j2 j3,
       ms' = MS (mkR (Z_to_bv 64 SKNUM_RET) (Z_to_bv 64 (bv_unsigned sp + -256)) gp tp t0' t1' t2' (Z_to_bv 64 (bv_unsigned sp + -160)) (Z_to_bv 64 0)
                     (Z_to_bv 64 n) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 SA) (Z_to_bv 64 0) s4 (Z_to_bv 64 1) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 SKNUM_RET) fc None m' (seg_rom ctusegs)
       /\ munch [(bv_unsigned sp - 272, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp + -256)
       /\ rw_cells ctusegs m' (bv_unsigned sp + -64) [CB 8%nat j1; C8 (Z_to_bv 64 0); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
       /\ rw_cells ctusegs m' (bv_unsigned sp + -160)
            [CB 8%nat j2; C8 (Z_to_bv 64 0); C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 (Z_to_bv 64 DER); C8 s1; C8 sp; C8 (Z_to_bv 64 I2D_RET1)]
       /\ rw_cells ctusegs m' (bv_unsigned sp + -256)
            [CB 8%nat j3; C8 (Z_to_bv 64 0); C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 SA);
             C8 (Z_to_bv 64 (bv_unsigned sp + -56)); C8 (Z_to_bv 64 (bv_unsigned sp + -64)); C8 (Z_to_bv 64 0x19d2a8)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 I2D_SCT_LIST) fc None m (seg_rom ctusegs)).
Proof.
  intros until DER. intros ST MI GLO LO SP16 SA0 SALO SA8 RNUM NR -> ->.
  unfold GLOBALS_TOP in GLO. unfold I2D_SCT_LIST, SKNUM_RET, I2D_RET1, STACK_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  (* [comment removed for export] *)
  carve_frame 64%nat ST. do 7 zstep. zstep. zstep. zstep. zstep. zstep. rename FR into FR1.
  (* [comment removed for export] *)
  carve_frame 96%nat ST. do 10 zstep. zstep. zstep. zstep. zstep. zstep. zstep. sfalse. ub. zstep. zstep. zstep. btaken. rename FR into FR2.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  carve_frame 96%nat ST. do 10 zstep. zstep. zstep. zstep. zstep. zstep. zstep. btaken. zstep. zstep. zstep. rename FR into FR3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -256)) = bv_unsigned sp + -256) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply (OPENSSL_sk_num_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo SA n);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| unfold STACK_SIZE; lia| exact SA8| exact RNUM| lia| reflexivity]. }
  unfold nid_post. cbv beta. intros ms1 PO. rewrite ?ESP in PO.
  destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  replace (ret_pc (Z_to_bv 64 0x19d168)) with (Z_to_bv 64 0x19d168) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  xport FR1 MU2 WM2. xport FR2 MU2 WM2. xport FR3 MU2 WM2.
  apply evt_done. do 14 eexists. exists m2. do 3 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
  split; [exact FR1|]. split; [exact FR2| exact FR3].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i2o_list_epilogue : forall x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (j : list byte) (c0 v24 v23 v22 v21 v20 v19 v18 v9 v8 vra : word),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> lo <= bv_unsigned sp -> bv_unsigned sp + 96 < 2^64 ->
  rw_cells ctusegs m (bv_unsigned sp) [CB 8%nat j; C8 c0; C8 v24; C8 v23; C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 vra] ->
  evt ctusegs (fun ms' =>
       ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 96)) gp tp t0 t1 t2 v8 v9 (Z_to_bv 64 (bv_swrap 32 (bv_unsigned s4))) a1 a2 a3 a4 a5 a6 a7
                     v18 v19 v20 v21 v22 v23 v24 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc vra) fc None m (seg_rom ctusegs)
       /\ stk ctusegs m lo (bv_unsigned sp + 96))
    (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 I2O_LIST_EPI) fc None m (seg_rom ctusegs)).
Proof.
  intros until vra. intros ST MI LO HI FR. unfold I2O_LIST_EPI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  zstep. rewrite Z.add_0_r. do 10 zstep. zstep. release_frame FR ST (bv_unsigned sp + 96). zstep.
  apply evt_done. split; [reflexivity| exact ST].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma write_entry_seg : forall ra (sp : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo SA n AD : Z) j1 j2 (f2 f3 f4 f5 f6 f7 : word) (c0 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 : word),
  stk ctusegs m lo (bv_unsigned sp + -160) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 176 -> bv_unsigned sp < 2^63 ->
  0 < SA -> SA + STACK_SIZE <= lo -> SA mod 8 = 0 -> ro_cells ctusegs m SA [C4 (wz n)] -> 0 <= n < 2^31 -> 0 < AD -> AD + 2 <= lo ->
  rw_cells ctusegs m (bv_unsigned sp + -64) [CB 8%nat j1; C8 (Z_to_bv 64 0); C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7] ->
  rw_cells ctusegs m (bv_unsigned sp + -160) [CB 8%nat j2; C8 c0; C8 g0; C8 g1; C8 g2; C8 g3; C8 g4; C8 g5; C8 g6; C8 g7; C8 g8; C8 g9] ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
       ms' = MS (mkR (Z_to_bv 64 SKNUM_RET) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0' t1' t2' (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 (bv_unsigned sp + -56))
                     (Z_to_bv 64 n) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 SA) (Z_to_bv 64 0) s4 (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 SKNUM_RET) fc None m' (seg_rom ctusegs)
       /\ munch [(bv_unsigned sp - 176, bv_unsigned sp + -48)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp + -160)
       /\ rw_cells ctusegs m' (bv_unsigned sp + -64) [CB 8%nat j1; C8 (Z_to_bv 64 AD); C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7]
       /\ rw_cells ctusegs m' (bv_unsigned sp + -160) [CB 8%nat j2; C8 (Z_to_bv 64 (AD + 2)); C8 g0; C8 g1; C8 g2; C8 g3; C8 g4; C8 g5; C8 g6; C8 g7; C8 g8; C8 g9])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 (bv_unsigned sp + -56))
             (Z_to_bv 64 AD) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SA) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19d2c0) fc None m (seg_rom ctusegs)).
Proof.
  intros until g9. intros ST MI GLO LO SP63 SA0 SALO SA8 RNUM NR AD0 ADLO FR1 FR2.
  unfold GLOBALS_TOP in GLO. unfold SKNUM_RET, STACK_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp + -48)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160)) = bv_unsigned sp + -160) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  zstep. zstep. strue. ub. zstep. zstep. zstep. zstep. zstep. change (Z.b2z (0 <? 0)) with 0.
  eapply evt_cut.
  { eapply (OPENSSL_sk_num_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo SA n);
      [rewrite ESP; exact ST| assumption| unfold GLOBALS_TOP; lia| rewrite ESP; lia| unfold STACK_SIZE; lia| exact SA8| exact RNUM| lia| reflexivity]. }
  unfold nid_post. cbv beta. intros ms1 PO. rewrite ?ESP in PO.
  destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  replace (ret_pc (Z_to_bv 64 0x19d168)) with (Z_to_bv 64 0x19d168) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  xport FR1 MU2 WM2. xport FR2 MU2 WM2.
  apply evt_done. do 14 eexists. exists m2. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
  split; [exact FR1| exact FR2].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma outer_tail_seg : forall x1 (sp : word) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo AD len2 : Z) j1 j2 (f2 f3 f4 f5 f6 f7 : word) (c0 g0 g1 g2 g3 g4 g5 g6 g7 g8 : word) bs,
  stk ctusegs m lo (bv_unsigned sp + -160) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp + -160 -> bv_unsigned sp < 2^63 -> bv_unsigned sp mod 16 = 0 ->
  0 < AD -> AD + len2 <= lo -> 2 <= len2 <= 65535 ->
  rw_cells ctusegs m (bv_unsigned sp + -64) [CB 8%nat j1; C8 (Z_to_bv 64 AD); C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7] ->
  rw_cells ctusegs m (bv_unsigned sp + -160) [CB 8%nat j2; C8 c0; C8 g0; C8 g1; C8 g2; C8 g3; C8 g4; C8 g5; C8 g6; C8 g7; C8 g8; C8 (Z_to_bv 64 I2D_RET1)] ->
  rw_cells ctusegs m AD [CB (Z.to_nat len2) bs] ->
  evt ctusegs (fun ms' => exists a1' a2' a3' m' bs',
       ms' = MS (mkR (Z_to_bv 64 I2D_RET1) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 g8 g7
                     (Z_to_bv 64 len2) a1' a2' a3' a4 a5 a6 a7 g6 g5 g4 g3 g2 g1 g0 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 I2D_RET1) fc None m' (seg_rom ctusegs)
       /\ munch [(bv_unsigned sp + -160, bv_unsigned sp + -64); (AD, AD + 2)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp + -64)
       /\ rw_cells ctusegs m' (bv_unsigned sp + -64) [CB 8%nat j1; C8 (Z_to_bv 64 AD); C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7]
       /\ rw_cells ctusegs m' AD [CB (Z.to_nat len2) bs'])
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -64)) (Z_to_bv 64 (bv_unsigned sp + -56))
             a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 len2) (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 I2O_LIST_FIN) fc None m (seg_rom ctusegs)).
Proof.
  intros until bs. intros ST MI GLO LO SP63 SP16 AD0 ADLO L2 FR1 FR2 HB.
  unfold GLOBALS_TOP in GLO. unfold I2O_LIST_FIN, I2D_RET1, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp + -160, bv_unsigned sp + -64); (AD, AD + 2)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  (* [comment removed for export] *)
  replace len2 with (2 + (len2 - 2)) in HB by lia.
  pose proof (cb_split2 m AD 2 (len2 - 2) bs HB ltac:(lia) ltac:(lia)) as [HB2 HBR]. clear HB.
  pose proof (cells_at_wf _ _ _ _ (proj1 HB2)) as [WF2 _]. cbn in WF2.
  destruct (take (Z.to_nat 2) bs) as [|b0 [|b1 [|b2 br]]] eqn:EJ; cbn [length] in WF2; try lia. clear WF2 EJ.
  assert (HS2 : rw_cells ctusegs m AD [C1 b0; C1 b1]).
  { eapply rw_cells_recast; [exact HB2| cbn; repeat split; reflexivity| reflexivity| reflexivity]. }
  clear HB2.
  (* [comment removed for export] *)
  zstep. sfalse. ub. zstep. zstep. ub. zstep. zstep. zstep. zstep. zstep. ub. zstep. zstep. ub. zstep. zstep. btaken.
  (* [comment removed for export] *)
  zstep. rewrite Z.add_0_r, (swrap32_small len2) by lia. do 10 zstep. zstep. release_frame FR2 ST (bv_unsigned sp + -64). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  apply cells_blob in HS2. cbn [cells_size csize Nat.add] in HS2.
  lazymatch type of HS2 with rw_cells _ _ _ [CB _ ?l] => change (rw_cells ctusegs m2 AD [CB (Z.to_nat 2) l]) in HS2 end.
  pose proof (cb_join2 _ _ _ _ _ _ HS2 HBR ltac:(lia) ltac:(lia)) as J. replace (2 + (len2 - 2)) with len2 in J by lia.
  apply evt_done. do 3 eexists. exists m2. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR1| exact J].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i2d_call_new_seg : forall (P : machine_state -> Prop)
    x1 (sp : word) gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo len2 : Z),
  stk ctusegs m lo (bv_unsigned sp + -64) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 80 -> bv_unsigned sp < 2^63 ->
  0 <= len2 <= 65535 ->
  (forall m1, munch [(bv_unsigned sp - 80, bv_unsigned sp + -64)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
              stk ctusegs m1 lo (bv_unsigned sp + -64) ->
              evt ctusegs P (MS (mkR (Z_to_bv 64 I2D_RET2) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (-1)) (wz V_ASN1_OCTET_STRING)
                                      a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 len2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz ASN1_STRING_TYPE_NEW) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len2) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 I2D_RET1) fc None m (seg_rom ctusegs)).
Proof.
  intros until len2. intros ST MI GLO LO SP63 L2 K.
  unfold GLOBALS_TOP in GLO. unfold I2D_RET1, I2D_RET2, ASN1_STRING_TYPE_NEW, V_ASN1_OCTET_STRING, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp + -64)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep. sfalse. zstep. zstep.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep. zstep. do 2 zstep. zstep. release_frame FR ST (bv_unsigned sp + -64). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (K mx MU WM ltac:(assumption) ST) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i2d_set0_seg : forall x1 (sp : word) gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo A AD len2 : Z) j1 (f2 f3 f4 f5 f6 f7 : word),
  stk ctusegs m lo (bv_unsigned sp + -64) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 160 -> bv_unsigned sp < 2^63 ->
  0 < A -> A + ASN1_STRING_SIZE <= lo -> A mod 8 = 0 -> 0 < AD < 2^64 -> 2 <= len2 <= 65535 ->
  rw_cells ctusegs m A (asn1_string_cells 0 V_ASN1_OCTET_STRING 0 0) ->
  rw_cells ctusegs m (bv_unsigned sp + -64) [CB 8%nat j1; C8 (Z_to_bv 64 AD); C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7] ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m',
       ms' = MS (mkR (Z_to_bv 64 0x19d470) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz RATP) t0' t1' t2' sp (Z_to_bv 64 (-1))
                     (Z_to_bv 64 A) s2 (wz ITEM_OCTET) (wz 0) a4' a5' a6' a7' s2 (Z_to_bv 64 A) (Z_to_bv 64 len2) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (wz ASN1_ITEM_FLAGS_I2D) fc None m' (seg_rom ctusegs)
       /\ munch [(bv_unsigned sp - 160, bv_unsigned sp + -64); (A, A + ASN1_STRING_SIZE)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
       /\ stk ctusegs m' lo (bv_unsigned sp + -64)
       /\ rw_cells ctusegs m' A (asn1_string_cells len2 V_ASN1_OCTET_STRING AD 0)
       /\ rw_cells ctusegs m' (bv_unsigned sp + -64) [CB 8%nat j1; C8 (Z_to_bv 64 AD); C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7])
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 (-1)) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 len2) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 I2D_RET2) fc None m (seg_rom ctusegs)).
Proof.
  intros until f7. intros ST MI GLO LO SP63 A0 ALO A8 ADR L2 HS FR1.
  unfold GLOBALS_TOP in GLO. unfold I2D_RET2, ASN1_STRING_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp + -64); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  zstep. zstep. sfalse. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply ASN1_STRING_set0_walk with (lo := lo) (A := A) (D := AD) (ty := V_ASN1_OCTET_STRING) (len := len2); rewrite ?ESP;
      [exact ST| unfold GLOBALS_TOP; lia| unfold ASN1_STRING_SET0_STACK; lia| exact MI| lia| unfold ASN1_STRING_SIZE; lia| lia| lia
      | unfold V_ASN1_OCTET_STRING; lia| exact HS| exact A8| reflexivity| reflexivity| reflexivity]. }
  cbv beta. intros ms1 PO. rewrite ?ESP in PO. unfold ASN1_STRING_SET0_STACK, ASN1_STRING_SIZE in PO.
  destruct PO as (u5 & u6 & u7 & u10 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & HS2).
  replace (ret_pc (Z_to_bv 64 0x19d464)) with (Z_to_bv 64 0x19d464) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  xport FR1 MU2 WM2.
  assert (MU' : munch [(bv_unsigned sp - 160, bv_unsigned sp + -64); (A, A + 24)]%Z m m2).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 MI ST. rename MU' into MU. rename WM' into WM.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  eapply i2d_octet_fwd with (lo := lo); rewrite ?ESP; [exact ST2| exact MI2| unfold GLOBALS_TOP; lia| lia|].
  intros m3 MU3 WM3 MI3 ST3. rewrite ?ESP in *.
  xport FR1 MU3 WM3. xport HS2 MU3 WM3.
  apply evt_done. do 11 eexists. exists m3. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  split; [eapply wmono_trans; [exact WM| exact WM3]|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact HS2| exact FR1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i2d_epilogue : forall x1 (sp : word) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) j1 (f1 f2 f3 f4 f5 f6 f7 : word),
  stk ctusegs m lo (bv_unsigned sp + -64) -> mem_inv ctusegs m -> lo <= bv_unsigned sp + -64 -> bv_unsigned sp < 2^63 ->
  rw_cells ctusegs m (bv_unsigned sp + -64) [CB 8%nat j1; C8 f1; C8 f2; C8 f3; C8 f4; C8 f5; C8 f6; C8 f7] ->
  evt ctusegs (fun ms' =>
       ms' = MS (mkR f7 sp gp tp t0 t1 t2 f6 f5 s1 a1 a2 a3 a4 a5 a6 a7 f4 f3 f2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc f7) fc None m (seg_rom ctusegs)
       /\ stk ctusegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 I2D_EPI) fc None m (seg_rom ctusegs)).
Proof.
  intros until f7. intros ST MI LO SP63 FR. unfold I2D_EPI in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  zstep. do 6 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. split; [reflexivity| exact ST].
Qed.
End WithCeiling.
